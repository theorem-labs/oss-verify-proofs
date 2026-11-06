(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second half of one round of the split loop of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x8698c .. 0x869dc: the UBSan guard of t + strcspn, the word's end and its byte, the UBSan guard of t + 1, the NUL at the word's end, the shadow check of the next byte; to the head 0x868e4 or to LO_K 0x86a04), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s48.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment closed by the statements of the points it leaves to) over the released plain proof's sw_round (lib/Prog/SlotWords.v). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB CmdGlob PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s40 LLVMFuzzerTestOneInput_s49.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the copy buffer with one byte replaced (the NUL the round puts at the word's end) ---- *)
Fixpoint s48_upd (l : list byte) (j : nat) (x : byte) : list byte :=
  match l, j with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', Datatypes.S j' => y :: s48_upd l' j' x
  end.
Lemma s48_upd_length : forall l j x, length (s48_upd l j x) = length l.
Proof. induction l as [|y l IH]; intros [|j] x; cbn [s48_upd length]; try reflexivity. f_equal. apply IH. Qed.
Lemma s48_nth_upd_same : forall l j x, (j < length l)%nat -> nth_error (s48_upd l j x) j = Some x.
Proof.
induction l as [|y l IH]; intros [|j] x H; cbn [s48_upd length nth_error] in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma s48_nth_upd_other : forall l j t x, j <> t -> nth_error (s48_upd l j x) t = nth_error l t.
Proof.
induction l as [|y l IH]; intros [|j] [|t] x H; cbn [s48_upd nth_error]; try reflexivity; try lia.
apply IH. lia.
Qed.
Lemma s48_nthd_upd_same : forall l j x d, (j < length l)%nat -> nth j (s48_upd l j x) d = x.
Proof.
induction l as [|y l IH]; intros [|j] x d H; cbn [s48_upd length nth] in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma s48_nthd_upd_other : forall l j t x d, j <> t -> nth t (s48_upd l j x) d = nth t l d.
Proof.
induction l as [|y l IH]; intros [|j] [|t] x d H; cbn [s48_upd nth]; try reflexivity; try lia.
apply IH. lia.
Qed.

(* ---- the words found so far (s40's aw_found, the plain proof's sw_found, lib/Prog/SlotWords.v) ---- *)
Lemma s48_found_upd : forall copy ws C wp i j b, aw_found copy ws C wp i -> (i <= j)%nat ->
  aw_found copy ws (s48_upd C j b) wp i.
Proof.
intros copy ws C wp i j b FD Hj k' p w Ep Ew. destruct (FD k' p w Ep Ew) as (P1 & P2 & P3).
split; [exact P1|]. split; [exact P2|]. intros t Ht. rewrite s48_nth_upd_other by lia. exact (P3 t Ht).
Qed.
Lemma s48_found_mono : forall copy ws C wp i i', aw_found copy ws C wp i -> (i <= i')%nat -> aw_found copy ws C wp i'.
Proof.
intros copy ws C wp i i' FD Hi k' p w Ep Ew. destruct (FD k' p w Ep Ew) as (P1 & P2 & P3).
split; [exact P1|]. split; [lia | exact P3].
Qed.
Lemma s48_found_snoc : forall copy ws C wp i i' p w,
  aw_found copy ws C wp i -> nth_error ws (length wp) = Some w -> copy <= p ->
  p + Z.of_nat (length w) + 1 <= copy + Z.of_nat i' -> (i <= i')%nat ->
  (forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (p - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t) ->
  aw_found copy ws C (wp ++ [p]) i'.
Proof.
intros copy ws C wp i i' p w FD Ew H1 H2 Hi HW k' p' w' Ep Ew'.
destruct (Nat.lt_ge_cases k' (length wp)) as [L|L].
- rewrite nth_error_app1 in Ep by exact L. destruct (FD k' p' w' Ep Ew') as (P1 & P2 & P3).
  split; [exact P1|]. split; [lia | exact P3].
- rewrite nth_error_app2 in Ep by exact L. destruct (k' - length wp)%nat as [|q] eqn:Eq.
  + cbn in Ep. injection Ep as <-. replace k' with (length wp) in Ew' by lia. rewrite Ew in Ew'. injection Ew' as <-.
    split; [exact H1|]. split; [exact H2 | exact HW].
  + cbn in Ep. destruct q; discriminate.
Qed.
Lemma s48_word_nth : forall (LN C : list byte) i0 c, (i0 + c <= length LN)%nat ->
  (forall j, (i0 <= j < i0 + c)%nat -> nth_error C j = nth_error LN j) ->
  nth_error C (i0 + c) = Some (Z_to_bv 8 0) ->
  forall t, (t <= length (firstn c (skipn i0 LN)))%nat ->
    nth_error C (i0 + t) = nth_error (firstn c (skipn i0 LN) ++ [Z_to_bv 8 0]) t.
Proof.
intros LN C i0 c Hc HL H0 t Ht.
assert (Lw : length (firstn c (skipn i0 LN)) = c) by (apply firstn_length_le; rewrite length_skipn; lia).
rewrite Lw in Ht. destruct (Nat.lt_ge_cases t c) as [T|T].
- rewrite nth_error_app1 by lia. rewrite SlotWords.sw_nth_firstn by exact T. rewrite SlotWords.sw_nth_skipn. apply HL. lia.
- replace t with c by lia. rewrite nth_error_app2 by lia. rewrite Lw, Nat.sub_diag. exact H0.
Qed.
Lemma s48_word_found : forall copy (LN : list byte) ws (C : list byte) wp i kw i0 c w,
  aw_found copy ws C wp i -> length wp = kw -> nth_error ws kw = Some w -> w = firstn c (skipn i0 LN) ->
  (i <= i0)%nat -> (i0 + c <= length LN)%nat ->
  (forall j, (i0 <= j < i0 + c)%nat -> nth_error C j = nth_error LN j) ->
  nth_error C (i0 + c) = Some (Z_to_bv 8 0) ->
  aw_found copy ws C (wp ++ [copy + Z.of_nat i0]) (i0 + c + 1).
Proof.
intros copy LN ws C wp i kw i0 c w FD Hwp Ew Ew2 Hi0 Hc HL H0.
assert (Lw : length w = c) by (rewrite Ew2; apply firstn_length_le; rewrite length_skipn; lia).
apply (s48_found_snoc copy ws C wp i (i0 + c + 1) (copy + Z.of_nat i0) w FD); [rewrite Hwp; exact Ew | lia | lia | lia |].
intros t Ht. replace (Z.to_nat (copy + Z.of_nat i0 - copy)) with i0 by lia. rewrite Ew2.
apply (s48_word_nth LN C i0 c Hc HL H0). rewrite <- Ew2. exact Ht.
Qed.

(* ---- lists ---- *)
Lemma s48_nodup_app_r : forall {A} (l r : list A), List.NoDup (l ++ r) -> List.NoDup r.
Proof. intros A l. induction l as [|y l IH]; intros r H; [exact H|]. cbn [app] in H. apply NoDup_cons_iff in H as [_ H]. exact (IH r H). Qed.
Lemma s48_nodup_app_disj : forall {A} (l r : list A) x, List.NoDup (l ++ r) -> In x r -> ~ In x l.
Proof.
intros A l. induction l as [|y l IH]; intros r x H Hr Hl; [destruct Hl|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hy Hd].
destruct Hl as [<- | Hl]; [apply Hy, in_or_app; right; exact Hr | exact (IH r x Hd Hr Hl)].
Qed.

(* ---- n-byte fields ---- *)
Lemma s48_le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma s48_aval1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. replace (a + Z.of_nat 0) with a by lia. rewrite H.
rewrite (s48_le_byte_1 v Hv). reflexivity.
Qed.
Lemma s48_rdword_kept : forall (rd rd' : reader) a v, (forall x, a <= x < a + 8 -> rd' x = rd x) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s48_aval_kept : forall (rd rd' : reader) a n v, (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) ->
  aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite HK by lia. exact (H k Hk). Qed.

(* ---- ~t, the UBSan pointer-overflow guard of t + c (0x8698c): bitwise not of a 64-bit word ---- *)
Lemma s48_lxor_ones_loc : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (Ho : 2 ^ 64 - 1 = Z.ones 64) by reflexivity. rewrite Ho.
assert (Hl : Z.land x (Z.lxor x (Z.ones 64)) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
  - rewrite (Z.ones_spec_high 64 n) by lia.
    replace (Z.testbit x n) with false; [reflexivity|].
    symmetry. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
pose proof (Z.add_nocarry_lxor x (Z.lxor x (Z.ones 64)) Hl) as Ha.
rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Ha. rewrite <- Ho in Ha |- *. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s48_val_of_aval : forall H (mem : word -> option byte) a n v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* the byte of the state's one region (its chunk at offset 0), read back *)
Lemma s48_chunk_byte : forall (W : world SEGS) E ss ms rg e v a,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some rg -> YP09.r_base rg = Some 33%nat ->
  In (YP09.mkChunk 0 (CVal 1 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E 33) = a ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  rdW W (ms_mem ms) a = Some v.
Proof.
intros W E ss ms rg e v a HS Hi Hb Hin Ha He Hv.
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) 0 rg 33 0 1 e a v HS Hi Hb Hin Ha) as Hm.
cbn [ms_mem restrict] in Hm.
assert (Hval : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (a + 0) (N.to_nat 1) v).
{ apply Hm; [exact He | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia]. }
specialize (Hval 0%nat ltac:(cbn; lia)). replace (a + 0 + Z.of_nat 0) with a in Hval by lia.
rewrite (YI04.le_byte_small v (N.to_nat 1) 0 ltac:(change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256; lia) ltac:(cbn; lia)) in Hval.
change (8 * Z.of_nat 0) with 0 in Hval. rewrite Z.shiftr_0_r in Hval.
unfold aview. rewrite Hval. cbn [option_map]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the copy and arr blocks of the message: live, copy made since the entry, the two apart *)
Lemma s48_blocks : forall cx q ly S (W : world SEGS) mem md text copy arr,
  AR SEGS B ly S W mem md -> aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) ->
  In (copy, q_L0 cx q + 1) (ablocks B ly S) /\ In (arr, SlotSpec.arr_size (q_L0 cx q)) (ablocks B ly S) /\
  ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx) /\
  zdisjoint (copy, req_size (q_L0 cx q + 1)) (arr, req_size (SlotSpec.arr_size (q_L0 cx q))).
Proof.
intros cx q ly S W mem md text copy arr HAR Hrec.
pose proof Hrec as (_ & _ & _ & _ & _ & HP). rewrite aw_blocks_eq in HP.
assert (Hc : In (copy, q_L0 cx q + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. right. left. reflexivity. }
assert (Ha : In (arr, SlotSpec.arr_size (q_L0 cx q)) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. right. right. left. reflexivity. }
split; [exact Hc|]. split; [exact Ha|]. split.
- pose proof (Permutation_NoDup HP (lt_ablocks_NoDup B LAWS ly S W mem md HAR)) as HND.
  apply s48_nodup_app_r in HND. apply (s48_nodup_app_disj _ _ _ HND). right. left. reflexivity.
- set (X := q_O1 q ++ x_bl0 B cx ++ [(text, q_L0 cx q + 1)]).
  assert (HP2 : Permutation (ablocks B ly S) ((copy, q_L0 cx q + 1) :: (arr, SlotSpec.arr_size (q_L0 cx q)) :: X)).
  { eapply Permutation_trans; [exact HP|]. apply Permutation_sym.
    replace (q_O1 q ++ x_bl0 B cx ++ [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))])
      with (X ++ (copy, q_L0 cx q + 1) :: (arr, SlotSpec.arr_size (q_L0 cx q)) :: []) by (subst X; rewrite <- !app_assoc; reflexivity).
    apply Permutation_cons_app. apply Permutation_cons_app. rewrite app_nil_r. apply Permutation_refl. }
  exact (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ X HAR HP2).
Qed.

(* the context of the segment carried to a later state of the same frame: B's words_of writes a0 .. a5, s7, s8 and
   the frame words 120 .. 147 only, so every other register of lt_body and lt_msg_regs is kept *)
Lemma s48_ctx_kept : forall cx q ly S (W : world SEGS) regs mem md k acc text copy arr regs' mem' md',
  aw_ctx B MT cx q ly S W regs mem md k acc ->
  aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  (forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W mem' a = rdW W mem a) ->
  (forall a, aw_area (q_O1 q) a -> rdW W mem' a = rdW W mem a) ->
  aw_ctx B MT cx q ly S W regs' mem' md' k acc /\ aw_rec B cx q ly S W mem' (aw_blocks cx q text copy arr).
Proof.
intros cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC Hrec HJ'
  E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E25 E26 E27 HKs HKa.
destruct HC as ((HB & (HFR & HSl & R8 & R9 & R18 & R25 & R26 & R27 & Hm32) & (Hr & R19 & R20 & R21 & R22 & Hst & Hh & Hhw)) & Hbud).
destruct HFR as (HJ & Hsp1 & Hgp & Htp & Hsaved).
assert (HS8 : forall a, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> forall x, a <= x < a + 8 -> rdW W mem' x = rdW W mem x).
{ intros a H1 H2 x Hx. apply HKs. lia. }
unfold x_sp1, x_sp0, LT_FRAME in HS8.
split; [split; [|exact Hbud] | exact (aw_rec_kept B cx q ly S W mem mem' _ Hrec HKa)].
split; [exact HB|]. split.
{ split.
  { split; [exact HJ'|]. split; [unfold spZ; rewrite E2; exact Hsp1|].
    split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
    intros i0 r Hi0. pose proof (nth_error_Some LT_SAVED i0) as HL. rewrite Hi0 in HL.
    assert (Hi13 : (i0 < 13)%nat) by (apply HL; discriminate).
    apply (s48_rdword_kept (rdW W mem) (rdW W mem')); [apply HS8; unfold x_sp0; lia | exact (Hsaved i0 r Hi0)]. }
  split.
  { intros o v Hov. apply (s48_rdword_kept (rdW W mem) (rdW W mem')); [|exact (HSl o v Hov)].
    assert (Ho : 0 <= o <= 104).
    { unfold LT_SLOTS in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [Hq | Hov]; [injection Hq as <- _; lia|]). destruct Hov. }
    apply HS8; unfold x_sp1, x_sp0, LT_FRAME; lia. }
  rewrite E8, E9, E18, E25, E26, E27.
  split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R25|].
  split; [exact R26|]. split; [exact R27 | exact Hm32]. }
unfold lt_msg_regs. rewrite E19, E20, E21, E22.
split; [exact Hr|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|].
split; [exact Hst|]. split; [exact Hh|].
apply (s48_rdword_kept (rdW W mem) (rdW W mem')); [|exact Hhw].
apply HS8; unfold x_sp1, x_sp0, LT_FRAME, LT_HOSTB; lia.
Qed.

(* the symbolic state at 0x8698c: every register its own atom, atom 33 the word's end copy + i + s + c (the alias
   of s7 + a0), atom 34 its byte; one region over that byte, writable (the NUL a separator gets), and a shadow
   entry over it (its load and store checks) *)
Definition S48x : sv := SOff 25 0.
Definition S48span : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition s48_al : list (sv * sv) := [ (SAlu ALU_ADD (SOff 23 0) (SOff 10 0), SOff 33 0) ].
Definition s48_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (25%nat, mkAF LT_SB LT_SB 0);
  (8%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0); (33%nat, mkAF 4096 0x7fffff800000 0); (34%nat, mkAF 0 255 0) ] [] s48_al.
Definition s48_rM : smem := [ YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition s48_SH : list shent := [ mkSHE 33 0 1 ].
Definition s48_extra (p b0 : Z) : list word := map (Z_to_bv 64) [0; p; b0].
Definition s48_E (regs : bvmap 5 word) (p b0 : Z) : env := Eimg (Ereg regs (s48_extra p b0)).

Lemma s48_env : forall regs p b0,
  (forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew (s48_E regs p b0) k = getr regs rr) /\
  ew (s48_E regs p b0) 33 = Z_to_bv 64 p /\ ew (s48_E regs p b0) 34 = Z_to_bv 64 b0 /\
  img_env VAL A_LIM (s48_E regs p b0).
Proof.
intros regs p b0. unfold s48_E.
split; [|split; [|split]].
- intros k rr Hk. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2).
- apply Eimg_env.
Qed.

Lemma s48_facts_ok : forall regs p b0 cur c0,
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 -> getr regs 25 = w64 LT_SB -> getr regs 8 = w64 (-1) ->
  getr regs 23 = w64 cur -> getr regs 10 = w64 c0 -> 0 <= cur < 2 ^ 63 -> 0 <= c0 < 2 ^ 63 -> p = cur + c0 ->
  4096 <= p <= 0x7fffff800000 -> 0 <= b0 <= 255 ->
  facts_ok (s48_E regs p b0) s48_facts.
Proof.
intros regs p b0 cur c0 Hal Hsp R25 R8 R23 R10 Hcur Hc0 Hp Hpr Hb0.
destruct (s48_env regs p b0) as (EEo & E33 & E34 & _).
set (E := s48_E regs p b0) in *.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E8 : bv_unsigned (ew E 8) = 2 ^ 64 - 1) by (rewrite (EEo 8%nat 8%bv eq_refl), R8; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 cur) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E10 : ew E 10 = Z_to_bv 64 c0) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
split; [|split; [exact I | split; [|exact I]]].
- cbn [s48_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E25, E8, E33, E34, !unsigned_lit_small by (unfold LT_SB; lia).
  unfold LT_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 23 cur E23) by lia. rewrite (U_atom E 10 c0 E10) by lia. rewrite (U_atom E 33 p E33) by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* the one write of the segment (the NUL at the word's end) is a byte of the copy block, made since the entry *)
Lemma s48_awr : forall E cs STK sp0 FP bl0 blc fr0 ly own p copy n,
  bv_unsigned (ew E 33) = p -> In (copy, n) blc -> ~ In (copy, n) bl0 -> copy <= p -> p + 1 <= copy + req_size n ->
  awr_ok SEGS B E [YP09.mkRegion (Some 33%nat) 0 1 0 1 cs] STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E cs STK sp0 FP bl0 blc fr0 ly own p copy n Hp Hin Hn H1 H2 a (r & Hr & Ha).
destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Hp in Ha.
right. right. left. exists copy, n. split; [exact Hin|]. split; [exact Hn | lia].
Qed.

(* ---- the segment: from 0x8698c to the head 0x868e4 (AW_S) or to LO_K 0x86a04 (AW_E) ---- *)
Theorem aw_seg_S2 : forall m, AW_E_stmt B MT m ->
  forall nm, (forall nm', (nm' < nm)%nat -> AW_S_stmt B MT m nm') -> AW_S2_stmt B MT m nm.
Proof.
intros m HE nm IH cx q ly S W regs mem md k acc text copy arr i s kw C wp
  Hm HFP0 HC Hrec Hws R23 R10 Hwn Hnm Hkw Hwp Hkws HWA HCat HCl HCF HFD Hs His HARR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HC as ((HB & (HFR & HSl & R8 & R9 & R18 & R25 & R26 & R27 & Hm32) &
  (Hr & R19 & R20 & R21 & R22 & Hst & Hhr & Hhw)) & Hbud).
pose proof HFR as (HJ & Hsp1 & Hgp & Htp & Hsaved).
pose proof (proj1 HJ) as HAR.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : LTOI_STK = 32768) by reflexivity. rewrite WS in Hstk0, Hslo, Hbot.
assert (Hsp : spZ regs = spZ (x_regs cx) - 256) by (rewrite Hsp1; reflexivity).
assert (Hsp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
assert (Hsp1' : x_sp1 cx = spZ (x_regs cx) - 256) by reflexivity.
(* the blocks *)
destruct (s48_blocks cx q ly S W mem md text copy arr HAR Hrec) as (Hcin & Hain & Hcnew & Hdisj).
destruct (al_blocks _ _ LAWS ly S W mem md copy (q_L0 cx q + 1) HAR Hcin) as (Hc16 & Hc4096 & Hcceil & Hcapp & Hcpres & _ & Hcmax).
destruct (al_blocks _ _ LAWS ly S W mem md arr _ HAR Hain) as (Ha16 & Ha4096 & Haceil & Haapp & Hapres & _ & Hamax).
(* the line *)
assert (NZL : forall b, In b (q_LN cx q) -> bv_unsigned b <> 0) by exact (SlotWords.sw_line_nz (q_D cx q)).
assert (Hlnl : (length (q_LN cx q) <= Z.to_nat (q_L0 cx q))%nat).
{ rewrite q_L0_U, Nat2Z.id. exact (SlotWords.sw_line_le (q_D cx q)). }
assert (HL0 : 0 <= q_L0 cx q) by (rewrite q_L0_U; lia).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (SlotSpec.arr_size (q_L0 cx q)) ltac:(unfold SlotSpec.arr_size; pose proof (Z.div_pos (q_L0 cx q) 2); lia)) as [Hra1 Hra2].
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
remember (aw_cspn (skipn (i + s) (q_LN cx q))) as c eqn:Ec.
assert (E2s : skipn s (skipn i (q_LN cx q)) = skipn (i + s) (q_LN cx q)) by (rewrite skipn_skipn; f_equal; lia).
pose proof (SlotWords.sw_cspn_le SlotWords.SEPS (skipn (i + s) (q_LN cx q))) as Hcl.
unfold aw_cspn in Ec. rewrite <- Ec, length_skipn in Hcl.
unfold aw_spn in Hs.
destruct (SlotWords.sw_round (skipn i (q_LN cx q)) (skipn s (skipn i (q_LN cx q))) s c Hs eq_refl
  ltac:(rewrite E2s; exact Ec) ltac:(rewrite length_skipn; lia)) as (Hc1 & Hfull & Hpart).
rewrite E2s in Hfull, Hpart. rewrite length_skipn in Hfull, Hpart.
(* the word's end e = i + s + c, its byte in the copy *)
assert (Hel : (i + s + c <= length (q_LN cx q))%nat) by lia.
destruct (SlotWords.sw_nth_z (q_LN cx q) (i + s + c) NZL Hel) as (bz & Ebz & Hbz).
assert (HCe : nth_error C (i + s + c) = Some bz) by (rewrite HCF by lia; exact Ebz).
assert (HCe' : nth (i + s + c) C (Z_to_bv 8 0) = bz) by (apply nth_error_nth; exact HCe).
assert (HCl' : (length C = Z.to_nat (q_L0 cx q) + 1)%nat) by (rewrite HCl; lia).
assert (Rb0 : rdW W mem (copy + Z.of_nat (i + s + c)) = Some (bv_unsigned bz)).
{ rewrite (HCat (i + s + c)%nat) by lia. rewrite HCe'. reflexivity. }
pose proof (bv_unsigned_in_range 8 bz) as Rbz. change (bv_modulus 8) with 256 in Rbz.
(* sizes *)
unfold MALLOC_MAX in Hcmax, Hamax.
assert (HLb : (i + s + c <= Z.to_nat (q_L0 cx q))%nat) by lia.
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite Hsp; lia).
assert (Hsp16 : spZ regs mod 16 = 0).
{ rewrite Hsp. replace (spZ (x_regs cx) - 256) with (spZ (x_regs cx) + (-16) * 16) by ring.
  rewrite Z_mod_plus_full. exact Hal16. }
assert (Hpb : copy + Z.of_nat (i + s + c) < spZ regs) by lia.
(* the stack and the recorder's area are not the word's end *)
assert (HnotS : forall a, x_sp1 cx <= a -> a <> copy + Z.of_nat (i + s + c)).
{ intros a Ha. rewrite Hsp1' in Ha. lia. }
assert (HnotA : forall a, aw_area (q_O1 q) a -> a <> copy + Z.of_nat (i + s + c)).
{ intros a Ha ->. apply (aw_area_words B LAWS cx q ly S W mem md text copy arr copy (q_L0 cx q + 1)
    (copy + Z.of_nat (i + s + c)) HAR Hrec); [rewrite aw_blocks_eq; right; left; reflexivity | lia | exact Ha]. }
assert (HbndA : forall a, aw_area (q_O1 q) a -> 0 <= a < 2 ^ 64).
{ intros a Ha. pose proof Hrec as (_ & _ & _ & _ & _ & HP).
  destruct Ha as [Ha | [Ha | [Ha | (r0 & Hr0 & Hlo & Hhi)]]]; [unfold A_G_REC, REC_SIZE in Ha; lia
    | unfold A_REC_SPILL, SC_SIZE in Ha; lia | unfold A_G_QUITTING in Ha; lia |].
  unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([b0' n0'] & Hbn & Hin). subst r0. cbn [fst snd] in Hlo, Hhi.
  assert (Hin2 : In (b0', n0') (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS ly S W mem md b0' n0' HAR Hin2) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hnmax).
  pose proof (req_size_pos n0' ltac:(lia)). lia. }
(* the seed *)
destruct (s48_env regs (copy + Z.of_nat (i + s + c)) (bv_unsigned bz)) as (EEo & E33 & E34 & HEI).
assert (HFO : facts_ok (s48_E regs (copy + Z.of_nat (i + s + c)) (bv_unsigned bz)) s48_facts).
{ apply (s48_facts_ok regs _ _ (copy + Z.of_nat (i + s)) (Z.of_nat c) Hsp16 Hspr R25 R8 R23 R10); lia. }
remember (s48_E regs (copy + Z.of_nat (i + s + c)) (bv_unsigned bz)) as E eqn:HE0.
assert (U25 : U E S48x = SHADOW_OFF).
{ unfold S48x. rewrite (U_atom E 25 LT_SB) by first [rewrite (EEo 25%nat 25%bv eq_refl); exact R25 | unfold LT_SB; lia].
  reflexivity. }
assert (HS : st_ok_pi SEGS VAL E (mkSS AW_S2 sr_atoms s48_rM None s48_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_S2)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold s48_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s48_rM. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E33, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS);
      exact (proj1 (Hcpres (copy + Z.of_nat (i + s + c) + o) ltac:(lia)))|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (copy + Z.of_nat (i + s + c)) 0 1 (SOff 34 0) (bv_unsigned bz));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply s48_val_of_aval. apply s48_aval1; [exact Rb0 | lia].
  + apply pairwise_disjoint_of_extents. unfold s48_rM. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  + exact HFO. }
assert (SHOK : sh_ok SEGS S48x s48_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s48_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E S48x 33 (copy + Z.of_nat (i + s + c)) 1 (copy + Z.of_nat (i + s + c)) 0 1).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md copy (q_L0 cx q + 1) (copy + Z.of_nat (i + s + c)) 1
      HAR Hcin ltac:(lia) ltac:(lia)).
  - exact U25.
  - exact (U_atom E 33 _ E33 ltac:(lia)).
  - lia.
  - lia.
  - intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold in_app, kLowShadowBeg, SHADOW_OFF in *. lia. }
clear HFO.
assert (HAWR : forall E1 cs blc, bv_unsigned (ew E1 33) = copy + Z.of_nat (i + s + c) -> In (copy, q_L0 cx q + 1) blc ->
  awr_ok SEGS B E1 [YP09.mkRegion (Some 33%nat) 0 1 0 1 cs] LTOI_STK (x_sp0 cx) cmd_PG (ablocks B (x_ly cx) (x_S cx))
    blc (frames (x_S cx)) ly []).
{ intros E1 cs blc H1 H2. apply (s48_awr E1 cs _ _ _ _ _ _ _ _ _ copy (q_L0 cx q + 1) H1 H2 Hcnew); lia. }
(* 0x8698c .. 0x86990: a1 := ~t; bltu, the UBSan guard of t + c *)
paj_run_tok RUN HS HJ SHOK S48span.
{ apply HAWR; [cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia | exact Hcin]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> a <> copy + Z.of_nat (i + s + c) -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hne; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => a = copy + Z.of_nat (i + s + c)) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
        rewrite E33, unsigned_lit_small in Hrr by lia; lia|]); destruct Hin
    | exact Ha | exact Hne ]) end.
clear HF HFr HG. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK S48span.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  lazymatch type of Hc with context [U ?E1 (SOff 23 0)] =>
    rewrite (U_atom E1 23 (copy + Z.of_nat (i + s))) in Hc
      by first [cbn [ew ewset Nat.eqb]; rewrite (EEo 23%nat 23%bv eq_refl); exact R23 | lia];
    rewrite (U_atom E1 10 (Z.of_nat c)) in Hc
      by first [cbn [ew ewset Nat.eqb]; rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | lia] end.
  rewrite U_SLit in Hc. replace (zcanon (-1)) with (2 ^ 64 - 1) in Hc by reflexivity.
  rewrite s48_lxor_ones_loc in Hc by lia. unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x86994 .. 0x869ac: a0 := t + c, the word's end; its load check (the shadow entry); its byte; beqz *)
paj_run_tok RUN HS HJ SHOK S48span.
{ apply HAWR; [cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia | exact Hcin]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> copy + Z.of_nat (i + s + c) -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hne; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => a = copy + Z.of_nat (i + s + c)) Hfr);
    [ exact (KEEP0 a Ha Hne)
    | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
        rewrite E33, unsigned_lit_small in Hrr by lia; lia|]); destruct Hin
    | exact Ha | exact Hne ]) end.
clear HF HFr HG KEEP0. rename ms into ms2. pose proof (proj1 HJ) as HAR2.
psrr_branch_tok RUN BR HS SHOK S48span.
- (* the byte is the line's NUL: the word ends the line; kw + 1 words, LO_K *)
  assert (HeA : (i + s + c)%nat = length (q_LN cx q)).
  { rewrite branch_eq_U in Hc.
    lazymatch type of Hc with context [U ?E1 (SOff 34 0)] =>
      rewrite (U_atom E1 34 (bv_unsigned bz)) in Hc by first [cbn [ew ewset Nat.eqb]; exact E34 | lia] end.
    rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. apply Hbz. exact Hc. }
  assert (Hb0z : bv_unsigned bz = 0) by (apply Hbz; exact HeA).
  assert (Hcfull : c = (length (q_LN cx q) - (i + s))%nat) by lia.
  pose proof (Hfull Hcfull) as W1. rewrite HWA in W1.
  destruct (SlotWords.sw_skipn_cons _ _ _ _ W1) as [Ew WS1].
  assert (Hlws : length (q_ws cx q) = Datatypes.S kw).
  { pose proof (nth_error_Some (q_ws cx q) kw) as NS. rewrite Ew in NS.
    assert (KW : (kw < length (q_ws cx q))%nat) by (apply NS; discriminate).
    apply (f_equal (@length _)) in WS1. rewrite length_skipn in WS1. cbn [length] in WS1. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK S48span LO_K.
  { apply HAWR; [cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia | exact Hcin]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> copy + Z.of_nat (i + s + c) -> rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha Hne; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => a = copy + Z.of_nat (i + s + c)) Hfr);
      [ exact (KEEP1 a Ha Hne)
      | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
          rewrite E33, unsigned_lit_small in Hrr by lia; lia|]); destruct Hin
      | exact Ha | exact Hne ]) end.
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
    let rgl := eval vm_compute in (nth_error (ss_mem ss2) 0) in
    lazymatch rgl with Some ?rg =>
      assert (Rst : rdW W (ms_mem ms) (copy + Z.of_nat (i + s + c)) = Some (bv_unsigned bz))
        by (apply (s48_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SOff 34 0) (bv_unsigned bz)); [exact HS | reflexivity | reflexivity
          | cbn [In YP09.r_chunks]; left; reflexivity
          | cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia])
    end end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  assert (HKs : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. apply KEEP; [rewrite Hsp1', Hsp0 in *; lia | apply HnotS; lia]. }
  assert (HKa : forall a, aw_area (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. exact (KEEP a (HbndA a Ha) (HnotA a Ha)). }
  destruct (s48_ctx_kept cx q ly S W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv HC Hrec HJ
    ltac:(rewrite P2; apply EEo; reflexivity) ltac:(rewrite P3; apply EEo; reflexivity)
    ltac:(rewrite P4; apply EEo; reflexivity) ltac:(rewrite P8; apply EEo; reflexivity)
    ltac:(rewrite P9; apply EEo; reflexivity) ltac:(rewrite P18; apply EEo; reflexivity)
    ltac:(rewrite P19; apply EEo; reflexivity) ltac:(rewrite P20; apply EEo; reflexivity)
    ltac:(rewrite P21; apply EEo; reflexivity) ltac:(rewrite P22; apply EEo; reflexivity)
    ltac:(rewrite P25; apply EEo; reflexivity) ltac:(rewrite P26; apply EEo; reflexivity)
    ltac:(rewrite P27; apply EEo; reflexivity) HKs HKa) as [HC' Hrec'].
  assert (HS8 : forall a v, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> rdword (rdW W mem) a = Some v ->
    rdword (rdW W (ms_mem ms)) a = Some v).
  { intros a v H1 H2. apply s48_rdword_kept. intros x Hx. apply HKs. lia. }
  assert (Hws' : aw_wslots cx (rdW W (ms_mem ms)) text copy arr).
  { destruct Hws as (W1' & W2' & W3').
    split; [|split]; (apply HS8; [unfold x_sp1, LT_FRAME, LT_W; lia | unfold x_sp1, x_sp0, LT_FRAME, LT_W; lia | assumption]). }
  assert (Hwn' : aw_wn cx (rdW W (ms_mem ms)) (Z.of_nat (length (q_ws cx q)))).
  { rewrite Hlws. replace (Z.of_nat (Datatypes.S kw)) with (Z.of_nat (kw + 1)) by lia. unfold aw_wn in *.
    apply (s48_aval_kept (rdW W mem)); [|exact Hwn]. intros x Hx. apply HKs. unfold x_sp1, x_sp0, LT_FRAME, LT_W in *. lia. }
  assert (HCat' : abytes_atR (rdW W (ms_mem ms)) copy C).
  { intros t Ht. destruct (Nat.eq_dec t (i + s + c)) as [-> | Hne].
    - rewrite Rst, HCe'. reflexivity.
    - rewrite KEEP by lia. exact (HCat t Ht). }
  assert (HARR' : aw_arr (rdW W (ms_mem ms)) arr (wp ++ [copy + Z.of_nat (i + s)])).
  { intros t pt Ht. pose proof (HARR t pt Ht) as Hw. pose proof (nth_error_Some (wp ++ [copy + Z.of_nat (i + s)]) t) as NS.
    rewrite Ht, length_app in NS. cbn [length] in NS. assert (Tl : (t < kw + 1)%nat) by (rewrite <- Hwp; apply NS; discriminate).
    apply (s48_rdword_kept (rdW W mem)); [|exact Hw]. intros x Hx.
    assert (HAS : SlotSpec.arr_size (q_L0 cx q) = 8 * (q_L0 cx q / 2) + 16) by reflexivity.
    pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)).
    apply KEEP; lia. }
  assert (HFD' : aw_found copy (q_ws cx q) C (wp ++ [copy + Z.of_nat (i + s)]) (Z.to_nat (q_L0 cx q + 1))).
  { apply (s48_found_mono copy (q_ws cx q) C _ (i + s + c + 1)); [|lia].
    apply (s48_word_found copy (q_LN cx q) (q_ws cx q) C wp i kw (i + s) c (skipn (i + s) (q_LN cx q)) HFD Hwp Ew).
    - symmetry. apply firstn_all2. rewrite length_skipn. lia.
    - lia.
    - lia.
    - intros j Hj. rewrite HCF by lia. apply nth_error_app1. lia.
    - rewrite HCF by lia. rewrite HeA, nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (Hlen' : length (wp ++ [copy + Z.of_nat (i + s)]) = length (q_ws cx q))
    by (rewrite length_app, Hwp, Hlws; cbn [length]; lia).
  exact (HE cx q ly S W (ms_regs ms) (ms_mem ms) mdv k acc text copy arr C (wp ++ [copy + Z.of_nat (i + s)])
    Hm HFP0 HC' Hrec' Hws' Hwn' Hlen' HCat' HCl HARR' HFD').
- (* a separator ends the word: its NUL at the word's end, t := the next byte, back to the head with
     i + s + c + 1 and kw + 1 *)
  assert (Hlt : (i + s + c < length (q_LN cx q))%nat).
  { rewrite branch_eq_U in Hc.
    lazymatch type of Hc with context [U ?E1 (SOff 34 0)] =>
      rewrite (U_atom E1 34 (bv_unsigned bz)) in Hc by first [cbn [ew ewset Nat.eqb]; exact E34 | lia] end.
    rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert ((i + s + c)%nat <> length (q_LN cx q)) by (intros He; apply Hc, Hbz, He). lia. }
  destruct (Hpart ltac:(lia)) as (xsep & Ex & Hxs & W2). rewrite HWA in W2.
  destruct (SlotWords.sw_skipn_cons _ _ _ _ W2) as [Ew WSk].
  assert (KW : (kw < length (q_ws cx q))%nat).
  { pose proof (nth_error_Some (q_ws cx q) kw) as NS. rewrite Ew in NS. apply NS. discriminate. }
  assert (WA' : Verbs.words_acc [] (skipn (i + s + c + 1) (q_LN cx q)) = skipn (kw + 1) (q_ws cx q)).
  { replace (kw + 1)%nat with (Datatypes.S kw) by lia. rewrite WSk, skipn_skipn. f_equal. f_equal. lia. }
  (* the copy after the NUL, and the words found *)
  set (C' := s48_upd C (i + s + c) (Z_to_bv 8 0)).
  assert (HCl2 : length C' = Z.to_nat (q_L0 cx q + 1)) by (unfold C'; rewrite s48_upd_length; exact HCl).
  assert (HFD2 : aw_found copy (q_ws cx q) C' (wp ++ [copy + Z.of_nat (i + s)]) (i + s + c + 1)).
  { apply (s48_word_found copy (q_LN cx q) (q_ws cx q) C' wp i kw (i + s) c (firstn c (skipn (i + s) (q_LN cx q)))
      (s48_found_upd copy (q_ws cx q) C wp i (i + s + c) (Z_to_bv 8 0) HFD ltac:(lia)) Hwp Ew eq_refl).
    - lia.
    - lia.
    - intros j Hj. unfold C'. rewrite s48_nth_upd_other by lia. rewrite HCF by lia. apply nth_error_app1. lia.
    - unfold C'. apply s48_nth_upd_same. lia. }
  (* 0x869b0 .. 0x869d8: the UBSan guard t + 1 (a0 = -1), the store check (the shadow entry), the NUL, s7 := a0 + 1,
     its load check (fast path or the partial granule's slow test); back to the head *)
  paj_run_to_tok RUNTO HS HJ SHOK S48span AW_S.
  { unfold S48x. rewrite (U_atom _ 25 LT_SB) by first [cbn [ew ewset Nat.eqb]; rewrite (EEo 25%nat 25%bv eq_refl); exact R25 | unfold LT_SB; lia].
    rewrite (U_atom_off _ 33 (copy + Z.of_nat (i + s + c)) 1) by first [cbn [ew ewset Nat.eqb]; exact E33 | lia].
    exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms2) mdv2 copy (q_L0 cx q + 1)
      (copy + Z.of_nat (i + s + c) + 1) 1 HAR2 Hcin ltac:(lia) ltac:(lia)). }
  { apply HAWR; [cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia | exact Hcin]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> copy + Z.of_nat (i + s + c) -> rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha Hne; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => a = copy + Z.of_nat (i + s + c)) Hfr);
      [ exact (KEEP1 a Ha Hne)
      | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
          rewrite E33, unsigned_lit_small in Hrr by lia; lia|]); destruct Hin
      | exact Ha | exact Hne ]) end.
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
    let rgl := eval vm_compute in (nth_error (ss_mem ss2) 0) in
    lazymatch rgl with Some ?rg =>
      assert (Rst : rdW W (ms_mem ms) (copy + Z.of_nat (i + s + c)) = Some 0)
        by (apply (s48_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SLit 0) 0); [exact HS | reflexivity | reflexivity
          | cbn [In YP09.r_chunks]; left; reflexivity
          | cbn [ew ewset Nat.eqb]; rewrite E33; apply unsigned_lit_small; lia
          | reflexivity | lia])
    end end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27. prreg HS (23%bv : bv 5) P23.
  assert (HKs : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. apply KEEP; [rewrite Hsp1', Hsp0 in *; lia | apply HnotS; lia]. }
  assert (HKa : forall a, aw_area (q_O1 q) a -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. exact (KEEP a (HbndA a Ha) (HnotA a Ha)). }
  destruct (s48_ctx_kept cx q ly S W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv HC Hrec HJ
    ltac:(rewrite P2; apply EEo; reflexivity) ltac:(rewrite P3; apply EEo; reflexivity)
    ltac:(rewrite P4; apply EEo; reflexivity) ltac:(rewrite P8; apply EEo; reflexivity)
    ltac:(rewrite P9; apply EEo; reflexivity) ltac:(rewrite P18; apply EEo; reflexivity)
    ltac:(rewrite P19; apply EEo; reflexivity) ltac:(rewrite P20; apply EEo; reflexivity)
    ltac:(rewrite P21; apply EEo; reflexivity) ltac:(rewrite P22; apply EEo; reflexivity)
    ltac:(rewrite P25; apply EEo; reflexivity) ltac:(rewrite P26; apply EEo; reflexivity)
    ltac:(rewrite P27; apply EEo; reflexivity) HKs HKa) as [HC' Hrec'].
  assert (HS8 : forall a v, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> rdword (rdW W mem) a = Some v ->
    rdword (rdW W (ms_mem ms)) a = Some v).
  { intros a v H1 H2. apply s48_rdword_kept. intros x Hx. apply HKs. lia. }
  assert (Hws' : aw_wslots cx (rdW W (ms_mem ms)) text copy arr).
  { destruct Hws as (W1' & W2' & W3').
    split; [|split]; (apply HS8; [unfold x_sp1, LT_FRAME, LT_W; lia | unfold x_sp1, x_sp0, LT_FRAME, LT_W; lia | assumption]). }
  assert (Hwn' : aw_wn cx (rdW W (ms_mem ms)) (Z.of_nat (kw + 1))).
  { unfold aw_wn in *. apply (s48_aval_kept (rdW W mem)); [|exact Hwn].
    intros x Hx. apply HKs. unfold x_sp1, x_sp0, LT_FRAME, LT_W in *. lia. }
  assert (HCat' : abytes_atR (rdW W (ms_mem ms)) copy C').
  { intros t Ht. unfold C' in Ht |- *. rewrite s48_upd_length in Ht.
    destruct (Nat.eq_dec t (i + s + c)) as [-> | Hne].
    - rewrite s48_nthd_upd_same by lia. rewrite Rst. reflexivity.
    - rewrite s48_nthd_upd_other by lia. rewrite KEEP by lia. exact (HCat t Ht). }
  assert (HARR' : aw_arr (rdW W (ms_mem ms)) arr (wp ++ [copy + Z.of_nat (i + s)])).
  { intros t pt Ht. pose proof (HARR t pt Ht) as Hw. pose proof (nth_error_Some (wp ++ [copy + Z.of_nat (i + s)]) t) as NS.
    rewrite Ht, length_app in NS. cbn [length] in NS. assert (Tl : (t < kw + 1)%nat) by (rewrite <- Hwp; apply NS; discriminate).
    apply (s48_rdword_kept (rdW W mem)); [|exact Hw]. intros x Hx.
    assert (HAS : SlotSpec.arr_size (q_L0 cx q) = 8 * (q_L0 cx q / 2) + 16) by reflexivity.
    pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)).
    apply KEEP; lia. }
  assert (HCF' : forall j, (i + s + c + 1 <= j <= length (q_LN cx q))%nat ->
    nth_error C' j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j).
  { intros j Hj. unfold C'. rewrite s48_nth_upd_other by lia. apply HCF. lia. }
  assert (Hlen' : length (wp ++ [copy + Z.of_nat (i + s)]) = (kw + 1)%nat) by (rewrite length_app, Hwp; cbn [length]; lia).
  assert (P23' : getr (ms_regs ms) 23 = w64 (copy + Z.of_nat (i + s + c + 1))).
  { rewrite P23, E33. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  exact (IH (length (q_LN cx q) - (i + s + c + 1))%nat ltac:(lia) cx q ly S W (ms_regs ms) (ms_mem ms) mdv k acc
    text copy arr (i + s + c + 1)%nat (kw + 1)%nat C' (wp ++ [copy + Z.of_nat (i + s)])
    Hm HFP0 HC' Hrec' Hws' P23' Hwn' eq_refl ltac:(lia) ltac:(lia) Hlen' ltac:(lia) WA' HCat' HCl2 HCF' HARR' HFD2).
Qed.

End e.
End f.
End d.
