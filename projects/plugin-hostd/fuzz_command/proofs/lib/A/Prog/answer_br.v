(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the BODY segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a61c ..
   0x8a734 / 0x8a670): the refusal branch, the snprintf of "resp %d", the mix_call of the changes and the store of
   g_rec.state, up to the cut points JOIN and HEAD of lib/A/Prog/answer_s1.v. *)
(* Modified by Theorem Labs, 2026-10: statement passes 4, 4b and 5 (lib/A/Prog/answer_c.v): the snprintf call goes
   through the shared contract (RtPFCmd.v asnprintf_sh) with the kit's printf step (PaFx.v aj_art_own_atF,
   srr_art_postF_of_pf); the refusal arm reaches JOIN at the FP state the wrapper returns, so BODY proves the
   statement's FP-existential post and takes JOIN at every FP state. *)
(* Modified by Theorem Labs, 2026-10: the snprintf buffer's fake frame lies above the image by the kit's
   RtPFDog.v pa_frame_above_img (the local copy br_frame_above_img is gone); the Lia settings and the Zify division
   flag are Local to this file. *)
(* Modified by Theorem Labs, 2026-10: the snprintf contract in omx-clap-core/fuzz_manifest's published form asks for
   8 bytes of band room past the destination (`amem_range d (sn_len (n - 1) T + 8)`); buf's class-7 fake frame gives
   them by the kit's PaLibH.v amem_range_sub_app. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh PaArt CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import mix_call_c hand_back_c answer_c answer_s0 answer_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFSx RtPFCmd RtPFDog.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
(* lia without the Euclidean-division equations: the flag value these proofs were checked with, which PaDenot.v
   gave them until an earlier commit made its redefinition Local *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* ---- generic helpers over the reader ---- *)
Lemma aval_mem_agree : forall (rd rd' : reader) a n v,
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) ->
aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK (Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma abytes_atR_agree : forall (rd rd' : reader) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> rd' (a + k) = rd (a + k)) ->
abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite (HK (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma astr_atR_agree : forall (rd rd' : reader) p s,
(forall k, 0 <= k <= Z.of_nat (length s) -> rd' (p + k) = rd (p + k)) ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s HK [H1 H2]. split; [|exact H2]. apply (abytes_atR_agree rd rd'); [|exact H1].
intros k Hk. rewrite length_app in Hk. cbn [length] in Hk. apply HK. lia.
Qed.

Lemma aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* a chunk whose value is any 64-bit atom, read at the width of w bytes *)
Lemma chunk_ok_any : forall segs E mem base off (n : N) (e : sv),
(Z.of_N n <= 8) -> val_mem segs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)) ->
YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)).
Proof.
intros segs E mem base off n e Hn Hv i Hi.
cbn [YP09.c_off YP09.c_val] in *. unfold YP09.c_len in Hi. cbn [YP09.c_val YP09.cv_len] in Hi.
assert (HN : Z.of_nat (N.to_nat n) = Z.of_N n)
  by (destruct n as [|p]; [reflexivity | cbn [N.to_nat Z.of_N]; apply positive_nat_Z]).
assert (E2 : Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
assert (Hlt : (Z.to_nat i < N.to_nat n)%nat) by (apply (proj2 (Nat2Z.inj_lt _ _)); rewrite HN, E2; lia).
pose proof (Hv (Z.to_nat i) Hlt) as Hb. rewrite E2 in Hb.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|]. rewrite Hb. f_equal.
pose proof (low_byte_mod (bv_unsigned (sv_denot E e)) (N.to_nat n) (Z.to_nat i)
  ltac:(pose proof (bv_unsigned_in_range 64 (sv_denot E e)); lia) Hlt) as L.
unfold byte_of_word, YO0f.le_byte.
rewrite HN, E2 in L. rewrite HN, E2.
rewrite Z.mod_mod by (pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_N n) ltac:(lia) ltac:(lia)); lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia.
apply (f_equal bv_unsigned) in L. rewrite !Z_to_bv_unsigned in L. unfold bv_wrap in L.
change (bv_modulus 8) with 256 in L. exact L.
Qed.

Lemma br_in_filter : forall (old : Z) (O : list (Z * Z)) x,
In x (filter (fun pn => fst pn =? old) O) -> In x O /\ fst x = old.
Proof.
intros old O x H. apply (proj2 (list_elem_of_In _ _)) in H. apply list_basics.list.list_elem_of_filter in H as [Hp H].
apply list_elem_of_In in H. split; [exact H|]. apply Is_true_eq_true in Hp. apply Z.eqb_eq. exact Hp.
Qed.

(* ---- the addresses the recorder's representation reads ---- *)
Definition rep_addr (O : list (Z * Z)) (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists p n, In (p, n) O /\ p <= a < p + n).

Lemma acall_at_agree : forall bl (rd rd' : reader) a c P,
(forall k, 0 <= k < CALL_SIZE -> rd' (a + k) = rd (a + k)) ->
(forall pn k, In pn P -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl rd a c P -> acall_at bl rd' a c P.
Proof.
intros bl rd rd' a c P HA HB (H1 & H2 & H3 & H4 & H5 & H6 & H7).
assert (HA' : forall d k, 0 <= d -> 0 <= k -> d + k < CALL_SIZE -> rd' (a + d + k) = rd (a + d + k)).
{ intros d k Hd Hk Hdk. replace (a + d + k) with (a + (d + k)) by lia. apply HA. lia. }
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HA'; unfold CALL_OFF_FN, CALL_SIZE in *; lia | exact H4]|].
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HA'; unfold CALL_OFF_NARGS, CALL_SIZE in *; lia | exact H5]|].
split; [exact H6|].
intros k s pn Hk Hp. destruct (H7 k s pn Hk Hp) as (G1 & G2 & G3 & G4 & G5).
assert (Hin : In pn P) by (eapply nth_error_In; exact Hp).
assert (Hk6 : (k < length (snd c))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
assert (Hkl : (k < length P)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hp; discriminate).
split; [apply (aval_mem_agree rd rd');
  [intros j Hj; replace (a + CALL_OFF_ARGS + 8 * Z.of_nat k + j) with (a + (CALL_OFF_ARGS + 8 * Z.of_nat k) + j) by lia;
   apply HA'; unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact G1]|].
split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
apply (astr_atR_agree rd rd'); [|exact G5]. intros j Hj. apply HB; [exact Hin | lia].
Qed.

Lemma aanswer_at_agree : forall bl (rd rd' : reader) gr t q,
(forall k, 0 <= k < 8 -> rd' (gr + OFF_ANSWER + k) = rd (gr + OFF_ANSWER + k)) ->
(forall pn k, q = Some pn -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
aanswer_at bl rd gr t q -> aanswer_at bl rd' gr t q.
Proof.
intros bl rd rd' gr t q HA HB H. destruct t as [x|]; destruct q as [pn|]; try exact H.
- destruct H as (G1 & G2 & G3 & G4 & G5 & G6).
  split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
  apply (astr_atR_agree rd rd'); [|exact G5]. intros j Hj. apply (HB pn j eq_refl). lia.
- apply (aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact H].
Qed.

Lemma areply_at_agree : forall bl (rd rd' : reader) gr y q,
(forall k, 0 <= k < 16 -> rd' (gr + OFF_REPLY + k) = rd (gr + OFF_REPLY + k)) ->
(forall pn k, q = Some pn -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
areply_at bl rd gr y q -> areply_at bl rd' gr y q.
Proof.
intros bl rd rd' gr y q HA HB H.
assert (HS : forall k, 0 <= k < 8 -> rd' (gr + OFF_REPLY_SIZE + k) = rd (gr + OFF_REPLY_SIZE + k)).
{ intros k Hk. replace (gr + OFF_REPLY_SIZE + k) with (gr + OFF_REPLY + (8 + k)) by (unfold OFF_REPLY, OFF_REPLY_SIZE; lia).
  apply HA. lia. }
destruct y as [x|]; destruct q as [pn|]; try exact H.
- destruct H as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HS; lia | exact G2]|].
  split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [|exact G8].
  apply (abytes_atR_agree rd rd'); [|exact G7]. intros j Hj. apply (HB pn j eq_refl). lia.
- destruct H as [G1 G2].
  split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  apply (aval_mem_agree rd rd'); [intros k Hk; apply HS; lia | exact G2].
Qed.
Section e.
Variable B : asyms.

Lemma acall_at_In : forall bl (rd : reader) a c P pn,
acall_at bl rd a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P pn (H1 & H2 & H3 & _ & _ & _ & H7) Hin.
apply In_nth_error in Hin as (k & Hk).
assert (Hk' : (k < length P)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
rewrite H3 in Hk'.
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & Hb & Hlen & _). split; [exact Hb | lia].
Qed.

Lemma rec_repA_O_blocks : forall ly S (rd : reader) R O pn,
rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn.
Proof.
intros ly S rd R O pn (Q & HR & HO) Hin. apply HO in Hin.
destruct HR as (_ & _ & _ & (HL1 & HL2 & _ & HCi & Hsp & _) & HA & HRe & _ & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn).
  apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (l_calls Q))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
  rewrite HL2 in Hi'.
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  destruct (HCi i c P Hc Hi) as [Hcall _]. exact (acall_at_In _ _ _ _ _ _ Hcall Hpn).
- apply in_app_or in Hin as [Hin | Hin].
  + exact (acall_at_In _ _ _ _ _ _ Hsp Hin).
  + apply in_app_or in Hin as [Hin | Hin].
    * destruct (r_answer R) as [x|] eqn:Ea;
      destruct (l_answer Q) as [q0|] eqn:Eq; cbn [oblk] in Hin;
      [ destruct Hin as [<-|[]]; destruct HA as (_ & _ & Hb & Hlen & _); split; [exact Hb | lia]
      | destruct HA | destruct HA | destruct Hin ].
    * destruct (r_reply R) as [x|] eqn:Ey;
      destruct (l_reply Q) as [q0|] eqn:Eq; cbn [oblk] in Hin;
      [ | destruct HRe | destruct HRe | destruct Hin ].
      destruct Hin as [<-|[]]. destruct HRe as (_ & _ & _ & Hx & Hb & Hlen & _).
      assert (Hx1 : (1 <= length x)%nat) by (destruct x; [congruence | cbn [length]; lia]).
      split; [exact Hb | lia].
Qed.

(* the recorder's representation over a reader that agrees on the bytes it reads, with g_rec.state set anew *)
Lemma rec_repA_set_state : forall ly S (rd rd' : reader) R O h,
rec_repA B ly S rd R O ->
(forall a, rep_addr O a -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
rec_repA B ly S rd' (set_state R h) O.
Proof.
intros ly S rd rd' R O h HRA HK Hh Hhr.
assert (P1 : r_refuse (set_state R h) = r_refuse R) by reflexivity.
assert (P2 : r_code (set_state R h) = r_code R) by reflexivity.
assert (P3 : r_calls (set_state R h) = r_calls R) by reflexivity.
assert (P4 : r_spill (set_state R h) = r_spill R) by reflexivity.
assert (P5 : r_answer (set_state R h) = r_answer R) by reflexivity.
assert (P6 : r_nreplies (set_state R h) = r_nreplies R) by reflexivity.
assert (P7 : r_reply (set_state R h) = r_reply R) by reflexivity.
assert (P8 : r_state (set_state R h) = h) by reflexivity.
assert (P9 : r_host (set_state R h) = r_host R) by reflexivity.
destruct HRA as (Q & HR & HO). exists Q. split; [|exact HO].
destruct HR as (Hg & Hs & Hap & HC & HA & HRe & HSc & HOw).
assert (HKg : forall d k, 0 <= d -> 0 <= k -> d + k < REC_SIZE -> ~ (OFF_STATE <= d + k < OFF_STATE + 8) ->
  rd' (A_G_REC + d + k) = rd (A_G_REC + d + k)).
{ intros d k Hd Hk Hdk Hns. replace (A_G_REC + d + k) with (A_G_REC + (d + k)) by lia.
  apply HK; [left; lia | unfold OFF_STATE in *; lia]. }
assert (HKs : forall k, 0 <= k < SC_SIZE -> rd' (A_REC_SPILL + k) = rd (A_REC_SPILL + k)).
{ intros k Hk. apply HK; [right; left; lia|]. unfold A_G_REC, A_REC_SPILL, OFF_STATE, SC_SIZE in *. lia. }
assert (HKb : forall pn k, In pn O -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)).
{ intros pn k Hin Hk. destruct (HOw) as (_ & Hiv). destruct (Hiv pn (proj1 (HO pn) Hin)) as [Hiv1 _].
  apply HK; [right; right; exists (fst pn), (snd pn); split; [rewrite <- surjective_pairing; exact Hin | lia]|].
  unfold iv_apart, REC_SIZE, OFF_STATE in *. lia. }
unfold arep_at, ag1_calls, ag1_scalars.
rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7, ?P8, ?P9.
split; [exact Hg|]. split; [exact Hs|]. split; [exact Hap|].
destruct HC as (HL1 & HL2 & HN & HCi & Hsp & HF).
split.
{ split; [exact HL1|]. split; [exact HL2|].
  split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_NCALLS k); unfold OFF_NCALLS, REC_SIZE, OFF_STATE; lia | exact HN]|].
  split.
  - intros i c P Hi Hp. destruct (HCi i c P Hi Hp) as [Hcall Hfa]. split; [|exact Hfa].
    assert (Hi' : (i < length (r_calls R))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
    assert (HPO : forall pn, In pn P -> In pn O).
    { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. left. apply in_concat.
      exists P. split; [eapply nth_error_In; exact Hp | exact Hpn]. }
    apply (acall_at_agree _ rd rd'); [| |exact Hcall].
    + intros k Hk. replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + k)
        with (A_G_REC + (OFF_CALLS + CALL_SIZE * Z.of_nat i) + k) by lia.
      apply HKg; unfold OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_STATE in *; lia.
    + intros pn k Hpn Hk. apply HKb; [exact (HPO pn Hpn) | exact Hk].
  - split; [|exact HF].
    assert (HPO : forall pn, In pn (l_spill Q) -> In pn O).
    { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
    apply (acall_at_agree _ rd rd'); [| |exact Hsp].
    + intros k Hk. apply HKs. unfold CALL_SIZE, SC_SIZE in *. lia.
    + intros pn k Hpn Hk. apply HKb; [exact (HPO pn Hpn) | exact Hk]. }
split.
{ apply (aanswer_at_agree _ rd rd'); [| |exact HA].
  - intros k Hk. apply (HKg OFF_ANSWER k); unfold OFF_ANSWER, REC_SIZE, OFF_STATE; lia.
  - intros pn k Hq Hk. apply HKb; [|exact Hk]. apply HO. unfold lay_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Hq. left. reflexivity. }
split.
{ apply (areply_at_agree _ rd rd'); [| |exact HRe].
  - intros k Hk. apply (HKg OFF_REPLY k); unfold OFF_REPLY, REC_SIZE, OFF_STATE; lia.
  - intros pn k Hq Hk. apply HKb; [|exact Hk]. apply HO. unfold lay_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite Hq. left. reflexivity. }
split; [|exact HOw].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_REFUSE k); unfold OFF_REFUSE, REC_SIZE, OFF_STATE; lia | exact S1]|].
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_CODE k); unfold OFF_CODE, REC_SIZE, OFF_STATE; lia | exact S2]|].
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_NREPLIES k); unfold OFF_NREPLIES, REC_SIZE, OFF_STATE; lia | exact S3]|].
split; [exact Hh|].
split; [apply (aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_HOST k); unfold OFF_HOST, REC_SIZE, OFF_STATE; lia | exact S5]|].
repeat (split; [lia|]). lia.
Qed.

Lemma rec_repA_keep : forall ly S (rd rd' : reader) R O,
rec_repA B ly S rd R O -> (forall a, rep_addr O a -> rd' a = rd a) -> rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O HR HK.
assert (HS : aval_mem rd' (A_G_REC + OFF_STATE) 8 (r_state R)).
{ destruct HR as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & S4 & _) & _) & _).
  apply (aval_mem_agree rd rd'); [intros k Hk; apply HK; left; unfold OFF_STATE, REC_SIZE; lia | exact S4]. }
assert (HB : 0 <= r_state R < 2 ^ 64).
{ destruct HR as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & S9 & _) & _) & _). exact S9. }
pose proof (rec_repA_set_state ly S rd rd' R O (r_state R) HR ltac:(intros a Ha _; apply HK; exact Ha) HS HB) as H.
destruct R; exact H.
Qed.
End e.
Lemma mod64_32 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as D.
replace (z mod 2 ^ 64) with (z - 2 ^ 64 * (z / 2 ^ 64)) by lia.
replace (2 ^ 64 * (z / 2 ^ 64)) with ((2 ^ 32 * (z / 2 ^ 64)) * 2 ^ 32) by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); lia).
rewrite Zminus_mod, Z_mod_mult, Z.sub_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma val_mem_mod : forall segs m a n v v',
v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) -> val_mem segs m a n v -> val_mem segs m a n v'.
Proof.
intros segs m a n v v' Hm H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YO0f.le_byte. rewrite Hm. reflexivity.
Qed.

(* ---- the symbolic state the segment starts from ---- *)
Definition br_greg : YP09.region := YP09.mkRegion (Some (A_OBJ 44)) 0 952 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0)); YP09.mkChunk 944 (CVal 8 (SOff 35 0))].
Definition br_facts : facts := mkFacts [(32%nat, mkAF SB SB 0)] [] [].
Definition ss_br0 : sstate := mkSS AN_BODY sr_atoms [br_greg] None br_facts.
Definition br_Bx : sv := SOff 32 0.
Definition br_SH : list shent := [].
Definition br_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Section e.
Variable B : asyms.
Hypothesis VOBJS : cmd_val_objs.

Definition br_extra (R : rstate) : list word :=
map (Z_to_bv 64) [SB; r_refuse R mod 2 ^ 32; r_code R mod 2 ^ 32; r_state R].
Definition br_E (regs : bvmap 5 word) (R : rstate) : env := Eimg (Ereg regs (br_extra R)).

Lemma br_grec : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma br_ew32 : forall regs R, ew (br_E regs R) 32 = Z_to_bv 64 SB.
Proof. intros regs R. unfold br_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma br_ew33 : forall regs R, ew (br_E regs R) 33 = Z_to_bv 64 (r_refuse R mod 2 ^ 32).
Proof. intros regs R. unfold br_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma br_ew34 : forall regs R, ew (br_E regs R) 34 = Z_to_bv 64 (r_code R mod 2 ^ 32).
Proof. intros regs R. unfold br_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). Qed.
Lemma br_ew35 : forall regs R, ew (br_E regs R) 35 = Z_to_bv 64 (r_state R).
Proof. intros regs R. unfold br_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3). Qed.
Lemma br_ewobj : forall regs R, ew (br_E regs R) (A_OBJ 44) = Z_to_bv 64 A_G_REC.
Proof.
intros regs R. unfold br_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite br_grec. reflexivity.
Qed.
Lemma br_img : forall regs R, img_env VAL A_LIM (br_E regs R).
Proof. intros regs R. unfold br_E. apply Eimg_env. Qed.

Lemma br_seed : forall (W : world SEGS) ly S (regs1 : bvmap 5 word) mem R O,
rec_repA B ly S (rdW W mem) R O ->
st_ok_pi SEGS VAL (br_E regs1 R) ss_br0
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AN_BODY)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs1 mem R O (Q & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) & _).
assert (Hb : base_val (br_E regs1 R) (Some (A_OBJ 44)) = A_G_REC).
{ cbn [base_val]. rewrite br_ewobj. apply unsigned_lit_small. unfold A_G_REC. lia. }
rewrite restrict_mkst_fx. unfold ss_br0. apply pa_entry_st_ok_full.
- unfold br_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, br_greg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_any SEGS (br_E regs1 R) _ A_G_REC 0 4 (SOff 33 0)); [lia|].
    cbn [sv_denot]. rewrite br_ew33. rewrite !Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (pose proof (Z.mod_pos_bound (r_refuse R) (2 ^ 32) ltac:(lia)); lia).
    apply (val_mem_mod SEGS _ _ 4%nat (r_refuse R)).
    * replace (8 * Z.of_nat 4) with 32 by (cbn; lia). rewrite !Zmod_mod. reflexivity.
    * apply (val_mem_of_aval SEGS (w_H W) mem). exact S1.
  + apply (chunk_ok_any SEGS (br_E regs1 R) _ A_G_REC 4 4 (SOff 34 0)); [lia|].
    cbn [sv_denot]. rewrite br_ew34. rewrite !Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (pose proof (Z.mod_pos_bound (r_code R) (2 ^ 32) ltac:(lia)); lia).
    apply (val_mem_mod SEGS _ _ 4%nat (r_code R)).
    * replace (8 * Z.of_nat 4) with 32 by (cbn; lia). rewrite !Zmod_mod. reflexivity.
    * apply (val_mem_of_aval SEGS (w_H W) mem). exact S2.
  + apply (chunk_ok_any SEGS (br_E regs1 R) _ A_G_REC 944 8 (SOff 35 0)); [lia|].
    cbn [sv_denot]. rewrite br_ew35. rewrite !Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia.
    apply (val_mem_mod SEGS _ _ 8%nat (r_state R)).
    * replace (8 * Z.of_nat 8) with 64 by (cbn; lia). rewrite !Zmod_mod. reflexivity.
    * apply (val_mem_of_aval SEGS (w_H W) mem). exact S4.
- apply pairwise_disjoint_of_extents. cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [br_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite br_ew32, unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. unfold SB. repeat split; lia.
Qed.
End e.
(* the 32-bit load of a signed field: its value and its low half *)
Lemma br_sext32_val : forall E (n : nat) z, ew E n = Z_to_bv 64 (z mod 2 ^ 32) -> - 2 ^ 31 <= z < 2 ^ 31 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) = z mod 2 ^ 64.
Proof.
intros E n z He Hz.
assert (Hm : z mod 2 ^ 32 = if z <? 0 then z + 2 ^ 32 else z).
{ destruct (Z.ltb_spec z 0) as [Hlt|Hge].
  - rewrite <- (Z.mod_add z 1 (2 ^ 32)) by lia. apply Z.mod_small. lia.
  - apply Z.mod_small. lia. }
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt.
assert (HU : U E (SOff n 0) = z mod 2 ^ 32).
{ unfold U. cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small; [reflexivity|]. pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)). lia. }
rewrite HU. change (Z.of_N 32) with 32. rewrite Z.mod_mod by lia.
assert (HS : bv_swrap 32 (z mod 2 ^ 32) = z).
{ unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Hm. destruct (Z.ltb_spec z 0) as [Hlt|Hge].
  - rewrite <- (Z.mod_add (z + 2 ^ 32 + 2 ^ 31) (-1) (2 ^ 32)) by lia.
    rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
rewrite HS. unfold zcanon. rewrite M64_val. reflexivity.
Qed.

Lemma br_sext32_mod : forall E (n : nat) z, ew E n = Z_to_bv 64 (z mod 2 ^ 32) -> - 2 ^ 31 <= z < 2 ^ 31 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros E n z He Hz. rewrite (br_sext32_val E n z He Hz). apply mod64_32. Qed.

Lemma br_sext32_zero : forall E (n : nat) z, ew E n = Z_to_bv 64 (z mod 2 ^ 32) -> - 2 ^ 31 <= z < 2 ^ 31 ->
(bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) = 0 <-> z = 0).
Proof.
intros E n z He Hz. rewrite (br_sext32_val E n z He Hz). split.
- intros H. destruct (Z.ltb_spec z 0) as [Hlt|Hge].
  + rewrite <- (Z.mod_add z 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
  + rewrite Z.mod_small in H by lia. exact H.
- intros ->. reflexivity.
Qed.

Lemma br_sext_off : forall E (n : nat), sv_denot E (SExt true 32 (SOff n 0)) = sext 64 (bv_extract 0 32 (ew E n)).
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* awr_ok over a state whose regions are all read-only *)
Ltac br_awr_ro :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end;
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

Section m.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses (answer_c.v:74, :79-80), word for word *)
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary walk facts, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
(* the image facts (CmdRecBase.v's cmd_img_facts); the record facts below are IMG's field and the CmdRecFacts.v
   lemmas, by exact *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let RRO := RRO SEGS B LAWS HB IMG.
Let RPG := RPG SEGS B LAWS HB IMG.
Let cif_prog_img := cif_prog_img _ _ IMG.
Let cmd_addressable_chk := cmd_addressable_chk SEGS B LAWS HB.
Let cmd_aread_ok_chk := cmd_aread_ok_chk SEGS B LAWS HB.
Let cmd_rec_cells := cmd_rec_cells SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := cmd_ro_ok_of_aro SEGS B LAWS HB IMG.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma br_ew_reg : forall regs R (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (br_E regs R) n = getr regs r.
Proof.
intros regs R n r H. unfold br_E.
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr; unfold A_TEXT; lia).
apply ew_Ereg_nat. exact H.
Qed.
Lemma br_ew288 : forall regs R, ew (br_E regs R) 288%nat = Z_to_bv 64 0x21d00.
Proof.
intros regs R. unfold br_E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
change 288%nat with (A_OBJ 47). rewrite (VOBJS 47%nat ltac:(vm_compute; lia)). vm_compute. reflexivity.
Qed.
Lemma br_ew285 : forall E, img_env VAL A_LIM E -> ew E 285%nat = Z_to_bv 64 A_G_REC.
Proof.
intros E HE. pose proof (HE 285%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
change 285%nat with (A_OBJ 44) in H |- *. rewrite (br_grec VOBJS) in H.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by (unfold A_G_REC; lia). reflexivity.
Qed.

(* the read-only bytes are kept by the walk's journal: its footprint is g_rec's two words and heap blocks *)
Lemma br_aro_journal : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k old O R,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
ajournal SEGS B STK sp0 (an_FP old O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k old O R HAR HR HJ HRO a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hrr)]. }
rewrite (F3 a Himg Ho He); [exact (HRO a Hro Ho He)|].
apply fp_spares_closed.
- unfold an_FP. apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_ANSWER; lia|].
  apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_STATE; lia|].
  apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hpn. apply br_in_filter in Hpn as [Hpn _].
  destruct (rec_repA_O_blocks B ly S _ R O (p, n) HR Hpn) as [Hb _].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & H4096 & _). cbn [fst]. lia.
- intros (r & Hr & Ha). unfold an_FP in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]].
  + apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
    split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_ANSWER in Ha; lia].
  + apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
    split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_STATE in Ha; lia].
  + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply br_in_filter in Hpn as [Hpn _].
    destruct (rec_repA_O_blocks B ly S _ R O (p, n) HR Hpn) as [Hb _].
    cbn [fst snd] in Ha. exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hb Ha Himg).
Qed.

(* the bytes the recorder's representation reads lie below the allocator's ceiling and outside the frame *)
Lemma br_rep_apart : forall lyc Sc (Wc : world SEGS) memc mdc R O pos a,
AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc (rdW Wc memc) R O -> In (7, pos) (frames Sc) ->
rep_addr O a -> 0 <= a < alloc_ceiling /\ ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + fs_frame_bytes 7).
Proof.
intros lyc Sc Wc memc mdc R O pos a HAR HR Hin Ha.
pose proof asan_consts as (C1 & _).
destruct Ha as [Ha | [Ha | (p & n & Hpn & Ha)]].
- split; [unfold A_G_REC, REC_SIZE in Ha; lia|]. intros Hf.
  assert (Hi : in_img SEGS a).
  { apply cif_prog_img. exists (A_G_REC, A_G_REC + 960). split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]. }
  exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos a HAR Hin Hf Hi).
- split; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|]. intros Hf.
  assert (Hi : in_img SEGS a).
  { apply cif_prog_img. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [cbn [In cmd_PG]; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]. }
  exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos a HAR Hin Hf Hi).
- destruct (rec_repA_O_blocks B lyc Sc _ R O (p, n) HR Hpn) as [Hb Hn1]. cbn [snd] in Hn1.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hb) as (_ & H4096 & Hceil & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
  split; [lia|]. intros Hf.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 7 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the shape string at a later state of the walk: its bytes are kept by the journal (a live block apart from the
   recorder's blocks, or read-only image bytes), and its shadow is still addressable *)
Lemma br_shape_at : forall STK sp0 own ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k old O R sh x,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
ajournal SEGS B STK sp0 (an_FP old O) ly S W mem md own lyc Sc Wc memc mdc k ->
Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O sh (Some x) ->
astr_atR (rdW Wc memc) sh x /\ range_addressable (rdW Wc memc) SHADOW_OFF sh (Z.of_nat (length x) + 1).
Proof.
intros STK sp0 own ly S W mem md lyc Sc Wc memc mdc k old O R sh x HAR HREP HJ HPERM HROD HARG.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
cbn [astr_argA] in HARG.
destruct HARG as (Hsh0 & HSTR & HLM & [[(p & kk & Hb & Hp1 & Hp2) HAP] | [HRO (Hab & Hhb & Hend)]]).
- assert (Hbc : In (p, kk) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hb).
  destruct (al_blocks _ _ LAWS ly S W mem md p kk HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hreq].
  assert (HK : forall i, 0 <= i <= Z.of_nat (length x) -> rdW Wc memc (sh + i) = rdW W mem (sh + i)).
  { intros i Hi. replace (sh + i) with (p + (sh + i - p)) by lia.
    apply (F2 p kk (sh + i - p) Hb Hbc ltac:(lia)).
    replace (p + (sh + i - p)) with (sh + i) by lia.
    intros (r & Hr & Ha). unfold an_FP in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | Hr]].
    + apply (blk_img SEGS B LAWS ly S W mem md p kk (sh + i) HAR Hb ltac:(lia)).
      apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
      split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_ANSWER in Ha; lia].
    + apply (blk_img SEGS B LAWS ly S W mem md p kk (sh + i) HAR Hb ltac:(lia)).
      apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
      split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_STATE in Ha; lia].
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm). apply br_in_filter in Hbm as [Hbm _].
      cbn [fst snd] in Ha.
      destruct (rec_repA_O_blocks B ly S _ R O (b, m) HREP Hbm) as [HbB _].
      destruct (Z.eq_dec b p) as [Ebp | Ebp]; [destruct (Z.eq_dec m kk) as [Emk | Emk]|].
      * subst b m. rewrite Forall_forall in HAP. specialize (HAP (p, kk) Hbm). unfold iv_apart in HAP. cbn [fst snd] in HAP. lia.
      * assert (Hne : (b, m) <> (p, kk)) by congruence.
        pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p kk HAR HbB Hb Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      * assert (Hne : (b, m) <> (p, kk)) by congruence.
        pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p kk HAR HbB Hb Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  split.
  + apply (astr_atR_agree (rdW W mem)); [|exact HSTR]. intros i Hi. apply HK. lia.
  + apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc p kk); [exact HARc | exact Hbc | lia | lia].
- pose proof (br_aro_journal STK sp0 ly S W mem md own lyc Sc Wc memc mdc k old O R HAR HREP HJ HROD) as HROD'.
  split.
  + apply (astr_atR_agree (rdW W mem)); [|exact HSTR]. intros i Hi.
    destruct (HRO i ltac:(lia)) as (Hr & Hno & Hne).
    rewrite (HROD' _ Hr Hno Hne), (HROD _ Hr Hno Hne). reflexivity.
  + exact (cmd_addressable_chk lyc Sc Wc memc mdc sh _ HARc Hab).
Qed.

(* the bytes an_mid reads, besides the journal: the recorder's representation without g_rec.state, the prologue's
   slots, the frame's flag word and the shadow of buf *)
Definition br_mid_dom (sp0 : Z) (O : list (Z * Z)) (F : Z) (a : Z) : Prop :=
(rep_addr O a /\ ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8)) \/
(sp0 - 104 <= a < sp0) \/
(F + 8184 <= a < F + 8192) \/
(shadow_of_addr SHADOW_OFF (F + 32) <= a < shadow_of_addr SHADOW_OFF (F + 32) + 512).

(* an_mid at a later state whose bytes agree on br_mid_dom and whose g_rec.state holds h *)
Lemma br_mid_set : forall ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc' memc' mdc' h,
an_mid B MT ly S W regs mem md R old O lyc Sc Wc memc mdc pos 0 sp1 ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc' memc' mdc' 0 ->
(forall a, br_mid_dom (spZ regs) O (frame_addr lyc 7 pos) a -> rdW Wc' memc' a = rdW Wc memc a) ->
aval_mem (rdW Wc' memc') (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
an_mid B MT ly S W regs mem md (set_state R h) old O lyc Sc Wc' memc' mdc' pos 0 sp1.
Proof.
intros ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc' memc' mdc' h HM HJ' HK Hh Hhr.
destruct HM as (HJ & HMOLE & HPERM & HSP1 & HSAVED & HFLAG & HZS & HRC & HOLDC).
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity.
unfold an_mid. rewrite FB in HFLAG |- *.
split; [exact HJ'|]. split; [exact HMOLE|]. split; [exact HPERM|]. split; [exact HSP1|].
split.
{ intros j r Hj.
  assert (Hj13 : (j < length an_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn [length an_saved] in Hj13.
  apply (aval_mem_agree (rdW Wc memc)); [|exact (HSAVED j r Hj)].
  intros k Hk. apply HK. right; left. lia. }
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc' memc')); [exact HFLAG|].
  intros k Hk. apply HK. right; right; left. lia. }
split.
{ intros i Hi. change (4096 / 8) with 512 in Hi. rewrite HK; [exact (HZS i ltac:(change (4096 / 8) with 512; lia))|].
  right; right; right. lia. }
split.
{ apply (rec_repA_set_state B lyc Sc (rdW Wc memc) _ R O h HRC); [|exact Hh|exact Hhr].
  intros a Ha Hns. apply HK. left. split; assumption. }
apply (aval_mem_agree (rdW Wc memc)); [|exact HOLDC].
intros k Hk. apply HK. left.
split; [left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | unfold OFF_ANSWER, OFF_STATE; lia].
Qed.

(* a byte value as a bit vector and back *)
Lemma br_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

(* the BODY cut (0x8a61c, after the two shadow fills) reaches JOIN (refusal; at the FP state the snprintf wrapper
   returns) or HEAD (no refusal) *)
Lemma an_body_ok : (forall fx0 : YK11.FPState, AN_JOIN_stmt (fx := fx0) B MT) -> AN_HEAD_stmt B MT -> AN_BODY_stmt B MT.
Proof.
intros HJOIN HHEAD. unfold AN_BODY_stmt.
intros ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HFRM HMID HREGS H19.
pose proof HPRE as (HFN & HFRL & HROD & HRO & H10 & H11 & HCHG & HREP & HOLD & HSHP & HSLOT & HEV & HLIVE & HMO & HRNG).
pose proof HMID as (HJ & HMOLE & HPERM & HSP1 & HSAVED & HFLAG & HZS & HRC & HOLDC).
pose proof HREGS as (G2 & G3 & G4 & G8 & G9 & G18 & G25 & G20 & G21 & G22 & G23 & G24 & G26).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hch & HQT0).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & F5 & Hpresw & Hstk & F6 & HQT).
pose proof Hstk as (Hal16 & Hstk1 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (br_seed B VOBJS Wc lyc Sc regs1 memc R O HRC) as HS.
pose proof (br_img regs1 R) as HEI.
assert (SHOK : sh_ok SEGS br_Bx br_SH (br_E regs1 R) (mrestrict (w_H Wc) memc)) by (unfold sh_ok, br_SH; apply Forall_nil).
unfold an_postF. paj_run_tok RUN HS HJ SHOK br_Bspan.
{ br_awr_ro. }
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *; clearbody mdv.
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) (br_E regs1 R) (ss_mem ss_br0) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha|intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
clear HF HFr HG.
pose proof HRC as (Q0 & (_ & _ & _ & _ & _ & _ & (HS1 & HS2 & HS3 & HS4 & HS5 & HRR & HRCD & HRN & HRS & HRH) & _) & _).
assert (WS : ANSWER_STK = 16592) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hs1a & Hs1b & Hs1c).
rewrite <- HSP1 in Hs1a, Hs1b, Hs1c.
assert (Ho16 : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hal16, Hs1c; reflexivity).
assert (Hin7 : In (7, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf32 & Hfapp & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf4096 & Hfceil & _).
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity. rewrite FB in Hfceil, Hfapp.
psrr_branch_tok RUN BR HS SHOK br_Bspan.
(* refuse <> 0 (0x8a62c): snprintf (buf, 4096, "resp %d", g_rec.code), then JOIN *)
2: {
  assert (HRF : r_refuse R <> 0).
  { intros H0.
    rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold U at 1.
    rewrite (proj2 (br_sext32_zero (br_E regs1 R) 33 (r_refuse R) (br_ew33 regs1 R) HRR) H0). reflexivity. }
  paj_run_tok RUN HS HJ SHOK br_Bspan.
  { br_awr_ro. }
  set (mdv2 := with_vm_backing (m_vm_lazy mdv) _ mdv) in *; clearbody mdv2. pmkst HS. prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
  prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha.
    rewrite <- (KEEP0 a Ha).
    apply (kept_of_frame (segs:=SEGS) (br_E regs1 R) _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
  clear HF HFr HG. assert (Rsp : spZ (ms_regs ms0) = sp1).
  { unfold spZ.
    rewrite P2, (br_ew_reg regs1 R 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (proj1 HJ) as HAR0.
  destruct (al_frames _ _ LAWS lyc Sc Wc (ms_mem ms0) mdv2 7 pos HAR0 Hin7) as (_ & _ & Hfp0 & _). rewrite FB in Hfp0.
  assert (HROD0 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms0)))
    by exact (br_aro_journal _ _ ly S W mem md _ lyc Sc Wc _ _ _ old O R HAR HREP HJ HROD).
  pose proof (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem ms0) mdv2 HAR0 HROD0) as HRO0.
  assert (HLIT : abytes_atR (rdW Wc (ms_mem ms0)) 0x21d00 RO_lit_21d00).
  { clear - HRO0.
    destruct HRO0 as [HRO0 _]. unfold cmd_ro_bytes in HRO0. repeat match type of HRO0 with
      | abytes_atR _ 0x21d00 _ /\ _ => exact (proj1 HRO0) | _ /\ _ => apply proj2 in HRO0 end. }
  (* the snprintf wrapper (buf, 4096, "resp %d", g_rec.code), the shared contract (RtPFCmd.v asnprintf_sh) at the
     entry's FP state, through the kit's printf step (PaFx.v); it writes the text T and its
     terminator at buf and returns at some FP state fx1, where the walk goes on to JOIN *)
  remember (RecAns.RESP_HEAD ++ PF.pf_dec (r_code R)) as T eqn:ET.
  assert (HT16 : (length T <= 16)%nat) by (rewrite ET; pose proof (RecAns.resp_len (r_code R) HRCD); lia).
  assert (Ew : RtPFShared.sn_len (4096 - 1) T = Z.of_nat (length T) + 1).
  { unfold RtPFShared.sn_len, RtPFShared.sn_bytes.
    rewrite firstn_all2 by (change (Z.to_nat (4096 - 1)) with 4095%nat; lia). rewrite length_app. cbn [length]. lia. }
  assert (Eby : RtPFShared.sn_bytes (4096 - 1) T = T ++ [0]).
  { unfold RtPFShared.sn_bytes. rewrite firstn_all2 by (change (Z.to_nat (4096 - 1)) with 4095%nat; lia). reflexivity. }
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  pose proof (RtPFDog.pa_frame_above_img (PI := PI) B lyc Sc Wc (ms_mem ms0) mdv2 7 pos HAR0 Hin7) as HFIMG.
  unfold RtPFCmd.CMD_IMG_HI in HFIMG.
  destruct (proj1 (proj2 (cmd_rec_cells lyc Sc Wc (ms_mem ms0) mdv2 HAR0))) as (HGC & cval & HGV).
  destruct (cmd_aread_ok_chk lyc Sc Wc (ms_mem ms0) mdv2 0x21d00 8 HAR0 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as [HRA HHV].
  assert (HRAb : range_addressable (rdW Wc (ms_mem ms0)) SHADOW_OFF (frame_addr lyc 7 pos + 32) 4096).
  { assert (HF8 : (frame_addr lyc 7 pos + 32) mod 8 = 0).
    { pose proof (Z.div_mod (frame_addr lyc 7 pos) 32 ltac:(lia)) as D.
      rewrite Hf32, Z.add_0_r in D. rewrite D.
      replace (32 * (frame_addr lyc 7 pos / 32) + 32) with ((4 * (frame_addr lyc 7 pos / 32) + 4) * 8) by lia.
      apply Z_mod_mult. }
    apply zero_shadow_range; [exact HF8 | reflexivity |]. intros i Hi. change (4096 / 8) with 512 in Hi.
    pose proof (Z.div_pos (frame_addr lyc 7 pos + 32) 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_le_upper_bound (frame_addr lyc 7 pos + 32) 8 (frame_addr lyc 7 pos + 32) ltac:(lia) ltac:(lia)) as D2.
    rewrite KEEP1; [exact (HZS i ltac:(change (4096 / 8) with 512; lia))|]. unfold shadow_of_addr, SHADOW_OFF. lia. }
  assert (AWR : forall a, frame_addr lyc 7 pos + 32 <= a < frame_addr lyc 7 pos + 32 + RtPFShared.sn_len (4096 - 1) T ->
    awr_byte SEGS B ANSWER_STK (spZ regs) (an_FP old O) (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [(7, pos)] a).
  { intros a Ha. rewrite Ew in Ha. right; right; right; left. exists 7, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite FB. lia. }
  eapply SRr_bind.
  { eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
      (fun a => frame_addr lyc 7 pos + 32 <= a < frame_addr lyc 7 pos + 32 + RtPFShared.sn_len (4096 - 1) T)
      (SIG CS___interceptor_trampoline_snprintf) Wc (ms_regs ms0) (ms_mem ms0) ANSWER_STK (spZ regs) (an_FP old O)
      ly S W mem md [(7, pos)] lyc Sc mdv2 0 (sp1 - spZ regs) (getr (ms_regs ms0) 1) _ HJ).
    - lia.
    - exact Ho16.
    - lia.
    - unfold RtPFCmd.CMD_SNP_K. lia.
    - unfold RtPFCmd.CMD_SNP_K. lia.
    - reflexivity.
    - exact AWR.
    - apply srr_art_postF_of_pf.
      { intros a Ha. rewrite Rsp in Ha. unfold RtPFCmd.CMD_SNP_K in Ha. apply HpresC. lia. }
      apply (ASNPRINTF fx lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv2 (frame_addr lyc 7 pos + 32) 4096 0x21d00 []
        (map (argZ (ms_regs ms0)) [3; 4; 5; 6; 7] ++ []) T cval).
      + (* ecall_pre *)
        eapply (ecall_pre_at SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc (ms_mem ms0)
          mdv2 0 (ms_regs ms0) (sp1 - spZ regs) HJ).
        * lia.
        * exact Ho16.
        * lia.
        * lia.
        * rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
        * rewrite P3, (br_ew_reg regs1 R 3 3%bv eq_refl). exact G3.
        * rewrite P4, (br_ew_reg regs1 R 4 4%bv eq_refl). exact G4.
      + rewrite Eslo, Rsp. unfold RtPFCmd.CMD_SNP_K. lia.
      + intros a Ha. rewrite Rsp in Ha. unfold RtPFCmd.CMD_SNP_K in Ha. apply HpresC. lia.
      + rewrite P10, (br_ew_reg regs1 R 21 21%bv eq_refl), G21. reflexivity.
      + rewrite P11. reflexivity.
      + rewrite P12, br_ew288. reflexivity.
      + exact (cmd_consts_view_snp SEGS B LAWS HB IMG CMD_RLO CMD_RHI Wc (ms_mem ms0) HROD0).
      + unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
      + apply Forall_forall. intros r Hr.
        pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as Hb.
        unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in Hb.
        apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. apply Z.leb_le in Hb3.
        apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite Rsp, Ew. unfold RtPFCmd.CMD_SNP_K.
        split; left; lia.
      + exact HGC.
      + exact HGV.
      + lia.
      + lia.
      + lia.
      + lia.
      + apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite Rsp, Ew. unfold RtPFCmd.CMD_SNP_K.
        split; left; lia.
      + apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite Rsp, Ew. unfold RtPFCmd.CMD_SNP_K.
        split; left; lia.
      + unfold RtPFShared.va_words. split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
      + cbn [length Z.of_nat]. rewrite Rsp. lia.
      + apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd length Z.of_nat]. rewrite Rsp, Ew.
        unfold RtPFCmd.CMD_SNP_K. split; right; lia.
      + (* the format family: "resp %d" at 0x21d00 with g_rec.code in a3 *)
        apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ RecAns.RESP_FMT RecAns.RESP_PS [PF.AInt (r_code R)]).
        * unfold RtPFShared.fmt_at. change (Z.of_nat (length RecAns.RESP_FMT)) with 7.
          split; [lia|]. split.
          { intros i Hi.
            replace (0x21d00 + i) with (0x21d00 + Z.of_nat (Z.to_nat i)) by lia.
            rewrite (HLIT (Z.to_nat i)) by (change (length RO_lit_21d00) with 8%nat; lia).
            assert (Hk : (Z.to_nat i < 8)%nat) by lia. revert Hk. generalize (Z.to_nat i) as k. intros k Hk.
            do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
          split.
          { apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite Rsp, Ew. unfold RtPFCmd.CMD_SNP_K.
            split; left; lia. }
          split; [unfold amem_range; left; lia|].
          split; [exact HRA | exact HHV].
        * exact RecAns.resp_parse.
        * cbn [map RtPFCmd.arg_of app RtPFShared.pf_args_asan RtPFShared.pf_arg_asan].
          split; [|exact I]. split; [exact HRCD|].
          unfold argZ. replace (getr (ms_regs ms0) (Z_to_bv 5 (10 + 3))) with (getr (ms_regs ms0) 13)
            by (f_equal; apply bv_eq; reflexivity).
          rewrite P13, <- (br_sext_off (br_E regs1 R) 34).
          exact (br_sext32_mod (br_E regs1 R) 34 (r_code R) (br_ew34 regs1 R) HRCD).
        * rewrite ET. exact (RecAns.resp_text (r_code R)).
        * vm_compute. exact I.
        * vm_compute; reflexivity.
      + lia.
      + lia.
      + lia.
      + rewrite Ew. lia.
      + apply RtPFSx.pairwise_snp. unfold zdisjoint. cbn [fst snd]. rewrite Rsp, Ew. unfold RtPFCmd.CMD_SNP_K.
        right. lia.
      + (* dest_ok: buf's bytes are the frame's, present and not the allocator's *)
        intros a Ha. split; [|split].
        * apply (apresent_writable SEGS). rewrite Ew in Ha. exact (proj1 (Hfp0 a ltac:(lia))).
        * exact (proj1 (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (AWR a Ha))).
        * rewrite Ew in Ha. rewrite Rsp. lia.
      + (* the `+ 8` band premise: the text, its terminator and 8 more bytes lie in buf's fake frame *)
        rewrite Ew. apply (amem_range_sub_app (frame_addr lyc 7 pos) 8192); [exact Hfapp | exact Hfceil | lia | lia | lia].
      + intros y Hy. apply HRAb. rewrite Ew in Hy. lia.
      + exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms0) mdv2 7 pos (frame_addr lyc 7 pos + 32)
          (RtPFShared.sn_len (4096 - 1) T) HAR0 Hin7 ltac:(lia) ltac:(rewrite Ew, FB; lia) ltac:(rewrite Ew; lia)).
      + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. right. lia.
      + exact HFRM. }
  cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & (HRES & HBYTES) & HKEEP).
  (* from here the walk runs at fx1: JOIN at fx1, lifted to the entry's FP state by fxrel fx fx1 *)
  apply (srr_apost_base_liftF (fx := fx) SEGS fx1); [exact Hfx|].
  pose proof (st_ok_restrict_xfx fx fx1 SEGS _ _ (w_H Wc) ms0 HS eq_refl) as HSX.
  jafter_call_keep_pi HSX 40%nat regs2 (mrestrict (w_H Wc) mem2) HP2 (@nil nat) HSn. specialize (HSn (Forall_nil _)).
  rewrite <- (restrict_mkst_fx (fx := fx1)) in HSn. clear HS HSX. rename HSn into HS. hei_havoc HS. rewrite P1.
  assert (SHOK2 : sh_ok SEGS br_Bx br_SH (havoc (br_E regs1 R) 40 (map (getr regs2) CLOB)) (mrestrict (w_H Wc) mem2))
    by (unfold sh_ok, br_SH; apply Forall_nil).
  clear SHOK. rename SHOK2 into SHOK. pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
  paj_run_to_tok RUNTO1 HS HJ2 SHOK br_Bspan AN_JOIN.
  { br_awr_ro. }
  set (mdv3 := with_vm_backing (m_vm_lazy md2) mat md2) in *; clearbody mdv3.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc mem2 a).
  { intros a Ha.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H Wc) mem2 (ms_mem ms1) (fun _ => False) HFr);
      [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
  clear HF HFr HG. pmkst HS. prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
  rewrite nth_overflow in J27 by (rewrite length_map; vm_compute; lia). rewrite (br_ew285 _ HEI) in J27.
  assert (HR1 : an_R1 R e chg = R) by (unfold an_R1; rewrite (proj2 (Z.eqb_neq _ _) HRF); reflexivity).
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos + 32 <= a < frame_addr lyc 7 pos + 32 + 4096) ->
    ~ (sp1 - 3 * ESTACK <= a < sp1) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha H1 H2. rewrite (KEEP2 a Ha).
    rewrite (HKEEP a Ha) by (rewrite ?Ew; unfold RtPFCmd.CMD_SNP_K; lia). exact (KEEP1 a Ha). }
  change (BASE + 16976) with (BASE + AN_JOIN).
  apply (HJOIN fx1 ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv3 pos sp1 HPRE).
  - rewrite HR1. unfold an_mid. split; [exact HJ2|]. split; [exact HMOLE|]. split; [exact HPERM|].
    split; [exact HSP1|]. split.
    { intros j r Hj.
      assert (Hj13 : (j < length an_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      cbn [length an_saved] in Hj13. apply (aval_mem_agree (rdW Wc memc)); [|exact (HSAVED j r Hj)]. intros k Hk.
      apply KEEPJ; rewrite ?Hes; lia. }
    split.
    { rewrite FB.
      rewrite FB in HFLAG. rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms1))); [exact HFLAG|]. intros k Hk.
      apply KEEPJ; rewrite ?Hes; lia. }
    split.
    { intros i Hi.
      change (4096 / 8) with 512 in Hi. pose proof (Z.div_mod (frame_addr lyc 7 pos + 32) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (frame_addr lyc 7 pos + 32) 8 ltac:(lia)) as M.
      rewrite KEEPJ; [exact (HZS i ltac:(change (4096 / 8) with 512; lia)) | | |].
      all: unfold shadow_of_addr, SHADOW_OFF; rewrite ?Hes; zlia. }
    split.
    { apply (rec_repA_keep B lyc Sc (rdW Wc memc) _ R O HRC).
      intros a Ha. destruct (br_rep_apart lyc Sc Wc memc mdc R O pos a HARc HRC Hin7 Ha) as [Ha1 Ha2].
      rewrite FB in Ha2. apply KEEPJ; rewrite ?Hes; lia. }
    { apply (aval_mem_agree (rdW Wc memc)); [|exact HOLDC].
      intros k Hk.
      assert (Hra' : rep_addr O (A_G_REC + OFF_ANSWER + k)) by (left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia).
      destruct (br_rep_apart lyc Sc Wc memc mdc R O pos _ HARc HRC Hin7 Hra') as [Ha1 Ha2]. rewrite FB in Ha2.
      apply KEEPJ; rewrite ?Hes; lia. }
  - unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
      (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
      (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
      (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
      (br_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  - rewrite J27. reflexivity.
  - unfold rec_answer. rewrite (proj2 (Z.eqb_neq _ _) HRF). cbn [snd hand_back].
    split; [|exact (resp_no0 (r_code R))].
    rewrite <- (RecAns.pf_resp (r_code R) HRCD), <- ET.
    intros i Hi. unfold PF.pf_bytes in Hi |- *. rewrite length_app, length_map in Hi. cbn [length] in Hi.
    rewrite KEEP2 by lia.
    pose proof (HBYTES (Z.of_nat i) ltac:(rewrite Ew; lia)) as Hb. rewrite Eby, Nat2Z.id in Hb.
    rewrite Hb. f_equal.
    replace (map (Z_to_bv 8) T ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (T ++ [0])) by (rewrite map_app; reflexivity).
    rewrite map_nth. destruct (aview_byte SEGS (w_H Wc) mem2 _ _ Hb) as (b & _ & _ & Hr).
    symmetry. exact (br_u8 _ Hr). }
(* refuse = 0 (0x8a648): the test of changes (s7) *)
assert (HRZ : r_refuse R = 0).
{ rewrite branch_eq_U in Hc.
  apply Z.eqb_eq in Hc. unfold U at 1 in Hc.
  apply (proj1 (br_sext32_zero (br_E regs1 R) 33 (r_refuse R) (br_ew33 regs1 R) HRR)). rewrite Hc. reflexivity. }
destruct (HSHP HRZ) as [HARG HFITS]. clear Hc. paj_run_tok RUN HS HJ SHOK br_Bspan.
{ br_awr_ro. }
set (mdvb := with_vm_backing (m_vm_lazy mdv) _ mdv) in *; clearbody mdvb.
assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha.
  rewrite <- (KEEP0 a Ha).
  apply (kept_of_frame (segs:=SEGS) (br_E regs1 R) _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
    [|exact Ha|intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
clear HF HFr HG KEEP0. psrr_branch_tok RUN BR HS SHOK br_Bspan.
(* changes = 0: straight to HEAD with j = d = 0, out = [] *)
- assert (HCF : chg = false).
  { rewrite branch_eq_U in Hc.
    apply Z.eqb_eq in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
    rewrite (br_ew_reg regs1 R 23 23%bv eq_refl), G23, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite HCHG, Hc.
    reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK br_Bspan AN_HEAD.
  { br_awr_ro. }
  set (mdvh := with_vm_backing (m_vm_lazy mdvb) _ mdvb) in *; clearbody mdvh.
  assert (KEEPh : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha.
    rewrite <- (KEEPb a Ha).
    apply (kept_of_frame (segs:=SEGS) (br_E regs1 R) _ (w_H Wc) (ms_mem ms0) (ms_mem ms1) (fun _ => False) HFr);
      [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
  clear HF HFr HG. pmkst HS. prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (10%bv : bv 5) J10.
  prreg HS (11%bv : bv 5) J11. prreg HS (12%bv : bv 5) J12. prreg HS (13%bv : bv 5) J13. prreg HS (14%bv : bv 5) J14.
  prreg HS (19%bv : bv 5) J19. rewrite (br_ew285 _ HEI) in J27. change (BASE + 16780) with (BASE + AN_HEAD).
  destruct (br_shape_at ANSWER_STK (spZ regs) [(7, pos)] ly S W mem md lyc Sc Wc (ms_mem ms1) mdvh 0 old O R sh x
    HAR HREP HJ HPERM HROD HARG) as [HSTRh HRAh].
  assert (HR1 : an_R1 R e chg = set_state R (r_state R)) by (unfold an_R1; rewrite HRZ, HCF; destruct R; reflexivity).
  apply (srr_apost_base_liftF (fx := fx) SEGS fx); [exact (fxrel_refl fx)|].
  apply (HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdvh pos sp1 0%nat 0%nat [] HPRE HRZ).
  + rewrite HR1.
    apply (br_mid_set ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc (ms_mem ms1) mdvh (r_state R) HMID HJ).
    * intros a Ha. apply KEEPh. destruct Ha as [[Ha _] | [Ha | [Ha | Ha]]].
      -- destruct (br_rep_apart lyc Sc Wc memc mdc R O pos a HARc HRC Hin7 Ha) as [Ha1 _]. lia.
      -- lia.
      -- lia.
      -- pose proof (Z.div_pos (frame_addr lyc 7 pos + 32) 8 ltac:(lia) ltac:(lia)) as D1.
        pose proof (Z.div_le_upper_bound (frame_addr lyc 7 pos + 32) 8 (frame_addr lyc 7 pos + 32) ltac:(lia) ltac:(lia)) as D2.
        unfold shadow_of_addr, SHADOW_OFF in Ha. lia.
    * apply (aval_mem_agree (rdW Wc memc)); [intros k Hk; apply KEEPh; unfold A_G_REC, OFF_STATE; lia | exact HS4].
    * exact HRS.
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
      (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
      (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
      (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
      (br_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J27. reflexivity.
  + lia.
  + lia.
  + reflexivity.
  + rewrite J10, (br_ew_reg regs1 R 19 19%bv eq_refl), H19, Z.add_0_r. reflexivity.
  + rewrite J19, (br_ew_reg regs1 R 19 19%bv eq_refl), H19, Z.add_0_r. reflexivity.
  + rewrite J11. reflexivity.
  + rewrite J12. reflexivity.
  + rewrite J13. reflexivity.
  + rewrite J14. reflexivity.
  + intros i Hi. cbn [length] in Hi. lia.
  + exact HSTRh.
  + exact HRAh.
(* changes <> 0: mix_call (g_rec.state, c), the store of g_rec.state, then HEAD *)
- assert (HCT : chg = true).
  { rewrite branch_eq_U in Hc.
    apply Z.eqb_neq in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
    rewrite (br_ew_reg regs1 R 23 23%bv eq_refl), G23, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite HCHG.
    destruct (bv_unsigned (getr regs 12) =? 0) eqn:E0; [|reflexivity]. apply Z.eqb_eq in E0. exfalso. apply Hc.
    rewrite E0. reflexivity. }
  paj_run_tok RUN HS HJ SHOK br_Bspan.
  { br_awr_ro. }
  set (mdvm := with_vm_backing (m_vm_lazy mdvb) _ mdvb) in *; clearbody mdvm.
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha.
    rewrite <- (KEEPb a Ha).
    apply (kept_of_frame (segs:=SEGS) (br_E regs1 R) _ (w_H Wc) (ms_mem ms0) (ms_mem ms1) (fun _ => False) HFr);
      [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
  clear HF HFr HG. pmkst HS. prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3.
  prreg HS (4%bv : bv 5) M4. prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11.
  assert (HSIGMC : SIG CS_mix_call = BASE + AF_mix_call).
  { rewrite (SIGP CS_mix_call ltac:(cbn [In]; repeat first [left; reflexivity | right])).
    f_equal; try (vm_compute; reflexivity). }
  rewrite HSIGMC. assert (Rsp : spZ (ms_regs ms1) = sp1).
  { unfold spZ.
    rewrite M2, (br_ew_reg regs1 R 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (proj1 HJ) as HAR1. assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
    by exact (br_aro_journal _ _ ly S W mem md _ lyc Sc Wc _ _ _ old O R HAR HREP HJ HROD).
  pose proof (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem ms1) mdvm HAR1 HROD1) as HRO1.
  pose proof HRC as (Qc & (_ & _ & _ & (HCL1 & HCL2 & _ & HCi & HCsp & _) & _) & _).
  assert (HPK : forall P, 0 <= c < 2 ^ 32 -> acall_at (ablocks B lyc Sc) (rdW Wc memc) c e P -> acall_at (ablocks B lyc Sc) (rdW Wc (ms_mem ms1)) c e P).
  { intros P Hc32 Hcall.
    apply (acall_at_agree _ (rdW Wc memc)); [| |exact Hcall].
    - intros kk Hkk. apply KEEPc. unfold CALL_SIZE in Hkk. lia.
    - intros pn kk Hpn Hkk. destruct (acall_at_In _ _ _ _ _ pn Hcall Hpn) as [Hb _]. destruct pn as [p n].
      destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HARc Hb) as (_ & H4096 & Hceil' & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. cbn [fst snd] in *. apply KEEPc. lia. }
  assert (HSL : ((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) /\
    exists P, acall_at (ablocks B lyc Sc) (rdW Wc (ms_mem ms1)) c e P).
  { destruct (HSLOT HRZ HCT) as [(k & Hk & Ec) | (Ec & Ee)].
    - assert (Hkl : (k < length (l_calls Qc))%nat) by (rewrite HCL2; apply nth_error_Some; rewrite Hk; discriminate).
      destruct (nth_error (l_calls Qc) k) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
      destruct (HCi k e P Hk HP) as [Hcall _]. rewrite <- Ec in Hcall.
      split; [left; exists (Z.of_nat k); split; [unfold REC_CALLS_MAX; lia | exact Ec] |]. exists P.
      apply (HPK P); [rewrite Ec; unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia | exact Hcall].
    - split; [right; exact Ec|]. exists (l_spill Qc). apply HPK; [rewrite Ec; unfold A_REC_SPILL; lia|].
      rewrite Ec, Ee. exact HCsp. }
  destruct HSL as [HSL (Pc & HCALLc)]. eapply SRr_bind.
  { eapply (PaNoChain.cl_callS_na B LAWS Wc (ms_regs ms1) (ms_mem ms1) (Z_to_bv 64 (BASE + AF_mix_call)) ANSWER_STK (spZ regs) (an_FP old O)
      ly S W mem md [(7, pos)] lyc Sc mdvm 0 MIX_CALL_STK [] EV_MIX_CALL (sp1 - spZ regs) (getr (ms_regs ms1) 1)
      (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (mixcall (r_state R) (fst e) (snd e)) /\
      Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc) HJ).
    - lia.
    - exact Ho16.
    - lia.
    - unfold MIX_CALL_STK. rewrite Hes. lia.
    - unfold MIX_CALL_STK. rewrite Hes, WS. lia.
    - rewrite M3, (br_ew_reg regs1 R 3 3%bv eq_refl). exact G3.
    - rewrite M4, (br_ew_reg regs1 R 4 4%bv eq_refl). exact G4.
    - reflexivity.
    - rewrite M1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. rewrite M1, unsigned_lit_small by lia. lia.
    - intros HPN.
      assert (Ha0 : getr (ms_regs ms1) 10 = w64 (r_state R)) by (rewrite M10, (br_ew35 regs1 R); reflexivity).
      assert (Ha1 : getr (ms_regs ms1) 11 = w64 c) by (rewrite M11, (br_ew_reg regs1 R 24 24%bv eq_refl), G24; exact H10).
      assert (Hev : st_nev Sc + EV_MIX_CALL <= EV_MAX)
        by (assert (E3 : EV_ANSWER = 3) by reflexivity; rewrite E3 in HEV; unfold EV_MIX_CALL; lia).
      exact (TMIX_CALL fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdvm (r_state R) c e Pc HPN HROD1 Ha0 HRS Ha1 HSL HCALLc HRO1 Hev).
    - intros a (r & [] & _). }
  cbv beta. intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJM & HJI & HPM & HMIX & HPERM2 & -> & ->).
  replace (0 + EV_MIX_CALL) with 0 in HJM by reflexivity. rewrite M1.
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HPM (@nil nat) HSn. specialize (HSn (Forall_nil _)).
  rewrite <- restrict_mkst_fx in HSn. clear HS. rename HSn into HS. hei_havoc HS.
  assert (Ebh : base_val (havoc (br_E regs1 R) 40 (map (getr regs2) CLOB)) (Some 285%nat) = A_G_REC).
  { cbn [base_val].
    rewrite (br_ew285 _ HEIh). apply unsigned_lit_small. unfold A_G_REC. lia. }
  assert (HPGs : forall o, 944 <= o < 952 -> inFP cmd_PG (A_G_REC + o)).
  { intros o Ho.
    exists (A_G_REC, A_G_REC + 960). split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; lia]. }
  pose proof (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 285%nat) 944 952 944 952 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite Ebh;
    split; [unfold A_G_REC; lia|]; split; [unfold A_G_REC; lia|]; split; [|apply Forall_nil];
    intros o Ho; exact (PRW _ _ (HPROG B HB _ (HPGs o Ho)))) I) as HSr.
  clear HS. rename HSr into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (SHOK2 : sh_ok SEGS br_Bx br_SH (havoc (br_E regs1 R) 40 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2))
    by (unfold sh_ok, br_SH; apply Forall_nil).
  clear SHOK. rename SHOK2 into SHOK. pose proof (st_ok_pi_add_fact _ _ _ 285%nat (mkAF A_G_REC A_G_REC 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (br_ew285 _ HEIh), unsigned_lit_small by (unfold A_G_REC; lia);
    rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HSf.
  clear HS. rename HSf into HS. paj_run_to_tok RUNTO HS HJM SHOK br_Bspan AN_HEAD.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end.
    eapply awr_ok_cons_gen with (b := A_G_REC); [reflexivity | rewrite (br_ew285 _ HEIh); apply unsigned_lit_small; unfold A_G_REC; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right; right; left. split; [|split].
    - exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8).
      split; [unfold an_FP; cbn [In]; right; left; reflexivity | cbn [fst snd]; unfold OFF_STATE; lia].
    - apply (HPROG B HB). replace a with (A_G_REC + (a - A_G_REC)) by lia. apply HPGs. lia.
    - apply cif_prog_img. replace a with (A_G_REC + (a - A_G_REC)) by lia. apply HPGs. lia. }
  set (mdvs := with_vm_backing (m_vm_lazy md2) _ md2) in *; clearbody mdvs.
  assert (KEEPs : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H W2) mem2 (ms_mem ms) (fun a => A_G_REC + 944 <= a < A_G_REC + 952) HFr);
      [|exact Ha|exact Hn].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-.
    rewrite Ebh in Hrr. exact Hrr. }
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRG.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 944 8%N (SOff 44 0) HRG ltac:(rewrite (br_ew285 _ HEIh); apply unsigned_lit_small; unfold A_G_REC; lia)
    ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as HVAL.
  clear HRG HF HFr HG. set (h' := mixcall (r_state R) (fst e) (snd e)) in *.
  assert (Hh' : 0 <= h' < 2 ^ 64) by (apply mixcall_range; exact HRS).
  assert (E44 : ew (havoc (br_E regs1 R) 40 (map (getr regs2) CLOB)) 44 = getr regs2 10)
    by exact (ew_havoc_new _ 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(rewrite length_map; vm_compute; lia)).
  assert (Hst : aval_mem (rdW W2 (ms_mem ms)) (A_G_REC + OFF_STATE) 8 h').
  { apply (aval_of_val_mem SEGS (w_H W2) (ms_mem ms)).
    cbn [ms_mem restrict] in HVAL. cbn [sv_denot] in HVAL. rewrite E44, HMIX, Z.add_0_r, Z_to_bv_bv_unsigned in HVAL.
    unfold w64 in HVAL. rewrite unsigned_lit_small in HVAL by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HVAL.
    rewrite Z.mod_small in HVAL by lia. exact HVAL. }
  pmkst HS. prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (10%bv : bv 5) J10.
  prreg HS (11%bv : bv 5) J11. prreg HS (12%bv : bv 5) J12. prreg HS (13%bv : bv 5) J13. prreg HS (14%bv : bv 5) J14.
  prreg HS (19%bv : bv 5) J19.
  assert (KDOM : forall a, br_mid_dom (spZ regs) O (frame_addr lyc 7 pos) a -> rdW W2 (ms_mem ms) a = rdW Wc memc a).
  { pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    assert (Hsh32 : (frame_addr lyc 7 pos + 32) / 8 = frame_addr lyc 7 pos / 8 + 4)
      by (replace (frame_addr lyc 7 pos + 32) with (frame_addr lyc 7 pos + 4 * 8) by lia; apply Z.div_add; lia).
    pose proof (Z.div_pos (frame_addr lyc 7 pos) 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_le_upper_bound (frame_addr lyc 7 pos) 8 (frame_addr lyc 7 pos) ltac:(lia) ltac:(lia)) as D2.
    intros a Ha. assert (Hst_out : ~ (A_G_REC + 944 <= a < A_G_REC + 952)).
    { destruct Ha as [[_ Hns] | [Ha | [Ha | Ha]]].
      - unfold OFF_STATE in Hns. exact Hns.
      - unfold A_G_REC. lia.
      - intros Hg. apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos a HARc Hin7 ltac:(rewrite FB; lia)).
        apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
        split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; lia].
      - unfold shadow_of_addr, SHADOW_OFF, A_G_REC in *. lia. }
    assert (Ha64 : 0 <= a < 2 ^ 64).
    { destruct Ha as [[Ha _] | [Ha | [Ha | Ha]]].
      - destruct (br_rep_apart lyc Sc Wc memc mdc R O pos a HARc HRC Hin7 Ha) as [Ha1 _]. lia.
      - lia.
      - lia.
      - unfold shadow_of_addr, SHADOW_OFF in Ha. lia. }
    rewrite (KEEPs a Ha64 Hst_out), <- (KEEPc a Ha64). destruct Ha as [[Ha _] | [Ha | [Ha | Ha]]].
    - destruct Ha as [Ha | [Ha | (p & n & Hpn & Ha)]].
      + assert (HPG : inFP cmd_PG a)
          by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]).
        pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HARc)) (HPROG B HB a HPG)) as (Hno & Hne & _).
        apply I3; [exact (cif_prog_img a HPG) | exact Hno | exact Hne | apply fp_spares_closed; intros (r & [] & _)].
      + assert (HPG : inFP cmd_PG a)
          by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [cbn [In cmd_PG]; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]).
        pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HARc)) (HPROG B HB a HPG)) as (Hno & Hne & _).
        apply I3; [exact (cif_prog_img a HPG) | exact Hno | exact Hne | apply fp_spares_closed; intros (r & [] & _)].
      + destruct (rec_repA_O_blocks B lyc Sc _ R O (p, n) HRC Hpn) as [Hb Hn1]. cbn [snd] in Hn1.
        pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. replace a with (p + (a - p)) by lia.
        apply (I2 p n (a - p)); [exact Hb | exact Hb | lia | intros (r & [] & _)].
    - apply I1; [lia | unfold MIX_CALL_STK; rewrite Hes; lia | intros (r & [] & _)].
    - apply (I4 7 pos a Hin7); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FB; lia | intros (r & [] & _)].
    - apply (I4 7 pos a Hin7); [right | intros (r & [] & _)]. unfold in_zr, shadow_addr; cbn [fst snd]; rewrite FB.
      change (8192 / 8) with 1024. unfold shadow_of_addr in Ha. rewrite Hsh32 in Ha. lia. }
  rewrite nth_overflow in J27 by (rewrite length_map; vm_compute; lia). rewrite (br_ew285 _ HEI) in J27.
  change (BASE + 16780) with (BASE + AN_HEAD).
  destruct (br_shape_at ANSWER_STK (spZ regs) [(7, pos)] ly S W mem md lyc Sc W2 (ms_mem ms) mdvs 0 old O R sh x
    HAR HREP HJM HPERM HROD HARG) as [HSTRh HRAh].
  assert (HR1 : an_R1 R e chg = set_state R h') by (unfold an_R1; rewrite HRZ, HCT; reflexivity).
  apply (srr_apost_base_liftF (fx := fx) SEGS fx); [exact (fxrel_refl fx)|].
  apply (HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc W2 (ms_regs ms) (ms_mem ms) mdvs pos sp1 0%nat 0%nat [] HPRE HRZ).
  + rewrite HR1.
    exact (br_mid_set ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 W2 (ms_mem ms) mdvs h' HMID HJM KDOM Hst Hh').
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
      (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
      (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
      (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
      (br_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J27. reflexivity.
  + lia.
  + lia.
  + reflexivity.
  + rewrite J10, (br_ew_reg regs1 R 19 19%bv eq_refl), H19, Z.add_0_r. reflexivity.
  + rewrite J19, (br_ew_reg regs1 R 19 19%bv eq_refl), H19, Z.add_0_r. reflexivity.
  + rewrite J11. reflexivity.
  + rewrite J12. reflexivity.
  + rewrite J13. reflexivity.
  + rewrite J14. reflexivity.
  + intros i Hi. cbn [length] in Hi. lia.
  + exact HSTRh.
  + exact HRAh. Qed.
End m.
End f.
End d.
