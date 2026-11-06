(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the BODY segment of answer's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8ab6c .. 0x8aca4 / 0x8ab98), the B re-walk of lib/A/Prog/answer_br.v
   (a working branch d28426fbb96): `auipc/addi s11 = g_rec`, `lw a0,0(s11)` (g_rec.refuse) and the refusal
   branch `beqz a0` at 0x8ab78.
   Refused (a0 <> 0): `lw a3,4(s11)` (g_rec.code), a2 = "resp %d" (0x21d40), a1 = 4096, a0 = buf (s5 = frame + 32),
   `jal snprintf` at 0x8ab90 under the SHARED snprintf contract (lib/B/Rt/RtFormat.v asnprintf_realizes; the step
   is lib/B/Prog/answer_snp.v's aj_snprintf_frameF), whose post is FP-existential: PaFx.v's srr_after_artF continues
   at the FP state fx1 the call returns, with an_join_j (the `j 0x8aca4` at 0x8ab94 and the cut point JOIN, at fx1;
   an_pre at fx1 by an_pre_fx, its rounding mode from the call's post by fxrel_frm0).
   Not refused (a0 = 0): the branch is taken to 0x8ab98, from where lib/B/Prog/answer_bm.v's an_body_nr walks the
   changes branch, mix_call, the store of g_rec.state, the UBSan trap site 0x8abac and the loop setup to HEAD.
   The refusal branch has no report or trap edge; this segment's only edges are the two arms. The frame above the
   image is a Theorem Labs lane's lib/B/Rt/RtPFDog.v pa_frame_above_img and the realignment's arithmetic CmdSnText.v's
   snt_sp1_facts; the snprintf destination's band premise (`+ 8`, a Theorem Labs lane fc8bcbd8b42) is answer_snp.v's, from the
   room the class-7 frame leaves after buf's 4096 bytes. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFShared RtPFCmd RtPFSx RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
mix_call_c hand_back_c answer_c answer_s1 answer_snp answer_bm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* awr_ok over a state whose regions are all read-only *)
Ltac br_awr_ro :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end;
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* the model term after a symbolic run, named *)
Ltac br_name_md md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md := m) in *; clearbody md end.

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

Lemma val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. change (bv_modulus 8) with 256.
rewrite Z.mod_small; [reflexivity | exact Hrange].
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

(* a register of the walk's environment is the register of the state the env was built from *)
Lemma br_ew_reg : forall regs R (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (br_E regs R) n = getr regs r.
Proof.
intros regs R n r H. unfold br_E.
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr; unfold A_TEXT; lia).
apply ew_Ereg_nat. exact H.
Qed.
(* the symbolic state after the snprintf call returns (0x8ab94, `j 0x8aca4`): every register its own atom, no
   region *)
Lemma brj_seed : forall (W : world SEGS) (regs1 : bvmap 5 word) mem R,
st_ok_pi SEGS VAL (br_E regs1 R) (mkSS (AN_SNP + 4) sr_atoms [] None br_facts)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + (AN_SNP + 4))) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem R. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold br_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; [exact I | exact I]].
  cbn [br_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite br_ew32, unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. unfold SB. repeat split; lia.
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma br_kept_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HFR Hw a. apply (aview_eq_of SEGS). apply HFR. intros Hin.
destruct (in_wrange_windows E rs _ Hin) as (b & wlo & whi & Hi & Hr).
unfold windows in Hi. apply in_map_iff in Hi as (r & Hq & Hr2). injection Hq as <- <- <-.
rewrite forallb_forall in Hw. specialize (Hw r Hr2). apply Z.leb_le in Hw. lia.
Qed.
(* the bytes a shared printf post leaves, as the bytes of a list of bytes *)
Lemma br_abytes_of_view : forall H (mem : word -> option byte) p (T : list Z),
(forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS H mem (p + i) = Some (nth (Z.to_nat i) T 0)) ->
abytes_atR (aview SEGS H mem) p (map (Z_to_bv 8) T).
Proof.
intros H mem p T HT i Hi. rewrite length_map in Hi.
pose proof (HT (Z.of_nat i) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. rewrite Hb. f_equal.
assert (Hr : 0 <= nth i T 0 < 256).
{ unfold aview in Hb. destruct (mbyte SEGS (mrestrict H mem) (p + Z.of_nat i)) as [b|]; cbn [option_map] in Hb; [|discriminate].
  injection Hb as Hb. rewrite <- Hb. pose proof (bv_unsigned_in_range 8 b) as Hq. change (bv_modulus 8) with 256 in Hq. exact Hq. }
rewrite (map_nth (Z_to_bv 8) T 0 i). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small; [reflexivity | exact Hr].
Qed.

(* the shadow bytes of buf lie outside buf and below the machine stack *)
Lemma br_shadow_apart : forall F i sp1, in_app F 8192 -> F + 8192 <= alloc_ceiling -> alloc_ceiling <= sp1 - 8192 ->
0 <= i < 512 ->
0 <= shadow_of_addr SHADOW_OFF (F + 32) + i < 2 ^ 64 /\
~ (F + 32 <= shadow_of_addr SHADOW_OFF (F + 32) + i < F + 32 + 4096) /\
~ (sp1 - 8192 <= shadow_of_addr SHADOW_OFF (F + 32) + i < sp1).
Proof.
intros F i sp1 Happ Hce Hsp Hi. pose proof ASAN_CEIL_range as [CR _].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold ASAN_CEIL in CR.
unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_mod (F + 32) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)) as M.
lia.
Qed.

Section j.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
(* an_mid at a later state of the same world whose bytes are all the earlier state's *)
Lemma br_mid_all : forall ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 (Wc' : world SEGS) memc' mdc',
an_mid B MT ly S W regs mem md R old O lyc Sc Wc memc mdc pos 0 sp1 ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc' memc' mdc' 0 ->
(forall a, rdW Wc' memc' a = rdW Wc memc a) ->
an_mid B MT ly S W regs mem md R old O lyc Sc Wc' memc' mdc' pos 0 sp1.
Proof.
intros ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc' memc' mdc' HM HJ' HK.
pose proof HM as (HJ & HMOLE & HPERM & HSP1 & HSAVED & HFLAG & HZS & HRC & HOLDC).
unfold an_mid. split; [exact HJ'|]. split; [exact HMOLE|]. split; [exact HPERM|]. split; [exact HSP1|].
split; [intros j r Hj; apply (aval_mem_agree (rdW Wc memc)); [intros k _; apply HK | exact (HSAVED j r Hj)]|].
split; [rewrite (rdword_ext (rdW Wc memc) (rdW Wc' memc')); [exact HFLAG | intros k _; apply HK]|].
split; [intros i Hi; rewrite HK; exact (HZS i Hi)|].
split; [apply (rec_repA_keep B lyc Sc (rdW Wc memc) _ R O HRC); intros a _; apply HK|].
apply (aval_mem_agree (rdW Wc memc)); [intros k _; apply HK | exact HOLDC].
Qed.
(* the cut point JOIN reached from 0x8ab94 (`j 0x8aca4`, the refused arm after snprintf returns) *)
Lemma an_join_j : AN_JOIN_stmt B MT ->
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1,
an_pre B MT ly S W regs mem md ch c sh old e x chg R O ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) ->
getr regs1 27 = w64 A_G_REC ->
astr_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) (snd (rec_answer R e x chg)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AN_SNP + 4))) memc (seg_rom SEGS)) mdc)
(an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros HJOIN ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HMID HREGS H27 HSTR.
pose proof HMID as (HJ & _).
pose proof (brj_seed Wc regs1 memc R) as HS. pose proof (br_img regs1 R) as HEI.
assert (SHOK : sh_ok SEGS br_Bx br_SH (br_E regs1 R) (mrestrict (w_H Wc) memc)) by (unfold sh_ok, br_SH; apply Forall_nil).
paj_run_to_tok RUNTO HS HJ SHOK br_Bspan AN_JOIN.
{ br_awr_ro. }
br_name_md mdv.
pose proof (br_kept_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEEP.
clear HF HFr HG. pmkst HS.
prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
change (BASE + 18292) with (BASE + AN_JOIN).
apply (HJOIN ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv pos sp1 HPRE).
- exact (br_mid_all ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos sp1 Wc (ms_mem ms) mdv HMID HJ KEEP).
- unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
  rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
    (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
    (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
    (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
    (br_ew_reg regs1 R 26 26%bv eq_refl).
  exact HREGS.
- rewrite J27, (br_ew_reg regs1 R 27 27%bv eq_refl). exact H27.
- apply (astr_atR_agree (rdW Wc memc)); [intros k _; apply KEEP | exact HSTR].
Qed.
End j.
End f.
End d.

(* an_pre at the FP state a call returns: only its rounding-mode conjunct (the sixteenth) names the FP state *)
Section x. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
Variable B : asyms.
Variable MT : ameter_ops.
Lemma an_pre_fx : forall (fxa fxb : YK11.FPState) ly S W regs mem md ch c sh old e x chg R O,
an_pre (fx := fxa) B MT ly S W regs mem md ch c sh old e x chg R O -> frm0 fxb ->
an_pre (fx := fxb) B MT ly S W regs mem md ch c sh old e x chg R O.
Proof.
intros fxa fxb ly S W regs mem md ch c sh old e x chg R O
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _) Hf.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
  (conj H12 (conj H13 (conj H14 (conj H15 Hf))))))))))))))).
Qed.
End x.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses this segment uses (answer_c.v:94, :99, :100), in the statement's forall-fx0 form;
   TMIX_CALL is answer_bm.v's (the not-refused arm) *)
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses (WORKER-BRIEF.md): the allocator record, the program functions' call targets and the
   program statics' write window (answer_bm.v's: mix_call's target, the store of g_rec.state), and a Theorem Labs lane's image facts
   (CmdRecImg.v cmd_img_facts_tfib) at these segments *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RRO : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RRO (SK := SK) SEGS B LAWS HB IMG.
Let RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a := CmdRecRo.RPG (SK := SK) SEGS B LAWS HB IMG.
Let PGI : forall a, inFP cmd_PG a -> in_img SEGS a := cif_prog_img _ _ IMG.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma br_ew288 : forall regs R, ew (br_E regs R) 288%nat = Z_to_bv 64 0x21d40.
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
  { apply PGI. exists (A_G_REC, A_G_REC + 960). split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]. }
  exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos a HAR Hin Hf Hi).
- split; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|]. intros Hf.
  assert (Hi : in_img SEGS a).
  { apply PGI. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [cbn [In cmd_PG]; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]. }
  exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos a HAR Hin Hf Hi).
- destruct (rec_repA_O_blocks B lyc Sc _ R O (p, n) HR Hpn) as [Hb Hn1]. cbn [snd] in Hn1.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hb) as (_ & H4096 & Hceil & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
  split; [lia|]. intros Hf.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 7 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the BODY cut (0x8ab6c, after the two shadow fills) reaches JOIN at the FP state snprintf returns (refusal) or
   0x8ab98, an_body_nr's start (no refusal) *)
Lemma an_body_ok : (forall fx1 : YK11.FPState, AN_JOIN_stmt (fx := fx1) B MT) -> AN_HEAD_stmt B MT -> AN_BODY_stmt B MT.
Proof.
intros HJOIN HHEAD. unfold AN_BODY_stmt.
intros ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HMID HREGS H19.
pose proof HPRE as (HFN & HFRL & HROD & HRO & H10 & H11 & HCHG & HREP & HOLD & HSHP & HSLOT & HEV & HLIVE & HMO & HRNG & HFRM).
pose proof HMID as (HJ & HMOLE & HPERM & HSP1 & HSAVED & HFLAG & HZS & HRC & HOLDC).
pose proof HREGS as (G2 & G3 & G4 & G8 & G9 & G18 & G25 & G20 & G21 & G22 & G23 & G24 & G26).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hch & HQT0).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & F5 & Hpresw & Hstk & F6 & HQT).
pose proof Hstk as (Hal16 & Hstk1 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (br_seed B VOBJS Wc lyc Sc regs1 memc R O HRC) as HS.
pose proof (br_img regs1 R) as HEI.
assert (SHOK : sh_ok SEGS br_Bx br_SH (br_E regs1 R) (mrestrict (w_H Wc) memc)) by (unfold sh_ok, br_SH; apply Forall_nil).
unfold an_post. paj_run_tok RUN HS HJ SHOK br_Bspan.
{ br_awr_ro. }
br_name_md mdv.
pose proof (br_kept_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEEP0.
clear HF HFr HG.
pose proof HRC as (Q0 & (_ & _ & _ & _ & _ & _ & (HS1 & HS2 & HS3 & HS4 & HS5 & HRR & HRCD & HRN & HRS & HRH) & _) & _).
assert (WS : ANSWER_STK = ltac:(let v := eval vm_compute in ANSWER_STK in exact v)) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. assert (HK8 : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
pose proof (CmdSnText.snt_sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hs1a & Hs1b & Hs1c).
rewrite <- HSP1 in Hs1a, Hs1b, Hs1c.
assert (Ho16 : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hal16, Hs1c; reflexivity).
assert (Hin7 : In (7, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf32 & Hfapp & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf4096 & Hfceil & _).
pose proof (RtPFDog.pa_frame_above_img (PI := PI) B lyc Sc Wc memc mdc 7 pos HARc Hin7) as Hfimg. unfold RtPFCmd.CMD_IMG_HI in Hfimg.
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity. rewrite FB in Hfceil, Hfapp.
psrr_branch_tok RUN BR HS SHOK br_Bspan.
(* refuse = 0 (0x8ab78 taken): 0x8ab98, an_body_nr's start *)
- assert (HRZ : r_refuse R = 0).
  { rewrite branch_eq_U in Hc.
    apply Z.eqb_eq in Hc. unfold U at 1 in Hc.
    apply (proj1 (br_sext32_zero (br_E regs1 R) 33 (r_refuse R) (br_ew33 regs1 R) HRR)). rewrite Hc. reflexivity. }
  clear Hc. paj_run_to_tok RUNTO HS HJ SHOK br_Bspan 0x4668.
  { br_awr_ro. }
  br_name_md mdvb.
  pose proof (br_kept_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEEPb.
  clear HF HFr HG. pmkst HS.
  prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (19%bv : bv 5) J19.
  rewrite (br_ew285 _ HEI) in J27. change (BASE + 18024) with (BASE + 0x4668).
  apply (an_body_nr B MT TMIX_CALL HB cmd_sig_prog_PB PRW cmd_img_facts_tfib HHEAD ly S W regs mem md ch c sh old e x chg R O
    lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdvb pos sp1 HPRE HRZ).
  + apply (br_mid_all B MT ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc (ms_mem ms0) mdvb HMID HJ).
    intros a. rewrite KEEPb. exact (KEEP0 a).
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
      (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
      (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
      (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
      (br_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J19, (br_ew_reg regs1 R 19 19%bv eq_refl). exact H19.
  + rewrite J27. reflexivity.
(* refuse <> 0 (0x8ab78 not taken): snprintf (buf, 4096, "resp %d", g_rec.code), then `j 0x8aca4` to JOIN *)
- assert (HRF : r_refuse R <> 0).
  { intros H0.
    rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold U at 1.
    rewrite (proj2 (br_sext32_zero (br_E regs1 R) 33 (r_refuse R) (br_ew33 regs1 R) HRR) H0). reflexivity. }
  paj_run_tok RUN HS HJ SHOK br_Bspan.
  { br_awr_ro. }
  br_name_md mdv2.
  pose proof (br_kept_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEEPr.
  assert (KEEP1 : forall a, rdW Wc (ms_mem ms0) a = rdW Wc memc a) by (intros a; rewrite KEEPr; exact (KEEP0 a)).
  clear HF HFr HG KEEPr. pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
  rewrite (br_ew285 _ HEI) in J27.
  assert (Rsp : spZ (ms_regs ms0) = sp1).
  { unfold spZ. rewrite P2, (br_ew_reg regs1 R 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (proj1 HJ) as HAR0.
  assert (HROD0 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms0)))
    by exact (br_aro_journal _ _ ly S W mem md _ lyc Sc Wc _ _ _ old O R HAR HREP HJ HROD).
  pose proof (CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG lyc Sc Wc (ms_mem ms0) mdv2 HAR0 HROD0) as HRO0.
  assert (HLIT : abytes_atR (rdW Wc (ms_mem ms0)) 0x21d40 RO_lit_21d40).
  { clear - HRO0.
    destruct HRO0 as [HRO0 _]. unfold cmd_ro_bytes in HRO0. repeat match type of HRO0 with
      | abytes_atR _ 0x21d40 _ /\ _ => exact (proj1 HRO0) | _ /\ _ => apply proj2 in HRO0 end. }
  set (T := RecAns.RESP_HEAD ++ PF.pf_dec (r_code R)).
  assert (HT16 : (length T <= 16)%nat) by (pose proof (RecAns.resp_len (r_code R) HRCD); unfold T; lia).
  assert (EW : RtPFShared.sn_len (4096 - 1) T = Z.of_nat (length T) + 1).
  { unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. lia. }
  assert (EB : RtPFShared.sn_bytes (4096 - 1) T = T ++ [0]).
  { unfold RtPFShared.sn_bytes. rewrite firstn_all2 by lia. reflexivity. }
  assert (HF8 : (frame_addr lyc 7 pos + 32) mod 8 = 0).
  { pose proof (Z.div_mod (frame_addr lyc 7 pos) 32 ltac:(lia)) as D.
    rewrite Hf32, Z.add_0_r in D. rewrite D.
    replace (32 * (frame_addr lyc 7 pos / 32) + 32) with ((4 * (frame_addr lyc 7 pos / 32) + 4) * 8) by lia.
    apply Z_mod_mult. }
  assert (HZA : range_addressable (rdW Wc (ms_mem ms0)) SHADOW_OFF (frame_addr lyc 7 pos + 32) 4096).
  { apply zero_shadow_range; [exact HF8 | reflexivity |]. intros i Hi. rewrite KEEP1. exact (HZS i Hi). }
  eapply srr_after_artF.
  { apply (aj_snprintf_frameF (fx := fx) B ASNPRINTF HB cmd_img_facts_tfib Wc (ms_regs ms0) (ms_mem ms0) ANSWER_STK
      (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc mdv2 0 (frame_addr lyc 7 pos + 32) 4096 0x21d40 T
      (sp1 - spZ regs) (Z_to_bv 64 (BASE + (AN_SNP + 4))) 7 pos).
    - exact HJ.
    - rewrite Rsp. lia.
    - exact Ho16.
    - lia.
    - rewrite HK8, WS. lia.
    - rewrite P3, (br_ew_reg regs1 R 3 3%bv eq_refl). exact G3.
    - rewrite P4, (br_ew_reg regs1 R 4 4%bv eq_refl). exact G4.
    - rewrite P1. reflexivity.
    - apply ret_ok_codeptr_v; [unfold AN_SNP; lia | reflexivity].
    - rewrite P10, (br_ew_reg regs1 R 21 21%bv eq_refl), G21. reflexivity.
    - rewrite P11. reflexivity.
    - rewrite P12, br_ew288. reflexivity.
    - exact HROD0.
    - apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ RecAns.RESP_FMT RecAns.RESP_PS [PF.AInt (r_code R)]).
      + split; [lia|]. split.
        { intros i Hi. change (Z.of_nat (length RecAns.RESP_FMT)) with 7 in Hi.
          assert (Hk : (Z.to_nat i < 8)%nat) by lia.
          pose proof (HLIT (Z.to_nat i) ltac:(change (length RO_lit_21d40) with 8%nat; exact Hk)) as Hb.
          rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal. clear - Hk.
          destruct (Z.to_nat i) as [|[|[|[|[|[|[|[|k]]]]]]]] eqn:Ei; first [vm_compute; reflexivity | lia]. }
        change (Z.of_nat (length RecAns.RESP_FMT) + 1) with 8.
        split; [apply an_snp_img_apart; [lia | lia | rewrite HK8, Rsp; lia | lia]|].
        split; [left; unfold kLowMemEnd; lia|].
        exact (CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB lyc Sc Wc (ms_mem ms0) mdv2 0x21d40 8 HAR0
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      + exact RecAns.resp_parse.
      + cbn [map RtPFCmd.arg_of RtPFShared.pf_args_asan RtPFShared.pf_arg_asan app]. split; [|exact I].
        split; [exact HRCD|]. unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
        rewrite P13, <- (br_sext_off (br_E regs1 R) 34).
        exact (br_sext32_mod (br_E regs1 R) 34 (r_code R) (br_ew34 regs1 R) HRCD).
      + exact (RecAns.resp_text (r_code R)).
      + cbn. exact I.
      + (* fr_lit_ok (a Theorem Labs lane 0934cb146c3, recipe E.0.4): "resp %d" at 0x21d40 in the image below the GOT word, nonempty,
           no %s argument *)
        vm_compute; reflexivity.
    - lia.
    - lia.
    - left. reflexivity.
    - lia.
    - rewrite EW, FB. lia.
    - rewrite EW. intros y Hy. apply HZA. lia.
    - exact HFRM. }
  cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HRES & HBYTES) & HKEEP).
  assert (HR1 : an_R1 R e chg = R) by (unfold an_R1; rewrite (proj2 (Z.eqb_neq _ _) HRF); reflexivity).
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos + 32 <= a < frame_addr lyc 7 pos + 32 + 4096) ->
    ~ (sp1 - 8192 <= a < sp1) -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha H1 H2. rewrite (HKEEP a Ha); [exact (KEEP1 a) | rewrite HK8; lia | rewrite EW; lia]. }
  assert (Q2 : getr regs2 2 = getr (ms_regs ms0) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (Q3 : getr regs2 3 = getr (ms_regs ms0) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (Q4 : getr regs2 4 = getr (ms_regs ms0) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (Q8 : getr regs2 8 = getr (ms_regs ms0) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (Q9 : getr regs2 9 = getr (ms_regs ms0) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (Q18 : getr regs2 18 = getr (ms_regs ms0) 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (Q20 : getr regs2 20 = getr (ms_regs ms0) 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
  assert (Q21 : getr regs2 21 = getr (ms_regs ms0) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (Q22 : getr regs2 22 = getr (ms_regs ms0) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  assert (Q23 : getr regs2 23 = getr (ms_regs ms0) 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (Q24 : getr regs2 24 = getr (ms_regs ms0) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
  assert (Q25 : getr regs2 25 = getr (ms_regs ms0) 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
  assert (Q26 : getr regs2 26 = getr (ms_regs ms0) 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
  assert (Q27 : getr regs2 27 = getr (ms_regs ms0) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  apply (an_join_j (fx := fx1) B MT (HJOIN fx1) ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs2 mem2 md2 pos sp1).
  + exact (an_pre_fx B MT fx fx1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE (fxrel_frm0 fx fx1 HFRM Hfx)).
  + rewrite HR1. unfold an_mid. split; [exact HJ2|]. split; [exact HMOLE|]. split; [exact HPERM|].
    split; [exact HSP1|]. split.
    { intros j r Hj.
      assert (Hj13 : (j < length an_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      cbn [length an_saved] in Hj13. apply (aval_mem_agree (rdW Wc memc)); [|exact (HSAVED j r Hj)]. intros k Hk.
      apply KEEPJ; lia. }
    split.
    { rewrite FB. rewrite FB in HFLAG. rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem2)); [exact HFLAG|]. intros k Hk.
      apply KEEPJ; lia. }
    split.
    { intros i Hi. change (4096 / 8) with 512 in Hi.
      destruct (br_shadow_apart (frame_addr lyc 7 pos) i sp1 Hfapp Hfceil ltac:(rewrite WS in Hslo; lia) Hi) as (S1 & S2 & S3).
      rewrite KEEPJ; [exact (HZS i ltac:(change (4096 / 8) with 512; lia)) | exact S1 | exact S2 | exact S3]. }
    split.
    { apply (rec_repA_keep B lyc Sc (rdW Wc memc) _ R O HRC).
      intros a Ha. destruct (br_rep_apart lyc Sc Wc memc mdc R O pos a HARc HRC Hin7 Ha) as [Ha1 Ha2].
      rewrite FB in Ha2. apply KEEPJ; lia. }
    { apply (aval_mem_agree (rdW Wc memc)); [|exact HOLDC].
      intros k Hk.
      assert (Hra' : rep_addr O (A_G_REC + OFF_ANSWER + k)) by (left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia).
      destruct (br_rep_apart lyc Sc Wc memc mdc R O pos _ HARc HRC Hin7 Hra') as [Ha1 Ha2]. rewrite FB in Ha2.
      apply KEEPJ; lia. }
  + unfold an_regs_body. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q25, Q20, Q21, Q22, Q23, Q24, Q26.
    rewrite P2, P3, P4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (br_ew_reg regs1 R 2 2%bv eq_refl), (br_ew_reg regs1 R 3 3%bv eq_refl), (br_ew_reg regs1 R 4 4%bv eq_refl),
      (br_ew_reg regs1 R 8 8%bv eq_refl), (br_ew_reg regs1 R 9 9%bv eq_refl), (br_ew_reg regs1 R 18 18%bv eq_refl),
      (br_ew_reg regs1 R 25 25%bv eq_refl), (br_ew_reg regs1 R 20 20%bv eq_refl), (br_ew_reg regs1 R 21 21%bv eq_refl),
      (br_ew_reg regs1 R 22 22%bv eq_refl), (br_ew_reg regs1 R 23 23%bv eq_refl), (br_ew_reg regs1 R 24 24%bv eq_refl),
      (br_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite Q27, J27. reflexivity.
  + unfold rec_answer. rewrite (proj2 (Z.eqb_neq _ _) HRF). cbn [snd hand_back].
    split; [|exact (resp_no0 (r_code R))].
    rewrite <- (RecAns.pf_resp (r_code R) HRCD). change (RecAns.RESP_HEAD ++ PF.pf_dec (r_code R)) with T.
    unfold PF.pf_bytes. replace (map (Z_to_bv 8) T ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (T ++ [0])) by (rewrite map_app; reflexivity).
    apply br_abytes_of_view. intros i Hi. rewrite <- EB. apply HBYTES. rewrite EW. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.
End e.
End f.
End d.
