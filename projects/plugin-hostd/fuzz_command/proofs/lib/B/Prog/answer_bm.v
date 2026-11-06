(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the not-refused part of the BODY segment of answer's ASan+UBSan walk
   (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan, 0x8ab98 .. 0x8abcc): the test of the changes (0x8ab98
   `beqz s7`), the mix_call of the changes (0x8ab9c .. 0x8aba4, `ld a0,944(s11)`, `mv a1,s8`, `jal mix_call`) and
   the store of g_rec.state (0x8aba8), the UBSan trap test of the shape pointer (0x8abac `beqz s3`, to the `unimp` at
   0x8ad30; refuted: an_pre's shape premise astr_argA gives sh <> 0), and the setup of syntax_instantiate's loop
   (0x8abb0 .. 0x8abc8), up to the cut point HEAD of lib/B/Prog/answer_s1.v (0x8abcc) with j = d = 0 and out = [].
   The B twin of the mix_call arm and the loop setup of lib/A/Prog/answer_br.v (a working branch d28426fbb96,
   A 0x8a648 .. 0x8a670); the helper lemmas are A's with a bm_ prefix. Changes from A: the walk starts at 0x8ab98
   with s11 = g_rec in a register (A's walk starts at 0x8a61c and computes s11 by auipc), so the seed's g_rec region
   is based at s11's atom; B's code has the UBSan test 0x8abac and B's loop registers (AN_HEAD_stmt's); the callee
   contract is taken at every FP state and used at the ambient one; the record facts are a Theorem Labs lane's CmdRecFacts lemmas
   over cmd_img_facts_tfib's statement at this walk's segments, the program statics' record fact CmdRecAns.v's
   rca_HPROG, and the seed environment and the realignment's arithmetic CmdSnText.v's snt_E / snt_sp1_facts. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
mix_call_c hand_back_c answer_c PaFx CmdRecBase CmdRecCells CmdRecRo CmdRecRest answer_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdSnText CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- generic helpers over the reader (A's answer_br.v) ---- *)
Lemma bm_aval_mem_agree : forall (rd rd' : reader) a n v,
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) ->
aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK (Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma bm_abytes_atR_agree : forall (rd rd' : reader) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> rd' (a + k) = rd (a + k)) ->
abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite (HK (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma bm_astr_atR_agree : forall (rd rd' : reader) p s,
(forall k, 0 <= k <= Z.of_nat (length s) -> rd' (p + k) = rd (p + k)) ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s HK [H1 H2]. split; [|exact H2]. apply (bm_abytes_atR_agree rd rd'); [|exact H1].
intros k Hk. rewrite length_app in Hk. cbn [length] in Hk. apply HK. lia.
Qed.

Lemma bm_aval_of_val_mem : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* a chunk whose value is any 64-bit atom, read at the width of w bytes *)
Lemma bm_chunk_ok_any : forall segs E mem base off (n : N) (e : sv),
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

Lemma bm_in_filter : forall (old : Z) (O : list (Z * Z)) x,
In x (filter (fun pn => fst pn =? old) O) -> In x O /\ fst x = old.
Proof.
intros old O x H. apply (proj2 (list_elem_of_In _ _)) in H. apply list_basics.list.list_elem_of_filter in H as [Hp H].
apply list_elem_of_In in H. split; [exact H|]. apply Is_true_eq_true in Hp. apply Z.eqb_eq. exact Hp.
Qed.

(* ---- the addresses the recorder's representation reads ---- *)
Definition bm_rep_addr (O : list (Z * Z)) (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists p n, In (p, n) O /\ p <= a < p + n).

Lemma bm_acall_at_agree : forall bl (rd rd' : reader) a c P,
(forall k, 0 <= k < CALL_SIZE -> rd' (a + k) = rd (a + k)) ->
(forall pn k, In pn P -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl rd a c P -> acall_at bl rd' a c P.
Proof.
intros bl rd rd' a c P HA HB (H1 & H2 & H3 & H4 & H5 & H6 & H7).
assert (HA' : forall d k, 0 <= d -> 0 <= k -> d + k < CALL_SIZE -> rd' (a + d + k) = rd (a + d + k)).
{ intros d k Hd Hk Hdk. replace (a + d + k) with (a + (d + k)) by lia. apply HA. lia. }
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA'; unfold CALL_OFF_FN, CALL_SIZE in *; lia | exact H4]|].
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA'; unfold CALL_OFF_NARGS, CALL_SIZE in *; lia | exact H5]|].
split; [exact H6|].
intros k s pn Hk Hp. destruct (H7 k s pn Hk Hp) as (G1 & G2 & G3 & G4 & G5).
assert (Hin : In pn P) by (eapply nth_error_In; exact Hp).
assert (Hk6 : (k < length (snd c))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
assert (Hkl : (k < length P)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hp; discriminate).
split; [apply (bm_aval_mem_agree rd rd');
  [intros j Hj; replace (a + CALL_OFF_ARGS + 8 * Z.of_nat k + j) with (a + (CALL_OFF_ARGS + 8 * Z.of_nat k) + j) by lia;
   apply HA'; unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact G1]|].
split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
apply (bm_astr_atR_agree rd rd'); [|exact G5]. intros j Hj. apply HB; [exact Hin | lia].
Qed.

Lemma bm_aanswer_at_agree : forall bl (rd rd' : reader) gr t q,
(forall k, 0 <= k < 8 -> rd' (gr + OFF_ANSWER + k) = rd (gr + OFF_ANSWER + k)) ->
(forall pn k, q = Some pn -> 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
aanswer_at bl rd gr t q -> aanswer_at bl rd' gr t q.
Proof.
intros bl rd rd' gr t q HA HB H. destruct t as [x|]; destruct q as [pn|]; try exact H.
- destruct H as (G1 & G2 & G3 & G4 & G5 & G6).
  split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
  apply (bm_astr_atR_agree rd rd'); [|exact G5]. intros j Hj. apply (HB pn j eq_refl). lia.
- apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact H].
Qed.

Lemma bm_areply_at_agree : forall bl (rd rd' : reader) gr y q,
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
  split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HS; lia | exact G2]|].
  split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [|exact G8].
  apply (bm_abytes_atR_agree rd rd'); [|exact G7]. intros j Hj. apply (HB pn j eq_refl). lia.
- destruct H as [G1 G2].
  split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HA; lia | exact G1]|].
  apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply HS; lia | exact G2].
Qed.

(* the not of a 64-bit atom: `xori rd,rs,-1` *)
Lemma bm_U_not : forall E n x z, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> zcanon z = 2 ^ 64 - 1 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit z)) = 2 ^ 64 - 1 - x.
Proof.
intros E n x z Hn Hx Hz. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit, Hz.
rewrite YI08.lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma bm_val_mem_mod : forall segs m a n v v',
v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) -> val_mem segs m a n v -> val_mem segs m a n v'.
Proof.
intros segs m a n v v' Hm H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YO0f.le_byte. rewrite Hm. reflexivity.
Qed.
(* awr_ok over a state whose regions are all read-only *)
Ltac bm_awr_ro :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end;
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

(* a register of the symbolic state, without normalising its value *)
Ltac bm_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* the machine state the last run left *)
Ltac bm_ms m := lazymatch goal with |- SRr _ _ (mkCfg ?x _) _ => rename x into m end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e0.
Variable B : asyms.

Lemma bm_acall_at_In : forall bl (rd : reader) a c P pn,
acall_at bl rd a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P pn (H1 & H2 & H3 & _ & _ & _ & H7) Hin.
apply In_nth_error in Hin as (k & Hk).
assert (Hk' : (k < length P)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hk; discriminate).
rewrite H3 in Hk'.
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (H7 k s pn Hs Hk) as (_ & _ & Hb & Hlen & _). split; [exact Hb | lia].
Qed.

Lemma bm_rep_O_blocks : forall ly S (rd : reader) R O pn,
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
  destruct (HCi i c P Hc Hi) as [Hcall _]. exact (bm_acall_at_In _ _ _ _ _ _ Hcall Hpn).
- apply in_app_or in Hin as [Hin | Hin].
  + exact (bm_acall_at_In _ _ _ _ _ _ Hsp Hin).
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
Lemma bm_rep_set_state : forall ly S (rd rd' : reader) R O h,
rec_repA B ly S rd R O ->
(forall a, bm_rep_addr O a -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
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
  split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_NCALLS k); unfold OFF_NCALLS, REC_SIZE, OFF_STATE; lia | exact HN]|].
  split.
  - intros i c P Hi Hp. destruct (HCi i c P Hi Hp) as [Hcall Hfa]. split; [|exact Hfa].
    assert (Hi' : (i < length (r_calls R))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
    assert (HPO : forall pn, In pn P -> In pn O).
    { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. left. apply in_concat.
      exists P. split; [eapply nth_error_In; exact Hp | exact Hpn]. }
    apply (bm_acall_at_agree _ rd rd'); [| |exact Hcall].
    + intros k Hk. replace (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + k)
        with (A_G_REC + (OFF_CALLS + CALL_SIZE * Z.of_nat i) + k) by lia.
      apply HKg; unfold OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_STATE in *; lia.
    + intros pn k Hpn Hk. apply HKb; [exact (HPO pn Hpn) | exact Hk].
  - split; [|exact HF].
    assert (HPO : forall pn, In pn (l_spill Q) -> In pn O).
    { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
    apply (bm_acall_at_agree _ rd rd'); [| |exact Hsp].
    + intros k Hk. apply HKs. unfold CALL_SIZE, SC_SIZE in *. lia.
    + intros pn k Hpn Hk. apply HKb; [exact (HPO pn Hpn) | exact Hk]. }
split.
{ apply (bm_aanswer_at_agree _ rd rd'); [| |exact HA].
  - intros k Hk. apply (HKg OFF_ANSWER k); unfold OFF_ANSWER, REC_SIZE, OFF_STATE; lia.
  - intros pn k Hq Hk. apply HKb; [|exact Hk]. apply HO. unfold lay_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Hq. left. reflexivity. }
split.
{ apply (bm_areply_at_agree _ rd rd'); [| |exact HRe].
  - intros k Hk. apply (HKg OFF_REPLY k); unfold OFF_REPLY, REC_SIZE, OFF_STATE; lia.
  - intros pn k Hq Hk. apply HKb; [|exact Hk]. apply HO. unfold lay_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite Hq. left. reflexivity. }
split; [|exact HOw].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_REFUSE k); unfold OFF_REFUSE, REC_SIZE, OFF_STATE; lia | exact S1]|].
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_CODE k); unfold OFF_CODE, REC_SIZE, OFF_STATE; lia | exact S2]|].
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_NREPLIES k); unfold OFF_NREPLIES, REC_SIZE, OFF_STATE; lia | exact S3]|].
split; [exact Hh|].
split; [apply (bm_aval_mem_agree rd rd'); [intros k Hk; apply (HKg OFF_HOST k); unfold OFF_HOST, REC_SIZE, OFF_STATE; lia | exact S5]|].
repeat (split; [lia|]). lia.
Qed.
End e0.

(* ---- the symbolic states the segment starts from ---- *)
(* at 0x8ab98: g_rec through s11 (atom 27), its state word g_rec.state (offset 944) read-only, as atom 32 *)
Definition bm_greg : YP09.region := YP09.mkRegion (Some 27%nat) 0 952 0 0 [YP09.mkChunk 944 (CVal 8 (SOff 32 0))].
Definition bm_facts : facts := mkFacts [(27%nat, mkAF A_G_REC A_G_REC 0)] [] [].
Definition bm_ss0 : sstate := mkSS 0x4668 sr_atoms [bm_greg] None bm_facts.
(* at 0x8abac: no memory *)
Definition bm_ss3 : sstate := mkSS 0x467c sr_atoms [] None (mkFacts [] [] []).
(* the segment makes no inline check (no token), so the shadow span only has to miss the store into g_rec.state *)
Definition bm_Bx : sv := SOff 26 0.
Definition bm_Bspan : Z * Z := (2 ^ 63, 2 ^ 63).
Definition bm_SH : list shent := [].
Definition bm_E (regs : bvmap 5 word) (R : rstate) : env := Eimg (Ereg regs [Z_to_bv 64 (r_state R)]).
(* the seed at 0x8abac has no extra atom: a Theorem Labs lane's CmdSnText.snt_E *)

Lemma bm_ew_nat : forall (regs : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma bm_ew_reg : forall regs R n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bm_E regs R) n = getr regs r.
Proof. intros regs R n r Hn. unfold bm_E. exact (bm_ew_nat regs _ n r Hn). Qed.
Lemma bm_ew3 : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (CmdSnText.snt_E (PI := PI) regs) n = getr regs r.
Proof. intros regs n r Hn. unfold CmdSnText.snt_E. exact (bm_ew_nat regs _ n r Hn). Qed.
Lemma bm_ew32 : forall regs R, ew (bm_E regs R) 32 = Z_to_bv 64 (r_state R).
Proof. intros regs R. unfold bm_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma bm_img : forall regs R, img_env VAL A_LIM (bm_E regs R).
Proof. intros regs R. unfold bm_E. apply Eimg_env. Qed.
Lemma bm_img3 : forall regs, img_env VAL A_LIM (CmdSnText.snt_E (PI := PI) regs).
Proof. intros regs. unfold CmdSnText.snt_E. apply Eimg_env. Qed.

Lemma bm_seed3 : forall (W : world SEGS) (regs1 : bvmap 5 word) mem,
st_ok_pi SEGS VAL (CmdSnText.snt_E (PI := PI) regs1) bm_ss3
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + 0x467c)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem. rewrite restrict_mkst_fx. unfold bm_ss3. apply (pa_entry_st_ok_full (L := cmd_listing) (PI := PI)).
- unfold CmdSnText.snt_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; exact I].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callee contract this segment uses (answer_c.v:94), at every FP state; the segment uses it at the
   ambient one *)
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
(* the walk hypotheses: the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), the program functions' call targets
   (a Theorem Labs lane's CmdRecRest.v cmd_sig_prog_PB, lib/B/Prog/CmdObj.v's cmd_sig_prog, for the abstract instance), the
   program statics' writability for the store into g_rec.state (the core's prog_rw, YCbq.v) *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.
(* the per-binary image facts (a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib, at this walk's abstract segments); the record
   facts below are its field and a Theorem Labs lane's CmdRecBase.v / CmdRecRo.v lemmas over it, by exact *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a := cif_prog_img _ _ IMG.
Let RRO : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RRO (SK := SK) SEGS B LAWS HB IMG.
Let RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a := CmdRecRo.RPG (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_addressable_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  cmd_addr_b a n = true -> range_addressable (rdW W mem) SHADOW_OFF a n :=
  CmdRecBase.cmd_addressable_chk SEGS B LAWS HB.

Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Lemma bm_seed : forall (W : world SEGS) ly S (regs1 : bvmap 5 word) mem R O,
rec_repA B ly S (rdW W mem) R O -> getr regs1 27 = w64 A_G_REC ->
st_ok_pi SEGS VAL (bm_E regs1 R) bm_ss0
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + 0x4668)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs1 mem R O (Q & HR & _) H27.
destruct HR as (_ & _ & _ & _ & _ & _ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) & _).
assert (E27 : ew (bm_E regs1 R) 27 = Z_to_bv 64 A_G_REC) by (rewrite (bm_ew_reg regs1 R 27 27%bv eq_refl); exact H27).
assert (Hb : base_val (bm_E regs1 R) (Some 27%nat) = A_G_REC).
{ cbn [base_val]. rewrite E27. apply unsigned_lit_small. unfold A_G_REC. lia. }
rewrite restrict_mkst_fx. unfold bm_ss0. apply (pa_entry_st_ok_full (L := cmd_listing) (PI := PI)).
- unfold bm_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, bm_greg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (bm_chunk_ok_any SEGS (bm_E regs1 R) _ A_G_REC 944 8 (SOff 32 0)); [lia|].
  cbn [sv_denot]. rewrite bm_ew32. rewrite !Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by lia.
  apply (bm_val_mem_mod SEGS _ _ 8%nat (r_state R)).
  + replace (8 * Z.of_nat 8) with 64 by (cbn; lia). rewrite !Zmod_mod. reflexivity.
  + apply (val_mem_of_aval SEGS (w_H W) mem). exact S4.
- apply pairwise_disjoint_of_extents. cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint].
  repeat split.
- split; [|split; [exact I | exact I]].
  cbn [bm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E27, unsigned_lit_small by (unfold A_G_REC; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. unfold A_G_REC. repeat split; lia.
Qed.

(* the read-only bytes are kept by the walk's journal: its footprint is g_rec's two words and heap blocks *)
Lemma bm_aro_journal : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k old O R,
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
  apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hpn. apply bm_in_filter in Hpn as [Hpn _].
  destruct (bm_rep_O_blocks B ly S _ R O (p, n) HR Hpn) as [Hb _].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & H4096 & _). cbn [fst]. lia.
- intros (r & Hr & Ha). unfold an_FP in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]].
  + apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
    split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_ANSWER in Ha; lia].
  + apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
    split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd] in Ha |- *; unfold OFF_STATE in Ha; lia].
  + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply bm_in_filter in Hpn as [Hpn _].
    destruct (bm_rep_O_blocks B ly S _ R O (p, n) HR Hpn) as [Hb _].
    cbn [fst snd] in Ha. exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hb Ha Himg).
Qed.

(* the bytes the recorder's representation reads lie below the allocator's ceiling and outside the frame *)
Lemma bm_rep_apart : forall lyc Sc (Wc : world SEGS) memc mdc R O pos a,
AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc (rdW Wc memc) R O -> In (7, pos) (frames Sc) ->
bm_rep_addr O a -> 0 <= a < alloc_ceiling /\ ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + fs_frame_bytes 7).
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
- destruct (bm_rep_O_blocks B lyc Sc _ R O (p, n) HR Hpn) as [Hb Hn1]. cbn [snd] in Hn1.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hb) as (_ & H4096 & Hceil & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
  split; [lia|]. intros Hf.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 7 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the shape string at a later state of the walk: its bytes are kept by the journal (a live block apart from the
   recorder's blocks, or read-only image bytes), and its shadow is still addressable *)
Lemma bm_shape_at : forall STK sp0 own ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k old O R sh x,
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
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm). apply bm_in_filter in Hbm as [Hbm _].
      cbn [fst snd] in Ha.
      destruct (bm_rep_O_blocks B ly S _ R O (b, m) HREP Hbm) as [HbB _].
      destruct (Z.eq_dec b p) as [Ebp | Ebp]; [destruct (Z.eq_dec m kk) as [Emk | Emk]|].
      * subst b m. rewrite Forall_forall in HAP. specialize (HAP (p, kk) Hbm). unfold iv_apart in HAP. cbn [fst snd] in HAP. lia.
      * assert (Hne : (b, m) <> (p, kk)) by congruence.
        pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p kk HAR HbB Hb Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      * assert (Hne : (b, m) <> (p, kk)) by congruence.
        pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p kk HAR HbB Hb Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  split.
  + apply (bm_astr_atR_agree (rdW W mem)); [|exact HSTR]. intros i Hi. apply HK. lia.
  + apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc p kk); [exact HARc | exact Hbc | lia | lia].
- pose proof (bm_aro_journal STK sp0 ly S W mem md own lyc Sc Wc memc mdc k old O R HAR HREP HJ HROD) as HROD'.
  split.
  + apply (bm_astr_atR_agree (rdW W mem)); [|exact HSTR]. intros i Hi.
    destruct (HRO i ltac:(lia)) as (Hr & Hno & Hne).
    rewrite (HROD' _ Hr Hno Hne), (HROD _ Hr Hno Hne). reflexivity.
  + exact (cmd_addressable_chk lyc Sc Wc memc mdc sh _ HARc Hab).
Qed.

(* the bytes an_mid reads, besides the journal: the recorder's representation without g_rec.state, the prologue's
   slots, the frame's flag word and the shadow of buf *)
Definition bm_mid_dom (sp0 : Z) (O : list (Z * Z)) (F : Z) (a : Z) : Prop :=
(bm_rep_addr O a /\ ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8)) \/
(sp0 - 104 <= a < sp0) \/
(F + 8184 <= a < F + 8192) \/
(shadow_of_addr SHADOW_OFF (F + 32) <= a < shadow_of_addr SHADOW_OFF (F + 32) + 512).

(* an_mid at a later state whose bytes agree on bm_mid_dom and whose g_rec.state holds h *)
Lemma bm_mid_set : forall ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 Wc' memc' mdc' h,
an_mid B MT ly S W regs mem md R old O lyc Sc Wc memc mdc pos 0 sp1 ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc' memc' mdc' 0 ->
(forall a, bm_mid_dom (spZ regs) O (frame_addr lyc 7 pos) a -> rdW Wc' memc' a = rdW Wc memc a) ->
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
  apply (bm_aval_mem_agree (rdW Wc memc)); [|exact (HSAVED j r Hj)].
  intros k Hk. apply HK. right; left. lia. }
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc' memc')); [exact HFLAG|].
  intros k Hk. apply HK. right; right; left. lia. }
split.
{ intros i Hi. change (4096 / 8) with 512 in Hi. rewrite HK; [exact (HZS i ltac:(change (4096 / 8) with 512; lia))|].
  right; right; right. lia. }
split.
{ apply (bm_rep_set_state B lyc Sc (rdW Wc memc) _ R O h HRC); [|exact Hh|exact Hhr].
  intros a Ha Hns. apply HK. left. split; assumption. }
apply (bm_aval_mem_agree (rdW Wc memc)); [|exact HOLDC].
intros k Hk. apply HK. left.
split; [left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia | unfold OFF_ANSWER, OFF_STATE; lia].
Qed.

(* an_mid at a later state of the same world whose bytes are the earlier state's *)
Lemma bm_mid_keep : forall ly S W regs mem md R1 old O lyc Sc Wc memc mdc pos sp1 memc' mdc',
an_mid B MT ly S W regs mem md R1 old O lyc Sc Wc memc mdc pos 0 sp1 ->
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
an_mid B MT ly S W regs mem md R1 old O lyc Sc Wc memc' mdc' pos 0 sp1.
Proof.
intros ly S W regs mem md R1 old O lyc Sc Wc memc mdc pos sp1 memc' mdc' HM HJ' HK.
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & HRC & _).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : 12288 <= ANSWER_STK) by (vm_compute; discriminate).
assert (Hin7 : In (7, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf4096 & Hfceil & _).
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity. rewrite FB in Hfceil.
pose proof HRC as (Q0 & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & HS4 & _ & _ & _ & _ & HRS & _) & _) & _).
assert (Hrs : set_state R1 (r_state R1) = R1) by (destruct R1; reflexivity).
rewrite <- Hrs.
apply (bm_mid_set ly S W regs mem md R1 old O lyc Sc Wc memc mdc pos sp1 Wc memc' mdc' (r_state R1) HM HJ').
- intros a Ha. apply HK. destruct Ha as [[Ha _] | [Ha | [Ha | Ha]]].
  + destruct (bm_rep_apart lyc Sc Wc memc mdc R1 O pos a HARc HRC Hin7 Ha) as [Ha1 _]. lia.
  + lia.
  + lia.
  + pose proof (Z.div_pos (frame_addr lyc 7 pos + 32) 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_le_upper_bound (frame_addr lyc 7 pos + 32) 8 (frame_addr lyc 7 pos + 32) ltac:(lia) ltac:(lia)) as D2.
    unfold shadow_of_addr, SHADOW_OFF in Ha. lia.
- apply (bm_aval_mem_agree (rdW Wc memc)); [intros k Hk; apply HK; unfold A_G_REC, OFF_STATE; lia | exact HS4].
- exact HRS.
Qed.

(* 0x8abac .. 0x8abcc: the UBSan test of the shape pointer, then the setup of syntax_instantiate's loop, to HEAD
   with j = d = 0 and out = [] *)
Lemma bm_s3_ok : AN_HEAD_stmt B MT ->
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1,
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) -> getr regs1 19 = w64 sh -> getr regs1 27 = w64 A_G_REC ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + 0x467c)) memc (seg_rom SEGS)) mdc)
(an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HRZ HMID HREGS H19 H27.
pose proof HPRE as (HFN & Hfr8 & HROD & HROK & H10 & H11 & H12 & HREP0 & HOLD0 & HSHP & HCALL & HEV & HLIVE & HMO &
  (Hcr & Hshr & Holdr) & HFRM0).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hch & HQT0).
pose proof HMID as (HJ & HMLE & HPERM & Hsp1 & HSAV & HFLAG & HZS & HREP & HOLD).
pose proof HREGS as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R25 & R20 & R21 & R22 & R23 & R24 & R26).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
destruct (HSHP HRZ) as [HARG HFITS].
assert (Hsh0 : sh <> 0) by (cbn [astr_argA] in HARG; exact (proj1 HARG)).
assert (Hin7 : In (7, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf4096 & Hfceil & _).
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity. rewrite FB in Hfceil.
pose proof alloc_ceiling_val as [HAC1 HAC2].
pose proof (bm_seed3 Wc regs1 memc) as HS.
pose proof (bm_img3 regs1) as HEI.
assert (SHOK : sh_ok SEGS bm_Bx bm_SH (CmdSnText.snt_E (PI := PI) regs1) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok, bm_SH; apply Forall_nil).
assert (Ew19 : ew (CmdSnText.snt_E (PI := PI) regs1) 19 = Z_to_bv 64 sh) by (rewrite (bm_ew3 regs1 19 19%bv eq_refl); exact H19).
psrr_branch_tok RUN BR HS SHOK bm_Bspan.
(* s3 = 0 (0x8abac taken): the UBSan trap 0x8ad30; refuted, astr_argA gives sh <> 0 *)
- exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  rewrite ?(U_atom (CmdSnText.snt_E (PI := PI) regs1) 19 sh Ew19 Hshr), ?U_SLit in Hc. change (zcanon 0) with 0 in Hc. lia.
(* s3 <> 0: the loop setup 0x8abb0 .. 0x8abc8, then HEAD *)
- paj_run_to_tok RUNTO HS HJ SHOK bm_Bspan 0x469c.
  { bm_awr_ro. }
  bm_ms ms3.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms3) a = rdW Wc memc a).
  { intros a Ha.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H Wc) memc (ms_mem ms3) (fun _ => False) HFr); [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
  clear HF HFr HG. pmkst HS.
  prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (19%bv : bv 5) J19.
  bm_rreg HS (11%bv : bv 5) J11. bm_rreg HS (12%bv : bv 5) J12. bm_rreg HS (13%bv : bv 5) J13.
  bm_rreg HS (14%bv : bv 5) J14. bm_rreg HS (15%bv : bv 5) J15. bm_rreg HS (16%bv : bv 5) J16.
  bm_rreg HS (17%bv : bv 5) J17.
  destruct (bm_shape_at ANSWER_STK (spZ regs) [(7, pos)] ly S W mem md lyc Sc Wc (ms_mem ms3) mdv 0 old O R sh x
    HAR0 HREP0 HJ HPERM HROD HARG) as [HSTRh HRAh].
  apply (HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc (ms_regs ms3) (ms_mem ms3) mdv pos sp1 0%nat 0%nat []
    HPRE HRZ).
  + exact (bm_mid_keep ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos sp1 (ms_mem ms3) mdv HMID HJ KEEP).
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (bm_ew3 regs1 2 2%bv eq_refl), (bm_ew3 regs1 3 3%bv eq_refl), (bm_ew3 regs1 4 4%bv eq_refl),
      (bm_ew3 regs1 8 8%bv eq_refl), (bm_ew3 regs1 9 9%bv eq_refl), (bm_ew3 regs1 18 18%bv eq_refl),
      (bm_ew3 regs1 25 25%bv eq_refl), (bm_ew3 regs1 20 20%bv eq_refl), (bm_ew3 regs1 21 21%bv eq_refl),
      (bm_ew3 regs1 22 22%bv eq_refl), (bm_ew3 regs1 23 23%bv eq_refl), (bm_ew3 regs1 24 24%bv eq_refl),
      (bm_ew3 regs1 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J27, (bm_ew3 regs1 27 27%bv eq_refl). exact H27.
  + lia.
  + lia.
  + reflexivity.
  + rewrite J19, (bm_ew3 regs1 19 19%bv eq_refl), H19, Z.add_0_r. reflexivity.
  + rewrite J12, denot_lit_U. unfold w64. f_equal.
    rewrite (U_atom_off (CmdSnText.snt_E (PI := PI) regs1) 19 sh (-1) Ew19 Hshr ltac:(lia)). lia.
  + rewrite J17, denot_lit_U. unfold w64. f_equal; rewrite ?U_SLit; reflexivity.
  + rewrite J13, denot_lit_U. unfold w64. f_equal; rewrite ?U_SLit; reflexivity.
  + rewrite J11, denot_lit_U. unfold w64. f_equal.
    apply (bm_U_not (CmdSnText.snt_E (PI := PI) regs1) 21 (frame_addr lyc 7 pos + 32));
      [rewrite (bm_ew3 regs1 21 21%bv eq_refl); exact R21 | lia | reflexivity].
  + rewrite J14, denot_lit_U. unfold w64. f_equal; rewrite ?U_SLit; reflexivity.
  + rewrite J15, denot_lit_U. unfold w64. f_equal; rewrite ?U_SLit; reflexivity.
  + rewrite J16, denot_lit_U. unfold w64. f_equal; rewrite ?U_SLit; reflexivity.
  + intros i Hi. cbn [length] in Hi. lia.
  + exact HSTRh.
  + exact HRAh.
Qed.

(* 0x8ab98 (not refused, s11 = g_rec): the test of the changes; changes <> 0: mix_call (g_rec.state, c) and the store
   of g_rec.state; then 0x8abac (bm_s3_ok) *)
Lemma an_body_nr : AN_HEAD_stmt B MT ->
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1,
an_pre B MT ly S W regs mem md ch c sh old e x chg R O -> r_refuse R = 0 ->
an_mid B MT ly S W regs mem md R old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body B regs regs1 sp1 (frame_addr lyc 7 pos) -> getr regs1 19 = w64 sh -> getr regs1 27 = w64 A_G_REC ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + 0x4668)) memc (seg_rom SEGS)) mdc)
(an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HRZ HMID HREGS H19 H27.
pose proof HPRE as (HFN & HFRL & HROD & HRO & H10 & H11 & HCHG & HREP & HOLD & HSHP & HSLOT & HEV & HLIVE & HMO &
  (Hcr & Hshr & Holdr) & HFRM0).
pose proof HMID as (HJ & HMOLE & HPERM & HSP1 & HSAVED & HFLAG & HZS & HRC & HOLDC).
pose proof HREGS as (G2 & G3 & G4 & G8 & G9 & G18 & G25 & G20 & G21 & G22 & G23 & G24 & G26).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hch & HQT0).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & F5 & Hpresw & Hstk & F6 & HQT).
pose proof Hstk as (Hal16 & Hstk1 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (bm_seed Wc lyc Sc regs1 memc R O HRC H27) as HS.
pose proof (bm_img regs1 R) as HEI.
assert (SHOK : sh_ok SEGS bm_Bx bm_SH (bm_E regs1 R) (mrestrict (w_H Wc) memc)) by (unfold sh_ok, bm_SH; apply Forall_nil).
pose proof HRC as (Q0 & (_ & _ & _ & _ & _ & _ & (HS1 & HS2 & HS3 & HS4 & HS5 & HRR & HRCD & HRN & HRS & HRH) & _) & _).
assert (WS : 12288 <= ANSWER_STK) by (vm_compute; discriminate). assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (CmdSnText.snt_sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hs1a & Hs1b & Hs1c).
rewrite <- HSP1 in Hs1a, Hs1b, Hs1c.
assert (Ho16 : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hal16, Hs1c; reflexivity).
assert (Hin7 : In (7, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf32 & Hfapp & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HARc Hin7) as (Hf4096 & Hfceil & _).
assert (FB : fs_frame_bytes 7 = 8192) by reflexivity. rewrite FB in Hfceil, Hfapp.
psrr_branch_tok RUN BR HS SHOK bm_Bspan.
(* changes = 0 (0x8ab98 taken): straight to 0x8abac *)
- assert (HCF : chg = false).
  { rewrite branch_eq_U in Hc.
    apply Z.eqb_eq in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
    rewrite (bm_ew_reg regs1 R 23 23%bv eq_refl), G23, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite HCHG, Hc.
    reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK bm_Bspan 0x467c.
  { bm_awr_ro. }
  bm_ms ms1.
  set (mdv1 := with_vm_backing _ _ _) in *; clearbody mdv1.
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H Wc) memc (ms_mem ms1) (fun _ => False) HFr); [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
  clear HF HFr HG. pmkst HS.
  prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (19%bv : bv 5) J19.
  assert (HR1 : an_R1 R e chg = R) by (unfold an_R1; rewrite HRZ, HCF; reflexivity).
  apply (bm_s3_ok HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 pos sp1
    HPRE HRZ).
  + rewrite HR1. exact (bm_mid_keep ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 (ms_mem ms1) mdv1 HMID HJ KEEP1).
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (bm_ew_reg regs1 R 2 2%bv eq_refl), (bm_ew_reg regs1 R 3 3%bv eq_refl), (bm_ew_reg regs1 R 4 4%bv eq_refl),
      (bm_ew_reg regs1 R 8 8%bv eq_refl), (bm_ew_reg regs1 R 9 9%bv eq_refl), (bm_ew_reg regs1 R 18 18%bv eq_refl),
      (bm_ew_reg regs1 R 25 25%bv eq_refl), (bm_ew_reg regs1 R 20 20%bv eq_refl), (bm_ew_reg regs1 R 21 21%bv eq_refl),
      (bm_ew_reg regs1 R 22 22%bv eq_refl), (bm_ew_reg regs1 R 23 23%bv eq_refl), (bm_ew_reg regs1 R 24 24%bv eq_refl),
      (bm_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J19, (bm_ew_reg regs1 R 19 19%bv eq_refl). exact H19.
  + rewrite J27, (bm_ew_reg regs1 R 27 27%bv eq_refl). exact H27.
(* changes <> 0: mix_call (g_rec.state, c), the store of g_rec.state, then 0x8abac *)
- assert (HCT : chg = true).
  { rewrite branch_eq_U in Hc.
    apply Z.eqb_neq in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
    rewrite (bm_ew_reg regs1 R 23 23%bv eq_refl), G23, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite HCHG.
    destruct (bv_unsigned (getr regs 12) =? 0) eqn:E0; [|reflexivity]. apply Z.eqb_eq in E0. exfalso. apply Hc.
    rewrite E0. reflexivity. }
  paj_run_tok RUN HS HJ SHOK bm_Bspan.
  { bm_awr_ro. }
  bm_ms msc.
  set (mdvm := with_vm_backing _ _ _) in *; clearbody mdvm.
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc memc a).
  { intros a Ha.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H Wc) memc (ms_mem msc) (fun _ => False) HFr); [|exact Ha|intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-. lia. }
  clear HF HFr HG. pmkst HS. prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3.
  prreg HS (4%bv : bv 5) M4. prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11.
  assert (HSIGMC : SIG CS_mix_call = BASE + AF_mix_call).
  { rewrite (cmd_sig_prog_PB CS_mix_call ltac:(cbn [In]; repeat first [left; reflexivity | right])).
    f_equal; try (vm_compute; reflexivity). }
  rewrite HSIGMC. assert (Rsp : spZ (ms_regs msc) = sp1).
  { unfold spZ.
    rewrite M2, (bm_ew_reg regs1 R 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (proj1 HJ) as HAR1. assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem msc)))
    by exact (bm_aro_journal _ _ ly S W mem md _ lyc Sc Wc _ _ _ old O R HAR HREP HJ HROD).
  pose proof (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem msc) mdvm HAR1 HROD1) as HRO1.
  pose proof HRC as (Qc & (_ & _ & _ & (HCL1 & HCL2 & _ & HCi & HCsp & _) & _) & _).
  assert (HPK : forall P, 0 <= c < 2 ^ 32 -> acall_at (ablocks B lyc Sc) (rdW Wc memc) c e P ->
    acall_at (ablocks B lyc Sc) (rdW Wc (ms_mem msc)) c e P).
  { intros P Hc32 Hcall.
    apply (bm_acall_at_agree _ (rdW Wc memc)); [| |exact Hcall].
    - intros kk Hkk. apply KEEPc. unfold CALL_SIZE in Hkk. lia.
    - intros pn kk Hpn Hkk. destruct (bm_acall_at_In _ _ _ _ _ pn Hcall Hpn) as [Hb _]. destruct pn as [p n].
      destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HARc Hb) as (_ & H4096 & Hceil' & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. cbn [fst snd] in *. apply KEEPc. lia. }
  assert (HSL : ((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) /\
    exists P, acall_at (ablocks B lyc Sc) (rdW Wc (ms_mem msc)) c e P).
  { destruct (HSLOT HRZ HCT) as [(k & Hk & Ec) | (Ec & Ee)].
    - assert (Hkl : (k < length (l_calls Qc))%nat) by (rewrite HCL2; apply nth_error_Some; rewrite Hk; discriminate).
      destruct (nth_error (l_calls Qc) k) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
      destruct (HCi k e P Hk HP) as [Hcall _]. rewrite <- Ec in Hcall.
      split; [left; exists (Z.of_nat k); split; [unfold REC_CALLS_MAX; lia | exact Ec] |]. exists P.
      apply (HPK P); [rewrite Ec; unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia | exact Hcall].
    - split; [right; exact Ec|]. exists (l_spill Qc). apply HPK; [rewrite Ec; unfold A_REC_SPILL; lia|].
      rewrite Ec, Ee. exact HCsp. }
  destruct HSL as [HSL (Pc & HCALLc)].
  assert (HMB : 0 <= MIX_CALL_STK /\ MIX_CALL_STK + 144 <= ANSWER_STK) by (split; vm_compute; discriminate).
  assert (HEVA : 0 <= EV_ANSWER) by (vm_compute; discriminate).
  eapply SRr_bind.
  { eapply (cl_callS_na (L := cmd_listing) (PI := PI) B LAWS Wc (ms_regs msc) (ms_mem msc)
      (Z_to_bv 64 (BASE + AF_mix_call)) ANSWER_STK (spZ regs) (an_FP old O)
      ly S W mem md [(7, pos)] lyc Sc mdvm 0 MIX_CALL_STK [] EV_MIX_CALL (sp1 - spZ regs) (getr (ms_regs msc) 1)
      (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (mixcall (r_state R) (fst e) (snd e)) /\
      Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc) HJ).
    - lia.
    - exact Ho16.
    - lia.
    - lia.
    - lia.
    - rewrite M3, (bm_ew_reg regs1 R 3 3%bv eq_refl). exact G3.
    - rewrite M4, (bm_ew_reg regs1 R 4 4%bv eq_refl). exact G4.
    - reflexivity.
    - rewrite M1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. rewrite M1, unsigned_lit_small by lia. lia.
    - intros HPN.
      assert (Ha0 : getr (ms_regs msc) 10 = w64 (r_state R)) by (rewrite M10, bm_ew32; reflexivity).
      assert (Ha1 : getr (ms_regs msc) 11 = w64 c) by (rewrite M11, (bm_ew_reg regs1 R 24 24%bv eq_refl), G24; exact H10).
      assert (Hev : st_nev Sc + EV_MIX_CALL <= EV_MAX) by (unfold EV_MIX_CALL; lia).
      exact (TMIX_CALL fx lyc Sc Wc (ms_regs msc) (ms_mem msc) mdvm (r_state R) c e Pc HPN HROD1 Ha0 HRS Ha1 HSL HCALLc
        HRO1 Hev).
    - intros a (r & [] & _). }
  cbv beta. intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJM & HJI & HPM & HMIX & HPERM2 & -> & ->).
  replace (0 + EV_MIX_CALL) with 0 in HJM by reflexivity. rewrite M1.
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HPM (@nil nat) HSn. specialize (HSn (Forall_nil _)).
  rewrite <- restrict_mkst_fx in HSn. clear HS. rename HSn into HS. hei_havoc HS.
  assert (E27h : ew (havoc (bm_E regs1 R) 40 (map (getr regs2) CLOB)) 27 = Z_to_bv 64 A_G_REC)
    by (rewrite ew_havoc_old by lia; rewrite (bm_ew_reg regs1 R 27 27%bv eq_refl); exact H27).
  assert (Ebh : base_val (havoc (bm_E regs1 R) 40 (map (getr regs2) CLOB)) (Some 27%nat) = A_G_REC).
  { cbn [base_val]. rewrite E27h. apply unsigned_lit_small. unfold A_G_REC. lia. }
  assert (HPGs : forall o, 944 <= o < 952 -> inFP cmd_PG (A_G_REC + o)).
  { intros o Ho.
    exists (A_G_REC, A_G_REC + 960). split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; lia]. }
  pose proof (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 27%nat) 944 952 944 952 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite Ebh;
    split; [unfold A_G_REC; lia|]; split; [unfold A_G_REC; lia|]; split; [|apply Forall_nil];
    intros o Ho; exact (PRW _ _ (CmdRecAns.rca_HPROG B HB _ (HPGs o Ho)))) I) as HSr.
  clear HS. rename HSr into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (SHOK2 : sh_ok SEGS bm_Bx bm_SH (havoc (bm_E regs1 R) 40 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2))
    by (unfold sh_ok, bm_SH; apply Forall_nil).
  clear SHOK. rename SHOK2 into SHOK.
  paj_run_to_tok RUNTO HS HJM SHOK bm_Bspan 0x467c.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end.
    eapply awr_ok_cons_gen with (b := A_G_REC);
      [reflexivity | rewrite E27h; apply unsigned_lit_small; unfold A_G_REC; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right; right; left. split; [|split].
    - exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8).
      split; [unfold an_FP; cbn [In]; right; left; reflexivity | cbn [fst snd]; unfold OFF_STATE; lia].
    - apply (CmdRecAns.rca_HPROG B HB). replace a with (A_G_REC + (a - A_G_REC)) by lia. apply HPGs. lia.
    - apply cif_prog_img. replace a with (A_G_REC + (a - A_G_REC)) by lia. apply HPGs. lia. }
  bm_ms mss.
  set (mdvs := with_vm_backing _ _ _) in *; clearbody mdvs.
  assert (KEEPs : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + 944 <= a < A_G_REC + 952) ->
    rdW W2 (ms_mem mss) a = rdW W2 mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs:=SEGS) _ _ (w_H W2) mem2 (ms_mem mss) (fun a => A_G_REC + 944 <= a < A_G_REC + 952) HFr);
      [|exact Ha|exact Hn].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq|[]]. injection Hq as <- <- <-.
    rewrite Ebh in Hrr. exact Hrr. }
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRG.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 944 8%N (SOff 44 0) HRG
    ltac:(rewrite E27h; apply unsigned_lit_small; unfold A_G_REC; lia)
    ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as HVAL.
  clear HRG HF HFr HG. set (h' := mixcall (r_state R) (fst e) (snd e)) in *.
  assert (Hh' : 0 <= h' < 2 ^ 64) by (apply mixcall_range; exact HRS).
  assert (E44 : ew (havoc (bm_E regs1 R) 40 (map (getr regs2) CLOB)) 44 = getr regs2 10)
    by exact (ew_havoc_new _ 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(rewrite length_map; vm_compute; lia)).
  assert (Hst : aval_mem (rdW W2 (ms_mem mss)) (A_G_REC + OFF_STATE) 8 h').
  { apply (bm_aval_of_val_mem SEGS (w_H W2) (ms_mem mss)).
    cbn [ms_mem restrict] in HVAL. cbn [sv_denot] in HVAL. rewrite E44, HMIX, Z.add_0_r, Z_to_bv_bv_unsigned in HVAL.
    unfold w64 in HVAL. rewrite unsigned_lit_small in HVAL by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HVAL.
    rewrite Z.mod_small in HVAL by lia. exact HVAL. }
  pmkst HS.
  prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4.
  prreg HS (8%bv : bv 5) J8. prreg HS (9%bv : bv 5) J9. prreg HS (18%bv : bv 5) J18. prreg HS (20%bv : bv 5) J20.
  prreg HS (21%bv : bv 5) J21. prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
  prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27. prreg HS (19%bv : bv 5) J19.
  (* the bytes an_mid reads besides g_rec.state: kept by mix_call's journal, the store and the two runs *)
  assert (KDOM : forall a, bm_mid_dom (spZ regs) O (frame_addr lyc 7 pos) a -> rdW W2 (ms_mem mss) a = rdW Wc memc a).
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
      - destruct (bm_rep_apart lyc Sc Wc memc mdc R O pos a HARc HRC Hin7 Ha) as [Ha1 _]. lia.
      - lia.
      - lia.
      - unfold shadow_of_addr, SHADOW_OFF in Ha. lia. }
    rewrite (KEEPs a Ha64 Hst_out), <- (KEEPc a Ha64). destruct Ha as [[Ha _] | [Ha | [Ha | Ha]]].
    - destruct Ha as [Ha | [Ha | (p & n & Hpn & Ha)]].
      + assert (HPG : inFP cmd_PG a)
          by (exists (A_G_REC, A_G_REC + 960); split; [cbn [In cmd_PG]; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]).
        pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HARc)) (CmdRecAns.rca_HPROG B HB a HPG)) as (Hno & Hne & _).
        apply I3; [exact (cif_prog_img a HPG) | exact Hno | exact Hne | apply fp_spares_closed; intros (r & [] & _)].
      + assert (HPG : inFP cmd_PG a)
          by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [cbn [In cmd_PG]; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia]).
        pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HARc)) (CmdRecAns.rca_HPROG B HB a HPG)) as (Hno & Hne & _).
        apply I3; [exact (cif_prog_img a HPG) | exact Hno | exact Hne | apply fp_spares_closed; intros (r & [] & _)].
      + destruct (bm_rep_O_blocks B lyc Sc _ R O (p, n) HRC Hpn) as [Hb Hn1]. cbn [snd] in Hn1.
        pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. replace a with (p + (a - p)) by lia.
        apply (I2 p n (a - p)); [exact Hb | exact Hb | lia | intros (r & [] & _)].
    - apply I1; [lia | unfold MIX_CALL_STK; rewrite Hes; lia | intros (r & [] & _)].
    - apply (I4 7 pos a Hin7); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FB; lia | intros (r & [] & _)].
    - apply (I4 7 pos a Hin7); [right | intros (r & [] & _)]. unfold in_zr, shadow_addr; cbn [fst snd]; rewrite FB.
      change (8192 / 8) with 1024. unfold shadow_of_addr in Ha. rewrite Hsh32 in Ha. lia. }
  assert (HR1 : an_R1 R e chg = set_state R h') by (unfold an_R1; rewrite HRZ, HCT; reflexivity).
  apply (bm_s3_ok HHEAD ly S W regs mem md ch c sh old e x chg R O lyc Sc W2 (ms_regs mss) (ms_mem mss) mdvs pos sp1
    HPRE HRZ).
  + rewrite HR1.
    exact (bm_mid_set ly S W regs mem md R old O lyc Sc Wc memc mdc pos sp1 W2 (ms_mem mss) mdvs h' HMID HJM KDOM Hst Hh').
  + unfold an_regs_body. rewrite J2, J3, J4, J8, J9, J18, J25, J20, J21, J22, J23, J24, J26.
    rewrite (bm_ew_reg regs1 R 2 2%bv eq_refl), (bm_ew_reg regs1 R 3 3%bv eq_refl), (bm_ew_reg regs1 R 4 4%bv eq_refl),
      (bm_ew_reg regs1 R 8 8%bv eq_refl), (bm_ew_reg regs1 R 9 9%bv eq_refl), (bm_ew_reg regs1 R 18 18%bv eq_refl),
      (bm_ew_reg regs1 R 25 25%bv eq_refl), (bm_ew_reg regs1 R 20 20%bv eq_refl), (bm_ew_reg regs1 R 21 21%bv eq_refl),
      (bm_ew_reg regs1 R 22 22%bv eq_refl), (bm_ew_reg regs1 R 23 23%bv eq_refl), (bm_ew_reg regs1 R 24 24%bv eq_refl),
      (bm_ew_reg regs1 R 26 26%bv eq_refl).
    exact HREGS.
  + rewrite J19, (bm_ew_reg regs1 R 19 19%bv eq_refl). exact H19.
  + rewrite J27, (bm_ew_reg regs1 R 27 27%bv eq_refl). exact H27.
Qed.

End e.
End f.
End d.
