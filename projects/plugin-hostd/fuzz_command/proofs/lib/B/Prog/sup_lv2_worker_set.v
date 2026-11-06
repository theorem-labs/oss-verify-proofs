(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_lv2_worker_set (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_lv2_worker_set = 0x8c0cc, 28 instructions, 112 bytes): it proves
   a Theorem Labs lane's `tsup_lv2_worker_set_spec` (lib/B/Prog/sup_lv2_worker_set_c.v; statement from a Theorem Labs lane f490061c104, over
   a Theorem Labs lane c022a2f6a88) in the form of cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic
   executor over the position-abstract listing up to each call (the plain runs of lib/B/Prog/PaCallRun.v, no shadow
   access in the function), the callee contracts of record, arg_s and rec_shape_of (taken at the entry's FP state,
   which these apost_base callees keep) through cl_callS_wide / cl_callS_na (lib/B/Prog/PaNoChain.v), and answer's
   FP-existential post (apost_baseF) through PaFx.callS_wideF at the tail jump, which is this function's
   apost_baseF. The frame chains (pass 5, no astack_pres): s0 = worker (a heap pointer) at the four program calls,
   achain_low; at the tail jump s0 and sp are the entry's, afn_pre's chain moved by achain_kept / achain_ly_top.
   It is the B re-walk of the A walk
   lib/A/Prog/sup_lv2_worker_set.v + _s0 .. _s3 (a working branch 5c647899d9f), whose rec_shape_of call,
   tail call of answer and post assembly (sup_lv2_worker_set_s2.v slw_D2 / slw_D3) it follows; B calls record and
   arg_s where A inlines them, so A's segments A, B and s3 become one contract step each. The Generation-N B walk
   lib/B/Prog/sup_lv2_worker_set.v on a working branch 543f2c3645b (template only, not ported) cuts the same
   code at the same return addresses.

   B code (MEASURED from the pinned fuzz_command.asan-ubsan with pyelftools and capstone, symbol-keyed; a Theorem Labs lane's
   gen/dis/sup_lv2_worker_set.s): a 32-byte frame (ra, s0, s1, s2), `mv s0,a1` (worker), `mv s1,a0` (uri);
   record(15) at 0x8c0ec (ret 0x8c0f0), `mv s2,a0` (the slot); arg_s(slot, uri) at 0x8c0f8; arg_s(slot, worker) at
   0x8c104; rec_shape_of(.str.13 = 0x21ee0, 14) at 0x8c114 (the listing's `PHi 10 176; PAddHi 10 10 176 (A_OBJ 75) 0`
   at 0x8c108: a0 = the literal's address, nothing is loaded or stored through the auipc base); the epilogue and the
   tail jump `j answer` (0x8c138) with a0 = slot, a1 = the shape, a2 = 1, at the entry sp.
   Report / trap edges: none. The function has no branch, no `unimp`/`ebreak`, no call to any of the 24
   __asan_report_* entries and 0 UBSan trap sites (a Theorem Labs lane's gen/traps.B.summary); its checks are its callees'
   (record 4, arg_s 5, answer 5 trap sites, rec_shape_of 2 inline checks), refuted in their own walks, whose
   contracts this walk uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecFacts PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_lv2_worker_set_c sup_lv2_worker_set_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's writable statics as (start, length): g_rec, record.spill, g_quitting (CmdBSyms' ts_prog) *)
Definition slw_PG : list (Z * Z) := TFIB_PROG_STATIC.
(* the statement's footprint (sup_lv2_worker_set_c.v, apost_base) *)
Definition slw_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the symbolic state at the entry: the 32-byte frame below the entry sp (atom 2), the sp's range and alignment *)
Definition slw_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_slw_entry : sstate := mkSS AF_sup_lv2_worker_set sr_atoms [stack_region 32] None slw_facts0.
(* the frame: ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24, s2 at sp0 - 32 *)
Definition slw_saved : list Z := [1; 8; 9; 18].

(* --- the recorder's state across writes outside it (A walk's sup_lv2_worker_set_s2.v:117-228, verbatim) ------- *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.

Section r.
Variable B : asyms.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.
(* the answer the recorder holds: 0, or the start of one of its blocks *)
Lemma slw_old_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) O).
Proof.
intros ly S rd R O (Q & (_ & _ & _ & _ & Ha & _) & HO). unfold aanswer_at in Ha. unfold lay_blocks in HO.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:EA; try contradiction.
- exists q. split; [exact (proj1 Ha)|]. right. exists m. apply HO.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- exists 0. split; [exact Ha | left; reflexivity].
Qed.
Lemma slw_rep_len : forall ly S rd R O, rec_repA B ly S rd R O -> (length (r_calls R) <= 16)%nat.
Proof. intros ly S rd R O (Q & (_ & _ & _ & (H & _) & _) & _). exact H. Qed.
(* a string the recorder or rec_shape_of hands on, read through another reader that agrees below alloc_ceiling *)
Lemma slw_astr_argA_rd : forall ly S (rd rd' : reader) ro O p v, astr_argA B ly S rd ro O p v ->
(forall i, 0 <= i < Z.of_nat (length (sarg v)) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly S rd' ro O p v.
Proof.
intros ly S rd rd' ro O p [x|] H K; [|exact H]. cbn [astr_argA sarg] in *. destruct H as (H0 & Hs & Hn & Hr).
split; [exact H0|]. split; [apply (rastr_kept rd); [exact Hs | exact K]|]. split; [exact Hn | exact Hr].
Qed.
End r.

Lemma slw_in_filter : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn : Z * Z => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|y l IH]; intros Hx; [exact Hx|].
revert Hx. cbn. case_decide as Hd; intros Hx; [destruct Hx as [-> | Hx]; [left; reflexivity | right; exact (IH Hx)] | right; exact (IH Hx)].
Qed.

(* the callee-saved registers of a state, register by register *)
Lemma slw_aregs : forall (regs regsA : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> aregs_preserved regs regsA.
Proof.
intros regs regsA H r Hr. apply H. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto ..|].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [cbn; tauto|]). subst. cbn; tauto.
Qed.

(* cgif's region_kept over aview for a region whose window bytes stay present (socket_send.v ss_region_kept_hi2) *)
Lemma slw_region_kept_hi2 {fx : YK11.FPState} : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (sup_lv2_worker_set_c.v, Section e, a Theorem Labs lane f490061c104): the callees' contracts
   at every FP state *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's named hypotheses, in a Theorem Labs lane's CmdRecFacts forms (lib/B/Prog/CmdRec*.v, a working branch f490061c104):
   HB, the allocator record (lib/B/YF0m.v Record CmdBSyms); MTL, the meter's laws; cmd_img_facts_tfib, the image
   facts record (lib/B/Prog/CmdRecBase.v cmd_img_facts) at every record, which a Theorem Labs lane proves at the pinned image
   (CmdRecImg.v cmd_img_facts_tfib) and from which a Theorem Labs lane's lemmas give cmd_prog_img, cmd_ro_prog_apart, RELRO_IMG,
   ROB, CMD_RO_IN and cmd_ro_ok_of_aro below; cmd_sig_prog_PB, the call target of every program function
   (lib/B/Prog/CmdObj.v cmd_sig_prog; a Theorem Labs lane proves it at PI := PB_cmd, CmdRecRest.v cmd_sig_prog_PB).
   cmd_heap_tail_vis needs only LAWS and HB. LAWS is AR_laws_ok. SupLv2WorkerSetClosed.v discharges
   cmd_img_facts_tfib and cmd_sig_prog_PB at the pinned image. *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let SIGP : cmd_sig_prog := cmd_sig_prog_PB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) := CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) := CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e := CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.

Lemma slw_prog_static : as_prog_static B = slw_PG.
Proof. rewrite (ts_prog B HB). reflexivity. Qed.

Lemma slw_in_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) slw_PG.
Proof. intros a Ha. unfold slw_PG, TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma slw_in_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) slw_PG.
Proof. intros a Ha. unfold slw_PG, TFIB_PROG_STATIC. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.

(* --- blocks ------------------------------------------------------------------------------------------- *)
Lemma slw_blk_pos : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ p + req_size n <= alloc_ceiling /\ n <= req_size n.
Proof.
intros ly S W mem md p n HAR H. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. lia.
Qed.

(* two distinct live blocks are apart; a live block's start determines it *)
Lemma slw_blk_apart : forall ly S (W : world SEGS) mem md b m p n,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
iv_apart b m p n /\ b <> p.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2]. pose proof (req_size_pos n ltac:(lia)) as [Rn1 Rn2].
unfold iv_apart. split; lia.
Qed.

Lemma slw_nodup : forall ly S (W : world SEGS) mem md L1 L2 x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) -> In x L1 -> In x L2 -> False.
Proof.
intros ly S W mem md L1 L2 x HAR HP H1 H2.
exact (list_nodup_app_disj L1 L2 x (Permutation_NoDup HP (recb_ablocks_nodup_m (PI := PI) B ly S W mem md HAR)) H1 H2).
Qed.

(* a fresh block (apart from every listed block) is none of them *)
Lemma slw_fresh_notin : forall p n (L : list (Z * Z)), 0 < n -> Forall (fun qk => iv_apart p n (fst qk) (snd qk)) L ->
~ In (p, n) L.
Proof.
intros p n L Hn HF Hin. rewrite Forall_forall in HF. pose proof (HF (p, n) Hin) as D. unfold iv_apart in D.
cbn [fst snd] in D. lia.
Qed.

(* --- the statement's footprint ------------------------------------------------------------------------ *)
(* every byte of the footprint lies below the stack *)
Lemma slw_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (slw_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & _ & Hpc & _). lia.
Qed.

(* a byte of a live block that is none of O lies outside the footprint *)
Lemma slw_blk_notFP : forall ly S (W : world SEGS) mem md O b m a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> In (b, m) (ablocks B ly S) -> ~ In (b, m) O ->
b <= a < b + req_size m -> ~ inFP (slw_FP O) a.
Proof.
intros ly S W mem md O b m a HAR HO Hb HbO Ha (r & Hr & Hra).
assert (Hni : ~ in_img SEGS a) by exact (blk_img SEGS B LAWS ly S W mem md b m a HAR Hb Ha).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra.
- apply Hni. apply cmd_prog_img. apply slw_in_grec. exact Hra.
- apply Hni. apply cmd_prog_img. apply slw_in_spill. exact Hra.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Hra.
  assert (Hne : (b, m) <> (p, n)) by (intros E; apply HbO; rewrite E; exact Hin).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR Hb (HO _ Hin) Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the bytes of a live block that is none of O are kept by the walk's journal while the block stays live *)
Lemma slw_blk_kept : forall STK sp0 ly S (W : world SEGS) mem md O ly' S' (W' : world SEGS) mem' md' k b m a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (slw_FP O) ly S W mem md [] ly' S' W' mem' md' k ->
In (b, m) (ablocks B ly S) -> ~ In (b, m) O -> In (b, m) (ablocks B ly' S') -> b <= a < b + m ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 ly S W mem md O ly' S' W' mem' md' k b m a HAR HO HJ Hb HbO Hb' Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
replace a with (b + (a - b)) by lia. apply (F2 b m (a - b) Hb Hb' ltac:(lia)).
apply (slw_blk_notFP ly S W mem md O b m); [exact HAR | exact HO | exact Hb | exact HbO | lia].
Qed.

(* the read-only bytes lie outside the statement's footprint, so arodata_okP survives every journal of the walk *)
Lemma slw_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (slw_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply HnPG. apply slw_in_grec. exact Ha.
- apply HnPG. apply slw_in_spill. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO (p, n) Hin) Ha Himg).
Qed.

Lemma slw_aro_at : forall ly S (W : world SEGS) mem md O STK sp0 own ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (slw_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros ly S W mem md O STK sp0 own ly' S' W' mem' md' k HAR HO HJ HR.
exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B STK sp0 (slw_FP O) ly S W mem md own ly' S' W' mem' md' k HJ
  (slw_ro_off ly S W mem md O HAR HO) HR).
Qed.

(* a footprint byte of g_rec / record.spill is a byte the walk may write: awr_byte's program-static arm *)
Lemma slw_awr_prog : forall STK sp0 O bl0 blc fr0 ly own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (slw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha. unfold awr_byte. right; right; right; right.
unfold awr_prog_or_caller. left.
assert (HP : Exists (in_zr a) slw_PG) by (destruct Ha as [Ha | Ha]; [apply slw_in_grec | apply slw_in_spill]; exact Ha).
split; [|split; [rewrite slw_prog_static; exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the slot a recorder call fills: inside g_rec's call table or record.spill *)
Lemma slw_slot_in : forall R i, (length (r_calls R) <= 16)%nat -> 0 <= i < CALL_SIZE ->
A_G_REC <= rec_slot R + i < A_G_REC + REC_SIZE \/ A_REC_SPILL <= rec_slot R + i < A_REC_SPILL + SC_SIZE.
Proof.
intros R i Hl Hi. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H]; [left | right];
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma slw_slot_range : forall R, (length (r_calls R) <= 16)%nat -> 4096 <= rec_slot R /\ rec_slot R + 56 <= 2 ^ 40.
Proof.
intros R Hl. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H];
unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL; lia.
Qed.

(* what a callee with an empty footprint keeps (rec_shape_of): the program's statics, the caller's frame above its
   sp, the bytes of every block live before and after it (the A walk's slw_callee_keeps) *)
Lemma slw_callee_keeps : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall a, Exists (in_zr a) slw_PG -> rdW W2 mem2 a = rdW Wc memc a) /\
(forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW Wc memc (p + i)).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
split.
- intros a HP. pose proof HP as HP0. rewrite <- slw_prog_static in HP.
  destruct (prog_static_sep B a (ts_ok B HB) HP) as (Ho & He & _).
  apply F3; [apply cmd_prog_img; exact HP0 | exact Ho | exact He |].
  apply fp_spares_closed; [exact sink_closed_nil | intros (r & [] & _)].
- intros p n i H1 H2 Hi. exact (F2 p n i H1 H2 Hi (fun HF => match HF with ex_intro _ r (conj Hr _) => Hr end)).
Qed.

(* a callee whose footprint lies below alloc_ceiling keeps the caller's frame above its own sp *)
Lemma slw_callee_stack : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall x, inFP FP1 x -> x < alloc_ceiling) -> sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ HFl Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & _).
apply F1; [lia | lia | intros Hf; pose proof (HFl a Hf); lia].
Qed.

(* --- the post's block facts (A walk's sup_lv2_worker_set_s2.v slw_D3, :1064-1141): record() freed F (none on the
   table arm), the two arg_s calls added p1 and p2, answer freed the old answer and added p1' and q --------------- *)
Lemma slw_post_blocks : forall ly S (W : world SEGS) mem md O ly1 S1 ly3 S3 (W3 : world SEGS) mem3 md3
  ly4 S4 (W4 : world SEGS) mem4 md4 F O1 p1 n1 p2 n2 old OA p1' q nt O',
AR SEGS B ly S W mem md -> AR SEGS B ly3 S3 W3 mem3 md3 -> AR SEGS B ly4 S4 W4 mem4 md4 ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) ->
(forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
Permutation (ablocks B ly3 S3) ((p2, n2) :: (p1, n1) :: ablocks B ly1 S1) ->
~ In (p1, n1) (ablocks B ly1 S1) -> ~ In (p2, n2) ((p1, n1) :: ablocks B ly1 S1) ->
OA = (p2, n2) :: (p1, n1) :: O1 ->
(forall pn, In pn OA -> In pn (ablocks B ly3 S3)) ->
(old = 0 \/ exists m, In (old, m) OA) ->
p1' <> q ->
(forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old -> pn <> (p1', nt) /\ pn <> (q, nt)) ->
(forall pn, In pn (ablocks B ly4 S4) <-> (In pn (ablocks B ly3 S3) /\ fst pn <> old) \/ pn = (p1', nt) \/ pn = (q, nt)) ->
(forall pn, In pn O' <-> (In pn OA /\ fst pn <> old) \/ pn = (p1', nt)) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
In (q, nt) (ablocks B ly4 S4) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, nt)) /\
~ In q (map fst O') /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly4 S4) /\ iv_apart (fst pn) (snd pn) q nt) /\
(forall pn, In pn (ablocks B ly4 S4) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, nt)).
Proof.
intros ly S W mem md O ly1 S1 ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 F O1 p1 n1 p2 n2 old OA p1' q nt O'
  HAR HARA HAR4 HPS0 HDf HO1 HP3 Hn1 Hn2 -> HOA3 Hold' Hne HG1 Hbl HO'.
set (Lk := ablocks B ly1 S1) in *.
assert (HPS : Permutation (ablocks B ly S) (F ++ Lk)) by (eapply perm_trans; [exact HPS0 | apply Permutation_app_comm]).
assert (HOA : forall pn, In pn ((p2, n2) :: (p1, n1) :: O1) -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn Hpn. destruct Hpn as [<- | [<- | Hpn]].
  - destruct (in_dec recb_pair_dec (p2, n2) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | exfalso; apply Hn2; right; exact Hin].
  - destruct (in_dec recb_pair_dec (p1, n1) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | exfalso; exact (Hn1 Hin)].
  - left. exact (proj1 (proj1 (HO1 pn) Hpn)). }
assert (HL3 : forall pn, In pn Lk -> In pn (ablocks B ly3 S3))
  by (intros pn HpnL; apply (Permutation_in _ (Permutation_sym HP3)); right; right; exact HpnL).
assert (HoldO : forall pn, In pn Lk -> ~ In pn O -> fst pn <> old).
{ intros pn HpnL HpnO Heq. destruct Hold' as [-> | (m & Hm)].
  - destruct pn as [pp pm]. pose proof (slw_blk_pos _ _ _ _ _ _ _ HARA (HL3 _ HpnL)) as (Hp4 & _). cbn in Heq. lia.
  - assert (Hm3 : In (old, m) (ablocks B ly3 S3)) by exact (HOA3 _ Hm).
    destruct (recb_pair_dec pn (old, m)) as [-> | Hne2].
    + destruct (HOA _ Hm) as [HinO | Hnin]; [exact (HpnO HinO)|].
      apply Hnin. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. exact HpnL.
    + destruct pn as [pp pm]. cbn in Heq. subst pp.
      exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HARA (HL3 _ HpnL) Hm3 Hne2) eq_refl). }
assert (HoldN : forall pn, ~ In pn Lk -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn HpnL. destruct (in_dec recb_pair_dec pn (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
  apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | contradiction]. }
assert (HfreshL : forall x, x = p1' \/ x = q -> In (x, nt) Lk -> In (x, nt) ((p2, n2) :: (p1, n1) :: O1)).
{ intros x Hx HxL. pose proof (HL3 _ HxL) as Hx3.
  destruct (Z.eq_dec x old) as [Hxo | Hxo].
  2: { exfalso. destruct (HG1 (x, nt) Hx3 Hxo) as [Ha Hb]. destruct Hx as [-> | ->]; [exact (Ha eq_refl) | exact (Hb eq_refl)]. }
  subst x. destruct Hold' as [Ho0 | (m & Hm)].
  - exfalso. pose proof (slw_blk_pos _ _ _ _ _ _ _ HARA Hx3) as (Hp4 & _). lia.
  - assert (Hm3 : In (old, m) (ablocks B ly3 S3)) by exact (HOA3 _ Hm).
    destruct (recb_pair_dec (old, nt) (old, m)) as [-> | Hne2]; [exact Hm|].
    exfalso. exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HARA Hx3 Hm3 Hne2) eq_refl). }
assert (Hq4 : In (q, nt) (ablocks B ly4 S4)) by (apply Hbl; right; right; reflexivity).
split.
{ intros pn Hpn. apply HO' in Hpn as [[HpnA _] | ->]; [exact (HOA pn HpnA)|].
  destruct (in_dec recb_pair_dec (p1', nt) Lk) as [HL | HL];
  [exact (HOA _ (HfreshL p1' (or_introl eq_refl) HL)) | exact (HoldN _ HL)]. }
split; [exact Hq4|].
split.
{ intros pn Hpn HpnO ->.
  assert (HpnL : In (q, nt) Lk).
  { apply (Permutation_in _ HPS), in_app_iff in Hpn as [Hpn'|Hpn']; [exact (False_ind _ (HpnO (HDf _ Hpn'))) | exact Hpn']. }
  destruct (HOA _ (HfreshL q (or_intror eq_refl) HpnL)) as [HinO | Hnin]; [exact (HpnO HinO) | exact (Hnin Hpn)]. }
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hpq & Hpn). apply HO' in Hpn as [[HpnA Hpold] | ->].
  - assert (Hp3 : In pn (ablocks B ly3 S3)) by exact (HOA3 _ HpnA).
    assert (Hp4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact Hp3 | exact Hpold]).
    destruct (recb_pair_dec pn (q, nt)) as [-> | Hne2]; [exact (proj2 (HG1 _ Hp3 Hpold) eq_refl)|].
    destruct pn as [pp pm]. cbn in Hpq. subst pp.
    exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR4 Hp4 Hq4 Hne2) eq_refl).
  - cbn in Hpq. exact (Hne Hpq). }
split.
{ intros pn Hpn HpnO.
  assert (HpnL : In pn Lk).
  { apply (Permutation_in _ HPS), in_app_iff in Hpn as [Hpn'|Hpn']; [exact (False_ind _ (HpnO (HDf _ Hpn'))) | exact Hpn']. }
  pose proof (HoldO pn HpnL HpnO) as Hpold.
  assert (Hp4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact (HL3 _ HpnL) | exact Hpold]).
  split; [exact Hp4|].
  destruct (recb_pair_dec pn (q, nt)) as [-> | Hne2]; [exact (False_ind _ (proj2 (HG1 _ (HL3 _ HpnL) Hpold) eq_refl))|].
  destruct pn as [pp pm]. exact (proj1 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR4 Hp4 Hq4 Hne2)). }
{ intros pn Hpn. apply Hbl in Hpn as [[Hp3 Hpold] | [-> | ->]].
  - apply (Permutation_in _ HP3) in Hp3. destruct Hp3 as [<- | [<- | HpnL]].
    + right; left. apply HO'. left. split; [left; reflexivity | exact Hpold].
    + right; left. apply HO'. left. split; [right; left; reflexivity | exact Hpold].
    + destruct (in_dec recb_pair_dec pn O) as [HinO | HnO].
      * right; left. apply HO'. left. split; [|exact Hpold]. right; right. apply HO1. split; [exact HinO|].
        intros HDfp. exact (slw_nodup ly S W mem md F Lk pn HAR HPS HDfp HpnL).
      * left. split; [apply (Permutation_in _ (Permutation_sym HPS)); apply in_or_app; right; exact HpnL | exact HnO].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
Qed.

(* --- the entry state of the walk ---------------------------------------------------------------------- *)
Lemma slw_entry_ok : forall ly S W regs mem md ch,
afn_pre SEGS B SUP_LV2_WORKER_SET_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_slw_entry
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_lv2_worker_set)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTKv. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn [slw_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. rewrite HSTKv in Hslo. repeat split; lia.
Qed.

(* --- the meter and budgets of the four calls --------------------------------------------------------- *)
Lemma slw_xm_nonneg : forall v, 0 <= XM_ARG_S MT v.
Proof. intros v. unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. Qed.
Lemma slw_xa_nonneg : forall t, 0 <= XM_ANSWER MT t.
Proof.
intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia.
Qed.
Lemma slw_xr_nonneg : forall R, 0 <= XM_RECORD MT R.
Proof.
intros R. unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL).
destruct (Nat.ltb (length (r_calls R)) 16); [lia | apply Z.mul_nonneg_nonneg; lia].
Qed.
Lemma slw_ev_nonneg : forall R, 0 <= EV_RECORD R.
Proof. intros R. unfold EV_RECORD, rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16); lia. Qed.

(* the footprints of record and arg_s lie below alloc_ceiling (the program statics and the recorder's blocks) *)
Lemma slw_FPR_low : forall ly S (W : world SEGS) mem md O R a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> (length (r_calls R) <= 16)%nat ->
inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
      (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O R a HAR HO Hlen (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, OFF_NCALLS in Ha. lia.
- pose proof (slw_slot_range R Hlen) as [_ Hs]. lia.
- destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
  destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & HpO & Hpa).
  pose proof (slw_blk_pos ly S W mem md p n HAR (HO _ HpO)) as (_ & _ & _ & Hc & _). lia.
Qed.
Lemma slw_FPA_in : forall (c : Z) (A : list (list byte)) a,
inFP (if Z.of_nat (length A) <? REC_ARGS_MAX
      then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
            (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A), c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
      else []) a ->
c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4 \/
c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8.
Proof.
intros c A a (r & Hr & Ha). destruct (Z.of_nat (length A) <? REC_ARGS_MAX); [|destruct Hr].
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [left | right]; exact Ha.
Qed.
Lemma slw_FPA_low : forall (c : Z) (A : list (list byte)) a, 4096 <= c -> c + 56 <= 2 ^ 40 -> (length A <= 6)%nat ->
inFP (if Z.of_nat (length A) <? REC_ARGS_MAX
      then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
            (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A), c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
      else []) a -> a < alloc_ceiling.
Proof.
intros c A a Hc1 Hc2 HA (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct (Z.of_nat (length A) <? REC_ARGS_MAX); [|destruct Hr].
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha; lia.
Qed.

(* the program statics lie in the image's span *)
Lemma slw_PG_low : forall a, Exists (in_zr a) slw_PG -> 0x10000 <= a < 0x606000.
Proof.
intros a HP. apply Exists_exists in HP as (r & Hr & Hz). unfold slw_PG, TFIB_PROG_STATIC in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; unfold in_zr in Hz; cbn [fst snd] in Hz; lia.
Qed.

(* a string handed to answer (astr_argA, either arm) lies below alloc_ceiling *)
Lemma slw_argA_low : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) -> forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly S W mem md rd O p x HAR H i Hi. pose proof asan_consts as (C1 & _ & _ & _ & C5).
cbn [astr_argA] in H. destruct H as (H0 & Hs & Hn & [((b & k & Hb & Hb1 & Hb2) & _) | (Hro & _)]).
- pose proof (slw_blk_pos ly S W mem md b k HAR Hb) as (Hb4 & _ & Hbc & _). lia.
- destruct (Hro i Hi) as (Hr & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
  pose proof (pa_segs_low _ Himg). lia.
Qed.

Local Ltac slw_awr HSTKv Usp :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTKv; lia | cbn; lia | apply awr_ok_nil].

(* --- the walk ------------------------------------------------------------------------------------------- *)
Theorem tsup_lv2_worker_set_holds : tsup_lv2_worker_set_spec B MT.
Proof.
unfold tsup_lv2_worker_set_spec.
intros ly S W regs mem md ch pu pw uri worker R O HPRE HRM HROD HROK H10 Hpu H11 Hpw HU HWK HREP HFR8 HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
assert (HRSv : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HASv : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HRSOv : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (HANv : ANSWER_STK = 16592) by (vm_compute; reflexivity).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (rec_repA_in B ly S _ R O HREP).
assert (Hlen : (length (r_calls R) <= 16)%nat) by exact (slw_rep_len B _ _ _ _ _ HREP).
destruct HU as (xu & -> & (bu & mu & Hbu & Hbu1 & Hbu2) & Hus & Hun & Hua).
destruct HWK as (xw & -> & (bw & mw & Hbw & Hbw1 & Hbw2) & Hws & Hwn & Hwa).
assert (HbuO : ~ In (bu, mu) O).
{ intros Hin. rewrite Forall_forall in Hua. pose proof (Hua _ Hin) as D. unfold iv_apart in D. cbn [fst snd] in D. lia. }
assert (HbwO : ~ In (bw, mw) O).
{ intros Hin. rewrite Forall_forall in Hwa. pose proof (Hwa _ Hin) as D. unfold iv_apart in D. cbn [fst snd] in D. lia. }
destruct (slw_blk_pos ly S W mem md bu mu HAR Hbu) as (Hbu4 & Hmu0 & Hbuc & _ & Hbur).
destruct (slw_blk_pos ly S W mem md bw mw HAR Hbw) as (Hbw4 & Hmw0 & Hbwc & _ & Hbwr).
set (sp0 := spZ regs) in *.
set (TOT := XM_SUP_LV2_WORKER_SET MT R (Some xu) (Some xw)) in *.
set (y := sup_lv2_worker_set_m R (Some xu) (Some xw)) in *.
pose proof (ajournal_init SEGS B SUP_LV2_WORKER_SET_STK (slw_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof (slw_entry_ok ly S W regs mem md ch HPRE) as HS.
unfold cfg_at. change (w64 (BASE + AF_sup_lv2_worker_set)) with (Z_to_bv 64 (BASE + AF_sup_lv2_worker_set)).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* run 1: the prologue to the call of record at 0x8c0ec *)
paj_run_shc RUNP RUNC HS HJ.
{ slw_awr HSTKv Usp. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
assert (Esp1 : spZ (ms_regs ms1) = sp0 + -32).
{ unfold spZ at 1. rewrite R2, Usp. apply unsigned_lit_small. rewrite HSTKv in Hslo. lia. }
(* the prologue writes only the frame *)
assert (KEEP1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'. destruct Hr' as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp in Hw. rewrite HSTKv in Hslo. lia. }
assert (HREP1 : rec_repA B ly S (rdW W (ms_mem ms1)) R O).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S _ R O HREP HOb).
  - intros a Ha. apply KEEP1. unfold A_G_REC in *. lia.
  - intros a Ha. apply KEEP1. unfold A_REC_SPILL in *. lia.
  - intros p n i Hin Hi. destruct (slw_blk_pos ly S W mem md p n HAR (HOb _ Hin)) as (H4 & _ & Hc & _). apply KEEP1. lia. }
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms1))) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJ HROD).
assert (HEV1 : st_nev S + EV_RECORD R <= EV_MAX).
{ unfold EV_SUP_LV2_WORKER_SET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia. }
assert (HMOK1 : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S (XM_RECORD MT R) TOT HMOK). unfold TOT, XM_SUP_LV2_WORKER_SET.
  pose proof (slw_xm_nonneg (Some xu)). pose proof (slw_xm_nonneg (Some xw)). pose proof (slw_xa_nonneg (snd y)). fold y. lia. }
assert (Hch1 : achain ly (rdW W (ms_mem ms1)) (sp0 + -32) (s0Z (ms_regs ms1)) []).
{ apply achain_low. unfold s0Z. rewrite R8, (EE 11%nat 11%bv eq_refl), H11. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pmkst HS. rewrite (CmdRecAns.rca_sig_record (PI := PI) SIGP).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms1) (ms_mem ms1) _ SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK
    ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
     (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O))
    (EV_RECORD R) (-32) (Z_to_bv 64 (BASE + 23488)) []
    (fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
      getr regs' 10 = w64 (rec_slot R) /\
      Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
      Z.of_nat (length F) = rec_spill_frees R /\
      (forall pn, In pn F -> In pn O) /\
      rec_repA B ly' S' (rdW W' mem') (rec_record R REC_LV2_WORKER_SET []) O' /\
      (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
      blocks_bytes S' <= blocks_bytes S /\
      mo_le MT S S' (XM_RECORD MT R)) HJ Esp1).
  - reflexivity.
  - lia.
  - rewrite HRSv. lia.
  - rewrite HRSv, HSTKv. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPREx. eapply SRr_mono.
    + apply (TRECORD fx ly S W (ms_regs ms1) (ms_mem ms1) _ [] REC_LV2_WORKER_SET R O HPREx HROD1).
      * rewrite R10. reflexivity.
      * unfold REC_LV2_WORKER_SET, REC_FN_COUNT. lia.
      * exact HREP1.
      * exact HEV1.
      * exact HMOK1.
    + cbv beta. unfold apost_base. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJx & HPx & HKx).
      exists ly', S', regs', mem', md'. split; [rewrite R1; reflexivity | split; [exact HJx | split; [exact HPx | exact HKx]]].
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply slw_awr_prog. left. unfold OFF_NCALLS, A_G_REC, REC_SIZE in *. lia.
    + apply slw_awr_prog. replace a with (rec_slot R + (a - rec_slot R)) by lia.
      apply slw_slot_in; [exact Hlen | unfold CALL_SIZE; lia].
    + destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
      right; left. split.
      * exists r. split; [right; right; exact Hr | exact Ha].
      * destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & HpO & Hpa).
        exists p, n. split; [exact (HOb _ HpO) | exact Hpa].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (slw_FPR_low ly S W mem md O R a HAR HOb Hlen Ha). rewrite HSTKv in Hslo. lia. }
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJr & HP1 &
  (F & O1 & Ha01 & Hperm1 & HlenF & HFO & HREP1' & HO1 & Hbb1 & MLE1)).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & HFRM1 & HNEV1 & _ & _ & _ & _ & _ & _ & HJ1pres & _).
jafter_call_keep_pi HS 32%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (slw_region_kept_hi2 SEGS E (w_H W) (w_H W1) (ms_mem ms1) mem1 2 sp0); [exact Usp | |].
  - intros a Ha. apply (slw_callee_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJr).
    + intros x Hx. exact (slw_FPR_low ly S W mem md O R x HAR HOb Hlen Hx).
    + lia.
  - intros a Ha. apply HJ1pres. rewrite HSTKv. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs1) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 32)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hn).
assert (E36 : ew E1 36 = w64 (rec_slot R)) by (rewrite HE1; cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha01).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by lia; exact Usp).
(* run 2: `mv s2,a0; mv a1,s1` to the call of arg_s at 0x8c0f8 *)
paj_run_shc RUNP RUNC HS HJ1.
{ slw_awr HSTKv Usp1. }
clear HF HG. rename HFr into HFr2. rename ms into ms2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (18%bv : bv 5) Q18.
assert (Esp2 : spZ (ms_regs ms2) = sp0 + -32).
{ unfold spZ at 1. rewrite Q2, Usp1. apply unsigned_lit_small. rewrite HSTKv in Hslo. lia. }
assert (KEEP2 : forall a, 0 <= a < alloc_ceiling -> rdW W1 (ms_mem ms2) a = rdW W1 mem1 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E1 _ (w_H W1) mem1 (ms_mem ms2) a HFr2); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'. destruct Hr' as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp1 in Hw. rewrite HSTKv in Hslo. lia. }
pose proof (proj1 HJ1) as HAR2.
assert (Hbu1' : In (bu, mu) (ablocks B ly1 S1)).
{ pose proof (Permutation_in _ Hperm1 Hbu) as H. apply in_app_iff in H as [H|H]; [exact H | exfalso; exact (HbuO (HFO _ H))]. }
assert (Hbw1' : In (bw, mw) (ablocks B ly1 S1)).
{ pose proof (Permutation_in _ Hperm1 Hbw) as H. apply in_app_iff in H as [H|H]; [exact H | exfalso; exact (HbwO (HFO _ H))]. }
assert (Hus2 : astr_atR (rdW W1 (ms_mem ms2)) pu xu).
{ apply (rastr_kept (rdW W mem)); [exact Hus|]. intros i Hi.
  apply (slw_blk_kept _ _ ly S W mem md O ly1 S1 W1 (ms_mem ms2) _ _ bu mu (pu + i) HAR HOb HJ1 Hbu HbuO Hbu1'). lia. }
assert (HREP2 : rec_repA B ly1 S1 (rdW W1 (ms_mem ms2)) (rec_record R REC_LV2_WORKER_SET []) O1).
{ apply (rec_repA_kept B ly1 S1 (rdW W1 mem1) ly1 S1 _ _ O1 HREP1' (rec_repA_in B _ _ _ _ _ HREP1')).
  - intros a Ha. apply KEEP2. unfold A_G_REC in *. lia.
  - intros a Ha. apply KEEP2. unfold A_REC_SPILL in *. lia.
  - intros p n i Hin Hi. destruct (slw_blk_pos ly1 S1 W1 mem1 md1 p n HAR1 (rec_repA_in B _ _ _ _ _ HREP1' _ Hin)) as (H4 & _ & Hc & _).
    apply KEEP2. lia. }
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms2))) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJ1 HROD).
assert (HROK2 : cmd_ro_ok (rdW W1 (ms_mem ms2))) by exact (cmd_ro_ok_of_aro ly1 S1 W1 (ms_mem ms2) _ HAR2 HROD2).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & HNEV2 & _).
assert (HEV2 : st_nev S1 + EV_ARG_S <= EV_MAX).
{ pose proof (slw_ev_nonneg R). unfold EV_SUP_LV2_WORKER_SET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (HLIVE2 : blocks_bytes S1 + LIVE_ARG_S (Some xu) <= LIVE_MAX).
{ unfold LIVE_SUP_LV2_WORKER_SET in HLIVE. fold y in HLIVE. unfold LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in *. lia. }
assert (HMOK2 : mo_ok MT S1 (XM_ARG_S MT (Some xu))).
{ apply (mok_station MT S S1 TOT (XM_RECORD MT R) _ MTL HMOK MLE1 (slw_xm_nonneg _)). unfold TOT, XM_SUP_LV2_WORKER_SET.
  pose proof (slw_xm_nonneg (Some xw)). pose proof (slw_xa_nonneg (snd y)). fold y. lia. }
assert (Hch2 : achain ly1 (rdW W1 (ms_mem ms2)) (sp0 + -32) (s0Z (ms_regs ms2)) []).
{ apply achain_low. unfold s0Z. rewrite Q8, OLD1, (EE 11%nat 11%bv eq_refl), H11 by lia. unfold w64. rewrite unsigned_lit_small by lia. lia. }
destruct (slw_slot_range R Hlen) as [Hc4 Hc40].
pmkst HS. rewrite (slw_sig_arg_s SIGP).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W1 (ms_regs ms2) (ms_mem ms2) _ SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] ly1 S1 _ _
    ARG_S_STK _ _ (-32) (getr (ms_regs ms2) 1) [] _ HJ1 Esp2).
  - reflexivity.
  - lia.
  - rewrite HASv. lia.
  - rewrite HASv, HSTKv. lia.
  - rewrite Q3, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Q4, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - exact Hch2.
  - intros HPREx.
    exact (TARG_S fx ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) _ [] (rec_slot R) pu REC_LV2_WORKER_SET [] (Some xu) R O1
      HPREx HROD2 HROK2 ltac:(rewrite Q10; exact E36) ltac:(rewrite Q11, OLD1, (EE 10%nat 10%bv eq_refl) by lia; exact H10)
      eq_refl HREP2
      ltac:(left; cbn [astr_argA]; split; [lia|]; split; [exact Hus2|]; split; [exact Hun|];
            left; split; [exists bu, mu; split; [exact Hbu1' | lia] | constructor])
      ltac:(intros x Hx; injection Hx as <-; eapply (cmd_heap_tail_vis ly1 S1 W1 (ms_mem ms2) _ bu mu); [exact HAR2 | exact Hbu1' | lia])
      HEV2 HLIVE2 HMOK2).
  - intros a (r & Hr & Ha).
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; apply slw_awr_prog;
    replace a with (rec_slot R + (a - rec_slot R)) by lia; apply slw_slot_in; try exact Hlen;
    cbn [length Z.of_nat] in Ha; unfold CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. exfalso.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha;
    rewrite HSTKv in Hslo; lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJa1 & HP2 & (Hbb2 & MLE2 & HK2)).
destruct HK2 as [(H6 & _) | (_ & p1 & HK2)]; [exfalso; unfold REC_ARGS_MAX in H6; cbn in H6; lia|].
cbv zeta in HK2. cbn [sarg app] in HK2. destruct HK2 as (Hp1 & Hperm2 & Hap2 & HREP2').
rewrite Q1.
pose proof (proj1 HJ2) as HAR3.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (slw_region_kept_hi2 SEGS E1 (w_H W1) (w_H W2) (ms_mem ms2) mem2 2 sp0); [exact Usp1 | |].
  - intros a Ha. apply (slw_callee_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJa1).
    + intros x (r & Hr & Hx).
      destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Hx; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hx; lia.
    + lia.
  - intros a Ha. apply HJ2pres. rewrite HSTKv. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E1 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall n, (n < 48)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by lia; exact Usp1).
(* run 3: `mv a0,s2; mv a1,s0` to the call of arg_s at 0x8c104 *)
paj_run_shc RUNP RUNC HS HJ2.
{ slw_awr HSTKv Usp2. }
clear HF HG. rename HFr into HFr3. rename ms into ms3.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
assert (Esp3 : spZ (ms_regs ms3) = sp0 + -32).
{ unfold spZ at 1. rewrite T2, Usp2. apply unsigned_lit_small. rewrite HSTKv in Hslo. lia. }
assert (KEEP3 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms3) a = rdW W2 mem2 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E2 _ (w_H W2) mem2 (ms_mem ms3) a HFr3); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'. destruct Hr' as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp2 in Hw. rewrite HSTKv in Hslo. lia. }
pose proof (proj1 HJ2) as HAR3'.
assert (Hbw2' : In (bw, mw) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hbw1').
assert (Hws3 : astr_atR (rdW W2 (ms_mem ms3)) pw xw).
{ apply (rastr_kept (rdW W mem)); [exact Hws|]. intros i Hi.
  apply (slw_blk_kept _ _ ly S W mem md O ly2 S2 W2 (ms_mem ms3) _ _ bw mw (pw + i) HAR HOb HJ2 Hbw HbwO Hbw2'). lia. }
assert (HREP3 : rec_repA B ly2 S2 (rdW W2 (ms_mem ms3)) (rec_record R REC_LV2_WORKER_SET [xu])
  ((p1, Z.of_nat (length xu) + 1) :: O1)).
{ apply (rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ _ HREP2' (rec_repA_in B _ _ _ _ _ HREP2')).
  - intros a Ha. apply KEEP3. unfold A_G_REC in *. lia.
  - intros a Ha. apply KEEP3. unfold A_REC_SPILL in *. lia.
  - intros p n i Hin Hi. destruct (slw_blk_pos ly2 S2 W2 mem2 md2 p n HAR3 (rec_repA_in B _ _ _ _ _ HREP2' _ Hin)) as (H4 & _ & Hc & _).
    apply KEEP3. lia. }
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms3))) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJ2 HROD).
assert (HROK3 : cmd_ro_ok (rdW W2 (ms_mem ms3))) by exact (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms3) _ HAR3' HROD3).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & HNEV3 & _).
assert (HEV3 : st_nev S2 + EV_ARG_S <= EV_MAX).
{ pose proof (slw_ev_nonneg R). unfold EV_SUP_LV2_WORKER_SET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (HLIVE3 : blocks_bytes S2 + LIVE_ARG_S (Some xw) <= LIVE_MAX).
{ unfold LIVE_SUP_LV2_WORKER_SET in HLIVE. fold y in HLIVE. unfold LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in *. lia. }
pose proof (mle_station MT S S1 S2 _ _ MTL MLE1 MLE2) as MLE12.
assert (HMOK3 : mo_ok MT S2 (XM_ARG_S MT (Some xw))).
{ apply (mok_station MT S S2 TOT _ _ MTL HMOK MLE12 (slw_xm_nonneg _)). unfold TOT, XM_SUP_LV2_WORKER_SET.
  pose proof (slw_xa_nonneg (snd y)). fold y. lia. }
assert (Hch3 : achain ly2 (rdW W2 (ms_mem ms3)) (sp0 + -32) (s0Z (ms_regs ms3)) []).
{ apply achain_low. unfold s0Z. rewrite T8, OLD2, OLD1, (EE 11%nat 11%bv eq_refl), H11 by lia. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
pmkst HS. rewrite (slw_sig_arg_s SIGP).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs ms3) (ms_mem ms3) _ SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] ly2 S2 _ _
    ARG_S_STK _ _ (-32) (getr (ms_regs ms3) 1) [] _ HJ2 Esp3).
  - reflexivity.
  - lia.
  - rewrite HASv. lia.
  - rewrite HASv, HSTKv. lia.
  - rewrite T3, OLD2, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite T4, OLD2, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite T1, unsigned_lit_small by lia. lia.
  - exact Hch3.
  - intros HPREx.
    exact (TARG_S fx ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ [] (rec_slot R) pw REC_LV2_WORKER_SET [xu] (Some xw) R
      ((p1, Z.of_nat (length xu) + 1) :: O1)
      HPREx HROD3 HROK3 ltac:(rewrite T10, OLD2 by lia; exact E36)
      ltac:(rewrite T11, OLD2, OLD1, (EE 11%nat 11%bv eq_refl) by lia; exact H11)
      eq_refl HREP3
      ltac:(left; cbn [astr_argA]; split; [lia|]; split; [exact Hws3|]; split; [exact Hwn|];
            left; split; [exists bw, mw; split; [exact Hbw2' | lia] | constructor])
      ltac:(intros x Hx; injection Hx as <-; eapply (cmd_heap_tail_vis ly2 S2 W2 (ms_mem ms3) _ bw mw); [exact HAR3' | exact Hbw2' | lia])
      HEV3 HLIVE3 HMOK3).
  - intros a (r & Hr & Ha).
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; apply slw_awr_prog;
    replace a with (rec_slot R + (a - rec_slot R)) by lia; apply slw_slot_in; try exact Hlen;
    cbn [length Z.of_nat] in Ha; unfold CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  - intros ly' S' W' regs' mem' md' _ a (r & Hr & Ha) Hw _. exfalso.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha;
    rewrite HSTKv in Hslo; lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJa2 & HP3 & (Hbb3 & MLE3 & HK3)).
destruct HK3 as [(H6 & _) | (_ & p2 & HK3)]; [exfalso; unfold REC_ARGS_MAX in H6; cbn in H6; lia|].
cbv zeta in HK3. cbn [sarg app] in HK3. destruct HK3 as (Hp2 & Hperm3 & Hap3 & HREP3').
rewrite T1.
(* the call of rec_shape_of at 0x8c114 *)
pose proof (proj1 HJ3) as HAR4.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (slw_region_kept_hi2 SEGS E2 (w_H W2) (w_H W3) (ms_mem ms3) mem3 2 sp0); [exact Usp2 | |].
  - intros a Ha. apply (slw_callee_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJa2).
    + intros x (r & Hr & Hx).
      destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat] in Hx; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hx; lia.
    + lia.
  - intros a Ha. apply HJ3pres. rewrite HSTKv. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E2 64 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 64)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp2).
(* run 4: a0 = .str.13 (the auipc/addi pair), a1 = 14 *)
paj_run_shc RUNP RUNC HS HJ3.
{ slw_awr HSTKv Usp3. }
clear HF HG. rename HFr into HFr4. rename ms into ms4.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
assert (Esp4 : spZ (ms_regs ms4) = sp0 + -32).
{ unfold spZ at 1. rewrite U2, Usp3. apply unsigned_lit_small. rewrite HSTKv in Hslo. lia. }
assert (KEEP4 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem ms4) a = rdW W3 mem3 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E3 _ (w_H W3) mem3 (ms_mem ms4) a HFr4); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'. destruct Hr' as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp3 in Hw. rewrite HSTKv in Hslo. lia. }
pose proof (proj1 HJ3) as HAR4'.
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms4))) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJ3 HROD).
assert (HROK4 : cmd_ro_ok (rdW W3 (ms_mem ms4))) by exact (cmd_ro_ok_of_aro ly3 S3 W3 (ms_mem ms4) _ HAR4' HROD4).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & HNEV4 & _).
assert (HEV4 : st_nev S3 + EV_REC_SHAPE_OF <= EV_MAX).
{ pose proof (slw_ev_nonneg R). unfold EV_SUP_LV2_WORKER_SET, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (U10' : getr (ms_regs ms4) 10 = w64 0x21ee0).
{ rewrite U10. change 316%nat with (A_OBJ 75). apply bv_eq. rewrite (HEI3 (A_OBJ 75)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (slw_lit_val VOBJS). unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (U11' : getr (ms_regs ms4) 11 = w64 (Z.of_nat (length slw_verb))) by (rewrite U11, slw_verb_len; reflexivity).
pmkst HS. rewrite (slw_sig_rec_shape_of SIGP).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W3 (ms_regs ms4) (ms_mem ms4) _ SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] ly3 S3 _ _
    REC_SHAPE_OF_STK _ _ (-32) (getr (ms_regs ms4) 1) _ HJ3 Esp4).
  - reflexivity.
  - lia.
  - rewrite HRSOv. lia.
  - rewrite HRSOv, HSTKv. lia.
  - rewrite U3, OLD3, OLD2, OLD1, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite U4, OLD3, OLD2, OLD1, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - reflexivity.
  - rewrite U1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite U1, unsigned_lit_small by lia. lia.
  - intros HPREx.
    exact (TREC_SHAPE_OF fx ly3 S3 W3 (ms_regs ms4) (ms_mem ms4) _ 0x21ee0 slw_verb HPREx HROD4 U10' ltac:(lia) U11'
      ltac:(rewrite slw_verb_len; lia) HROK4 VOBJS (slw_verb_ok B HB ly3 S3 _ HROK4 CMD_RO_IN) HEV4).
  - intros a (r & [] & _). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJs & HP4 & ((qs & Hqs10 & Hqsr & Hqs) & Hperm4 & -> & ->)).
rewrite U1.
pose proof (proj1 HJ4) as HAR5.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
jafter_call_keep_pi HS 80%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (slw_region_kept_hi2 SEGS E3 (w_H W3) (w_H W4) (ms_mem ms4) mem4 2 sp0); [exact Usp3 | |].
  - intros a Ha. apply (slw_callee_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJs); [intros x (r & [] & _) | lia].
  - intros a Ha. apply HJ4pres. rewrite HSTKv. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E3 80 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 80)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (E84 : ew E4 84 = w64 qs) by (rewrite HE4; cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Hqs10).
clear HE4.
assert (OLDall : forall n, (n < 32)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite OLD4, OLD3, OLD2, OLD1 by lia; reflexivity).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLDall by lia; exact Usp).
(* run 5: `li a2,1; mv a1,a0; mv a0,s2`, the epilogue, and the tail jump `j answer` at 0x8c138 *)
paj_run_shc RUNP RUNC HS HJ4.
{ slw_awr HSTKv Usp4. }
clear HF HG. rename HFr into HFr5. rename ms into ms5.
prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
prreg HS (8%bv : bv 5) V8. prreg HS (10%bv : bv 5) V10. prreg HS (11%bv : bv 5) V11. prreg HS (12%bv : bv 5) V12.
(* the tail jump into answer (0x8c138): answer runs at the entry's sp and returns to the entry's ra *)
assert (QA1 : getr (ms_regs ms5) 1 = getr regs 1) by (rewrite V1, OLDall by lia; exact (EE 1%nat 1%bv eq_refl)).
assert (QA2 : getr (ms_regs ms5) 2 = getr regs 2) by (rewrite V2, OLDall by lia; exact (EE 2%nat 2%bv eq_refl)).
assert (QA3 : getr (ms_regs ms5) 3 = w64 (as_gp B)) by (rewrite V3, OLDall, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp).
assert (QA4 : getr (ms_regs ms5) 4 = w64 (as_tp B)) by (rewrite V4, OLDall, (EE 4%nat 4%bv eq_refl) by lia; exact Htp).
assert (QA10 : getr (ms_regs ms5) 10 = w64 (rec_slot R)) by (rewrite V10, OLD4, OLD3, OLD2 by lia; exact E36).
assert (QA11 : getr (ms_regs ms5) 11 = w64 qs) by (rewrite V11; exact E84).
assert (HspA : spZ (ms_regs ms5) = sp0 + 0) by (unfold spZ at 1; rewrite QA2; unfold sp0, spZ; lia).
assert (HPRA : aregs_preserved regs (ms_regs ms5)).
{ apply slw_aregs. intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ rewrite (st_ok_restrict_reg SEGS _ E4 _ _ _ HS); cbn [ms_regs];
      lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
        let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      lazymatch goal with |- ew E4 ?n = getr regs (Z_to_bv 5 ?m) =>
        rewrite (OLDall n) by lia; apply (EE n); reflexivity end
    | ]).
  destruct Hr. }
assert (KEEP5 : forall a, 0 <= a < alloc_ceiling -> rdW W4 (ms_mem ms5) a = rdW W4 mem4 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E4 _ (w_H W4) mem4 (ms_mem ms5) a HFr5); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'. destruct Hr' as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite Usp4 in Hw. rewrite HSTKv in Hslo. lia. }
pose proof (slw_callee_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ HJs) as [CKp CKb].
assert (KK : forall a, (Exists (in_zr a) slw_PG \/ exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + m) ->
  rdW W4 (ms_mem ms5) a = rdW W3 mem3 a).
{ intros a Ha.
  assert (Hlo : 0 <= a < alloc_ceiling).
  { destruct Ha as [HP | (b & m & Hb & Hab)].
    - pose proof (slw_PG_low a HP). lia.
    - destruct (slw_blk_pos _ _ _ _ _ _ _ HAR4' Hb) as (H4 & _ & Hc & _). lia. }
  rewrite (KEEP5 a Hlo). rewrite <- (KEEP4 a Hlo).
  destruct Ha as [HP | (b & m & Hb & Hab)].
  - exact (CKp a HP).
  - destruct (slw_blk_pos _ _ _ _ _ _ _ HAR4' Hb) as (_ & Hm0 & _ & _ & Hmr).
    replace a with (b + (a - b)) by lia. apply (CKb b m (a - b) Hb Hb). lia. }
set (OA := (p2, Z.of_nat (length xw) + 1) :: (p1, Z.of_nat (length xu) + 1) :: O1).
set (RA := rec_record R REC_LV2_WORKER_SET [xu; xw]).
assert (HREPA : rec_repA B ly3 S3 (rdW W4 (ms_mem ms5)) RA OA).
{ apply (rec_repA_kept B ly3 S3 (rdW W3 mem3) ly3 S3 _ _ _ HREP3' (rec_repA_in B _ _ _ _ _ HREP3')).
  - intros a Ha. apply KK. left. apply slw_in_grec. exact Ha.
  - intros a Ha. apply KK. left. apply slw_in_spill. exact Ha.
  - intros p n i Hin Hi. apply KK. right. exists p, n. split; [exact (rec_repA_in B _ _ _ _ _ HREP3' _ Hin) | lia]. }
destruct (slw_old_answer B _ _ _ _ _ HREPA) as (old & Hold & Hold').
assert (Holdb : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm)]; [lia|].
  destruct (slw_blk_pos _ _ _ _ _ _ _ HAR4' (rec_repA_in B _ _ _ _ _ HREPA _ Hm)) as (H4 & Hm0 & Hc & _). lia. }
assert (Hn1 : ~ In (p1, Z.of_nat (length xu) + 1) (ablocks B ly1 S1)) by (apply slw_fresh_notin; [lia | exact Hap2]).
assert (Hn2 : ~ In (p2, Z.of_nat (length xw) + 1) ((p1, Z.of_nat (length xu) + 1) :: ablocks B ly1 S1)).
{ intros Hin. apply (slw_fresh_notin p2 (Z.of_nat (length xw) + 1) (ablocks B ly2 S2) ltac:(lia) Hap3).
  apply (Permutation_in _ (Permutation_sym Hperm2)). exact Hin. }
assert (HP3' : Permutation (ablocks B ly3 S3)
  ((p2, Z.of_nat (length xw) + 1) :: (p1, Z.of_nat (length xu) + 1) :: ablocks B ly1 S1))
  by (eapply perm_trans; [exact Hperm3 | apply perm_skip; exact Hperm2]).
assert (HOA : forall pn, In pn OA -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn Hpn. destruct Hpn as [<- | [<- | Hpn]].
  - destruct (in_dec recb_pair_dec (p2, Z.of_nat (length xw) + 1) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    pose proof (Permutation_in _ Hperm1 Hin) as H. apply in_app_iff in H as [H|H]; [exfalso; apply Hn2; right; exact H | exact (HFO _ H)].
  - destruct (in_dec recb_pair_dec (p1, Z.of_nat (length xu) + 1) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    pose proof (Permutation_in _ Hperm1 Hin) as H. apply in_app_iff in H as [H|H]; [exfalso; exact (Hn1 H) | exact (HFO _ H)].
  - left. exact (proj1 (proj1 (HO1 pn) Hpn)). }
assert (HM : y = rec_answer RA (REC_LV2_WORKER_SET, [xu; xw]) (shape_of slw_verb) true) by exact (slw_model R (Some xu) (Some xw)).
pose proof HJ4 as (_ & HLYA & _ & _ & _ & HFRA & HNEVA & _).
pose proof (mle_station MT S S2 S3 _ _ MTL MLE12 MLE3) as MLE123.
assert (HROA : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5))) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOb HJ4 HROD).
pose proof (proj1 HJ4) as HARA.
assert (Hach : achain ly3 (rdW W4 (ms_mem ms5)) (sp0 + 0) (s0Z (ms_regs ms5)) ch).
{ assert (Hs0 : s0Z (ms_regs ms5) = s0Z regs).
  { unfold s0Z. pose proof (HPRA 8 ltac:(unfold acallee_saved; lia)) as H8.
    replace (Z_to_bv 5 8) with (8%bv : bv 5) in H8 by (apply bv_eq; reflexivity). rewrite H8. reflexivity. }
  rewrite Hs0, Z.add_0_r.
  pose proof HLYA as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  apply (achain_ly_top ly ly3 _ sp0 (s0Z regs) ch Etop).
  apply (achain_kept ly (rdW W mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [rewrite HSTKv in Hslo; lia | rewrite HSTKv; lia |].
  intros HinF. pose proof (slw_FP_low ly S W mem md O a HAR HOb HinF). rewrite HSTKv in Hslo. lia. }
pmkst HS. rewrite (slw_sig_answer SIGP).
eapply SRr_mono.
{ eapply (PaFx.callS_wideF B LAWS W4 (ms_regs ms5) (ms_mem ms5) _ SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md []
    ly3 S3 _ _ ANSWER_STK _ _ 0 (getr (ms_regs ms5) 1) ch _ HJ4 HspA eq_refl ltac:(lia)
    ltac:(rewrite HANv; lia) ltac:(rewrite HANv, HSTKv; lia) QA3 QA4 eq_refl
    ltac:(rewrite QA1; exact Hra) ltac:(rewrite QA1; exact Hra4) Hach).
  - intros HPREA.
    pose proof (TANSWER fx ly3 S3 W4 (ms_regs ms5) (ms_mem ms5) _ ch (rec_slot R) qs old (REC_LV2_WORKER_SET, [xu; xw])
      (shape_of slw_verb) true RA OA HPREA HRM) as T.
    cbv zeta in T. apply T; clear T.
    + rewrite HFRA. exact HFR8.
    + exact HROA.
    + exact (cmd_ro_ok_of_aro _ _ _ _ _ HARA HROA).
    + exact QA10.
    + pose proof (slw_slot_range R Hlen). lia.
    + exact QA11.
    + exact Hqsr.
    + rewrite V12. reflexivity.
    + exact HREPA.
    + exact Hold.
    + exact Holdb.
    + intros _. split.
      * apply (slw_astr_argA_rd B ly3 S3 (rdW W4 mem4)); [exact (Hqs _)|]. intros i Hi.
        pose proof (slw_argA_low ly3 S3 W4 mem4 md4 _ [] qs _ HAR5 (Hqs []) i Hi) as Hlo. apply KEEP5. lia.
      * unfold fits. apply Z.leb_le. vm_compute. reflexivity.
    + intros _ _. unfold RA, rec_record, rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
      * left. exists (length (r_calls R)). split; [|reflexivity].
        cbn [set_calls r_calls]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
      * right. split; reflexivity.
    + pose proof (slw_ev_nonneg R). unfold EV_SUP_LV2_WORKER_SET, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_LV2_WORKER_SET in HLIVE. fold y in HLIVE. rewrite HM in HLIVE. unfold LIVE_ARG_S, LIVE_XMALLOC in *. lia.
    + apply (mok_station MT S S3 TOT _ _ MTL HMOK MLE123 (slw_xa_nonneg _)).
      unfold TOT, XM_SUP_LV2_WORKER_SET. fold y. rewrite HM. lia.
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]].
    + apply slw_awr_prog. left. cbn [fst snd] in Ha. unfold OFF_ANSWER, A_G_REC, REC_SIZE in *. lia.
    + apply slw_awr_prog. left. cbn [fst snd] in Ha. unfold OFF_STATE, A_G_REC, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
      apply slw_in_filter in Hin.
      assert (Hin3 : In (p, n) (ablocks B ly3 S3)) by exact (rec_repA_in B _ _ _ _ _ HREPA _ Hin).
      destruct (HOA (p, n) Hin) as [HinO | Hnew].
      * right; left. split.
        -- exists (p, p + req_size n). split; [right; right; unfold ablocks_fp; apply in_map_iff; exists (p, n); split; [reflexivity | exact HinO] | cbn; lia].
        -- exists p, n. split; [exact Hin3 | lia].
      * right; right; left. exists p, n. split; [exact Hin3|]. split; [exact Hnew | lia].
  - intros ly' S' W' regs' mem' md' _ a Ha Hw _. exfalso.
    destruct Ha as (r & Hr & Ha). rewrite HSTKv in Hslo.
    destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + unfold OFF_ANSWER, A_G_REC in Ha. lia.
    + unfold OFF_STATE, A_G_REC in Ha. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
      apply slw_in_filter in Hin.
      destruct (slw_blk_pos _ _ _ _ _ _ _ HAR4' (rec_repA_in B _ _ _ _ _ HREPA _ Hin)) as (_ & _ & _ & Hc & _). lia. }
cbv beta. intros W5 c5 Hwle5 (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & HFX5 & HCSR5 & HJ5 & HJan & HP5 & HK5).
unfold apost_baseF. exists fx5, ly5, S5, regs5, mem5, md5.
split; [rewrite QA1; reflexivity|].
split; [exact HFX5|]. split; [exact HCSR5|].
split.
{ eapply (ajournal_mono_k SEGS B); [exact HJ5|].
  pose proof (slw_ev_nonneg R). unfold EV_SUP_LV2_WORKER_SET, EV_REC_SHAPE_OF. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPRA HP5)|].
destruct HK5 as (p1' & q & O' & HK5). cbv zeta in HK5.
destruct HK5 as (HA10 & H4096 & Hne & HG1 & Hbl & Hrep' & HO' & Hstr & Hbb5 & Hmle).
set (t := snd (rec_answer RA (REC_LV2_WORKER_SET, [xu; xw]) (shape_of slw_verb) true)) in *.
set (nt := Z.of_nat (length t) + 1) in *.
destruct (slw_post_blocks ly S W mem md O ly1 S1 ly3 S3 W3 (ms_mem ms4) _ ly5 S5 W5 mem5 md5 F O1
  p1 (Z.of_nat (length xu) + 1) p2 (Z.of_nat (length xw) + 1) old OA p1' q nt O'
  HAR HAR4' (proj1 HJ5) Hperm1 HFO HO1 HP3' Hn1 Hn2 eq_refl (rec_repA_in B _ _ _ _ _ HREPA) Hold' Hne HG1 Hbl HO')
  as (P1 & P2 & P3 & P4 & P5 & P6).
exists (fst (rec_answer RA (REC_LV2_WORKER_SET, [xu; xw]) (shape_of slw_verb) true)), t, q, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact HA10|]. split; [exact H4096|]. split; [exact Hrep'|].
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact Hstr|].
split; [exact P5|]. split; [exact P6|].
split.
{ unfold LIVE_SUP_LV2_WORKER_SET. fold y. rewrite HM. fold t. lia. }
unfold TOT, XM_SUP_LV2_WORKER_SET. fold y. rewrite HM. fold t.
exact (mle_station MT S S3 S5 _ _ MTL MLE123 Hmle).
Qed.

Print Assumptions tsup_lv2_worker_set_holds.

End e.
End f.
End d.

Print Assumptions tsup_lv2_worker_set_holds.
