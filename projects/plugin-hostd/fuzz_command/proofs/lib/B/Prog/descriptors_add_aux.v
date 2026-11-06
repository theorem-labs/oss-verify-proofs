(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of descriptors_add's ASan+UBSan walk (plugin-hostd/fuzz_command,
   image fuzz_command.asan-ubsan) that need no callee statement: the listing of the function, the symbolic
   states that start its four straight-line segments with the executor's run over each, the state checks of those
   states, and the recorder's representation after the store of g_rec.state. Copied in part from the ASan walk
   (lib/A/Prog/descriptors_add_s1.v, descriptors_add_s2.v and descriptors_add_m.v on a working branch),
   re-derived on B's code.

   B's code (entry BASE + AF_descriptors_add = 0x8cc54, 20 instructions, 80 bytes; no branch, no inline ASan check,
   no __asan_report call, no UBSan trap site):
     0x8cc54 .. 0x8cc68  the 32-byte frame (ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24), s0 := uri, a0 := 22
     0x8cc6c             jal record                      (returns the slot c in a0)
     0x8cc70 .. 0x8cc74  s1 := c, a1 := uri
     0x8cc78             jal arg_s
     0x8cc7c .. 0x8cc84  s0 := 0x5e3c7c (auipc), a0 := g_rec.state (ld through the auipc, 0x5e3670), a1 := c
     0x8cc88             jal mix_call                    (returns the digest in a0)
     0x8cc8c .. 0x8cca0  g_rec.state := a0 (sd a0, -0x60c(s0)), the frame popped, ret
   The store at 0x8cc8c is a plain word whose base is s0, the auipc value pa_val (A_HI 203): the walk needs that
   value, which the statement does not carry (it carries cmd_val_objs only), so the section below takes
   `VHIS : cmd_val_his` (CmdObj.v:41) as a PROVISIONAL named hypothesis, for that one value. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the listing ------------------------------------------------------------------------------------------- *)
Definition DAB_AFTER_RECORD : Z := AF_descriptors_add + 0x1c. (* 0x8cc70, after jal record *)
Definition DAB_AFTER_ARG_S : Z := AF_descriptors_add + 0x28.  (* 0x8cc7c, after jal arg_s *)
Definition DAB_AFTER_MIX : Z := AF_descriptors_add + 0x38.    (* 0x8cc8c, after jal mix_call *)
Definition DAB_RET : Z := AF_descriptors_add + 0x4c.          (* 0x8cca0, ret *)

(* the 20 slots from the entry: the listing names the three calls, the auipc (A_HI 203) and the load through it
   (g_rec.state, the object A_OBJ 86); the rest are the image's words *)
Lemma dab_listing : firstn 20 (skipn (Z.to_nat (AF_descriptors_add / 4)) cmd_listing) =
[PW 0xfe010113; PW 0x113c23; PW 0x813823; PW 0x913423; PW 0x50413; PW 0x1600513; PCall CS_record (1%bv : bv 5);
 PW 0x50493; PW 0x40593; PCall CS_arg_s (1%bv : bv 5); PHi (8%bv : bv 5) 203;
 PLdHi (10%bv : bv 5) (8%bv : bv 5) 203 (A_OBJ 86) 0x0 SZ8 true; PW 0x48593; PCall CS_mix_call (1%bv : bv 5);
 PW 0x9ea43a23; PW 0x1813083; PW 0x1013403; PW 0x813483; PW 0x2010113; PW 0x8067].
Proof. vm_compute. reflexivity. Qed.

(* the image's addresses behind the listing's names: the entry 0x8cc54, the callees' offsets, g_rec.state
   0x5e3670 (object 86) and the auipc value 0x5e3c7c (hi 203), 1548 bytes above it *)
Lemma dab_addrs :
cmd_text + AF_descriptors_add = 0x8cc54 /\
cmd_af CS_descriptors_add = AF_descriptors_add /\ cmd_af CS_record = AF_record /\
cmd_af CS_arg_s = AF_arg_s /\ cmd_af CS_mix_call = AF_mix_call /\
(86 < length cmd_objs)%nat /\ cmd_obj 86 = A_G_REC + OFF_STATE /\
(203 < length cmd_his)%nat /\ cmd_hi 203 = A_G_REC + OFF_STATE + 1548.
Proof. vm_compute. repeat split; first [reflexivity | lia]. Qed.

(* --- the symbolic states ----------------------------------------------------------------------------------- *)
(* atom 2 (sp) is 16-aligned and in the stack window *)
Definition dab_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* the entry: every register its own atom, the 32 bytes below sp writable *)
Definition dab_ss0 : sstate := mkSS AF_descriptors_add sr_atoms [stack_region 32] None dab_facts.
(* the callee-saved registers the prologue stores, in frame order from sp0 - 8 down *)
Definition dab_saved : list Z := [1; 8; 9].
(* the frame after the prologue, relative to the current sp (atom 2 = sp0 - 32): the caller's ra, s0, s1 at 24,
   16, 8 (atoms 32, 33, 34); read only *)
Definition dab_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
(* g_rec.state as the object the load at 0x8cc80 names (atom 35 = its value) *)
Definition dab_stateO : YP09.region := YP09.mkRegion (Some (A_OBJ 86)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
(* g_rec.state as the store at 0x8cc8c reaches it: 1548 bytes below the auipc value; written *)
Definition dab_stateH : YP09.region := YP09.mkRegion (Some (A_HI 203)) (-1548) (-1540) (-1548) (-1540) [].
(* the three states after a call: every register its own atom (after mix_call, s0 the auipc value) *)
Definition dab_ssR : sstate := mkSS DAB_AFTER_RECORD sr_atoms [dab_frame] None dab_facts.
Definition dab_ssA : sstate := mkSS DAB_AFTER_ARG_S sr_atoms [dab_frame; dab_stateO] None dab_facts.
Definition dab_ssM : sstate :=
mkSS DAB_AFTER_MIX (sr_set sr_atoms (8%bv : bv 5) (SOff (A_HI 203) 0)) [dab_frame; dab_stateH] None dab_facts.

(* --- the executor's run over each segment ------------------------------------------------------------------ *)
Definition dab_frame0 : YP09.region :=
YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
  [YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* 0x8cc54 .. 0x8cc6c: the prologue and the call of record(22) *)
Lemma dab_run_entry : sym_run_pi cmd_tpi 7 dab_ss0 =
(mkSS DAB_AFTER_RECORD
   (sr_set (sr_set (sr_set (sr_set sr_atoms (1%bv : bv 5) (SOff A_TEXT DAB_AFTER_RECORD)) (2%bv : bv 5) (SOff 2 (-32)))
     (8%bv : bv 5) (SOff 10 0)) (10%bv : bv 5) (SLit 22))
   [dab_frame0] None dab_facts, PRS_call CS_record).
Proof. vm_compute. reflexivity. Qed.
(* 0x8cc70 .. 0x8cc78: s1 := c, a1 := uri, the call of arg_s(c, uri) *)
Lemma dab_run_record : sym_run_pi cmd_tpi 3 dab_ssR =
(mkSS DAB_AFTER_ARG_S
   (sr_set (sr_set (sr_set sr_atoms (1%bv : bv 5) (SOff A_TEXT DAB_AFTER_ARG_S)) (9%bv : bv 5) (SOff 10 0))
     (11%bv : bv 5) (SOff 8 0))
   [dab_frame] None dab_facts, PRS_call CS_arg_s).
Proof. vm_compute. reflexivity. Qed.
(* 0x8cc7c .. 0x8cc88: s0 := the auipc value, a0 := g_rec.state, a1 := c, the call of mix_call(state, c) *)
Lemma dab_run_arg_s : sym_run_pi cmd_tpi 4 dab_ssA =
(mkSS DAB_AFTER_MIX
   (sr_set (sr_set (sr_set (sr_set sr_atoms (1%bv : bv 5) (SOff A_TEXT DAB_AFTER_MIX)) (8%bv : bv 5) (SOff (A_HI 203) 0))
     (10%bv : bv 5) (SOff 35 0)) (11%bv : bv 5) (SOff 9 0))
   [dab_frame; dab_stateO] None dab_facts, PRS_call CS_mix_call).
Proof. vm_compute. reflexivity. Qed.
(* 0x8cc8c .. 0x8cc9c: g_rec.state := the digest (a0), ra / s0 / s1 reloaded, sp back to sp0; stops at the ret *)
Lemma dab_run_mix : sym_run_to_pi cmd_tpi 6 DAB_RET dab_ssM =
(mkSS DAB_RET
   (sr_set (sr_set (sr_set (sr_set sr_atoms (1%bv : bv 5) (SOff 32 0)) (2%bv : bv 5) (SOff 2 32))
     (8%bv : bv 5) (SOff 33 0)) (9%bv : bv 5) (SOff 34 0))
   [dab_frame; YP09.mkRegion (Some (A_HI 203)) (-1548) (-1540) (-1548) (-1540)
                 [YP09.mkChunk (-1548) (CVal 8 (SOff 10 0))]] None dab_facts, PRS_running).
Proof. vm_compute. reflexivity. Qed.
(* the ret (jalr zero, 0(ra)): the walk leaves it to the return lemma (PaLibH's paj_ret_at) *)
Lemma dab_ret_slot : plookup cmd_tpi DAB_RET = Some (PW 0x8067).
Proof. vm_compute. reflexivity. Qed.

(* --- the model --------------------------------------------------------------------------------------------- *)
Lemma dab_rec_record_state : forall R fn A, r_state (rec_record R fn A) = r_state R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.
(* the call's model: record(22), the copy of the argument, and g_rec.state := mix_call(state, the slot) *)
Lemma dab_model : forall R uri,
descriptors_add_m R uri = set_state (rec_record R 22 [sarg uri]) (mixcall (r_state R) 22 [sarg uri]).
Proof.
intros R uri. unfold descriptors_add_m, rec_stub_mix, rec_mix, REC_DESCRIPTORS_ADD. cbn [fst snd].
rewrite dab_rec_record_state. reflexivity.
Qed.
Lemma dab_set_state_same : forall R, set_state R (r_state R) = R.
Proof. intros []. reflexivity. Qed.

(* --- the representation after the store of g_rec.state ---------------------------------------------------- *)
Lemma dab_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma dab_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma dab_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (dab_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma dab_acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (dab_aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (dab_aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (dab_aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (dab_rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma dab_aanswer_at_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 8 -> rd' (gr + OFF_ANSWER + i) = rd (gr + OFF_ANSWER + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. destruct t as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [apply (dab_aval_mem_kept rd); [exact A1 | intros k Hk; apply Ha; lia]|].
  split; [exact A2|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A4|]. split; [|exact A6].
  apply (dab_rastr_kept rd); [exact A5 | intros i Hi; apply (Hp pn i eq_refl); lia].
- apply (dab_aval_mem_kept rd); [exact H | intros k Hk; apply Ha; lia].
Qed.
Lemma dab_areply_at_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 16 -> rd' (gr + OFF_REPLY + i) = rd (gr + OFF_REPLY + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold OFF_REPLY_SIZE, OFF_REPLY in *.
destruct y as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  split; [apply (dab_aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  split; [apply (dab_aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia]|].
  split; [exact A3|]. split; [exact A4|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A6|]. split; [|exact A8].
  apply (dab_rabytes_kept rd); [exact A7 | intros i Hi; apply (Hp pn i eq_refl); lia].
- destruct H as (A1 & A2).
  split; [apply (dab_aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  apply (dab_aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia].
Qed.
Lemma dab_lay_calls_in : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn HP Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ HP) | exact Hpn].
Qed.
Lemma dab_lay_spill_in : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma dab_lay_answer_in : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. left. left. reflexivity.
Qed.
Lemma dab_lay_reply_in : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. right. left. reflexivity.
Qed.

(* g_rec.state := v, every other byte of g_rec and record.spill and every byte of the recorder's blocks kept *)
Lemma dab_arep_state : forall bl bl' (rd rd' : reader) R Q v,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 v -> 0 <= v < 2 ^ 64 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL (set_state R v) Q.
Proof.
intros bl bl' rd rd' R Q v HA Hv Hvr HK HKB Hbl.
destruct HA as (Hg8 & Hs8 & Hap & HC & HAN & HRP & HSC & HOWN).
destruct HC as (Hlen16 & HlQ & HNC & HCi & HSp & HSpM).
destruct HSC as (S1 & S2 & S3 & S4 & S5 & R1 & R2 & R3 & R4 & R5).
assert (KG : forall o, 0 <= o < REC_SIZE -> ~ (OFF_STATE <= o < OFF_STATE + 8) -> rd' (A_G_REC + o) = rd (A_G_REC + o)).
{ intros o Ho Hn. apply HK; [left; lia | lia]. }
assert (KGv : forall o (n : nat) w, aval_mem rd (A_G_REC + o) n w -> 0 <= o -> o + Z.of_nat n <= REC_SIZE ->
  (o + Z.of_nat n <= OFF_STATE \/ OFF_STATE + 8 <= o) -> aval_mem rd' (A_G_REC + o) n w).
{ intros o n w H Ho1 Ho2 Ho3. apply (dab_aval_mem_kept rd); [exact H|].
  intros k Hk. rewrite <- Z.add_assoc. apply KG; lia. }
assert (KS : forall o, 0 <= o < SC_SIZE -> rd' (A_REC_SPILL + o) = rd (A_REC_SPILL + o)).
{ intros o Ho. apply HK; [right; lia|]. unfold A_REC_SPILL, A_G_REC, OFF_STATE, SC_SIZE in *. lia. }
unfold arep_at, ag1_calls, ag1_scalars.
cbn [set_state r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host].
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ split; [exact Hlen16|]. split; [exact HlQ|]. split.
  { apply (KGv OFF_NCALLS 4%nat); [exact HNC | | |]; unfold OFF_NCALLS, OFF_STATE, REC_SIZE; lia. }
  split.
  { intros i c P Ec EP. destruct (HCi i c P Ec EP) as [HAc HFc]. split; [|exact HFc].
    assert (Hi : (i < 16)%nat)
      by (pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Ec; discriminate)); lia).
    apply (dab_acall_at_kept bl bl' rd rd'); [exact HAc | | |].
    - intros pn Hpn. apply Hbl. exact (dab_lay_calls_in Q i P pn EP Hpn).
    - intros j Hj. pose proof HAc as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj.
      rewrite <- Z.add_assoc, <- Z.add_assoc. apply KG; unfold OFF_CALLS, CALL_SIZE, OFF_STATE, REC_SIZE in *; lia.
    - intros pn j Hpn Hj. apply HKB; [exact (dab_lay_calls_in Q i P pn EP Hpn) | exact Hj]. }
  split; [|exact HSpM].
  apply (dab_acall_at_kept bl bl' rd rd'); [exact HSp | | |].
  - intros pn Hpn. apply Hbl. exact (dab_lay_spill_in Q pn Hpn).
  - intros j Hj. pose proof HSp as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj. apply KS. unfold SC_SIZE. lia.
  - intros pn j Hpn Hj. apply HKB; [exact (dab_lay_spill_in Q pn Hpn) | exact Hj]. }
split.
{ apply (dab_aanswer_at_kept bl bl' rd rd'); [exact HAN | | |].
  - intros pn Hq. apply Hbl. exact (dab_lay_answer_in Q pn Hq).
  - intros i Hi. rewrite <- Z.add_assoc. apply KG; unfold OFF_ANSWER, OFF_STATE, REC_SIZE; lia.
  - intros pn i Hq Hi. apply HKB; [exact (dab_lay_answer_in Q pn Hq) | exact Hi]. }
split.
{ apply (dab_areply_at_kept bl bl' rd rd'); [exact HRP | | |].
  - intros pn Hq. apply Hbl. exact (dab_lay_reply_in Q pn Hq).
  - intros i Hi. rewrite <- Z.add_assoc. apply KG; unfold OFF_REPLY, OFF_STATE, REC_SIZE; lia.
  - intros pn i Hq Hi. apply HKB; [exact (dab_lay_reply_in Q pn Hq) | exact Hi]. }
split; [|exact HOWN].
split; [apply (KGv OFF_REFUSE 4%nat); [exact S1 | | |]; unfold OFF_REFUSE, OFF_STATE, REC_SIZE; lia|].
split; [apply (KGv OFF_CODE 4%nat); [exact S2 | | |]; unfold OFF_CODE, OFF_STATE, REC_SIZE; lia|].
split; [apply (KGv OFF_NREPLIES 4%nat); [exact S3 | | |]; unfold OFF_NREPLIES, OFF_STATE, REC_SIZE; lia|].
split; [exact Hv|].
split; [apply (KGv OFF_HOST 8%nat); [exact S5 | | |]; unfold OFF_HOST, OFF_STATE, REC_SIZE; lia|].
repeat split; first [exact Hvr | lia].
Qed.
(* the same with g_rec.state kept: a change of memory off the recorder's bytes keeps the representation *)
Lemma dab_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HK HKB Hbl.
pose proof HA as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & S4 & _ & _ & _ & _ & R4 & _) & _).
rewrite <- (dab_set_state_same R).
apply (dab_arep_state bl bl' rd rd' R Q (r_state R) HA); [| exact R4 | intros a Ha _; exact (HK a Ha) | exact HKB | exact Hbl].
apply (dab_aval_mem_kept rd); [exact S4|]. intros k Hk. apply HK. left. unfold A_G_REC, OFF_STATE, REC_SIZE. lia.
Qed.
(* the recorder's state of the statement (rec_repA) after the store of g_rec.state *)
Lemma dab_rep_state : forall (B : asyms) ly S ly' S' (rd rd' : reader) R O v,
rec_repA B ly S rd R O ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 v -> 0 <= v < 2 ^ 64 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
rec_repA B ly' S' rd' (set_state R v) O.
Proof.
intros B ly S ly' S' rd rd' R O v (Q & HA & HOQ) Hv Hvr HK HKB Hbl.
exists Q. split; [|exact HOQ].
apply (dab_arep_state (ablocks B ly S) (ablocks B ly' S') rd rd' R Q v HA Hv Hvr HK).
- intros pn i Hin Hi. apply HKB; [apply (proj2 (HOQ pn)); exact Hin | exact Hi].
- intros pn Hin. apply Hbl. apply (proj2 (HOQ pn)). exact Hin.
Qed.

(* --- the state checks of the segment starts ---------------------------------------------------------------- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of a state after a call: the registers at the call's return, then the caller's ra, s0, s1
   (atoms 32, 33, 34) and g_rec.state (atom 35) *)
Definition dab_extra (regs : bvmap 5 word) (h : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) dab_saved ++ [Z_to_bv 64 h].
Definition dab_E (regsc regs : bvmap 5 word) (h : Z) : env := Eimg (Ereg regsc (dab_extra regs h)).
(* the caller's three saved registers in the frame below sp0 (ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24) *)
Definition dab_frame_at (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error dab_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

Lemma dab_sig_record : cmd_sig_prog -> SIG CS_record = BASE + AF_record.
Proof. intros SIGP. rewrite (SIGP CS_record ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dab_sig_arg_s : cmd_sig_prog -> SIG CS_arg_s = BASE + AF_arg_s.
Proof. intros SIGP. rewrite (SIGP CS_arg_s ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dab_sig_mix_call : cmd_sig_prog -> SIG CS_mix_call = BASE + AF_mix_call.
Proof. intros SIGP. rewrite (SIGP CS_mix_call ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

Lemma dab_E_reg : forall regsc regs h n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (dab_E regsc regs h) n = getr regsc r.
Proof.
intros regsc regs h n r Hn. unfold dab_E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma dab_E_extra : forall regsc regs h j, (j < 4)%nat -> ew (dab_E regsc regs h) (32 + j) = nth j (dab_extra regs h) (Z_to_bv 64 0).
Proof. intros regsc regs h j Hj. unfold dab_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma dab_frame_chunk : forall E m sp0 (regs : bvmap 5 word) j r,
nth_error dab_saved j = Some r -> dab_frame_at m sp0 regs ->
ew E (32 + j) = getr regs (Z_to_bv 5 r) ->
YP09.chunk_ok SEGS E m (sp0 - 32) (YP09.mkChunk (24 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))).
Proof.
intros E m sp0 regs j r Hj Hfr Ej.
apply (chunk_ok_val SEGS E m (sp0 - 32) (24 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
- cbn [sv_denot]. rewrite Ej, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  change (8 * Z.of_N 8) with 64. lia.
- change (Z.of_N 8) with 8. lia.
- replace (sp0 - 32 + (24 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (Hfr j r Hj).
Qed.

(* the frame region after the prologue, under the environment of a state after a call *)
Lemma dab_frame_ok : forall (regsc regs : bvmap 5 word) h m sp0,
bv_unsigned (getr regsc 2) = sp0 - 32 -> 32 <= sp0 <= 2 ^ 64 -> dab_frame_at m sp0 regs ->
YP09.region_ok SEGS (dab_E regsc regs h) m dab_frame.
Proof.
intros regsc regs h m sp0 Hsp Hsp0 Hfr.
assert (E2 : bv_unsigned (ew (dab_E regsc regs h) 2) = sp0 - 32) by (rewrite (dab_E_reg regsc regs h 2 2%bv eq_refl); exact Hsp).
assert (Hfj : forall j r, nth_error dab_saved j = Some r ->
  YP09.chunk_ok SEGS (dab_E regsc regs h) m (sp0 - 32)
    (YP09.mkChunk (24 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j r Hj. assert (Hj3 : (j < length dab_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  apply (dab_frame_chunk _ m sp0 regs j r Hj Hfr). rewrite dab_E_extra by (cbn in Hj3; lia). unfold dab_extra.
  rewrite app_nth1 by (rewrite length_map; exact Hj3).
  apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
unfold YP09.region_ok, dab_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil;
[exact (Hfj 0%nat 1 eq_refl) | exact (Hfj 1%nat 8 eq_refl) | exact (Hfj 2%nat 9 eq_refl)].
Qed.

(* the entry (0x8cc54): every register its own atom, the 32 bytes below sp present *)
Lemma dab_entry : forall (W : world SEGS) mem (regs : bvmap 5 word),
spZ regs mod 16 = 0 -> 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47 ->
(forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) dab_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_descriptors_add)) mem (seg_rom SEGS))).
Proof.
intros W mem regs Hsp16 Hsp Hpres.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
rewrite restrict_mkst_fx. unfold dab_ss0.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [dab_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

(* after record (0x8cc70) *)
Lemma dab_seat_record : forall (Wc : world SEGS) memc (regsc regs : bvmap 5 word) sp0 h,
bv_unsigned (getr regsc 2) = sp0 - 32 -> sp0 mod 16 = 0 -> 2 ^ 46 + 32 <= sp0 <= 2 ^ 47 ->
dab_frame_at (mrestrict (w_H Wc) memc) sp0 regs ->
st_ok_pi SEGS VAL (dab_E regsc regs h) dab_ssR
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + DAB_AFTER_RECORD)) memc (seg_rom SEGS))).
Proof.
intros Wc memc regsc regs sp0 h Hsp Hsp16 Hsp47 Hfr.
assert (E2 : bv_unsigned (ew (dab_E regsc regs h) 2) = sp0 - 32) by (rewrite (dab_E_reg regsc regs h 2 2%bv eq_refl); exact Hsp).
assert (Hsp16' : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
rewrite restrict_mkst_fx. unfold dab_ssR.
apply pa_entry_st_ok_full.
- unfold dab_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. apply (dab_frame_ok regsc regs h _ sp0 Hsp ltac:(lia) Hfr).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [dab_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

Section e.
Hypothesis VOBJS : cmd_val_objs.
(* PROVISIONAL: the auipc value at 0x8cc7c, which the statement does not carry (see the header) *)
Hypothesis VHIS : cmd_val_his.

Lemma dab_val_state_obj : VAL (A_OBJ 86) = A_G_REC + OFF_STATE.
Proof. rewrite (VOBJS 86%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma dab_val_state_hi : VAL (A_HI 203) = A_G_REC + OFF_STATE + 1548.
Proof. rewrite (VHIS 203%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
(* the store at 0x8cc8c (sd a0, -0x60c(s0), s0 = the auipc value) writes the word the load at 0x8cc80 read *)
Lemma dab_store_addr : VAL (A_HI 203) + -1548 = VAL (A_OBJ 86).
Proof. rewrite dab_val_state_hi, dab_val_state_obj. lia. Qed.

(* after arg_s (0x8cc7c): g_rec.state, holding h, is the object of the load at 0x8cc80 *)
Lemma dab_seat_arg_s : forall (Wc : world SEGS) memc (regsc regs : bvmap 5 word) sp0 h,
bv_unsigned (getr regsc 2) = sp0 - 32 -> sp0 mod 16 = 0 -> 2 ^ 46 + 32 <= sp0 <= 2 ^ 47 ->
dab_frame_at (mrestrict (w_H Wc) memc) sp0 regs ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
st_ok_pi SEGS VAL (dab_E regsc regs h) dab_ssA
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + DAB_AFTER_ARG_S)) memc (seg_rom SEGS))).
Proof.
intros Wc memc regsc regs sp0 h Hsp Hsp16 Hsp47 Hfr Hst Hh.
set (E := dab_E regsc regs h).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 32) by (subst E; rewrite (dab_E_reg regsc regs h 2 2%bv eq_refl); exact Hsp).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; change 35%nat with (32 + 3)%nat; rewrite dab_E_extra by lia; reflexivity).
assert (U86 : bv_unsigned (ew E (A_OBJ 86)) = A_G_REC + OFF_STATE).
{ subst E. unfold dab_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite dab_val_state_obj. apply unsigned_lit_small. unfold A_G_REC, OFF_STATE; lia. }
assert (Hsp16' : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
rewrite restrict_mkst_fx. unfold dab_ssA.
apply pa_entry_st_ok_full.
- subst E. unfold dab_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [exact (dab_frame_ok regsc regs h _ sp0 Hsp ltac:(lia) Hfr)|].
  apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, dab_stateO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U86. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|].
  split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (A_G_REC + OFF_STATE) 0 8 (SOff 35 0) h);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia |].
  rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H Wc) memc (A_G_REC + OFF_STATE) 8%nat h Hst).
- apply pairwise_disjoint_of_extents.
  unfold dab_frame, dab_stateO, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, U86. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_STATE in *. repeat split; lia.
- split; [|split; exact I]. cbn [dab_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

(* after mix_call (0x8cc8c): s0 holds the auipc value, and the 8 bytes 1548 below it (g_rec.state) are writable *)
Lemma dab_seat_mix : forall (Wc : world SEGS) memc (regsc regs : bvmap 5 word) sp0 h,
bv_unsigned (getr regsc 2) = sp0 - 32 -> sp0 mod 16 = 0 -> 2 ^ 46 + 32 <= sp0 <= 2 ^ 47 ->
dab_frame_at (mrestrict (w_H Wc) memc) sp0 regs ->
getr regsc 8 = Z_to_bv 64 (A_G_REC + OFF_STATE + 1548) ->
(forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H Wc) memc) (A_G_REC + OFF_STATE + o)) ->
st_ok_pi SEGS VAL (dab_E regsc regs h) dab_ssM
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + DAB_AFTER_MIX)) memc (seg_rom SEGS))).
Proof.
intros Wc memc regsc regs sp0 h Hsp Hsp16 Hsp47 Hfr H8 Hwr.
set (E := dab_E regsc regs h).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 32) by (subst E; rewrite (dab_E_reg regsc regs h 2 2%bv eq_refl); exact Hsp).
assert (UHI : bv_unsigned (ew E (A_HI 203)) = A_G_REC + OFF_STATE + 1548).
{ subst E. unfold dab_E. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite dab_val_state_hi. apply unsigned_lit_small. unfold A_G_REC, OFF_STATE; lia. }
assert (Hsp16' : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
rewrite restrict_mkst_fx. unfold dab_ssM.
apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [subst E; unfold dab_E; apply regs_ok_Eimg_Ereg | reflexivity |].
  cbn [sv_denot]. rewrite UHI, Z.add_0_r. exact H8.
- vm_compute. reflexivity.
- apply Forall_cons; [exact (dab_frame_ok regsc regs h _ sp0 Hsp ltac:(lia) Hfr)|].
  apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, dab_stateH. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UHI. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|].
  split; [|constructor].
  intros o Ho. replace (A_G_REC + OFF_STATE + 1548 + o) with (A_G_REC + OFF_STATE + (o + 1548)) by lia.
  apply Hwr. lia.
- apply pairwise_disjoint_of_extents.
  unfold dab_frame, dab_stateH, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, UHI. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_STATE in *. repeat split; lia.
- split; [|split; exact I]. cbn [dab_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.
End e.
End f.
End d.
