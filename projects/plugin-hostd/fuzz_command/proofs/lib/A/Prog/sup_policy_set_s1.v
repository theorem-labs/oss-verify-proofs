(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first part of sup_policy_set's ASan walk (plugin-hostd/fuzz_command, 0x8b9b0), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and AChc.v (cgif_close: the seed of a walk segment, the run, the step through a program call) and of an earlier version of lib/A/Prog/sup_reply_code.v: the entry, the inlined record() with both arms (the call of rec_calls_free on record.spill when the table holds 16 calls), the two checked stores into the slot, and the walk to the call of xstrdup on the first argument. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4 and 5: the bundled pre
   carries the rounding-mode-0 premise where astack_pres was, the post is apost_baseF, the callees' contracts are taken
   at every FP state; the frame chains at the two calls are achain_low (s0 = the slot, below alloc_ceiling). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaLibF PaLibG PaLibH PaSB
PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c hand_back_c answer_c sup_policy_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBTemplate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the member's parameters -------------------------------------------------------------------------- *)
(* the verb recorded (REC_POLICY_SET, recorder.h), the function's entry and frame, and the offsets of the walk's
   cut points in the listing (MEASURED: the disassembly of sup_policy_set in fuzz_command.asan) *)
Definition SPS_FN : Z := REC_POLICY_SET.
Definition SPS_ENTRY : Z := AF_sup_policy_set.          (* 0x8b9b0 *)
Definition SPS_FRAME : Z := 64.
Definition SPS_RET_RCF : Z := AF_sup_policy_set + 0x5c.  (* after the call of rec_calls_free (0x8ba0c) *)
Definition SPS_JOIN : Z := AF_sup_policy_set + 0x7c.     (* record()'s two arms meet (0x8ba2c) *)
Definition SPS_RET_X1 : Z := AF_sup_policy_set + 0xc0.   (* after the first call of xstrdup (0x8ba70) *)
Definition SPS_RET1 : Z := AF_sup_policy_set + 0xc0.    (* after the first xstrdup (0x8ba70) *)
Definition SPS_RET2 : Z := AF_sup_policy_set + 0x110.   (* after the second xstrdup (0x8bac0) *)
Definition SPS_RET3 : Z := AF_sup_policy_set + 0x150.   (* after rec_shape_of (0x8bb00) *)
Definition sps_SB : Z := 0x7fff8000.
(* the callee-saved registers the prologue stores, in the order of their slots below the entry sp: ra at sp0 - 8,
   s0 at sp0 - 16, ..., s5 at sp0 - 56 *)
Definition sps_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
Definition sps_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sps_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the statement's footprint (sup_policy_set_c.v:105) *)
Definition sps_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the slot record() fills: g_rec.calls[ncalls], or record.spill when the table holds 16 calls *)
Definition sps_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else A_REC_SPILL.

(* --- the symbolic state of the entry segment ----------------------------------------------------------- *)
(* atoms: the 32 registers, 32 = the shadow base, 33 = g_rec.ncalls; regions: the 64-byte frame below the entry sp
   (atom 2), the GOT word of the shadow base cell, that cell, and g_rec.ncalls *)
Definition sps_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition sps_rsA : smem := [stack_region SPS_FRAME; got_regionP; bcell_regionP 32; sps_ncalls].
Definition sps_factsA : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF sps_SB sps_SB 0); (33%nat, mkAF 0 16 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_spsA : sstate := mkSS SPS_ENTRY sr_atoms sps_rsA None sps_factsA.
Definition sps_BxA : sv := SOff 32 0.
Definition sps_Bspan : Z * Z := (sps_SB, sps_SB + 2 ^ 44 - 1).
Definition sps_extraA (n : Z) : list word := [Z_to_bv 64 sps_SB; Z_to_bv 64 n].

(* --- the recorder's representation under byte changes outside it, and under the stores of record() --------- *)
Lemma sps_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma sps_aval_kept_rng : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk. apply (sps_aval_kept rd); [exact H|]. intros k Hkn. apply Hk. lia. Qed.
Lemma sps_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma sps_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (sps_abytes_kept rd); [exact H1|].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hk. lia.
Qed.
Lemma sps_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS, CALL_SIZE in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (sps_aval_kept_rng rd); [exact H4 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact H5 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (sps_aval_kept_rng rd); [exact G1 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (sps_astr_kept rd); [exact G5 | intros x Hx; apply (Hp pn); [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma sps_in_lay_calls : forall Q P pn i, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q P pn i Hi Hp. unfold lay_blocks. apply in_app_iff. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hp].
Qed.
Lemma sps_in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn Hp. unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hp. Qed.
Lemma sps_in_lay_answer : forall Q q, l_answer Q = Some q -> In q (lay_blocks Q).
Proof. intros Q q Hq. unfold lay_blocks. rewrite Hq. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn [oblk]. left. reflexivity. Qed.
Lemma sps_in_lay_reply : forall Q q, l_reply Q = Some q -> In q (lay_blocks Q).
Proof.
intros Q q Hq. unfold lay_blocks. rewrite Hq. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
cbn [oblk]. left. reflexivity.
Qed.
Ltac sps_zl := unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE,
  OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE, REC_SIZE, SC_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *;
  cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
(* the representation is kept when g_rec, record.spill and the recorder's blocks are *)
Lemma sps_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) ->
(forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) ->
(forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA Hbl Hg Hs Hb.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE,
  OFF_HOST, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
  split; [apply (sps_aval_kept_rng rd); [exact C3 | intros x Hx; apply Hg; sps_zl]|].
  split.
  - intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
    pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
    apply (sps_acall_kept bl _ rd); [exact HC | | |].
    + intros pn Hpn. apply Hbl. exact (sps_in_lay_calls Q P pn i Hp Hpn).
    + intros x Hx. apply Hg. sps_zl.
    + intros pn x Hpn Hx. apply (Hb pn); [exact (sps_in_lay_calls Q P pn i Hp Hpn) | exact Hx].
  - split; [|exact C6].
    apply (sps_acall_kept bl _ rd); [exact C5 | | |].
    + intros pn Hpn. apply Hbl. exact (sps_in_lay_spill Q pn Hpn).
    + intros x Hx. apply Hs. sps_zl.
    + intros pn x Hpn Hx. apply (Hb pn); [exact (sps_in_lay_spill Q pn Hpn) | exact Hx]. }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; sps_zl]|].
    split; [exact A2|]. split; [apply Hbl; exact (sps_in_lay_answer Q q Eq)|]. split; [exact A4|].
    split; [apply (sps_astr_kept rd); [exact A5 | intros y Hy; apply (Hb q); [exact (sps_in_lay_answer Q q Eq) | lia]] | exact A6].
  - apply (sps_aval_kept_rng rd); [exact Ha | intros y Hy; apply Hg; sps_zl]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; sps_zl]|].
    split; [apply (sps_aval_kept_rng rd); [exact A2 | intros y Hy; apply Hg; sps_zl]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply Hbl; exact (sps_in_lay_reply Q q Eq)|]. split; [exact A6|].
    split; [apply (sps_abytes_kept rd); [exact A7 | intros y Hy; apply (Hb q); [exact (sps_in_lay_reply Q q Eq) | lia]] | exact A8].
  - destruct Hr as [A1 A2].
    split; apply (sps_aval_kept_rng rd); first [exact A1 | exact A2 | intros y Hy; apply Hg; sps_zl]. }
split; [|exact Hown].
split; [apply (sps_aval_kept_rng rd); [exact S1 | intros y Hy; apply Hg; sps_zl]|].
split; [apply (sps_aval_kept_rng rd); [exact S2 | intros y Hy; apply Hg; sps_zl]|].
split; [apply (sps_aval_kept_rng rd); [exact S3 | intros y Hy; apply Hg; sps_zl]|].
split; [apply (sps_aval_kept_rng rd); [exact S4 | intros y Hy; apply Hg; sps_zl]|].
split; [apply (sps_aval_kept_rng rd); [exact S5 | intros y Hy; apply Hg; sps_zl]|].
exact S6.
Qed.
(* record()'s stores into a fresh slot of g_rec's table: ncalls := n + 1, slot.fn := fn, slot.nargs := 0 *)
Lemma sps_arep_slot : forall bl (rd rd' : reader) R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
(forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4) ->
   ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= x <
      A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 8) -> rd' x = rd x) ->
(forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) ->
(forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) 4 fn ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 4) 4 0 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, [])]))
  (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl rd rd' R Q fn HA Hn Hfn Hg Hs Hb HNC Hfnv Hnav.
set (m := length (r_calls R)) in *.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
assert (Hlay : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite !app_nil_r. reflexivity. }
assert (Hm16 : 0 <= Z.of_nat m < 16) by lia.
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host set_calls l_calls l_spill l_answer l_reply].
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE,
  OFF_HOST, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ rewrite !length_app. cbn [length]. split; [lia|]. split; [lia|].
  split; [rewrite Nat2Z.inj_add; exact HNC|].
  split.
  - intros i c P Hc Hp.
    destruct (Nat.lt_ge_cases i m) as [Hi | Hi].
    + rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in Hp by lia.
      destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
      apply (sps_acall_kept bl _ rd); [exact HC | exact (RecBLemmas.acall_at_in _ _ _ _ _ HC) | |].
      * intros x Hx. apply Hg; unfold CALL_SIZE in *; lia.
      * intros pn x Hpn Hx. apply (Hb pn); [exact (sps_in_lay_calls Q P pn i Hp Hpn) | exact Hx].
    + rewrite nth_error_app2 in Hc by exact Hi. rewrite nth_error_app2 in Hp by lia.
      rewrite C2 in Hp. fold m in Hp, Hc.
      destruct (Nat.eq_dec i m) as [-> | Hne].
      * rewrite Nat.sub_diag in Hc, Hp. cbn [nth_error] in Hc, Hp.
        injection Hc as <-. injection Hp as <-.
        split; [|constructor].
        unfold acall_at, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS. cbn [fst snd length].
        split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
        split; [rewrite Z.add_0_r; exact Hfnv|]. split; [exact Hnav|]. split; [constructor|].
        intros k s pn Hs' _. destruct k; discriminate Hs'.
      * revert Hc. destruct (i - m)%nat as [|j] eqn:Ej; [lia|]. intros Hc. cbn [nth_error] in Hc. destruct j; discriminate Hc.
  - split; [|exact C6].
    apply (sps_acall_kept bl _ rd); [exact C5 | exact (RecBLemmas.acall_at_in _ _ _ _ _ C5) | |].
    + intros x Hx. apply Hs. unfold CALL_SIZE in Hx. lia.
    + intros pn x Hpn Hx. apply (Hb pn); [exact (sps_in_lay_spill Q pn Hpn) | exact Hx]. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    split; [apply (sps_astr_kept rd); [exact A5 | intros y Hy; apply (Hb q); [exact (sps_in_lay_answer Q q Eq) | lia]] | exact A6].
  - apply (sps_aval_kept_rng rd); [exact Ha | intros y Hy; apply Hg; cbn in Hy; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [apply (sps_aval_kept_rng rd); [exact A2 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [apply (sps_abytes_kept rd); [exact A7 | intros y Hy; apply (Hb q); [exact (sps_in_lay_reply Q q Eq) | lia]] | exact A8].
  - destruct Hr as [A1 A2].
    split; apply (sps_aval_kept_rng rd); first [exact A1 | exact A2 | intros y Hy; apply Hg; cbn in Hy; lia]. }
split; [|unfold ag1_own in Hown |- *; rewrite Hlay; exact Hown].
split; [apply (sps_aval_kept_rng rd); [exact S1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S2 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S3 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S4 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S5 | intros y Hy; apply Hg; cbn in Hy; lia]|].
exact S6.
Qed.

(* record()'s store into record.spill once rec_calls_free emptied it: spill.fn := fn, spill.nargs = 0 *)
Lemma sps_arep_spillw : forall bl (rd rd' : reader) R Q fn,
arep_at bl rd A_G_REC A_REC_SPILL R Q -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
(forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) ->
(forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aval_mem rd' A_REC_SPILL 4 fn -> aval_mem rd' (A_REC_SPILL + 4) 4 0 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_spill R (fn, [])) Q.
Proof.
intros bl rd rd' R Q fn HA Hsp Hfn Hg Hb Hfnv Hnav.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
pose proof C5 as (_ & _ & HLP & _). rewrite Hsp in HLP. cbn [length] in HLP.
destruct (l_spill Q) as [|p0 ps0] eqn:ElQ; [|discriminate HLP].
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host set_spill].
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE,
  OFF_HOST, CALL_SIZE, REC_SIZE, SC_SIZE, A_G_REC, A_REC_SPILL in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
  split; [apply (sps_aval_kept_rng rd); [exact C3 | intros x Hx; apply Hg; cbn in Hx; lia]|].
  split.
  - intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
    pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
    apply (sps_acall_kept bl _ rd); [exact HC | exact (RecBLemmas.acall_at_in _ _ _ _ _ HC) | |].
    + intros x Hx. apply Hg. unfold CALL_SIZE in *. lia.
    + intros pn x Hpn Hx. apply (Hb pn); [exact (sps_in_lay_calls Q P pn i Hp Hpn) | exact Hx].
  - split; [|constructor].
    rewrite ElQ. unfold acall_at, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS. cbn [fst snd length].
    split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
    split; [rewrite Z.add_0_r; exact Hfnv|]. split; [exact Hnav|]. split; [constructor|].
    intros k s pn Hs' _. destruct k; discriminate Hs'. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|] eqn:Eq; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    split; [apply (sps_astr_kept rd); [exact A5 | intros y Hy; apply (Hb q); [exact (sps_in_lay_answer Q q Eq) | lia]] | exact A6].
  - apply (sps_aval_kept_rng rd); [exact Ha | intros y Hy; apply Hg; cbn in Hy; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|] eqn:Eq; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply (sps_aval_kept_rng rd); [exact A1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [apply (sps_aval_kept_rng rd); [exact A2 | intros y Hy; apply Hg; cbn in Hy; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [apply (sps_abytes_kept rd); [exact A7 | intros y Hy; apply (Hb q); [exact (sps_in_lay_reply Q q Eq) | lia]] | exact A8].
  - destruct Hr as [A1 A2].
    split; apply (sps_aval_kept_rng rd); first [exact A1 | exact A2 | intros y Hy; apply Hg; cbn in Hy; lia]. }
split; [|exact Hown].
split; [apply (sps_aval_kept_rng rd); [exact S1 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S2 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S3 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S4 | intros y Hy; apply Hg; cbn in Hy; lia]|].
split; [apply (sps_aval_kept_rng rd); [exact S5 | intros y Hy; apply Hg; cbn in Hy; lia]|].
exact S6.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sps_EA (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (sps_extraA n)).

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary fact `cmd_prog_writable` (PROG_PRESENT; the recorder walks' shared form): the bytes of the program's
   writable statics are present *)
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma sps_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the seed of the entry segment *)
Lemma sps_seedA : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md n,
AR SEGS B ly S W mem md ->
astk_ok SUP_POLICY_SET_STK ly (spZ regs) ->
(forall a, spZ regs - SUP_POLICY_SET_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (sps_EA regs n) ss_spsA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SPS_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sps_BxA [] (sps_EA regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md n HAR Hstk Hpres Hn HNC.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := sps_EA regs n).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold sps_EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 sps_SB).
{ subst E. unfold sps_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ subst E. unfold sps_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ subst E. unfold sps_EA. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite sps_grec_val. reflexivity. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_spsA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sps_EA. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sps_rsA, stack_region, got_regionP, bcell_regionP, sps_ncalls.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E2. unfold SPS_FRAME. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia. }
      constructor.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (pa_val_range _) | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) sps_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold sps_SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
      split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
      split.
      { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR).
        apply Exists_cons_hd. unfold in_zr, A_G_REC, REC_SIZE, OFF_NCALLS in *. cbn [fst snd]. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
      exact (RecBLemmas.val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
  + apply pairwise_disjoint_of_extents.
    unfold sps_rsA, stack_region, got_regionP, bcell_regionP, sps_ncalls, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
    cbn [nth cmd_objs]. unfold SPS_FRAME, A_G_REC, OFF_NCALLS in *.
    rewrite WS in Hslo. repeat split; lia.
  + split; [|split; exact I].
    cbn [sps_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E32, E33, EG, !unsigned_lit_small by (unfold sps_SB, A_G_REC; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold sps_SB, A_G_REC.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok. apply Forall_nil.
Qed.

Hypothesis HB : CmdBSyms B.
(* the per-binary fact `cmd_prog_img` (the recorder walks' shared form): the program's statics are image bytes *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.

(* a footprint byte of g_rec / record.spill may be written by the walk (awr_byte's program-static arm) *)
Lemma sps_awr_prog : forall STK sp0 FP bl0 blc fr0 ly own a,
inFP FP a -> Exists (in_zr a) recb_PG -> awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof.
intros STK sp0 FP bl0 blc fr0 ly own a Hfp Hpg. unfold awr_byte. right; right; right; right.
unfold awr_prog_or_caller. left. split; [exact Hfp|]. split; [rewrite (recb_ts_prog_m B HB); exact Hpg | exact (cmd_prog_img a Hpg)].
Qed.

Lemma sps_awr_grec : forall STK sp0 O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (sps_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha. apply sps_awr_prog; [|exact (recb_grec_in a Ha)].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma sps_awr_spill : forall STK sp0 O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (sps_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha. apply sps_awr_prog; [|exact (recb_spill_in a Ha)].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Ltac sps_awrA Usp EGu :=
  awr_ok_tac; [exact Usp|];
  eapply awr_ok_cons_gen; [reflexivity | exact EGu | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    apply sps_awr_grec; unfold REC_SIZE; lia |];
  apply awr_ok_nil.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* --- the segment interface (shared with sup_lv2_worker_set's walk: the same listing, other constants) ------- *)
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* a string argument as the statement states it (sup_policy_set_c.v:90-97): a string in a live heap block, apart
   from every block of O (sup_lv2_worker_set_s1.v's slw_harg, renamed) *)
Definition sps_harg ly S (rd : reader) (O : list (Z * Z)) (p : Z) (v : option (list byte)) : Prop :=
exists x, v = Some x /\ in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR rd p x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\ Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.

(* the statement's premises (sup_policy_set_c.v:78-102), bundled in their order *)
Definition sps_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (pf pp : Z) (format place : option (list byte))
(R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_POLICY_SET_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pf /\ 0 <= pf < 2 ^ 64 /\
getr regs 11 = w64 pp /\ 0 <= pp < 2 ^ 64 /\
sps_harg ly S (rdW W mem) O pf format /\
sps_harg ly S (rdW W mem) O pp place /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_POLICY_SET R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_POLICY_SET R format place <= LIVE_MAX /\
mo_ok MT S (XM_SUP_POLICY_SET MT R format place).

(* the statement's post (sup_policy_set_c.v:107-126) verbatim *)
Definition sps_Q ly S (R : rstate) (format place : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_policy_set_m R format place = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_POLICY_SET R format place /\
 mo_le MT S S' (XM_SUP_POLICY_SET MT R format place).
Definition sps_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (format place : option (list byte))
(O : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_POLICY_SET_STK (sps_FP O) regs ly S W mem md (EV_SUP_POLICY_SET R)
(sps_Q ly S R format place O).

Definition sps_n (x : option (list byte)) : Z := Z.of_nat (length (sarg x)) + 1.

(* MID1, the state at +0xc0 (0x8ba70), just after the first xstrdup returned the copy p1 of the first argument
   (sup_lv2_worker_set_s1.v's slw_mid1, renamed) *)
Definition sps_mid1 ly S (W : world SEGS) (regs : bvmap 5 word) mem md (pp : Z) (format place : option (list byte))
(R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (k p1 : Z) (Df Lk O1 : list (Z * Z)) : Prop :=
let sp0 := spZ regs in
let c := sps_slot R in
ajournal SEGS B SUP_POLICY_SET_STK sp0 (sps_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R + EV_XSTRDUP /\
sps_frame (rdW Wc memc) sp0 regs /\
getr regs1 2 = w64 (sp0 - 64) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 c /\ getr regs1 9 = w64 pp /\ getr regs1 18 = w64 (c + 4) /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 21 = w64 (SHADOW_OFF + (c + 4) / 8) /\
getr regs1 10 = w64 p1 /\
(forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
rec_repA B lyc Sc (rdW Wc memc) (rec_record R SPS_FN []) O1 /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Df) /\
(forall pn, In pn Df -> In pn O) /\
((length (r_calls R) < 16)%nat -> Df = []) /\
Permutation (ablocks B ly S) (Df ++ Lk) /\
Permutation (ablocks B lyc Sc) ((p1, sps_n format) :: Lk) /\
Forall (fun qk => iv_apart p1 (sps_n format) (fst qk) (snd qk)) Lk /\
4096 <= p1 < 2 ^ 64 /\ astr_atR (rdW Wc memc) p1 (sarg format) /\
sps_harg lyc Sc (rdW Wc memc) O1 pp place /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg format)).

(* the statement of the segment from +0xc0 to the end *)
Definition SPS_C_stmt : Prop :=
forall ly S W regs mem md ch pf pp format place R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1,
sps_pre ly S W regs mem md ch pf pp format place R O ->
sps_mid1 ly S W regs mem md pp format place R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + SPS_RET_X1) regs1 memc mdc) (sps_post ly S W regs mem md R format place O).

(* MIDJ, the state where record()'s two arms meet (+0x7c, 0x8ba2c): the slot c is chosen (s0), g_rec.ncalls is
   bumped on the slot arm, the spill's old arguments are freed on the spill arm (Df), and the slot's fn / nargs are
   still to be stored: the recorder's representation is stated for any reader that agrees outside [c, c + 8) and
   holds fn = 12, nargs = 0 there *)
Definition sps_midJ ly S (W : world SEGS) (regs : bvmap 5 word) mem md (pf pp : Z) (format place : option (list byte))
(R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (k : Z) (Df Lk O1 : list (Z * Z)) : Prop :=
let sp0 := spZ regs in
let c := sps_slot R in
ajournal SEGS B SUP_POLICY_SET_STK sp0 (sps_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R /\
sps_frame (rdW Wc memc) sp0 regs /\
getr regs1 2 = w64 (sp0 - 64) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 c /\ getr regs1 9 = w64 pp /\ getr regs1 19 = w64 pf /\ getr regs1 20 = w64 SHADOW_OFF /\
(forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW Wc memc a) ->
   aval_mem rd' c 4 SPS_FN -> aval_mem rd' (c + 4) 4 0 -> rec_repA B lyc Sc rd' (rec_record R SPS_FN []) O1) /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Df) /\
(forall pn, In pn Df -> In pn O) /\
((length (r_calls R) < 16)%nat -> Df = []) /\
Permutation (ablocks B ly S) (Df ++ Lk) /\
Permutation (ablocks B lyc Sc) Lk /\
sps_harg lyc Sc (rdW Wc memc) O1 pf format /\
sps_harg lyc Sc (rdW Wc memc) O1 pp place /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT).

Definition SPS_J_stmt : Prop :=
forall ly S W regs mem md ch pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1,
sps_pre ly S W regs mem md ch pf pp format place R O ->
sps_midJ ly S W regs mem md pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + SPS_JOIN) regs1 memc mdc) (sps_post ly S W regs mem md R format place O).

(* the walk's core statement: the statement's premises give its post *)
Definition SPS_AB_stmt : Prop :=
forall ly S W regs mem md ch pf pp format place R O,
sps_pre ly S W regs mem md ch pf pp format place R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_policy_set) regs mem md) (sps_post ly S W regs mem md R format place O).

(* --- the walk's hypotheses beyond the statement's (the recorder walks' shared names and forms) ------------ *)
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
(* arodata_okP crosses a journal by CmdBase.v's arodata_ok_journalP, whose two facts the statement does not carry yet *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
(* this port's decision: cmd_ro_ok names only unowned read-only bytes, so arodata_okP gives it at every AR state *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* cmd_heap_tail_vis (this port's HEAP_TAIL_VIS): a live block's bytes are visible to the end of their
   8-byte word *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

(* --- facts the segment glue uses ------------------------------------------------------------------------ *)
(* a string argument as the statement states it (its heap form), carried to a later state: its block survives (it
   is none of the blocks the walk frees) and its bytes are kept *)
Lemma sps_harg_move : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' (md' : Model) O O' p v,
AR SEGS B ly S W mem md ->
sps_harg ly S (rdW W mem) O p v ->
(forall pk, In pk (ablocks B ly S) -> ~ In pk O -> In pk (ablocks B ly' S') /\
   forall a, fst pk <= a < fst pk + snd pk -> rdW W' mem' a = rdW W mem a) ->
(forall pn, In pn O' -> In pn O) ->
sps_harg ly' S' (rdW W' mem') O' p v.
Proof.
intros ly S W mem md ly' S' W' mem' md' O O' p v HAR (x & -> & (q & k & Hqk & Hq & Hqe) & Hs & Hn & Hap) HBLK HO'.
assert (HnO : ~ In (q, k) O).
{ intros HqO. rewrite Forall_forall in Hap. specialize (Hap (q, k) HqO). unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
destruct (HBLK (q, k) Hqk HnO) as [Hqk' Hkeep].
exists x. split; [reflexivity|]. split; [exists q, k; split; [exact Hqk' | lia]|].
split; [apply (sps_astr_kept (rdW W mem)); [exact Hs|]; intros a Ha; apply Hkeep; cbn [fst snd]; lia|].
split; [exact Hn|].
rewrite Forall_forall in Hap |- *. intros qk Hqk2. apply Hap. apply HO'. exact Hqk2.
Qed.

(* the tail of a string argument's last word is visible (cmd_heap_tail_vis on its block) *)
Lemma sps_harg_tail : forall ly S (W : world SEGS) mem md O p x,
AR SEGS B ly S W mem md -> sps_harg ly S (rdW W mem) O p (Some x) ->
atail_vis SEGS W mem (p + Z.of_nat (length x)).
Proof.
intros ly S W mem md O p x HAR (x' & Hx & (q & k & Hqk & Hq & Hqe) & _). injection Hx as <-.
apply (cmd_heap_tail_vis ly S W mem md q k _ HAR Hqk). lia.
Qed.

(* the heap form gives astr_argA's heap arm, the form xstrdup's contract asks for its source *)
Lemma sps_harg_argA : forall ly S (W : world SEGS) mem md O p x,
AR SEGS B ly S W mem md -> sps_harg ly S (rdW W mem) O p (Some x) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some x).
Proof.
intros ly S W mem md O p x HAR (x' & Hx & (q & k & Hqk & Hq & Hqe) & Hs & Hn & _). injection Hx as <-.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hqk) as (_ & Hq4096 & _).
cbn [astr_argA]. split; [lia|]. split; [exact Hs|]. split; [exact Hn|]. left. split; [exists q, k; split; [exact Hqk | lia]|].
constructor.
Qed.

(* a string argument's address lies in [4096, 2^64) *)
Lemma sps_harg_range : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md ->
sps_harg ly S rd O p (Some x) -> 4096 <= p < 2 ^ 64.
Proof.
intros ly S W mem md rd O p x HAR (x' & Hx & (q & k & Hqk & Hq & Hqe) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hqk) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk0).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrq]. pose proof asan_consts as (C1 & _). lia.
Qed.

(* a heap block of the entry state is no image byte and lies below the stack *)
Lemma sps_blk_low : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
~ in_img SEGS a /\ 4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceilp & _).
split; [exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha) | lia].
Qed.

(* MIDJ on record()'s slot arm (ncalls < 16): only the frame and g_rec.ncalls were written *)
Lemma sps_midJ_slot : forall ly S W regs mem md ch pf pp format place R O (regs1 : bvmap 5 word) mem1 md1,
sps_pre ly S W regs mem md ch pf pp format place R O ->
(length (r_calls R) < 16)%nat ->
ajournal SEGS B SUP_POLICY_SET_STK (spZ regs) (sps_FP O) ly S W mem md [] ly S W mem1 md1 0 ->
sps_frame (rdW W mem1) (spZ regs) regs ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
   ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W mem1 a = rdW W mem a) ->
aval_mem (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) ->
getr regs1 2 = w64 (spZ regs - 64) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 8 = w64 (sps_slot R) -> getr regs1 9 = w64 pp -> getr regs1 19 = w64 pf ->
getr regs1 20 = w64 SHADOW_OFF ->
(forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
sps_midJ ly S W regs mem md pf pp format place R O ly S W regs1 mem1 md1 0 [] (ablocks B ly S) O.
Proof.
intros ly S W regs mem md ch pf pp format place R O regs1 mem1 md1 PRE Hn HJ HFR KEEP HNC HG
  R2 R3 R4 R8 R9 R19 R20 Rhi.
pose proof PRE as (HPRE & HRM & HROD & HRO & H10 & Hpf & H11 & Hpp & HAF & HAP & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
pose proof (proj1 HJ) as HAR1.
assert (Hslot : sps_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
{ unfold sps_slot. pose proof Hn as Hn'. apply Nat.ltb_lt in Hn'. rewrite Hn'. reflexivity. }
assert (Hsf : rec_spill_frees R = 0).
{ unfold rec_spill_frees. pose proof Hn as Hn'. apply Nat.ltb_lt in Hn'. rewrite Hn'. reflexivity. }
assert (KEEPI : forall a, in_img SEGS a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW W mem1 a = rdW W mem a).
{ intros a Hi Hnc. pose proof (pa_img_range a Hi) as Har. apply KEEP; [lia | lia | exact Hnc]. }
assert (KEEPB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> rdW W mem1 a = rdW W mem a).
{ intros p n a Hin Ha. destruct (sps_blk_low ly S W mem md p n a HAR Hin Ha) as [Hni Hlo].
  apply KEEP; [lia | lia |]. intros Hnc. apply Hni. apply cmd_prog_img. apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
pose proof HREP as (QL & HA & HO).
unfold sps_midJ. cbn zeta.
split; [exact HJ|]. split; [rewrite Hsf; lia|]. split; [exact HFR|].
do 7 (split; [assumption|]). split; [exact Rhi|].
split.
{ intros rd' Hrd' Hfn Hna. rewrite Hslot in Hrd', Hfn, Hna.
  exists (RLay (l_calls QL ++ [[]]) (l_spill QL) (l_answer QL) (l_reply QL)).
  rewrite (rec_record_calls R SPS_FN [] Hn). split.
  - apply (sps_arep_slot (ablocks B ly S) (rdW W mem) rd' R QL SPS_FN HA Hn ltac:(unfold SPS_FN, REC_POLICY_SET, REC_FN_COUNT; lia)).
    + intros x Hx Hx1 Hx2. rewrite (Hrd' x) by sps_zl.
      apply KEEPI; [apply cmd_prog_img, recb_grec_in; exact Hx | exact Hx1].
    + intros x Hx. rewrite (Hrd' x) by sps_zl.
      apply KEEPI; [apply cmd_prog_img, recb_spill_in; exact Hx | sps_zl].
    + intros [p n] x Hpn Hx. cbn [fst snd] in Hx.
      pose proof (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA (p, n) Hpn) as Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
      destruct (sps_blk_low ly S W mem md p n x HAR Hin ltac:(lia)) as [Hni Hlo].
      rewrite (Hrd' x); [apply (KEEPB p n x Hin); lia | lia |].
      intros Hc. apply Hni. apply cmd_prog_img, recb_grec_in. sps_zl.
    + apply (sps_aval_kept_rng (rdW W mem1)); [exact HNC|]. intros x Hx. apply Hrd'; sps_zl.
    + exact Hfn.
    + exact Hna.
  - intros pn. rewrite (HO pn). unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    rewrite concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. }
split; [intros pn; split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]|].
split; [intros pn []|].
split; [intros _; reflexivity|].
split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
assert (HBLK : forall pk, In pk (ablocks B ly S) -> ~ In pk O -> In pk (ablocks B ly S) /\
   forall a, fst pk <= a < fst pk + snd pk -> rdW W mem1 a = rdW W mem a).
{ intros [p n] Hin _. split; [exact Hin|]. intros a Ha. cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. apply (KEEPB p n a Hin). lia. }
split; [exact (sps_harg_move ly S W mem md ly S W mem1 md1 O O pf format HAR HAF HBLK (fun pn H => H))|].
split; [exact (sps_harg_move ly S W mem md ly S W mem1 md1 O O pp place HAR HAP HBLK (fun pn H => H))|].
rewrite Hsf, Z.mul_0_l. exact (mle_start MT S MTL).
Qed.

(* --- reading the symbolic state back ------------------------------------------------------------------- *)
Lemma sps_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma sps_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma sps_zcanon : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x.
Proof. intros x Hx. unfold zcanon, M64. apply Z.mod_small. exact Hx. Qed.
(* s0 on the slot arm: g_rec + 16 + 56 * ncalls *)
Lemma sps_denot_slot : forall E n, ew E 33 = Z_to_bv 64 (Z.of_nat n) -> ew E 285 = Z_to_bv 64 A_G_REC -> (n < 16)%nat ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n).
Proof.
intros E n E33 E285 Hn. apply sps_denot_U.
assert (U1 : U E (SOff 33 0) = Z.of_nat n) by (apply (U_atom E 33 (Z.of_nat n) E33); lia).
assert (U5 : U E (SOff 285 0) = A_G_REC) by (apply (U_atom E 285 A_G_REC E285); unfold A_G_REC; lia).
rewrite U_SAlu, U_SAlu, U_SMd, U1, U5, !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (sps_zcanon 56), (sps_zcanon 16) by lia.
rewrite (sps_zcanon (Z.of_nat n * 56)) by lia.
rewrite (sps_zcanon (Z.of_nat n * 56 + 16)) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE. rewrite sps_zcanon by lia. lia.
Qed.

(* the frame the prologue stores (ra, s0 .. s5 below the entry sp, atom 2), as the walk's stack region holds it *)
Definition sps_fchunks : list YP09.chunk :=
[YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma sps_frame_of_region : forall E (W : world SEGS) m sp0 (regs : bvmap 5 word),
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 sps_fchunks) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
sps_frame (rdW W m) sp0 regs.
Proof.
intros E W m sp0 regs HR Hsp Hew j r Hj.
assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sps_saved j)); rewrite Hj; discriminate).
apply (RecBLemmas.aval_mem_view SEGS).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
assert (ONE : forall off rn, In (YP09.mkChunk off (CVal 8 (SOff rn 0))) sps_fchunks -> Z.of_nat rn = r -> (rn < 32)%nat ->
  val_mem SEGS (mrestrict (w_H W) m) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off rn Hin Hrn Hrn32. change 8%nat with (N.to_nat 8).
  apply (field_of_region E _ 2 sp0 sps_fchunks (-64) 0 (-64) 0 off 8 (SOff rn 0) _ HR Hsp Hin); [| exact HRr | cbn; lia].
  rewrite sps_soff0. rewrite (Hew rn (Z_to_bv 5 r)); [symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrn. }
do 7 (destruct j as [|j]; [cbn [nth_error sps_saved] in Hj; injection Hj as <-;
  match goal with |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?jj) _ _ =>
    let off := eval cbv in (-8 - 8 * Z.of_nat jj) in
    replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + off) by (cbn; lia) end;
  (eapply ONE; [cbn [sps_fchunks In]; tauto | reflexivity | lia]) |]).
lia.
Qed.

Ltac sps_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* the region i of the symbolic state, evaluated *)
Ltac sps_region HS i HR :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
| st_ok _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
end.

Ltac sps_winA Usp EGu' :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu' in Hrr;
    first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin.

(* --- record()'s spill arm: the glue around the call of rec_calls_free -------------------------------------- *)
Lemma sps_nodup_disj : forall {A C : Type} (f : A -> C) (l1 l2 : list A) x, NoDup (map f (l1 ++ l2)) -> In x l1 -> In x l2 -> False.
Proof.
intros A C f l1 l2 x HN0. apply NoDup_ListNoDup in HN0. revert HN0.
induction l1 as [|y l1 IH]; intros HN H1 H2; [destruct H1|].
cbn [map app] in HN. inversion HN as [|z l HNi HN' Ez]; subst.
destruct H1 as [<- | H1]; [|exact (IH HN' H1 H2)].
apply HNi. rewrite map_app. apply in_or_app. right. apply in_map. exact H2.
Qed.

(* the footprint of rec_calls_free on record.spill alone: the spill's nargs word and the blocks it frees *)
Lemma sps_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
A_REC_SPILL + 4 <= a < A_REC_SPILL + 8 \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- left. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_SIZE, CALL_OFF_NARGS in Ha; cbn in Ha; lia | exact (False_ind _ (inFP_nil a Ha))].
- right. exact (inFP_ablocks_fp_inv P a Ha).
Qed.

Lemma sps_rcf_spares : forall P a, (forall p n, In (p, n) P -> 4096 <= p) ->
~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) -> (forall p n, In (p, n) P -> ~ (p <= a < p + req_size n)) ->
fp_spares (rcf_fp A_REC_SPILL [P]) a.
Proof.
intros P a Hpos Hs Hb. apply fp_spares_closed.
- intros H0. unfold YI16.sink_open_fp in H0. apply in_fp_inFP in H0.
  destruct (sps_rcf_fp_inv P 0 H0) as [H | (p & n & Hin & Hr)]; [unfold A_REC_SPILL in H; lia|].
  pose proof (Hpos p n Hin). lia.
- intros H. destruct (sps_rcf_fp_inv P a H) as [H' | (p & n & Hin & Hr)]; [exact (Hs H') | exact (Hb p n Hin Hr)].
Qed.

(* MIDJ on record()'s spill arm (ncalls = 16): the frame was written, then rec_calls_free emptied the spill *)
Lemma sps_midJ_spill : forall ly S W regs mem md ch pf pp format place R O QL (memc : word -> option byte) mdc
  (regsc : bvmap 5 word) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 (mem3 : word -> option byte) md3,
sps_pre ly S W regs mem md ch pf pp format place R O ->
length (r_calls R) = 16%nat ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R QL -> (forall pn, In pn O <-> In pn (lay_blocks QL)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> rdW W memc a = rdW W mem a) ->
sps_frame (rdW W memc) (spZ regs) regs ->
ajournal SEGS B REC_CALLS_FREE_STK (spZ regs - 64) (rcf_fp A_REC_SPILL [l_spill QL]) ly S W memc mdc []
  ly2 S2 W2 mem2 md2 (EV_REC_CALLS_FREE [l_spill QL]) ->
aregs_preserved regsc regs2 ->
Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ concat [l_spill QL]) ->
rec_repA B ly2 S2 (rdW W2 mem2) (set_spill R (fst (r_spill R), []))
  (concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)) ->
mo_le MT S S2 (XM_REC_CALLS_FREE MT [l_spill QL]) ->
ajournal SEGS B SUP_POLICY_SET_STK (spZ regs) (sps_FP O) ly S W mem md [] ly2 S2 W2 mem3 md3
  (0 + EV_REC_CALLS_FREE [l_spill QL]) ->
(forall a, 0 <= a < 2 ^ 64 -> rdW W2 mem3 a = rdW W2 mem2 a) ->
getr regsc 2 = w64 (spZ regs - 64) -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
getr regsc 8 = w64 A_REC_SPILL -> getr regsc 9 = w64 pp -> getr regsc 19 = w64 pf -> getr regsc 20 = w64 SHADOW_OFF ->
(forall r, 22 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
sps_midJ ly S W regs mem md pf pp format place R O ly2 S2 W2 regs2 mem3 md3 (0 + EV_REC_CALLS_FREE [l_spill QL])
  (l_spill QL) (ablocks B ly2 S2) (concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)).
Proof.
intros ly S W regs mem md ch pf pp format place R O QL memc mdc regsc ly2 S2 W2 regs2 mem2 md2 mem3 md3
  PRE Hn HA HO KEEPc HFRc HJr HP2 HPERM HREP2 HMLE HJ3 KEEP3 R2 R3 R4 R8 R9 R19 R20 Rhi.
pose proof PRE as (HPRE & HRM & HROD & HRO & H10 & Hpf & H11 & Hpp & HAF & HAP & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
assert (WR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
pose proof (proj1 HJ3) as HAR3. pose proof (proj1 HJr) as HAR2.
pose proof HJr as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & HSPILL & _) & _ & _ & _ & HOWN).
pose proof HSPILL as (_ & HSP6 & HLP & _ & _ & HSPND & _).
set (P := l_spill QL) in *.
set (O1 := concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)) in *.
assert (Hslot : sps_slot R = A_REC_SPILL) by (unfold sps_slot; rewrite Hn; reflexivity).
assert (Hsf : rec_spill_frees R = Z.of_nat (length P)) by (unfold rec_spill_frees; rewrite Hn, HLP; reflexivity).
assert (HEVk : EV_REC_CALLS_FREE [P] = Z.of_nat (length P))
  by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
assert (HPin : forall pn, In pn P -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (RecBLemmas.acall_at_in _ _ _ _ _ HSPILL pn Hpn)).
assert (HPpos : forall p n, In (p, n) P -> 4096 <= p).
{ intros p n Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HPin _ Hin)) as (_ & H4096 & _). exact H4096. }
assert (HPO : forall pn, In pn P -> In pn O) by (intros pn Hpn; apply HO; exact (sps_in_lay_spill QL pn Hpn)).
(* a byte of the image outside record.spill's nargs word is kept by rec_calls_free *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) -> rdW W2 mem2 a = rdW W memc a).
{ intros a Hi Ho He Hs. apply (G3 a Hi Ho He). apply sps_rcf_spares; [exact HPpos | exact Hs |].
  intros p n Hin Hr. exact (proj1 (sps_blk_low ly S W mem md p n a HAR (HPin _ Hin) Hr) Hi). }
(* a block of the entry state that rec_calls_free does not free survives with its bytes *)
assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> ~ In (p, n) P -> p <= a < p + req_size n ->
  In (p, n) (ablocks B ly2 S2) /\ rdW W2 mem2 a = rdW W memc a).
{ intros p n a Hin HnP Ha.
  assert (Hin2 : In (p, n) (ablocks B ly2 S2)).
  { apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [H|H]; [exact H|].
    cbn [concat] in H. rewrite app_nil_r in H. contradiction. }
  split; [exact Hin2|].
  replace a with (p + (a - p)) by lia. apply (G2 p n (a - p) Hin Hin2); [lia|].
  replace (p + (a - p)) with a by lia. intros Hf.
  destruct (sps_rcf_fp_inv P a Hf) as [Hs | (q & k & Hqk & Hr)].
  - destruct (sps_blk_low ly S W mem md p n a HAR Hin Ha) as [Hni _]. apply Hni.
    apply cmd_prog_img, recb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia.
  - assert (Hne : (q, k) <> (p, n)) by (intros E; rewrite E in Hqk; contradiction).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md q k p n HAR (HPin _ Hqk) Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HO1 : forall pn, In pn O1 -> In pn O).
{ intros pn Hpn. apply HO. unfold O1, lay_blocks in *. apply in_app_iff in Hpn as [H|H]; apply in_app_iff;
  [left; exact H | right; apply in_app_iff; right; exact H]. }
assert (HND : NoDup (map fst (lay_blocks QL))) by exact (proj1 HOWN).
unfold sps_midJ. cbn zeta.
split; [exact HJ3|]. split; [rewrite HEVk, Hsf; lia|].
split.
{ intros j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sps_saved j)); rewrite Hj; discriminate).
  apply (sps_aval_kept_rng (rdW W memc)); [exact (HFRc j r Hj)|]. intros x Hx. cbn [Z.of_nat] in Hx.
  assert (Hsp' : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia).
  rewrite KEEP3 by lia. apply G1; [lia | rewrite WR; lia |].
  intros Hf. destruct (sps_rcf_fp_inv P x Hf) as [Hs | (q & k & Hqk & Hr)]; [unfold A_REC_SPILL in Hs; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR (HPin _ Hqk)) as (_ & _ & Hqc & _). lia. }
assert (Hra2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) by exact HP2.
split; [etransitivity; [exact (Hra2 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
split; [etransitivity; [exact (Hra2 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
split; [etransitivity; [exact (Hra2 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
split; [rewrite Hslot; etransitivity; [exact (Hra2 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
split; [etransitivity; [exact (Hra2 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
split; [etransitivity; [exact (Hra2 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
split; [etransitivity; [exact (Hra2 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
split; [intros r Hr; rewrite (Hra2 r ltac:(unfold acallee_saved; lia)); exact (Rhi r Hr)|].
split.
{ intros rd' Hrd' Hfn Hna. rewrite Hslot in Hrd', Hfn, Hna.
  destruct HREP2 as (Q2 & HA2 & HO2). exists Q2. split; [|exact HO2].
  rewrite (rec_record_spill R SPS_FN [] Hn).
  change (set_spill R (SPS_FN, [])) with (set_spill (set_spill R (fst (r_spill R), [])) (SPS_FN, [])).
  apply (sps_arep_spillw _ (rdW W2 mem2) rd' _ Q2 SPS_FN HA2 eq_refl ltac:(unfold SPS_FN, REC_POLICY_SET, REC_FN_COUNT; lia)).
  - intros x Hx. rewrite Hrd' by sps_zl. apply KEEP3. sps_zl.
  - intros [q k] x Hq Hx. cbn [fst snd] in Hx.
    pose proof (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA2 (q, k) Hq) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR2 Hin) as (_ & _ & _ & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
    destruct (sps_blk_low ly2 S2 W2 mem2 md2 q k x HAR2 Hin ltac:(lia)) as [Hni Hlo].
    rewrite Hrd'; [apply KEEP3; lia | lia |].
    intros Hc. apply Hni. apply cmd_prog_img, recb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia.
  - exact Hfn.
  - exact Hna. }
split.
{ intros pn. rewrite (HO pn).
  assert (HND' : NoDup (map fst (concat (l_calls QL) ++ P ++ oblk (l_answer QL) ++ oblk (l_reply QL)))) by exact HND.
  split.
  - intros H. split; [apply HO, HO1, H|]. intros HP. unfold O1 in H. apply in_app_iff in H as [Hc | Hr].
    + apply (sps_nodup_disj fst (concat (l_calls QL)) (P ++ oblk (l_answer QL) ++ oblk (l_reply QL)) pn HND' Hc).
      apply in_or_app. left. exact HP.
    + apply (sps_nodup_disj fst (concat (l_calls QL) ++ P) (oblk (l_answer QL) ++ oblk (l_reply QL)) pn);
      [rewrite <- app_assoc; exact HND' | apply in_or_app; right; exact HP | exact Hr].
  - intros [H HnP]. unfold lay_blocks in H. unfold O1. apply in_app_iff in H as [H|H]; [apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H|H]; [contradiction|]. apply in_app_iff. right. exact H. }
split; [exact HPO|].
split; [intros Hlt; lia|].
split; [cbn [concat] in HPERM; rewrite app_nil_r in HPERM; eapply Permutation_trans; [exact HPERM | apply Permutation_app_comm]|].
split; [apply Permutation_refl|].
assert (HBLK : forall pk, In pk (ablocks B ly S) -> ~ In pk O -> In pk (ablocks B ly2 S2) /\
   forall a, fst pk <= a < fst pk + snd pk -> rdW W2 mem3 a = rdW W mem a).
{ intros [p n] Hin HnO. assert (HnP : ~ In (p, n) P) by (intros H; exact (HnO (HPO _ H))).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq].
  split; [exact (proj1 (KBLK p n p Hin HnP ltac:(lia)))|]. intros a Ha. cbn [fst snd] in Ha.
  destruct (sps_blk_low ly S W mem md p n a HAR Hin ltac:(lia)) as [Hni Hlo].
  rewrite KEEP3 by lia. rewrite (proj2 (KBLK p n a Hin HnP ltac:(lia))). apply KEEPc; [lia|].
  assert (Hsp' : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia). lia. }
split; [exact (sps_harg_move ly S W mem md ly2 S2 W2 mem3 md3 O O1 pf format HAR HAF HBLK HO1)|].
split; [exact (sps_harg_move ly S W mem md ly2 S2 W2 mem3 md3 O O1 pp place HAR HAP HBLK HO1)|].
rewrite Hsf. unfold XM_REC_CALLS_FREE in HMLE. cbn [concat] in HMLE. rewrite app_nil_r in HMLE. exact HMLE.
Qed.

Lemma sps_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sps_BxA [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* a read-only byte is no byte of the statement's footprint: not g_rec, not record.spill, not a heap block *)
Lemma sps_ro_not_fp : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> in_roP SEGS RLO RHI a -> ~ inFP (sps_FP O) a.
Proof.
intros ly S W mem md O a HAR HOb Hro Hf. destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg].
unfold sps_FP in Hf. apply inFP_cons in Hf as [Hf | Hf]; [exact (Hpg (recb_grec_in a Hf))|].
apply inFP_cons in Hf as [Hf | Hf]; [exact (Hpg (recb_spill_in a Hf))|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Hr).
exact (proj1 (sps_blk_low ly S W mem md p n a HAR (HOb _ Hin) Hr) Hi).
Qed.

(* every byte of the statement's footprint lies below the allocator's ceiling, so below the frame *)
Lemma sps_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sps_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HOb Hf. pose proof asan_consts as (C1 & _).
unfold sps_FP in Hf. apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE in Hf; lia|].
apply inFP_cons in Hf as [Hf | Hf]; [unfold A_REC_SPILL, SC_SIZE in Hf; lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Hr).
exact (proj2 (proj2 (sps_blk_low ly S W mem md p n a HAR (HOb _ Hin) Hr))).
Qed.

(* --- segment A: the entry, record()'s two arms, to the join --------------------------------------------- *)
Lemma sps_A_ok : SPS_J_stmt -> SPS_AB_stmt.
Proof.
intros JN ly S W regs mem md ch pf pp format place R O PRE.
pose proof PRE as (HPRE & HRM & HROD & HRO & H10 & Hpf & H11 & Hpp & HAF & HAP & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
pose proof HREP as (QL & HA & HO).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hp; exact (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA pn (proj1 (HO pn) Hp))).
pose proof HA as (Hg8 & Hs8 & Hgs & (Hlen & Hlenl & HNC & HCALLS & HSPILL & HSPF) & _).
destruct (sps_seedA ly S W regs mem md (Z.of_nat (length (r_calls R))) HAR Hstk Hpres ltac:(lia) HNC) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_POLICY_SET_STK (sps_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (sps_EA regs (Z.of_nat (length (r_calls R))))) by (unfold sps_EA; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (sps_EA regs (Z.of_nat (length (r_calls R)))) m = getr regs rr)
  by (intros m rr Hm; unfold sps_EA; apply ew_Eimg_Ereg_nat; exact Hm).
assert (EG : ew (sps_EA regs (Z.of_nat (length (r_calls R)))) 285 = Z_to_bv 64 A_G_REC).
{ unfold sps_EA. change 285%nat with (A_OBJ 44). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite sps_grec_val. reflexivity. }
assert (E33 : ew (sps_EA regs (Z.of_nat (length (r_calls R)))) 33 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
  by (unfold sps_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E32 : ew (sps_EA regs (Z.of_nat (length (r_calls R)))) 32 = Z_to_bv 64 sps_SB)
  by (unfold sps_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (sps_EA regs (Z.of_nat (length (r_calls R)))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E (A_OBJ 44)) = A_G_REC)
  by (change (A_OBJ 44) with 285%nat; rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EGu' : bv_unsigned (ew E 285) = A_G_REC) by exact EGu.
unfold cfg_at, w64. unfold SPS_ENTRY in HS.
paj_run_tok RUN HS HJ SHOK sps_Bspan.
{ sps_awrA Usp EGu. }
(* the prologue's memory: everything outside the frame and g_rec.ncalls is kept *)
assert (WIN : forall b wlo whi a, In (b, wlo, whi) (windows sps_rsA) -> base_val E b + wlo <= a < base_val E b + whi ->
  spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4).
{ sps_winA Usp EGu'. }
psrr_branch_tok RUN BR HS SHOK sps_Bspan.
- (* g_rec.ncalls <> 16: the slot arm *)
  assert (Hn16 : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33 _ E33) in Hc by lia. rewrite U_SLit in Hc.
    rewrite (sps_zcanon 16) in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK sps_Bspan SPS_JOIN.
  { sps_awrA Usp EGu. }
  pmkst HS.
  sps_reg HS (2%bv : bv 5) Q2. sps_reg HS (3%bv : bv 5) Q3. sps_reg HS (4%bv : bv 5) Q4.
  sps_reg HS (8%bv : bv 5) Q8. sps_reg HS (9%bv : bv 5) Q9. sps_reg HS (19%bv : bv 5) Q19.
  sps_reg HS (20%bv : bv 5) Q20.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
      (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr0);
      [ | sps_winA Usp EGu' | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  sps_region HS 0%nat HRs. sps_region HS 3%nat HRn.
  assert (HFRM : sps_frame (rdW W (ms_mem ms0)) (spZ regs) regs)
    by exact (sps_frame_of_region E W (ms_mem ms0) (spZ regs) regs HRs Usp EEo).
  assert (HNC1 : aval_mem (rdW W (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)).
  { apply (RecBLemmas.aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) _ HRn EGu' ltac:(cbn; tauto)); [| cbn; lia | cbn; lia].
    apply sps_denot_U. rewrite U_SOff, E33, unsigned_lit_small by lia. apply sps_zcanon. lia. }
  assert (HGt : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)))
    by exact (mem_grows_trans _ _ _ HG HG0).
  assert (Hsp' : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia).
  assert (Q2' : getr (ms_regs ms0) 2 = w64 (spZ regs - 64)).
  { rewrite Q2. apply sps_denot_U. rewrite U_SOff, Usp. apply sps_zcanon. lia. }
  assert (Q3' : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite Q3, sps_soff0; apply EEo; reflexivity).
  assert (Q4' : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite Q4, sps_soff0; apply EEo; reflexivity).
  assert (Q8' : getr (ms_regs ms0) 8 = w64 (sps_slot R)).
  { rewrite Q8, (sps_denot_slot E _ E33 EG Hn16). unfold sps_slot, w64.
    pose proof Hn16 as Hn'. apply Nat.ltb_lt in Hn'. rewrite Hn'. reflexivity. }
  assert (Q9' : getr (ms_regs ms0) 9 = w64 pp) by (rewrite Q9, sps_soff0, (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (Q19' : getr (ms_regs ms0) 19 = w64 pf) by (rewrite Q19, sps_soff0, (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (Q20' : getr (ms_regs ms0) 20 = w64 SHADOW_OFF) by (rewrite Q20, sps_soff0, E32; reflexivity).
  assert (Qhi : forall r, 22 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    (match goal with |- getr _ ?rr = _ => sps_reg HS rr Qr end; rewrite Qr, sps_soff0; apply EEo; reflexivity). }
  pose proof (sps_midJ_slot ly S W regs mem md ch pf pp format place R O (ms_regs ms0) (ms_mem ms0) _
    PRE Hn16 HJ HFRM KEEP HNC1 HGt Q2' Q3' Q4' Q8' Q9' Q19' Q20' Qhi) as MID.
  exact (JN ly S W regs mem md ch pf pp format place R O ly S W (ms_regs ms0) (ms_mem ms0) _ 0 [] (ablocks B ly S) O
    PRE MID).
- (* g_rec.ncalls = 16: the spill arm, record() frees the spill's arguments by rec_calls_free(&record.spill, 1) *)
  assert (Hn16 : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U, (U_atom E 33 _ E33) in Hc by lia. rewrite U_SLit in Hc.
    rewrite (sps_zcanon 16) in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_tok RUN HS HJ SHOK sps_Bspan.
  { sps_awrA Usp EGu. }
  pmkst HS.
  sps_reg HS (1%bv : bv 5) Q1. sps_reg HS (2%bv : bv 5) Q2. sps_reg HS (3%bv : bv 5) Q3. sps_reg HS (4%bv : bv 5) Q4.
  sps_reg HS (8%bv : bv 5) Q8. sps_reg HS (9%bv : bv 5) Q9. sps_reg HS (10%bv : bv 5) Q10. sps_reg HS (11%bv : bv 5) Q11.
  sps_reg HS (19%bv : bv 5) Q19. sps_reg HS (20%bv : bv 5) Q20.
  set (regsc := ms_regs ms0) in *. set (memc := ms_mem ms0) in *.
  sps_region HS 0%nat HRs. sps_region HS 3%nat HRn.
  assert (HNCc : aval_mem (rdW W memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)))).
  { apply (RecBLemmas.aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) _ HRn EGu' ltac:(cbn; tauto)); [| cbn; lia | cbn; lia].
    rewrite sps_soff0. exact E33. }
  assert (KEEPw : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) memc
      (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr0);
      [ | sps_winA Usp EGu' | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1. destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl | Hl];
    [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh]].
    - apply KEEPw; [exact Ha | exact H1 | lia].
    - replace a with ((A_G_REC + OFF_NCALLS) + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
      rewrite (HNCc (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)), (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)).
      reflexivity.
    - apply KEEPw; [exact Ha | exact H1 | lia]. }
  assert (HFRc : sps_frame (rdW W memc) (spZ regs) regs)
    by exact (sps_frame_of_region E W memc (spZ regs) regs HRs Usp EEo).
  assert (Hsp' : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia).
  (* the recorder at the call: g_rec, record.spill and the recorder's blocks are untouched by the prologue *)
  assert (HAc : arep_at (ablocks B ly S) (rdW W memc) A_G_REC A_REC_SPILL R QL).
  { apply (sps_arep_kept (ablocks B ly S) _ (rdW W mem)); [exact HA | exact (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA) | | |].
    - intros x Hx. apply KEEPc; sps_zl.
    - intros x Hx. apply KEEPc; sps_zl.
    - intros [p n] x Hpn Hx. cbn [fst snd] in Hx. pose proof (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA (p, n) Hpn) as Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq].
      destruct (sps_blk_low ly S W mem md p n x HAR Hin ltac:(lia)) as [_ Hlo]. apply KEEPc; lia. }
  assert (HSPc : acall_at (ablocks B ly S) (rdW W memc) A_REC_SPILL (r_spill R) (l_spill QL))
    by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj2 (proj2 (proj2 HAc))))))))).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W memc)).
  { apply (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B _ _ _ ly S W mem md [] ly S W memc _ 0 HJ); [|exact HROD].
    intros a. exact (sps_ro_not_fp ly S W mem md O a HAR (fun pn H => RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA pn (proj1 (HO pn) H))). }
  assert (Ec292 : ew E 292 = Z_to_bv 64 A_REC_SPILL).
  { apply bv_eq. rewrite (HEI 292%nat ltac:(unfold A_TEXT, A_LIM; lia)). change 292%nat with (A_OBJ 51).
    rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia). vm_compute. reflexivity. }
  assert (HRA : getr regsc 1 = Z_to_bv 64 (BASE + SPS_RET_RCF)) by (rewrite Q1; apply codeptr_val; exact HEI).
  assert (Q2' : getr regsc 2 = w64 (spZ regs - 64)).
  { rewrite Q2. apply sps_denot_U. rewrite U_SOff, Usp. apply sps_zcanon. lia. }
  assert (Q3' : getr regsc 3 = getr regs 3) by (rewrite Q3, sps_soff0; apply EEo; reflexivity).
  assert (Q4' : getr regsc 4 = getr regs 4) by (rewrite Q4, sps_soff0; apply EEo; reflexivity).
  assert (Q8' : getr regsc 8 = w64 A_REC_SPILL) by (rewrite Q8, sps_soff0; exact Ec292).
  assert (Q9' : getr regsc 9 = w64 pp) by (rewrite Q9, sps_soff0, (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (Q10' : getr regsc 10 = w64 A_REC_SPILL) by (rewrite Q10, sps_soff0; exact Ec292).
  assert (Q11' : getr regsc 11 = w64 (Z.of_nat (length [l_spill QL]))) by (rewrite Q11; reflexivity).
  assert (Q19' : getr regsc 19 = w64 pf) by (rewrite Q19, sps_soff0, (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (Q20' : getr regsc 20 = w64 SHADOW_OFF) by (rewrite Q20, sps_soff0, E32; reflexivity).
  assert (Qhi : forall r, 22 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. unfold regsc. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    (match goal with |- getr _ ?rr = _ => sps_reg HS rr Qr end; rewrite Qr, sps_soff0; apply EEo; reflexivity). }
  pose proof (SIGP CS_rec_calls_free ltac:(cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))) as SIGr.
  assert (SIGr' : SIG CS_rec_calls_free = BASE + AF_rec_calls_free) by (rewrite SIGr; f_equal; vm_compute; reflexivity).
  rewrite SIGr'.
  pose proof HSPc as (_ & HSP6 & HLP & _ & HSPN & HSPND & HSPA).
  assert (HPin : forall pn, In pn (l_spill QL) -> In pn (ablocks B ly S)) by exact (RecBLemmas.acall_at_in _ _ _ _ _ HSPc).
  assert (HPO : forall pn, In pn (l_spill QL) -> In pn O) by (intros pn Hpn; apply HO; exact (sps_in_lay_spill QL pn Hpn)).
  assert (Hsf : rec_spill_frees R = Z.of_nat (length (l_spill QL))) by (unfold rec_spill_frees; rewrite Hn16, HLP; reflexivity).
  assert (HEVk : EV_REC_CALLS_FREE [l_spill QL] = Z.of_nat (length (l_spill QL)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W regsc memc _ SUP_POLICY_SET_STK (spZ regs) (sps_FP O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill QL]) (EV_REC_CALLS_FREE [l_spill QL]) (-64) (getr regsc 1) []
      _ HJ);
    [ unfold spZ at 1; rewrite Q2'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | reflexivity | lia | vm_compute; congruence | rewrite WS; vm_compute; congruence
    | rewrite Q3'; exact Hgp | rewrite Q4'; exact Htp | reflexivity
    | rewrite HRA; apply ret_ok_codeptr_v; [unfold SPS_RET_RCF, AF_sup_policy_set; lia | reflexivity]
    | rewrite HRA, unsigned_lit_small by (unfold SPS_RET_RCF, AF_sup_policy_set; lia); unfold SPS_RET_RCF, AF_sup_policy_set; lia
    | apply achain_low; unfold s0Z; rewrite Q8'; unfold w64; rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia);
      unfold A_REC_SPILL; lia
    | | | ].
    - intros HPRE1.
      assert (HT := TRCF fx ly S W regsc memc _ [] A_REC_SPILL [l_spill QL] HPRE1 HRODc Q10' Q11'
        ltac:(cbn [length]; lia)
        ltac:(right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; cbn [length Z.of_nat]; lia)
        ltac:(unfold A_REC_SPILL; reflexivity)).
      unfold apost_base, cfg_at, w64 in HT. apply HT.
      + intros i P Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn [nth_error] in Hi. injection Hi as <-.
        split; [lia|]. split.
        * cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r, HLP. exact HSPN.
        * intros a pn Ha. destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs.
          -- destruct (HSPA a s pn Hs Ha) as (G1 & _ & G3 & _). split; [|exact G3].
             cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact G1.
          -- exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill QL) a) ltac:(rewrite Ha; discriminate)). lia.
      + cbn [concat]. rewrite app_nil_r. exact HSPND.
      + rewrite HEVk, <- Hsf. unfold EV_SUP_POLICY_SET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
      + apply (mo_ok_le MT MTL S _ (XM_SUP_POLICY_SET MT R format place) HMOK).
        unfold XM_REC_CALLS_FREE, XM_SUP_POLICY_SET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
        cbn [concat]. rewrite app_nil_r, <- Hsf.
        pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg format)) + 1) ltac:(lia)).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg place)) + 1) ltac:(lia)).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_policy_set_m R format place))) + 1) ltac:(lia)). lia.
    - intros a Ha. destruct (sps_rcf_fp_inv (l_spill QL) a Ha) as [Hs | (p & n & Hin & Hr)].
      + apply sps_awr_spill. unfold A_REC_SPILL, SC_SIZE in *. lia.
      + unfold awr_byte. right; left. split; [|exists p, n; split; [exact (HPin _ Hin) | exact Hr]].
        unfold sps_FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p n (a - p)); [exact (HPO _ Hin) | lia].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
      destruct (sps_rcf_fp_inv (l_spill QL) a Ha) as [Hs | (p & n & Hin & Hr)]; [unfold A_REC_SPILL in Hs; rewrite WS in Hw; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HPin _ Hin)) as (_ & _ & Hpc & _). rewrite WS in Hw. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJr & HP2 & HK2).
  destruct HK2 as (HPERM & _ & _ & _ & _ & HRSP & _ & _ & HMLE).
  pose proof (HRSP R QL HAc eq_refl eq_refl) as HREP2.
  (* 0x8ba0c: `j 0x8ba2c`, record()'s arms meet *)
  rewrite HRA.
  destruct (sps_seed0 W2 regs2 mem2 SPS_RET_RCF) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 sps_Bspan SPS_JOIN.
  { apply awr_ok_nil. }
  pmkst HS2.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H W2) mem2 (ms_mem ms1) (fun _ => False) HFr1); [|exact Ha | tauto].
    intros b wlo whi a' Hin. destruct Hin. }
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 []))).
  { split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)) as HPT3.
  cbn [ms_regs restrict] in HPT3.
  pose proof (sps_midJ_spill ly S W regs mem md ch pf pp format place R O QL memc _ regsc ly2 S2 W2 (ms_regs ms1) mem2 md2
    (ms_mem ms1) _ PRE Hn16 HA HO KEEPc HFRc HJr (aregs_preserved_trans _ _ _ HP2 HPT3) HPERM HREP2 HMLE HJ2 KEEP3
    Q2' Q3' Q4' Q8' Q9' Q19' Q20' Qhi) as MID.
  exact (JN ly S W regs mem md ch pf pp format place R O ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ PRE MID).
Qed.

(* --- segment B: from the join to the call of xstrdup on the first argument ------------------------------- *)
(* the registers at the join as the symbolic state names them (RecBTemplate.v's atoms): s0 = the slot c, s4 = the
   shadow base; the one region is the slot's fn and nargs words [c, c + 8), the one shadow entry the slot's
   (rbt_SH) *)
Definition sps_sregsB : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 8 (SOff RB_C 0)) 20 (SOff RB_SB 0).
Definition sps_slotB : YP09.region := YP09.mkRegion (Some RB_C) 0 8 0 8 [].
Definition ss_spsB : sstate := mkSS SPS_JOIN sps_sregsB [sps_slotB] None (rbt_facts 0 16).
Definition sps_EB (regs1 : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs1 (rbt_extra regs1 0 c)).
Definition sps_BspanB : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma sps_slot_ok : forall R, (length (r_calls R) <= 16)%nat -> rbt_slot_ok (sps_slot R).
Proof.
intros R H. unfold sps_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
apply Z.mod_divide; [lia|]. exists (771818 + 7 * Z.of_nat (length (r_calls R))). lia.
Qed.

Lemma sps_awr_slot : forall STK sp0 O bl0 blc fr0 ly own c a, rbt_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (sps_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own c a [(H1 & H2 & _) | ->] Ha.
- apply sps_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply sps_awr_spill. unfold A_REC_SPILL, CALL_SIZE, SC_SIZE in *. lia.
Qed.

Ltac sps_regs_tac EEo :=
  apply regs_ok_by_cases; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [all_regs In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?l ?rr) =>
        let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ symmetry; apply EEo; reflexivity | rewrite getr_zero; reflexivity | idtac ]
    | ]); try (destruct Hr; fail).

Lemma sps_seedB : forall ly S (W : world SEGS) mem md (regs1 : bvmap 5 word) c,
AR SEGS B ly S W mem md -> rbt_slot_ok c ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
getr regs1 8 = w64 c -> getr regs1 20 = w64 SHADOW_OFF ->
st_ok_pi SEGS VAL (sps_EB regs1 c) ss_spsB
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + SPS_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbt_SH (sps_EB regs1 c) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs1 c HAR Hc Hsp Hsp16 R8 R20.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
set (E := sps_EB regs1 c).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (rbt_extra regs1 0 c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold sps_EB; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold sps_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ESB : ew E RB_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (EN : ew E RB_N = Z_to_bv 64 0) by exact (EX 1%nat ltac:(lia)).
assert (EC : ew E RB_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (HENV : rbt_env_ok E (spZ regs1) 0 c).
{ split; [exact HEI|]. split; [rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [exact ESB|]. split; [exact EN | exact EC]. }
assert (UC : base_val E (Some RB_C) = c)
  by (cbn [base_val]; rewrite EC; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split.
2: { apply (rbt_sh_ok B) with (ly := ly) (S := S) (md := md) (sp := spZ regs1) (n := 0) (c := c);
     first [exact HAR | exact HENV | exact Hc | exact LAWS | exact HB]. }
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- sps_regs_tac EEo.
  + rewrite R8. symmetry. exact EC.
  + rewrite R20. symmetry. exact ESB.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold sps_slotB, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite UC. split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
  split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
  split; [|constructor].
  intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR).
  destruct Hc as [(H1 & H2 & H3) | ->].
  + apply recb_grec_in. unfold CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *. lia.
  + apply recb_spill_in. unfold CALL_SIZE, SC_SIZE, A_REC_SPILL in *. lia.
- cbn. repeat split.
- apply rbt_facts_ok with (sp := spZ regs1) (n := 0) (c := c);
  first [exact HENV | exact Hsp16 | exact Hc | exact VOBJS | lia].
Qed.

(* --- the call of xstrdup that ends segment B, and the walk's facts after it ---------------------------------- *)

(* what a callee with an empty footprint keeps (sup_lv2_worker_set_s2.v's slw_callee_keeps, with the image clause) *)
Lemma sps_callee_keeps : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc memc a) /\
(forall a, sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
(forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW Wc memc (p + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rdW W2 mem2 a = rdW Wc memc a).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & _).
assert (SP : forall a, fp_spares [] a) by (intros a; apply fp_spares_closed; [exact sink_closed_nil | intros (r & [] & _)]).
split; [|split; [|split]].
- intros a HP. rewrite <- (recb_ts_prog_m B HB) in HP.
  destruct (prog_static_sep B a (ts_ok B HB) HP) as (Ho & He & _).
  apply F3; [apply cmd_prog_img; rewrite <- (recb_ts_prog_m B HB); exact HP | exact Ho | exact He | apply SP].
- intros a Ha. apply F1; [lia | lia | intros (r & [] & _)].
- intros p n i H1 H2 Hi. exact (F2 p n i H1 H2 Hi (fun HF => match HF with ex_intro _ r (conj Hr _) => Hr end)).
- intros a Hi Ho He. exact (F3 a Hi Ho He (SP a)).
Qed.

Lemma sps_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' P. induction P; unfold bsum in *; cbn [fold_right] in *; lia. Qed.

Lemma sps_bsum_nonneg : forall ly S (W : world SEGS) mem md L, AR SEGS B ly S W mem md ->
(forall pn, In pn L -> In pn (ablocks B ly S)) -> 0 <= bsum L.
Proof.
intros ly S W mem md L HAR HL. induction L as [|[p n] L IH]; [unfold bsum; cbn; lia|].
rewrite bsum_cons. cbn [snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HL _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
assert (0 <= bsum L) by (apply IH; intros pn Hpn; apply HL; right; exact Hpn). lia.
Qed.

Lemma sps_slot_pg : forall c a, rbt_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a [(H1 & H2 & _) | ->] Ha.
- apply recb_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply recb_spill_in. unfold A_REC_SPILL, CALL_SIZE, SC_SIZE in *. lia.
Qed.

(* a string argument survives record()'s stores into the slot's first 8 bytes *)
Lemma sps_harg_slot_move : forall lyc Sc (Wc : world SEGS) memc mdc memb c O O' p v,
AR SEGS B lyc Sc Wc memc mdc -> rbt_slot_ok c ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc memb a = rdW Wc memc a) ->
sps_harg lyc Sc (rdW Wc memc) O p v ->
(forall pn, In pn O' -> In pn O) ->
sps_harg lyc Sc (rdW Wc memb) O' p v.
Proof.
intros lyc Sc Wc memc mdc memb c O O' p v HARc Hc KEEPb HA HO'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (sps_harg_move lyc Sc Wc memc mdc lyc Sc Wc memb mdc O O' p v HARc HA); [|exact HO'].
intros [q n] Hin _. split; [exact Hin|]. intros a Ha. cbn [fst snd] in Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq].
destruct (sps_blk_low lyc Sc Wc memc mdc q n a HARc Hin ltac:(lia)) as [Hni Hlo].
apply KEEPb; [lia|]. intros Hcs. apply Hni. apply cmd_prog_img. apply (sps_slot_pg c a Hc). unfold CALL_SIZE. lia.
Qed.

(* the call of xstrdup at +0xbc and the state MID1 at its return: the slot holds fn and nargs (the stores of
   segment B), a0 the string s with its copy's facts *)
Lemma sps_xcall : SPS_C_stmt ->
forall ly S W regs mem md ch pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1
  (regsb : bvmap 5 word) memb mdb s,
sps_pre ly S W regs mem md ch pf pp format place R O ->
sps_midJ ly S W regs mem md pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1 ->
ajournal SEGS B SUP_POLICY_SET_STK (spZ regs) (sps_FP O) ly S W mem md [] lyc Sc Wc memb mdb k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sps_slot R <= a < sps_slot R + 8) -> rdW Wc memb a = rdW Wc memc a) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memb) ->
aval_mem (rdW Wc memb) (sps_slot R) 4 SPS_FN -> aval_mem (rdW Wc memb) (sps_slot R + 4) 4 0 ->
getr regsb 1 = Z_to_bv 64 (BASE + SPS_RET_X1) -> getr regsb 2 = w64 (spZ regs - 64) ->
getr regsb 3 = getr regs 3 -> getr regsb 4 = getr regs 4 ->
getr regsb 8 = w64 (sps_slot R) -> getr regsb 9 = w64 pp -> getr regsb 10 = w64 s ->
getr regsb 18 = w64 (sps_slot R + 4) -> getr regsb 20 = w64 SHADOW_OFF ->
getr regsb 21 = w64 (SHADOW_OFF + (sps_slot R + 4) / 8) ->
(forall r, 22 <= r <= 27 -> getr regsb (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
astr_argA B lyc Sc (rdW Wc memb) (in_roP SEGS RLO RHI) [] s (Some (sarg format)) ->
atail_vis SEGS Wc memb (s + Z.of_nat (length (sarg format))) ->
SRr SEGS Wc (mkCfg (mkst regsb (Z_to_bv 64 (BASE + AF_xstrdup)) memb (seg_rom SEGS)) mdb)
  (sps_post ly S W regs mem md R format place O).
Proof.
intros CN ly S W regs mem md ch pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1 regsb memb mdb s
  PRE MID HJb KEEPb HGb HFN HNA Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q20 Q21 Qhi HSTR HTL.
pose proof PRE as (HPRE & HRM & HROD & HRO & H10 & Hpf & H11 & Hpp & HAF & HAP & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
assert (HXS : 0 <= XSTRDUP_STK /\ XSTRDUP_STK - -64 <= SUP_POLICY_SET_STK) by (vm_compute; split; congruence).
pose proof MID as (HJ & Hk & HFR & R2 & R3 & R4 & R8 & R9 & R19 & R20 & Rhi & HREPF & HO1 & HDf & HDf0 & HPS & HPC
  & HAF1 & HAP1 & HMLE).
set (sp0 := spZ regs) in *. set (c := sps_slot R) in *.
pose proof (proj1 HJ) as HARc. pose proof (proj1 HJb) as HARb.
assert (Hlen : (length (r_calls R) <= 16)%nat) by (destruct HREP as (Q & (_ & _ & _ & (H & _) & _) & _); exact H).
assert (Hc : rbt_slot_ok c) by exact (sps_slot_ok R Hlen).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
assert (Hcnum : 4096 <= c < 2 ^ 40) by (cbv [A_G_REC A_REC_SPILL OFF_CALLS] in Hcb; lia).
assert (Hsp' : 2 ^ 46 + 64 <= sp0 <= 2 ^ 47) by (rewrite WS in Hslo; subst sp0; lia).
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)).
{ destruct HREP as (QL & HA & HO). intros pn H. exact (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA pn (proj1 (HO pn) H)). }
assert (HRODb : arodata_okP SEGS RLO RHI B (rdW Wc memb)).
{ apply (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B _ _ _ ly S W mem md [] lyc Sc Wc memb mdb k HJb);
  [|exact HROD].
  intros a. exact (sps_ro_not_fp ly S W mem md O a HAR HOb). }
pose proof HJb as (_ & _ & _ & _ & _ & HFRb & HNEVb & _).
assert (HEVb : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ unfold EV_SUP_POLICY_SET, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (HBB : blocks_bytes Sc <= blocks_bytes S).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S).
  rewrite (sps_bsum_perm _ _ HPC), (sps_bsum_perm _ _ HPS), bsum_app.
  assert (0 <= bsum Df) by (apply (sps_bsum_nonneg ly S W mem md Df HAR); intros pn Hpn; exact (HOb _ (HDf _ Hpn))).
  lia. }
assert (HLIVEb : blocks_bytes Sc + LIVE_XSTRDUP (sarg format) <= LIVE_MAX).
{ unfold LIVE_SUP_POLICY_SET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. lia. }
assert (HMOKb : mo_ok MT Sc (XM_XSTRDUP MT (sarg format))).
{ apply (mok_station MT S Sc (XM_SUP_POLICY_SET MT R format place) (rec_spill_frees R * mo_free MT) _ MTL HMOK HMLE).
  - unfold XM_XSTRDUP. apply (mo_malloc_nonneg MT MTL). lia.
  - unfold XM_SUP_POLICY_SET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
    pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg place)) + 1) ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_policy_set_m R format place))) + 1) ltac:(lia)).
    lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc regsb memb _ SUP_POLICY_SET_STK sp0 (sps_FP O) ly S W mem md [] lyc Sc mdb k
    XSTRDUP_STK [] EV_XSTRDUP (-64) (getr regsb 1) [] _ HJb);
  [ unfold spZ at 1; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia
  | reflexivity | lia | exact (proj1 HXS) | exact (proj2 HXS)
  | rewrite Q3; exact Hgp | rewrite Q4; exact Htp | reflexivity
  | rewrite Q1; apply ret_ok_codeptr_v; [unfold SPS_RET_X1, AF_sup_policy_set; lia | reflexivity]
  | rewrite Q1, unsigned_lit_small by (unfold SPS_RET_X1, AF_sup_policy_set; lia); unfold SPS_RET_X1, AF_sup_policy_set; lia
  | apply achain_low; unfold s0Z; rewrite Q8; unfold w64; rewrite unsigned_lit_small by lia; lia
  | | | ].
  - intros HPRE1.
    pose proof (TXSTRDUP fx lyc Sc Wc regsb memb mdb [] s (sarg format) HPRE1 HRODb Q10 (or_introl HSTR) HTL
      HEVb HLIVEb HMOKb) as HT.
    unfold apost_base, cfg_at, w64 in HT. exact HT.
  - intros a Ha. destruct Ha as (r & [] & _).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha. destruct Ha as (r & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP2 & HK2).
destruct HK2 as (p1 & Hp1r & Hp14 & HPERMx & HAPx & HBLKx & HCP & HSRC & HBBx & HMLEx).
pose proof (proj1 HJ2) as HAR2.
destruct (sps_callee_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) as (KPG & KSTK & KBLK & KIMG).
assert (Hra2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsb (Z_to_bv 5 r)) by exact HP2.
assert (HIN2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERMx)); right; exact Hpn).
rewrite Q1.
apply (CN ly S W regs mem md ch pf pp format place R O ly2 S2 W2 regs2 mem2 md2 (k + EV_XSTRDUP) p1 Df Lk O1 PRE).
unfold sps_mid1. cbn zeta. fold sp0 c.
split; [exact HJ2|].
split; [unfold EV_XSTRDUP in *; lia|].
split.
{ intros j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sps_saved j)); rewrite Hj; discriminate).
  apply (sps_aval_kept_rng (rdW Wc memc)); [exact (HFR j r Hj)|]. intros x Hx. cbn [Z.of_nat] in Hx.
  rewrite KSTK by lia. apply KEEPb; lia. }
split; [etransitivity; [exact (Hra2 2 ltac:(unfold acallee_saved; lia)) | exact Q2]|].
split; [etransitivity; [exact (Hra2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]|].
split; [etransitivity; [exact (Hra2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]|].
split; [etransitivity; [exact (Hra2 8 ltac:(unfold acallee_saved; lia)) | exact Q8]|].
split; [etransitivity; [exact (Hra2 9 ltac:(unfold acallee_saved; lia)) | exact Q9]|].
split; [etransitivity; [exact (Hra2 18 ltac:(unfold acallee_saved; lia)) | exact Q18]|].
split; [etransitivity; [exact (Hra2 20 ltac:(unfold acallee_saved; lia)) | exact Q20]|].
split; [etransitivity; [exact (Hra2 21 ltac:(unfold acallee_saved; lia)) | exact Q21]|].
split; [exact Hp1r|].
split; [intros r Hr; etransitivity; [exact (Hra2 r ltac:(unfold acallee_saved; lia)) | exact (Qhi r Hr)]|].
split.
{ destruct (HREPF (rdW Wc memb) KEEPb HFN HNA) as (Q & HA & HO).
  exists Q. split; [|exact HO].
  apply (sps_arep_kept (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc memb)); [exact HA | | | |].
  - intros pn Hpn. exact (HIN2 _ (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA pn Hpn)).
  - intros x Hx. apply KPG. apply recb_grec_in. exact Hx.
  - intros x Hx. apply KPG. apply recb_spill_in. exact Hx.
  - intros [p n] x Hpn Hx. cbn [fst snd] in Hx. pose proof (RecBLemmas.lay_blocks_in _ _ A_G_REC A_REC_SPILL _ _ HA (p, n) Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARb Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq].
    replace x with (p + (x - p)) by lia. apply (KBLK p n (x - p)); [exact Hin | exact (HIN2 _ Hin) | lia]. }
split; [exact HO1|]. split; [exact HDf|]. split; [exact HDf0|]. split; [exact HPS|].
split; [eapply Permutation_trans; [exact HPERMx | apply perm_skip; exact HPC]|].
split.
{ apply Forall_forall. intros qk Hqk. rewrite Forall_forall in HAPx.
  exact (HAPx qk (Permutation_in _ (Permutation_sym HPC) Hqk)). }
split; [exact Hp14|]. split; [exact HCP|].
assert (HAPb : sps_harg lyc Sc (rdW Wc memb) O1 pp place)
  by exact (sps_harg_slot_move lyc Sc Wc memc mdc memb c O1 O1 pp place HARc Hc KEEPb HAP1 (fun pn H => H)).
assert (HBLK2 : forall pk, In pk (ablocks B lyc Sc) -> ~ In pk O1 -> In pk (ablocks B ly2 S2) /\
   forall a, fst pk <= a < fst pk + snd pk -> rdW W2 mem2 a = rdW Wc memb a).
{ intros [p n] Hin _. split; [exact (HIN2 _ Hin)|]. intros a Ha. cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARb Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq].
  replace a with (p + (a - p)) by lia. apply (KBLK p n (a - p)); [exact Hin | exact (HIN2 _ Hin) | lia]. }
split; [exact (sps_harg_move lyc Sc Wc memb mdb ly2 S2 W2 mem2 md2 O1 O1 pp place HARb HAPb HBLK2 (fun pn H => H))|].
exact (mle_station MT S Sc S2 _ _ MTL HMLE HMLEx).
Qed.

Ltac sps_md := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

Ltac sps_winB UCb :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?UCb in Hrr; lia|]);
  destruct Hin.

Lemma sps_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof.
rewrite (SIGP CS_xstrdup ltac:(cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]))).
f_equal; try (vm_compute; reflexivity).
Qed.

(* --- segment B: the join, the two checked stores into the slot, the call of xstrdup on the first argument --- *)
Lemma sps_B_ok : SPS_C_stmt -> SPS_J_stmt.
Proof.
intros CN ly S W regs mem md ch pf pp format place R O lyc Sc Wc regs1 memc mdc k Df Lk O1 PRE MID.
pose proof PRE as (HPRE & HRM & HROD & HRO & H10 & Hpf & H11 & Hpp & HAF & HAP & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_POLICY_SET_STK = 16592) by (vm_compute; reflexivity).
pose proof MID as (HJ & Hk & HFR & R2 & R3 & R4 & R8 & R9 & R19 & R20 & Rhi & HREPF & HO1 & HDf & HDf0 & HPS & HPC
  & HAF1 & HAP1 & HMLE).
set (sp0 := spZ regs) in *. set (c := sps_slot R) in *.
pose proof (proj1 HJ) as HARc.
assert (Hlen : (length (r_calls R) <= 16)%nat) by (destruct HREP as (Q & (_ & _ & _ & (H & _) & _) & _); exact H).
assert (Hc : rbt_slot_ok c) by exact (sps_slot_ok R Hlen).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
assert (Hcnum : 4096 <= c < 2 ^ 40) by (cbv [A_G_REC A_REC_SPILL OFF_CALLS] in Hcb; lia).
assert (Hsp' : 2 ^ 46 + 64 <= sp0 <= 2 ^ 47) by (rewrite WS in Hslo; subst sp0; lia).
assert (Usp1 : spZ regs1 = sp0 - 64) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
destruct (sps_seedB lyc Sc Wc memc mdc regs1 c HARc Hc) as [HS SHOK];
  [rewrite Usp1; lia | rewrite Usp1; subst sp0; Z.div_mod_to_equations; lia | exact R8 | exact R20 |].
set (E := sps_EB regs1 c) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (rbt_extra regs1 0 c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold sps_EB; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold sps_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EC : ew E RB_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (ESB : ew E RB_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (UCb : bv_unsigned (ew E RB_C) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (UCb' : bv_unsigned (ew E 34%nat) = c) by exact UCb.
assert (ESBu : bv_unsigned (ew E 32%nat) = SB)
  by (change 32%nat with RB_SB; rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sps_BspanB.
{ eapply awr_ok_cons_gen; [reflexivity | exact UCb | | apply awr_ok_nil].
  intros a Ha. cbn [sps_slotB YP09.r_wlo YP09.r_whi] in Ha. apply (sps_awr_slot _ _ _ _ _ _ _ _ c); [exact Hc | unfold CALL_SIZE; lia]. }
sps_md.
pose proof HAF as HAFd. destruct HAFd as (x & Hfmt & _). subst format.
assert (Hpf0 : 4096 <= pf < 2 ^ 64) by exact (sps_harg_range ly S W mem md _ O pf x HAR HAF).
assert (U19 : U E (SOff 19 0) = pf)
  by (apply (U_atom E 19 pf); [rewrite (EEo 19%nat 19%bv eq_refl), R19; reflexivity | lia]).
psrr_branch_tok RUN BR HS SHOK sps_BspanB.
- paj_run_tok RUN HS HJ SHOK sps_BspanB.
  { eapply awr_ok_cons_gen; [reflexivity | exact UCb | | apply awr_ok_nil].
    intros a Ha. cbn [sps_slotB YP09.r_wlo YP09.r_whi] in Ha.
    apply (sps_awr_slot _ _ _ _ _ _ _ _ c); [exact Hc | unfold CALL_SIZE; lia]. }
  sps_md. pmkst HS.
  sps_reg HS (1%bv : bv 5) Q1. sps_reg HS (2%bv : bv 5) Q2. sps_reg HS (3%bv : bv 5) Q3.
  sps_reg HS (4%bv : bv 5) Q4. sps_reg HS (8%bv : bv 5) Q8. sps_reg HS (9%bv : bv 5) Q9.
  sps_reg HS (10%bv : bv 5) Q10. sps_reg HS (18%bv : bv 5) Q18. sps_reg HS (20%bv : bv 5) Q20.
  sps_reg HS (21%bv : bv 5) Q21.
  sps_region HS 0%nat HRg.
  assert (WINB : forall b wlo whi a, In (b, wlo, whi) (windows (ss_mem ss_spsB)) ->
    base_val E b + wlo <= a < base_val E b + whi -> c <= a < c + 8) by (sps_winB UCb').
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha H1.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun a => c <= a < c + 8) HFr0 WINB);
      [ | exact Ha | exact H1].
    exact (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a => c <= a < c + 8) HFr WINB a Ha H1). }
  assert (HGb : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms0)))
    by exact (mem_grows_trans _ _ _ HG HG0).
  assert (HFN0 : aval_mem (rdW Wc (ms_mem ms0)) (c + 0) 4 SPS_FN).
  { apply (RecBLemmas.aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ RB_C c _ _ _ _ _ 0 4 (SLit 12) _ HRg UCb ltac:(cbn; tauto));
    [ apply sps_denot_U; rewrite U_SLit; unfold SPS_FN, REC_POLICY_SET; apply sps_zcanon; lia
    | unfold SPS_FN, REC_POLICY_SET; cbn; lia | cbn; lia]. }
  rewrite Z.add_0_r in HFN0.
  assert (HNA : aval_mem (rdW Wc (ms_mem ms0)) (c + 4) 4 0).
  { apply (RecBLemmas.aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ RB_C c _ _ _ _ _ 4 4 (SLit 0) _ HRg UCb ltac:(cbn; tauto));
    [ apply sps_denot_U; rewrite U_SLit; apply sps_zcanon; lia | cbn; lia | cbn; lia]. }
  assert (U21 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 4) (SLit 3)) (SOff 32 0)) = SHADOW_OFF + (c + 4) / 8).
  { rewrite U_SAlu, U_SAlu, U_SLit, (U_SOff E 34%nat 4), (U_SOff E 32%nat 0), UCb', ESBu.
    unfold zcanon, M64. rewrite (Z.mod_small (c + 4)) by lia. rewrite (Z.mod_small 3) by lia.
    cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hq : 0 <= (c + 4) / 8 < 2 ^ 61) by (Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small ((c + 4) / 8)) by lia. rewrite (Z.mod_small (SB + 0)) by (unfold SB; lia).
    rewrite Z.mod_small by (unfold SB; lia). unfold SB, SHADOW_OFF. lia. }
  assert (HAFb : sps_harg lyc Sc (rdW Wc (ms_mem ms0)) [] pf (Some x))
    by exact (sps_harg_slot_move lyc Sc Wc memc mdc (ms_mem ms0) c O1 [] pf (Some x) HARc Hc KEEPb HAF1
      ltac:(intros pn Hpn; destruct Hpn)).
  rewrite (sps_sig_xstrdup).
  apply (sps_xcall CN ly S W regs mem md ch pf pp (Some x) place R O lyc Sc Wc regs1 memc mdc k Df Lk O1
    (ms_regs ms0) (ms_mem ms0) _ pf PRE MID HJ KEEPb HGb HFN0 HNA).
  + rewrite Q1. exact (codeptr_val E SPS_RET_X1 HEI).
  + rewrite Q2, sps_soff0, (EEo 2%nat 2%bv eq_refl). exact R2.
  + rewrite Q3, sps_soff0, (EEo 3%nat 3%bv eq_refl). exact R3.
  + rewrite Q4, sps_soff0, (EEo 4%nat 4%bv eq_refl). exact R4.
  + rewrite Q8, sps_soff0. exact EC.
  + rewrite Q9, sps_soff0, (EEo 9%nat 9%bv eq_refl). exact R9.
  + rewrite Q10, sps_soff0, (EEo 19%nat 19%bv eq_refl). exact R19.
  + rewrite Q18. apply sps_denot_U. rewrite (U_SOff E 34%nat 4), UCb'. apply sps_zcanon. lia.
  + rewrite Q20, sps_soff0. change 32%nat with RB_SB. rewrite ESB. reflexivity.
  + rewrite Q21. apply sps_denot_U. exact U21.
  + intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ (Z_to_bv 5 r) HS). cbn [ms_regs].
    assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    (match goal with
     | |- _ = sv_denot _ (sr_get ?l ?rr) =>
         let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v
     | |- sv_denot _ (sr_get ?l ?rr) = _ =>
         let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v
     end;
     cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
     match goal with |- ew _ ?n = getr _ ?rr => rewrite (EEo n rr ltac:(vm_compute; reflexivity)) end;
     apply Rhi; lia).
  + exact (sps_harg_argA lyc Sc Wc (ms_mem ms0) _ [] pf x (proj1 HJ) HAFb).
  + exact (sps_harg_tail lyc Sc Wc (ms_mem ms0) _ [] pf x (proj1 HJ) HAFb).
- exfalso. rewrite branch_ne_U, U19, U_SLit in Hc0. rewrite (sps_zcanon 0) in Hc0 by lia.
  apply negb_false_iff, Z.eqb_eq in Hc0. lia.
Qed.


End e.
End f.
End d.
