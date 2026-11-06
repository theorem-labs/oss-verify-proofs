(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB QCiC Qpj5 QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MAX_INPUT : Z := 67108864.
Definition RD_CHUNK : Z := 65536.
Definition HDR_MIN : Z := 6.
Definition COUNT_MAX : Z := 251.

Inductive diag_msg : Type :=
| DUsage (argv0 : list Z)
| DCannotOpen (path : list Z)
| DReadError (path : list Z)
| DOom
| DTooBig
| DShortHdr
| DCfgOverrun.

Record IOStyle (St : Type) := mkIO {
io_diag : diag_msg -> M St unit;
io_emit : Z -> M St unit;
io_exit : M St unit
}.
Arguments io_diag {St} _.
Arguments io_emit {St} _.
Arguments io_exit {St} _.

Section Driver.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable stage : Z.
Variable alloc_init : Z -> M St unit.
Variable run : Z -> list Z -> M St Z.
Variable alloc_count : M St Z.

Inductive rd_result : Type :=
| RdExit
| RdDone (buf : ptr) (content : list Z).

Record rd_st := mkRd { rd_buf : ptr; rd_cap : Z; rd_content : list Z }.

Definition u8s_of_bytes (bs : list byte) : list Z := map bv_unsigned bs.

Definition read_loop_body (fd : Z) (path : list Z) (st : rd_st) : M St (rd_st + rd_result) :=
let len := zlength (rd_content st) in

g <- (if len =? rd_cap st then
if MAX_INPUT <=? rd_cap st then
io_diag io DTooBig ;;; mret None
else
nb <- drv_malloc (rd_cap st * 2) ;;
match nb with
| None => io_diag io DOom ;;; mret None
| Some nb' => drv_free (rd_buf st) ;;;
mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
end
else mret (Some st)) ;;
match g with
| None => mret (inr RdExit)
| Some st1 =>
let want := rd_cap st1 - len in
let cnt := if RD_CHUNK <? want then RD_CHUNK else want in
a <- msys (NRead fd stage cnt) (dec_read stage cnt) ;;
match a with
| RdErr _ => io_diag io (DReadError path) ;;; mret (inr RdExit)
| RdData bs =>
if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
end
end.

Definition READ_FUEL : nat := Z.to_nat (MAX_INPUT + 16).

Definition read_all (path : list Z) : M St rd_result :=
r <- msys (NOpen (map (Z_to_bv 8) path)) dec_open ;;
match r with
| SErr _ => io_diag io (DCannotOpen path) ;;; mret RdExit
| SVal fd =>
b <- drv_malloc 65536 ;;
match b with
| None => io_diag io DOom ;;; mret RdExit
| Some buf =>
res <- mloop READ_FUEL (read_loop_body fd path) (mkRd buf 65536 []) ;;
match res with
| RdExit => mret RdExit
| RdDone buf' content => _ <- msys (NClose fd) dec_close ;; mret (RdDone buf' content)
end
end
end.

Definition le16 (l : list Z) : Z := znth l 0 + znth l 1 * 256.
Definition le32 (l : list Z) : Z := znth l 0 + znth l 1 * 2^8 + znth l 2 * 2^16 + znth l 3 * 2^24.

Definition main_model (argv : list (list Z)) : M St Z :=
if negb (Z.of_nat (length argv) =? 2) then
io_diag io (DUsage (nth 0 argv [])) ;;; mret 2
else
ra <- read_all (nth 1 argv []) ;;
match ra with
| RdExit => mret 2
| RdDone buf content =>
let len := zlength content in
if len <? HDR_MIN then io_diag io DShortHdr ;;; drv_free buf ;;; mret 2
else
let cfg_word := le16 content in
let count_allocs := Z.testbit cfg_word 15 in
let config_len := Z.land cfg_word 0x7fff in
if len <? HDR_MIN + config_len then io_diag io DCfgOverrun ;;; drv_free buf ;;; mret 2
else
let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
let payload := skipn (Z.to_nat (6 + config_len)) content in
let cfg := if 0 <? config_len then znth content 2 else 0 in
alloc_init bitmap ;;;
status <- run cfg payload ;;
status' <- (if count_allocs then
n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
else mret status) ;;
drv_free buf ;;;
mret status'
end.

Definition exit_model (code : Z) : M St Empty_set :=
io_exit io ;;;
msys (NExit code) dec_exit.

End Driver.

Section IO_S.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition s_diag (d : diag_msg) : M St unit :=
match d with
| DUsage argv0 => stderr_fprintf (pieces_usage argv0)
| DCannotOpen p => stderr_fprintf (pieces_cannot_open p)
| DReadError p => stderr_fprintf (pieces_read_error p)
| DOom => stderr_fwrite (concat pieces_oom)
| DTooBig => stderr_fprintf pieces_too_big
| DShortHdr => stderr_fwrite (concat pieces_short_hdr)
| DCfgOverrun => stderr_fwrite (concat pieces_cfg_overrun)
end.
Definition s_emit (v : Z) : M St unit := stdout_vprintf get_so set_so (pieces_emit_d v).
Definition io_S : IOStyle St := mkIO St s_diag s_emit (stdout_exit_flush get_so set_so).
End IO_S.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc6I QJFf.
Import QCiC.Mq1 Qpj5.Mq1 QvDJ.Mq0.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetRun.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable emit : Z -> M St unit.
Variable fuzz : list Z -> M St Z.

Fixpoint run_calls (n : nat) (payload : list Z) (rc : Z) : M St Z :=
match n with
| O => mret rc
| S n' => rc' <- fuzz payload ;; emit rc' ;;; run_calls n' payload rc'
end.

Definition target_run (cfg : Z) (payload : list Z) : M St Z :=
let calls := Z.to_nat (1 + Z.land cfg 3) in
let payload_len := zlength payload in

t <- (if payload_len =? 0 then mret (Some None)
else r <- drv_malloc payload_len ;;
mret (match r with None => None | Some p => Some (Some p) end)) ;;
match t with
| None => mret 2
| Some owned =>
rc <- run_calls calls payload 0 ;;
(match owned with Some p => drv_free p | None => mret tt end) ;;;
mret (if rc =? 0 then 0 else 1)
end.

Section Spec.
Variable own : list ptr -> assn St.
Hypothesis Hdm : forall X n, 0 <= n ->
mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).

Definition fuzz_ok (payload : list Z) : Prop := forall X, mspec (own X) (fuzz payload) (fun _ => own X).

End Spec.

End TargetRun.
End Mq1.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.
Import ListNotations.
Open Scope Z_scope.

Lemma rz_size_bound' n : 16 <= rz_size n <= 2048.
Proof.
unfold rz_size. destruct (n <=? 48); [lia|]. destruct (n <=? 96); [lia|]. destruct (n <=? 448); [lia|].
destruct (n <=? 3968); [lia|]. destruct (n <=? 16128); [lia|]. destruct (n <=? 32256); [lia|]. destruct (n <=? 64512); lia.
Qed.

Section Cost.
Context {ptr : Type}.

Fixpoint acost_ok {A} (R : Z) (t : aprog ptr A) : Prop :=
match t with
| ARet _ => 0 <= R
| AUnr => 0 <= R
| AMalloc n k => mcost n <= R /\ forall r, acost_ok (R - mcost n) (k r)
| AFree _ k => acost_ok R k
end.

Lemma mcost_nonneg n : 0 <= mcost n.
Proof.
unfold mcost. destruct (from_primary n); [lia|]. unfold sec_cost, sec_map_size, kPage.
pose proof (round_up_ge (needed n + rz_size n) 4096 ltac:(lia)).
assert (0 <= needed n + rz_size n).
{ unfold needed. pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rz_size_bound' n). lia. }
pose proof (Z.div_pos (round_up (needed n + rz_size n) 4096 + 4096) 32768 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma acost_ok_nonneg {A} (t : aprog ptr A) : forall R, acost_ok R t -> 0 <= R.
Proof.
induction t as [a| |n k IH|p k IH]; intros R H; cbn in H; try lia.
- destruct H as [Hn _]. pose proof (mcost_nonneg n). lia.
- exact (IH R H).
Qed.

Lemma acost_ok_mono {A} (t : aprog ptr A) : forall R R', acost_ok R t -> R <= R' -> acost_ok R' t.
Proof.
induction t as [a| |n k IH|p k IH]; intros R R' H HR; cbn in *; try lia.
- destruct H as [Hn Hk]. split; [lia|]. intros r. eapply IH; [apply Hk| lia].
- eapply IH; [exact H| exact HR].
Qed.

Lemma acost_ok_apbind {A B} (t : aprog ptr A) (f : A -> aprog ptr B) : forall R1 R2,
acost_ok R1 t -> 0 <= R2 -> (forall a, acost_ok R2 (f a)) -> acost_ok (R1 + R2) (apbind t f).
Proof.
induction t as [a| |n k IH|p k IH]; intros R1 R2 H HR2 Hf; cbn in *.
- eapply acost_ok_mono; [apply Hf| lia].
- lia.
- destruct H as [Hn Hk]. split; [lia|].
intros r. replace (R1 + R2 - mcost n) with ((R1 - mcost n) + R2) by lia. apply IH; [apply Hk| exact HR2| exact Hf].
- apply IH; assumption.
Qed.

Definition mcost_ok {St A} (R : Z) (m : AM ptr St A) : Prop := forall s, acost_ok R (m s).

Lemma mcost_ok_mono {St A} (m : AM ptr St A) R R' : mcost_ok R m -> R <= R' -> mcost_ok R' m.
Proof. intros H HR s. eapply acost_ok_mono; [apply H| exact HR]. Qed.

Lemma mcost_ok_aret {St A} (a : A) : mcost_ok (St:=St) 0 (aret a).
Proof. intros s. cbn. lia. Qed.

Lemma mcost_ok_aget {St} : mcost_ok (St:=St) 0 aget.
Proof. intros s. cbn. lia. Qed.

Lemma mcost_ok_aput {St} (s1 : St) : mcost_ok 0 (aput s1).
Proof. intros s. cbn. lia. Qed.

Lemma mcost_ok_aupd {St} (f : St -> St) : mcost_ok 0 (aupd f).
Proof. intros s. cbn. lia. Qed.

Lemma mcost_ok_aassert {St} (b : bool) : mcost_ok (St:=St) 0 (aassert b).
Proof. intros s. unfold aassert. destruct b; cbn; lia. Qed.

Lemma mcost_ok_awhen {St} (b : bool) (m : AM ptr St unit) R : mcost_ok R m -> mcost_ok R (awhen b m).
Proof. intros H s. unfold awhen. destruct b; [apply H|]. cbn. pose proof (acost_ok_nonneg _ _ (H s)). lia. Qed.

Lemma mcost_ok_amalloc {St} (n : Z) : mcost_ok (St:=St) (mcost n) (amalloc n).
Proof. intros s. cbn. split; [lia|]. intros r. lia. Qed.

Lemma mcost_ok_acalloc {St} (m n : Z) : mcost_ok (St:=St) (mcost (m * n)) (acalloc m n).
Proof.
intros s. unfold acalloc. destruct (QCiC.Mq0.calloc_overflows m n); [| apply mcost_ok_amalloc].
cbn. apply mcost_nonneg.
Qed.

Lemma mcost_ok_afree {St} (p : ptr) : mcost_ok (St:=St) 0 (afree p).
Proof. intros s. cbn. lia. Qed.

Lemma mcost_ok_abind {St A B} (m : AM ptr St A) (f : A -> AM ptr St B) R1 R2 :
mcost_ok R1 m -> 0 <= R2 -> (forall a, mcost_ok R2 (f a)) -> mcost_ok (R1 + R2) (abind m f).
Proof. intros Hm HR2 Hf s. unfold abind. apply acost_ok_apbind; [apply Hm| exact HR2|]. intros [a s']. apply Hf. Qed.

Lemma mcost_ok_abind0 {St A B} (m : AM ptr St A) (f : A -> AM ptr St B) R :
mcost_ok 0 m -> 0 <= R -> (forall a, mcost_ok R (f a)) -> mcost_ok R (abind m f).
Proof. intros Hm HR Hf. replace R with (0 + R) by lia. apply mcost_ok_abind; assumption. Qed.

Lemma mcost_ok_aloop {St X Rt} (body : X -> AM ptr St (X + Rt)) :
(forall x, mcost_ok 0 (body x)) -> forall fuel x, mcost_ok 0 (aloop fuel body x).
Proof.
intros Hb fuel. induction fuel as [|fuel IH]; intros x s; cbn [aloop].
- cbn. lia.
- apply (mcost_ok_abind0 (body x)); [apply Hb| lia|]. intros [x'|r]; [apply IH| apply mcost_ok_aret].
Qed.

End Cost.

Lemma mcost_ok_aret_le {ptr St A} (a : A) R : 0 <= R -> mcost_ok (ptr:=ptr) (St:=St) R (aret a).
Proof. intros H s. cbn. exact H. Qed.
Lemma mcost_ok_aunr_le {ptr St A} R : 0 <= R -> mcost_ok (ptr:=ptr) (St:=St) R (aunr (A:=A)).
Proof. intros H s. cbn. exact H. Qed.
Lemma mcost_ok_amalloc_le {ptr St} (n : Z) R : mcost n <= R -> mcost_ok (ptr:=ptr) (St:=St) R (amalloc n).
Proof. intros H. eapply mcost_ok_mono; [apply mcost_ok_amalloc| exact H]. Qed.
Lemma mcost_ok_acalloc_le {ptr St} (m n : Z) R : mcost (m * n) <= R -> mcost_ok (ptr:=ptr) (St:=St) R (acalloc m n).
Proof. intros H. eapply mcost_ok_mono; [apply mcost_ok_acalloc| exact H]. Qed.
Lemma mcost_ok_zero_le {ptr St A} (m : AM ptr St A) R : mcost_ok 0 m -> 0 <= R -> mcost_ok R m.
Proof. intros H HR. eapply mcost_ok_mono; [exact H| exact HR]. Qed.

Lemma mcost_primary n : from_primary n = true -> mcost n = 0.
Proof. intros H. unfold mcost. rewrite H. reflexivity. Qed.

Create HintDb cost0.

Ltac cost_head t := lazymatch t with ?f _ => cost_head f | _ => t end.

Ltac cost0_step :=
lazymatch goal with
| |- mcost_ok _ (aret _) => apply mcost_ok_aret_le; lia
| |- mcost_ok _ aunr => apply mcost_ok_aunr_le; lia
| |- mcost_ok _ (@aunr _ _ _) => apply mcost_ok_aunr_le; lia
| |- mcost_ok _ aget => apply mcost_ok_zero_le; [apply mcost_ok_aget| lia]
| |- mcost_ok _ (aput _) => apply mcost_ok_zero_le; [apply mcost_ok_aput| lia]
| |- mcost_ok _ (aupd _) => apply mcost_ok_zero_le; [apply mcost_ok_aupd| lia]
| |- mcost_ok _ (aassert _) => apply mcost_ok_zero_le; [apply mcost_ok_aassert| lia]
| |- mcost_ok _ (afree _) => apply mcost_ok_zero_le; [apply mcost_ok_afree| lia]
| |- mcost_ok _ (awhen _ _) => apply mcost_ok_awhen
| |- mcost_ok _ (amalloc _) => apply mcost_ok_amalloc_le; rewrite ?mcost_primary by reflexivity; lia
| |- mcost_ok _ (acalloc _ _) => apply mcost_ok_acalloc_le; rewrite ?mcost_primary by reflexivity; lia
| |- mcost_ok _ (abind _ _) => apply mcost_ok_abind0; [| lia| intros ?; cbn beta]
| |- mcost_ok _ (aloop _ _ _) => apply mcost_ok_zero_le; [apply mcost_ok_aloop; intros ?; cbn beta| lia]
| |- mcost_ok _ (match ?x with _ => _ end) => destruct x
| |- mcost_ok _ ((fun _ => _) _) => cbn beta
| |- mcost_ok _ ?m => first [ solve [auto 2 with cost0] | let h := cost_head m in unfold h ]
end.

Ltac cost0 := repeat cost0_step.
