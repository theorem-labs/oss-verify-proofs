(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1ka X1kd X1k9 X1l0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd X1ei.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1oc X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.
Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
end).
Ltac zst := zstep; fix_lit_store.

Definition S_OOM : Z := 0x103d2.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x10612.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x10416.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b rsegs S_OOM (zbytes s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b rsegs S_SHORT (zbytes s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b rsegs S_OVER (zbytes s_over) = true. Proof. vm_compute. reflexivity. Qed.

Lemma rodata_bytes : forall m A (s : list Z),
mem_inv rsegs m -> ro_bytes_b rsegs A (zbytes s) = true -> 0x10000 <= A -> A + zlength s <= 0x6e000 ->
bytes_at rsegs m A (zbytes s).
Proof.
intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| rewrite zbytes_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound rsegs); exact RO].
Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
implM rsegs (f s) s Q ms -> implM rsegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
Lemma implM_mret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
implM rsegs (f a) s Q ms -> implM rsegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.

Section B.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis EARGV : argv = [arg0; arg1].
Hypothesis HT : 0 < TID < 4194304.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FKP : rfree_keeps_ptr_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.

Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).
Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
Notation FRAME' mm := (exists pad, MFRAME sp0 argv mm pad S7 S6 S5 S4).
Ltac hyps := first [exact VSP | exact HCEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact RHF | exact MALLOC | exact FREE | exact FKP | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
RHEAP s [(bufp, A, cap)] mm /\ ps_fa s = (0, 0) /\ ps_so s = stdout_init /\ A = X1r3.ptr_addr s bufp
/\ rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
/\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
(GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm).

Definition RDHEAD (pc len cap : Z) : Prop := (pc = 0x1bd14 /\ len < cap) \/ (pc = 0x1bd1c /\ len = cap).

Definition RDINV (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
exists (pc : Z) (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
(A : Z) (DATA junk : list byte) (errv : word),
ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
/\ RDHEAD pc (zlength (rd_content st)) (rd_cap st)
/\ rd_content st = map bv_unsigned DATA
/\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk
/\ FRAME' mm /\ BASE' mm /\ ADP0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc /\ is_mkF F
/\ (exists stg, rw_cells rsegs mm RSTG [CB (Z.to_nat 65536) stg]).

Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
(A cap : Z) (DATA junk : list byte) (errv : word),
ms = RST 0x1bd7c x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
/\ content = map bv_unsigned DATA
/\ BUF mm s bufp A cap DATA junk
/\ FRAME' mm /\ BASE' mm /\ ADP0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc /\ is_mkF F.

Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
match r with
| inl st' => RDINV fd P1v st' s ms
| inr RdExit => rat_exit 2 s ms
| inr (RdDone b c) => RDBRK fd P1v b c s ms
end.

Definition rd_read_part (fd : Z) (path : list Z) (st1 : @rd_st bptr) : M PState (rd_st + rd_result) :=
let len := zlength (rd_content st1) in
let want := rd_cap st1 - len in
let cnt := if READ_CAP <? want then READ_CAP else want in
a <- msys (NRead fd RSTAGE_ubsan cnt) (dec_read RSTAGE_ubsan cnt) ;;
match a with
| RdErr _ => io_diag (DReadError path) ;;; mret (inr RdExit)
| RdData bs =>
if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
end.

Definition rd_grow_part (st : rd_st) : M PState (option rd_st) :=
if zlength (rd_content st) =? rd_cap st then
if MAX_INPUT <=? rd_cap st then io_diag DTooBig ;;; mret None
else
nb <- raw_malloc (rd_cap st * 2) ;;
match nb with
| None => io_diag DOom ;;; mret None
| Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
end
else mret (Some st).

#[using="Type"] Lemma read_loop_body_eq : forall fd path st,
read_loop_body io_diag raw_malloc raw_free RSTAGE_ubsan fd path st
= (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
let want := rd_cap st1 - zlength (rd_content st) in
let cnt := if READ_CAP <? want then READ_CAP else want in
a <- msys (NRead fd RSTAGE_ubsan cnt) (dec_read RSTAGE_ubsan cnt) ;;
match a with
| RdErr _ => io_diag (DReadError path) ;;; mret (inr RdExit)
| RdData bs =>
if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
end end).
Proof. intros. reflexivity. Qed.

#[using="VSP HCEIL HT RHF FPR FWX SWF"] Lemma fprintf_exit : forall (d : diag_msg) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
diag_args d mm a1v a2v (usp0 - 8388608) (usp0 - 128) ->
BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init -> frm0 fc ->
(forall ms', rat_exit 2 s ms' -> implM rsegs K s Q ms') ->
implM rsegs (s_diag d ;;; K) s Q
(GST 0x1bee8 x1 t0 t1 t2 x9 (Z_to_bv 64 0x3d110) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros DA BA HP SO FRM HK.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF.
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST.
unfold implM. iprefix. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
eapply implM_bind.
{ eapply (FPR d) with (lo := usp0 - 8388608) (canary := run_canary);
[exact FWX| exact SWF| apply stderr_wfile0_wfile; exact SE| reflexivity| rewrite unsigned_lit by lia; replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
| rewrite unsigned_lit by lia; exact ST
| rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
| apply (RHEAP_ssp _ _ _ HP)| exact MI| exact FRM]. }
cbv beta. intros [] st' ms' PO.
first [ sf_destruct 28%nat PO as u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 -> MUc WMc MI2 FRM2 FEQ ST2 SEW SSP2 -> | sf_fb; destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->) ].
ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
replace (ret_pc (Z_to_bv 64 0x1beec)) with (Z_to_bv 64 0x1beec) by (symmetry; rpc).
pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
assert (OUT2 : forall a, (0x10000 <= a < 0x6e000 /\ ~ (0x3d110 <= a < 0x3d110 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x3d110, 0x3d110 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
eapply implM_evt; [| intros ms'' H; apply HK; exact H].
zstep.
eapply (exit2_tail sp0 TID VSP HCEIL HT s LB).
- unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
- eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
- eapply RHF; [exact HP| exact MUc| exact WMc|].
constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. lia.
- rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
- apply stderr_wfile_file. exact SEW.
- exact MI2.
Qed.

#[using="VSP HCEIL HT RHF FWR TOW"] Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init ->
(forall ms', rat_exit 2 s ms' -> implM rsegs K s Q ms') ->
implM rsegs (s_diag DOom ;;; K) s Q
(GST 0x1bf0c x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 0x3d110) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros BA HP SO HK.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF.
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST.
unfold implM. iprefix. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
cbn [s_diag]. change (concat pieces_oom) with s_oom.
eapply implM_bind.
{ eapply (FWR) with (lo := usp0 - 8388608) (canary := run_canary) (s := s_oom);
[exact TOW| exact SE| rewrite unsigned_lit by (unfold S_OOM; lia); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
| apply str_range || (unfold s_oom; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]])
| unfold s_oom, zlength; cbn; lia| reflexivity| reflexivity| reflexivity
| rewrite unsigned_lit by lia; exact ST
| rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
| rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
| rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
| apply (RHEAP_ssp _ _ _ HP)| exact MI]. }
cbv beta. intros [] st' ms' PO.
first [ sf_destruct 24%nat PO as u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 -> MUc WMc MI2 ST2 SEW SSP2 -> | sf_fb; destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & SEW & SSP2 & ->) ].
ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
replace (ret_pc (Z_to_bv 64 0x1bf10)) with (Z_to_bv 64 0x1bf10) by (symmetry; rpc).
pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
assert (OUT2 : forall a, (0x10000 <= a < 0x6e000 /\ ~ (0x3d110 <= a < 0x3d110 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x3d110, 0x3d110 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
eapply implM_evt; [| intros ms'' H; apply HK; exact H].
eapply (exit2_tail sp0 TID VSP HCEIL HT s LB).
- unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. first [exact ST2 | replace (usp0 + -8388608) with (usp0 - 8388608) in ST2 by lia; exact ST2].
- eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
- eapply RHF; [exact HP| exact MUc| exact WMc|].
constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. lia.
- rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
- apply stderr_wfile0_file. exact SEW.
- exact MI2.
Qed.
End B.
