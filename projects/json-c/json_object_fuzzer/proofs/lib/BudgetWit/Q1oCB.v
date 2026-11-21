(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Q1oC.v: module Mq0 (the exit walk ref_exit, ref_exit_Z) and stdio_call_sound, over BudgetWit.QRjHB.realizes. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise m_channel_reader model = true on ref_exit_flush, the cases of ref_exit and stdio_call_sound). *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QsV0 QBxa QSpR Qm90 QMOs QFOH QWQV Q1SW QSPu QU2A Q8LG QZSc QsN4 QlKb Q39n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB QSpRB QWQVB.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Plain.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4 QBxa.Mq5 QSpR.Mq0.
Import Qm90 Qm90.Mq1 Qm90.Mq2 QMOs.Mq0 QMOs.Mq1 QFOH QWQV Q1SW QSPu QU2A Q8LG QZSc QsN4 QlKb Q39n.
Import ListNotations.
Open Scope bv_scope.
Import QRjHB QSpRB.Mq0 QSpRB.Mq2 QWQVB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Theorem ref_exit_clean :
forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
exit_common regs mem sp tp code tid wp2 rp2 ->
file_clean mem 0x650a0 wp1 rp1 ->
m_halted model = None -> m_vm_lazy model = [] ->
realizes RSEGS (mkCfg (mkst regs (0x4f0e4 : word) mem (seg_rom RSEGS)) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
destruct EC.

destruct ec_atx as [armed ATX]. pose proof (proj1 ec_glob) as Gnl0.
destruct (w1 armed regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

destruct (w2 regs1 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: lazymatch goal with |- realizes _ _ _ => idtac | _ => destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; first [store_ok_peel; exact ec_sok | rdn_solve] end.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3a regs2 (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
1:{ unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

eapply rz_exit_at; [exact F_4ee68 | exact E_4ee68 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

#[using="Type"] Theorem ref_exit_flush :
forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
exit_common regs mem sp tp code tid wp2 rp2 ->
stdout_pending mem wb wp bufp bufsz rp1 can pending ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
m_channel_reader model = true ->
realizes RSEGS (mkCfg (mkst regs (0x4f0e4 : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.

destruct ec_atx as [armed ATX]. pose proof (proj1 ec_glob) as Gnl0.
destruct (w1 armed regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

destruct (w2 regs1 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: lazymatch goal with |- realizes _ _ _ => idtac | _ => destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; first [store_ok_peel; exact ec_sok | rdn_solve] end.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct (w3b1 regs2 (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wb wp)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

replace (Z_to_bv 64 0x530a4) with (0x530a4 : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9)) sp code).
eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x650a0 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x530a4 : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; sok_stack ec_sok
| lia | lia
|  split; subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve
|  split; subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve
| lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
rewrite R3s0 in Q8.
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
eapply rz_exit_at; [exact F_4ee68 | exact E_4ee68 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

#[using="Type"] Theorem ref_exit : forall regs mem model code pending,
exit_pre regs mem model code pending ->
realizes RSEGS (mkCfg (mkst regs (0x4f0e4 : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
- eapply rz_conseq; [ | apply t_emit_nil_exit ].
eapply ref_exit_clean; eassumption.
- eapply ref_exit_flush; eassumption.
Qed.

#[using="Type"] Corollary ref_exit_Z : forall regs mem model code pending,
exit_pre regs mem model code pending ->
realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x4f0e4) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros. replace (Z_to_bv 64 0x4f0e4) with (0x4f0e4 : word) by (apply bv_eq; reflexivity).
apply ref_exit; assumption.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFeQ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qm90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qm90. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWQV.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1oC.
Import Q1oC QRjHB QWQVB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Theorem stdio_call_sound :
forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
(R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
(pending extra : list byte) (K : TSet),
let E := Env (vals_ev vals) ebs in
regs_ok E sr R -> know_ok RSEGS E M kn ->
stdio_call (length vals) sr kn = Some res ->
let wb := bv_unsigned (edenot E (sc_wb res)) in
let wp := bv_unsigned (edenot E (sc_wp res)) in
let s := edenot E (sc_s res) in
let l := edenot E (sc_l res) in
let su := bv_unsigned (edenot E (sc_sp res)) in
(wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS M s (length extra) = Some extra ->
fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
m_channel_reader model = true ->
m_halted model = None -> m_vm_lazy model = [] ->
K [] ->
(forall R' M',
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x53454) M (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
destruct (kread RSEGS kn (ELit 0) 0x63e88 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
destruct (kread RSEGS kn (ELit 0) 0x960e0 8) as [canv|] eqn:Hcan; [|discriminate].
destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
intros Hwbwp Hwpts Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.

apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
apply andb_prop in Hcond as [Hf0 Hf232].
apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.

assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
{ unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
{ intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
assert (R1 : getr R 1 = Z_to_bv 64 ret).
{ replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
assert (R10 : getr R 10 = Z_to_bv 64 f).
{ replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
rewrite H10. reflexivity. }
assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
{ replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R11 : getr R 11 = s).
{ replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R12 : getr R 12 = l).
{ replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
set (sp := edenot E (nth 2 sr (ELit 0))) in *.
pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
{ subst su. rewrite Hsqd. apply u64_lit. lia. }
pose proof (u64_range sp) as Hspr2. fold su in Hspr2.

destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
{ unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }

assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
{ intros off n A B C. apply flat_abs0; lia. }
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x63e88 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x960e0 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
fold wp in Hwpr. fold wb in Hwbr.

replace (Z_to_bv 64 0x53454) with (0x53454%bv : word) by (apply bv_eq; reflexivity).
eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
pending extra K).
- rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- lia.
- lia.
- exact Wst'.
- lia.
- lia.
- constructor.
+ rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rfd. cbn [edenot]. reflexivity.
+ exact Rbufp.
+ exact Rbufsz.
- split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
- apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
- exact Hfdlk.
- exact Hrdr.
- exact Hh.
- exact Hlz.
- lia.
- lia.
- exact Hlenp.
- exact Hlene.
- exact H30.
- exact Dw.
- exact Ds.
- exact Hsl.
- exact Rpend.
- exact Rextra.
- apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
- exact HKnil.
-
intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
apply HCONT.
+
assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
{ apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
- intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
(split; [lia|]);
lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
| replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
| replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
| replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
| replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
| replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
| replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
| replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
| replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
| replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
| replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
| replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
| replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
| replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
| replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
| replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
end.
- unfold SC_KEPT. cbn [In]. lia. }
apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
[ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
intros i Hi. rewrite length_sr_after_call_j in Hi.
destruct (Nat.eq_dec i 10) as [->|Hne].
* rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
* rewrite nth_sr_upd_other by lia. reflexivity.
+
destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
assert (HK3 : know_ok RSEGS E' M'
(kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
(ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
{ assert (Eqb : edenot E' qb = edenot E qb).
{ symmetry. apply (edenot_agree (length vals)); [exact Hag|].
apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
- unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
- intros x N1 N2 N3. apply Pagree.
+ unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
+ unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
+ unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
subst E'.
repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
* rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
* rewrite Xb. exact Pwpos.
* rewrite Xb. exact Pwbase.
Qed.
End FPGEN1.

