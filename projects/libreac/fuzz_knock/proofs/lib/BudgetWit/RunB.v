(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP03.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP04.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN35.v, with its module paths and addresses changed. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3v.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YP0n.v, YP03.v, YP04.v, YN35.v and YN3v.v: their realizes lemmas and tactics that the driver's usage path uses, restated over BudgetWit.Rzb.rzb. *)

(** * The run, branch and exit lemmas of [YP0n], [YP03], [YP04] and [YN35] over [rzb]

    Each lemma below mirrors the released lemma of the same part: its name is
    the released name with [rz_] or [realizes_] written [rzb_] ([_b] appended
    when the name has neither), its statement is the released statement with
    [realizes] written [rzb], and its proof is the released proof with the
    mirrored lemmas renamed.  Where a released statement names a definition of
    its own section ([sym_runN], [exit_run_check], [run_to_check]) the mirror
    passes that definition its section arguments ([segs tbl]) explicitly; the
    term is the same.  Each part sits in a copy of its released section, so the
    section binders of each mirror are the released ones.  Where a released
    proof builds a syscall node, the mirror also gives [grant_ok] for it.

    Mirrored:
    - [YP0n]: [rz_chk1_silent], [rz_ret_only_copyins_silent], [rz_exit_at],
      [rz_exit_small], [rz_set_tid_first] (its grant is [grant_ok_no] at 96,
      set_tid_address).
    - [YP03]: [rz_run_gen], [rz_run_stop], [rz_run_running], [rz_run_ecall],
      [rz_run_to_gen], [rz_branch], [rz_sym_exit].
    - [YP04]: [rz_run_to_stop], [rz_run_to_running], [rz_run_to_ecall].
    - [YN35]: [realizes_exit_by_run], [realizes_run_to], [src0_exit],
      [src0_exit_to_flush].

    Statement changes: [rzb_chk1_silent] and [rzb_ret_only_copyins_silent]
    build a node at a syscall whose number their hypotheses do not fix, so they
    take [grant_ok segs (mkCfg (pend_at regs pc mem rom) model)] as one more
    hypothesis, right after their [check_syscall] hypothesis.

    Tactics copied under their released names, bodies changed only by the
    renames ([realizes] -> [rzb], mirrored lemma -> its mirror), so that a file
    importing this one after the released files gets them:
    - [YP03]: [sym_run_with], [sym_branch_with], [sym_exit_with], [sym_splice],
      [sym_splice1], [sym_splice0] (the last two call [sym_splice]).
    - [YP04]: [sym_run_to_with].
    - [YN3v]: [sym_splice_havoc], [sym_step_manual], [sym_run3_with],
      [sym_run3_to_with].
    - [YN35]: [src0_exit_tac].
    The other tactics of these files name no mirrored lemma and match no
    [realizes] goal, directly or through a tactic they call, and stay in use as
    released.  Each part first imports the modules of its released file in the
    released order, so that the names in each proof and each tactic body
    resolve as in the released file. *)

(** ** [YP0n] *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Place Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit Require Import Rzb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.

Section f.
Context {AM : AllocMode}.
Context {fx : FPState}.
Section g.
Variable segs : list Segment.
Lemma rzb_chk1_silent : forall regs pc mem rom model eff m' T,
m_halted model = None -> m_vm_lazy model = [] ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= CheckOk m' [] ->
grant_ok segs (mkCfg (pend_at regs pc mem rom) model) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model
= CheckOk m2 evs2 -> eff2 = eff /\ m2 = m' /\ evs2 = []) ->
rzb segs (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4)
(effmem mem eff) rom) m') T ->
rzb segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model eff m' T Hh Hlz Hok Hg Hh' Hlz' Huniq Hc.
eapply rzb_silent1.
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) unit tt
(fun _ => eff) (fun _ => m') (fun _ => []) Hh eq_refl
(fun _ => Hok) (fun _ => Hh') (fun _ => Hlz')).
+ intros eff2 m2 evs2 H2. exists tt. apply Huniq. exact H2.
+ intros []. apply nonspurious_of_unique. intros eff2 m2 evs2 Hs2.
apply check_syscall_ok_iff in Hs2. apply Huniq in Hs2 as (-> & _ & _). reflexivity.
- exact Hg.
- cbn. rewrite adv_pend. exact Hc.
Qed.
Lemma rzb_ret_only_copyins_silent : forall regs pc mem rom model reads r m' T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' []) ->
grant_ok segs (mkCfg (pend_at regs pc mem rom) model) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
rzb segs (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
rzb segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model reads r m' T Hh Hlz Hchk Hg Hh' Hlz' Hc.
apply (rzb_chk1_silent regs pc mem rom model (with_copyins reads (mkEffect r [] [])) m' T Hh Hlz).
- rewrite Hchk. apply check_ret_only_copyins_refl.
- exact Hg.
- exact Hh'.
- exact Hlz'.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_copyins_ok_iff. exact H2.
- cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. exact Hc.
Qed.
Lemma rzb_exit_at : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
rzb segs (mkCfg (pend_at regs pc mem rom) model)
(t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model Hh Hlz Hx8.
rewrite <- (pend_gpr0 regs pc mem rom).
apply (rzb_exit segs (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl Hx8).
Qed.
Lemma rzb_exit_small : forall regs pc mem rom model (c : word),
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
getr regs 10 = c -> (bv_unsigned c < 256)%Z ->
rzb segs (mkCfg (pend_at regs pc mem rom) model) (t_exit c (m_fs model)).
Proof.
intros regs pc mem rom model c Hh Hlz Hx8 Hc Hsmall.
rewrite <- (land_255_small c Hsmall), <- Hc. apply rzb_exit_at; assumption.
Qed.
Lemma rzb_set_tid_first : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 96%Z ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
rzb segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom)
(with_tid tid model)) T) ->
rzb segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model T Hh Hlz Hno Htid Hc.
pose (I := {tid : word | (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z}).
assert (H1 : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z).
{ rewrite PID_MAX_ENVELOPE_val. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
eapply (rzb_silent_allI segs (mkCfg (pend_at regs pc mem rom) model) I _ (exist _ (Z_to_bv 64 1) H1)).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) I (exist _ (Z_to_bv 64 1) H1)
(fun i => mkEffect (proj1_sig i) [] [])
(fun i => with_tid (proj1_sig i) model)
(fun _ => []) Hh eq_refl).
+ intros [tid Ht]. cbn [proj1_sig]. rewrite chk96 by exact Hno.
unfold check_set_tid_address. rewrite Htid.
rewrite (proj2 (Z.ltb_lt _ _) (proj1 Ht)), (proj2 (Z.ltb_lt _ _) (proj2 Ht)).
reflexivity.
+ intros [tid Ht]. cbn. exact Hh.
+ intros [tid Ht]. cbn. exact Hlz.
+ intros [r ws zs us cs ci] m' evs Hk. rewrite chk96 in Hk by exact Hno.
unfold check_set_tid_address in Hk. rewrite Htid in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned r)%Z) eqn:E1; [|discriminate].
destruct ((bv_unsigned r <? PID_MAX_ENVELOPE)%Z) eqn:E2; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
exists (exist _ r (conj E1 E2)). cbn [proj1_sig]. auto.
+ exact (fun _ => mcfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- exact (grant_ok_no segs (pend_at regs pc mem rom) model (getr regs 17) 96%Z
(pend_svc regs pc mem rom) Hno eq_refl).
- intros [tid Ht]. cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret].
rewrite effmem_ret_only. apply Hc. exact Ht.
Qed.
End g.
End f.

(** ** [YP03] *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP03.
Open Scope bv_scope.
Open Scope Z_scope.

Section e.
Context {AM : AllocMode}.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma rzb_run_gen : forall n E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof.
intros n E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_sound segs tbl tbl_ok _ E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (rzb_msteps segs ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma rzb_run_stop : forall n E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n E ss ss' why. exact (rzb_run_gen n E ss ss' (RS_stopped why)). Qed.
Lemma rzb_run_running : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n E ss ss'. exact (rzb_run_gen n E ss ss' RS_running). Qed.
Lemma rzb_run_ecall : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n E ss ss'. exact (rzb_run_gen n E ss ss' RS_ecall). Qed.
Lemma rzb_run_to_gen : forall n stop E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof.
intros n stop E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_to_sound segs tbl tbl_ok _ stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (rzb_msteps segs ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma rzb_branch : forall E ss ms model T c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms ->
rzb segs (mkCfg ms model) T) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
rzb segs (mkCfg ms model) T) ->
rzb segs (mkCfg ms model) T.
Proof.
intros E ss ms model T c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; assumption.
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; assumption.
Qed.
Lemma rzb_sym_exit : forall E ss ms model (code : Z),
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
is_exit_no (sv_denot E (sr_get (ss_regs ss) 17)) ->
sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 code -> 0 <= code < 256 ->
rzb segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros E ss ms model code Hh Hlz HS Hrv Hno Ha0 Hc.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
apply rzb_exit_small.
- exact Hh.
- exact Hlz.
- rewrite (Hregs 17%bv). exact Hno.
- rewrite (Hregs 10%bv). exact Ha0.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small; lia.
Qed.
End e.

Ltac sym_run_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rzb_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rzb_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (rzb_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (rzb_branch segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sym_branch: state is not stuck at a branch:" why
end
end
end.
Ltac sym_exit_with HS :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms =>
lazymatch goal with |- rzb _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (rzb_sym_exit segs E ss ms model code);
[ assumption | assumption | exact HS | reflexivity
| first [left; reflexivity | right; reflexivity]
| reflexivity | lia ]
end
end.
Ltac sym_splice HS Hms k E' Hagree upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rzb_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
unshelve epose proof (st_ok_set_regs segs k E E' ss _ regs' _ pc' _ upd HS Hagree _ _ _ _ _);
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
|
|
| clear HS Hms;
match goal with Hn : st_ok _ _ (set_regs_pc _ _ _) _ |- _ => rename Hn into HS end;
sym_norm HS ]
end end.
Ltac sym_splice1 HS Hms k v upd :=
lazymatch type of HS with st_ok _ ?E _ _ =>
sym_splice HS Hms k (ewset E k v) (env_agree_ewset E k v) upd
end.
Ltac sym_splice0 HS Hms upd :=
lazymatch type of HS with st_ok _ ?E _ _ =>
sym_splice HS Hms 0%nat E (env_agree_refl 0%nat E) upd
end.

(** ** [YP04] *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP04.
Open Scope bv_scope.
Open Scope Z_scope.

Section e4.
Context {AM : AllocMode}.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma rzb_run_to_stop : forall n stop E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n stop E ss ss' why. exact (rzb_run_to_gen segs tbl tbl_ok n stop E ss ss' (RS_stopped why)). Qed.
Lemma rzb_run_to_running : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n stop E ss ss'. exact (rzb_run_to_gen segs tbl tbl_ok n stop E ss ss' RS_running). Qed.
Lemma rzb_run_to_ecall : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
rzb segs (mkCfg ms' model) T) ->
rzb segs (mkCfg ms model) T.
Proof. intros n stop E ss ss'. exact (rzb_run_to_gen segs tbl tbl_ok n stop E ss ss' RS_ecall). Qed.
End e4.

Ltac sym_run_to_with tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rzb_run_to_ecall segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rzb_run_to_stop segs tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (rzb_run_to_running segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.

(** ** [YN35] *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YH00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN35.
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Section b.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Theorem rzb_exit_by_run : forall E ss ms model code,
st_ok segs E ss ms ->
0 <= code < 256 ->
exit_run_check segs tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
rzb segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros E ss ms model code HS Hcode Hchk Hh Hlz. unfold exit_run_check in Hchk.
destruct (sym_runN segs tbl FUEL ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate.
destruct (sr_get (ss_regs ss') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct (sr_get (ss_regs ss') 10) as [c| | | | | | | | | |] eqn:H10; try discriminate.
destruct (ss_resv ss') eqn:Hrv; try discriminate.
apply andb_prop in Hchk as [Hno Hc]. apply Z.eqb_eq in Hc. subst c.
eapply (rzb_run_ecall segs tbl tbl_ok FUEL E ss ss' ms model _ Hh Hlz HS Hrun).
intros ms' HS' _.
apply (rzb_sym_exit segs E ss' ms' model code Hh Hlz HS' Hrv).
- rewrite H17. cbn [sv_denot]. apply orb_prop in Hno as [Hno|Hno]; apply Z.eqb_eq in Hno; subst no;
[left | right]; reflexivity.
- rewrite H10. reflexivity.
- exact Hcode.
Qed.
Theorem rzb_run_to : forall stop E ss ss1 ms model T,
st_ok segs E ss ms ->
run_to_check segs tbl stop ss = Some ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
(forall ms1, st_ok segs E ss1 ms1 ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
rzb segs (mkCfg ms1 model) T) ->
rzb segs (mkCfg ms model) T.
Proof.
intros stop E ss ss1 ms model T HS Hchk Hh Hlz K. unfold run_to_check in Hchk.
destruct (sym_run_toN segs tbl FUEL stop ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate.
destruct (ss_pc ss' =? stop); [|discriminate]. injection Hchk as ->.
exact (rzb_run_to_running segs tbl tbl_ok FUEL stop E ss ss1 ms model T Hh Hlz HS Hrun K).
Qed.
End b.
Theorem src0_exit_b : forall E ss ms model code,
st_ok src0segs E ss ms ->
0 <= code < 256 ->
exit_run_check src0segs src0tbl ss code = true ->
m_halted model = None -> m_vm_lazy model = [] ->
rzb src0segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof. exact (rzb_exit_by_run src0segs src0tbl src0tbl_ok). Qed.
Theorem src0_exit_to_flush_b : forall E ss ss1 ms model T,
st_ok src0segs E ss ms ->
run_to_check src0segs src0tbl SRC1_STDIO_WRITE ss = Some ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
(forall ms1, st_ok src0segs E ss1 ms1 ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
rzb src0segs (mkCfg ms1 model) T) ->
rzb src0segs (mkCfg ms model) T.
Proof. exact (rzb_run_to src0segs src0tbl src0tbl_ok SRC1_STDIO_WRITE). Qed.
End a.
Ltac src0_exit_tac HS :=
first
[ lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch goal with |- rzb _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (src0_exit_b E ss ms model code HS); [lia | vm_compute; reflexivity | assumption | assumption]
end end
| sym_run_with src0tbl_ok HS; sym_exit_with HS ].

(** ** [YN3v] tactics *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac sym_splice_havoc HS Hms k upd rl :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') ?mem' _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rzb_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' _ pc' (ms_mem ms) mem' (ss_mem ss) upd rl
HS _ _ _ _ _ _ _ _) as H;
[ vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| | |
| env_transport (havoc E k (map (getr regs') rl)) (env_agree_havoc E k (map (getr regs') rl));
clear HS Hms; rename H into HS; sym_norm HS ]
end end.
Ltac sym_step_manual HS Hstep upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hstep with _ = MachineOk (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rzb_msteps; [assumption | assumption | eapply msteps_one; [reflexivity | exact Hstep] | ];
rewrite Hshape in HS; clear Hshape;
let H := fresh "HS'" in
unshelve epose proof (st_ok_set_regs segs 1000%nat E E ss (ms_regs ms) regs' _ pc' (ms_mem ms) upd
HS (env_agree_refl 1000%nat E) _ _ _ _ _) as H;
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
| |
| clear HS Hstep; rename H into HS; sym_norm HS ]
end end.
Ltac sym_run3_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rzb_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rzb_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
| RS_running =>
eapply (rzb_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_run3_to_with tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (rzb_run_to_gen segs tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
lazymatch st with
| RS_ecall => change (st_ok_ecall segs E ss' ms') in HS; sym_transport3_ecall segs E ss ss' ms' HS HF
| _ => change (st_ok segs E ss' ms') in HS; sym_transport3 segs E ss ss' ms' HS HF
end
end
end
end.
