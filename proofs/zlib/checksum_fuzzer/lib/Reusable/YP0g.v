(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma SR_run_gen : forall n E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros n E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_run_stop : forall n E ss ss' why ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss' why. exact (SR_run_gen n E ss ss' (RS_stopped why)). Qed.
Lemma SR_run_running : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_run_gen n E ss ss' RS_running). Qed.
Lemma SR_run_ecall : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_run_gen n E ss ss' RS_ecall). Qed.
Lemma SR_run_to_gen : forall n stop E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros n stop E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_sym_branch : forall E ss ms model Q c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms ->
SR segs (mkCfg ms model) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
SR segs (mkCfg ms model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros E ss ms model Q c a b HS Ht Hf T HK.
apply (rz_branch segs E ss ms model T c a b HS).
- intros Hb HS'. exact (Ht Hb HS' T HK).
- intros Hb HS'. exact (Hf Hb HS' T HK).
Qed.
Lemma SR_st_ok_ret : forall (Q : config -> Prop) ms model,
Q (mkCfg ms model) -> SR segs (mkCfg ms model) Q.
Proof. intros Q ms model HQ. apply SR_ret. exact HQ. Qed.
Lemma SR_pend_silent : forall c (I : Type) (i0 : I) (nx : I -> config) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, SR segs (nx i) Q) ->
SR segs c Q.
Proof. intros c I i0 nx Q Hn Hk. apply (SR_node segs c I nx i0 Q Hn Hk). Qed.
Lemma SR_of_rz : forall c (P : config -> Prop) Q,
(forall T, (forall c', P c' -> realizes segs c' T) -> realizes segs c T) ->
(forall c', P c' -> SR segs c' Q) ->
SR segs c Q.
Proof. intros c P Q Hnode Hk T HK. apply Hnode. intros c' HP. exact (Hk c' HP T HK). Qed.
Lemma t_alt2_idem : forall T, t_eq (t_alt2 T T) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_idem3 : forall T, t_eq (t_alt2 T (t_alt2 T T)) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.
Lemma SR_of_rz_alt2 : forall c (PA PB : config -> Prop) Q,
(forall A B, (forall c', PA c' -> realizes segs c' A) -> (forall c', PB c' -> realizes segs c' B) ->
realizes segs c (t_alt2 A B)) ->
(forall c', PA c' -> SR segs c' Q) ->
(forall c', PB c' -> SR segs c' Q) ->
SR segs c Q.
Proof.
intros c PA PB Q Hnode HA HB T HK.
apply (rz_conseq segs c (t_alt2 T T)); [|apply t_alt2_idem].
apply Hnode; intros c' Hc'; [exact (HA c' Hc' T HK) | exact (HB c' Hc' T HK)].
Qed.
Lemma SR_mmap_rw : forall regs pc mem rom model Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
(forall a, grant_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true ->
SR segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
(apply_zeros mem [(a, page_round_up (getr regs 11))]) rom)
(mmap_model a (page_round_up (getr regs 11)) model)) Q) ->
(exists a, grant_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true) ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model Q Hh Hlz Hno H1 H2 H3 H4 H5 HA HB Hex T HK.
apply (rz_mmap_rw_ok segs regs pc mem rom model T Hh Hlz Hno H1 H2 H3 H4 H5); [|exact Hex].
intros a Ha. exact (HB a Ha T HK).
Qed.
Lemma SR_mmap_none : forall regs pc mem rom model Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
(forall a, place_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true ->
SR segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
(apply_unmaps mem [(a, page_round_up (getr regs 11))]) rom)
(mmap_none_model a (page_round_up (getr regs 11)) model)) Q) ->
(exists a, place_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true) ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model Q Hh Hlz Hno H1 H2 H3 H4 H5 HA HB Hex T HK.
apply (rz_mmap_none_ok segs regs pc mem rom model T Hh Hlz Hno H1 H2 H3 H4 H5); [|exact Hex].
intros a Ha. exact (HB a Ha T HK).
Qed.
Lemma SR_mmap_fixed_none : forall regs pc mem rom model Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z -> (0 < bv_unsigned (getr regs 10))%Z ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model))%Z ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
(forall e, In e mmap_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
SR segs (mkCfg (mkst (regupd regs 10 (getr regs 10)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_model (getr regs 10) (page_round_up (getr regs 11)) model)) Q ->
(forall e, In e mmap_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_destroyed_model (getr regs 10) (page_round_up (getr regs 11)) model)) Q) ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model Q Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont HA HB HC T HK.
apply (rz_mmap_fixed_none_ok segs regs pc mem rom model T Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont).
exact (HB T HK).
Qed.
Lemma SR_mprotect_rw : forall regs pc mem rom model Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64)%Z ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
mprotect_budget_ok model (getr regs 10) (page_round_up (getr regs 11)) = true ->
(forall e, In e mprotect_errnos ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) Q) ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_zeros mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model)) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model Q Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma Hbud HA HB T HK.
apply (rz_mprotect_rw_ok segs regs pc mem rom model T Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma Hbud).
exact (HB T HK).
Qed.
Lemma SR_munmap_exact : forall regs pc mem rom model Q,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 215%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(munmap_model (getr regs 10) (page_round_up (getr regs 11)) model)) Q ->
SR segs (mkCfg (pend_at regs pc mem rom) model) Q.
Proof.
intros regs pc mem rom model Q Hh Hlz Hno Hal Hlen Hnw Hhas HK0 T HK.
apply (rz_munmap_exact segs regs pc mem rom model T Hh Hlz Hno Hal Hlen Hnw Hhas). exact (HK0 T HK).
Qed.
End d.
Ltac sr_run_with tblok HS :=
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
eapply (SR_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (SR_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (SR_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sr_run_to_with tblok HS stop :=
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
eapply (SR_run_to_gen segs tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; cbv beta iota; intros ms' HS HF ];
[assumption|assumption|];
lazymatch st with
| RS_ecall => sym_transport_ecall segs E ss ss' ms' HS HF
| _ => sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sr_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SR_sym_branch segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sr_branch: state is not stuck at a branch:" why
end
end
end.
