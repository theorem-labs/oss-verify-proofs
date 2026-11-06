(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YN06 YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0k YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Definition sym_runFN (n : N) (ss : sstate) : sstate * run_status :=
sym_runF segs tbl (N.to_nat n) ss.
Definition sym_run_toFN (n : N) (stop : Z) (ss : sstate) : sstate * run_status :=
sym_run_toF segs tbl (N.to_nat n) stop ss.
Lemma msteps_runF_gen : forall n E ss ss' st ms,
st_okF segs E ss ms ->
sym_runFN n ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_okF_ecall segs E ss' ms' | _ => st_okF segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ss' st ms HS Hrun.
destruct (sym_runF_sound segs tbl tbl_ok _ E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
exists ms'. auto.
Qed.
Lemma msteps_runF_to_gen : forall n stop E ss ss' st ms,
st_okF segs E ss ms ->
sym_run_toFN n stop ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_okF_ecall segs E ss' ms' | _ => st_okF segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ss' st ms HS Hrun.
destruct (sym_run_toF_sound segs tbl tbl_ok _ stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
exists ms'. auto.
Qed.
Lemma rz_runF_gen : forall n E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_runFN n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_okF_ecall segs E ss' ms' | _ => st_okF segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros n E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (msteps_runF_gen n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (rz_msteps segs ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.

Lemma rz_branchF : forall E ss ms model T c a b,
st_okF segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_okF segs E (add_cond ss (mkAC c a b)) ms ->
realizes segs (mkCfg ms model) T) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_okF segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
realizes segs (mkCfg ms model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model T c a b HS Ht Hf.
apply (st_okF_branch segs E ss ms _ c a b HS); intros Hb HS'; [exact (Ht Hb HS') | exact (Hf Hb HS')].
Qed.
Lemma SR_runF_gen : forall n E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_runFN n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_okF_ecall segs E ss' ms' | _ => st_okF segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros n E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_runF_gen n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_runF_stop : forall n E ss ss' why ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_runFN n ss = (ss', RS_stopped why) ->
(forall ms', st_okF segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss' why. exact (SR_runF_gen n E ss ss' (RS_stopped why)). Qed.
Lemma SR_runF_running : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_runFN n ss = (ss', RS_running) ->
(forall ms', st_okF segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_runF_gen n E ss ss' RS_running). Qed.
Lemma SR_runF_ecall : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_runFN n ss = (ss', RS_ecall) ->
(forall ms', st_okF_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_runF_gen n E ss ss' RS_ecall). Qed.
Lemma SR_runF_to_gen : forall n stop E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_okF segs E ss ms ->
sym_run_toFN n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_okF_ecall segs E ss' ms' | _ => st_okF segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros n stop E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_runF_to_gen n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_sym_branchF : forall E ss ms model Q c a b,
st_okF segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_okF segs E (add_cond ss (mkAC c a b)) ms ->
SR segs (mkCfg ms model) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_okF segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
SR segs (mkCfg ms model) Q) ->
SR segs (mkCfg ms model) Q.
Proof.
intros E ss ms model Q c a b HS Ht Hf T HK.
apply (rz_branchF E ss ms model T c a b HS).
- intros Hb HS'. exact (Ht Hb HS' T HK).
- intros Hb HS'. exact (Hf Hb HS' T HK).
Qed.
Lemma st_okF_reg : forall E ss ms r,
st_okF segs E ss ms -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros E ss ms r HS. apply (st_okF_regs_ok segs E ss ms HS). Qed.
Lemma ew_fregs_low : forall E0 k fregs0 i, (i < k)%nat -> ew (ew_fregs E0 k fregs0) i = ew E0 i.
Proof.
intros E0 k fregs0 i Hi. cbn [ew ew_fregs].
destruct (Nat.leb_spec k i); [lia|]. reflexivity.
Qed.
Lemma ew_fregs_at : forall E0 k fregs0 (r : reg),
ew (ew_fregs E0 k fregs0) (k + ridx r)%nat = reg_get fregs0 r.
Proof.
intros E0 k fregs0 r. pose proof (fregs_ok_atoms E0 k fregs0 r) as H.
rewrite sfr_get_atoms in H. cbn [sv_denot] in H. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H.
symmetry. exact H.
Qed.
Lemma st_okF_fregs_kept : forall E ss ms k fregs0 (L : list reg),
st_okF segs E ss ms ->
(forall r : reg, ew E (k + ridx r)%nat = reg_get fregs0 r) ->
forallb (fun r : reg => sv_eqb (sfr_get (ss_fregs ss) r) (SOff (k + ridx r) 0)) L = true ->
forall r, In r L -> reg_get (ms_fregs ms) r = reg_get fregs0 r.
Proof.
intros E ss ms k fregs0 L HS HE HL r Hr.
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_okF_freg segs E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, HE.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma st_okF_regs_kept : forall E ss ms regs0 (L : list reg),
st_okF segs E ss ms ->
(forall r : reg, In r L -> ew E (ridx r) = getr regs0 r) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (ridx r) 0)) L = true ->
forall r, In r L -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 L HS HE HL r Hr.
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_okF_reg E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, (HE r Hr).
apply Z_to_bv_bv_unsigned.
Qed.
Definition FCALLEE_SAVED : list reg := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition fregs_preserved (f f' : bvmap 5 word) : Prop :=
forall r, In r FCALLEE_SAVED -> reg_get f' r = reg_get f r.
Lemma frame_of_extend : forall E rs0 rs m0 m m',
skeleton rs0 = skeleton rs ->
frame_of E rs0 m0 m -> frame_of E rs m m' -> frame_of E rs0 m0 m'.
Proof. intros. eapply frame_of_trans; eassumption. Qed.
End d.
Ltac sym_whyF segs tbl ss :=
let r := eval vm_compute in (sym_stepF segs tbl ss) in
match r with
| SStop ?why => why
| SEcall _ => constr:(SR_unsupported)
| SRun _ => constr:(SR_unsupported)
end.
Ltac symF_cleanup HS HF :=
cbn [ms_mem mkst pend_at] in HF;
try clear HF;
try match type of HS with st_okF _ _ _ ?ms' =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with ms' => fail | _ => clear old end
end
end.
Ltac sr_runF_with tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runFN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runFN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (SR_runF_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
symF_cleanup HS HF
| RS_stopped ?why =>
eapply (SR_runF_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
symF_cleanup HS HF
| RS_running =>
eapply (SR_runF_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
symF_cleanup HS HF
end
end
end
end.
Ltac sr_runF_frame tblok HS HFR :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runFN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runFN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in let HFR' := fresh "HFR" in
eapply (SR_runF_gen segs tbl tblok FUEL E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; cbv beta iota; intros ms' HS HF ];
[assumption|assumption|];
lazymatch type of HFR with
| frame_of _ ?rs0 ?m0 _ =>
pose proof (frame_of_extend E rs0 (ss_mem ss) m0 (ms_mem ms) (ms_mem ms')
ltac:(vm_compute; reflexivity) HFR HF) as HFR';
clear HFR HF; rename HFR' into HFR;
try match type of HS with st_okF _ _ _ ?msn =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end
end
end
end
end.
Ltac sr_runF_to_with tblok HS stop :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toFN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toFN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (SR_runF_to_gen segs tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; cbv beta iota; intros ms' HS HF ];
[assumption|assumption|];
symF_cleanup HS HF
end
end
end.
Ltac sr_branchF_with tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SR_sym_branchF segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sr_branchF: state is not stuck at a branch:" why
end
end
end.
Ltac sym_runF_with tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runFN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runFN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (rz_runF_gen segs tbl tblok FUEL E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; cbv beta iota; intros ms' HS HF ];
[assumption|assumption|];
symF_cleanup HS HF
end
end
end.
Ltac sym_branchF_with tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (rz_branchF segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sym_branchF: state is not stuck at a branch:" why
end
end
end.
