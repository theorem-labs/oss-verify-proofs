(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBOS.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition SCR : Z := 26624.
Definition CSK : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Section Call.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Definition op : Z := fb + 40.
Definition ec : Z := fb + 8.
Definition vis : Z := fb + 432.
Definition ois : Z := fb + 440.
Definition pre : Prop :=
hi_heap HI (PM.parser_own s0 ++ LBX) cr0 M0 (m_vmmaps model0) /\ PMSP.model_ok model0 /\ K [] /\ PMSP.entry AD L R0 M0 S r 7
/\ PMSP.frame_ok AD L S fb /\ PMSP.args3 AD R0 fb s0 /\ PMSP.run_pre RSEGS AD M0 fb s0 str sm0 e0 /\ incl (PM.vs_own str) LBX /\ PM.inv s0
/\ PMSP.ec_at RSEGS M0 (PMSP.o_ec AD fb) 0 cat /\ PM.unread (PM.p_src s0) sm0 < 2 ^ 26 /\ PMSP.credit_le (PM.pot_parser L s0) cr0.
Definition kont : Prop :=
forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R0 R' ->
PMSP.run_post RSEGS AD (fun _ => PMSP.prog_value) R' M' fb s0 s' str sm0 sm' e0 e' cat ->
L5C.hpres L LBX S (PMSP.pm_scr 7) (PMSP.W_run AD fb) M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_parser L s0) (PM.pot_parser L s') ->
model_but_vm model0 model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k CSK -> getr R (reg k) = getr R0 (reg k).
Definition regs_at (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 112) /\ getr R (reg 8) = Z_to_bv 64 op /\ getr R (reg 9) = Z_to_bv 64 ec
/\ getr R (reg 18) = Z_to_bv 64 vis /\ kept0 R.
Definition saves (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
/\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
/\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
Definition mem_ok (M : word -> option byte) : Prop :=
PMK.ek L LBX S SCR (PMSP.W_run AD fb) M0 M /\ PMK.dk L LBX S SCR M0 M /\ L5C.stk (hl_sptop L) M S SCR.
Definition world (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (e : bool) (cr : credit) : Prop :=
PMSP.run_pre RSEGS AD M fb s str sm e /\ hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) /\ model_but_vm model0 model
/\ PMSP.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ (e0 = true -> e = true)
/\ PMSP.credit_keep cr0 cr (PM.pot_parser L s0) (PM.pot_parser L s).
Definition sd (src : PM.srcst) : PM.pst :=
PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0 + 1) src (PM.p_tb s0) (PM.p_tg s0) (PM.p_b s0) (PM.p_k s0) (PM.p_stk s0).
Definition spush (src : PM.srcst) (b k : Z) (c : PM.pstate) : PM.pst :=
PM.PST (PM.p_more s0) (PM.p_done s0) (PM.p_depth s0 + 1) src (PM.p_tb s0) (PM.p_tg s0) b k (PM.p_stk s0 ++ [c]).
End Call.
End PMBOS.
