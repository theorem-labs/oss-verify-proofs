(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmSpecs PmSpecsS PmStep PmParKit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSLPD.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Definition pkont (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z)
(s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R R' -> PMSP.parse_post RSEGS AD M' fb s s' str sm sm' e e' ->
L5C.hpres L LBX sp (PMSP.pm_scr 10) (PMSP.W_run AD fb) M M' -> PMSP.credit_keep cr cr' (PM.pot_parser L s) PMSP.cr0 ->
model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition pctx (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z)
(s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ K [] /\ PMSP.entry AD L R M sp r 10 /\ PMSP.frame_ok AD L sp fb /\
PMSP.args3 AD R fb s /\ PMSP.run_pre RSEGS AD M fb s str sm e /\ incl (PM.vs_own str) LBX /\ PM.inv s /\ PMSP.ec_at RSEGS M (PMSP.o_ec AD fb) 0 cat /\
PM.unread (PM.p_src s) sm < 2 ^ 26 /\ PMSP.credit_le (PM.pot_parser L s) cr /\ pkont K R M model LBX cr sp r fb s str sm e.
Definition lslots (R : bvmap 5 word) (M1 : word -> option byte) (sp : Z) : Prop :=
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\
L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\
L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\
L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) /\
L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21))) /\
L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 22))) /\
L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (PMK.reg 23))) /\
L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (PMK.reg 24))) /\
L5.u64_at RSEGS M1 (sp - 88) (bv_unsigned (getr R (PMK.reg 25))) /\
L5.u64_at RSEGS M1 (sp - 96) (bv_unsigned (getr R (PMK.reg 26))) /\
L5.u64_at RSEGS M1 (sp - 104) (bv_unsigned (getr R (PMK.reg 27))).
Definition lrel (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb : Z)
(s : PM.pst) (sm : PM.strm) (e : bool)
(M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
PMSP.src_step (PM.p_src s) (PM.p_src s1) sm sm1 /\ (e = true -> e1 = true) /\
L5C.hpres L LBX sp 32768 (PMSP.W_run AD fb) M M1 /\ PMSP.credit_keep cr cr1 (PM.pot_parser L s) (PM.pot_parser L s1) /\
model_but_vm model model1 /\ hi_heap HI (PM.parser_own s1 ++ LBX) cr1 M1 (m_vmmaps model1) /\ lslots R M1 sp.
Definition lmem (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb cat : Z)
(s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool)
(M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
PMSP.run_pre RSEGS AD M1 fb s1 str sm1 e1 /\ PMSP.ec_at RSEGS M1 (fb + 8) 0 cat /\
lrel R M model LBX cr sp fb s sm e M1 model1 s1 sm1 e1 cr1.
Definition linv (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb cat : Z)
(s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool)
(R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit) : Prop :=
getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 128) /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) /\ getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 432) /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (fb + 64) /\ getr R1 (PMK.reg 20) = Z_to_bv 64 (10) /\ getr R1 (PMK.reg 21) = Z_to_bv 64 (79444) /\ getr R1 (PMK.reg 22) = Z_to_bv 64 (9) /\ getr R1 (PMK.reg 23) = Z_to_bv 64 (256) /\ getr R1 (PMK.reg 24) = Z_to_bv 64 (93) /\ getr R1 (PMK.reg 25) = Z_to_bv 64 (7) /\ getr R1 (PMK.reg 26) = Z_to_bv 64 (5) /\ getr R1 (PMK.reg 27) = Z_to_bv 64 (125) /\
getr R1 (PMK.reg 3) = getr R (PMK.reg 3) /\ getr R1 (PMK.reg 4) = getr R (PMK.reg 4) /\
PM.inv s1 /\ lmem R M model LBX cr sp fb cat s str sm e M1 model1 s1 sm1 e1 cr1.
Definition top_mode (s : PM.pst) : Z := PM.ps_mode (last (PM.p_stk s) PM.ps_root).
Definition lpG1 (m : Z) : Prop := m = 0 \/ m = 1 \/ m = 6 \/ m = 8 \/ m = 10.
Definition lpG2 (m : Z) : Prop := m = 2 \/ m = 4.
Definition lpG3 (m : Z) : Prop := m = 5 \/ m = 7.
Definition lpG4 (m : Z) : Prop := m = 3 \/ m = 9.
Lemma lp_split m : 0 <= m <= 10 -> lpG1 m \/ lpG2 m \/ lpG3 m \/ lpG4 m.
Proof. intros H. unfold lpG1, lpG2, lpG3, lpG4. lia. Qed.
Definition iter_ok (G : Z -> Prop) : Prop :=
forall (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z)
(s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
pctx K R M model LBX cr sp r fb cat s str sm e ->
forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (e1 : bool) (cr1 : credit),
linv R M model LBX cr sp fb cat s str sm e R1 M1 model1 s1 sm1 e1 cr1 -> G (top_mode s1) ->
(forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (s2 : PM.pst) (sm2 : PM.strm) (e2 : bool) (cr2 : credit),
linv R M model LBX cr sp fb cat s str sm e R2 M2 model2 s2 sm2 e2 cr2 -> PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu s1 sm1 ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x35b20 M2 model2) K) ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x35b20 M1 model1) K.
End WithHeap.
End PMSLPD.
