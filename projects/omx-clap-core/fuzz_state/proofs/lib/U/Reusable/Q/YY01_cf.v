From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YH00 YH03 YN0b_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW0e_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM06_cf YO0d_cf.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition regs_mallocG (res s2v : sv) : list sv :=
[SLit 0; junk 1; SOff aSP (-64); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aN 0; SOff aP 0; res; junk 11; junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
s2v; junk 19; junk 20; junk 21; junk 22; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition regs_callG : list sv :=
[SLit 0; junk 1; SOff aSP (-64); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aQ 0; SOff aP 0; junk 10; junk 11; junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
junk 18; junk 19; junk 20; junk 21; junk 22; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition atomsG : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 8256) (2^63 - 1) 4); (aTP, mkAF 4096 (2^63 - 1) 0); (aP, mkAF 4096 CEIL_MAX 4);
(aN, mkAF 0 (2^62 - 1) 0); (aNOLD, mkAF 0 (2^62 - 1) 0); (aQ, mkAF 4096 CEIL_MAX 4) ].
Definition ALIAS_OLD : sv * sv := (SAlu ALU_SUB (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0)) (SOff aP 0), SOff aNOLD 0).
Definition G6z : sstate :=
mkSS RA_MALLOC (regs_mallocG (SLit 0) (SOff aNOLD 0)) after_memR None (mkFacts atomsG [] []).
Definition G7 : sstate := fst (sym_run_toN src0segs src0tbl FUEL REALLOC_RET G6z).
Definition G6q (c : branch_cond) : sstate :=
mkSS RA_MALLOC (regs_mallocG (SOff aQ 0) (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0))) after_memR None
(mkFacts atomsG [mkAC c (SOff aN 0) (SOff aNOLD 0)] [ALIAS_OLD]).
Definition G8 (c : branch_cond) : sstate := fst (sym_run_toN src0segs src0tbl FUEL src0_A_memcpy (G6q c)).
Definition G9 : sstate := mkSS RA_MEMCPY regs_callG after_memR None (mkFacts atomsG [] []).
Definition G10 : sstate := fst (sym_run_toN src0segs src0tbl FUEL src0_A_libc_free G9).
Definition G11 : sstate := mkSS RA_FREE regs_callG after_memR None (mkFacts atomsG [] []).
Definition G12 : sstate := fst (sym_run_toN src0segs src0tbl FUEL REALLOC_RET G11).
Definition mlen (c : branch_cond) : sv := match c with BC_LTU => SOff aN 0 | _ => SOff aNOLD 0 end.
Lemma G7_run_ok : run_to_ok REALLOC_RET G6z G7.
Proof using. split; vm_compute; reflexivity. Qed.
Lemma G7_shape :
ss_pc G7 = REALLOC_RET /\ ss_resv G7 = None /\ callee_view G7 = callee_view0 /\
sr_get (ss_regs G7) 10 = SLit 0 /\ ss_mem G7 = after_memR.
Proof using. vm_compute. repeat split; reflexivity. Qed.
Lemma G8_run_ok c : c = BC_GEU \/ c = BC_LTU -> run_to_ok src0_A_memcpy (G6q c) (G8 c).
Proof using. intros [-> | ->]; split; vm_compute; reflexivity. Qed.
Lemma G8_shape c : c = BC_GEU \/ c = BC_LTU ->
ss_pc (G8 c) = src0_A_memcpy /\ ss_resv (G8 c) = None /\
view [1; 2; 3; 4; 8; 9; 10; 11; 12; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat (G8 c)
= [SLit RA_MEMCPY; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aQ 0; SOff aP 0; SOff aQ 0; SOff aP 0; mlen c;
junk 19; junk 20; junk 21; junk 22; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_mem (G8 c) = after_memR.
Proof using. intros [-> | ->]; vm_compute; repeat split; reflexivity. Qed.
Lemma G10_run_ok : run_to_ok src0_A_libc_free G9 G10.
Proof using. split; vm_compute; reflexivity. Qed.
Lemma G10_shape :
ss_pc G10 = src0_A_libc_free /\ ss_resv G10 = None /\
view [1; 2; 3; 4; 8; 9; 10; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat G10
= [SLit RA_FREE; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aQ 0; SOff aP 0; SOff aP 0;
junk 19; junk 20; junk 21; junk 22; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_mem G10 = after_memR.
Proof using. vm_compute. repeat split; reflexivity. Qed.
Lemma G12_run_ok : run_to_ok REALLOC_RET G11 G12.
Proof using. split; vm_compute; reflexivity. Qed.
Lemma G12_shape :
ss_pc G12 = REALLOC_RET /\ ss_resv G12 = None /\ callee_view G12 = callee_view0 /\
sr_get (ss_regs G12) 10 = SOff aQ 0 /\ ss_mem G12 = after_memR.
Proof using. vm_compute. repeat split; reflexivity. Qed.
Section e.
Variables (E : env) (ms : machine_state) (model : Model).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlz : m_vm_lazy model = [].
Lemma G7_run : st_ok src0segs E G6z ms -> SR_cfv src0segs (mkCfg ms model) (to_state E ms model G7 after_memR).
Proof using Hh Hlz. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS G7_run_ok Hh Hlz). Qed.
Lemma G8_run c : c = BC_GEU \/ c = BC_LTU ->
st_ok src0segs E (G6q c) ms -> SR_cfv src0segs (mkCfg ms model) (to_state E ms model (G8 c) after_memR).
Proof using Hh Hlz. intros Hc HS. exact (SR_run_to' src0_A_memcpy E _ _ ms model HS (G8_run_ok c Hc) Hh Hlz). Qed.
Lemma G10_run : st_ok src0segs E G9 ms -> SR_cfv src0segs (mkCfg ms model) (to_state E ms model G10 after_memR).
Proof using Hh Hlz. intros HS. exact (SR_run_to' src0_A_libc_free E _ _ ms model HS G10_run_ok Hh Hlz). Qed.
Lemma G12_run : st_ok src0segs E G11 ms -> SR_cfv src0segs (mkCfg ms model) (to_state E ms model G12 after_memR).
Proof using Hh Hlz. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS G12_run_ok Hh Hlz). Qed.
End e.
End d.
