From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YH00 YH03 YN0b_cf YN07_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW0e_cf YV00_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN1y_cf YN1d_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM06_cf YO0d_cf.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition arr_regs : list nat := [1; 2; 3; 4; 8; 9; 10; 18; 23; 24; 25; 26; 27]%nat.
Definition arr_view (r : rcase) : list sv :=
[SLit RA_MALLOC; SOff aSP (-64); SOff 3 0; SOff 4 0; SOff aN 0; SOff aP 0; SOff aN 0; ENDR r;
SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Definition regs_view (sr : list sv) : list sv := map (fun i => nth i sr (SLit 0)) arr_regs.
Definition mem_fin (r : rcase) : smem :=
[reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk1; reg_got; reg_guard; reg_errnoR] ++ r_mem r.
Lemma ENDR_lt r : sv_atoms_lt 110 (ENDR r) = true.
Proof using. destruct r; reflexivity. Qed.
Lemma stk1_in r : In stk1 (mem_fin r).
Proof using. unfold mem_fin. apply in_or_app. left. cbn [In]. do 6 right. left. reflexivity. Qed.
Lemma errno_in r : In reg_errnoR (mem_fin r).
Proof using. unfold mem_fin. apply in_or_app. left. cbn [In]. do 9 right. left. reflexivity. Qed.
Lemma arr_intro (E E' : env) (r : rcase) (mem0 mem1 mem4 : word -> option byte) (sr : list sv) (regs4 : bvmap 5 word) :
env_agree 110 E E' -> regs_ok E' sr regs4 -> regs_view sr = arr_view r ->
(forall x, mem4 x = mem1 x) -> region_ok src0segs E mem1 stk1 -> region_ok src0segs E mem1 reg_errnoR ->
frame_of E (entry_mem r) mem0 mem1 -> arr_ok E r mem0 regs4 mem4.
Proof using.
intros HA HR V EQ Rstk Rerr FR.
assert (D : forall n v, (1 <= n <= 31)%nat -> nth n sr (SLit 0) = v -> sv_atoms_lt 110 v = true ->
getr regs4 (nat_to_reg n) = sv_denot E v).
{ intros n v Hn Hv Hl. rewrite (HR (nat_to_reg n)), (YN1y_cf.sr_get_nat sr n Hn), Hv. exact (YP06.sv_denot_agree 110 E E' v HA Hl). }
unfold regs_view, arr_regs, arr_view in V. cbn [map] in V.
injection V as V1 V2 V3 V4 V8 V9 V10 V18 V23 V24 V25 V26 V27.
destruct Rstk as (_ & _ & Wstk & Cstk). destruct Rerr as (_ & _ & Werr & _).
cbn [r_base r_wlo r_whi r_chunks stk1 reg_errnoR] in Wstk, Cstk, Werr.
constructor.
- exact (D 1%nat _ ltac:(lia) V1 eq_refl).
- exact (D 2%nat _ ltac:(lia) V2 eq_refl).
- exact (D 8%nat _ ltac:(lia) V8 eq_refl).
- exact (D 9%nat _ ltac:(lia) V9 eq_refl).
- exact (D 10%nat _ ltac:(lia) V10 eq_refl).
- exact (D 18%nat _ ltac:(lia) V18 (ENDR_lt r)).
- intros i Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
+ exact (D 3%nat _ ltac:(lia) V3 eq_refl).
+ exact (D 4%nat _ ltac:(lia) V4 eq_refl).
+ exact (D 23%nat _ ltac:(lia) V23 eq_refl).
+ exact (D 24%nat _ ltac:(lia) V24 eq_refl).
+ exact (D 25%nat _ ltac:(lia) V25 eq_refl).
+ exact (D 26%nat _ ltac:(lia) V26 eq_refl).
+ exact (D 27%nat _ ltac:(lia) V27 eq_refl).
- eapply Forall_impl; [|exact Cstk]. intros c Hc i Hi. destruct (Hc i Hi) as (b & B1 & B2).
exists b. split; [exact B1|]. rewrite (YN1d_cf.mbyte_ext1 mem1 mem4 _ (EQ _)). exact B2.
- intros o Ho. exact (YN1d_cf.writable_ext1 mem1 mem4 _ (EQ _) (Wstk o Ho)).
- intros o Ho. exact (YN1d_cf.writable_ext1 mem1 mem4 _ (EQ _) (Werr o Ho)).
- intros x Hx. rewrite EQ. exact (FR x Hx).
Qed.
Lemma arrive_run (E : env) (r : rcase) (ss0 ss1 : sstate) ms md :
st_ok src0segs E ss0 ms -> ss_mem ss0 = entry_mem r -> run_to_ok src0_A_libc_malloc_impl ss0 ss1 ->
ss_resv ss1 = None -> regs_view (ss_regs ss1) = arr_view r -> ss_mem ss1 = mem_fin r ->
m_halted md = None -> m_vm_lazy md = [] ->
SR_cfv src0segs (mkCfg ms md) (arrives E r (ms_mem ms) md).
Proof using.
intros HS Hm Hrun Hrv V Hmf Hh Hlz.
eapply SR_cfv_mono; [exact (SR_run_to' _ E _ _ ms md HS Hrun Hh Hlz)|].
intros c (ms1 & -> & HS1 & HF). rewrite Hm in HF.
pose proof (st_ok_mem_ok src0segs E _ _ HS1) as (_ & ROK & _). rewrite Hmf in ROK.
exists (ms_regs ms1), (ms_mem ms1). split.
- rewrite (st_ok_mkst src0segs E _ _ HS1 Hrv) at 1. rewrite (proj2 Hrun). reflexivity.
- apply (arr_intro E E r (ms_mem ms) (ms_mem ms1) (ms_mem ms1) (ss_regs ss1) (ms_regs ms1)
(env_agree_refl 110 E) (st_ok_regs_ok src0segs E _ _ HS1) V (fun x => eq_refl)).
+ exact (proj1 (Forall_forall _ _) ROK _ (stk1_in r)).
+ exact (proj1 (Forall_forall _ _) ROK _ (errno_in r)).
+ exact HF.
Qed.
Definition Sgt (r : rcase) : sstate :=
fst (sym_run_toN src0segs src0tbl FUEL src0_A_libc_malloc_impl (S0n 0 131051 [mkAC BC_LTU (SOff aEP 0) (SOff aN 0)] r)).
Lemma Sgt_run_ok r : run_to_ok src0_A_libc_malloc_impl (S0n 0 131051 [mkAC BC_LTU (SOff aEP 0) (SOff aN 0)] r) (Sgt r).
Proof using. split; destruct r; vm_compute; reflexivity. Qed.
Lemma Sgt_shape r : ss_resv (Sgt r) = None /\ regs_view (ss_regs (Sgt r)) = arr_view r /\ ss_mem (Sgt r) = mem_fin r.
Proof using. destruct r; vm_compute; repeat split; reflexivity. Qed.
Definition Sle (r : rcase) : sstate :=
fst (sym_run_toN src0segs src0tbl FUEL src0_A_libc_malloc_impl (S0n 0 156 [mkAC BC_GEU (SOff aEP 0) (SOff aN 0)] r)).
Lemma Sle_run_ok r : run_to_ok src0_A_libc_malloc_impl (S0n 0 156 [mkAC BC_GEU (SOff aEP 0) (SOff aN 0)] r) (Sle r).
Proof using. split; destruct r; vm_compute; reflexivity. Qed.
Lemma Sle_shape r : ss_resv (Sle r) = None /\ regs_view (ss_regs (Sle r)) = arr_view r /\ ss_mem (Sle r) = mem_fin r.
Proof using. destruct r; vm_compute; repeat split; reflexivity. Qed.
Theorem k3b_small_gt (E : env) (r : rcase) ms md :
st_ok src0segs E (S0n 0 131051 [mkAC BC_LTU (SOff aEP 0) (SOff aN 0)] r) ms ->
m_halted md = None -> m_vm_lazy md = [] ->
SR_cfv src0segs (mkCfg ms md) (arrives E r (ms_mem ms) md).
Proof using.
intros HS Hh Hlz. destruct (Sgt_shape r) as (Hrv & V & Hm).
exact (arrive_run E r _ _ ms md HS eq_refl (Sgt_run_ok r) Hrv V Hm Hh Hlz).
Qed.
Theorem k3b_small_le157 (E : env) (r : rcase) ms md :
st_ok src0segs E (S0n 0 156 [mkAC BC_GEU (SOff aEP 0) (SOff aN 0)] r) ms ->
m_halted md = None -> m_vm_lazy md = [] ->
SR_cfv src0segs (mkCfg ms md) (arrives E r (ms_mem ms) md).
Proof using.
intros HS Hh Hlz. destruct (Sle_shape r) as (Hrv & V & Hm).
exact (arrive_run E r _ _ ms md HS eq_refl (Sle_run_ok r) Hrv V Hm Hh Hlz).
Qed.
End a.
