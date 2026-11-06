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
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aST := 112%nat. Definition aKR := 113%nat. Definition aER := 114%nat. Definition aPR := 115%nat.
Definition aTQ1R := 116%nat. Definition aT1R := 117%nat. Definition aTQ2R := 118%nat. Definition aT2R := 119%nat.
Definition aTQ3R := 120%nat. Definition aCL := 121%nat.
Definition DEBR : Z := src0_D_debruijn32.
Definition SCTR : Z := src0_D_size_classes.
Definition k_aliasR (k : kcase) : list (sv * sv) :=
match k with
| K3a | K3b => [(SAlu ALU_ADD (SOff aMEM 0) (SMd M_MUL (SOff aMP (-16)) (SOff aIDX 0)), SOff aMEM 0);
(SAlu ALU_ADD (SOff aMEM 0) (SOff aMP 0), SOff aEND 4)]
| _ => [(SAlu ALU_ADD (SOff aMEM 0) (SMd M_MUL STR16 (SOff aIDX 0)), SOff aST 0);
(SAlu ALU_ADD (SAlu ALU_ADD STR16 (SLit 16)) (SOff aST 0), SOff aEND 4)]
end.
Definition k_atomsR (k : kcase) : list (nat * afact) :=
match k with K1 | K2 => [(aST, mkAF 4096 (2^63 - 1) 0)] | _ => [] end.
Definition AL_kR : sv * sv := (SAlu ALU_SRL (SOff 11 3) (SLit 4), SOff aKR 0).
Definition smxR : sv := SOff aKR 1.
Definition sm1R : sv := SAlu ALU_OR (SAlu ALU_OR (SAluw ALU_SRL smxR (SLit 2)) smxR) (SAluw ALU_SRL smxR (SLit 1)).
Definition sm2R : sv := SAlu ALU_OR (SAluw ALU_SRL sm1R (SLit 2)) (SAluw ALU_SRL smxR (SLit 1)).
Definition sm3R : sv := SAlu ALU_OR (SAlu ALU_SRL sm2R (SLit 4)) sm2R.
Definition sm4R : sv := SAlu ALU_OR (SAlu ALU_SRL sm3R (SLit 8)) sm3R.
Definition ANDXR : sv := SAlu ALU_AND (SAlu ALU_ADD sm4R (SLit 1)) (SAlu ALU_XOR sm4R (SLit (-1))).
Definition TQ1XR : sv := SAlu ALU_ADD (SLit DEBR) (SAluw ALU_SRL (SMd M_MUL (SOff aPR 0) (SLit 125613361)) (SLit 27)).
Definition C4XR : sv := SAlu ALU_XOR (SAlu ALU_SLL (SOff aER 0) (SLit 2)) (SLit 124).
Definition TQ2XR : sv := SAlu ALU_ADD (SLit SCTR) (SAlu ALU_SLL (SAlu ALU_SUB (SLit 121) C4XR) (SLit 1)).
Definition I2CR (b1 : bool) : Z := if b1 then 120 else 122.
Definition TQ3XR (b1 : bool) : sv := SAlu ALU_ADD (SLit SCTR) (SAlu ALU_SLL (SAlu ALU_SUB (SLit (I2CR b1)) C4XR) (SLit 1)).
Definition C_b1R (b1 : bool) : acond := mkAC (if b1 then BC_LTU else BC_GEU) (SOff aKR 0) (SOff aT1R 0).
Definition RESXR (b1 : bool) : sv :=
SAlu ALU_OR (SAlu ALU_SUB (SLit (I2CR b1)) C4XR) (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aKR 0) (SOff aT2R 0)) (SLit 1)).
Definition R_tq1R : region := mkRegion (Some aTQ1R) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aER 0))].
Definition R_tq2R : region := mkRegion (Some aTQ2R) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT1R 0))].
Definition R_tq3R : region := mkRegion (Some aTQ3R) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT2R 0))].
Definition tabsR : smem := [R_tq1R; R_tq2R; R_tq3R].
Inductive ncase := NBig | NOver | NSmall (ge : bool) | NMid (b1 ge : bool).
Definition cLT : acond := mkAC BC_LTU (SOff aEP 0) (SOff aN 0).
Definition cGE : acond := mkAC BC_GEU (SOff aEP 0) (SOff aN 0).
Definition cCL (c : nat) (ge : bool) : acond := mkAC (if ge then BC_GE else BC_LT) (SOff c 1) (SOff aSC 0).
Definition nc_lo (nc : ncase) : Z := match nc with NBig => 131052 | NOver | NSmall _ => 0 | NMid _ _ => 157 end.
Definition nc_hi (nc : ncase) : Z := match nc with NBig => 2 ^ 62 - 1 | NSmall _ => 156 | _ => 131051 end.
Definition nc_atoms (nc : ncase) : list (nat * afact) :=
match nc with
| NBig | NOver => []
| NSmall _ => [(aKR, mkAF 0 9 0)]
| NMid _ _ => [(aKR, mkAF 10 8190 0); (aER, mkAF 3 12 0); (aPR, mkAF 8 4096 0);
(aTQ1R, mkAF DEBR (DEBR + 31) 0); (aT1R, mkAF 0 8191 0); (aTQ2R, mkAF SCTR (SCTR + 94) 1);
(aT2R, mkAF 0 8191 0); (aTQ3R, mkAF SCTR (SCTR + 94) 1); (aCL, mkAF 0 47 0)]
end.
Definition nc_conds (nc : ncase) : list acond :=
match nc with
| NBig => []
| NOver => [cLT]
| NSmall ge => [cGE; cCL aKR ge]
| NMid b1 ge => [cGE; C_b1R b1; cCL aCL ge]
end.
Definition nc_alias (nc : ncase) : list (sv * sv) :=
match nc with
| NBig | NOver => []
| NSmall _ => [AL_kR]
| NMid b1 _ => [AL_kR; (ANDXR, SOff aPR 0); (TQ1XR, SOff aTQ1R 0); (TQ2XR, SOff aTQ2R 0); (TQ3XR b1, SOff aTQ3R 0); (RESXR b1, SOff aCL 0)]
end.
Definition entry_memS (k : kcase) (r : rcase) : smem :=
[reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; reg_stkR] ++ k_mem k ++ r_mem r.
Definition entry_atomsS (k : kcase) (r : rcase) (nc : ncase) : list (nat * afact) :=
(aN, mkAF (nc_lo nc) (nc_hi nc) 0) :: (aSP, mkAF (CEIL_MIN + 8256) (2^63 - 1) 4) :: nc_atoms nc ++ k_atomsR k ++ common_atoms ++ k_atoms k ++ r_atoms r.
Definition entry_factsS (k : kcase) (r : rcase) (nc : ncase) : facts :=
mkFacts (entry_atomsS k r nc) (nc_conds nc ++ common_conds ++ k_conds k ++ r_conds r) (nc_alias nc ++ k_aliasR k ++ common_alias ++ k_alias k ++ r_alias r).
Definition S0s (k : kcase) (r : rcase) (nc : ncase) : sstate := mkSS src0_A_realloc regs_init (entry_memS k r) None (entry_factsS k r nc).
Definition IP : Z := src0_A_realloc + 0x3cc.
Definition MID : Z := src0_A_realloc + 0x204.
Definition stopA (nc : ncase) : Z :=
match nc with NSmall true => IP | NMid _ _ => MID | _ => src0_A_libc_malloc_impl end.
Definition SA (k : kcase) (r : rcase) (nc : ncase) : sstate := fst (sym_run_toN src0segs src0tbl FUEL (stopA nc) (S0s k r nc)).
Definition midS (ss : sstate) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (drop_bases [aTQ] (ss_mem ss) ++ tabsR) (ss_resv ss) (ss_facts ss).
Definition stopB (ge : bool) : Z := if ge then IP else src0_A_libc_malloc_impl.
Definition SB (k : kcase) (r : rcase) (b1 ge : bool) : sstate :=
fst (sym_run_toN src0segs src0tbl FUEL (stopB ge) (midS (SA k r (NMid b1 ge)))).
Definition reg_end5w : region := mkRegion (Some aEND) (-5) 0 (-5) 0 [].
Definition t_memS (t : rcase) : smem :=
match t with R0 => [] | R14 => [reg_npn] | R5 => [reg_end5w] | R6 => [reg_npn; reg_end5w] end.
Definition PNX : sv := SAlu ALU_ADD (SOff aP 0) (SOff aN 0).
Definition WRSVR : sv := SAluw ALU_SUB (SOff aEND 0) (SOff aNPN 0).
Definition t_atomsS (t : rcase) : list (nat * afact) :=
match t with R14 | R6 => [(aNPN, mkAF 4096 CEIL_MAX 0)] | _ => [] end.
Definition t_condsS (t : rcase) : list acond :=
match t with
| R14 => [mkAC BC_NE WRSVR (SLit 0); mkAC BC_LT WRSVR (SLit 5)]
| R6 => [mkAC BC_NE WRSVR (SLit 0); mkAC BC_GE WRSVR (SLit 5)]
| _ => []
end.
Definition t_aliasS (t : rcase) : list (sv * sv) :=
match t with
| R0 => [(PNX, SOff aEND 0)]
| R5 => [(PNX, SOff aEND (-5))]
| R14 | R6 => [(PNX, SOff aNPN 0); (SAlu ALU_ADD (SOff aEND 0) (SAluw ALU_SUB (SLit 0) WRSVR), SOff aNPN 0)]
end.
Definition exitS (ss : sstate) (t : rcase) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (drop_bases [aP; aEND; aPN] (ss_mem ss) ++ reg_hdr :: t_memS t) (ss_resv ss)
(facts_app (ss_facts ss) (t_atomsS t) (t_condsS t) (t_aliasS t)).
Definition SIP (k : kcase) (r : rcase) (nc : ncase) : sstate :=
match nc with NMid b1 ge => SB k r b1 ge | _ => SA k r nc end.
Definition SX (k : kcase) (r : rcase) (nc : ncase) (t : rcase) : sstate :=
fst (sym_run_toN src0segs src0tbl FUEL REALLOC_RET (exitS (SIP k r nc) t)).
Lemma SA_run_ok k r nc : k <> K3b -> run_to_ok (stopA nc) (S0s k r nc) (SA k r nc).
Proof. intros Hk. split; destruct k, r, nc as [| |[]|[] []]; (contradiction || vm_compute; reflexivity). Qed.
Lemma SB_run_ok k r b1 ge : k <> K3b -> run_to_ok (stopB ge) (midS (SA k r (NMid b1 ge))) (SB k r b1 ge).
Proof. intros Hk. split; destruct k, r, b1, ge; (contradiction || vm_compute; reflexivity). Qed.
Lemma SX_run_ok k r nc t : k <> K3b -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) ->
run_to_ok REALLOC_RET (exitS (SIP k r nc) t) (SX k r nc t).
Proof. intros Hk [->|[b1 ->]]; split; destruct k, r, t; try contradiction; try destruct b1; vm_compute; reflexivity. Qed.
Definition MV : list nat := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition arr_view (r : rcase) : list sv :=
[SLit RA_MALLOC; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aN 0; SOff aP 0; SOff aN 0; ENDR r;
SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Definition head_memS : smem := [reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk1].
Definition tabs_of (nc : ncase) : smem := match nc with NMid _ _ => tabsR | _ => [reg_tq] end.
Definition mem_at (r : rcase) (nc : ncase) : smem :=
match nc with NMid _ _ => head_memS ++ r_mem r ++ tabsR | _ => head_memS ++ [reg_tq] ++ r_mem r end.
Lemma SA_shape_mid k r b1 ge : k <> K3b ->
ss_pc (SA k r (NMid b1 ge)) = MID /\ ss_resv (SA k r (NMid b1 ge)) = None /\
ss_mem (SA k r (NMid b1 ge)) = head_memS ++ [reg_tq] ++ r_mem r /\
ss_facts (SA k r (NMid b1 ge)) = entry_factsS k r (NMid b1 ge).
Proof. intros Hk. destruct k, r, b1, ge; (contradiction || vm_compute; repeat split; reflexivity). Qed.
Lemma SA_shape_arr k r nc : k <> K3b -> stopA nc = src0_A_libc_malloc_impl ->
ss_pc (SA k r nc) = src0_A_libc_malloc_impl /\ ss_resv (SA k r nc) = None /\
view MV (SA k r nc) = arr_view r /\ ss_mem (SA k r nc) = mem_at r nc.
Proof.
intros Hk Hs. destruct nc as [| |[]|[] []]; cbn in Hs; try (vm_compute in Hs; discriminate);
destruct k, r; (contradiction || vm_compute; repeat split; reflexivity).
Qed.
Lemma SB_shape_arr k r b1 : k <> K3b ->
ss_pc (SB k r b1 false) = src0_A_libc_malloc_impl /\ ss_resv (SB k r b1 false) = None /\
view MV (SB k r b1 false) = arr_view r /\ ss_mem (SB k r b1 false) = mem_at r (NMid b1 false).
Proof. intros Hk. destruct k, r, b1; (contradiction || vm_compute; repeat split; reflexivity). Qed.
Lemma SI_shape k r nc : k <> K3b -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) ->
ss_pc (SIP k r nc) = IP /\ ss_resv (SIP k r nc) = None /\ ss_mem (SIP k r nc) = mem_at r nc.
Proof.
intros Hk [->|[b1 ->]]; destruct k, r; try contradiction; try destruct b1; vm_compute; repeat split; reflexivity.
Qed.
Definition H3F (t : rcase) : sv :=
match t with
| R0 => SAlu ALU_OR (SLit 0) (SOff aIDX 0)
| R14 => SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_ADD WRSVR (SLit 0)) (SLit 5)) (SOff aIDX 0)
| R5 | R6 => SAlu ALU_OR (SLit 160) (SOff aIDX 0)
end.
Definition hdr_fin (t : rcase) : region :=
mkRegion (Some aP) (-4) 0 (-3) 0 [mkChunk (-3) (CVal 1 (H3F t)); mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-2) (CVal 2 (SOff aOFF 0))].
Definition npn_fin : region := mkRegion (Some aNPN) 0 1 0 1 [mkChunk 0 (CVal 1 (SLit 0))].
Definition end5_fin (v : sv) : region := mkRegion (Some aEND) (-5) 0 (-5) 0 [mkChunk (-4) (CVal 4 v); mkChunk (-5) (CVal 1 (SLit 0))].
Definition t_fin (t : rcase) : smem :=
match t with R0 => [] | R14 => [npn_fin] | R5 => [end5_fin (SLit 5)] | R6 => [npn_fin; end5_fin WRSVR] end.
Definition fin_mem (nc : ncase) (t : rcase) : smem :=
[reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk1] ++ tabs_of nc ++ hdr_fin t :: t_fin t.
Lemma SX_shape k r nc t : k <> K3b -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) ->
ss_pc (SX k r nc t) = REALLOC_RET /\ ss_resv (SX k r nc t) = None /\ callee_view (SX k r nc t) = callee_view0 /\
sr_get (ss_regs (SX k r nc t)) 10 = SOff aP 0 /\ ss_mem (SX k r nc t) = fin_mem nc t.
Proof.
intros Hk [->|[b1 ->]]; destruct k, r, t; try contradiction; try destruct b1; vm_compute; repeat split; reflexivity.
Qed.
Section e.
Variables (E : env) (ms : machine_state) (model : Model).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlz : m_vm_lazy model = [].
Lemma SA_run k r nc : k <> K3b -> st_ok src0segs E (S0s k r nc) ms -> SR_cfv src0segs (mkCfg ms model) (to_state E ms model (SA k r nc) (entry_memS k r)).
Proof. intros Hk HS. exact (SR_run_to' (stopA nc) E _ _ ms model HS (SA_run_ok k r nc Hk) Hh Hlz). Qed.
Lemma SB_run k r b1 ge : k <> K3b -> st_ok src0segs E (midS (SA k r (NMid b1 ge))) ms ->
SR_cfv src0segs (mkCfg ms model) (to_state E ms model (SB k r b1 ge) (ss_mem (midS (SA k r (NMid b1 ge))))).
Proof. intros Hk HS. exact (SR_run_to' (stopB ge) E _ _ ms model HS (SB_run_ok k r b1 ge Hk) Hh Hlz). Qed.
Lemma SX_run k r nc t : k <> K3b -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) -> st_ok src0segs E (exitS (SIP k r nc) t) ms ->
SR_cfv src0segs (mkCfg ms model) (to_state E ms model (SX k r nc t) (ss_mem (exitS (SIP k r nc) t))).
Proof. intros Hk Hnc HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS (SX_run_ok k r nc t Hk Hnc) Hh Hlz). Qed.
End e.
End d.
