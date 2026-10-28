(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YQ0k YN06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UO0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition aN := 11%nat. Definition aGUARD := 96%nat. Definition aRET := 106%nat. Definition aNP := 107%nat.
Definition aNEND := 108%nat. Definition aNPN := 109%nat. Definition aNOLD := 101%nat. Definition aQ := 102%nat.
Definition aB16 := 103%nat. Definition aNEED := 104%nat. Definition aERRR := 105%nat.
Definition reg_errnoR : region :=
mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SOff aERRR 0))].
Definition BEQ : Z := ubs2_A_realloc + 0x2c8.
Definition MREMAP_ECALL : Z := ubs2_A_mremap + 0x94.
Definition REALLOC_RET : Z := ubs2_A_realloc + 0x440.
Definition RA_MALLOC : Z := ubs2_A_realloc + 0x39c.
Definition RA_MEMCPY : Z := ubs2_A_realloc + 0x3bc.
Definition RA_FREE : Z := ubs2_A_realloc + 0x3c4.
Definition reg_stkR : region := mkRegion (Some aSP) (-8256) 0 (-8256) 0 [].
Definition reg_metaR : region :=
mkRegion (Some aG) 16 40 16 40 [mkChunk 16 (CVal 8 (SOff aMEM 0)); mkChunk 24 (CVal 4 (SOff aAV 0)); mkChunk 28 (CVal 4 (SOff aFR 0)); mkChunk 32 (CVal 8 (SOff aBITS 0))].
Definition reg_hdr0 : region :=
mkRegion (Some aP) (-4) 0 0 0 [mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-3) (CVal 1 (SOff aH3 0)); mkChunk (-2) (CVal 2 (SOff aOFF 0))].
Definition reg_meta0 : region :=
mkRegion (Some aG) 16 40 0 0 [mkChunk 16 (CVal 8 (SOff aMEM 0)); mkChunk 24 (CVal 4 (SOff aAV 0)); mkChunk 28 (CVal 4 (SOff aFR 0)); mkChunk 32 (CVal 8 (SOff aBITS 0))].
Definition reg_got : region := mkRegion None ubs2_D_got_stack_chk_guard (ubs2_D_got_stack_chk_guard + 8) 0 0
[mkChunk ubs2_D_got_stack_chk_guard (CVal 8 (SLit ubs2_D_stack_chk_guard))].
Definition reg_guard : region := mkRegion None ubs2_D_stack_chk_guard (ubs2_D_stack_chk_guard + 8) 0 0
[mkChunk ubs2_D_stack_chk_guard (CVal 8 (SOff aGUARD 0))].
Definition entry_mem (r : rcase) : smem :=
[reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; reg_stkR; reg_got; reg_guard; reg_errnoR] ++ r_mem r.
Definition entry_atoms (r : rcase) : list (nat * afact) :=
(aN, mkAF 131052 (2^62 - 1) 0) :: (aB16, mkAF 0 4080 4) :: (aNEED, mkAF 4096 (2^63 - 4096) 12) ::
(aGUARD, mkAF 0 (2^64 - 1) 0) :: (aTP, mkAF 4096 (2^63 - 1) 0) :: (aERRR, mkAF 0 (2^32 - 1) 0) ::
(aSP, mkAF (CEIL_MIN + 8256) (2^63 - 1) 4) ::
common_atoms ++ k_atoms K3b ++ r_atoms r.
Definition NEEDX1 : sv := SAlu ALU_AND (SAlu ALU_ADD (SOff aN 4115) (SOff aB16 0)) (SLit (-4096)).
Definition NEEDX2 : sv := SAlu ALU_AND (SAlu ALU_ADD (SOff aB16 4115) (SOff aN 0)) (SLit (-4096)).
Definition entry_alias (r : rcase) : list (sv * sv) :=
(SAlu ALU_ADD (SOff aMEM 0) (SMd M_MUL (SOff aMP (-16)) (SOff aIDX 0)), SOff aMEM 0)
:: (SAlu ALU_ADD (SOff aMEM 0) (SOff aMP 0), SOff aEND 4)
:: (SAlu ALU_SUB (SOff aP 0) (SOff aMEM 0), SOff aB16 16)
:: (NEEDX1, SOff aNEED 0) :: (NEEDX2, SOff aNEED 0)
:: common_alias ++ k_alias K3b ++ r_alias r.
Definition entry_facts (r : rcase) : facts :=
mkFacts (entry_atoms r) (common_conds ++ k_conds K3b ++ r_conds r) (entry_alias r).
Definition S0 (r : rcase) : sstate := mkSS ubs2_A_realloc regs_init (entry_mem r) None (entry_facts r).
Definition run_to_ok (stop : Z) (ss ss1 : sstate) : Prop :=
sym_run_toN ubs2segs ubs2tbl FUEL stop ss = (ss1, RS_running) /\ ss_pc ss1 = stop.
Definition run_ecall_ok (ss ss1 : sstate) : Prop :=
sym_runN ubs2segs ubs2tbl FUEL ss = (ss1, RS_ecall).
Lemma SR_run_to' : forall stop E ss ss1 ms model,
st_ok ubs2segs E ss ms -> run_to_ok stop ss ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
SR ubs2segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok ubs2segs E ss1 ms1 /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros stop E ss ss1 ms model HS [Hrun Hpc] Hh Hlz.
eapply (SR_run_to_gen ubs2segs ubs2tbl ubs2tbl_ok FUEL stop E ss ss1 RS_running ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF. apply SR_ret. exists ms1. auto.
Qed.
Lemma SR_run_ecall'' : forall E ss ss1 ms model,
st_ok ubs2segs E ss ms -> run_ecall_ok ss ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
SR ubs2segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok_ecall ubs2segs E ss1 ms1 /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros E ss ss1 ms model HS Hrun Hh Hlz.
eapply (SR_run_ecall ubs2segs ubs2tbl ubs2tbl_ok FUEL E ss ss1 ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF. apply SR_ret. exists ms1. auto.
Qed.
Definition S1 (r : rcase) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL BEQ (S0 r)).
Lemma S1_run_ok : forall r, run_to_ok BEQ (S0 r) (S1 r).
Proof. intros r. split; destruct r; vm_compute; reflexivity. Qed.
Definition frame_chunks : list chunk :=
[mkChunk (-64) (CVal 8 (SOff 22 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ENDR (r : rcase) : sv :=
match r with R0 => SOff aEND 0 | R5 => SOff aEND (-5) | R14 | R6 => SOff aPN 0 end.
Definition view (l : list nat) (ss : sstate) : list sv := map (fun i => sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) l.
Lemma S1_shape : forall r,
ss_pc (S1 r) = BEQ /\ ss_resv (S1 r) = None /\
view [1; 2; 3; 4; 8; 9; 10; 11; 12; 14; 18; 19; 23; 24; 25; 26; 27]%nat (S1 r)
= [SOff 1 0; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aNEED 0; SOff aG 0; SOff aP 0; SOff aN 0; SOff aMEM 0; SOff aMP 0;
ENDR r; SOff aB16 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_facts (S1 r) = entry_facts r /\
ss_mem (S1 r) = [reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl;
mkRegion (Some aSP) (-8256) 0 (-8256) 0 frame_chunks; reg_got; reg_guard; reg_errnoR] ++ r_mem r.
Proof. intros r. destruct r; vm_compute; repeat split; reflexivity. Qed.
Definition condNE : acond := mkAC BC_NE (SOff aMP 0) (SOff aNEED 0).
Definition condEQ : acond := mkAC BC_EQ (SOff aMP 0) (SOff aNEED 0).
Definition S2 (r : rcase) : sstate := fst (sym_runN ubs2segs ubs2tbl FUEL (add_cond (S1 r) condNE)).
Lemma S2_run_ok : forall r, run_ecall_ok (add_cond (S1 r) condNE) (S2 r) /\ ss_pc (S2 r) = MREMAP_ECALL /\ ss_resv (S2 r) = None.
Proof. intros r. destruct r; (split; [|split]); vm_compute; reflexivity. Qed.
Definition frame_chunks2 (r : rcase) : list chunk :=
[mkChunk (-152) (CVal 8 (SOff aGUARD 0)); mkChunk (-72) (CVal 8 (SOff aEP 0)); mkChunk (-80) (CVal 8 (SOff aEND 4));
mkChunk (-88) (CVal 8 (SAlu ALU_ADD (SOff aN 4115) (SOff aB16 0))); mkChunk (-96) (CVal 8 (SOff aMP 0));
mkChunk (-144) (CVal 8 (SLit 4095)); mkChunk (-136) (CVal 8 (SOff aB16 0)); mkChunk (-128) (CVal 8 (ENDR r));
mkChunk (-120) (CVal 8 (SOff aG 0)); mkChunk (-112) (CVal 8 (SOff aNEED 0)); mkChunk (-104) (CVal 8 (SLit (ubs2_A_realloc + 0x2e8)))].
Definition frame_chunks3 : list chunk :=
[mkChunk (-176) (CVal 8 (SLit (2^64 - 1))); mkChunk (-168) (CVal 8 (SLit (ubs2_A_mremap + 0x9c)))].
Lemma S2_shape : forall r,
view [10; 11; 12; 13; 14; 17]%nat (S2 r) = [SOff aMEM 0; SOff aMP 0; SOff aNEED 0; SLit 1; SLit 0; SLit 216] /\
view [2; 3; 4; 21; 22; 23; 24; 25; 26; 27]%nat (S2 r) = [SOff 2 (-160); SOff 3 0; SOff 4 0; SOff aP 0; SOff aN 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
f_atoms (ss_facts (S2 r)) = entry_atoms r /\ f_alias (ss_facts (S2 r)) = entry_alias r.
Proof. intros r. destruct r; vm_compute; repeat split; reflexivity. Qed.
Fixpoint drop_bases (bs : list nat) (m : smem) : smem :=
match m with
| [] => []
| x :: m' => match r_base x with
| Some b => if existsb (Nat.eqb b) bs then drop_bases bs m' else x :: drop_bases bs m'
| None => x :: drop_bases bs m'
end
end.
Definition reg_nhdr : region :=
mkRegion (Some aNP) (-4) 0 (-4) 0 [mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-3) (CVal 1 (SOff aH3 0)); mkChunk (-2) (CVal 2 (SOff aOFF 0))].
Definition reg_nend1 : region := mkRegion (Some aNEND) 0 1 0 1 [].
Definition reg_nend5 : region := mkRegion (Some aNEND) (-5) 1 (-5) 1 [].
Definition reg_npn : region := mkRegion (Some aNPN) 0 1 0 1 [].
Definition t_mem (t : rcase) : smem :=
match t with
| R0 => [reg_nend1]
| R14 => [reg_nend1; reg_npn]
| R5 => [reg_nend5]
| R6 => [reg_nend5; reg_npn]
end.
Definition tail_mem (ss : sstate) (t : rcase) : smem :=
drop_bases [aP; aMEM; aEND; aPN; aG] (ss_mem ss) ++ [reg_metaR; reg_nhdr] ++ t_mem t.
Definition WRSV : sv := SAluw ALU_SUB (SOff aNEND 0) (SOff aNPN 0).
Definition t_atoms (t : rcase) : list (nat * afact) :=
(aNP, mkAF 4096 CEIL_MAX 4) :: (aNEND, mkAF 4096 CEIL_MAX 0) ::
match t with R14 | R6 => [(aNPN, mkAF 4096 CEIL_MAX 0)] | _ => [] end.
Definition t_conds (t : rcase) : list acond :=
match t with
| R14 => [mkAC BC_NE WRSV (SLit 0); mkAC BC_LT WRSV (SLit 5)]
| R6 => [mkAC BC_NE WRSV (SLit 0); mkAC BC_GE WRSV (SLit 5)]
| _ => []
end.
Definition t_alias (base : nat) (t : rcase) : list (sv * sv) :=
(SAlu ALU_ADD (SOff base 0) (SOff aB16 0), SOff aNP (-16))
:: (SAlu ALU_ADD (SOff base 0) (SOff aNEED 0), SOff aNEND 4)
:: match t with
| R0 => [(SAlu ALU_ADD (SOff aN 0) (SOff aNP 0), SOff aNEND 0)]
| R5 => [(SAlu ALU_ADD (SOff aN 0) (SOff aNP 0), SOff aNEND (-5))]
| R14 | R6 => [(SAlu ALU_ADD (SOff aN 0) (SOff aNP 0), SOff aNPN 0);
(SAlu ALU_ADD (SOff aNEND 0) (SAluw ALU_SUB (SLit 0) WRSV), SOff aNPN 0)]
end.
Definition facts_app (G : facts) (a : list (nat * afact)) (c : list acond) (al : list (sv * sv)) : facts :=
mkFacts (a ++ f_atoms G) (c ++ f_conds G) (al ++ f_alias G).
Definition S1eq (r t : rcase) : sstate :=
let s1 := S1 r in
mkSS (ss_pc s1) (ss_regs s1) (tail_mem s1 t) None
(facts_app (ss_facts s1) (t_atoms t) (condEQ :: t_conds t) (t_alias aMEM t)).
Definition S3 (r t : rcase) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL REALLOC_RET (S1eq r t)).
Lemma S3_run_ok : forall r t, run_to_ok REALLOC_RET (S1eq r t) (S3 r t).
Proof. intros r t. split; destruct r, t; vm_compute; reflexivity. Qed.
Definition S2ok (r t : rcase) : sstate :=
let s2 := S2 r in
resume s2 (SOff aRET 0) (tail_mem s2 t)
(facts_app (ss_facts s2) ((aRET, mkAF 4096 CEIL_MAX 12) :: t_atoms t) (t_conds t) (t_alias aRET t)).
Definition S5 (r t : rcase) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL REALLOC_RET (S2ok r t)).
Lemma S5_run_ok : forall r t, run_to_ok REALLOC_RET (S2ok r t) (S5 r t).
Proof. intros r t. split; destruct r, t; vm_compute; reflexivity. Qed.
Definition callee_view (ss : sstate) : list sv :=
view [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ss.
Definition callee_view0 : list sv :=
[SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0; SOff 9 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0;
SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Definition NEWBITS : sv := SAlu ALU_OR (SAlu ALU_AND (SOff aBITS 0) (SLit 4095)) (SOff aNEED 0).
Definition NEWH3 (t : rcase) : sv :=
SAlu ALU_OR (SLit (match t with R0 => 0 | R14 => 0 | _ => 160 end)) (SOff aIDX 0).
Definition NEWH3_14 : sv := SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_ADD WRSV (SLit 0)) (SLit 5)) (SOff aIDX 0).
Definition tail_mem_final (base : nat) (stk : region) (t : rcase) : smem :=
[reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR;
mkRegion (Some aG) 16 40 16 40 [mkChunk 32 (CVal 8 NEWBITS); mkChunk 16 (CVal 8 (SOff base 0)); mkChunk 24 (CVal 4 (SOff aAV 0)); mkChunk 28 (CVal 4 (SOff aFR 0))];
mkRegion (Some aNP) (-4) 0 (-4) 0 [mkChunk (-3) (CVal 1 (match t with R14 => NEWH3_14 | _ => NEWH3 t end)); mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-2) (CVal 2 (SOff aOFF 0))]]
++ match t with
| R0 => [mkRegion (Some aNEND) 0 1 0 1 [mkChunk 0 (CVal 1 (SLit 0))]]
| R14 => [mkRegion (Some aNEND) 0 1 0 1 [mkChunk 0 (CVal 1 (SLit 0))]; mkRegion (Some aNPN) 0 1 0 1 [mkChunk 0 (CVal 1 (SLit 0))]]
| R5 => [mkRegion (Some aNEND) (-5) 1 (-5) 1 [mkChunk (-4) (CVal 4 (SLit 5)); mkChunk (-5) (CVal 1 (SLit 0)); mkChunk 0 (CVal 1 (SLit 0))]]
| R6 => [mkRegion (Some aNEND) (-5) 1 (-5) 1 [mkChunk (-4) (CVal 4 WRSV); mkChunk (-5) (CVal 1 (SLit 0)); mkChunk 0 (CVal 1 (SLit 0))];
mkRegion (Some aNPN) 0 1 0 1 [mkChunk 0 (CVal 1 (SLit 0))]]
end.
Definition stk1 : region := mkRegion (Some aSP) (-8256) 0 (-8256) 0 frame_chunks.
Definition stk2 (r : rcase) : region := mkRegion (Some aSP) (-8256) 0 (-8256) 0 (frame_chunks2 r ++ frame_chunks).
Definition stk3 (r : rcase) : region := mkRegion (Some aSP) (-8256) 0 (-8256) 0 (frame_chunks3 ++ frame_chunks2 r ++ frame_chunks).
Lemma S2_mem : forall r,
ss_mem (S2 r) = [reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk2 r; reg_got; reg_guard; reg_errnoR] ++ r_mem r.
Proof. intros r. destruct r; vm_compute; reflexivity. Qed.
Lemma S3_shape : forall r t,
ss_pc (S3 r t) = REALLOC_RET /\ ss_resv (S3 r t) = None /\ callee_view (S3 r t) = callee_view0 /\
sr_get (ss_regs (S3 r t)) 10 = SOff aNP 0 /\
ss_mem (S3 r t) = tail_mem_final aMEM stk1 t.
Proof. intros r t. destruct r, t; vm_compute; repeat split; reflexivity. Qed.
Lemma S5_shape : forall r t,
ss_pc (S5 r t) = REALLOC_RET /\ ss_resv (S5 r t) = None /\ callee_view (S5 r t) = callee_view0 /\
sr_get (ss_regs (S5 r t)) 10 = SOff aNP 0 /\
ss_mem (S5 r t) = tail_mem_final aRET (stk2 r) t.
Proof. intros r t. destruct r, t; vm_compute; repeat split; reflexivity. Qed.
Definition S2no (r : rcase) : sstate :=
let s2 := S2 r in resume s2 (SLit (2^64 - 12)) (ss_mem s2) (ss_facts s2).
Definition S4 (r : rcase) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_libc_malloc_impl (S2no r)).
Lemma S4_run_ok : forall r, run_to_ok ubs2_A_libc_malloc_impl (S2no r) (S4 r).
Proof. intros r. split; destruct r; vm_compute; reflexivity. Qed.
Lemma S4_shape : forall r,
ss_pc (S4 r) = ubs2_A_libc_malloc_impl /\ ss_resv (S4 r) = None /\
view [1; 2; 3; 4; 8; 9; 10; 18; 23; 24; 25; 26; 27]%nat (S4 r)
= [SLit RA_MALLOC; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aN 0; SOff aP 0; SOff aN 0; ENDR r; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_mem (S4 r) = [reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk3 r; reg_got; reg_guard;
mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SLit 12))]] ++ r_mem r.
Proof. intros r. destruct r; vm_compute; repeat split; reflexivity. Qed.
Definition junk (i : nat) : sv := SOff (64 + i) 0.
Definition regs_after_malloc (res s2v : sv) : list sv :=
[SLit 0; junk 1; SOff aSP (-64); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aN 0; SOff aP 0; res; junk 11; junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
s2v; SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition after_memR : smem := [mkRegion (Some aSP) (-8256) 0 (-8256) 0 frame_chunks].
Definition after_atomsR : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 8256) (2^63 - 1) 4); (aTP, mkAF 4096 (2^63 - 1) 0); (aP, mkAF 4096 CEIL_MAX 4);
(aN, mkAF 131052 (2^62 - 1) 0); (aNOLD, mkAF 0 (2^62 - 1) 0); (aQ, mkAF 4096 CEIL_MAX 4) ].
Definition S6z : sstate :=
mkSS RA_MALLOC (regs_after_malloc (SLit 0) (SOff aNOLD 0)) after_memR None (mkFacts after_atomsR [] []).
Definition S7 : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL REALLOC_RET S6z).
Lemma S7_run_ok : run_to_ok REALLOC_RET S6z S7.
Proof. split; vm_compute; reflexivity. Qed.
Lemma S7_shape :
ss_pc S7 = REALLOC_RET /\ ss_resv S7 = None /\ callee_view S7 = callee_view0 /\
sr_get (ss_regs S7) 10 = SLit 0 /\ ss_mem S7 = after_memR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition S6q : sstate :=
mkSS RA_MALLOC (regs_after_malloc (SOff aQ 0) (SOff aP 0  )) after_memR None
(mkFacts after_atomsR [mkAC BC_GEU (SOff aN 0) (SOff aNOLD 0)] []).
Definition S6q' : sstate :=
mkSS RA_MALLOC (regs_after_malloc (SOff aQ 0) (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0))) after_memR None
(mkFacts after_atomsR [mkAC BC_GEU (SOff aN 0) (SOff aNOLD 0)]
[(SAlu ALU_SUB (SAlu ALU_ADD (SOff aP 0) (SOff aNOLD 0)) (SOff aP 0), SOff aNOLD 0)]).
Definition S8 : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_memcpy S6q').
Lemma S8_run_ok : run_to_ok ubs2_A_memcpy S6q' S8.
Proof. split; vm_compute; reflexivity. Qed.
Lemma S8_shape :
ss_pc S8 = ubs2_A_memcpy /\ ss_resv S8 = None /\
view [1; 2; 3; 4; 8; 9; 10; 11; 12; 23; 24; 25; 26; 27]%nat S8
= [SLit RA_MEMCPY; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aQ 0; SOff aP 0; SOff aQ 0; SOff aP 0; SOff aNOLD 0;
SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_mem S8 = after_memR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition regs_after_memcpy : list sv :=
[SLit 0; junk 1; SOff aSP (-64); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aQ 0; SOff aP 0; junk 10; junk 11; junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
junk 18; SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition S9 : sstate := mkSS RA_MEMCPY regs_after_memcpy after_memR None (mkFacts after_atomsR [] []).
Definition S10 : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL ubs2_A_libc_free S9).
Lemma S10_run_ok : run_to_ok ubs2_A_libc_free S9 S10.
Proof. split; vm_compute; reflexivity. Qed.
Lemma S10_shape :
ss_pc S10 = ubs2_A_libc_free /\ ss_resv S10 = None /\
view [1; 2; 3; 4; 8; 9; 10; 23; 24; 25; 26; 27]%nat S10
= [SLit RA_FREE; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff aQ 0; SOff aP 0; SOff aP 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
ss_mem S10 = after_memR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition regs_after_free : list sv :=
[SLit 0; junk 1; SOff aSP (-64); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aQ 0; SOff aP 0; junk 10; junk 11; junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
junk 18; SOff aB16 0; SLit 4095; SOff aP 0; SOff aN 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition S11 : sstate := mkSS RA_FREE regs_after_free after_memR None (mkFacts after_atomsR [] []).
Definition S12 : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL REALLOC_RET S11).
Lemma S12_run_ok : run_to_ok REALLOC_RET S11 S12.
Proof. split; vm_compute; reflexivity. Qed.
Lemma S12_shape :
ss_pc S12 = REALLOC_RET /\ ss_resv S12 = None /\ callee_view S12 = callee_view0 /\
sr_get (ss_regs S12) 10 = SOff aQ 0 /\ ss_mem S12 = after_memR.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section e.
Variables (E : env) (ms : machine_state) (model : Model).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlz : m_vm_lazy model = [].
Definition to_state (ss1 : sstate) (m0 : smem) : config -> Prop :=
fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok ubs2segs E ss1 ms1 /\ frame_of E m0 (ms_mem ms) (ms_mem ms1).
Definition to_ecall (ss1 : sstate) (m0 : smem) : config -> Prop :=
fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok_ecall ubs2segs E ss1 ms1 /\ frame_of E m0 (ms_mem ms) (ms_mem ms1).
Lemma S1_run r : st_ok ubs2segs E (S0 r) ms -> SR ubs2segs (mkCfg ms model) (to_state (S1 r) (entry_mem r)).
Proof. intros HS. exact (SR_run_to' BEQ E _ _ ms model HS (S1_run_ok r) Hh Hlz). Qed.
Lemma S2_run r : st_ok ubs2segs E (add_cond (S1 r) condNE) ms -> SR ubs2segs (mkCfg ms model) (to_ecall (S2 r) (ss_mem (S1 r))).
Proof. intros HS. exact (SR_run_ecall'' E _ _ ms model HS (proj1 (S2_run_ok r)) Hh Hlz). Qed.
Lemma S3_run r t : st_ok ubs2segs E (S1eq r t) ms -> SR ubs2segs (mkCfg ms model) (to_state (S3 r t) (ss_mem (S1eq r t))).
Proof. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS (S3_run_ok r t) Hh Hlz). Qed.
Lemma S4_run r : st_ok ubs2segs E (S2no r) ms -> SR ubs2segs (mkCfg ms model) (to_state (S4 r) (ss_mem (S2no r))).
Proof. intros HS. exact (SR_run_to' ubs2_A_libc_malloc_impl E _ _ ms model HS (S4_run_ok r) Hh Hlz). Qed.
Lemma S5_run r t : st_ok ubs2segs E (S2ok r t) ms -> SR ubs2segs (mkCfg ms model) (to_state (S5 r t) (ss_mem (S2ok r t))).
Proof. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS (S5_run_ok r t) Hh Hlz). Qed.
Lemma S7_run : st_ok ubs2segs E S6z ms -> SR ubs2segs (mkCfg ms model) (to_state S7 after_memR).
Proof. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS S7_run_ok Hh Hlz). Qed.
Lemma S8_run : st_ok ubs2segs E S6q' ms -> SR ubs2segs (mkCfg ms model) (to_state S8 after_memR).
Proof. intros HS. exact (SR_run_to' ubs2_A_memcpy E _ _ ms model HS S8_run_ok Hh Hlz). Qed.
Lemma S10_run : st_ok ubs2segs E S9 ms -> SR ubs2segs (mkCfg ms model) (to_state S10 after_memR).
Proof. intros HS. exact (SR_run_to' ubs2_A_libc_free E _ _ ms model HS S10_run_ok Hh Hlz). Qed.
Lemma S12_run : st_ok ubs2segs E S11 ms -> SR ubs2segs (mkCfg ms model) (to_state S12 after_memR).
Proof. intros HS. exact (SR_run_to' REALLOC_RET E _ _ ms model HS S12_run_ok Hh Hlz). Qed.
End e.
End d.
