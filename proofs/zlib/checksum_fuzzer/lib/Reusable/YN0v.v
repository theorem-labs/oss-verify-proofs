(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YN0b YN0t YN0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition regs_lit (l : list (nat * Z)) : list sv :=
map (fun i => match find (fun p => Nat.eqb (fst p) i) l with
| Some (_, z) => SLit z
| None => if Nat.eqb i 0 then SLit 0 else SOff i 0
end) (seq 0 32).
Definition XM : Z := src0_A_nontrivial_free + 0x2c8.
Definition XF : Z := src0_A_nontrivial_free + 0x2e4.
Definition XJ : Z := src0_A_nontrivial_free + 0x288.
Definition aSEQ := 64%nat.
Definition m1_atoms (u z : bool) : list (nat * afact) :=
[ (aNG, mkAF 4096 (2^63 - 1) 3); (aGMEM, mkAF 0 (2^64 - 1) 0); (aGBITS, mkAF 0 (2^64 - 1) 0);
(aSC, mkAF 0 63 0); (aLAST, mkAF 0 31 0); (aSEQ, mkAF 0 255 0) ]
++ (if u then [ (aACT, mkAF (CTX + 80) (CTX + 80 + 8 * 47) 3); (aUSG, mkAF 0 (2^64 - 1) 0) ] else []).
Definition m1_alias (u : bool) : list (sv * sv) :=
(SCX, SOff aSC 0) :: (if u then [ (SAlu ALU_SLL (SOff aSC 0) (SLit 3), SOff aACT (- (CTX + 80))) ] else []).
Definition m1_conds (u z : bool) : list acond :=
[ mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0);
(if u then mkAC BC_GEU (SLit 47) (SOff aSC 0) else mkAC BC_LTU (SLit 47) (SOff aSC 0));
(if z then mkAC BC_EQ (SOff aSEQ 0) (SLit 255) else mkAC BC_NE (SOff aSEQ 0) (SLit 255)) ].
Definition reg_gM : region := mkRegion (Some aNG) 0 40 0 0 [mkChunk 16 (CVal 8 (SOff aGMEM 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))].
Definition reg_usgw : region := mkRegion (Some aACT) 384 392 384 392 [mkChunk 384 (CVal 8 (SOff aUSG 0))].
Definition reg_seq (w : bool) : region := mkRegion None (CTX + 912) (CTX + 913) (if w then CTX + 912 else 0) (if w then CTX + 913 else 0) [mkChunk (CTX + 912) (CVal 1 (SOff aSEQ 0))].
Definition reg_useq0 : region := mkRegion None (CTX + 848) (CTX + 880) (CTX + 848) (CTX + 880) [].
Definition m1_mem (u z : bool) : smem :=
[reg_gM; reg_seq true] ++ (if u then [reg_usgw] else []) ++ (if z then [reg_useq0] else []).
Definition ss_M1 (u z : bool) : sstate :=
mkSS XU (regs_lit [(18%nat, CTX)]) (m1_mem u z) None (mkFacts (m1_atoms u z) (m1_conds u z) (m1_alias u)).
Definition SSM1 (u z : bool) : sstate := fst (sym_run_toN src0segs src0tbl FUEL XM (ss_M1 u z)).
Definition NEWSEQ (z : bool) : sv := if z then SLit 1 else SOff aSEQ 1.
Definition m1_mem_out (u z : bool) : smem :=
[reg_gM; mkRegion None (CTX + 912) (CTX + 913) (CTX + 912) (CTX + 913) [mkChunk (CTX + 912) (CVal 1 (NEWSEQ z))]]
++ (if u then [mkRegion (Some aACT) 384 392 384 392
[mkChunk 384 (CVal 8 (SAlu ALU_ADD (SOff aUSG 0) (SAlu ALU_OR (SAlu ALU_XOR (SOff aGBITS 0) (SLit (-1))) (SLit (-32)))))]] else [])
++ (if z then [mkRegion None (CTX + 848) (CTX + 880) (CTX + 848) (CTX + 880)
[mkChunk (CTX + 872) (CVal 8 (SLit 0)); mkChunk (CTX + 864) (CVal 8 (SLit 0)); mkChunk (CTX + 856) (CVal 8 (SLit 0)); mkChunk (CTX + 848) (CVal 8 (SLit 0))]] else []).
Definition validM1 (u z : bool) : bool := true.
Definition m2_atoms (b : bool) : list (nat * afact) :=
[ (aNG, mkAF 4096 (2^63 - 1) 3); (11%nat, if b then mkAF 0 31 0 else mkAF 0 (2^64 - 1) 0); (12%nat, mkAF 1 255 0);
(aGMEM, mkAF 0 (2^64 - 1) 0); (aGBITS, mkAF 0 (2^64 - 1) 0); (aMP, mkAF 4096 (2^63 - 1) 12) ].
Definition m2_alias : list (sv * sv) := [ (SAlu ALU_AND (SOff aGBITS 0) (SLit (-4096)), SOff aMP 0) ].
Definition m2_conds (b : bool) : list acond :=
[ if b then mkAC BC_GEU (SLit 31) (SOff 11 0) else mkAC BC_LTU (SLit 31) (SOff 11 0) ].
Definition reg_useqb : region := mkRegion (Some 11%nat) (CTX + 848) (CTX + 849) (CTX + 848) (CTX + 849) [].
Definition m2_mem (b : bool) : smem := [reg_gM] ++ (if b then [reg_useqb] else []).
Definition ss_M2 (b : bool) : sstate :=
mkSS XM (regs_lit [(13%nat, 31); (18%nat, CTX)]) (m2_mem b) None (mkFacts (m2_atoms b) (m2_conds b) m2_alias).
Definition SSM2 (b : bool) : sstate := fst (sym_run_toN src0segs src0tbl FUEL XF (ss_M2 b)).
Definition m2_mem_out (b : bool) : smem :=
[reg_gM] ++ (if b then [mkRegion (Some 11%nat) (CTX + 848) (CTX + 849) (CTX + 848) (CTX + 849) [mkChunk (CTX + 848) (CVal 1 (SOff 12 0))]] else []).
Definition aPG := 65%nat.  Definition aPM := 66%nat.  Definition aH3 := 67%nat.  Definition aH16 := 68%nat.
Definition aPBITS := 69%nat. Definition aPAV := 70%nat. Definition aPFR := 71%nat. Definition aAREA := 72%nat.
Definition aPSC := 74%nat. Definition aPSCL := 75%nat. Definition aPTQ2 := 76%nat. Definition aPML := 77%nat.
Definition aPI := 78%nat. Definition aPLAST := 79%nat.
Definition SELFP : sv := SAluw ALU_SLL (SLit 1) (SOff aPI 0).
Definition MLCHKP : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff aPML 0) (SLit 8)) (SLit (-1)).
Definition n_atoms (m : bool) : list (nat * afact) :=
[ (aNG, mkAF 4096 (2^63 - 1) 3); (aGMEM, mkAF 4096 (2^63 - 1) 4); (aGBITS, mkAF 0 (2^64 - 1) 0);
(aSC, mkAF 0 47 0); (aLAST, mkAF 0 31 0); (aACT, mkAF (CTX + 80) (CTX + 80 + 8 * 47) 3); (aUSG, mkAF 0 (2^64 - 1) 0);
(aPG, mkAF 4096 (2^63 - 1) 3); (aPM, mkAF 4096 (2^63 - 1) 4); (aH3, mkAF 192 223 0); (aH16, mkAF 0 65535 0);
(aPBITS, mkAF 0 (2^64 - 1) 0); (aPAV, mkAF 0 (2^32 - 1) 0); (aPFR, mkAF 0 (2^32 - 1) 0); (aAREA, mkAF 4096 (2^63 - 1) 0);
(aPSC, mkAF 0 47 0); (aPSCL, mkAF 1 8191 0); (aPTQ2, mkAF TBL (TBL + 94) 1); (aPI, mkAF 0 31 0); (aPLAST, mkAF 0 31 0) ]
++ (if m then [ (aPML, mkAF 1 (2^52 - 1) 0) ] else []).
Definition n_alias (m : bool) : list (sv * sv) :=
[ (SCX, SOff aSC 0);
(SAlu ALU_SLL (SOff aSC 0) (SLit 3), SOff aACT (- (CTX + 80)));
(SAlu ALU_SRL (SOff aGBITS 0) (SLit 12), SLit 0);
(SAlu ALU_AND (SOff aH3 0) (SLit 31), SOff aPI 0);
(SAlu ALU_SUB (SOff aGMEM 0) (SAlu ALU_SLL (SOff aH16 0) (SLit 4)), SOff aPM 16);
(SAlu ALU_AND (SOff aPG 0) (SLit (-4096)), SOff aAREA 0);
(SAlu ALU_AND (SOff aPBITS 0) (SLit 31), SOff aPLAST 0);
(SAlu ALU_SRL (SAlu ALU_SLL (SOff aPBITS 0) (SLit 52)) (SLit 58), SOff aPSC 0);
(SAlu ALU_SLL (SOff aPSC 0) (SLit 1), SOff aPTQ2 (- TBL));
(SAlu ALU_SRL (SOff aPBITS 0) (SLit 12), if m then SOff aPML 0 else SLit 0) ].
Definition n_conds (m : bool) : list acond :=
[ mkAC BC_GEU (SOff aPLAST 0) (SOff aPI 0);
mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aPAV 0)) SELFP) (SLit 0);
mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aPFR 0)) SELFP) (SLit 0);
mkAC BC_GEU (SOff aH16 0) (SMd M_MUL (SOff aPSCL 0) (SOff aPI 0));
mkAC BC_LTU (SOff aH16 0) (SMd M_MUL (SOff aPI 1) (SOff aPSCL 0)) ]
++ (if m then [ mkAC BC_GEU MLCHKP (SOff aH16 0) ] else []).
Definition reg_nm : region :=
mkRegion (Some aGMEM) (-4) 8 0 8 [mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-3) (CVal 1 (SOff aH3 0)); mkChunk (-2) (CVal 2 (SOff aH16 0))].
Definition reg_pgrp : region := mkRegion (Some aPM) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff aPG 0))].
Definition reg_pmeta : region :=
mkRegion (Some aPG) 16 40 0 0 [mkChunk 16 (CVal 8 (SOff aPM 0)); mkChunk 24 (CVal 4 (SOff aPAV 0)); mkChunk 28 (CVal 4 (SOff aPFR 0)); mkChunk 32 (CVal 8 (SOff aPBITS 0))].
Definition reg_parea : region := mkRegion (Some aAREA) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff aSEC 0))].
Definition reg_ctx0 : region := mkRegion None CTX (CTX + 8) 0 0 [mkChunk CTX (CVal 8 (SOff aSEC 0))].
Definition reg_ptq : region := mkRegion (Some aPTQ2) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aPSCL 0))].
Definition n_mem (m : bool) : smem := [reg_gM; reg_usgw; reg_nm; reg_pgrp; reg_pmeta; reg_parea; reg_ctx0; reg_ptq].
Definition ss_N (m : bool) : sstate :=
mkSS XU (regs_lit [(18%nat, CTX)]) (n_mem m) None (mkFacts (n_atoms m) (n_conds m) (n_alias m)).
Definition SSN (m : bool) : sstate := fst (sym_run_toN src0segs src0tbl FUEL src0_A_nontrivial_free (ss_N m)).
Definition n_mem_out (m : bool) : smem :=
[reg_gM;
mkRegion (Some aACT) 384 392 384 392 [mkChunk 384 (CVal 8 (SAlu ALU_ADD (SOff aUSG 0) (SAlu ALU_OR (SAlu ALU_XOR (SOff aGBITS 0) (SLit (-1))) (SLit (-32)))))];
mkRegion (Some aGMEM) (-4) 8 0 8 [mkChunk 0 (CVal 8 (SLit 0)); mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-3) (CVal 1 (SOff aH3 0)); mkChunk (-2) (CVal 2 (SOff aH16 0))];
reg_pgrp; reg_pmeta; reg_parea; reg_ctx0; reg_ptq].
Inductive fentry := FE_XF | FE_RET2.
Inductive fvar := F0 | F1a | F1b.
Definition aGF (e : fentry) : nat := match e with FE_XF => 10%nat | FE_RET2 => 19%nat end.
Definition aBASE (e : fentry) : nat := match e with FE_XF => 12%nat | FE_RET2 => 10%nat end.
Definition aE1 := 80%nat. Definition aE8 := 81%nat. Definition aE9 := 82%nat. Definition aE18 := 83%nat. Definition aE19 := 84%nat.
Definition f_atoms (e : fentry) (v : fvar) : list (nat * afact) :=
[ (aGF e, mkAF 4096 (2^63 - 1) 3); (2%nat, mkAF CEIL_MIN (2^63 - 1) 4);
(aGV, mkAF 0 (2^64 - 1) 0); (aE1, mkAF 0 (2^64 - 1) 0); (aE8, mkAF 0 (2^64 - 1) 0); (aE9, mkAF 0 (2^64 - 1) 0);
(aE18, mkAF 0 (2^64 - 1) 0); (aE19, mkAF 0 (2^64 - 1) 0) ]
++ match v with
| F0 => []
| F1a => [ (aH, mkAF 4096 (2^63 - 1) 3) ]
| F1b => [ (aH, mkAF 4096 (2^63 - 1) 3); (aHP, mkAF 4096 (2^63 - 1) 3) ]
end.
Definition fstk_chunks : list chunk :=
[mkChunk 48 (CVal 8 (SOff aGV 0)); mkChunk 56 (CVal 8 (SOff aE19 0)); mkChunk 64 (CVal 8 (SOff aE18 0));
mkChunk 72 (CVal 8 (SOff aE9 0)); mkChunk 80 (CVal 8 (SOff aE8 0)); mkChunk 88 (CVal 8 (SOff aE1 0))].
Definition reg_fstk : region := mkRegion (Some 2%nat) 0 96 8 48 fstk_chunks.
Definition reg_gF (e : fentry) : region := mkRegion (Some (aGF e)) 0 40 0 40 [].
Definition reg_fhd (v : fvar) : region :=
mkRegion None (CTX + 16) (CTX + 24) (match v with F0 => CTX + 16 | _ => 0 end) (match v with F0 => CTX + 24 | _ => 0 end)
[mkChunk (CTX + 16) (CVal 8 (match v with F0 => SLit 0 | _ => SOff aH 0 end))].
Definition f_vmem (v : fvar) : smem :=
match v with
| F0 => []
| F1a => [mkRegion (Some aH) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff aH 0))]]
| F1b => [mkRegion (Some aH) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff aHP 0))]; mkRegion (Some aHP) 8 16 8 16 []]
end.
Definition f_mem (e : fentry) (v : fvar) : smem := [reg_gF e; reg_fstk; reg_guard; reg_fhd v] ++ f_vmem v.
Definition ss_F (e : fentry) (v : fvar) : sstate :=
mkSS (match e with FE_XF => XF | FE_RET2 => XJ end) (regs_lit [(18%nat, CTX); (9%nat, GUARD)]) (f_mem e v) None
(mkFacts (f_atoms e v) [] []).
Definition SSF (e : fentry) (v : fvar) : sstate := fst (sym_run_toN src0segs src0tbl FUEL NT_RET (ss_F e v)).
Definition gF_chunks (e : fentry) (v : fvar) : list chunk :=
match v with
| F0 => [mkChunk 8 (CVal 8 (SOff (aGF e) 0)); mkChunk 0 (CVal 8 (SOff (aGF e) 0))]
| F1a => [mkChunk 0 (CVal 8 (SOff aH 0)); mkChunk 8 (CVal 8 (SOff aH 0))]
| F1b => [mkChunk 0 (CVal 8 (SOff aHP 0)); mkChunk 8 (CVal 8 (SOff aH 0))]
end ++ [mkChunk 32 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0))].
Definition fstk_out : list chunk :=
[mkChunk 40 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0))]
++ fstk_chunks.
Definition f_vmem_out (e : fentry) (v : fvar) : smem :=
match v with
| F0 => []
| F1a => [mkRegion (Some aH) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff (aGF e) 0)); mkChunk 8 (CVal 8 (SOff (aGF e) 0))]]
| F1b => [mkRegion (Some aH) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff (aGF e) 0))]; mkRegion (Some aHP) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff (aGF e) 0))]]
end.
Definition f_mem_out (e : fentry) (v : fvar) : smem :=
[mkRegion (Some (aGF e)) 0 40 0 40 (gF_chunks e v); mkRegion (Some 2%nat) 0 96 8 48 fstk_out; reg_guard;
match v with
| F0 => mkRegion None (CTX + 16) (CTX + 24) (CTX + 16) (CTX + 24) [mkChunk (CTX + 16) (CVal 8 (SOff (aGF e) 0))]
| _ => reg_fhd v
end] ++ f_vmem_out e v.
Definition view (ss : sstate) (l : list nat) : list sv := map (fun i => sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) l.
Definition kept : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition keptU : list sv := map (fun i => SOff i 0) kept.
Lemma M1_run_ok : forall u z, run_to_ok XM (ss_M1 u z) (SSM1 u z).
Proof. intros u z. split; destruct u, z; vm_compute; reflexivity. Qed.
Lemma SSM1_shape : forall u z,
ss_pc (SSM1 u z) = XM /\ ss_resv (SSM1 u z) = None /\
view (SSM1 u z) ([1; 2; 8; 9; 10; 11; 12; 13; 18; 19]%nat ++ kept) =
[SOff 1 0; SOff 2 0; SOff 8 0; SOff 9 0; SOff 10 0; SOff aSC (-7); NEWSEQ z; SLit 31; SLit CTX; SOff 19 0] ++ keptU /\
ss_mem (SSM1 u z) = m1_mem_out u z.
Proof. intros u z. destruct u, z; vm_compute; repeat split; reflexivity. Qed.
Lemma M2_run_ok : forall b, run_to_ok XF (ss_M2 b) (SSM2 b).
Proof. intros b. split; destruct b; vm_compute; reflexivity. Qed.
Lemma SSM2_shape : forall b,
ss_pc (SSM2 b) = XF /\ ss_resv (SSM2 b) = None /\
view (SSM2 b) ([1; 2; 8; 9; 10; 11; 12; 18; 19]%nat ++ kept) =
[SOff 1 0; SOff 2 0; SOff 8 0; SOff 9 0; SOff 10 0; SOff aMP 0; SOff aGMEM 0; SLit CTX; SOff 19 0] ++ keptU /\
ss_mem (SSM2 b) = m2_mem_out b.
Proof. intros b. destruct b; vm_compute; repeat split; reflexivity. Qed.
Lemma N_run_ok : forall m, run_to_ok src0_A_nontrivial_free (ss_N m) (SSN m).
Proof. intros m. split; destruct m; vm_compute; reflexivity. Qed.
Lemma SSN_shape : forall m,
ss_pc (SSN m) = src0_A_nontrivial_free /\ ss_resv (SSN m) = None /\
view (SSN m) ([1; 2; 8; 9; 10; 11; 18; 19]%nat ++ kept) =
[SLit XJ; SOff 2 0; SOff aGMEM 0; SOff 9 0; SOff aPG 0; SOff aPI 0; SLit CTX; SOff 10 0] ++ keptU /\
ss_mem (SSN m) = n_mem_out m.
Proof. intros m. destruct m; vm_compute; repeat split; reflexivity. Qed.
Lemma F_run_ok : forall e v, run_to_ok NT_RET (ss_F e v) (SSF e v).
Proof. intros e v. split; destruct e, v; vm_compute; reflexivity. Qed.
Lemma SSF_shape : forall e v,
ss_pc (SSF e v) = NT_RET /\ ss_resv (SSF e v) = None /\
view (SSF e v) ([1; 2; 8; 9; 10; 11; 18; 19]%nat ++ kept) =
[SOff aE1 0; SOff 2 96; SOff aE8 0; SOff aE9 0; SOff (aBASE e) 0; SOff 11 0; SOff aE18 0; SOff aE19 0] ++ keptU /\
ss_mem (SSF e v) = f_mem_out e v.
Proof. intros e v. destruct e, v; vm_compute; repeat split; reflexivity. Qed.
Theorem stage_run : forall stop ss ss1 E ms model,
run_to_ok stop ss ss1 ->
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E ss1 ms1 /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros stop ss ss1 E ms model Hr HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to stop); [exact HS | exact Hr | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
End a.
