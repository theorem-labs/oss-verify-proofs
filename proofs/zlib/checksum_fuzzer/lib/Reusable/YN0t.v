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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aNG := 10%nat.
Definition aNI := 11%nat.
Definition aPREV := 41%nat. Definition aNEXT := 42%nat. Definition aGMEM := 43%nat.
Definition aGAV := 44%nat. Definition aGFR := 45%nat. Definition aGBITS := 46%nat. Definition aGV := 47%nat.
Definition aSC := 48%nat.
Definition aACT := 49%nat.
Definition aH := 50%nat.
Definition aHP := 51%nat.
Definition aTQ2 := 52%nat.
Definition aSCL := 53%nat.
Definition aUSG := 54%nat.
Definition aBNC := 55%nat.
Definition aLAST := 56%nat.
Definition aMP := 57%nat.
Definition GOT : Z := src0_D_got_stack_chk_guard.
Definition GUARD : Z := src0_D_stack_chk_guard.
Definition CTX : Z := src0_D_malloc_context.
Definition TBL : Z := src0_D_size_classes.
Definition NT_RET : Z := src0_A_nontrivial_free + 0x3d0.
Lemma ctx_al8 z : (CTX + 80 + 8 * z) mod 8 = 0.
Proof. replace (CTX + 80 + 8 * z) with (CTX + (10 + z) * 8) by lia. rewrite Z_mod_plus_full. reflexivity. Qed.
Lemma tbl_al2 z : (TBL + 2 * z) mod 2 = 0.
Proof. replace (TBL + 2 * z) with (TBL + z * 2) by lia. rewrite Z_mod_plus_full. reflexivity. Qed.
Definition NSELF : sv := SAluw ALU_SLL (SLit 1) (SOff aNI 0).
Definition NMASK : sv := SAlu ALU_OR (SExt true 32 (SOff aGAV 0)) (SExt true 32 (SOff aGFR 0)).
Definition NALL : sv := SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aGBITS 0)) (SLit (-1)).
Definition NMS : sv := SAluw ALU_ADD NMASK NSELF.
Definition SCX : sv := SAlu ALU_SRL (SAlu ALU_SLL (SOff aGBITS 0) (SLit 52)) (SLit 58).
Definition NFREED : sv := SAlu ALU_OR (SExt true 32 (SOff aGFR 0)) NSELF.
Definition nt_atoms : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 96) (2^63 - 1) 4);
(aNG, mkAF 4096 (2^63 - 1) 3);
(aNI, mkAF 0 31 0);
(aPREV, mkAF 0 (2^64 - 1) 0); (aNEXT, mkAF 0 (2^64 - 1) 0); (aGMEM, mkAF 0 (2^64 - 1) 0);
(aGAV, mkAF 0 (2^32 - 1) 0); (aGFR, mkAF 0 (2^32 - 1) 0);
(aGBITS, mkAF 0 (2^64 - 1) 0); (aGV, mkAF 0 (2^64 - 1) 0);
(aSC, mkAF 0 63 0); (aACT, mkAF (CTX + 80) (CTX + 80 + 8 * 47) 3); (aLAST, mkAF 0 31 0);
(aUSG, mkAF 0 (2^64 - 1) 0); (aBNC, mkAF 0 255 0) ].
Definition nt_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SExt true 32 (SOff aGFR 0)) (SLit 0), SExt true 32 (SOff aGFR 0));
(SCX, SOff aSC 0);
(SAlu ALU_SLL (SOff aSC 0) (SLit 3), SOff aACT (- (CTX + 80))) ].
Definition cond_C32 : acond := mkAC BC_NE (SAlu ALU_AND (SOff aGBITS 0) (SLit 32)) (SLit 0).
Inductive bpath := P0 | P1V1 | P1V2 | P2V2.
Inductive bvar := VB1 | VB2 | VB3 | VB4a | VB4b.
Definition validB (p : bpath) (v : bvar) : bool :=
match p, v with
| P0, _ => true
| P1V2, VB1 | P2V2, VB1 => true
| P1V1, VB2 => true
| _, _ => false
end.
Definition p_atoms (p : bpath) : list (nat * afact) :=
match p with
| P0 => []
| _ => [ (aTQ2, mkAF TBL (TBL + 94) 1); (aSCL, mkAF 1 8191 0); (aMP, mkAF 4096 (2^63 - 1) 12) ]
end.
Definition v_atoms (v : bvar) : list (nat * afact) :=
match v with
| VB4a => [ (aH, mkAF 4096 (2^63 - 1) 3) ]
| VB4b => [ (aH, mkAF 4096 (2^63 - 1) 3); (aHP, mkAF 4096 (2^63 - 1) 3) ]
| _ => []
end.
Definition p_alias (p : bpath) : list (sv * sv) :=
match p with
| P0 => []
| _ => [ (SAlu ALU_AND (SAlu ALU_SRL (SOff aGBITS 0) (SLit 5)) (SLit 126), SOff aTQ2 (- TBL));
(SAlu ALU_SLL (SOff aSC 0) (SLit 1), SOff aTQ2 (- TBL));
(SAlu ALU_AND (SOff aGBITS 0) (SLit (-4096)), SOff aMP 0) ]
end
++ [ (SAlu ALU_AND (SOff aGBITS 0) (SLit 31), match p with P1V1 => SLit 0 | _ => SOff aLAST 0 end) ].
Definition NINE : sv := SAlu ALU_ADD (SMd M_MUL (SOff aLAST 0) (SLit 9)) (SLit 9).
Definition okay_conds : list acond :=
[ mkAC BC_EQ NMS NALL; mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0);
mkAC BC_EQ (SOff aNEXT 0) (SOff aNG 0); mkAC BC_GEU (SLit 31) (SOff aSC (-7)); mkAC BC_GEU (SOff aBNC 0) (SLit 100) ].
Definition p_conds (p : bpath) : list acond :=
match p with
| P0 => [ mkAC BC_NE NMS NALL ]
| P1V1 => okay_conds ++ [ mkAC BC_GEU (SOff aMP (-16)) (SAlu ALU_SLL (SOff aSCL 0) (SLit 4)); mkAC BC_LTU (SOff aUSG 0) (SLit 9) ]
| P1V2 => okay_conds ++ [ mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_LTU (SOff aUSG 0) NINE ]
| P2V2 => okay_conds ++ [ mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_GEU (SOff aUSG 0) NINE; mkAC BC_LTU (SLit 18) (SOff aLAST 0) ]
end.
Definition v_conds (v : bvar) : list acond :=
match v with
| VB1 => [ mkAC BC_NE NMASK (SLit 0) ]
| VB2 | VB3 => [ mkAC BC_EQ NMASK (SLit 0); mkAC BC_LTU (SOff aSC 0) (SLit 48) ]
| VB4a | VB4b => [ mkAC BC_EQ NMASK (SLit 0); mkAC BC_LTU (SOff aSC 0) (SLit 48); mkAC BC_NE (SOff aH 0) (SOff aNG 0) ]
end.
Definition b_facts (p : bpath) (v : bvar) : facts :=
mkFacts (nt_atoms ++ p_atoms p ++ v_atoms v) (cond_C32 :: p_conds p ++ v_conds v) (nt_alias ++ p_alias p).
Definition metag_chunks (pn : sv) (freed : sv) : list chunk :=
[mkChunk 0 (CVal 8 pn); mkChunk 8 (CVal 8 pn); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 28 (CVal 4 freed); mkChunk 32 (CVal 8 (SOff aGBITS 0))].
Definition reg_metag (wlo whi : Z) : region :=
mkRegion (Some aNG) 0 40 wlo whi
[mkChunk 0 (CVal 8 (SOff aPREV 0)); mkChunk 8 (CVal 8 (SOff aNEXT 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 28 (CVal 4 (SOff aGFR 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))].
Definition reg_metag0 : region := mkRegion (Some aNG) 0 40 0 32 (metag_chunks (SLit 0) (SOff aGFR 0)).
Definition reg_metag_v (v : bvar) : region :=
match v with VB1 | VB2 => reg_metag 28 32 | _ => reg_metag0 end.
Definition reg_got : region := mkRegion None GOT (GOT + 8) 0 0 [mkChunk GOT (CVal 8 (SLit GUARD))].
Definition reg_guard : region := mkRegion None GUARD (GUARD + 8) 0 0 [mkChunk GUARD (CVal 8 (SOff aGV 0))].
Definition reg_ntstk : region := mkRegion (Some aSP) (-96) 0 (-96) 0 [].
Definition ntstk_chunks : list chunk :=
[mkChunk (-48) (CVal 8 (SOff aGV 0)); mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition reg_ntstk' : region := mkRegion (Some aSP) (-96) 0 (-96) 0 ntstk_chunks.
Definition reg_act (val : sv) (w : bool) : region :=
mkRegion (Some aACT) 0 8 0 (if w then 8 else 0) [mkChunk 0 (CVal 8 val)].
Definition reg_h2 (pr : sv) : region := mkRegion (Some aH) 0 16 0 16 [mkChunk 0 (CVal 8 pr)].
Definition reg_h1 (pr : sv) : region := mkRegion (Some aH) 0 8 0 8 [mkChunk 0 (CVal 8 pr)].
Definition reg_hp : region := mkRegion (Some aHP) 8 16 8 16 [].
Definition reg_hp' (nx : sv) : region := mkRegion (Some aHP) 8 16 8 16 [mkChunk 8 (CVal 8 nx)].
Definition v_mem (v : bvar) : smem :=
match v with
| VB1 => []
| VB2 => [reg_act (SOff aNG 0) false]
| VB3 => [reg_act (SLit 0) true]
| VB4a => [reg_act (SOff aH 0) false; reg_h2 (SOff aH 0)]
| VB4b => [reg_act (SOff aH 0) false; reg_h1 (SOff aHP 0); reg_hp]
end.
Definition reg_tq2 : region := mkRegion (Some aTQ2) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aSCL 0))].
Definition reg_bnc : region := mkRegion (Some aSC) (CTX + 873) (CTX + 874) 0 0 [mkChunk (CTX + 873) (CVal 1 (SOff aBNC 0))].
Definition reg_usg : region := mkRegion (Some aACT) 384 392 0 0 [mkChunk 384 (CVal 8 (SOff aUSG 0))].
Definition p_mem (p : bpath) : smem :=
match p with P0 => [] | _ => [reg_tq2; reg_bnc; reg_usg] end.
Definition common_memB (v : bvar) : smem := [reg_metag_v v; reg_got; reg_guard; reg_ntstk].
Definition b_mem (p : bpath) (v : bvar) : smem := common_memB v ++ v_mem v ++ p_mem p.
Definition ss_ntB (p : bpath) (v : bvar) : sstate :=
mkSS src0_A_nontrivial_free regs_init (b_mem p v) None (b_facts p v).
Definition SSB (p : bpath) (v : bvar) : sstate := fst (sym_run_toN src0segs src0tbl FUEL NT_RET (ss_ntB p v)).
Definition metag_outB (v : bvar) : region :=
match v with
| VB1 | VB2 => mkRegion (Some aNG) 0 40 28 32
[mkChunk 28 (CVal 4 NFREED); mkChunk 0 (CVal 8 (SOff aPREV 0)); mkChunk 8 (CVal 8 (SOff aNEXT 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]
| VB3 => mkRegion (Some aNG) 0 40 0 32
[mkChunk 28 (CVal 4 NFREED); mkChunk 8 (CVal 8 (SOff aNG 0)); mkChunk 0 (CVal 8 (SOff aNG 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]
| VB4a => mkRegion (Some aNG) 0 40 0 32
[mkChunk 28 (CVal 4 NFREED); mkChunk 0 (CVal 8 (SOff aH 0)); mkChunk 8 (CVal 8 (SOff aH 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]
| VB4b => mkRegion (Some aNG) 0 40 0 32
[mkChunk 28 (CVal 4 NFREED); mkChunk 0 (CVal 8 (SOff aHP 0)); mkChunk 8 (CVal 8 (SOff aH 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]
end.
Definition v_memB_out (v : bvar) : smem :=
match v with
| VB1 => []
| VB2 => [reg_act (SOff aNG 0) false]
| VB3 => [reg_act (SOff aNG 0) true]
| VB4a => [reg_act (SOff aH 0) false; mkRegion (Some aH) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff aNG 0)); mkChunk 8 (CVal 8 (SOff aNG 0))]]
| VB4b => [reg_act (SOff aH 0) false; reg_h1 (SOff aNG 0); reg_hp' (SOff aNG 0)]
end.
Definition memB_out (p : bpath) (v : bvar) : smem :=
[metag_outB v; reg_got; reg_guard; reg_ntstk'] ++ v_memB_out v ++ p_mem p.
Lemma ntB_run_ok : forall p v, validB p v = true -> run_to_ok NT_RET (ss_ntB p v) (SSB p v).
Proof. intros p v Hv. split; destruct p, v; try discriminate Hv; vm_compute; reflexivity. Qed.
Theorem ntB_run : forall p v E ms model,
validB p v = true ->
st_ok src0segs E (ss_ntB p v) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E (SSB p v) ms1 /\
frame_of E (b_mem p v) (ms_mem ms) (ms_mem ms1)).
Proof.
intros p v E ms model Hv HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to NT_RET); [exact HS | apply ntB_run_ok; exact Hv | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Lemma SSB_shape : forall p v, validB p v = true ->
ss_pc (SSB p v) = NT_RET /\ ss_resv (SSB p v) = None /\ callee_view (SSB p v) = callee_view0 /\
sr_get (ss_regs (SSB p v)) 10 = SLit 0 /\ sr_get (ss_regs (SSB p v)) 11 = SLit 0 /\
ss_mem (SSB p v) = memB_out p v.
Proof. intros p v Hv. destruct p, v; try discriminate Hv; vm_compute; repeat split; reflexivity. Qed.
End a.
