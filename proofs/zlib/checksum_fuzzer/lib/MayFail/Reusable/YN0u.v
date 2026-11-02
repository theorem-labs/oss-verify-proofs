(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0u.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aP := 58%nat. Definition aN := 59%nat. Definition aNMEM := 60%nat. Definition aNAIDX := 61%nat. Definition aNFR := 62%nat. Definition aHD := 63%nat.
Definition XU : Z := src0_A_nontrivial_free + 0x228.
Inductive apath := Q1 | Q2 | Q3 | Q4V1 | Q4V2 | Q5V1 | Q5V2 | Q6V1 | Q6V2 | Q7V1 | Q7V2.
Inductive dvar := D0 | D1 | D2a | D2b | D2a' | D2b'.
Definition nt_atoms0 : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 96) (2^63 - 1) 4);
(aNG, mkAF 4096 (2^63 - 1) 3);
(aNI, mkAF 0 31 0);
(aPREV, mkAF 0 (2^64 - 1) 0); (aNEXT, mkAF 0 (2^64 - 1) 0); (aGMEM, mkAF 0 (2^64 - 1) 0);
(aGAV, mkAF 0 (2^32 - 1) 0); (aGFR, mkAF 0 (2^32 - 1) 0);
(aGBITS, mkAF 0 (2^64 - 1) 0); (aGV, mkAF 0 (2^64 - 1) 0);
(aSC, mkAF 0 63 0); (aLAST, mkAF 0 31 0); (aUSG, mkAF 0 (2^64 - 1) 0); (aBNC, mkAF 0 255 0) ].
Definition q_atoms (q : apath) : list (nat * afact) :=
match q with
| Q1 => []
| _ => [ (aACT, mkAF (CTX + 80) (CTX + 80 + 8 * 47) 3); (aTQ2, mkAF TBL (TBL + 94) 1); (aSCL, mkAF 1 8191 0); (aMP, mkAF 0 (2^63 - 1) 12) ]
end.
Definition d_atoms : list (nat * afact) :=
[ (aP, mkAF 4096 (2^63 - 1) 3); (aN, mkAF 4096 (2^63 - 1) 3); (aNMEM, mkAF 4096 (2^63 - 1) 4);
(aNAIDX, mkAF 0 255 0); (aNFR, mkAF 0 (2^32 - 1) 0); (aHD, mkAF 0 (2^64 - 1) 0) ].
Definition a1_atoms (q : apath) (d : dvar) : list (nat * afact) := nt_atoms0 ++ q_atoms q ++ d_atoms.
Definition a1_alias (q : apath) : list (sv * sv) :=
[ (SCX, SOff aSC 0);
(SAlu ALU_ADD (SExt true 32 (SOff aNFR 0)) (SLit 0), SExt true 32 (SOff aNFR 0)) ] ++
match q with
| Q1 => []
| _ => [ (SAlu ALU_SLL (SOff aSC 0) (SLit 3), SOff aACT (- (CTX + 80)));
(SAlu ALU_AND (SAlu ALU_SRL (SOff aGBITS 0) (SLit 5)) (SLit 126), SOff aTQ2 (- TBL));
(SAlu ALU_SLL (SOff aSC 0) (SLit 1), SOff aTQ2 (- TBL));
(SAlu ALU_AND (SOff aGBITS 0) (SLit (-4096)), SOff aMP 0);
(SAlu ALU_AND (SOff aGBITS 0) (SLit 31), match q with Q3 | Q4V1 | Q5V1 | Q6V1 | Q7V1 => SLit 0 | _ => SOff aLAST 0 end) ]
end.
Definition nextx (d : dvar) : sv := match d with D0 => SLit 0 | D1 => SOff aNG 0 | _ => SOff aN 0 end.
Definition prevx (d : dvar) : sv := match d with D0 => SLit 0 | D1 => SOff aNG 0 | D2a | D2b => SOff aP 0 | _ => SOff aN 0 end.
Definition hdx (d : dvar) : sv := match d with D1 | D2b | D2b' => SOff aNG 0 | _ => SOff aHD 0 end.
Definition STRIDE_GE : acond := mkAC BC_GEU (SOff aMP (-16)) (SAlu ALU_SLL (SOff aSCL 0) (SLit 4)).
Definition q_conds (q : apath) (d : dvar) : list acond :=
mkAC BC_EQ NMS NALL ::
match q with
| Q1 => [ mkAC BC_LTU (SLit 47) (SOff aSC 0) ]
| Q2 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_EQ (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0) ]
| Q3 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0);
mkAC BC_LTU (SOff aMP (-16)) (SAlu ALU_SLL (SOff aSCL 0) (SLit 4)) ]
| Q4V1 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); STRIDE_GE; mkAC BC_NE (nextx d) (SOff aNG 0) ]
| Q4V2 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_NE (nextx d) (SOff aNG 0) ]
| Q5V1 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); STRIDE_GE; mkAC BC_LTU (SLit 31) (SOff aSC (-7)) ]
| Q5V2 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_LTU (SLit 31) (SOff aSC (-7)) ]
| Q6V1 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); STRIDE_GE; mkAC BC_GEU (SLit 31) (SOff aSC (-7)); mkAC BC_LTU (SOff aBNC 0) (SLit 100) ]
| Q6V2 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_GEU (SLit 31) (SOff aSC (-7)); mkAC BC_LTU (SOff aBNC 0) (SLit 100) ]
| Q7V1 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); STRIDE_GE; mkAC BC_GEU (SLit 31) (SOff aSC (-7)); mkAC BC_GEU (SOff aBNC 0) (SLit 100); mkAC BC_GEU (SOff aUSG 0) (SLit 9) ]
| Q7V2 => [ mkAC BC_GEU (SLit 47) (SOff aSC 0); mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0); mkAC BC_NE (SOff aLAST 0) (SLit 0); mkAC BC_GEU (SLit 31) (SOff aSC (-7)); mkAC BC_GEU (SOff aBNC 0) (SLit 100); mkAC BC_GEU (SOff aUSG 0) NINE; mkAC BC_GEU (SLit 18) (SOff aLAST 0) ]
end.
Definition d_conds (d : dvar) : list acond :=
match d with
| D0 => []
| D1 => [ mkAC BC_LTU (SOff aSC 0) (SLit 48) ]
| D2a | D2a' => [ mkAC BC_LTU (SOff aSC 0) (SLit 48); mkAC BC_NE (SOff aN 0) (SOff aNG 0); mkAC BC_NE (SOff aHD 0) (SOff aNG 0) ]
| D2b | D2b' => [ mkAC BC_LTU (SOff aSC 0) (SLit 48); mkAC BC_NE (SOff aN 0) (SOff aNG 0) ]
end.
Definition a1_facts (q : apath) (d : dvar) : facts := mkFacts (a1_atoms q d) (cond_C32 :: q_conds q d ++ d_conds d) (a1_alias q).
Definition metagA_chunks (d : dvar) : list chunk :=
[mkChunk 0 (CVal 8 (prevx d)); mkChunk 8 (CVal 8 (nextx d)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 28 (CVal 4 (SOff aGFR 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))].
Definition reg_metagA' (d : dvar) : region := mkRegion (Some aNG) 0 40 0 (match d with D0 => 0 | _ => 16 end) (metagA_chunks d).
Definition reg_n0 : region := mkRegion (Some aN) 0 8 0 8 [].
Definition reg_n016 : region := mkRegion (Some aN) 0 16 0 16 [].
Definition reg_n24 : region := mkRegion (Some aN) 16 32 24 32 [mkChunk 16 (CVal 8 (SOff aNMEM 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SOff aNFR 0))].
Definition reg_naidx : region := mkRegion (Some aNMEM) 8 9 0 0 [mkChunk 8 (CVal 1 (SOff aNAIDX 0))].
Definition reg_p8 : region := mkRegion (Some aP) 8 16 8 16 [].
Definition d_mem (d : dvar) : smem :=
match d with
| D0 => []
| D1 => [reg_act (SOff aNG 0) true]
| D2a => [reg_act (SOff aHD 0) false; reg_p8; reg_n0]
| D2b => [reg_act (SOff aNG 0) true; reg_p8; reg_n0; reg_n24; reg_naidx]
| D2a' => [reg_act (SOff aHD 0) false; reg_n016]
| D2b' => [reg_act (SOff aNG 0) true; reg_n016; reg_n24; reg_naidx]
end.
Definition q_mem (q : apath) : smem :=
match q with
| Q1 => []
| Q2 | Q3 | Q4V1 | Q4V2 => [reg_tq2]
| Q5V1 | Q5V2 => [reg_tq2]
| Q6V1 | Q6V2 => [reg_tq2; reg_bnc]
| Q7V1 | Q7V2 => [reg_tq2; reg_bnc; reg_usg]
end.
Definition a1_mem (q : apath) (d : dvar) : smem := [reg_metagA' d; reg_got; reg_guard; reg_ntstk] ++ d_mem d ++ q_mem q.
Definition ss_A1 (q : apath) (d : dvar) : sstate := mkSS src0_A_nontrivial_free regs_init (a1_mem q d) None (a1_facts q d).
Definition validA (q : apath) (d : dvar) : bool :=
match q, d with
| Q1, D0 => true
| (Q2 | Q3), _ => true
| (Q4V1 | Q4V2), (D0 | D2a | D2b | D2a' | D2b') => true
| (Q5V1 | Q5V2 | Q6V1 | Q6V2 | Q7V1 | Q7V2), D1 => true
| _, _ => false
end.
Definition SSA1 (q : apath) (d : dvar) : sstate := fst (sym_run_toN src0segs src0tbl FUEL XU (ss_A1 q d)).
Definition live_view (ss : sstate) : list sv :=
map (fun i => sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition live_viewU : list sv :=
[SOff 1 0; SOff 2 (-96); SOff 3 0; SOff 4 0; SOff 8 0; SLit GUARD; SOff 10 0; SLit CTX;
SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Definition NACT : sv := SAluw ALU_SLL (SLit 2) (SOff aNAIDX 0).
Definition NAVAIL : sv := SAlu ALU_AND (SExt true 32 (SOff aNFR 0)) (SAlu ALU_ADD NACT (SLit (-1))).
Definition NFREED2 : sv := SAlu ALU_AND (SExt true 32 (SOff aNFR 0)) (SAluw ALU_SUB (SLit 0) NACT).
Definition metagA_out (d : dvar) : region :=
mkRegion (Some aNG) 0 40 0 (match d with D0 => 0 | _ => 16 end)
(match d with
| D0 => metagA_chunks D0
| _ => [mkChunk 8 (CVal 8 (SLit 0)); mkChunk 0 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SOff aGMEM 0));
mkChunk 24 (CVal 4 (SOff aGAV 0)); mkChunk 28 (CVal 4 (SOff aGFR 0)); mkChunk 32 (CVal 8 (SOff aGBITS 0))]
end).
Definition reg_n24_out : region :=
mkRegion (Some aN) 16 32 24 32 [mkChunk 24 (CVal 4 NAVAIL); mkChunk 28 (CVal 4 NFREED2); mkChunk 16 (CVal 8 (SOff aNMEM 0))].
Definition d_mem_out (d : dvar) : smem :=
match d with
| D0 => []
| D1 => [reg_act (SLit 0) true]
| D2a => [reg_act (SOff aHD 0) false; mkRegion (Some aP) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff aN 0))]; mkRegion (Some aN) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff aP 0))]]
| D2b => [reg_act (SOff aN 0) true; mkRegion (Some aP) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff aN 0))]; mkRegion (Some aN) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff aP 0))];
reg_n24_out; reg_naidx]
| D2a' => [reg_act (SOff aHD 0) false; mkRegion (Some aN) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff aN 0)); mkChunk 8 (CVal 8 (SOff aN 0))]]
| D2b' => [reg_act (SOff aN 0) true; mkRegion (Some aN) 0 16 0 16 [mkChunk 0 (CVal 8 (SOff aN 0)); mkChunk 8 (CVal 8 (SOff aN 0))]; reg_n24_out; reg_naidx]
end.
Definition memA1_out (q : apath) (d : dvar) : smem := [metagA_out d; reg_got; reg_guard; reg_ntstk'] ++ d_mem_out d ++ q_mem q.
Lemma A1_run_ok : forall q d, validA q d = true -> run_to_ok XU (ss_A1 q d) (SSA1 q d).
Proof. intros q d Hv. split; destruct q, d; try discriminate Hv; vm_compute; reflexivity. Qed.
Theorem A1_run : forall q d E ms model,
validA q d = true ->
st_ok src0segs E (ss_A1 q d) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E (SSA1 q d) ms1 /\
frame_of E (a1_mem q d) (ms_mem ms) (ms_mem ms1)).
Proof.
intros q d E ms model Hv HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to XU); [exact HS | apply A1_run_ok; exact Hv | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Lemma SSA1_shape : forall q d, validA q d = true ->
ss_pc (SSA1 q d) = XU /\ ss_resv (SSA1 q d) = None /\ live_view (SSA1 q d) = live_viewU /\
ss_mem (SSA1 q d) = memA1_out q d.
Proof. intros q d Hv. destruct q, d; try discriminate Hv; vm_compute; repeat split; reflexivity. Qed.
End a.
