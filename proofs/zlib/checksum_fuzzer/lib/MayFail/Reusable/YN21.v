(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN21.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aACT := 40%nat.
Definition aG := 41%nat.
Definition aAV := 42%nat.
Definition aUS := 43%nat.
Definition aH := 44%nat.
Definition aHU := 45%nat.
Definition aHAV := 46%nat.
Definition aHFR := 47%nat.
Inductive hcase := HN | H1 | H2 | H3.
Inductive t1v := VA | VB6 | VBout | VBodd | VC | VD (h : hcase) (lt : bool).
Definition R_act (cs : list chunk) : region := mkRegion (Some aACT) 0 400 0 0 cs.
Definition c_act0 (g : bool) : chunk := mkChunk 0 (CVal 8 (if g then SOff aG 0 else SLit 0)).
Definition c_us0 (z : bool) : chunk := mkChunk 384 (CVal 8 (if z then SLit 0 else SOff aUS 0)).
Definition c_act1 (h : hcase) : chunk := mkChunk 8 (CVal 8 (match h with HN => SLit 0 | _ => SOff aH 0 end)).
Definition c_us1 : chunk := mkChunk 392 (CVal 8 (SOff aHU 0)).
Definition R_g : region := mkRegion (Some aG) 0 40 0 0 [mkChunk 24 (CVal 4 (SOff aAV 0))].
Definition h_chunks (h : hcase) : list chunk :=
match h with
| H1 => [mkChunk 24 (CVal 4 (SOff aHAV 0))]
| H2 => [mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SOff aHFR 0))]
| _ => [mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0))]
end.
Definition R_h (h : hcase) : region := mkRegion (Some aH) 0 40 0 0 (h_chunks h).
Definition act_chunks (v : t1v) : list chunk :=
match v with
| VA => [c_act0 true]
| VB6 | VBout | VBodd => [c_act0 false]
| VC => [c_act0 false; c_us0 false]
| VD h _ => [c_act0 false; c_us0 true; c_act1 h; c_us1]
end.
Definition t1_mem (v : t1v) : smem :=
R_nl :: R_act (act_chunks v) ::
match v with VA => [R_g] | VD HN _ => [] | VD h _ => [R_h h] | _ => [] end.
Definition t1_atoms (v : t1v) : list (nat * afact) :=
match v with
| VA => [(20%nat, mkAF 0 47 0); (aG, mkAF 4096 (2^63) 3); (aAV, mkAF 0 (2^32-1) 0)]
| VB6 => [(20%nat, mkAF 6 6 0)]
| VBout | VBodd => [(20%nat, mkAF 0 47 0)]
| VC => [(20%nat, mkAF 0 47 0); (aUS, mkAF 1 (2^48) 0)]
| VD h _ => [(20%nat, mkAF 0 46 0); (aHU, mkAF 0 (2^48) 0)]
++ match h with HN => [] | _ => [(aH, mkAF 4096 (2^63) 3)] end
++ match h with H1 => [(aHAV, mkAF 1 (2^32-1) 0)] | H2 => [(aHFR, mkAF 1 (2^32-1) 0)] | _ => [] end
end ++ [(8%nat, mkAF 0 131051 0); (2%nat, F_sp48); (aACT, mkAF (CTX+80) (CTX+80+8*47) 3)].
Definition C_eq6 := mkAC BC_EQ (SOff 20 0) (SLit 6).
Definition C_ne6 := mkAC BC_NE (SOff 20 0) (SLit 6).
Definition C_lt4 := mkAC BC_LTU (SLit 27) (SOff 20 (-4)).
Definition C_in := mkAC BC_GEU (SLit 27) (SOff 20 (-4)).
Definition C_odd := mkAC BC_NE (SAlu ALU_AND (SOff 20 0) (SLit 1)) (SLit 0).
Definition C_even := mkAC BC_EQ (SAlu ALU_AND (SOff 20 0) (SLit 1)) (SLit 0).
Definition C_hav := mkAC BC_NE (SExt true 32 (SOff aHAV 0)) (SLit 0).
Definition C_hfr := mkAC BC_NE (SExt true 32 (SOff aHFR 0)) (SLit 0).
Definition UX (h : hcase) : sv := match h with HN | H3 => SOff aHU 3 | _ => SOff aHU 0 end.
Definition C_u (h : hcase) (lt : bool) := mkAC (if lt then BC_LTU else BC_GEU) (UX h) (SLit 13).
Definition t1_conds (v : t1v) : list acond :=
match v with
| VA => [] | VB6 => [C_eq6] | VBout => [C_ne6; C_lt4] | VBodd => [C_ne6; C_in; C_odd] | VC => [C_ne6; C_in; C_even]
| VD h lt => [C_ne6; C_in; C_even; C_u h lt] ++ match h with H1 => [C_hav] | H2 => [C_hfr] | _ => [] end
end.
Definition AL1 : sv * sv := (SAlu ALU_SLL (SOff 20 0) (SLit 3), SOff aACT (-(CTX+80))).
Definition AL2 : sv * sv := (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_OR (SOff 20 0) (SLit 1)) (SLit 0)) (SLit 3), SOff aACT (8 - (CTX + 80))).
Definition t1_alias (v : t1v) : list (sv * sv) := match v with VD _ _ => [AL1; AL2] | _ => [AL1] end.
Definition t1_facts (v : t1v) : facts := mkFacts (t1_atoms v) (t1_conds v) (t1_alias v).
Definition ss_T1 (v : t1v) : sstate :=
mkSS PA (regs_lit [(9%nat, LOCK); (19%nat, DEB); (4%nat, TP)]) (t1_mem v) None (t1_facts v).
Definition SST1 (v : t1v) : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PB (ss_T1 v))) (t1_facts v).
Definition OR1 : sv := SAlu ALU_ADD (SAlu ALU_OR (SOff 20 0) (SLit 1)) (SLit 0).
Definition t1_s4 (v : t1v) : sv := match v with VD _ true => OR1 | _ => SOff 20 0 end.
Definition t1_s2 (v : t1v) : sv := match v with VA => SOff aG 0 | VD HN true => SLit 0 | VD _ true => SOff aH 0 | _ => SLit 0 end.
Definition t1_a0 (v : t1v) : sv :=
match v with VA => SExt true 32 (SOff aAV 0) | VD H1 true => SExt true 32 (SOff aHAV 0) | _ => SLit 0 end.
Definition T1_VIEW : list nat := ([20; 18; 10; 2; 4; 8; 9; 19]%nat ++ CSAVED).
Lemma T1_run_ok v : run_to_ok PB (ss_T1 v) (fst (sym_run_toN src0segs src0tbl FUEL PB (ss_T1 v))).
Proof. destruct v as [| | | | |[| | |] [|]]; split; vm_compute; reflexivity. Qed.
Lemma SST1_view v :
cview T1_VIEW (SST1 v) = (PB, None, t1_mem v, [t1_s4 v; t1_s2 v; t1_a0 v; SOff 2 0; SLit TP; SOff 8 0; SLit LOCK; SLit DEB] ++ csaved_svs).
Proof. destruct v as [| | | | |[| | |] [|]]; vm_compute; reflexivity. Qed.
Theorem T1_run v E ms md :
st_ok src0segs E (ss_T1 v) ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E (SST1 v) ms1 /\ frame_of E (t1_mem v) (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PB); [exact HS | apply T1_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST1. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
End a.
