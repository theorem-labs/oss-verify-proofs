(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN0b.
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
Definition regs_sv (l : list (nat * sv)) : list sv :=
map (fun i => match find (fun p => Nat.eqb (fst p) i) l with
| Some (_, v) => v
| None => if Nat.eqb i 0 then SLit 0 else SOff i 0
end) (seq 0 32).
Definition LOCK : Z := src0_D_malloc_lock.
Definition CTX : Z := src0_D_malloc_context.
Definition NLK : Z := src0_D_libc + 3.
Definition TP : Z := src0_tp.
Definition DEB : Z := src0_D_debruijn32.
Definition SCT : Z := src0_D_size_classes.
Definition MI : Z := src0_A_libc_malloc_impl.
Definition PA : Z := MI + 0x1f4.
Definition PB : Z := MI + 0x2c8.
Definition PC : Z := MI + 0x324.
Definition RA_AS : Z := MI + 0x310.
Definition FRET : Z := MI + 0x58.
Definition ASLOT : Z := src0_A_alloc_slot.
Definition ENF : Z := src0_A_enframe.
Definition cview (l : list nat) (ss : sstate) : Z * option sv * smem * list sv :=
(ss_pc ss, ss_resv ss, ss_mem ss, map (fun n => nth n (ss_regs ss) (SLit 0)) l).
Definition CSAVED : list nat := [3; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition csaved_svs : list sv := map (fun n => SOff n 0) CSAVED.
Definition R_lock : region := mkRegion None LOCK (LOCK + 4) 0 0 [mkChunk LOCK (CVal 4 (SLit 0))].
Definition R_nl : region := mkRegion None NLK (NLK + 1) 0 0 [mkChunk NLK (CVal 1 (SLit 0))].
Definition F_sp48 : afact := mkAF (CEIL_MIN + 8192 - 48) (2 ^ 63 - 49) 4.
Definition aCTR := 33%nat.
Definition aS4 := 34%nat. Definition aS3 := 35%nat. Definition aS2 := 36%nat.
Definition aS1 := 37%nat. Definition aS0 := 38%nat. Definition aRA := 39%nat.
Definition R_frame : region := mkRegion (Some aSP) 0 48 0 0
[mkChunk 0 (CVal 8 (SOff aS4 0)); mkChunk 8 (CVal 8 (SOff aS3 0)); mkChunk 16 (CVal 8 (SOff aS2 0));
mkChunk 24 (CVal 8 (SOff aS1 0)); mkChunk 32 (CVal 8 (SOff aS0 0)); mkChunk 40 (CVal 8 (SOff aRA 0))].
Definition R_ctr : region := mkRegion None (CTX + 12) (CTX + 16) 0 0 [mkChunk (CTX + 12) (CVal 4 (SOff aCTR 0))].
Definition t5_facts : facts := mkFacts [ (aSP, F_sp48); (aCTR, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
Definition t5_mem : smem := [R_frame; R_lock; R_ctr].
Definition ss_T5 : sstate := mkSS PC (regs_lit [(9%nat, LOCK); (4%nat, TP)]) t5_mem None t5_facts.
Definition SST5 : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL ENF ss_T5)) t5_facts.
Lemma T5_run_ok : run_to_ok ENF ss_T5 (fst (sym_run_toN src0segs src0tbl FUEL ENF ss_T5)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SST5_view :
cview ([1; 2; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20]%nat ++ CSAVED) SST5 =
(ENF, None, t5_mem,
[SOff aRA 0; SOff 2 48; SLit TP; SOff aS0 0; SOff aS1 0; SOff 18 0; SOff 19 0; SOff 8 0; SAlu ALU_ADD (SExt true 32 (SOff aCTR 0)) (SLit 0);
SOff aS2 0; SOff aS3 0; SOff aS4 0] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Theorem T5_run E ms md :
st_ok src0segs E ss_T5 ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST5 ms1 /\
frame_of E t5_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to ENF); [exact HS | apply T5_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST5. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
End a.
