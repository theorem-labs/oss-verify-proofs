(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2f.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2f.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK00 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09 YL02 YL04.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1y_w AD2h_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Export ACeg_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_INITFLAG : Z := 0x5d35d0.
Definition R161 : YP09.region := YP09.mkRegion (Some 161%nat) 0 4 0 0 [mkChunk 0 (CData 3 0 4)].
Definition RBh (h : Z) : YP09.region := YP09.mkRegion (Some A_BUF) 0 h 0 0 [mkChunk 0 (CData 2 0 h)].
Definition fact_P : afact := mkAF 4098 140737479966720 0.
Definition S_Pm : sstate := Eval vm_compute in mkSS (ss_pc S_P) (ss_regs S_P) (removelast (ss_mem S_P)) None (ss_facts S_P).
Definition ssP (h : Z) : sstate :=
mkSS (ss_pc S_P) (sr_set (ss_regs S_P) 10%bv (SOff 161 0))
(ss_mem S_Pm ++ [RBh h; R161]) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_P)) (f_conds (ss_facts S_P)) (f_alias (ss_facts S_P))).
Definition ssP1 : sstate := Eval vm_compute in (ssP 3).
Definition sB1 : sstate := Eval vm_compute in (run_lp ssP1).
Definition clip_chunk (lo hi : Z) (c : YP09.chunk) : list YP09.chunk :=
let a := YP09.c_off c in let l := c_len c in
let a' := Z.max a lo in let b' := Z.min (a + l) hi in
if b' <=? a' then [] else
match YP09.c_val c with
| CImg _ => [mkChunk a' (CImg (b' - a'))]
| CZero _ => [mkChunk a' (CZero (b' - a'))]
| CVal w v => if ((lo <=? a) && (a + l <=? hi))%bool then [c] else []
| CData d s _ => [mkChunk a' (CData d (s + (a' - a)) (b' - a'))]
end.
Definition clip_region (lo hi : Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (r_base r) (Z.max (r_lo r) lo) (Z.min (r_hi r) hi)
(if (r_whi r <=? r_wlo r)%bool then 0 else Z.max (r_wlo r) lo) (if (r_whi r <=? r_wlo r)%bool then 0 else Z.min (r_whi r) hi)
(flat_map (clip_chunk lo hi) (r_chunks r)).
Definition STDOUT_LO : Z := 0x9d568.  Definition STDOUT_HI : Z := 0x9d650.
Definition SOBUF_LO : Z := 0x5f4618.   Definition SOBUF_HI : Z := 0x5f4a28.
Definition IMG_B : smem := firstn 35 (skipn 3 (ss_mem sB1)).
Definition clip_out (lo hi : Z) (r : YP09.region) : list YP09.region :=
if ((hi <=? r_lo r) || (r_hi r <=? lo))%bool then [r] else
(if (r_lo r <? lo)%bool then [clip_region (r_lo r) lo r] else []) ++ (if (hi <? r_hi r)%bool then [clip_region hi (r_hi r) r] else []).
Definition IMG_L : smem := Eval vm_compute in flat_map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_B.
