(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/FGsN.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 ac22d4526363) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 11 image addresses moved by code-verified function pairs (11 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 19 pcs named in comments; 1 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk; a Theorem Labs lane approval 01:19Z): an ADDITIVE copy of
   FGs.v for tfib_efa_spec_lk (FGtN.v): EnsureFreeArraySpace's walk with the region info's LOCK WORD (RG+0) carried as a literal
   chunk.  The ONLY semantic change against FGs.v is noted at its site; everything else is FGs.v with FGs/FGk/FGw/FGc/FGt renamed to
   their N copies.  Why: ReturnToAllocator re-reads RG+0 after the call (0x34920, the unlock), and the original leaf frames the callee by
   all of RG..RG+128, so the value was lost.  rule 24: proves function __sanitizer::SizeClassAllocator64::EnsureFreeArraySpace
   (re-walk of the released FG* walk with one more invariant chunk); reuse search `proof-index ReturnToAllocator EnsureFreeArraySpace
   0x348d0 0x3476c` 2026-10-30T01:1xZ exit 4: no released contract of EnsureFreeArraySpace that keeps RG+0 (the released
   YFgz.segK2 walks ReturnToAllocator's tail only on the no-growth arm). *)
(* The symbolic states of EnsureFreeArraySpace (0x34a94) entered from ReturnToAllocator (the jal at 0x348cc, return
   pc 0x348d0), with the caller's frame abstract.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFk9.v (the released growth walk R3_De3 .. R3_FGe3, entered from
   PopulateFreeArray) by re-basing it on EnsureFreeArraySpace's own entry: the seed SSF is at 0x34a94, atom 2 is
   EnsureFreeArraySpace's entry sp, atom 1 its return pc, and the arguments are this = A_ALLOCATOR (a0), the region
   info of the class (a1 = rRG), the region begin (a2 = rRB) and the requested count (a3 = rNFe).  The atoms and the
   tail regions are YFk6.REG0R3's (the same skeleton, so YFk5's at_R3 machinery and YFkn.node3 apply); the chunks
   the walk does not read are dropped (the per-class cache cells of region 35, the refill's region-info and thread
   words of regions 33 and 36), the region info keeps its mapped_free_array word (RGv + 24 = rMF). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFhy AFhz AFkp AFk6 AFk8 AFk9.
Import ListNotations. Open Scope Z_scope.

(* EnsureFreeArraySpace's entry, its return, and its caller's return address (ReturnToAllocator 0x348d0). *)
Definition A_EFA : Z := 0x34a94.
Definition A_EFA_RET : Z := 0x34b94.
Definition A_RTA_EFA : Z := 0x348d0.

(* The entry registers: this, the region info, the region begin, the count. *)
Definition REGSF : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit A_ALLOCATOR)) 11%bv (SOff rRG 0))
  12%bv (SOff rRB 0)) 13%bv (SOff rNFe 0).
(* N: the caller's stats word T+2784 (CacheDealloc's amoadd target) rides the walk in the refill's spare junk atom rJSM. *)
Definition R_TJF : YP09.region := YP09.mkRegion (Some rT) 2768 2800 2768 2800 [YP09.mkChunk 2784 (CVal 8 (SOff rJSM 0))].
(* N: the per-class cache header the caller re-reads after the call (CacheDealloc 0x343f4 lw a4, 0(s0); 0x34290 ld a1, 8(s0)):
   the count (= n after Drain's store) and the class size, in the atoms rN / rCSZ. *)
Definition R_PF : YP09.region := YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SOff rN 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))].
(* N: the region info carries its lock word as a literal chunk: RG+0 = 2^60, the word ReturnToAllocator's lock acquire leaves
   (0x347fc ld a3, 0(s0) = 0 at the cut; 0x34808 s11 := 1 << 60; 0x34820 or a4, a3, s11; 0x34824 and a5, a1, a4 with a1 = -1;
   0x34828 lr.d / 0x34830 sc.d a5 -> RG+0 = 0 | 2^60).  EnsureFreeArraySpace never stores to RG+0 (its one region store is
   0x34b70 sd s0, 0x18(a1) = RG+24), so the chunk rides the whole walk. *)
Definition LOCKV : Z := 2 ^ 60.
(* N: also RG+80 (ReturnToAllocator 0x348fc ld a0, 0x50(s0)) and RG+88 (read by its callee at 0x34c14), in the spare junk
   atoms rJNA / rJNF, and every CELL of the region record (YG0n.region_cells: +8 = 0, +16 = the free count nf, +32 = the
   allocated user size au, +40 = 0, +48 = the mapped user size mu, +56 = 0; the byte +68 is the class's exhausted flag at cf, left to the frame), so the caller can re-establish
   the region's cells after the call (CfF2b 03:57Z). *)
Definition R_RGF : YP09.region := YP09.mkRegion (Some rRG) 0 128 0 128
  [YP09.mkChunk 0 (CVal 8 (SLit LOCKV)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SOff rNF 0));
   YP09.mkChunk 24 (CVal 8 (SOff rMF 0)); YP09.mkChunk 32 (CVal 8 (SOff rAU 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
   YP09.mkChunk 48 (CVal 8 (SOff rMU 0)); YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 68 (CVal 1 (SOff rJ64 0));
   YP09.mkChunk 80 (CVal 8 (SOff rJNA 0)); YP09.mkChunk 88 (CVal 8 (SOff rJNF 0))].
Definition TAILF : smem := firstn 32 (tl REG0R3) ++ [R_TJF; nth 34 REG0R3 R_TJF; R_PF; R_RGF] ++ skipn 37 REG0R3.
Definition REG0F : smem := YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 [] :: TAILF.
Definition SSF : sstate := mkSS A_EFA REGSF REG0F None FR3.

Lemma TAILF_skel : skeleton TAILF = skeleton (tl REG0R3).
Proof. vm_compute. reflexivity. Qed.

(* The arm 4 * need <= mapped (no growth): straight to the return. *)
Definition F_D : sstate := Eval vm_compute in runto 0x34ab8 SSF.
Definition F_RN : sstate := Eval vm_compute in runto 0x7ffffff0 (arm BC_GEU true (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) F_D).
(* The growth arm: the round-up, the capacity check, the map call, the mmap ecall. *)
Definition F_1 : sstate := Eval vm_compute in pin (runto 0x34ad0 (arm BC_GEU false (SOff rMF 0) (SAlu ALU_SLL (SOff rNFe 0) (SLit 2)) F_D)) 8%bv (SOff rMF2 0).
Definition F_2 : sstate := Eval vm_compute in pin (runto 0x34af0 (arm BC_GEU false (SOff rMF2 0) (SLit 536870913) (runto 0x34ad8 F_1))) 9%bv (SOff rFADR 0).
Definition F_3 : sstate := Eval vm_compute in pin (runto 0x34b20 F_2) 18%bv (SLit 262144).
Definition F_4 : sstate := Eval vm_compute in runto 0x6ff14 F_3.
Definition F_N : sstate := Eval vm_compute in runtoC 0x7ffffff0 F_4.
(* The granted answer: back through the map wrapper to EnsureFreeArraySpace, the shadow fill, the stats, the return. *)
Definition F_Ng : sstate := Eval vm_compute in setpc (pin F_N 10%bv (SOff rFADR 0)) 0x65a0c.
Definition F_G1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 F_Ng.
Definition F_G2 : sstate := Eval vm_compute in runto 0x7ffffff0 F_G1.
Definition F_MS : sstate := Eval vm_compute in pin (pin F_G2 10%bv (SOff rSHF 0)) 12%bv (SLit 32768).
Definition F_G3 : sstate := Eval vm_compute in ss_after_stretch F_MS (ss_mem F_MS) hMSF CLOB_MS 0x34b50.
Definition F_RG : sstate := Eval vm_compute in runto 0x7ffffff0 F_G3.

