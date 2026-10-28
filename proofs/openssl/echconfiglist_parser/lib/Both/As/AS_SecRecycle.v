(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_AllocBase AW_LargeAlloc1 AW_SysconfPg AW_PoisonRemap1
     SecLazy SecLazy2 AW_GetBlockBegin AW_SecRecycle1 AW_LargeDealloc1 AW_LargeDealloc2 AW_LargeDealloc3 AS_SecRecycle1 AS_SecRecycle2 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SecRecycle.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch lst lidx TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte) (sbs : list byte) (g : word) (b244 : byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40.
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= TH \/ TH + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch <= nres <= 2^20.
  Hypothesis IDX : nth_error chunks (Z.to_nat idx) = Some a.
  Hypothesis LNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis PLCL : idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= TH \/ TH + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst)).
  Hypothesis LSTA : idx = nch - 1 -> lst = a.
  (* [comment removed for export] *)
  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks.
  Hypothesis NR : 0 <= n < 2^32.
  (* [comment removed for export] *)
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis REN : RENV g b244 m.
  Hypothesis SB32 : rw_cells asegs m 6976184 [C8 (wz sb)].
  Hypothesis INST64 : rw_cells asegs m 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 6976264 [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m 6976288 6976832.
  Hypothesis MTX : rw_cells asegs m 6976832 [C8 (wz 0)].
  Hypothesis GST : stk asegs m 6976840 6976880.
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis LSTC : idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz lidx)].
  Hypothesis CHDR : rw_cells asegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SHD : u8arr asegs m (sh a) sbs. Hypothesis SHDL : Z.of_nat (length sbs) = msz / 8.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199214) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  (* [comment removed for export] *)
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  (* [comment removed for export] *)
  Hypothesis HSNA : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_noaccess (m_vmmaps mo)) a n = true.
  (* [comment removed for export] *)
  Hypothesis WIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x S = true.
  Hypothesis HAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis NOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x L = false.
  Hypothesis NOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let LRE : 12599296 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  (* [comment removed for export] *)
  Theorem recycle_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    assert (NWL : entries_nowrap L) by (apply (lazy_ranges_okb_nowrap asegs); exact (lzok_ranges OK)).
    eapply recycle_sec_head; try eassumption. intros msF3 mo3 M3.
    (* [comment removed for export] *)
    eapply recycle_sec_poison; try eassumption. intros msF4 mo4 M4.
    eapply recycle_sec_unmap with (L := L) (S := S) (Zr := Zr); try eassumption.   (* [comment removed for export] *)
  Qed.
End SecRecycle.
