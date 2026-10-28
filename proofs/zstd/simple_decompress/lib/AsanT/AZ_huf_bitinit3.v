(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_libc_iface AZ_libc AZ_huf_iface AZ_kx AZ_hufkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Ltac bi_enum3 :=
  let BCE := fresh "BCE" in
  match goal with
  | BDC : rw_cells _ _ ?B _ |- _ =>
    is_var B;
    lazymatch type of BDC with
    | context [C4 (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + ?c))] =>     (* [comment removed for export] *)
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (-1 * Z.lxor v 31 + c) mod 2^64) && ((-1 * Z.lxor v 31 + c) mod 2^64 <=? 8))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 64))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
    | context [C4 (edenot ?E ?e)] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
    end;
    cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
  end.

Section CANSEC1. Context {rc : runConstT}.
Section BI.
  (* [comment removed for export] *)
  Variables (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte).
  Hypotheses (MI : mem_inv bsegs m) (BDC : rw_cells bsegs m BD [CB 40 junk]) (BDA : BD mod 8 = 0)
             (SRCB : bytes_at bsegs m SRC src) (SRCL : zlen src = n)
             (B0 : 4096 <= BD) (B1 : BD + 40 < 2^47) (S0 : 4096 <= SRC) (S1 : SRC + n < 2^47) (N32 : n < 2^32)
             (DJ : BD + 40 <= SRC \/ SRC + n <= BD)
             (STK : stk bsegs m lo SPV) (LOS : lo <= SPV - 2224) (SPB : SPV < 2^47)
             (OSB : BD + 40 <= lo \/ SPV <= BD) (OSS : SRC + n <= lo \/ SPV <= SRC)
             (APB : app_blk BD (BD + 40)) (AROB : aro RNG m BD 40) (AHB : ahull RNG m BD 40) (AROS : aro RNG m SRC n)
             (ART : art m) (AST : astk RNG lo SPV).
  Notation GOAL := (evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa9b34) fc None m (seg_rom bsegs))).

  Lemma sbi_hi : 5 <= n <= 7 -> GOAL.
  Proof.
    intros N27.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROB as (UB & RB & RBS).
  pose proof atop_range as ATR.
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (MU : munch [(BD, BD + 40); (SPV - 2224, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof STK as STK0.
  carve_frame 16%nat STK.
    destruct AROS as (US & RS & RSS).
    (* [comment removed for export] *)
    kx_autoFA_v 8 [KAUnp BD 40; KAUnp SRC n; KAApp BD 40; KAApp (SPV - 16) 16] (@nil Z) 260%nat
         [KZRange n 5 7; KZRange BD 4096 (2^47 - 40); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
          KZRange SPV 4096 (2^47); KZAlign BD 8; KZWr BD 40; KZWr (SPV - 16) 16;
          KZDisj BD 40 SRC n; KZDisj (SPV - 16) 16 SRC n; KZDisj (SPV - 16) 16 BD 40; KZImg 0x22448 0x22460]
         [(SRC, n); (SPV - 16, 16); (BD, 40)] [(SRC, n); (SPV - 16, 16); (BD, 40)].
    all: try kx_cell_lit; try kx_z; try kx_acc RI.
    all: clear GOT RIC SHB INI LAY REAL STK0 UB US.
    all: kx_mem.
    all: zstep.
    all: try bi_enum3.
    all: kx_abs.
    all: release_frame FR STK SPV.
    all: kx_mkR_fold.
    all: (apply evtF_done; unfold bit_init_postA; repeat (lazymatch goal with |- ex _ => eexists end);
          split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact STK|]).
    all: first
      [ (* [comment removed for export] *)
        left; split; [first [reflexivity | lia]|]; split; [lia|];
        match goal with BDC' : rw_cells _ _ ?B ?cs |- _ => is_var B;
        lazymatch cs with
        | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
        | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
        end;
        split; [lia|]; split; [intros; lia|]; rewrite KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned; unfold bitd_cells, bitd_ptr;
        first [ replace (8 <=? n) with true by (symmetry; apply Z.leb_le; lia);
                replace (SRC + n - 8) with (SRC + n + -8) by lia; exact BDC'
              | replace (8 <=? n) with false by (symmetry; apply Z.leb_gt; lia); exact BDC'
              | exact BDC' ]
        end
      | (* [comment removed for export] *)
        right; split; [vm_compute; reflexivity|]; split; [reflexivity|];
        lazymatch goal with |- exists bs, rw_cells _ ?mc _ _ =>
          match goal with H : rw_cells _ mc ?B _ |- _ => is_var B; destruct (rw_cells_forget bsegs _ _ _ H) as [bs Hbs]; exists bs; exact Hbs end end ].
  Qed.
End BI.
End CANSEC1.
