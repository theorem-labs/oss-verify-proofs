(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ESA.
Definition GOT_LO : Z := 0x1644b8.  Definition GOT_HI : Z := 0x165350.  Definition SHVAR : Z := 0x16d7b8.  Definition SBz : Z := 0x7fff8000.
Definition STATICS : list kentry := [KImg GOT_LO GOT_HI; KWord (SA (ELit 0) SHVAR) 8 (ELit SBz)].

(* [comment removed for export] *)
Definition sink_xsumA (pc scr : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => let '(ob, ok) := split_lit (nth 10 regs (ELit 0)) in [(ob, ok, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition sinkret_xsumA (pc scr : Z) (s2e : expr) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 1%nat
    (fun _ g => Some (EVar g))
    (fun regs => [(s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (KRange (EVar g) 0 1125899906842624 :: STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition wd_xsumA (pc scr : Z) (s2e : expr) (errno : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit 0))
    (fun regs => [(s2e, 0, ELit 24); (ELit 0, errno, ELit 4)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition cp_xsumA (pc scr : Z) (breg : nat) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun regs _ => Some (APC.eaddz (nth 10 regs (ELit 0)) 1))
    (fun regs => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in [(ob, ok, ELit 8)])
    (fun regs BL => BL)
    (fun regs cells g BLk => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in
       (KWord (SA ob ok) 4 (nth breg regs (ELit 0)) :: KRange (EVar (g + 5)) 0 0 :: STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition tail_xsumA (pc scr : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat (fun _ _ => None) (fun _ => []) (fun regs BL => BL) (fun regs cells g BLk => ([], BLk)) (fun F => F)) (fun _ => []).

(* [comment removed for export] *)
Definition col_region (regs : list expr) : SGP.region := let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (vb, vk + 296, ELit 8).
Definition hcall_xsumA (pc scr : Z) (s2e : expr) (blk : CA.blocks) (news : list expr -> list kentry -> list kentry) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => [col_region regs; (s2e, 0, ELit 24)])
    (fun regs BL => [])
    (fun regs cells g BLk => (STATICS ++ news regs cells, blk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition hcol_xsumA (pc scr : Z) (s2e : expr) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => [col_region regs; (s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition lit_news (S TXT LEN : Z) : list kentry :=
  [KWord (SA (ELit 0) (S + 16)) 1 (ELit 1); KWord (SA (ELit 0) (S + 17)) 1 (ELit 1); KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)].
Definition lit_xsumA (pc scr S TXT LEN : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit TXT))
    (fun regs => [(ELit 0, S, ELit 18)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (KRange (EVar (g + 5)) LEN LEN :: lit_news S TXT LEN ++ STATICS, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition guard_news (gb : expr) (gk : Z) (b0 b1 : Z) : list kentry := [KWord (SA gb gk) 1 (ELit b0); KWord (SA gb (gk + 1)) 1 (ELit b1)].
Definition guard_acq_xsumA (pc scr : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit 1))
    (fun regs => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in [(gb, gk, ELit 2)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in (guard_news gb gk 0 2, BLk))
    (fun F => F)) (fun _ => []).
Definition guard_rel_xsumA (pc scr : Z) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in [(gb, gk, ELit 2)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in (guard_news gb gk 1 1, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition sinkn_xsumA (pc scr : Z) (news : list expr -> list kentry -> list kentry) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => let '(ob, ok) := split_lit (nth 10 regs (ELit 0)) in [(ob, ok, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (STATICS ++ news regs cells, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition sinkretn_xsumA (pc scr : Z) (s2e : expr) (news : list expr -> list kentry -> list kentry) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 1%nat
    (fun _ g => Some (EVar g))
    (fun regs => [(s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (KRange (EVar g) 0 1125899906842624 :: STATICS ++ news regs cells, BLk))
    (fun F => F)) (fun _ => []).
Definition litn_xsumA (pc scr S TXT LEN : Z) (news : list expr -> list kentry -> list kentry) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit TXT))
    (fun regs => [(ELit 0, S, ELit 18)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (KRange (EVar (g + 5)) LEN LEN :: lit_news S TXT LEN ++ STATICS ++ news regs cells, BLk))
    (fun F => F)) (fun _ => []).
End ESA.
