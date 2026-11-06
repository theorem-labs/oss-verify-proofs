(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim StoreOk Frame AgentLib RefMemcpyLib Hoare.
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
Record apftab : Type := APFT {
  apf_entry : Z;                 (* [comment removed for export] *)
  apf_file  : Z;                 (* [comment removed for export] *)
  apf_buf   : Z;                 (* [comment removed for export] *)
  apf_rvp   : Z; apf_vp  : Z;    (* [comment removed for export] *)
  apf_rvfp  : Z; apf_vfp : Z;    (* [comment removed for export] *)
  apf_rmc   : Z; apf_mc  : Z;    (* [comment removed for export] *)
  apf_rms   : Z; apf_ms  : Z;    (* [comment removed for export] *)
  apf_init  : Z;                 (* [comment removed for export] *)
  apf_chkpf : Z;                 (* [comment removed for export] *)
  apf_sbc   : Z;                 (* [comment removed for export] *)
  apf_canc  : Z                  (* [comment removed for export] *)
}.
Definition APF_ASAN : apftab :=
  APFT 0x106ba0 0x1483c0 0x66f450 0x145138 0x1164e4 0x145140 0x111c08 0x145ac8 0x116748 0x145ad0 0x116b4c 0x14c9a0 0x1dd83c 0x14bcc0 0x66ed60.
Definition APF_BOTH : apftab :=
  APFT 0x106ba0 0x148418 0x66f490 0x145190 0x11653c 0x145198 0x111c60 0x145b20 0x1167a0 0x145b28 0x116ba4 0x14c9e0 0x1dd87c 0x14bd00 0x66eda0.

Definition APF_WIN : Z := 3328.          (* [comment removed for export] *)
Definition APF_SB  : Z := 0x7fff8000.    (* [comment removed for export] *)
Definition APF_FMT_SHW : Z := 0x7fffaaf0.
End WithFP1.
 (* [comment removed for export] *)

#[local] Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
#[local] Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Section WithFP2. Context {FP : PropExec.FPState}.
Section WithTable.
Variable SEGS : list Segment.
Variable T : apftab.

(* [comment removed for export] *)
Record apfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := APFH {
  Asp16  : bv_unsigned sp mod 16 = 0;
  AspLo  : 2 ^ 46 <= bv_unsigned sp;                      (* [comment removed for export] *)
  AspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Astk   : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - APF_WIN)) (Z.to_nat APF_WIN) = true;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Arod   : forall i, 0x10000 <= i < 0x4b000 -> mem (Z_to_bv 64 i) = None;
  Agot   : forall i, 0x143000 <= i < 0x144000 -> mem (Z_to_bv 64 i) = None;
  (* [comment removed for export] *)
  Arvp   : rdn SEGS mem (Z_to_bv 64 (apf_rvp T)) 8 = Some (W8 (apf_vp T));
  Arvfp  : rdn SEGS mem (Z_to_bv 64 (apf_rvfp T)) 8 = Some (W8 (apf_vfp T));
  Armc   : rdn SEGS mem (Z_to_bv 64 (apf_rmc T)) 8 = Some (W8 (apf_mc T));
  Arms   : rdn SEGS mem (Z_to_bv 64 (apf_rms T)) 8 = Some (W8 (apf_ms T));
  (* [comment removed for export] *)
  Ainit0 : rdn SEGS mem (Z_to_bv 64 (apf_init T)) 1 = Some [Z_to_bv 8 1];
  Ainit1 : rdn SEGS mem (Z_to_bv 64 (apf_init T + 1)) 1 = Some [Z_to_bv 8 1];
  Achkpf : rdn SEGS mem (Z_to_bv 64 (apf_chkpf T)) 1 = Some [Z_to_bv 8 1];
  Asb    : rdn SEGS mem (Z_to_bv 64 (apf_sbc T)) 8 = Some (W8 APF_SB);
  (* [comment removed for export] *)
  Aflags : rdn SEGS mem (Z_to_bv 64 (apf_file T)) 4 = Some (W4 5);
  Awend  : rdn SEGS mem (Z_to_bv 64 (apf_file T + 32)) 8 = Some (W8 (apf_buf T + 1024));
  Awpos  : rdn SEGS mem (Z_to_bv 64 (apf_file T + 40)) 8 = Some (W8 w);
  Aw     : w = apf_buf T \/ w = apf_buf T + 2 \/ w = apf_buf T + 4;     (* [comment removed for export] *)
  Absz   : rdn SEGS mem (Z_to_bv 64 (apf_file T + 96)) 8 = Some (W8 1024);
  Alock  : rdn SEGS mem (Z_to_bv 64 (apf_file T + 140)) 4 = Some (W4 0xffffffff);
  Albf   : rdn SEGS mem (Z_to_bv 64 (apf_file T + 144)) 4 = Some (W4 0xffffffff);
  (* [comment removed for export] *)
  Acan   : rdn SEGS mem (Z_to_bv 64 (apf_canc T)) 8 = Some (W8 can);
  Acan64 : 0 <= can < 2 ^ 64;
  (* [comment removed for export] *)
  AshFmt : forall g, APF_FMT_SHW <= g < APF_FMT_SHW + 8 -> mem (Z_to_bv 64 g) = Some (Z_to_bv 8 0);
  AshBuf : forall g, APF_SB + apf_buf T / 8 - 8 <= g < APF_SB + (apf_buf T + 1024) / 8 + 8 -> mem (Z_to_bv 64 g) = Some (Z_to_bv 8 0);
  AshStk : forall g, APF_SB + bv_unsigned sp / 8 - APF_WIN / 8 - 8 <= g < APF_SB + bv_unsigned sp / 8 + 8 ->
           mem (Z_to_bv 64 g) = Some (Z_to_bv 8 0) }.

(* [comment removed for export] *)
Definition apf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp ra : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps SEGS (mkst regs (Z_to_bv 64 (apf_entry T)) mem rom) (mkst regs' ra mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - APF_WIN), APF_WIN); (Z_to_bv 64 (apf_file T), 4);
                          (Z_to_bv 64 (apf_file T + 40), 8); (Z_to_bv 64 w, 2)]
    /\ rdn SEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn SEGS mem' (Z_to_bv 64 (apf_file T + 40)) 8 = Some (W8 (w + 2))
    /\ rdn SEGS mem' (Z_to_bv 64 (apf_file T)) 4 = Some (W4 5).

Definition apf_stmt : Prop :=
  forall regs mem rom (sp ra : word) (w can : Z),
    apfH mem sp w can ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = sp -> getr regs 11%bv = Z_to_bv 64 0 ->
    apf_post regs mem rom sp ra w.
End WithTable.
End WithFP2.

