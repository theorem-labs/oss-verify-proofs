(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxSys AxOcc AxSysDisp.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSys2 AxSysSound AxSysMmapS AxSysNorep AxSysBrk AxSysFixS AxSysFixS2 AxSysFixS3 AxSysProt AxSysUnmap.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Disp.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis KT_agree : forall ρ ρ' o, (forall x, entry_var x = true -> ρ' x = ρ x) -> KT ρ' o = KT ρ o.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).
Notation Snd B := (forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)).
Notation Goal A := (forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
                    forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o)).


Theorem sys_disp_sound (A : AST) (l : list AST) : sys_disp segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Goal A.
Proof.
  intros Hs HS. unfold sys_disp in Hs. destruct (pc_ok (npc A)) eqn:Hpc; [|discriminate Hs].
  destruct (xlit (aget (a_regs A) 17%uint63)) as [x8|] eqn:H17; [|discriminate Hs].
  destruct (Z.eq_dec x8 96) as [->|N96].
  - destruct (sys_fresh A) eqn:Efr; [|discriminate Hs].
    exact (sys_set_tid_sound segs cfg LIM fs0 KT KT_agree A l Hpc H17 (sys_fresh_spec A Efr) Hs HS).
  - destruct (Z.eq_dec x8 222) as [->|N222].
    + destruct (null_shape A) as [sh|] eqn:Esh.
      * destruct (sys_fresh A) eqn:Efr; [|discriminate Hs].
        exact (sys_mmap_null_sound segs LIM fs0 Hlow cfg Hcfg2 KT KT_agree A l Hpc H17 (sys_fresh_spec A Efr) Hs HS).
      * exact (sys_mmap_noreplace_sound segs LIM fs0 Hlow cfg Hcfg2 KT A l Hpc H17 Hs HS).
    + exfalso. destruct x8 as [|p|p]; try discriminate Hs;
        repeat (destruct p as [p|p|]; try discriminate Hs; try (exfalso; lia)).
Qed.

Theorem sys_disp2_sound (A : AST) (l : list AST) : sys_disp2 segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Goal A.
Proof.
  intros Hs HS. unfold sys_disp2 in Hs. destruct (sys_disp segs LIM A) as [l1|] eqn:E1.
  - injection Hs as <-. exact (sys_disp_sound A l1 E1 HS).
  - destruct (pc_ok (npc A)) eqn:Hpc; [|discriminate Hs].
    destruct (xlit (aget (a_regs A) 17%uint63)) as [x8|] eqn:H17; [|discriminate Hs].
    destruct (Z.eq_dec x8 222) as [->|N222].
    + destruct (sys_fix_rw LIM A) as [l2|] eqn:E2.
      * injection Hs as <-. exact (sys_fix_rw_sound segs cfg Hcfg2 LIM fs0 KT Hlow A l2 Hpc H17 E2 HS).
      * destruct (sys_fix_sh LIM A) as [l3|] eqn:E3.
        -- injection Hs as <-. exact (sys_fix_sh_sound segs cfg Hcfg2 LIM fs0 KT Hlow A l3 Hpc H17 E3 HS).
        -- exact (sys_fix_none_sound segs cfg Hcfg2 LIM fs0 KT Hlow A l Hpc H17 Hs HS).
    + destruct (Z.eq_dec x8 215) as [->|N215]; [exact (sys_munmap2_sound segs cfg LIM fs0 KT Hlow A l Hpc H17 Hs HS)|].
      destruct (Z.eq_dec x8 226) as [->|N226]; [exact (sys_mprotect2_sound segs cfg Hcfg2 LIM fs0 KT Hlow A l Hpc H17 Hs HS)|].
      destruct (Z.eq_dec x8 214) as [->|N214]; [exact (sys_brk2_sound segs cfg Hcfg2 LIM fs0 KT Hlow A l Hpc H17 Hs HS)|].
      exfalso. destruct x8 as [|p|p]; try discriminate Hs;
        repeat (destruct p as [p|p|]; try discriminate Hs; try (exfalso; lia)).
Qed.

End Disp.
