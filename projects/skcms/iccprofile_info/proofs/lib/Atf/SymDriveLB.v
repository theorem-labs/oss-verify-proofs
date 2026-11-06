(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec PropExecFP SymExecFP SymExecFPSound SymRunFP SymDriveFP.
Unset Lia Cache.
Import ListNotations.
Import SXF. Import SXFS.

Ltac run_fp_with_h_lb HR HF HK fuel stops scr chints keep extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr (@fp_regs ?FPI) =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst FPI R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval cbn in (length VALS) in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr sfr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn chints) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let pc' := eval cbv [s_pc] in (s_pc ss') in
            let sr' := eval cbv [s_regs] in (s_regs ss') in
            let sfr' := eval cbv [s_fregs] in (s_fregs ss') in
            let log' := eval cbv [s_log] in (s_log ss') in
            let SR0 := fresh "SR0" in let SFR0 := fresh "SFR0" in let KN0 := fresh "KN0" in
            let SSX := fresh "SSX" in let KNX := fresh "KNX" in
            pose (SR0 := sr); pose (SFR0 := sfr); pose (KN0 := kn);
            pose (SSX := ss'); pose (KNX := kn');
            eapply (rt_run segs fuel stops scr chints pc SR0 SFR0 KN0 NX SSX scs scr' KNX scs2 hs2 E M rom R FPI Q);
            [ vm_cast_no_check (@eq_refl _ (SSX, scs, scr'))
            | vm_cast_no_check (@eq_refl _ (KNX, scs2, hs2))
            | exact HR | exact HF | exact HK
            | clear SR0 SFR0 KN0 SSX KNX; split_foralls; sc_auto_fp extra
            | clear SR0 SFR0 KN0 SSX KNX; split_foralls; sc_auto_fp extra
            | clear HR HF HK;
              let R' := fresh "R" in let FPI' := fresh "FPI" in
              let M' := fresh "M" in let EQM := fresh "EQM" in let HLF := fresh "HLF" in
              intros R' FPI' M' HR HF HK EQM HLF;
              change (regs_ok E sr' R') in HR;
              change (fregs_ok E sfr' (@fp_regs FPI')) in HF;
              change (know_ok segs E M' kn') in HK;
              change (M' = mem_denot E M log') in EQM;
              change (log_flat E log') in HLF;
              change (runs_to segs (@mkst FPI' R' (Z_to_bv 64 pc') M' rom) Q);
              clear SR0 SFR0 KN0 SSX KNX;
              try change (mem_denot E M []) with M in EQM;
              lazymatch keep with
              | true => idtac
              | false => clear HLF; subst M'; readable_fwd;
                         try clear R; try clear FPI;
                         try rename R' into R; try rename FPI' into FPI
              end ]
          end
        end)
      end
     end
   end
  end.
