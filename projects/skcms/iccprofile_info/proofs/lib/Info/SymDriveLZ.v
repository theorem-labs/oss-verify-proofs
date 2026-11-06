(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP PerfNats.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.


(* [comment removed for export] *)
Theorem rt_run2 : forall segs fuel stops scr (chints : list bool) pc sr sfr kn nx ss' scs scr' kn' scs2 hs2
                        E M rom R (FPI : FPState) Q,
  (let r := sym_exec segs fuel true stops scr (SS pc sr sfr [] kn nx) [] in (r, carry (s_log (fst (fst r))) kn chints))
    = ((ss', scs, scr'), (kn', scs2, hs2)) ->
  regs_ok E sr R -> fregs_ok E sfr fp_regs -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  (forall R' (FPI' : FPState) M',
     regs_ok E (s_regs ss') R' -> fregs_ok E (s_fregs ss') (fp_regs (FPState:=FPI')) ->
     know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     log_flat E (s_log ss') ->
     runs_to segs (mkst (FP:=FPI') R' (Z_to_bv 64 (s_pc ss')) M' rom) Q) ->
  runs_to segs (mkst (FP:=FPI) R (Z_to_bv 64 pc) M rom) Q.
Proof.
  intros segs fuel stops scr chints pc sr sfr kn nx ss' scs scr' kn' scs2 hs2 E M rom R FPI Q H.
  cbv zeta in H. injection H as H1 H2.
  rewrite H1 in H2. cbn [fst] in H2.
  exact (rt_run segs fuel stops scr chints pc sr sfr kn nx ss' scs scr' kn' scs2 hs2 E M rom R FPI Q H1 H2).
Qed.

(* [comment removed for export] *)
Ltac ev_simpl_lz E :=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Ltac ev_simpl_in_lz E H := try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.

Ltac run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr (@fp_regs ?FPI) =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst FPI R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval lazy in (length VALS) in
        let fN := eval vm_compute in (N.of_nat fuel) in
        let fuelB := constr:(N.to_nat fN) in
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
            (* [comment removed for export] *)
            (* [comment removed for export] *)
            binarize_k constr:((sr, sfr, kn, ss', kn')) ltac:(fun T =>
              lazymatch T with (?srB, ?sfrB, ?knB, ?ssB, ?knxB) =>
                pose (SR0 := srB); pose (SFR0 := sfrB); pose (KN0 := knB);
                lazymatch ssB with
                | SS ?pcx ?srx ?sfrx ?logx _ ?nxx => pose (SSX := SS pcx srx sfrx logx KN0 nxx)
                end;
                pose (KNX := knxB) end);
            eapply (rt_run2 segs fuelB stops scr chints pc SR0 SFR0 KN0 NX SSX scs scr' KNX scs2 hs2 E M rom R FPI Q);
            [ vm_cast_no_check (@eq_refl _ ((SSX, scs, scr'), (KNX, scs2, hs2)))
            | exact HR | exact HF | exact HK
            | clear SR0 SFR0 KN0 SSX KNX; split_foralls; sc_auto_fp extra
            | clear SR0 SFR0 KN0 SSX KNX; split_foralls; sc_auto_fp extra
            | clear HR HF HK;
              let R' := fresh "R" in let FPI' := fresh "FPI" in
              let M' := fresh "M" in let EQM := fresh "EQM" in let HLF := fresh "HLF" in
              intros R' FPI' M' HR HF HK EQM HLF;
              (* [comment removed for export] *)
              lazymatch eval cbv delta [SSX] in SSX with
              | SS _ ?srx ?sfrx _ _ _ =>
              change (regs_ok E srx R') in HR;
              change (fregs_ok E sfrx (@fp_regs FPI')) in HF;
              change (know_ok segs E M' KNX) in HK;
              change (M' = mem_denot E M log') in EQM;     (* [comment removed for export] *)
              change (log_flat E log') in HLF
              end;
              change (runs_to segs (@mkst FPI' R' (Z_to_bv 64 pc') M' rom) Q);
              clear SR0 SFR0 SSX; clear KN0; (lazymatch kn with ?v => tryif is_var v then try clear v else idtac end);
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

Ltac branch_case_with_lz HR HF HK Hc :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr _ =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst _ R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval lazy in (length VALS) in
        let r := eval vm_compute in (sym_exec segs 1%nat true (@nil Z) (dirs [true]) (SS pc sr sfr [] kn NX) []) in
        lazymatch r with
        | (_, [SCBr true ?c ?a ?b], _) =>
            destruct (branch_taken c (edenot E a) (edenot E b)) eqn:Hc;
            [ run_fp_with HR HF HK 1%nat (@nil Z) (dirs [true]) false fail
            | run_fp_with HR HF HK 1%nat (@nil Z) (dirs [false]) false fail ]
        | _ => fail "branch_case: no undecided branch at this pc"
        end)
      end
     end
   end
  end.
