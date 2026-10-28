(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk BBFrame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive MemcpyLib AgentLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymAux PrintfLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_printfbuf_base.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_printfbuf () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.saddr"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps_cs"; "RocqVerifyHarness.AgentSubmission.BB.BBFrame.frame_mod"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_exec"; "pf_fuel"; "Corelib.Init.Datatypes.true"; "pf_stops"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCR"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SS"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_printfbuf_base.pf_sr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_printfbuf_base.pf_kn"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "RocqVerifyHarness.AgentSubmission.BB.SymAux.log_covered"; "pf_regions"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_log"; "RocqVerifyHarness.AgentSubmission.BB.SymAux.same_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_regs"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.callee_saved"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.carry"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.kread"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.scs_denot"; "pf_post"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_printfbuf_base.pfH"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"].


Definition pf_stops : list Z := [0x1d5f8].
Definition pf_fuel : nat := 3000.

(* [comment removed for export] *)
Definition pf_regions : list sregion := ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "(0.(1.$2.$3.)(4.$2.$3.(5.(6.#0.)-420.)+420.)(0.(1.$2.$3.)(4.$2.$3.(5.(7.=)+4<>20.)+4.)(0.(1.$2.$3.)(4.$2.$3.(5.(7.=)+4<>48.)+8.)(0.(1.$2.$3.)(4.$2.$3.(5.(6.#1.)=)+2.)(8.(1.$2.$3.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "(9.(:.&5.(;.&40.))Lregs',(:.&5.(;.&40.))(9.P,(;.&40.)(<.(;.&8.))Lmem',P,(;.&40.)(<.(;.&8.))(=.(>.$?.(10.$11.O5.(12.&40.+1=6:4.)O4.O3.)(10.$11.R2.(12.&40.+1=5?8.)R1.O3.))(=.(13.O5.R2.)(=.(14.O4.R1.(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.(15.(16.&40.O2.)+420.))+420.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.+4<>20.)+4.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.+4<>48.)+8.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.O1.)+2.)(8.(1.(;.&40.)$3.)))))))(=.(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.O1.)#2.)(1:.(18.(;.&8.))(0.(;.&8.)(12.&8.+30.)(0.(;.&8.)(12.&8.+:.)(8.(;.&8.))))))(=.(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.+4<>48.)#8.)(1:.(18.(;.&8.))(1;.#8.(12.&40.(1<.O1.+2.)))))(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.+4<>20.)#4.)(1:.(18.(;.&8.))(1;.#4.(12.&40.+5.)))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x1d5f8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  #[using="Type"] Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  #[using="mem PH"] Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
  Proof.
    intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
    change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
  Qed.

  #[using="PH R1 R2 R11"] Lemma pf_case : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pdirs,(18.$1=.)Pss',$1>.Pscs,(18.$1?.)Pscr',$20.Pkn',(18.$21.)Phs',(18.$1=.)P,(17.(1.(1.$1>.(18.$1?.))$20.)(22.$?.$23.$24.$25.(26.R6.(8.$27.)(8.$1=.))(28.+1=6:4.$29.(8.$2:.)$2;.#28.)(8.$1?.))(4.(1.$1>.(18.$1?.))$20.(4.$1>.(18.$1?.)R5.R4.)R3.))P,(17.$3.(2<.R6.)+1=5?8.)P,(17.$1=.(2=.$2>.(2?.R7.))$24.)P,(17.$1=.(30.$29.(31.R8.)$32.)$24.)P,(17.(1.(1.(18.$21.)(18.$1?.))(18.$1=.))(33.(2?.R9.)$2;.(8.$1=.))(4.(1.(18.$21.)(18.$1?.))(18.$1=.)(4.(18.$21.)(18.$1?.)R6.(8.$1?.))R5.))P,(17.(<.$27.)(34.$?.R7.(7.=)+4<>48.#8.)(1:.$27.(35.$36.(6.#1.)(7.+2.))))P,(17.(<.$27.)(34.$?.R8.(7.=)+4<>20.#4.)(1:.$27.(7.+5.)))P,(17.(<.$27.)(34.$?.R9.(6.#1.)=#1.)(1:.$27.(7.+30.)))P,(17.(<.$27.)(34.$?.R:.(6.#1.)+1.#1.)(1:.$27.(7.+:.)))P,(37.$?.Vmem,VE,R=.)(38.Vregs,Vmem,Vrom,Vsp,Vw,)")
(* [comment removed for export] *).
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    ddestruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x1d6a4 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
    dexists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x4ce20, 4);
               (Z_to_bv 64 0x4ce48, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) pf_regions).
      2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
    - pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_var1 in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + rewrite Z.add_0_r in B0. apply B0.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
      + rewrite u64_lit by lia. apply B1.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x4ce48 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x4ce20 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pf_run (dirs : list bool) :=
  sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x1d6a4 pf_sr [] pf_kn 40) [].

(* [comment removed for export] *)
Definition dirsA : list bool := [false; true; false; true; false].  (* [comment removed for export] *)
Definition dirsB : list bool := [true; false; true; true; true].    (* [comment removed for export] *)

Definition dirsC : list bool := [true; false; true; true; false].   (* [comment removed for export] *)
Definition dirsD : list bool := [true; false; true; false; false].  (* [comment removed for export] *)

Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

(* [comment removed for export] *)
Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.

Lemma pf_caseA : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pregs,(:.&5.(;.&40.))Pmem,P,(;.&40.)(<.(;.&8.))Prom,P,(;.&40.)(<.(;.&8.))Psp,(;.&40.)Pw,$3.Pcan,$3.P,(39.R5.R3.R2.R1.)P,(17.$3.(3:.R3.+4.)=)P,(17.(;.&40.)(3;.R8.(3<.&5.+1.$3=.))(12.&40.+1=5?8.))P,(17.(;.&40.)(3;.R9.(3<.&5.+2.$3=.))R6.)P,(17.(;.&40.)(3;.R:.(3<.&5.+;.$3=.))(12.&40.=))(38.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.

Lemma pf_caseB : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pregs,(:.&5.(;.&40.))Pmem,P,(;.&40.)(<.(;.&8.))Prom,P,(;.&40.)(<.(;.&8.))Psp,(;.&40.)Pw,$3.Pcan,$3.P,(39.R5.R3.R2.R1.)P,(17.$3.(3:.R3.+4.)+2.)P,(17.(;.&40.)(3;.R8.(3<.&5.+1.$3=.))(12.&40.+1=5?8.))P,(17.(;.&40.)(3;.R9.(3<.&5.+2.$3=.))R6.)P,(17.(;.&40.)(3;.R:.(3<.&5.+;.$3=.))(12.&40.=))(38.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.

Lemma pf_caseC : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pregs,(:.&5.(;.&40.))Pmem,P,(;.&40.)(<.(;.&8.))Prom,P,(;.&40.)(<.(;.&8.))Psp,(;.&40.)Pw,$3.Pcan,$3.P,(39.R5.R3.R2.R1.)P,(17.$3.(3:.R3.+4.)+1.)P,(17.(;.&40.)(3;.R8.(3<.&5.+1.$3=.))(12.&40.+1=5?8.))P,(17.(;.&40.)(3;.R9.(3<.&5.+2.$3=.))R6.)P,(17.(;.&40.)(3;.R:.(3<.&5.+;.$3=.))(12.&40.=))(38.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.

Lemma pf_caseD : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pregs,(:.&5.(;.&40.))Pmem,P,(;.&40.)(<.(;.&8.))Prom,P,(;.&40.)(<.(;.&8.))Psp,(;.&40.)Pw,$3.Pcan,$3.P,(39.R5.R3.R2.R1.)P,(17.$3.(3:.R3.+4.)+3.)P,(17.(;.&40.)(3;.R8.(3<.&5.+1.$3=.))(12.&40.+1=5?8.))P,(17.(;.&40.)(3;.R9.(3<.&5.+2.$3=.))R6.)P,(17.(;.&40.)(3;.R:.(3<.&5.+;.$3=.))(12.&40.=))(38.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem printf0_buffered : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf ()) "Pregs,(:.&5.(;.&40.))Pmem,P,(;.&40.)(<.(;.&8.))Prom,P,(;.&40.)(<.(;.&8.))Psp,(;.&40.)Pw,$3.Pcan,$3.P,(39.R5.R3.R2.R1.)P,(17.(;.&40.)(3;.R7.(3<.&5.+1.$3=.))(12.&40.+1=5?8.))P,(17.(;.&40.)(3;.R8.(3<.&5.+2.$3=.))R5.)P,(17.(;.&40.)(3;.R9.(3<.&5.+;.$3=.))(12.&40.=))(9.(:.&5.(;.&40.))Lregs',(:.&5.(;.&40.))(9.P,(;.&40.)(<.(;.&8.))Lmem',P,(;.&40.)(<.(;.&8.))(=.(>.$?.(10.$11.R<.(12.&40.+1=6:4.)R;.R:.)(10.$11.R2.(12.&40.+1=5?8.)R1.R:.))(=.(13.R<.R2.)(=.(14.R;.R1.(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.(15.(16.&40.R9.)+420.))+420.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.+4<>20.)+4.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.+4<>48.)+8.)(0.(1.(;.&40.)$3.)(4.(;.&40.)$3.(12.&40.R8.)+2.)(8.(1.(;.&40.)$3.)))))))(=.(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.R8.)#2.)(1:.(18.(;.&8.))(0.(;.&8.)(12.&8.+30.)(0.(;.&8.)(12.&8.+:.)(8.(;.&8.))))))(=.(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.+4<>48.)#8.)(1:.(18.(;.&8.))(1;.#8.(12.&40.(1<.R8.+2.)))))(17.(<.(18.(;.&8.)))(19.$?.R1.(12.&40.+4<>20.)#4.)(1:.(18.(;.&8.))(1;.#4.(12.&40.+5.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.

