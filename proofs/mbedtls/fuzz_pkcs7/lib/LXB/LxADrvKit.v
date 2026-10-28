(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymExec2 SymExec2Sound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_fwrite_err1 A_tail_lib.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxADrvKit () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "log_in_b"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ev"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_fwrite_err1.log_out"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"].


(* [comment removed for export] *)
Definition ent_in_b (spi : nat) (slo shi flo fhi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ =>
      let n := Z.of_nat w in
      match b with
      | EVar i => Nat.eqb i spi && Z.leb slo k && Z.leb (k + n) shi && Z.ltb 0 n
      | ELit z => Z.eqb z 0 && Z.leb flo k && Z.leb (k + n) fhi && Z.ltb 0 n
      | _ => false
      end
  end.
Definition log_in_b (spi : nat) (slo shi flo fhi : Z) (log : list sentry) : bool := forallb (ent_in_b spi slo shi flo fhi) log.

Lemma log_in_out : ltac2:(CDefT.buildp (gd_tbl_LxADrvKit ()) "PE,$0.Pspi,$1.Pslo,$2.Pshi,$2.Pflo,$2.Pfhi,$2.Plog,(3.$4.)Px,(5.&40.)P,(6.$7.(8.R7.R6.R5.R4.R3.R2.)$9.)P,(:.=(;.(<.&40.(=.R9.R8.))R7.))P,(:.(;.(<.&40.(=.R:.R9.))R7.)(>.+2.+40.))P,(:.=R7.)P,(:.R7.(>.+2.+40.))P,(?.(10.(:.(;.(<.&40.(=.R=.R<.))R;.)(<.&40.R6.))(11.(<.&40.R6.)(;.(<.&40.(=.R=.R<.))R:.))))P,(?.(10.(:.R:.(<.&40.R7.))(11.(<.&40.R7.)R9.)))(12.R?.R8.R9.)")
(* [comment removed for export] *).
Proof.
  intros E spi slo shi flo fhi log x H B1 B2 B3 B4 NS NF.
  induction log as [|[[b k] w v] rest IH]; [exact I|].
  cbn [log_in_b forallb] in H. apply andb_prop in H as [He Hrest]. specialize (IH Hrest).
  cbn [log_out]. unfold adenot. cbn [a_base a_off]. unfold v_addi.
  cbn [ent_in_b] in He. destruct b as [z|i| | | | | |]; try discriminate.
  - (* [comment removed for export] *)
    repeat (apply andb_prop in He; destruct He as [He ?]). apply Z.eqb_eq in He. subst z.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
    cbn [edenot]. rewrite (u_small 0) by lia. rewrite u_small by lia. split; [lia|]. split; [lia| exact IH].
  - (* [comment removed for export] *)
    repeat (apply andb_prop in He; destruct He as [He ?]). apply Nat.eqb_eq in He. subst i.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
    cbn [edenot]. pose proof (u64_range (ev E spi)). rewrite u_small by lia. split; [lia|]. split; [lia| exact IH].
Qed.

(* [comment removed for export] *)
Lemma AGR_blockb : ltac2:(CDefT.buildp (gd_tbl_LxADrvKit ()) "PD,P,(5.&40.)$7.PE,$0.PM,P,(5.&40.)(13.(5.&8.))Plo,$2.Phi,$2.PMk,P,(5.&40.)(13.(5.&8.))PM',P,(5.&40.)(13.(5.&8.))Plog,(3.$4.)Pspi,$1.Pslo,$2.Pshi,$2.Pspv,(5.&40.)P,(14.R:.R9.R8.R7.)P,(6.P,(5.&40.)(13.(5.&8.))(15.R=.R7.)(16.R<.(15.R=.R8.)R6.))P,Pa,(5.&40.)P,(6.$7.A1.R?.R1.$17.)(6.(13.(5.&8.))A1.R:.R2.A1.R;.R2.)P,(6.(5.&40.)(=.R>.R7.)R4.)P,(6.$7.(8.R8.R7.R6.+?:488.+?:570.R9.)$9.)P,(:.R>.(;.(<.&40.R6.)R8.))P,(:.(;.(<.&40.R7.)R8.)R>.)P,(:.=R10.)P,(:.R10.(>.+2.+40.))(14.R13.R12.R11.R?.)")
(* [comment removed for export] *).
Proof.
  intros D E M lo hi Mk M' log spi slo shi spv AG EQM OUT EV LI B1 B2 B3 B4. subst spv.
  eapply AGR_block; [exact AG| exact EQM| exact OUT|].
  intros x _ [O1 O2]. eapply (log_in_out E spi slo shi 0x0fa488 0x0fa570); [exact LI| lia| lia| lia| lia| lia| exact O2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow Restrict RestrictLib RestrictRun SymDriveA SymDriveAX.

Ltac run_blockA2_with RRUN HR HK fuel stops scr NX keep covtac :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizesJ _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let xss := fresh "bk_ss" in let xscs := fresh "bk_scs" in let xscr := fresh "bk_scr" in
            let xkn := fresh "bk_kn" in let xscs2 := fresh "bk_scs2" in let xhs := fresh "bk_hs" in
            pose (xss := ss'); pose (xscs := scs); pose (xscr := scr'); pose (xkn := kn'); pose (xscs2 := scs2); pose (xhs := hs2);
            eapply (RRUN fuel stops scr pc sr kn NX xss xscs xscr xkn xscs2 xhs E M R model T);
            [ vm_cast_no_check (@eq_refl _ (xss, xscs, xscr))
            | vm_cast_no_check (@eq_refl _ (xkn, xscs2, xhs))
            | exact HR | exact HK
            | try (solve_kn_inD covtac)
            | cbv delta [xkn]; try (solve_kn_inD covtac)
            | cbv delta [xscs]; split_foralls
            | cbv delta [xscs2]; split_foralls
            | try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in let OUT := fresh "OUT" in
              let mo' := fresh "mo" in let HKM := fresh "HKmo" in let MM := fresh "MM" in
              intros R' M' mo' HR HK EQM OUT HKM MM; cbv delta [xss xkn] in HR, HK, EQM |- *;
              cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_blockA2" constr(RRUN) constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) tactic3(covtac) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_blockA2_with RRUN HR HK fuel stops scr NX keep covtac
  end.
