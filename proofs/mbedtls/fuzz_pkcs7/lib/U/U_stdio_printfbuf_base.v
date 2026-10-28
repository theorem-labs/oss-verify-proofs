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
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_printfbuf_base () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "allregs32"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition PF_FR : Z := 1056.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 0x7e420 <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok RSEGS mem sp PF_FR;
  Pimg   : forall i, 0x10000 <= i < 0x4bcd8 -> mem (Z_to_bv 64 i) = None;      (* [comment removed for export] *)
  Pgot   : rdn RSEGS mem (Z_to_bv 64 0x4bcd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7d330));  (* [comment removed for export] *)
  Prest  : forall i, 0x4bce0 <= i < 0x4c000 -> mem (Z_to_bv 64 i) = None;
  Pflags : rdn RSEGS mem (Z_to_bv 64 0x4ce20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn RSEGS mem (Z_to_bv 64 0x4ce40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7db98));
  Pwpos  : rdn RSEGS mem (Z_to_bv 64 0x4ce48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0x7d798 <= w <= 0x7db96;
  Pbsz   : rdn RSEGS mem (Z_to_bv 64 0x4ce80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn RSEGS mem (Z_to_bv 64 0x4ceac) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn RSEGS mem (Z_to_bv 64 0x4ceb0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
  [sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.

Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
  Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).

Definition pf_sr : list expr := ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf_base ()) "(0.$1.(2.=)(0.$1.(2.+1=5?8.)(0.$1.(3.#0.)(0.$1.(3.#6.)(0.$1.(3.#7.)(0.$1.(3.#8.)(0.$1.(3.#9.)(0.$1.(3.#:.)(0.$1.(3.#;.)(0.$1.(3.#<.)(0.$1.(3.#=.)(0.$1.(2.=)(0.$1.(3.#?.)(0.$1.(3.#10.)(0.$1.(3.#11.)(0.$1.(3.#12.)(0.$1.(3.#13.)(0.$1.(3.#14.)(0.$1.(3.#15.)(0.$1.(3.#16.)(0.$1.(3.#17.)(0.$1.(3.#18.)(0.$1.(3.#19.)(0.$1.(3.#1:.)(0.$1.(3.#1;.)(0.$1.(3.#1<.)(0.$1.(3.#1=.)(0.$1.(3.#1>.)(0.$1.(3.#1?.)(0.$1.(3.#20.)(0.$1.(3.#21.)(0.$1.(3.#22.)(4.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pf_kn : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf_base ()) "(0.$5.(6.(3.#0.)+10.)(0.$5.(7.(3.#0.)+7>420.+7???????????.)(0.$5.(8.(9.(3.#0.)-420.)+420.)(0.$5.(:.+10000.+4;<=8.)(0.$5.(;.(9.(2.=)+4;<=8.)#8.(2.+7=330.))(0.$5.(:.+4;<>0.+4<000.)(0.$5.(;.(9.(2.=)+4<>20.)#4.(2.+5.))(0.$5.(;.(9.(2.=)+4<>40.)#8.(2.+7=;98.))(0.$5.(;.(9.(2.=)+4<>48.)#8.(3.#1.))(0.$5.(7.(3.#1.)+7=798.+7=;96.)(0.$5.(;.(9.(2.=)+4<>80.)#8.(2.+400.))(0.$5.(;.(9.(2.=)+4<>:<.)#4.(2.+????????.))(0.$5.(;.(9.(2.=)+4<>;0.)#4.(2.+????????.))(0.$5.(;.(9.(2.=)+7=330.)#8.(3.#2.))(0.$5.(8.(9.(2.=)+4<000.)+1000.)(0.$5.(8.(9.(3.#1.)=)+2.)(4.$5.)))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allregs32 : list reg := ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf_base ()) "(0.(<.&5.)(=.&5.=$>.)(0.(<.&5.)(=.&5.+1.$>.)(0.(<.&5.)(=.&5.+2.$>.)(0.(<.&5.)(=.&5.+3.$>.)(0.(<.&5.)(=.&5.+4.$>.)(0.(<.&5.)(=.&5.+5.$>.)(0.(<.&5.)(=.&5.+6.$>.)(0.(<.&5.)(=.&5.+7.$>.)(0.(<.&5.)(=.&5.+8.$>.)(0.(<.&5.)(=.&5.+9.$>.)(0.(<.&5.)(=.&5.+:.$>.)(0.(<.&5.)(=.&5.+;.$>.)(0.(<.&5.)(=.&5.+<.$>.)(0.(<.&5.)(=.&5.+=.$>.)(0.(<.&5.)(=.&5.+>.$>.)(0.(<.&5.)(=.&5.+?.$>.)(0.(<.&5.)(=.&5.+10.$>.)(0.(<.&5.)(=.&5.+11.$>.)(0.(<.&5.)(=.&5.+12.$>.)(0.(<.&5.)(=.&5.+13.$>.)(0.(<.&5.)(=.&5.+14.$>.)(0.(<.&5.)(=.&5.+15.$>.)(0.(<.&5.)(=.&5.+16.$>.)(0.(<.&5.)(=.&5.+17.$>.)(0.(<.&5.)(=.&5.+18.$>.)(0.(<.&5.)(=.&5.+19.$>.)(0.(<.&5.)(=.&5.+1:.$>.)(0.(<.&5.)(=.&5.+1;.$>.)(0.(<.&5.)(=.&5.+1<.$>.)(0.(<.&5.)(=.&5.+1=.$>.)(0.(<.&5.)(=.&5.+1>.$>.)(0.(<.&5.)(=.&5.+1?.$>.)(4.(<.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_idx : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf_base ()) "PE,$?.Psr,(10.$1.)PR,(11.&5.(<.&40.))P,Pi,$12.P,(13.R1.#20.)(14.(<.&40.)(15.R3.(16.(<.&5.)R2.$17.(=.&5.=$>.)))(18.R5.(16.$1.R2.R4.(2.=))))(19.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section Entry.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x1d5f8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  #[using="Type"] Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, pfE, pf_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 w; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev1 : ev E 1 = Z_to_bv 64 w. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev2 : ev E 2 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  #[using="R1 R2 R11"] Lemma pf_regs_ok : regs_ok E pf_sr regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf_sr allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  #[using="Type"] Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x4c000) 204800 = true.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Type"] Lemma data_store_ok : ltac2:(CDefT.buildp (gd_tbl_P_stdio_printfbuf_base ()) "Pm,P,(<.&40.)(1:.(<.&8.))Pa,$1;.Pn,$12.P,(1<.+4<000.R2.)P,(1<.(1=.R3.(1>.R2.))+7>000.)(14.$1?.(20.$21.R5.(22.&40.R4.)R3.)$23.)")
(* [comment removed for export] *).
  Proof.
    intros m a n Ha Hn.
    eapply (store_ok_window RSEGS m (Z_to_bv 64 0x4c000) (Z_to_bv 64 a) 204800 n 0x4c000 0x7e000);
      [ apply u64_lit; lia | reflexivity | cbn; lia | apply wseg_data
      | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia ].
  Qed.

  #[using="PH"] Lemma pf_know_ok : know_ok RSEGS E mem pf_kn.
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold pf_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1056); [apply ev0 | exact Pstk0 | unfold PF_FR; lia].
    - apply kimg_intro; [lia | lia | exact Pimg0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pgot0].
    - apply kimg_intro; [lia | lia | exact Prest0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pflags0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwend0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwpos0].
    - apply krange_intro. cbn [edenot]. rewrite ev1, u64_lit by lia. lia.
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pbsz0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plock0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plbf0].
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan0].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1, u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.
End Entry.
