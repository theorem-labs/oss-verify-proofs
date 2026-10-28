(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SumsLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Sums_code.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanIMemcpy () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.memk"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "imemcpy_clob"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.cpyH"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "asan_imemcpy_entry"].


(* [comment removed for export] *)
Definition imemcpy_words : list (bv 32) :=
  [W_7a478; W_7a47c; W_7a480; W_7a484; W_7a488; W_7a48c; W_7a490; W_7a494; W_7a498].

(* [comment removed for export] *)
Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemcpy_words.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemcpy_clob).
  Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  #[using="HCODE HOK Hnwd"] Lemma imemcpy_loop : ltac2:(CDefT.buildp (gd_tbl_AsanIMemcpy ()) "Pi,$0.Pregs,(1.&5.(2.&40.))Pret,(2.&40.)Pk,$3.P,(4.R2.)P,(5.(2.&40.)(6.R4.(7.&5.+1.$8.))R3.)P,(5.(2.&40.)(6.R5.(7.&5.+;.$8.))(9.Vsrc,R3.))P,(5.(2.&40.)(6.R6.(7.&5.+=.$8.))(9.Vdst,R4.))P,(5.(2.&40.)(6.R7.(7.&5.+<.$8.))(9.Vdst,Vn,))P,(:.(;.=R6.)(<.R6.Vn,))P,(5.$3.(=.R:.)(>.(>.Vn,+1.)R7.))(?.(1.&5.(2.&40.))Lregs',(1.&5.(2.&40.))(:.(10.Vsegs,(11.$12.R;.(9.Vbase,+<.)(13.Vmem0,Vdst,Vbs,R9.)Vrom,)(11.$12.R1.R:.(13.Vmem0,Vdst,Vbs,Vn,)Vrom,))(14.Lr,(2.&5.)(15.(2.&5.)R1.$16.)R;.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      eexists. split.
      + mlbu C12 D_7a484 k.                       (* [comment removed for export] *)
        msb C16 D_7a488 k.                        (* [comment removed for export] *)
        an C20 D_7a48c.                           (* [comment removed for export] *)
        an C24 D_7a490.                           (* [comment removed for export] *)
        ab_ft C28 D_7a494 ltac:(condz).           (* [comment removed for export] *)
        aret C32 D_7a498 ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemcpy_clob. solve_regs_agree.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C12 D_7a484 k.
          msb C16 D_7a488 k.
          an C20 D_7a48c.
          an C24 D_7a490.
          ab_tk C28 D_7a494 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="HCODE HOK Hn0 Hnws Hnwd"] Theorem imemcpy_run : ltac2:(CDefT.buildp (gd_tbl_AsanIMemcpy ()) "Pregs,(1.&5.(2.&40.))Pret,(2.&40.)P,(4.R1.)P,(5.(2.&40.)(6.R3.(7.&5.+1.$8.))R2.)P,(5.(2.&40.)(6.R4.(7.&5.+:.$8.))Vdst,)P,(5.(2.&40.)(6.R5.(7.&5.+;.$8.))Vsrc,)P,(5.(2.&40.)(6.R6.(7.&5.+<.$8.))(17.&40.Vn,))(?.(1.&5.(2.&40.))Lregs',(1.&5.(2.&40.))(:.(10.Vsegs,(11.$12.R8.(9.Vbase,=)Vmem0,Vrom,)(11.$12.R1.R7.(18.Vmem0,Vdst,Vbs,)Vrom,))(14.Lr,(2.&5.)(15.(2.&5.)R1.$16.)R8.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    - (* [comment removed for export] *)
      eexists. split.
      + ab_tk C0 D_7a478 ltac:(condz).            (* [comment removed for export] *)
        aret C32 D_7a498 ret.
        rewrite Hz. apply mst_refl.
      + apply regs_agree_refl.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C0 D_7a478 ltac:(condz).          (* [comment removed for export] *)
          av C4 D_7a47c (at_ dst n) ltac:(apply v_add_at; lia).  (* [comment removed for export] *)
          an C8 D_7a480.                          (* [comment removed for export] *)
          apply mst_refl.
        * post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_imemcpy_entry : word := 0x7a9dc.

Lemma asan_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments asan_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : ltac2:(CDefT.buildp (gd_tbl_AsanIMemcpy ()) "Pmem0,P,(2.&40.)(19.(2.&8.))Pdst,(2.&40.)Psrc,(2.&40.)Pn,$3.Pbs,(1:.(2.&8.))Prom,P,(2.&40.)(19.(2.&8.))Pregs,(1.&5.(2.&40.))Pret,(2.&40.)P,(1;.$1<.R8.R7.R6.R5.R4.)P,(4.R2.)P,(5.(2.&40.)(6.R4.(7.&5.+1.$8.))R3.)P,(5.(2.&40.)(6.R5.(7.&5.+:.$8.))R:.)P,(5.(2.&40.)(6.R6.(7.&5.+;.$8.))R:.)P,(5.(2.&40.)(6.R7.(7.&5.+<.$8.))(17.&40.R:.))(?.(1.&5.(2.&40.))Lregs',(1.&5.(2.&40.))(:.(10.$1<.(11.$12.R9.$1=.R?.R:.)(11.$12.R1.R8.(18.R?.R>.R;.)R:.))(14.Lr,(2.&5.)(15.(2.&5.)R1.$16.)R9.R1.)))")
(* [comment removed for export] *).
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 asan_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
