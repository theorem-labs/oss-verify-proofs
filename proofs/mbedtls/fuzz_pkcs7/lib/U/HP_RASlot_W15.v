(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B F_malloc_bigw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W15.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RF_ntf_A HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_W15 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.bounces"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.unmap_seq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.b2z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.is_bouncing"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RP_1.SEQ.rseqW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.account_bounce"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.step_seq"].


Section RP_1. Context {hRP : run_params}.
Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SC"] Lemma rbounce_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W15 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pst,$2.Pm,$3.P,(4.VhRP,R2.R1.)P,(5.(6.=(7.(8.R3.)))(9.(7.(8.R3.))+100.))P,Pi,$:.(5.(6.=(;.R5.R1.))(9.(;.R5.R1.)+100.))P,Pi,$:.(5.(6.=(<.R6.R1.))(9.(<.R6.R1.)+100.))P,(=.$>.R5.)(?.$>.Lms',$10.(11.(0.&40.)Lt0',(0.&40.)(11.(0.&40.)Lt1',(0.&40.)(11.(0.&40.)La3',(0.&40.)(11.(0.&40.)La5',(0.&40.)(11.(0.&40.)La7',(0.&40.)(11.P,(0.&40.)(12.(0.&8.))Lm',P,(0.&40.)(12.(0.&8.))(5.(13.$10.R7.(14.(15.R2=.R2<.R2;.R2:.R6.R5.R27.(16.&40.Vsc,)R26.R25.R24.R23.R4.R21.R3.(17.(7.(8.R>.)))R2.R1=.R1<.R1;.R1:.(16.&40.$18.)R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(16.&40.+40>58.)R?.(19.(0.&40.))R1.(1:.$>.)))(5.(13.(0.&40.)R4.(16.&40.(1;.(1<.Vsc,R>.))))(5.(1=.$1>.R=.R1.)(5.(1?.$>.R=.R1.)(5.(=.$>.R1.)(4.VhRP,(20.Vsc,R>.)R1.))))))))))))(14.(15.R26.R25.R24.R23.R22.R21.R20.(16.&40.Vsc,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(16.&40.$18.)R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(16.&40.+40;:4.)R8.(19.(0.&40.))R6.(1:.$>.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold rseqW in MU.
  unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
    rmrep stX mX -> stX = account_bounce sc st -> mem_inv rsegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
    munch [(512968 + 848, 512968 + 913)]%Z m mX -> wmono rsegs m mX ->
    evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x40e58) fc None m' (seg_rom rsegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch [(512968 + 848, 512968 + 913)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40e54) fc None mX (seg_rom rsegs))).
  { intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
    pose proof (rmrep_seq_read stX mX (wa (512968 + 912)) MRX eq_refl) as RDS.
    replace (wa (512968 + 912)) with (Z_to_bv 64 (512960 + 920)) in RDS by (unfold wa; f_equal; lia).
    assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
    { rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
      destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
    rewrite SQX in RDS.
    step. rewrite ?zxb_b8 by lia. clear RDS.
    apply evt_done. deexists 6. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *)
    assert (HO : sc_in_seq_range sc = false).
    { unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
      - replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
        replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    step. step.
    eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
    - unfold account_bounce. rewrite HO. reflexivity.
    - unfold is_bouncing. rewrite HO. reflexivity. }
  rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
  destruct (Z.lt_ge_cases sc 7) as [L7|G7].
  { exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
  rewrite Z.mod_small in K by lia.
  assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc + -7)) by lia.
  pose proof (rmrep_bounces_read st m (sc - 7) (wa (512968 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
  replace (wa (512968 + 880 + (sc - 7))) with (Z_to_bv 64 (512960 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
  pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
  step. rewrite ?zxb_b8 by lia. clear RDB.
  dpose MR as (_ & (_ & _ & _ & US & _) & _).
  pose proof (u8arr_read rsegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (512960 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
                ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
  step. rewrite ?zxb_b8 by lia. clear RDU.
  (* [comment removed for export] *)
  step. step.
  set (nos := 100 <=? bounces st (sc - 7)).
  assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
  assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
  { rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    change (bv_wrap 64 100) with 100.
    destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
  rewrite A3. clear A3.
  assert (AB : account_bounce sc st =
    (if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
     then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
     else st)) by (unfold account_bounce; rewrite IN; reflexivity).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
  { eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (512968 + 912)) MR eq_refl) as RDS.
  replace (wa (512968 + 912)) with (Z_to_bv 64 (512960 + 920)) in RDS by (unfold wa; f_equal; lia).
  step. rewrite ?zxb_b8 by lia. clear RDS.
  step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
  step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in K2.
    apply evt_done. deexists 6. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. exact MR. }
  apply Z.ltb_ge in K2.
  assert (AB2 : account_bounce sc st =
    (if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
  { rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  clear AB K1 K2.
  dpose MR as (_ & (_ & _ & _ & _ & BA & _) & _).
  pose proof (u8arr_store_ok rsegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (512960 + (sc + -7) + 888)) BA
                ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (512968 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. step. st1. rewrite (le1_lit 150) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (512968 + 880 + (sc - 7)) [b8 150] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rseq_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W15 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pst,$2.Pm0,$3.Pm,$3.P,(4.VhRP,R3.R1.)P,(5.(6.=(7.(8.R4.)))(9.(7.(8.R4.))+100.))P,(=.$>.R3.)P,(1=.$1>.R5.R4.)P,(1?.$>.R6.R5.)(?.$>.Lms',$10.(11.(0.&40.)La6',(0.&40.)(11.P,(0.&40.)(12.(0.&8.))Lm',P,(0.&40.)(12.(0.&8.))(5.(13.$10.R3.(14.(15.R29.R28.R27.R26.R25.R24.R23.(16.&40.Vsc,)R22.R21.R20.R1?.R1>.R1=.(16.&40.+1?.)R2.R1;.R1:.R19.R18.R17.(16.&40.$18.)R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(16.&40.+40>84.)R<.(19.(0.&40.))R1.(1:.$>.)))(5.(1=.$1>.R:.R1.)(5.(1?.$>.R:.R1.)(5.(=.$>.R1.)(4.VhRP,(21.R;.)R1.)))))))(14.(15.R26.R25.R24.R23.R22.R21.R20.(16.&40.Vsc,)R1?.R1>.R1=.R1<.R1;.R1:.R19.(17.(7.(8.R8.)))R18.R17.R16.R15.R14.(16.&40.$18.)R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(16.&40.+40>58.)R9.(19.(0.&40.))R6.(1:.$>.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
  set (q := c_seq (ctx st)) in *.
  dpose MR as (_ & (_ & _ & _ & US & _ & C6) & _).
  unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
  replace (512968 + 912) with 513880 in C6 by reflexivity. replace (512968 + 848) with 513816 in US by reflexivity.
  (* [comment removed for export] *)
  assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv rsegs mj ->
    munch [(512968 + 848, 512968 + 913)]%Z m0 mj -> wmono rsegs m0 mj ->
    evt rsegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x40e84) fc None m' (seg_rom rsegs)
      /\ munch [(512968 + 848, 512968 + 913)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x40e7c) fc None mj (seg_rom rsegs))).
  { intros mj stj ns NS MRj CTj MIj MUj WMj.
    dpose MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (512968 + 912) with 513880 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (512960 + 920)) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    (* [comment removed for export] *)
    step. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    rraw_store_finish0 (512968 + 912) [b8 ns] MUj WMj SOK.
    apply evt_done. deexists 2. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned q) by lia.
    eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
    pose proof (munch_refl [(512968 + 848, 512968 + 880)]%Z m) as MUz. pose proof (wmono_refl rsegs m) as WMz.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (UZ : u8arr rsegs mX 513816 (zeros 32));
    [ apply (u8arr_of_rw_cells rsegs mX 513816 32);
      lazymatch goal with H : rw_cells rsegs mX 513816 _ |- _ =>
        apply (rw_cells_congr rsegs mX 513816 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    dpose MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRz : rmrep stz mX);
    [ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
    | clear MUc WMc ] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono rsegs m0 ?mX, MIc : mem_inv rsegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
(* [comment removed for export] *)
#[using="SC"] Lemma rmm_seq_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W15 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pst,$2.Pm,$3.P,(4.VhRP,R2.R1.)P,(5.(6.=(7.(8.R3.)))(9.(7.(8.R3.))+100.))P,Pi,$:.(5.(6.=(;.R5.R1.))(9.(;.R5.R1.)+100.))P,Pi,$:.(5.(6.=(<.R6.R1.))(9.(<.R6.R1.)+100.))P,(=.$>.R5.)(?.$>.Lms',$10.(11.(0.&40.)Lt0',(0.&40.)(11.(0.&40.)Lt1',(0.&40.)(11.(0.&40.)La3',(0.&40.)(11.(0.&40.)La6',(0.&40.)(11.(0.&40.)La7',(0.&40.)(11.P,(0.&40.)(12.(0.&8.))Lm',P,(0.&40.)(12.(0.&8.))(5.(13.$10.R7.(14.(15.R2=.R2<.R2;.R2:.R6.R5.R27.(16.&40.Vsc,)R26.R25.R24.R23.R4.R21.(16.&40.+1?.)R3.R2.R1=.R1<.R1;.R1:.(16.&40.$18.)R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(16.&40.+40>84.)R?.(19.(0.&40.))R1.(1:.$>.)))(5.(13.(0.&40.)R4.(16.&40.(1;.(1<.Vsc,R>.))))(5.(1=.$1>.R=.R1.)(5.(1?.$>.R=.R1.)(5.(=.$>.R1.)(4.VhRP,(21.(20.Vsc,R>.))R1.))))))))))))(14.(15.R26.R25.R24.R23.R22.R21.R20.(16.&40.Vsc,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(16.&40.$18.)R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(16.&40.+40;:4.)R8.(19.(0.&40.))R6.(1:.$>.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  eapply evt_cut; [eapply rbounce_walk; eassumption|].
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR')).
  assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
  { unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
    destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
  rewrite <- SEQ'.
  eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
  cbv beta. (intros ms'' dd_H; ddestruct dd_H as (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'')).
  deexists 6. split; [reflexivity|]. subst a3'.
  repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.

End RP_1.
