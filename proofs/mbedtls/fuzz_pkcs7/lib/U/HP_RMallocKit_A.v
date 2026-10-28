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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocKit_A () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "Corelib.Init.Logic.eq"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr32"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RAUXV_CELL"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"].


Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rmrep_wr32 : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pp,(3.$4.$5.)Pv,$5.Pr,$6.P,(7.VhRP,R5.R4.)P,(8.R6.)P,(9.(2.$6.)(:.$4.$6.(;.$4.$<.$=.$6.)(>.$4.$<.$=.$6.)(?.$4.$5.R5.)(10.R7.))(11.$6.R3.))P,(9.$12.(13.R4.)$14.)P,(15.=(16.$4.$5.R7.))P,(15.(17.(16.$4.$5.R8.)+4.)(18.(19.R6.)))P,Pb,(3.$4.$5.)Pgh,$1:.P,(9.(2.$1:.)(:.(3.$4.$5.)$1:.(;.$1;.(1<.$4.$<.$5.$1=.)(1>.$4.$<.$=.$5.$1=.$1?.)$1:.)(>.$1;.(1<.$4.$<.$5.$1=.)(1>.$4.$<.$=.$5.$1=.$1?.)$1:.)R2.(20.R=.))(11.$1:.R1.))P,(9.$4.(?.$4.$5.R3.)(?.$4.$5.R<.))(21.(15.(17.(16.$4.$5.R=.)+4.)(16.$4.$5.R4.))(15.(17.(16.$4.$5.R4.)+9.)(16.$4.$5.R=.)))P,(22.(15.=R9.)(23.R9.(24.+2.+20.)))(22.(7.VhRP,(25.R;.R:.R=.)(26.R<.(27.(17.(28.R9.)(16.$4.$5.R;.)))(29.(2:.R:.))))(8.(25.R;.R:.R=.)))")
(* [comment removed for export] *).
Proof.
  intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
  rewrite le4_bytes by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
    with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
            (wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
            (wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
  rewrite !wa_succ.
  unfold wr32.
  assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
  rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
  { split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S1 as [M1 T1].
  assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
               /\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
  { split; [|apply ticks_ok_wr8; exact T1].
    replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S2 as [M2 T2].
  assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
                    (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
               /\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
  { split; [|apply ticks_ok_wr8; exact T2].
    replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S3 as [M3 T3].
  split; [|apply ticks_ok_wr8; exact T3].
  replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
  apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
  intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rauxv_ok_pres : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A ()) "PC,P,$5.SpPm,$2;.Pm',$2;.PB,$5.P,(2<.VhRP,R3.R1.)P,(2=.R5.R4.R3.)P,Pa,$5.P,(15.R4.R1.)(2>.A1.R8.R2.)P,Pa,$5.P,(22.(15.$2?.R1.)(23.R1.(17.$2?.+8.)))(2>.A1.R9.R2.)(2<.VhRP,R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros C m m' B dd_H; ddestruct dd_H as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H); intros HP HB HC).
  dexists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rpres_write : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A ()) "PC,P,$5.SpPm0,$2;.Pm,$2;.Pa,$5.Pbs,(30.(1.&8.))P,(2=.R5.R4.R3.)P,(15.=R3.)P,(15.(17.R4.(31.(32.(1.&8.)R3.)))(24.+2.+40.))P,Px,$5.P,(22.(15.R6.R1.)(23.R1.(17.R6.(31.(32.(1.&8.)R5.)))))A1.R:.R2.(2=.R9.R8.(26.R7.(27.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros C m0 m a bs HP Ha Hl HC x Hx HCx.
  destruct (HP x Hx HCx) as [E W].
  assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
  { rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. apply HCx, HC. lia. }
  split.
  - rewrite NE. exact E.
  - intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

#[using="Type"] Lemma rpres_except_munch_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A ()) "PC,P,$5.SpPm0,$2;.Pm,$2;.Pm',P,(1.&40.)(2.(1.&8.))PW,(30.$33.)P,(2=.R5.R4.R3.)P,(34.R2.R4.R3.)P,(35.$36.R5.R4.)P,Px,$5.P,(22.(15.=R1.)(23.R1.(24.+2.+40.)))P,(2>.A1.R:.R2.)(37.R7.R3.)(2=.R9.R8.R6.)")
(* [comment removed for export] *).
Proof.
  intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.

End RP_1.
