(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AsDepotInv AW_MallocBase AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state37Corelib7Numbers7BinNumsk64Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~m65asegs37Corelib4Init9Datatypesq94None37Corelib4Init5Logics83ands82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~u73mkRu73stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hif2MShif6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hnc7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hs62wz35stdpp9bitvectorbdefinitionsig72bvig7bbv_unsignedig77Z_to_bv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_MallocRet3Ret~~~~~~ik4fmalloc_ret_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~ipd3evt46Stdlib6ZArith6BinInt1Zitf3additf2leitf2ltitf3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jh14cellq94consjh12C8q93nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jm88rw_cellsq96lengthk61Zitf6of_natq93app37Corelib5Lists7ListDefjsc3map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jua6u64arrq93nat37Corelib4Init3Natkj43sub37Corelib4Init5Peanokkd2lejh12CB" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section Ret.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp ra0 s0v s1v s2v s3v s4v s5v : word).
  (* [comment removed for export] *)
  Variables (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U : Z) (T : list Z) (rest : list word) (jk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : ltac2:(zQ "40!lf!iv7!ive!iia@2$2@2$1?2lo+ps0@2$3@1$0#k0?2sp").
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis UR : ltac2:(zQ "40!tc!ive!jg4!jga@2$0@2$1+1?1U@2$2?1U@2$3+2+k0").
  Hypothesis ST : ltac2:(zQ "50!lf!q1!hi9!iv7!iia@4$2$1?1m?2lo@2$3@2$4@1$0#k0?2sp-om0").
  Hypothesis FR : ltac2:(zQ "a0!jkd!jl5!jlc!jm2!lf!q1!jq3!ig1!iv7!iia@4$6$5?1m@2$8@2$9@1$4#k0?2sp-om0@3$1$0@1$2?2sp@3$1$0@1$2@1$7+pgumc@1$3$0").
  Hypothesis ESO : ltac2:(zQ "d0!jkd!iv7!jl5!lf!jlc!ig1!iia!jqf!jm2!jr8!q1!jq3!jrc@4$b$a?1m@2$1@2$6@1$3#k0?2sp-ol0@3$2$0@1$4@1$5@2$1@2$1@2$6@1$3#k0?2sp-ol0+h0@3$2$0@1$4@1$5@1$c@2$7$9?1T@1$8$0").
  Hypothesis TRB : ltac2:(zQ "a0!lf!iv7!ii4!js6!ju3!jr8!q1!ki4!ig1!iia@4$7$6?1m@2$1@2$1@2$9@1$0#k0?2sp-ol0+h0@3$3@1$2@1$0#k0@4$4$5@1$2@1$0#k0$8?1T?4rest").
  Hypothesis LR : ltac2:(zQ "70!jqf!kie!u2!kk6!lf!jr8!ii4@3$2$1@2$0@1$6@1$4#k0?4rest@2$3Nvf@2$0$5?1T").
  Hypothesis NR : ltac2:(zQ "40!jqf!km1!jr8!tc@2$3@2$1N1@2$0$2?1T@2$1@2$0$2?1TNhe").
  Hypothesis TFB : ltac2:(zQ "90!jkd!jl5!jm2!lf!q1!jlc!jq3!iv7!iia@4$6$4?1m@2$7@2$8@1$3#k0?2sp-k8@3$1$0@1$5?2sp@1$2$0").
  Hypothesis F4 : ltac2:(zQ "a0!jkd!jl5!jlc!jm2!lf!q1!km7!jq3!iv7!iia@4$7$5?1m@2$8@2$9@1$4#k0?2sp-k0@3$1$0@2$6N8?2jk@3$1$0@1$2?3s5v@3$1$0@1$2?3s4v@3$1$0@1$2?3s3v@3$1$0@1$2?3s2v@3$1$0@1$2?3s1v@3$1$0@1$2?3s0v@3$1$0@1$2?3ra0@1$3$0").

  Definition malloc_ret_post : ltac2:(zQ "10!j7>0$0P") := ltac2:(zQ "e0!lf!j7!q1!s1!tc!u2!hi3!hi9!hmc!hn2!hrb!ig1!ii4!iia\3ms'$1@2$4@3$5$1^1@7$8@hf$6?3ra0?2sp?2gp?2tp?2x5?2x6?2x7?3s0v?3s1v@1$b?1U?3x11?3x12?3x13?3x14?3x15?3x16?3x17?3s2v?3s3v?3s4v?3s5v?3x22?3x23?3x24?3x25?3x26?3x27?3x28?3x29?3x30?3x31?1F@1$9?3ra0?2fc@1$3@1$c@1$0#k0?1m@1$a$2@4$7$2?1m?2lo@2$d@1$0#k0?2sp").

  Theorem malloc_ret : ltac2:(zQ "d0!lf!q1!ij9!s1!ioa!it8!hi3!hmc!hrb!ig1!iv7!ii4!iia@3$5$1$4@7$7@hf$6?2x1@2$2@1$0#k0@2$a@2$c@1$0#k0?2sp-om0?2gp?2tp?2x5?2x6?2x7?2x8?2x9@1$9?1U?3x11?3x12?3x13?3x14?3x15?3x16?3x17?3x18?3x19?3x20?3x21?3x22?3x23?3x24?3x25?3x26?3x27?3x28?3x29?3x30?3x31?1F@2$2@1$0#k0+mpgl8?2fc@1$3@1$b@1$0#k0?1m@1$8$1").
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    acb. unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    { exfalso. clear - K UR; try acb. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    step. step. step. step.
    (* [comment removed for export] *)
    step. do 7 step. step. step.
    apply evt_done. split; [reflexivity|].
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells asegs _ _ _ FR) as K1. pose proof (stk_of_rw_cells asegs _ _ _ ESO) as K2.
    pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4. pose proof (stk_of_rw_cells asegs _ _ _ F4) as K5.
    pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB))) as K3.
    cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5.
    rewrite u64s_length, length_app, length_map, LR in K3.
    eapply stk_merge; [exact ST| |lia]. eapply stk_merge; [exact K1| |lia].
    replace (bv_unsigned sp + -2144 + Z.of_nat 16) with (bv_unsigned sp + -2128) by lia.
    eapply stk_merge; [exact K2| |lia]. replace (bv_unsigned sp + -2128 + Z.of_nat 16) with (bv_unsigned sp + -2128 + 16) by lia.
    eapply stk_merge; [exact K3| |lia].
    replace (bv_unsigned sp + -2128 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -72) by lia.
    eapply stk_merge; [exact K4| |lia]. replace (bv_unsigned sp + -72 + Z.of_nat 8) with (bv_unsigned sp + -64) by lia.
    replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat 64) at 2 by lia. exact K5.
  Qed.
End Ret.
