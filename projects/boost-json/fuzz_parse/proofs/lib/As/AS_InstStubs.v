(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsWalk AsCXXHeap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init5Logick42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ld5asegsk43and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~q66AOPDEL37Corelib4Init9Datatypesuc4Nonek42or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh0dmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hl83mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hpb2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hte7seg_romhf7Z_to_bv3h5LinuxProcessSemantics5Riscv7Preludeij25bvmapq6aAFREE_STUBq67AOPDEL2q67AOPDELAq63mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~io83evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~isa7mem_invq6cfree_stmt_atq6h1free_null_stmt_atq69free_stmtq6aopdel_stmtq6bopdel2_stmtq6bopdelA_stmtuc4listuc4produc4consuc3niluc4pair46Stdlib6ZArith6BinInt1Zjoa3subhfbbv_unsignedjoa3addjoa2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~js44celluc6optionjs42C8hl83stkk42ex89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAS_InstStubs5Stubs~~~~~~ki37opnew_Wq6cAMALLOC_STUBq66AOPNEWq69ARA_OPNEW79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kpa5aceilhl85munchhl85wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kv38rw_cellsjoa3powjoa2lthpb6ret_pcuc3fstuc3snd37Corelib5Lists7ListDeflld6Forallq65apresq68as_RHEAPq65as_Stq65blockhl83ivlq6aopnew_stmtq63asrq67SR_lawsq6aMPRES_lawsq6h1RHEAP_block_rangeq69RHEAP_fsbq6bRHEAP_frameq6brauxv_frameq6achain_lawsq67TR_lawsq6bmalloc_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Stubs.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!lr5$0").
  Hypothesis Lsr : ltac2:(zQ "10!lrb@1$0?1H").
  Hypothesis Lmpres : ltac2:(zQ "10!ls5@1$0?1H").

  Let SRdone : forall (Q : config -> Prop) c, Q c -> as_SR H Q c. Proof. exact (proj1 Lsr). Qed.
  Let SRmono : forall (Q Q' : config -> Prop) c, as_SR H Q c -> (forall c', Q c' -> Q' c') -> as_SR H Q' c. Proof. exact (proj1 (proj2 Lsr)). Qed.
  Let SRseq : forall (Q1 Q2 : config -> Prop) c, as_SR H Q1 c -> (forall c', Q1 c' -> as_SR H Q2 c') -> as_SR H Q2 c. Proof. exact (proj1 (proj2 (proj2 Lsr))). Qed.
  Let SRlift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
      as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
      (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).
  Proof. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Let MPtrans : forall mo1 mo2 mo3, as_MPRES H mo1 mo2 -> as_MPRES H mo2 mo3 -> as_MPRES H mo1 mo3. Proof. exact (proj2 Lmpres). Qed.

  (* [comment removed for export] *)
  Lemma j_evt : ltac2:(zQ "h50!h9!jc!k1!l8!p8!q0!u3!hg4!hgb!hk7!hp4!ht8!ihd!ii8!il8!im1!ime!in8!io2!is3!jg4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h2>2pc$2>6target$2>0@2$8@2$5@3$3$2^2$6@3$3$2^1$f@2$8@2$5@3$3$2^2$h0@3$3$2^1$6@2$5@3$3$2^2$h1@3$3$2^1$6>0@2$h4$4^4@3$h3$4\3ms'$9@3$3$9^1@7$b@hf$a^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8@2$d@1$0#k0^4^7@1$7@1$1@1$0#k0^6@1$c$4@7$b@hf$a^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7@2$d@1$0#k0^4^6@1$7@1$1@1$0#k0^5@1$c$4").
  Proof.
    intros until target. intros PT MI.
    destruct PT as [[-> ->]|[[-> ->]|[-> ->]]]; unfold AOPDEL, AOPDEL2, AOPDELA, AFREE_STUB.
    - step. apply evt_done. reflexivity.
    - step. apply evt_done. reflexivity.
    - step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma free_stmt_via_j : ltac2:(zQ "90!k1!l8!q0!u3!hgb!jgf!im1!ime!in8>2pc$0>6target$0>3pc0$0>0@2$4@2$2@3$1$0^3$3@3$1$0^2$6@2$4@2$2@3$1$0^3$7@3$1$0^2$3@2$2@3$1$0^3$8@3$1$0^2$3>0@4$5?5HCEIL?1H^3^2@4$5?5HCEIL?1H^5^3").
  Proof.
    intros pc target pc0 PT FS. unfold free_stmt_at. intros until sbs. intros VIS HP K IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0.
    eapply SRlift; [exact K | exact VIS | apply j_evt; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB p A n lo B errv mo' CH bs sbs
                E HP K' IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0). }
    intros c' PO. unfold free_post in *.
    ndestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    nexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma free_null_stmt_via_j : ltac2:(zQ "90!k1!l8!q0!u3!hgb!jhe!im1!ime!in8>2pc$0>6target$0>0@2$4@2$2@3$1$0^2$3@3$1$0^1$6@2$4@2$2@3$1$0^2$7@3$1$0^1$3@2$2@3$1$0^2$8@3$1$0^1$3>0@3$5?5HCEIL?1H^2@3$5?5HCEIL?1H^4").
  Proof.
    intros pc target PT FS. unfold free_null_stmt_at. intros until CH. intros VIS HP K CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH.
    eapply SRlift; [exact K | exact VIS | apply j_evt; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB lo B errv mo' CH
                E HP K' CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH). }
    intros c' PO. unfold free_null_post in *.
    ndestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    nexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma opdel_of_free : ltac2:(zQ "20!jj3!jjf>0@2$0?5HCEIL?1H@2$1?5HCEIL?1H").
  Proof. intros FS. exact (free_stmt_via_j AOPDEL AFREE_STUB APC0_FREE (or_introl (conj eq_refl eq_refl)) FS). Qed.
  Lemma opdel2_of_free : ltac2:(zQ "20!jj3!jkc>0@2$0?5HCEIL?1H@2$1?5HCEIL?1H").
  Proof. intros FS. exact (free_stmt_via_j AOPDEL2 AOPDEL APC0_FREE (or_intror (or_introl (conj eq_refl eq_refl))) (opdel_of_free FS)). Qed.
  Lemma opdel_null_of_free_null : ltac2:(zQ "30!jhe!im1!u3>0@3$0?5HCEIL?1H$1@3$0?5HCEIL?1H$2").
  Proof. intros FS. exact (free_null_stmt_via_j AOPDEL AFREE_STUB (or_introl (conj eq_refl eq_refl)) FS). Qed.
  Lemma opdel2_null_of_free_null : ltac2:(zQ "30!jhe!im1!ime>0@3$0?5HCEIL?1H$1@3$0?5HCEIL?1H$2").
  Proof. intros FS. exact (free_null_stmt_via_j AOPDEL2 AOPDEL (or_intror (or_introl (conj eq_refl eq_refl))) (opdel_null_of_free_null FS)). Qed.
  (* [comment removed for export] *)
  Lemma opdelA_of_free : ltac2:(zQ "20!jj3!jla>0@2$0?5HCEIL?1H@2$1?5HCEIL?1H").
  Proof. intros FS. exact (free_stmt_via_j AOPDELA AOPDEL APC0_FREE (or_intror (or_intror (conj eq_refl eq_refl))) (opdel_of_free FS)). Qed.
  Lemma opdelA_null_of_free_null : ltac2:(zQ "30!jhe!im1!in8>0@3$0?5HCEIL?1H$1@3$0?5HCEIL?1H$2").
  Proof. intros FS. exact (free_null_stmt_via_j AOPDELA AOPDEL (or_intror (or_intror (conj eq_refl eq_refl))) (opdel_null_of_free_null FS)). Qed.

  (* [comment removed for export] *)
  Definition opnew_W : ltac2:(zQ "30!k1!jm8!jmf>2SP$0@1$1@2$2$0$0") := ltac2:(zQ "60!k1!jmf!jn6!jnd!jo3!jq2\2SP$0@3$2@2$1$0$0@4$4$0$0@2$5^1+h0^1@1$3@2$1$0$0").
  Lemma opnew_pro : ltac2:(zQ "i31!h9!jc!p8!ii8!q0!jq9!jr7!jre!kg0!hg4!jn6!kg8!l8!k1!hk7!kh1!hp4!kh7!ht8!jg4!ihd!jnd!khe!il8!kmb!kn6!ko5!koe!io2!kt8!is3!ku1!kua!lie!lja&>0@1$1@1$0#k0@1$b@1$1@1$0#8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hc>1n$d>2lo$d>0@3$c@1$1@1$0#k0^hb@2$3@1$0#k0^2>0@2$4@2$7+1^3@2$7^3@2$i2+2+hf>0@4$h1$2^5^3@2$5@1$0#k0^i5>0@2$7@1$hd?5HCEIL^4>0@2$7@2$6^5+h0@2$5@1$0#k0^i7>0@2$h3$2^8@3$he$2\3ms'$e@2$h6~0\2m1~0@2$4@3$c$e^2@7$h2@hf$h0@2$3@1$0#k0$hb@2$3@1$0#k0@2$6@2$5@1$0#k0^ib-h0^ia^i9^i8^i7^i6@2$3@1$0#k0^a^i4@2$3@1$0#k0^a^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d@2$3@1$0#k0$h9^c@1$9@1$1@1$0#k0^1@1$h4$2@2$4@3$hf@1$h8@2$5@1$0#k0^ib^b^1@2$4@3$i0$2^b^1@2$4@2$h3$2^1@2$4@4$h1$2^1^9@2$6@2$5@1$0#k0^ib-h0@4$i1$2^1@2$6@2$5@1$0#k0^ib-h0@3$a$8@1$f^i5@3$a$8@1$f^ic@1$h5$8@7$h2@hf$h0^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b@2$3@1$0#k0$ha^a@1$9@1$1@1$0#k0^9@1$h4$2").
  Proof.
    intros until lo. intros -> N ST CEIL LO MI. unfold AOPNEW, AMALLOC_STUB, ARA_OPNEW. acb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl (opnew_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold opnew_W in MU.
    carve_frame 16%nat ST.
    step. step. step. zstep. zstep. step. step. step.   (* [comment removed for export] *)
    replace (n + Z.b2z (n <? 1)) with n by (destruct (Z.ltb_spec n 1); cbn; lia).
    apply evt_done. exists m1. split; [reflexivity|]. unfold opnew_W. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma opnew_epi : ltac2:(zQ "hf0!h9!jc!p8!jq9!ii8!jr7!q0!kg0!lk1!hg4!jn6!l8!k1!hk7!kh1!hp4!kh7!ht8!lk7!ihd!jre!lja!jnd!il8!koe!io2!kt8!is3!jg4!lie!jq2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>3ra0@1$1@1$0#k0>3s00@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h9>1A$c>2lo$c>0@2$6@2$8Z^2@2$8^2@2$h5+2+if>0@3$b@1$1@1$0#k0^i5@2$4@1$0#k0@2$5@2$he@2$3@1$0#k0^i5+h0+h0>0@4$h0$2^5^3@2$3@1$0#k0^i6>0@2$6@2$h4@1$ha?5HCEIL^4@2$h4^4@2$3@1$0#k0^i7>0@4$hd$2^7@2$3@1$0#k0^i8@3$a$7@1$e^a@3$a$7@1$e^b@1$h6$7>0@2$8@2$5@2$3@1$0#k0^i9+h0@2$h5+2+k0>0@2$hc$2^9@3$hb$2\3ms'$d@2$6@3$b$d^1@7$h1@hf$f^f@2$4@1$0#k0@2$5@2$3@1$0#k0^ic+h0^ib^ia^i9^i8^i7^e^i5@2$4@1$0#k0^a^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^d@1$h2^f^c@1$9@1$1@1$0#k0^b@1$h3$2@4$h0$2^b^9@2$5@2$3@1$0#k0^ic+h0@7$h1@hf$f^ic^ib^ia^i9^i8^i7^i6^i5^i4@2$4@1$0#k0^9^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^c@1$h2@2$4@1$0#k0$h8^b@1$9@1$1@1$0#k0^a@1$h3$2").
  Proof.
    intros until lo. intros HA _ ST CEIL FR SPH MI. unfold ARA_OPNEW. acb.
    replace (ret_pc (Z_to_bv 64 0x1ac2d4)) with (Z_to_bv 64 0x1ac2d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    step. step. step. step. apply evt_done. split; [reflexivity|].
    release_frame FR ST (bv_unsigned sp + 16). exact ST.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Lbr : ltac2:(zQ "10!lt2@2$0?5HCEIL?1H").
  Hypothesis Lfsb : ltac2:(zQ "10!lu7@2$0?5HCEIL?1H").
  Lemma apres_of_munch0 : ltac2:(zQ "h51!k1!h9!jc!jm8!kg8!jmf!jre!ll1!ll7!q0!ln4!p8!lne!lo6!lp1!lp9!io2!kt8!lq1!ku1!kua&>0@1$2@1$1#k0@1$4@1$2@1$1#8>1s@1$e?1H>2LB@1$3$f>2SP$0>1W@1$3$h2>2m0$h0>1m~0>2m'~0>0@4$d?1H^7^6^3>0@3$h3^5^3^2>0@3$h4$b^4^3>0@3$a@2$5$0$0\2iv@2$5$0$0@2$9@2$6@1$h1?5HCEIL@3$7$0$0^1@2$6@3$8$0$0^1^9^7@6$c?5HCEIL?1H^a^9^6^5").
  Proof.
    intros s LB SP W m0 m m' RH MU WM FW a Ha Hc. acb.
    pose proof (Lfsb _ _ _ RH) as (F1 & F2 & F3).
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      intros K. unfold aclient_addr in Hc.
      destruct Hc as [Hc|Hc]; [lia|].
      assert (LOW : a < aceil); [| lia].
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      - acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      - pose proof (Lbr _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      - pose proof (Lbr _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      - lia.
      - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      - acb; unfold AHI_LO in *. lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma apres_trans0 : ltac2:(zQ "50!lne!io2!jm8!k1!lp9>2LB@1$2$4>2SP$3>2m1$1>2m2$1>2m3$1>0@6$0?5HCEIL?1H^5^4^3^2>0@6$0?5HCEIL?1H^6^5^3^2@6$0?5HCEIL?1H^7^6^5^3").
  Proof.
    intros LB SP m1 m2 m3 P1 P2 a Ha Hc. destruct (P1 a Ha Hc) as [E1 W1]. destruct (P2 a Ha Hc) as [E2 W2].
    split; [congruence| auto].
  Qed.
  Lemma apres_weaken_sp : ltac2:(zQ "60!k1!lne!io2!jm8!lp9!jre>2LB@1$3$4>2SP$0>3SP'$0>1m$2>2m'$2>0@6$1?5HCEIL?1H^5^4^2^1>0@2$5^5^4@6$1?5HCEIL?1H^7^5^4^3").
  Proof.
    intros LB SP SP' m m' P LE a Ha Hc. apply P; [exact Ha|].
    unfold aclient_addr in *. destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc].
  Qed.

  Hypothesis Lrf : ltac2:(zQ "10!lv3@2$0?5HCEIL?1H").
  Hypothesis Laux : ltac2:(zQ "10!mg1@2$0?5HCEIL?1H").
  Hypothesis Lch : ltac2:(zQ "10!mgf@2$0?5HCEIL?1H").
  Hypothesis Ltr : ltac2:(zQ "10!mhc@1$0?1H").
  Hypothesis Lmalloc : ltac2:(zQ "10!mi6@2$0?5HCEIL?1H").

  Theorem opnew_of_malloc : ltac2:(zQ "10!lq8@2$0?5HCEIL?1H").
  Proof.
    unfold opnew_stmt. intros until mo. intros VIS HP K AOK COST AUX SPB ST CEIL LO ERR MI TP SP16 AC A0 N.
    unfold AOPNEW_STACK, AMALLOC_STACK in LO. acb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EA : bv_unsigned tp + (-164) = AERRNO) by (subst tp; unfold AERRNO, ATP; rewrite unsigned_lit; lia).
    rewrite EA in ERR.
    (* [comment removed for export] *)
    eapply SRlift; [exact K | exact VIS | eapply (opnew_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n lo A0 N ST CEIL ltac:(lia) MI) |].
    intros msF1 mo1 K1 MP1 PO. cbv beta in PO. ndestruct PO as (m1 & V1 & MU & WM & MI1 & ST1 & FR).
    assert (FW : Forall (fun iv : Z * Z => aceil <= fst iv /\ snd iv <= bv_unsigned sp) (opnew_W (bv_unsigned sp))).
    { unfold opnew_W. constructor; [cbn; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1).
    { eapply Lrf; [exact HP| exact MU| exact WM|]. unfold opnew_W. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : as_rauxv_ok H m1 B).
    { eapply (Laux LB); [exact AUX| exact MU| exact WM|]. unfold opnew_W. constructor; [left; cbn; lia| constructor]. }
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU| exact WM|]. unfold opnew_W. constructor; [| constructor].
      apply aconst_ok_high; [| right; left]; acb; unfold sh, AIMG_TOP, ASHADOW_BASE in *; lia. }
    assert (ERR1 : rw_cells asegs m1 AERRNO [C4 errv]).
    { eapply (rw_cells_transport asegs _ m m1); [exact ERR| exact MU| exact WM|]. unfold opnew_W, AERRNO, ATP. cbn. lia. }
    pose proof (apres_of_munch0 s LB (bv_unsigned sp) _ m m m1 HP MU WM FW) as PRES1.
    (* [comment removed for export] *)
    eapply SRseq.
    { unfold malloc_stmt, malloc_stmt_at in Lmalloc.
      eapply (Lmalloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF1 m1 s LB n lo B errv mo1 []);
        [ exact V1| exact HP1| exact K1| exact AOK| exact COST| exact AUX1| rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; exact ST1| exact CEIL| rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
        | rewrite EA; exact ERR1| exact MI1| exact TP
        | rewrite unsigned_lit by lia; rewrite <- Z.add_mod_idemp_l, SP16 by lia; reflexivity| exact AC1
        | apply (proj1 Lch); rewrite unsigned_lit by lia; left; lia
        | cbn [map]; rewrite unsigned_lit by (unfold ARA_OPNEW; lia); exact Ltr
        | reflexivity| exact N]. }
    (* [comment removed for export] *)
    intros [msF2 mo2] PO. unfold malloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    ndestruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & bj & p & s' &
                    V2 & K2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HP2 & BLK & ADN & AC2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, HPRES by lia.
    npose BR as (BA & _ & _ & _ & BHI & _).
    apply (apres_rw_cells H _ _ _ _ _ _ HPRES) in FR; [| left; cbn; lia].
    eapply SRlift; [exact K2 | exact V2 | |].
    { eapply (opnew_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ra s0 F fc m2 A lo);
        rewrite ?unsigned_lit by lia; [lia| | exact ST2| lia| exact FR| lia| exact MI2].
      rewrite Z.sub_add. reflexivity. }
    intros msF3 mo3 K3 MP3 PO. cbv beta in PO. destruct PO as [V3 ST3].
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in V3, ST3 by lia.
    replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in V3, ST3 by lia. rewrite Z_to_bv_bv_unsigned in V3.
    apply SRdone. unfold malloc_post.
    nexists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, bj, p, s'.
    split; [exact V3|]. split; [exact K3|]. split; [exact (MPtrans _ _ _ MP1 (MPtrans _ _ _ MP2 MP3))|].
    split; [exact MI2|]. split; [exact ST3|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [| split; [exact BR| split; [exact HP2| split; [exact BLK| split; [exact ADN| split; [exact AC2| exact AL2]]]]]].
    eapply apres_trans0; [exact PRES1|]. eapply apres_weaken_sp; [exact HPRES| lia].
  Qed.

End Stubs.
