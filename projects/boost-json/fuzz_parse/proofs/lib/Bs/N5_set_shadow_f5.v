(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsWalk F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~lf4cell46Stdlib6ZArith6BinInt1Zq22lek14consk16option37Corelib4Init5Logicsf3and01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~uc5asegslf2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hj48rw_cellsq23pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~ho1h2set_shadow_f5_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_CB0_any : ltac2:(zQ "d0!h9!jc!l9!pb!ra!rf!s6!u3!u9!hi7!hif!hmf!hnb>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1a$8>0@2$7@2$4Z^1@2$4^1@2$c+2+k0@4$b$9^3^2@3$5$3@2$aN0@1$2@1$1@1$0#8@1$2$3").
Proof.
  intros m a Ha. split; [split|].
  - cbn. exact (conj eq_refl I).
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Section S.
  Lemma set_shadow_f5_ok : ltac2:(zQ "10!hre$0").
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa n junk.
    intros Ha0 Ha1 Hn DST MI AC. subst a0 a1. unfold ASET_SHADOW_F5.
    pose proof (ACONST_memsetp m AC) as [G1 G2]. unfold AGOT_MEMSETP, AMEMSETP_CELL, AREAL_MEMSET, wz in G1, G2.
    pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
    assert (SA : 0 <= sa < 2^64 \/ (sa = 2^64 /\ n = 0)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    destruct SA as [SA|[Esa En]].
    - eapply evt_mono.
      { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact DST. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      ndestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      rewrite !unsigned_lit in MU, RC by lia.
      nexists x0, x1, x2, (Z_to_bv 64 sa), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      unfold poison_bytes, b8. change (245 mod 256) with 245 in RC. exact RC.
    - subst sa n. eapply evt_mono.
      { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []); [| exact MI].
        replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 by (vm_compute; reflexivity).
        rewrite unsigned_lit by lia. apply rw_cells_CB0_any. lia. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      ndestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in MU by (vm_compute; reflexivity).
      rewrite !unsigned_lit in MU by lia.
      nexists x0, x1, x2, (Z_to_bv 64 (2 ^ 64)), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split.
      { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [exact WM|]. split; [exact MI'|].
      apply rw_cells_CB0_any. lia.
  Qed.
End S.

End HCW.

