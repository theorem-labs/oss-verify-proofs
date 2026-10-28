(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ct_memcpy_if () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "CT_MEMCPY_IF_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "ct_memcpy_if_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"].


Definition U_CT_MEMCPY_IF : Z := 0x258b8.
Definition CT_MEMCPY_IF_STACK : Z := 16.

Definition ct_memcpy_if_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (dbs : list byte) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ct_memcpy_if ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Ldbs',(4.(2.&8.))(5.(6.$0.R12.(7.(8.O17.O16.O15.O14.R11.R10.R?.O13.O12.R>.R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(9.O17.)O6.(:.(2.&40.))R2.(;.O18.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.O4.))(=.(>.$?.$?.)(10.$?.$?.(12.(13.&40.O16.)$14.)(13.&40.O16.))(15.(>.$?.$?.))))O1.R2.)(5.(16.O18.O1.R2.)(5.(17.O18.R2.)(5.(18.O18.R2.O5.R1.)(5.(6.$19.(1:.(2.&8.)R1.)(1:.(2.&8.)O3.))(5.(6.(4.(2.&8.))(1;.(2.&8.)(1<.O4.)R1.)(1;.(2.&8.)(1<.O4.)O3.))(1=.O18.R2.O2.(13.&40.O16.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ct_memcpy_if_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ct_memcpy_if ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PD,$?.PS1,$?.PS2,$?.Pn,$?.Plo,$?.Pdbs,(4.(2.&8.))Psbs,(4.(2.&8.))P,(18.O2.R8.R7.R2.)P,(1?.O2.R9.R7.R2.)P,(5.(20.=R6.)(20.R6.+9<40.))P,(20.R7.(21.(1:.(2.&8.)R5.)))P,(20.R8.(21.(1:.(2.&8.)R5.)))P,(22.(20.(11.R;.(21.(1:.(2.&8.)R6.)))R<.)(20.(11.R<.(21.(1:.(2.&8.)R7.)))R;.))P,(22.(6.$?.R;.=)(6.$?.R;.R=.))P,(23.=R>.)P,(22.(6.$?.R<.=)(23.=R>.))P,(23.(11.R10.(21.(1:.(2.&8.)R;.)))(24.+2.+40.))P,(23.(11.R10.(21.(1:.(2.&8.)R;.)))(24.+2.+40.))P,(1=.O2.R13.R>.(13.&40.R33.))P,(20.R?.(12.(13.&40.R34.)$14.))P,(6.$?.(25.(13.&40.R35.)+10.)=)P,(22.(20.(11.R15.(21.(1:.(2.&8.)R10.)))R11.)(20.(13.&40.R36.)R15.))P,(22.(20.(11.R15.(21.(1:.(2.&8.)R10.)))R12.)(20.(13.&40.R37.)R15.))P,(17.O2.R18.)P,(6.(2.&40.)R30.(26.&40.R18.))P,(6.(2.&40.)R30.(26.&40.R18.))P,(6.(2.&40.)R30.(26.&40.R18.))P,(6.(2.&40.)R30.(26.&40.R18.))(27.O2.(28.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1<.R19.R17.R18.R1=.)(7.(8.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(26.&40.O1.)R1>.(:.(2.&40.))R1=.(;.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D S1 n ld ls lo : Z) (dbs0 sbs : list byte).
  Hypothesis Hn : 0 <= n <= 40000.
  Hypothesis Ln : n <= ld /\ n <= ls.
  Hypothesis L0 : Z.of_nat (length dbs0) = ld.
  Hypothesis LS : Z.of_nat (length sbs) = ls.
  Hypothesis DIS : S1 + ls <= D \/ D + ld <= S1.
  Hypothesis DB : 0 < D /\ D + ld < 2^64.
  Hypothesis SB : 0 <= S1 /\ S1 + ls < 2^64.
  Hypothesis NZS : n = 0 \/ 0 < S1.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 16.
  Hypothesis SX : D + ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S1 + ls <= lo \/ bv_unsigned sp <= S1.
  Hypothesis HS0 : bytes_at usegs m S1 sbs.

  Notation POST := (ct_memcpy_if_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n dbs0 lo m).
  Notation W := [(D, D + n); (bv_unsigned sp - 16, bv_unsigned sp)].
  Notation DINV mm ds := (u8arr usegs mm D ds /\ Z.of_nat (length ds) = ld /\ same_from (Z.to_nat n) ds dbs0
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -16)).
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -16) [C8 s1; C8 s0]).
  Local Ltac ck K := if_cases K; zify_cond K; [ exfalso; rewrite ?unsigned_lit in K by lia; lia | clear K ].
  Local Ltac ckx K := if_cases K;
    [ exfalso; lazymatch type of K with context [Z.b2z (?x <? 1)] =>
        replace (x <? 1) with false in K by (symmetry; apply Z.ltb_ge; lia) end;
      cbn [Z.b2z] in K; rewrite Z.lxor_0_r in K; vm_compute in K; discriminate
    | clear K ].

  (* [comment removed for export] *)
  #[using="ls sbs Hn Ln L0 LS DIS DB SB NZS SPR LO SX SSX HS0"] Lemma loop_walk : forall (k : nat) (i : Z) (ds : list byte) (mm : mem)
      (xs0 xs1 xa0 xa3 wt1 wt2 wt3 wt4 wt5 wt6 wa4 : word),
    Z.to_nat (n - i) = k -> 0 <= i < n ->
    wt1 = Z_to_bv 64 (S1 + i) -> wt2 = Z_to_bv 64 (D + i) -> wt3 = Z_to_bv 64 (D + i) -> wt4 = Z_to_bv 64 (S1 + i) ->
    wt5 = Z_to_bv 64 (D + i) -> wt6 = Z_to_bv 64 (D + i) -> wa4 = Z_to_bv 64 (n - i) ->
    DINV mm ds -> FRAME mm ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 1) wt1 wt2 xs0 xs1 xa0 (Z_to_bv 64 D) (Z_to_bv 64 S1) xa3 wa4
                            (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6)
                        F (Z_to_bv 64 0x25900) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; (intros i ds mm xs0 xs1 xa0 xa3 wt1 wt2 wt3 wt4 wt5 wt6 wa4 Hk Hi -> -> -> -> -> -> -> dd_H FR; ddestruct dd_H as (HX & LX & FX & MU & WM & MI & ST)); [lia|].
    pose proof (bytes_at_transport usegs _ m mm S1 sbs HS0 MU ltac:(cbn [disjoint_from]; rewrite LS; lia)) as HS.
    zstep. ck KC1. zstep. zstep. zstep. ckx KC2. zstep. ck KC3.
    zstep. ck KC4. zstep. zstep. zstep. ckx KC5. zstep. ck KC6.
    zstep. ck KC7. zstep. zstep. zstep. ckx KC8. zstep. ck KC9.
    rd8 HS i. clear HS.
    rd8 HX i.
    zstep. zstep. zstep. zstep. zstep.
    vstep 8%positive. vstep 9%positive. vstep 8%positive.
    wr8 HX LX FX i.
    zstep. zstep.
    zstep. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by lia.
    - eapply (IH (i + 1)); try (f_equal; lia); try lia.
      + exact (conj HX (conj LX (conj FX (conj MU (conj WM (conj MI ST)))))).
      + exact FR.
    - zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
      finish. 1: exact HX. lia. apply same_from_skipn; [exact FX | lia].
  Qed.
End Walk.

Lemma U_ct_memcpy_if_spec : ct_memcpy_if_stmt usegs U_CT_MEMCPY_IF.
Proof.
  unfold ct_memcpy_if_stmt, U_CT_MEMCPY_IF.
  intros until sbs. intros HX HS Hn LX LS DIS S2C NZD NZS DT ST1 ST LO SPA SX SSX MI -> -> -> ->.
  unfold CT_MEMCPY_IF_STACK in *.
  pose proof (u8arr_bound _ _ _ _ HX) as DB. pose proof (bytes_at_bound _ _ _ _ HS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(D, D + n); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (conj HS I) as HSbox.
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  2: zstep.
  (* [comment removed for export] *)
  2: replace (Z_to_bv 64 S2) with (Z_to_bv 64 D) by (f_equal; lia).
  all: zstep; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  1,3: zstep; zstep; release_frame FR ST (bv_unsigned sp); zstep; zstep; finish; [exact HX | reflexivity | reflexivity].
  all: do 10 zstep.
  all: replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia);
       replace (0 <? S1) with true by (symmetry; apply Z.ltb_lt; lia); change (Z.b2z true) with 1.
  all: eapply (@loop_walk) with (k := Z.to_nat n) (i := 0) (ld := Z.of_nat (length dbs)) (ls := Z.of_nat (length sbs));
       try eassumption; try lia; try (f_equal; lia).
  all: try exact (conj HX (conj eq_refl (conj (same_from_refl _ _) (conj MU (conj WM (conj MI ST)))))).
  all: try exact FR.
  all: exact (proj1 HSbox).
Qed.
