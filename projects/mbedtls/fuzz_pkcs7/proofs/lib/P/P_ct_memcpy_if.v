(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ct_memcpy_if () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "CT_MEMCPY_IF_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Exec.evt"; "ct_memcpy_if_post"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"].


Definition P_CT_MEMCPY_IF : Z := 0x24250.
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
  Hypothesis HS0 : bytes_at psegs m S1 sbs.

  Notation POST := (ct_memcpy_if_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n dbs0 lo m).
  Notation W := [(D, D + n); (bv_unsigned sp - 16, bv_unsigned sp)].
  Notation DINV mm ds := (u8arr psegs mm D ds /\ Z.of_nat (length ds) = ld /\ same_from (Z.to_nat n) ds dbs0
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp)).

  (* [comment removed for export] *)
  #[using="ls sbs Hn Ln L0 LS DIS DB SB NZS SPR LO SX SSX HS0"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_ct_memcpy_if ()) "Pk,$19.Pi,$?.Pds,(4.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwpd,(2.&40.)Pwps,(2.&40.)P,(6.$19.(1<.(12.Vn,R10.))R11.)P,(5.(20.=R11.)(23.R11.Vn,))P,(6.(2.&40.)R4.(26.&40.(11.VD,R12.)))P,(6.(2.&40.)R4.(26.&40.(11.VS1,R13.)))P,(5.(18.$29.R12.VD,R13.)(5.(6.$?.(21.(1:.(2.&8.)R13.))Vld,)(5.(2:.(2.&8.)(1<.Vn,)R13.Vdbs0,)(5.(<.(=.(>.$?.$?.)(10.$?.$?.VD,(11.VD,Vn,))(=.(>.$?.$?.)(10.$?.$?.(12.(13.&40.Vsp,)+10.)(13.&40.Vsp,))(15.(>.$?.$?.))))Vm,R12.)(5.(16.$29.Vm,R12.)(5.(17.$29.R12.)(1=.$29.R12.Vlo,(13.&40.Vsp,))))))))(27.$29.(28.$29.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vn,Vdbs0,Vlo,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,R?.R7.R6.R>.(26.&40.(11.VD,Vn,))R7.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(26.&40.+2426<.)Vfc,(:.(2.&40.))R13.(;.$29.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; (intros i ds mm xt0 xt1 xt2 xa0 xa3 xa6 xa7 xt3 xt4 xt5 xt6 wpd wps Hk Hi -> -> dd_H; ddestruct dd_H as (HX & LX & FX & MU & WM & MI & ST)); [lia|].
    pose proof (bytes_at_transport psegs _ m mm S1 sbs HS0 MU ltac:(cbn [disjoint_from]; rewrite LS; lia)) as HS.
    rd8 HS i. clear HS.
    rd8 HX i.
    vstep 16%positive. vstep 17%positive. vstep 16%positive.
    wr8 HX LX FX i.
    zstep. zstep. zstep. zstep.
    ptr_cases Kl.
    - eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | exact (conj HX (conj LX (conj FX (conj MU (conj WM (conj MI ST))))))].
    - zstep. finish. 1: exact HX. lia. apply same_from_skipn; [exact FX | lia].
  Qed.
End Walk.

Lemma P_ct_memcpy_if_spec : ct_memcpy_if_stmt psegs P_CT_MEMCPY_IF.
Proof.
  unfold ct_memcpy_if_stmt, P_CT_MEMCPY_IF.
  intros until sbs. intros HX HS Hn LX LS DIS S2C NZD NZS DT ST1 ST LO SPA SX SSX MI -> -> -> ->.
  unfold CT_MEMCPY_IF_STACK in *.
  pose proof (u8arr_bound _ _ _ _ HX) as DB. pose proof (bytes_at_bound _ _ _ _ HS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(D, D + n); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  2: zstep.
  (* [comment removed for export] *)
  2: replace (Z_to_bv 64 S2) with (Z_to_bv 64 D) by (f_equal; lia).
  all: zstep; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  1,3: zstep; finish; [exact HX | reflexivity | reflexivity].
  all: vstep 13%positive; zstep.
  all: eapply (@loop_walk) with (k := Z.to_nat n) (i := 0) (ld := Z.of_nat (length dbs)) (ls := Z.of_nat (length sbs));
       try eassumption; try lia; try (f_equal; lia).
  all: exact (conj HX (conj eq_refl (conj (same_from_refl _ _) (conj MU (conj WM (conj MI ST)))))).
Qed.
