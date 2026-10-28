(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require HP_F_memcpy HP_F_memset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_string () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "memcpy_post"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.modulo"; "memset_post"; "Corelib.Init.Logic.iff"; "memcmp_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Peano.ge"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.firstn"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition memcpy_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O17.O16.O15.O14.R?.R>.R=.O13.O12.O5.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.O17.)O6.(9.(2.&40.))R1.(:.O18.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.&40.O5.)(11.(10.&40.O5.)(10.&40.O3.)))(12.(=.$>.$>.)))O1.R1.)(4.(13.O18.O1.R1.)(4.(14.O18.R1.)(4.(15.O18.R1.(10.&40.O5.)(<.$16.(17.(18.(10.&40.O3.))O2.)(12.$16.)))(19.O18.R1.(10.&40.O4.)O2.)))))))))))))))))))))")
(* [comment removed for export] *).

Definition memcpy_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Psrc,(1;.(2.&8.))Pjunk,(1;.(2.&8.))P,(19.O2.R3.(10.&40.R1:.)R2.)P,(5.$1<.(1=.(2.&8.)R3.)(18.(10.&40.R1:.)))P,(15.O2.R5.(10.&40.R1=.)(<.$16.(17.(18.(10.&40.R1;.))R3.)(12.$16.)))P,(1>.(1?.(11.(10.&40.R1=.)(10.&40.R1<.))(10.&40.R1>.))(1?.(11.(10.&40.R1>.)(10.&40.R1<.))(10.&40.R1=.)))P,(14.O2.R7.)(20.O2.(21.O2.R29.R28.R27.R26.R22.R21.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.R20.R1?.R1>.R7.R8.)(6.(7.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(22.&40.O1.)R9.(9.(2.&40.))R8.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition memset_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O16.O15.O14.O13.R?.R>.R=.O12.O11.O4.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O17.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.&40.O4.)(11.(10.&40.O4.)(10.&40.O2.)))(12.(=.$>.$>.)))O1.R1.)(4.(13.O17.O1.R1.)(4.(14.O17.R1.)(15.O17.R1.(10.&40.O4.)(<.$16.(17.(18.(10.&40.O2.))(23.(2.&8.)(22.&8.(24.(10.&40.O3.)+100.))(18.(10.&40.O2.))))(12.$16.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition memset_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(1;.(2.&8.))P,(15.O2.R2.(10.&40.R1:.)(<.$16.(17.(18.(10.&40.R18.))R1.)(12.$16.)))P,(14.O2.R3.)(20.O2.(25.O2.R25.R24.R23.R22.R1>.R1=.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R6.R5.R1<.R1;.R1:.R4.)(6.(7.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(22.&40.O1.)R5.(9.(2.&40.))R4.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition memcmp_post (segs : list Segment) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (xs ys : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Lms',$0.(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.$>.Lr,$>.(4.(5.$0.R7.(6.(7.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.O17.R6.R5.R4.R3.R2.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(8.O1?.)O4.(9.(2.&40.))O1.(:.O20.)))(4.(5.(2.&40.)R6.(22.&40.R1.))(4.(4.(1?.-??.R1.)(1?.R1.+??.))(26.(5.$>.R1.=)(5.(1;.(2.&8.))O3.O2.)))))))))))")
(* [comment removed for export] *).

Definition memcmp_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pxs,(1;.(2.&8.))Pys,(1;.(2.&8.))P,(19.O2.R3.(10.&40.R1;.)R2.)P,(19.O2.R4.(10.&40.R1;.)R2.)P,(5.$1<.(1=.(2.&8.)R4.)(18.(10.&40.R1;.)))P,(5.$1<.(1=.(2.&8.)R4.)(18.(10.&40.R1<.)))(20.O2.(27.O2.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R6.R5.R7.)(6.(7.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(22.&40.O1.)R8.(9.(2.&40.))R7.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma U_memcpy_spec : memcpy_stmt usegs 0x46a40.
Proof. exact HP_F_memcpy.memcpy_spec. Qed.

Lemma U_memset_spec : memset_stmt usegs 0x46e44.
Proof. exact HP_F_memset.memset_spec. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_S_nth {A} (l : list A) i x : nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
  revert i. induction l as [|a l IH]; intros [|i] H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. f_equal. apply IH. exact H.
Qed.

Section Memcmp.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).

  (* [comment removed for export] *)
  #[using="Type"] Lemma memcmp_loop : ltac2:(CDefT.buildp (gd_tbl_P_string ()) "Pk,$1<.PP0,$>.PQ0,$>.Pxs0,(1;.(2.&8.))Pys0,(1;.(2.&8.))Pp,$>.Pq,$>.Pa3,(2.&40.)Pa4,(2.&40.)P,(19.$28.Vm,R8.R6.)P,(19.$28.Vm,R8.R6.)P,(5.$1<.(1=.(2.&8.)R8.)(1=.(2.&8.)R7.))P,(1?.R;.R7.)P,(1?.R;.R7.)P,(5.$>.(29.R9.R=.)(29.R8.R<.))P,(2:.R?.#1.)P,(5.$>.(2;.R10.)(29.(2;.(1=.(2.&8.)R=.))(29.R;.R?.)))P,(5.(1;.(2.&8.))(2<.(2.&8.)(18.(29.R<.R10.))R>.)(2<.(2.&8.)(18.(29.R;.R?.))R=.))(20.$28.(27.$28.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,VF,Vfc,R?.R>.Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(22.&40.R=.)(22.&40.R<.)(22.&40.(2;.R12.))R;.R:.Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(22.&40.+46:14.)Vfc,(9.(2.&40.))Vm,(:.$28.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros P0 Q0 xs0 ys0 p q a3 a4 HX HY HL HP HQ HD Hk HK HF; [lia|].
    dpose HX as (X0 & X1 & _). dpose HY as (Y0 & Y1 & _).
    destruct (nth_error xs0 (Z.to_nat (p - P0))) as [x|] eqn:NX; [| apply nth_error_None in NX; lia].
    destruct (nth_error ys0 (Z.to_nat (q - Q0))) as [y|] eqn:NY; [| apply nth_error_None in NY; lia].
    pose proof (u8ro_read usegs m P0 xs0 (p - P0) x _ HX NX ltac:(lia) eq_refl) as RDX.
    pose proof (u8ro_read usegs m Q0 ys0 (q - Q0) y _ HY NY ltac:(lia) eq_refl) as RDY.
    pose proof (bv_unsigned_in_range 8 x) as XR. pose proof (bv_unsigned_in_range 8 y) as YR. unfold bv_modulus in XR, YR. cbn in XR, YR.
    zstep. zstep. zstep.
    if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KE by lia.
      zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists (bv_unsigned x - bv_unsigned y).
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [intros E; exfalso|intros E; exfalso].
      + apply KE. f_equal. lia.
      + subst ys0. rewrite <- HD in NY. replace (Z.to_nat (q - Q0)) with (Z.to_nat (p - P0)) in NY by lia. rewrite NX in NY. injection NY as ->. apply KE. reflexivity.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KE by lia.
      assert (EXY : x = y) by (apply bv_eq; lia).
      zstep. zstep. zstep. zstep.
      if_cases KZ; zify_cond KZ.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KZ by lia.
        replace (Z_to_bv 64 (Z.of_nat (S k) + -1)) with (Z_to_bv 64 (Z.of_nat k)) by (f_equal; lia).
        eapply (IH P0 Q0 xs0 ys0 (p + 1) (q + 1)); try eassumption; try lia.
        replace (Z.to_nat (p + 1 - P0)) with (S (Z.to_nat (p - P0))) by lia.
        replace (Z.to_nat (q + 1 - Q0)) with (S (Z.to_nat (q - Q0))) by lia.
        rewrite (firstn_S_nth xs0 _ x NX), (firstn_S_nth ys0 _ y NY), HF, EXY. reflexivity.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in KZ by lia.
        zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists 0.
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros _|intros _; reflexivity].
        assert (LX : length xs0 = S (Z.to_nat (p - P0))) by lia.
        assert (LY : length ys0 = S (Z.to_nat (q - Q0))) by lia.
        rewrite <- (firstn_all xs0), <- (firstn_all ys0), LX, LY.
        rewrite (firstn_S_nth xs0 _ x NX), (firstn_S_nth ys0 _ y NY), HF, EXY. reflexivity.
  Qed.
End Memcmp.

Lemma memcmp_entry_walk (ENTRY : Z) :
  (ENTRY = 0x46a10 \/ ENTRY = 0x46940) -> memcmp_stmt usegs ENTRY.
Proof.
  intros HE. intros until ys. intros HX HY LX LY.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
  unfold bv_modulus in R0, R1, R2. cbn in R0, R1, R2.
  assert (J : evt usegs (memcmp_post usegs ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc xs ys m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x46a10) fc None m (seg_rom usegs))).
  { zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) zstep. zstep. apply evt_done. unfold memcmp_post. deexists 5. exists 0.
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros _|reflexivity].
      destruct xs; [|cbn in LX; lia]. destruct ys; [reflexivity|cbn in LY; lia].
    - rewrite <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned a1), <- (Z_to_bv_bv_unsigned a2).
      replace (bv_unsigned a2) with (Z.of_nat (length xs)) by lia.
      eapply (memcmp_loop ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (length xs) (bv_unsigned a0) (bv_unsigned a1) xs ys); try eassumption; try lia.
      rewrite !Z.sub_diag. reflexivity. }
  destruct HE as [-> | ->]; [exact J|].
  (* [comment removed for export] *)
  zstep. exact J.
Qed.


Lemma U_bcmp_spec : memcmp_stmt usegs 0x46940.
Proof. apply memcmp_entry_walk. right. reflexivity. Qed.
