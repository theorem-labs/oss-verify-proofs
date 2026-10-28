(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_asn1_get_len () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "asn1_get_len_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"].


Definition U_ASN1_GET_LEN : Z := 0x1e4e4.

Definition asn1_get_len_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_len ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(9.O17.)O6.(:.(2.&40.))R4.(;.O18.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+8.))(11.(>.$4.$4.))))O1.R4.)(5.(12.O18.O1.R4.)(5.(13.O18.R4.)(5.(6.(2.&40.)R10.(14.&40.R3.))(5.(5.(15.-7?.R3.)(16.R3.=))(5.(17.O18.R4.O5.(=.$18.(19.(14.&40.R2.))(11.$18.)))(5.(17.O18.R4.O4.(=.$18.(19.R1.)(11.$18.)))(5.(5.(16.O3.R2.)(16.R2.O2.))P,(6.$4.R3.=)(5.(16.(10.O3.+1.)R3.)(16.(1:.&40.R2.)(1;.O2.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_len_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_len ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Pbs,(1=.(2.&8.))Plenv,(2.&40.)P,(17.O2.R8.R7.(=.$18.(19.(14.&40.R5.))(11.$18.)))P,(17.O2.R9.R7.(=.$18.(19.R2.)(11.$18.)))P,(1>.O2.R:.R5.R4.)P,(16.R6.R8.)P,(16.R9.R8.)P,(16.R9.(10.R8.(1?.(20.(2.&8.)R7.))))P,(15.(10.R9.(1?.(20.(2.&8.)R8.)))(21.+2.+3?.))P,(22.(16.(10.R>.+8.)R=.)(16.(10.R=.+8.)R>.))P,(22.(16.(10.R?.+8.)R;.)(16.(10.R;.(1?.(20.(2.&8.)R:.)))R?.))P,(22.(16.(10.R?.+8.)R<.)(16.(10.R<.(1?.(20.(2.&8.)R;.)))R?.))P,(6.$4.(23.R11.+8.)=)P,(6.$4.(23.R11.+8.)=)P,(15.=R13.)P,(15.=R13.)P,(15.=R11.)P,(13.O2.R17.)P,(6.(2.&40.)R30.(14.&40.R17.))P,(6.(2.&40.)R30.(14.&40.R15.))P,(6.(2.&40.)R30.(14.&40.R18.))(24.O2.(25.O2.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R1:.R19.R18.R17.R1;.)(7.(8.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(14.&40.O1.)R1<.(:.(2.&40.))R1;.(;.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation POST := (asn1_get_len_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END m).


  (* [comment removed for export] *)
  Lemma loop_walk : forall (n cur : Z) (L pw x5 : word) (mm : mem),
    0 <= n <= 4 -> P + 1 <= cur -> cur + n <= END ->
    rw_cells usegs mm PP [C8 pw] -> rw_cells usegs mm LENP [C8 L] -> bytes_at usegs mm BUF bs ->
    munch [(PP, PP + 8); (LENP, LENP + 8)] m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 LENP)
               (Z_to_bv 64 cur) (Z_to_bv 64 n) L (Z_to_bv 64 cur) (Z_to_bv 64 2)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e58c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
  intros n. remember (Z.to_nat n) as k eqn:Hk. revert n Hk.
  induction k as [|k IH]; intros n Hk cur L pw x5 mm Hn Hcur HE HPP HLEN HBUF MU WM MI.
  - assert (Hn0 : n = 0) by lia. subst n.
    lxp_run (PLAN [0x1e58c; 0x1e5b4] [] 120%N).
    all: lxp_ret.
  - assert (Hn1 : 1 <= n) by lia.
    assert (Hk' : k = Z.to_nat (n + -1)) by lia.
    lxp_run (PLAN [0x1e58c; 0x1e5b4] [] 120%N).
  (* [comment removed for export] *)
    all: first [ lxp_at 124300; lxp_apply (IH (n + -1) Hk' (cur + 1)) | lxp_ret ].
Qed.

End Walk.

Lemma U_asn1_get_len_spec : asn1_get_len_stmt usegs U_ASN1_GET_LEN.
Proof.
  unfold asn1_get_len_stmt, U_ASN1_GET_LEN.
  intros until lenv.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1e58c; 0x1e5b4] [] 120%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 124300; lxp_longform nn; lxp_apply loop_walk | lxp_ret ].
Qed.
