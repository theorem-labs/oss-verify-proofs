(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_asn1_get_tag () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "asn1_get_tag_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"].


Definition U_ASN1_GET_TAG : Z := 0x1e5b8.

Definition asn1_get_tag_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(9.O17.)O6.(:.(2.&40.))R4.(;.O18.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+8.))(11.(>.$4.$4.))))O1.R4.)(5.(12.O18.O1.R4.)(5.(13.O18.R4.)(5.(6.(2.&40.)R10.(14.&40.R3.))(5.(5.(15.-7?.R3.)(16.R3.=))(5.(17.O18.R4.O5.(=.$18.(19.(14.&40.R2.))(11.$18.)))(5.(17.O18.R4.O4.(=.$18.(19.R1.)(11.$18.)))(5.(5.(16.O3.R2.)(16.R2.O2.))P,(6.$4.R3.=)(5.(16.(10.O3.+2.)R3.)(16.(1:.&40.R2.)(1;.O2.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_tag_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Pbs,(1=.(2.&8.))Plenv,(2.&40.)Ptag,$4.P,(17.O2.R9.R8.(=.$18.(19.(14.&40.R6.))(11.$18.)))P,(17.O2.R:.R8.(=.$18.(19.R3.)(11.$18.)))P,(1>.O2.R;.R6.R5.)P,(16.R7.R9.)P,(16.R:.R9.)P,(16.R:.(10.R9.(1?.(20.(2.&8.)R8.))))P,(15.(10.R:.(1?.(20.(2.&8.)R9.)))(21.+2.+3?.))P,(22.(16.(10.R?.+8.)R>.)(16.(10.R>.+8.)R?.))P,(22.(16.(10.R10.+8.)R<.)(16.(10.R<.(1?.(20.(2.&8.)R;.)))R10.))P,(22.(16.(10.R10.+8.)R=.)(16.(10.R=.(1?.(20.(2.&8.)R<.)))R10.))P,(6.$4.(23.R12.+8.)=)P,(6.$4.(23.R12.+8.)=)P,(15.=R14.)P,(15.=R14.)P,(15.=R12.)P,(13.O2.R18.)P,(6.(2.&40.)R31.(14.&40.R18.))P,(6.(2.&40.)R31.(14.&40.R16.))P,(6.(2.&40.)R31.(14.&40.R19.))P,(6.(2.&40.)R31.(14.&40.R14.))(24.O2.(25.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1<.R1;.R1:.R19.R1=.)(7.(8.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(14.&40.O1.)R1>.(:.(2.&40.))R1=.(;.O2.)))")
(* [comment removed for export] *).


Lemma land_127_range : forall x, 0 <= Z.land (Z.land x 255) 127 <= 127.
Proof.
  intros x. split. apply Z.land_nonneg; right; lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. rewrite Z.ones_equiv.
  pose proof (Z.mod_pos_bound (Z.land x 255) (2^7) ltac:(lia)) as H. change (2^7) with 128 in *. cbn. lia.
Qed.

Lemma longform_n : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Pnn,$4.P,(5.(16.=R1.)(16.R1.+7?.))P,(16.+???????????????<.(23.(10.R2.-5.)+10000000000000000.))(5.(16.+1.R3.)(16.R3.+4.))")
(* [comment removed for export] *).
Proof.
  intros nn NR Kn.
  destruct (Z_lt_le_dec nn 5) as [Hl|Hl]; [| rewrite Z.mod_small in Kn by lia; lia].
  destruct (Z_le_gt_dec nn 0) as [Hz|Hz]; [| ].
  - exfalso. assert (E0 : nn = 0) by lia. subst nn. vm_compute in Kn. exact (Kn eq_refl).
  - replace ((nn + -5) mod 18446744073709551616) with (nn + -5 + 18446744073709551616) in Kn; [lia|].
    rewrite <- (Z.mod_small (nn + -5 + 18446744073709551616) 18446744073709551616) by lia.
    rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Local Ltac bvu_ranges :=
  repeat match goal with
  | H : context [bv_unsigned ?w] |- _ => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  | |- context [bv_unsigned ?w] => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  end.

Local Ltac len_bridge :=
  let ms2 := fresh "ms" in let HQ := fresh "HQ" in
  intros ms2 HQ; unfold asn1_get_len_post in HQ; unfold asn1_get_tag_post;
  destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU2 & WM2 & MI2 & A02 & RB2 & HPP2 & HLEN2 & PB2 & HR2);
  do 19 eexists;
  split; [reflexivity|]; split; [eapply munch_trans; eassumption|]; split; [eapply wmono_trans; eassumption|];
  split; [exact MI2|]; split; [exact A02|]; split; [exact RB2|]; split; [exact HPP2|]; split; [exact HLEN2|];
  split; [lia|]; intros R0; specialize (HR2 R0); lia.

Local Ltac tail_len ppv lenp endv bufv bsv :=
  lxp_gc;
  lazymatch goal with H : rw_cells _ _ ppv [C8 (Z_to_bv 64 ?p)] |- _ =>
    let SP := fresh "SP" in
    pose proof U_asn1_get_len_spec as SP; unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SP;
    eapply evt_mono;
    [ eapply SP with (PP := ppv) (LENP := lenp) (P := p) (END := endv) (BUF := bufv) (bs := bsv);
      first [ eassumption | reflexivity | lia | (bvu_ranges; lia) ]
    | clear SP; len_bridge ]
  end.

Lemma U_asn1_get_tag_spec : asn1_get_tag_stmt usegs U_ASN1_GET_TAG.
Proof.
  unfold asn1_get_tag_stmt, U_ASN1_GET_TAG.
  intros until tag.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI -> -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1e4e4; 0x1e600] [] 60%N).
  all: first [ lxp_at 124132; tail_len PP LENP END BUF bs | lxp_ret ].
Qed.
