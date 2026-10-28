(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells CellsX Step Frame HeapIface Asn1Aux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_crt_parse P_x509_crt_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_crt_ext_area () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell_at"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.XST"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.zeros"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_parse.wbuf"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_v1"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_v2"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_v3"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_v4"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_sct"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_scp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_scl"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_sp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_sn"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_k1"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_k2"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_k3"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_k4"; "RocqVerifyHarness.AgentSubmission.Spec.CrtExtStmts.akid_cells"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_a1"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_a2"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_a3"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_a4"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_act"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_acp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_acl"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ap"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_an"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_r1"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_r2"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_r3"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_r4"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_w1"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_w2"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_w3"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_w4"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pct"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pcp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pcl"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pn"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_et"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ca"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_mp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ku"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ect"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ecp"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ecl"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ep"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_en"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_ns"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_snodes"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_anodes"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_pnodes"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_enodes"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.x_seen"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.CellsX.zero_cells"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.xst"; "Area.xown"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.SEQ_SIZE"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.xblocks"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.seteku"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.setsan"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.setpol"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.setakid"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_ext.setet"].


(* [comment removed for export] *)
Lemma aobj_of_part_shadow_sh : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Psegs,(0.$1.)PAL,$2.PCS,P,$3.SpPm,P,(4.&40.)(5.(4.&8.))PB,$3.Pcs,(0.$6.)PA,$3.Pg0,$7.Pk,$3.P,(8.R8.R7.)P,(9.R:.R7.(:.(;.R6.+3.)(<.R9.))R5.)P,(=.R9.R5.R3.)P,(>.$3.(?.R8.+8.)=)P,(10.=R9.)P,(>.$3.R8.(:.R:.(11.+8.(12.R7.))))P,(13.(14.=R7.)(10.R7.+7.))P,(>.(5.$6.)(15.R;.R9.)(16.$6.(17.(18.&8.R8.))))(19.R11.R10.R?.R>.R;.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs AL CS m B cs A g0 k OK H HC HB H0 HA Hk HZ.
  replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in H
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  split; [exact HC|].
  intros a Ha. exists (Z_to_bv 8 k). split.
  - destruct OK as (C1' & _). ddestruct (C1' a (HC a Ha)) as (R0 & R1 & R2 & _).
    pose proof (rw_cells_read segs m _ cs g0 _ H HZ) as RD. cbn [csize cbytes] in RD.
    assert (E : shadow_of AL a = shadow_of AL B + Z.of_nat g0).
    { unfold shadow_of. subst A. pose proof (Z.div_mod B 8 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). nia. }
    rewrite E. apply bytes_at_of_read1; [lia | lia | exact RD].
  - right. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite (Z.mod_small k) by lia.
    subst A. pose proof (Z.div_mod B 8 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Lemma floc_of_junk : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Psegs,(0.$1.)Pm,P,(4.&40.)(5.(4.&8.))PA,$3.Pjloc,(0.(4.&8.))P,(9.R4.R3.R2.(1:.$6.(1;.#=8.R1.)(1<.$6.)))(1=.(4.&40.)Llenw,(4.&40.)(1=.(4.&40.)Lotg,(4.&40.)(1=.(4.&40.)Lopd,(4.&40.)(1=.(4.&40.)Lolen,(4.&40.)(1=.(4.&40.)Lop,(4.&40.)(1=.(4.&40.)Lcrit,(4.&40.)(1=.(4.&40.)Let,(4.&40.)(1=.(0.(4.&8.))Lj1,(0.(4.&8.))(1=.(0.(4.&8.))Lj2,(0.(4.&8.))(1=.(0.(4.&8.))Lj3,(0.(4.&8.))(1=.(0.(4.&8.))Lj4,(0.(4.&8.))(9.R10.R?.R>.(1:.$6.(1>.R;.)(1:.$6.(1;.#18.R4.)(1:.$6.(1?.R:.)(1:.$6.(1?.R9.)(1:.$6.(1>.R8.)(1:.$6.(1>.R7.)(1:.$6.(1;.#28.R3.)(1:.$6.(1?.R6.)(1:.$6.(1;.#<.R2.)(1:.$6.(1?.R5.)(1:.$6.(1;.#64.R1.)(1<.$6.))))))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m A jloc H.
  assert (LJ : length jloc = 216%nat) by (destruct H as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  set (a0 := firstn 8 jloc). set (r0 := skipn 8 jloc).
  set (a1 := firstn 24 r0). set (r1 := skipn 24 r0).
  set (a2 := firstn 4 r1). set (r2 := skipn 4 r1).
  set (a3 := firstn 4 r2). set (r3 := skipn 4 r2).
  set (a4 := firstn 8 r3). set (r4 := skipn 8 r3).
  set (a5 := firstn 8 r4). set (r5 := skipn 8 r4).
  set (a6 := firstn 40 r5). set (r6 := skipn 40 r5).
  set (a7 := firstn 4 r6). set (r7 := skipn 4 r6).
  set (a8 := firstn 12 r7). set (r8 := skipn 12 r7).
  set (a9 := firstn 4 r8). set (r9 := skipn 4 r8).
  assert (L0 : length r0 = 208%nat) by (subst r0; rewrite length_skipn; lia).
  assert (L1 : length r1 = 184%nat) by (subst r1; rewrite length_skipn; lia).
  assert (L2 : length r2 = 180%nat) by (subst r2; rewrite length_skipn; lia).
  assert (L3 : length r3 = 176%nat) by (subst r3; rewrite length_skipn; lia).
  assert (L4 : length r4 = 168%nat) by (subst r4; rewrite length_skipn; lia).
  assert (L5 : length r5 = 160%nat) by (subst r5; rewrite length_skipn; lia).
  assert (L6 : length r6 = 120%nat) by (subst r6; rewrite length_skipn; lia).
  assert (L7 : length r7 = 116%nat) by (subst r7; rewrite length_skipn; lia).
  assert (L8 : length r8 = 104%nat) by (subst r8; rewrite length_skipn; lia).
  assert (L9 : length r9 = 100%nat) by (subst r9; rewrite length_skipn; lia).
  dexists (le_bytes_to_word a0), (le_bytes_to_word a2), (le_bytes_to_word a3), (le_bytes_to_word a4), (le_bytes_to_word a5),
         (le_bytes_to_word a7), (le_bytes_to_word a9), a1, a6, a8, r9.
  eapply rw_cells_reshape; [exact H| |].
  - cbn [cells_wf cell_wf]. subst a1 a6 a8. rewrite !length_firstn. repeat split; lia.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    rewrite !le8_le_bytes_to_word by (subst a0 a4 a5; rewrite length_firstn; lia).
    rewrite !le4_le_bytes_to_word by (subst a2 a3 a7 a9; rewrite length_firstn; lia).
    subst a9 r9. rewrite (firstn_skipn 4 r8). subst a8 r8. rewrite (firstn_skipn 12 r7). subst a7 r7. rewrite (firstn_skipn 4 r6).
    subst a6 r6. rewrite (firstn_skipn 40 r5). subst a5 r5. rewrite (firstn_skipn 8 r4). subst a4 r4. rewrite (firstn_skipn 8 r3).
    subst a3 r3. rewrite (firstn_skipn 4 r2). subst a2 r2. rewrite (firstn_skipn 4 r1). subst a1 r1. rewrite (firstn_skipn 24 r0).
    subst a0 r0. rewrite (firstn_skipn 8 jloc). reflexivity.
Qed.

(* [comment removed for export] *)
Definition xst_v3 (tg pad : word) (len q : Z) : xst := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "(20.O4.O3.(18.&40.O2.)(18.&40.O1.)(18.&40.=)(18.&40.=)===(1<.$3.)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)===(1<.$3.)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)===(1<.$3.)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)(18.&40.=)===(1<.$3.)(21.#8.)=)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma etn_bits : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Petl,(4.&40.)Pet,(4.&40.)Pb,$3.P,(13.(10.=R1.)(14.R1.(22.+2.+20.)))P,(>.$3.(23.(24.&40.(18.&40.(25.(24.&40.(26.R4.))(24.&40.(26.R3.)))))R2.)=)(13.(>.$3.(23.(24.&40.(26.R5.))R3.)=)(>.$3.(23.(24.&40.R4.)R3.)=))")
(* [comment removed for export] *).
Proof.
  intros etl et b Hb H. rewrite Z_to_bv_unsigned in H. change (bv_wrap 64 ?x) with (x mod 2^64) in H.
  rewrite land_mod_low in H by lia. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2].
  split; [exact H1|]. rewrite <- (land_sx32_low et b Hb). exact H2.
Qed.

Section Area.
  Variable segs : list Segment.
  Variable CRT : Z.
  Local Notation E := (CRT + 424).

  Definition xcells (mc : mem) (X : xst) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "(13.(9.Vsegs,O2.(:.VCRT,+1:8.)(27.(28.O1.)(29.O1.)(2:.O1.)(2;.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+1<0.)(2<.(2=.O1.)(2>.O1.)(2?.O1.)(30.O1.)(31.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+1>0.)(27.(32.O1.)(33.O1.)(34.O1.)(35.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+1?8.)(36.(37.O1.)(38.O1.)(39.O1.)(3:.O1.)(3;.O1.)(3<.O1.)(3=.O1.)(3>.O1.)(3?.O1.)(40.O1.)(41.O1.)(42.O1.)(43.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+248.)(27.(44.O1.)(45.O1.)(46.O1.)(47.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+260.)(2<.(48.O1.)(49.O1.)(4:.O1.)(4;.O1.)(4<.O1.)))(13.(9.Vsegs,O2.(:.VCRT,+280.)(1:.$6.(1?.(4=.O1.))(1:.$6.(1?.(4>.O1.))(1:.$6.(1?.(4?.O1.))(1:.$6.(1?.(50.O1.))(1<.$6.))))))(13.(9.Vsegs,O2.(:.VCRT,+290.)(2<.(51.O1.)(52.O1.)(53.O1.)(54.O1.)(55.O1.)))(9.Vsegs,O2.(:.VCRT,+2;0.)(1:.$6.(1;.#8.(56.O1.))(1<.$6.)))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition xown (mc : mem) (LBx : list blk) (X : xst) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "(13.(13.(>.$3.(31.O1.)(57.$3.=(58.O1.)))(59.Vsegs,L,(0.$6.)$5:.O3.O2.(31.O1.)(58.O1.)))(13.(13.(>.$3.(3?.O1.)(57.$3.=(5;.O1.)))(59.Vsegs,L,(0.$6.)$5:.O3.O2.(3?.O1.)(5;.O1.)))(13.(13.(>.$3.(4<.O1.)(57.$3.=(5<.O1.)))(59.Vsegs,L,(0.$6.)$5:.O3.O2.(4<.O1.)(5<.O1.)))(13.(13.(>.$3.(55.O1.)(57.$3.=(5=.O1.)))(59.Vsegs,L,(0.$6.)$5:.O3.O2.(55.O1.)(5=.O1.)))(13.P,(>.$3.(23.(5>.O1.)+20.)=)(13.(>.$3.(2?.O1.)=)(13.(>.$3.(30.O1.)=)(13.(>.$3.(31.O1.)=)(>.(0.$3.)(58.O1.)(1<.$3.)))))(13.P,(>.$3.(23.(5>.O1.)+1.)=)(13.(>.$3.(3=.O1.)=)(13.(>.$3.(3>.O1.)=)(13.(>.$3.(3?.O1.)=)(>.(0.$3.)(5;.O1.)(1<.$3.)))))(13.P,(>.$3.(23.(5>.O1.)+8.)=)(13.(>.$3.(4:.O1.)=)(13.(>.$3.(4;.O1.)=)(13.(>.$3.(4<.O1.)=)(>.(0.$3.)(5<.O1.)(1<.$3.)))))(13.P,(>.$3.(23.(5>.O1.)+800.)=)(13.(>.$3.(53.O1.)=)(13.(>.$3.(54.O1.)=)(13.(>.$3.(55.O1.)=)(>.(0.$3.)(5=.O1.)(1<.$3.)))))Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.(4=.O1.))R2.)=)(>.$3.(23.(5>.O1.)R3.)=)))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma zeros_app : forall a b, zeros (a + b) = zeros a ++ zeros b.
  Proof. intros. unfold zeros. apply repeat_app. Qed.
  #[using="Type"] Lemma zero_sub : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pmq,P,(4.&40.)(5.(4.&8.))PA,$3.Pnn,$7.Poff,$7.Pcs,(0.$6.)P,(9.Vsegs,R5.R4.(1:.$6.(1;.R3.(21.R3.))(1<.$6.)))P,(60.R2.)P,(61.(62.R4.(63.R3.))R5.)(9.Vsegs,R8.(:.R7.(12.R5.))R4.)")
(* [comment removed for export] *).
  Proof.
    intros mq A nn off cs H Z Hle.
    assert (H3 : rw_cells segs mq A ([CB off (zeros off)] ++ [CB (cells_size cs) (zeros (cells_size cs))] ++ [CB (nn - off - cells_size cs) (zeros (nn - off - cells_size cs))])).
    { eapply rw_cells_reshape; [exact H| cbn; unfold zeros; rewrite !repeat_length; repeat split; reflexivity|].
      cbn [cells_bytes cbytes app]. rewrite !app_nil_r. rewrite <- !zeros_app. f_equal. lia. }
    destruct (rw_cells_split3 segs mq A _ _ _ H3) as (_ & H2 & _). cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2.
    unfold zeros in H2. eapply rw_cells_zeros; [exact H2| exact Z| reflexivity].
  Qed.

  #[using="Type"] Lemma xcells_zero : forall mc, rw_cells segs mc E [CB 272 (zeros 272)] -> xcells mc xst_zero.
  Proof.
    intros mc CZq. unfold xcells, xst_zero, wbuf, akid_cells, seq_cells.
    cbn [x_v1 x_v2 x_v3 x_v4 x_sct x_scp x_scl x_sp x_sn x_k1 x_k2 x_k3 x_k4 x_a1 x_a2 x_a3 x_a4 x_act x_acp x_acl x_ap x_an x_r1 x_r2 x_r3 x_r4
         x_w1 x_w2 x_w3 x_w4 x_pct x_pcp x_pcl x_pp x_pn x_et x_ca x_mp x_ku x_ect x_ecp x_ecl x_ep x_en x_ns app].
    repeat match goal with |- _ /\ _ => split end.
    1: pose proof (zero_sub mc E 272 0 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] CZq ltac:(cbn; repeat split; reflexivity) ltac:(cbn; lia)) as H;
       rewrite Z.add_0_r in H; exact H.
    all: lazymatch goal with |- rw_cells _ _ (CRT + ?off) ?cs =>
           let offn := eval vm_compute in (Z.to_nat (off - 424)) in
           pose proof (zero_sub mc E 272 offn cs CZq ltac:(cbn; repeat split; reflexivity) ltac:(cbn; lia)) as H;
           let v := eval vm_compute in (Z.of_nat offn) in change (Z.of_nat offn) with v in H;
           replace (E + v) with (CRT + off) in H by lia; exact H end.
  Qed.

  #[using="Type"] Lemma xown_zero : forall mc LBx, xown mc LBx xst_zero.
  Proof. intros mc LBx. unfold xown, xst_zero. cbn -[Z.land bv_unsigned]. repeat split; try reflexivity; intros b _ _; apply Z.land_0_l. Qed.

  #[using="Type"] Lemma xown_v3 : forall mc LBx tg pad len q, xown mc LBx (xst_v3 tg pad len q).
  Proof. intros mc LBx tg pad len q. unfold xown, xst_v3. cbn -[Z.land bv_unsigned]. repeat split; try reflexivity; intros b _ _; apply Z.land_0_l. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma xown_tr : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "PmA,P,(4.&40.)(5.(4.&8.))PmB,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)PX,$65.P,(66.R5.R3.R1.)P,Pb,$64.P,(67.$64.R1.R5.)(67.$64.R2.R5.)P,Px,$3.Pcs,(0.$6.)P,(67.(68.$3.$3.)(69.$3.$3.R2.$6:.)(6;.R5.))P,(9.Vsegs,R:.R3.R2.)P,(>.$3.(12.(63.R3.))$6:.)(9.Vsegs,R;.R5.R4.)(66.R7.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros mA mB Lp Lp' X XO HS HT.
    ddestruct XO as ((E1 & Q1) & (E2 & Q2) & (E3 & Q3) & (E4 & Q4) & REST).
    assert (INS : forall l x, In x l -> In (x, SEQ_SIZE) (SSEQ l)) by (intros l x Hx; unfold SSEQ; apply (in_map (fun a => (a, SEQ_SIZE))); exact Hx).
    assert (T : forall a nodes, (forall x, In x nodes -> In (x, SEQ_SIZE) (xblocks X)) ->
                seq_chain segs (fun _ => True) mA Lp a nodes -> seq_chain segs (fun _ => True) mB Lp' a nodes).
    { intros a nodes HX HC. eapply chain_mem; [exact HC| intros x Hx; apply HS; eapply chain_nodes_in; [exact HC| exact Hx]|].
      intros x cs Hx HR Hsz. eapply HT; [apply HX; exact Hx| exact HR| exact Hsz]. }
    unfold xblocks in T.
    refine (conj (conj E1 (T _ _ _ Q1)) (conj (conj E2 (T _ _ _ Q2)) (conj (conj E3 (T _ _ _ Q3)) (conj (conj E4 (T _ _ _ Q4)) REST)))).
    - intros x Hx. apply in_or_app; right; apply in_or_app; left. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; left. apply INS. exact Hx.
  Qed.

  #[using="Type"] Lemma seq_chain_sub : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pm,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)Pa,$3.Pnodes,(0.$3.)P,(59.Vsegs,L,(0.$6.)$5:.R5.R4.R2.R1.)P,Pb,$64.P,(67.$64.R1.R6.)(67.$64.R2.R6.)(59.Vsegs,L,(0.$6.)$5:.R7.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m Lp Lp' a nodes HC HS. eapply chain_mem; [exact HC| intros x Hx; apply HS; eapply chain_nodes_in; [exact HC| exact Hx]|].
    intros x cs _ HR _. exact HR.
  Qed.
  #[using="Type"] Lemma SSEQ_rev : forall l, Permutation (SSEQ (rev l)) (SSEQ l).
  Proof. intros l. unfold SSEQ. apply Permutation_map. apply Permutation_sym. apply Permutation_rev. Qed.

  (* [comment removed for export] *)
  Local Ltac xown_set_tac XO HS HZ HSUB Hcn CH :=
    destruct XO as ((E1 & Q1) & (E2 & Q2) & (E3 & Q3) & (E4 & Q4) & XZ1 & XZ2 & XZ3 & XZ4 & SUBo);
    unfold xown, seteku, setsan, setpol, setakid; cbn -[Z.land Z.lor bv_unsigned];
    repeat match goal with
    | |- (_ = hd 0 _ /\ seq_chain _ _ _ _ _ _) /\ _ => split; [split; first [exact Hcn | assumption | idtac]; first [exact CH | eapply seq_chain_sub; [eassumption| exact HS]]|]
    end;
    repeat match goal with
    | |- (Z.land (Z.lor _ _) _ = 0 -> _) /\ _ =>
        split; [let Hb := fresh "Hb" in intros Hb; rewrite Z.land_lor_distr_l in Hb;
                first [ exfalso; pose proof (proj2 (proj1 (Z.lor_eq_0_iff _ _) Hb)) as Hb2; vm_compute in Hb2; discriminate Hb2
                      | match goal with XZ : _ -> _ |- _ => apply XZ; exact (proj1 (proj1 (Z.lor_eq_0_iff _ _) Hb)) end ]|]
    end;
    exact HSUB.

  #[using="Type"] Lemma xown_seteku : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pm,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)P,(66.R:.R9.R7.)P,Pb,$64.P,(67.$64.R1.R;.)(67.$64.R2.R;.)P,Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.(4=.R;.))R2.)=)(>.$3.(23.(25.(5>.R<.)+800.)R3.)=)P,(>.$3.R5.(57.$3.=R4.))P,(59.Vsegs,L,(0.$6.)$5:.R>.R<.R6.R5.)(66.R?.R=.(6<.R<.R;.R:.R9.R8.R7.R6.(25.(5>.R<.)+800.)))")
(* [comment removed for export] *).
  Proof. intros m Lp Lp' X ct cp cl cq cn nodes XO HS HSUB Hcn CH. xown_set_tac XO HS HZ HSUB Hcn CH. Qed.
  #[using="Type"] Lemma xown_setsan : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pm,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)P,(66.R:.R9.R7.)P,Pb,$64.P,(67.$64.R1.R;.)(67.$64.R2.R;.)P,Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.(4=.R;.))R2.)=)(>.$3.(23.(25.(5>.R<.)+20.)R3.)=)P,(>.$3.R5.(57.$3.=R4.))P,(59.Vsegs,L,(0.$6.)$5:.R>.R<.R6.R5.)(66.R?.R=.(6=.R<.R;.R:.R9.R8.R7.R6.(25.(5>.R<.)+20.)))")
(* [comment removed for export] *).
  Proof. intros m Lp Lp' X ct cp cl cq cn nodes XO HS HSUB Hcn CH. xown_set_tac XO HS HZ HSUB Hcn CH. Qed.
  #[using="Type"] Lemma xown_setpol : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pm,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)P,(66.R:.R9.R7.)P,Pb,$64.P,(67.$64.R1.R;.)(67.$64.R2.R;.)P,Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.(4=.R;.))R2.)=)(>.$3.(23.(25.(5>.R<.)+8.)R3.)=)P,(>.$3.R5.(57.$3.=R4.))P,(59.Vsegs,L,(0.$6.)$5:.R>.R<.R6.R5.)(66.R?.R=.(6>.R<.R;.R:.R9.R8.R7.R6.(25.(5>.R<.)+8.)))")
(* [comment removed for export] *).
  Proof. intros m Lp Lp' X ct cp cl cq cn nodes XO HS HSUB Hcn CH. xown_set_tac XO HS HZ HSUB Hcn CH. Qed.
  #[using="Type"] Lemma xown_setakid : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pm,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PLp',(0.$64.)PX,$65.Pk1,(4.&40.)Pk2,(4.&40.)Pk3,(4.&40.)Pk4,(4.&40.)Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)Pr1,(4.&40.)Pr2,(4.&40.)Pr3,(4.&40.)Pr4,(4.&40.)P,(66.R12.R11.R?.)P,Pb,$64.P,(67.$64.R1.R13.)(67.$64.R2.R13.)P,Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.(4=.R13.))R2.)=)(>.$3.(23.(25.(5>.R14.)+1.)R3.)=)P,(>.$3.R9.(57.$3.=R8.))P,(59.Vsegs,L,(0.$6.)$5:.R16.R14.R:.R9.)(66.R17.R15.(6?.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.(25.(5>.R14.)+1.)))")
(* [comment removed for export] *).
  Proof. intros m Lp Lp' X k1 k2 k3 k4 ct cp cl cq cn nodes r1 r2 r3 r4 XO HS HSUB Hcn CH. xown_set_tac XO HS HZ HSUB Hcn CH. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma perm_mid : forall (A B C : list blk), Permutation (B ++ A ++ C) (A ++ B ++ C).
  Proof. intros A B C. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.
  #[using="Type"] Lemma xblocks_seteku : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "PLx,(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)Pseen,$3.P,(70.$64.R9.(6;.R8.))P,(>.(0.$3.)(5=.R9.)(1<.$3.))(70.$64.(71.$64.(72.(73.$3.R4.))R;.)(6;.(6<.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros Lx X ct cp cl cq cn nodes seen PERM Z4. unfold xblocks, seteku in *. cbn -[app map rev SSEQ]. rewrite Z4 in PERM. cbn [SSEQ map app] in PERM.
    apply Permutation_app; [apply SSEQ_rev| exact PERM].
  Qed.
  #[using="Type"] Lemma xblocks_setsan : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "PLx,(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)Pseen,$3.P,(70.$64.R9.(6;.R8.))P,(>.(0.$3.)(58.R9.)(1<.$3.))(70.$64.(71.$64.(72.(73.$3.R4.))R;.)(6;.(6=.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros Lx X ct cp cl cq cn nodes seen PERM Z4. unfold xblocks, setsan in *. cbn -[app map rev SSEQ]. rewrite Z4 in PERM. cbn [SSEQ map app] in PERM.
    eapply Permutation_trans; [apply Permutation_app; [apply SSEQ_rev| exact PERM]|]. apply perm_mid.
  Qed.
  #[using="Type"] Lemma xblocks_setpol : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "PLx,(0.$64.)PX,$65.Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)Pseen,$3.P,(70.$64.R9.(6;.R8.))P,(>.(0.$3.)(5<.R9.)(1<.$3.))(70.$64.(71.$64.(72.(73.$3.R4.))R;.)(6;.(6>.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros Lx X ct cp cl cq cn nodes seen PERM Z4. unfold xblocks, setpol in *. cbn -[app map rev SSEQ]. rewrite Z4 in PERM. cbn [SSEQ map app] in PERM.
    eapply Permutation_trans; [apply Permutation_app; [apply SSEQ_rev| exact PERM]|].
    rewrite (app_assoc (SSEQ (x_enodes X)) (SSEQ (x_snodes X))). rewrite (app_assoc (SSEQ (x_enodes X)) (SSEQ (x_snodes X)) (SSEQ nodes ++ _)). apply perm_mid.
  Qed.
  #[using="Type"] Lemma xblocks_setakid : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "PLx,(0.$64.)PX,$65.Pk1,(4.&40.)Pk2,(4.&40.)Pk3,(4.&40.)Pk4,(4.&40.)Pct,(4.&40.)Pcp,(4.&40.)Pcl,$3.Pcq,$3.Pcn,$3.Pnodes,(0.$3.)Pr1,(4.&40.)Pr2,(4.&40.)Pr3,(4.&40.)Pr4,(4.&40.)Pseen,$3.P,(70.$64.R11.(6;.R10.))P,(>.(0.$3.)(5;.R11.)(1<.$3.))(70.$64.(71.$64.(72.(73.$3.R8.))R13.)(6;.(6?.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros Lx X k1 k2 k3 k4 ct cp cl cq cn nodes r1 r2 r3 r4 seen PERM Z4. unfold xblocks, setakid in *. cbn -[app map rev SSEQ]. rewrite Z4 in PERM. cbn [SSEQ map] in PERM. rewrite !app_nil_r in PERM.
    eapply Permutation_trans; [apply Permutation_app; [apply SSEQ_rev| exact PERM]|].
    eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma xown_setet : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_area ()) "Pmc,P,(4.&40.)(5.(4.&8.))PLp,(0.$64.)PX,$65.Petn,(4.&40.)P,(66.R4.R3.R2.)P,Pb,$3.P,(5?.(>.$3.R1.+1.)(5?.(>.$3.R1.+8.)(5?.(>.$3.R1.+20.)(>.$3.R1.+800.))))P,(>.$3.(23.(24.&40.R4.)R2.)=)(>.$3.(23.(24.&40.(4=.R6.))R3.)=)(66.R6.R5.(74.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros mc Lp X etn XO HB. ddestruct XO as (C1 & C2 & C3 & C4 & Z1 & Z2 & Z3 & Z4 & SUB).
    unfold xown, setet. cbn -[Z.land bv_unsigned].
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj Z1 (conj Z2 (conj Z3 (conj Z4 _)))))))).
    intros b Hb H0. apply SUB; [exact Hb|]. apply HB; [exact Hb| exact H0].
  Qed.

  #[using="Type"] Lemma xown_ok : forall mc Lp X, xown mc Lp X -> ext_ok segs mc Lp (eo_of X).
  Proof. (intros mc Lp X dd_H; ddestruct dd_H as ((_ & Q1) & (_ & Q2) & (_ & Q3) & (_ & Q4) & _)). exact (conj Q1 (conj Q2 (conj Q3 Q4))). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma xfold : forall mc X, xcells mc X -> rw_cells segs mc E (ext_cells (eo_of X) (ej_of X)).
  Proof.
    intros mc X XC. ddestruct XC as (C0 & C1 & C2 & C3 & C4' & C5 & C6 & C7 & C8').
    pose proof C8' as [[WF8 _] _]. cbn in WF8. destruct WF8 as [LNS _].
    unfold wbuf, seq_cells, akid_cells in *. cbn [app] in C3.
    assert (J : forall A1 A2 cs1 cs2, rw_cells segs mc A1 cs1 -> rw_cells segs mc A2 cs2 -> A2 = A1 + Z.of_nat (cells_size cs1) -> rw_cells segs mc A1 (cs1 ++ cs2)).
    { intros A1 A2 cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app segs mc A1 cs1 cs2)). exact (conj H1 H2). }
    pose proof (J _ _ _ _ C0 C1 ltac:(cbn; lia)) as D1. pose proof (J _ _ _ _ D1 C2 ltac:(cbn; lia)) as D2. pose proof (J _ _ _ _ D2 C3 ltac:(cbn; lia)) as D3.
    pose proof (J _ _ _ _ D3 C4' ltac:(cbn; lia)) as D4. pose proof (J _ _ _ _ D4 C5 ltac:(cbn; lia)) as D5. pose proof (J _ _ _ _ D5 C6 ltac:(cbn; lia)) as D6.
    pose proof (J _ _ _ _ D6 C7 ltac:(cbn; lia)) as D7. pose proof (J _ _ _ _ D7 C8' ltac:(cbn; lia)) as D8.
    eapply rw_cells_reshape; [exact D8| |].
    - unfold ext_cells, ej_of, eo_of, wbuf. cbn [cells_wf cell_wf ej0 ej1 ej2 ej3 ej4 eo_san_next eo_akid_next eo_pol_next eo_eku_next].
      rewrite !cells_bytes_length by (cbn; tauto). cbn. repeat split; try reflexivity. exact LNS.
    - unfold ext_cells, ej_of, eo_of, wbuf. cbn [cells_bytes cbytes app ej0 ej1 ej2 ej3 ej4 eo_san_next eo_akid_next eo_pol_next eo_eku_next].
      repeat rewrite <- app_assoc. reflexivity.
  Qed.
End Area.
