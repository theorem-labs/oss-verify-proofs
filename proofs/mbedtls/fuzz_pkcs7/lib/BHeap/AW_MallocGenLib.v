(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX Tac Frame Step Cells.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_MallocGenLib () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Nat.add"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Peano.lt"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.Lists.List.nth_error"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_GetFrom.cpy"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate2.carve_list"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.mul"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma le_small_word : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pk,$0.Pbs,(1.(2.&8.))P,(3.$0.(4.(2.&8.)R1.)R2.)P,(5.R3.#8.)(3.(1.(2.&8.))(6.R4.(7.&40.(8.R3.)))R3.)")
(* [comment removed for export] *).
Proof.
  intros k bs L K. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Mem.Z_to_le_bytes_mod by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

#[using="Type"] Lemma rw_cells_CB4_C4 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Ppre,(1.$;.)Pbs,(1.(2.&8.))Ppost,(1.$;.)P,(<.Vsegs,R5.R4.(=.$;.R3.(>.$;.(?.#4.R2.)R1.)))(<.Vsegs,R6.R5.(=.$;.R4.(>.$;.(10.(8.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros m A pre bs post H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [L _]]. cbn in L.
  eapply rw_cells_reshape; [exact H| |].
  - apply cells_wf_app. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. split; [exact H1| split; [exact I| exact H3]].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold le4. rewrite le_small_word by (try exact L; lia). reflexivity.
Qed.
#[using="Type"] Lemma rw_cells_CB2_C2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Ppre,(1.$;.)Pbs,(1.(2.&8.))Ppost,(1.$;.)P,(<.Vsegs,R5.R4.(=.$;.R3.(>.$;.(?.#2.R2.)R1.)))(<.Vsegs,R6.R5.(=.$;.R4.(>.$;.(11.(8.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros m A pre bs post H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [L _]]. cbn in L.
  eapply rw_cells_reshape; [exact H| |].
  - apply cells_wf_app. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. split; [exact H1| split; [exact I| exact H3]].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold le2. rewrite le_small_word by (try exact L; lia). reflexivity.
Qed.
#[using="Type"] Lemma rw_cells_CB1_C1 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Ppre,(1.$;.)Pb,(2.&8.)Ppost,(1.$;.)P,(<.Vsegs,R5.R4.(=.$;.R3.(>.$;.(?.#1.(>.(2.&8.)R2.(12.(2.&8.))))R1.)))(<.Vsegs,R6.R5.(=.$;.R4.(>.$;.(13.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros m A pre b post H. eapply rw_cells_reshape; [exact H| |].
  - apply cells_wf_app. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. split; [exact H1| split; [exact I| exact H3]].
  - rewrite !cells_bytes_app. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CB_sub : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Pn,$0.Pbs,(1.(2.&8.))Po,$0.Pk,$0.P,(<.Vsegs,R6.R5.(>.$;.(?.R4.R3.)(12.$;.)))P,(5.(14.R3.R2.)R5.)(<.Vsegs,R8.(15.R7.(16.R4.))(>.$;.(?.R3.(17.(2.&8.)R3.(18.(2.&8.)R4.R5.)))(12.$;.)))")
(* [comment removed for export] *).
Proof.
  intros m A n bs o k H Hk. dpose H as [[[L _] _] _]. cbn in L.
  pose proof (rw_cells_split_CB segs m A [] n bs [] [o; k; n - o - k]%nat) as X. cbn [app mk_CB_cells sum_nat] in X.
  specialize (X H ltac:(lia)).
  apply (proj1 (rw_cells_app segs m A [CB o _] _)) in X. destruct X as [_ X]. cbn [cells_size csize Nat.add] in X.
  apply (proj1 (rw_cells_app segs m _ [CB k _] _)) in X. destruct X as [X _]. rewrite Nat.add_0_r in X. exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CB_merge : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Pn1,$0.Pb1,(1.(2.&8.))Pn2,$0.Pb2,(1.(2.&8.))P,(<.Vsegs,R6.R5.(>.$;.(?.R4.R3.)(12.$;.)))P,(<.Vsegs,R7.(15.R6.(16.R5.))(>.$;.(?.R3.R2.)(12.$;.)))(<.Vsegs,R8.R7.(>.$;.(?.(14.R6.R4.)(=.(2.&8.)R5.R3.))(12.$;.)))")
(* [comment removed for export] *).
Proof.
  intros m A n1 b1 n2 b2 H1 H2. dpose H1 as [[[L1 _] _] _]. dpose H2 as [[[L2 _] _] _]. cbn in L1, L2.
  assert (H : rw_cells segs m A ([CB n1 b1] ++ [CB n2 b2])) by (apply rw_cells_app; split; [exact H1| cbn [cells_size csize]; rewrite Nat.add_0_r; exact H2]).
  eapply rw_cells_reshape; [exact H| cbn; rewrite app_length; split; [lia| exact I]| cbn; rewrite !app_nil_r; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CB16_hdr : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Pbs,(1.(2.&8.))P,(<.Vsegs,R3.R2.(>.$;.(?.#10.R1.)(12.$;.)))(19.(2.&8.)Lb0,(2.&8.)(19.(2.&8.)Lb1,(2.&8.)(19.(2.&40.)Lw2,(2.&40.)(19.(2.&40.)Lw4,(2.&40.)(19.(2.&40.)Lw8,(2.&40.)(<.Vsegs,R9.R8.(>.$;.(13.R5.)(>.$;.(13.R4.)(>.$;.(11.R3.)(>.$;.(10.R2.)(>.$;.(1:.R1.)(12.$;.))))))))))))")
(* [comment removed for export] *).
Proof.
  intros m A bs H. dpose H as [[[L _] _] _]. cbn in L.
  pose proof (rw_cells_split_CB segs m A [] 16 bs [] [1; 1; 2; 4; 8]%nat H eq_refl) as X. cbn [app mk_CB_cells] in X.
  destruct bs as [|b0 [|b1 bs]]; try discriminate L. cbn [firstn skipn] in X.
  apply (rw_cells_CB1_C1 m A [] b0) in X. apply (rw_cells_CB1_C1 m A [C1 b0] b1) in X.
  apply (rw_cells_CB2_C2 m A [C1 b0; C1 b1]) in X. apply (rw_cells_CB4_C4 m A [C1 b0; C1 b1; C2 _]) in X.
  apply (rw_cells_CB8_C8 segs m A [C1 b0; C1 b1; C2 _; C4 _]) in X. cbn [app] in X.
  deexists 5. exact X.
Qed.
#[using="Type"] Lemma CB16_words : forall m A bs, rw_cells segs m A [CB 16 bs] -> exists g0 g1, rw_cells segs m A [C8 g0; C8 g1].
Proof.
  intros m A bs H. pose proof (rw_cells_split_CB segs m A [] 16 bs [] [8; 8]%nat H eq_refl) as X. cbn [app mk_CB_cells] in X.
  apply (rw_cells_CB8_C8 segs m A []) in X. apply (rw_cells_CB8_C8 segs m A [C8 _]) in X. cbn [app] in X. deexists 2. exact X.
Qed.
#[using="Type"] Lemma CB1_byte : forall m A bs, rw_cells segs m A [CB 1 bs] -> exists b, rw_cells segs m A [C1 b].
Proof.
  intros m A bs H. dpose H as [[[L _] _] _]. cbn in L. destruct bs as [|b [|]]; try discriminate L.
  exists b. apply (rw_cells_CB1_C1 m A []). exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CB_holed : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "PW,(1.$1;.)Pm,P,(2.&40.)(9.(2.&8.))Pm',P,(2.&40.)(9.(2.&8.))PA,$:.Pn,$0.Pbs,(1.(2.&8.))P,(<.Vsegs,R5.R3.(>.$;.(?.R2.R1.)(12.$;.)))P,(1<.R7.R6.R5.)P,(1=.Vsegs,R7.R6.)P,Pi,$0.P,(1>.R1.R6.)(3.(9.$1?.)(20.Vsegs,(15.R8.(16.R2.))+1.)(21.$1?.))(19.(1.(2.&8.))Lbs',(1.(2.&8.))(22.(<.Vsegs,R9.R8.(>.$;.(?.R7.R1.)(12.$;.)))Pi,$0.P,(1>.R1.R8.)P,(23.R=.(15.R:.(16.R2.)))(3.(9.(2.&8.))(24.(2.&8.)R4.R3.)(24.(2.&8.)R9.R3.))))")
(* [comment removed for export] *).
Proof.
  (intros W m m' A n bs dd_H; ddestruct dd_H as [[[L _] (A0 & A1 & HB)] (_ & _ & HW)]; intros MU WM NOSEG). cbn [cells_bytes cbytes cells_size csize] in L, HB, HW, A1.
  rewrite app_nil_r in HB, A1. rewrite Nat.add_0_r in HW. rewrite L in A1.
  set (rd := fun i : nat => match m' (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (UA : forall i, (i < n)%nat -> bv_unsigned (wa (A + Z.of_nat i)) = A + Z.of_nat i) by (intros i Hi; apply wa_unsigned; lia).
  assert (PRES : forall i, (i < n)%nat -> m' (wa (A + Z.of_nat i)) = Some (rd i)).
  { intros i Hi. specialize (HW (Z.of_nat i) ltac:(lia)). specialize (WM _ HW). unfold wview in WM. subst rd. cbn beta.
    destruct (m' (wa (A + Z.of_nat i))) as [b|] eqn:E; [reflexivity|]. exfalso. rewrite UA in WM by exact Hi. rewrite (NOSEG i Hi) in WM. apply WM. reflexivity. }
  exists (map rd (seq 0 n)).
  assert (LM : length (map rd (seq 0 n)) = n) by (rewrite map_length, seq_length; reflexivity).
  split.
  - split; [split; [cbn; split; [exact LM| exact I]|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact A0| split; [rewrite LM; exact A1|]].
      intros i Hi. rewrite LM in Hi. unfold mrd. rewrite (PRES i Hi). rewrite nth_error_map, nth_error_seq.
      replace (Nat.ltb i n) with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact A0| split; [exact A1|]].
      intros j Hj. apply WM. apply HW. exact Hj.
  - intros i Hi HO. rewrite nth_error_map, nth_error_seq. replace (Nat.ltb i n) with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
    rewrite <- (HB i ltac:(rewrite L; exact Hi)). unfold mrd. rewrite <- (MU (wa (A + Z.of_nat i))) by (rewrite UA by exact Hi; exact HO).
    rewrite (PRES i Hi). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_C1_at : forall m A b, rw_cells segs m A [C1 b] -> find_segment segs A 1 = None -> m (wa A) = Some b.
Proof.
  (intros m A b dd_H; ddestruct dd_H as [[[_ _] (A0 & A1 & HB)] (_ & _ & HW)]; intros NOSEG). cbn [cells_bytes cbytes cells_size csize app length] in HB, HW, A1.
  specialize (HB 0%nat ltac:(cbn; lia)). specialize (HW 0 ltac:(lia)). rewrite Z.add_0_r in HB, HW. cbn [nth_error] in HB.
  unfold mrd in HB. unfold wview in HW. rewrite wa_unsigned in HW by lia. rewrite NOSEG in HW.
  destruct (m (wa A)) as [b'|]; [exact HB| exfalso; apply HW; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma byte_mono : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "PW,(1.$1;.)Pm,P,(2.&40.)(9.(2.&8.))Pm',P,(2.&40.)(9.(2.&8.))PA,$:.Pb,(2.&8.)P,(<.Vsegs,R4.R2.(>.$;.(13.R1.)(12.$;.)))P,(1<.R6.R5.R4.)P,(1=.Vsegs,R6.R5.)P,(3.(9.$1?.)(20.Vsegs,R5.+1.)(21.$1?.))(19.(2.&8.)Lb',(2.&8.)(<.Vsegs,R8.R7.(>.$;.(13.R1.)(12.$;.))))")
(* [comment removed for export] *).
Proof.
  intros W m m' A b H MU WM NS.
  assert (H1 : rw_cells segs m A [CB 1 [b]]) by (eapply rw_cells_reshape; [exact H| cbn; tauto| reflexivity]).
  destruct (CB_holed W m m' A 1 [b] H1 MU WM ltac:(intros i Hi; replace (A + Z.of_nat i) with A by lia; exact NS)) as [bs' [H' _]].
  exact (CB1_byte m' A bs' H').
Qed.

End WithSegs.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
#[using="Type"] Lemma find_segment_none_above' : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pl,(1.$1?.)Pz,$:.Pn,$:.P,(25.$1?.Ls,$1?.(26.(15.(27.(28.R1.))(27.(29.R1.)))+65?000.)R3.)P,(26.+65?000.R3.)P,(2:.=R3.)(3.(9.$1?.)(20.R6.R5.R4.)(21.$1?.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [HS HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. exfalso. clear - E2 HS Hz Hn. lia.
  - apply IH; assumption.
Qed.
#[using="Type"] Lemma asegs_end' : Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) asegs.
Proof.
  assert (E : List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) asegs = [286720; 987136; 1011712; 6680576]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) l = [286720; 987136; 1011712; 6680576] ->
              Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E2 E3 E4. repeat constructor; lia. }
  exact (G _ E).
Qed.
#[using="Type"] Lemma asegs_none : forall z n, 0x65f000 <= z -> 0 < n -> find_segment asegs z n = None.
Proof. intros z n Hz Hn. apply find_segment_none_above'; [exact asegs_end'| exact Hz| exact Hn]. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma find_segment_none_off' : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pl,(1.$1?.)Pz,$:.Pn,$:.P,(25.$1?.Ls,$1?.(22.(26.+10000.(27.(28.R1.)))(26.(15.(27.(28.R1.))(27.(29.R1.)))+65?000.))R3.)P,(2;.(26.(15.R3.R2.)+10000.)(26.+65?000.R3.))P,(2:.=R3.)(3.(9.$1?.)(20.R6.R5.R4.)(21.$1?.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [[HS1 HS2] HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. exfalso. pose proof (N2Z.is_nonneg (seg_size s)). clear - E1 E2 HS1 HS2 Hz Hn H. lia.
  - apply IH; assumption.
Qed.
#[using="Type"] Lemma asegs_lohi' : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "(25.$1?.Ls,$1?.(22.(26.+10000.(27.(28.R1.)))(26.(15.(27.(28.R1.))(27.(29.R1.)))+65?000.))$2<.)")
(* [comment removed for export] *).
Proof.
  assert (E : List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) asegs = [(65536, 286720); (286720, 987136); (987136, 1011712); (1011712, 6680576)]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s))) l = [(65536, 286720); (286720, 987136); (987136, 1011712); (1011712, 6680576)] ->
              Forall (fun s => 0x10000 <= Z.of_N (seg_base s) /\ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E1' E2 E2' E3 E3' E4 E4'. repeat constructor; lia. }
  exact (G _ E).
Qed.
#[using="Type"] Lemma asegs_none_off : forall z n, (z + n <= 0x10000 \/ 0x65f000 <= z) -> 0 < n -> find_segment asegs z n = None.
Proof. intros z n Hz Hn. apply find_segment_none_off'; [exact asegs_lohi'| exact Hz| exact Hn]. Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AW_GetFrom AW_Populate2.

#[using="Type"] Lemma In_firstn_of_nth : forall {A} (l : list A) i k x, nth_error l i = Some x -> (i < k)%nat -> In x (firstn k l).
Proof.
  intros A l i k x H Hk. apply (nth_error_In _ i). rewrite nth_error_firstn. replace (Nat.ltb i k) with true by (symmetry; apply Nat.ltb_lt; exact Hk). exact H.
Qed.

#[using="Type"] Lemma cpy_last : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pk,$0.Pws,(1.(2.&40.))Pds,(1.(2.&40.))P,(3.$0.(4.(2.&40.)R2.)R3.)P,(1>.#0.R4.)(19.(2.&40.)Lw,(2.&40.)(22.(3.(9.(2.&40.))(24.(2.&40.)R5.(2=.R6.#1.))(2>.(2.&40.)R1.))(3.(9.(2.&40.))(24.(2.&40.)(2?.R6.R5.R4.)(2=.R6.#1.))(2>.(2.&40.)(30.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros k ws ds L Hk. destruct (nth_error ws (k - 1)) as [w|] eqn:E.
  - exists w. split; [reflexivity|]. unfold cpy. rewrite firstn_all2 by lia. rewrite nth_error_app1 by (rewrite length_map; lia).
    rewrite nth_error_map, E. reflexivity.
  - exfalso. apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma sx32_mod32 : forall v, bv_unsigned (sx32 v) mod 2^32 = bv_unsigned v mod 2^32.
Proof.
  intros v. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). change (bv_modulus 64) with (2^32 * 2^32).
  rewrite Z.rem_mul_r by lia.
  set (x := bv_unsigned v). rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. rewrite Zminus_mod_idemp_l.
  replace (x + 2^31 - 2^31) with x by lia. reflexivity.
Qed.

#[using="Type"] Lemma In_carve_list : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenLib ()) "Pau,$:.Pcs,$:.Pnw,$0.Pw,(2.&40.)P,(31.(2.&40.)R1.(32.R4.R3.R2.))(19.$0.Li,$0.(22.(1>.R1.R4.)(3.(2.&40.)R3.(33.&40.(34.(15.R6.(35.(16.R1.)R5.))+10.)))))")
(* [comment removed for export] *).
Proof.
  intros au cs nw w H. unfold carve_list in H. apply in_map_iff in H. ddestruct H as (j & <- & Hj). apply in_seq in Hj.
  exists (nw - 1 - j)%nat. split; [lia|]. replace (Z.of_nat (nw - 1 - j)) with (Z.of_nat nw - 1 - Z.of_nat j) by lia. reflexivity.
Qed.

#[using="Type"] Lemma firstn_skipn_repeat : forall {A} (a : A) n o k, (o + k <= n)%nat -> firstn k (skipn o (repeat a n)) = repeat a k.
Proof.
  intros A a n o k H. replace n with (o + ((k + (n - o - k))))%nat by lia. rewrite List.repeat_app, skipn_app, skipn_all2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag, skipn_O. cbn [app].
  rewrite (List.repeat_app a k), firstn_app, firstn_all2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fits_chkL (x : Z) : bool := x <=? class_size (class_of x).
Fixpoint allzL (f : Z -> bool) (x : Z) (n : nat) : bool := match n with O => true | S n' => f x && allzL f (x + 1) n' end.
#[using="Type"] Lemma fits_tblL : allzL fits_chkL 1 65536 = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma allzL_spec : forall f x n y, allzL f x n = true -> x <= y < x + Z.of_nat n -> f y = true.
Proof.
  intros f x n. revert x. induction n as [|n IH]; intros x y H R; [lia|]. cbn in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec y x) as [->|NE]; [exact H1|]. apply (IH (x + 1)); [exact H2| lia].
Qed.
#[using="Type"] Lemma class_fitsL : forall x, 1 <= x <= 65536 -> x <= class_size (class_of x).
Proof.
  intros x Hx. assert (E : Z.of_nat 65536 = 65536) by (vm_compute; reflexivity).
  pose proof (allzL_spec fits_chkL 1 65536 x fits_tblL) as H. rewrite E in H. specialize (H ltac:(lia)). unfold fits_chkL in H. apply Z.leb_le in H. exact H.
Qed.

End ARUN_1.
