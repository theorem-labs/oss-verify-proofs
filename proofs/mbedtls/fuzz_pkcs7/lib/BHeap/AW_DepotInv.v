(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_DepotA AW_DepotB AW_DepotC AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_DepotInv () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnodes"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnode"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotCfg.zblock"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dmap1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "Corelib.Init.Peano.lt"; "Corelib.Init.Nat.of_num_uint"; "Corelib.Init.Number.UIntDecimal"; "Corelib.Init.Decimal.D3"; "Corelib.Init.Decimal.D2"; "Corelib.Init.Decimal.D7"; "Corelib.Init.Decimal.D6"; "Corelib.Init.Decimal.D8"; "Corelib.Init.Decimal.Nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.dblocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "ARUN_1.sblks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma firstn_repeat' : forall {A} (x : A) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x n. induction n as [|n IH]; intros [|k] Hk; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
#[using="Type"] Lemma skipn_repeat' : forall {A} (x : A) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma dnodes_reest : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pnb,(0.$4.)PN,$4.Phsh,(2.&40.)Psid,(2.&40.)Plnk,$4.P,(5.R7.R5.R4.)P,(6.R9.R8.R7.)P,(7.$8.R9.R8.)P,Ps,$4.P,(9.(:.=R1.)(;.R1.(<.+10000.(=.(>.$4.R9.)))))P,(?.(10.$4.R2.(11.R9.+1.)))(12.R>.(13.R;.R3.)+10.)P,(9.(:.=(11.R8.+1.))(;.(11.R8.+1.)(<.+10000.(=.(>.$4.R9.)))))P,(14.$8.R;.(13.R:.(11.R9.+1.))(15.$16.(17.R8.)(15.$16.(18.(19.&40.R6.))(15.$16.(18.R7.)(1:.$16.)))))P,(9.(:.=R7.)(;.R7.(11.R:.+1.)))(5.R=.R<.(11.R;.+1.))")
(* [comment removed for export] *).
Proof.
  intros W m m' nb N hsh sid lnk DN MU WM DJ S0 NC LNK s Hs.
  destruct (Z.eq_dec s (N + 1)) as [->|NE]; [dexists hsh, sid, lnk; split; [exact NC| lia]|].
  ddestruct (DN s Hs) as (h' & sid' & l' & C & L0 & LS). dexists h', sid', l'. split; [| split; [exact L0| intros; apply LS; lia]].
  eapply rw_cells_transport; [exact C| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJ; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zblock_node : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "Pm,P,(2.&40.)(3.(2.&8.))Pb,$4.Pn,$4.Poff,$4.P,(1;.R4.R3.R2.)P,(:.=R3.)P,(:.=R3.)P,(:.(11.R4.+10.)R5.)(14.$8.R8.(11.R7.R5.)(15.$16.(17.(19.&40.=))(15.$16.(18.(19.&40.=))(15.$16.(18.(19.&40.=))(1:.$16.)))))")
(* [comment removed for export] *).
Proof.
  intros m b n off ZB Hn H0 H1. Transparent zblock. unfold zblock in ZB. Opaque zblock.
  apply (rw_cells_split_CB asegs m b [] (Z.to_nat n) _ [] [Z.to_nat off; 16%nat; (Z.to_nat n - Z.to_nat off - 16)%nat]) in ZB; [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in ZB.
  apply (proj1 (rw_cells_app asegs m b [CB (Z.to_nat off) _] _)) in ZB. destruct ZB as [_ ZB].
  apply (proj1 (rw_cells_app asegs m _ [CB 16 _] _)) in ZB. destruct ZB as [ZB _].
  cbn [cells_size csize Nat.add] in ZB. rewrite Nat.add_0_r, Z2Nat.id in ZB by lia.
  rewrite skipn_repeat', firstn_repeat' in ZB by lia.
  eapply (rw_cells_reshape asegs m (b + off) _ _ ZB); [cbn; tauto| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dnodes_app : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "Pm,P,(2.&40.)(3.(2.&8.))Pnb,(0.$4.)PN,$4.Pb,$4.P,(5.R4.R3.R2.)P,(1;.R5.R2.(1<.+2.+14.))P,(;.R4.(<.+10000.(=.(>.$4.R5.))))P,(1=.$4.Lb,$4.(9.(:.+65?000.R1.)(9.(:.(11.R1.(1<.+2.+14.))(1>.VhAR,))(10.$4.(1?.R1.+1000.)=)))R6.)(5.R8.(20.$4.R7.(15.$4.R5.(1:.$4.)))R6.)")
(* [comment removed for export] *).
Proof.
  intros m nb N b DN ZB NL HF s Hs. rewrite app_length in Hs. cbn [length] in Hs.
  unfold dnode, dblk in *.
  destruct (Z.lt_ge_cases s (65536 * Z.of_nat (length nb))) as [LT|GE].
  - ddestruct (DN s ltac:(lia)) as (h & sid & l & C & L0 & LS). dexists h, sid, l. split; [| split; [exact L0| exact LS]].
    rewrite app_nth1; [exact C|]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia.
  - assert (E : Z.to_nat (s / 65536) = length nb).
    { assert (s / 65536 = Z.of_nat (length nb)); [| lia].
      symmetry. apply Z.div_unique with (r := s - 65536 * Z.of_nat (length nb)); lia. }
    rewrite E, app_nth2, Nat.sub_diag by lia. cbn [nth].
    dexists (Z_to_bv 64 0), (Z_to_bv 64 0), 0. split; [| split; [lia| intros; lia]].
    pose proof (Z.mod_pos_bound s 65536 ltac:(lia)).
    assert (SM : s mod 65536 = s - 65536 * Z.of_nat (length nb)).
    { pose proof (Z.div_mod s 65536 ltac:(lia)). lia. }
    apply (zblock_node m b (2^20) (16 * (s mod 65536)) ZB); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dmap1v_app_old : forall nb b k, 0 <= k -> k <> Z.of_nat (length nb) -> dmap1v (nb ++ [b]) k = dmap1v nb k.
Proof.
  intros nb b k H NE. unfold dmap1v, dblk. rewrite app_length. cbn [length].
  destruct (Z.ltb_spec0 k (Z.of_nat (length nb))).
  - replace (k <? Z.of_nat (length nb + 1)) with true by (symmetry; apply Z.ltb_lt; lia). rewrite app_nth1 by lia. reflexivity.
  - replace (k <? Z.of_nat (length nb + 1)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
#[using="Type"] Lemma dmap1v_app_new : forall nb b, dmap1v (nb ++ [b]) (Z.of_nat (length nb)) = b.
Proof.
  intros nb b. unfold dmap1v, dblk. rewrite app_length. cbn [length].
  replace (Z.of_nat (length nb) <? Z.of_nat (length nb + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.
#[using="Type"] Lemma dmap1_app : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pnb,(0.$4.)Pb,$4.P,(21.VhAR,R4.R2.)P,(6.R6.R5.R4.)P,(7.$8.R6.R5.)P,Pk,$4.P,(9.(:.=R1.)(;.R1.+8000.))P,(?.(10.$4.R2.(=.(>.$4.R7.))))(12.R;.(11.$22.(<.+8.R3.))+8.)P,(14.$8.R7.(11.$22.(<.+8.(=.(>.$4.R6.))))(15.$16.(17.(19.&40.R5.))(1:.$16.)))P,(23.(>.$4.R7.)(24.(25.(26.(27.(28.(29.(2:.$2;.))))))))P,(:.+65?000.R7.)P,(:.(11.R8.(1<.+2.+14.))(1>.VhAR,))P,(10.$4.(1?.R9.+1000.)=)(21.VhAR,R<.(20.$4.R;.(15.$4.R:.(1:.$4.))))")
(* [comment removed for export] *).
Proof.
  (intros W m m' nb b dd_H; ddestruct dd_H as (DM & DF & DL); intros MU WM DJ NEWC LEN B0 B1 BA). split; [|split].
  - intros k Hk. destruct (Z.eq_dec k (Z.of_nat (length nb))) as [->|NE].
    + rewrite dmap1v_app_new. exact NEWC.
    + rewrite dmap1v_app_old by lia. eapply rw_cells_transport; [exact (DM k Hk)| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJ; assumption].
  - apply Forall_app. split; [exact DF|]. constructor; [| constructor]. repeat split; assumption.
  - rewrite app_length. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dblocks_app : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pbl,(0.$4.)Pb,$4.Pstored,(2.&40.)P,(2<.VhAR,R5.R3.)P,(6.R7.R6.R5.)P,(7.$8.R7.R6.)P,Pj,$4.P,(9.(:.=R1.)(;.R1.+1000.))P,(?.(10.$4.R2.(=.(>.$4.R8.))))(12.R<.(11.(11.$2=.+10.)(<.+10.R3.))+10.)P,(14.$8.R8.(11.(11.$2=.+10.)(<.+10.(=.(>.$4.R7.))))(15.$16.(17.(19.&40.R6.))(15.$16.(18.R5.)(15.$16.(18.(19.&40.=))(1:.$16.)))))P,(23.(>.$4.R8.)#1000.)P,(:.+65?000.R8.)P,(:.(11.R9.(1<.+2.+17.))(1>.VhAR,))P,(10.$4.(1?.R:.+1000.)=)(2<.VhAR,R=.(20.$4.R<.(15.$4.R;.(1:.$4.))))")
(* [comment removed for export] *).
Proof.
  (intros W m m' bl b stored dd_H; ddestruct dd_H as (DB & DF & DL); intros MU WM DJ NEWC LEN B0 B1 BA). split; [|split].
  - intros j Hj. destruct (Z.eq_dec j (Z.of_nat (length bl))) as [->|NE].
    + rewrite sptr_app_new. exists stored. exact NEWC.
    + rewrite sptr_app_old by lia. destruct (DB j Hj) as (st & C). exists st.
      eapply rw_cells_transport; [exact C| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJ; assumption].
  - apply Forall_app. split; [exact DF|]. constructor; [| constructor]. repeat split; assumption.
  - rewrite app_length. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Definition sblks (m : mem) (bl : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length bl) -> stk asegs m (sblk bl j) (sblk bl j + 2^23).
#[using="Type"] Lemma sblks_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pbl,(0.$4.)P,(2>.R3.R1.)P,(6.R5.R4.R3.)P,(7.$8.R5.R4.)P,Pj,$4.P,(9.(:.=R1.)(;.R1.(=.(>.$4.R5.))))(12.R9.(2?.R6.R2.)(1<.+2.+17.))(2>.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' bl SB MU WM DJ j Hj. eapply stk_transport_disjoint; [exact (SB j Hj)| exact MU| exact WM|].
  replace (sblk bl j + 2 ^ 23 - sblk bl j) with (2^23) by lia. apply DJ. exact Hj.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma sblks_set : ltac2:(CDefT.buildp (gd_tbl_AW_DepotInv ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pbl,(0.$4.)Pj0,$4.P,(2>.R4.R2.)P,(9.(:.=R2.)(;.R2.(=.(>.$4.R3.))))P,(30.$8.R5.(2?.R4.R3.)(11.(2?.R4.R3.)(1<.+2.+17.)))P,Pj,$4.P,(9.(:.=R1.)(;.R1.(=.(>.$4.R6.))))P,(?.(10.$4.R2.R6.))(30.$8.R9.(2?.R8.R3.)(11.(2?.R8.R3.)(1<.+2.+17.)))(2>.R7.R6.)")
(* [comment removed for export] *).
Proof. intros m m' bl j0 SB J0 S0 OTH j Hj. destruct (Z.eq_dec j j0) as [->|NE]; [exact S0| apply OTH; assumption]. Qed.

End ARUN_1.
