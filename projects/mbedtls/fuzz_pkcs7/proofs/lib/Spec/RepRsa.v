(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepRsa () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Corelib.Init.Logic.or"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.Rep.LNull"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "WithSegs.rsa_head_cells"; "Stdlib.ZArith.BinInt.Z.add"; "WithSegs.rsa_tail_cells"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "WithSegs.r_N"; "WithSegs.r_E"; "WithSegs.rsa_field_ok"; "Stdlib.ZArith.BinInt.Z.le"; "WithSegs.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.RepEcp.mpdr_at"; "WithSegs.rsa_mpds"; "Stdlib.ZArith.BinInt.Z.modulo"; "RSA_CTX_SIZE"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "WithSegs.mpd_z"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "WithSegs.rsa_at"; "WithSegs.rsa_fresh"; "WithSegs.rsa_st"; "WithSegs.rsa_addrs_ok"; "Stdlib.ZArith.BinInt.Z.sub"].


Definition RSA_CTX_SIZE : Z := 232.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma rmpd_of_mpd : forall m LB d, mpd_at segs m LB d -> mpdr_at segs m LB d.
Proof. intros m LB d [H _]; exact H. Qed.
#[using="Type"] Lemma mpd_of_rmpd : forall m LB d, mpdr_at segs m LB d -> (md_sg d = 1 \/ md_sg d = -1) -> mpd_at segs m LB d.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
Definition mpd_z (A : Z) : mpd := mkMPD A 0 0 0 [] (Z_to_bv 64 0) LNull.

(* [comment removed for export] *)
Definition rsa_zero_offs : list Z := [48; 64; 80; 96; 112; 128; 144; 160; 176; 192; 208].
Definition rsa_zero_mpds (C : Z) : list mpd := map (fun o => mpd_z (C + o)) rsa_zero_offs.

(* [comment removed for export] *)
Record rsa_st := mkRSA { r_len : Z; r_N : mpd; r_E : mpd }.

Definition rsa_fresh (C : Z) : rsa_st := mkRSA 0 (mpd_z (C + 16)) (mpd_z (C + 32)).

Definition rsa_mpds (C : Z) (r : rsa_st) : list mpd := r_N r :: r_E r :: rsa_zero_mpds C.

Definition rsa_head_cells (r : rsa_st) : list cell := [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_len r))].
Definition rsa_tail_cells : list cell := [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition rsa_field_ok (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "(0.(1.(2.$3.(4.O1.)$5.))(6.(0.(2.$7.(8.O1.)=)(0.(2.$3.(4.O1.)$9.)(2.(:.&40.)(;.O1.)(<.&40.=))))(6.(2.$7.(8.O1.)+1.)(2.$7.(8.O1.)-1.))))")
(* [comment removed for export] *).

Definition rsa_at (m : mem) (LB : list blk) (C : Z) (r : rsa_st) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "(0.(=.Vsegs,O4.O2.(>.O1.))(0.(=.Vsegs,O4.(?.O2.+>0.)$10.)(0.(2.$7.(11.(12.O1.))(?.O2.+10.))(0.(2.$7.(11.(13.O1.))(?.O2.+20.))(0.(14.(12.O1.))(0.(14.(13.O1.))(0.(0.(15.=(16.O1.))(17.(16.O1.)(18.+2.+40.)))(0.(19.$1:.(1;.Vsegs,O4.O3.)(1<.O2.O1.))(0.(2.$7.(1=.O2.+10.)=)(0.(17.=O2.)(0.(15.(?.O2.$1>.)(18.+2.+40.))(0.(1?.(20.$7.$7.)(21.$7.$7.O2.$1>.)O3.)(0.P,(2.$3.(4.(12.O1.))$22.)(1.(2.$7.(23.(12.O1.))O2.))(0.P,(2.$3.(4.(13.O1.))$22.)(1.(2.$7.(23.(13.O1.))O2.))P,(2.$3.(4.(12.O1.))$22.)P,(2.$3.(4.(13.O1.))$22.)(1.(2.$7.(23.(12.O1.))(23.(13.O1.))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rsa_limb_blocks (r : rsa_st) : list blk := mpd_blk (r_N r) ++ mpd_blk (r_E r).

(* [comment removed for export] *)
Definition rsa_ivs (C : Z) (r : rsa_st) : list (Z * Z) :=
  (C, C + RSA_CTX_SIZE) :: tl (mpd_ivs (r_N r)) ++ tl (mpd_ivs (r_E r)).

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rsa_zero_offs_spec : forall o, In o rsa_zero_offs -> 48 <= o <= 208 /\ o mod 16 = 0.
Proof. intros o H. cbn in H. intuition (subst; cbn; lia). Qed.

#[using="Type"] Lemma mpd_z_cells : ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "PA,$7.(2.(24.$25.)(26.(23.(27.R1.))(<.&40.(8.(27.R1.)))(28.(27.R1.))(;.(27.R1.)))(29.$25.(2:.(<.&40.=))(29.$25.(2;.(<.&40.=))(29.$25.(2;.(<.&40.=))(29.$25.(2<.(<.&40.=))(2=.$25.))))))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

#[using="Type"] Lemma rmpd_z_of_cells : ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "Pm,P,(:.&40.)(2>.(:.&8.))PLB,(24.$2?.)PA,$7.P,(=.Vsegs,R3.R1.(29.$25.(2:.(<.&40.=))(29.$25.(2;.(<.&40.=))(29.$25.(2;.(<.&40.=))(29.$25.(2<.(<.&40.=))(2=.$25.))))))P,(2.$7.(1=.R2.+8.)=)P,(17.=R3.)(1;.Vsegs,R6.R5.(27.R4.))")
(* [comment removed for export] *).
Proof.
  intros m LB A H HA H0. unfold mpdr_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_z].
  split; [exact H|]. split; [exact HA|]. split; [exact H0|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsa_at_of_zero : ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "Pm,P,(:.&40.)(2>.(:.&8.))PLB,(24.(20.$7.$7.))PC,$7.P,(=.Vsegs,R3.R1.(29.$25.(30.#>8.(31.(:.&8.)(<.&8.=)#>8.))(2=.$25.)))P,(2.$7.(1=.R2.+10.)=)P,(17.=R3.)P,(1?.(20.$7.$7.)(21.$7.$7.R4.+>8.)R5.)(32.R7.R6.R5.(33.R5.))")
(* [comment removed for export] *).
Proof.
  intros m LB C H HC H0 HIN.
  pose proof (rw_cells_bound _ _ _ _ H) as B. cbn [cells_size csize Nat.add] in B.
  set (z16 := [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
  assert (R : rw_cells segs m C ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
            ++ (z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16 ++ z16)
            ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])).
  { eapply rw_cells_zeros; [exact H| subst z16; cbn; repeat split; reflexivity| reflexivity]. }
  subst z16. cbn [app] in R.
  Ltac take H k NAME :=
    match type of H with rw_cells ?sg ?mm ?A ?cs =>
      let pre := eval cbv in (firstn k cs) in let post := eval cbv in (skipn k cs) in
      change (rw_cells sg mm A (pre ++ post)) in H; apply rw_cells_app in H;
      let T := fresh "TMP" in destruct H as [NAME T]; rename T into H;
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in H
    end.
  take R 3%nat HD.
  take R 4%nat MN. take R 4%nat ME.
  take R 4%nat M48. take R 4%nat M64. take R 4%nat M80. take R 4%nat M96. take R 4%nat M112. take R 4%nat M128.
  take R 4%nat M144. take R 4%nat M160. take R 4%nat M176. take R 4%nat M192. take R 4%nat M208. rename R into TL.
  repeat match goal with H : rw_cells segs m (?a + ?b + ?c) _ |- _ => let v := eval cbv in (b + c) in replace (a + b + c) with (a + v) in H by lia end.
  unfold rsa_at, rsa_fresh. cbn [r_len r_N r_E rsa_head_cells md_addr mpd_z].
  split; [exact HD|]. split; [exact TL|]. split; [reflexivity|]. split; [reflexivity|].
  split; [split; [cbn; discriminate| left; repeat split; reflexivity]|].
  split; [split; [cbn; discriminate| left; repeat split; reflexivity]|].
  split; [lia|].
  split.
  - unfold rsa_mpds, rsa_zero_mpds, rsa_zero_offs. cbn [map r_N r_E].
    repeat (constructor; [apply rmpd_z_of_cells; [assumption| clear -HC; lia| lia] |]). constructor.
  - unfold RSA_CTX_SIZE. cbn [md_own mpd_z]. repeat split; try lia; try exact HIN; intros; discriminate.
Qed.


Definition rsa_addrs_ok (C : Z) (r : rsa_st) : Prop := md_addr (r_N r) = C + 16 /\ md_addr (r_E r) = C + 32.

#[using="Type"] Lemma rsa_mpds_addr : ltac2:(CDefT.buildp (gd_tbl_RepRsa ()) "PC,$7.Pr,$34.Pd,$1:.P,(35.R3.R2.)P,(1?.$1:.R2.(1<.R4.R3.))(0.(15.(?.R5.+10.)(11.R3.))(0.(15.(?.(11.R3.)+10.)(?.R5.+>0.))(2.$7.(1=.(36.(11.R3.)R5.)+10.)=)))")
(* [comment removed for export] *).
Proof.
  intros C r d [HN HE] Hd. unfold rsa_mpds in Hd. cbn [In] in Hd.
  destruct Hd as [<-|[<-|Hd]].
  - rewrite HN. split; [lia|]. split; [lia|]. replace (C + 16 - C) with 16 by lia. reflexivity.
  - rewrite HE. split; [lia|]. split; [lia|]. replace (C + 32 - C) with 32 by lia. reflexivity.
  - unfold rsa_zero_mpds in Hd. apply in_map_iff in Hd. destruct Hd as (o & <- & Ho).
    apply rsa_zero_offs_spec in Ho. cbn [md_addr mpd_z]. split; [lia|]. split; [lia|]. replace (C + o - C) with o by lia. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsa_zero_mpds_len : forall C, length (rsa_zero_mpds C) = 11%nat.
Proof. reflexivity. Qed.

End WithSegs.
