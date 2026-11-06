(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtAllocG Pm9ArtFree1 Pm9ArtRefill1.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Definition art_gfa_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (r chp nf na : Z) (ws : list Z) : word -> option byte :=
  Wn 8 (Wn 8 (art_w4s (Wn 8 (Wn 8 (art_gfa_frame M sp raw regs) r (2 ^ 60)) (r + 16) (nf - Z.of_nat (length ws))) chp ws) (r + 72) (na + Z.of_nat (length ws))) r 0.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_gfa_run : forall ws regs (M rom : word -> option byte) (raw : word) (sp ia st c chp spb ris qris nf na : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 (Z.of_nat (length ws)) ->
  128 <= sp -> sp < 2 ^ 64 -> 0x6b4000 + 128 <= sp -> 0x10000 <= ia -> ia + 4096 <= 0x6b4000 -> 1 <= c <= 31 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris ->
  0 <= st < 2 ^ 64 -> 0x6b4000 <= chp -> chp + 4 * Z.of_nat (length ws) < 2 ^ 64 -> (1 <= length ws)%nat -> Z.of_nat (length ws) <= nf -> nf < 2 ^ 26 -> 0 <= na -> na + Z.of_nat (length ws) < 2 ^ 64 ->
  apart (ris + 128 * c) 128 (sp - 128) 128 -> apart chp (4 * Z.of_nat (length ws)) (sp - 128) 128 -> apart chp (4 * Z.of_nat (length ws)) (ris + 128 * c) 128 ->
  apart chp (4 * Z.of_nat (length ws)) (spb + c * 2 ^ 32 + 3758096384) (4 * nf) ->
  apart (spb + c * 2 ^ 32 + 3758096384) (4 * nf) (sp - 128) 128 -> apart (spb + c * 2 ^ 32 + 3758096384) (4 * nf) (ris + 128 * c) 128 ->
  wrA M (sp - 128) 128 -> wrA M (ris + 128 * c) 128 -> wrA M chp (4 * Z.of_nat (length ws)) ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 72) 8 na ->
  cellA M 0x10458 8 0xafffff00000fffff ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 28 /\ cellA M (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf - Z.of_nat (length ws)) + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x5e7c4 : word) M rom) (mkst regs' raw (art_gfa_mem M sp raw regs (ris + 128 * c) chp nf na ws) rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros ws regs M rom raw sp ia st c chp spb ris qris nf na H1 Hret H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hc Hspb Hspb' Hris Hris' Eris
         Hst Hchp Hchp' Hlen Hnf Hnf' Hna Hna' Ar Achsp Achr Achfa Afasp Afar W Wr Wch Cspb Cris Cmx Cnf Cna Crd Cws.
  set (n := Z.of_nat (length ws)) in *. set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *.

  pose proof (art_gfa_lock_fn regs M rom raw sp ia st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hc Hspb Hspb' Hris Hris' Eris
                Ar Hst ltac:(lia) ltac:(lia) W Wr Cspb Cris Cmx) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?X _) => set (r1 := R) in RUN1; set (M1 := X) in RUN1 end.

  pose proof (art_gfa_mid_fn r1 M1 rom r fa chp n nf ltac:(unfold r1, r; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(unfold r1, fa; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(unfold r1; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(unfold r1; gres; rwH; first [reflexivity | f_equal; lia])
                ltac:(unfold r; lia) ltac:(unfold r; lia) ltac:(unfold fa; lia) ltac:(unfold fa; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold M1, art_gfa_frame; zwr) ltac:(unfold M1, art_gfa_frame, r; unfold apart in Ar; zcell)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ ?X _) => set (r2 := R) in RUN2; set (M2 := X) in RUN2 end.

  destruct (art_gfa_copy ws r2 M2 rom chp (fa + 4 * (nf - n)) (chp + 4 * n) ltac:(unfold r2, r1; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(unfold r2; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(unfold r2; gres; rwH; first [reflexivity | f_equal; lia])
              ltac:(lia) Hlen ltac:(lia) ltac:(lia) ltac:(unfold fa; lia) ltac:(unfold fa; lia) ltac:(lia) ltac:(unfold apart in Achfa |- *; lia)
              ltac:(unfold M2, M1, art_gfa_frame; zwr)
              ltac:(intros j Hj; destruct (Cws j Hj) as [R C]; split; [lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Afasp, Afar;
                    do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); do 13 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); exact C))
    as (r3 & RUN3 & P3_13 & P3_20 & K3).

  pose proof (art_gfa_tail_fn r3 (art_w4s M2 chp ws) rom raw sp r n na ris qris c (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
                (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) (U (getr regs 26)) (U (getr regs 27))
                ltac:(rewrite K3 by discriminate; unfold r2, r1; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(rewrite K3 by discriminate; unfold r2, r1, r; gres; rwH; first [reflexivity | f_equal; lia])
                ltac:(rewrite K3 by discriminate; unfold r2, r1; gres; rwH; first [reflexivity | f_equal; lia]) ltac:(rewrite K3 by discriminate; unfold r2, r1; gres; rwH; first [reflexivity | f_equal; lia])
                Hsp Hsp' IMG eq_refl Eris Hris Hc ltac:(unfold r; lia) Ar ltac:(lia) ltac:(lia) Hret
                (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
                ltac:(eapply wr_grows; [apply art_w4s_grows|]; unfold M2, M1, art_gfa_frame; zwr)
                ltac:(unfold r; unfold apart in Achr; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame; unfold apart in Ar; zcell)
                ltac:(unfold r; unfold apart in Achr; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame; unfold apart in Ar; zcell)
                ltac:(apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)
                ltac:(unfold apart in Achsp; apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|]; unfold M2, M1, art_gfa_frame, r; unfold apart in Ar; zcell)) as RUN4.
  match type of RUN4 with msteps _ _ (mkst ?R _ ?X _) => exists R end.
  split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
           unfold art_gfa_mem. fold n. unfold M2, M1 in RUN4. exact RUN4. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned; rewrite K3 by (intros E; discriminate E); unfold r2, r1; gres; reflexivity.
Qed.
End FPX.
