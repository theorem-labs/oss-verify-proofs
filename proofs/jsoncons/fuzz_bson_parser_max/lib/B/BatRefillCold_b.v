(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocG_b BatRefill1_b BatRefill2_b BatRefill3_b BatInitCache_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

(* [comment removed for export] *)
Definition art_refill_cold_rA (regs : bvmap 5 word) (sp ca c ia n : Z) : bvmap 5 word :=
  (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x574cc : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 n)).
Definition art_refill_cold_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ca c ia r nf na : Z) (ws : list Z) : word -> option byte :=
  let n := Z.of_nat (length ws) in
  let M3 := Wn 8 (Wn 8 (Wn 8 M (sp - 8) (bv_unsigned raw)) (sp - 16) (bv_unsigned (getr regs 8))) (sp - 24) (bv_unsigned (getr regs 9)) in
  Wn 4 (art_gfa_mem (art_ic_mem M3 ca 31) (sp - 32) (0x574cc : bv 64)%bv (art_refill_cold_rA regs sp ca c ia n) r (ca + 80 * c + 16) nf na ws) (ca + 80 * c) n.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_a_cold : forall regs (M rom : word -> option byte) (raw : word) (sp ca c ia : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  32 <= sp -> sp < 2 ^ 64 -> 0x696000 + 32 <= sp -> 4096 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 ->
  apart (sp - 32) 32 ca 4096 ->
  wrA M (sp - 32) 32 -> wrA M ca 2592 -> cellA M (ca + 80 * c + 4) 4 0 ->
  exists rA,
    msteps ASEGS (mkst regs (0x5748c : word) M rom)
      (mkst rA (0x5758c : word) (art_ic_mem (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) ca 31) rom)
    /\ getr rA 1 = (0x574cc : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ getr rA 10 = Z_to_bv 64 ia /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16) /\ getr rA 14 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ (forall r : reg, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA r = getr regs r).
Proof.
  intros regs M rom raw sp ca c ia H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia A W Wca Cmc.
  pose proof (art_ic_mc_range c Hc) as Hmc.
  (* [comment removed for export] *)
  assert (RUN1 : exists r1 M1, msteps ASEGS (mkst regs (0x5748c : word) M rom) (mkst r1 (0x57530 : word) M1 rom)
            /\ M1 = Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))
            /\ getr r1 11 = Z_to_bv 64 (ca + 88) /\ getr r1 13 = Z_to_bv 64 32 /\ getr r1 15 = Z_to_bv 64 18446744073709551601
            /\ getr r1 16 = Z_to_bv 64 15 /\ getr r1 17 = Z_to_bv 64 1024 /\ getr r1 5 = Z_to_bv 64 16 /\ getr r1 6 = Z_to_bv 64 17 /\ getr r1 7 = Z_to_bv 64 512
            /\ getr r1 2 = Z_to_bv 64 (sp - 32) /\ getr r1 8 = Z_to_bv 64 (ca + 80 * c) /\ getr r1 10 = Z_to_bv 64 ca /\ getr r1 12 = Z_to_bv 64 ia /\ getr r1 14 = Z_to_bv 64 c
            /\ (forall r : reg, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
  { eexists. eexists. split.
    - zstep F_57074 D_57074.
      zsd F_57078 D_57078 (sp - 8) (U raw) ltac:(rewok W). zsd F_5707c D_5707c (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_57080 D_57080 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zstep F_57084 D_57084. zstep F_57088 D_57088.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 0) by (unfold apart in A; zcell) end.
      zlw F_5708c D_5708c (ca + 80 * c + 4) Cmc'.
      zbtk F_57090 D_57090.
      zstep F_570d0 D_570d0. zstep F_570d4 D_570d4. zstep F_570d8 D_570d8. zstep F_570dc D_570dc. zstep F_570e0 D_570e0. zstep F_570e4 D_570e4.
      zstep F_570e8 D_570e8. zstep F_570ec D_570ec.
      stepn F_570f0 D_570f0.
      first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]].
    - split; [reflexivity|]. repeat (split; [kept_solve|]).
      intros r Hr. cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; kept_solve. }
  destruct RUN1 as (r1 & M1 & RUN1 & EM1 & A11 & A13 & A15 & A16 & A17 & A5 & A6 & A7 & B2 & B8 & B10 & B12 & B14 & K1).
  assert (W1 : wrA M1 ca 2592). { rewrite EM1. do 3 apply wr_Wn. exact Wca. }
  destruct (art_ic_loop r1 M1 rom ca A11 A13 A15 A16 A17 A5 A6 A7 Hca Hca' W1) as (r2 & RUN2 & K2).
  #[local] Ltac ick := unfold art_ic_kept; repeat split; intros E; discriminate E.
  assert (C2 : cellA (art_ic_mem M1 ca 31) (ca + 80 * c + 4) 4 (art_ic_mc c)). { apply cell_ic_mc; [lia|lia|lia|cbn; lia]. }
  assert (P2 : getr r2 2 = Z_to_bv 64 (sp - 32)) by (rewrite (K2 2%bv) by ick; exact B2).
  assert (P8 : getr r2 8 = Z_to_bv 64 (ca + 80 * c)) by (rewrite (K2 8%bv) by ick; exact B8).
  assert (P10 : getr r2 10 = Z_to_bv 64 ca) by (rewrite (K2 10%bv) by ick; exact B10).
  assert (P12 : getr r2 12 = Z_to_bv 64 ia) by (rewrite (K2 12%bv) by ick; exact B12).
  assert (P14 : getr r2 14 = Z_to_bv 64 c) by (rewrite (K2 14%bv) by ick; exact B14).
  assert (RUN3 : exists rA, msteps ASEGS (mkst r2 (0x57584 : word) (art_ic_mem M1 ca 31) rom) (mkst rA (0x5758c : word) (art_ic_mem M1 ca 31) rom)
    /\ getr rA 1 = (0x574cc : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ getr rA 10 = Z_to_bv 64 ia /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16) /\ getr rA 14 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ (forall r : reg, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA r = getr r2 r)).
  { eexists. split.
    - zlw F_5716c D_5716c (ca + 80 * c + 4) C2.
      stepn F_57170 D_57170.
      stepn F_57094 D_57094. rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
      zstep F_57098 D_57098. zstep F_5709c D_5709c. zstep F_570a0 D_570a0. zstep F_570a4 D_570a4. zstep F_570a8 D_570a8. zstep F_570ac D_570ac.
      stepn F_570b0 D_570b0.
      first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]].
    - split; [gres; rwH; zval|]. repeat (split; [kept_solve|]).
      intros r Hr. cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; kept_solve. }
  destruct RUN3 as (rA & RUN3 & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & K3).
  exists rA. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. rewrite <- EM1. exact RUN3. }
  repeat (split; [assumption|]).
  intros r Hr. rewrite (K3 r Hr). pose proof Hr as Hr'. cbn [In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; (rewrite K2 by ick; apply K1; cbn; tauto).
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma art_gfa_frame_ext : forall M sp raw (r1 r2 : bvmap 5 word),
  (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr r2 r) ->
  art_gfa_frame M sp raw r1 = art_gfa_frame M sp raw r2.
Proof.
  intros M sp raw r1 r2 H. unfold art_gfa_frame.
  rewrite (H 8%bv), (H 9%bv), (H 18%bv), (H 19%bv), (H 20%bv), (H 21%bv), (H 22%bv), (H 23%bv), (H 24%bv), (H 25%bv), (H 26%bv), (H 27%bv) by (cbn; tauto).
  reflexivity.
Qed.
#[using="Type"] Lemma art_gfa_mem_ext : forall M sp raw (r1 r2 : bvmap 5 word) r chp nf na ws,
  (forall x : reg, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 x = getr r2 x) ->
  art_gfa_mem M sp raw r1 r chp nf na ws = art_gfa_mem M sp raw r2 r chp nf na ws.
Proof. intros. unfold art_gfa_mem. rewrite (art_gfa_frame_ext M sp raw r1 r2) by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End FPX.
