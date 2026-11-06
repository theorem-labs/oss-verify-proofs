(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtAllocG ArtRefill1 ArtRefill2 ArtRefill3 ArtInitCache.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

(* [comment removed for export] *)
Definition art_refill_cold_rA (regs : bvmap 5 word) (sp ca c ia n : Z) : bvmap 5 word :=
  (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x42258 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 n)).
Definition art_refill_cold_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ca c ia r nf na : Z) (ws : list Z) : word -> option byte :=
  let n := Z.of_nat (length ws) in
  let M3 := Wn 8 (Wn 8 (Wn 8 M (sp - 8) (bv_unsigned raw)) (sp - 16) (bv_unsigned (getr regs 8))) (sp - 24) (bv_unsigned (getr regs 9)) in
  Wn 4 (art_gfa_mem (art_ic_mem M3 ca 31) (sp - 32) (0x42258 : bv 64)%bv (art_refill_cold_rA regs sp ca c ia n) r (ca + 80 * c + 16) nf na ws) (ca + 80 * c) n.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_refill_a_cold : forall regs (M rom : word -> option byte) (raw : word) (sp ca c ia : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  32 <= sp -> sp < 2 ^ 64 -> 0x633000 + 32 <= sp -> 4096 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 ->
  apart (sp - 32) 32 ca 4096 ->
  wrA M (sp - 32) 32 -> wrA M ca 2592 -> cellA M (ca + 80 * c + 4) 4 0 ->
  exists rA,
    msteps ASEGS (mkst regs (0x42218 : word) M rom)
      (mkst rA (0x42318 : word) (art_ic_mem (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) ca 31) rom)
    /\ getr rA 1 = (0x42258 : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ getr rA 10 = Z_to_bv 64 ia /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16) /\ getr rA 14 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ (forall r : reg, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA r = getr regs r).
Proof.
  intros regs M rom raw sp ca c ia H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia A W Wca Cmc.
  pose proof (art_ic_mc_range c Hc) as Hmc.
  (* [comment removed for export] *)
  assert (RUN1 : exists r1 M1, msteps ASEGS (mkst regs (0x42218 : word) M rom) (mkst r1 (0x422bc : word) M1 rom)
            /\ M1 = Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))
            /\ getr r1 11 = Z_to_bv 64 (ca + 88) /\ getr r1 13 = Z_to_bv 64 32 /\ getr r1 15 = Z_to_bv 64 18446744073709551601
            /\ getr r1 16 = Z_to_bv 64 15 /\ getr r1 17 = Z_to_bv 64 1024 /\ getr r1 5 = Z_to_bv 64 16 /\ getr r1 6 = Z_to_bv 64 17 /\ getr r1 7 = Z_to_bv 64 512
            /\ getr r1 2 = Z_to_bv 64 (sp - 32) /\ getr r1 8 = Z_to_bv 64 (ca + 80 * c) /\ getr r1 10 = Z_to_bv 64 ca /\ getr r1 12 = Z_to_bv 64 ia /\ getr r1 14 = Z_to_bv 64 c
            /\ (forall r : reg, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
  { eexists. eexists. split.
    - zstep F_42218 D_42218.
      zsd F_4221c D_4221c (sp - 8) (U raw) ltac:(rewok W). zsd F_42220 D_42220 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_42224 D_42224 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zstep F_42228 D_42228. zstep F_4222c D_4222c.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 0) by (unfold apart in A; zcell) end.
      zlw F_42230 D_42230 (ca + 80 * c + 4) Cmc'.
      zbtk F_42234 D_42234.
      zstep F_42274 D_42274. zstep F_42278 D_42278. zstep F_4227c D_4227c. zstep F_42280 D_42280. zstep F_42284 D_42284. zstep F_42288 D_42288.
      zstep F_4228c D_4228c. zstep F_42290 D_42290.
      stepn F_42294 D_42294.
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
  assert (RUN3 : exists rA, msteps ASEGS (mkst r2 (0x42310 : word) (art_ic_mem M1 ca 31) rom) (mkst rA (0x42318 : word) (art_ic_mem M1 ca 31) rom)
    /\ getr rA 1 = (0x42258 : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ getr rA 10 = Z_to_bv 64 ia /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16) /\ getr rA 14 = Z_to_bv 64 (art_ic_mc c / 2)
    /\ (forall r : reg, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA r = getr r2 r)).
  { eexists. split.
    - zlw F_42310 D_42310 (ca + 80 * c + 4) C2.
      stepn F_42314 D_42314.
      stepn F_42238 D_42238. rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
      zstep F_4223c D_4223c. zstep F_42240 D_42240. zstep F_42244 D_42244. zstep F_42248 D_42248. zstep F_4224c D_4224c. zstep F_42250 D_42250.
      stepn F_42254 D_42254.
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
Lemma art_gfa_frame_ext : forall M sp raw (r1 r2 : bvmap 5 word),
  (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr r2 r) ->
  art_gfa_frame M sp raw r1 = art_gfa_frame M sp raw r2.
Proof.
  intros M sp raw r1 r2 H. unfold art_gfa_frame.
  rewrite (H 8%bv), (H 9%bv), (H 18%bv), (H 19%bv), (H 20%bv), (H 21%bv), (H 22%bv), (H 23%bv), (H 24%bv), (H 25%bv), (H 26%bv), (H 27%bv) by (cbn; tauto).
  reflexivity.
Qed.
Lemma art_gfa_mem_ext : forall M sp raw (r1 r2 : bvmap 5 word) r chp nf na ws,
  (forall x : reg, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 x = getr r2 x) ->
  art_gfa_mem M sp raw r1 r chp nf na ws = art_gfa_mem M sp raw r2 r chp nf na ws.
Proof. intros. unfold art_gfa_mem. rewrite (art_gfa_frame_ext M sp raw r1 r2) by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_refill_cold_run : forall ws regs (M rom : word -> option byte) (raw : word) (sp ca c ia spb ris qris nf na : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  art_ic_mc c = 2 * Z.of_nat (length ws) -> (1 <= length ws <= 8)%nat ->
  160 <= sp -> sp < 2 ^ 64 -> 0x633000 + 160 <= sp -> 0x633000 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 1 <= c <= 31 -> 0x10000 <= ia -> ia + 4096 <= 0x633000 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris -> Z.of_nat (length ws) <= nf -> nf < 2 ^ 26 -> 0 <= na -> na + Z.of_nat (length ws) < 2 ^ 64 ->
  apart (sp - 160) 160 ca 4096 -> apart (ris + 128 * c) 128 (sp - 160) 160 -> apart ca 4096 (ris + 128 * c) 128 ->
  apart ca 4096 (spb + c * 2 ^ 32 + 3758096384) (4 * nf) -> apart (spb + c * 2 ^ 32 + 3758096384) (4 * nf) (sp - 160) 160 -> apart (spb + c * 2 ^ 32 + 3758096384) (4 * nf) (ris + 128 * c) 128 ->
  wrA M (sp - 160) 160 -> wrA M (ris + 128 * c) 128 -> wrA M ca 4096 ->
  cellA M (ca + 80 * c + 4) 4 0 -> cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 72) 8 na ->
  cellA M 0x103d8 8 0xafffff00000fffff ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 28 /\ cellA M (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf - Z.of_nat (length ws)) + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x42218 : word) M rom) (mkst regs' raw (art_refill_cold_mem M sp raw regs ca c ia (ris + 128 * c) nf na ws) rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros ws regs M rom raw sp ca c ia spb ris qris nf na H1 Hret H2 H10 H11 H12 H13 Emc Hlen Hsp Hsp' IMG Hca Hca' Hca8 Hc Hia Hia'
         Hspb Hspb' Hris Hris' Eris Hnf Hnf' Hna Hna' Aspca Arsp Acar Acafa Afasp Afar W Wr Wca Cmc Cspb Cris Cmx Cnf Cna Crd Cws.
  set (n := Z.of_nat (length ws)) in *.
  assert (Hmc2 : art_ic_mc c / 2 = n) by (rewrite Emc; rewrite Z.mul_comm; apply Z.div_mul; lia).
  destruct (art_refill_a_cold regs M rom raw sp ca c ia H1 H2 H10 H11 H12 H13 ltac:(lia) Hsp' ltac:(lia) ltac:(lia) Hca' Hc ltac:(lia)
                ltac:(unfold apart in Aspca |- *; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_sub; [exact Wca|lia|lia]) Cmc)
    as (rA & RUN1 & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & KA).
  rewrite Hmc2 in Q9, Q14.
  match type of RUN1 with msteps _ _ (mkst _ _ (art_ic_mem ?X _ _) _) => set (M3 := X) in * end.
  set (MI := art_ic_mem M3 ca 31) in *.
  (* [comment removed for export] *)
  assert (T3 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 32 \/ sp <= a) -> (a + Z.of_nat k <= ca \/ ca + 4096 <= a) -> cellA M a k v -> cellA MI a k v).
  { intros a k v Ha Hak O Oc C. unfold MI. apply cell_ic_other; [lia|lia|lia|lia|lia| |].
    - intros c0 Hc0. unfold apart. lia.
    - unfold M3. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (WI : forall a k, wrA M a k -> wrA MI a k). { intros a k Hw. unfold MI. apply wr_ic. unfold M3. do 3 apply wr_Wn. exact Hw. }
  destruct (art_gfa_run ws rA MI rom (0x42258 : bv 64)%bv (sp - 32) ia (ca + 2560) c (ca + 80 * c + 16) spb ris qris nf na
              Q1 ltac:(unfold ret_ok; bveq) Q2 Q10 Q11 Q12 Q13 Q14
              ltac:(lia) ltac:(lia) ltac:(lia) Hia Hia' ltac:(lia) Hspb Hspb' Hris Hris' Eris ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnf Hnf' Hna Hna'
              ltac:(unfold apart in Arsp |- *; lia) ltac:(unfold apart in Aspca |- *; lia) ltac:(unfold apart in Acar |- *; lia) ltac:(unfold apart in Acafa |- *; lia)
              ltac:(unfold apart in Afasp |- *; lia) Afar
              ltac:(eapply wr_sub; [apply WI; exact W|lia|lia]) ltac:(apply WI; exact Wr) ltac:(eapply wr_sub; [apply WI; exact Wca|lia|lia])
              ltac:(apply T3; [lia|cbn; lia|cbn; lia|cbn; lia|exact Cspb]) ltac:(apply T3; [lia|cbn; lia|cbn; lia|cbn; lia|exact Cris])
              ltac:(apply T3; [lia|cbn; lia|cbn; unfold apart in Arsp; lia|cbn; unfold apart in Acar; lia|exact Cmx])
              ltac:(apply T3; [lia|cbn; lia|cbn; unfold apart in Arsp; lia|cbn; unfold apart in Acar; lia|exact Cnf])
              ltac:(apply T3; [lia|cbn; lia|cbn; unfold apart in Arsp; lia|cbn; unfold apart in Acar; lia|exact Cna])
              ltac:(apply T3; [lia|cbn; lia|cbn; lia|cbn; lia|exact Crd])
              ltac:(intros j Hj; destruct (Cws j Hj) as [R C]; split; [exact R|]; apply T3; [lia|cbn; lia|cbn; unfold apart in Afasp; lia|cbn; unfold apart in Acafa; lia|exact C]))
    as (r4 & RUN4 & P4_10 & P4_2 & P4_1 & K4).
  (* [comment removed for export] *)
  assert (EXT : forall x : reg, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA x = getr (art_refill_cold_rA regs sp ca c ia n) x).
  { intros x Hx. unfold art_refill_cold_rA. cbn [In] in Hx.
    destruct Hx as [<-|[<-|Hx]]; [rewrite Q8; gres; reflexivity | rewrite Q9; gres; reflexivity |].
    rewrite KA by (cbn [In]; tauto).
    repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; gres; reflexivity. }
  rewrite (art_gfa_mem_ext MI (sp - 32) (0x42258 : bv 64)%bv rA (art_refill_cold_rA regs sp ca c ia n)) in RUN4 by exact EXT.
  set (MG := art_gfa_mem MI (sp - 32) (0x42258 : bv 64)%bv (art_refill_cold_rA regs sp ca c ia n) (ris + 128 * c) (ca + 80 * c + 16) nf na ws) in *.
  assert (TG : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 32 + 32 -> sp - 32 <= a -> cellA M3 a k v -> cellA MG a k v).
  { intros a k v Ha Hak Hlo C. unfold MG, art_gfa_mem, art_gfa_frame. unfold apart in Arsp, Aspca, Afasp.
    do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; lia|]). apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; lia|].
    do 15 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; lia|]).
    apply cell_ic_other; [lia|lia|lia|lia|lia| |exact C]. intros c0 Hc0. unfold apart. lia. }
  assert (GM : mem_grows M MG).
  { unfold MG, art_gfa_mem. do 2 (eapply mem_grows_trans; [|apply Wn_grows]). eapply mem_grows_trans; [|apply art_w4s_grows]. do 2 (eapply mem_grows_trans; [|apply Wn_grows]).
    unfold art_gfa_frame. do 13 (eapply mem_grows_trans; [|apply Wn_grows]). unfold MI. eapply mem_grows_trans; [|apply art_ic_mem_grows].
    unfold M3. do 3 (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  pose proof (art_refill_b_fn r4 MG rom raw sp (ca + 80 * c) n (U (getr regs 8)) (U (getr regs 9))
                P4_2 ltac:(rewrite K4 by (cbn; tauto); exact Q8) ltac:(rewrite K4 by (cbn; tauto); exact Q9) P4_10
                ltac:(lia) Hsp' ltac:(lia) ltac:(lia) ltac:(lia) Hret (u64_range _) (u64_range _) ltac:(unfold apart in Aspca |- *; lia)
                ltac:(eapply wr_grows; [exact GM|eapply wr_sub; [exact Wca|lia|lia]])
                ltac:(apply TG; [lia|cbn; lia|lia|unfold M3; zcell])
                ltac:(apply TG; [lia|cbn; lia|lia|unfold M3; zcell])
                ltac:(apply TG; [lia|cbn; lia|lia|unfold M3; zcell]))
    as RUN5.
  match type of RUN5 with msteps _ _ (mkst ?R _ _ _) => exists R end.
  split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN4|]. unfold art_refill_cold_mem. fold n. fold M3. fold MI. fold MG. exact RUN5. }
  split; [gres; exact P4_10 || (gres; reflexivity)|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros rr Hr. pose proof Hr as Hr'. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned;
    rewrite K4 by exact Hr'; apply KA; cbn [In]; tauto.
Qed.

End FPX.
