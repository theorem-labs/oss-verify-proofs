(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatPoisonRun_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatMmapFixed_b BatPopulate1_b BatPopulate2_b BatPopulate3_b BatFp_b BatClsPop1_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_agree_carve : forall k M E au sz i, 0 <= i -> 0 <= E - 4 * (i + Z.of_nat k) -> E < 2 ^ 64 ->
  art_agree [(E - 4 * (i + Z.of_nat k), 4 * Z.of_nat k)] M (art_carve M E au sz i k).
Proof. intros k M E au sz i Hi HE HE' x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_carve_outside; [exact Hi|exact HE|exact HE'|lia]. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_D : forall regs (M rom : word -> option byte) (raw : word) (sp r rb sz au mu' nf new fb : Z) (g8 g9 g18 g19 g20 g21 g22 : word),
  let fa := rb + 3758096384 in
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 (nf + new) -> getr regs 10 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 rb ->
  getr regs 19 = Z_to_bv 64 new -> getr regs 20 = Z_to_bv 64 fb -> getr regs 21 = Z_to_bv 64 sz ->
  0x696000 + 64 <= sp -> sp < 2 ^ 47 -> ret_ok raw -> 0x696000 <= r -> r + 128 <= sp - 64 -> 0x696000 <= rb -> rb + 2 ^ 32 <= sp - 64 -> apart r 128 fa (2 ^ 29) ->
  32 <= sz <= 65536 -> sz <= fb < 2 ^ 64 -> 0 <= au -> 1 <= new -> au + new * sz <= mu' -> mu' <= 2 ^ 32 -> 0 <= nf -> 4 * (nf + new) <= 2 ^ 29 ->
  wrA M r 128 -> wrA M (fa + 4 * nf) (4 * new) ->
  cellA M (r + 32) 8 au -> cellA M (r + 16) 8 nf -> cellA M (r + 48) 8 mu' -> cellA M (r + 40) 8 0 -> cellA M (r + 56) 8 0 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 (U g8) -> cellA M (sp - 24) 8 (U g9) -> cellA M (sp - 32) 8 (U g18) -> cellA M (sp - 40) 8 (U g19) ->
  cellA M (sp - 48) 8 (U g20) -> cellA M (sp - 56) 8 (U g21) -> cellA M (sp - 64) 8 (U g22) ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x57a28 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ getr regs' 8 = g8 /\ getr regs' 9 = g9 /\ getr regs' 18 = g18 /\ getr regs' 19 = g19 /\ getr regs' 20 = g20 /\ getr regs' 21 = g21 /\ getr regs' 22 = g22
    /\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(fa + 4 * nf, 4 * new); (r + 16, 8); (r + 32, 8); (r + 68, 1)] M M'
    /\ cellA M' (r + 16) 8 (nf + new) /\ cellA M' (r + 32) 8 (au + new * sz)
    /\ (forall j, 0 <= j < new -> cellA M' (fa + 4 * (nf + new) - 4 * (j + 1)) 4 ((au + j * sz) / 16)).
Proof.
  intros regs M rom raw sp r rb sz au mu' nf new fb g8 g9 g18 g19 g20 g21 g22 fa H2 H8 H9 H10 H18 H19 H20 H21 IMG Hsp' Hret Hr Hr' Hrb Hrb' Arfa Hsz Hfb Hau Hnew Haumu Hmu' Hnf Htot
         Wr Wfa Cau Cnf Cmu Cam Cmm F1 F8 F9 F18 F19 F20 F21 F22.
  assert (Hfa : fa = rb + 3758096384) by reflexivity. clearbody fa.
  pose proof (art_pop_d_fn regs M rom r rb sz au (nf + new) fb H10 H8 H9 H18 H20 H21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsz Hfb ltac:(lia) ltac:(lia) Cau) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ _ _) => set (r1 := R) in RUN1 end.
  set (E := fa + 4 * (nf + new)).
  destruct (art_pop_loop (Z.to_nat new) r1 M rom E au sz 0 new
              ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1, E; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; exact H19) ltac:(unfold r1; gres; exact H21)
              ltac:(lia) ltac:(lia) ltac:(lia) Hau Hsz ltac:(lia) ltac:(unfold E; lia) ltac:(unfold E; lia)
              ltac:(rewrite Z2Nat.id by lia; replace (E - 4 * new) with (fa + 4 * nf) by (unfold E; lia); exact Wfa))
    as (r2 & RUN2 & K2).
  set (M2 := art_carve M E au sz 0 (Z.to_nat new)) in *.
  assert (A2 : art_agree [(fa + 4 * nf, 4 * new)] M M2).
  { pose proof (art_agree_carve (Z.to_nat new) M E au sz 0 ltac:(lia) ltac:(unfold E; lia) ltac:(unfold E; lia)) as A. rewrite Z2Nat.id in A by lia.
    replace (E - 4 * (0 + new)) with (fa + 4 * nf) in A by (unfold E; lia). exact A. }
  assert (G2 : mem_grows M M2) by apply art_carve_grows.
  assert (R2 : forall x : reg, x <> 10%bv -> x <> 12%bv -> x <> 14%bv -> x <> 15%bv -> getr r2 x = getr r1 x) by exact K2.
  assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  unfold apart in Arfa.
  pose proof (art_pop_e_fn r2 M2 rom raw sp r sz new au nf mu' 0 0 (new * sz) (U g8) (U g9) (U g18) (U g19) (U g20) (U g21) (U g22)
                ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H2) ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H8)
                ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; reflexivity) ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H19)
                ltac:(rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; exact H21)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsz ltac:(lia) ltac:(reflexivity) Hau Haumu ltac:(lia) Hnf ltac:(lia) ltac:(lia) ltac:(lia) Hret
                (UB g8) (UB g9) (UB g18) (UB g19) (UB g20) (UB g21) (UB g22)
                ltac:(unfold apart; lia) ltac:(eapply wr_grows; [exact G2|exact Wr])
                ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN3.
  match type of RUN3 with msteps _ _ (mkst ?R _ ?MM _) => set (r3 := R) in RUN3; set (M3 := MM) in RUN3 end.
  assert (A3 : art_agree [(r + 16, 8); (r + 32, 8); (r + 68, 1)] M2 M3). { unfold M3. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G3 : mem_grows M2 M3) by (unfold M3; zgrows).
  exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
  split; [unfold r3; gres; reflexivity|]. split; [unfold r3; gres; reflexivity|]. split; [unfold r3; gres; reflexivity|].
  split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r3; gres; apply Z_to_bv_bv_unsigned|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
           (unfold r3; gres; rewrite R2 by (intros E0; discriminate E0); unfold r1; gres; reflexivity). }
  split; [eapply mem_grows_trans; [exact G2|exact G3]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A2|exact A3]|]. zsub. }
  split; [unfold M3; zcell|]. split; [unfold M3; zcell|].
  intros j Hj. assert (C2 : cellA M2 (E - 4 * (j + 1)) 4 ((au + j * sz) / 16)).
  { unfold M2. apply cell_carve_hit; [lia|unfold E; lia|unfold E; lia|rewrite Z2Nat.id by lia; lia]. }
  fold E. ztr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_Cw : forall regs (M rom : word -> option byte) (sp r total mfa : Z),
  getr regs 1 = (0x57a28 : bv 64)%bv -> getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 11 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 total ->
  0x696000 + 112 <= sp -> sp < 2 ^ 47 -> 0x696000 <= r -> r + 128 <= sp - 112 -> 0 <= total -> 4 * total <= mfa -> mfa < 2 ^ 64 ->
  wrA M (sp - 112) 48 -> cellA M (r + 24) 8 mfa ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x55558 : word) M rom) (mkst regs' (0x57a28 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 112, 48)] M M'.
Proof.
  intros regs M rom sp r total mfa H1 H2 H11 H13 IMG Hsp' Hr Hr' Htot Hmfa Hmfa' W Cmfa.
  pose proof (art_efas_warm_fn regs M rom (0x57a28 : bv 64)%bv (sp - 64) r total mfa H1 ltac:(unfold ret_ok; bveq) H2 H11 H13 ltac:(lia) ltac:(lia) ltac:(lia) Hr ltac:(lia) Htot Hmfa Hmfa'
                ltac:(unfold apart; lia) ltac:(replace (sp - 64 - 48) with (sp - 112) by lia; exact W) Cmfa) as RUN.
  match type of RUN with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN; set (M1 := MM) in RUN end.
  exists r1, M1. split; [exact RUN|].
  split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; (unfold r1; gres; reflexivity). }
  split; [unfold M1, art_efas_frame; zgrows|]. unfold M1, art_efas_frame. eapply art_agree_sub; [zagree|]. zsub.
Qed.

#[using="Type"] Lemma art_mod4096_lin2 : forall a b c, (4096 * a + b * 2 ^ 32 + 3758096384 + 4096 * c) mod 4096 = 0.
Proof. intros a b c. replace (4096 * a + b * 2 ^ 32 + 3758096384 + 4096 * c) with ((a + b * 2 ^ 20 + 917504 + c) * 4096) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_Cm1 : forall regs (M rom : word -> option byte) (sp r c spb qs total mfa kf q rr addr2 : Z),
  addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa ->
  getr regs 1 = (0x57a28 : bv 64)%bv -> getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 r ->
  getr regs 12 = Z_to_bv 64 (spb + c * 2 ^ 32) -> getr regs 13 = Z_to_bv 64 total ->
  0x696000 + 512 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 30 -> 0x696000 <= r -> r + 128 <= sp - 512 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> spb = 65536 * qs ->
  0 <= total -> 0 <= mfa < 4 * total -> mfa = 262144 * kf -> 4 * total + 262143 = 262144 * q + rr -> 0 <= rr < 262144 -> 262144 * q <= 536870912 ->
  wrA M (sp - 512) 448 ->
  cellA M (r + 24) 8 mfa -> cellA M (1295832 + 56) 1 0 ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 260) 1 0 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x55558 : word) M rom) (mkst regs' (0x8bc80 : word) M' rom)
    /\ art_mmap_args regs' addr2 (262144 * q - mfa) 50
    /\ getr regs' 1 = Z_to_bv 64 0x8da40 /\ getr regs' 2 = Z_to_bv 64 (sp - 112 - 128) /\ getr regs' 8 = Z_to_bv 64 (262144 * q - mfa)
    /\ (forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 512, 448)] M M'
    /\ cellA M' (sp - 64 - 8) 8 0x57a28 /\ cellA M' (sp - 64 - 16) 8 (U (getr regs 8)) /\ cellA M' (sp - 64 - 24) 8 (U (getr regs 9))
    /\ cellA M' (sp - 64 - 32) 8 (U (getr regs 18)) /\ cellA M' (sp - 64 - 40) 8 (U (getr regs 19))
    /\ cellA M' (sp - 112 - 8) 8 0x555f8 /\ cellA M' (sp - 112 - 16) 8 (262144 * q) /\ cellA M' (sp - 112 - 24) 8 addr2 /\ cellA M' (sp - 112 - 32) 8 (262144 * q - mfa)
    /\ cellA M' (sp - 112 - 40) 8 0x95bf8 /\ cellA M' (sp - 112 - 48) 8 (262144 * q - mfa) /\ cellA M' (sp - 112 - 56) 8 addr2 /\ cellA M' (sp - 112 - 64) 8 (262144 * q - mfa)
    /\ cellA M' (sp - 112 - 72) 8 r /\ cellA M' (sp - 112 - 80) 8 (U (getr regs 20)).      (* [comment removed for export] *)
Proof.
  intros regs M rom sp r c spb qs total mfa kf q rr addr2 Haddr2 H1 H2 H10 H11 H12 H13 IMG Hsp' Hc Hr Hr' Hspb Hspb' Espb Htot Hmfa Emfa Eq Hrr Hq W Cmfa Cpm Cpg1 Cpg2 Ccf Cdec.
  pose proof (art_efas_a_fn regs M rom (0x57a28 : bv 64)%bv (sp - 64) 1295832 r (spb + c * 2 ^ 32) total mfa q rr H1 H2 H10 H11 H12 H13
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr ltac:(lia) ltac:(lia) ltac:(lia) Htot Hmfa Eq Hrr Hq
                ltac:(unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Cmfa Cpm) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  assert (A1 : art_agree [(sp - 512, 448)] M M1). { unfold M1, art_efas_frame. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G1 : mem_grows M M1) by (unfold M1, art_efas_frame; zgrows).
  assert (Hq1 : kf + 1 <= q) by lia.
  assert (Ha4 : addr2 mod 4096 = 0).
  { rewrite Haddr2, Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with (4096 * (16 * qs) + c * 2 ^ 32 + 3758096384 + 4096 * (64 * kf)) by lia. apply art_mod4096_lin2. }
  assert (Hl4 : (262144 * q - mfa) mod 4096 = 0). { rewrite Emfa. replace (262144 * q - 262144 * kf) with ((64 * (q - kf)) * 4096) by lia. apply Z_mod_mult. }
  pose proof (art_rar_map_pre_fn r1 M1 rom (0x555f8 : bv 64)%bv (sp - 112) addr2 (262144 * q - mfa) 104781 0x1d1768 0
                ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia)
                ltac:(unfold r1; gres; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) Ha4 ltac:(lia) Hl4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
                ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia])
                ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ ?MM _) => set (r2 := R) in RUN2; set (M2 := MM) in RUN2 end.
  assert (A2 : art_agree [(sp - 512, 400)] M1 M2).
  { intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold M2. apply art_rar_map_mem_agree; [lia|lia|lia]. }
  assert (G2 : mem_grows M1 M2) by (apply art_rar_map_mem_grows).
  destruct (art_rar_map_mem_cells M1 (sp - 112) (0x555f8 : bv 64)%bv r1 addr2 (262144 * q - mfa) 104781 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F8 & F9 & F18 & D1 & D8 & D9 & D18 & D19 & D20).
  fold M2 in F1, F8, F9, F18, D1, D8, D9, D18, D19, D20.
  exists r2, M2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  split. { unfold art_mmap_args, r2. repeat split; gres; reflexivity. }
  split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; (unfold r2, r1; gres; reflexivity). }
  split; [eapply mem_grows_trans; [exact G1|exact G2]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. zsub. }
  assert (E8 : cellA M1 (sp - 64 - 8) 8 0x57a28 /\ cellA M1 (sp - 64 - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 64 - 24) 8 (U (getr regs 9))
               /\ cellA M1 (sp - 64 - 32) 8 (U (getr regs 18)) /\ cellA M1 (sp - 64 - 40) 8 (U (getr regs 19))).
  { unfold M1, art_efas_frame. repeat split; zcell. }
  destruct E8 as (E1 & E8 & E9 & E18 & E19).
  split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|].
  split; [exact F1|].
  assert (X8 : U (getr r1 8) = 262144 * q). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X9 : U (getr r1 9) = addr2). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X18 : U (getr r1 18) = 262144 * q - mfa). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X19 : U (getr r1 19) = r). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X20 : getr r1 20 = getr regs 20). { unfold r1; gres. reflexivity. }
  rewrite X8 in F8. rewrite X9 in F9. rewrite X18 in F18, D18. rewrite X19 in D19. rewrite X20 in D20.
  split; [exact F8|]. split; [exact F9|]. split; [exact F18|].
  split; [exact D1|]. split; [exact D8|]. split; [exact D9|]. split; [exact D18|]. split; [exact D19|]. exact D20.
Qed.

#[using="Type"] Lemma art_div8_lin2 : forall qs c kf, (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) / 8 = 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf.
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) * 8) by lia. apply Z_div_mult. lia. Qed.
#[using="Type"] Lemma art_mod8_lin2 : forall qs c kf, (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) mod 8 = 0.
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) * 8) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_Cm2 : forall regs (M rom : word -> option byte) (sp tp key tsd ctx t r c spb qs mfa kf q m1 m2 addr2 len2 shb2 : Z) (g8 g9 g18 g19 g20 : word),
  addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa -> len2 = 262144 * q - mfa -> shb2 = 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf ->
  getr regs 1 = Z_to_bv 64 0x8da40 -> getr regs 2 = Z_to_bv 64 (sp - 112 - 128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 len2 -> getr regs 10 = Z_to_bv 64 addr2 ->
  0x696000 + 512 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 30 -> spb = 65536 * qs -> mfa = 262144 * kf -> 0 <= kf -> kf + 1 <= q -> 262144 * q <= 536870912 ->
  kHighMemBeg <= spb -> spb + 2 ^ 37 < 2 ^ 47 ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 ->
  4096 <= t -> t + 4096 <= sp - 512 -> 0x696000 <= r -> r + 128 <= sp - 512 -> apart t 4096 r 128 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 -> 4096 <= ctx -> ctx + 4096 <= sp - 512 ->
  apart shb2 (32768 * (q - kf)) t 4096 -> apart shb2 (32768 * (q - kf)) r 128 -> apart shb2 (32768 * (q - kf)) ctx 4096 -> shb2 + 32768 * (q - kf) <= sp - 512 ->
  wrA M (sp - 512) 400 -> wrA M shb2 (32768 * (q - kf)) -> wrA M (t + 2872) 16 -> wrA M r 128 ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  cellA M (sp - 64 - 8) 8 0x57a28 -> cellA M (sp - 64 - 16) 8 (U g8) -> cellA M (sp - 64 - 24) 8 (U g9) -> cellA M (sp - 64 - 32) 8 (U g18) -> cellA M (sp - 64 - 40) 8 (U g19) ->
  cellA M (sp - 112 - 8) 8 0x555f8 -> cellA M (sp - 112 - 16) 8 (262144 * q) -> cellA M (sp - 112 - 24) 8 addr2 -> cellA M (sp - 112 - 32) 8 len2 ->
  cellA M (sp - 112 - 40) 8 0x95bf8 -> cellA M (sp - 112 - 48) 8 len2 -> cellA M (sp - 112 - 56) 8 addr2 -> cellA M (sp - 112 - 64) 8 len2 ->
  cellA M (sp - 112 - 72) 8 r -> cellA M (sp - 112 - 80) 8 (U g20) ->
  cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 144) 8 0 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x8bc84 : word) M rom) (mkst regs' (0x57a28 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ getr regs' 8 = g8 /\ getr regs' 9 = g9 /\ getr regs' 18 = g18 /\ getr regs' 19 = g19 /\ getr regs' 20 = g20
    /\ (forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf)); (t + 2872, 16); (r + 24, 8)] M M'
    /\ cellA M' (t + 2872) 8 (m1 + 1) /\ cellA M' (t + 2880) 8 (m2 + len2) /\ cellA M' (r + 24) 8 (262144 * q).
Proof.
  intros regs M rom sp tp key tsd ctx t r c spb qs mfa kf q m1 m2 addr2 len2 shb2 g8 g9 g18 g19 g20 Haddr2 Hlen2 Hshb2 H1 H2 H4 H8 H10 IMG Hsp' Hc Espb Emfa Hkf Hq1 Hq Hspb Hspb'
         Hm1 Hm2 Ht Ht' Hr Hr' Atr Htp Htp' Htsd Htsd' Hctx Hctx' Ast Asr Asc Hshsp W Wsh Wts Wr L T E1 E8 E9 E18 E19 F1 F8 F9 F18 D1 D8 D9 D18 D19 D20 Ccf Clim Cm1 Cm2.
  unfold kHighMemBeg in Hspb.
  assert (Eshb : SB + addr2 / 8 = shb2). { rewrite Haddr2, Hshb2. unfold SB. rewrite Espb, Emfa, art_div8_lin2. lia. }
  assert (El8 : len2 / 8 = 32768 * (q - kf)). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_div_mult. lia. }
  assert (Hl8 : len2 mod 8 = 0). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_mod_mult. }
  assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  (* [comment removed for export] *)
  pose proof (art_rar_map_post_fn regs M rom (0x555f8 : bv 64)%bv (Z_to_bv 64 (262144 * q)) (Z_to_bv 64 addr2) (Z_to_bv 64 len2) (Z_to_bv 64 r) g20
                (Z_to_bv 64 len2) (Z_to_bv 64 addr2) (Z_to_bv 64 len2)
                (sp - 112) len2 addr2 0x1d1768 H1 H2 H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia])
                ltac:(exact F1) ltac:(rewrite art_u_lit by lia; exact F8) ltac:(rewrite art_u_lit by lia; exact F9) ltac:(rewrite art_u_lit by lia; exact F18)
                ltac:(exact D1) ltac:(rewrite art_u_lit by lia; exact D8) ltac:(rewrite art_u_lit by lia; exact D9)
                ltac:(rewrite art_u_lit by lia; exact D18) ltac:(rewrite art_u_lit by lia; exact D19) ltac:(exact D20)
                Ccf Clim) as RUN1.      (* [comment removed for export] *)
  match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  assert (A1 : art_agree [(sp - 512, 400)] M M1). { eapply art_agree_sub; [unfold M1; zagree|]. zsub. }
  assert (G1 : mem_grows M M1) by (unfold M1; zgrows).
  (* [comment removed for export] *)
  pose proof (art_efas_b_fn r1 M1 rom addr2 len2 ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(lia)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ _ _) => set (r2 := R) in RUN2 end.
  (* [comment removed for export] *)
  assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. repeat split; lia. }
  destruct (art_poison_hi_run r2 M1 rom (0x55614 : bv 64)%bv (sp - 112) addr2 len2 250
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r2, r1; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
              L1 ltac:(unfold kHighMemBeg; lia) ltac:(unfold kHighMemEnd; lia)
              ltac:(rewrite Haddr2, Espb, Emfa; apply art_mod8_lin2) Hl8 ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E)
              ltac:(rewrite Eshb, El8; eapply wr_grows; [exact G1|exact Wsh]))
    as (r3 & RUN3 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
  match type of RUN3 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in RUN3 end.
  assert (A3 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M1 M3).
  { unfold M3, art_poison_frame. rewrite Eshb, El8. eapply art_agree_sub; [zagree|]. rewrite Z2Nat.id by lia. zsub. }
  assert (G3 : mem_grows M1 M3) by (unfold M3, art_poison_frame; zgrows).
  assert (A13 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M M3). { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A3]|]. zsub. }
  assert (G13 : mem_grows M M3) by (eapply mem_grows_trans; eassumption).
  assert (Hqs : 0 <= qs) by lia.
  assert (T3 : art_tsd M3 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A13| | |exact Htp|exact Htp'|exact Htsd|exact Htsd'|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. cbn. unfold apart in Asc. repeat split; lia. }
  assert (R3_4 : getr r3 4 = Z_to_bv 64 tp). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H4. }
  assert (R3_8 : getr r3 8 = Z_to_bv 64 (262144 * q)). { rewrite P8. unfold r2, r1; gres. reflexivity. }
  assert (R3_18 : getr r3 18 = Z_to_bv 64 len2). { rewrite P18. unfold r2, r1; gres. reflexivity. }
  assert (R3_19 : getr r3 19 = Z_to_bv 64 r). { rewrite P19. unfold r2, r1; gres. reflexivity. }
  unfold apart in Ast, Asr, Atr.
  pose proof (art_efas_c_fn r3 M3 rom (0x57a28 : bv 64)%bv (sp - 64) tp key tsd ctx t r (262144 * q) len2 m1 m2 (U g8) (U g9) (U g18) (U g19)
                ltac:(rewrite P2; f_equal; lia) R3_4 R3_8 R3_18 R3_19
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold ret_ok; bveq)
                Hm1 Hm2 ltac:(lia) ltac:(lia) (UB g8) (UB g9) (UB g18) (UB g19)
                ltac:(eapply wr_grows; [exact G13|]; eapply wr_sub; [exact W|lia|lia]) T3
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; destruct T as (_ & _ & _ & _ & _ & _ & _ & Hk & _); lia) ltac:(unfold apart; lia)
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
                ltac:(eapply wr_grows; [exact G13|exact Wts]) ltac:(eapply wr_grows; [exact G13|exact Wr])
                ltac:(ztr) ltac:(ztr) ltac:(change (U (0x57a28 : bv 64)%bv) with 0x57a28; ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN4.
  match type of RUN4 with msteps _ _ (mkst ?R _ ?MM _) => set (r4 := R) in RUN4; set (M4 := MM) in RUN4 end.
  assert (A4 : art_agree [(sp - 512, 400); (t + 2872, 16); (r + 24, 8)] M3 M4).
  { unfold M4, art_efas_c_mem. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G4 : mem_grows M3 M4) by (unfold M4, art_efas_c_mem; zgrows).
  exists r4, M4. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|exact RUN4]|].
  split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
  split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r4; gres; rewrite P20; unfold r2, r1; gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
           first [ unfold r4; gres; rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E); unfold r2, r1; gres; reflexivity
                 | unfold r4; gres; rewrite P21; unfold r2, r1; gres; reflexivity ]. }
  split; [eapply mem_grows_trans; [exact G13|exact G4]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A13|exact A4]|]. zsub. }
  unfold M4, art_efas_c_mem.
  split; [zcell|]. split; [zcell|]. zcell.
Qed.
End FPX.
