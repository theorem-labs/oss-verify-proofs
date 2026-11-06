(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp EbtRefill1 EbtPopulate1 EbtPopulate2 EbtCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtRecycle3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rta_lock_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia mp st c chp n spb ris qris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 mp -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 chp -> getr regs 15 = Z_to_bv 64 n ->
  0x69c000 + 128 <= sp -> sp < 2 ^ 64 -> 0x10000 <= ia -> ia + 4096 <= 0x69c000 -> 1 <= c <= 31 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris ->
  apart (ris + 128 * c) 128 (sp - 128) 128 -> 0 <= mp < 2 ^ 64 -> 0 <= st < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  wrA M (sp - 128) 128 -> wrA M (ris + 128 * c) 128 ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 ->
  msteps ASEGS (mkst regs (0x56240 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 (ris + 128 * c))) 9 (Z_to_bv 64 16140901064495857663)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 18446744073709551615)) 12 (Z_to_bv 64 (spb + c * 2 ^ 32))) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (2 ^ 60))) 16 (Z_to_bv 64 0)) 17 (Z_to_bv 64 1500)) 18 (Z_to_bv 64 c)) 19 (Z_to_bv 64 mp)) 20 (Z_to_bv 64 ia)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 chp)) 23 (Z_to_bv 64 (2 ^ 40))) 24 (Z_to_bv 64 (2 ^ 61))) 25 (Z_to_bv 64 (spb + c * 2 ^ 32 + 3758096384))) 26 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1))) 27 (Z_to_bv 64 (2 ^ 60)))
       (0x5638c : word) (Wn 8 (Wn 8 (art_gfa_frame M sp raw regs) (sp - 112) (ris + 128 * c + 8)) (ris + 128 * c) (2 ^ 60)) rom).
Proof.
  intros regs M rom raw sp ia mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hc Hspb Hspb' Hris Hris' Eris Ar Hmp Hst Hchp Hn W Wr Cspb Cris Cmx.
  zstep F_561f0 D_561f0.
  zsd F_561f4 D_561f4 (sp - 8) (U raw) ltac:(rewok W). zsd F_561f8 D_561f8 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_561fc D_561fc (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_56200 D_56200 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_56204 D_56204 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_56208 D_56208 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_5620c D_5620c (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_56210 D_56210 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_56214 D_56214 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_56218 D_56218 (sp - 80) (U (getr regs 24)) ltac:(rewok W). zsd F_5621c D_5621c (sp - 88) (U (getr regs 25)) ltac:(rewok W). zsd F_56220 D_56220 (sp - 96) (U (getr regs 26)) ltac:(rewok W).
  zsd F_56224 D_56224 (sp - 104) (U (getr regs 27)) ltac:(rewok W).
  zstep F_56228 D_56228. zstep F_5622c D_5622c. zstep F_56230 D_56230. zstep F_56234 D_56234. zstep F_56238 D_56238. zstep F_5623c D_5623c. zstep F_56240 D_56240.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
  zld F_56244 D_56244 (ia + 32) Cspb'. zld F_56248 D_56248 (ia + 48) Cris'.
  zstep F_5624c D_5624c. zstep F_56250 D_56250. zstep F_56254 D_56254. zstep F_56258 D_56258. zstep F_5625c D_5625c. zstep F_56260 D_56260. zstep F_56264 D_56264.
  zstep F_56268 D_56268. zstep F_5626c D_5626c. zstep F_56270 D_56270. zstep F_56274 D_56274. zstep F_56278 D_56278. zstep F_5627c D_5627c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx' : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell) end.
  zld F_56280 D_56280 (ris + c * 2 ^ 7) Cmx'.
  zstep F_56284 D_56284.
  zsd F_56288 D_56288 (sp - 112) (ris + c * 2 ^ 7 + 8) ltac:(rewok W).
  zstep F_5628c D_5628c. zstep F_56290 D_56290.
  stepn F_56294 D_56294. rwH. zclosed 16140901064495857664.
  zstep F_56298 D_56298.
  stepn F_5629c D_5629c. rwH. zclosed 0.
  zbft F_562a0 D_562a0.
  stepn F_562a4 D_562a4. rwH. zclosed (2 ^ 60).
  stepn F_562a8 D_562a8. rwH. zclosed (2 ^ 60).
  assert (Hr8 : (ris + c * 2 ^ 7) mod 8 = 0). { rewrite Eris. replace (128 * qris + c * 2 ^ 7) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx2 : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell);
                                                   assert (Wr' : wokA X (ris + c * 2 ^ 7) 8) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zwok) end.
  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)) _ (Z_to_bv 64 0));
      [exact F_562ac | reflexivity | exact D_562ac | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cmx2 | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_562b0 | reflexivity | exact D_562b0 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)));
      [exact F_562b4 | reflexivity | exact D_562b4 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wr' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 (ris + c * 2 ^ 7)) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 60)))) with (Wn 8 M0 (ris + c * 2 ^ 7) (2 ^ 60)).
  zbft F_562b8 D_562b8.
  zbtk F_562bc D_562bc.
  unfold art_gfa_frame. zret.
Qed.

#[using="Type"] Lemma art_rta_copy : forall ws regs (M rom : word -> option byte) (dst src send : Z),
  getr regs 25 = Z_to_bv 64 dst -> getr regs 22 = Z_to_bv 64 src -> getr regs 10 = Z_to_bv 64 send ->
  send = src + 4 * Z.of_nat (length ws) -> (1 <= length ws)%nat ->
  0 <= src -> send < 2 ^ 64 -> 4096 <= dst -> dst + 4 * Z.of_nat (length ws) < 2 ^ 64 ->
  apart dst (4 * Z.of_nat (length ws)) src (4 * Z.of_nat (length ws)) ->
  wrA M dst (4 * Z.of_nat (length ws)) ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (src + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x563bc : word) M rom) (mkst regs' (0x563d0 : word) (art_w4s M dst ws) rom)
    /\ (forall r : reg, r <> 11%bv -> r <> 22%bv -> r <> 25%bv -> getr regs' r = getr regs r).
Proof.
  induction ws as [|w ws IH]; intros regs M rom dst src send H25 H22 H10 Esend Hlen Hs Hs' Hd Hd' A W Cws; cbn [length] in *. lia.
  destruct (Cws O ltac:(lia)) as [Rw Cw]. cbn [nth] in Rw, Cw. replace (src + 4 * Z.of_nat 0) with src in Cw by lia.
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x563bc : word) M rom) (mkst regs1 (0x563cc : word) (Wn 4 M dst w) rom)
            /\ getr regs1 25 = Z_to_bv 64 (dst + 4) /\ getr regs1 22 = Z_to_bv 64 (src + 4) /\ getr regs1 10 = Z_to_bv 64 send
            /\ (forall r : reg, r <> 11%bv -> r <> 22%bv -> r <> 25%bv -> getr regs1 r = getr regs r)).
  { eexists. split.
    - zlw F_5636c D_5636c src Cw.
      zstep F_56370 D_56370.
      zsw F_56374 D_56374 dst w ltac:(rewok W).
      zstep F_56378 D_56378. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P25 & P22 & P10 & K1).
  destruct ws as [|w2 ws2].
  - cbn [length] in *. eexists. split.
    + eapply msteps_trans; [exact RUN1|]. cbn [art_w4s]. zbft F_5637c D_5637c. apply mst_refl.
    + intros r N11 N22 N25. gres. apply K1; assumption.
  - cbn [length] in *.
    assert (RUNb : msteps ASEGS (mkst regs1 (0x563cc : word) (Wn 4 M dst w) rom) (mkst regs1 (0x563bc : word) (Wn 4 M dst w) rom)).
    { zbtk F_5637c D_5637c. apply mst_refl. }
    unfold apart in A.
    destruct (IH regs1 (Wn 4 M dst w) rom (dst + 4) (src + 4) send P25 P22 P10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold apart; lia) ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])
                 ltac:(intros j Hj; destruct (Cws (S j) ltac:(lia)) as [R C]; split; [exact R|];
                       replace (src + 4 + 4 * Z.of_nat j) with (src + 4 * Z.of_nat (S j)) by lia; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|exact C]))
      as (regs' & RUN2 & K2).
    exists regs'. split.
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_w4s]. exact RUN2.
    + intros r N11 N22 N25. rewrite K2 by assumption. apply K1; assumption.
Qed.

Ltac inl3 := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac gkeep3 K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).

#[using="Type"] Lemma art_rta_mid_run : forall ws regs (M rom : word -> option byte) (sp HI ia mp c chp n r rb nf mfa nfr : Z),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 12 = Z_to_bv 64 rb -> getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 mp ->
  getr regs 20 = Z_to_bv 64 ia -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 chp -> getr regs 25 = Z_to_bv 64 (rb + 3758096384) ->
  0x69c000 <= HI -> HI <= sp - 176 -> sp < 2 ^ 64 -> 0x69c000 <= r -> r + 128 <= HI -> 0x69c000 <= rb -> rb + 2 ^ 32 <= HI -> HI < 2 ^ 47 ->
  n = Z.of_nat (length ws) -> 1 <= n <= 16 -> 4096 <= chp -> chp + 4 * n <= HI -> 0 <= nf -> 4 * (nf + n) <= mfa -> mfa <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 ->
  0 <= ia < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  apart (rb + 3758096384 + 4 * nf) (4 * n) chp (4 * n) -> apart chp (4 * n) r 128 -> apart r 128 (rb + 3758096384) (2 ^ 29) ->
  wrA M (sp - 176) 48 -> wrA M r 128 -> wrA M (rb + 3758096384) mfa ->
  cellA M (r + 16) 8 nf -> cellA M (r + 24) 8 mfa -> cellA M (r + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x5638c : word) M rom) (mkst regs' (0x566e8 : word) M' rom)
    /\ getr regs' 1 = (0x563f4 : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 128) /\ getr regs' 10 = Z_to_bv 64 ia /\ getr regs' 11 = Z_to_bv 64 mp
    /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 0
    /\ (forall x : reg, In x [3; 4; 8; 24]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)] M M'
    /\ cellA M' (r + 16) 8 (nf + n) /\ cellA M' (r + 80) 8 (nfr + n)
    /\ (forall j, (j < length ws)%nat -> cellA M' (rb + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)).
Proof.
  intros ws regs M rom sp HI ia mp c chp n r rb nf mfa nfr H2 H8 H12 H18 H19 H20 H21 H22 H25 HHI Hsp Hsp' Hr Hr' Hrb Hrb' HHI' En Hn Hchp Hchp' Hnf Hmfa Hmfa' Hnfr Hia Hmp Hc
    A1 A2 A3 W Wr Wfa Cnf Cmfa Cnfr Cws.
  unfold apart in A1, A2, A3.
  eassert (RUN1 : msteps ASEGS (mkst regs (0x5638c : word) M rom) _).
  { zld F_5633c D_5633c (r + 16) Cnf.
    zstep F_56340 D_56340. zstep F_56344 D_56344. zstep F_56348 D_56348. zstep F_5634c D_5634c.
    stepn F_56350 D_56350.
    zcall (art_efas_warm_fn _ _ _ (0x563a4 : word) (sp - 128) r (nf + n) mfa).
    zbft F_56354 D_56354.
    zbft F_56358 D_56358.
    zstep F_5635c D_5635c. zstep F_56360 D_56360. zstep F_56364 D_56364. zstep F_56368 D_56368.
    apply mst_refl. }
  unfold art_efas_frame in RUN1.
  assert (Hlen : (1 <= length ws)%nat) by lia.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0))
      by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
    assert (Wfa1 : wrA X1 (rb + 3758096384 + 4 * nf) (4 * Z.of_nat (length ws))) by (repeat apply wr_Wn; eapply wr_sub; [exact Wfa|lia|lia]);
    assert (Cnfr1 : cellA X1 (r + 80) 8 nfr) by zcell;
    assert (Wr1 : wrA X1 r 128) by zwr;
    assert (G1 : mem_grows M X1) by zgrows;
    assert (AG1 : art_agree [(sp - 176, 48)] M X1) by (eapply art_agree_sub; [zagree|]; zsub);
    destruct (art_rta_copy ws R1 X1 rom (rb + 3758096384 + 4 * nf) chp (chp + 4 * n) ltac:(gres; f_equal; lia) ltac:(gres; rwH; reflexivity) ltac:(gres; f_equal; lia)
                ltac:(lia) Hlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Wfa1 Cws1) as (r2 & RUN2 & K2);
    gkeep3 K2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -128)); gkeep3 K2 r2 (8%bv : reg) (Z_to_bv 64 r); gkeep3 K2 r2 (18%bv : reg) (Z_to_bv 64 c);
    gkeep3 K2 r2 (19%bv : reg) (Z_to_bv 64 mp); gkeep3 K2 r2 (20%bv : reg) (Z_to_bv 64 ia); gkeep3 K2 r2 (21%bv : reg) (Z_to_bv 64 n); gkeep3 K2 r2 (23%bv : reg) (Z_to_bv 64 (nf + n));
    set (X2 := art_w4s X1 (rb + 3758096384 + 4 * nf) ws) in *;
    assert (Cnfr2 : cellA X2 (r + 80) 8 nfr) by (apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|exact Cnfr1]);
    assert (Wr2 : wrA X2 r 128) by (eapply wr_grows; [apply art_w4s_grows|exact Wr1]);
    assert (G2 : mem_grows X1 X2) by (apply art_w4s_grows);
    assert (AG2 : art_agree [(rb + 3758096384 + 4 * nf, 4 * n)] X1 X2) by (intros x Hx; cbn [art_out fst snd] in Hx; apply art_w4s_outside; [lia|lia|rewrite <- En; tauto]);
    assert (CW2 : forall j, (j < length ws)%nat -> cellA X2 (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) 4 (nth j ws 0))
      by (intros j Hj; apply cell_w4s_nth; [lia|lia|exact Hj|intros k Hk; destruct (Cws k Hk) as [Rk _]; lia])
  end.
  clearbody X2.
  match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
  { zld F_56380 D_56380 (r + 80) Cnfr2.
    zsd F_56384 D_56384 (r + 16) (nf + n) ltac:(zwok').
    zstep F_56388 D_56388.
    zsd F_5638c D_5638c (r + 80) (nfr + n) ltac:(zwok').
    zstep F_56390 D_56390. zstep F_56394 D_56394. zstep F_56398 D_56398. zstep F_5639c D_5639c.
    stepn F_563a0 D_563a0.
    apply mst_refl. }
  eexists. eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; bveq|]. split; [gres; rwH; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rewrite K2 by reg_neq_tac; gres; first [reflexivity | rwH; reflexivity]|]). destruct Hx. }
  split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. zgrows. }
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; zagree|]. zsub. }
  split; [zcell|]. split; [zcell|].
  intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. replace (rb + 3758096384 + 4 * (nf + Z.of_nat j)) with (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) by lia.
  apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact (CW2 j Hj).
Qed.

Ltac zcl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ =>
  let v := eval vm_compute in (bv_unsigned x) in replace x with (Z_to_bv 64 v : word) by (apply bv_eq; vm_compute; reflexivity) end.

#[using="Type"] Lemma art_rta_tail_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 24 = Z_to_bv 64 (2 ^ 61) ->
  128 <= sp -> sp < 2 ^ 64 -> r = ris + 128 * c -> ris = 128 * qris -> 0 <= ris -> 1 <= c <= 31 -> r + 128 < 2 ^ 64 -> apart r 8 (sp - 128) 128 -> ret_ok raw ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 -> 0 <= g23 < 2 ^ 64 ->
  0 <= g24 < 2 ^ 64 -> 0 <= g25 < 2 ^ 64 -> 0 <= g26 < 2 ^ 64 -> 0 <= g27 < 2 ^ 64 ->
  wokA M r 8 -> cellA M r 8 (2 ^ 60) -> cellA M 0x10430 8 0xafffff00000fffff ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 -> cellA M (sp - 80) 8 g24 -> cellA M (sp - 88) 8 g25 -> cellA M (sp - 96) 8 g26 -> cellA M (sp - 104) 8 g27 ->
  msteps ASEGS (mkst regs (0x563f4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 0)) 6 (Z_to_bv 64 1152921504606846976)) 7 (Z_to_bv 64 0)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1152921504606846976)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 6917529027641081856)) 13 (Z_to_bv 64 12682135451164737535)) 14 (Z_to_bv 64 17293822569102704639)) 15 (Z_to_bv 64 1152920405095219200)) 16 (Z_to_bv 64 18446742974197923840)) 17 (Z_to_bv 64 4611686018427387904)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20)) 21 (Z_to_bv 64 g21)) 22 (Z_to_bv 64 g22)) 23 (Z_to_bv 64 g23)) 24 (Z_to_bv 64 g24)) 25 (Z_to_bv 64 g25)) 26 (Z_to_bv 64 g26)) 27 (Z_to_bv 64 g27))
       raw (Wn 8 M r 0) rom).
Proof.
  intros regs M rom raw sp r ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 H2 H8 H24 Hsp Hsp' Er Eris Hris Hc Hr' Ar Hret
         Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24 Hg25 Hg26 Hg27 Wst Cst Crd F8 F16 F24 F32 F40 F48 F56 F64 F72 F80 F88 F96 F104.
  assert (Hr8 : r mod 8 = 0). { rewrite Er, Eris. replace (128 * qris + 128 * c) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
  zld F_563a4 D_563a4 r Cst.
  stepn F_563a8 D_563a8. zcl. stepn F_563ac D_563ac. zcl. stepn F_563b0 D_563b0. zcl.
  stepn F_563b4 D_563b4.
  stepn F_563b8 D_563b8. zcl. stepn F_563bc D_563bc. zcl. stepn F_563c0 D_563c0. zcl.
  zld F_563c4 D_563c4 0x10430 Crd.
  stepn F_563c8 D_563c8. zcl. stepn F_563cc D_563cc. zcl. stepn F_563d0 D_563d0. zcl. stepn F_563d4 D_563d4. zcl. stepn F_563d8 D_563d8. zcl.
  stepn F_563dc D_563dc.
  stepn F_563f8 D_563f8. zcl. stepn F_563fc D_563fc. zcl.
  zbft F_56400 D_56400.
  stepn F_56404 D_56404. zcl.
  zbtk F_56408 D_56408.
  stepn F_5642c D_5642c. rwH. zcl. stepn F_56430 D_56430. zcl. stepn F_56434 D_56434. zcl. stepn F_56438 D_56438. zcl. stepn F_5643c D_5643c. zcl.
  stepn F_56440 D_56440. zcl. stepn F_56444 D_56444. zcl.
  zbtk F_56448 D_56448.
  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r) _ (Z_to_bv 64 (2 ^ 60)));
      [exact F_563e0 | reflexivity | exact D_563e0 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cst | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_563e4 | reflexivity | exact D_563e4 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite ?art_u_lit by lia; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r));
      [exact F_563e8 | reflexivity | exact D_563e8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wst ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 r) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 r 0).
  zbft F_563ec D_563ec.
  zbtk F_563f0 D_563f0.
  zbft F_56458 D_56458.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E8 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (E16 : cellA X (sp - 16) 8 g8) by zcell; assert (E24 : cellA X (sp - 24) 8 g9) by zcell;
    assert (E32 : cellA X (sp - 32) 8 g18) by zcell; assert (E40 : cellA X (sp - 40) 8 g19) by zcell; assert (E48 : cellA X (sp - 48) 8 g20) by zcell;
    assert (E56 : cellA X (sp - 56) 8 g21) by zcell; assert (E64 : cellA X (sp - 64) 8 g22) by zcell; assert (E72 : cellA X (sp - 72) 8 g23) by zcell;
    assert (E80 : cellA X (sp - 80) 8 g24) by zcell; assert (E88 : cellA X (sp - 88) 8 g25) by zcell; assert (E96 : cellA X (sp - 96) 8 g26) by zcell;
    assert (E104 : cellA X (sp - 104) 8 g27) by zcell end.
  zld F_5645c D_5645c (sp - 8) E8. rewrite Z_to_bv_bv_unsigned.
  zld F_56460 D_56460 (sp - 16) E16. zld F_56464 D_56464 (sp - 24) E24. zld F_56468 D_56468 (sp - 32) E32. zld F_5646c D_5646c (sp - 40) E40.
  zld F_56470 D_56470 (sp - 48) E48. zld F_56474 D_56474 (sp - 56) E56. zld F_56478 D_56478 (sp - 64) E64. zld F_5647c D_5647c (sp - 72) E72.
  zld F_56480 D_56480 (sp - 80) E80. zld F_56484 D_56484 (sp - 88) E88. zld F_56488 D_56488 (sp - 96) E96. zld F_5648c D_5648c (sp - 104) E104.
  zstep F_56490 D_56490.
  stepret F_56494 D_56494 raw ltac:(reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rta_run : forall ws regs (M rom : word -> option byte) (raw : word) (sp HI ia mp st c chp n spb ris qris nf mfa nfr : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 mp -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 chp -> getr regs 15 = Z_to_bv 64 n ->
  0x69c000 <= HI -> HI <= sp - 208 -> sp < 2 ^ 64 -> HI + 8388608 <= 2 ^ 47 -> 0x10000 <= ia -> ia + 4096 <= 0x69c000 -> 1 <= c <= 30 ->
  0x69c000 <= spb -> ris = spb + 2 ^ 37 -> ris = 128 * qris -> ris + 4096 <= HI ->
  n = Z.of_nat (length ws) -> 1 <= n <= 16 -> 4096 <= chp -> chp + 4 * n <= HI -> apart chp (4 * n) spb (2 ^ 37 + 4096) ->
  0 <= nf < 2 ^ 40 -> 4 * (nf + n) <= mfa -> mfa <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= st < 2 ^ 64 ->
  wrA M (sp - 208) 208 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ia + 40) 4 0xffffffff -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 -> cellA M 0x10430 8 0xafffff00000fffff ->
  cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x56240 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M'
    /\ art_agree [(sp - 208, 208); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * n); (ris + 128 * c, 8); (ris + 128 * c + 16, 8); (ris + 128 * c + 80, 8)] M M'
    /\ cellA M' (ris + 128 * c) 8 0 /\ cellA M' (ris + 128 * c + 16) 8 (nf + n) /\ cellA M' (ris + 128 * c + 80) 8 (nfr + n)
    /\ (forall j, (j < length ws)%nat -> cellA M' (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)).
Proof.
  intros ws regs M rom raw sp HI ia mp st c chp n spb ris qris nf mfa nfr H1 Hret H2 H10 H11 H12 H13 H14 H15 HHI Hsp Hsp' HHI' Hia Hia' Hc Hspb Eris Eq Hris' En Hn Hchp Hchp' Achp
    Hnf Hmfa Hmfa' Hnfr Hmp Hst W Wr Wfa Cspb Cris Crel Cpc Cpg Crd Cmx Cnf Cmfa Cnfr Cws.
  set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *.
  assert (Hr : 0x69c000 <= r /\ r + 128 <= HI) by (unfold r; lia). destruct Hr as (Hr & Hr').
  assert (Hrb : 0x69c000 <= rb /\ rb + 2 ^ 32 <= ris) by (unfold rb; lia). destruct Hrb as (Hrb & Hrb').
  unfold apart in Achp.

  pose proof (art_rta_lock_fn regs M rom raw sp ia mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) Hsp' Hia Hia' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Eq
                ltac:(unfold apart; fold r; lia) Hmp Hst ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Cspb Cris Cmx) as RUN1.
  fold r in RUN1. unfold art_gfa_frame in RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (F1 : mem_grows M X1 /\ art_agree [(sp - 208, 208); (r, 8)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    assert (C1 : cellA X1 r 8 (2 ^ 60) /\ cellA X1 (r + 16) 8 nf /\ cellA X1 (r + 24) 8 mfa /\ cellA X1 (r + 80) 8 nfr
                 /\ cellA X1 (ia + 48) 8 ris /\ cellA X1 (ia + 40) 4 0xffffffff /\ cellA X1 0x13d8a8 8 0x1d5ba0 /\ cellA X1 0x1d5ba0 8 4096 /\ cellA X1 0x10430 8 0xafffff00000fffff
                 /\ cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 16) 8 (U (getr regs 8)) /\ cellA X1 (sp - 24) 8 (U (getr regs 9)) /\ cellA X1 (sp - 32) 8 (U (getr regs 18))
                 /\ cellA X1 (sp - 40) 8 (U (getr regs 19)) /\ cellA X1 (sp - 48) 8 (U (getr regs 20)) /\ cellA X1 (sp - 56) 8 (U (getr regs 21)) /\ cellA X1 (sp - 64) 8 (U (getr regs 22))
                 /\ cellA X1 (sp - 72) 8 (U (getr regs 23)) /\ cellA X1 (sp - 80) 8 (U (getr regs 24)) /\ cellA X1 (sp - 88) 8 (U (getr regs 25)) /\ cellA X1 (sp - 96) 8 (U (getr regs 26))
                 /\ cellA X1 (sp - 104) 8 (U (getr regs 27))) by (repeat split; zcell);
    assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0))
      by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
    assert (W1 : wrA X1 (sp - 208) 208 /\ wrA X1 r 128 /\ wrA X1 (rb + 3758096384) mfa) by (repeat split; zwr);
    set (Ra := R1) in *; set (Xa := X1) in *
  end.
  destruct F1 as (G1 & AG1). destruct W1 as (W1a & W1r & W1f).
  destruct C1 as (Cst1 & Cnf1 & Cmfa1 & Cnfr1 & Cris1 & Crel1 & Cpc1 & Cpg1 & Crd1 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104).
  clearbody Xa.

  destruct (art_rta_mid_run ws Ra Xa rom sp HI ia mp c chp n r rb nf mfa nfr ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
              ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
              ltac:(unfold Ra; gres; reflexivity) HHI ltac:(lia) Hsp' Hr Hr' Hrb ltac:(lia) ltac:(lia) En Hn Hchp Hchp' ltac:(lia) Hmfa Hmfa' Hnfr ltac:(lia) Hmp ltac:(lia)
              ltac:(unfold apart, rb; lia) ltac:(unfold apart, r; lia) ltac:(unfold apart, r, rb; lia)
              ltac:(eapply wr_sub; [exact W1a|lia|lia]) W1r W1f Cnf1 Cmfa1 Cnfr1 Cws1)
    as (r2 & M2 & RUN2 & B1 & B2 & B10 & B11 & B12 & B13 & BK & G2 & AG2 & Cnf2 & Cnfr2 & Cfa2).

  set (W2 := [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)]) in *.
  assert (T2 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M2 a k v).
  { intros a k v G Ha Hk C. exact (art_cell_tr W2 Xa M2 a k v AG2 G Ha Hk C). }
  assert (GI : forall a k, 0x10000 <= a -> a + k <= 0x69c000 -> art_gap W2 a k).
  { intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (Cris2 : cellA M2 (ia + 48) 8 ris) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cris1]).
  assert (Crel2 : cellA M2 (ia + 40) 4 0xffffffff) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Crel1]).
  assert (Cpc2 : cellA M2 0x13d8a8 8 0x1d5ba0) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpc1]).
  assert (Cpg2 : cellA M2 0x1d5ba0 8 4096) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpg1]).
  destruct (art_mrtos_ret r2 M2 rom (0x563f4 : bv 64)%bv (sp - 128) ia c ris (nf + n) ((nfr + n) mod 2 ^ 64) B1 ltac:(unfold ret_ok; bveq) B2 B10 B12 B13 ltac:(lia) ltac:(lia)
              ltac:(eapply wr_grows; [exact G2|]; eapply wr_sub; [exact W1a|lia|lia]) Hc Hia ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; fold r; lia) ltac:(lia)
              ltac:(apply Z.mod_pos_bound; lia) ltac:(eapply wr_grows; [exact G2|exact W1r]) Cris2 Cpc2 Cpg2 Crel2 Cnf2 ltac:(apply art_cell_norm; exact Cnfr2))
    as (r3 & RUN3 & D2 & DK).
  destruct (art_f80_facts M2 (sp - 128) (0x563f4 : bv 64)%bv r2 ltac:(lia) ltac:(lia)) as (G3 & AG3).
  set (M3 := art_f80 M2 (sp - 128) (0x563f4 : bv 64)%bv r2) in *. clearbody M3.
  replace (sp - 128 - 80) with (sp - 208) in AG3 by lia.

  assert (T3 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> apart a (Z.of_nat k) (sp - 208) 80 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M3 a k v).
  { intros a k v G A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|]. exact (T2 a k v G Ha Hk C). }
  assert (GF : forall a k, sp - 128 <= a -> a + k <= sp -> art_gap W2 a k /\ apart a k (sp - 208) 80).
  { intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GR : art_gap W2 r 8 /\ apart r 8 (sp - 208) 80) by (unfold W2; cbn [art_gap fst snd]; unfold apart, r, rb; repeat split; try exact I; lia).
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
  pose proof (bv_unsigned_in_range 64 (getr regs 19)) as R19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as R20. pose proof (bv_unsigned_in_range 64 (getr regs 21)) as R21.
  pose proof (bv_unsigned_in_range 64 (getr regs 22)) as R22. pose proof (bv_unsigned_in_range 64 (getr regs 23)) as R23. pose proof (bv_unsigned_in_range 64 (getr regs 24)) as R24.
  pose proof (bv_unsigned_in_range 64 (getr regs 25)) as R25. pose proof (bv_unsigned_in_range 64 (getr regs 26)) as R26. pose proof (bv_unsigned_in_range 64 (getr regs 27)) as R27.
  change (bv_modulus 64) with (2 ^ 64) in *.
  pose proof (art_rta_tail_fn r3 M3 rom raw sp r ris qris c _ _ _ _ _ _ _ _ _ _ _ _ D2
                ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity) ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity)
                ltac:(lia) Hsp' eq_refl Eq ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Hret R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
                ltac:(apply (wr_wok _ _ r 128); [eapply wr_grows; [exact G3|]; eapply wr_grows; [exact G2|exact W1r]|lia|cbn; lia])
                ltac:(apply T3; [apply GR|apply GR|lia|cbn; lia|exact Cst1]) ltac:(apply T3; [apply GI; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Crd1])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E8]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E16])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E24]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E32])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E40]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E48])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E56]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E64])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E72]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E80])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E88]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E96])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E104])) as RUN4.
  assert (T4 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 208) 80 -> apart a (Z.of_nat k) r 8 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA (Wn 8 M3 r 0) a k v).
  { intros a k v A1 A2 Ha Hk C. apply cell_Wn_other; [lia|cbn; lia|exact Ha|exact Hk|apply apart_sym; exact A2|].
    apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A1|exact I]|exact Ha|exact Hk|exact C]. }
  eexists. exists (Wn 8 M3 r 0).
  split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|]; exact RUN4|].
  split; [gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
    destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
    repeat (destruct Hx as [<-|Hx]; [gres; apply Z_to_bv_bv_unsigned|]). destruct Hx. }
  split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G3|]. apply Wn_grows. }
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; eapply art_agree_trans; [exact AG3|]; apply art_agree_Wn; [lia|cbn; lia]|].
           unfold W2. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia. }
  split; [apply cell_Wn_hit; [lia|cbn; lia]|].
  split; [apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2]|].
  split; [apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2]|].
  intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T4; [unfold apart, rb; cbn; lia|unfold apart, r, rb; cbn; lia|unfold rb; lia|unfold rb; cbn; lia|exact (Cfa2 j Hj)].
Qed.
End FPX.
