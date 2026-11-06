(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison ArtRuns ArtRunsMem EatFp EatRefill1 EatPopulate1 EatPopulate2 EatCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatRecycle3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rta_lock_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia mp st c chp n spb ris qris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 mp -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 chp -> getr regs 15 = Z_to_bv 64 n ->
  0x698000 + 128 <= sp -> sp < 2 ^ 64 -> 0x10000 <= ia -> ia + 4096 <= 0x698000 -> 1 <= c <= 31 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris ->
  apart (ris + 128 * c) 128 (sp - 128) 128 -> 0 <= mp < 2 ^ 64 -> 0 <= st < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  wrA M (sp - 128) 128 -> wrA M (ris + 128 * c) 128 ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 ->
  msteps ASEGS (mkst regs (0x55a18 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 (ris + 128 * c))) 9 (Z_to_bv 64 16140901064495857663)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 18446744073709551615)) 12 (Z_to_bv 64 (spb + c * 2 ^ 32))) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (2 ^ 60))) 16 (Z_to_bv 64 0)) 17 (Z_to_bv 64 1500)) 18 (Z_to_bv 64 c)) 19 (Z_to_bv 64 mp)) 20 (Z_to_bv 64 ia)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 chp)) 23 (Z_to_bv 64 (2 ^ 40))) 24 (Z_to_bv 64 (2 ^ 61))) 25 (Z_to_bv 64 (spb + c * 2 ^ 32 + 3758096384))) 26 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1))) 27 (Z_to_bv 64 (2 ^ 60)))
       (0x55b64 : word) (Wn 8 (Wn 8 (art_gfa_frame M sp raw regs) (sp - 112) (ris + 128 * c + 8)) (ris + 128 * c) (2 ^ 60)) rom).
Proof.
  intros regs M rom raw sp ia mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hc Hspb Hspb' Hris Hris' Eris Ar Hmp Hst Hchp Hn W Wr Cspb Cris Cmx.
  zstep F_559c8 D_559c8.
  zsd F_559cc D_559cc (sp - 8) (U raw) ltac:(rewok W). zsd F_559d0 D_559d0 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_559d4 D_559d4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_559d8 D_559d8 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_559dc D_559dc (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_559e0 D_559e0 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_559e4 D_559e4 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_559e8 D_559e8 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_559ec D_559ec (sp - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_559f0 D_559f0 (sp - 80) (U (getr regs 24)) ltac:(rewok W). zsd F_559f4 D_559f4 (sp - 88) (U (getr regs 25)) ltac:(rewok W). zsd F_559f8 D_559f8 (sp - 96) (U (getr regs 26)) ltac:(rewok W).
  zsd F_559fc D_559fc (sp - 104) (U (getr regs 27)) ltac:(rewok W).
  zstep F_55a00 D_55a00. zstep F_55a04 D_55a04. zstep F_55a08 D_55a08. zstep F_55a0c D_55a0c. zstep F_55a10 D_55a10. zstep F_55a14 D_55a14. zstep F_55a18 D_55a18.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
  zld F_55a1c D_55a1c (ia + 32) Cspb'. zld F_55a20 D_55a20 (ia + 48) Cris'.
  zstep F_55a24 D_55a24. zstep F_55a28 D_55a28. zstep F_55a2c D_55a2c. zstep F_55a30 D_55a30. zstep F_55a34 D_55a34. zstep F_55a38 D_55a38. zstep F_55a3c D_55a3c.
  zstep F_55a40 D_55a40. zstep F_55a44 D_55a44. zstep F_55a48 D_55a48. zstep F_55a4c D_55a4c. zstep F_55a50 D_55a50. zstep F_55a54 D_55a54.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx' : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell) end.
  zld F_55a58 D_55a58 (ris + c * 2 ^ 7) Cmx'.
  zstep F_55a5c D_55a5c.
  zsd F_55a60 D_55a60 (sp - 112) (ris + c * 2 ^ 7 + 8) ltac:(rewok W).
  zstep F_55a64 D_55a64. zstep F_55a68 D_55a68.
  stepn F_55a6c D_55a6c. rwH. zclosed 16140901064495857664.
  zstep F_55a70 D_55a70.
  stepn F_55a74 D_55a74. rwH. zclosed 0.
  zbft F_55a78 D_55a78.
  stepn F_55a7c D_55a7c. rwH. zclosed (2 ^ 60).
  stepn F_55a80 D_55a80. rwH. zclosed (2 ^ 60).
  assert (Hr8 : (ris + c * 2 ^ 7) mod 8 = 0). { rewrite Eris. replace (128 * qris + c * 2 ^ 7) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx2 : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell);
                                                   assert (Wr' : wokA X (ris + c * 2 ^ 7) 8) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zwok) end.
  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)) _ (Z_to_bv 64 0));
      [exact F_55a84 | reflexivity | exact D_55a84 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cmx2 | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_55a88 | reflexivity | exact D_55a88 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)));
      [exact F_55a8c | reflexivity | exact D_55a8c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wr' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 (ris + c * 2 ^ 7)) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 60)))) with (Wn 8 M0 (ris + c * 2 ^ 7) (2 ^ 60)).
  zbft F_55a90 D_55a90.
  zbtk F_55a94 D_55a94.
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
    msteps ASEGS (mkst regs (0x55b94 : word) M rom) (mkst regs' (0x55ba8 : word) (art_w4s M dst ws) rom)
    /\ (forall r : reg, r <> 11%bv -> r <> 22%bv -> r <> 25%bv -> getr regs' r = getr regs r).
Proof.
  induction ws as [|w ws IH]; intros regs M rom dst src send H25 H22 H10 Esend Hlen Hs Hs' Hd Hd' A W Cws; cbn [length] in *. lia.
  destruct (Cws O ltac:(lia)) as [Rw Cw]. cbn [nth] in Rw, Cw. replace (src + 4 * Z.of_nat 0) with src in Cw by lia.
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x55b94 : word) M rom) (mkst regs1 (0x55ba4 : word) (Wn 4 M dst w) rom)
            /\ getr regs1 25 = Z_to_bv 64 (dst + 4) /\ getr regs1 22 = Z_to_bv 64 (src + 4) /\ getr regs1 10 = Z_to_bv 64 send
            /\ (forall r : reg, r <> 11%bv -> r <> 22%bv -> r <> 25%bv -> getr regs1 r = getr regs r)).
  { eexists. split.
    - zlw F_55b44 D_55b44 src Cw.
      zstep F_55b48 D_55b48.
      zsw F_55b4c D_55b4c dst w ltac:(rewok W).
      zstep F_55b50 D_55b50. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P25 & P22 & P10 & K1).
  destruct ws as [|w2 ws2].
  - cbn [length] in *. eexists. split.
    + eapply msteps_trans; [exact RUN1|]. cbn [art_w4s]. zbft F_55b54 D_55b54. apply mst_refl.
    + intros r N11 N22 N25. gres. apply K1; assumption.
  - cbn [length] in *.
    assert (RUNb : msteps ASEGS (mkst regs1 (0x55ba4 : word) (Wn 4 M dst w) rom) (mkst regs1 (0x55b94 : word) (Wn 4 M dst w) rom)).
    { zbtk F_55b54 D_55b54. apply mst_refl. }
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
  0x698000 <= HI -> HI <= sp - 176 -> sp < 2 ^ 64 -> 0x698000 <= r -> r + 128 <= HI -> 0x698000 <= rb -> rb + 2 ^ 32 <= HI -> HI < 2 ^ 47 ->
  n = Z.of_nat (length ws) -> 1 <= n <= 16 -> 4096 <= chp -> chp + 4 * n <= HI -> 0 <= nf -> 4 * (nf + n) <= mfa -> mfa <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 ->
  0 <= ia < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  apart (rb + 3758096384 + 4 * nf) (4 * n) chp (4 * n) -> apart chp (4 * n) r 128 -> apart r 128 (rb + 3758096384) (2 ^ 29) ->
  wrA M (sp - 176) 48 -> wrA M r 128 -> wrA M (rb + 3758096384) mfa ->
  cellA M (r + 16) 8 nf -> cellA M (r + 24) 8 mfa -> cellA M (r + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x55b64 : word) M rom) (mkst regs' (0x55ec0 : word) M' rom)
    /\ getr regs' 1 = (0x55bcc : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 128) /\ getr regs' 10 = Z_to_bv 64 ia /\ getr regs' 11 = Z_to_bv 64 mp
    /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 0
    /\ (forall x : reg, In x [3; 4; 8; 24]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)] M M'
    /\ cellA M' (r + 16) 8 (nf + n) /\ cellA M' (r + 80) 8 (nfr + n)
    /\ (forall j, (j < length ws)%nat -> cellA M' (rb + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)).
Proof.
  intros ws regs M rom sp HI ia mp c chp n r rb nf mfa nfr H2 H8 H12 H18 H19 H20 H21 H22 H25 HHI Hsp Hsp' Hr Hr' Hrb Hrb' HHI' En Hn Hchp Hchp' Hnf Hmfa Hmfa' Hnfr Hia Hmp Hc
    A1 A2 A3 W Wr Wfa Cnf Cmfa Cnfr Cws.
  unfold apart in A1, A2, A3.
  eassert (RUN1 : msteps ASEGS (mkst regs (0x55b64 : word) M rom) _).
  { zld F_55b14 D_55b14 (r + 16) Cnf.
    zstep F_55b18 D_55b18. zstep F_55b1c D_55b1c. zstep F_55b20 D_55b20. zstep F_55b24 D_55b24.
    stepn F_55b28 D_55b28.
    zcall (art_efas_warm_fn _ _ _ (0x55b7c : word) (sp - 128) r (nf + n) mfa).
    zbft F_55b2c D_55b2c.
    zbft F_55b30 D_55b30.
    zstep F_55b34 D_55b34. zstep F_55b38 D_55b38. zstep F_55b3c D_55b3c. zstep F_55b40 D_55b40.
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
  { zld F_55b58 D_55b58 (r + 80) Cnfr2.
    zsd F_55b5c D_55b5c (r + 16) (nf + n) ltac:(zwok').
    zstep F_55b60 D_55b60.
    zsd F_55b64 D_55b64 (r + 80) (nfr + n) ltac:(zwok').
    zstep F_55b68 D_55b68. zstep F_55b6c D_55b6c. zstep F_55b70 D_55b70. zstep F_55b74 D_55b74.
    stepn F_55b78 D_55b78.
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
  wokA M r 8 -> cellA M r 8 (2 ^ 60) -> cellA M 0x10428 8 0xafffff00000fffff ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 -> cellA M (sp - 80) 8 g24 -> cellA M (sp - 88) 8 g25 -> cellA M (sp - 96) 8 g26 -> cellA M (sp - 104) 8 g27 ->
  msteps ASEGS (mkst regs (0x55bcc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 0)) 6 (Z_to_bv 64 1152921504606846976)) 7 (Z_to_bv 64 0)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1152921504606846976)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 6917529027641081856)) 13 (Z_to_bv 64 12682135451164737535)) 14 (Z_to_bv 64 17293822569102704639)) 15 (Z_to_bv 64 1152920405095219200)) 16 (Z_to_bv 64 18446742974197923840)) 17 (Z_to_bv 64 4611686018427387904)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20)) 21 (Z_to_bv 64 g21)) 22 (Z_to_bv 64 g22)) 23 (Z_to_bv 64 g23)) 24 (Z_to_bv 64 g24)) 25 (Z_to_bv 64 g25)) 26 (Z_to_bv 64 g26)) 27 (Z_to_bv 64 g27))
       raw (Wn 8 M r 0) rom).
Proof.
  intros regs M rom raw sp r ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 H2 H8 H24 Hsp Hsp' Er Eris Hris Hc Hr' Ar Hret
         Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24 Hg25 Hg26 Hg27 Wst Cst Crd F8 F16 F24 F32 F40 F48 F56 F64 F72 F80 F88 F96 F104.
  assert (Hr8 : r mod 8 = 0). { rewrite Er, Eris. replace (128 * qris + 128 * c) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
  zld F_55b7c D_55b7c r Cst.
  stepn F_55b80 D_55b80. zcl. stepn F_55b84 D_55b84. zcl. stepn F_55b88 D_55b88. zcl.
  stepn F_55b8c D_55b8c.
  stepn F_55b90 D_55b90. zcl. stepn F_55b94 D_55b94. zcl. stepn F_55b98 D_55b98. zcl.
  zld F_55b9c D_55b9c 0x10428 Crd.
  stepn F_55ba0 D_55ba0. zcl. stepn F_55ba4 D_55ba4. zcl. stepn F_55ba8 D_55ba8. zcl. stepn F_55bac D_55bac. zcl. stepn F_55bb0 D_55bb0. zcl.
  stepn F_55bb4 D_55bb4.
  stepn F_55bd0 D_55bd0. zcl. stepn F_55bd4 D_55bd4. zcl.
  zbft F_55bd8 D_55bd8.
  stepn F_55bdc D_55bdc. zcl.
  zbtk F_55be0 D_55be0.
  stepn F_55c04 D_55c04. rwH. zcl. stepn F_55c08 D_55c08. zcl. stepn F_55c0c D_55c0c. zcl. stepn F_55c10 D_55c10. zcl. stepn F_55c14 D_55c14. zcl.
  stepn F_55c18 D_55c18. zcl. stepn F_55c1c D_55c1c. zcl.
  zbtk F_55c20 D_55c20.
  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r) _ (Z_to_bv 64 (2 ^ 60)));
      [exact F_55bb8 | reflexivity | exact D_55bb8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cst | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_55bbc | reflexivity | exact D_55bbc | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite ?art_u_lit by lia; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r));
      [exact F_55bc0 | reflexivity | exact D_55bc0 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wst ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 r) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 r 0).
  zbft F_55bc4 D_55bc4.
  zbtk F_55bc8 D_55bc8.
  zbft F_55c30 D_55c30.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E8 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (E16 : cellA X (sp - 16) 8 g8) by zcell; assert (E24 : cellA X (sp - 24) 8 g9) by zcell;
    assert (E32 : cellA X (sp - 32) 8 g18) by zcell; assert (E40 : cellA X (sp - 40) 8 g19) by zcell; assert (E48 : cellA X (sp - 48) 8 g20) by zcell;
    assert (E56 : cellA X (sp - 56) 8 g21) by zcell; assert (E64 : cellA X (sp - 64) 8 g22) by zcell; assert (E72 : cellA X (sp - 72) 8 g23) by zcell;
    assert (E80 : cellA X (sp - 80) 8 g24) by zcell; assert (E88 : cellA X (sp - 88) 8 g25) by zcell; assert (E96 : cellA X (sp - 96) 8 g26) by zcell;
    assert (E104 : cellA X (sp - 104) 8 g27) by zcell end.
  zld F_55c34 D_55c34 (sp - 8) E8. rewrite Z_to_bv_bv_unsigned.
  zld F_55c38 D_55c38 (sp - 16) E16. zld F_55c3c D_55c3c (sp - 24) E24. zld F_55c40 D_55c40 (sp - 32) E32. zld F_55c44 D_55c44 (sp - 40) E40.
  zld F_55c48 D_55c48 (sp - 48) E48. zld F_55c4c D_55c4c (sp - 56) E56. zld F_55c50 D_55c50 (sp - 64) E64. zld F_55c54 D_55c54 (sp - 72) E72.
  zld F_55c58 D_55c58 (sp - 80) E80. zld F_55c5c D_55c5c (sp - 88) E88. zld F_55c60 D_55c60 (sp - 96) E96. zld F_55c64 D_55c64 (sp - 104) E104.
  zstep F_55c68 D_55c68.
  stepret F_55c6c D_55c6c raw ltac:(reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rta_run : forall ws regs (M rom : word -> option byte) (raw : word) (sp HI ia mp st c chp n spb ris qris nf mfa nfr : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 mp -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 chp -> getr regs 15 = Z_to_bv 64 n ->
  0x698000 <= HI -> HI <= sp - 208 -> sp < 2 ^ 64 -> HI + 8388608 <= 2 ^ 47 -> 0x10000 <= ia -> ia + 4096 <= 0x698000 -> 1 <= c <= 30 ->
  0x698000 <= spb -> ris = spb + 2 ^ 37 -> ris = 128 * qris -> ris + 4096 <= HI ->
  n = Z.of_nat (length ws) -> 1 <= n <= 16 -> 4096 <= chp -> chp + 4 * n <= HI -> apart chp (4 * n) spb (2 ^ 37 + 4096) ->
  0 <= nf < 2 ^ 40 -> 4 * (nf + n) <= mfa -> mfa <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= st < 2 ^ 64 ->
  wrA M (sp - 208) 208 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ia + 40) 4 0xffffffff -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 -> cellA M 0x10428 8 0xafffff00000fffff ->
  cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x55a18 : word) M rom) (mkst regs' raw M' rom)
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
  assert (Hr : 0x698000 <= r /\ r + 128 <= HI) by (unfold r; lia). destruct Hr as (Hr & Hr').
  assert (Hrb : 0x698000 <= rb /\ rb + 2 ^ 32 <= ris) by (unfold rb; lia). destruct Hrb as (Hrb & Hrb').
  unfold apart in Achp.

  pose proof (art_rta_lock_fn regs M rom raw sp ia mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) Hsp' Hia Hia' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Eq
                ltac:(unfold apart; fold r; lia) Hmp Hst ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Cspb Cris Cmx) as RUN1.
  fold r in RUN1. unfold art_gfa_frame in RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (F1 : mem_grows M X1 /\ art_agree [(sp - 208, 208); (r, 8)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    assert (C1 : cellA X1 r 8 (2 ^ 60) /\ cellA X1 (r + 16) 8 nf /\ cellA X1 (r + 24) 8 mfa /\ cellA X1 (r + 80) 8 nfr
                 /\ cellA X1 (ia + 48) 8 ris /\ cellA X1 (ia + 40) 4 0xffffffff /\ cellA X1 0x139198 8 0x1d14a0 /\ cellA X1 0x1d14a0 8 4096 /\ cellA X1 0x10428 8 0xafffff00000fffff
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
  assert (GI : forall a k, 0x10000 <= a -> a + k <= 0x698000 -> art_gap W2 a k).
  { intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (Cris2 : cellA M2 (ia + 48) 8 ris) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cris1]).
  assert (Crel2 : cellA M2 (ia + 40) 4 0xffffffff) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Crel1]).
  assert (Cpc2 : cellA M2 0x139198 8 0x1d14a0) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpc1]).
  assert (Cpg2 : cellA M2 0x1d14a0 8 4096) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpg1]).
  destruct (art_mrtos_ret r2 M2 rom (0x55bcc : bv 64)%bv (sp - 128) ia c ris (nf + n) ((nfr + n) mod 2 ^ 64) B1 ltac:(unfold ret_ok; bveq) B2 B10 B12 B13 ltac:(lia) ltac:(lia)
              ltac:(eapply wr_grows; [exact G2|]; eapply wr_sub; [exact W1a|lia|lia]) Hc Hia ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; fold r; lia) ltac:(lia)
              ltac:(apply Z.mod_pos_bound; lia) ltac:(eapply wr_grows; [exact G2|exact W1r]) Cris2 Cpc2 Cpg2 Crel2 Cnf2 ltac:(apply art_cell_norm; exact Cnfr2))
    as (r3 & RUN3 & D2 & DK).
  destruct (art_f80_facts M2 (sp - 128) (0x55bcc : bv 64)%bv r2 ltac:(lia) ltac:(lia)) as (G3 & AG3).
  set (M3 := art_f80 M2 (sp - 128) (0x55bcc : bv 64)%bv r2) in *. clearbody M3.
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
