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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatAllocG EatFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Definition art_gfa_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (bv_unsigned raw)) (sp - 16) (bv_unsigned (getr regs 8))) (sp - 24) (bv_unsigned (getr regs 9))) (sp - 32) (bv_unsigned (getr regs 18))) (sp - 40) (bv_unsigned (getr regs 19))) (sp - 48) (bv_unsigned (getr regs 20))) (sp - 56) (bv_unsigned (getr regs 21))) (sp - 64) (bv_unsigned (getr regs 22))) (sp - 72) (bv_unsigned (getr regs 23))) (sp - 80) (bv_unsigned (getr regs 24))) (sp - 88) (bv_unsigned (getr regs 25))) (sp - 96) (bv_unsigned (getr regs 26))) (sp - 104) (bv_unsigned (getr regs 27))).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_gfa_lock_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia st c chp n spb ris qris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  128 <= sp -> sp < 2 ^ 64 -> 0x698000 + 128 <= sp -> 0x10000 <= ia -> ia + 4096 <= 0x698000 -> 1 <= c <= 31 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris ->
  apart (ris + 128 * c) 128 (sp - 128) 128 -> 0 <= st < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  wrA M (sp - 128) 128 -> wrA M (ris + 128 * c) 128 ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 ->
  msteps ASEGS (mkst regs (0x57d74 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (Z_to_bv 64 (sp - 128))) 5 (Z_to_bv 64 0)) 6 (Z_to_bv 64 (2 ^ 60))) 7 (Z_to_bv 64 0)) 8 (Z_to_bv 64 (ris + 128 * c))) 9 (Z_to_bv 64 ia)) 10 (Z_to_bv 64 (ris + 128 * c + 8))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 19 (Z_to_bv 64 (2 ^ 61))) 20 (Z_to_bv 64 (spb + c * 2 ^ 32 + 3758096384))) 21 (Z_to_bv 64 (2 ^ 40))) 22 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1))) 23 (Z_to_bv 64 (2 ^ 60))) 24 (Z_to_bv 64 1500)) 25 (Z_to_bv 64 (2 ^ 64 - 2 ^ 61 - 1))) (0x57ec4 : word) (Wn 8 (art_gfa_frame M sp raw regs) (ris + 128 * c) (2 ^ 60)) rom).
Proof.
  intros regs M rom raw sp ia st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hc Hspb Hspb' Hris Hris' Eris Ar Hst Hchp Hn W Wr Cspb Cris Cmx.
  zstep F_57d24 D_57d24.
  zsd F_57d28 D_57d28 (sp - 8) (U raw) ltac:(rewok W). zsd F_57d2c D_57d2c (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_57d30 D_57d30 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_57d34 D_57d34 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_57d38 D_57d38 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_57d3c D_57d3c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_57d40 D_57d40 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_57d44 D_57d44 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_57d48 D_57d48 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_57d4c D_57d4c (sp - 80) (U (getr regs 24)) ltac:(rewok W). zsd F_57d50 D_57d50 (sp - 88) (U (getr regs 25)) ltac:(rewok W). zsd F_57d54 D_57d54 (sp - 96) (U (getr regs 26)) ltac:(rewok W).
  zsd F_57d58 D_57d58 (sp - 104) (U (getr regs 27)) ltac:(rewok W).
  zstep F_57d5c D_57d5c. zstep F_57d60 D_57d60. zstep F_57d64 D_57d64.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
  zld F_57d68 D_57d68 (ia + 32) Cspb'. zld F_57d6c D_57d6c (ia + 48) Cris'.
  zstep F_57d70 D_57d70. zstep F_57d74 D_57d74. zstep F_57d78 D_57d78. zstep F_57d7c D_57d7c. zstep F_57d80 D_57d80. zstep F_57d84 D_57d84.
  zstep F_57d88 D_57d88. zstep F_57d8c D_57d8c. zstep F_57d90 D_57d90. zstep F_57d94 D_57d94. zstep F_57d98 D_57d98. zstep F_57d9c D_57d9c. zstep F_57da0 D_57da0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx' : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell);
                                                   assert (Wr' : wok Asan.M.loaded_segments X (ris + c * 2 ^ 7) 8) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; rewok Wr) end.
  zld F_57da4 D_57da4 (ris + c * 2 ^ 7) Cmx'.
  zstep F_57da8 D_57da8.
  zstep F_57dac D_57dac. zstep F_57db0 D_57db0.
  stepn F_57db4 D_57db4. rwH. try rewrite art_zb_slli by lia.
  zstep F_57db8 D_57db8.
  stepn F_57dbc D_57dbc. rwH. try (rewrite art_zb_and by lia; rewrite Z.land_0_l).
  zbft F_57dc0 D_57dc0.
  stepn F_57dc4 D_57dc4. rwH. try (unfold v_or; rewrite !art_u_lit by lia; rewrite Z.lor_0_l).
  stepn F_57dc8 D_57dc8. rwH. try (rewrite art_zb_and by lia; rewrite art_land_full_l by lia).
  assert (Hr8 : (ris + c * 2 ^ 7) mod 8 = 0). { rewrite Eris. replace (128 * qris + c * 2 ^ 7) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }

  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)) _ (Z_to_bv 64 0));
      [exact F_57dcc | reflexivity | exact D_57dcc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cmx' | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_57dd0 | reflexivity | exact D_57dd0 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)));
      [exact F_57dd4 | reflexivity | exact D_57dd4 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wr' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 (ris + c * 2 ^ 7)) (word_to_le_bytes 8 (Z_to_bv 64 1152921504606846976))) with (Wn 8 M0 (ris + c * 2 ^ 7) (2 ^ 60)).
  zbft F_57dd8 D_57dd8.
  zbtk F_57ddc D_57ddc.
  unfold art_gfa_frame. zret.
Qed.
End FPX.

Fixpoint art_w4s (M : word -> option byte) (dst : Z) (ws : list Z) : word -> option byte :=
  match ws with [] => M | w :: ws' => art_w4s (Wn 4 M dst w) (dst + 4) ws' end.

Lemma art_w4s_grows : forall ws M dst, mem_grows M (art_w4s M dst ws).
Proof. induction ws as [|w ws IH]; intros M dst; cbn [art_w4s]. apply mem_grows_refl. eapply mem_grows_trans; [apply Wn_grows | apply IH]. Qed.
Lemma art_w4s_outside : forall ws M dst (x : word), 0 <= dst -> dst + 4 * Z.of_nat (length ws) < 2 ^ 64 ->
  ~ (dst <= bv_unsigned x < dst + 4 * Z.of_nat (length ws)) -> art_w4s M dst ws x = M x.
Proof.
  induction ws as [|w ws IH]; intros M dst x Hd Hd' N; cbn [art_w4s]. reflexivity.
  cbn [length] in Hd', N. rewrite IH; [|lia|lia|lia]. rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia].
Qed.
Lemma cell_w4s_other : forall ws M dst b m u, 0 <= dst -> dst + 4 * Z.of_nat (length ws) < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 ->
  apart dst (4 * Z.of_nat (length ws)) b (Z.of_nat m) -> cellA M b m u -> cellA (art_w4s M dst ws) b m u.
Proof.
  induction ws as [|w ws IH]; intros M dst b m u Hd Hd' Hb Hm A C; cbn [art_w4s]. exact C.
  cbn [length] in Hd', A. unfold apart in A. apply IH; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|exact C].
Qed.

Lemma cell_w4s_nth : forall ws M dst i, 0 <= dst -> dst + 4 * Z.of_nat (length ws) < 2 ^ 64 -> (i < length ws)%nat ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 32) ->
  cellA (art_w4s M dst ws) (dst + 4 * Z.of_nat i) 4 (nth i ws 0).
Proof.
  induction ws as [|w ws IH]; intros M dst i Hd Hd' Hi Hws; cbn [length] in *. lia.
  destruct i as [|i].
  - cbn [nth art_w4s]. replace (dst + 4 * Z.of_nat 0) with dst by lia.
    apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia.
  - cbn [nth art_w4s]. replace (dst + 4 * Z.of_nat (S i)) with (dst + 4 + 4 * Z.of_nat i) by lia.
    apply IH; [lia|lia|lia|]. intros j Hj. apply (Hws (S j)). lia.
Qed.

Section FPX2. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_gfa_copy : forall ws regs (M rom : word -> option byte) (dst src dend : Z),
  getr regs 13 = Z_to_bv 64 dst -> getr regs 20 = Z_to_bv 64 src -> getr regs 11 = Z_to_bv 64 dend ->
  dend = dst + 4 * Z.of_nat (length ws) -> (1 <= length ws)%nat ->
  0 <= dst -> dend < 2 ^ 64 -> 0 <= src -> src + 4 * Z.of_nat (length ws) < 2 ^ 64 -> 4096 <= dst ->
  apart dst (4 * Z.of_nat (length ws)) src (4 * Z.of_nat (length ws)) ->
  wrA M dst (4 * Z.of_nat (length ws)) ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (src + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x57ee8 : word) M rom) (mkst regs' (0x57efc : word) (art_w4s M dst ws) rom)
    /\ getr regs' 13 = Z_to_bv 64 dend /\ getr regs' 20 = Z_to_bv 64 (src + 4 * Z.of_nat (length ws))
    /\ (forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 20%bv -> getr regs' r = getr regs r).
Proof.
  induction ws as [|w ws IH]; intros regs M rom dst src dend H13 H20 H11 Edend Hlen Hd Hd' Hs Hs' IMG A W Cws; cbn [length] in *. lia.
  destruct (Cws O ltac:(lia)) as [Rw Cw]. cbn [nth] in Rw, Cw. replace (src + 4 * Z.of_nat 0) with src in Cw by lia.
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x57ee8 : word) M rom) (mkst regs1 (0x57ef8 : word) (Wn 4 M dst w) rom)
            /\ getr regs1 13 = Z_to_bv 64 (dst + 4) /\ getr regs1 20 = Z_to_bv 64 (src + 4) /\ getr regs1 11 = Z_to_bv 64 dend
            /\ (forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 20%bv -> getr regs1 r = getr regs r)).
  { eexists. split.
    - zlw F_57e98 D_57e98 src Cw.
      zsw F_57e9c D_57e9c dst w ltac:(rewok W).
      zstep F_57ea0 D_57ea0. zstep F_57ea4 D_57ea4. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P13 & P20 & P11 & K1).
  destruct ws as [|w2 ws2].
  -
    cbn [length] in *. eexists. split; [|split; [|split]].
    + eapply msteps_trans; [exact RUN1|]. cbn [art_w4s]. zbft F_57ea8 D_57ea8. replace (dst + 4) with dend by lia. apply mst_refl.
    + gres. rewrite P13. f_equal; lia.
    + gres. rewrite P20. f_equal; lia.
    + intros r N12 N13 N20. gres. apply K1; assumption.
  - cbn [length] in *.
    assert (RUNb : msteps ASEGS (mkst regs1 (0x57ef8 : word) (Wn 4 M dst w) rom) (mkst regs1 (0x57ee8 : word) (Wn 4 M dst w) rom)).
    { zbtk F_57ea8 D_57ea8. apply mst_refl. }
    unfold apart in A.
    destruct (IH regs1 (Wn 4 M dst w) rom (dst + 4) (src + 4) dend P13 P20 P11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold apart; lia) ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])
                 ltac:(intros j Hj; destruct (Cws (S j) ltac:(lia)) as [R C]; split; [exact R|];
                       replace (src + 4 + 4 * Z.of_nat j) with (src + 4 * Z.of_nat (S j)) by lia; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|exact C]))
      as (regs' & RUN2 & Q13 & Q20 & K2).
    exists regs'. split; [|split; [|split]].
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_w4s]. exact RUN2.
    + exact Q13.
    + rewrite Q20. f_equal. lia.
    + intros r N12 N13 N20. rewrite K2 by assumption. apply K1; assumption.
Qed.
End FPX2.

Section FPX3. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_gfa_mid_fn : forall regs (M rom : word -> option byte) (r fa chp n nf : Z),
  getr regs 8 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 fa -> getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 4 * nf < 2 ^ 64 -> 0 <= chp -> chp + 4 * n < 2 ^ 64 -> 1 <= n <= nf -> nf < 2 ^ 40 ->
  wrA M r 128 -> cellA M (r + 16) 8 nf ->
  msteps ASEGS (mkst regs (0x57ec4 : word) M rom)
    (mkst (regupd (regupd (regupd regs 11 (Z_to_bv 64 (chp + n * 2 ^ 2))) 15 (Z_to_bv 64 ((nf - n) * 2 ^ 2))) 20 (Z_to_bv 64 (fa + (nf - n) * 2 ^ 2))) (0x57ee8 : word) (Wn 8 M (r + 16) (nf - n)) rom).
Proof.
  intros regs M rom r fa chp n nf H8 H20 H13 H14 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Wr Cnf.
  zld F_57e74 D_57e74 (r + 16) Cnf.
  zbft F_57e78 D_57e78.
  zstep F_57e7c D_57e7c.
  zsd F_57e80 D_57e80 (r + 16) (nf - n) ltac:(rewok Wr).
  zbft F_57e84 D_57e84.
  zstep F_57e88 D_57e88. zstep F_57e8c D_57e8c. zstep F_57e90 D_57e90. zstep F_57e94 D_57e94.
  zret.
Qed.

#[using="Type"] Lemma art_gfa_tail_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r n na ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 14 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (2 ^ 61) ->
  128 <= sp -> sp < 2 ^ 64 -> 0x698000 + 128 <= sp -> r = ris + 128 * c -> ris = 128 * qris -> 0 <= ris -> 1 <= c <= 31 -> r + 128 < 2 ^ 64 -> apart r 128 (sp - 128) 128 ->
  0 <= n -> 0 <= na < 2 ^ 64 -> ret_ok raw ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 -> 0 <= g23 < 2 ^ 64 ->
  0 <= g24 < 2 ^ 64 -> 0 <= g25 < 2 ^ 64 -> 0 <= g26 < 2 ^ 64 -> 0 <= g27 < 2 ^ 64 ->
  wrA M r 128 -> cellA M (r + 72) 8 na -> cellA M r 8 (2 ^ 60) -> cellA M 0x10428 8 0xafffff00000fffff ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 -> cellA M (sp - 80) 8 g24 -> cellA M (sp - 88) 8 g25 -> cellA M (sp - 96) 8 g26 -> cellA M (sp - 104) 8 g27 ->
  msteps ASEGS (mkst regs (0x57efc : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (2 ^ 62))) 6 (Z_to_bv 64 0)) 7 (Z_to_bv 64 (2 ^ 60))) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 (2 ^ 60))) 13 (Z_to_bv 64 6917529027641081856)) 14 (Z_to_bv 64 12682135451164737535)) 15 (Z_to_bv 64 17293822569102704639)) 16 (Z_to_bv 64 1152920405095219200)) 17 (Z_to_bv 64 18446742974197923840)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20)) 21 (Z_to_bv 64 g21)) 22 (Z_to_bv 64 g22)) 23 (Z_to_bv 64 g23)) 24 (Z_to_bv 64 g24)) 25 (Z_to_bv 64 g25)) 26 (Z_to_bv 64 g26)) 27 (Z_to_bv 64 g27)) 28 (Z_to_bv 64 0)) raw (Wn 8 (Wn 8 M (r + 72) (na + n)) r 0) rom).
Proof.
  intros regs M rom raw sp r n na ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 H2 H8 H14 H19 Hsp Hsp' IMG Er Eris Hris Hc Hr' Ar Hn Hna Hret
         Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24 Hg25 Hg26 Hg27 Wr Cna Cst Crd F8 F16 F24 F32 F40 F48 F56 F64 F72 F80 F88 F96 F104.
  assert (Hr8 : r mod 8 = 0). { rewrite Er, Eris. replace (128 * qris + 128 * c) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
  zld F_57eac D_57eac (r + 72) Cna.
  zstep F_57eb0 D_57eb0.
  zsd F_57eb4 D_57eb4 (r + 72) (na + n) ltac:(rewok Wr).
  zstep F_57eb8 D_57eb8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cst' : cellA X r 8 (2 ^ 60)) by zcell; assert (Crd' : cellA X 0x10428 8 0xafffff00000fffff) by zcell;
                                                   assert (Wst : wok Asan.M.loaded_segments X r 8) by (rewok Wr) end.
  zld F_57ebc D_57ebc r Cst'.
  zstep F_57ec0 D_57ec0. zstep F_57ec4 D_57ec4.
  stepn F_57ec8 D_57ec8. zstep F_57ecc D_57ecc.
  stepn F_57ed0 D_57ed0. stepn F_57ed4 D_57ed4. stepn F_57ed8 D_57ed8.
  zld F_57edc D_57edc 0x10428 Crd'.
  stepn F_57ee0 D_57ee0. stepn F_57ee4 D_57ee4. stepn F_57ee8 D_57ee8. zstep F_57eec D_57eec. stepn F_57ef0 D_57ef0.
  stepn F_57ef4 D_57ef4.
  stepn F_57f10 D_57f10. stepn F_57f14 D_57f14.
  zbft F_57f18 D_57f18.
  stepn F_57f1c D_57f1c.
  zbtk F_57f20 D_57f20.
  stepn F_57f44 D_57f44. rwH. vnorm. stepn F_57f48 D_57f48. stepn F_57f4c D_57f4c. stepn F_57f50 D_57f50. stepn F_57f54 D_57f54. stepn F_57f58 D_57f58. stepn F_57f5c D_57f5c.
  zbtk F_57f60 D_57f60.

  chain_step; [reflexivity
    | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r) _ (Z_to_bv 64 (2 ^ 60)));
      [exact F_57ef8 | reflexivity | exact D_57ef8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
      | exact Cst' | apply bytes_le_to_Z_8 ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_57efc | reflexivity | exact D_57efc | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite ?art_u_lit by lia; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.
  chain_step; [reflexivity
    | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r));
      [exact F_57f00 | reflexivity | exact D_57f00 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wst ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 r) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 r 0).
  zbft F_57f04 D_57f04.
  zbtk F_57f08 D_57f08.
  zbtk F_57f70 D_57f70.
  zstep F_57f84 D_57f84.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E8 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (E16 : cellA X (sp - 16) 8 g8) by zcell; assert (E24 : cellA X (sp - 24) 8 g9) by zcell;
    assert (E32 : cellA X (sp - 32) 8 g18) by zcell; assert (E40 : cellA X (sp - 40) 8 g19) by zcell; assert (E48 : cellA X (sp - 48) 8 g20) by zcell;
    assert (E56 : cellA X (sp - 56) 8 g21) by zcell; assert (E64 : cellA X (sp - 64) 8 g22) by zcell; assert (E72 : cellA X (sp - 72) 8 g23) by zcell;
    assert (E80 : cellA X (sp - 80) 8 g24) by zcell; assert (E88 : cellA X (sp - 88) 8 g25) by zcell; assert (E96 : cellA X (sp - 96) 8 g26) by zcell;
    assert (E104 : cellA X (sp - 104) 8 g27) by zcell end.
  zld F_57f88 D_57f88 (sp - 8) E8. rewrite Z_to_bv_bv_unsigned.
  zld F_57f8c D_57f8c (sp - 16) E16. zld F_57f90 D_57f90 (sp - 24) E24. zld F_57f94 D_57f94 (sp - 32) E32. zld F_57f98 D_57f98 (sp - 40) E40.
  zld F_57f9c D_57f9c (sp - 48) E48. zld F_57fa0 D_57fa0 (sp - 56) E56. zld F_57fa4 D_57fa4 (sp - 64) E64. zld F_57fa8 D_57fa8 (sp - 72) E72.
  zld F_57fac D_57fac (sp - 80) E80. zld F_57fb0 D_57fb0 (sp - 88) E88. zld F_57fb4 D_57fb4 (sp - 96) E96. zld F_57fb8 D_57fb8 (sp - 104) E104.
  zstep F_57fbc D_57fbc.
  stepret F_57fc0 D_57fc0 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX3.
