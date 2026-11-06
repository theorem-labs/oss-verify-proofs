(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow ACheck ASaves.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BCode2 BRt BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_pv stops := wp_go 0x2737d0 40%nat C_put_value_eq C_put_value stops.

Definition KS_pv : list nat := [10; 11; 12; 13; 14; 15; 16; 17]%nat.
Definition FR_pv (spv d : Z) (x : word) : Prop := inr x (spv - 16) 16 \/ inr x d 1.

Theorem put_value1_cps : forall rom Post M d spv (val : word) l,
  rt_ok M -> B_IMG_END <= d -> memrange d 1 -> addr_ok M d 1 -> wr_ok BSEGS M d 1 ->
  B_IMG_END <= spv - 16 /\ spv < 2 ^ 63 /\ (spv <= SB \/ HIMEM_BEG <= spv - 16) /\ (d + 1 <= spv - 16 \/ spv <= d) ->
  wr_ok BSEGS M (spv - 16) 16 ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W d -> rget l 11 = val -> rget l 12 = W 1 ->
  (forall l' M', length l' = 32%nat -> same_except KS_pv l l' ->
     unch M M' (FR_pv spv d) -> mem_grows M M' ->
     reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (W 0x2737d0) l M Post.
Proof.
  intros rom Post M d spv val l Hrt Hd Hm Hok Hwd (Hs1 & Hs2 & Hs3 & Hs4) Hfr Hl H2 H10 H11 H12 K.
  destruct Hrt as (G1 & G2 & _). destruct Hm as [_ Hm].
  unfold G_SB, C_SB, B_IMG_END, LOMEM_END, HIMEM_BEG, HIMEM_END in *.
  regs_open l Hl. subst sp a0 a2.
  wp_pv [0x273858; 0x27386c; 0x273850; 0x273814]. mem_auto.
  name_mem M1.
  assert (HU1 : unch M M1 (FR_pv spv d)) by (unname_mems; solve_unch ltac:(unfold FR_pv, inr in *; lia)).
  assert (HG1 : mem_grows M M1) by (unname_mems; solve_grows).
  assert (Cra : cell BSEGS M1 (spv + -16 + 8) 8 ra) by (unname_mems; solve_cell).
  assert (Cs0 : cell BSEGS M1 (spv + -16) 8 s0) by (unname_mems; solve_cell).
  assert (G1' : cell BSEGS M1 6164312 8 (Z_to_bv 64 6961784)) by (unname_mems; solve_cell).
  assert (G2' : cell BSEGS M1 6961784 8 (Z_to_bv 64 SB)) by (unname_mems; solve_cell).
  assert (Hok1 : addr_ok M1 d 1).
  { eapply addr_ok_unch; [exact HU1 | lia | unfold HIMEM_END; lia | | exact Hok].
    intros y Hy. unfold FR_pv, inr, SB, HIMEM_BEG in *. lia. }
  assert (Hwd1 : wr_ok BSEGS M1 d 1) by (eapply wr_ok_grows; [exact HG1 | exact Hwd]).
  clearbody M1.
  rewrite (Wu d) by lia. split; intros Hb; [exfalso; lia|]. clear Hb.
  rewrite (u_not_W d) by lia. replace (1 + -1) with 0 by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. split; intros Hb; [exfalso; lia|]. clear Hb.
  mem_auto. rewrite ?add_W, ?addi_W, ?sub_W.
  replace (d + 0) with d by lia. replace (1 + d + -1) with d by lia.
  destruct (sh_load_k BSEGS M1 d 1 Hok1 ltac:(lia) ltac:(lia) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
  pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as Hm8.
  wp_pv [0x273814; 0x27386c; 0x27384c]. rewrite sha_addr_r by lia.
  exists (W u). split; [exact Hu|]. rewrite lb_small by lia. rewrite ?andi7_W by lia.
  rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  rewrite ?addi_W. replace (0 - 1 + 1) with 0 by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  split; [intros Hnz; split; [intros _ | intros Hbad; exfalso; lia] | intros _];
  (split; [eapply wr_ok_store; [exact Hwd1 | lia | cbn; lia]|];
   split; [intros Hb; exfalso; lia|]; intros _;
   split; [intros Hb; exfalso; apply Hb; reflexivity|]; intros _;
   mem_auto; replace (spv + -16 + 16) with spv by lia;
   match goal with |- reach _ _ (v_jalr ?r 0) ?l' _ _ =>
     replace (v_jalr r 0) with (v_jalr (rget [x0; ra; Z_to_bv 64 spv; gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 d; a1; Z_to_bv 64 1; a3; a4;
        a5; a6; a7; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] 1) 0) by reflexivity end;
   apply K; [reflexivity | same_ex
            | eapply unch_trans; [exact HU1|]; apply unch_store; [apply unch_refl | lia | cbn; lia | intros x Hx; cbn in Hx; right; exact Hx]
            | eapply mem_grows_trans; [exact HG1 | apply wbytes_grows]]).
Qed.

Print Assumptions put_value1_cps.
