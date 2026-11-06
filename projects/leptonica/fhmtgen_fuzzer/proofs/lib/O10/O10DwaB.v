(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import CatSim StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 GrayLib DwaLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10_code_fhI.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DWA.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables w h wpls wpld PW datas datad sp : Z.
  Variables gpv tpv : word.
  Hypothesis Hw : (1 <= w < 2 ^ 30)%Z.
  Hypothesis Hh : (1 <= h < 2 ^ 30)%Z.
  Hypothesis Hwpls : (1 <= wpls < 2 ^ 26)%Z.
  Hypothesis Hwpld : (1 <= wpld < 2 ^ 26)%Z.
  Hypothesis HPW : ((w + 31) / 2 ^ 5 = PW)%Z.
  Hypothesis Hsz : ((wpls * h) < 2 ^ 28 /\ (wpld * h) < 2 ^ 28)%Z.
  Hypothesis Hsp : (4096 <= sp /\ sp + 160 <= 2 ^ 63)%Z.
  (* [comment removed for export] *)
  #[local] Abbreviation SLO := (datas - 24 * wpls - 4)%Z (only parsing).
  #[local] Abbreviation SHI := (datas + 4 * (wpls * h) + 20 * wpls + 4 * PW + 8)%Z (only parsing).
  #[local] Abbreviation DN := (4 * (wpld * h) - 4 * wpld + 4 * PW)%Z (only parsing).
  Hypothesis Hds : (4096 <= SLO /\ SHI <= 2 ^ 62)%Z.
  Hypothesis Hdd : (4096 <= datad /\ datad + DN <= 2 ^ 62)%Z.
  Hypothesis SOKs : store_ok SEGS M (Z_to_bv 64 SLO) (Z.to_nat (SHI - SLO)) = true.
  Hypothesis SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat DN) = true.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 sp) 56 = true.
  Hypothesis FR : disj_apart datad DN sp 160.

  Lemma HPW1 : (1 <= PW)%Z.
  Proof. rewrite <- HPW. change (2 ^ 5)%Z with 32%Z. apply Z.div_le_lower_bound; lia. Qed.
  Lemma HPW2 : (32 * PW <= w + 31)%Z.
  Proof. rewrite <- HPW. change (2 ^ 5)%Z with 32%Z. apply Z.mul_div_le. lia. Qed.
  Lemma wi_bound : forall i, (0 <= i < h)%Z -> (0 <= (wpls * i) /\ (wpls * i) <= (wpls * h) - wpls /\ 0 <= (wpld * i) /\ (wpld * i) <= (wpld * h) - wpld)%Z.
  Proof. intros i Hi. nia. Qed.

  Lemma wr_readable_o10 : wr_readable SEGS.
  Proof.
    intros seg Hin Hwr. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  #[local] Abbreviation MInv := (dwa_MInv M datad DN sp 56) (only parsing).
  #[local] Abbreviation cell := (dwa_cell SEGS sp) (only parsing).
  (* [comment removed for export] *)
  #[local] Abbreviation DWA_EN := (fun (regs : bvmap 5 word) (Mi : word -> option byte) =>
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 wpls) /\ cell Mi 32 (Z_to_bv 64 h) /\ cell Mi 40 (Z_to_bv 64 datad) /\ cell Mi 48 (Z_to_bv 64 wpld) /\
    getr regs 2 = Z_to_bv 64 sp /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\
    getr regs 10 = Z_to_bv 64 datad /\ getr regs 11 = Z_to_bv 64 w /\ getr regs 12 = Z_to_bv 64 h /\ getr regs 13 = Z_to_bv 64 wpld /\
    getr regs 14 = Z_to_bv 64 datas /\ getr regs 15 = Z_to_bv 64 wpls) (only parsing).
  #[local] Abbreviation DWA_EX := (dwa_EX M datad DN sp 56 gpv tpv) (only parsing).
  Lemma MInv_M : MInv M.
  Proof. unfold dwa_MInv. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
  Lemma MInv_store : forall Mi (a : Z) (bs : list byte),
    MInv Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + DN)%Z -> MInv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    unfold dwa_MInv. intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx Hy. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI; assumption.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.
  Lemma MInv_spill : forall Mi (off : Z) (bs : list byte),
    MInv Mi -> (0 <= off)%Z -> (off + Z.of_nat (length bs) <= 56)%Z -> MInv (wbytes Mi (Z_to_bv 64 (sp + off)) bs).
  Proof.
    unfold dwa_MInv. intros Mi off bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx Hy. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI; assumption.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.
  Lemma sok_in : forall Mi base (a N : Z) (n : nat),
    mem_grows M Mi -> store_ok SEGS M (Z_to_bv 64 base) (Z.to_nat N) = true -> (0 <= base /\ base + N <= 2 ^ 64 /\ 0 <= N)%Z ->
    (base <= a)%Z -> (a + Z.of_nat n <= base + N)%Z -> store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi base a N n HG SOK Hb Ha Hn. eapply store_ok_mono; [exact HG|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 base) _ (Z.to_nat N)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma rd_src4 : forall Mi (a : Z), mem_grows M Mi -> (SLO <= a)%Z -> (a + 4 <= SHI)%Z ->
    exists (bs : list byte) (v : word), rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.
  Proof.
    intros Mi a HG Ha H1.
    destruct (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) wr_readable_o10) as (bs & Hbs & Lbs).
    { apply (sok_in Mi SLO a (SHI - SLO) 4 HG SOKs); [pose proof HPW1; nia | lia | cbn; lia]. }
    destruct (bytes4_word bs Lbs) as (v & Hv). exists bs, v. split; [exact Hbs | exact Hv].
  Qed.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  (* [comment removed for export] *)
  Ltac kdestruct HF :=
    let HIv := fresh "HIv" in destruct HF as (HIv & HF);
    repeat (lazymatch type of HF with _ /\ _ => let HKx := fresh "HK" in destruct HF as (HKx & HF) end);
    unfold dwa_MInv in HIv;
    pose proof (proj2 HIv) as HIvG; pose proof HPW1 as HPW1'; pose proof HPW2 as HPW2'; pose proof FR as FR'; unfold disj_apart in FR'.
  Ltac ibound H := let X := fresh "HWi" in pose proof (wi_bound _ H) as X.
  Ltac ibound1 H0 H1 := lazymatch type of H0 with (0 <= ?ii)%Z => let Y := fresh "HIi" in assert (Y : (0 <= ii < h)%Z) by lia; let X := fresh "HWi" in pose proof (wi_bound ii Y) as X end.
  Lemma rdn_hit8_eq : forall m (a v v' : word), (bv_unsigned a + 8 <= 2 ^ 64)%Z -> v = v' ->
    rdn SEGS (wbytes m a (word_to_le_bytes 8 v')) a 8 = Some (word_to_le_bytes 8 v).
  Proof. intros m a v v' Ha ->. apply rdn_wbytes_hit8. exact Ha. Qed.
  Ltac celln :=
    lazymatch goal with
    | |- rdn _ (wbytes _ ?a _) ?b 8 = _ => tryif constr_eq a b then (apply rdn_hit8_eq; [unorm; lia | first [reflexivity | f_equal; lia]]) else (rewrite rdn_wbytes_out_Z by (zlen; lia); celln)
    | |- rdn _ ?mm (Z_to_bv 64 (sp + ?o)) 8 = Some _ => match goal with H : dwa_cell _ _ mm o _ |- _ => exact H end
    end.
  Ltac cellk := unfold dwa_cell; celln.
  Ltac minv := repeat first [ apply MInv_store; [| lia | zlen; lia] | apply MInv_spill; [| lia | zlen; lia] ]; unfold dwa_MInv; assumption.
  Ltac kfact := gres; pin; first [ reflexivity | f_equal; lia ].
  Ltac kpost1 := lazymatch goal with |- dwa_cell _ _ _ _ _ => cellk | |- getr _ _ = _ => kfact end.
  Ltac kpost := split; [ minv | repeat split; kpost1 ].
  (* [comment removed for export] *)
  Ltac stf F D off v :=
    stepST F D (Z_to_bv 64 (sp + off)) v
      ltac:(store_ok_peel; eapply store_ok_mono; [ grows | lazymatch goal with HG : mem_grows M ?mi |- _ => apply (sok_in mi sp (sp + off) 56 8 HG SOKf) end; [lia | lia | cbn; lia] ]).
  Ltac ldf F D off v := stepLD F D (word_to_le_bytes 8 v) v ltac:(rdn_addr (sp + off)%Z; cellk) ltac:(apply bytes_le_to_Z_8).
  (* [comment removed for export] *)
  Ltac gsw F D aa :=
    chain_step;
    [ reflexivity
    | eapply step_sw_at with (a := Z_to_bv 64 aa);
      [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
      | store_ok_peel; eapply store_ok_mono; [ grows | lazymatch goal with HG : mem_grows M ?mi |- _ => apply (sok_in mi datad aa DN 4 HG SOKd) end; [lia | lia | cbn; lia] ] ]
    | step_simpl ].
  (* [comment removed for export] *)
  Ltac zvw F D v := sn F D; fixv v ltac:(rewrite ?v_addiw_Z, ?sw32_small by lia; first [reflexivity | f_equal; lia]).
  Ltac zvpw F D := sn F D; fixv (Z_to_bv 64 PW) ltac:(rewrite zbv_srliw_small by lia; rewrite HPW; reflexivity).
  Ltac zvsl F D v k := sn F D; fixv v ltac:(rewrite zbv_slli by lia; f_equal; lia).
  Ltac zvsl32 F D v := sn F D; fixv v ltac:(rewrite zbv_slli by lia; reflexivity).
  Ltac zvsr30 F D v := sn F D; fixv v ltac:(rewrite slli32_srli30 by lia; f_equal; lia).
  Ltac zvslw F D v k := sn F D; fixv v ltac:(rewrite v_slliw_Z, sw32_small by lia; f_equal; lia).
  Ltac zvsubw F D v := sn F D; fixv v ltac:(rewrite v_subw_Z, sw32_small by lia; f_equal; lia).
  Ltac zvaddw F D v := sn F D; fixv v ltac:(rewrite v_addw_Z, sw32_small by lia; f_equal; lia).
  Ltac zvmulw F D v := sn F D; fixv v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).

  (* [comment removed for export] *)
  Definition k5_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)).
  Definition k5_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 18 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Definition k5_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 9 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 18 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).
  Definition k5_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)).

  Lemma k5_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21de4 : word) Mi rom) (mkst regs' (0x21e60 : word) M' rom) /\ k5_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_21ce8 D_21ce8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21cec D_21cec.   (* [comment removed for export] *)
      zvw F_21cf0 D_21cf0 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_21cf4 D_21cf4 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_21cf8 D_21cf8 (Z_to_bv 64 (8 * wpls)) 8%Z.   (* [comment removed for export] *)
      zvslw F_21cfc D_21cfc (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_21d00 D_21d00 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_21d04 D_21d04 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvsl F_21d08 D_21d08 (Z_to_bv 64 (4 * wpld)) 4%Z.   (* [comment removed for export] *)
      zvpw F_21d0c D_21d0c.   (* [comment removed for export] *)
      zvsubw F_21d10 D_21d10 (Z_to_bv 64 (6 * wpls)).   (* [comment removed for export] *)
      zvsl F_21d14 D_21d14 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zvsl F_21d18 D_21d18 (Z_to_bv 64 (24 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21d1c D_21d1c (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_21d20 D_21d20 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_21d24 D_21d24 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zv F_21d28 D_21d28 (Z_to_bv 64 (datas + 24 * wpls)).   (* [comment removed for export] *)
      zv F_21d2c D_21d2c (Z_to_bv 64 (datas - 24 * wpls)).   (* [comment removed for export] *)
      zv F_21d30 D_21d30 (Z_to_bv 64 (datas - 8 * wpls + 4)).   (* [comment removed for export] *)
      zvsl32 F_21d34 D_21d34 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zv F_21d38 D_21d38 (Z_to_bv 64 (datas - 24 * wpls + 4)).   (* [comment removed for export] *)
      zvsr30 F_21d3c D_21d3c (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21d40 D_21d40 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21d44 D_21d44.   (* [comment removed for export] *)
      sn F_21d48 D_21d48.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RH. kpost.
  Qed.

  Lemma k5_rowset : forall regs Mi i, (0 <= i < h)%Z -> k5_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21e60 : word) Mi rom) (mkst regs' (0x21e94 : word) M' rom) /\ k5_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k5_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21d64 D_21d64 ltac:(condZ).   (* [comment removed for export] *)
      zv F_21d68 D_21d68 (Z_to_bv 64 (4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_21d6c D_21d6c 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21d70 D_21d70 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zv F_21d74 D_21d74 (Z_to_bv 64 (4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zvsl F_21d78 D_21d78 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_21d7c D_21d7c 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21d80 D_21d80 (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21d84 D_21d84 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21d88 D_21d88 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21d8c D_21d8c (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d90 D_21d90 (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d94 D_21d94 (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_IN. kpost.
  Qed.

  Definition k5_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 18 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k5_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21e94 : word) Mi rom) (mkst regs' (0x21ecc : word) M' rom) /\ k5_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    eexists. eexists. split.
    -
      stepLD F_21d98 D_21d98 bs0 v0 ltac:(rdn_addr (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21d9c D_21d9c bs1 v1 ltac:(rdn_addr (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21da0 D_21da0 bs2 v2 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_21da4 D_21da4 bs3 v3 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21da8 D_21da8 bs4 v4 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21dac D_21dac bs5 v5 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_21db0 D_21db0 bs6 v6 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      zv F_21db4 D_21db4 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_21db8 D_21db8.   (* [comment removed for export] *)
      sn F_21dbc D_21dbc.   (* [comment removed for export] *)
      sn F_21dc0 D_21dc0.   (* [comment removed for export] *)
      sn F_21dc4 D_21dc4.   (* [comment removed for export] *)
      sn F_21dc8 D_21dc8.   (* [comment removed for export] *)
      sn F_21dcc D_21dcc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_C1. kpost.
  Qed.

  Definition k5_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 18 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k5_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21ecc : word) Mi rom) (mkst regs' (0x21f04 : word) M' rom) /\ k5_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_C1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 24 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    eexists. eexists. split.
    -
      sn F_21dd0 D_21dd0.   (* [comment removed for export] *)
      sn F_21dd4 D_21dd4.   (* [comment removed for export] *)
      sn F_21dd8 D_21dd8.   (* [comment removed for export] *)
      sn F_21ddc D_21ddc.   (* [comment removed for export] *)
      sn F_21de0 D_21de0.   (* [comment removed for export] *)
      sn F_21de4 D_21de4.   (* [comment removed for export] *)
      sn F_21de8 D_21de8.   (* [comment removed for export] *)
      sn F_21dec D_21dec.   (* [comment removed for export] *)
      stepLD F_21df0 D_21df0 bs0 v0 ltac:(rdn_addr (datas + 24 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21df4 D_21df4 bs1 v1 ltac:(rdn_addr (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      zv F_21df8 D_21df8 (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_21dfc D_21dfc.   (* [comment removed for export] *)
      sn F_21e00 D_21e00.   (* [comment removed for export] *)
      sn F_21e04 D_21e04.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_C2. kpost.
  Qed.

  Definition k5_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 18 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k5_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21f04 : word) Mi rom) (mkst regs' (0x21f3c : word) M' rom) /\ k5_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_C2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21e08 D_21e08.   (* [comment removed for export] *)
      sn F_21e0c D_21e0c.   (* [comment removed for export] *)
      sn F_21e10 D_21e10.   (* [comment removed for export] *)
      sn F_21e14 D_21e14.   (* [comment removed for export] *)
      sn F_21e18 D_21e18.   (* [comment removed for export] *)
      sn F_21e1c D_21e1c.   (* [comment removed for export] *)
      sn F_21e20 D_21e20.   (* [comment removed for export] *)
      sn F_21e24 D_21e24.   (* [comment removed for export] *)
      sn F_21e28 D_21e28.   (* [comment removed for export] *)
      sn F_21e2c D_21e2c.   (* [comment removed for export] *)
      sn F_21e30 D_21e30.   (* [comment removed for export] *)
      sn F_21e34 D_21e34.   (* [comment removed for export] *)
      sn F_21e38 D_21e38.   (* [comment removed for export] *)
      sn F_21e3c D_21e3c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_C3. kpost.
  Qed.

  Lemma k5_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21f3c : word) Mi rom) (mkst regs' (0x21f50 : word) M' rom) /\ k5_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21e40 D_21e40.   (* [comment removed for export] *)
      gsw F_21e44 D_21e44 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_21e48 D_21e48 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21e4c D_21e4c (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      zv F_21e50 D_21e50 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_BN. kpost.
  Qed.

  Lemma k5_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21e94 : word) Mi rom) (mkst regs' (0x21f50 : word) M' rom) /\ k5_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k5_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k5_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k5_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k5_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Lemma k5_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k5_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21f50 : word) Mi rom) (mkst regs' (0x21e94 : word) M' rom) /\ k5_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k5_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_21e54 D_21e54 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_IN. kpost.
  Qed.

  Lemma k5_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k5_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21f50 : word) Mi rom) (mkst regs' (0x21e48 : word) M' rom) /\ k5_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k5_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21e54 D_21e54 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21e58 D_21e58.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RL. kpost.
  Qed.

  Lemma k5_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k5_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21e48 : word) Mi rom) (mkst regs' (0x21e60 : word) M' rom) /\ k5_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k5_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21d4c D_21d4c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21d50 D_21d50 (Z_to_bv 64 (datas + 28 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21d54 D_21d54 (Z_to_bv 64 (datas - 20 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d58 D_21d58 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d5c D_21d5c (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_21d60 D_21d60 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RH. kpost.
  Qed.

  Lemma k5_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k5_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21e48 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k5_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21d4c D_21d4c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21d50 D_21d50 (Z_to_bv 64 (datas + 28 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21d54 D_21d54 (Z_to_bv 64 (datas - 20 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d58 D_21d58 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21d5c D_21d5c (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_21d60 D_21d60 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k5_inner : forall regs Mi i, (0 <= i < h)%Z -> k5_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21e94 : word) Mi rom) (mkst regs' (0x21e48 : word) M' rom) /\ k5_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21e94 : word) (0x21e48 : word) (fun r m j => k5_IN r m i j) (fun r m => k5_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k5_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k5_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k5_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k5_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21de4 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k5_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21e60 : word) (0x22300 : word) (fun r m i => k5_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k5_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k5_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k5_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k5_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k6_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).
  Definition k6_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Definition k6_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).
  Definition k6_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).

  Lemma k6_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21f58 : word) Mi rom) (mkst regs' (0x21fcc : word) M' rom) /\ k6_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_21e5c D_21e5c ltac:(condZ).   (* [comment removed for export] *)
      sn F_21e60 D_21e60.   (* [comment removed for export] *)
      zvw F_21e64 D_21e64 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_21e68 D_21e68 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvslw F_21e6c D_21e6c (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_21e70 D_21e70 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21e74 D_21e74 (Z_to_bv 64 (datas + 4)).   (* [comment removed for export] *)
      ldf F_21e78 D_21e78 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvsl F_21e7c D_21e7c (Z_to_bv 64 (4 * wpld)) 4%Z.   (* [comment removed for export] *)
      stf F_21e80 D_21e80 16%Z (Z_to_bv 64 (4 * wpld)).   (* [comment removed for export] *)
      stf F_21e84 D_21e84 24%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_21e88 D_21e88.   (* [comment removed for export] *)
      zv F_21e8c D_21e8c (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvsl F_21e90 D_21e90 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21e94 D_21e94 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_21e98 D_21e98 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_21e9c D_21e9c (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21ea0 D_21ea0 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21ea4 D_21ea4 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21ea8 D_21ea8 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      stf F_21eac D_21eac 8%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21eb0 D_21eb0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RH. kpost.
  Qed.

  Lemma k6_rowset : forall regs Mi i, (0 <= i < h)%Z -> k6_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21fcc : word) Mi rom) (mkst regs' (0x22010 : word) M' rom) /\ k6_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k6_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_21ed0 D_21ed0 24%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_21ed4 D_21ed4.   (* [comment removed for export] *)
      stepb_ft F_21ed8 D_21ed8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_21edc D_21edc 16%Z (Z_to_bv 64 (4 * wpld)).   (* [comment removed for export] *)
      zv F_21ee0 D_21ee0 (Z_to_bv 64 (4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_21ee4 D_21ee4 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21ee8 D_21ee8 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_21eec D_21eec 8%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      zv F_21ef0 D_21ef0 (Z_to_bv 64 (4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zvsl F_21ef4 D_21ef4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_21ef8 D_21ef8 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21efc D_21efc (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21f00 D_21f00 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21f04 D_21f04 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21f08 D_21f08 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21f0c D_21f0c (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21f10 D_21f10 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_IN. kpost.
  Qed.

  Definition k6_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k6_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22010 : word) Mi rom) (mkst regs' (0x22048 : word) M' rom) /\ k6_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs8 & v8 & Hb8 & Hv8).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs9 & v9 & Hb9 & Hv9).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs10 & v10 & Hb10 & Hv10).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs11 & v11 & Hb11 & Hv11).
    eexists. eexists. split.
    -
      stepLD F_21f14 D_21f14 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21f18 D_21f18 bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21f1c D_21f1c bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_21f20 D_21f20 bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21f24 D_21f24 bs4 v4 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21f28 D_21f28 bs5 v5 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_21f2c D_21f2c bs6 v6 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_21f30 D_21f30 bs7 v7 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      stepLD F_21f34 D_21f34 bs8 v8 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb8) ltac:(exact Hv8).   (* [comment removed for export] *)
      stepLD F_21f38 D_21f38 bs9 v9 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb9) ltac:(exact Hv9).   (* [comment removed for export] *)
      stepLD F_21f3c D_21f3c bs10 v10 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb10) ltac:(exact Hv10).   (* [comment removed for export] *)
      stepLD F_21f40 D_21f40 bs11 v11 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb11) ltac:(exact Hv11).   (* [comment removed for export] *)
      sn F_21f44 D_21f44.   (* [comment removed for export] *)
      sn F_21f48 D_21f48.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_C1. kpost.
  Qed.

  Definition k6_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k6_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22048 : word) Mi rom) (mkst regs' (0x22080 : word) M' rom) /\ k6_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21f4c D_21f4c.   (* [comment removed for export] *)
      sn F_21f50 D_21f50.   (* [comment removed for export] *)
      sn F_21f54 D_21f54.   (* [comment removed for export] *)
      sn F_21f58 D_21f58.   (* [comment removed for export] *)
      sn F_21f5c D_21f5c.   (* [comment removed for export] *)
      sn F_21f60 D_21f60.   (* [comment removed for export] *)
      sn F_21f64 D_21f64.   (* [comment removed for export] *)
      sn F_21f68 D_21f68.   (* [comment removed for export] *)
      sn F_21f6c D_21f6c.   (* [comment removed for export] *)
      sn F_21f70 D_21f70.   (* [comment removed for export] *)
      sn F_21f74 D_21f74.   (* [comment removed for export] *)
      sn F_21f78 D_21f78.   (* [comment removed for export] *)
      sn F_21f7c D_21f7c.   (* [comment removed for export] *)
      sn F_21f80 D_21f80.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_C2. kpost.
  Qed.

  Definition k6_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k6_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22080 : word) Mi rom) (mkst regs' (0x220b8 : word) M' rom) /\ k6_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_C2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21f84 D_21f84.   (* [comment removed for export] *)
      sn F_21f88 D_21f88.   (* [comment removed for export] *)
      sn F_21f8c D_21f8c.   (* [comment removed for export] *)
      sn F_21f90 D_21f90.   (* [comment removed for export] *)
      sn F_21f94 D_21f94.   (* [comment removed for export] *)
      sn F_21f98 D_21f98.   (* [comment removed for export] *)
      sn F_21f9c D_21f9c.   (* [comment removed for export] *)
      sn F_21fa0 D_21fa0.   (* [comment removed for export] *)
      sn F_21fa4 D_21fa4.   (* [comment removed for export] *)
      sn F_21fa8 D_21fa8.   (* [comment removed for export] *)
      sn F_21fac D_21fac.   (* [comment removed for export] *)
      sn F_21fb0 D_21fb0.   (* [comment removed for export] *)
      sn F_21fb4 D_21fb4.   (* [comment removed for export] *)
      sn F_21fb8 D_21fb8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_C3. kpost.
  Qed.

  Definition k6_C4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (4 * PW)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k6_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x220b8 : word) Mi rom) (mkst regs' (0x220f0 : word) M' rom) /\ k6_C4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21fbc D_21fbc.   (* [comment removed for export] *)
      sn F_21fc0 D_21fc0.   (* [comment removed for export] *)
      zv F_21fc4 D_21fc4 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21fc8 D_21fc8 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21fcc D_21fcc (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_21fd0 D_21fd0.   (* [comment removed for export] *)
      sn F_21fd4 D_21fd4.   (* [comment removed for export] *)
      sn F_21fd8 D_21fd8.   (* [comment removed for export] *)
      sn F_21fdc D_21fdc.   (* [comment removed for export] *)
      sn F_21fe0 D_21fe0.   (* [comment removed for export] *)
      sn F_21fe4 D_21fe4.   (* [comment removed for export] *)
      sn F_21fe8 D_21fe8.   (* [comment removed for export] *)
      sn F_21fec D_21fec.   (* [comment removed for export] *)
      sn F_21ff0 D_21ff0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_C4. kpost.
  Qed.

  Lemma k6_it4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_C4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x220f0 : word) Mi rom) (mkst regs' (0x22130 : word) M' rom) /\ k6_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_C4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21ff4 D_21ff4.   (* [comment removed for export] *)
      sn F_21ff8 D_21ff8.   (* [comment removed for export] *)
      sn F_21ffc D_21ffc.   (* [comment removed for export] *)
      sn F_22000 D_22000.   (* [comment removed for export] *)
      sn F_22004 D_22004.   (* [comment removed for export] *)
      sn F_22008 D_22008.   (* [comment removed for export] *)
      sn F_2200c D_2200c.   (* [comment removed for export] *)
      sn F_22010 D_22010.   (* [comment removed for export] *)
      sn F_22014 D_22014.   (* [comment removed for export] *)
      sn F_22018 D_22018.   (* [comment removed for export] *)
      sn F_2201c D_2201c.   (* [comment removed for export] *)
      sn F_22020 D_22020.   (* [comment removed for export] *)
      sn F_22024 D_22024.   (* [comment removed for export] *)
      gsw F_22028 D_22028 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_2202c D_2202c (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_22030 D_22030 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_BN. kpost.
  Qed.

  Lemma k6_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22010 : word) Mi rom) (mkst regs' (0x22130 : word) M' rom) /\ k6_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k6_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k6_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k6_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k6_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    destruct (k6_it4 r4 M4 i j Hi Hj H4) as (r5 & M5 & RUN5 & H5).
    exists r5, M5. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | exact RUN5]]]] | exact H5].
  Qed.

  Lemma k6_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k6_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22130 : word) Mi rom) (mkst regs' (0x22010 : word) M' rom) /\ k6_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k6_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_22034 D_22034 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_IN. kpost.
  Qed.

  Lemma k6_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k6_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22130 : word) Mi rom) (mkst regs' (0x21fb0 : word) M' rom) /\ k6_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k6_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_22034 D_22034 ltac:(condZ).   (* [comment removed for export] *)
      sn F_22038 D_22038.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RL. kpost.
  Qed.

  Lemma k6_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k6_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21fb0 : word) Mi rom) (mkst regs' (0x21fcc : word) M' rom) /\ k6_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k6_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21eb4 D_21eb4 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21eb8 D_21eb8 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ebc D_21ebc (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ec0 D_21ec0 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21ec4 D_21ec4 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21ec8 D_21ec8 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_21ecc D_21ecc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RH. kpost.
  Qed.

  Lemma k6_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k6_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21fb0 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k6_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21eb4 D_21eb4 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21eb8 D_21eb8 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ebc D_21ebc (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ec0 D_21ec0 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21ec4 D_21ec4 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21ec8 D_21ec8 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_21ecc D_21ecc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k6_inner : forall regs Mi i, (0 <= i < h)%Z -> k6_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x22010 : word) Mi rom) (mkst regs' (0x21fb0 : word) M' rom) /\ k6_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x22010 : word) (0x21fb0 : word) (fun r m j => k6_IN r m i j) (fun r m => k6_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k6_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k6_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k6_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k6_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21f58 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k6_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21fcc : word) (0x22300 : word) (fun r m i => k6_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k6_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k6_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k6_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k6_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k7_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).
  Definition k7_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Definition k7_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Definition k7_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).

  Lemma k7_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21af0 : word) Mi rom) (mkst regs' (0x21b74 : word) M' rom) /\ k7_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_219f4 D_219f4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_219f8 D_219f8.   (* [comment removed for export] *)
      zvw F_219fc D_219fc (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_21a00 D_21a00 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvslw F_21a04 D_21a04 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_21a08 D_21a08 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21a0c D_21a0c (Z_to_bv 64 (datas + 4)).   (* [comment removed for export] *)
      ldf F_21a10 D_21a10 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvsl F_21a14 D_21a14 (Z_to_bv 64 (4 * wpld)) 4%Z.   (* [comment removed for export] *)
      stf F_21a18 D_21a18 8%Z (Z_to_bv 64 (4 * wpld)).   (* [comment removed for export] *)
      sn F_21a1c D_21a1c.   (* [comment removed for export] *)
      stf F_21a20 D_21a20 24%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_21a24 D_21a24.   (* [comment removed for export] *)
      zv F_21a28 D_21a28 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvsl F_21a2c D_21a2c (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21a30 D_21a30 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      stf F_21a34 D_21a34 16%Z (Z_to_bv 64 (4 * wpls)).   (* [comment removed for export] *)
      zv F_21a38 D_21a38 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_21a3c D_21a3c (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21a40 D_21a40 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21a44 D_21a44 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21a48 D_21a48 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      stf F_21a4c D_21a4c 0%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21a50 D_21a50.   (* [comment removed for export] *)
      sn F_21a54 D_21a54.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RH. kpost.
  Qed.

  Lemma k7_rowset : forall regs Mi i, (0 <= i < h)%Z -> k7_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21b74 : word) Mi rom) (mkst regs' (0x21bb8 : word) M' rom) /\ k7_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k7_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_21a78 D_21a78 24%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_21a7c D_21a7c.   (* [comment removed for export] *)
      stepb_ft F_21a80 D_21a80 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_21a84 D_21a84 8%Z (Z_to_bv 64 (4 * wpld)).   (* [comment removed for export] *)
      zv F_21a88 D_21a88 (Z_to_bv 64 (4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_21a8c D_21a8c 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21a90 D_21a90 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_21a94 D_21a94 0%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      zv F_21a98 D_21a98 (Z_to_bv 64 (4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zvsl F_21a9c D_21a9c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_21aa0 D_21aa0 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21aa4 D_21aa4 (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21aa8 D_21aa8 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21aac D_21aac (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ab0 D_21ab0 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21ab4 D_21ab4 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21ab8 D_21ab8 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_IN. kpost.
  Qed.

  Definition k7_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Lemma k7_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21bb8 : word) Mi rom) (mkst regs' (0x21bf0 : word) M' rom) /\ k7_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs8 & v8 & Hb8 & Hv8).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs9 & v9 & Hb9 & Hv9).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs10 & v10 & Hb10 & Hv10).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs11 & v11 & Hb11 & Hv11).
    eexists. eexists. split.
    -
      stepLD F_21abc D_21abc bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21ac0 D_21ac0 bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21ac4 D_21ac4 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_21ac8 D_21ac8 bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21acc D_21acc bs4 v4 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21ad0 D_21ad0 bs5 v5 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_21ad4 D_21ad4 bs6 v6 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_21ad8 D_21ad8 bs7 v7 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      stepLD F_21adc D_21adc bs8 v8 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb8) ltac:(exact Hv8).   (* [comment removed for export] *)
      stepLD F_21ae0 D_21ae0 bs9 v9 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb9) ltac:(exact Hv9).   (* [comment removed for export] *)
      stepLD F_21ae4 D_21ae4 bs10 v10 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb10) ltac:(exact Hv10).   (* [comment removed for export] *)
      stepLD F_21ae8 D_21ae8 bs11 v11 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb11) ltac:(exact Hv11).   (* [comment removed for export] *)
      sn F_21aec D_21aec.   (* [comment removed for export] *)
      sn F_21af0 D_21af0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_C1. kpost.
  Qed.

  Definition k7_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Lemma k7_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21bf0 : word) Mi rom) (mkst regs' (0x21c28 : word) M' rom) /\ k7_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21af4 D_21af4.   (* [comment removed for export] *)
      sn F_21af8 D_21af8.   (* [comment removed for export] *)
      sn F_21afc D_21afc.   (* [comment removed for export] *)
      sn F_21b00 D_21b00.   (* [comment removed for export] *)
      sn F_21b04 D_21b04.   (* [comment removed for export] *)
      sn F_21b08 D_21b08.   (* [comment removed for export] *)
      sn F_21b0c D_21b0c.   (* [comment removed for export] *)
      sn F_21b10 D_21b10.   (* [comment removed for export] *)
      sn F_21b14 D_21b14.   (* [comment removed for export] *)
      sn F_21b18 D_21b18.   (* [comment removed for export] *)
      sn F_21b1c D_21b1c.   (* [comment removed for export] *)
      sn F_21b20 D_21b20.   (* [comment removed for export] *)
      sn F_21b24 D_21b24.   (* [comment removed for export] *)
      sn F_21b28 D_21b28.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_C2. kpost.
  Qed.

  Definition k7_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Lemma k7_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21c28 : word) Mi rom) (mkst regs' (0x21c60 : word) M' rom) /\ k7_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_C2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21b2c D_21b2c.   (* [comment removed for export] *)
      sn F_21b30 D_21b30.   (* [comment removed for export] *)
      sn F_21b34 D_21b34.   (* [comment removed for export] *)
      sn F_21b38 D_21b38.   (* [comment removed for export] *)
      sn F_21b3c D_21b3c.   (* [comment removed for export] *)
      sn F_21b40 D_21b40.   (* [comment removed for export] *)
      sn F_21b44 D_21b44.   (* [comment removed for export] *)
      sn F_21b48 D_21b48.   (* [comment removed for export] *)
      sn F_21b4c D_21b4c.   (* [comment removed for export] *)
      sn F_21b50 D_21b50.   (* [comment removed for export] *)
      sn F_21b54 D_21b54.   (* [comment removed for export] *)
      sn F_21b58 D_21b58.   (* [comment removed for export] *)
      sn F_21b5c D_21b5c.   (* [comment removed for export] *)
      sn F_21b60 D_21b60.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_C3. kpost.
  Qed.

  Definition k7_C4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (4 * PW)) /\ cell Mi 8 (Z_to_bv 64 (4 * wpld)) /\ cell Mi 16 (Z_to_bv 64 (4 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (w + 31)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).
  Lemma k7_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21c60 : word) Mi rom) (mkst regs' (0x21c98 : word) M' rom) /\ k7_C4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21b64 D_21b64.   (* [comment removed for export] *)
      sn F_21b68 D_21b68.   (* [comment removed for export] *)
      zv F_21b6c D_21b6c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21b70 D_21b70 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21b74 D_21b74 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_21b78 D_21b78.   (* [comment removed for export] *)
      sn F_21b7c D_21b7c.   (* [comment removed for export] *)
      sn F_21b80 D_21b80.   (* [comment removed for export] *)
      sn F_21b84 D_21b84.   (* [comment removed for export] *)
      sn F_21b88 D_21b88.   (* [comment removed for export] *)
      sn F_21b8c D_21b8c.   (* [comment removed for export] *)
      sn F_21b90 D_21b90.   (* [comment removed for export] *)
      sn F_21b94 D_21b94.   (* [comment removed for export] *)
      sn F_21b98 D_21b98.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_C4. kpost.
  Qed.

  Lemma k7_it4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_C4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21c98 : word) Mi rom) (mkst regs' (0x21cd8 : word) M' rom) /\ k7_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_C4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21b9c D_21b9c.   (* [comment removed for export] *)
      sn F_21ba0 D_21ba0.   (* [comment removed for export] *)
      sn F_21ba4 D_21ba4.   (* [comment removed for export] *)
      sn F_21ba8 D_21ba8.   (* [comment removed for export] *)
      sn F_21bac D_21bac.   (* [comment removed for export] *)
      sn F_21bb0 D_21bb0.   (* [comment removed for export] *)
      sn F_21bb4 D_21bb4.   (* [comment removed for export] *)
      sn F_21bb8 D_21bb8.   (* [comment removed for export] *)
      sn F_21bbc D_21bbc.   (* [comment removed for export] *)
      sn F_21bc0 D_21bc0.   (* [comment removed for export] *)
      sn F_21bc4 D_21bc4.   (* [comment removed for export] *)
      sn F_21bc8 D_21bc8.   (* [comment removed for export] *)
      sn F_21bcc D_21bcc.   (* [comment removed for export] *)
      gsw F_21bd0 D_21bd0 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_21bd4 D_21bd4 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21bd8 D_21bd8 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_BN. kpost.
  Qed.

  Lemma k7_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21bb8 : word) Mi rom) (mkst regs' (0x21cd8 : word) M' rom) /\ k7_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k7_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k7_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k7_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k7_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    destruct (k7_it4 r4 M4 i j Hi Hj H4) as (r5 & M5 & RUN5 & H5).
    exists r5, M5. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | exact RUN5]]]] | exact H5].
  Qed.

  Lemma k7_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k7_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21cd8 : word) Mi rom) (mkst regs' (0x21bb8 : word) M' rom) /\ k7_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k7_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_21bdc D_21bdc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_IN. kpost.
  Qed.

  Lemma k7_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k7_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21cd8 : word) Mi rom) (mkst regs' (0x21b54 : word) M' rom) /\ k7_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k7_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21bdc D_21bdc ltac:(condZ).   (* [comment removed for export] *)
      sn F_21be0 D_21be0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RL. kpost.
  Qed.

  Lemma k7_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k7_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21b54 : word) Mi rom) (mkst regs' (0x21b74 : word) M' rom) /\ k7_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k7_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21a58 D_21a58 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_21a5c D_21a5c 16%Z (Z_to_bv 64 (4 * wpls)).   (* [comment removed for export] *)
      zv F_21a60 D_21a60 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21a64 D_21a64 (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21a68 D_21a68 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21a6c D_21a6c (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21a70 D_21a70 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_21a74 D_21a74 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RH. kpost.
  Qed.

  Lemma k7_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k7_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21b54 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k7_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21a58 D_21a58 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_21a5c D_21a5c 16%Z (Z_to_bv 64 (4 * wpls)).   (* [comment removed for export] *)
      zv F_21a60 D_21a60 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21a64 D_21a64 (Z_to_bv 64 (datas + 12 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21a68 D_21a68 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21a6c D_21a6c (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21a70 D_21a70 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_21a74 D_21a74 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k7_inner : forall regs Mi i, (0 <= i < h)%Z -> k7_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21bb8 : word) Mi rom) (mkst regs' (0x21b54 : word) M' rom) /\ k7_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21bb8 : word) (0x21b54 : word) (fun r m j => k7_IN r m i j) (fun r m => k7_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k7_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k7_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k7_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k7_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21af0 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k7_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21b74 : word) (0x22300 : word) (fun r m i => k7_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k7_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k7_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k7_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k7_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k8_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)).
  Definition k8_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Definition k8_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).
  Definition k8_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)).

  Lemma k8_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x22138 : word) Mi rom) (mkst regs' (0x22190 : word) M' rom) /\ k8_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_2203c D_2203c ltac:(condZ).   (* [comment removed for export] *)
      sn F_22040 D_22040.   (* [comment removed for export] *)
      zvw F_22044 D_22044 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_22048 D_22048 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvslw F_2204c D_2204c (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_22050 D_22050 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      zvpw F_22054 D_22054.   (* [comment removed for export] *)
      zvsl F_22058 D_22058 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_2205c D_2205c (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_22060 D_22060 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_22064 D_22064 (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_22068 D_22068 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_2206c D_2206c (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_22070 D_22070 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_22074 D_22074 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_22078 D_22078.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RH. kpost.
  Qed.

  Lemma k8_rowset : forall regs Mi i, (0 <= i < h)%Z -> k8_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x22190 : word) Mi rom) (mkst regs' (0x221d4 : word) M' rom) /\ k8_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k8_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_22094 D_22094.   (* [comment removed for export] *)
      stepb_ft F_22098 D_22098 ltac:(condZ).   (* [comment removed for export] *)
      zv F_2209c D_2209c (Z_to_bv 64 (4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_220a0 D_220a0 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_220a4 D_220a4 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_220a8 D_220a8 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zv F_220ac D_220ac (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zv F_220b0 D_220b0 (Z_to_bv 64 (4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      zvsl F_220b4 D_220b4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_220b8 D_220b8 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_220bc D_220bc (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_220c0 D_220c0 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_220c4 D_220c4 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_220c8 D_220c8 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_220cc D_220cc (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_220d0 D_220d0 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_220d4 D_220d4 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_IN. kpost.
  Qed.

  Definition k8_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k8_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x221d4 : word) Mi rom) (mkst regs' (0x2220c : word) M' rom) /\ k8_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs8 & v8 & Hb8 & Hv8).
    eexists. eexists. split.
    -
      stepLD F_220d8 D_220d8 bs0 v0 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_220dc D_220dc bs1 v1 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_220e0 D_220e0 bs2 v2 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_220e4 D_220e4 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_220e8 D_220e8 bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_220ec D_220ec bs4 v4 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_220f0 D_220f0 bs5 v5 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      zv F_220f4 D_220f4 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_220f8 D_220f8 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_220fc D_220fc bs6 v6 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_22100 D_22100 bs7 v7 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      stepLD F_22104 D_22104 bs8 v8 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb8) ltac:(exact Hv8).   (* [comment removed for export] *)
      sn F_22108 D_22108.   (* [comment removed for export] *)
      sn F_2210c D_2210c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_C1. kpost.
  Qed.

  Definition k8_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k8_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2220c : word) Mi rom) (mkst regs' (0x22244 : word) M' rom) /\ k8_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_22110 D_22110.   (* [comment removed for export] *)
      sn F_22114 D_22114.   (* [comment removed for export] *)
      sn F_22118 D_22118.   (* [comment removed for export] *)
      sn F_2211c D_2211c.   (* [comment removed for export] *)
      sn F_22120 D_22120.   (* [comment removed for export] *)
      sn F_22124 D_22124.   (* [comment removed for export] *)
      sn F_22128 D_22128.   (* [comment removed for export] *)
      sn F_2212c D_2212c.   (* [comment removed for export] *)
      sn F_22130 D_22130.   (* [comment removed for export] *)
      sn F_22134 D_22134.   (* [comment removed for export] *)
      sn F_22138 D_22138.   (* [comment removed for export] *)
      sn F_2213c D_2213c.   (* [comment removed for export] *)
      sn F_22140 D_22140.   (* [comment removed for export] *)
      sn F_22144 D_22144.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_C2. kpost.
  Qed.

  Definition k8_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k8_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x22244 : word) Mi rom) (mkst regs' (0x2227c : word) M' rom) /\ k8_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_C2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    eexists. eexists. split.
    -
      sn F_22148 D_22148.   (* [comment removed for export] *)
      sn F_2214c D_2214c.   (* [comment removed for export] *)
      sn F_22150 D_22150.   (* [comment removed for export] *)
      sn F_22154 D_22154.   (* [comment removed for export] *)
      stepLD F_22158 D_22158 bs0 v0 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2215c D_2215c bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_22160 D_22160 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_22164 D_22164 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_22168 D_22168.   (* [comment removed for export] *)
      sn F_2216c D_2216c.   (* [comment removed for export] *)
      sn F_22170 D_22170.   (* [comment removed for export] *)
      sn F_22174 D_22174.   (* [comment removed for export] *)
      sn F_22178 D_22178.   (* [comment removed for export] *)
      sn F_2217c D_2217c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_C3. kpost.
  Qed.

  Definition k8_C4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (4 * PW)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k8_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2227c : word) Mi rom) (mkst regs' (0x222b4 : word) M' rom) /\ k8_C4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_22180 D_22180.   (* [comment removed for export] *)
      sn F_22184 D_22184.   (* [comment removed for export] *)
      sn F_22188 D_22188.   (* [comment removed for export] *)
      sn F_2218c D_2218c.   (* [comment removed for export] *)
      sn F_22190 D_22190.   (* [comment removed for export] *)
      sn F_22194 D_22194.   (* [comment removed for export] *)
      sn F_22198 D_22198.   (* [comment removed for export] *)
      sn F_2219c D_2219c.   (* [comment removed for export] *)
      sn F_221a0 D_221a0.   (* [comment removed for export] *)
      sn F_221a4 D_221a4.   (* [comment removed for export] *)
      sn F_221a8 D_221a8.   (* [comment removed for export] *)
      sn F_221ac D_221ac.   (* [comment removed for export] *)
      sn F_221b0 D_221b0.   (* [comment removed for export] *)
      sn F_221b4 D_221b4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_C4. kpost.
  Qed.

  Lemma k8_it4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_C4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x222b4 : word) Mi rom) (mkst regs' (0x222f8 : word) M' rom) /\ k8_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_C4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_221b8 D_221b8.   (* [comment removed for export] *)
      sn F_221bc D_221bc.   (* [comment removed for export] *)
      sn F_221c0 D_221c0.   (* [comment removed for export] *)
      sn F_221c4 D_221c4.   (* [comment removed for export] *)
      sn F_221c8 D_221c8.   (* [comment removed for export] *)
      sn F_221cc D_221cc.   (* [comment removed for export] *)
      sn F_221d0 D_221d0.   (* [comment removed for export] *)
      sn F_221d4 D_221d4.   (* [comment removed for export] *)
      sn F_221d8 D_221d8.   (* [comment removed for export] *)
      sn F_221dc D_221dc.   (* [comment removed for export] *)
      sn F_221e0 D_221e0.   (* [comment removed for export] *)
      sn F_221e4 D_221e4.   (* [comment removed for export] *)
      sn F_221e8 D_221e8.   (* [comment removed for export] *)
      sn F_221ec D_221ec.   (* [comment removed for export] *)
      gsw F_221f0 D_221f0 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_221f4 D_221f4 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_221f8 D_221f8 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_BN. kpost.
  Qed.

  Lemma k8_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x221d4 : word) Mi rom) (mkst regs' (0x222f8 : word) M' rom) /\ k8_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k8_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k8_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k8_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k8_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    destruct (k8_it4 r4 M4 i j Hi Hj H4) as (r5 & M5 & RUN5 & H5).
    exists r5, M5. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | exact RUN5]]]] | exact H5].
  Qed.

  Lemma k8_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k8_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x222f8 : word) Mi rom) (mkst regs' (0x221d4 : word) M' rom) /\ k8_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k8_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_221fc D_221fc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_IN. kpost.
  Qed.

  Lemma k8_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k8_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x222f8 : word) Mi rom) (mkst regs' (0x22178 : word) M' rom) /\ k8_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k8_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_221fc D_221fc ltac:(condZ).   (* [comment removed for export] *)
      sn F_22200 D_22200.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RL. kpost.
  Qed.

  Lemma k8_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k8_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x22178 : word) Mi rom) (mkst regs' (0x22190 : word) M' rom) /\ k8_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k8_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2207c D_2207c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_22080 D_22080 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_22084 D_22084 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_22088 D_22088 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2208c D_2208c 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_22090 D_22090 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RH. kpost.
  Qed.

  Lemma k8_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k8_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x22178 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k8_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2207c D_2207c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_22080 D_22080 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_22084 D_22084 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_22088 D_22088 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2208c D_2208c 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_22090 D_22090 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k8_inner : forall regs Mi i, (0 <= i < h)%Z -> k8_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x221d4 : word) Mi rom) (mkst regs' (0x22178 : word) M' rom) /\ k8_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x221d4 : word) (0x22178 : word) (fun r m j => k8_IN r m i j) (fun r m => k8_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k8_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k8_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k8_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k8_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x22138 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k8_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x22190 : word) (0x22300 : word) (fun r m i => k8_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k8_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k8_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k8_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k8_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k9_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).
  Definition k9_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Definition k9_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Definition k9_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).

  Lemma k9_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x216fc : word) Mi rom) (mkst regs' (0x21760 : word) M' rom) /\ k9_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_21600 D_21600 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21604 D_21604.   (* [comment removed for export] *)
      zvw F_21608 D_21608 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_2160c D_2160c 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvslw F_21610 D_21610 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_21614 D_21614 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      sn F_21618 D_21618.   (* [comment removed for export] *)
      zvpw F_2161c D_2161c.   (* [comment removed for export] *)
      zvsl F_21620 D_21620 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_21624 D_21624 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_21628 D_21628 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_2162c D_2162c (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_21630 D_21630 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21634 D_21634 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21638 D_21638 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_2163c D_2163c (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      stf F_21640 D_21640 16%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21644 D_21644.   (* [comment removed for export] *)
      sn F_21648 D_21648.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RH. kpost.
  Qed.

  Lemma k9_rowset : forall regs Mi i, (0 <= i < h)%Z -> k9_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21760 : word) Mi rom) (mkst regs' (0x217a8 : word) M' rom) /\ k9_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k9_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21664 D_21664.   (* [comment removed for export] *)
      stepb_ft F_21668 D_21668 ltac:(condZ).   (* [comment removed for export] *)
      zv F_2166c D_2166c (Z_to_bv 64 (4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21670 D_21670 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21674 D_21674 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_21678 D_21678 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zv F_2167c D_2167c (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      ldf F_21680 D_21680 16%Z (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      zv F_21684 D_21684 (Z_to_bv 64 (4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      zvsl F_21688 D_21688 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_2168c D_2168c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_21690 D_21690 (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21694 D_21694 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21698 D_21698 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_2169c D_2169c (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_216a0 D_216a0 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_216a4 D_216a4 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_216a8 D_216a8 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_IN. kpost.
  Qed.

  Definition k9_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Lemma k9_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x217a8 : word) Mi rom) (mkst regs' (0x217e0 : word) M' rom) /\ k9_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs8 & v8 & Hb8 & Hv8).
    eexists. eexists. split.
    -
      stepLD F_216ac D_216ac bs0 v0 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_216b0 D_216b0 bs1 v1 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_216b4 D_216b4 bs2 v2 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_216b8 D_216b8 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_216bc D_216bc bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_216c0 D_216c0 bs4 v4 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_216c4 D_216c4 bs5 v5 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      zv F_216c8 D_216c8 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_216cc D_216cc (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_216d0 D_216d0 bs6 v6 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_216d4 D_216d4 bs7 v7 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      stepLD F_216d8 D_216d8 bs8 v8 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb8) ltac:(exact Hv8).   (* [comment removed for export] *)
      sn F_216dc D_216dc.   (* [comment removed for export] *)
      sn F_216e0 D_216e0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_C1. kpost.
  Qed.

  Definition k9_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Lemma k9_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x217e0 : word) Mi rom) (mkst regs' (0x21818 : word) M' rom) /\ k9_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_216e4 D_216e4.   (* [comment removed for export] *)
      sn F_216e8 D_216e8.   (* [comment removed for export] *)
      sn F_216ec D_216ec.   (* [comment removed for export] *)
      sn F_216f0 D_216f0.   (* [comment removed for export] *)
      sn F_216f4 D_216f4.   (* [comment removed for export] *)
      sn F_216f8 D_216f8.   (* [comment removed for export] *)
      sn F_216fc D_216fc.   (* [comment removed for export] *)
      sn F_21700 D_21700.   (* [comment removed for export] *)
      sn F_21704 D_21704.   (* [comment removed for export] *)
      sn F_21708 D_21708.   (* [comment removed for export] *)
      sn F_2170c D_2170c.   (* [comment removed for export] *)
      sn F_21710 D_21710.   (* [comment removed for export] *)
      sn F_21714 D_21714.   (* [comment removed for export] *)
      sn F_21718 D_21718.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_C2. kpost.
  Qed.

  Definition k9_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Lemma k9_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21818 : word) Mi rom) (mkst regs' (0x21850 : word) M' rom) /\ k9_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_C2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    eexists. eexists. split.
    -
      sn F_2171c D_2171c.   (* [comment removed for export] *)
      sn F_21720 D_21720.   (* [comment removed for export] *)
      sn F_21724 D_21724.   (* [comment removed for export] *)
      sn F_21728 D_21728.   (* [comment removed for export] *)
      stepLD F_2172c D_2172c bs0 v0 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21730 D_21730 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21734 D_21734 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_21738 D_21738 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_2173c D_2173c.   (* [comment removed for export] *)
      sn F_21740 D_21740.   (* [comment removed for export] *)
      sn F_21744 D_21744.   (* [comment removed for export] *)
      sn F_21748 D_21748.   (* [comment removed for export] *)
      sn F_2174c D_2174c.   (* [comment removed for export] *)
      sn F_21750 D_21750.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_C3. kpost.
  Qed.

  Definition k9_C4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (4 * PW)) /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 32 (Z_to_bv 64 (h)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (w + 31)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).
  Lemma k9_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21850 : word) Mi rom) (mkst regs' (0x21888 : word) M' rom) /\ k9_C4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21754 D_21754.   (* [comment removed for export] *)
      sn F_21758 D_21758.   (* [comment removed for export] *)
      sn F_2175c D_2175c.   (* [comment removed for export] *)
      sn F_21760 D_21760.   (* [comment removed for export] *)
      sn F_21764 D_21764.   (* [comment removed for export] *)
      sn F_21768 D_21768.   (* [comment removed for export] *)
      sn F_2176c D_2176c.   (* [comment removed for export] *)
      sn F_21770 D_21770.   (* [comment removed for export] *)
      sn F_21774 D_21774.   (* [comment removed for export] *)
      sn F_21778 D_21778.   (* [comment removed for export] *)
      sn F_2177c D_2177c.   (* [comment removed for export] *)
      sn F_21780 D_21780.   (* [comment removed for export] *)
      sn F_21784 D_21784.   (* [comment removed for export] *)
      sn F_21788 D_21788.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_C4. kpost.
  Qed.

  Lemma k9_it4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_C4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21888 : word) Mi rom) (mkst regs' (0x218cc : word) M' rom) /\ k9_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_C4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2178c D_2178c.   (* [comment removed for export] *)
      sn F_21790 D_21790.   (* [comment removed for export] *)
      sn F_21794 D_21794.   (* [comment removed for export] *)
      sn F_21798 D_21798.   (* [comment removed for export] *)
      sn F_2179c D_2179c.   (* [comment removed for export] *)
      sn F_217a0 D_217a0.   (* [comment removed for export] *)
      sn F_217a4 D_217a4.   (* [comment removed for export] *)
      sn F_217a8 D_217a8.   (* [comment removed for export] *)
      sn F_217ac D_217ac.   (* [comment removed for export] *)
      sn F_217b0 D_217b0.   (* [comment removed for export] *)
      sn F_217b4 D_217b4.   (* [comment removed for export] *)
      sn F_217b8 D_217b8.   (* [comment removed for export] *)
      sn F_217bc D_217bc.   (* [comment removed for export] *)
      sn F_217c0 D_217c0.   (* [comment removed for export] *)
      gsw F_217c4 D_217c4 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_217c8 D_217c8 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_217cc D_217cc (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_BN. kpost.
  Qed.

  Lemma k9_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x217a8 : word) Mi rom) (mkst regs' (0x218cc : word) M' rom) /\ k9_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k9_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k9_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k9_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k9_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    destruct (k9_it4 r4 M4 i j Hi Hj H4) as (r5 & M5 & RUN5 & H5).
    exists r5, M5. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | exact RUN5]]]] | exact H5].
  Qed.

  Lemma k9_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k9_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x218cc : word) Mi rom) (mkst regs' (0x217a8 : word) M' rom) /\ k9_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k9_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_217d0 D_217d0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_IN. kpost.
  Qed.

  Lemma k9_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k9_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x218cc : word) Mi rom) (mkst regs' (0x21748 : word) M' rom) /\ k9_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k9_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_217d0 D_217d0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_217d4 D_217d4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RL. kpost.
  Qed.

  Lemma k9_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k9_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21748 : word) Mi rom) (mkst regs' (0x21760 : word) M' rom) /\ k9_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k9_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2164c D_2164c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21650 D_21650 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21654 D_21654 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21658 D_21658 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2165c D_2165c 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_21660 D_21660 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RH. kpost.
  Qed.

  Lemma k9_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k9_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21748 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k9_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2164c D_2164c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21650 D_21650 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21654 D_21654 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21658 D_21658 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2165c D_2165c 32%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_21660 D_21660 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k9_inner : forall regs Mi i, (0 <= i < h)%Z -> k9_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x217a8 : word) Mi rom) (mkst regs' (0x21748 : word) M' rom) /\ k9_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x217a8 : word) (0x21748 : word) (fun r m j => k9_IN r m i j) (fun r m => k9_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k9_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k9_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k9_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k9_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x216fc : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k9_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21760 : word) (0x22300 : word) (fun r m i => k9_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k9_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k9_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k9_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k9_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
