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
  Definition k0_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)).
  Definition k0_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Definition k0_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).
  Definition k0_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)).

  Lemma k0_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x214b8 : word) Mi rom) (mkst regs' (0x21508 : word) M' rom) /\ k0_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_213bc D_213bc ltac:(condZ).   (* [comment removed for export] *)
      sn F_213c0 D_213c0.   (* [comment removed for export] *)
      zvw F_213c4 D_213c4 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_213c8 D_213c8 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_213cc D_213cc (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      sn F_213d0 D_213d0.   (* [comment removed for export] *)
      sn F_213d4 D_213d4.   (* [comment removed for export] *)
      zvpw F_213d8 D_213d8.   (* [comment removed for export] *)
      zv F_213dc D_213dc (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_213e0 D_213e0 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_213e4 D_213e4 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_213e8 D_213e8 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_213ec D_213ec (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_213f0 D_213f0 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_213f4 D_213f4.   (* [comment removed for export] *)
      sn F_213f8 D_213f8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RH. kpost.
  Qed.

  Lemma k0_rowset : forall regs Mi i, (0 <= i < h)%Z -> k0_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21508 : word) Mi rom) (mkst regs' (0x21544 : word) M' rom) /\ k0_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k0_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2140c D_2140c ltac:(condZ).   (* [comment removed for export] *)
      zv F_21410 D_21410 (Z_to_bv 64 (4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21414 D_21414 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21418 D_21418 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_2141c D_2141c 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zv F_21420 D_21420 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zv F_21424 D_21424 (Z_to_bv 64 (4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      zvsl F_21428 D_21428 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_2142c D_2142c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_21430 D_21430 (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21434 D_21434 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21438 D_21438 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_2143c D_2143c (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21440 D_21440 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21444 D_21444 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_IN. kpost.
  Qed.

  Definition k0_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k0_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21544 : word) Mi rom) (mkst regs' (0x2157c : word) M' rom) /\ k0_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_21448 D_21448 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2144c D_2144c bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21450 D_21450 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_21454 D_21454 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21458 D_21458 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_2145c D_2145c bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21460 D_21460 bs4 v4 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21464 D_21464 bs5 v5 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_21468 D_21468.   (* [comment removed for export] *)
      sn F_2146c D_2146c.   (* [comment removed for export] *)
      sn F_21470 D_21470.   (* [comment removed for export] *)
      sn F_21474 D_21474.   (* [comment removed for export] *)
      sn F_21478 D_21478.   (* [comment removed for export] *)
      sn F_2147c D_2147c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_C1. kpost.
  Qed.

  Definition k0_C2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k0_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2157c : word) Mi rom) (mkst regs' (0x215b4 : word) M' rom) /\ k0_C2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_C1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    eexists. eexists. split.
    -
      sn F_21480 D_21480.   (* [comment removed for export] *)
      sn F_21484 D_21484.   (* [comment removed for export] *)
      sn F_21488 D_21488.   (* [comment removed for export] *)
      sn F_2148c D_2148c.   (* [comment removed for export] *)
      sn F_21490 D_21490.   (* [comment removed for export] *)
      sn F_21494 D_21494.   (* [comment removed for export] *)
      sn F_21498 D_21498.   (* [comment removed for export] *)
      sn F_2149c D_2149c.   (* [comment removed for export] *)
      stepLD F_214a0 D_214a0 bs0 v0 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_214a4 D_214a4 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_214a8 D_214a8 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_214ac D_214ac (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_214b0 D_214b0.   (* [comment removed for export] *)
      sn F_214b4 D_214b4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_C2. kpost.
  Qed.

  Definition k0_C3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k0_it2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_C2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x215b4 : word) Mi rom) (mkst regs' (0x215ec : word) M' rom) /\ k0_C3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_C2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_214b8 D_214b8.   (* [comment removed for export] *)
      sn F_214bc D_214bc.   (* [comment removed for export] *)
      sn F_214c0 D_214c0.   (* [comment removed for export] *)
      sn F_214c4 D_214c4.   (* [comment removed for export] *)
      sn F_214c8 D_214c8.   (* [comment removed for export] *)
      sn F_214cc D_214cc.   (* [comment removed for export] *)
      sn F_214d0 D_214d0.   (* [comment removed for export] *)
      sn F_214d4 D_214d4.   (* [comment removed for export] *)
      sn F_214d8 D_214d8.   (* [comment removed for export] *)
      sn F_214dc D_214dc.   (* [comment removed for export] *)
      sn F_214e0 D_214e0.   (* [comment removed for export] *)
      sn F_214e4 D_214e4.   (* [comment removed for export] *)
      sn F_214e8 D_214e8.   (* [comment removed for export] *)
      sn F_214ec D_214ec.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_C3. kpost.
  Qed.

  Lemma k0_it3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_C3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x215ec : word) Mi rom) (mkst regs' (0x2160c : word) M' rom) /\ k0_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_C3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_214f0 D_214f0.   (* [comment removed for export] *)
      sn F_214f4 D_214f4.   (* [comment removed for export] *)
      sn F_214f8 D_214f8.   (* [comment removed for export] *)
      sn F_214fc D_214fc.   (* [comment removed for export] *)
      sn F_21500 D_21500.   (* [comment removed for export] *)
      gsw F_21504 D_21504 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_21508 D_21508 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_2150c D_2150c (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_BN. kpost.
  Qed.

  Lemma k0_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21544 : word) Mi rom) (mkst regs' (0x2160c : word) M' rom) /\ k0_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k0_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k0_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    destruct (k0_it2 r2 M2 i j Hi Hj H2) as (r3 & M3 & RUN3 & H3).
    destruct (k0_it3 r3 M3 i j Hi Hj H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Lemma k0_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k0_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2160c : word) Mi rom) (mkst regs' (0x21544 : word) M' rom) /\ k0_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k0_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_21510 D_21510 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_IN. kpost.
  Qed.

  Lemma k0_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k0_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2160c : word) Mi rom) (mkst regs' (0x214f8 : word) M' rom) /\ k0_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k0_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21510 D_21510 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21514 D_21514.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RL. kpost.
  Qed.

  Lemma k0_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k0_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x214f8 : word) Mi rom) (mkst regs' (0x21508 : word) M' rom) /\ k0_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k0_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_213fc D_213fc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21400 D_21400 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21404 D_21404 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_21408 D_21408 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RH. kpost.
  Qed.

  Lemma k0_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k0_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x214f8 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k0_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_213fc D_213fc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21400 D_21400 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21404 D_21404 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_21408 D_21408 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k0_inner : forall regs Mi i, (0 <= i < h)%Z -> k0_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21544 : word) Mi rom) (mkst regs' (0x214f8 : word) M' rom) /\ k0_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21544 : word) (0x214f8 : word) (fun r m j => k0_IN r m i j) (fun r m => k0_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k0_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k0_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k0_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k0_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x214b8 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k0_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21508 : word) (0x22300 : word) (fun r m i => k0_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k0_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k0_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k0_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k0_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k1_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).
  Definition k1_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 29 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).
  Definition k1_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 29 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)).
  Definition k1_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).

  Lemma k1_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21ce0 : word) Mi rom) (mkst regs' (0x21d38 : word) M' rom) /\ k1_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_21be4 D_21be4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21be8 D_21be8.   (* [comment removed for export] *)
      zvw F_21bec D_21bec (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zv F_21bf0 D_21bf0 (Z_to_bv 64 (datas + 4)).   (* [comment removed for export] *)
      ldf F_21bf4 D_21bf4 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_21bf8 D_21bf8 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_21bfc D_21bfc 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvsl F_21c00 D_21c00 (Z_to_bv 64 (4 * wpld)) 4%Z.   (* [comment removed for export] *)
      sn F_21c04 D_21c04.   (* [comment removed for export] *)
      sn F_21c08 D_21c08.   (* [comment removed for export] *)
      zvpw F_21c0c D_21c0c.   (* [comment removed for export] *)
      zv F_21c10 D_21c10 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_21c14 D_21c14 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21c18 D_21c18 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21c1c D_21c1c (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21c20 D_21c20 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21c24 D_21c24.   (* [comment removed for export] *)
      sn F_21c28 D_21c28.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RH. kpost.
  Qed.

  Lemma k1_rowset : forall regs Mi i, (0 <= i < h)%Z -> k1_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21d38 : word) Mi rom) (mkst regs' (0x21d64 : word) M' rom) /\ k1_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k1_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21c3c D_21c3c ltac:(condZ).   (* [comment removed for export] *)
      zv F_21c40 D_21c40 (Z_to_bv 64 (4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_21c44 D_21c44 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_21c48 D_21c48 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zv F_21c4c D_21c4c (Z_to_bv 64 (4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zvsl F_21c50 D_21c50 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_21c54 D_21c54 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_21c58 D_21c58 (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21c5c D_21c5c (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21c60 D_21c60 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21c64 D_21c64 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_IN. kpost.
  Qed.

  Definition k1_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 29 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).
  Lemma k1_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21d64 : word) Mi rom) (mkst regs' (0x21d9c : word) M' rom) /\ k1_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k1_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_21c68 D_21c68 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21c6c D_21c6c bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21c70 D_21c70 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_21c74 D_21c74 bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21c78 D_21c78 bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21c7c D_21c7c bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      zv F_21c80 D_21c80 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_21c84 D_21c84.   (* [comment removed for export] *)
      sn F_21c88 D_21c88.   (* [comment removed for export] *)
      sn F_21c8c D_21c8c.   (* [comment removed for export] *)
      sn F_21c90 D_21c90.   (* [comment removed for export] *)
      sn F_21c94 D_21c94.   (* [comment removed for export] *)
      sn F_21c98 D_21c98.   (* [comment removed for export] *)
      sn F_21c9c D_21c9c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_C1. kpost.
  Qed.

  Lemma k1_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21d9c : word) Mi rom) (mkst regs' (0x21ddc : word) M' rom) /\ k1_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k1_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21ca0 D_21ca0.   (* [comment removed for export] *)
      sn F_21ca4 D_21ca4.   (* [comment removed for export] *)
      sn F_21ca8 D_21ca8.   (* [comment removed for export] *)
      sn F_21cac D_21cac.   (* [comment removed for export] *)
      sn F_21cb0 D_21cb0.   (* [comment removed for export] *)
      sn F_21cb4 D_21cb4.   (* [comment removed for export] *)
      sn F_21cb8 D_21cb8.   (* [comment removed for export] *)
      sn F_21cbc D_21cbc.   (* [comment removed for export] *)
      sn F_21cc0 D_21cc0.   (* [comment removed for export] *)
      sn F_21cc4 D_21cc4.   (* [comment removed for export] *)
      sn F_21cc8 D_21cc8.   (* [comment removed for export] *)
      sn F_21ccc D_21ccc.   (* [comment removed for export] *)
      sn F_21cd0 D_21cd0.   (* [comment removed for export] *)
      gsw F_21cd4 D_21cd4 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_21cd8 D_21cd8 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21cdc D_21cdc (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_BN. kpost.
  Qed.

  Lemma k1_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21d64 : word) Mi rom) (mkst regs' (0x21ddc : word) M' rom) /\ k1_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k1_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k1_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Lemma k1_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k1_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21ddc : word) Mi rom) (mkst regs' (0x21d64 : word) M' rom) /\ k1_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k1_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_21ce0 D_21ce0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_IN. kpost.
  Qed.

  Lemma k1_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k1_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21ddc : word) Mi rom) (mkst regs' (0x21d28 : word) M' rom) /\ k1_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k1_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21ce0 D_21ce0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_21ce4 D_21ce4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RL. kpost.
  Qed.

  Lemma k1_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k1_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21d28 : word) Mi rom) (mkst regs' (0x21d38 : word) M' rom) /\ k1_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k1_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21c2c D_21c2c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21c30 D_21c30 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21c34 D_21c34 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_21c38 D_21c38 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RH. kpost.
  Qed.

  Lemma k1_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k1_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21d28 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k1_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21c2c D_21c2c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21c30 D_21c30 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21c34 D_21c34 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_21c38 D_21c38 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k1_inner : forall regs Mi i, (0 <= i < h)%Z -> k1_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21d64 : word) Mi rom) (mkst regs' (0x21d28 : word) M' rom) /\ k1_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21d64 : word) (0x21d28 : word) (fun r m j => k1_IN r m i j) (fun r m => k1_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k1_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k1_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k1_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k1_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21ce0 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k1_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21d38 : word) (0x22300 : word) (fun r m i => k1_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k1_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k1_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k1_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k1_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k2_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)).
  Definition k2_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).
  Definition k2_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).
  Definition k2_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)).

  Lemma k2_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x218d4 : word) Mi rom) (mkst regs' (0x2191c : word) M' rom) /\ k2_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_217d8 D_217d8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_217dc D_217dc.   (* [comment removed for export] *)
      zvw F_217e0 D_217e0 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_217e4 D_217e4 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_217e8 D_217e8 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      sn F_217ec D_217ec.   (* [comment removed for export] *)
      sn F_217f0 D_217f0.   (* [comment removed for export] *)
      zvpw F_217f4 D_217f4.   (* [comment removed for export] *)
      zv F_217f8 D_217f8 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_217fc D_217fc (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21800 D_21800 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21804 D_21804 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21808 D_21808 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_2180c D_2180c.   (* [comment removed for export] *)
      sn F_21810 D_21810.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RH. kpost.
  Qed.

  Lemma k2_rowset : forall regs Mi i, (0 <= i < h)%Z -> k2_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2191c : word) Mi rom) (mkst regs' (0x21954 : word) M' rom) /\ k2_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k2_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21820 D_21820 ltac:(condZ).   (* [comment removed for export] *)
      zv F_21824 D_21824 (Z_to_bv 64 (4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21828 D_21828 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_2182c D_2182c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_21830 D_21830 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zv F_21834 D_21834 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zv F_21838 D_21838 (Z_to_bv 64 (4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      zvsl F_2183c D_2183c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_21840 D_21840 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_21844 D_21844 (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21848 D_21848 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_2184c D_2184c (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21850 D_21850 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21854 D_21854 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_IN. kpost.
  Qed.

  Definition k2_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (32)) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k2_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21954 : word) Mi rom) (mkst regs' (0x2198c : word) M' rom) /\ k2_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k2_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_21858 D_21858 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2185c D_2185c bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21860 D_21860 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      zv F_21864 D_21864 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_21868 D_21868 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      stepLD F_2186c D_2186c bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21870 D_21870 bs4 v4 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21874 D_21874 bs5 v5 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_21878 D_21878.   (* [comment removed for export] *)
      sn F_2187c D_2187c.   (* [comment removed for export] *)
      sn F_21880 D_21880.   (* [comment removed for export] *)
      sn F_21884 D_21884.   (* [comment removed for export] *)
      sn F_21888 D_21888.   (* [comment removed for export] *)
      sn F_2188c D_2188c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_C1. kpost.
  Qed.

  Lemma k2_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2198c : word) Mi rom) (mkst regs' (0x219d0 : word) M' rom) /\ k2_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k2_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_21890 D_21890.   (* [comment removed for export] *)
      sn F_21894 D_21894.   (* [comment removed for export] *)
      sn F_21898 D_21898.   (* [comment removed for export] *)
      sn F_2189c D_2189c.   (* [comment removed for export] *)
      sn F_218a0 D_218a0.   (* [comment removed for export] *)
      sn F_218a4 D_218a4.   (* [comment removed for export] *)
      sn F_218a8 D_218a8.   (* [comment removed for export] *)
      sn F_218ac D_218ac.   (* [comment removed for export] *)
      sn F_218b0 D_218b0.   (* [comment removed for export] *)
      sn F_218b4 D_218b4.   (* [comment removed for export] *)
      sn F_218b8 D_218b8.   (* [comment removed for export] *)
      sn F_218bc D_218bc.   (* [comment removed for export] *)
      sn F_218c0 D_218c0.   (* [comment removed for export] *)
      sn F_218c4 D_218c4.   (* [comment removed for export] *)
      gsw F_218c8 D_218c8 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_218cc D_218cc (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_218d0 D_218d0 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_BN. kpost.
  Qed.

  Lemma k2_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21954 : word) Mi rom) (mkst regs' (0x219d0 : word) M' rom) /\ k2_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k2_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k2_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Lemma k2_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k2_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x219d0 : word) Mi rom) (mkst regs' (0x21954 : word) M' rom) /\ k2_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k2_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_218d4 D_218d4 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_IN. kpost.
  Qed.

  Lemma k2_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k2_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x219d0 : word) Mi rom) (mkst regs' (0x21910 : word) M' rom) /\ k2_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k2_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_218d4 D_218d4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_218d8 D_218d8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RL. kpost.
  Qed.

  Lemma k2_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k2_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21910 : word) Mi rom) (mkst regs' (0x2191c : word) M' rom) /\ k2_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k2_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21814 D_21814 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21818 D_21818 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_2181c D_2181c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RH. kpost.
  Qed.

  Lemma k2_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k2_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21910 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k2_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21814 D_21814 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21818 D_21818 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_2181c D_2181c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k2_inner : forall regs Mi i, (0 <= i < h)%Z -> k2_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21954 : word) Mi rom) (mkst regs' (0x21910 : word) M' rom) /\ k2_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21954 : word) (0x21910 : word) (fun r m j => k2_IN r m i j) (fun r m => k2_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k2_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k2_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k2_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k2_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x218d4 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k2_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x2191c : word) (0x22300 : word) (fun r m i => k2_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k2_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k2_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k2_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k2_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k3_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)).
  Definition k3_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Definition k3_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 9 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).
  Definition k3_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)).

  Lemma k3_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x219d8 : word) Mi rom) (mkst regs' (0x21a3c : word) M' rom) /\ k3_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_218dc D_218dc ltac:(condZ).   (* [comment removed for export] *)
      sn F_218e0 D_218e0.   (* [comment removed for export] *)
      zvw F_218e4 D_218e4 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_218e8 D_218e8 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_218ec D_218ec (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_218f0 D_218f0 (Z_to_bv 64 (datas + 4)).   (* [comment removed for export] *)
      ldf F_218f4 D_218f4 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvsl F_218f8 D_218f8 (Z_to_bv 64 (4 * wpld)) 4%Z.   (* [comment removed for export] *)
      sn F_218fc D_218fc.   (* [comment removed for export] *)
      sn F_21900 D_21900.   (* [comment removed for export] *)
      zvpw F_21904 D_21904.   (* [comment removed for export] *)
      zv F_21908 D_21908 (Z_to_bv 64 (datas + 4 * wpls + 4)).   (* [comment removed for export] *)
      zv F_2190c D_2190c (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_21910 D_21910 (Z_to_bv 64 (datas - 4 * wpls + 4)).   (* [comment removed for export] *)
      zv F_21914 D_21914 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_21918 D_21918 (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_2191c D_2191c (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21920 D_21920 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21924 D_21924.   (* [comment removed for export] *)
      sn F_21928 D_21928.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RH. kpost.
  Qed.

  Lemma k3_rowset : forall regs Mi i, (0 <= i < h)%Z -> k3_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21a3c : word) Mi rom) (mkst regs' (0x21a6c : word) M' rom) /\ k3_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k3_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21940 D_21940 ltac:(condZ).   (* [comment removed for export] *)
      zv F_21944 D_21944 (Z_to_bv 64 (4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_21948 D_21948 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_2194c D_2194c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zv F_21950 D_21950 (Z_to_bv 64 (4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zvsl F_21954 D_21954 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_21958 D_21958 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_2195c D_2195c (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21960 D_21960 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21964 D_21964 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21968 D_21968 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_2196c D_2196c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_IN. kpost.
  Qed.

  Definition k3_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (4 * wpld)) /\ getr regs 6 = (Z_to_bv 64 (32)) /\ getr regs 7 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4)) /\ getr regs 15 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)) /\ getr regs 18 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 8)) /\ getr regs 28 = (Z_to_bv 64 (4 * PW)) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * PW + 4 * (i * wpld))) /\ getr regs 31 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).
  Lemma k3_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21a6c : word) Mi rom) (mkst regs' (0x21aa4 : word) M' rom) /\ k3_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_21970 D_21970 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_21974 D_21974 bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_21978 D_21978 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2197c D_2197c bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_21980 D_21980 bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_21984 D_21984 bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      zv F_21988 D_21988 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      sn F_2198c D_2198c.   (* [comment removed for export] *)
      sn F_21990 D_21990.   (* [comment removed for export] *)
      sn F_21994 D_21994.   (* [comment removed for export] *)
      sn F_21998 D_21998.   (* [comment removed for export] *)
      sn F_2199c D_2199c.   (* [comment removed for export] *)
      sn F_219a0 D_219a0.   (* [comment removed for export] *)
      sn F_219a4 D_219a4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_C1. kpost.
  Qed.

  Lemma k3_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21aa4 : word) Mi rom) (mkst regs' (0x21ae8 : word) M' rom) /\ k3_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_219a8 D_219a8.   (* [comment removed for export] *)
      sn F_219ac D_219ac.   (* [comment removed for export] *)
      sn F_219b0 D_219b0.   (* [comment removed for export] *)
      sn F_219b4 D_219b4.   (* [comment removed for export] *)
      sn F_219b8 D_219b8.   (* [comment removed for export] *)
      sn F_219bc D_219bc.   (* [comment removed for export] *)
      sn F_219c0 D_219c0.   (* [comment removed for export] *)
      sn F_219c4 D_219c4.   (* [comment removed for export] *)
      sn F_219c8 D_219c8.   (* [comment removed for export] *)
      sn F_219cc D_219cc.   (* [comment removed for export] *)
      sn F_219d0 D_219d0.   (* [comment removed for export] *)
      sn F_219d4 D_219d4.   (* [comment removed for export] *)
      sn F_219d8 D_219d8.   (* [comment removed for export] *)
      gsw F_219dc D_219dc (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_219e0 D_219e0 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_219e4 D_219e4 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      zv F_219e8 D_219e8 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 8)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_BN. kpost.
  Qed.

  Lemma k3_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21a6c : word) Mi rom) (mkst regs' (0x21ae8 : word) M' rom) /\ k3_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k3_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k3_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Lemma k3_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k3_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21ae8 : word) Mi rom) (mkst regs' (0x21a6c : word) M' rom) /\ k3_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k3_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_219ec D_219ec ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_IN. kpost.
  Qed.

  Lemma k3_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k3_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21ae8 : word) Mi rom) (mkst regs' (0x21a28 : word) M' rom) /\ k3_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k3_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_219ec D_219ec ltac:(condZ).   (* [comment removed for export] *)
      sn F_219f0 D_219f0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RL. kpost.
  Qed.

  Lemma k3_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k3_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21a28 : word) Mi rom) (mkst regs' (0x21a3c : word) M' rom) /\ k3_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k3_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2192c D_2192c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21930 D_21930 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21934 D_21934 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21938 D_21938 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      stepb_ft F_2193c D_2193c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RH. kpost.
  Qed.

  Lemma k3_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k3_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x21a28 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k3_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_2192c D_2192c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21930 D_21930 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21934 D_21934 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      zv F_21938 D_21938 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4)).   (* [comment removed for export] *)
      stepb_tk F_2193c D_2193c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k3_inner : forall regs Mi i, (0 <= i < h)%Z -> k3_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21a6c : word) Mi rom) (mkst regs' (0x21a28 : word) M' rom) /\ k3_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21a6c : word) (0x21a28 : word) (fun r m j => k3_IN r m i j) (fun r m => k3_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k3_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k3_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k3_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k3_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x219d8 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k3_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x21a3c : word) (0x22300 : word) (fun r m i => k3_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k3_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k3_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k3_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k3_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k4_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (32)).
  Definition k4_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (32)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).
  Definition k4_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (32)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).
  Definition k4_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (32)).

  Lemma k4_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21614 : word) Mi rom) (mkst regs' (0x2165c : word) M' rom) /\ k4_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      stepb_ft F_21518 D_21518 ltac:(condZ).   (* [comment removed for export] *)
      sn F_2151c D_2151c.   (* [comment removed for export] *)
      zvw F_21520 D_21520 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      ldf F_21524 D_21524 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zvsl F_21528 D_21528 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      zvpw F_2152c D_2152c.   (* [comment removed for export] *)
      zv F_21530 D_21530 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_21534 D_21534 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_21538 D_21538 (Z_to_bv 64 (PW - 1)).   (* [comment removed for export] *)
      zvsl32 F_2153c D_2153c (Z_to_bv 64 ((PW - 1) * 2 ^ 32)).   (* [comment removed for export] *)
      zvsr30 F_21540 D_21540 (Z_to_bv 64 (4 * PW - 4)).   (* [comment removed for export] *)
      zv F_21544 D_21544 (Z_to_bv 64 (4 * PW)).   (* [comment removed for export] *)
      sn F_21548 D_21548.   (* [comment removed for export] *)
      sn F_2154c D_2154c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RH. kpost.
  Qed.

  Lemma k4_rowset : forall regs Mi i, (0 <= i < h)%Z -> k4_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2165c : word) Mi rom) (mkst regs' (0x21698 : word) M' rom) /\ k4_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k4_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_21560 D_21560 ltac:(condZ).   (* [comment removed for export] *)
      zv F_21564 D_21564 (Z_to_bv 64 (4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21568 D_21568 48%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_2156c D_2156c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      ldf F_21570 D_21570 24%Z (Z_to_bv 64 (wpls)).   (* [comment removed for export] *)
      zv F_21574 D_21574 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zv F_21578 D_21578 (Z_to_bv 64 (4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      zvsl F_2157c D_2157c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_21580 D_21580 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_21584 D_21584 (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_21588 D_21588 40%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_2158c D_2158c (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_21590 D_21590 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21594 D_21594 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21598 D_21598 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_IN. kpost.
  Qed.

  Definition k4_C1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 24 (Z_to_bv 64 (wpls)) /\ cell Mi 40 (Z_to_bv 64 (datad)) /\ cell Mi 48 (Z_to_bv 64 (wpld)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 6 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 7 = (Z_to_bv 64 (4 * PW)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 9 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 (w + 31)) /\ getr regs 12 = (Z_to_bv 64 (h)) /\ getr regs 14 = (Z_to_bv 64 (datas)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 17 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 28 = (Z_to_bv 64 (32)) /\ getr regs 29 = (Z_to_bv 64 (datas + 4 * PW + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).
  Lemma k4_it0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21698 : word) Mi rom) (mkst regs' (0x216d0 : word) M' rom) /\ k4_C1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k4_IN in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_2159c D_2159c bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_215a0 D_215a0 bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_215a4 D_215a4 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_215a8 D_215a8 bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_215ac D_215ac bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_215b0 D_215b0 bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      zv F_215b4 D_215b4 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_215b8 D_215b8 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_215bc D_215bc.   (* [comment removed for export] *)
      sn F_215c0 D_215c0.   (* [comment removed for export] *)
      sn F_215c4 D_215c4.   (* [comment removed for export] *)
      sn F_215c8 D_215c8.   (* [comment removed for export] *)
      sn F_215cc D_215cc.   (* [comment removed for export] *)
      sn F_215d0 D_215d0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_C1. kpost.
  Qed.

  Lemma k4_it1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_C1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x216d0 : word) Mi rom) (mkst regs' (0x216f4 : word) M' rom) /\ k4_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k4_C1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_215d4 D_215d4.   (* [comment removed for export] *)
      sn F_215d8 D_215d8.   (* [comment removed for export] *)
      sn F_215dc D_215dc.   (* [comment removed for export] *)
      sn F_215e0 D_215e0.   (* [comment removed for export] *)
      sn F_215e4 D_215e4.   (* [comment removed for export] *)
      sn F_215e8 D_215e8.   (* [comment removed for export] *)
      gsw F_215ec D_215ec (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      zv F_215f0 D_215f0 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j + 4)).   (* [comment removed for export] *)
      zv F_215f4 D_215f4 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_BN. kpost.
  Qed.

  Lemma k4_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x21698 : word) Mi rom) (mkst regs' (0x216f4 : word) M' rom) /\ k4_BN regs' M' i j.
  Proof.
    intros regs Mi i j Hi Hj H0.
    destruct (k4_it0 regs Mi i j Hi Hj H0) as (r1 & M1 & RUN1 & H1).
    destruct (k4_it1 r1 M1 i j Hi Hj H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Lemma k4_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k4_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x216f4 : word) Mi rom) (mkst regs' (0x21698 : word) M' rom) /\ k4_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k4_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_215f8 D_215f8 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_IN. kpost.
  Qed.

  Lemma k4_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k4_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x216f4 : word) Mi rom) (mkst regs' (0x2164c : word) M' rom) /\ k4_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k4_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_215f8 D_215f8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_215fc D_215fc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RL. kpost.
  Qed.

  Lemma k4_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k4_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2164c : word) Mi rom) (mkst regs' (0x2165c : word) M' rom) /\ k4_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k4_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21550 D_21550 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21554 D_21554 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21558 D_21558 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_2155c D_2155c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RH. kpost.
  Qed.

  Lemma k4_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k4_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2164c : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k4_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zv F_21550 D_21550 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zv F_21554 D_21554 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_21558 D_21558 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_2155c D_2155c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k4_inner : forall regs Mi i, (0 <= i < h)%Z -> k4_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x21698 : word) Mi rom) (mkst regs' (0x2164c : word) M' rom) /\ k4_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x21698 : word) (0x2164c : word) (fun r m j => k4_IN r m i j) (fun r m => k4_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k4_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k4_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k4_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k4_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x21614 : word) Mi rom) (mkst regs' (0x22300 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k4_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x2165c : word) (0x22300 : word) (fun r m i => k4_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k4_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k4_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k4_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k4_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
