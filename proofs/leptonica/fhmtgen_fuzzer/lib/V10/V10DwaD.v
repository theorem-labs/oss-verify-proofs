(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import CatSim StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 GrayLib DwaLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhI.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  Hypothesis Hsp : (4096 <= sp /\ sp + 272 <= 2 ^ 63)%Z.
  (* [comment removed for export] *)
  #[local] Abbreviation SLO := (datas - 24 * wpls - 4)%Z (only parsing).
  #[local] Abbreviation SHI := (datas + 4 * (wpls * h) + 20 * wpls + 4 * PW + 8)%Z (only parsing).
  #[local] Abbreviation DN := (4 * (wpld * h) - 4 * wpld + 4 * PW)%Z (only parsing).
  Hypothesis Hds : (4096 <= SLO /\ SHI <= 2 ^ 62)%Z.
  Hypothesis Hdd : (4096 <= datad /\ datad + DN <= 2 ^ 62)%Z.
  Hypothesis SOKs : store_ok SEGS M (Z_to_bv 64 SLO) (Z.to_nat (SHI - SLO)) = true.
  Hypothesis SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat DN) = true.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 sp) 168 = true.
  Hypothesis FR : disj_apart datad DN sp 272.
  Hypothesis Hals : (datas mod 4 = 0)%Z.
  Hypothesis Hald : (datad mod 4 = 0)%Z.

  Lemma HPW1 : (1 <= PW)%Z.
  Proof. rewrite <- HPW. change (2 ^ 5)%Z with 32%Z. apply Z.div_le_lower_bound; lia. Qed.
  Lemma HPW2 : (32 * PW <= w + 31)%Z.
  Proof. rewrite <- HPW. change (2 ^ 5)%Z with 32%Z. apply Z.mul_div_le. lia. Qed.
  Lemma wi_bound : forall i, (0 <= i < h)%Z -> (0 <= (wpls * i) /\ (wpls * i) <= (wpls * h) - wpls /\ 0 <= (wpld * i) /\ (wpld * i) <= (wpld * h) - wpld)%Z.
  Proof. intros i Hi. nia. Qed.

  Lemma wr_readable_v10 : wr_readable SEGS.
  Proof.
    intros seg Hin Hwr. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  #[local] Abbreviation MInv := (dwa_MInv M datad DN sp 168) (only parsing).
  #[local] Abbreviation cell := (dwa_cell SEGS sp) (only parsing).
  (* [comment removed for export] *)
  #[local] Abbreviation DWA_EN := (fun (regs : bvmap 5 word) (Mi : word -> option byte) =>
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 h) /\ cell Mi 144 (Z_to_bv 64 wpld) /\ cell Mi 152 (Z_to_bv 64 datad) /\ cell Mi 160 (Z_to_bv 64 datas) /\
    getr regs 2 = Z_to_bv 64 sp /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\
    getr regs 11 = Z_to_bv 64 w /\ getr regs 13 = Z_to_bv 64 wpld /\ getr regs 14 = Z_to_bv 64 datas /\ getr regs 15 = Z_to_bv 64 wpls) (only parsing).
  #[local] Abbreviation DWA_EX := (dwa_EX M datad DN sp 168 gpv tpv) (only parsing).
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
    MInv Mi -> (0 <= off)%Z -> (off + Z.of_nat (length bs) <= 168)%Z -> MInv (wbytes Mi (Z_to_bv 64 (sp + off)) bs).
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
    destruct (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) wr_readable_v10) as (bs & Hbs & Lbs).
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
      ltac:(store_ok_peel; eapply store_ok_mono; [ grows | lazymatch goal with HG : mem_grows M ?mi |- _ => apply (sok_in mi sp (sp + off) 168 8 HG SOKf) end; [lia | lia | cbn; lia] ]).
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
  Lemma zbv_shift : forall a k : Z, Z_to_bv 64 (a + k * 2 ^ 64) = Z_to_bv 64 a.
  Proof. intros a k. apply bv_eq. rewrite !u_Z2bv_mod. apply Z.mod_add. lia. Qed.
  Lemma sltu_lt : forall a b : Z, (0 <= a < b)%Z -> (b < 2 ^ 64)%Z -> v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
  Proof. intros a b H1 H2. rewrite v_sltu_Z by lia. replace (a <? b)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
  Lemma slti_lt : forall a i : Z, (0 <= a < i)%Z -> (a < 2 ^ 63)%Z -> v_slti (Z_to_bv 64 a) i = Z_to_bv 64 1.
  Proof. intros a i H1 H2. rewrite v_slti_Z by lia. replace (a <? i)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
  Lemma slti_ge : forall a i : Z, (i <= a < 2 ^ 63)%Z -> (0 <= a)%Z -> v_slti (Z_to_bv 64 a) i = Z_to_bv 64 0.
  Proof. intros a i H1 H2. rewrite v_slti_Z by lia. replace (a <? i)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
  Ltac knorm := rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul.
  Ltac zvn F D v := sn F D; fixv v ltac:(knorm; lazymatch goal with |- Z_to_bv 64 ?x = Z_to_bv 64 ?y =>
                      first [ (replace y with (x + 1 * 2 ^ 64)%Z by lia; symmetry; apply zbv_shift) | (replace y with (x + (-1) * 2 ^ 64)%Z by lia; symmetry; apply zbv_shift) ] end).
  Ltac zvneg F D v := sn F D; fixv v ltac:(first [ (rewrite zbv_neg by lia; f_equal; lia)
                      | (knorm; lazymatch goal with |- Z_to_bv 64 ?x = Z_to_bv 64 ?y => replace y with (x + 1 * 2 ^ 64)%Z by lia; symmetry; apply zbv_shift end) ]).
  Ltac kclosed F D c := sn F D; fixv (Z_to_bv 64 c) ltac:(first [ reflexivity | apply bv_eq; reflexivity ]).
  Ltac lineg F D c := kclosed F D c.
  Ltac kli F D c := kclosed F D c.
  Ltac andi3 F D := sn F D; fixv (Z_to_bv 64 0) ltac:(rewrite andi_3, u_Z2bv by lia; first [rewrite Hals | rewrite Hald]; reflexivity).
  Ltac seqzx F D c := sn F D; fixv (Z_to_bv 64 0) ltac:(apply xor_seqz_ne; lia).
  Ltac seqz_nz F D c := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_seqz_nz; lia).
  Ltac seqz_z F D c := kclosed F D c.
  Ltac snez_nz F D c := sn F D; fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
  Ltac snez_z F D c := kclosed F D c.
  Ltac sltu_1 F D c := sn F D; fixv (Z_to_bv 64 1) ltac:(apply sltu_lt; lia).
  Ltac sltu_0 F D c := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
  Ltac slti_1 F D c := sn F D; fixv (Z_to_bv 64 1) ltac:(apply slti_lt; lia).
  Ltac slti_0 F D c := sn F D; fixv (Z_to_bv 64 0) ltac:(apply slti_ge; lia).
  Ltac condR := pin; first [ apply c_eq_refl | (cbn; rewrite ?c_eq_refl; reflexivity) | vm_compute; reflexivity ].

  (* [comment removed for export] *)
  Definition k8_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 13 = (Z_to_bv 64 (i)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k8_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k8_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 13 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k8_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).

  Definition k8_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 13 = (Z_to_bv 64 (0)) /\ getr regs 14 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 15 = (Z_to_bv 64 (wpls)).
  Lemma k8_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2f4 : word) Mi rom) (mkst regs' (0x2a334 : word) M' rom) /\ k8_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      kli F_2a1f8 D_2a1f8 1073741824%Z.   (* [comment removed for export] *)
      zvaddw F_2a1fc D_2a1fc (Z_to_bv 64 (wpls + 1073741824)).   (* [comment removed for export] *)
      stepb_ft F_2a200 D_2a200 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_2a204 D_2a204 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_2a208 D_2a208 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_ft F_2a20c D_2a20c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a210 D_2a210 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_2a214 D_2a214 ltac:(condZ).   (* [comment removed for export] *)
      stf F_2a218 D_2a218 96%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stf F_2a21c D_2a21c 80%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_2a220 D_2a220.   (* [comment removed for export] *)
      zvslw F_2a224 D_2a224 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      ldf F_2a228 D_2a228 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_2a22c D_2a22c.   (* [comment removed for export] *)
      stf F_2a230 D_2a230 64%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_2a234 D_2a234 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_pre_c1. kpost.
  Qed.

  Definition k8_pre_c2 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 11 = (Z_to_bv 64 (datas)) /\ getr regs 12 = (Z_to_bv 64 (8 * wpls)) /\ getr regs 13 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_pre_s1 : forall regs Mi, k8_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x2a334 : word) Mi rom) (mkst regs' (0x2a374 : word) M' rom) /\ k8_pre_c2 regs' M'.
  Proof.
    intros regs Mi  HF. unfold k8_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      ldf F_2a238 D_2a238 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_2a23c D_2a23c.   (* [comment removed for export] *)
      stf F_2a240 D_2a240 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_2a244 D_2a244 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_2a248 D_2a248.   (* [comment removed for export] *)
      stf F_2a24c D_2a24c 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_2a250 D_2a250.   (* [comment removed for export] *)
      zv F_2a254 D_2a254 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      stf F_2a258 D_2a258 128%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      zvsl F_2a25c D_2a25c (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_2a260 D_2a260 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_2a264 D_2a264 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_2a268 D_2a268 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_2a26c D_2a26c 40%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a270 D_2a270 (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      stf F_2a274 D_2a274 32%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_pre_c2. kpost.
  Qed.

  Lemma k8_pre_s2 : forall regs Mi, k8_pre_c2 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x2a374 : word) Mi rom) (mkst regs' (0x2a3bc : word) M' rom) /\ k8_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k8_pre_c2 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvn F_2a278 D_2a278 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_2a27c D_2a27c 24%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_2a280 D_2a280 56%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zvneg F_2a284 D_2a284 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_2a288 D_2a288 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      lineg F_2a28c D_2a28c 18446744073709551611%Z.   (* [comment removed for export] *)
      sn F_2a290 D_2a290.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RH. kpost.
  Qed.

  Lemma k8_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2f4 : word) Mi rom) (mkst regs' (0x2a3bc : word) M' rom) /\ k8_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k8_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k8_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    destruct (k8_pre_s2 r2 M2  H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k8_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k8_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a3bc : word) Mi rom) (mkst regs' (0x2a3fc : word) M' rom) /\ k8_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k8_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_2a2c0 D_2a2c0 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stf F_2a2c4 D_2a2c4 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvmulw F_2a2c8 D_2a2c8 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_2a2cc D_2a2cc ltac:(condR).   (* [comment removed for export] *)
      ldf F_2a2d0 D_2a2d0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      snez_nz F_2a2d4 D_2a2d4 1%Z.   (* [comment removed for export] *)
      zvw F_2a2d8 D_2a2d8 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_2a2dc D_2a2dc (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_2a2e0 D_2a2e0 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_2a2e4 D_2a2e4 0%Z.   (* [comment removed for export] *)
      stepb_ft F_2a2e8 D_2a2e8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a2ec D_2a2ec 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_2a2f0 D_2a2f0 0%Z.   (* [comment removed for export] *)
      slti_0 F_2a2f4 D_2a2f4 0%Z.   (* [comment removed for export] *)
      kclosed F_2a2f8 D_2a2f8 0%Z.   (* [comment removed for export] *)
      kclosed F_2a2fc D_2a2fc 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_rowset_c1. kpost.
  Qed.

  Definition k8_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k8_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a3fc : word) Mi rom) (mkst regs' (0x2a43c : word) M' rom) /\ k8_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k8_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2a300 D_2a300 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a304 D_2a304 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_2a308 D_2a308 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zv F_2a30c D_2a30c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_2a310 D_2a310 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_ft F_2a314 D_2a314 ltac:(condR).   (* [comment removed for export] *)
      ldf F_2a318 D_2a318 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_2a31c D_2a31c 1%Z.   (* [comment removed for export] *)
      zvw F_2a320 D_2a320 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_2a324 D_2a324 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_2a328 D_2a328 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_2a32c D_2a32c 0%Z.   (* [comment removed for export] *)
      stepb_ft F_2a330 D_2a330 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a334 D_2a334 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_2a338 D_2a338 0%Z.   (* [comment removed for export] *)
      slti_0 F_2a33c D_2a33c 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_rowset_c2. kpost.
  Qed.

  Definition k8_rowset_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * (i * wpls))) /\ getr regs 13 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k8_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a43c : word) Mi rom) (mkst regs' (0x2a47c : word) M' rom) /\ k8_rowset_c3 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k8_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      kclosed F_2a340 D_2a340 0%Z.   (* [comment removed for export] *)
      kclosed F_2a344 D_2a344 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a348 D_2a348 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a34c D_2a34c 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_2a350 D_2a350.   (* [comment removed for export] *)
      stepb_ft F_2a354 D_2a354 ltac:(condZ).   (* [comment removed for export] *)
      sn F_2a358 D_2a358.   (* [comment removed for export] *)
      ldf F_2a35c D_2a35c 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_2a360 D_2a360 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_2a364 D_2a364 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_2a368 D_2a368 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_2a36c D_2a36c 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_2a370 D_2a370 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      stf F_2a374 D_2a374 136%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_2a378 D_2a378 56%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_2a37c D_2a37c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_rowset_c3. kpost.
  Qed.

  Lemma k8_rowset_s3 : forall regs Mi i, (0 <= i < h)%Z -> k8_rowset_c3 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a47c : word) Mi rom) (mkst regs' (0x2a4b0 : word) M' rom) /\ k8_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k8_rowset_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_2a380 D_2a380 32%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_2a384 D_2a384 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a388 D_2a388 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_2a38c D_2a38c (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a390 D_2a390 24%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a394 D_2a394 (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a398 D_2a398 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_2a39c D_2a39c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a3a0 D_2a3a0 40%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a3a4 D_2a3a4 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a3a8 D_2a3a8 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a3ac D_2a3ac (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a3b0 D_2a3b0 64%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_IN. kpost.
  Qed.

  Lemma k8_rowset : forall regs Mi i, (0 <= i < h)%Z -> k8_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a3bc : word) Mi rom) (mkst regs' (0x2a4b0 : word) M' rom) /\ k8_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k8_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k8_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k8_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k8_rowset_s3 r3 M3 i HR0 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Definition k8_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 10 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a4b0 : word) Mi rom) (mkst regs' (0x2a4f0 : word) M' rom) /\ k8_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_2a3b4 D_2a3b4 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_2a3b8 D_2a3b8.   (* [comment removed for export] *)
      snez_nz F_2a3bc D_2a3bc 1%Z.   (* [comment removed for export] *)
      seqzx F_2a3c0 D_2a3c0 0%Z.   (* [comment removed for export] *)
      stepb_ft F_2a3c4 D_2a3c4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a3c8 D_2a3c8 128%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      slti_0 F_2a3cc D_2a3cc 0%Z.   (* [comment removed for export] *)
      zv F_2a3d0 D_2a3d0 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_2a3d4 D_2a3d4 1%Z.   (* [comment removed for export] *)
      kclosed F_2a3d8 D_2a3d8 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a3dc D_2a3dc ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a3e0 D_2a3e0 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a3e4 D_2a3e4 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_2a3e8 D_2a3e8 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_2a3ec D_2a3ec ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a3f0 D_2a3f0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c1. kpost.
  Qed.

  Definition k8_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 10 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 24 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a4f0 : word) Mi rom) (mkst regs' (0x2a530 : word) M' rom) /\ k8_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2a3f4 D_2a3f4 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_2a3f8 D_2a3f8 0%Z.   (* [comment removed for export] *)
      zv F_2a3fc D_2a3fc (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_2a400 D_2a400 1%Z.   (* [comment removed for export] *)
      kclosed F_2a404 D_2a404 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a408 D_2a408 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a40c D_2a40c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a410 D_2a410 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a414 D_2a414 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a418 D_2a418 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a41c D_2a41c ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_2a420 D_2a420 0%Z.   (* [comment removed for export] *)
      zv F_2a424 D_2a424 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_2a428 D_2a428 0%Z.   (* [comment removed for export] *)
      kclosed F_2a42c D_2a42c 0%Z.   (* [comment removed for export] *)
      kclosed F_2a430 D_2a430 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c2. kpost.
  Qed.

  Definition k8_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a530 : word) Mi rom) (mkst regs' (0x2a570 : word) M' rom) /\ k8_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    eexists. eexists. split.
    -
      stepb_ft F_2a434 D_2a434 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a438 D_2a438 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a43c D_2a43c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a440 D_2a440 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_2a444 D_2a444 ltac:(condR).   (* [comment removed for export] *)
      ldf F_2a448 D_2a448 136%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_2a44c D_2a44c (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_2a450 D_2a450 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_2a454 D_2a454 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2a458 D_2a458 bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_2a45c D_2a45c bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2a460 D_2a460 bs3 v3 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_2a464 D_2a464 bs4 v4 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_2a468 D_2a468 bs5 v5 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_2a46c D_2a46c bs6 v6 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_2a470 D_2a470 bs7 v7 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c3. kpost.
  Qed.

  Definition k8_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a570 : word) Mi rom) (mkst regs' (0x2a5b0 : word) M' rom) /\ k8_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c3 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    eexists. eexists. split.
    -
      stepLD F_2a474 D_2a474 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2a478 D_2a478 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_2a47c D_2a47c bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2a480 D_2a480 bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      sn F_2a484 D_2a484.   (* [comment removed for export] *)
      sn F_2a488 D_2a488.   (* [comment removed for export] *)
      sn F_2a48c D_2a48c.   (* [comment removed for export] *)
      sn F_2a490 D_2a490.   (* [comment removed for export] *)
      sn F_2a494 D_2a494.   (* [comment removed for export] *)
      sn F_2a498 D_2a498.   (* [comment removed for export] *)
      sn F_2a49c D_2a49c.   (* [comment removed for export] *)
      sn F_2a4a0 D_2a4a0.   (* [comment removed for export] *)
      sn F_2a4a4 D_2a4a4.   (* [comment removed for export] *)
      sn F_2a4a8 D_2a4a8.   (* [comment removed for export] *)
      sn F_2a4ac D_2a4ac.   (* [comment removed for export] *)
      sn F_2a4b0 D_2a4b0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c4. kpost.
  Qed.

  Definition k8_iter_c5 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a5b0 : word) Mi rom) (mkst regs' (0x2a5f0 : word) M' rom) /\ k8_iter_c5 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a4b4 D_2a4b4.   (* [comment removed for export] *)
      sn F_2a4b8 D_2a4b8.   (* [comment removed for export] *)
      sn F_2a4bc D_2a4bc.   (* [comment removed for export] *)
      sn F_2a4c0 D_2a4c0.   (* [comment removed for export] *)
      sn F_2a4c4 D_2a4c4.   (* [comment removed for export] *)
      sn F_2a4c8 D_2a4c8.   (* [comment removed for export] *)
      sn F_2a4cc D_2a4cc.   (* [comment removed for export] *)
      sn F_2a4d0 D_2a4d0.   (* [comment removed for export] *)
      sn F_2a4d4 D_2a4d4.   (* [comment removed for export] *)
      sn F_2a4d8 D_2a4d8.   (* [comment removed for export] *)
      sn F_2a4dc D_2a4dc.   (* [comment removed for export] *)
      sn F_2a4e0 D_2a4e0.   (* [comment removed for export] *)
      sn F_2a4e4 D_2a4e4.   (* [comment removed for export] *)
      sn F_2a4e8 D_2a4e8.   (* [comment removed for export] *)
      sn F_2a4ec D_2a4ec.   (* [comment removed for export] *)
      sn F_2a4f0 D_2a4f0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c5. kpost.
  Qed.

  Definition k8_iter_c6 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 9 = (Z_to_bv 64 (PW - j)) /\ getr regs 13 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 26 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k8_iter_s5 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c5 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a5f0 : word) Mi rom) (mkst regs' (0x2a630 : word) M' rom) /\ k8_iter_c6 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c5 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a4f4 D_2a4f4.   (* [comment removed for export] *)
      sn F_2a4f8 D_2a4f8.   (* [comment removed for export] *)
      sn F_2a4fc D_2a4fc.   (* [comment removed for export] *)
      sn F_2a500 D_2a500.   (* [comment removed for export] *)
      sn F_2a504 D_2a504.   (* [comment removed for export] *)
      sn F_2a508 D_2a508.   (* [comment removed for export] *)
      sn F_2a50c D_2a50c.   (* [comment removed for export] *)
      sn F_2a510 D_2a510.   (* [comment removed for export] *)
      sn F_2a514 D_2a514.   (* [comment removed for export] *)
      sn F_2a518 D_2a518.   (* [comment removed for export] *)
      sn F_2a51c D_2a51c.   (* [comment removed for export] *)
      sn F_2a520 D_2a520.   (* [comment removed for export] *)
      sn F_2a524 D_2a524.   (* [comment removed for export] *)
      sn F_2a528 D_2a528.   (* [comment removed for export] *)
      sn F_2a52c D_2a52c.   (* [comment removed for export] *)
      sn F_2a530 D_2a530.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_iter_c6. kpost.
  Qed.

  Lemma k8_iter_s6 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_iter_c6 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a630 : word) Mi rom) (mkst regs' (0x2a668 : word) M' rom) /\ k8_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k8_iter_c6 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a534 D_2a534.   (* [comment removed for export] *)
      sn F_2a538 D_2a538.   (* [comment removed for export] *)
      sn F_2a53c D_2a53c.   (* [comment removed for export] *)
      sn F_2a540 D_2a540.   (* [comment removed for export] *)
      sn F_2a544 D_2a544.   (* [comment removed for export] *)
      sn F_2a548 D_2a548.   (* [comment removed for export] *)
      sn F_2a54c D_2a54c.   (* [comment removed for export] *)
      sn F_2a550 D_2a550.   (* [comment removed for export] *)
      sn F_2a554 D_2a554.   (* [comment removed for export] *)
      sn F_2a558 D_2a558.   (* [comment removed for export] *)
      gsw F_2a55c D_2a55c (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_ft F_2a560 D_2a560 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_2a564 D_2a564 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_2a568 D_2a568 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_BN. kpost.
  Qed.

  Lemma k8_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k8_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a4b0 : word) Mi rom) (mkst regs' (0x2a668 : word) M' rom) /\ k8_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k8_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k8_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k8_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k8_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k8_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    destruct (k8_iter_s5 r5 M5 i j HR0 HR1 H5) as (r6 & M6 & RUN6 & H6).
    destruct (k8_iter_s6 r6 M6 i j HR0 HR1 H6) as (r7 & M7 & RUN7 & H7).
    exists r7, M7. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]] | exact H7].
  Qed.

  Lemma k8_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k8_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a668 : word) Mi rom) (mkst regs' (0x2a4b0 : word) M' rom) /\ k8_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k8_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_2a56c D_2a56c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_IN. kpost.
  Qed.

  Lemma k8_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k8_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a668 : word) Mi rom) (mkst regs' (0x2a390 : word) M' rom) /\ k8_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k8_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2a56c D_2a56c ltac:(condZ).   (* [comment removed for export] *)
      sn F_2a570 D_2a570.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RL. kpost.
  Qed.

  Lemma k8_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k8_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a390 : word) Mi rom) (mkst regs' (0x2a3bc : word) M' rom) /\ k8_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k8_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_2a294 D_2a294 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_2a298 D_2a298 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_2a29c D_2a29c 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_2a2a0 D_2a2a0 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_2a2a4 D_2a2a4 80%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a2a8 D_2a2a8 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_2a2ac D_2a2ac 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_2a2b0 D_2a2b0 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_2a2b4 D_2a2b4 96%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_2a2b8 D_2a2b8 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_2a2bc D_2a2bc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k8_RH. kpost.
  Qed.

  Lemma k8_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k8_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a390 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k8_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_2a294 D_2a294 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_2a298 D_2a298 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_2a29c D_2a29c 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_2a2a0 D_2a2a0 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_2a2a4 D_2a2a4 80%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a2a8 D_2a2a8 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_2a2ac D_2a2ac 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_2a2b0 D_2a2b0 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_2a2b4 D_2a2b4 96%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_2a2b8 D_2a2b8 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_2a2bc D_2a2bc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k8_inner : forall regs Mi i, (0 <= i < h)%Z -> k8_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x2a4b0 : word) Mi rom) (mkst regs' (0x2a390 : word) M' rom) /\ k8_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x2a4b0 : word) (0x2a390 : word) (fun r m j => k8_IN r m i j) (fun r m => k8_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k8_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k8_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k8_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k8_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2f4 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k8_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x2a3bc : word) (0x2a670 : word) (fun r m i => k8_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k8_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k8_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k8_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k8_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k9_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 14 = (Z_to_bv 64 (i)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k9_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k9_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k9_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).

  Definition k9_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 13 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)).
  Lemma k9_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28dc8 : word) Mi rom) (mkst regs' (0x28e14 : word) M' rom) /\ k9_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      kli F_28ccc D_28ccc 1073741824%Z.   (* [comment removed for export] *)
      zvaddw F_28cd0 D_28cd0 (Z_to_bv 64 (wpls + 1073741824)).   (* [comment removed for export] *)
      stepb_tk F_28cd4 D_28cd4 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_28cdc D_28cdc (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_28ce0 D_28ce0 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_28ce4 D_28ce4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28cec D_28cec 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_28cf0 D_28cf0 ltac:(condZ).   (* [comment removed for export] *)
      stf F_28cf8 D_28cf8 96%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stf F_28cfc D_28cfc 80%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_28d00 D_28d00.   (* [comment removed for export] *)
      zvslw F_28d04 D_28d04 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      ldf F_28d08 D_28d08 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_28d0c D_28d0c.   (* [comment removed for export] *)
      stf F_28d10 D_28d10 64%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_28d14 D_28d14 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_pre_c1. kpost.
  Qed.

  Definition k9_pre_c2 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 11 = (Z_to_bv 64 (datas)) /\ getr regs 12 = (Z_to_bv 64 (18446744073709551615)) /\ getr regs 13 = (Z_to_bv 64 (8 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_pre_s1 : forall regs Mi, k9_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28e14 : word) Mi rom) (mkst regs' (0x28e54 : word) M' rom) /\ k9_pre_c2 regs' M'.
  Proof.
    intros regs Mi  HF. unfold k9_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      ldf F_28d18 D_28d18 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_28d1c D_28d1c.   (* [comment removed for export] *)
      stf F_28d20 D_28d20 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_28d24 D_28d24 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_28d28 D_28d28.   (* [comment removed for export] *)
      stf F_28d2c D_28d2c 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_28d30 D_28d30.   (* [comment removed for export] *)
      lineg F_28d34 D_28d34 18446744073709551611%Z.   (* [comment removed for export] *)
      lineg F_28d38 D_28d38 18446744073709551615%Z.   (* [comment removed for export] *)
      zv F_28d3c D_28d3c (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      stf F_28d40 D_28d40 128%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      zvsl F_28d44 D_28d44 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_28d48 D_28d48 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_28d4c D_28d4c 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_28d50 D_28d50 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_28d54 D_28d54 40%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_pre_c2. kpost.
  Qed.

  Lemma k9_pre_s2 : forall regs Mi, k9_pre_c2 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28e54 : word) Mi rom) (mkst regs' (0x28ea8 : word) M' rom) /\ k9_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k9_pre_c2 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zv F_28d58 D_28d58 (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      stf F_28d5c D_28d5c 32%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zvn F_28d60 D_28d60 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_28d64 D_28d64 24%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_28d68 D_28d68 56%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zvneg F_28d6c D_28d6c (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_28d70 D_28d70 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_28d74 D_28d74.   (* [comment removed for export] *)
      sn F_28d78 D_28d78.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RH. kpost.
  Qed.

  Lemma k9_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28dc8 : word) Mi rom) (mkst regs' (0x28ea8 : word) M' rom) /\ k9_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k9_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k9_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    destruct (k9_pre_s2 r2 M2  H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k9_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k9_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28ea8 : word) Mi rom) (mkst regs' (0x28ef0 : word) M' rom) /\ k9_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k9_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28dac D_28dac (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stf F_28db0 D_28db0 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvmulw F_28db4 D_28db4 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_28db8 D_28db8 ltac:(condR).   (* [comment removed for export] *)
      ldf F_28dc0 D_28dc0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      snez_nz F_28dc4 D_28dc4 1%Z.   (* [comment removed for export] *)
      zvw F_28dc8 D_28dc8 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_28dcc D_28dcc (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_28dd0 D_28dd0 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_28dd4 D_28dd4 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28dd8 D_28dd8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28de0 D_28de0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_28de4 D_28de4 0%Z.   (* [comment removed for export] *)
      slti_0 F_28de8 D_28de8 0%Z.   (* [comment removed for export] *)
      kclosed F_28dec D_28dec 0%Z.   (* [comment removed for export] *)
      kclosed F_28df0 D_28df0 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_rowset_c1. kpost.
  Qed.

  Definition k9_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k9_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28ef0 : word) Mi rom) (mkst regs' (0x28f3c : word) M' rom) /\ k9_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k9_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_28df4 D_28df4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28dfc D_28dfc 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_28e00 D_28e00 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zv F_28e04 D_28e04 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_28e08 D_28e08 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_tk F_28e0c D_28e0c ltac:(condR).   (* [comment removed for export] *)
      ldf F_28e14 D_28e14 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_28e18 D_28e18 1%Z.   (* [comment removed for export] *)
      zvw F_28e1c D_28e1c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_28e20 D_28e20 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_28e24 D_28e24 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_28e28 D_28e28 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28e2c D_28e2c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28e34 D_28e34 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_28e38 D_28e38 0%Z.   (* [comment removed for export] *)
      slti_0 F_28e3c D_28e3c 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_rowset_c2. kpost.
  Qed.

  Definition k9_rowset_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k9_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28f3c : word) Mi rom) (mkst regs' (0x28f80 : word) M' rom) /\ k9_rowset_c3 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k9_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      kclosed F_28e40 D_28e40 0%Z.   (* [comment removed for export] *)
      kclosed F_28e44 D_28e44 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28e48 D_28e48 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28e50 D_28e50 72%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_28e54 D_28e54.   (* [comment removed for export] *)
      stepb_ft F_28e58 D_28e58 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28e5c D_28e5c.   (* [comment removed for export] *)
      ldf F_28e60 D_28e60 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_28e64 D_28e64 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_28e68 D_28e68 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_28e6c D_28e6c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_28e70 D_28e70 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_28e74 D_28e74 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      stf F_28e78 D_28e78 136%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_28e7c D_28e7c 56%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_28e80 D_28e80 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_rowset_c3. kpost.
  Qed.

  Lemma k9_rowset_s3 : forall regs Mi i, (0 <= i < h)%Z -> k9_rowset_c3 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28f80 : word) Mi rom) (mkst regs' (0x28fb4 : word) M' rom) /\ k9_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k9_rowset_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_28e84 D_28e84 32%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_28e88 D_28e88 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_28e8c D_28e8c 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_28e90 D_28e90 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_28e94 D_28e94 24%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_28e98 D_28e98 (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_28e9c D_28e9c 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_28ea0 D_28ea0 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_28ea4 D_28ea4 40%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_28ea8 D_28ea8 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_28eac D_28eac 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_28eb0 D_28eb0 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_28eb4 D_28eb4 64%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_IN. kpost.
  Qed.

  Lemma k9_rowset : forall regs Mi i, (0 <= i < h)%Z -> k9_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28ea8 : word) Mi rom) (mkst regs' (0x28fb4 : word) M' rom) /\ k9_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k9_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k9_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k9_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k9_rowset_s3 r3 M3 i HR0 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Definition k9_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28fb4 : word) Mi rom) (mkst regs' (0x2900c : word) M' rom) /\ k9_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28eb8 D_28eb8 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_28ebc D_28ebc.   (* [comment removed for export] *)
      snez_nz F_28ec0 D_28ec0 1%Z.   (* [comment removed for export] *)
      seqzx F_28ec4 D_28ec4 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28ec8 D_28ec8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28ed0 D_28ed0 128%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      slti_0 F_28ed4 D_28ed4 0%Z.   (* [comment removed for export] *)
      zv F_28ed8 D_28ed8 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_28edc D_28edc 1%Z.   (* [comment removed for export] *)
      kclosed F_28ee0 D_28ee0 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28ee4 D_28ee4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28eec D_28eec ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28ef4 D_28ef4 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_tk F_28ef8 D_28ef8 ltac:(condR).   (* [comment removed for export] *)
      stepb_tk F_28f00 D_28f00 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f08 D_28f08 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c1. kpost.
  Qed.

  Definition k9_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 22 = (Z_to_bv 64 (1)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2900c : word) Mi rom) (mkst regs' (0x29068 : word) M' rom) /\ k9_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_28f10 D_28f10 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28f18 D_28f18 0%Z.   (* [comment removed for export] *)
      zv F_28f1c D_28f1c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_28f20 D_28f20 1%Z.   (* [comment removed for export] *)
      kclosed F_28f24 D_28f24 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28f28 D_28f28 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f30 D_28f30 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f38 D_28f38 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f40 D_28f40 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f48 D_28f48 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f50 D_28f50 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28f58 D_28f58 0%Z.   (* [comment removed for export] *)
      zv F_28f5c D_28f5c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_28f60 D_28f60 0%Z.   (* [comment removed for export] *)
      kclosed F_28f64 D_28f64 0%Z.   (* [comment removed for export] *)
      kclosed F_28f68 D_28f68 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c2. kpost.
  Qed.

  Definition k9_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29068 : word) Mi rom) (mkst regs' (0x290bc : word) M' rom) /\ k9_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs7 & v7 & Hb7 & Hv7).
    eexists. eexists. split.
    -
      stepb_tk F_28f6c D_28f6c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f74 D_28f74 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28f7c D_28f7c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28f84 D_28f84 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_tk F_28f88 D_28f88 ltac:(condR).   (* [comment removed for export] *)
      ldf F_28f90 D_28f90 136%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_28f94 D_28f94 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_tk F_28f98 D_28f98 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_28fa0 D_28fa0 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_28fa4 D_28fa4 bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_28fa8 D_28fa8 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_28fac D_28fac bs3 v3 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_28fb0 D_28fb0 bs4 v4 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_28fb4 D_28fb4 bs5 v5 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_28fb8 D_28fb8 bs6 v6 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      stepLD F_28fbc D_28fbc bs7 v7 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb7) ltac:(exact Hv7).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c3. kpost.
  Qed.

  Definition k9_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x290bc : word) Mi rom) (mkst regs' (0x290fc : word) M' rom) /\ k9_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_28fc0 D_28fc0.   (* [comment removed for export] *)
      sn F_28fc4 D_28fc4.   (* [comment removed for export] *)
      sn F_28fc8 D_28fc8.   (* [comment removed for export] *)
      sn F_28fcc D_28fcc.   (* [comment removed for export] *)
      sn F_28fd0 D_28fd0.   (* [comment removed for export] *)
      sn F_28fd4 D_28fd4.   (* [comment removed for export] *)
      sn F_28fd8 D_28fd8.   (* [comment removed for export] *)
      sn F_28fdc D_28fdc.   (* [comment removed for export] *)
      sn F_28fe0 D_28fe0.   (* [comment removed for export] *)
      sn F_28fe4 D_28fe4.   (* [comment removed for export] *)
      sn F_28fe8 D_28fe8.   (* [comment removed for export] *)
      sn F_28fec D_28fec.   (* [comment removed for export] *)
      sn F_28ff0 D_28ff0.   (* [comment removed for export] *)
      sn F_28ff4 D_28ff4.   (* [comment removed for export] *)
      sn F_28ff8 D_28ff8.   (* [comment removed for export] *)
      sn F_28ffc D_28ffc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c4. kpost.
  Qed.

  Definition k9_iter_c5 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 25 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x290fc : word) Mi rom) (mkst regs' (0x2913c : word) M' rom) /\ k9_iter_c5 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c4 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    eexists. eexists. split.
    -
      sn F_29000 D_29000.   (* [comment removed for export] *)
      sn F_29004 D_29004.   (* [comment removed for export] *)
      sn F_29008 D_29008.   (* [comment removed for export] *)
      sn F_2900c D_2900c.   (* [comment removed for export] *)
      stepLD F_29010 D_29010 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29014 D_29014 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29018 D_29018 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2901c D_2901c bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      sn F_29020 D_29020.   (* [comment removed for export] *)
      sn F_29024 D_29024.   (* [comment removed for export] *)
      sn F_29028 D_29028.   (* [comment removed for export] *)
      sn F_2902c D_2902c.   (* [comment removed for export] *)
      sn F_29030 D_29030.   (* [comment removed for export] *)
      sn F_29034 D_29034.   (* [comment removed for export] *)
      sn F_29038 D_29038.   (* [comment removed for export] *)
      sn F_2903c D_2903c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c5. kpost.
  Qed.

  Definition k9_iter_c6 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (PW)) /\ cell Mi 72 (Z_to_bv 64 (w + 31)) /\ cell Mi 80 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 104 (Z_to_bv 64 (i)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 19 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (PW - j)) /\ getr regs 25 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k9_iter_s5 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c5 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2913c : word) Mi rom) (mkst regs' (0x2917c : word) M' rom) /\ k9_iter_c6 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c5 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_29040 D_29040.   (* [comment removed for export] *)
      sn F_29044 D_29044.   (* [comment removed for export] *)
      sn F_29048 D_29048.   (* [comment removed for export] *)
      sn F_2904c D_2904c.   (* [comment removed for export] *)
      sn F_29050 D_29050.   (* [comment removed for export] *)
      sn F_29054 D_29054.   (* [comment removed for export] *)
      sn F_29058 D_29058.   (* [comment removed for export] *)
      sn F_2905c D_2905c.   (* [comment removed for export] *)
      sn F_29060 D_29060.   (* [comment removed for export] *)
      sn F_29064 D_29064.   (* [comment removed for export] *)
      sn F_29068 D_29068.   (* [comment removed for export] *)
      sn F_2906c D_2906c.   (* [comment removed for export] *)
      sn F_29070 D_29070.   (* [comment removed for export] *)
      sn F_29074 D_29074.   (* [comment removed for export] *)
      sn F_29078 D_29078.   (* [comment removed for export] *)
      sn F_2907c D_2907c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_iter_c6. kpost.
  Qed.

  Lemma k9_iter_s6 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_iter_c6 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2917c : word) Mi rom) (mkst regs' (0x291b8 : word) M' rom) /\ k9_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k9_iter_c6 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_29080 D_29080.   (* [comment removed for export] *)
      sn F_29084 D_29084.   (* [comment removed for export] *)
      sn F_29088 D_29088.   (* [comment removed for export] *)
      sn F_2908c D_2908c.   (* [comment removed for export] *)
      sn F_29090 D_29090.   (* [comment removed for export] *)
      sn F_29094 D_29094.   (* [comment removed for export] *)
      sn F_29098 D_29098.   (* [comment removed for export] *)
      sn F_2909c D_2909c.   (* [comment removed for export] *)
      sn F_290a0 D_290a0.   (* [comment removed for export] *)
      sn F_290a4 D_290a4.   (* [comment removed for export] *)
      gsw F_290a8 D_290a8 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_tk F_290ac D_290ac ltac:(condZ).   (* [comment removed for export] *)
      zvw F_290b4 D_290b4 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_290b8 D_290b8 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_BN. kpost.
  Qed.

  Lemma k9_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k9_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28fb4 : word) Mi rom) (mkst regs' (0x291b8 : word) M' rom) /\ k9_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k9_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k9_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k9_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k9_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k9_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    destruct (k9_iter_s5 r5 M5 i j HR0 HR1 H5) as (r6 & M6 & RUN6 & H6).
    destruct (k9_iter_s6 r6 M6 i j HR0 HR1 H6) as (r7 & M7 & RUN7 & H7).
    exists r7, M7. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]] | exact H7].
  Qed.

  Lemma k9_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k9_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x291b8 : word) Mi rom) (mkst regs' (0x28fb4 : word) M' rom) /\ k9_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k9_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_290bc D_290bc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_IN. kpost.
  Qed.

  Lemma k9_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k9_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x291b8 : word) Mi rom) (mkst regs' (0x28e78 : word) M' rom) /\ k9_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k9_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_290bc D_290bc ltac:(condZ).   (* [comment removed for export] *)
      sn F_290c0 D_290c0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RL. kpost.
  Qed.

  Lemma k9_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k9_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28e78 : word) Mi rom) (mkst regs' (0x28ea8 : word) M' rom) /\ k9_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k9_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_28d7c D_28d7c 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_28d80 D_28d80 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_28d84 D_28d84 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_28d88 D_28d88 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_28d8c D_28d8c 80%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_28d90 D_28d90 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_28d94 D_28d94 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_28d98 D_28d98 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_28d9c D_28d9c 96%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28da0 D_28da0 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_28da4 D_28da4 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k9_RH. kpost.
  Qed.

  Lemma k9_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k9_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28e78 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k9_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_28d7c D_28d7c 104%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_28d80 D_28d80 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_28d84 D_28d84 80%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_28d88 D_28d88 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_28d8c D_28d8c 80%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_28d90 D_28d90 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_28d94 D_28d94 96%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_28d98 D_28d98 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_28d9c D_28d9c 96%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28da0 D_28da0 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_28da4 D_28da4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28da8 D_28da8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k9_inner : forall regs Mi i, (0 <= i < h)%Z -> k9_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x28fb4 : word) Mi rom) (mkst regs' (0x28e78 : word) M' rom) /\ k9_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x28fb4 : word) (0x28e78 : word) (fun r m j => k9_IN r m i j) (fun r m => k9_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k9_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k9_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k9_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k9_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28dc8 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k9_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x28ea8 : word) (0x2a670 : word) (fun r m i => k9_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k9_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k9_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k9_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k9_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
