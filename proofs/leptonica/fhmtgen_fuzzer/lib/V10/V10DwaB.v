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
  Definition k4_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k4_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 19 = (Z_to_bv 64 (4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 23 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k4_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 19 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 23 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k4_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).

  Definition k4_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (datas)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)) /\ getr regs 17 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)).
  Lemma k4_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28b70 : word) Mi rom) (mkst regs' (0x28bb8 : word) M' rom) /\ k4_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvw F_28a74 D_28a74 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_28a78 D_28a78 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28a80 D_28a80 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_28a84 D_28a84 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28a8c D_28a8c.   (* [comment removed for export] *)
      sn F_28a90 D_28a90.   (* [comment removed for export] *)
      sn F_28a94 D_28a94.   (* [comment removed for export] *)
      zvpw F_28a98 D_28a98.   (* [comment removed for export] *)
      stf F_28a9c D_28a9c 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_28aa0 D_28aa0 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_28aa4 D_28aa4 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_28aa8 D_28aa8.   (* [comment removed for export] *)
      ldf F_28aac D_28aac 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_28ab0 D_28ab0.   (* [comment removed for export] *)
      snez_nz F_28ab4 D_28ab4 1%Z.   (* [comment removed for export] *)
      sn F_28ab8 D_28ab8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_pre_c1. kpost.
  Qed.

  Lemma k4_pre_s1 : forall regs Mi, k4_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28bb8 : word) Mi rom) (mkst regs' (0x28bf4 : word) M' rom) /\ k4_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k4_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zv F_28abc D_28abc (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_28ac0 D_28ac0 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_28ac4 D_28ac4 128%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_28ac8 D_28ac8 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_28acc D_28acc 120%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zvneg F_28ad0 D_28ad0 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      lineg F_28ad4 D_28ad4 18446744073709551611%Z.   (* [comment removed for export] *)
      sn F_28ad8 D_28ad8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RH. kpost.
  Qed.

  Lemma k4_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28b70 : word) Mi rom) (mkst regs' (0x28bf4 : word) M' rom) /\ k4_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k4_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k4_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Definition k4_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (wpld)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k4_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k4_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28bf4 : word) Mi rom) (mkst regs' (0x28c40 : word) M' rom) /\ k4_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k4_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28af8 D_28af8 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvmulw F_28afc D_28afc (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_28b00 D_28b00 ltac:(condR).   (* [comment removed for export] *)
      zvw F_28b08 D_28b08 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_28b0c D_28b0c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_28b10 D_28b10 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_28b14 D_28b14 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_28b18 D_28b18 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28b1c D_28b1c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28b24 D_28b24 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_28b28 D_28b28 0%Z.   (* [comment removed for export] *)
      slti_0 F_28b2c D_28b2c 0%Z.   (* [comment removed for export] *)
      kclosed F_28b30 D_28b30 0%Z.   (* [comment removed for export] *)
      kclosed F_28b34 D_28b34 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28b38 D_28b38 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28b40 D_28b40 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_rowset_c1. kpost.
  Qed.

  Definition k4_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k4_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k4_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28c40 : word) Mi rom) (mkst regs' (0x28c8c : word) M' rom) /\ k4_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k4_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28b44 D_28b44 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_28b48 D_28b48 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_tk F_28b4c D_28b4c ltac:(condR).   (* [comment removed for export] *)
      ldf F_28b54 D_28b54 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_28b58 D_28b58 1%Z.   (* [comment removed for export] *)
      zvw F_28b5c D_28b5c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_28b60 D_28b60 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_28b64 D_28b64 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_28b68 D_28b68 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28b6c D_28b6c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28b74 D_28b74 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_28b78 D_28b78 0%Z.   (* [comment removed for export] *)
      slti_0 F_28b7c D_28b7c 0%Z.   (* [comment removed for export] *)
      kclosed F_28b80 D_28b80 0%Z.   (* [comment removed for export] *)
      kclosed F_28b84 D_28b84 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28b88 D_28b88 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_rowset_c2. kpost.
  Qed.

  Lemma k4_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k4_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28c8c : word) Mi rom) (mkst regs' (0x28ccc : word) M' rom) /\ k4_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k4_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_28b90 D_28b90.   (* [comment removed for export] *)
      stepb_ft F_28b94 D_28b94 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28b98 D_28b98.   (* [comment removed for export] *)
      zvsl F_28b9c D_28b9c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_28ba0 D_28ba0 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_28ba4 D_28ba4 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_28ba8 D_28ba8 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_28bac D_28bac 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_28bb0 D_28bb0 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_28bb4 D_28bb4 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_28bb8 D_28bb8 128%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_28bbc D_28bbc (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_28bc0 D_28bc0 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_28bc4 D_28bc4 120%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_28bc8 D_28bc8 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_28bcc D_28bcc 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_IN. kpost.
  Qed.

  Lemma k4_rowset : forall regs Mi i, (0 <= i < h)%Z -> k4_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28bf4 : word) Mi rom) (mkst regs' (0x28ccc : word) M' rom) /\ k4_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k4_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k4_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k4_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k4_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 19 = (Z_to_bv 64 (4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 23 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (PW - j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 27 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k4_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28ccc : word) Mi rom) (mkst regs' (0x28d28 : word) M' rom) /\ k4_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k4_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28bd0 D_28bd0 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_28bd4 D_28bd4.   (* [comment removed for export] *)
      snez_nz F_28bd8 D_28bd8 1%Z.   (* [comment removed for export] *)
      seqzx F_28bdc D_28bdc 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28be0 D_28be0 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28be8 D_28be8 0%Z.   (* [comment removed for export] *)
      zv F_28bec D_28bec (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_28bf0 D_28bf0 1%Z.   (* [comment removed for export] *)
      kclosed F_28bf4 D_28bf4 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28bf8 D_28bf8 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c00 D_28c00 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c08 D_28c08 ltac:(condR).   (* [comment removed for export] *)
      stepb_tk F_28c10 D_28c10 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c18 D_28c18 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c20 D_28c20 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28c28 D_28c28 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_iter_c1. kpost.
  Qed.

  Definition k4_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 19 = (Z_to_bv 64 (4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 23 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (PW - j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 27 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k4_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28d28 : word) Mi rom) (mkst regs' (0x28d78 : word) M' rom) /\ k4_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k4_iter_c1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      zv F_28c2c D_28c2c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_28c30 D_28c30 0%Z.   (* [comment removed for export] *)
      kclosed F_28c34 D_28c34 0%Z.   (* [comment removed for export] *)
      kclosed F_28c38 D_28c38 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28c3c D_28c3c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c44 D_28c44 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28c4c D_28c4c ltac:(condR).   (* [comment removed for export] *)
      zv F_28c54 D_28c54 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_tk F_28c58 D_28c58 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_28c60 D_28c60 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_28c64 D_28c64 bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_28c68 D_28c68 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_28c6c D_28c6c bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_28c70 D_28c70 bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_28c74 D_28c74 bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_28c78 D_28c78.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_iter_c2. kpost.
  Qed.

  Lemma k4_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28d78 : word) Mi rom) (mkst regs' (0x28dc0 : word) M' rom) /\ k4_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k4_iter_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_28c7c D_28c7c.   (* [comment removed for export] *)
      sn F_28c80 D_28c80.   (* [comment removed for export] *)
      sn F_28c84 D_28c84.   (* [comment removed for export] *)
      sn F_28c88 D_28c88.   (* [comment removed for export] *)
      sn F_28c8c D_28c8c.   (* [comment removed for export] *)
      sn F_28c90 D_28c90.   (* [comment removed for export] *)
      sn F_28c94 D_28c94.   (* [comment removed for export] *)
      sn F_28c98 D_28c98.   (* [comment removed for export] *)
      sn F_28c9c D_28c9c.   (* [comment removed for export] *)
      sn F_28ca0 D_28ca0.   (* [comment removed for export] *)
      sn F_28ca4 D_28ca4.   (* [comment removed for export] *)
      gsw F_28ca8 D_28ca8 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_tk F_28cac D_28cac ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28cb4 D_28cb4 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_28cbc D_28cbc (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_28cc0 D_28cc0 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_BN. kpost.
  Qed.

  Lemma k4_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k4_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28ccc : word) Mi rom) (mkst regs' (0x28dc0 : word) M' rom) /\ k4_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k4_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k4_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k4_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Lemma k4_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k4_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28dc0 : word) Mi rom) (mkst regs' (0x28ccc : word) M' rom) /\ k4_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k4_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_28cc4 D_28cc4 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_IN. kpost.
  Qed.

  Lemma k4_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k4_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28dc0 : word) Mi rom) (mkst regs' (0x28bd8 : word) M' rom) /\ k4_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k4_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_28cc4 D_28cc4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28cc8 D_28cc8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RL. kpost.
  Qed.

  Lemma k4_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k4_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28bd8 : word) Mi rom) (mkst regs' (0x28bf4 : word) M' rom) /\ k4_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k4_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_28adc D_28adc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_28ae0 D_28ae0 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_28ae4 D_28ae4 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_28ae8 D_28ae8 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28aec D_28aec 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_28af0 D_28af0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k4_RH. kpost.
  Qed.

  Lemma k4_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k4_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28bd8 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k4_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_28adc D_28adc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_28ae0 D_28ae0 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_28ae4 D_28ae4 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_28ae8 D_28ae8 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28aec D_28aec 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_28af0 D_28af0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_28af4 D_28af4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k4_inner : forall regs Mi i, (0 <= i < h)%Z -> k4_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x28ccc : word) Mi rom) (mkst regs' (0x28bd8 : word) M' rom) /\ k4_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x28ccc : word) (0x28bd8 : word) (fun r m j => k4_IN r m i j) (fun r m => k4_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k4_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k4_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k4_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k4_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28b70 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k4_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x28bf4 : word) (0x2a670 : word) (fun r m i => k4_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k4_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k4_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k4_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k4_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k5_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 14 = (Z_to_bv 64 (i)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).
  Definition k5_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Definition k5_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Definition k5_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).

  Definition k5_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).
  Lemma k5_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29bfc : word) Mi rom) (mkst regs' (0x29c3c : word) M' rom) /\ k5_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      kli F_29b00 D_29b00 429498368%Z.   (* [comment removed for export] *)
      kli F_29b04 D_29b04 858992640%Z.   (* [comment removed for export] *)
      zv F_29b08 D_29b08 (Z_to_bv 64 (429496729)).   (* [comment removed for export] *)
      zvaddw F_29b0c D_29b0c (Z_to_bv 64 (wpls + 429496729)).   (* [comment removed for export] *)
      zvw F_29b10 D_29b10 (Z_to_bv 64 (858993459)).   (* [comment removed for export] *)
      stepb_ft F_29b14 D_29b14 ltac:(condZ).   (* [comment removed for export] *)
      zvsl F_29b18 D_29b18 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      zvsl F_29b1c D_29b1c (Z_to_bv 64 (8 * wpls)) 8%Z.   (* [comment removed for export] *)
      zvsubw F_29b20 D_29b20 (Z_to_bv 64 (6 * wpls)).   (* [comment removed for export] *)
      zv F_29b24 D_29b24 (Z_to_bv 64 (6 * wpls)).   (* [comment removed for export] *)
      stepb_ft F_29b28 D_29b28 ltac:(condR).   (* [comment removed for export] *)
      zvw F_29b2c D_29b2c (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_29b30 D_29b30 80%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_ft F_29b34 D_29b34 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29b38 D_29b38 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29b3c D_29b3c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_pre_c1. kpost.
  Qed.

  Definition k5_pre_c2 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (24 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (- datas + 18446744073709551616)) /\ getr regs 13 = (Z_to_bv 64 (datas)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).
  Lemma k5_pre_s1 : forall regs Mi, k5_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29c3c : word) Mi rom) (mkst regs' (0x29c7c : word) M' rom) /\ k5_pre_c2 regs' M'.
  Proof.
    intros regs Mi  HF. unfold k5_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      stf F_29b40 D_29b40 104%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stf F_29b44 D_29b44 96%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_29b48 D_29b48.   (* [comment removed for export] *)
      zvslw F_29b4c D_29b4c (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      ldf F_29b50 D_29b50 80%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_29b54 D_29b54.   (* [comment removed for export] *)
      stf F_29b58 D_29b58 72%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_29b5c D_29b5c (Z_to_bv 64 (24 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_29b60 D_29b60 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_29b64 D_29b64.   (* [comment removed for export] *)
      stf F_29b68 D_29b68 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_29b6c D_29b6c 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_29b70 D_29b70.   (* [comment removed for export] *)
      stf F_29b74 D_29b74 128%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      zvneg F_29b78 D_29b78 (Z_to_bv 64 (- datas + 18446744073709551616)).   (* [comment removed for export] *)
      lineg F_29b7c D_29b7c 18446744073709551611%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_pre_c2. kpost.
  Qed.

  Lemma k5_pre_s2 : forall regs Mi, k5_pre_c2 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29c7c : word) Mi rom) (mkst regs' (0x29cf0 : word) M' rom) /\ k5_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k5_pre_c2 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvsl F_29b80 D_29b80 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_29b84 D_29b84 (Z_to_bv 64 (datas + 24 * wpls)).   (* [comment removed for export] *)
      stf F_29b88 D_29b88 64%Z (Z_to_bv 64 (datas + 24 * wpls)).   (* [comment removed for export] *)
      zv F_29b8c D_29b8c (Z_to_bv 64 (datas - 24 * wpls)).   (* [comment removed for export] *)
      stf F_29b90 D_29b90 56%Z (Z_to_bv 64 (datas - 24 * wpls)).   (* [comment removed for export] *)
      zv F_29b94 D_29b94 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29b98 D_29b98 48%Z (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zvn F_29b9c D_29b9c (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29ba0 D_29ba0 40%Z (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29ba4 D_29ba4 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      stf F_29ba8 D_29ba8 32%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_29bac D_29bac (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      stf F_29bb0 D_29bb0 24%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_29bb4 D_29bb4 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29bb8 D_29bb8 16%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zvn F_29bbc D_29bbc (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29bc0 D_29bc0 8%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_29bc4 D_29bc4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RH. kpost.
  Qed.

  Lemma k5_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29bfc : word) Mi rom) (mkst regs' (0x29cf0 : word) M' rom) /\ k5_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k5_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k5_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    destruct (k5_pre_s2 r2 M2  H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k5_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).
  Lemma k5_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k5_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29cf0 : word) Mi rom) (mkst regs' (0x29d30 : word) M' rom) /\ k5_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k5_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29bf4 D_29bf4 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stf F_29bf8 D_29bf8 112%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvmulw F_29bfc D_29bfc (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_29c00 D_29c00 ltac:(condR).   (* [comment removed for export] *)
      ldf F_29c04 D_29c04 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      snez_nz F_29c08 D_29c08 1%Z.   (* [comment removed for export] *)
      zvw F_29c0c D_29c0c (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_29c10 D_29c10 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_29c14 D_29c14 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_29c18 D_29c18 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29c1c D_29c1c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29c20 D_29c20 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_29c24 D_29c24 0%Z.   (* [comment removed for export] *)
      slti_0 F_29c28 D_29c28 0%Z.   (* [comment removed for export] *)
      kclosed F_29c2c D_29c2c 0%Z.   (* [comment removed for export] *)
      kclosed F_29c30 D_29c30 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_rowset_c1. kpost.
  Qed.

  Definition k5_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 11 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)).
  Lemma k5_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k5_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29d30 : word) Mi rom) (mkst regs' (0x29d70 : word) M' rom) /\ k5_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k5_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29c34 D_29c34 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29c38 D_29c38 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29c3c D_29c3c 112%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zv F_29c40 D_29c40 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_29c44 D_29c44 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_ft F_29c48 D_29c48 ltac:(condR).   (* [comment removed for export] *)
      ldf F_29c4c D_29c4c 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_29c50 D_29c50 1%Z.   (* [comment removed for export] *)
      zvw F_29c54 D_29c54 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_29c58 D_29c58 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_29c5c D_29c5c (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_29c60 D_29c60 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29c64 D_29c64 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29c68 D_29c68 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_29c6c D_29c6c 0%Z.   (* [comment removed for export] *)
      slti_0 F_29c70 D_29c70 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_rowset_c2. kpost.
  Qed.

  Definition k5_rowset_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))).
  Lemma k5_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k5_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29d70 : word) Mi rom) (mkst regs' (0x29db0 : word) M' rom) /\ k5_rowset_c3 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k5_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      kclosed F_29c74 D_29c74 0%Z.   (* [comment removed for export] *)
      kclosed F_29c78 D_29c78 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29c7c D_29c7c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29c80 D_29c80 80%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_29c84 D_29c84.   (* [comment removed for export] *)
      stepb_ft F_29c88 D_29c88 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29c8c D_29c8c.   (* [comment removed for export] *)
      ldf F_29c90 D_29c90 96%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_29c94 D_29c94 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_29c98 D_29c98 104%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_29c9c D_29c9c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_29ca0 D_29ca0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_29ca4 D_29ca4 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      stf F_29ca8 D_29ca8 136%Z (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29cac D_29cac 64%Z (Z_to_bv 64 (datas + 24 * wpls)).   (* [comment removed for export] *)
      zv F_29cb0 D_29cb0 (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_rowset_c3. kpost.
  Qed.

  Lemma k5_rowset_s3 : forall regs Mi i, (0 <= i < h)%Z -> k5_rowset_c3 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29db0 : word) Mi rom) (mkst regs' (0x29df4 : word) M' rom) /\ k5_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k5_rowset_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_29cb4 D_29cb4 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_29cb8 D_29cb8 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_29cbc D_29cbc 32%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_29cc0 D_29cc0 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29cc4 D_29cc4 56%Z (Z_to_bv 64 (datas - 24 * wpls)).   (* [comment removed for export] *)
      zv F_29cc8 D_29cc8 (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29ccc D_29ccc 24%Z (Z_to_bv 64 (datas - 8 * wpls)).   (* [comment removed for export] *)
      zv F_29cd0 D_29cd0 (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29cd4 D_29cd4 48%Z (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29cd8 D_29cd8 (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29cdc D_29cdc 16%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29ce0 D_29ce0 (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29ce4 D_29ce4 8%Z (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29ce8 D_29ce8 (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29cec D_29cec 40%Z (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29cf0 D_29cf0 (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29cf4 D_29cf4 72%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_IN. kpost.
  Qed.

  Lemma k5_rowset : forall regs Mi i, (0 <= i < h)%Z -> k5_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29cf0 : word) Mi rom) (mkst regs' (0x29df4 : word) M' rom) /\ k5_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k5_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k5_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k5_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k5_rowset_s3 r3 M3 i HR0 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Definition k5_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Lemma k5_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29df4 : word) Mi rom) (mkst regs' (0x29e34 : word) M' rom) /\ k5_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_29cf8 D_29cf8 136%Z (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_29cfc D_29cfc (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_29d00 D_29d00.   (* [comment removed for export] *)
      snez_nz F_29d04 D_29d04 1%Z.   (* [comment removed for export] *)
      seqzx F_29d08 D_29d08 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29d0c D_29d0c ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29d10 D_29d10 0%Z.   (* [comment removed for export] *)
      zv F_29d14 D_29d14 (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_29d18 D_29d18 1%Z.   (* [comment removed for export] *)
      kclosed F_29d1c D_29d1c 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29d20 D_29d20 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29d24 D_29d24 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29d28 D_29d28 128%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_29d2c D_29d2c ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_29d30 D_29d30 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29d34 D_29d34 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_iter_c1. kpost.
  Qed.

  Definition k5_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Lemma k5_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29e34 : word) Mi rom) (mkst regs' (0x29e74 : word) M' rom) /\ k5_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_iter_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      slti_0 F_29d38 D_29d38 0%Z.   (* [comment removed for export] *)
      zv F_29d3c D_29d3c (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_29d40 D_29d40 1%Z.   (* [comment removed for export] *)
      kclosed F_29d44 D_29d44 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29d48 D_29d48 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29d4c D_29d4c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29d50 D_29d50 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29d54 D_29d54 0%Z.   (* [comment removed for export] *)
      zv F_29d58 D_29d58 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_29d5c D_29d5c 0%Z.   (* [comment removed for export] *)
      kclosed F_29d60 D_29d60 0%Z.   (* [comment removed for export] *)
      kclosed F_29d64 D_29d64 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29d68 D_29d68 ltac:(condZ).   (* [comment removed for export] *)
      zv F_29d6c D_29d6c (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)).   (* [comment removed for export] *)
      sn F_29d70 D_29d70.   (* [comment removed for export] *)
      stepb_ft F_29d74 D_29d74 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_iter_c2. kpost.
  Qed.

  Definition k5_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 20 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Lemma k5_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29e74 : word) Mi rom) (mkst regs' (0x29eb4 : word) M' rom) /\ k5_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    eexists. eexists. split.
    -
      stepb_ft F_29d78 D_29d78 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29d7c D_29d7c 0%Z.   (* [comment removed for export] *)
      zv F_29d80 D_29d80 (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_29d84 D_29d84 0%Z.   (* [comment removed for export] *)
      kclosed F_29d88 D_29d88 0%Z.   (* [comment removed for export] *)
      kclosed F_29d8c D_29d8c 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29d90 D_29d90 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29d94 D_29d94.   (* [comment removed for export] *)
      stepb_ft F_29d98 D_29d98 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29d9c D_29d9c 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_29da0 D_29da0 ltac:(condR).   (* [comment removed for export] *)
      zv F_29da4 D_29da4 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_29da8 D_29da8 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_29dac D_29dac bs0 v0 ltac:(rdn_addr (datas - 24 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29db0 D_29db0 bs1 v1 ltac:(rdn_addr (datas - 24 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29db4 D_29db4 bs2 v2 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_iter_c3. kpost.
  Qed.

  Definition k5_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Lemma k5_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29eb4 : word) Mi rom) (mkst regs' (0x29ef4 : word) M' rom) /\ k5_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_iter_c3 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 24 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    eexists. eexists. split.
    -
      stepLD F_29db8 D_29db8 bs0 v0 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29dbc D_29dbc bs1 v1 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29dc0 D_29dc0 bs2 v2 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_29dc4 D_29dc4 bs3 v3 ltac:(rdn_addr (datas - 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_29dc8 D_29dc8 bs4 v4 ltac:(rdn_addr (datas + 24 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      sn F_29dcc D_29dcc.   (* [comment removed for export] *)
      sn F_29dd0 D_29dd0.   (* [comment removed for export] *)
      sn F_29dd4 D_29dd4.   (* [comment removed for export] *)
      sn F_29dd8 D_29dd8.   (* [comment removed for export] *)
      sn F_29ddc D_29ddc.   (* [comment removed for export] *)
      sn F_29de0 D_29de0.   (* [comment removed for export] *)
      sn F_29de4 D_29de4.   (* [comment removed for export] *)
      sn F_29de8 D_29de8.   (* [comment removed for export] *)
      sn F_29dec D_29dec.   (* [comment removed for export] *)
      sn F_29df0 D_29df0.   (* [comment removed for export] *)
      sn F_29df4 D_29df4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_iter_c4. kpost.
  Qed.

  Definition k5_iter_c5 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas + 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (datas - 8 * wpls)) /\ cell Mi 32 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (- datas + 24 * wpls + 18446744073709551616)) /\ cell Mi 48 (Z_to_bv 64 (- datas - 24 * wpls + 18446744073709551616)) /\ cell Mi 56 (Z_to_bv 64 (datas - 24 * wpls)) /\ cell Mi 64 (Z_to_bv 64 (datas + 24 * wpls)) /\ cell Mi 72 (Z_to_bv 64 (PW)) /\ cell Mi 80 (Z_to_bv 64 (w + 31)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 104 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 112 (Z_to_bv 64 (i)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (0)) /\ cell Mi 136 (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 11 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 14 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (6 * wpls)) /\ getr regs 17 = (Z_to_bv 64 (datas - 24 * wpls + 4 * (i * wpls))) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 21 = (Z_to_bv 64 (- datas + 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 8 * wpls + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (datas + 24 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (- datas + 24 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (- datas - 24 * wpls - 4 * (i * wpls) + 18446744073709551616)).
  Lemma k5_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29ef4 : word) Mi rom) (mkst regs' (0x29f34 : word) M' rom) /\ k5_iter_c5 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_iter_c4 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    eexists. eexists. split.
    -
      sn F_29df8 D_29df8.   (* [comment removed for export] *)
      sn F_29dfc D_29dfc.   (* [comment removed for export] *)
      sn F_29e00 D_29e00.   (* [comment removed for export] *)
      sn F_29e04 D_29e04.   (* [comment removed for export] *)
      sn F_29e08 D_29e08.   (* [comment removed for export] *)
      stepLD F_29e0c D_29e0c bs0 v0 ltac:(rdn_addr (datas + 24 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      sn F_29e10 D_29e10.   (* [comment removed for export] *)
      sn F_29e14 D_29e14.   (* [comment removed for export] *)
      sn F_29e18 D_29e18.   (* [comment removed for export] *)
      sn F_29e1c D_29e1c.   (* [comment removed for export] *)
      sn F_29e20 D_29e20.   (* [comment removed for export] *)
      sn F_29e24 D_29e24.   (* [comment removed for export] *)
      sn F_29e28 D_29e28.   (* [comment removed for export] *)
      sn F_29e2c D_29e2c.   (* [comment removed for export] *)
      sn F_29e30 D_29e30.   (* [comment removed for export] *)
      sn F_29e34 D_29e34.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_iter_c5. kpost.
  Qed.

  Lemma k5_iter_s5 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_iter_c5 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29f34 : word) Mi rom) (mkst regs' (0x29f60 : word) M' rom) /\ k5_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k5_iter_c5 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_29e38 D_29e38.   (* [comment removed for export] *)
      sn F_29e3c D_29e3c.   (* [comment removed for export] *)
      sn F_29e40 D_29e40.   (* [comment removed for export] *)
      sn F_29e44 D_29e44.   (* [comment removed for export] *)
      sn F_29e48 D_29e48.   (* [comment removed for export] *)
      sn F_29e4c D_29e4c.   (* [comment removed for export] *)
      gsw F_29e50 D_29e50 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_ft F_29e54 D_29e54 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29e58 D_29e58 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29e5c D_29e5c (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_29e60 D_29e60 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_BN. kpost.
  Qed.

  Lemma k5_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k5_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29df4 : word) Mi rom) (mkst regs' (0x29f60 : word) M' rom) /\ k5_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k5_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k5_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k5_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k5_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k5_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    destruct (k5_iter_s5 r5 M5 i j HR0 HR1 H5) as (r6 & M6 & RUN6 & H6).
    exists r6, M6. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | eapply msteps_trans; [exact RUN5 | exact RUN6]]]]] | exact H6].
  Qed.

  Lemma k5_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k5_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29f60 : word) Mi rom) (mkst regs' (0x29df4 : word) M' rom) /\ k5_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k5_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_29e64 D_29e64 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_IN. kpost.
  Qed.

  Lemma k5_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k5_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29f60 : word) Mi rom) (mkst regs' (0x29cc4 : word) M' rom) /\ k5_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k5_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29e64 D_29e64 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29e68 D_29e68.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RL. kpost.
  Qed.

  Lemma k5_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k5_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29cc4 : word) Mi rom) (mkst regs' (0x29cf0 : word) M' rom) /\ k5_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k5_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29bc8 D_29bc8 112%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29bcc D_29bcc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29bd0 D_29bd0 96%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29bd4 D_29bd4 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29bd8 D_29bd8 96%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29bdc D_29bdc 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29be0 D_29be0 104%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29be4 D_29be4 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29be8 D_29be8 104%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29bec D_29bec 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29bf0 D_29bf0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k5_RH. kpost.
  Qed.

  Lemma k5_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k5_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29cc4 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k5_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29bc8 D_29bc8 112%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29bcc D_29bcc (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29bd0 D_29bd0 96%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29bd4 D_29bd4 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29bd8 D_29bd8 96%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29bdc D_29bdc 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29be0 D_29be0 104%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29be4 D_29be4 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29be8 D_29be8 104%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29bec D_29bec 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_29bf0 D_29bf0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k5_inner : forall regs Mi i, (0 <= i < h)%Z -> k5_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x29df4 : word) Mi rom) (mkst regs' (0x29cc4 : word) M' rom) /\ k5_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x29df4 : word) (0x29cc4 : word) (fun r m j => k5_IN r m i j) (fun r m => k5_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k5_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k5_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k5_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k5_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29bfc : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k5_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x29cf0 : word) (0x2a670 : word) (fun r m i => k5_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k5_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k5_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k5_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k5_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
