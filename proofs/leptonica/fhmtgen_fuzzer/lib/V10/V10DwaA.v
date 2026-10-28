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
  Definition k0_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k0_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k0_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 12 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k0_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).

  Definition k0_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (datas)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (0)).
  Lemma k0_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28868 : word) Mi rom) (mkst regs' (0x288b0 : word) M' rom) /\ k0_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvw F_2876c D_2876c (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_28770 D_28770 128%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_28774 D_28774 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2877c D_2877c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_28780 D_28780 ltac:(condZ).   (* [comment removed for export] *)
      stf F_28788 D_28788 136%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_2878c D_2878c.   (* [comment removed for export] *)
      sn F_28790 D_28790.   (* [comment removed for export] *)
      ldf F_28794 D_28794 128%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_28798 D_28798.   (* [comment removed for export] *)
      stf F_2879c D_2879c 112%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_287a0 D_287a0 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_287a4 D_287a4 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_287a8 D_287a8.   (* [comment removed for export] *)
      ldf F_287ac D_287ac 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_287b0 D_287b0.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_pre_c1. kpost.
  Qed.

  Lemma k0_pre_s1 : forall regs Mi, k0_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x288b0 : word) Mi rom) (mkst regs' (0x28910 : word) M' rom) /\ k0_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k0_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      snez_nz F_287b4 D_287b4 1%Z.   (* [comment removed for export] *)
      stf F_287b8 D_287b8 120%Z (Z_to_bv 64 (1)).   (* [comment removed for export] *)
      sn F_287bc D_287bc.   (* [comment removed for export] *)
      lineg F_287c0 D_287c0 18446744073709551611%Z.   (* [comment removed for export] *)
      lineg F_287c4 D_287c4 18446744073709551615%Z.   (* [comment removed for export] *)
      zv F_287c8 D_287c8 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_287cc D_287cc (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_287d0 D_287d0 96%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_287d4 D_287d4 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_287d8 D_287d8 80%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_287dc D_287dc 104%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zvneg F_287e0 D_287e0 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_287e4 D_287e4 72%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_287e8 D_287e8.   (* [comment removed for export] *)
      sn F_287ec D_287ec.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RH. kpost.
  Qed.

  Lemma k0_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28868 : word) Mi rom) (mkst regs' (0x28910 : word) M' rom) /\ k0_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k0_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k0_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Definition k0_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k0_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28910 : word) Mi rom) (mkst regs' (0x2895c : word) M' rom) /\ k0_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k0_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28814 D_28814 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvmulw F_28818 D_28818 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_2881c D_2881c ltac:(condR).   (* [comment removed for export] *)
      zvw F_28824 D_28824 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_28828 D_28828 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_2882c D_2882c 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_28830 D_28830 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_28834 D_28834 0%Z.   (* [comment removed for export] *)
      ldf F_28838 D_28838 120%Z (Z_to_bv 64 (1)).   (* [comment removed for export] *)
      stepb_tk F_2883c D_2883c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28844 D_28844 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_28848 D_28848 0%Z.   (* [comment removed for export] *)
      slti_0 F_2884c D_2884c 0%Z.   (* [comment removed for export] *)
      kclosed F_28850 D_28850 0%Z.   (* [comment removed for export] *)
      kclosed F_28854 D_28854 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28858 D_28858 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_rowset_c1. kpost.
  Qed.

  Definition k0_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k0_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2895c : word) Mi rom) (mkst regs' (0x289a4 : word) M' rom) /\ k0_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k0_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_28860 D_28860 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zv F_28864 D_28864 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_28868 D_28868 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_tk F_2886c D_2886c ltac:(condR).   (* [comment removed for export] *)
      ldf F_28874 D_28874 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_28878 D_28878 1%Z.   (* [comment removed for export] *)
      zvw F_2887c D_2887c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_28880 D_28880 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_28884 D_28884 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_28888 D_28888 0%Z.   (* [comment removed for export] *)
      stepb_tk F_2888c D_2888c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_28894 D_28894 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_28898 D_28898 0%Z.   (* [comment removed for export] *)
      slti_0 F_2889c D_2889c 0%Z.   (* [comment removed for export] *)
      kclosed F_288a0 D_288a0 0%Z.   (* [comment removed for export] *)
      kclosed F_288a4 D_288a4 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_rowset_c2. kpost.
  Qed.

  Lemma k0_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k0_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x289a4 : word) Mi rom) (mkst regs' (0x289fc : word) M' rom) /\ k0_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k0_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_288a8 D_288a8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_288b0 D_288b0 128%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_288b4 D_288b4.   (* [comment removed for export] *)
      stepb_ft F_288b8 D_288b8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_288bc D_288bc.   (* [comment removed for export] *)
      ldf F_288c0 D_288c0 136%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_288c4 D_288c4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_288c8 D_288c8 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_288cc D_288cc 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_288d0 D_288d0 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_288d4 D_288d4 104%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_288d8 D_288d8 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_288dc D_288dc 96%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_288e0 D_288e0 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_288e4 D_288e4 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_288e8 D_288e8 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_288ec D_288ec 80%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_288f0 D_288f0 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_288f4 D_288f4 72%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_288f8 D_288f8 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_288fc D_288fc 112%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_IN. kpost.
  Qed.

  Lemma k0_rowset : forall regs Mi i, (0 <= i < h)%Z -> k0_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x28910 : word) Mi rom) (mkst regs' (0x289fc : word) M' rom) /\ k0_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k0_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k0_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k0_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k0_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x289fc : word) Mi rom) (mkst regs' (0x28a5c : word) M' rom) /\ k0_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_28900 D_28900 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_28904 D_28904.   (* [comment removed for export] *)
      snez_nz F_28908 D_28908 1%Z.   (* [comment removed for export] *)
      seqzx F_2890c D_2890c 0%Z.   (* [comment removed for export] *)
      stepb_tk F_28910 D_28910 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28918 D_28918 0%Z.   (* [comment removed for export] *)
      zv F_2891c D_2891c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_28920 D_28920 1%Z.   (* [comment removed for export] *)
      kclosed F_28924 D_28924 1%Z.   (* [comment removed for export] *)
      stepb_tk F_28928 D_28928 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28930 D_28930 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28938 D_28938 ltac:(condR).   (* [comment removed for export] *)
      stepb_tk F_28940 D_28940 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28948 D_28948 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28950 D_28950 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28958 D_28958 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_iter_c1. kpost.
  Qed.

  Definition k0_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28a5c : word) Mi rom) (mkst regs' (0x28ab4 : word) M' rom) /\ k0_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_iter_c1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    eexists. eexists. split.
    -
      stepb_tk F_28960 D_28960 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_28968 D_28968 0%Z.   (* [comment removed for export] *)
      zv F_2896c D_2896c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_28970 D_28970 0%Z.   (* [comment removed for export] *)
      kclosed F_28974 D_28974 0%Z.   (* [comment removed for export] *)
      kclosed F_28978 D_28978 1%Z.   (* [comment removed for export] *)
      stepb_tk F_2897c D_2897c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28984 D_28984 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_2898c D_2898c ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_28994 D_28994 ltac:(condR).   (* [comment removed for export] *)
      zv F_2899c D_2899c (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_tk F_289a0 D_289a0 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_289a8 D_289a8 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_289ac D_289ac bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_289b0 D_289b0 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_289b4 D_289b4 bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_iter_c2. kpost.
  Qed.

  Definition k0_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28ab4 : word) Mi rom) (mkst regs' (0x28af4 : word) M' rom) /\ k0_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    eexists. eexists. split.
    -
      stepLD F_289b8 D_289b8 bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_289bc D_289bc bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_289c0 D_289c0 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_289c4 D_289c4 bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      sn F_289c8 D_289c8.   (* [comment removed for export] *)
      sn F_289cc D_289cc.   (* [comment removed for export] *)
      sn F_289d0 D_289d0.   (* [comment removed for export] *)
      sn F_289d4 D_289d4.   (* [comment removed for export] *)
      sn F_289d8 D_289d8.   (* [comment removed for export] *)
      sn F_289dc D_289dc.   (* [comment removed for export] *)
      sn F_289e0 D_289e0.   (* [comment removed for export] *)
      sn F_289e4 D_289e4.   (* [comment removed for export] *)
      sn F_289e8 D_289e8.   (* [comment removed for export] *)
      sn F_289ec D_289ec.   (* [comment removed for export] *)
      sn F_289f0 D_289f0.   (* [comment removed for export] *)
      sn F_289f4 D_289f4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_iter_c3. kpost.
  Qed.

  Definition k0_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 72 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 80 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 104 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (PW)) /\ cell Mi 120 (Z_to_bv 64 (1)) /\ cell Mi 128 (Z_to_bv 64 (w + 31)) /\ cell Mi 136 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 5 = (Z_to_bv 64 (i)) /\ getr regs 6 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 17 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 25 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 26 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 27 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k0_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28af4 : word) Mi rom) (mkst regs' (0x28b34 : word) M' rom) /\ k0_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_iter_c3 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    eexists. eexists. split.
    -
      sn F_289f8 D_289f8.   (* [comment removed for export] *)
      sn F_289fc D_289fc.   (* [comment removed for export] *)
      stepLD F_28a00 D_28a00 bs0 v0 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      sn F_28a04 D_28a04.   (* [comment removed for export] *)
      sn F_28a08 D_28a08.   (* [comment removed for export] *)
      sn F_28a0c D_28a0c.   (* [comment removed for export] *)
      sn F_28a10 D_28a10.   (* [comment removed for export] *)
      sn F_28a14 D_28a14.   (* [comment removed for export] *)
      sn F_28a18 D_28a18.   (* [comment removed for export] *)
      sn F_28a1c D_28a1c.   (* [comment removed for export] *)
      sn F_28a20 D_28a20.   (* [comment removed for export] *)
      sn F_28a24 D_28a24.   (* [comment removed for export] *)
      sn F_28a28 D_28a28.   (* [comment removed for export] *)
      sn F_28a2c D_28a2c.   (* [comment removed for export] *)
      sn F_28a30 D_28a30.   (* [comment removed for export] *)
      sn F_28a34 D_28a34.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_iter_c4. kpost.
  Qed.

  Lemma k0_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28b34 : word) Mi rom) (mkst regs' (0x28b68 : word) M' rom) /\ k0_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k0_iter_c4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_28a38 D_28a38.   (* [comment removed for export] *)
      sn F_28a3c D_28a3c.   (* [comment removed for export] *)
      sn F_28a40 D_28a40.   (* [comment removed for export] *)
      sn F_28a44 D_28a44.   (* [comment removed for export] *)
      sn F_28a48 D_28a48.   (* [comment removed for export] *)
      sn F_28a4c D_28a4c.   (* [comment removed for export] *)
      sn F_28a50 D_28a50.   (* [comment removed for export] *)
      sn F_28a54 D_28a54.   (* [comment removed for export] *)
      gsw F_28a58 D_28a58 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_tk F_28a5c D_28a5c ltac:(condZ).   (* [comment removed for export] *)
      zvw F_28a64 D_28a64 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_28a68 D_28a68 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_BN. kpost.
  Qed.

  Lemma k0_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k0_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x289fc : word) Mi rom) (mkst regs' (0x28b68 : word) M' rom) /\ k0_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k0_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k0_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k0_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k0_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k0_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    exists r5, M5. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | exact RUN5]]]] | exact H5].
  Qed.

  Lemma k0_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k0_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28b68 : word) Mi rom) (mkst regs' (0x289fc : word) M' rom) /\ k0_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k0_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_28a6c D_28a6c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_IN. kpost.
  Qed.

  Lemma k0_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k0_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x28b68 : word) Mi rom) (mkst regs' (0x288ec : word) M' rom) /\ k0_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k0_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_28a6c D_28a6c ltac:(condZ).   (* [comment removed for export] *)
      sn F_28a70 D_28a70.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RL. kpost.
  Qed.

  Lemma k0_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k0_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x288ec : word) Mi rom) (mkst regs' (0x28910 : word) M' rom) /\ k0_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k0_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_287f0 D_287f0 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_287f4 D_287f4 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_287f8 D_287f8 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_287fc D_287fc 136%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_28800 D_28800 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_28804 D_28804 136%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28808 D_28808 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_2880c D_2880c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k0_RH. kpost.
  Qed.

  Lemma k0_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k0_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x288ec : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k0_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_287f0 D_287f0 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_287f4 D_287f4 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_287f8 D_287f8 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_287fc D_287fc 136%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_28800 D_28800 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_28804 D_28804 136%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_28808 D_28808 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_2880c D_2880c ltac:(condZ).   (* [comment removed for export] *)
      sn F_28810 D_28810.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k0_inner : forall regs Mi i, (0 <= i < h)%Z -> k0_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x289fc : word) Mi rom) (mkst regs' (0x288ec : word) M' rom) /\ k0_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x289fc : word) (0x288ec : word) (fun r m j => k0_IN r m i j) (fun r m => k0_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k0_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k0_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k0_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k0_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x28868 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k0_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x28910 : word) (0x2a670 : word) (fun r m i => k0_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k0_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k0_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k0_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k0_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k1_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k1_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k1_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k1_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).

  Definition k1_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (datad)) /\ getr regs 13 = (Z_to_bv 64 (datas)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)) /\ getr regs 17 = (Z_to_bv 64 (0)).
  Lemma k1_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29a14 : word) Mi rom) (mkst regs' (0x29a54 : word) M' rom) /\ k1_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvw F_29918 D_29918 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_ft F_2991c D_2991c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29920 D_29920 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29924 D_29924 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29928 D_29928.   (* [comment removed for export] *)
      sn F_2992c D_2992c.   (* [comment removed for export] *)
      sn F_29930 D_29930.   (* [comment removed for export] *)
      zvpw F_29934 D_29934.   (* [comment removed for export] *)
      stf F_29938 D_29938 128%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_2993c D_2993c (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_29940 D_29940 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_29944 D_29944.   (* [comment removed for export] *)
      stf F_29948 D_29948 136%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_2994c D_2994c 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_29950 D_29950.   (* [comment removed for export] *)
      snez_nz F_29954 D_29954 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_pre_c1. kpost.
  Qed.

  Lemma k1_pre_s1 : forall regs Mi, k1_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29a54 : word) Mi rom) (mkst regs' (0x29a90 : word) M' rom) /\ k1_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k1_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      snez_nz F_29958 D_29958 1%Z.   (* [comment removed for export] *)
      sn F_2995c D_2995c.   (* [comment removed for export] *)
      sn F_29960 D_29960.   (* [comment removed for export] *)
      lineg F_29964 D_29964 18446744073709551611%Z.   (* [comment removed for export] *)
      lineg F_29968 D_29968 18446744073709551615%Z.   (* [comment removed for export] *)
      zv F_2996c D_2996c (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zvneg F_29970 D_29970 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_29974 D_29974.   (* [comment removed for export] *)
      sn F_29978 D_29978.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RH. kpost.
  Qed.

  Lemma k1_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29a14 : word) Mi rom) (mkst regs' (0x29a90 : word) M' rom) /\ k1_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k1_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k1_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Definition k1_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 13 = (Z_to_bv 64 (wpld)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k1_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k1_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29a90 : word) Mi rom) (mkst regs' (0x29ad0 : word) M' rom) /\ k1_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k1_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29994 D_29994 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvmulw F_29998 D_29998 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_2999c D_2999c ltac:(condR).   (* [comment removed for export] *)
      zvw F_299a0 D_299a0 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_299a4 D_299a4 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_299a8 D_299a8 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_299ac D_299ac (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_299b0 D_299b0 0%Z.   (* [comment removed for export] *)
      stepb_ft F_299b4 D_299b4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_299b8 D_299b8 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_299bc D_299bc 0%Z.   (* [comment removed for export] *)
      slti_0 F_299c0 D_299c0 0%Z.   (* [comment removed for export] *)
      kclosed F_299c4 D_299c4 0%Z.   (* [comment removed for export] *)
      kclosed F_299c8 D_299c8 1%Z.   (* [comment removed for export] *)
      stepb_ft F_299cc D_299cc ltac:(condZ).   (* [comment removed for export] *)
      ldf F_299d0 D_299d0 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_rowset_c1. kpost.
  Qed.

  Definition k1_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k1_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k1_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29ad0 : word) Mi rom) (mkst regs' (0x29b10 : word) M' rom) /\ k1_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k1_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_299d4 D_299d4 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_299d8 D_299d8 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_ft F_299dc D_299dc ltac:(condR).   (* [comment removed for export] *)
      zvw F_299e0 D_299e0 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_299e4 D_299e4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_299e8 D_299e8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_299ec D_299ec (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_299f0 D_299f0 0%Z.   (* [comment removed for export] *)
      stepb_ft F_299f4 D_299f4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_299f8 D_299f8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_299fc D_299fc 0%Z.   (* [comment removed for export] *)
      slti_0 F_29a00 D_29a00 0%Z.   (* [comment removed for export] *)
      kclosed F_29a04 D_29a04 0%Z.   (* [comment removed for export] *)
      kclosed F_29a08 D_29a08 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29a0c D_29a0c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a10 D_29a10 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_rowset_c2. kpost.
  Qed.

  Lemma k1_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k1_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29b10 : word) Mi rom) (mkst regs' (0x29b3c : word) M' rom) /\ k1_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k1_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      ldf F_29a14 D_29a14 136%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_29a18 D_29a18 ltac:(condR).   (* [comment removed for export] *)
      zvsl F_29a1c D_29a1c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_29a20 D_29a20 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_29a24 D_29a24 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_29a28 D_29a28 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_29a2c D_29a2c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_29a30 D_29a30 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29a34 D_29a34 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_29a38 D_29a38 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29a3c D_29a3c 128%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_IN. kpost.
  Qed.

  Lemma k1_rowset : forall regs Mi i, (0 <= i < h)%Z -> k1_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29a90 : word) Mi rom) (mkst regs' (0x29b3c : word) M' rom) /\ k1_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k1_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k1_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k1_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k1_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 23 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k1_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29b3c : word) Mi rom) (mkst regs' (0x29b7c : word) M' rom) /\ k1_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k1_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29a40 D_29a40 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_29a44 D_29a44 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a48 D_29a48 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a4c D_29a4c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a50 D_29a50 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29a54 D_29a54 0%Z.   (* [comment removed for export] *)
      zv F_29a58 D_29a58 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_29a5c D_29a5c 0%Z.   (* [comment removed for export] *)
      kclosed F_29a60 D_29a60 0%Z.   (* [comment removed for export] *)
      kclosed F_29a64 D_29a64 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29a68 D_29a68 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a6c D_29a6c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a70 D_29a70 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29a74 D_29a74 ltac:(condR).   (* [comment removed for export] *)
      zv F_29a78 D_29a78 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_29a7c D_29a7c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_iter_c1. kpost.
  Qed.

  Definition k1_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 128 (Z_to_bv 64 (PW)) /\ cell Mi 136 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas + 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 23 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (32)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k1_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29b7c : word) Mi rom) (mkst regs' (0x29bbc : word) M' rom) /\ k1_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k1_iter_c1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_29a80 D_29a80 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29a84 D_29a84 bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29a88 D_29a88 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_29a8c D_29a8c bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_29a90 D_29a90 bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_29a94 D_29a94 bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_29a98 D_29a98.   (* [comment removed for export] *)
      sn F_29a9c D_29a9c.   (* [comment removed for export] *)
      sn F_29aa0 D_29aa0.   (* [comment removed for export] *)
      sn F_29aa4 D_29aa4.   (* [comment removed for export] *)
      sn F_29aa8 D_29aa8.   (* [comment removed for export] *)
      sn F_29aac D_29aac.   (* [comment removed for export] *)
      sn F_29ab0 D_29ab0.   (* [comment removed for export] *)
      sn F_29ab4 D_29ab4.   (* [comment removed for export] *)
      sn F_29ab8 D_29ab8.   (* [comment removed for export] *)
      sn F_29abc D_29abc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_iter_c2. kpost.
  Qed.

  Lemma k1_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29bbc : word) Mi rom) (mkst regs' (0x29bf4 : word) M' rom) /\ k1_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k1_iter_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_29ac0 D_29ac0.   (* [comment removed for export] *)
      sn F_29ac4 D_29ac4.   (* [comment removed for export] *)
      sn F_29ac8 D_29ac8.   (* [comment removed for export] *)
      sn F_29acc D_29acc.   (* [comment removed for export] *)
      sn F_29ad0 D_29ad0.   (* [comment removed for export] *)
      sn F_29ad4 D_29ad4.   (* [comment removed for export] *)
      sn F_29ad8 D_29ad8.   (* [comment removed for export] *)
      sn F_29adc D_29adc.   (* [comment removed for export] *)
      sn F_29ae0 D_29ae0.   (* [comment removed for export] *)
      sn F_29ae4 D_29ae4.   (* [comment removed for export] *)
      gsw F_29ae8 D_29ae8 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_ft F_29aec D_29aec ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29af0 D_29af0 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_29af4 D_29af4 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_BN. kpost.
  Qed.

  Lemma k1_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k1_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29b3c : word) Mi rom) (mkst regs' (0x29bf4 : word) M' rom) /\ k1_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k1_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k1_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k1_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Lemma k1_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k1_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29bf4 : word) Mi rom) (mkst regs' (0x29b3c : word) M' rom) /\ k1_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k1_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_29af8 D_29af8 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_IN. kpost.
  Qed.

  Lemma k1_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k1_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29bf4 : word) Mi rom) (mkst regs' (0x29a78 : word) M' rom) /\ k1_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k1_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29af8 D_29af8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29afc D_29afc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RL. kpost.
  Qed.

  Lemma k1_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k1_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29a78 : word) Mi rom) (mkst regs' (0x29a90 : word) M' rom) /\ k1_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k1_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_2997c D_2997c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_29980 D_29980 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29984 D_29984 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29988 D_29988 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_2998c D_2998c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29990 D_29990 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k1_RH. kpost.
  Qed.

  Lemma k1_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k1_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29a78 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k1_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_2997c D_2997c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_29980 D_29980 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29984 D_29984 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29988 D_29988 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_2998c D_2998c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_29990 D_29990 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k1_inner : forall regs Mi i, (0 <= i < h)%Z -> k1_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x29b3c : word) Mi rom) (mkst regs' (0x29a78 : word) M' rom) /\ k1_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x29b3c : word) (0x29a78 : word) (fun r m j => k1_IN r m i j) (fun r m => k1_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k1_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k1_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k1_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k1_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29a14 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k1_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x29a90 : word) (0x2a670 : word) (fun r m i => k1_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k1_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k1_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k1_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k1_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k2_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k2_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k2_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Definition k2_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).

  Definition k2_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (datas)) /\ getr regs 11 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)) /\ getr regs 17 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)).
  Lemma k2_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x291c0 : word) Mi rom) (mkst regs' (0x29208 : word) M' rom) /\ k2_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvw F_290c4 D_290c4 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_290c8 D_290c8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_290d0 D_290d0 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_290d4 D_290d4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_290dc D_290dc.   (* [comment removed for export] *)
      sn F_290e0 D_290e0.   (* [comment removed for export] *)
      sn F_290e4 D_290e4.   (* [comment removed for export] *)
      zvpw F_290e8 D_290e8.   (* [comment removed for export] *)
      stf F_290ec D_290ec 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      ldf F_290f0 D_290f0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_290f4 D_290f4.   (* [comment removed for export] *)
      ldf F_290f8 D_290f8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_290fc D_290fc.   (* [comment removed for export] *)
      zvsl F_29100 D_29100 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      snez_nz F_29104 D_29104 1%Z.   (* [comment removed for export] *)
      snez_nz F_29108 D_29108 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_pre_c1. kpost.
  Qed.

  Lemma k2_pre_s1 : forall regs Mi, k2_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29208 : word) Mi rom) (mkst regs' (0x29240 : word) M' rom) /\ k2_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k2_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      sn F_2910c D_2910c.   (* [comment removed for export] *)
      lineg F_29110 D_29110 18446744073709551611%Z.   (* [comment removed for export] *)
      lineg F_29114 D_29114 18446744073709551615%Z.   (* [comment removed for export] *)
      zv F_29118 D_29118 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_2911c D_2911c (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_29120 D_29120.   (* [comment removed for export] *)
      sn F_29124 D_29124.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RH. kpost.
  Qed.

  Lemma k2_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x291c0 : word) Mi rom) (mkst regs' (0x29240 : word) M' rom) /\ k2_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k2_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k2_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Definition k2_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (wpld)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k2_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k2_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29240 : word) Mi rom) (mkst regs' (0x2928c : word) M' rom) /\ k2_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k2_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29144 D_29144 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvmulw F_29148 D_29148 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_2914c D_2914c ltac:(condR).   (* [comment removed for export] *)
      zvw F_29154 D_29154 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_29158 D_29158 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_2915c D_2915c 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_29160 D_29160 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_29164 D_29164 0%Z.   (* [comment removed for export] *)
      stepb_tk F_29168 D_29168 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29170 D_29170 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_29174 D_29174 0%Z.   (* [comment removed for export] *)
      slti_0 F_29178 D_29178 0%Z.   (* [comment removed for export] *)
      kclosed F_2917c D_2917c 0%Z.   (* [comment removed for export] *)
      kclosed F_29180 D_29180 1%Z.   (* [comment removed for export] *)
      stepb_tk F_29184 D_29184 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2918c D_2918c 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_rowset_c1. kpost.
  Qed.

  Definition k2_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (32)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k2_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k2_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2928c : word) Mi rom) (mkst regs' (0x292d8 : word) M' rom) /\ k2_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k2_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29190 D_29190 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_29194 D_29194 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_tk F_29198 D_29198 ltac:(condR).   (* [comment removed for export] *)
      zvw F_291a0 D_291a0 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_291a4 D_291a4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_291a8 D_291a8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_291ac D_291ac (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_291b0 D_291b0 0%Z.   (* [comment removed for export] *)
      stepb_tk F_291b4 D_291b4 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_291bc D_291bc 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_291c0 D_291c0 0%Z.   (* [comment removed for export] *)
      slti_0 F_291c4 D_291c4 0%Z.   (* [comment removed for export] *)
      kclosed F_291c8 D_291c8 0%Z.   (* [comment removed for export] *)
      kclosed F_291cc D_291cc 1%Z.   (* [comment removed for export] *)
      stepb_tk F_291d0 D_291d0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_291d8 D_291d8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_rowset_c2. kpost.
  Qed.

  Lemma k2_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k2_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x292d8 : word) Mi rom) (mkst regs' (0x29304 : word) M' rom) /\ k2_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k2_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_291dc D_291dc ltac:(condZ).   (* [comment removed for export] *)
      sn F_291e0 D_291e0.   (* [comment removed for export] *)
      zvsl F_291e4 D_291e4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_291e8 D_291e8 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_291ec D_291ec 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_291f0 D_291f0 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_291f4 D_291f4 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_291f8 D_291f8 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_291fc D_291fc (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_29200 D_29200 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29204 D_29204 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_IN. kpost.
  Qed.

  Lemma k2_rowset : forall regs Mi i, (0 <= i < h)%Z -> k2_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29240 : word) Mi rom) (mkst regs' (0x29304 : word) M' rom) /\ k2_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k2_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k2_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k2_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k2_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k2_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29304 : word) Mi rom) (mkst regs' (0x29364 : word) M' rom) /\ k2_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k2_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29208 D_29208 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_2920c D_2920c.   (* [comment removed for export] *)
      snez_nz F_29210 D_29210 1%Z.   (* [comment removed for export] *)
      seqzx F_29214 D_29214 0%Z.   (* [comment removed for export] *)
      stepb_tk F_29218 D_29218 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29220 D_29220 0%Z.   (* [comment removed for export] *)
      zv F_29224 D_29224 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_29228 D_29228 1%Z.   (* [comment removed for export] *)
      kclosed F_2922c D_2922c 1%Z.   (* [comment removed for export] *)
      stepb_tk F_29230 D_29230 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29238 D_29238 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29240 D_29240 ltac:(condR).   (* [comment removed for export] *)
      stepb_tk F_29248 D_29248 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29250 D_29250 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29258 D_29258 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29260 D_29260 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_iter_c1. kpost.
  Qed.

  Definition k2_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 8 = (Z_to_bv 64 (datas - 4 * wpls)) /\ getr regs 9 = (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 12 = (Z_to_bv 64 (4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 19 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 20 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 21 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 22 = (Z_to_bv 64 (PW - j)) /\ getr regs 24 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 29 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (5)) /\ getr regs 31 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k2_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29364 : word) Mi rom) (mkst regs' (0x293ac : word) M' rom) /\ k2_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k2_iter_c1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepb_tk F_29268 D_29268 ltac:(condR).   (* [comment removed for export] *)
      zv F_29270 D_29270 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_tk F_29274 D_29274 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_2927c D_2927c bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29280 D_29280 bs1 v1 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29284 D_29284 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_29288 D_29288 bs3 v3 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_2928c D_2928c bs4 v4 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_29290 D_29290 bs5 v5 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_29294 D_29294.   (* [comment removed for export] *)
      sn F_29298 D_29298.   (* [comment removed for export] *)
      sn F_2929c D_2929c.   (* [comment removed for export] *)
      sn F_292a0 D_292a0.   (* [comment removed for export] *)
      sn F_292a4 D_292a4.   (* [comment removed for export] *)
      sn F_292a8 D_292a8.   (* [comment removed for export] *)
      sn F_292ac D_292ac.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_iter_c2. kpost.
  Qed.

  Lemma k2_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x293ac : word) Mi rom) (mkst regs' (0x293f4 : word) M' rom) /\ k2_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k2_iter_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_292b0 D_292b0.   (* [comment removed for export] *)
      sn F_292b4 D_292b4.   (* [comment removed for export] *)
      sn F_292b8 D_292b8.   (* [comment removed for export] *)
      sn F_292bc D_292bc.   (* [comment removed for export] *)
      sn F_292c0 D_292c0.   (* [comment removed for export] *)
      sn F_292c4 D_292c4.   (* [comment removed for export] *)
      sn F_292c8 D_292c8.   (* [comment removed for export] *)
      sn F_292cc D_292cc.   (* [comment removed for export] *)
      sn F_292d0 D_292d0.   (* [comment removed for export] *)
      sn F_292d4 D_292d4.   (* [comment removed for export] *)
      sn F_292d8 D_292d8.   (* [comment removed for export] *)
      sn F_292dc D_292dc.   (* [comment removed for export] *)
      sn F_292e0 D_292e0.   (* [comment removed for export] *)
      gsw F_292e4 D_292e4 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_tk F_292e8 D_292e8 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_292f0 D_292f0 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_292f4 D_292f4 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_BN. kpost.
  Qed.

  Lemma k2_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k2_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29304 : word) Mi rom) (mkst regs' (0x293f4 : word) M' rom) /\ k2_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k2_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k2_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k2_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Lemma k2_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k2_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x293f4 : word) Mi rom) (mkst regs' (0x29304 : word) M' rom) /\ k2_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k2_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_292f8 D_292f8 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_IN. kpost.
  Qed.

  Lemma k2_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k2_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x293f4 : word) Mi rom) (mkst regs' (0x29224 : word) M' rom) /\ k2_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k2_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_292f8 D_292f8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_292fc D_292fc.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RL. kpost.
  Qed.

  Lemma k2_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k2_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29224 : word) Mi rom) (mkst regs' (0x29240 : word) M' rom) /\ k2_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k2_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_29128 D_29128 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_2912c D_2912c (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29130 D_29130 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29134 D_29134 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29138 D_29138 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_2913c D_2913c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k2_RH. kpost.
  Qed.

  Lemma k2_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k2_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29224 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k2_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_29128 D_29128 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      zvaddw F_2912c D_2912c (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29130 D_29130 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29134 D_29134 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29138 D_29138 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_2913c D_2913c ltac:(condZ).   (* [comment removed for export] *)
      sn F_29140 D_29140.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k2_inner : forall regs Mi i, (0 <= i < h)%Z -> k2_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x29304 : word) Mi rom) (mkst regs' (0x29224 : word) M' rom) /\ k2_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x29304 : word) (0x29224 : word) (fun r m j => k2_IN r m i j) (fun r m => k2_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k2_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k2_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k2_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k2_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x291c0 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k2_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x29240 : word) (0x2a670 : word) (fun r m i => k2_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k2_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k2_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k2_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k2_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k3_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k3_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (PW - j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k3_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Definition k3_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).

  Definition k3_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (0)) /\ getr regs 13 = (Z_to_bv 64 (datas)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)) /\ getr regs 17 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)).
  Lemma k3_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x293fc : word) Mi rom) (mkst regs' (0x29444 : word) M' rom) /\ k3_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvw F_29300 D_29300 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_29304 D_29304 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2930c D_2930c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_29310 D_29310 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29318 D_29318.   (* [comment removed for export] *)
      sn F_2931c D_2931c.   (* [comment removed for export] *)
      sn F_29320 D_29320.   (* [comment removed for export] *)
      zvpw F_29324 D_29324.   (* [comment removed for export] *)
      stf F_29328 D_29328 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_2932c D_2932c (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      ldf F_29330 D_29330 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_29334 D_29334.   (* [comment removed for export] *)
      ldf F_29338 D_29338 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_2933c D_2933c.   (* [comment removed for export] *)
      snez_nz F_29340 D_29340 1%Z.   (* [comment removed for export] *)
      lineg F_29344 D_29344 18446744073709551611%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_pre_c1. kpost.
  Qed.

  Lemma k3_pre_s1 : forall regs Mi, k3_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29444 : word) Mi rom) (mkst regs' (0x29484 : word) M' rom) /\ k3_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k3_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      lineg F_29348 D_29348 18446744073709551615%Z.   (* [comment removed for export] *)
      zv F_2934c D_2934c (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_29350 D_29350 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_29354 D_29354 128%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zvn F_29358 D_29358 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_2935c D_2935c 120%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zvneg F_29360 D_29360 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_29364 D_29364.   (* [comment removed for export] *)
      sn F_29368 D_29368.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RH. kpost.
  Qed.

  Lemma k3_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x293fc : word) Mi rom) (mkst regs' (0x29484 : word) M' rom) /\ k3_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k3_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k3_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact H2].
  Qed.

  Definition k3_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (wpld)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k3_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k3_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29484 : word) Mi rom) (mkst regs' (0x294d0 : word) M' rom) /\ k3_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k3_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29388 D_29388 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvmulw F_2938c D_2938c (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_tk F_29390 D_29390 ltac:(condR).   (* [comment removed for export] *)
      zvw F_29398 D_29398 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_2939c D_2939c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_293a0 D_293a0 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_293a4 D_293a4 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_293a8 D_293a8 0%Z.   (* [comment removed for export] *)
      stepb_tk F_293ac D_293ac ltac:(condZ).   (* [comment removed for export] *)
      ldf F_293b4 D_293b4 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_293b8 D_293b8 0%Z.   (* [comment removed for export] *)
      slti_0 F_293bc D_293bc 0%Z.   (* [comment removed for export] *)
      kclosed F_293c0 D_293c0 0%Z.   (* [comment removed for export] *)
      kclosed F_293c4 D_293c4 1%Z.   (* [comment removed for export] *)
      stepb_tk F_293c8 D_293c8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_293d0 D_293d0 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_rowset_c1. kpost.
  Qed.

  Definition k3_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k3_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k3_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x294d0 : word) Mi rom) (mkst regs' (0x2951c : word) M' rom) /\ k3_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k3_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_293d4 D_293d4 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_293d8 D_293d8 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_tk F_293dc D_293dc ltac:(condR).   (* [comment removed for export] *)
      ldf F_293e4 D_293e4 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_293e8 D_293e8 1%Z.   (* [comment removed for export] *)
      zvw F_293ec D_293ec (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_293f0 D_293f0 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_293f4 D_293f4 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_293f8 D_293f8 0%Z.   (* [comment removed for export] *)
      stepb_tk F_293fc D_293fc ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29404 D_29404 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_29408 D_29408 0%Z.   (* [comment removed for export] *)
      slti_0 F_2940c D_2940c 0%Z.   (* [comment removed for export] *)
      kclosed F_29410 D_29410 0%Z.   (* [comment removed for export] *)
      kclosed F_29414 D_29414 1%Z.   (* [comment removed for export] *)
      stepb_tk F_29418 D_29418 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_rowset_c2. kpost.
  Qed.

  Lemma k3_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k3_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2951c : word) Mi rom) (mkst regs' (0x2955c : word) M' rom) /\ k3_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k3_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_29420 D_29420.   (* [comment removed for export] *)
      stepb_ft F_29424 D_29424 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29428 D_29428.   (* [comment removed for export] *)
      zvsl F_2942c D_2942c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zvsl F_29430 D_29430 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_29434 D_29434 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_29438 D_29438 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_2943c D_2943c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29440 D_29440 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_29444 D_29444 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29448 D_29448 128%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_2944c D_2944c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_29450 D_29450 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29454 D_29454 120%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29458 D_29458 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2945c D_2945c 136%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_IN. kpost.
  Qed.

  Lemma k3_rowset : forall regs Mi i, (0 <= i < h)%Z -> k3_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29484 : word) Mi rom) (mkst regs' (0x2955c : word) M' rom) /\ k3_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k3_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k3_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k3_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k3_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 13 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (PW - j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 27 = (Z_to_bv 64 (0)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k3_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2955c : word) Mi rom) (mkst regs' (0x295b8 : word) M' rom) /\ k3_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29460 D_29460 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_29464 D_29464.   (* [comment removed for export] *)
      snez_nz F_29468 D_29468 1%Z.   (* [comment removed for export] *)
      seqzx F_2946c D_2946c 0%Z.   (* [comment removed for export] *)
      stepb_tk F_29470 D_29470 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29478 D_29478 0%Z.   (* [comment removed for export] *)
      zv F_2947c D_2947c (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_29480 D_29480 1%Z.   (* [comment removed for export] *)
      kclosed F_29484 D_29484 1%Z.   (* [comment removed for export] *)
      stepb_tk F_29488 D_29488 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29490 D_29490 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_29498 D_29498 ltac:(condR).   (* [comment removed for export] *)
      stepb_tk F_294a0 D_294a0 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_294a8 D_294a8 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_294b0 D_294b0 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_294b8 D_294b8 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_iter_c1. kpost.
  Qed.

  Definition k3_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (PW - j)) /\ getr regs 27 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k3_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x295b8 : word) Mi rom) (mkst regs' (0x29608 : word) M' rom) /\ k3_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_iter_c1 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      zv F_294bc D_294bc (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_294c0 D_294c0 0%Z.   (* [comment removed for export] *)
      kclosed F_294c4 D_294c4 0%Z.   (* [comment removed for export] *)
      kclosed F_294c8 D_294c8 1%Z.   (* [comment removed for export] *)
      stepb_tk F_294cc D_294cc ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_294d4 D_294d4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_tk F_294dc D_294dc ltac:(condR).   (* [comment removed for export] *)
      zv F_294e4 D_294e4 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_tk F_294e8 D_294e8 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_294f0 D_294f0 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_294f4 D_294f4 bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_294f8 D_294f8 bs2 v2 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_294fc D_294fc bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_29500 D_29500 bs4 v4 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_29504 D_29504 bs5 v5 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_29508 D_29508.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_iter_c2. kpost.
  Qed.

  Definition k3_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 120 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 128 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 136 (Z_to_bv 64 (PW)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 6 = (Z_to_bv 64 (0)) /\ getr regs 7 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (4 * j)) /\ getr regs 11 = (Z_to_bv 64 ((i * wpls))) /\ getr regs 12 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 14 = (Z_to_bv 64 (w + 31)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 ((i * wpld))) /\ getr regs 17 = (Z_to_bv 64 (i)) /\ getr regs 18 = (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ getr regs 20 = (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ getr regs 21 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 23 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (PW - j)) /\ getr regs 27 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 28 = (Z_to_bv 64 (1)) /\ getr regs 30 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (datas + 4 * wpls)).
  Lemma k3_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29608 : word) Mi rom) (mkst regs' (0x29648 : word) M' rom) /\ k3_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_iter_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2950c D_2950c.   (* [comment removed for export] *)
      sn F_29510 D_29510.   (* [comment removed for export] *)
      sn F_29514 D_29514.   (* [comment removed for export] *)
      sn F_29518 D_29518.   (* [comment removed for export] *)
      sn F_2951c D_2951c.   (* [comment removed for export] *)
      sn F_29520 D_29520.   (* [comment removed for export] *)
      sn F_29524 D_29524.   (* [comment removed for export] *)
      sn F_29528 D_29528.   (* [comment removed for export] *)
      sn F_2952c D_2952c.   (* [comment removed for export] *)
      sn F_29530 D_29530.   (* [comment removed for export] *)
      sn F_29534 D_29534.   (* [comment removed for export] *)
      sn F_29538 D_29538.   (* [comment removed for export] *)
      sn F_2953c D_2953c.   (* [comment removed for export] *)
      sn F_29540 D_29540.   (* [comment removed for export] *)
      sn F_29544 D_29544.   (* [comment removed for export] *)
      sn F_29548 D_29548.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_iter_c3. kpost.
  Qed.

  Lemma k3_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29648 : word) Mi rom) (mkst regs' (0x29668 : word) M' rom) /\ k3_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k3_iter_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2954c D_2954c.   (* [comment removed for export] *)
      sn F_29550 D_29550.   (* [comment removed for export] *)
      sn F_29554 D_29554.   (* [comment removed for export] *)
      gsw F_29558 D_29558 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_tk F_2955c D_2955c ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29564 D_29564 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_29568 D_29568 (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_BN. kpost.
  Qed.

  Lemma k3_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k3_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2955c : word) Mi rom) (mkst regs' (0x29668 : word) M' rom) /\ k3_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k3_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k3_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k3_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k3_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Lemma k3_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k3_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29668 : word) Mi rom) (mkst regs' (0x2955c : word) M' rom) /\ k3_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k3_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_2956c D_2956c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_IN. kpost.
  Qed.

  Lemma k3_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k3_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29668 : word) Mi rom) (mkst regs' (0x29468 : word) M' rom) /\ k3_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k3_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2956c D_2956c ltac:(condZ).   (* [comment removed for export] *)
      sn F_29570 D_29570.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RL. kpost.
  Qed.

  Lemma k3_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k3_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29468 : word) Mi rom) (mkst regs' (0x29484 : word) M' rom) /\ k3_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k3_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_2936c D_2936c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29370 D_29370 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29374 D_29374 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29378 D_29378 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_2937c D_2937c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_29380 D_29380 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k3_RH. kpost.
  Qed.

  Lemma k3_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k3_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29468 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k3_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      zvw F_2936c D_2936c (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29370 D_29370 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      zvaddw F_29374 D_29374 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29378 D_29378 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_2937c D_2937c 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29380 D_29380 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29384 D_29384.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k3_inner : forall regs Mi i, (0 <= i < h)%Z -> k3_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x2955c : word) Mi rom) (mkst regs' (0x29468 : word) M' rom) /\ k3_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x2955c : word) (0x29468 : word) (fun r m j => k3_IN r m i j) (fun r m => k3_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k3_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k3_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k3_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k3_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x293fc : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k3_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x29484 : word) (0x2a670 : word) (fun r m i => k3_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k3_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k3_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k3_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k3_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
