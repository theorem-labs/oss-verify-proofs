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
  Definition k6_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 14 = (Z_to_bv 64 (i)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k6_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k6_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k6_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).

  Definition k6_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 (0)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 13 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)).
  Lemma k6_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29f68 : word) Mi rom) (mkst regs' (0x29fa8 : word) M' rom) /\ k6_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      kli F_29e6c D_29e6c 1073741824%Z.   (* [comment removed for export] *)
      zvaddw F_29e70 D_29e70 (Z_to_bv 64 (wpls + 1073741824)).   (* [comment removed for export] *)
      stepb_ft F_29e74 D_29e74 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29e78 D_29e78 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_29e7c D_29e7c 64%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_ft F_29e80 D_29e80 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29e84 D_29e84 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29e88 D_29e88 ltac:(condZ).   (* [comment removed for export] *)
      stf F_29e8c D_29e8c 80%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stf F_29e90 D_29e90 72%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_29e94 D_29e94.   (* [comment removed for export] *)
      zvslw F_29e98 D_29e98 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      ldf F_29e9c D_29e9c 64%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_29ea0 D_29ea0.   (* [comment removed for export] *)
      stf F_29ea4 D_29ea4 56%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_29ea8 D_29ea8 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_pre_c1. kpost.
  Qed.

  Definition k6_pre_c2 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 (0)) /\ cell Mi 80 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (datas)) /\ getr regs 12 = (Z_to_bv 64 (- datas + 18446744073709551616)) /\ getr regs 13 = (Z_to_bv 64 (8 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_pre_s1 : forall regs Mi, k6_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29fa8 : word) Mi rom) (mkst regs' (0x29fe8 : word) M' rom) /\ k6_pre_c2 regs' M'.
  Proof.
    intros regs Mi  HF. unfold k6_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      ldf F_29eac D_29eac 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_29eb0 D_29eb0.   (* [comment removed for export] *)
      stf F_29eb4 D_29eb4 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_29eb8 D_29eb8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_29ebc D_29ebc.   (* [comment removed for export] *)
      stf F_29ec0 D_29ec0 104%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      zvneg F_29ec4 D_29ec4 (Z_to_bv 64 (- datas + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_29ec8 D_29ec8.   (* [comment removed for export] *)
      stf F_29ecc D_29ecc 112%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      zvsl F_29ed0 D_29ed0 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_29ed4 D_29ed4 (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_29ed8 D_29ed8 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_29edc D_29edc (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      stf F_29ee0 D_29ee0 40%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zvn F_29ee4 D_29ee4 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29ee8 D_29ee8 32%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_pre_c2. kpost.
  Qed.

  Lemma k6_pre_s2 : forall regs Mi, k6_pre_c2 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29fe8 : word) Mi rom) (mkst regs' (0x2a034 : word) M' rom) /\ k6_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k6_pre_c2 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zv F_29eec D_29eec (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29ef0 D_29ef0 24%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29ef4 D_29ef4 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      stf F_29ef8 D_29ef8 16%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_29efc D_29efc (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29f00 D_29f00 8%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      lineg F_29f04 D_29f04 18446744073709551611%Z.   (* [comment removed for export] *)
      sn F_29f08 D_29f08.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RH. kpost.
  Qed.

  Lemma k6_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29f68 : word) Mi rom) (mkst regs' (0x2a034 : word) M' rom) /\ k6_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k6_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k6_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    destruct (k6_pre_s2 r2 M2  H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k6_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k6_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a034 : word) Mi rom) (mkst regs' (0x2a074 : word) M' rom) /\ k6_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k6_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29f38 D_29f38 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stf F_29f3c D_29f3c 96%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvmulw F_29f40 D_29f40 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_29f44 D_29f44 ltac:(condR).   (* [comment removed for export] *)
      ldf F_29f48 D_29f48 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      snez_nz F_29f4c D_29f4c 1%Z.   (* [comment removed for export] *)
      zvw F_29f50 D_29f50 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_29f54 D_29f54 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_29f58 D_29f58 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_29f5c D_29f5c 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29f60 D_29f60 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29f64 D_29f64 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_29f68 D_29f68 0%Z.   (* [comment removed for export] *)
      slti_0 F_29f6c D_29f6c 0%Z.   (* [comment removed for export] *)
      kclosed F_29f70 D_29f70 0%Z.   (* [comment removed for export] *)
      kclosed F_29f74 D_29f74 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_rowset_c1. kpost.
  Qed.

  Definition k6_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k6_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a074 : word) Mi rom) (mkst regs' (0x2a0b4 : word) M' rom) /\ k6_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k6_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29f78 D_29f78 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29f7c D_29f7c 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29f80 D_29f80 96%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zv F_29f84 D_29f84 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_29f88 D_29f88 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_ft F_29f8c D_29f8c ltac:(condR).   (* [comment removed for export] *)
      ldf F_29f90 D_29f90 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_29f94 D_29f94 1%Z.   (* [comment removed for export] *)
      zvw F_29f98 D_29f98 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_29f9c D_29f9c (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_29fa0 D_29fa0 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_29fa4 D_29fa4 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29fa8 D_29fa8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29fac D_29fac 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_29fb0 D_29fb0 0%Z.   (* [comment removed for export] *)
      slti_0 F_29fb4 D_29fb4 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_rowset_c2. kpost.
  Qed.

  Definition k6_rowset_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k6_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a0b4 : word) Mi rom) (mkst regs' (0x2a0f4 : word) M' rom) /\ k6_rowset_c3 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k6_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      kclosed F_29fb8 D_29fb8 0%Z.   (* [comment removed for export] *)
      kclosed F_29fbc D_29fbc 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29fc0 D_29fc0 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29fc4 D_29fc4 64%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_29fc8 D_29fc8.   (* [comment removed for export] *)
      stepb_ft F_29fcc D_29fcc ltac:(condZ).   (* [comment removed for export] *)
      sn F_29fd0 D_29fd0.   (* [comment removed for export] *)
      ldf F_29fd4 D_29fd4 80%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_29fd8 D_29fd8 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_29fdc D_29fdc 72%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_29fe0 D_29fe0 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_29fe4 D_29fe4 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_29fe8 D_29fe8 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      stf F_29fec D_29fec 128%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_29ff0 D_29ff0 16%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_29ff4 D_29ff4 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_rowset_c3. kpost.
  Qed.

  Lemma k6_rowset_s3 : forall regs Mi i, (0 <= i < h)%Z -> k6_rowset_c3 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a0f4 : word) Mi rom) (mkst regs' (0x2a12c : word) M' rom) /\ k6_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k6_rowset_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stf F_29ff8 D_29ff8 136%Z (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29ffc D_29ffc 48%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_2a000 D_2a000 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a004 D_2a004 40%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_2a008 D_2a008 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a00c D_2a00c 32%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a010 D_2a010 (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a014 D_2a014 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_2a018 D_2a018 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_2a01c D_2a01c 24%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a020 D_2a020 (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a024 D_2a024 8%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2a028 D_2a028 (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_2a02c D_2a02c 56%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_IN. kpost.
  Qed.

  Lemma k6_rowset : forall regs Mi i, (0 <= i < h)%Z -> k6_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a034 : word) Mi rom) (mkst regs' (0x2a12c : word) M' rom) /\ k6_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k6_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k6_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k6_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k6_rowset_s3 r3 M3 i HR0 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Definition k6_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a12c : word) Mi rom) (mkst regs' (0x2a16c : word) M' rom) /\ k6_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_2a030 D_2a030 (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_2a034 D_2a034.   (* [comment removed for export] *)
      snez_nz F_2a038 D_2a038 1%Z.   (* [comment removed for export] *)
      seqzx F_2a03c D_2a03c 0%Z.   (* [comment removed for export] *)
      stepb_ft F_2a040 D_2a040 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_2a044 D_2a044 0%Z.   (* [comment removed for export] *)
      zv F_2a048 D_2a048 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_2a04c D_2a04c 1%Z.   (* [comment removed for export] *)
      kclosed F_2a050 D_2a050 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a054 D_2a054 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a058 D_2a058 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a05c D_2a05c 120%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_2a060 D_2a060 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_2a064 D_2a064 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a068 D_2a068 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a06c D_2a06c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c1. kpost.
  Qed.

  Definition k6_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 9 = (Z_to_bv 64 (0)) /\ getr regs 10 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a16c : word) Mi rom) (mkst regs' (0x2a1ac : word) M' rom) /\ k6_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2a070 D_2a070 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a074 D_2a074 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_2a078 D_2a078 0%Z.   (* [comment removed for export] *)
      zv F_2a07c D_2a07c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_2a080 D_2a080 0%Z.   (* [comment removed for export] *)
      kclosed F_2a084 D_2a084 0%Z.   (* [comment removed for export] *)
      kclosed F_2a088 D_2a088 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a08c D_2a08c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a090 D_2a090 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a094 D_2a094 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a098 D_2a098 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a09c D_2a09c 112%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      slti_0 F_2a0a0 D_2a0a0 0%Z.   (* [comment removed for export] *)
      ldf F_2a0a4 D_2a0a4 136%Z (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_2a0a8 D_2a0a8 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_2a0ac D_2a0ac 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c2. kpost.
  Qed.

  Definition k6_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 9 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 10 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 23 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a1ac : word) Mi rom) (mkst regs' (0x2a1ec : word) M' rom) /\ k6_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      kclosed F_2a0b0 D_2a0b0 0%Z.   (* [comment removed for export] *)
      kclosed F_2a0b4 D_2a0b4 1%Z.   (* [comment removed for export] *)
      stepb_ft F_2a0b8 D_2a0b8 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a0bc D_2a0bc ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_2a0c0 D_2a0c0 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2a0c4 D_2a0c4 104%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_2a0c8 D_2a0c8 ltac:(condR).   (* [comment removed for export] *)
      ldf F_2a0cc D_2a0cc 128%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_2a0d0 D_2a0d0 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_2a0d4 D_2a0d4 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_2a0d8 D_2a0d8 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2a0dc D_2a0dc bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_2a0e0 D_2a0e0 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2a0e4 D_2a0e4 bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_2a0e8 D_2a0e8 bs4 v4 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_2a0ec D_2a0ec bs5 v5 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c3. kpost.
  Qed.

  Definition k6_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 9 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a1ec : word) Mi rom) (mkst regs' (0x2a22c : word) M' rom) /\ k6_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c3 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    eexists. eexists. split.
    -
      stepLD F_2a0f0 D_2a0f0 bs0 v0 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_2a0f4 D_2a0f4 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_2a0f8 D_2a0f8 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_2a0fc D_2a0fc bs3 v3 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_2a100 D_2a100 bs4 v4 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_2a104 D_2a104 bs5 v5 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      sn F_2a108 D_2a108.   (* [comment removed for export] *)
      sn F_2a10c D_2a10c.   (* [comment removed for export] *)
      sn F_2a110 D_2a110.   (* [comment removed for export] *)
      sn F_2a114 D_2a114.   (* [comment removed for export] *)
      sn F_2a118 D_2a118.   (* [comment removed for export] *)
      sn F_2a11c D_2a11c.   (* [comment removed for export] *)
      sn F_2a120 D_2a120.   (* [comment removed for export] *)
      sn F_2a124 D_2a124.   (* [comment removed for export] *)
      sn F_2a128 D_2a128.   (* [comment removed for export] *)
      sn F_2a12c D_2a12c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c4. kpost.
  Qed.

  Definition k6_iter_c5 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 9 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a22c : word) Mi rom) (mkst regs' (0x2a26c : word) M' rom) /\ k6_iter_c5 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a130 D_2a130.   (* [comment removed for export] *)
      sn F_2a134 D_2a134.   (* [comment removed for export] *)
      sn F_2a138 D_2a138.   (* [comment removed for export] *)
      sn F_2a13c D_2a13c.   (* [comment removed for export] *)
      sn F_2a140 D_2a140.   (* [comment removed for export] *)
      sn F_2a144 D_2a144.   (* [comment removed for export] *)
      sn F_2a148 D_2a148.   (* [comment removed for export] *)
      sn F_2a14c D_2a14c.   (* [comment removed for export] *)
      sn F_2a150 D_2a150.   (* [comment removed for export] *)
      sn F_2a154 D_2a154.   (* [comment removed for export] *)
      sn F_2a158 D_2a158.   (* [comment removed for export] *)
      sn F_2a15c D_2a15c.   (* [comment removed for export] *)
      sn F_2a160 D_2a160.   (* [comment removed for export] *)
      sn F_2a164 D_2a164.   (* [comment removed for export] *)
      sn F_2a168 D_2a168.   (* [comment removed for export] *)
      sn F_2a16c D_2a16c.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c5. kpost.
  Qed.

  Definition k6_iter_c6 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 24 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 40 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 56 (Z_to_bv 64 (PW)) /\ cell Mi 64 (Z_to_bv 64 (w + 31)) /\ cell Mi 72 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 80 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (i)) /\ cell Mi 104 (Z_to_bv 64 (0)) /\ cell Mi 112 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 120 (Z_to_bv 64 (0)) /\ cell Mi 128 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 136 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (PW - j)) /\ getr regs 9 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 20 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 22 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 24 = (Z_to_bv 64 (4 * j)) /\ getr regs 26 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ getr regs 27 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 30 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k6_iter_s5 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c5 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a26c : word) Mi rom) (mkst regs' (0x2a2ac : word) M' rom) /\ k6_iter_c6 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c5 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a170 D_2a170.   (* [comment removed for export] *)
      sn F_2a174 D_2a174.   (* [comment removed for export] *)
      sn F_2a178 D_2a178.   (* [comment removed for export] *)
      sn F_2a17c D_2a17c.   (* [comment removed for export] *)
      sn F_2a180 D_2a180.   (* [comment removed for export] *)
      sn F_2a184 D_2a184.   (* [comment removed for export] *)
      sn F_2a188 D_2a188.   (* [comment removed for export] *)
      sn F_2a18c D_2a18c.   (* [comment removed for export] *)
      sn F_2a190 D_2a190.   (* [comment removed for export] *)
      sn F_2a194 D_2a194.   (* [comment removed for export] *)
      sn F_2a198 D_2a198.   (* [comment removed for export] *)
      sn F_2a19c D_2a19c.   (* [comment removed for export] *)
      sn F_2a1a0 D_2a1a0.   (* [comment removed for export] *)
      sn F_2a1a4 D_2a1a4.   (* [comment removed for export] *)
      sn F_2a1a8 D_2a1a8.   (* [comment removed for export] *)
      sn F_2a1ac D_2a1ac.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_iter_c6. kpost.
  Qed.

  Lemma k6_iter_s6 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_iter_c6 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2ac : word) Mi rom) (mkst regs' (0x2a2ec : word) M' rom) /\ k6_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k6_iter_c6 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2a1b0 D_2a1b0.   (* [comment removed for export] *)
      sn F_2a1b4 D_2a1b4.   (* [comment removed for export] *)
      sn F_2a1b8 D_2a1b8.   (* [comment removed for export] *)
      sn F_2a1bc D_2a1bc.   (* [comment removed for export] *)
      sn F_2a1c0 D_2a1c0.   (* [comment removed for export] *)
      sn F_2a1c4 D_2a1c4.   (* [comment removed for export] *)
      sn F_2a1c8 D_2a1c8.   (* [comment removed for export] *)
      sn F_2a1cc D_2a1cc.   (* [comment removed for export] *)
      sn F_2a1d0 D_2a1d0.   (* [comment removed for export] *)
      sn F_2a1d4 D_2a1d4.   (* [comment removed for export] *)
      sn F_2a1d8 D_2a1d8.   (* [comment removed for export] *)
      sn F_2a1dc D_2a1dc.   (* [comment removed for export] *)
      gsw F_2a1e0 D_2a1e0 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_ft F_2a1e4 D_2a1e4 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_2a1e8 D_2a1e8 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_2a1ec D_2a1ec (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_BN. kpost.
  Qed.

  Lemma k6_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k6_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a12c : word) Mi rom) (mkst regs' (0x2a2ec : word) M' rom) /\ k6_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k6_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k6_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k6_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k6_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k6_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    destruct (k6_iter_s5 r5 M5 i j HR0 HR1 H5) as (r6 & M6 & RUN6 & H6).
    destruct (k6_iter_s6 r6 M6 i j HR0 HR1 H6) as (r7 & M7 & RUN7 & H7).
    exists r7, M7. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]] | exact H7].
  Qed.

  Lemma k6_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k6_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2ec : word) Mi rom) (mkst regs' (0x2a12c : word) M' rom) /\ k6_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k6_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_2a1f0 D_2a1f0 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_IN. kpost.
  Qed.

  Lemma k6_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k6_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x2a2ec : word) Mi rom) (mkst regs' (0x2a008 : word) M' rom) /\ k6_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k6_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2a1f0 D_2a1f0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_2a1f4 D_2a1f4.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RL. kpost.
  Qed.

  Lemma k6_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k6_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a008 : word) Mi rom) (mkst regs' (0x2a034 : word) M' rom) /\ k6_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k6_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29f0c D_29f0c 96%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29f10 D_29f10 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29f14 D_29f14 72%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29f18 D_29f18 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29f1c D_29f1c 72%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29f20 D_29f20 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29f24 D_29f24 80%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29f28 D_29f28 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29f2c D_29f2c 80%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29f30 D_29f30 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29f34 D_29f34 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k6_RH. kpost.
  Qed.

  Lemma k6_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k6_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2a008 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k6_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29f0c D_29f0c 96%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29f10 D_29f10 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_29f14 D_29f14 72%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29f18 D_29f18 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29f1c D_29f1c 72%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29f20 D_29f20 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29f24 D_29f24 80%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29f28 D_29f28 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29f2c D_29f2c 80%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29f30 D_29f30 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_29f34 D_29f34 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k6_inner : forall regs Mi i, (0 <= i < h)%Z -> k6_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x2a12c : word) Mi rom) (mkst regs' (0x2a008 : word) M' rom) /\ k6_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x2a12c : word) (0x2a008 : word) (fun r m j => k6_IN r m i j) (fun r m => k6_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k6_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k6_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k6_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k6_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29f68 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k6_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x2a034 : word) (0x2a670 : word) (fun r m i => k6_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k6_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k6_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k6_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k6_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.

  (* [comment removed for export] *)
  Definition k7_RH (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (i)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k7_IN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k7_BN (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j - 1)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j + 4)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Definition k7_RL (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).

  Definition k7_pre_c1 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 (0)) /\ cell Mi 72 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 14 = (Z_to_bv 64 (2 * wpls)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)).
  Lemma k7_pre_s0 : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29670 : word) Mi rom) (mkst regs' (0x296b8 : word) M' rom) /\ k7_pre_c1 regs' M'.
  Proof.
    intros regs Mi  HF. kdestruct HF.
    eexists. eexists. split.
    -
      kli F_29574 D_29574 1073741824%Z.   (* [comment removed for export] *)
      zvaddw F_29578 D_29578 (Z_to_bv 64 (wpls + 1073741824)).   (* [comment removed for export] *)
      stepb_tk F_2957c D_2957c ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29584 D_29584 (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stf F_29588 D_29588 56%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      stepb_tk F_2958c D_2958c ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29594 D_29594 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_29598 D_29598 ltac:(condZ).   (* [comment removed for export] *)
      stf F_2959c D_2959c 72%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stf F_295a0 D_295a0 64%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      sn F_295a4 D_295a4.   (* [comment removed for export] *)
      zvslw F_295a8 D_295a8 (Z_to_bv 64 (2 * wpls)) 2%Z.   (* [comment removed for export] *)
      ldf F_295ac D_295ac 56%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      zvpw F_295b0 D_295b0.   (* [comment removed for export] *)
      stf F_295b4 D_295b4 48%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      zvsl F_295b8 D_295b8 (Z_to_bv 64 (4 * wpls)) 4%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_pre_c1. kpost.
  Qed.

  Definition k7_pre_c2 (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    MInv Mi /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 (0)) /\ cell Mi 72 (Z_to_bv 64 (0)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * wpls)) /\ getr regs 11 = (Z_to_bv 64 (datas)) /\ getr regs 12 = (Z_to_bv 64 (- datas + 18446744073709551616)) /\ getr regs 13 = (Z_to_bv 64 (18446744073709551615)) /\ getr regs 14 = (Z_to_bv 64 (8 * wpls)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 16 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_pre_s1 : forall regs Mi, k7_pre_c1 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x296b8 : word) Mi rom) (mkst regs' (0x296f8 : word) M' rom) /\ k7_pre_c2 regs' M'.
  Proof.
    intros regs Mi  HF. unfold k7_pre_c1 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      ldf F_295bc D_295bc 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      andi3 F_295c0 D_295c0.   (* [comment removed for export] *)
      stf F_295c4 D_295c4 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      ldf F_295c8 D_295c8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      andi3 F_295cc D_295cc.   (* [comment removed for export] *)
      stf F_295d0 D_295d0 96%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      zvneg F_295d4 D_295d4 (Z_to_bv 64 (- datas + 18446744073709551616)).   (* [comment removed for export] *)
      sn F_295d8 D_295d8.   (* [comment removed for export] *)
      lineg F_295dc D_295dc 18446744073709551611%Z.   (* [comment removed for export] *)
      lineg F_295e0 D_295e0 18446744073709551615%Z.   (* [comment removed for export] *)
      stf F_295e4 D_295e4 104%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      zvsl F_295e8 D_295e8 (Z_to_bv 64 (8 * wpls)) 4%Z.   (* [comment removed for export] *)
      zv F_295ec D_295ec (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      stf F_295f0 D_295f0 40%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_295f4 D_295f4 (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      stf F_295f8 D_295f8 32%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_pre_c2. kpost.
  Qed.

  Lemma k7_pre_s2 : forall regs Mi, k7_pre_c2 regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x296f8 : word) Mi rom) (mkst regs' (0x2974c : word) M' rom) /\ k7_RH regs' M' 0.
  Proof.
    intros regs Mi  HF. unfold k7_pre_c2 in HF. kdestruct HF.
    eexists. eexists. split.
    -
      zvn F_295fc D_295fc (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29600 D_29600 24%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29604 D_29604 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29608 D_29608 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2960c D_2960c (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      stf F_29610 D_29610 8%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29614 D_29614 (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      stf F_29618 D_29618 0%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      sn F_2961c D_2961c.   (* [comment removed for export] *)
      sn F_29620 D_29620.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RH. kpost.
  Qed.

  Lemma k7_pre : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29670 : word) Mi rom) (mkst regs' (0x2974c : word) M' rom) /\ k7_RH regs' M' 0.
  Proof.
    intros regs Mi  H0.
    destruct (k7_pre_s0 regs Mi  H0) as (r1 & M1 & RUN1 & H1).
    destruct (k7_pre_s1 r1 M1  H1) as (r2 & M2 & RUN2 & H2).
    destruct (k7_pre_s2 r2 M2  H2) as (r3 & M3 & RUN3 & H3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
  Qed.

  Definition k7_rowset_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (1)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_rowset_s0 : forall regs Mi i, (0 <= i < h)%Z -> k7_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2974c : word) Mi rom) (mkst regs' (0x2978c : word) M' rom) /\ k7_rowset_c1 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k7_RH in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_29650 D_29650 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stf F_29654 D_29654 80%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvmulw F_29658 D_29658 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      stepb_ft F_2965c D_2965c ltac:(condR).   (* [comment removed for export] *)
      ldf F_29660 D_29660 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      snez_nz F_29664 D_29664 1%Z.   (* [comment removed for export] *)
      zvw F_29668 D_29668 (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_2966c D_2966c (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      zv F_29670 D_29670 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      seqz_nz F_29674 D_29674 0%Z.   (* [comment removed for export] *)
      stepb_ft F_29678 D_29678 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2967c D_2967c 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      sltu_0 F_29680 D_29680 0%Z.   (* [comment removed for export] *)
      slti_0 F_29684 D_29684 0%Z.   (* [comment removed for export] *)
      kclosed F_29688 D_29688 0%Z.   (* [comment removed for export] *)
      kclosed F_2968c D_2968c 1%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_rowset_c1. kpost.
  Qed.

  Definition k7_rowset_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (0)) /\ getr regs 12 = (Z_to_bv 64 (0)) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_rowset_s1 : forall regs Mi i, (0 <= i < h)%Z -> k7_rowset_c1 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2978c : word) Mi rom) (mkst regs' (0x297cc : word) M' rom) /\ k7_rowset_c2 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k7_rowset_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29690 D_29690 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_29694 D_29694 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_29698 D_29698 80%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zv F_2969c D_2969c (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvmulw F_296a0 D_296a0 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      stepb_ft F_296a4 D_296a4 ltac:(condR).   (* [comment removed for export] *)
      ldf F_296a8 D_296a8 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      snez_nz F_296ac D_296ac 1%Z.   (* [comment removed for export] *)
      zvw F_296b0 D_296b0 (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_296b4 D_296b4 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      zv F_296b8 D_296b8 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      seqz_nz F_296bc D_296bc 0%Z.   (* [comment removed for export] *)
      stepb_ft F_296c0 D_296c0 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_296c4 D_296c4 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      sltu_0 F_296c8 D_296c8 0%Z.   (* [comment removed for export] *)
      slti_0 F_296cc D_296cc 0%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_rowset_c2. kpost.
  Qed.

  Definition k7_rowset_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 10 = (Z_to_bv 64 (4 * (i * wpls))) /\ getr regs 11 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 25 = (Z_to_bv 64 (0)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_rowset_s2 : forall regs Mi i, (0 <= i < h)%Z -> k7_rowset_c2 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x297cc : word) Mi rom) (mkst regs' (0x2980c : word) M' rom) /\ k7_rowset_c3 regs' M' i.
  Proof.
    intros regs Mi i HR0 HF. unfold k7_rowset_c2 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      kclosed F_296d0 D_296d0 0%Z.   (* [comment removed for export] *)
      kclosed F_296d4 D_296d4 1%Z.   (* [comment removed for export] *)
      stepb_ft F_296d8 D_296d8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_296dc D_296dc 56%Z (Z_to_bv 64 (w + 31)).   (* [comment removed for export] *)
      sn F_296e0 D_296e0.   (* [comment removed for export] *)
      stepb_ft F_296e4 D_296e4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_296e8 D_296e8.   (* [comment removed for export] *)
      ldf F_296ec D_296ec 72%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvsl F_296f0 D_296f0 (Z_to_bv 64 (4 * (i * wpld))) 4%Z.   (* [comment removed for export] *)
      ldf F_296f4 D_296f4 64%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvsl F_296f8 D_296f8 (Z_to_bv 64 (4 * (i * wpls))) 4%Z.   (* [comment removed for export] *)
      ldf F_296fc D_296fc 152%Z (Z_to_bv 64 (datad)).   (* [comment removed for export] *)
      zv F_29700 D_29700 (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      stf F_29704 D_29704 120%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      ldf F_29708 D_29708 0%Z (Z_to_bv 64 (datas + 8 * wpls)).   (* [comment removed for export] *)
      zv F_2970c D_2970c (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_rowset_c3. kpost.
  Qed.

  Lemma k7_rowset_s3 : forall regs Mi i, (0 <= i < h)%Z -> k7_rowset_c3 regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2980c : word) Mi rom) (mkst regs' (0x29848 : word) M' rom) /\ k7_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 HF. unfold k7_rowset_c3 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stf F_29710 D_29710 128%Z (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29714 D_29714 40%Z (Z_to_bv 64 (datas - 4 * wpls)).   (* [comment removed for export] *)
      zv F_29718 D_29718 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      stf F_2971c D_2971c 136%Z (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29720 D_29720 32%Z (Z_to_bv 64 (datas + 4 * wpls)).   (* [comment removed for export] *)
      zv F_29724 D_29724 (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29728 D_29728 24%Z (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2972c D_2972c (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29730 D_29730 160%Z (Z_to_bv 64 (datas)).   (* [comment removed for export] *)
      zv F_29734 D_29734 (Z_to_bv 64 (datas + 4 * (i * wpls))).   (* [comment removed for export] *)
      ldf F_29738 D_29738 16%Z (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_2973c D_2973c (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29740 D_29740 8%Z (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)).   (* [comment removed for export] *)
      zv F_29744 D_29744 (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)).   (* [comment removed for export] *)
      ldf F_29748 D_29748 48%Z (Z_to_bv 64 (PW)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_IN. kpost.
  Qed.

  Lemma k7_rowset : forall regs Mi i, (0 <= i < h)%Z -> k7_RH regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x2974c : word) Mi rom) (mkst regs' (0x29848 : word) M' rom) /\ k7_IN regs' M' i 0.
  Proof.
    intros regs Mi i HR0 H0.
    destruct (k7_rowset_s0 regs Mi i HR0 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k7_rowset_s1 r1 M1 i HR0 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k7_rowset_s2 r2 M2 i HR0 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k7_rowset_s3 r3 M3 i HR0 H3) as (r4 & M4 & RUN4 & H4).
    exists r4, M4. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] | exact H4].
  Qed.

  Definition k7_iter_c1 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s0 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29848 : word) Mi rom) (mkst regs' (0x29888 : word) M' rom) /\ k7_iter_c1 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_IN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      zv F_2974c D_2974c (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sn F_29750 D_29750.   (* [comment removed for export] *)
      snez_nz F_29754 D_29754 1%Z.   (* [comment removed for export] *)
      seqzx F_29758 D_29758 0%Z.   (* [comment removed for export] *)
      stepb_ft F_2975c D_2975c ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29760 D_29760 0%Z.   (* [comment removed for export] *)
      ldf F_29764 D_29764 136%Z (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_29768 D_29768 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_1 F_2976c D_2976c 1%Z.   (* [comment removed for export] *)
      kclosed F_29770 D_29770 1%Z.   (* [comment removed for export] *)
      stepb_ft F_29774 D_29774 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29778 D_29778 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_2977c D_2977c 112%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_29780 D_29780 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_29784 D_29784 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29788 D_29788 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c1. kpost.
  Qed.

  Definition k7_iter_c2 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 12 = (Z_to_bv 64 (datas + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (0)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s1 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c1 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29888 : word) Mi rom) (mkst regs' (0x298c8 : word) M' rom) /\ k7_iter_c2 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c1 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_2978c D_2978c ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29790 D_29790 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_29794 D_29794 ltac:(condZ).   (* [comment removed for export] *)
      slti_0 F_29798 D_29798 0%Z.   (* [comment removed for export] *)
      zv F_2979c D_2979c (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      sltu_0 F_297a0 D_297a0 0%Z.   (* [comment removed for export] *)
      kclosed F_297a4 D_297a4 0%Z.   (* [comment removed for export] *)
      kclosed F_297a8 D_297a8 1%Z.   (* [comment removed for export] *)
      stepb_ft F_297ac D_297ac ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_297b0 D_297b0 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_297b4 D_297b4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_297b8 D_297b8 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_297bc D_297bc 104%Z (Z_to_bv 64 (2 * wpls)).   (* [comment removed for export] *)
      slti_0 F_297c0 D_297c0 0%Z.   (* [comment removed for export] *)
      ldf F_297c4 D_297c4 128%Z (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))).   (* [comment removed for export] *)
      zv F_297c8 D_297c8 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c2. kpost.
  Qed.

  Definition k7_iter_c3 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 10 = (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 13 = (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 24 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s2 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c2 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x298c8 : word) Mi rom) (mkst regs' (0x29908 : word) M' rom) /\ k7_iter_c3 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c2 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    eexists. eexists. split.
    -
      sltu_0 F_297cc D_297cc 0%Z.   (* [comment removed for export] *)
      kclosed F_297d0 D_297d0 0%Z.   (* [comment removed for export] *)
      kclosed F_297d4 D_297d4 1%Z.   (* [comment removed for export] *)
      stepb_ft F_297d8 D_297d8 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_297dc D_297dc ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_297e0 D_297e0 ltac:(condZ).   (* [comment removed for export] *)
      ldf F_297e4 D_297e4 96%Z (Z_to_bv 64 (0)).   (* [comment removed for export] *)
      stepb_ft F_297e8 D_297e8 ltac:(condR).   (* [comment removed for export] *)
      ldf F_297ec D_297ec 120%Z (Z_to_bv 64 (datad + 4 * (i * wpld))).   (* [comment removed for export] *)
      zv F_297f0 D_297f0 (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)).   (* [comment removed for export] *)
      stepb_ft F_297f4 D_297f4 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_297f8 D_297f8 bs0 v0 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_297fc D_297fc bs1 v1 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29800 D_29800 bs2 v2 ltac:(rdn_addr (datas + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_29804 D_29804 bs3 v3 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_29808 D_29808 bs4 v4 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c3. kpost.
  Qed.

  Definition k7_iter_c4 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s3 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c3 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29908 : word) Mi rom) (mkst regs' (0x29948 : word) M' rom) /\ k7_iter_c4 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c3 in HF. kdestruct HF. ibound HR0.
    destruct (rd_src4 Mi (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs0 & v0 & Hb0 & Hv0).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs1 & v1 & Hb1 & Hv1).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs2 & v2 & Hb2 & Hv2).
    destruct (rd_src4 Mi (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs3 & v3 & Hb3 & Hv3).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs4 & v4 & Hb4 & Hv4).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z HIvG ltac:(lia) ltac:(lia)) as (bs5 & v5 & Hb5 & Hv5).
    destruct (rd_src4 Mi (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z HIvG ltac:(lia) ltac:(lia)) as (bs6 & v6 & Hb6 & Hv6).
    eexists. eexists. split.
    -
      stepLD F_2980c D_2980c bs0 v0 ltac:(rdn_addr (datas - 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb0) ltac:(exact Hv0).   (* [comment removed for export] *)
      stepLD F_29810 D_29810 bs1 v1 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb1) ltac:(exact Hv1).   (* [comment removed for export] *)
      stepLD F_29814 D_29814 bs2 v2 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb2) ltac:(exact Hv2).   (* [comment removed for export] *)
      stepLD F_29818 D_29818 bs3 v3 ltac:(rdn_addr (datas + 4 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb3) ltac:(exact Hv3).   (* [comment removed for export] *)
      stepLD F_2981c D_2981c bs4 v4 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j - 4)%Z; exact Hb4) ltac:(exact Hv4).   (* [comment removed for export] *)
      stepLD F_29820 D_29820 bs5 v5 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j)%Z; exact Hb5) ltac:(exact Hv5).   (* [comment removed for export] *)
      stepLD F_29824 D_29824 bs6 v6 ltac:(rdn_addr (datas + 8 * wpls + 4 * (i * wpls) + 4 * j + 4)%Z; exact Hb6) ltac:(exact Hv6).   (* [comment removed for export] *)
      sn F_29828 D_29828.   (* [comment removed for export] *)
      sn F_2982c D_2982c.   (* [comment removed for export] *)
      sn F_29830 D_29830.   (* [comment removed for export] *)
      sn F_29834 D_29834.   (* [comment removed for export] *)
      sn F_29838 D_29838.   (* [comment removed for export] *)
      sn F_2983c D_2983c.   (* [comment removed for export] *)
      sn F_29840 D_29840.   (* [comment removed for export] *)
      sn F_29844 D_29844.   (* [comment removed for export] *)
      sn F_29848 D_29848.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c4. kpost.
  Qed.

  Definition k7_iter_c5 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s4 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c4 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29948 : word) Mi rom) (mkst regs' (0x29988 : word) M' rom) /\ k7_iter_c5 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c4 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2984c D_2984c.   (* [comment removed for export] *)
      sn F_29850 D_29850.   (* [comment removed for export] *)
      sn F_29854 D_29854.   (* [comment removed for export] *)
      sn F_29858 D_29858.   (* [comment removed for export] *)
      sn F_2985c D_2985c.   (* [comment removed for export] *)
      sn F_29860 D_29860.   (* [comment removed for export] *)
      sn F_29864 D_29864.   (* [comment removed for export] *)
      sn F_29868 D_29868.   (* [comment removed for export] *)
      sn F_2986c D_2986c.   (* [comment removed for export] *)
      sn F_29870 D_29870.   (* [comment removed for export] *)
      sn F_29874 D_29874.   (* [comment removed for export] *)
      sn F_29878 D_29878.   (* [comment removed for export] *)
      sn F_2987c D_2987c.   (* [comment removed for export] *)
      sn F_29880 D_29880.   (* [comment removed for export] *)
      sn F_29884 D_29884.   (* [comment removed for export] *)
      sn F_29888 D_29888.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c5. kpost.
  Qed.

  Definition k7_iter_c6 (regs : bvmap 5 word) (Mi : word -> option byte) (i j : Z) : Prop :=
    MInv Mi /\ cell Mi 0 (Z_to_bv 64 (datas + 8 * wpls)) /\ cell Mi 8 (Z_to_bv 64 (- datas - 8 * wpls + 18446744073709551616)) /\ cell Mi 16 (Z_to_bv 64 (- datas - 4 * wpls + 18446744073709551616)) /\ cell Mi 24 (Z_to_bv 64 (- datas + 4 * wpls + 18446744073709551616)) /\ cell Mi 32 (Z_to_bv 64 (datas + 4 * wpls)) /\ cell Mi 40 (Z_to_bv 64 (datas - 4 * wpls)) /\ cell Mi 48 (Z_to_bv 64 (PW)) /\ cell Mi 56 (Z_to_bv 64 (w + 31)) /\ cell Mi 64 (Z_to_bv 64 ((i * wpls))) /\ cell Mi 72 (Z_to_bv 64 ((i * wpld))) /\ cell Mi 80 (Z_to_bv 64 (i)) /\ cell Mi 88 (Z_to_bv 64 (h)) /\ cell Mi 96 (Z_to_bv 64 (0)) /\ cell Mi 104 (Z_to_bv 64 (2 * wpls)) /\ cell Mi 112 (Z_to_bv 64 (0)) /\ cell Mi 120 (Z_to_bv 64 (datad + 4 * (i * wpld))) /\ cell Mi 128 (Z_to_bv 64 (datas + 8 * wpls + 4 * (i * wpls))) /\ cell Mi 136 (Z_to_bv 64 (datas - 4 * wpls + 4 * (i * wpls))) /\ cell Mi 144 (Z_to_bv 64 (wpld)) /\ cell Mi 152 (Z_to_bv 64 (datad)) /\ cell Mi 160 (Z_to_bv 64 (datas)) /\ getr regs 1 = (Z_to_bv 64 (datas + 4 * wpls + 4 * (i * wpls))) /\ getr regs 2 = (Z_to_bv 64 (sp)) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\ getr regs 7 = (Z_to_bv 64 (- datas + 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 8 = (Z_to_bv 64 (18446744073709551611)) /\ getr regs 9 = (Z_to_bv 64 (- datas - 4 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 14 = (Z_to_bv 64 (datas + 4 * (i * wpls))) /\ getr regs 15 = (Z_to_bv 64 (wpls)) /\ getr regs 18 = (Z_to_bv 64 (PW - j)) /\ getr regs 19 = (Z_to_bv 64 (datad + 4 * (i * wpld) + 4 * j)) /\ getr regs 20 = (Z_to_bv 64 (- datas - 8 * wpls - 4 * (i * wpls) + 18446744073709551616)) /\ getr regs 25 = (Z_to_bv 64 (4 * j)) /\ getr regs 31 = (Z_to_bv 64 (5)).
  Lemma k7_iter_s5 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c5 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29988 : word) Mi rom) (mkst regs' (0x299c8 : word) M' rom) /\ k7_iter_c6 regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c5 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_2988c D_2988c.   (* [comment removed for export] *)
      sn F_29890 D_29890.   (* [comment removed for export] *)
      sn F_29894 D_29894.   (* [comment removed for export] *)
      sn F_29898 D_29898.   (* [comment removed for export] *)
      sn F_2989c D_2989c.   (* [comment removed for export] *)
      sn F_298a0 D_298a0.   (* [comment removed for export] *)
      sn F_298a4 D_298a4.   (* [comment removed for export] *)
      sn F_298a8 D_298a8.   (* [comment removed for export] *)
      sn F_298ac D_298ac.   (* [comment removed for export] *)
      sn F_298b0 D_298b0.   (* [comment removed for export] *)
      sn F_298b4 D_298b4.   (* [comment removed for export] *)
      sn F_298b8 D_298b8.   (* [comment removed for export] *)
      sn F_298bc D_298bc.   (* [comment removed for export] *)
      sn F_298c0 D_298c0.   (* [comment removed for export] *)
      sn F_298c4 D_298c4.   (* [comment removed for export] *)
      sn F_298c8 D_298c8.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_iter_c6. kpost.
  Qed.

  Lemma k7_iter_s6 : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_iter_c6 regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x299c8 : word) Mi rom) (mkst regs' (0x29a0c : word) M' rom) /\ k7_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 HF. unfold k7_iter_c6 in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      sn F_298cc D_298cc.   (* [comment removed for export] *)
      sn F_298d0 D_298d0.   (* [comment removed for export] *)
      sn F_298d4 D_298d4.   (* [comment removed for export] *)
      sn F_298d8 D_298d8.   (* [comment removed for export] *)
      sn F_298dc D_298dc.   (* [comment removed for export] *)
      sn F_298e0 D_298e0.   (* [comment removed for export] *)
      sn F_298e4 D_298e4.   (* [comment removed for export] *)
      sn F_298e8 D_298e8.   (* [comment removed for export] *)
      sn F_298ec D_298ec.   (* [comment removed for export] *)
      sn F_298f0 D_298f0.   (* [comment removed for export] *)
      sn F_298f4 D_298f4.   (* [comment removed for export] *)
      sn F_298f8 D_298f8.   (* [comment removed for export] *)
      sn F_298fc D_298fc.   (* [comment removed for export] *)
      gsw F_29900 D_29900 (datad + 4 * (i * wpld) + 4 * j)%Z.   (* [comment removed for export] *)
      stepb_ft F_29904 D_29904 ltac:(condZ).   (* [comment removed for export] *)
      zvw F_29908 D_29908 (Z_to_bv 64 (PW - j - 1)).   (* [comment removed for export] *)
      zv F_2990c D_2990c (Z_to_bv 64 (4 * j + 4)).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_BN. kpost.
  Qed.

  Lemma k7_iter : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j < PW)%Z -> k7_IN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29848 : word) Mi rom) (mkst regs' (0x29a0c : word) M' rom) /\ k7_BN regs' M' i j.
  Proof.
    intros regs Mi i j HR0 HR1 H0.
    destruct (k7_iter_s0 regs Mi i j HR0 HR1 H0) as (r1 & M1 & RUN1 & H1).
    destruct (k7_iter_s1 r1 M1 i j HR0 HR1 H1) as (r2 & M2 & RUN2 & H2).
    destruct (k7_iter_s2 r2 M2 i j HR0 HR1 H2) as (r3 & M3 & RUN3 & H3).
    destruct (k7_iter_s3 r3 M3 i j HR0 HR1 H3) as (r4 & M4 & RUN4 & H4).
    destruct (k7_iter_s4 r4 M4 i j HR0 HR1 H4) as (r5 & M5 & RUN5 & H5).
    destruct (k7_iter_s5 r5 M5 i j HR0 HR1 H5) as (r6 & M6 & RUN6 & H6).
    destruct (k7_iter_s6 r6 M6 i j HR0 HR1 H6) as (r7 & M7 & RUN7 & H7).
    exists r7, M7. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 | eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]] | exact H7].
  Qed.

  Lemma k7_back : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 < PW)%Z -> k7_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29a0c : word) Mi rom) (mkst regs' (0x29848 : word) M' rom) /\ k7_IN regs' M' i (j + 1).
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k7_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_tk F_29910 D_29910 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_IN. kpost.
  Qed.

  Lemma k7_out : forall regs Mi i j, (0 <= i < h)%Z -> (0 <= j)%Z -> (j + 1 = PW)%Z -> k7_BN regs Mi i j ->
    exists regs' M', msteps SEGS (mkst regs (0x29a0c : word) Mi rom) (mkst regs' (0x29720 : word) M' rom) /\ k7_RL regs' M' i.
  Proof.
    intros regs Mi i j HR0 HR1 HR2 HF. unfold k7_BN in HF. kdestruct HF. ibound HR0.
    eexists. eexists. split.
    -
      stepb_ft F_29910 D_29910 ltac:(condZ).   (* [comment removed for export] *)
      sn F_29914 D_29914.   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RL. kpost.
  Qed.

  Lemma k7_latch : forall regs Mi i, (0 <= i)%Z -> (i + 1 < h)%Z -> k7_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29720 : word) Mi rom) (mkst regs' (0x2974c : word) M' rom) /\ k7_RH regs' M' (i + 1).
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k7_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29624 D_29624 80%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29628 D_29628 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_2962c D_2962c 64%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29630 D_29630 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29634 D_29634 64%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29638 D_29638 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_2963c D_2963c 72%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29640 D_29640 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29644 D_29644 72%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29648 D_29648 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_ft F_2964c D_2964c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold k7_RH. kpost.
  Qed.

  Lemma k7_exit : forall regs Mi i, (0 <= i)%Z -> (i + 1 = h)%Z -> k7_RL regs Mi i ->
    exists regs' M', msteps SEGS (mkst regs (0x29720 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof.
    intros regs Mi i HR0 HR1 HF. unfold k7_RL in HF. kdestruct HF. ibound1 HR0 HR1.
    eexists. eexists. split.
    -
      ldf F_29624 D_29624 80%Z (Z_to_bv 64 (i)).   (* [comment removed for export] *)
      zvw F_29628 D_29628 (Z_to_bv 64 (i + 1)).   (* [comment removed for export] *)
      ldf F_2962c D_2962c 64%Z (Z_to_bv 64 ((i * wpls))).   (* [comment removed for export] *)
      zvaddw F_29630 D_29630 (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      stf F_29634 D_29634 64%Z (Z_to_bv 64 (wpls + (i * wpls))).   (* [comment removed for export] *)
      ldf F_29638 D_29638 144%Z (Z_to_bv 64 (wpld)).   (* [comment removed for export] *)
      ldf F_2963c D_2963c 72%Z (Z_to_bv 64 ((i * wpld))).   (* [comment removed for export] *)
      zvaddw F_29640 D_29640 (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      stf F_29644 D_29644 72%Z (Z_to_bv 64 (wpld + (i * wpld))).   (* [comment removed for export] *)
      ldf F_29648 D_29648 88%Z (Z_to_bv 64 (h)).   (* [comment removed for export] *)
      stepb_tk F_2964c D_2964c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold dwa_EX. kpost.
  Qed.

  Lemma k7_inner : forall regs Mi i, (0 <= i < h)%Z -> k7_IN regs Mi i 0 ->
    exists regs' M', msteps SEGS (mkst regs (0x29848 : word) Mi rom) (mkst regs' (0x29720 : word) M' rom) /\ k7_RL regs' M' i.
  Proof.
    intros regs Mi i Hi H0.
    apply (dowhile_loop SEGS rom (0x29848 : word) (0x29720 : word) (fun r m j => k7_IN r m i j) (fun r m => k7_RL r m i) PW); [| exact HPW1 | exact H0].
    intros r m j Hj HI. destruct (k7_iter r m i j Hi Hj HI) as (r1 & M1 & RUN1 & HB).
    destruct (Z_lt_ge_dec (j + 1) PW) as [LT|GE].
    - destruct (k7_back r1 M1 i j Hi ltac:(lia) LT HB) as (r2 & M2 & RUN2 & HI2). left. split; [exact LT|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HI2].
    - destruct (k7_out r1 M1 i j Hi ltac:(lia) ltac:(lia) HB) as (r2 & M2 & RUN2 & HO). right. split; [lia|]. exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO].
  Qed.

  Lemma k7_run : forall regs Mi, DWA_EN regs Mi ->
    exists regs' M', msteps SEGS (mkst regs (0x29670 : word) Mi rom) (mkst regs' (0x2a670 : word) M' rom) /\ DWA_EX regs' M'.
  Proof using All.
    intros regs Mi HE. destruct (k7_pre regs Mi HE) as (r0 & M0 & RUN0 & H0).
    destruct (dowhile_loop SEGS rom (0x2974c : word) (0x2a670 : word) (fun r m i => k7_RH r m i) (fun r m => DWA_EX r m) h) with (regs := r0) (m := M0) as (r9 & M9 & RUN9 & H9); [| lia | exact H0 |].
    - intros r m i Hi HI. destruct (k7_rowset r m i Hi HI) as (r1 & M1 & RUN1 & H1). destruct (k7_inner r1 M1 i Hi H1) as (r2 & M2 & RUN2 & H2).
      destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
      + destruct (k7_latch r2 M2 i ltac:(lia) LT H2) as (r3 & M3 & RUN3 & H3). left. split; [exact LT|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
      + destruct (k7_exit r2 M2 i ltac:(lia) ltac:(lia) H2) as (r3 & M3 & RUN3 & H3). right. split; [lia|]. exists r3, M3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] | exact H3].
    - exists r9, M9. split; [eapply msteps_trans; [exact RUN0 | exact RUN9] | exact H9].
  Qed.


End DWA.
