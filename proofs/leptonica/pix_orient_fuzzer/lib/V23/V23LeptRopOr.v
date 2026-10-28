(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_80000_81000 V23_code_rasteropLow_81000_82000 V23_code_rasteropLow_87000_875f4.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition o14_disp : word := 0x803d8.
Definition o14_head : word := 0x81958.
Definition o14_br : word := 0x819c0.
Definition o14_inner : word := 0x819e0.
Definition o14_tail : word := 0x81a20.
Definition o14_next : word := 0x81940.
Definition o14_test : word := 0x81950.
Definition o14_epi : word := 0x875b8.
Definition o14_jt : Z := 0x1f43c.
Definition o14_jtv : Z := 402640.
Ltac o14pcs := unfold o14_disp, o14_head, o14_br, o14_inner, o14_tail, o14_next, o14_test, o14_epi in *.

Lemma wr_readable_o14 : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Section RL14.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M2 : word -> option byte.
  Variable rom : word -> option byte.
  Variables s datad RSd datas RSs dwpl swpl dh PDF PSF DW nf lw : Z.
  Variables od1 od2 os1 os2 sxr P dxr e Q SX : Z.
  Variables ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word.

  Hypothesis Hs : (240 <= s /\ s < 2 ^ 64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis Hdd : (4096 <= datad /\ datad + RSd < 2 ^ 47 /\ datad mod 4 = 0)%Z.
  Hypothesis Hds : (4096 <= datas /\ datas + RSs < 2 ^ 47 /\ datas mod 4 = 0)%Z.
  Hypothesis HRS : (0 <= RSd /\ 0 <= RSs)%Z.
  Hypothesis Hdim : (1 <= dh < 2 ^ 24 /\ 0 <= dwpl /\ 0 <= swpl /\ dwpl * dh <= 2 ^ 30 /\ swpl * dh <= 2 ^ 30)%Z.
  Hypothesis Hcol : (DW = 32 * nf + lw /\ 0 <= lw < 32 /\ 0 <= nf < 2 ^ 26 /\ 1 <= DW)%Z.
  #[local] Abbreviation NW := (nf + (if Z.eq_dec lw 0 then 0 else 1))%Z (only parsing).
  #[local] Abbreviation SR i := (PSF + 4 * (swpl * i))%Z (only parsing).
  #[local] Abbreviation DR i := (PDF + 4 * (dwpl * i))%Z (only parsing).
  Hypothesis Hrowd : forall i, (0 <= i < dh)%Z -> (datad <= DR i /\ DR i + 4 * NW <= datad + RSd)%Z.
  Hypothesis Hrows : forall i, (0 <= i < dh)%Z -> (datas <= SR i /\ SR i + 4 * NW <= datas + RSs)%Z.
  Hypothesis Hal : (PDF mod 4 = 0 /\ PSF mod 4 = 0)%Z.
  Hypothesis SOKd : store_ok SEGS M2 (Z_to_bv 64 datad) (Z.to_nat RSd) = true.
  Hypothesis SOKs : store_ok SEGS M2 (Z_to_bv 64 datas) (Z.to_nat RSs) = true.
  Hypothesis FR : disj_apart datad RSd (s - 240) 240.
  Hypothesis C_dh : rdn SEGS M2 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Hypothesis C_swpl : rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Hypothesis C_ra : rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ra).
  Hypothesis C_s0 : rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis C_s1 : rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis C_s2 : rdn SEGS M2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis C_s3 : rdn SEGS M2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis C_s4 : rdn SEGS M2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis C_s5 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v).
  Hypothesis C_s6 : rdn SEGS M2 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v).
  Hypothesis C_s7 : rdn SEGS M2 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 s7v).
  Hypothesis C_s8 : rdn SEGS M2 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 s8v).
  Hypothesis C_s9 : rdn SEGS M2 (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 s9v).
  Hypothesis C_s10 : rdn SEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 s10v).
  Hypothesis C_s11 : rdn SEGS M2 (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 s11v).
  Hypothesis JT : rdn SEGS M2 (Z_to_bv 64 o14_jt) 4 = Some (Z_to_le_bytes 4 o14_jtv).
  Hypothesis EPDF : (PDF = datad + od1 + od2)%Z.
  Hypothesis EPSF : (PSF = datas + os1 + os2)%Z.
  Hypothesis Hraw : (- 2 ^ 28 <= sxr <= 2 ^ 28 /\ - 2 ^ 28 <= P <= 2 ^ 28 /\ - 2 ^ 28 <= dxr <= 2 ^ 28 /\
                     - 2 ^ 28 <= e <= 2 ^ 28 /\ - 2 ^ 28 <= Q <= 2 ^ 28 /\ - 2 ^ 28 <= SX <= 2 ^ 28)%Z.
  Hypothesis Hnf : (DW = Q - SX + Z.min 0 (sxr + P - dxr + Z.min 0 e - Q))%Z.

  Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
  Ltac condSe := pin; rewrite ?c_eq_Zs by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
  Ltac mulw_v F D v := sn F D; fixv' v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
  Ltac sextw F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
  Ltac addw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
  Ltac subw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).
  Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac sltu0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
  Ltac slti0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
  Ltac slli2 F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  Ltac zand0 F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
  Ltac zmin F D v := sn F D; fixv' (Z_to_bv 64 (Z.min 0 v)) ltac:(rewrite srai63_Z by lia; apply and_smsk).

  Lemma col14 : (DW / 32 = nf /\ DW mod 32 = lw /\ DW < 2 ^ 31 /\ 0 <= (if Z.eq_dec lw 0 then 0 else 1) <= 1 /\ (32 <= DW -> 1 <= nf) /\ (DW < 32 -> nf = 0))%Z.
  Proof.
    destruct Hcol as (E & Hlw & Hnf0 & HDW).
    assert (DW / 32 = nf)%Z by (rewrite E, Z.add_comm, Z.mul_comm, Z.div_add by lia; rewrite (Z.div_small lw 32) by lia; lia).
    assert (DW mod 32 = lw)%Z by (rewrite E, Z.add_comm, Z.mul_comm, Z_mod_plus_full; apply Z.mod_small; lia).
    destruct (Z.eq_dec lw 0); lia.
  Qed.

  Lemma row_in14 : forall i, (0 <= i < dh)%Z ->
    (0 <= swpl * i /\ swpl * i + swpl <= 2 ^ 30 /\ 0 <= dwpl * i /\ dwpl * i + dwpl <= 2 ^ 30
     /\ datas <= SR i /\ SR i + 4 * NW <= datas + RSs /\ datad <= DR i /\ DR i + 4 * NW <= datad + RSd
     /\ datas <= PSF /\ datad <= PDF)%Z.
  Proof.
    intros i Hi. destruct Hdim as (H1 & H2 & H3 & H4 & H5).
    assert (0 <= swpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= dwpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
    assert (swpl * (i + 1) <= swpl * dh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (dwpl * (i + 1) <= dwpl * dh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    pose proof (Hrowd i Hi). pose proof (Hrows i Hi). pose proof (Hrowd 0 ltac:(lia)). pose proof (Hrows 0 ltac:(lia)). lia.
  Qed.

  Lemma ptr_mod4_14 : forall i k, ((DR i + 4 * k) mod 4 = 0 /\ (SR i + 4 * k) mod 4 = 0)%Z.
  Proof.
    intros i k. destruct Hal as [AD AS]. split.
    - replace (DR i + 4 * k)%Z with (PDF + (dwpl * i + k) * 4)%Z by lia. rewrite Z_mod_plus_full. exact AD.
    - replace (SR i + 4 * k)%Z with (PSF + (swpl * i + k) * 4)%Z by lia. rewrite Z_mod_plus_full. exact AS.
  Qed.

  Definition LInv14 (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 1 = Z_to_bv 64 swpl /\ getr regs 14 = Z_to_bv 64 dwpl /\
    getr regs 17 = Z_to_bv 64 PSF /\ getr regs 7 = Z_to_bv 64 PDF /\ getr regs 16 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 1 /\
    getr regs 9 = Z_to_bv 64 DW /\ getr regs 30 = Z_to_bv 64 32 /\ getr regs 21 = Z_to_bv 64 0 /\ getr regs 31 = Z_to_bv 64 0 /\
    getr regs 10 = Z_to_bv 64 PDF /\ getr regs 19 = Z_to_bv 64 PSF /\ getr regs 29 = Z_to_bv 64 (- nf) /\
    getr regs 8 = Z_to_bv 64 18446744073709551611 /\ getr regs 12 = Z_to_bv 64 lw.

  Lemma LInv14_agree : forall regs regs',
    regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26; 27]%list) regs regs' -> LInv14 regs -> LInv14 regs'.
  Proof.
    intros regs regs' AG (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12).
    unfold LInv14. repeat split; match goal with |- getr regs' ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.
  Qed.

  Lemma rl14_A3b : forall regs (mk : word),
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 17 = Z_to_bv 64 PSF -> getr regs 7 = Z_to_bv 64 PDF -> getr regs 16 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 os1 -> getr regs 18 = Z_to_bv 64 os2 ->
    getr regs 22 = Z_to_bv 64 od1 -> getr regs 23 = Z_to_bv 64 od2 ->
    getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 14 -> getr regs 12 = Z_to_bv 64 lw ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 datas -> getr regs 20 = Z_to_bv 64 sxr -> getr regs 21 = Z_to_bv 64 P ->
    getr regs 27 = Z_to_bv 64 SX -> getr regs 28 = mk -> getr regs 29 = Z_to_bv 64 Q ->
    getr regs 30 = Z_to_bv 64 dxr -> getr regs 31 = Z_to_bv 64 e ->
    exists regs',
      msteps SEGS (mkst regs o14_disp M2 rom) (mkst regs' o14_head M2 rom)
      /\ getr regs' 25 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (swpl * 0) /\ getr regs' 13 = Z_to_bv 64 (dwpl * 0)
      /\ LInv14 regs'
      /\ regs_agree (fun r : reg => In r [1; 6; 8; 10; 11; 13; 15; 18; 19; 20; 21; 22; 25; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs mk H2 H17 H7 H16 H5 H8 H18 H22 H23 H9 H10 H11 H12 H14 H19 H20 H21 H27 H28 H29 H30 H31.
    o14pcs. pose proof JT as JT'. unfold o14_jt, o14_jtv in JT'.
    pose proof col14 as (DWd & DWm & DW31 & _). pose proof Hdd as (Gd & Td & ALd). pose proof Hds as (Gs & Ts & ALs).
    pose proof Hraw as (R1 & R2 & R3 & R4 & R5 & R6). pose proof Hcol as (_ & Hlw & Hnf0 & HDW).
    assert (M1 : (Z.min 0 e <= 0 /\ - 2 ^ 28 <= Z.min 0 e)%Z) by lia.
    assert (MM : (Z.min 0 (sxr + P - dxr + Z.min 0 e - Q) <= 0 /\ - 2 ^ 31 <= Z.min 0 (sxr + P - dxr + Z.min 0 e - Q))%Z) by lia.
    eexists. split.
    - sn F_803d8 D_803d8.
      zv F_803dc D_803dc (Z_to_bv 64 13).
      sn F_803e0 D_803e0. sn F_803e4 D_803e4.
      stepb_tk F_803e8 D_803e8 ltac:(condZ).
      sn F_803f0 D_803f0. sn F_803f4 D_803f4. sn F_803f8 D_803f8.
      sn F_803fc D_803fc. fixv' (Z_to_bv 64 0x1f43c) ltac:(apply bv_eq; reflexivity).
      stepLD F_80400 D_80400 (Z_to_le_bytes 4 402640) (Z_to_bv 64 402640) ltac:(addr_norm; rewrite ?Z.add_0_r; exact JT') ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 402640)) with (Z_to_bv 64 402640).
      sn F_80404 D_80404. fixv' (Z_to_bv 64 0x818d8) ltac:(apply bv_eq; reflexivity).
      stepret F_80408 D_80408 (0x818d8 : word) ltac:(bveq).
      sn F_818d8 D_818d8. fixv' (Z_to_bv 64 (swpl * 0)) ltac:(f_equal; lia).
      sn F_818dc D_818dc. fixv' (Z_to_bv 64 (dwpl * 0)) ltac:(f_equal; lia).
      sn F_818e0 D_818e0.
      zv F_818e4 D_818e4 (Z_to_bv 64 (sxr + P)).
      sn F_818e8 D_818e8.
      zv F_818ec D_818ec (Z_to_bv 64 (od2 + od1)).
      zand0 F_818f0 D_818f0 andi_3 ALs.
      zv F_818f4 D_818f4 (Z_to_bv 64 (os2 + os1)).
      sn F_818f8 D_818f8. zmin F_818fc D_818fc e.
      zand0 F_81900 D_81900 andi_3 ALd.
      subw_v F_81904 D_81904 (Q - SX)%Z.
      subw_v F_81908 D_81908 (sxr + P - dxr)%Z.
      sn F_8190c D_8190c.
      zv F_81910 D_81910 (Z_to_bv 64 PDF).
      zv F_81914 D_81914 (Z_to_bv 64 PSF).
      zv F_81918 D_81918 (Z_to_bv 64 (sxr + P - dxr + Z.min 0 e)).
      subw_v F_8191c D_8191c (sxr + P - dxr + Z.min 0 e - Q)%Z.
      sn F_81920 D_81920. zmin F_81924 D_81924 (sxr + P - dxr + Z.min 0 e - Q)%Z.
      zv F_81928 D_81928 (Z_to_bv 64 DW).
      sn F_8192c D_8192c. fixv' (Z_to_bv 64 nf) ltac:(rewrite zbv_srliw_small by lia; change (2 ^ 5)%Z with 32%Z; rewrite DWd; reflexivity).
      zv F_81930 D_81930 (Z_to_bv 64 (- nf)).
      sn F_81934 D_81934.
      stepLD F_81938 D_81938 (word_to_le_bytes 8 (Z_to_bv 64 swpl)) (Z_to_bv 64 swpl) ltac:(rdn_addr (s - 152)%Z; exact C_swpl) ltac:(apply bytes_le_to_Z_8).
      sn F_8193c D_8193c.
      apply mst_refl.
    - unfold LInv14. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Definition Inv14 (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < datad \/ datad + RSd <= bv_unsigned x)%Z -> Mi x = M2 x) /\ mem_grows M2 Mi.
  Lemma Inv14_M2 : Inv14 M2.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma Inv14_store : forall Mi (a : Z) (bs : list byte),
    Inv14 Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + RSd)%Z -> Inv14 (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma Inv14_sok : forall Mi (a : Z) (n : nat), Inv14 Mi -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + RSd)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [exact HG|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M2 (Z_to_bv 64 datad) _ (Z.to_nat RSd)); [ | exact SOKd | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rd4_14 : forall Mi base RS (a : Z), Inv14 Mi -> store_ok SEGS M2 (Z_to_bv 64 base) (Z.to_nat RS) = true ->
    (0 <= base /\ base + RS <= 2 ^ 64)%Z -> (base <= a)%Z -> (a + 4 <= base + RS)%Z ->
    exists bs, rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros Mi base RS a [_ HG] SOK Hb Ha H4.
    apply (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) wr_readable_o14).
    eapply store_ok_mono; [exact HG|].
    eapply (store_ok_sub SEGS M2 (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma Inv14_dh : forall Mi, Inv14 Mi -> rdn SEGS Mi (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Proof.
    intros Mi [HI _]. use_apart FR. rewrite <- C_dh.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma rl14_H : forall regs Mi i, (0 <= i < dh)%Z -> LInv14 regs -> getr regs 25 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs o14_head Mi rom) (mkst regs' o14_br Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (SR i) /\ getr regs' 18 = Z_to_bv 64 (DR i)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 22]%list) regs regs'.
  Proof.
    intros regs Mi i Hi (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25.
    o14pcs. pose proof (row_in14 i Hi) as RI. pose proof col14 as CC. pose proof Hdd as HD. pose proof Hds as HS.
    eexists. split.
    - zv F_81958 D_81958 (Z_to_bv 64 (swpl * i)).
      mulw_v F_8195c D_8195c (Z_to_bv 64 (swpl * i)).
      stepb_ft F_81960 D_81960 ltac:(condR).
      sextw F_81964 D_81964 (swpl * i)%Z.
      slli2 F_81968 D_81968 (4 * (swpl * i))%Z.
      zv F_8196c D_8196c (Z_to_bv 64 (SR i)).
      seqz0 F_81970 D_81970.
      stepb_ft F_81974 D_81974 ltac:(condR).
      sltu0 F_81978 D_81978. slti0 F_8197c D_8197c. sn F_81980 D_81980. sn F_81984 D_81984.
      stepb_ft F_81988 D_81988 ltac:(condR).
      zv F_8198c D_8198c (Z_to_bv 64 (dwpl * i)).
      mulw_v F_81990 D_81990 (Z_to_bv 64 (dwpl * i)).
      stepb_ft F_81994 D_81994 ltac:(condR).
      sextw F_81998 D_81998 (dwpl * i)%Z.
      slli2 F_8199c D_8199c (4 * (dwpl * i))%Z.
      zv F_819a0 D_819a0 (Z_to_bv 64 (DR i)).
      seqz0 F_819a4 D_819a4.
      stepb_ft F_819a8 D_819a8 ltac:(condR).
      sltu0 F_819ac D_819ac. slti0 F_819b0 D_819b0. sn F_819b4 D_819b4. sn F_819b8 D_819b8.
      stepb_ft F_819bc D_819bc ltac:(condR).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl14_Hf : forall regs Mi i, (0 <= i < dh)%Z -> (32 <= DW)%Z -> LInv14 regs ->
    getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs',
      msteps SEGS (mkst regs o14_br Mi rom) (mkst regs' o14_inner Mi rom)
      /\ getr regs' 15 = Z_to_bv 64 (4 * 0) /\ getr regs' 18 = Z_to_bv 64 (DR i) /\ getr regs' 22 = Z_to_bv 64 (SR i) /\ getr regs' 23 = Z_to_bv 64 (- (nf - 0))
      /\ regs_agree (fun r : reg => In r [15; 18; 22; 23]%list) regs regs'.
  Proof.
    intros regs Mi i Hi H32 (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H11 H13.
    o14pcs. pose proof (row_in14 i Hi) as RI. pose proof col14 as CC.
    eexists. split.
    - stepb_ft F_819c0 D_819c0 ltac:(condZ).
      stepb_ft F_819c4 D_819c4 ltac:(condR).
      sn F_819c8 D_819c8. fixv' (Z_to_bv 64 (4 * 0)) ltac:(reflexivity).
      slli2 F_819cc D_819cc (4 * (dwpl * i))%Z.
      slli2 F_819d0 D_819d0 (4 * (swpl * i))%Z.
      zv F_819d4 D_819d4 (Z_to_bv 64 (DR i)).
      zv F_819d8 D_819d8 (Z_to_bv 64 (SR i)).
      zv F_819dc D_819dc (Z_to_bv 64 (- (nf - 0))).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl14_I : forall regs Mi i k, (0 <= i < dh)%Z -> (0 <= k < nf)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 15 = Z_to_bv 64 (4 * k) -> getr regs 18 = Z_to_bv 64 (DR i) -> getr regs 22 = Z_to_bv 64 (SR i) -> getr regs 23 = Z_to_bv 64 (- (nf - k)) ->
    exists regs' M',
      msteps SEGS (mkst regs o14_inner Mi rom) (mkst regs' (0x81a14 : word) M' rom)
      /\ Inv14 M' /\ getr regs' 15 = Z_to_bv 64 (4 * (k + 1)) /\ getr regs' 23 = Z_to_bv 64 (- (nf - (k + 1)))
      /\ regs_agree (fun r : reg => In r [6; 15; 23; 24; 26; 27]%list) regs regs'.
  Proof.
    intros regs Mi i k Hi Hk HIv (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18 H22 H23.
    o14pcs. pose proof (row_in14 i Hi) as RI. pose proof col14 as CC. pose proof Hdd as HD. pose proof Hds as HS.
    destruct (rd4_14 Mi datas RSs (SR i + 4 * k) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
    destruct (rd4_14 Mi datad RSd (DR i + 4 * k) HIv SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rbd & Lbd).
    eexists. eexists. split; [|split; [|split; [|split]]].
    - zv F_819e0 D_819e0 (Z_to_bv 64 (SR i + 4 * k)).
      stepb_ft F_819e4 D_819e4 ltac:(condZ).
      stepb_ft F_819e8 D_819e8 ltac:(condR).
      zv F_819ec D_819ec (Z_to_bv 64 (DR i + 4 * k)).
      stepb_ft F_819f0 D_819f0 ltac:(condZ).
      stepLD F_819f4 D_819f4 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
      stepLD F_819f8 D_819f8 bd (Z_to_bv 64 (bytes_le_to_Z bd)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbd) ltac:(symmetry; apply u_lez4; exact Lbd).
      sn F_819fc D_819fc.
      chain_step; [ reflexivity
                  | eapply step_sw_at with (a := Z_to_bv 64 (DR i + 4 * k));
                    [ exact F_81a00 | reflexivity | exact D_81a00 | gres; imm_norm; addr_tac | gres; reflexivity
                    | apply (Inv14_sok _ _ 4 HIv); [lia | cbn; lia] ]
                  | step_simpl ].
      stepb_ft F_81a04 D_81a04 ltac:(condZ).
      stepb_ft F_81a08 D_81a08 ltac:(condZ).
      sn F_81a0c D_81a0c. fixv' (Z_to_bv 64 (- (nf - (k + 1)))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      zv F_81a10 D_81a10 (Z_to_bv 64 (4 * (k + 1))).
      apply mst_refl.
    - apply Inv14_store; [exact HIv | lia | rewrite length_N_to_le_bytes; cbn; lia].
    - gres; pin; reflexivity.
    - gres; pin; reflexivity.
    - solve_regs_agree.
  Qed.

  Lemma rl14_words : forall (j : nat) regs Mi i k, (0 <= i < dh)%Z -> (0 <= k)%Z -> (k + Z.of_nat j = nf - 1)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 15 = Z_to_bv 64 (4 * k) -> getr regs 18 = Z_to_bv 64 (DR i) -> getr regs 22 = Z_to_bv 64 (SR i) -> getr regs 23 = Z_to_bv 64 (- (nf - k)) ->
    exists regs' M',
      msteps SEGS (mkst regs o14_inner Mi rom) (mkst regs' o14_tail M' rom)
      /\ Inv14 M' /\ getr regs' 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr regs' 18 = Z_to_bv 64 (DR i + 4 * nf)
      /\ regs_agree (fun r : reg => In r [6; 15; 18; 23; 24; 26; 27]%list) regs regs'.
  Proof.
    pose proof col14 as CC.
    induction j as [|j IH]; intros regs Mi i k Hi Hk Hj HIv LI H15 H18 H22 H23;
      destruct (rl14_I regs Mi i k Hi ltac:(lia) HIv LI H15 H18 H22 H23) as (r1 & Ma & S1 & HI1 & A15 & A23 & AG1);
      pose proof (AG1 18 ltac:(notin_list)) as A18; rewrite H18 in A18;
      pose proof (AG1 22 ltac:(notin_list)) as A22; rewrite H22 in A22.
    - eexists. exists Ma. split; [|split; [exact HI1 | split; [|split]]].
      + eapply msteps_trans; [exact S1|]. o14pcs.
        pose proof (row_in14 i Hi) as RI.
        stepb_ft F_81a14 D_81a14 ltac:(condSe).
        zv F_81a18 D_81a18 (Z_to_bv 64 (DR i + 4 * nf)).
        zv F_81a1c D_81a1c (Z_to_bv 64 (SR i + 4 * nf)).
        apply mst_refl.
      + gres; pin; reflexivity.
      + gres; pin; reflexivity.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (L1 : LInv14 r1) by (apply (LInv14_agree regs); [regs_agree_weaken AG1 | exact LI]).
      destruct (IH r1 Ma i (k + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 L1 A15 A18 A22 A23) as (r2 & Mb & S2 & HI2 & B15 & B18 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B15 | split; [exact B18|]]]].
      + eapply msteps_trans; [exact S1|]. o14pcs.
        stepb_tk F_81a14 D_81a14 ltac:(condSe).
        exact S2.
      + eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma rl14_P : forall regs Mi i n, (0 <= i < dh)%Z -> (n = nf)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 15 = Z_to_bv 64 (SR i + 4 * n) -> getr regs 18 = Z_to_bv 64 (DR i + 4 * n) ->
    exists regs' M',
      msteps SEGS (mkst regs o14_tail Mi rom) (mkst regs' o14_next M' rom)
      /\ Inv14 M'
      /\ regs_agree (fun r : reg => In r [6; 15; 22]%list) regs regs'.
  Proof.
    intros regs Mi i n Hi -> HIv (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H15 H18.
    o14pcs. pose proof (row_in14 i Hi) as RI. pose proof col14 as CC. pose proof (ptr_mod4_14 i nf) as (MD & MS).
    pose proof Hdd as HD. pose proof Hds as HS.
    assert (Hlw : (0 <= lw < 32)%Z) by (destruct Hcol as (_ & X & _); exact X).
    destruct (Z.eq_dec lw 0) as [E0 | NE0].
    - exists regs, Mi. split; [|split; [exact HIv | apply regs_agree_refl]].
      stepb_tk F_81a20 D_81a20 ltac:(condZ).
      apply mst_refl.
    - destruct (rd4_14 Mi datad RSd (DR i + 4 * nf) HIv SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rbd & Lbd).
      destruct (rd4_14 Mi datas RSs (SR i + 4 * nf) HIv SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Rbs & Lbs).
      eexists. eexists. split; [|split].
      + stepb_ft F_81a20 D_81a20 ltac:(condZ).
        stepb_ft F_81a24 D_81a24 ltac:(condZ).
        zand0 F_81a28 D_81a28 andi_3 MD.
        stepb_ft F_81a2c D_81a2c ltac:(condR).
        stepb_ft F_81a30 D_81a30 ltac:(condZ).
        zand0 F_81a34 D_81a34 andi_3 MS.
        stepb_ft F_81a38 D_81a38 ltac:(condR).
        stepLD F_81a3c D_81a3c bd (Z_to_bv 64 (bytes_le_to_Z bd)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbd) ltac:(symmetry; apply u_lez4; exact Lbd).
        stepLD F_81a40 D_81a40 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rbs) ltac:(symmetry; apply u_lez4; exact Lbs).
        sn F_81a44 D_81a44. sn F_81a48 D_81a48. sn F_81a4c D_81a4c. sn F_81a50 D_81a50.
        chain_step; [ reflexivity
                    | eapply step_sw_at with (a := Z_to_bv 64 (DR i + 4 * nf));
                      [ exact F_81a54 | reflexivity | exact D_81a54 | gres; imm_norm; addr_tac | gres; reflexivity
                      | apply (Inv14_sok _ _ 4 HIv); [lia | cbn; lia] ]
                    | step_simpl ].
        sn F_81a58 D_81a58.
        apply mst_refl.
      + apply Inv14_store; [exact HIv | lia | rewrite length_N_to_le_bytes; cbn; lia].
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rl14_N1 : forall regs Mi i, (0 <= i < dh)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs',
      msteps SEGS (mkst regs o14_next Mi rom) (mkst regs' o14_test Mi rom)
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (swpl * (i + 1)) /\ getr regs' 13 = Z_to_bv 64 (dwpl * (i + 1))
      /\ getr regs' 15 = Z_to_bv 64 dh
      /\ regs_agree (fun r : reg => In r [11; 13; 15; 25]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & I21 & I31 & I10 & I19 & I29 & I8 & I12) H25 H11 H13.
    o14pcs. pose proof (row_in14 i Hi) as RI. pose proof Hdim as HM.
    eexists. split.
    - sextw F_81940 D_81940 (i + 1)%Z.
      addw_v F_81944 D_81944 (dwpl * (i + 1))%Z.
      addw_v F_81948 D_81948 (swpl * (i + 1))%Z.
      stepLD F_8194c D_8194c (word_to_le_bytes 8 (Z_to_bv 64 dh)) (Z_to_bv 64 dh) ltac:(rdn_addr (s - 112)%Z; exact (Inv14_dh Mi HIv)) ltac:(apply bytes_le_to_Z_8).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma rl14_row : forall regs Mi i, (0 <= i < dh)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs o14_head Mi rom) (mkst regs' o14_test M' rom)
      /\ Inv14 M' /\ LInv14 regs'
      /\ getr regs' 25 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (swpl * (i + 1)) /\ getr regs' 13 = Z_to_bv 64 (dwpl * (i + 1))
      /\ getr regs' 15 = Z_to_bv 64 dh
      /\ regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs Mi i Hi HIv LI H25 H11 H13.
    pose proof col14 as CC.
    assert (Hlw : (0 <= lw < 32)%Z) by (destruct Hcol as (_ & X & _); exact X).
    assert (EDW3 : (DW = 32 * nf + lw)%Z) by (destruct Hcol as (X & _); exact X).
    destruct (rl14_H regs Mi i Hi LI H25) as (r1 & S1 & A15 & A18 & AG1).
    assert (L1 : LInv14 r1) by (apply (LInv14_agree regs); [regs_agree_weaken AG1 | exact LI]).
    pose proof (AG1 11 ltac:(notin_list)) as A11; rewrite H11 in A11.
    pose proof (AG1 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
    pose proof (AG1 25 ltac:(notin_list)) as A25; rewrite H25 in A25.
    assert (MID : exists r2 Ma, msteps SEGS (mkst r1 o14_br Mi rom) (mkst r2 o14_tail Ma rom)
                    /\ Inv14 Ma /\ getr r2 15 = Z_to_bv 64 (SR i + 4 * nf) /\ getr r2 18 = Z_to_bv 64 (DR i + 4 * nf)
                    /\ regs_agree (fun r : reg => In r [6; 15; 18; 22; 23; 24; 26; 27]%list) r1 r2).
    { destruct (Z_lt_ge_dec DW 32) as [Hs32 | Hf32].
      - assert (Enf0 : (nf = 0)%Z) by lia.
        exists r1, Mi. split; [|split; [exact HIv | split; [|split; [|apply regs_agree_refl]]]].
        + destruct L1 as (I2 & I1 & I14 & I17 & I7 & I16 & I5 & I9 & I30 & _). o14pcs.
          stepb_tk F_819c0 D_819c0 ltac:(condZ).
          apply mst_refl.
        + rewrite A15. f_equal. lia.
        + rewrite A18. f_equal. lia.
      - destruct (rl14_Hf r1 Mi i Hi ltac:(lia) L1 A11 A13) as (r2 & S2 & B15 & B18 & B22 & B23 & AG2).
        assert (L2 : LInv14 r2) by (apply (LInv14_agree r1); [regs_agree_weaken AG2 | exact L1]).
        destruct (rl14_words (Z.to_nat (nf - 1)) r2 Mi i 0 Hi ltac:(lia) ltac:(lia) HIv L2 B15 B18 B22 B23) as (r3 & Ma & S3 & HI3 & C15 & C18 & AG3).
        exists r3, Ma. split; [eapply msteps_trans; [exact S2 | exact S3]|]. split; [exact HI3|]. split; [exact C15|]. split; [exact C18|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]. }
    destruct MID as (r2 & Ma & S2 & HI2 & B15 & B18 & AG2).
    assert (L2 : LInv14 r2) by (apply (LInv14_agree r1); [regs_agree_weaken AG2 | exact L1]).
    destruct (rl14_P r2 Ma i nf Hi eq_refl HI2 L2 B15 B18) as (r3 & Mb & S3 & HI3 & AG3).
    assert (L3 : LInv14 r3) by (apply (LInv14_agree r2); [regs_agree_weaken AG3 | exact L2]).
    pose proof (AG3 25 ltac:(notin_list)) as C25; rewrite (AG2 25 ltac:(notin_list)), A25 in C25.
    pose proof (AG3 11 ltac:(notin_list)) as C11; rewrite (AG2 11 ltac:(notin_list)), A11 in C11.
    pose proof (AG3 13 ltac:(notin_list)) as C13; rewrite (AG2 13 ltac:(notin_list)), A13 in C13.
    destruct (rl14_N1 r3 Mb i Hi HI3 L3 C25 C11 C13) as (r4 & S4 & D25 & D11 & D13 & D15 & AG4).
    assert (L4 : LInv14 r4) by (apply (LInv14_agree r3); [regs_agree_weaken AG4 | exact L3]).
    exists r4, Mb. split; [|split; [exact HI3 | split; [exact L4 | split; [exact D25 | split; [exact D11 | split; [exact D13 | split; [exact D15|]]]]]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3 | exact S4].
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|].
      eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4].
  Qed.

  Lemma rl14_rows : forall (k : nat) regs Mi i, (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv14 Mi -> LInv14 regs ->
    getr regs 25 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (swpl * i) -> getr regs 13 = Z_to_bv 64 (dwpl * i) ->
    exists regs' M',
      msteps SEGS (mkst regs o14_head Mi rom) (mkst regs' o14_epi M' rom)
      /\ Inv14 M' /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [6; 11; 13; 15; 18; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk HIv LI H25 H11 H13;
      destruct (rl14_row regs Mi i ltac:(lia) HIv LI H25 H11 H13) as (r1 & Ma & S1 & HI1 & L1 & A25 & A11 & A13 & A15 & AG1).
    - exists r1, Ma. split; [|split; [exact HI1 | split; [exact (proj1 L1) | exact AG1]]].
      eapply msteps_trans; [exact S1|]. o14pcs. pose proof Hdim as HM.
      stepb_ft F_81950 D_81950 ltac:(condZ).
      sn F_81954 D_81954.
      apply mst_refl.
    - destruct (IH r1 Ma (i + 1)%Z ltac:(lia) ltac:(lia) HI1 L1 A25 A11 A13) as (r2 & Mb & S2 & HI2 & B2 & AG2).
      exists r2, Mb. split; [|split; [exact HI2 | split; [exact B2|]]].
      + eapply msteps_trans; [exact S1|]. o14pcs. pose proof Hdim as HM.
        stepb_tk F_81950 D_81950 ltac:(condZ).
        exact S2.
      + eapply regs_agree_trans; [exact AG1 | exact AG2].
  Qed.

  Lemma Inv14_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv14 Mi -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
    rdn SEGS M2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. use_apart FR. rewrite <- HM.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.
  Ltac ldsv F D k v FL HIv :=
    stepLD F D (word_to_le_bytes 8 v) v
      ltac:(rdn_addr (s - k)%Z; apply (Inv14_rdn_frame _ _ _ _ HIv); [lia | cbn; lia | exact FL])
      ltac:(apply bytes_le_to_Z_8).

  (* [comment removed for export] *)
  Lemma rl14_N2 : forall regs Mi, Inv14 Mi -> getr regs 2 = Z_to_bv 64 (s - 240) ->
    exists regs',
      msteps SEGS (mkst regs o14_epi Mi rom) (mkst regs' ra Mi rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2. o14pcs.
    eexists. split.
    - ldsv F_875b8 D_875b8 8%Z ra C_ra HIv.
      ldsv F_875bc D_875bc 16%Z s0v C_s0 HIv.
      ldsv F_875c0 D_875c0 24%Z s1v C_s1 HIv.
      ldsv F_875c4 D_875c4 32%Z s2v C_s2 HIv.
      ldsv F_875c8 D_875c8 40%Z s3v C_s3 HIv.
      ldsv F_875cc D_875cc 48%Z s4v C_s4 HIv.
      ldsv F_875d0 D_875d0 56%Z s5v C_s5 HIv.
      ldsv F_875d4 D_875d4 64%Z s6v C_s6 HIv.
      ldsv F_875d8 D_875d8 72%Z s7v C_s7 HIv.
      ldsv F_875dc D_875dc 80%Z s8v C_s8 HIv.
      ldsv F_875e0 D_875e0 88%Z s9v C_s9 HIv.
      ldsv F_875e4 D_875e4 96%Z s10v C_s10 HIv.
      ldsv F_875e8 D_875e8 104%Z s11v C_s11 HIv.
      zv F_875ec D_875ec (Z_to_bv 64 s).
      stepret F_875f0 D_875f0 ra ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Theorem rl14_run : forall regs (mk : word),
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 17 = Z_to_bv 64 PSF -> getr regs 7 = Z_to_bv 64 PDF -> getr regs 16 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 os1 -> getr regs 18 = Z_to_bv 64 os2 ->
    getr regs 22 = Z_to_bv 64 od1 -> getr regs 23 = Z_to_bv 64 od2 ->
    getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 14 -> getr regs 12 = Z_to_bv 64 lw ->
    getr regs 14 = Z_to_bv 64 dwpl -> getr regs 19 = Z_to_bv 64 datas -> getr regs 20 = Z_to_bv 64 sxr -> getr regs 21 = Z_to_bv 64 P ->
    getr regs 27 = Z_to_bv 64 SX -> getr regs 28 = mk -> getr regs 29 = Z_to_bv 64 Q ->
    getr regs 30 = Z_to_bv 64 dxr -> getr regs 31 = Z_to_bv 64 e ->
    exists regs' M',
      msteps SEGS (mkst regs o14_disp M2 rom) (mkst regs' ra M' rom)
      /\ Inv14 M' /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs mk H2 H17 H7 H16 H5 H8 H18 H22 H23 H9 H10 H11 H12 H14 H19 H20 H21 H27 H28 H29 H30 H31.
    destruct (rl14_A3b regs mk H2 H17 H7 H16 H5 H8 H18 H22 H23 H9 H10 H11 H12 H14 H19 H20 H21 H27 H28 H29 H30 H31)
      as (r1 & S1 & A25 & A11 & A13 & L1 & AG1).
    pose proof Hdim as HM.
    destruct (rl14_rows (Z.to_nat (dh - 1)) r1 M2 0 ltac:(lia) ltac:(lia) Inv14_M2 L1 A25 A11 A13) as (r2 & M5 & S2 & HI2 & B2 & AG2).
    destruct (rl14_N2 r2 M5 HI2 B2) as (r3 & S3 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & AG3).
    exists r3, M5. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
    - split; [exact HI2|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

End RL14.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
