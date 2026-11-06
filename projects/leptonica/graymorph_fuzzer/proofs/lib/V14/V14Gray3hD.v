(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptArith LeptArith2 GrayLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14_code_gmD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section G3.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables w h wpl datas datad sp pixd : Z.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hwpl : (w <= 4 * wpl /\ wpl <= 20000)%Z.
  Hypothesis Hsp : (0 <= sp /\ sp + 56 <= 2 ^ 64)%Z.
  Hypothesis Hpixd : (0 <= pixd < 2 ^ 64)%Z.
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w).
  #[local] Abbreviation RS := (4 * (wpl * h))%Z (only parsing).
  Hypothesis Hds : (4 <= datas /\ datas + RS <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
  Hypothesis Hdd : (4 <= datad /\ datad + RS <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
  Hypothesis SOKs : store_ok SEGS M (Z_to_bv 64 datas) (Z.to_nat RS) = true.
  Hypothesis SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat RS) = true.
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 sp) 48 = true.
  Hypothesis FR : disj_apart datad RS sp 56.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.

  Lemma sok_spill : forall m k (n : nat), mem_grows M m -> (0 <= k)%Z -> (k + Z.of_nat n <= 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp + k)) n = true.
  Proof.
    intros m k n Hg Hk Hn. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 sp) _ 48%nat); [ | exact SOKf | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma lez4w : forall z, (0 <= z < 2 ^ 31)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
  Ltac condS := pin; rewrite ?c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
  Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac sltu0 F D := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
  Ltac slti0 F D := sn F D; fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
  Ltac snez1 F D := sn F D; fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
  Ltac mulw_v F D v := sn F D; fixv v ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
  Ltac addw_v F D v := sn F D; fixv v ltac:(rewrite zbv_addw_small by lia; f_equal; lia).

  (* [comment removed for export] *)
  Definition Mp : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp + 32)) (word_to_le_bytes 8 (Z_to_bv 64 datad)))
      (Z_to_bv 64 (sp + 0)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
      (Z_to_bv 64 (sp + 24)) (word_to_le_bytes 8 (Z_to_bv 64 datas)))
      (Z_to_bv 64 (sp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 wpl)).

  (* [comment removed for export] *)
  Lemma g3_pre : forall regs,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 datad ->
    getr regs 19 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (0x28498 : word) M rom) (mkst regs' (0x28500 : word) Mp rom)
      /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 1
      /\ getr regs' 5 = Z_to_bv 64 18446744073709551615 /\ getr regs' 6 = Z_to_bv 64 18446744073709551614
      /\ getr regs' 7 = Z_to_bv 64 18446744073709551613 /\ getr regs' 28 = Z_to_bv 64 18446744073709551612
      /\ getr regs' 29 = Z_to_bv 64 18446744073709551611
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 11; 13; 14; 15; 17; 28; 29]%list) regs regs'.
  Proof.
    intros regs H2 H8 H9 H19 H10.
    eexists. split.
    - stepLD F_2839c D_2839c (Z_to_le_bytes 4 h) (Z_to_bv 64 h)
        ltac:(rdn_addr (sp + 48)%Z; exact Ch) ltac:(apply lez4w; lia).
      rewrite (v_lw_small h) by lia.                        (* [comment removed for export] *)
      stepb_ft F_283a0 D_283a0 ltac:(condZ).                (* [comment removed for export] *)
      stepST F_283a4 D_283a4 (Z_to_bv 64 (sp + 40)) (Z_to_bv 64 0) ltac:(apply sok_spill; [grows | lia | cbn; lia]).   (* [comment removed for export] *)
      sn F_283a8 D_283a8.                                   (* [comment removed for export] *)
      snez1 F_283ac D_283ac.                                (* [comment removed for export] *)
      stepST F_283b0 D_283b0 (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 datad) ltac:(apply sok_spill; [grows | lia | cbn; lia]).   (* [comment removed for export] *)
      snez1 F_283b4 D_283b4.                                (* [comment removed for export] *)
      sn F_283b8 D_283b8.                                   (* [comment removed for export] *)
      sn F_283bc D_283bc.                                   (* [comment removed for export] *)
      sn F_283c0 D_283c0.                                   (* [comment removed for export] *)
      sn F_283c4 D_283c4.                                   (* [comment removed for export] *)
      sn F_283c8 D_283c8.                                   (* [comment removed for export] *)
      sn F_283cc D_283cc.                                   (* [comment removed for export] *)
      stepST F_283d0 D_283d0 (Z_to_bv 64 (sp + 0)) (Z_to_bv 64 pixd) ltac:(apply sok_spill; [grows | lia | cbn; lia]).    (* [comment removed for export] *)
      stepST F_283d4 D_283d4 (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 datas) ltac:(apply sok_spill; [grows | lia | cbn; lia]).  (* [comment removed for export] *)
      stepST F_283d8 D_283d8 (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 wpl) ltac:(apply sok_spill; [grows | lia | cbn; lia]).     (* [comment removed for export] *)
      sn F_283dc D_283dc.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wr_readable_v14 : wr_readable SEGS.
  Proof.
    intros seg Hin Hwr. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
  Qed.

  Lemma xor3_off : forall p base off c : Z,
    (p = base + off)%Z -> (0 <= base)%Z -> (base mod 4 = 0)%Z -> (0 <= off)%Z -> (p < 2 ^ 64)%Z ->
    (off - off mod 4 + (3 - off mod 4) = c)%Z -> v_xori (Z_to_bv 64 p) 3 = Z_to_bv 64 (base + c).
  Proof.
    intros p base off c -> Hb Hm Ho Hp <-. rewrite zbv_xori3 by lia. f_equal.
    assert (E : ((base + off) mod 4 = off mod 4)%Z).
    { rewrite Z.add_mod by lia. rewrite Hm, Z.add_0_l. apply Z.mod_mod. lia. }
    rewrite E. lia.
  Qed.

  Lemma mod4_lin : forall a x y : Z, (a mod 4 = 0)%Z -> ((a + 4 * wpl * x + 8 * y) mod 4 = 0)%Z.
  Proof.
    intros a x y Ha. replace (a + 4 * wpl * x + 8 * y)%Z with (a + (wpl * x + 2 * y) * 4)%Z by lia.
    rewrite Z_mod_plus_full. exact Ha.
  Qed.

  Lemma row_bound : forall i, (0 <= i < h)%Z -> (0 <= 4 * wpl * i /\ 4 * wpl * i + 4 * wpl <= RS)%Z.
  Proof.
    intros i Hi. assert (wpl * i <= wpl * (h - 1))%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= wpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition LInv (regs : bvmap 5 word) (i : Z) : Prop :=
    getr regs 2 = Z_to_bv 64 sp /\ getr regs 13 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 1 /\
    getr regs 5 = Z_to_bv 64 18446744073709551615 /\ getr regs 6 = Z_to_bv 64 18446744073709551614 /\
    getr regs 7 = Z_to_bv 64 18446744073709551613 /\ getr regs 28 = Z_to_bv 64 18446744073709551612 /\
    getr regs 29 = Z_to_bv 64 18446744073709551611 /\
    getr regs 18 = Z_to_bv 64 (datas + 4 * wpl * i) /\ getr regs 19 = Z_to_bv 64 (datad + 4 * wpl * i) /\
    getr regs 21 = Z_to_bv 64 (datas + 4 * wpl * i) /\ getr regs 22 = Z_to_bv 64 (datad + 4 * wpl * i) /\
    getr regs 23 = Z_to_bv 64 (2 ^ 64 - (datas + 4 * wpl * i)).

  Lemma LInv_agree : forall regs regs' i,
    regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 15; 16; 20; 24; 25; 26; 27; 30; 31]%list) regs regs' -> LInv regs i -> LInv regs' i.
  Proof.
    intros regs regs' i AG (I2 & I13 & I14 & I17 & I5 & I6 & I7 & I28 & I29 & I18 & I19 & I21 & I22 & I23).
    unfold LInv. repeat split; match goal with |- getr regs' ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.
  Qed.

  Section INNER.
  Variable Mr : word -> option byte.
  Hypothesis HGr : mem_grows M Mr.
  Hypothesis CwR : rdn SEGS Mr (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w).

  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < datad \/ datad + RS <= bv_unsigned x)%Z -> Mi x = Mr x) /\ mem_grows Mr Mi.
  Lemma Inv_Mr : Inv Mr.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + RS)%Z -> Inv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma sok_in : forall Mi base (a : Z) (n : nat),
    mem_grows Mr Mi -> store_ok SEGS M (Z_to_bv 64 base) (Z.to_nat RS) = true -> (0 <= base /\ base + RS <= 2 ^ 64)%Z ->
    (base <= a)%Z -> (a + Z.of_nat n <= base + RS)%Z -> store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi base a n HG SOK Hb Ha Hn. eapply store_ok_mono; [eapply mem_grows_trans; [exact HGr | exact HG]|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rd_src : forall Mi (a : Z), mem_grows Mr Mi -> (datas <= a)%Z -> (a + 1 <= datas + RS)%Z ->
    exists b, rdn SEGS Mi (Z_to_bv 64 a) 1 = Some [b].
  Proof.
    intros Mi a HG Ha H1.
    destruct (store_ok_rdn SEGS Mi 1 (Z_to_bv 64 a) wr_readable_v14) as (bs & Hbs & Lbs).
    { apply (sok_in Mi datas a 1 HG SOKs); [lia | lia | cbn; lia]. }
    destruct bs as [|b [|? ?]]; try discriminate. exists b. exact Hbs.
  Qed.

  (* [comment removed for export] *)
  Lemma Inv_rdn_frame : forall Mi k (n : nat) bs, Inv Mi -> (0 <= k)%Z -> (1 <= Z.of_nat n)%Z -> (k + Z.of_nat n <= 56)%Z ->
    rdn SEGS Mr (Z_to_bv 64 (sp + k)) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 (sp + k)) n = Some bs.
  Proof.
    intros Mi k n bs [HI _] Hk Hn1 Hn HM. use_apart FR. rewrite <- HM.
    assert (U : bv_unsigned (Z_to_bv 64 (sp + k)) = (sp + k)%Z) by (apply u_Z2bv; lia).
    apply rdn_ext; rewrite U; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  (* [comment removed for export] *)
  Section ITER.
  Variables i m : Z.
  #[local] Abbreviation LSROW := (datas + 4 * wpl * i)%Z (only parsing).
  #[local] Abbreviation LDROW := (datad + 4 * wpl * i)%Z (only parsing).
  #[local] Abbreviation LS := (datas + 4 * wpl * i + 8 * m)%Z (only parsing).
  #[local] Abbreviation LD := (datad + 4 * wpl * i + 8 * m)%Z (only parsing).
  Hypothesis Hi : (0 <= i < h)%Z.
  Hypothesis Hm : (0 <= m /\ 8 * m + 9 < w)%Z.
  Hypothesis HLS4 : (LS mod 4 = 0)%Z.
  Hypothesis HLD4 : (LD mod 4 = 0)%Z.

  Ltac gxor3 F D base off c :=
    stepiv F D (Z_to_bv 64 (base + c))
      ltac:(gres; pin; imm_norm; apply (xor3_off _ base off c); [ lia | lia | assumption | lia | lia | reflexivity ]).
  Ltac gsb F D aa :=
    chain_step;
    [ reflexivity
    | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 aa);
      [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | reflexivity
      | eapply store_ok_mono; [ grows | lazymatch goal with HGx : mem_grows Mr _ |- _ => apply (sok_in _ datad aa 1 HGx SOKd); [lia | lia | cbn; lia] end ] ]
    | step_simpl ].

  (* [comment removed for export] *)
  Lemma g3_iterA : forall regs Mi,
    getr regs 10 = Z_to_bv 64 (w - 8) -> getr regs 16 = Z_to_bv 64 (8 * m) ->
    getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 18446744073709551615 -> getr regs 6 = Z_to_bv 64 18446744073709551614 ->
    getr regs 7 = Z_to_bv 64 18446744073709551613 -> getr regs 28 = Z_to_bv 64 18446744073709551612 ->
    getr regs 29 = Z_to_bv 64 18446744073709551611 ->
    getr regs 18 = Z_to_bv 64 LSROW -> getr regs 21 = Z_to_bv 64 LSROW -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - LSROW) ->
    exists regs',
      msteps SEGS (mkst regs (0x28584 : word) Mi rom) (mkst regs' (0x28688 : word) Mi rom)
      /\ getr regs' 24 = Z_to_bv 64 LS /\ getr regs' 25 = Z_to_bv 64 (LS + 1) /\ getr regs' 8 = Z_to_bv 64 (LS + 2)
      /\ getr regs' 31 = Z_to_bv 64 (LS + 3) /\ getr regs' 26 = Z_to_bv 64 (LS + 4) /\ getr regs' 27 = Z_to_bv 64 (LS + 5)
      /\ getr regs' 1 = Z_to_bv 64 (LS + 6) /\ getr regs' 11 = Z_to_bv 64 (LS + 7) /\ getr regs' 12 = Z_to_bv 64 (LS + 8)
      /\ getr regs' 15 = Z_to_bv 64 (LS + 9)
      /\ regs_agree (fun r : reg => In r [1; 8; 10; 11; 12; 15; 24; 25; 26; 27; 31]%list) regs regs'.
  Proof.
    intros regs Mi H10 H16 H13 H14 H17 H5 H6 H7 H28 H29 H18 H21 H23.
    pose proof (row_bound i Hi) as RB.
    assert (Hw4 : (8 * m + 12 <= 4 * wpl)%Z) by lia.
    eexists. split.
    - zv F_28488 D_28488 (Z_to_bv 64 (8 * m + 1)).          (* [comment removed for export] *)
      stepb_ft F_2848c D_2848c ltac:(condZ).                (* [comment removed for export] *)
      zv F_28490 D_28490 (Z_to_bv 64 (8 * m)).              (* [comment removed for export] *)
      sn F_28494 D_28494.                                   (* [comment removed for export] *)
      stepiv F_28498 D_28498 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply xor_seqz_ne; lia).   (* [comment removed for export] *)
      stepb_ft F_2849c D_2849c ltac:(condR).                (* [comment removed for export] *)
      zv F_284a0 D_284a0 (Z_to_bv 64 (LS)).                 (* [comment removed for export] *)
      sn F_284a4 D_284a4.   (* [comment removed for export] *)
      stepb_ft F_284a8 D_284a8 ltac:(condZ).   (* [comment removed for export] *)
      zv F_284ac D_284ac (Z_to_bv 64 (LS + 1)).   (* [comment removed for export] *)
      stepb_ft F_284b0 D_284b0 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_284b4 D_284b4.   (* [comment removed for export] *)
      sn F_284b8 D_284b8.   (* [comment removed for export] *)
      stepb_ft F_284bc D_284bc ltac:(condR).   (* [comment removed for export] *)
      sn F_284c0 D_284c0.   (* [comment removed for export] *)
      stepb_ft F_284c4 D_284c4 ltac:(condZ).   (* [comment removed for export] *)
      zv F_284c8 D_284c8 (Z_to_bv 64 (LS + 2)).   (* [comment removed for export] *)
      stepb_ft F_284cc D_284cc ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_284d0 D_284d0.   (* [comment removed for export] *)
      sn F_284d4 D_284d4.   (* [comment removed for export] *)
      stepb_ft F_284d8 D_284d8 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_284dc D_284dc ltac:(condZ).   (* [comment removed for export] *)
      zv F_284e0 D_284e0 (Z_to_bv 64 (LS + 3)).   (* [comment removed for export] *)
      stepb_ft F_284e4 D_284e4 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_284e8 D_284e8.   (* [comment removed for export] *)
      sn F_284ec D_284ec.   (* [comment removed for export] *)
      stepb_ft F_284f0 D_284f0 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_284f4 D_284f4 ltac:(condZ).   (* [comment removed for export] *)
      zv F_284f8 D_284f8 (Z_to_bv 64 (LS + 4)).   (* [comment removed for export] *)
      stepb_ft F_284fc D_284fc ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28500 D_28500.   (* [comment removed for export] *)
      sn F_28504 D_28504.   (* [comment removed for export] *)
      stepb_ft F_28508 D_28508 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_2850c D_2850c ltac:(condZ).   (* [comment removed for export] *)
      zv F_28510 D_28510 (Z_to_bv 64 (LS + 5)).   (* [comment removed for export] *)
      stepb_ft F_28514 D_28514 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28518 D_28518.   (* [comment removed for export] *)
      sn F_2851c D_2851c.   (* [comment removed for export] *)
      stepb_ft F_28520 D_28520 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28524 D_28524 ltac:(condZ).   (* [comment removed for export] *)
      zv F_28528 D_28528 (Z_to_bv 64 (LS + 6)).   (* [comment removed for export] *)
      stepb_ft F_2852c D_2852c ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28530 D_28530.   (* [comment removed for export] *)
      sn F_28534 D_28534.   (* [comment removed for export] *)
      stepb_ft F_28538 D_28538 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_2853c D_2853c ltac:(condZ).   (* [comment removed for export] *)
      zv F_28540 D_28540 (Z_to_bv 64 (LS + 7)).   (* [comment removed for export] *)
      stepb_ft F_28544 D_28544 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28548 D_28548.   (* [comment removed for export] *)
      sn F_2854c D_2854c.   (* [comment removed for export] *)
      stepb_ft F_28550 D_28550 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28554 D_28554 ltac:(condZ).   (* [comment removed for export] *)
      zv F_28558 D_28558 (Z_to_bv 64 (LS + 8)).   (* [comment removed for export] *)
      stepb_ft F_2855c D_2855c ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28560 D_28560.   (* [comment removed for export] *)
      sn F_28564 D_28564.   (* [comment removed for export] *)
      stepb_ft F_28568 D_28568 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_2856c D_2856c ltac:(condZ).   (* [comment removed for export] *)
      zv F_28570 D_28570 (Z_to_bv 64 (LS + 9)).   (* [comment removed for export] *)
      stepb_ft F_28574 D_28574 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28578 D_28578.   (* [comment removed for export] *)
      sn F_2857c D_2857c.   (* [comment removed for export] *)
      stepb_ft F_28580 D_28580 ltac:(condR).   (* [comment removed for export] *)
      sn F_28584 D_28584.   (* [comment removed for export] *)
      stepb_ft F_28588 D_28588 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_iterB : forall regs Mi, Inv Mi ->
    getr regs 24 = Z_to_bv 64 LS -> getr regs 25 = Z_to_bv 64 (LS + 1) -> getr regs 8 = Z_to_bv 64 (LS + 2) ->
    getr regs 31 = Z_to_bv 64 (LS + 3) -> getr regs 26 = Z_to_bv 64 (LS + 4) -> getr regs 27 = Z_to_bv 64 (LS + 5) ->
    getr regs 1 = Z_to_bv 64 (LS + 6) -> getr regs 11 = Z_to_bv 64 (LS + 7) -> getr regs 12 = Z_to_bv 64 (LS + 8) ->
    getr regs 15 = Z_to_bv 64 (LS + 9) ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 16 = Z_to_bv 64 (8 * m) -> getr regs 19 = Z_to_bv 64 LDROW -> getr regs 22 = Z_to_bv 64 LDROW ->
    exists regs',
      msteps SEGS (mkst regs (0x28688 : word) Mi rom) (mkst regs' (0x28708 : word) Mi rom)
      /\ getr regs' 20 = Z_to_bv 64 LD /\ getr regs' 24 = Z_to_bv 64 (LD + 1)
      /\ reg_present regs' 9 /\ reg_present regs' 10 /\ reg_present regs' 11 /\ reg_present regs' 8 /\ reg_present regs' 27
      /\ reg_present regs' 31 /\ reg_present regs' 25
      /\ regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 20; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    intros regs Mi HIv H24 H25 H8 H31 H26 H27 H1 H11 H12 H15 H14 H16 H19 H22.
    pose proof (row_bound i Hi) as RB.
    assert (Hw4 : (8 * m + 12 <= 4 * wpl)%Z) by lia.
    pose proof (proj2 HIv) as HG.
    destruct (rd_src Mi (LS + 2) HG ltac:(lia) ltac:(lia)) as (b0 & Hb0).
    destruct (rd_src Mi (LS + 1) HG ltac:(lia) ltac:(lia)) as (b1 & Hb1).
    destruct (rd_src Mi (LS + 3) HG ltac:(lia) ltac:(lia)) as (b2 & Hb2).
    destruct (rd_src Mi (LS + 0) HG ltac:(lia) ltac:(lia)) as (b3 & Hb3). rewrite Z.add_0_r in Hb3.
    destruct (rd_src Mi (LS + 7) HG ltac:(lia) ltac:(lia)) as (b4 & Hb4).
    destruct (rd_src Mi (LS + 6) HG ltac:(lia) ltac:(lia)) as (b5 & Hb5).
    destruct (rd_src Mi (LS + 5) HG ltac:(lia) ltac:(lia)) as (b6 & Hb6).
    destruct (rd_src Mi (LS + 4) HG ltac:(lia) ltac:(lia)) as (b7 & Hb7).
    destruct (rd_src Mi (LS + 11) HG ltac:(lia) ltac:(lia)) as (b8 & Hb8).
    destruct (rd_src Mi (LS + 10) HG ltac:(lia) ltac:(lia)) as (b9 & Hb9).
    eexists. split.
    -
      gxor3 F_2858c D_2858c (LS)%Z 1%Z 2%Z.   (* [comment removed for export] *)
      gxor3 F_28590 D_28590 (LS)%Z 2%Z 1%Z.   (* [comment removed for export] *)
      stepLBU F_28594 D_28594 b0 ltac:(rdn_addr (LS + 2)%Z; exact Hb0).   (* [comment removed for export] *)
      stepLBU F_28598 D_28598 b1 ltac:(rdn_addr (LS + 1)%Z; exact Hb1).   (* [comment removed for export] *)
      stepDIA F_2859c D_2859c F_285a0 D_285a0.   (* [comment removed for export] *)
      gxor3 F_285a4 D_285a4 (LS)%Z 0%Z 3%Z.   (* [comment removed for export] *)
      stepLBU F_285a8 D_285a8 b2 ltac:(rdn_addr (LS + 3)%Z; exact Hb2).   (* [comment removed for export] *)
      stepDIA F_285ac D_285ac F_285b0 D_285b0.   (* [comment removed for export] *)
      zv F_285b4 D_285b4 (Z_to_bv 64 (LD)).   (* [comment removed for export] *)
      zv F_285b8 D_285b8 (Z_to_bv 64 (LD + 1)).   (* [comment removed for export] *)
      stepb_ft F_285bc D_285bc ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_285c0 D_285c0.   (* [comment removed for export] *)
      sn F_285c4 D_285c4.   (* [comment removed for export] *)
      stepb_ft F_285c8 D_285c8 ltac:(condR).   (* [comment removed for export] *)
      sn F_285cc D_285cc.   (* [comment removed for export] *)
      stepb_ft F_285d0 D_285d0 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_285d4 D_285d4 (LS)%Z 3%Z 0%Z.   (* [comment removed for export] *)
      gxor3 F_285d8 D_285d8 (LS)%Z 4%Z 7%Z.   (* [comment removed for export] *)
      gxor3 F_285dc D_285dc (LS)%Z 5%Z 6%Z.   (* [comment removed for export] *)
      gxor3 F_285e0 D_285e0 (LS)%Z 6%Z 5%Z.   (* [comment removed for export] *)
      gxor3 F_285e4 D_285e4 (LS)%Z 7%Z 4%Z.   (* [comment removed for export] *)
      gxor3 F_285e8 D_285e8 (LS)%Z 8%Z 11%Z.   (* [comment removed for export] *)
      stepLBU F_285ec D_285ec b3 ltac:(rdn_addr (LS)%Z; exact Hb3).   (* [comment removed for export] *)
      stepLBU F_285f0 D_285f0 b4 ltac:(rdn_addr (LS + 7)%Z; exact Hb4).   (* [comment removed for export] *)
      stepLBU F_285f4 D_285f4 b5 ltac:(rdn_addr (LS + 6)%Z; exact Hb5).   (* [comment removed for export] *)
      stepLBU F_285f8 D_285f8 b6 ltac:(rdn_addr (LS + 5)%Z; exact Hb6).   (* [comment removed for export] *)
      stepLBU F_285fc D_285fc b7 ltac:(rdn_addr (LS + 4)%Z; exact Hb7).   (* [comment removed for export] *)
      stepLBU F_28600 D_28600 b8 ltac:(rdn_addr (LS + 11)%Z; exact Hb8).   (* [comment removed for export] *)
      gxor3 F_28604 D_28604 (LS)%Z 9%Z 10%Z.   (* [comment removed for export] *)
      stepLBU F_28608 D_28608 b9 ltac:(rdn_addr (LS + 10)%Z; exact Hb9).   (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; pin; reflexivity|]. split; [gres; pin; reflexivity|].
      repeat (split; [gray_presence|]). solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_iterC1 : forall regs Mi, Inv Mi ->
    getr regs 20 = Z_to_bv 64 LD -> getr regs 24 = Z_to_bv 64 (LD + 1) ->
    reg_present regs 9 -> reg_present regs 10 -> reg_present regs 11 ->
    reg_present regs 8 -> reg_present regs 27 -> reg_present regs 25 -> reg_present regs 31 ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 18446744073709551615 -> getr regs 6 = Z_to_bv 64 18446744073709551614 ->
    getr regs 7 = Z_to_bv 64 18446744073709551613 -> getr regs 28 = Z_to_bv 64 18446744073709551612 ->
    getr regs 29 = Z_to_bv 64 18446744073709551611 -> getr regs 19 = Z_to_bv 64 LDROW ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28708 : word) Mi rom) (mkst regs' (0x287a0 : word) M' rom)
      /\ Inv M' /\ reg_present regs' 8 /\ reg_present regs' 27 /\ reg_present regs' 25 /\ reg_present regs' 31
      /\ regs_agree (fun r : reg => In r [8; 9; 10; 11; 12; 15]%list) regs regs'.
  Proof.
    intros regs Mi HIv H20 H24 P9 P10 P11 P8 P27 P25 P31 H14 H17 H5 H6 H7 H28 H29 H19.
    pose proof (row_bound i Hi) as RB.
    assert (Hw4 : (8 * m + 12 <= 4 * wpl)%Z) by lia.
    pose proof (proj2 HIv) as HG.
    eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    -
      gxor3 F_2860c D_2860c (LD)%Z 1%Z 2%Z.   (* [comment removed for export] *)
      gsb F_28610 D_28610 (LD + 2)%Z.   (* [comment removed for export] *)
      stepDIA F_28614 D_28614 F_28618 D_28618.   (* [comment removed for export] *)
      zv F_2861c D_2861c (Z_to_bv 64 (LD + 2)).   (* [comment removed for export] *)
      stepb_ft F_28620 D_28620 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_28624 D_28624.   (* [comment removed for export] *)
      sn F_28628 D_28628.   (* [comment removed for export] *)
      stepb_ft F_2862c D_2862c ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28630 D_28630 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_28634 D_28634 (LD)%Z 2%Z 1%Z.   (* [comment removed for export] *)
      gsb F_28638 D_28638 (LD + 1)%Z.   (* [comment removed for export] *)
      stepSEL F_2863c D_2863c F_28640 D_28640 F_28644 D_28644 F_28648 D_28648 F_28650 D_28650 F_28654 D_28654 F_28658 D_28658 F_2865c D_2865c F_28660 D_28660 (Z_to_bv 64 (LD + 3)).   (* [comment removed for export] *)
      seqz0 F_28664 D_28664.   (* [comment removed for export] *)
      sn F_28668 D_28668.   (* [comment removed for export] *)
      stepb_ft F_2866c D_2866c ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28670 D_28670 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_28674 D_28674 (LD)%Z 3%Z 0%Z.   (* [comment removed for export] *)
      gsb F_28678 D_28678 (LD)%Z.   (* [comment removed for export] *)
      stepDIA F_2867c D_2867c F_28680 D_28680.   (* [comment removed for export] *)
      zv F_28684 D_28684 (Z_to_bv 64 (LD + 4)).   (* [comment removed for export] *)
      stepb_ft F_28688 D_28688 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_2868c D_2868c.   (* [comment removed for export] *)
      sn F_28690 D_28690.   (* [comment removed for export] *)
      stepb_ft F_28694 D_28694 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28698 D_28698 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_2869c D_2869c (LD)%Z 4%Z 7%Z.   (* [comment removed for export] *)
      gsb F_286a0 D_286a0 (LD + 7)%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat (apply Inv_store; [ | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia ]). exact HIv.
    - gray_presence.
    - gray_presence.
    - gray_presence.
    - gray_presence.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_iterC2 : forall regs Mi, Inv Mi ->
    getr regs 20 = Z_to_bv 64 LD -> reg_present regs 27 -> reg_present regs 8 -> reg_present regs 25 -> reg_present regs 31 ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 18446744073709551615 -> getr regs 6 = Z_to_bv 64 18446744073709551614 ->
    getr regs 7 = Z_to_bv 64 18446744073709551613 -> getr regs 28 = Z_to_bv 64 18446744073709551612 ->
    getr regs 29 = Z_to_bv 64 18446744073709551611 -> getr regs 19 = Z_to_bv 64 LDROW ->
    exists regs' M',
      msteps SEGS (mkst regs (0x287a0 : word) Mi rom) (mkst regs' (0x28808 : word) M' rom)
      /\ Inv M' /\ reg_present regs' 25 /\ reg_present regs' 31
      /\ regs_agree (fun r : reg => In r [8; 10; 11; 27]%list) regs regs'.
  Proof.
    intros regs Mi HIv H20 P27 P8 P25 P31 H14 H17 H5 H6 H7 H28 H29 H19.
    pose proof (row_bound i Hi) as RB.
    assert (Hw4 : (8 * m + 12 <= 4 * wpl)%Z) by lia.
    pose proof (proj2 HIv) as HG.
    eexists. eexists. split; [|split; [|split; [|split]]].
    -
      stepSEL F_286a4 D_286a4 F_286a8 D_286a8 F_286ac D_286ac F_286b0 D_286b0 F_286b8 D_286b8 F_286bc D_286bc F_286c0 D_286c0 F_286c4 D_286c4 F_286c8 D_286c8 (Z_to_bv 64 (LD + 5)).   (* [comment removed for export] *)
      seqz0 F_286cc D_286cc.   (* [comment removed for export] *)
      sn F_286d0 D_286d0.   (* [comment removed for export] *)
      stepb_ft F_286d4 D_286d4 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_286d8 D_286d8 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_286dc D_286dc (LD)%Z 5%Z 6%Z.   (* [comment removed for export] *)
      gsb F_286e0 D_286e0 (LD + 6)%Z.   (* [comment removed for export] *)
      stepDIA F_286e4 D_286e4 F_286e8 D_286e8.   (* [comment removed for export] *)
      zv F_286ec D_286ec (Z_to_bv 64 (LD + 6)).   (* [comment removed for export] *)
      stepb_ft F_286f0 D_286f0 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_286f4 D_286f4.   (* [comment removed for export] *)
      sn F_286f8 D_286f8.   (* [comment removed for export] *)
      stepb_ft F_286fc D_286fc ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28700 D_28700 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_28704 D_28704 (LD)%Z 6%Z 5%Z.   (* [comment removed for export] *)
      gsb F_28708 D_28708 (LD + 5)%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat (apply Inv_store; [ | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia ]). exact HIv.
    - gray_presence.
    - gray_presence.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_iterC3 : forall regs Mi, Inv Mi ->
    getr regs 20 = Z_to_bv 64 LD -> reg_present regs 25 -> reg_present regs 31 ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
    getr regs 5 = Z_to_bv 64 18446744073709551615 -> getr regs 6 = Z_to_bv 64 18446744073709551614 ->
    getr regs 7 = Z_to_bv 64 18446744073709551613 -> getr regs 28 = Z_to_bv 64 18446744073709551612 ->
    getr regs 29 = Z_to_bv 64 18446744073709551611 -> getr regs 19 = Z_to_bv 64 LDROW ->
    getr regs 16 = Z_to_bv 64 (8 * m) -> getr regs 22 = Z_to_bv 64 LDROW ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28808 : word) Mi rom) (mkst regs' (0x28878 : word) M' rom)
      /\ Inv M' /\ getr regs' 16 = Z_to_bv 64 (8 * (m + 1))
      /\ regs_agree (fun r : reg => In r [10; 11; 16; 25; 31]%list) regs regs'.
  Proof.
    intros regs Mi HIv H20 P25 P31 H14 H17 H5 H6 H7 H28 H29 H19 H16 H22.
    pose proof (row_bound i Hi) as RB.
    assert (Hw4 : (8 * m + 12 <= 4 * wpl)%Z) by lia.
    pose proof (proj2 HIv) as HG.
    eexists. eexists. split; [|split; [|split]].
    -
      stepSEL F_2870c D_2870c F_28710 D_28710 F_28714 D_28714 F_28718 D_28718 F_28720 D_28720 F_28724 D_28724 F_28728 D_28728 F_2872c D_2872c F_28730 D_28730 (Z_to_bv 64 (LD + 7)).   (* [comment removed for export] *)
      seqz0 F_28734 D_28734.   (* [comment removed for export] *)
      sn F_28738 D_28738.   (* [comment removed for export] *)
      stepb_ft F_2873c D_2873c ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28740 D_28740 ltac:(condZ).   (* [comment removed for export] *)
      gxor3 F_28744 D_28744 (LD)%Z 7%Z 4%Z.   (* [comment removed for export] *)
      gsb F_28748 D_28748 (LD + 4)%Z.   (* [comment removed for export] *)
      stepDIA F_2874c D_2874c F_28750 D_28750.   (* [comment removed for export] *)
      zv F_28754 D_28754 (Z_to_bv 64 (LD + 8)).   (* [comment removed for export] *)
      stepb_ft F_28758 D_28758 ltac:(condZ).   (* [comment removed for export] *)
      seqz0 F_2875c D_2875c.   (* [comment removed for export] *)
      sn F_28760 D_28760.   (* [comment removed for export] *)
      stepb_ft F_28764 D_28764 ltac:(condR).   (* [comment removed for export] *)
      stepb_ft F_28768 D_28768 ltac:(condZ).   (* [comment removed for export] *)
      zv F_2876c D_2876c (Z_to_bv 64 (8 * (m + 1))).        (* [comment removed for export] *)
      zv F_28770 D_28770 (Z_to_bv 64 (LD + 8)).             (* [comment removed for export] *)
      gxor3 F_28774 D_28774 (LD)%Z 8%Z 11%Z.                (* [comment removed for export] *)
      gsb F_28778 D_28778 (LD + 11)%Z.                      (* [comment removed for export] *)
      apply mst_refl.
    - repeat (apply Inv_store; [ | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia ]). exact HIv.
    - gres; pin; reflexivity.
    - solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma g3_iter : forall regs Mi, Inv Mi -> LInv regs i ->
    getr regs 10 = Z_to_bv 64 (w - 8) -> getr regs 16 = Z_to_bv 64 (8 * m) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28584 : word) Mi rom) (mkst regs' (0x28878 : word) M' rom)
      /\ Inv M' /\ LInv regs' i /\ getr regs' 16 = Z_to_bv 64 (8 * (m + 1))
      /\ regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 15; 16; 20; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    intros regs Mi HIv LI H10 H16.
    pose proof LI as (I2 & I13 & I14 & I17 & I5 & I6 & I7 & I28 & I29 & I18 & I19 & I21 & I22 & I23).
    destruct (g3_iterA regs Mi H10 H16 I13 I14 I17 I5 I6 I7 I28 I29 I18 I21 I23)
      as (r1 & S1 & A24 & A25 & A8 & A31 & A26 & A27 & A1 & A11 & A12 & A15 & AG1).
    assert (L1 : LInv r1 i) by (apply (LInv_agree regs r1 i); [regs_agree_weaken AG1 | exact LI]).
    pose proof L1 as (J2 & J13 & J14 & J17 & J5 & J6 & J7 & J28 & J29 & J18 & J19 & J21 & J22 & J23).
    pose proof (AG1 16 ltac:(notin_list)) as A16; rewrite H16 in A16.
    destruct (g3_iterB r1 Mi HIv A24 A25 A8 A31 A26 A27 A1 A11 A12 A15 J14 A16 J19 J22)
      as (r2 & S2 & B20 & B24 & Q9 & Q10 & Q11 & Q8 & Q27 & Q31 & Q25 & AG2).
    assert (L2 : LInv r2 i) by (apply (LInv_agree r1 r2 i); [regs_agree_weaken AG2 | exact L1]).
    pose proof L2 as (K2 & K13 & K14 & K17 & K5 & K6 & K7 & K28 & K29 & K18 & K19 & K21 & K22 & K23).
    destruct (g3_iterC1 r2 Mi HIv B20 B24 Q9 Q10 Q11 Q8 Q27 Q25 Q31 K14 K17 K5 K6 K7 K28 K29 K19)
      as (r3 & M3 & S3 & HI3 & R8 & R27 & R25 & R31 & AG3).
    assert (L3 : LInv r3 i) by (apply (LInv_agree r2 r3 i); [regs_agree_weaken AG3 | exact L2]).
    pose proof L3 as (N2 & N13 & N14 & N17 & N5 & N6 & N7 & N28 & N29 & N18 & N19 & N21 & N22 & N23).
    pose proof (AG3 20 ltac:(notin_list)) as C20; rewrite B20 in C20.
    destruct (g3_iterC2 r3 M3 HI3 C20 R27 R8 R25 R31 N14 N17 N5 N6 N7 N28 N29 N19) as (r4 & M4 & S4 & HI4 & T25 & T31 & AG4).
    assert (L4 : LInv r4 i) by (apply (LInv_agree r3 r4 i); [regs_agree_weaken AG4 | exact L3]).
    pose proof L4 as (O2 & O13 & O14 & O17 & O5 & O6 & O7 & O28 & O29 & O18 & O19 & O21 & O22 & O23).
    pose proof (AG4 20 ltac:(notin_list)) as D20; rewrite C20 in D20.
    pose proof (AG4 16 ltac:(notin_list)) as D16; rewrite (AG3 16 ltac:(notin_list)), (AG2 16 ltac:(notin_list)), A16 in D16.
    destruct (g3_iterC3 r4 M4 HI4 D20 T25 T31 O14 O17 O5 O6 O7 O28 O29 O19 D16 O22) as (r5 & M5 & S5 & HI5 & E16 & AG5).
    assert (L5 : LInv r5 i) by (apply (LInv_agree r4 r5 i); [regs_agree_weaken AG5 | exact L4]).
    exists r5, M5. split; [|split; [exact HI5 | split; [exact L5 | split; [exact E16|]]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
      eapply msteps_trans; [exact S4 | exact S5].
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|].
      eapply regs_agree_trans; [regs_agree_weaken AG3|]. eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5].
  Qed.
  End ITER.
  (* [comment removed for export] *)
  Lemma g3_latch : forall regs Mi, Inv Mi -> getr regs 2 = Z_to_bv 64 sp ->
    exists regs',
      msteps SEGS (mkst regs (0x28878 : word) Mi rom) (mkst regs' (0x28584 : word) Mi rom)
      /\ getr regs' 10 = Z_to_bv 64 (w - 8)
      /\ regs_agree (fun r : reg => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2. eexists. split.
    - stepLD F_2877c D_2877c (Z_to_le_bytes 4 w) (Z_to_bv 64 w)
        ltac:(rdn_addr (sp + 52)%Z; apply (Inv_rdn_frame Mi 52 4 _ HIv); [lia | cbn; lia | cbn; lia | exact CwR])
        ltac:(apply lez4w; lia).
      rewrite (v_lw_small w) by lia.                        (* [comment removed for export] *)
      zvw F_28780 D_28780 (Z_to_bv 64 (w - 8)).             (* [comment removed for export] *)
      stepb_tk F_28784 D_28784 ltac:(condS).                (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; pin; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  Lemma g3_inner : forall (k : nat) regs Mi i m,
    (0 <= i < h)%Z -> (0 <= m /\ 8 * m <= w + 8)%Z -> (w <= 8 * (m + Z.of_nat k) + 9)%Z -> ((0 < k)%nat -> (8 * (m + Z.of_nat k - 1) + 9 < w)%Z) ->
    Inv Mi -> LInv regs i -> getr regs 10 = Z_to_bv 64 (w - 8) -> getr regs 16 = Z_to_bv 64 (8 * m) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28584 : word) Mi rom) (mkst regs' (0x284dc : word) M' rom)
      /\ Inv M' /\ LInv regs' i
      /\ regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 15; 16; 20; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i m Hi Hm Hk1 Hk2 HIv LI H10 H16.
    - exists (regupd regs 11 (Z_to_bv 64 (8 * m + 1))), Mi. split; [|split; [exact HIv | split]].
      + zv F_28488 D_28488 (Z_to_bv 64 (8 * m + 1)).        (* [comment removed for export] *)
        stepb_tk F_2848c D_2848c ltac:(condS).              (* [comment removed for export] *)
        apply mst_refl.
      + apply (LInv_agree regs); [solve_regs_agree | exact LI].
      + solve_regs_agree.
    - assert (Hm' : (0 <= m /\ 8 * m + 9 < w)%Z) by (specialize (Hk2 ltac:(lia)); lia).
      destruct (g3_iter i m Hi Hm' (mod4_lin datas i m (proj2 (proj2 Hds))) (mod4_lin datad i m (proj2 (proj2 Hdd))) regs Mi HIv LI H10 H16)
        as (r1 & M1 & S1 & HI1 & L1 & A16 & AG1).
      destruct (g3_latch r1 M1 HI1 (proj1 L1)) as (r2 & S2 & B10 & AG2).
      assert (L2 : LInv r2 i) by (apply (LInv_agree r1); [regs_agree_weaken AG2 | exact L1]).
      pose proof (AG2 16 ltac:(notin_list)) as B16; rewrite A16 in B16.
      destruct (IH r2 M1 i (m + 1)%Z Hi ltac:(lia) ltac:(lia) ltac:(intros; lia) HI1 L2 B10 B16) as (r3 & M3 & S3 & HI3 & L3 & AG3).
      exists r3, M3. split; [|split; [exact HI3 | split; [exact L3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.
  End INNER.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation le8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)) (only parsing).
  Definition RowMem (Mi : word -> option byte) (i : Z) : Prop :=
    (forall x : word, (bv_unsigned x < datad \/ datad + RS <= bv_unsigned x)%Z -> (bv_unsigned x < sp \/ sp + 48 <= bv_unsigned x)%Z -> Mi x = M x)
    /\ mem_grows M Mi
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 0)) 8 = Some (le8 pixd)
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 8)) 8 = Some (le8 wpl)
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 24)) 8 = Some (le8 datas)
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 32)) 8 = Some (le8 datad)
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 40)) 8 = Some (le8 (wpl * i))
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h)
    /\ rdn SEGS Mi (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w).

  Ltac peel := repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

  Lemma RowMem_Mp : RowMem Mp 0.
  Proof.
    unfold RowMem, Mp. split; [|split; [grows|]].
    - intros x _ Hx. rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
    - replace (wpl * 0)%Z with 0%Z by lia.
      repeat split; peel; first [ exact Ch | exact Cw | apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma RowMem_16 : forall Mi i v, RowMem Mi i -> RowMem (wbytes Mi (Z_to_bv 64 (sp + 16)) (le8 v)) i.
  Proof.
    intros Mi i v (HF & HG & C0 & C8 & C24 & C32 & C40 & C48 & C52). unfold RowMem. split; [|split].
    - intros x Hx1 Hx2. rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). apply HF; assumption.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
    - repeat split; peel; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma RowMem_40 : forall Mi i, RowMem Mi i -> RowMem (wbytes Mi (Z_to_bv 64 (sp + 40)) (le8 (wpl * (i + 1)))) (i + 1).
  Proof.
    intros Mi i (HF & HG & C0 & C8 & C24 & C32 & C40 & C48 & C52). unfold RowMem. split; [|split].
    - intros x Hx1 Hx2. rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). apply HF; assumption.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
    - repeat split; peel; first [ assumption | apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma RowMem_inner : forall Mr Mi i bs, RowMem Mr i -> rdn SEGS Mr (Z_to_bv 64 (sp + 16)) 8 = Some bs -> Inv Mr Mi ->
    RowMem Mi i /\ rdn SEGS Mi (Z_to_bv 64 (sp + 16)) 8 = Some bs.
  Proof.
    intros Mr Mi i bs (HF & HG & C0 & C8 & C24 & C32 & C40 & C48 & C52) C16 HIv.
    pose proof HIv as [HI HGi].
    assert (FRD : forall k (n : nat) b, (0 <= k)%Z -> (1 <= Z.of_nat n)%Z -> (k + Z.of_nat n <= 56)%Z ->
              rdn SEGS Mr (Z_to_bv 64 (sp + k)) n = Some b -> rdn SEGS Mi (Z_to_bv 64 (sp + k)) n = Some b)
      by (intros k n b; apply (Inv_rdn_frame Mr Mi k n b HIv)).
    split; [|apply (FRD 16%Z 8%nat); [lia | cbn; lia | cbn; lia | exact C16]].
    unfold RowMem. split; [|split].
    - intros x Hx1 Hx2. rewrite (HI x Hx1). apply HF; assumption.
    - eapply mem_grows_trans; [exact HG | exact HGi].
    - repeat split; [apply (FRD 0%Z 8%nat) | apply (FRD 8%Z 8%nat) | apply (FRD 24%Z 8%nat) | apply (FRD 32%Z 8%nat)
                     | apply (FRD 40%Z 8%nat) | apply (FRD 48%Z 4%nat) | apply (FRD 52%Z 4%nat)]; first [assumption | lia | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Definition RInv (regs : bvmap 5 word) (i : Z) : Prop :=
    getr regs 2 = Z_to_bv 64 sp /\ getr regs 10 = Z_to_bv 64 wpl /\ getr regs 15 = Z_to_bv 64 i /\ getr regs 19 = Z_to_bv 64 datas /\
    getr regs 13 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 1 /\ getr regs 17 = Z_to_bv 64 1 /\
    getr regs 5 = Z_to_bv 64 18446744073709551615 /\ getr regs 6 = Z_to_bv 64 18446744073709551614 /\
    getr regs 7 = Z_to_bv 64 18446744073709551613 /\ getr regs 28 = Z_to_bv 64 18446744073709551612 /\
    getr regs 29 = Z_to_bv 64 18446744073709551611.

  Ltac ldc F D k z C :=
    stepLD F D (le8 z) (Z_to_bv 64 z) ltac:(rdn_addr (sp + k)%Z; exact C) ltac:(apply bytes_le_to_Z_8).

  (* [comment removed for export] *)
  Lemma g3_rowhead : forall regs Mi i, (0 <= i < h)%Z -> RowMem Mi i -> RInv regs i ->
    exists regs',
      msteps SEGS (mkst regs (0x28500 : word) Mi rom) (mkst regs' (0x28584 : word) (wbytes Mi (Z_to_bv 64 (sp + 16)) (le8 i)) rom)
      /\ LInv regs' i /\ getr regs' 10 = Z_to_bv 64 (w - 8) /\ getr regs' 16 = Z_to_bv 64 (8 * 0)
      /\ regs_agree (fun r : reg => In r [10; 11; 12; 16; 18; 19; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs Mi i Hi RM (I2 & I10 & I15 & I19 & I13 & I14 & I17 & I5 & I6 & I7 & I28 & I29).
    pose proof (RowMem_16 Mi i i RM) as (_ & _ & C0 & C8 & C24 & C32 & C40 & C48 & C52).
    pose proof (row_bound i Hi) as RB.
    assert (WI : (0 <= wpl * i <= 400000000)%Z)
      by (split; [apply Z.mul_nonneg_nonneg; lia | change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia]).
    eexists. split; [|split; [|split; [|split]]].
    - zv F_28404 D_28404 (Z_to_bv 64 (wpl * i)).            (* [comment removed for export] *)
      stepST F_28408 D_28408 (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 i)
        ltac:(apply sok_spill; [exact (proj1 (proj2 RM)) | lia | cbn; lia]).          (* [comment removed for export] *)
      mulw_v F_2840c D_2840c (Z_to_bv 64 (wpl * i)).        (* [comment removed for export] *)
      stepb_ft F_28410 D_28410 ltac:(condR).                (* [comment removed for export] *)
      zvw F_28414 D_28414 (Z_to_bv 64 (wpl * i)).           (* [comment removed for export] *)
      zvs F_28418 D_28418 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zv F_2841c D_2841c (Z_to_bv 64 (datas + 4 * wpl * i)).   (* [comment removed for export] *)
      seqz0 F_28420 D_28420.                                (* [comment removed for export] *)
      stepb_ft F_28424 D_28424 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_28428 D_28428.                                (* [comment removed for export] *)
      slti0 F_2842c D_2842c.                                (* [comment removed for export] *)
      sn F_28430 D_28430.                                   (* [comment removed for export] *)
      sn F_28434 D_28434.                                   (* [comment removed for export] *)
      stepb_ft F_28438 D_28438 ltac:(condR).                (* [comment removed for export] *)
      ldc F_2843c D_2843c 32%Z datad C32.                   (* [comment removed for export] *)
      zv F_28440 D_28440 (Z_to_bv 64 (datad + 4 * wpl * i)).   (* [comment removed for export] *)
      seqz0 F_28444 D_28444.                                (* [comment removed for export] *)
      stepb_ft F_28448 D_28448 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_2844c D_2844c.                                (* [comment removed for export] *)
      sn F_28450 D_28450.                                   (* [comment removed for export] *)
      sn F_28454 D_28454.                                   (* [comment removed for export] *)
      stepb_ft F_28458 D_28458 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_2845c D_2845c (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(rdn_addr (sp + 52)%Z; exact C52) ltac:(apply lez4w; lia).
      rewrite (v_lw_small w) by lia.                        (* [comment removed for export] *)
      zvw F_28460 D_28460 (Z_to_bv 64 (w - 8)).             (* [comment removed for export] *)
      stepb_ft F_28464 D_28464 ltac:(condS).                (* [comment removed for export] *)
      sn F_28468 D_28468. fixv (Z_to_bv 64 (8 * 0)) ltac:(f_equal; lia).   (* [comment removed for export] *)
      ldc F_2846c D_2846c 40%Z (wpl * i)%Z C40.             (* [comment removed for export] *)
      zvs F_28470 D_28470 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      ldc F_28474 D_28474 24%Z datas C24.                   (* [comment removed for export] *)
      zv F_28478 D_28478 (Z_to_bv 64 (datas + 4 * wpl * i)).   (* [comment removed for export] *)
      ldc F_2847c D_2847c 32%Z datad C32.                   (* [comment removed for export] *)
      zv F_28480 D_28480 (Z_to_bv 64 (datad + 4 * wpl * i)).   (* [comment removed for export] *)
      sn F_28484 D_28484. fixv (Z_to_bv 64 (2 ^ 64 - (datas + 4 * wpl * i))) ltac:(apply zbv_neg; lia).   (* [comment removed for export] *)
      apply mst_refl.
    - unfold LInv. repeat split; gres; pin; reflexivity.
    - gres; pin; reflexivity.
    - gres; pin; reflexivity.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_rowlatch : forall regs Mi i, (0 <= i < h)%Z -> RowMem Mi i ->
    rdn SEGS Mi (Z_to_bv 64 (sp + 16)) 8 = Some (le8 i) -> getr regs 2 = Z_to_bv 64 sp ->
    exists regs',
      msteps SEGS (mkst regs (0x284dc : word) Mi rom) (mkst regs' (0x284fc : word) (wbytes Mi (Z_to_bv 64 (sp + 40)) (le8 (wpl * (i + 1)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 (i + 1) /\ getr regs' 19 = Z_to_bv 64 datas
      /\ regs_agree (fun r : reg => In r [10; 11; 12; 15; 19]%list) regs regs'.
  Proof.
    intros regs Mi i Hi RM C16 H2.
    pose proof RM as (_ & HG & C0 & C8 & C24 & C32 & C40 & C48 & C52).
    pose proof (RowMem_40 Mi i RM) as (_ & _ & _ & _ & D24 & _).
    assert (WI : (0 <= wpl * i /\ wpl * (i + 1) <= 400000000)%Z)
      by (split; [apply Z.mul_nonneg_nonneg; lia | change 400000000%Z with (20000 * 20000)%Z; apply Z.mul_le_mono_nonneg; lia]).
    eexists. split.
    - stepLD F_283e0 D_283e0 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(rdn_addr (sp + 48)%Z; exact C48) ltac:(apply lez4w; lia).
      rewrite (v_lw_small h) by lia.                        (* [comment removed for export] *)
      ldc F_283e4 D_283e4 16%Z i C16.                       (* [comment removed for export] *)
      zvw F_283e8 D_283e8 (Z_to_bv 64 (i + 1)).             (* [comment removed for export] *)
      ldc F_283ec D_283ec 8%Z wpl C8.                       (* [comment removed for export] *)
      ldc F_283f0 D_283f0 40%Z (wpl * i)%Z C40.             (* [comment removed for export] *)
      addw_v F_283f4 D_283f4 (Z_to_bv 64 (wpl * (i + 1))).  (* [comment removed for export] *)
      stepST F_283f8 D_283f8 (Z_to_bv 64 (sp + 40)) (Z_to_bv 64 (wpl * (i + 1)))
        ltac:(apply sok_spill; [exact HG | lia | cbn; lia]).                          (* [comment removed for export] *)
      ldc F_283fc D_283fc 24%Z datas D24.                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_rows : forall (k : nat) regs Mi i,
    (0 <= i)%Z -> (i + Z.of_nat k = h - 1)%Z -> RowMem Mi i -> RInv regs i ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28500 : word) Mi rom) (mkst regs' (0x28914 : word) M' rom)
      /\ RowMem M' h /\ getr regs' 2 = Z_to_bv 64 sp
      /\ regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hi Hk RM RI.
    all: destruct (g3_rowhead regs Mi i ltac:(lia) RM RI) as (r1 & S1 & L1 & A10 & A16 & AG1).
    all: pose proof (RowMem_16 Mi i i RM) as RMr.
    all: assert (C16r : rdn SEGS (wbytes Mi (Z_to_bv 64 (sp + 16)) (le8 i)) (Z_to_bv 64 (sp + 16)) 8 = Some (le8 i))
           by (apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia).
    all: set (Mr := wbytes Mi (Z_to_bv 64 (sp + 16)) (le8 i)) in *.
    all: assert (KK : exists kk : nat, (w <= 8 * (0 + Z.of_nat kk) + 9)%Z /\ ((0 < kk)%nat -> (8 * (0 + Z.of_nat kk - 1) + 9 < w)%Z)).
    1, 3: (destruct (Z_le_gt_dec w 9) as [Hs|Hl];
           [ exists 0%nat; split; [lia | intros; lia]
           | exists (Z.to_nat ((w - 2) / 8));
             pose proof (Z.div_mod (w - 2) 8 ltac:(lia)) as DM; pose proof (Z.mod_pos_bound (w - 2) 8 ltac:(lia)) as MB;
             assert (0 <= (w - 2) / 8)%Z by (apply Z.div_pos; lia);
             rewrite Z2Nat.id by lia; split; [lia | intros _; lia] ]).
    all: destruct KK as (kk & Hk1 & Hk2).
    all: destruct (g3_inner Mr (proj1 (proj2 RMr)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RMr))))))))
                     kk r1 Mr i 0 ltac:(lia) ltac:(lia) Hk1 Hk2 (Inv_Mr Mr) L1 A10 A16) as (r2 & M2 & S2 & HI2 & L2 & AG2).
    all: destruct (RowMem_inner Mr M2 i _ RMr C16r HI2) as (RM2 & C16_2).
    all: destruct (g3_rowlatch r2 M2 i ltac:(lia) RM2 C16_2 (proj1 L2)) as (r3 & S3 & B10 & B11 & B15 & B19 & AG3).
    all: pose proof (RowMem_40 M2 i RM2) as RM3.
    all: assert (AG13 : regs_agree (fun r : reg => In r [1; 8; 9; 10; 11; 12; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31]%list) regs r3)
           by (eapply regs_agree_trans; [regs_agree_weaken AG1|]; eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
    - exists r3. eexists. split; [|split; [|split; [|exact AG13]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_tk F_28400 D_28400 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      + replace h with (i + 1)%Z by lia. exact RM3.
      + rewrite (AG13 2 ltac:(notin_list)). exact (proj1 RI).
    - assert (RI3' : RInv r3 (i + 1)).
      { destruct L2 as (I2 & I13 & I14 & I17 & I5 & I6 & I7 & I28 & I29 & _). unfold RInv.
        repeat split; first [ assumption | match goal with |- getr r3 ?r = _ => rewrite (AG3 r ltac:(notin_list)); assumption end ]. }
      destruct (IH r3 _ (i + 1)%Z ltac:(lia) ltac:(lia) RM3 RI3') as (r4 & M4 & S4 & RM4 & D2 & AG4).
      exists r4, M4. split; [|split; [exact RM4 | split; [exact D2|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_ft F_28400 D_28400 ltac:(condZ).
        exact S4.
      + eapply regs_agree_trans; [exact AG13 | exact AG4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem g3_run : forall regs,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 datad ->
    getr regs 19 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 wpl ->
    exists regs' M',
      msteps SEGS (mkst regs (0x28498 : word) M rom) (mkst regs' (0x28920 : word) M' rom)
      /\ (forall x : word, (bv_unsigned x < datad \/ datad + RS <= bv_unsigned x)%Z -> (bv_unsigned x < sp \/ sp + 48 <= bv_unsigned x)%Z -> M' x = M x)
      /\ mem_grows M M'
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r : reg => In r [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H2 H8 H9 H19 H10.
    destruct (g3_pre regs H2 H8 H9 H19 H10) as (r1 & S1 & A15 & A13 & A14 & A17 & A5 & A6 & A7 & A28 & A29 & AG1).
    assert (RI : RInv r1 0).
    { unfold RInv. repeat split; try assumption.
      - rewrite (AG1 2 ltac:(notin_list)); exact H2.
      - rewrite (AG1 10 ltac:(notin_list)); exact H10.
      - rewrite (AG1 19 ltac:(notin_list)); exact H19. }
    destruct (g3_rows (Z.to_nat (h - 1)) r1 Mp 0 ltac:(lia) ltac:(lia) RowMem_Mp RI) as (r2 & M2 & S2 & RM2 & B2 & AG2).
    pose proof RM2 as (HF & HG & C0 & _).
    eexists. exists M2. split; [|split; [exact HF | split; [exact HG | split; [|split]]]].
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      ldc F_28818 D_28818 0%Z pixd C0.                      (* [comment removed for export] *)
      sn F_2881c D_2881c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - gres. exact B2.
    - gres. reflexivity.
    - eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. solve_regs_agree.
  Qed.

End G3.
