(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib GrayLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14_code_gmD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

Section G3.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables w h wpl datas datad sp pixd : Z.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hwpl : (w <= 4 * wpl /\ wpl <= 20000)%Z.
  Hypothesis Hsp : (0 <= sp /\ sp + 8 <= 2 ^ 64)%Z.
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 sp) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 (sp + 4)) 4 = Some (Z_to_le_bytes 4 w).

  (* [comment removed for export] *)
  Lemma g3_pre : forall regs,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 datas -> getr regs 9 = Z_to_bv 64 datad ->
    getr regs 19 = Z_to_bv 64 pixd -> getr regs 10 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (0x208cc : word) M rom) (mkst regs' (0x20900 : word) M rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 datas /\ getr regs' 9 = Z_to_bv 64 datad
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * wpl)
      /\ getr regs' 13 = Z_to_bv 64 10 /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [10; 11; 12; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs H2 H8 H9 H19 H10.
    eexists. split.
    - stepLD F_207d0 D_207d0 (Z_to_le_bytes 4 h) (Z_to_bv 64 h)
        ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; exact Ch)
        ltac:(rewrite bytes_le_Z_to_le by lia; change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z; rewrite Z.mod_small by lia; rewrite u_Z2bv by lia; reflexivity).
      rewrite (v_lw_small h) by lia.
      stepb_ft F_207d4 D_207d4 ltac:(condZ).
      sn F_207d8 D_207d8.
      stepLD F_207dc D_207dc (Z_to_le_bytes 4 w) (Z_to_bv 64 w)
        ltac:(unfold v_addi; unorm; exact Cw)
        ltac:(rewrite bytes_le_Z_to_le by lia; change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z; rewrite Z.mod_small by lia; rewrite u_Z2bv by lia; reflexivity).
      rewrite (v_lw_small w) by lia.
      stepiv F_207e0 D_207e0 (Z_to_bv 64 (4 * wpl))
        ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_207e4 D_207e4.
      zv F_207e8 D_207e8 (Z_to_bv 64 pixd).
      sn F_207ec D_207ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation RS := (4 * (wpl * h))%Z (only parsing).
  Hypothesis Hds : (0 <= datas /\ datas + RS <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
  Hypothesis Hdd : (0 <= datad /\ datad + RS <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
  Hypothesis SOKs : store_ok SEGS M (Z_to_bv 64 datas) (Z.to_nat RS) = true.
  Hypothesis SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat RS) = true.
  Hypothesis FR : disj_apart datad RS sp 8.

  Lemma wr_readable_o14d : wr_readable SEGS.
  Proof.
    intros seg Hin Hwr. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < datad \/ datad + RS <= bv_unsigned x)%Z -> Mi x = M x) /\ mem_grows M Mi.
  Lemma Inv_M : Inv M.
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
    mem_grows M Mi -> store_ok SEGS M (Z_to_bv 64 base) (Z.to_nat RS) = true -> (0 <= base /\ base + RS <= 2 ^ 64)%Z ->
    (base <= a)%Z -> (a + Z.of_nat n <= base + RS)%Z -> store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi base a n HG SOK Hb Ha Hn. eapply store_ok_mono; [exact HG|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rd_src : forall Mi (a : Z), mem_grows M Mi -> (datas <= a)%Z -> (a + 1 <= datas + RS)%Z ->
    exists b, rdn SEGS Mi (Z_to_bv 64 a) 1 = Some [b].
  Proof.
    intros Mi a HG Ha H1.
    destruct (store_ok_rdn SEGS Mi 1 (Z_to_bv 64 a) wr_readable_o14d) as (bs & Hbs & Lbs).
    { apply (sok_in Mi datas a 1 HG SOKs); [lia | lia | cbn; lia]. }
    destruct bs as [|b [|? ?]]; try discriminate. exists b. exact Hbs.
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

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ITER.
  Variables i m : Z.
  #[local] Abbreviation LS := (datas + 4 * wpl * i + 8 * m)%Z (only parsing).
  #[local] Abbreviation LD := (datad + 4 * wpl * i + 8 * m)%Z (only parsing).
  Hypothesis Hi : (0 <= i)%Z.
  Hypothesis Hm : (0 <= m /\ 8 * m + 9 < w)%Z.
  Hypothesis Hrow : (4 * wpl * i + 4 * wpl <= RS)%Z.
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
      | eapply store_ok_mono; [ grows | lazymatch goal with HGx : mem_grows M _ |- _ => apply (sok_in _ datad aa 1 HGx SOKd); [lia | lia | cbn; lia] end ] ]
    | step_simpl ].

  Lemma g3_iter : forall regs Mi,
    Inv Mi ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 (datas + 4 * wpl * i) -> getr regs 9 = Z_to_bv 64 (datad + 4 * wpl * i) ->
    getr regs 14 = Z_to_bv 64 (8 * m) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x2092c : word) Mi rom) (mkst regs' (0x20918 : word) M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 14 = Z_to_bv 64 (8 * m)
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Mi HIv H2 H8 H9 H14.
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
    eexists. eexists. split; [|split; [|split; [|split]]].
    -
      zv F_20830 D_20830 (Z_to_bv 64 (LS)).   (* [comment removed for export] *)
      zv F_20834 D_20834 (Z_to_bv 64 (LS + 1)).   (* [comment removed for export] *)
      zv F_20838 D_20838 (Z_to_bv 64 (LS + 2)).   (* [comment removed for export] *)
      gxor3 F_2083c D_2083c (LS)%Z 1%Z 2%Z.   (* [comment removed for export] *)
      gxor3 F_20840 D_20840 (LS)%Z 2%Z 1%Z.   (* [comment removed for export] *)
      stepLBU F_20844 D_20844 b0 ltac:(rdn_addr (LS + 2)%Z; exact Hb0).   (* [comment removed for export] *)
      stepLBU F_20848 D_20848 b1 ltac:(rdn_addr (LS + 1)%Z; exact Hb1).   (* [comment removed for export] *)
      stepDIA F_2084c D_2084c F_20850 D_20850.   (* [comment removed for export] *)
      gxor3 F_20854 D_20854 (LS)%Z 0%Z 3%Z.   (* [comment removed for export] *)
      stepLBU F_20858 D_20858 b2 ltac:(rdn_addr (LS + 3)%Z; exact Hb2).   (* [comment removed for export] *)
      stepDIA F_2085c D_2085c F_20860 D_20860.   (* [comment removed for export] *)
      zv F_20864 D_20864 (Z_to_bv 64 (LS + 3)).   (* [comment removed for export] *)
      zv F_20868 D_20868 (Z_to_bv 64 (LS + 4)).   (* [comment removed for export] *)
      zv F_2086c D_2086c (Z_to_bv 64 (LS + 5)).   (* [comment removed for export] *)
      zv F_20870 D_20870 (Z_to_bv 64 (LS + 6)).   (* [comment removed for export] *)
      zv F_20874 D_20874 (Z_to_bv 64 (LS + 7)).   (* [comment removed for export] *)
      zv F_20878 D_20878 (Z_to_bv 64 (LS + 8)).   (* [comment removed for export] *)
      zv F_2087c D_2087c (Z_to_bv 64 (LS + 9)).   (* [comment removed for export] *)
      gxor3 F_20880 D_20880 (LS)%Z 3%Z 0%Z.   (* [comment removed for export] *)
      gxor3 F_20884 D_20884 (LS)%Z 4%Z 7%Z.   (* [comment removed for export] *)
      gxor3 F_20888 D_20888 (LS)%Z 5%Z 6%Z.   (* [comment removed for export] *)
      gxor3 F_2088c D_2088c (LS)%Z 6%Z 5%Z.   (* [comment removed for export] *)
      gxor3 F_20890 D_20890 (LS)%Z 7%Z 4%Z.   (* [comment removed for export] *)
      gxor3 F_20894 D_20894 (LS)%Z 8%Z 11%Z.   (* [comment removed for export] *)
      gxor3 F_20898 D_20898 (LS)%Z 9%Z 10%Z.   (* [comment removed for export] *)
      stepLBU F_2089c D_2089c b3 ltac:(rdn_addr (LS)%Z; exact Hb3).   (* [comment removed for export] *)
      stepLBU F_208a0 D_208a0 b4 ltac:(rdn_addr (LS + 7)%Z; exact Hb4).   (* [comment removed for export] *)
      stepLBU F_208a4 D_208a4 b5 ltac:(rdn_addr (LS + 6)%Z; exact Hb5).   (* [comment removed for export] *)
      stepLBU F_208a8 D_208a8 b6 ltac:(rdn_addr (LS + 5)%Z; exact Hb6).   (* [comment removed for export] *)
      stepLBU F_208ac D_208ac b7 ltac:(rdn_addr (LS + 4)%Z; exact Hb7).   (* [comment removed for export] *)
      stepLBU F_208b0 D_208b0 b8 ltac:(rdn_addr (LS + 11)%Z; exact Hb8).   (* [comment removed for export] *)
      stepLBU F_208b4 D_208b4 b9 ltac:(rdn_addr (LS + 10)%Z; exact Hb9).   (* [comment removed for export] *)
      zv F_208b8 D_208b8 (Z_to_bv 64 (LD)).   (* [comment removed for export] *)
      zv F_208bc D_208bc (Z_to_bv 64 (LD + 1)).   (* [comment removed for export] *)
      gxor3 F_208c0 D_208c0 (LD)%Z 1%Z 2%Z.   (* [comment removed for export] *)
      gsb F_208c4 D_208c4 (LD + 2)%Z.   (* [comment removed for export] *)
      stepDIA F_208c8 D_208c8 F_208cc D_208cc.   (* [comment removed for export] *)
      zv F_208d0 D_208d0 (Z_to_bv 64 (LD + 2)).   (* [comment removed for export] *)
      gxor3 F_208d4 D_208d4 (LD)%Z 2%Z 1%Z.   (* [comment removed for export] *)
      gsb F_208d8 D_208d8 (LD + 1)%Z.   (* [comment removed for export] *)
      stepDIA F_208dc D_208dc F_208e0 D_208e0.   (* [comment removed for export] *)
      stepDIA F_208e4 D_208e4 F_208e8 D_208e8.   (* [comment removed for export] *)
      zv F_208ec D_208ec (Z_to_bv 64 (LD + 3)).   (* [comment removed for export] *)
      gxor3 F_208f0 D_208f0 (LD)%Z 3%Z 0%Z.   (* [comment removed for export] *)
      gsb F_208f4 D_208f4 (LD)%Z.   (* [comment removed for export] *)
      stepDIA F_208f8 D_208f8 F_208fc D_208fc.   (* [comment removed for export] *)
      zv F_20900 D_20900 (Z_to_bv 64 (LD + 4)).   (* [comment removed for export] *)
      gxor3 F_20904 D_20904 (LD)%Z 4%Z 7%Z.   (* [comment removed for export] *)
      gsb F_20908 D_20908 (LD + 7)%Z.   (* [comment removed for export] *)
      stepDIA F_2090c D_2090c F_20910 D_20910.   (* [comment removed for export] *)
      stepDIA F_20914 D_20914 F_20918 D_20918.   (* [comment removed for export] *)
      zv F_2091c D_2091c (Z_to_bv 64 (LD + 5)).   (* [comment removed for export] *)
      gxor3 F_20920 D_20920 (LD)%Z 5%Z 6%Z.   (* [comment removed for export] *)
      gsb F_20924 D_20924 (LD + 6)%Z.   (* [comment removed for export] *)
      stepDIA F_20928 D_20928 F_2092c D_2092c.   (* [comment removed for export] *)
      zv F_20930 D_20930 (Z_to_bv 64 (LD + 6)).   (* [comment removed for export] *)
      gxor3 F_20934 D_20934 (LD)%Z 6%Z 5%Z.   (* [comment removed for export] *)
      gsb F_20938 D_20938 (LD + 5)%Z.   (* [comment removed for export] *)
      stepDIA F_2093c D_2093c F_20940 D_20940.   (* [comment removed for export] *)
      stepDIA F_20944 D_20944 F_20948 D_20948.   (* [comment removed for export] *)
      zv F_2094c D_2094c (Z_to_bv 64 (LD + 7)).   (* [comment removed for export] *)
      gxor3 F_20950 D_20950 (LD)%Z 7%Z 4%Z.   (* [comment removed for export] *)
      gsb F_20954 D_20954 (LD + 4)%Z.   (* [comment removed for export] *)
      stepDIAJ F_20958 D_20958 F_2095c D_2095c F_20960 D_20960.   (* [comment removed for export] *)
      zv F_20810 D_20810 (Z_to_bv 64 (LD + 8)).   (* [comment removed for export] *)
      gxor3 F_20814 D_20814 (LD)%Z 8%Z 11%Z.   (* [comment removed for export] *)
      gsb F_20818 D_20818 (LD + 11)%Z.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat (apply Inv_store; [ | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia ]). exact HIv.
    - gres; pin; try reflexivity; assumption.
    - gres; pin; try reflexivity; assumption.
    - solve_regs_agree.
  Qed.
  End ITER.

  (* [comment removed for export] *)
  Lemma Inv_rdn_frame : forall Mi k (n : nat) bs, Inv Mi -> (0 <= k)%Z -> (1 <= Z.of_nat n)%Z -> (k + Z.of_nat n <= 8)%Z ->
    rdn SEGS M (Z_to_bv 64 (sp + k)) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 (sp + k)) n = Some bs.
  Proof.
    intros Mi k n bs [HI _] Hk Hn1 Hn HM. use_apart FR. rewrite <- HM.
    assert (U : bv_unsigned (Z_to_bv 64 (sp + k)) = (sp + k)%Z) by (apply u_Z2bv; lia).
    apply rdn_ext; rewrite U; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma lez4w : forall z, (0 <= z < 2 ^ 31)%Z -> bytes_le_to_Z (Z_to_le_bytes 4 z) = bv_unsigned (Z_to_bv 64 z).
  Proof.
    intros z Hz. rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. rewrite u_Z2bv by lia. reflexivity.
  Qed.

  Lemma mod4_lin : forall a x y : Z, (a mod 4 = 0)%Z -> ((a + 4 * wpl * x + 8 * y) mod 4 = 0)%Z.
  Proof.
    intros a x y Ha. replace (a + 4 * wpl * x + 8 * y)%Z with (a + (wpl * x + 2 * y) * 4)%Z by lia.
    rewrite Z_mod_plus_full. exact Ha.
  Qed.

  Lemma row_bound : forall i, (0 <= i < h)%Z -> (4 * wpl * i + 4 * wpl <= RS)%Z.
  Proof.
    intros i Hi. assert (wpl * i <= wpl * (h - 1))%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_latch : forall regs Mi m, Inv Mi -> (0 <= m /\ 8 * m + 9 < w)%Z ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 14 = Z_to_bv 64 (8 * m) ->
    exists regs',
      msteps SEGS (mkst regs (0x20918 : word) Mi rom) (mkst regs' (0x20928 : word) Mi rom)
      /\ getr regs' 14 = Z_to_bv 64 (8 * (m + 1)) /\ getr regs' 15 = Z_to_bv 64 w
      /\ getr regs' 16 = Z_to_bv 64 (8 * m + 9) /\ getr regs' 17 = Z_to_bv 64 (w - 8)
      /\ regs_agree (fun r : reg => In r [14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs Mi m HIv Hm H2 H14.
    eexists. split.
    - stepLD F_2081c D_2081c (Z_to_le_bytes 4 w) (Z_to_bv 64 w)
        ltac:(rdn_addr (sp + 4)%Z; apply (Inv_rdn_frame Mi 4 4 _ HIv); [lia | cbn; lia | cbn; lia | exact Cw])
        ltac:(apply lez4w; lia).
      rewrite (v_lw_small w) by lia.
      zv F_20820 D_20820 (Z_to_bv 64 (8 * m + 9)).
      zv F_20824 D_20824 (Z_to_bv 64 (w - 8)).
      zv F_20828 D_20828 (Z_to_bv 64 (8 * (m + 1))).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3_inner : forall (k : nat) regs Mi i m,
    (0 <= i < h)%Z -> (0 <= m)%Z -> (8 * (m + Z.of_nat k) + 9 < w <= 8 * (m + Z.of_nat k) + 17)%Z ->
    Inv Mi ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 (datas + 4 * wpl * i) -> getr regs 9 = Z_to_bv 64 (datad + 4 * wpl * i) ->
    getr regs 14 = Z_to_bv 64 (8 * m) ->
    exists regs' M',
      msteps SEGS (mkst regs (0x2092c : word) Mi rom) (mkst regs' (0x208ec : word) M' rom)
      /\ Inv M' /\ getr regs' 15 = Z_to_bv 64 w
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i m Hi Hm Hk HIv H2 H8 H9 H14.
    - destruct (g3_iter i m ltac:(lia) ltac:(lia) (row_bound i Hi) (mod4_lin datas i m (proj2 (proj2 Hds))) (mod4_lin datad i m (proj2 (proj2 Hdd)))
                  regs Mi HIv H2 H8 H9 H14) as (r1 & M1 & S1 & HI1 & A2 & A14 & AG1).
      destruct (g3_latch r1 M1 m HI1 ltac:(lia) A2 A14) as (r2 & S2 & B14 & B15 & B16 & B17 & AG2).
      exists r2, M1. split; [|split; [exact HI1 | split; [exact B15|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        stepb_tk F_2082c D_2082c ltac:(condZ).
        apply mst_refl.
      + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - destruct (g3_iter i m ltac:(lia) ltac:(lia) (row_bound i Hi) (mod4_lin datas i m (proj2 (proj2 Hds))) (mod4_lin datad i m (proj2 (proj2 Hdd)))
                  regs Mi HIv H2 H8 H9 H14) as (r1 & M1 & S1 & HI1 & A2 & A14 & AG1).
      destruct (g3_latch r1 M1 m HI1 ltac:(lia) A2 A14) as (r2 & S2 & B14 & B15 & B16 & B17 & AG2).
      pose proof (AG2 2 ltac:(notin_list)) as B2. rewrite A2 in B2.
      pose proof (AG2 8 ltac:(notin_list)) as B8. rewrite (AG1 8 ltac:(notin_list)), H8 in B8.
      pose proof (AG2 9 ltac:(notin_list)) as B9. rewrite (AG1 9 ltac:(notin_list)), H9 in B9.
      destruct (IH r2 M1 i (m + 1)%Z Hi ltac:(lia) ltac:(lia) HI1 B2 B8 B9 B14) as (r3 & M3 & S3 & HI3 & C15 & AG3).
      exists r3, M3. split; [|split; [exact HI3 | split; [exact C15|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
        stepb_ft F_2082c D_2082c ltac:(condZ).
        exact S3.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma g3_rowlatch_a : forall regs Mi i, Inv Mi ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 (datas + 4 * wpl * i) -> getr regs 9 = Z_to_bv 64 (datad + 4 * wpl * i) ->
    getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (4 * wpl) ->
    exists regs',
      msteps SEGS (mkst regs (0x208ec : word) Mi rom) (mkst regs' (0x208fc : word) Mi rom)
      /\ getr regs' 8 = Z_to_bv 64 (datas + 4 * wpl * (i + 1)) /\ getr regs' 9 = Z_to_bv 64 (datad + 4 * wpl * (i + 1))
      /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 14 = Z_to_bv 64 h
      /\ regs_agree (fun r : reg => In r [8; 9; 11; 14]%list) regs regs'.
  Proof.
    intros regs Mi i HIv H2 H8 H9 H11 H12.
    eexists. split.
    - stepLD F_207f0 D_207f0 (Z_to_le_bytes 4 h) (Z_to_bv 64 h)
        ltac:(rdn_addr (sp + 0)%Z; apply (Inv_rdn_frame Mi 0 4 _ HIv); [lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Ch])
        ltac:(apply lez4w; lia).
      rewrite (v_lw_small h) by lia.
      zv F_207f4 D_207f4 (Z_to_bv 64 (i + 1)).
      zv F_207f8 D_207f8 (Z_to_bv 64 (datad + 4 * wpl * (i + 1))).
      zv F_207fc D_207fc (Z_to_bv 64 (datas + 4 * wpl * (i + 1))).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma g3_rowhead : forall regs Mi, (10 <= w)%Z -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x20900 : word) Mi rom) (mkst regs' (0x2092c : word) Mi rom)
      /\ getr regs' 14 = Z_to_bv 64 (8 * 0) /\ regs_agree (fun r : reg => In r [14]%list) regs regs'.
  Proof.
    intros regs Mi Hw10 H13 H15. eexists. split.
    - stepb_ft F_20804 D_20804 ltac:(condZ).
      sn F_20808 D_20808.
      sn F_2080c D_2080c.
      apply mst_refl.
    - split; [gres; pin; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  Lemma g3_rows : forall (k : nat) regs Mi i,
    (10 <= w)%Z -> (0 <= i)%Z -> (Z.of_nat k = h - 1 - i)%Z -> Inv Mi ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 (datas + 4 * wpl * i) -> getr regs 9 = Z_to_bv 64 (datad + 4 * wpl * i) ->
    getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (4 * wpl) -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 w ->
    exists regs' M',
      msteps SEGS (mkst regs (0x20900 : word) Mi rom) (mkst regs' (0x20ad8 : word) M' rom)
      /\ Inv M'
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Hw10 Hi Hk HIv H2 H8 H9 H11 H12 H13 H15;
      set (kk := Z.to_nat ((w - 10) / 8));
      assert (Hkk : (8 * (0 + Z.of_nat kk) + 9 < w <= 8 * (0 + Z.of_nat kk) + 17)%Z)
        by (unfold kk; rewrite Z2Nat.id by (apply Z.div_pos; lia);
            pose proof (Z.div_mod (w - 10) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (w - 10) 8 ltac:(lia)); lia);
      clearbody kk;
      destruct (g3_rowhead regs Mi Hw10 H13 H15) as (r1 & S1 & A14 & AG1);
      pose proof (AG1 2 ltac:(notin_list)) as A2; rewrite H2 in A2;
      pose proof (AG1 8 ltac:(notin_list)) as A8; rewrite H8 in A8;
      pose proof (AG1 9 ltac:(notin_list)) as A9; rewrite H9 in A9;
      destruct (g3_inner kk r1 Mi i 0 ltac:(lia) ltac:(lia) Hkk HIv A2 A8 A9 A14) as (r2 & M2 & S2 & HI2 & B15 & AG2);
      pose proof (AG2 2 ltac:(notin_list)) as B2; rewrite A2 in B2;
      pose proof (AG2 8 ltac:(notin_list)) as B8; rewrite A8 in B8;
      pose proof (AG2 9 ltac:(notin_list)) as B9; rewrite A9 in B9;
      pose proof (AG2 11 ltac:(notin_list)) as B11; rewrite (AG1 11 ltac:(notin_list)), H11 in B11;
      pose proof (AG2 12 ltac:(notin_list)) as B12; rewrite (AG1 12 ltac:(notin_list)), H12 in B12;
      destruct (g3_rowlatch_a r2 M2 i HI2 B2 B8 B9 B11 B12) as (r3 & S3 & C8 & C9 & C11 & C14 & AG3).
    - (* [comment removed for export] *)
      exists r3, M2. split; [|split; [exact HI2|]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_tk F_20800 D_20800 ltac:(condZ).
        apply mst_refl.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3].
    - pose proof (AG3 2 ltac:(notin_list)) as C2; rewrite B2 in C2.
      pose proof (AG3 12 ltac:(notin_list)) as C12; rewrite B12 in C12.
      pose proof (AG3 13 ltac:(notin_list)) as C13; rewrite (AG2 13 ltac:(notin_list)), (AG1 13 ltac:(notin_list)), H13 in C13.
      pose proof (AG3 15 ltac:(notin_list)) as C15; rewrite B15 in C15.
      destruct (IH r3 M2 (i + 1)%Z Hw10 ltac:(lia) ltac:(lia) HI2 C2 C8 C9 C11 C12 C13 C15) as (r4 & M4 & S4 & HI4 & AG4).
      exists r4, M4. split; [|split; [exact HI4|]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_ft F_20800 D_20800 ltac:(condZ).
        exact S4.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|].
        eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4].
  Qed.

  (* [comment removed for export] *)
  Lemma g3_rows_short : forall (k : nat) regs i,
    (w < 10)%Z -> (0 <= i)%Z -> (Z.of_nat k = h - 1 - i)%Z ->
    getr regs 11 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 10 -> getr regs 14 = Z_to_bv 64 h -> getr regs 15 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x20900 : word) M rom) (mkst regs' (0x20ad8 : word) M rom)
      /\ regs_agree (fun r : reg => In r [8; 9; 11]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs i Hw10 Hi Hk H11 H13 H14 H15.
    - eexists. split.
      + stepb_tk F_20804 D_20804 ltac:(condZ).
        zv F_207f4 D_207f4 (Z_to_bv 64 (i + 1)).
        sn F_207f8 D_207f8.
        sn F_207fc D_207fc.
        stepb_tk F_20800 D_20800 ltac:(condZ).
        apply mst_refl.
      + solve_regs_agree.
    - assert (S1 : exists r1, msteps SEGS (mkst regs (0x20900 : word) M rom) (mkst r1 (0x20900 : word) M rom)
                     /\ getr r1 11 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r : reg => In r [8; 9; 11]%list) regs r1).
      { eexists. split; [|split].
        - stepb_tk F_20804 D_20804 ltac:(condZ).
          zv F_207f4 D_207f4 (Z_to_bv 64 (i + 1)).
          sn F_207f8 D_207f8.
          sn F_207fc D_207fc.
          stepb_ft F_20800 D_20800 ltac:(condZ).
          apply mst_refl.
        - gres; pin; reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & A11 & AG1).
      pose proof (AG1 13 ltac:(notin_list)) as A13; rewrite H13 in A13.
      pose proof (AG1 14 ltac:(notin_list)) as A14; rewrite H14 in A14.
      pose proof (AG1 15 ltac:(notin_list)) as A15; rewrite H15 in A15.
      destruct (IH r1 (i + 1)%Z Hw10 ltac:(lia) ltac:(lia) A11 A13 A14 A15) as (r2 & S2 & AG2).
      exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem g3_run : forall regs,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 datas -> getr regs 9 = Z_to_bv 64 datad ->
    getr regs 19 = Z_to_bv 64 pixd -> getr regs 10 = Z_to_bv 64 wpl ->
    exists regs' M',
      msteps SEGS (mkst regs (0x208cc : word) M rom) (mkst regs' (0x20ad8 : word) M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H2 H8 H9 H19 H10.
    destruct (g3_pre regs H2 H8 H9 H19 H10) as (r1 & S1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & AG1).
    destruct (Z_lt_ge_dec w 10) as [Hs|Hl].
    - destruct (g3_rows_short (Z.to_nat (h - 1)) r1 0 Hs ltac:(lia) ltac:(lia) A11 A13 A14 A15) as (r2 & S2 & AG2).
      exists r2, M. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact Inv_M|].
      split; [rewrite (AG2 2 ltac:(notin_list)); exact A2|]. split; [rewrite (AG2 10 ltac:(notin_list)); exact A10|].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - replace (Z_to_bv 64 datas) with (Z_to_bv 64 (datas + 4 * wpl * 0)) in A8 by (f_equal; lia).
      replace (Z_to_bv 64 datad) with (Z_to_bv 64 (datad + 4 * wpl * 0)) in A9 by (f_equal; lia).
      destruct (g3_rows (Z.to_nat (h - 1)) r1 M 0 ltac:(lia) ltac:(lia) ltac:(lia) Inv_M A2 A8 A9 A11 A12 A13 A15) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2]|]. split; [exact HI2|].
      split; [rewrite (AG2 2 ltac:(notin_list)); exact A2|]. split; [rewrite (AG2 10 ltac:(notin_list)); exact A10|].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

End G3.
