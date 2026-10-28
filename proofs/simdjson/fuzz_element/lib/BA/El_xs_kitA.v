(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA El_xs_adaptA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Definition fpcellsA (F : bvmap 5 word) : list cell := map (fun i => C8 (reg_get F (Z_to_bv 5 (Z.of_nat i)))) (seq 0 32).

Section FPBLK.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Notation R := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation A := (bv_unsigned a0).

  Lemma getctx_fsd_walkA : forall junk,
    rw_cells asegs m (A + 256) [CB 256 junk] -> mem_inv asegs m -> (A + 512 <= 2 ^ 64)%Z ->
    evt asegs (fun ms' => exists m',
        ms' = MS R F (Z_to_bv 64 (XS_FSD_A + 128)) fc None m' (seg_rom asegs)
        /\ munch [(A + 256, A + 512)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (A + 256) (fpcellsA F))
      (MS R F (Z_to_bv 64 XS_FSD_A) fc None m (seg_rom asegs)).
  Proof.
    intros junk DST MI HB. unfold XS_FSD_A.
    pose proof (munch_refl [(A + 256, A + 512)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 32 zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact DST.
  Qed.

  Lemma jumpto_fld_walkA : forall ws : list word, length ws = 32%nat ->
    ro_cells asegs m (A + 256) (map (fun w => C8 w) ws) -> (A + 512 <= 2 ^ 64)%Z ->
    evt asegs (fun ms' => exists F', ms' = MS R F' (Z_to_bv 64 (XS_FLD_A + 128)) fc None m (seg_rom asegs))
      (MS R F (Z_to_bv 64 XS_FLD_A) fc None m (seg_rom asegs)).
  Proof.
    intros ws Hlen SRC HB. unfold XS_FLD_A.
    destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|w22 [|w23 [|w24 [|w25 [|w26 [|w27 [|w28 [|w29 [|w30 [|w31 [|w32 ws]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      cbn in Hlen; try discriminate.
    cbn [map] in SRC.
    do 32 zstep.
    apply evt_done. eexists. reflexivity.
  Qed.
End FPBLK.

Lemma cb8_lengthA : forall (g : nat -> word) n k, length (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = (8 * n)%nat.
Proof.
  intros g n. induction n as [|n IH]; intros k; [reflexivity|]. cbn [seq map cells_bytes cbytes]. rewrite length_app, IH. rewrite Mem.length_le8. lia.
Qed.
Lemma cb8_firstA : forall (g : nat -> word) n k, (0 < n)%nat -> firstn 8 (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = le8 (g k).
Proof.
  intros g n k Hn. destruct n as [|n]; [lia|]. cbn [seq map cells_bytes cbytes].
  rewrite firstn_app. rewrite Mem.length_le8. replace (8 - 8)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. rewrite Mem.length_le8. lia.
Qed.
Lemma cb8_skipA : forall (g : nat -> word) i n k, (i <= n)%nat ->
  skipn (8 * i) (cells_bytes (map (fun j => C8 (g j)) (seq k n))) = cells_bytes (map (fun j => C8 (g j)) (seq (k + i) (n - i))).
Proof.
  intros g i. induction i as [|i IH]; intros n k Hi.
  - rewrite Nat.mul_0_r, Nat.add_0_r, Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [seq map cells_bytes cbytes]. replace (8 * S i)%nat with (8 + 8 * i)%nat by lia.
    rewrite skipn_app. rewrite Mem.length_le8. replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia.
    rewrite skipn_all2 by (rewrite Mem.length_le8; lia). cbn [app].
    replace (k + S i)%nat with (S k + i)%nat by lia. apply IH. lia.
Qed.
Lemma fpcells_readA : forall m A F i, (i < 32)%nat ->
  cells_at asegs m A (fpcellsA F) -> rdn asegs m (Z_to_bv 64 (A + 8 * Z.of_nat i)) 8 = Some (fle8 F i).
Proof.
  intros m A F i Hi [WF BA].
  pose proof (Mem.bytes_at_rdn asegs m A _ (8 * i) 8 BA) as X. unfold fpcellsA in X. rewrite cb8_lengthA in X. specialize (X ltac:(lia)).
  rewrite rdn_common in X. unfold wa in X. replace (A + Z.of_nat (8 * i)) with (A + 8 * Z.of_nat i) in X by lia. rewrite X. f_equal.
  rewrite cb8_skipA by lia. rewrite cb8_firstA by lia. unfold fle8, Mem.le8. rewrite Nat.add_0_l. reflexivity.
Qed.

Lemma fsd_contract_A : fsdA_contract XS_FSD_A.
Proof.
  unfold fsdA_contract, fsd_contract. intros R F fc m junk HFR RWC HB MI.
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (_ & G10 & _ & _).
  rewrite G10 in RWC, HB. replace (reg_get (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 10)) with x10 by (symmetry; exact G10).
  eapply evt_mono; [apply (getctx_fsd_walkA x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m junk RWC MI HB)|].
  intros ms' (m' & -> & MU & WM & MI' & RW'). exists m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  intros i Hi. replace (bv_unsigned x10 + 256 + 8 * Z.of_nat i) with ((bv_unsigned x10 + 256) + 8 * Z.of_nat i) by lia.
  apply fpcells_readA; [exact Hi|]. exact (proj1 RW').
Qed.

Lemma fld_contract_A : fldA_contract XS_FLD_A.
Proof.
  unfold fldA_contract. intros R F fc m ws HFR Hlen HB CS.
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (_ & G10 & _ & _).
  rewrite G10 in HB, CS. replace (reg_get (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 10)) with x10 by (symmetry; exact G10).
  exact (jumpto_fld_walkA x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ws Hlen CS HB).
Qed.

Lemma wf_xs_WA : forall FSZ, wf_W (xs_WA FSZ) = true. Proof. reflexivity. Qed.
Lemma wf_xs_CWA : wf_W xs_CWA = true. Proof. reflexivity. Qed.

Section KitA.
  Variable RT : rt_sig.
  Variable WIN : rt_win RT.
  Variable c : Z.

  Definition RTX : rt_sig := rt_sigW RT (ARTW RT WIN c).
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variable Σ : rts RT.

  Hypothesis TLS : tls_icG RTX TPV_XA XS_TLS_A.
  Hypothesis XROW : forall Σ0 (m : word -> option byte), ARTW RT WIN c Σ0 m -> el_xroA m.
  Variables (FSZ lo : Z) (IT : itab).
  Hypothesis ITS : itab_sound asegs IT.

  Lemma KRO_A : forall E (m : word -> option byte), ART RTX Σ m -> mem_inv asegs m -> know_ok asegs E m kn_xroA.
  Proof.
    intros E m HA MI. unfold kn_xroA. apply kn_lits_ok. pose proof (XROW Σ m HA) as X. unfold el_xroA in X. rewrite Forall_forall in X |- *.
    intros p Hp. split; [exact (X p Hp)|]. unfold el_xro_wordsA in Hp. cbn in Hp.
    repeat (destruct Hp as [<-|Hp]; [cbn; lia|]). destruct Hp.
  Qed.

  Theorem xautoXA_sound : forall fc fuel k ss ss' E m0 base ms,
    xautoXA FSZ IT XS_END_A fuel k ss = Some ss' ->
    CIXA RTX Σ (xs_WA FSZ) xs_CWA lo XS_SPLO FSZ fc E m0 base ss ms ->
    nodeA_ok RTX PMc Σ (xs_WA FSZ) xs_CWA lo XS_SPLO FSZ fc ss ss' E m0 base ms.
  Proof.
    intros fc fuel k ss ss' E m0 base ms HX HC. unfold xautoXA in HX.
    refine (xautoA_sound RTX PMc FDO MST (w_facts RT WIN c) Σ IT ITS TPV_XA XS_SET_A XS_CPY_A XS_TLS_A XS_UNW_A XS_UNWREAL_A XS_FSD_A XS_FLD_A
              (xs_WA FSZ) xs_CWA kn_xroA lo XS_SPLO FSZ XS_ROTOP_A (wf_xs_WA FSZ) ltac:(left; reflexivity) KRO_A bsegs_ro
              (rc_memset RTX (w_rc RT WIN c)) (rc_memcpy RTX (w_rc RT WIN c)) TLS _ fsd_contract_A fld_contract_A fc XS_END_A fuel k ss ss' E m0 base ms HX HC).

    exact (w_unwind RT WIN c).
  Qed.
End KitA.
