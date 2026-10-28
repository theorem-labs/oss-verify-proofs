(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_prod_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
(* [comment removed for export] *)
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

Section U32R.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (RNG : footprint) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis PNZ : 0 < P.
  Hypothesis PAL : P mod 8 = 0.
  Hypothesis DNZ : 0 < D.
  Hypothesis ST : stk bsegs m lo SP.
  Hypothesis LO : lo <= SP - 16.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis SP47 : SP < 2^47.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis ARP : areg RNG m P 16.
  Hypothesis ARD : aro RNG m D (zlen pl).
  Hypothesis ART : art m.
  Hypothesis AST : astk RNG lo SP.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis MM : 0 <= mn <= mx.
  Hypothesis MX : mx < 2^31.

  Notation W := [(P + 8, P + 16); (SP - 16, SP)].
  Notation POST := (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).
  Notation range := (mx - mn).

  Definition INV (m1 : amem) (sz : Z) : Prop :=
    rw_cells bsegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
    /\ bytes_at bsegs m1 D (map (Z_to_bv 8) pl)
    /\ (exists junk8, rw_cells bsegs m1 (SP + -16) [CB 8 junk8; C8 ra])
    /\ stk bsegs m1 lo (SP + -16)
    /\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
    split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].

  Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

  Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
  Proof. intros [|f] sz result; reflexivity. Qed.

  Lemma wrap32_zsx32 : forall v, 0 <= v < 4294967296 -> bv_wrap 32 (zsx32 v) = v.
  Proof.
    intros v Hv. rewrite wrap32_eq. unfold zsx32. destruct (v <? 2147483648); [apply Z.mod_small; lia|].
    replace (v + 18446744069414584320) with (v + 4294967295 * 4294967296) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  Lemma pl_nth : forall i, 0 <= i < zlen pl ->
    nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
  Proof.
    intros i Hi. destruct PL as [_ PLR]. unfold Znth.
    assert (L : (Z.to_nat i < length pl)%nat) by lia.
    split.
    - rewrite nth_error_map. rewrite (nth_error_nth' pl 0 L). reflexivity.
    - apply (proj1 (Forall_forall _ _) PLR). apply nth_In. exact L.
  Qed.

  (* [comment removed for export] *)
  Notation SHB := 2147450880.
  Notation STpc pc mm x6 x12 x14 x28 x29 x30 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 (-1)) x6 (Z_to_bv 64 (SHB + P / 8)) s0 s1
             (Z_to_bv 64 P) (Z_to_bv 64 mn) x12 (Z_to_bv 64 (P + 8)) x14 (Z_to_bv 64 range) (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + (P + 8) / 8))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STtl mm x5 x6 x7 x10 x12 x13 x14 x16 x17 x28 x29 x30 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1
             x10 (Z_to_bv 64 mn) x12 x13 x14 (Z_to_bv 64 range) x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 0xb0208) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma u32r_tail : forall m1 result sz (x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 : word),
    0 <= result < 2^32 -> INV m1 sz ->
    (result, sz) = draw_loop 4 pl size range 0 ->
    evtF bsegs RNG POST (STtl m1 x5 x6 x7 x10 (Z_to_bv 64 (zsx32 result)) x13 x14 x16 x17 x28 x29 x30).
  Proof.
    intros m1 result sz x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
    change (2^32) with 4294967296 in RR. change (2^31) with 2147483648 in MX.
    pose proof (zsx32_range result RR) as RZ.
    destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
    zstep. zstep. unfold v_remuw. zsimp.
    rewrite (wrap32_small (range + 1)) by lia. rewrite (wrap32_zsx32 result) by lia.
    replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
    rewrite swrap32_small by lia.
    zstep. rewrite swrap32_small by lia.
    zstep. zstep. zstep.
    release_frame FR1 ST1 SP.
    zstep.
    apply evtF_done. unfold prod_u32r_postA, uint32Range.
    rewrite (u32_id range) by (change (2^32) with 4294967296; lia). rewrite <- DL.
    replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; change (2^32) with 4294967296; lia).
    cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by (change (2^32) with 4294967296; lia).
    replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
    do 14 eexists. exists m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
  Qed.

  (* [comment removed for export] *)
  Lemma u32r_loop : forall f sz rolling result m1 (x14 x29 x30 : word),
    0 < rolling < 2^(8 * Z.of_nat f) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
    0 <= sz <= zlen pl -> INV m1 sz ->
    (forall m2 (y5 y6 y7 y10 y13 y14 y16 y17 y28 y29 y30 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
       0 <= fst (draw_loop f pl sz rolling result) < 2^32 ->
       evtF bsegs RNG POST (STtl m2 y5 y6 y7 y10 (Z_to_bv 64 (zsx32 (fst (draw_loop f pl sz rolling result)))) y13 y14 y16 y17 y28 y29 y30)) ->
    evtF bsegs RNG POST (STpc 0xb019c m1 (Z_to_bv 64 (sz + -1)) (Z_to_bv 64 result) x14 (Z_to_bv 64 rolling) x29 x30).
  Proof.
    induction f as [|f IH]; intros sz rolling result m1 x14 x29 x30 RO RE F4 SZ1 (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
    { exfalso. cbn in RO. lia. }
    pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    assert (P8 : 2^(8 * Z.of_nat (S f)) = 256 * 2^(8 * Z.of_nat f)).
    { replace (8 * Z.of_nat (S f)) with (8 + 8 * Z.of_nat f) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
    { replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
    assert (P32 : 2^(8 * Z.of_nat (S f)) <= 2^32) by (apply Z.pow_le_mono_r; lia).
    assert (P0 : 0 < 2^(8 * Z.of_nat f)) by (apply Z.pow_pos_nonneg; lia).
    assert (Q0 : 0 < 2^(32 - 8 * Z.of_nat (S f))) by (apply Z.pow_pos_nonneg; lia).
    cbn [draw_loop] in K. change (2^8) with 256 in K.
    replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
    change (2^24) with 16777216 in Q24. change (2^32) with 4294967296 in *.
    destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
    destruct (ARP ltac:(lia)) as (ABP & UP & RP & RPS). destruct ARD as (UD & RD & RDS).
    pose proof (ablk_lin _ _ ABP) as PLIN. unfold AIMG_HI in PLIN.
    assert (PA : P + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in ABP; lia).
    zstep. if_cases B; zify_cond B.
    - (* [comment removed for export] *)
      assert (sz = 0) by (Z.div_mod_to_equations; lia). subst sz.
      replace (0 <? 0) with false in K by reflexivity. cbn [fst snd] in K.
      rewrite (zsx32_small result) in K by lia.
      zstep. zstep. if_cases B1; zify_cond B1; [| exfalso; lia].
      apply K; [| lia].
      inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
    - assert (SZP : 0 < sz) by (Z.div_mod_to_equations; lia).
      replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
      destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
      (* [comment removed for export] *)
      assert (B1 : bytes_at bsegs m1 (D + (sz + -1)) [Z_to_bv 8 (Znth (sz - 1) pl)]).
      { destruct PL1 as (H0 & H1 & H). rewrite length_map in H1. split; [lia|]. split; [cbn; lia|].
        intros i Hi. cbn [length] in Hi. replace (D + (sz + -1) + Z.of_nat i) with (D + Z.of_nat (Z.to_nat (sz - 1))) by lia.
        rewrite H by (rewrite length_map; lia). destruct i as [|i]; [| lia]. cbn [nth_error]. exact NTH. }
      unp_now UP MU1 UP1. unp_now UD MU1 UD1.
      (* [comment removed for export] *)
      kx_autoFLAx [KAUnp P 16; KAApp P 16; KAShp (SHB + P / 8) P; KAShp (SHB + (P + 8) / 8) (P + 8); KAUnp (D + (sz + -1)) 1]
        [0xb01cc] 40%nat
        [KZRange P 4096 (2^47); KZAlign P 8; KZRange D 1 (2^47); KZRange sz 1 (2^47); KZRange (D + sz) 2 (2^47);
         KZWord (D + (sz + -1)) 1 (Znth (sz - 1) pl); KZRange (Znth (sz - 1) pl) 0 255]
        [(P, 16); (D + (sz + -1), 1)] [(P, 16); (D + (sz + -1), 1)].
      all: try kx_cell_lit. all: try kx_acc RI. all: try (rdb1 B1).
      all: kx_mem.
      (* [comment removed for export] *)
      zstep.
      zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
      assert (SWZ : Z_to_bv 64 (bv_swrap 32 (result * 256)) = Z_to_bv 64 (zsx32 (result * 256))).
      { apply Z_to_bv_eqm. rewrite swrap32_eq. unfold zsx32. destruct (Z.ltb_spec (result * 256) 2147483648) as [L|L].
        - rewrite Z.mod_small by lia. f_equal. lia.
        - replace ((result * 256 + 2147483648) mod 4294967296) with (result * 256 - 2147483648)
            by (apply (Z.mod_unique _ _ 1); lia).
          change (2^64) with 18446744073709551616.
          replace (result * 256 + 18446744069414584320) with (result * 256 - 2147483648 - 2147483648 + 1 * 18446744073709551616) by lia.
          rewrite Z.mod_add by lia. reflexivity. }
      rewrite SWZ. clear SWZ.
      pose proof (zsx32_range (result * 256) ltac:(lia)) as RZS.
      zstep. rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
      assert (RD8 : 0 <= rolling / 256 < 2^(8 * Z.of_nat f)).
      { split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
      rewrite swrap32_small by lia.
      set (bt := Znth (sz - 1) pl) in *.
      zstep.
      assert (LORZ : Z.lor (zsx32 (result * 256)) bt = zsx32 (result * 256 + bt)).
      { rewrite (lor_add_disj 8); [ | lia | change (2^8) with 256; lia | ].
        - unfold zsx32. destruct (Z.ltb_spec (result * 256) 2147483648) as [L|L]; destruct (Z.ltb_spec (result * 256 + bt) 2147483648) as [L2|L2]; lia.
        - change (2^8) with 256. unfold zsx32. destruct (result * 256 <? 2147483648); [apply Z_mod_mult|].
          replace (result * 256 + 18446744069414584320) with ((result + 72057594021150720) * 256) by lia. apply Z_mod_mult. }
      rewrite LORZ. clear LORZ.
      rewrite (u32_id (result * 256)) in K by (change (2^32) with 4294967296; lia).
      assert (LOR : Z.lor (result * 256) bt = result * 256 + bt) by (apply (lor_byte result); lia).
      rewrite LOR in K.
      zstep. zstep.
      if_cases B2; zify_cond B2.
      + (* [comment removed for export] *)
        assert (F1 : (1 <= f)%nat). { destruct f; [exfalso; cbn in RD8; lia| lia]. }
        assert (Q24' : 2^(32 - 8 * Z.of_nat f) <= 2^24) by (apply Z.pow_le_mono_r; lia).
        change (2^24) with 16777216 in Q24'.
        rewrite (zsx32_small (result * 256 + bt)) by lia.
        replace (sz + -2) with ((sz - 1) + -1) by lia.
        eapply (IH (sz - 1) (rolling / 256) (result * 256 + bt)); try lia.
        * replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 KXMI.
        * exact K.
      + (* [comment removed for export] *)
        assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K. cbn [fst snd] in K.
        zstep. zstep. zstep. if_cases B3; zify_cond B3; [| exfalso; lia].
        apply K; [| lia].
        replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 KXMI.
  Qed.

  Lemma u32r_body : evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_U32R) fc None m (seg_rom bsegs)).
  Proof.
    pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    change (2^31) with 2147483648 in MX.
    destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
    destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
    destruct (ARP ltac:(lia)) as (ABP & UP & RP & RPS). destruct ARD as (UD & RD & RDS).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    carve_frame 16%nat ST.
    pose proof (rw_cells_bound _ _ _ _ PR0) as PB. cbn [cells_size csize Nat.add] in PB.
    pose proof (ablk_lin _ _ ABP) as PLIN. unfold AIMG_HI in PLIN.
    assert (PA : P + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in ABP; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    zstep. rewrite swrap32_small by lia. zstep.
    if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep.
      eapply (u32r_tail _ 0 size); [change (2^32) with 4294967296; lia| | ].
      + inv_close PR0 PLB FR ST MU WM MI.
      + rewrite K2. reflexivity.
    - assert (K2' : 0 < range) by (Z.div_mod_to_equations; lia).
      unp_now UP MU UP0.
      (* [comment removed for export] *)
      kx_autoFLAx [KAUnp P 16; KAApp P 16] [0xb019c] 40%nat
        [KZRange P 4096 (2^47); KZAlign P 8]
        [(P, 16)] [(P, 16)].
      all: try kx_cell_lit. all: try kx_acc RI.
      all: kx_mem.
      replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      replace (P mod 2 ^ 64 / 8 + 2147450880) with (2147450880 + P / 8) by (rewrite Z.mod_small by lia; lia).
      replace ((P + 8) mod 2 ^ 64 / 8 + 2147450880) with (2147450880 + (P + 8) / 8) by (rewrite Z.mod_small by lia; lia).
      replace (-1 * mn + mx) with range by lia.
      eapply (u32r_loop 4 size range 0);
        [ change (2^(8 * Z.of_nat 4)) with 4294967296; lia | cbn; lia | lia | lia | | ].
      + inv_close PR0 PLB FR ST MU WM KXMI.
      + intros m2 y5 y6 y7 y10 y13 y14 y16 y17 y28 y29 y30 I2 R2.
        eapply u32r_tail; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
  Qed.
End U32R.

Lemma zd_u32r_proofA : zd_u32r_stmtA.
Proof.
  intros until lo. intros PR PL SZ PNZ PAL DNZ ST LO RSP PLO DLO DP ARP ARD ART AST SP47 MI MM MX -> -> ->.
  eapply u32r_body; eassumption.
Qed.
End CANSEC1.
