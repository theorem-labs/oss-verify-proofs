(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_mem RF_fse_rd_body.
Import ListNotations.
Open Scope Z_scope.

Section Top.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem).
  Variables (SPV NC MSVP TLP BUF : Z) (rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word).
  Hypothesis ARR : u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)).
  Hypothesis HMSV : rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)].
  Hypothesis HTL : rw_cells usegs m TLP [C4 tl0].
  Hypothesis HBUF : bytes_at usegs m BUF (map (Z_to_bv 8) buf).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) buf.
  Hypothesis RN : read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n).
  Hypothesis HM0 : 0 <= msv0 <= 255.
  Hypothesis HLEN : zlen buf <= 65536.
  Hypothesis HNC0 : 0 < NC.
  Hypothesis HNC2 : NC mod 2 = 0.
  Hypothesis HMP0 : 0 < MSVP.
  Hypothesis HMP4 : MSVP mod 4 = 0.
  Hypothesis HTP0 : 0 < TLP.
  Hypothesis HTP4 : TLP mod 4 = 0.
  Hypothesis HBP : 0 < BUF.
  Hypothesis HSLACK : BUF + zlen buf + 8 <= 2^64.
  Hypothesis ST : stk usegs m lo SPV.
  Hypothesis LO : lo <= SPV - FSE_READ_STACK.
  Hypothesis RSP : 0 <= SPV < 2^64.
  Hypothesis SNS : NC + 2 * zlen rt0 <= lo \/ SPV <= NC.
  Hypothesis SMS : MSVP + 4 <= lo \/ SPV <= MSVP.
  Hypothesis STS : TLP + 4 <= lo \/ SPV <= TLP.
  Hypothesis SBS : BUF + zlen buf <= lo \/ SPV <= BUF.
  Hypothesis SNM : NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC.
  Hypothesis SNT : NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC.
  Hypothesis SNB : NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC.
  Hypothesis SMT : MSVP + 4 <= TLP \/ TLP + 4 <= MSVP.
  Hypothesis SMB : MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP.
  Hypothesis STB : TLP + 4 <= BUF \/ BUF + zlen buf <= TLP.
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m).

  Lemma bounds : 0 <= lo /\ (0 <= NC /\ NC + 2 * zlen rt0 <= 2^64) /\ (0 <= MSVP /\ MSVP + 4 <= 2^64) /\ (0 <= TLP /\ TLP + 4 <= 2^64).
  Proof.
    destruct ST as (L0 & _). pose proof (u8arr_bound _ _ _ _ ARR) as B1. rewrite u16s_length, length_map in B1.
    pose proof (rw_cells_bound _ _ _ _ HMSV) as B2. pose proof (rw_cells_bound _ _ _ _ HTL) as B3.
    cbn [cells_size csize Nat.add] in B2, B3. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_top8 : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), 8 <= zlen buf ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x29cc4) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
    destruct bounds as (L0 & BN & BM & BT).
    pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'.
    replace (zlen buf <? 8) with false in RN' by (symmetry; apply Z.ltb_ge; lia).
    destruct (read_body8_inv buf (msv0 + 1) rt0 rt msv tl n H8 RN') as (HL & _).
    set (C := mkRD ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF lo rt0 buf msv0).
    assert (OK : rd_ok C).
    { unfold rd_ok, RD_STACK, FSE_READ_STACK in *. cbn. repeat split; try assumption; try lia. }
    eapply evt_mono.
    - exact (rd_body8 C OK rt msv tl n tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RN').
    - intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & ST' & A' & M' & T').
      unfold fse_read_post. do 14 eexists. exists m'. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, rd_W, RD_STACK, FSE_READ_STACK. subst C. cbn [outside c_NC c_rt0 c_MSVP c_TLP c_SP]. intros x; lia. }
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact A'|]. split; [exact M'| exact T'].
  Qed.
  Lemma pad_tail : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
  Proof. intros z k Hk. do 9 (destruct k as [|k]; [reflexivity|]). lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_top_small : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), zlen buf < 8 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
               (Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x29cc4) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
    destruct bounds as (L0 & BN & BM & BT). unfold FSE_READ_STACK in *.
    set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
    set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
    assert (RB : read_ncount_body8 buf' (msv0 + 1) rt0 = Ok (rt, msv, tl, n) /\ n <= hb).
    { pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'. fold hb in RN'.
      replace (hb <? 8) with true in RN' by (symmetry; apply Z.ltb_lt; lia). fold buf' in RN'.
      destruct (read_ncount_body8 buf' (msv0 + 1) rt0) as [[[[nc1 msv1'] tl1] cs]| | |]; cbn [bind] in RN'; try discriminate RN'.
      destruct (Z.ltb_spec hb cs); [discriminate RN'|]. injection RN' as <- <- <- <-. split; [reflexivity| lia]. }
    destruct RB as [RB NLE].
    assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; lia).
    destruct (read_body8_inv buf' (msv0 + 1) rt0 rt msv tl n ltac:(lia) RB) as (HL & _).
    pose proof (munch_refl [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - 256, SPV)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    assert (LWS : length (map (Z_to_bv 64) rt0) = length rt0) by apply length_map.
    assert (LBS : zlen (map (Z_to_bv 8) buf) = hb) by (rewrite length_map; reflexivity).
    carve_frame 128%nat ST.
    do 14 zstep.
    zstep. zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
    zstep. zstep. zstep.
    zstep. replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia).
    zstep. replace (BUF + hb <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. zstep. if_false.
    zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
    zstep. replace (Z.land MSVP 3) with 0
      by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 16 ?j :: ?rest) =>
      change (CB 16 j :: rest) with ([CB 16 j] ++ rest) in FR end.
    apply rd_rw_cells_app in FR. destruct FR as [J16 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) in FR by lia.
    (* [comment removed for export] *)
    pose proof (rw_cells_merge usegs _ (SPV + -112) [] [C8 (Z_to_bv 64 0)]
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
    cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FR.
    change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
    pose proof (rw_cells_split_CB usegs _ (SPV + -112) [] 8 (repeat (Z_to_bv 8 0) 8)
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                  [hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
    cbn [app mk_CB_cells] in FS. clear FM. rewrite (pad_tail (Z_to_bv 8 0) hbn) in FS by lia.
    change (CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)) :: CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn)) ::
            [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ ([CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] ++
            [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FS.
    apply rd_rw_cells_app in FS. destruct FS as [R1 FS]. apply rd_rw_cells_app in FS. destruct FS as [R2 R3].
    cbn [cells_size csize Nat.add] in R2, R3.
    replace (SPV + -112 + Z.of_nat (hbn + 0)) with (SPV + -112 + hb) in R2, R3 by lia.
    replace (SPV + -112 + hb + Z.of_nat (8 - hbn + 0)) with (SPV + -104) in R3 by lia.
    call (rd_memcpy_specZ (SPV + -112) BUF hb); [exact HBUF | rewrite length_map; unfold hb; lia | exact R1 | lia | eassumption
          | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    (* [comment removed for export] *)
    assert (FB' : Forall (fun c => 0 <= c < 256) buf').
    { subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RB8 : rw_cells usegs mm (SPV + -112) [CB 8 (map (Z_to_bv 8) buf')]) end.
    { replace (SPV + -112 + hb) with (SPV + -112 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
        by (cbn [cells_size csize Nat.add]; lia).
      lazymatch goal with P : rw_cells usegs ?mm (SPV + -112) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ =>
        pose proof (proj2 (rd_rw_cells_app usegs mm (SPV + -112) [CB hbn (map (Z_to_bv 8) buf)]
                            [CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj P R2)) as RJ;
        pose proof (rw_cells_merge usegs mm (SPV + -112) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RM
      end.
      cbn [app cells_size cells_bytes csize cbytes Nat.add] in RM. rewrite app_nil_r in RM.
      replace (hbn + (8 - hbn + 0))%nat with 8%nat in RM by lia.
      subst buf'. rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RM. }
    clear R2.
    do 7 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      set (C' := mkRD (Z_to_bv 64 171372) gp tp (Z_to_bv 64 hb) (Z_to_bv 64 MSVP) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) s4
                      (Z_to_bv 64 (BUF + hb)) s6 s7 s8 s9 s10 s11 F fc mm (SPV + -128) NC MSVP TLP (SPV + -112) lo rt0 buf' msv0) end.
    assert (OK' : rd_ok C').
    { unfold rd_ok, RD_STACK. subst C'. cbn [c_buf c_msv0 c_rt0 c_SP c_lo c_NC c_BUF c_MSVP c_TLP]. rewrite LB'.
      repeat split; try assumption; try lia. }
    assert (HBUF' : bytes_at usegs (c_m C') (c_BUF C') (map (Z_to_bv 8) (c_buf C'))).
    { subst C'. cbn [c_m c_BUF c_buf]. destruct RB8 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
    replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen (c_buf C'))) by (subst C'; cbn [c_buf]; rewrite LB'; reflexivity).
    eapply evt_cut.
    { eapply (rd_body8 C' OK' rt msv tl n tl0); subst C'; cbn [c_m c_NC c_rt0 c_MSVP c_msv0 c_TLP c_BUF c_buf c_lo c_SP];
        try eassumption. }
    intros ms' PO. hnf in PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ARR' & HMSV' & HTL').
    unfold rd_W, RD_STACK in MU'. subst C'.
    cbn [c_ra c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m c_SP c_NC c_MSVP c_TLP c_BUF c_lo c_rt0 c_buf c_msv0] in *.
    clear ARR HMSV HTL HBUF'.
    lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call usegs ma mb MU' WM'; clear MU' WM'; try clear ma end.
    replace (ret_pc (Z_to_bv 64 171372)) with (Z_to_bv 64 171372) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (N1 : 1 <= n).
    { destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; lia)
                  ltac:(unfold FseNCount.Zlength; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & N2 & _) | (e & E2)];
        rewrite RB in E2; [injection E2 as <- <- <- <-; lia| discriminate E2]. }
    zstep. zstep. replace (hb <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    zstep. rewrite Z.land_0_r.
    zstep. if_true.
    (* [comment removed for export] *)
    assert (FR : exists mm, True) by (exists m; exact I). clear FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of J16 with rw_cells _ _ _ [CB 16 ?j] =>
      assert (FR : rw_cells usegs mm (SPV + -128)
                     [CB 16 j; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      end
    end.
    { match goal with |- rw_cells _ _ _ (?c :: ?rest) => change (c :: rest) with ([c] ++ rest) end.
      apply rd_rw_cells_app. split; [exact J16|]. cbn [cells_size csize Nat.add].
      replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
      change [CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
    clear RB8 R3 J16.
    do 13 zstep. zstep. zstep.
    release_frame FR ST' SPV.
    apply evt_done. unfold fse_read_post, FSE_READ_STACK.
    do 14 eexists. eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
  Qed.
End Top.

(* [comment removed for export] *)
Theorem fse_read_proof : fse_read_stmt.
Proof.
  unfold fse_read_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF
         rt0 rt buf msv0 msv tl n lo tl0
         ARR HMSV HTL HBUF FBY RN HM0 HLEN HNC0 HNC2 HMP0 HMP4 HTP0 HTP4 HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI -> -> -> -> ->.
  unfold PFSE_READ.
  zstep. zstep.
  destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
  - eapply (rd_top_small ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 rt buf msv0 msv tl n lo tl0); eassumption.
  - eapply (rd_top8 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 rt buf msv0 msv tl n lo tl0); eassumption.
Qed.
