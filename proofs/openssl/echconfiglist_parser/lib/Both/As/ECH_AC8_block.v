(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C8 ECH_AKit ECH_AsKit ECH_AsKitK ECH_AC8_small ECH_AC8_blockA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition DB_T1 : Z := 0x422790.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox H := unfold boxed in H.

Section TOP.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Definition ctx_chunk (nn : Z) (raw : list byte) (line : Z) : list cell := [C4 (wz nn); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]].
  (* [comment removed for export] *)
  Definition adb_frame (j8 : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Local Ltac reacc ACC' MU :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let ACC := fresh "ACC" in
      lazymatch type of ACC' with id (accessible _ ?a0 ?n0) =>
        assert (ACC : accessible mx a0 n0) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
          apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]) end end.

  (* [comment removed for export] *)
  Lemma tab_in_aglobals : In (A_data_ascii2bin, 128, 128) aglobals.
  Proof. unfold aglobals, A_data_ascii2bin. cbv. repeat (first [left; reflexivity| right]). Qed.
  Lemma tab_accessible : forall m, ACONST m -> accessible m A_data_ascii2bin 128.
  Proof.
    intros m AC. acb. eapply addressable_accessible; [eapply (ACONST_global_addressable m A_data_ascii2bin 128 128 AC tab_in_aglobals); lia| lia| lia|].
    unfold A_data_ascii2bin, AAPP_HI. lia.
  Qed.
End TOP.
Section P1.
  Context {HCEIL : HeapCeil}.
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Local Ltac reacc ACC' MU :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let ACC := fresh "ACC" in
      lazymatch type of ACC' with id (accessible _ ?a0 ?n0) =>
        assert (ACC : accessible mx a0 n0) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
          apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]) end end.

  (* [comment removed for export] *)
  Lemma adb_p1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
      0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j8 (x15 x17 : word),
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (a + 88)) a1 a2 a3 a4
                       x15 (Z_to_bv 64 ASHADOW_BASE) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x4226dc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64) /\ rw_cells asegs m1 (bv_unsigned sp + -64) (adb_frame j8 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros POS AL BL CEIL ACC0 AC ST LO MI. unfold P_evp_decodeblock_int.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB. rewrite ASHADOW_BASE_val.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 92)) in ACC'.
    carve_frame 64%nat ST.
    do 12 step.
    step. fbr.
    step. ubal_by AL. step. if_lit.
    reacc ACC' MU. zstep. zstep. zstep. ck4_load ACC (a + 88) v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). finish. unfold adb_frame. exact FR.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      step. step. step. if_true_by (ck4_blt_true (a + 88) v Ha V1 VV). finish. unfold adb_frame. exact FR.
  Qed.
End P1.
(* [comment removed for export] *)
Ltac ck1f_load ACC x :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let Hx := fresh "Hx" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc (x - x mod 8) 8) by (eapply accessible_sub; [exact ACC| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia]) end;
  assert (Hx : 0 <= x) by lia;
  pose proof (accessible_read8 _ _ ACW) as RD;
  replace (sh (x - x mod 8)) with (sh x) in RD by (unfold sh; Z.div_mod_to_equations; nia);
  rewrite <- (sh_shiftr x), ASHADOW_BASE_val in RD by exact Hx;
  replace (wa (Z.shiftr x 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr x 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW Hx; rewrite ?ck8_zxb0, ?ck8_sxb0.
Ltac ck1f_check ACC x := ck1f_load ACC x; step; if_false_by (ck1_bnez_false 0 eq_refl).

Section P2.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].

  Local Ltac stepto P := repeat (tryif at_pc P then fail else step).
  Local Ltac nsx32 x := replace (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32) with x by
    (rewrite (unsigned_lit x) by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by lia; rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_mul by lia; reflexivity).
  Local Ltac b2z_in K := repeat match type of K with context [Z.b2z (?x <? ?y)] =>
      first [rewrite (proj2 (Z.ltb_lt x y) ltac:(lia)) in K | rewrite (proj2 (Z.ltb_ge x y) ltac:(lia)) in K]; cbn [Z.b2z] in K end.
  Local Ltac ubnc := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; b2z_in K; vm_compute in K; congruence | clear K].
  (* [comment removed for export] *)
  Lemma adb_p2 :
    forall (ra spw gp tp t0 t1 t2 s0 s1 a1 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a n nn line : Z) (raw : list byte),
      rw_cells asegs m a (ctx_chunk nn raw line) -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> accessible m a 92 -> ACONST m ->
      0 < n <= 64 -> Forall b64_saved (map bv_unsigned (firstn (Z.to_nat n) raw)) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (x7 x9 x13 x15 x28 x29 x30 x31 : word),
          ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 n) x7 s0 x9 (Z_to_bv 64 (a + 4)) a1 (Z_to_bv 64 (Z.land n 3)) x13 a4 x15
                       (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 DB_J) fc None m (seg_rom asegs))
        (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (a + 88)) a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) a4 a5 (Z_to_bv 64 ASHADOW_BASE) a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x4226dc) fc None m (seg_rom asegs)).
  Proof.
    intros until raw. intros CTX POS AL BL ACC AC NR SAVED MI. unfold DB_J, A_data_ascii2bin. rewrite ASHADOW_BASE_val.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    assert (L80 : length raw = 80%nat) by (destruct CTX as [[WF _] _]; cbn in WF; tauto).
    acb. pose proof (tab_accessible _ AC) as TACC. unfold A_data_ascii2bin in TACC.
    pose proof (ctx_raw _ _ _ _ _ _ CTX) as RAW. unfold ctx_chunk, wz in CTX.
    (* [comment removed for export] *)
    step. step. step. if_lit.
    step. step. step. step. step. fbr.
    step. step. step. step. step. step. fbr.
    (* [comment removed for export] *)
    step. step. step. zsimp. ck1f_load ACC (a + 4). step. if_lit.
    destruct (nth_error raw (Z.to_nat 0)) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    pose proof (saved_nth n raw 0 c0 SAVED N0 ltac:(lia)) as S0. pose proof (b64_saved_lt64 _ S0) as V0. destruct S0 as [B0 _]. pose proof (byte_range c0).
    box CTX. pose proof (rd_raw _ _ _ 0 c0 RAW N0 ltac:(lia)) as RD. replace (a + 4 + 0) with (a + 4) in RD by lia. step. clear RD. rewrite (sxb_small c0) by lia.
    step. fbr.
    repeat step. fbr.
    repeat step. zsimp. ck1f_load TACC (790304 + bv_unsigned c0). step. if_lit.
    pose proof (rd_tab _ (bv_unsigned c0) MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD. unfold wz.
    step. tbr.
    (* [comment removed for export] *)
    repeat step. if_cases KS3; zify_cond KS3; rewrite ?signed_lit in KS3 by lia.
    - (* [comment removed for export] *)
      repeat step. tbr. step. stepto DB_J. unbox CTX. rewrite (unsigned_lit n) by lia. finish.
    - (* [comment removed for export] *)
      repeat step. if_cases KN4; zify_cond KN4; rewrite ?signed_lit in KN4 by lia.
      + assert (E3 : n = 3) by lia. subst n. stepto DB_J. unbox CTX. finish.
      + nsx32 n. repeat step. fbr. repeat step. ubnc. repeat step. fbr. repeat step.
        zsimp. ck1f_load ACC (a + 4 + n + -1). step. if_lit.
        destruct (nth_error raw (Z.to_nat (n - 1))) as [cl|] eqn:NL; [| apply nth_error_None in NL; lia].
        pose proof (saved_nth n raw (n - 1) cl SAVED NL ltac:(lia)) as SL. pose proof (b64_saved_lt64 _ SL) as VL. destruct SL as [BL1 _]. pose proof (byte_range cl).
        pose proof (rd_raw _ _ _ (n - 1) cl RAW NL ltac:(lia)) as RD. replace (a + 4 + (n - 1)) with (a + 4 + n + -1) in RD by lia.
        repeat step. clear RD. rewrite (sxb_small cl) by lia. fbr. repeat step. fbr. repeat step. zsimp. ck1f_load TACC (790304 + bv_unsigned cl). step. if_lit. pose proof (rd_tab _ (bv_unsigned cl) MI ltac:(lia)) as RD. unfold A_data_ascii2bin in RD. st1. clear RD. unfold wz. pose proof (land_lt_pow2 (a2b (bv_unsigned cl)) 236 6 ltac:(lia) ltac:(lia)) as LL. change (2^6) with 64 in LL. repeat step. fbr.
        stepto DB_J. unbox CTX. rewrite (unsigned_lit n) by lia. finish.
  Qed.
End P2.
Section P3.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].

  (* [comment removed for export] *)
  Lemma adb_bad_tail :
    forall (ra sp gp tp t0 t1 t2 s0 s1 x8 x9 x10 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n lo : Z) (j8 : list byte),
      n mod 4 <> 0 -> 0 < n <= 64 ->
      rw_cells asegs m (bv_unsigned sp + -64) (adb_frame j8 s5 s4 s3 s2 s1 s0 ra) -> stk asegs m lo (bv_unsigned sp + -64) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
          ms' = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                   F (ret_pc ra) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 x10 a1 (Z_to_bv 64 (Z.land n 3)) a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom asegs)).
  Proof.
    intros until j8. intros NM NR FR ST LO0 LO MI. unfold DB_J. pose proof (aword_range sp) as SPR. unfold adb_frame in FR.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (Z.land n 3) with (Z.land n (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
    step. fbr.
    zstep. zstep.
    do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 14 eexists. split; [reflexivity| exact ST].
  Qed.

  Definition adb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : Z) (Q : mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs) /\ Q m'.

  (* [comment removed for export] *)
  Lemma adecblock_bad_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a n lo nn line : Z) (raw : list byte),
      rw_cells asegs m a (ctx_chunk nn raw line) -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> ACONST m ->
      0 < n <= 64 -> n mod 4 <> 0 -> Forall b64_saved (map bv_unsigned (firstn (Z.to_nat n) raw)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (adb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (-1)
                   (fun m' => munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                              /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' a (ctx_chunk nn raw line)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom asegs)).
  Proof.
    intros until raw. intros CTX POS AL BL CEIL ACC AC NR NM SAVED ST LO MI RAE.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). acb.
    eapply evt_cut; [eapply adb_p1; [exact POS| exact AL| exact BL| exact CEIL| exact ACC| exact AC| exact ST| exact LO| exact MI]|].
    intros ms1 (m1 & j8 & x15 & x17 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CTX1 : rw_cells asegs m1 a (ctx_chunk nn raw line)).
    { eapply rw_cells_transport; [exact CTX| exact MU1| exact WM1|]. unfold ctx_chunk. cbn [cells_size csize Nat.add length disjoint_from]. split; [lia| exact I]. }
    assert (ACC1 : accessible m1 a 92).
    { eapply accessible_across; [exact ACC| exact MU1|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]. }
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]. }
    eapply evt_cut; [eapply adb_p2; [exact CTX1| exact POS| exact AL| exact BL| exact ACC1| exact AC1| exact NR| exact SAVED| exact MI1]|].
    intros ms2 (x7 & x9 & x13 & x15' & x28 & x29 & x30 & x31 & ->).
    eapply evt_mono; [eapply adb_bad_tail; [exact NM| exact NR| exact FR1| exact ST1| exact LO0| lia| exact MI1]|].
    intros ms3 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & ST3). unfold adb_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST3| exact CTX1].
  Qed.
End P3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADB_LB : Z := 0x422a30.  Definition ADB_LC : Z := 0x422a58.  Definition ADB_LD : Z := 0x422a80.  Definition ADB_L3X : Z := 0x422b40.

Lemma groups_bytes_nth' : forall vs g j a b c d,
  nth_error vs (4 * g) = Some a -> nth_error vs (4 * g + 1) = Some b -> nth_error vs (4 * g + 2) = Some c -> nth_error vs (4 * g + 3) = Some d ->
  (j < 3)%nat -> nth_error (groups_bytes vs) (3 * g + j) = nth_error (quad_bytes (quad_val a b c d)) j.
Proof.
  intros vs g j a b c d Na Nb Nc Nd J. eapply groups_bytes_nth; [| exact J].
  rewrite (skipn_nth_cons' _ _ a) by exact Na. f_equal. replace (S (4 * g)) with (4 * g + 1)%nat by lia.
  rewrite (skipn_nth_cons' _ _ b) by exact Nb. f_equal. replace (S (4 * g + 1)) with (4 * g + 2)%nat by lia.
  rewrite (skipn_nth_cons' _ _ c) by exact Nc. f_equal. replace (S (4 * g + 2)) with (4 * g + 3)%nat by lia.
  rewrite (skipn_nth_cons' _ _ d) by exact Nd. reflexivity.
Qed.

Lemma firstn1_of_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof. intros X l i x N. rewrite (skipn_nth_cons' l i x N). reflexivity. Qed.


Section AL3.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  (* [comment removed for export] *)
  Variables (ra spw gp tp s0 a0w s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (a f0 t q eof : Z) (raw tj : list byte) (m0 : mem).
  Hypothesis F0 : f0 = a + 4.
  Hypothesis AR : 0 < a /\ a mod 16 = 0 /\ a + 92 <= aceil.
  Hypothesis ACCa : accessible m0 a 92.
  Hypothesis ACCt : accessible m0 t (Z.of_nat (length tj)).
  Hypothesis NSHt : t + Z.of_nat (length tj) <= ALOWSH_LO \/ AHI_LO <= t.
  Hypothesis AC0 : ACONST m0.
  Hypothesis L80 : length raw = 80%nat.
  Hypothesis SAVED : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Hypothesis QR : 1 <= q <= 16.
  Hypothesis ER : 0 <= eof <= 2.
  Hypothesis TJ : 3 * q <= Z.of_nat (length tj).
  Hypothesis SEP : f0 + 80 <= t \/ t + Z.of_nat (length tj) <= f0.
  Hypothesis TB : 0 <= t /\ t + Z.of_nat (length tj) <= 2^64.
  Hypothesis TP : 0 < t.
  Definition vs : list Z := map a2b (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Definition SRC : list byte := map b8 (groups_bytes vs) ++ skipn (Z.to_nat (3 * q)) tj.
  Definition W : list (Z * Z) := [(t, t + Z.of_nat (length tj))].
  Definition INV (m : mem) (bs : list byte) (k : Z) : Prop :=
    bytes_at asegs m f0 raw /\ u8arr asegs m t bs /\ length bs = length tj /\ copied SRC bs (Z.to_nat k)
    /\ mem_inv asegs m /\ munch W m0 m /\ wmono asegs m0 m.

  Lemma vs_length : length vs = Z.to_nat (4 * q).
  Proof. unfold vs. rewrite !length_map, length_firstn. lia. Qed.
  Lemma SRC_length : length SRC = length tj.
  Proof. unfold SRC. rewrite length_app, length_map, (groups_bytes_length (Z.to_nat q)), length_skipn; [lia|]. rewrite vs_length. lia. Qed.
  Lemma vs_nth : forall i c, nth_error raw (Z.to_nat i) = Some c -> 0 <= i < 4 * q -> nth_error vs (Z.to_nat i) = Some (a2b (bv_unsigned c)).
  Proof.
    intros i c N R. unfold vs. rewrite !nth_error_map, nth_error_firstn.
    replace (Z.to_nat i <? Z.to_nat (4 * q))%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite N. reflexivity.
  Qed.
  Lemma grp_facts : forall g, 0 <= g < q ->
    exists ca cb cc cd,
      nth_error raw (Z.to_nat (4 * g)) = Some ca /\ nth_error raw (Z.to_nat (4 * g + 1)) = Some cb /\
      nth_error raw (Z.to_nat (4 * g + 2)) = Some cc /\ nth_error raw (Z.to_nat (4 * g + 3)) = Some cd /\
      bv_unsigned ca < 128 /\ bv_unsigned cb < 128 /\ bv_unsigned cc < 128 /\ bv_unsigned cd < 128 /\
      0 <= a2b (bv_unsigned ca) < 64 /\ 0 <= a2b (bv_unsigned cb) < 64 /\ 0 <= a2b (bv_unsigned cc) < 64 /\ 0 <= a2b (bv_unsigned cd) < 64 /\
      (forall j, (j < 3)%nat -> nth_error SRC (Z.to_nat (3 * g) + j)
           = Some (b8 (nth j (quad_bytes (quad_val (a2b (bv_unsigned ca)) (a2b (bv_unsigned cb)) (a2b (bv_unsigned cc)) (a2b (bv_unsigned cd)))) 0))).
  Proof.
    intros g G.
    destruct (nth_error raw (Z.to_nat (4 * g))) as [ca|] eqn:Na; [| apply nth_error_None in Na; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 1))) as [cb|] eqn:Nb; [| apply nth_error_None in Nb; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 2))) as [cc|] eqn:Nc; [| apply nth_error_None in Nc; lia].
    destruct (nth_error raw (Z.to_nat (4 * g + 3))) as [cd|] eqn:Nd; [| apply nth_error_None in Nd; lia].
    pose proof (saved_nth (4 * q) raw (4 * g) ca SAVED Na ltac:(lia)) as Sa.
    pose proof (saved_nth (4 * q) raw (4 * g + 1) cb SAVED Nb ltac:(lia)) as Sb.
    pose proof (saved_nth (4 * q) raw (4 * g + 2) cc SAVED Nc ltac:(lia)) as Sc.
    pose proof (saved_nth (4 * q) raw (4 * g + 3) cd SAVED Nd ltac:(lia)) as Sd.
    pose proof (b64_saved_lt64 _ Sa) as Va. pose proof (b64_saved_lt64 _ Sb) as Vb. pose proof (b64_saved_lt64 _ Sc) as Vc. pose proof (b64_saved_lt64 _ Sd) as Vd.
    exists ca, cb, cc, cd. do 4 (split; [reflexivity|]).
    split; [destruct Sa as [K _]; lia|]. split; [destruct Sb as [K _]; lia|]. split; [destruct Sc as [K _]; lia|]. split; [destruct Sd as [K _]; lia|].
    split; [exact Va|]. split; [exact Vb|]. split; [exact Vc|]. split; [exact Vd|].
    intros j J. unfold SRC. rewrite nth_error_app1.
    2:{ rewrite length_map, (groups_bytes_length (Z.to_nat q)) by (rewrite vs_length; lia). lia. }
    rewrite nth_error_map. replace (Z.to_nat (3 * g) + j)%nat with (3 * Z.to_nat g + j)%nat by lia.
    rewrite (groups_bytes_nth' vs (Z.to_nat g) j (a2b (bv_unsigned ca)) (a2b (bv_unsigned cb)) (a2b (bv_unsigned cc)) (a2b (bv_unsigned cd))).
    - destruct j as [|[|[|j]]]; cbn; try reflexivity. lia.
    - replace (4 * Z.to_nat g)%nat with (Z.to_nat (4 * g)) by lia. apply vs_nth; [exact Na| lia].
    - replace (4 * Z.to_nat g + 1)%nat with (Z.to_nat (4 * g + 1)) by lia. apply vs_nth; [exact Nb| lia].
    - replace (4 * Z.to_nat g + 2)%nat with (Z.to_nat (4 * g + 2)) by lia. apply vs_nth; [exact Nc| lia].
    - replace (4 * Z.to_nat g + 3)%nat with (Z.to_nat (4 * g + 3)) by lia. apply vs_nth; [exact Nd| lia].
    - exact J.
  Qed.
  Local Ltac ldc i c N B RAW := let RD := fresh "RD" in
    pose proof (rd_raw _ _ _ i c RAW N ltac:(lia)) as RD; step; clear RD; rewrite (sxb_small c) by lia.
  Local Ltac ldt c MI := let RD := fresh "RD" in
    pose proof (rd_tab _ (bv_unsigned c) MI ltac:(lia)) as RD; unfold A_data_ascii2bin in RD; st1; clear RD.

  (* [comment removed for export] *)
  Definition AL3st (g : Z) (m : mem) (xs1 xa3 xa5 xs2 xs3 xs4 xs5 : word) : machine_state :=
    MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 xs1 (Z_to_bv 64 f0) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (t + 3 * g)) xa3 (Z_to_bv 64 eof)
            xa5 (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
       F (Z_to_bv 64 DB_L3) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Lemma al3_A : forall g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5,
    0 <= g -> g + 2 <= q -> INV m bs (3 * g) ->
    exists ca cb cc cd, nth_error raw (Z.to_nat (4 * g)) = Some ca /\ nth_error raw (Z.to_nat (4 * g + 1)) = Some cb /\
      nth_error raw (Z.to_nat (4 * g + 2)) = Some cc /\ nth_error raw (Z.to_nat (4 * g + 3)) = Some cd /\
    evt asegs (fun ms' => exists (xs5' : word),
        ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (t + 3 * g + 1)) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof) (Z_to_bv 64 (a2b (bv_unsigned cc)))
                     (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 1)) (Z_to_bv 64 (a2b (bv_unsigned cb) * 4096))
                     (Z_to_bv 64 (Z.shiftr (Z.lor (a2b (bv_unsigned cb) * 4096) (a2b (bv_unsigned ca) * 262144)) 16)) xs5' s6 s7 s8 s9 s10 s11
                     (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
                 F (Z_to_bv 64 ADB_LB) fc None m (seg_rom asegs))
      (AL3st g m xs1 xa3 xa5 xs2 xs3 xs4 xs5).
  Proof.
    intros g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5 G0 GQ (RAW & ARR & LEN & CP & MI & MU & WM).
    destruct (grp_facts g ltac:(lia)) as (ca & cb & cc & cd & Na & Nb & Nc & Nd & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    exists ca, cb, cc, cd. split; [exact Na|]. split; [exact Nb|]. split; [exact Nc|]. split; [exact Nd|].
    unfold AL3st, DB_L3, ADB_LB, A_data_ascii2bin. rewrite ASHADOW_BASE_val. unfold W in MU.
    pose proof AR as (POS & AL & BL). acb.
    pose proof (byte_range ca). pose proof (byte_range cb). pose proof (byte_range cc). pose proof (byte_range cd).
    assert (ACC : accessible m a 92) by (eapply accessible_across; [exact ACCa| exact MU|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]).
    assert (ACT : accessible m t (Z.of_nat (length tj))) by (eapply accessible_across; [exact ACCt| exact MU|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]).
    pose proof (tab_accessible _ AC0) as TACC0. unfold A_data_ascii2bin in TACC0.
    assert (TACC : accessible m 790304 128) by (eapply accessible_across; [exact TACC0| exact MU|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]).
    subst f0.
    repeat step. fbr.
    (* [comment removed for export] *)
    repeat step. zsimp. ck1f_load ACC (a + 4 + 4 * g). step. if_lit.
    ldc (4 * g) ca Na Ba RAW. repeat step. fbr. repeat step. fbr.
    repeat zstep. ck1f_load TACC (790304 + bv_unsigned ca). step. if_lit. ldt ca MI. repeat step. fbr.
    (* [comment removed for export] *)
    repeat step. zsimp. ck1f_load ACC (a + 4 + 4 * g + 1). step. if_lit.
    ldc (4 * g + 1) cb Nb Bb RAW. repeat step. fbr. repeat step. fbr.
    repeat zstep. ck1f_load TACC (790304 + bv_unsigned cb). step. if_lit. ldt cb MI. repeat step. fbr.
    (* [comment removed for export] *)
    repeat step. zsimp. ck1f_load ACC (a + 4 + 4 * g + 2). step. if_lit.
    ldc (4 * g + 2) cc Nc Bc RAW. repeat step. fbr. repeat step. fbr.
    repeat zstep. ck1f_load TACC (790304 + bv_unsigned cc). step. if_lit. ldt cc MI. repeat step. fbr.
    (* [comment removed for export] *)
    repeat step. zsimp. ck1f_load ACC (a + 4 + 4 * g + 3). step. if_lit.
    ldc (4 * g + 3) cd Nd Bd RAW. repeat step. fbr. repeat step. fbr.
    repeat zstep. ck1f_load TACC (790304 + bv_unsigned cd). step. if_lit. ldt cd MI.
    unfold wz.
    set (va := a2b (bv_unsigned ca)) in *. set (vb := a2b (bv_unsigned cb)) in *. set (vc := a2b (bv_unsigned cc)) in *. set (vd := a2b (bv_unsigned cd)) in *.
    (* [comment removed for export] *)
    pose proof (lor_lt_pow2 vb va 6 ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow2 vc vd 6 ltac:(lia) ltac:(lia)) as L2.
    pose proof (lor_lt_pow2 (Z.lor vb va) (Z.lor vc vd) 6 L1 L2) as L3. change (2^6) with 64 in L1, L2, L3.
    repeat zstep.
    set (x := Z.lor (Z.lor vb va) (Z.lor vc vd)) in *. rewrite (Z.shiftl_mul_pow2 x 56) by lia. fbr.
    repeat step. fbr.
    (* [comment removed for export] *)
    repeat zstep. ck1_load ACT (t + 3 * g) v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). repeat step. rewrite (unsigned_lit vb) by lia. rewrite (unsigned_lit va) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. change (2^18) with 262144. rewrite (unsigned_lit (vb * 4096)) by lia. rewrite (unsigned_lit (va * 262144)) by lia. pose proof (lor_lt_pow2 (vb * 4096) (va * 262144) 24 ltac:(lia) ltac:(lia)) as L4. rewrite (unsigned_lit (Z.lor (vb * 4096) (va * 262144))) by lia. apply evt_done. eexists. reflexivity.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      repeat step. if_false_by (ck1_bge_false (t + 3 * g) v Ha V1 VV). repeat step. rewrite (unsigned_lit vb) by lia. rewrite (unsigned_lit va) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. change (2^18) with 262144. rewrite (unsigned_lit (vb * 4096)) by lia. rewrite (unsigned_lit (va * 262144)) by lia. pose proof (lor_lt_pow2 (vb * 4096) (va * 262144) 24 ltac:(lia) ltac:(lia)) as L4. rewrite (unsigned_lit (Z.lor (vb * 4096) (va * 262144))) by lia. apply evt_done. eexists. reflexivity.
  Qed.
End AL3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AL3B.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Variables (ra spw gp tp s0 a0w s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (a f0 t q eof : Z) (raw tj : list byte) (m0 : mem).
  Hypothesis F0 : f0 = a + 4.
  Hypothesis AR : 0 < a /\ a mod 16 = 0 /\ a + 92 <= aceil.
  Hypothesis ACCa : accessible m0 a 92.
  Hypothesis ACCt : accessible m0 t (Z.of_nat (length tj)).
  Hypothesis NSHt : t + Z.of_nat (length tj) <= ALOWSH_LO \/ AHI_LO <= t.
  Hypothesis AC0 : ACONST m0.
  Hypothesis L80 : length raw = 80%nat.
  Hypothesis SAVED : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Hypothesis QR : 1 <= q <= 16.
  Hypothesis ER : 0 <= eof <= 2.
  Hypothesis TJ : 3 * q <= Z.of_nat (length tj).
  Hypothesis SEP : f0 + 80 <= t \/ t + Z.of_nat (length tj) <= f0.
  Hypothesis TB : 0 <= t /\ t + Z.of_nat (length tj) <= 2^64.
  Hypothesis TP : 0 < t.
  Local Notation INVc := (INV f0 t q raw tj m0).
  Local Notation SRCc := (SRC q raw tj).
  (* [comment removed for export] *)
  Local Ltac arr_store E P P' MB NS :=
    match goal with ARR : u8arr asegs ?m t ?bs, CP : copied _ ?bs' _, LEN : length ?bs'' = length tj |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok asegs m t bs P (wa E) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      step; rewrite le1_mod; rewrite MB;
      let ARR2 := fresh "ARR" in let CP2 := fresh "CP" in let LEN2 := fresh "LEN" in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?x]) _) =>
        pose proof (u8arr_write_bytes asegs m t bs P [x] ARR ltac:(lia) ltac:(cbn; lia)) as ARR2;
        try (replace (t + P) with E in ARR2 by lia);
        pose proof (copied_updZ _ bs P [x] CP ltac:(lia) (firstn1_of_nth _ _ _ NS) ltac:(rewrite (SRC_length a q raw tj AR L80 QR TJ); cbn; lia)) as CP2;
        lazymatch type of CP2 with copied _ _ ?idx => replace idx with (Z.to_nat P') in CP2 by (cbn; lia) end;
        pose proof LEN as LEN2; rewrite <- (upd_bytes_length bs (Z.to_nat P) [x]) in LEN2 by (cbn; lia);
        clear ARR CP LEN; store_done; try clear SOK;
        let bs2 := fresh "bs" in let Ebs := fresh "Ebs" in remember (upd_bytes bs (Z.to_nat P) [x]) as bs2 eqn:Ebs; clear Ebs
      end
    end.

  (* [comment removed for export] *)
  Lemma al3_B : forall g m bs ca cb cc cd (xs5 : word),
    0 <= g -> g + 2 <= q -> INVc m bs (3 * g) ->
    nth_error raw (Z.to_nat (4 * g)) = Some ca -> nth_error raw (Z.to_nat (4 * g + 1)) = Some cb ->
    nth_error raw (Z.to_nat (4 * g + 2)) = Some cc -> nth_error raw (Z.to_nat (4 * g + 3)) = Some cd ->
    evt asegs (fun ms' => exists m' bs' (xs4' xs5' : word),
        ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (Z.shiftr (Z.lor (a2b (bv_unsigned cc) * 64) (a2b (bv_unsigned cb) * 4096)) 8)) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof)
                     (Z_to_bv 64 (a2b (bv_unsigned cc) * 64)) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 2)) (Z_to_bv 64 (a2b (bv_unsigned cb) * 4096))
                     xs4' xs5' s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
                 F (Z_to_bv 64 ADB_LC) fc None m' (seg_rom asegs)
        /\ INVc m' bs' (3 * g + 1))
      (MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (t + 3 * g + 1)) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof) (Z_to_bv 64 (a2b (bv_unsigned cc)))
                     (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 1)) (Z_to_bv 64 (a2b (bv_unsigned cb) * 4096))
                     (Z_to_bv 64 (Z.shiftr (Z.lor (a2b (bv_unsigned cb) * 4096) (a2b (bv_unsigned ca) * 262144)) 16)) xs5 s6 s7 s8 s9 s10 s11
                     (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
           F (Z_to_bv 64 ADB_LB) fc None m (seg_rom asegs)).
  Proof.
    intros g m bs ca cb cc cd xs5 G0 GQ (RAW & ARR & LEN & CP & MI & MU & WM) Na Nb Nc Nd.
    destruct (grp_facts a q raw tj AR L80 SAVED QR g ltac:(lia)) as (ca' & cb' & cc' & cd' & Na' & Nb' & Nc' & Nd' & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    rewrite Na in Na'. injection Na' as <-. rewrite Nb in Nb'. injection Nb' as <-. rewrite Nc in Nc'. injection Nc' as <-. rewrite Nd in Nd'. injection Nd' as <-.
    pose proof (NS 0%nat ltac:(lia)) as NS0. clear NS. rewrite Nat.add_0_r in NS0. cbn [nth quad_bytes] in NS0.
    unfold ADB_LB, ADB_LC, A_data_ascii2bin. rewrite ASHADOW_BASE_val. unfold W in MU.
    pose proof AR as (POS & AL & BL). acb. subst f0.
    set (va := a2b (bv_unsigned ca)) in *. set (vb := a2b (bv_unsigned cb)) in *. set (vc := a2b (bv_unsigned cc)) in *. set (vd := a2b (bv_unsigned cd)) in *.
    (* [comment removed for export] *)
    pose proof TB as [T0 T1].
    (* [comment removed for export] *)
    arr_store (t + 3 * g) (3 * g) (3 * g + 1) (mb0_ok va vb vc vd Va Vb Vc Vd) NS0.
    step. fbr.
    (* [comment removed for export] *)
    match goal with MU' : munch _ m0 ?mc |- _ =>
      assert (ACT : accessible mc t (Z.of_nat (length tj))) by (eapply accessible_across; [exact ACCt| exact MU'|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]) end.
    zstep. zstep. ck1_load ACT (t + 3 * g + 1) v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). repeat step. rewrite (unsigned_lit vc) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. rewrite (unsigned_lit (vc * 64)) by lia. rewrite (unsigned_lit (vb * 4096)) by lia. pose proof (lor_lt_pow2 (vc * 64) (vb * 4096) 18 ltac:(lia) ltac:(lia)) as L5. rewrite (unsigned_lit (Z.lor (vc * 64) (vb * 4096))) by lia.
      apply evt_done. eexists _, _, _, _. split; [reflexivity|].
      split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      step. step. if_false_by (ck1_bge_false (t + 3 * g + 1) v Ha V1 VV). repeat step. rewrite (unsigned_lit vc) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. rewrite (unsigned_lit (vc * 64)) by lia. rewrite (unsigned_lit (vb * 4096)) by lia. pose proof (lor_lt_pow2 (vc * 64) (vb * 4096) 18 ltac:(lia) ltac:(lia)) as L5. rewrite (unsigned_lit (Z.lor (vc * 64) (vb * 4096))) by lia.
      apply evt_done. eexists _, _, _, _. split; [reflexivity|].
      split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma al3_C : forall g m bs ca cb cc cd (xs4 xs5 : word),
    0 <= g -> g + 2 <= q -> INVc m bs (3 * g + 1) ->
    nth_error raw (Z.to_nat (4 * g)) = Some ca -> nth_error raw (Z.to_nat (4 * g + 1)) = Some cb ->
    nth_error raw (Z.to_nat (4 * g + 2)) = Some cc -> nth_error raw (Z.to_nat (4 * g + 3)) = Some cd ->
    evt asegs (fun ms' => exists m' bs' (xs3' xs4' xs5' : word),
        ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (Z.lor (a2b (bv_unsigned cd)) (Z.land (a2b (bv_unsigned cc) * 64) 255))) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof)
                     (Z_to_bv 64 (3 * g + 3)) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 2)) xs3'
                     xs4' xs5' s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
                 F (Z_to_bv 64 ADB_LD) fc None m' (seg_rom asegs)
        /\ INVc m' bs' (3 * g + 2))
      (MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (Z.shiftr (Z.lor (a2b (bv_unsigned cc) * 64) (a2b (bv_unsigned cb) * 4096)) 8)) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof)
                     (Z_to_bv 64 (a2b (bv_unsigned cc) * 64)) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 2)) (Z_to_bv 64 (a2b (bv_unsigned cb) * 4096))
                     xs4 xs5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
           F (Z_to_bv 64 ADB_LC) fc None m (seg_rom asegs)).
  Proof.
    intros g m bs ca cb cc cd xs4 xs5 G0 GQ (RAW & ARR & LEN & CP & MI & MU & WM) Na Nb Nc Nd.
    destruct (grp_facts a q raw tj AR L80 SAVED QR g ltac:(lia)) as (ca' & cb' & cc' & cd' & Na' & Nb' & Nc' & Nd' & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    rewrite Na in Na'. injection Na' as <-. rewrite Nb in Nb'. injection Nb' as <-. rewrite Nc in Nc'. injection Nc' as <-. rewrite Nd in Nd'. injection Nd' as <-.
    pose proof (NS 1%nat ltac:(lia)) as NS1. clear NS. replace (Z.to_nat (3 * g) + 1)%nat with (Z.to_nat (3 * g + 1)) in NS1 by lia. cbn [nth quad_bytes] in NS1.
    unfold ADB_LC, ADB_LD, A_data_ascii2bin. rewrite ASHADOW_BASE_val. unfold W in MU.
    pose proof AR as (POS & AL & BL). acb. subst f0.
    set (va := a2b (bv_unsigned ca)) in *. set (vb := a2b (bv_unsigned cb)) in *. set (vc := a2b (bv_unsigned cc)) in *. set (vd := a2b (bv_unsigned cd)) in *.
    (* [comment removed for export] *)
    pose proof TB as [T0 T1].
    (* [comment removed for export] *)
    arr_store (t + 3 * g + 1) (3 * g + 1) (3 * g + 2) (mb1_ok va vb vc vd Va Vb Vc Vd) NS1.
    step. fbr.
    (* [comment removed for export] *)
    match goal with MU' : munch _ m0 ?mc |- _ =>
      assert (ACT : accessible mc t (Z.of_nat (length tj))) by (eapply accessible_across; [exact ACCt| exact MU'|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]) end.
    zstep. zstep. zstep. ck1_load ACT (t + 3 * g + 2) v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). repeat step. rewrite (unsigned_lit vd) by lia. rewrite (unsigned_lit (vc * 64)) by lia. assert (LB : 0 <= Z.land (vc * 64) 255 <= 255) by (change (Z.land (vc * 64) 255) with (Z.land (vc * 64) (Z.ones 8)); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound (vc * 64) (2 ^ 8) ltac:(lia)); change (2 ^ 8) with 256 in *; lia). rewrite (unsigned_lit (Z.land (vc * 64) 255)) by lia. rewrite (unsigned_lit (3 * g)) by lia. rewrite (bv_swrap_small 32 (3 * g + 3)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      apply evt_done. eexists _, _, _, _, _. split; [reflexivity|].
      split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      step. step. if_false_by (ck1_bge_false (t + 3 * g + 2) v Ha V1 VV). repeat step. rewrite (unsigned_lit vd) by lia. rewrite (unsigned_lit (vc * 64)) by lia. assert (LB : 0 <= Z.land (vc * 64) 255 <= 255) by (change (Z.land (vc * 64) 255) with (Z.land (vc * 64) (Z.ones 8)); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound (vc * 64) (2 ^ 8) ltac:(lia)); change (2 ^ 8) with 256 in *; lia). rewrite (unsigned_lit (Z.land (vc * 64) 255)) by lia. rewrite (unsigned_lit (3 * g)) by lia. rewrite (bv_swrap_small 32 (3 * g + 3)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      apply evt_done. eexists _, _, _, _, _. split; [reflexivity|].
      split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma mb2A_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 (Z.lor vd (Z.land (vc * 64) 255) mod 256) = b8 (nth 2 (quad_bytes (quad_val va vb vc vd)) 0).
  Proof.
    intros va vb vc vd Ra Rb Rc Rd. rewrite <- (mb2_ok va vb vc vd Ra Rb Rc Rd). apply b8_eqm. rewrite !Z.mod_mod by lia.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    assert (E1 : (vc * 64) mod 256 = (vc mod 4) * 64) by (Z.div_mod_to_equations; nia).
    rewrite E1. change ((vc mod 4) * 64) with ((vc mod 4) * 2 ^ 6). rewrite (lor_add_disjoint vd (vc mod 4) 6) by lia.
    change (vc * 64) with (vc * 2 ^ 6). rewrite (lor_add_disjoint vd vc 6) by lia. change (2 ^ 6) with 64.
    Z.div_mod_to_equations. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma al3_D : forall g m bs ca cb cc cd (xs3 xs4 xs5 : word),
    0 <= g -> g + 2 <= q -> INVc m bs (3 * g + 2) ->
    nth_error raw (Z.to_nat (4 * g)) = Some ca -> nth_error raw (Z.to_nat (4 * g + 1)) = Some cb ->
    nth_error raw (Z.to_nat (4 * g + 2)) = Some cc -> nth_error raw (Z.to_nat (4 * g + 3)) = Some cd ->
    evt asegs (fun ms' => exists m' bs',
        ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * (g + 1))) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (t + 3 * (g + 1))) (Z_to_bv 64 (t + 3 * (g + 1))) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof)
                     (Z_to_bv 64 (3 * (g + 1))) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 2)) xs3
                     xs4 xs5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * (g + 1))) (Z_to_bv 64 (3 * (g + 1))) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
                 F (Z_to_bv 64 (if g + 3 <=? q then DB_L3 else ADB_L3X)) fc None m' (seg_rom asegs)
        /\ INVc m' bs' (3 * (g + 1)))
      (MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 f0)
                     (Z_to_bv 64 (Z.lor (a2b (bv_unsigned cd)) (Z.land (a2b (bv_unsigned cc) * 64) 255))) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (a2b (bv_unsigned cd))) (Z_to_bv 64 eof)
                     (Z_to_bv 64 (3 * g + 3)) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) (Z_to_bv 64 (t + 3 * g + 2)) xs3
                     xs4 xs5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
           F (Z_to_bv 64 ADB_LD) fc None m (seg_rom asegs)).
  Proof.
    intros g m bs ca cb cc cd xs3 xs4 xs5 G0 GQ (RAW & ARR & LEN & CP & MI & MU & WM) Na Nb Nc Nd.
    destruct (grp_facts a q raw tj AR L80 SAVED QR g ltac:(lia)) as (ca' & cb' & cc' & cd' & Na' & Nb' & Nc' & Nd' & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    rewrite Na in Na'. injection Na' as <-. rewrite Nb in Nb'. injection Nb' as <-. rewrite Nc in Nc'. injection Nc' as <-. rewrite Nd in Nd'. injection Nd' as <-.
    pose proof (NS 2%nat ltac:(lia)) as NS2. clear NS. replace (Z.to_nat (3 * g) + 2)%nat with (Z.to_nat (3 * g + 2)) in NS2 by lia. cbn [nth quad_bytes] in NS2.
    unfold ADB_LD, DB_L3, ADB_L3X, A_data_ascii2bin. rewrite ASHADOW_BASE_val. unfold W in MU.
    pose proof AR as (POS & AL & BL). acb. subst f0.
    set (va := a2b (bv_unsigned ca)) in *. set (vb := a2b (bv_unsigned cb)) in *. set (vc := a2b (bv_unsigned cc)) in *. set (vd := a2b (bv_unsigned cd)) in *.
    (* [comment removed for export] *)
    pose proof TB as [T0 T1].
    (* [comment removed for export] *)
    arr_store (t + 3 * g + 2) (3 * g + 2) (3 * (g + 1)) (mb2A_ok va vb vc vd Va Vb Vc Vd) NS2.
    (* [comment removed for export] *)
    step. fbr. repeat step.
    rewrite (unsigned_lit (4 * g)) by lia. rewrite (bv_swrap_small 32 (4 * g + 4)) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    lazymatch goal with ARRx : u8arr asegs ?mx t ?bsx |- _ =>
      if_cases EQ; zify_cond EQ; rewrite ?signed_lit in EQ by lia;
      [ replace (g + 3 <=? q) with false by (symmetry; apply Z.leb_gt; lia)
      | replace (g + 3 <=? q) with true by (symmetry; apply Z.leb_le; lia); step ];
      replace (4 * g + 4) with (4 * (g + 1)) by lia; replace (t + 3 * g + 3) with (t + 3 * (g + 1)) by lia; replace (3 * g + 3) with (3 * (g + 1)) by lia;
      apply evt_done; exists mx, bsx;
      (split; [reflexivity| split; [assumption| split; [exact ARRx| split; [assumption| split; [assumption| split; [assumption| split; assumption]]]]]])
    end.
  Qed.

  (* [comment removed for export] *)
  Definition AL3at (pc g : Z) (m : mem) (xs1 xa3 xa5 xs2 xs3 xs4 xs5 : word) : machine_state :=
    MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 (4 * g)) s0 xs1 (Z_to_bv 64 f0) (Z_to_bv 64 (t + 3 * g)) (Z_to_bv 64 (t + 3 * g)) xa3 (Z_to_bv 64 eof)
            xa5 (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (4 * g)) (Z_to_bv 64 (3 * g)) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
       F (Z_to_bv 64 pc) fc None m (seg_rom asegs).
  Lemma AL3st_at : forall g m xs1 xa3 xa5 xs2 xs3 xs4 xs5,
    AL3st ra spw gp tp s0 s6 s7 s8 s9 s10 s11 F fc f0 t q eof g m xs1 xa3 xa5 xs2 xs3 xs4 xs5 = AL3at DB_L3 g m xs1 xa3 xa5 xs2 xs3 xs4 xs5.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma al3_iter : forall g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5,
    0 <= g -> g + 2 <= q -> INVc m bs (3 * g) ->
    evt asegs (fun ms' => exists m' bs' xa3' xs2' xs3' xs4' xs5',
        ms' = AL3at (if g + 3 <=? q then DB_L3 else ADB_L3X) (g + 1) m' (Z_to_bv 64 (t + 3 * g)) xa3' (Z_to_bv 64 (3 * (g + 1))) xs2' xs3' xs4' xs5'
        /\ INVc m' bs' (3 * (g + 1)))
      (AL3st ra spw gp tp s0 s6 s7 s8 s9 s10 s11 F fc f0 t q eof g m xs1 xa3 xa5 xs2 xs3 xs4 xs5).
  Proof.
    intros g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5 G0 GQ I.
    destruct (al3_A ra spw gp tp s0 s6 s7 s8 s9 s10 s11 F fc a f0 t q eof raw tj m0 F0 AR ACCa ACCt NSHt AC0 L80 SAVED QR TJ SEP TB TP g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5 G0 GQ I)
      as (ca & cb & cc & cd & Na & Nb & Nc & Nd & EA).
    eapply evt_cut; [exact EA|]. intros ms1 (xs5a & ->).
    eapply evt_cut; [eapply al3_B; [exact G0| exact GQ| exact I| exact Na| exact Nb| exact Nc| exact Nd]|]. intros ms2 (m2 & bs2 & xs4b & xs5b & -> & I2).
    eapply evt_cut; [eapply al3_C; [exact G0| exact GQ| exact I2| exact Na| exact Nb| exact Nc| exact Nd]|]. intros ms3 (m3 & bs3 & xs3c & xs4c & xs5c & -> & I3).
    eapply evt_mono; [eapply al3_D; [exact G0| exact GQ| exact I3| exact Na| exact Nb| exact Nc| exact Nd]|]. intros ms4 (m4 & bs4 & -> & I4).
    exists m4, bs4. do 5 eexists. split; [| exact I4]. unfold AL3at. destruct (g + 3 <=? q); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma al3_loop : forall k g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5,
    Z.to_nat (q - 2 - g) = k -> 0 <= g -> g + 2 <= q -> INVc m bs (3 * g) ->
    evt asegs (fun ms' => exists m' bs' (x6 x7 x9 x12 x13 x18 x19 x20 x21 x28 x29 x30 x31 : word),
        ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) x6 x7 s0 x9 (Z_to_bv 64 (f0 + 4 * (q - 1))) (Z_to_bv 64 (t + 3 * (q - 1))) x12 x13 (Z_to_bv 64 eof)
                      (Z_to_bv 64 (3 * (q - 1))) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 DB_LAST) fc None m' (seg_rom asegs)
        /\ INVc m' bs' (3 * (q - 1)))
      (AL3st ra spw gp tp s0 s6 s7 s8 s9 s10 s11 F fc f0 t q eof g m xs1 xa3 xa5 xs2 xs3 xs4 xs5).
  Proof.
    induction k as [|k IH]; intros g m bs xs1 xa3 xa5 xs2 xs3 xs4 xs5 HK G0 GQ I.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply al3_iter; [exact G0| exact GQ| exact I]|].
      intros ms1 (m1 & bs1 & xa3' & xs2' & xs3' & xs4' & xs5' & -> & I1).
      replace (g + 3 <=? q) with false by (symmetry; apply Z.leb_gt; lia). unfold AL3at, ADB_L3X, DB_LAST.
      pose proof AR as (POS & AL & BL). pose proof TB as [T0 T1]. subst f0.
      destruct I1 as (RAW1 & ARR1 & LEN1 & CP1 & MI1 & MU1 & WM1).
      zstep. zstep. apply evt_done. exists m1, bs1. do 13 eexists.
      replace (g + 1) with (q - 1) by lia. replace (t + 3 * g + 3) with (t + 3 * (q - 1)) by lia.
      replace (3 * (g + 1)) with (3 * (q - 1)) in CP1 by lia.
      split; [reflexivity|]. split; [exact RAW1|]. split; [exact ARR1|]. split; [exact LEN1|]. split; [exact CP1|]. split; [exact MI1|]. split; [exact MU1| exact WM1].
    - eapply evt_cut; [eapply al3_iter; [exact G0| exact GQ| exact I]|].
      intros ms1 (m1 & bs1 & xa3' & xs2' & xs3' & xs4' & xs5' & -> & I1).
      replace (g + 3 <=? q) with true by (symmetry; apply Z.leb_le; lia). rewrite <- AL3st_at.
      eapply (IH (g + 1)); [lia| lia| lia| exact I1].
  Qed.
End AL3B.

Section ALAST.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Variables (ra sp gp tp a0w s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (a f0 t q eof : Z) (raw tj : list byte) (m0 : mem).
  Hypothesis F0 : f0 = a + 4.
  Hypothesis AR : 0 < a /\ a mod 16 = 0 /\ a + 92 <= aceil.
  Hypothesis ACCa : accessible m0 a 92.
  Hypothesis ACCt : accessible m0 t (Z.of_nat (length tj)).
  Hypothesis NSHt : t + Z.of_nat (length tj) <= ALOWSH_LO \/ AHI_LO <= t.
  Hypothesis AC0 : ACONST m0.
  Hypothesis L80 : length raw = 80%nat.
  Hypothesis SAVED : Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)).
  Hypothesis QR : 1 <= q <= 16.
  Hypothesis ER : 0 <= eof <= 2.
  Hypothesis TJ : 3 * q <= Z.of_nat (length tj).
  Hypothesis SEP : f0 + 80 <= t \/ t + Z.of_nat (length tj) <= f0.
  Hypothesis TB : 0 <= t /\ t + Z.of_nat (length tj) <= 2^64.
  Hypothesis TP : 0 < t.
  Local Notation INVc := (INV f0 t q raw tj m0).
  Local Notation SRCc := (SRC q raw tj).
  Local Ltac arr_store E P P' MB NS :=
    match goal with ARR : u8arr asegs ?m t ?bs, CP : copied _ ?bs' _, LEN : length ?bs'' = length tj |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok asegs m t bs P (wa E) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      step; rewrite le1_mod; rewrite MB;
      let ARR2 := fresh "ARR" in let CP2 := fresh "CP" in let LEN2 := fresh "LEN" in
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?x]) _) =>
        pose proof (u8arr_write_bytes asegs m t bs P [x] ARR ltac:(lia) ltac:(cbn; lia)) as ARR2;
        try (replace (t + P) with E in ARR2 by lia);
        pose proof (copied_updZ _ bs P [x] CP ltac:(lia) (firstn1_of_nth _ _ _ NS) ltac:(rewrite (SRC_length a q raw tj AR L80 QR TJ); cbn; lia)) as CP2;
        lazymatch type of CP2 with copied _ _ ?idx => replace idx with (Z.to_nat P') in CP2 by (cbn; lia) end;
        pose proof LEN as LEN2; rewrite <- (upd_bytes_length bs (Z.to_nat P) [x]) in LEN2 by (cbn; lia);
        clear ARR CP LEN; store_done; try clear SOK;
        let bs2 := fresh "bs" in let Ebs := fresh "Ebs" in remember (upd_bytes bs (Z.to_nat P) [x]) as bs2 eqn:Ebs; clear Ebs
      end
    end.
  Local Ltac ldc i c N B RAW := let RD := fresh "RD" in
    pose proof (rd_raw _ _ _ i c RAW N ltac:(lia)) as RD; step; clear RD; rewrite (sxb_small c) by lia.
  Local Ltac ldt c MI := let RD := fresh "RD" in
    pose proof (rd_tab _ (bv_unsigned c) MI ltac:(lia)) as RD; unfold A_data_ascii2bin in RD; st1; clear RD.
  (* [comment removed for export] *)
  Local Ltac reacc_t := match goal with MU' : munch _ m0 ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let A := fresh "ACT" in
      assert (A : accessible mc t (Z.of_nat (length tj))) by (eapply accessible_across; [exact ACCt| exact MU'|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]) end.

  (* [comment removed for export] *)
  Lemma mb1L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 ((Z.lor (Z.lor (vc * 64) vd) (Z.lor (vb * 4096) (va * 262144)) ≫ 8) mod 256) = b8 ((quad_val va vb vc vd / 256) mod 256).
  Proof.
    intros va vb vc vd Ra Rb Rc Rd. rewrite (Z.lor_comm (vc * 64) vd).
    change (vc * 64) with (vc * 2^6). rewrite (lor_add_disjoint vd vc 6) by lia.
    change (va * 262144) with (va * 2^18). rewrite (lor_add_disjoint (vb * 4096) va 18) by lia.
    replace (vb * 4096 + va * 2^18) with ((vb + va * 64) * 2^12) by lia. rewrite (lor_add_disjoint _ _ 12) by lia.
    rewrite Z.shiftr_div_pow2 by lia. apply b8_eqm. unfold quad_val. rewrite !Z.mod_mod by lia.
    change (2^6) with 64. change (2^12) with 4096. change (2^8) with 256. f_equal. f_equal. lia.
  Qed.
  Lemma mb2L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 (Z.lor (vc * 64) vd mod 256) = b8 (quad_val va vb vc vd mod 256).
  Proof. intros va vb vc vd Ra Rb Rc Rd. rewrite (Z.lor_comm (vc * 64) vd). exact (mb2_ok va vb vc vd Ra Rb Rc Rd). Qed.
  Lemma mb0L_ok : forall va vb vc vd, 0 <= va < 64 -> 0 <= vb < 64 -> 0 <= vc < 64 -> 0 <= vd < 64 ->
    b8 ((Z.lor (vb * 4096) (va * 262144) ≫ 16) mod 256) = b8 ((quad_val va vb vc vd / 65536) mod 256).
  Proof. intros. apply mb0_ok; assumption. Qed.

  (* [comment removed for export] *)
  Lemma alast_grp : forall m bs (x6 x7 x8 x9 x12 x13 x18 x19 x20 x21 x28 x29 x30 x31 : word) (S5 S4 S3 S2 S1 S0 : word) (lo : Z) (j8 : list byte),
    INVc m bs (3 * (q - 1)) ->
    rw_cells asegs m0 (bv_unsigned sp + -64) (adb_frame j8 S5 S4 S3 S2 S1 S0 ra) -> stk asegs m0 lo (bv_unsigned sp + -64) -> 0 <= lo -> lo <= bv_unsigned sp + -64 ->
    (t + Z.of_nat (length tj) <= lo \/ bv_unsigned sp <= t) -> bv_unsigned ra mod 2 = 0 ->
    evt asegs (fun ms' => exists m' bs' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        ms' = MS (mkR ra sp gp tp y5 y6 y7 S0 S1 (Z_to_bv 64 (3 * q - eof)) y11 y12 y13 y14 y15 y16 y17 S2 S3 S4 S5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ INVc m' bs' (3 * q - eof) /\ stk asegs m' lo (bv_unsigned sp))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 18446744073708761311) x6 x7 x8 x9 (Z_to_bv 64 (f0 + 4 * (q - 1))) (Z_to_bv 64 (t + 3 * (q - 1))) x12 x13 (Z_to_bv 64 eof)
               (Z_to_bv 64 (3 * (q - 1))) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 DB_LAST) fc None m (seg_rom asegs)).
  Proof.
    intros m bs x6 x7 x8 x9 x12 x13 x18 x19 x20 x21 x28 x29 x30 x31 S5 S4 S3 S2 S1 S0 lo j8 (RAW & ARR & LEN & CP & MI & MU & WM) FR0 ST0 LO0 LO TSEP RAE.
    unfold DB_LAST, A_data_ascii2bin. rewrite ASHADOW_BASE_val. unfold W in MU. pose proof (aword_range sp) as SPR.
    pose proof AR as (POS & AL & BL). acb. pose proof TB as [T0 T1].
    destruct (grp_facts a q raw tj AR L80 SAVED QR (q - 1) ltac:(lia)) as (ca & cb & cc & cd & Na & Nb & Nc & Nd & Ba & Bb & Bc & Bd & Va & Vb & Vc & Vd & NS).
    pose proof (NS 0%nat ltac:(lia)) as NS0. pose proof (NS 1%nat ltac:(lia)) as NS1. pose proof (NS 2%nat ltac:(lia)) as NS2. clear NS.
    rewrite Nat.add_0_r in NS0. replace (Z.to_nat (3 * (q - 1)) + 1)%nat with (Z.to_nat (3 * (q - 1) + 1)) in NS1 by lia.
    replace (Z.to_nat (3 * (q - 1)) + 2)%nat with (Z.to_nat (3 * (q - 1) + 2)) in NS2 by lia.
    cbn [nth quad_bytes] in NS0, NS1, NS2.
    pose proof (byte_range ca). pose proof (byte_range cb). pose proof (byte_range cc). pose proof (byte_range cd).
    assert (ACC : accessible m a 92) by (eapply accessible_across; [exact ACCa| exact MU|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]).
    pose proof (tab_accessible _ AC0) as TACC0. unfold A_data_ascii2bin in TACC0.
    assert (TACC : accessible m 790304 128) by (eapply accessible_across; [exact TACC0| exact MU|]; apply Forall_cons; [cbn [fst snd]; exact NSHt| apply Forall_nil]).
    subst f0.
    (* [comment removed for export] *)
    zstep. zstep. step. fbr. zstep. zstep. ck1f_load ACC (a + 4 + 4 * (q - 1)). step. if_false_by (ck1_bnez_false 0 eq_refl).
    ldc (4 * (q - 1)) ca Na Ba RAW. step. fbr. step. fbr. zstep. zstep. zstep. ck1f_load TACC (790304 + bv_unsigned ca). step. if_false_by (ck1_bnez_false 0 eq_refl). ldt ca MI. step.
    (* [comment removed for export] *)
    zstep. step. fbr. zstep. zstep. ck1f_load ACC (a + 4 + 4 * (q - 1) + 1). step. if_false_by (ck1_bnez_false 0 eq_refl).
    ldc (4 * (q - 1) + 1) cb Nb Bb RAW. step. fbr. step. fbr. zstep. zstep. zstep. ck1f_load TACC (790304 + bv_unsigned cb). step. if_false_by (ck1_bnez_false 0 eq_refl). ldt cb MI. step.
    (* [comment removed for export] *)
    zstep. zstep. step. fbr. zstep. zstep. ck1f_load ACC (a + 4 + 4 * (q - 1) + 2). step. if_false_by (ck1_bnez_false 0 eq_refl).
    ldc (4 * (q - 1) + 2) cc Nc Bc RAW. step. fbr. step. fbr. zstep. zstep. zstep. ck1f_load TACC (790304 + bv_unsigned cc). step. if_false_by (ck1_bnez_false 0 eq_refl). ldt cc MI. step.
    (* [comment removed for export] *)
    zstep. zstep. step. fbr. zstep. zstep. ck1f_load ACC (a + 4 + 4 * (q - 1) + 3). step. if_false_by (ck1_bnez_false 0 eq_refl).
    ldc (4 * (q - 1) + 3) cd Nd Bd RAW. step. fbr. step. fbr. zstep. zstep. zstep. ck1f_load TACC (790304 + bv_unsigned cd). step. if_false_by (ck1_bnez_false 0 eq_refl). ldt cd MI. step.
    unfold wz.
    set (va := a2b (bv_unsigned ca)) in *. set (vb := a2b (bv_unsigned cb)) in *. set (vc := a2b (bv_unsigned cc)) in *. set (vd := a2b (bv_unsigned cd)) in *.
    (* [comment removed for export] *)
    pose proof (lor_lt_pow2 vb va 6 ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow2 vc vd 6 ltac:(lia) ltac:(lia)) as L2.
    pose proof (lor_lt_pow2 (Z.lor vb va) (Z.lor vc vd) 6 L1 L2) as L3. change (2^6) with 64 in L1, L2, L3.
    zstep. zstep. zstep. zstep.
    set (x := Z.lor (Z.lor vb va) (Z.lor vc vd)) in *. rewrite (Z.shiftl_mul_pow2 x 56) by lia. change (2^56) with 72057594037927936.
    step. fbr.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. step. zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. change (2^18) with 262144. change (2^6) with 64.
    change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia. rewrite !(Z.mod_small _ (2 ^ 64)) by lia.
    step. tbr.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    assert (EPI : forall m2 bs2 (k : Z) (z5 z6 z7 z10 z11 z12 z13 z16 z17 : word),
      INV (a + 4) t q raw tj m0 m2 bs2 k ->
      evt asegs (fun ms' => exists m' bs' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
          ms' = MS (mkR ra sp gp tp y5 y6 y7 S0 S1 (Z_to_bv 64 (3 * q - eof)) y11 y12 y13 y14 y15 y16 y17 S2 S3 S4 S5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ INV (a + 4) t q raw tj m0 m' bs' k /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z5 z6 z7 x8 x9 z10 z11 z12 z13 (Z_to_bv 64 eof) (Z_to_bv 64 (3 * (q - 1))) z16 z17
                 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x422d74) fc None m2 (seg_rom asegs))).
    { intros m2 bs2 k z5 z6 z7 z10 z11 z12 z13 z16 z17 (RAW2 & ARR2 & LEN2 & CP2 & MI2 & MU2 & WM2).
      pose proof (rw_cells_transport asegs _ m0 m2 _ _ FR0 MU2 WM2 ltac:(cbn; lia)) as FR.
      pose proof (stk_transport_disjoint asegs _ m0 m2 _ _ ST0 MU2 WM2 ltac:(cbn; lia)) as ST.
      unfold adb_frame in FR.
      (* [comment removed for export] *)
      step. zstep. rewrite ?(bv_swrap_small 32) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      zstep. zstep. rewrite ?(bv_swrap_small 32) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      step. tbr. zstep. rewrite ?(bv_swrap_small 32) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      do 7 st1. step. step.
      release_frame FR ST (bv_unsigned sp).
      replace (3 * (q - 1) + (3 - eof)) with (3 * q - eof) by lia.
      apply evt_done. eexists m2, bs2, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|]. split; [| exact ST].
      split; [exact RAW2|]. split; [exact ARR2|]. split; [exact LEN2|]. split; [exact CP2|]. split; [exact MI2|]. split; [exact MU2| exact WM2]. }
    step. if_cases EQ0; zify_cond EQ0.
    - (* [comment removed for export] *)
      reacc_t. zstep. zstep. step. fbr. zstep. zstep. ck1_load ACT (t + 3 * (q - 1)) v V1 V2 Ha.
      ck_K 6 0x422d14 KA.
      { intros tv. red_tset.
        (* [comment removed for export] *)
        zstep. zstep. arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * (q - 1) + 1) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
        (* [comment removed for export] *)
        step. fbr. clear ACT. reacc_t. zstep. zstep. ck1_load ACT (t + 3 * (q - 1) + 1) v' V1' V2' Ha'.
        ck_K 5 0x422d34 KB.
        { intros tv'. red_tset.
          (* [comment removed for export] *)
          zstep. zstep. arr_store (t + 3 * (q - 1) + 1) (3 * (q - 1) + 1) (3 * (q - 1) + 2) (mb1L_ok va vb vc vd Va Vb Vc Vd) NS1.
          (* [comment removed for export] *)
          clear ACT. reacc_t. zstep. zstep. ck1_load ACT (t + 3 * (q - 1) + 2) v'' V1'' V2'' Ha''.
          ck_K 12 0x422d50 KC.
          { intros tv''. red_tset.
            (* [comment removed for export] *)
            arr_store (t + 3 * (q - 1) + 2) (3 * (q - 1) + 2) (3 * q - eof) (mb2L_ok va vb vc vd Va Vb Vc Vd) NS2.
            step. eapply EPI. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; assumption. }
          ck1_branch_blt (t + 3 * (q - 1) + 2) v'' V1'' V2'' Ha'' KC. }
        ck1_branch_blt (t + 3 * (q - 1) + 1) v' V1' V2' Ha' KB. }
      ck1_branch_blt (t + 3 * (q - 1)) v V1 V2 Ha KA.
    - (* [comment removed for export] *)
      step. step. if_cases EQ1; zify_cond EQ1.
      + (* [comment removed for export] *)
        reacc_t. step. fbr. zstep. zstep. ck1_load ACT (t + 3 * (q - 1)) v V1 V2 Ha.
        ck_K 13 0x422d6c KA.
        { intros tv. red_tset.
          zstep. arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * q - eof) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
          eapply EPI. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; assumption. }
        ck1_branch_blt (t + 3 * (q - 1)) v V1 V2 Ha KA.
      + (* [comment removed for export] *)
        reacc_t. zstep. zstep. step. fbr. zstep. zstep. ck1_load ACT (t + 3 * (q - 1)) v V1 V2 Ha.
        ck_K 5 0x422cd4 KA.
        { intros tv. red_tset.
          (* [comment removed for export] *)
          zstep. arr_store (t + 3 * (q - 1)) (3 * (q - 1)) (3 * (q - 1) + 1) (mb0L_ok va vb vc vd Va Vb Vc Vd) NS0.
          (* [comment removed for export] *)
          clear ACT. reacc_t. zstep. zstep. ck1_load ACT (t + 3 * (q - 1) + 1) v' V1' V2' Ha'.
          ck_K 12 0x422cec KB.
          { intros tv'. red_tset.
            (* [comment removed for export] *)
            zstep. arr_store (t + 3 * (q - 1) + 1) (3 * (q - 1) + 1) (3 * q - eof) (mb1L_ok va vb vc vd Va Vb Vc Vd) NS1.
            step. eapply EPI. split; [assumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; assumption. }
          ck1_branch_blt (t + 3 * (q - 1) + 1) v' V1' V2' Ha' KB. }
        ck1_branch_blt (t + 3 * (q - 1)) v V1 V2 Ha KA.
  Qed.
End ALAST.

Section ATOP2.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].
  Local Ltac at_pc2 P := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let b := eval vm_compute in (Z.eqb pc P) in lazymatch b with true => idtac | false => fail end end.
  Local Ltac stepto2 P := repeat (tryif at_pc2 P then fail else step).

  (* [comment removed for export] *)
  Lemma adb_disp_loop :
    forall (ra spw gp tp x7 s0 x9 x13 x15 x28 x29 x30 x31 a1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a q : Z),
      2 <= q <= 16 -> 0 < a -> a + 92 <= 2^47 ->
      evt asegs (fun ms' => exists (y9 y13 y15 : word),
          ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q - 4)) (Z_to_bv 64 0) s0 y9 (Z_to_bv 64 (a + 4)) a1 a1 y13 a4 y15
                        (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 (-1)))
                   F (Z_to_bv 64 DB_L3) fc None m (seg_rom asegs))
        (MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 (4 * q)) x7 s0 x9 (Z_to_bv 64 (a + 4)) a1 (Z_to_bv 64 (Z.land (4 * q) 3)) x13 a4 x15
                 (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom asegs)).
  Proof.
    intros until q. intros QR POS AB. unfold DB_J.
    change (Z.land (4 * q) 3) with (Z.land (4 * q) (2^2 - 1)). rewrite zb_land_mask by lia. change (2^2) with 4.
    replace ((4 * q) mod 4) with 0 by (rewrite Z.mul_comm, Z.mod_mul; lia).
    step. if_lit. repeat step. rewrite ?Z.add_0_r, ?(unsigned_lit (4 * q)) by lia. rewrite (bv_swrap_small 32 (4 * q)) by (change (bv_half_modulus 32) with 2147483648%Z; lia). fbr.
    repeat step. rewrite (unsigned_lit (4 * q)) by lia. rewrite (bv_swrap_small 32 (4 * q + -4)) by (change (bv_half_modulus 32) with 2147483648%Z; lia). fbr.
    repeat step. if_cases KQ; zify_cond KQ; try rewrite ?signed_lit in KQ by lia.
    - exfalso; lia.
    - stepto2 DB_L3. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma adb_disp_one :
    forall (ra spw gp tp x7 s0 x9 x13 x15 x28 x29 x30 x31 a1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      0 < a -> a + 92 <= 2^47 ->
      evt asegs (fun ms' => exists (y13 : word),
          ms' = MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 0) x7 s0 x9 (Z_to_bv 64 (a + 4)) a1 (Z_to_bv 64 4) y13 a4 (Z_to_bv 64 0)
                        (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 DB_LAST) fc None m (seg_rom asegs))
        (MS (mkR ra spw gp tp (Z_to_bv 64 18446744073708761311) (Z_to_bv 64 4) x7 s0 x9 (Z_to_bv 64 (a + 4)) a1 (Z_to_bv 64 (Z.land 4 3)) x13 a4 x15
                 (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 DB_J) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold DB_J. change (Z.land 4 3) with 0.
    step. if_lit. repeat step. if_lit. repeat step. if_lit. repeat step. if_lit.
    stepto2 DB_LAST. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma adecblock_ok_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a t q eof lo nn line : Z) (raw tj : list byte),
      rw_cells asegs m a (ctx_chunk nn raw line) -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> ACONST m ->
      1 <= q <= 16 -> 0 <= eof <= 2 ->
      Forall b64_saved (map bv_unsigned (firstn (Z.to_nat (4 * q)) raw)) ->
      u8arr asegs m t tj -> 0 < t -> 3 * q <= Z.of_nat (length tj) -> (a + 92 <= t \/ t + Z.of_nat (length tj) <= a) ->
      (t + Z.of_nat (length tj) <= lo \/ bv_unsigned sp <= t) ->
      accessible m t (Z.of_nat (length tj)) -> (t + Z.of_nat (length tj) <= ALOWSH_LO \/ AHI_LO <= t) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (adb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (3 * q - eof)
                   (fun m' => munch [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + Z.of_nat (length tj))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                              /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' a (ctx_chunk nn raw line)
                              /\ exists bs', u8arr asegs m' t bs' /\ length bs' = length tj
                                   /\ firstn (Z.to_nat (3 * q - eof)) bs' = map b8 (firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw)))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 t) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 eof) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_evp_decodeblock_int) fc None m (seg_rom asegs)).
  Proof.
    intros until tj. intros CTX POS AL BL CEIL ACC AC QR ER SAVED ARR TP0 TJ ASEP TSEP ACT NSHt ST LO MI RAE.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). acb.
    pose proof (u8arr_bound _ _ _ _ ARR) as TB.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    assert (L80 : length raw = 80%nat) by (destruct CTX as [[WF _] _]; cbn in WF; tauto).
    eapply evt_cut; [eapply adb_p1; [exact POS| exact AL| exact BL| exact CEIL| exact ACC| exact AC| exact ST| exact LO| exact MI]|].
    intros ms1 (m1 & j8 & x15 & x17 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CTX1 : rw_cells asegs m1 a (ctx_chunk nn raw line)).
    { eapply rw_cells_transport; [exact CTX| exact MU1| exact WM1|]. unfold ctx_chunk. cbn [cells_size csize Nat.add length disjoint_from]. split; [lia| exact I]. }
    assert (ACC1 : accessible m1 a 92).
    { eapply accessible_across; [exact ACC| exact MU1|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]. }
    assert (ACT1 : accessible m1 t (Z.of_nat (length tj))).
    { eapply accessible_across; [exact ACT| exact MU1|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]. }
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]. }
    eapply evt_cut; [eapply adb_p2; [exact CTX1| exact POS| exact AL| exact BL| exact ACC1| exact AC1| lia| exact SAVED| exact MI1]|].
    intros ms2 (x7 & x9 & x13 & x15' & x28 & x29 & x30 & x31 & ->).
    pose proof (ctx_raw _ _ _ _ _ _ CTX1) as RAW1.
    assert (ARR1 : u8arr asegs m1 t tj) by (eapply u8arr_transport; [exact ARR| exact MU1| exact WM1| cbn; lia]).
    assert (AR3 : 0 < a /\ a mod 16 = 0 /\ a + 92 <= aceil) by (split; [exact POS| split; [exact AL| exact BL]]).
    assert (I0 : INV (a + 4) t q raw tj m1 m1 tj 0).
    { split; [exact RAW1|]. split; [exact ARR1|]. split; [reflexivity|]. split; [apply copied_0; symmetry; apply (SRC_length a q raw tj AR3 L80 QR TJ)|].
      split; [exact MI1|]. split; [apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    assert (FIN : forall m2 bs2 (y6 y7 y9 y12 y13 y18 y19 y20 y21 y28 y29 y30 y31 : word),
      INV (a + 4) t q raw tj m1 m2 bs2 (3 * (q - 1)) ->
      evt asegs (adb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (3 * q - eof)
                   (fun m' => munch [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + Z.of_nat (length tj))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                              /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' a (ctx_chunk nn raw line)
                              /\ exists bs', u8arr asegs m' t bs' /\ length bs' = length tj
                                   /\ firstn (Z.to_nat (3 * q - eof)) bs' = map b8 (firstn (Z.to_nat (3 * q - eof)) (groups_bytes (vs q raw)))))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 18446744073708761311) y6 y7 sp y9 (Z_to_bv 64 (a + 4 + 4 * (q - 1))) (Z_to_bv 64 (t + 3 * (q - 1))) y12 y13 (Z_to_bv 64 eof)
                 (Z_to_bv 64 (3 * (q - 1))) (Z_to_bv 64 ASHADOW_BASE) (Z_to_bv 64 A_data_ascii2bin) y18 y19 y20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F (Z_to_bv 64 DB_LAST) fc None m2 (seg_rom asegs))).
    { intros m2 bs2 y6 y7 y9 y12 y13 y18 y19 y20 y21 y28 y29 y30 y31 I2.
      eapply evt_mono.
      { eapply (alast_grp ra sp gp tp s6 s7 s8 s9 s10 s11 F fc a (a + 4) t q eof raw tj m1); try eassumption; try lia. }
      intros ms3 (m3 & bs3 & z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & I3 & ST3).
      destruct I3 as (RAW3 & ARR3 & LEN3 & CP3 & MI3 & MU3 & WM3). unfold W in MU3.
      unfold adb_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m3. split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; lia. }
      split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply rw_cells_transport; [exact CTX1| exact MU3| exact WM3|]. unfold ctx_chunk. cbn. lia. }
      exists bs3. split; [exact ARR3|]. split; [exact LEN3|].
      destruct CP3 as [_ CP3]. rewrite CP3. unfold SRC.
      assert (LG : length (map b8 (groups_bytes (vs q raw))) = (3 * Z.to_nat q)%nat).
      { rewrite length_map. apply groups_bytes_length. unfold vs. rewrite !length_map, length_firstn. lia. }
      rewrite firstn_app, LG, firstn_map. replace (Z.to_nat (3 * q - eof) - 3 * Z.to_nat q)%nat with 0%nat by lia.
      cbn [firstn]. rewrite app_nil_r. reflexivity. }
    destruct (Z.eq_dec q 1) as [Q1|QN].
    - (* [comment removed for export] *)
      subst q. change (4 * 1) with 4.
      eapply evt_cut; [eapply adb_disp_one; lia|]. intros ms2 (y13 & ->).
      replace (t + 3 * (1 - 1)) with t in FIN by lia. replace (a + 4 + 4 * (1 - 1)) with (a + 4) in FIN by lia.
      replace (3 * (1 - 1)) with 0 in FIN by lia. change (3 * 1) with 3 in FIN.
      rewrite ASHADOW_BASE_val in FIN. eapply FIN. exact I0.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply adb_disp_loop; lia|]. intros ms2 (y9 & y13 & y15 & ->).
      eapply evt_cut.
      { replace (Z_to_bv 64 t) with (Z_to_bv 64 (t + 3 * 0)) by (f_equal; lia).
        eapply (al3_loop ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp sp s6 s7 s8 s9 s10 s11 F fc a (a + 4) t q eof raw tj m1) with (k := Z.to_nat (q - 2)) (g := 0);
          try eassumption; try lia. }
      intros ms3 (m3 & bs3 & z6 & z7 & z9 & z12 & z13 & z18 & z19 & z20 & z21 & z28 & z29 & z30 & z31 & -> & I3).
      eapply FIN. exact I3.
  Qed.
End ATOP2.
