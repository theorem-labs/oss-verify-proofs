(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsAtomics AsDepotInv AsDepotHash AsDepotLock AsDepotStore.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma srliw16_small : forall x, 0 <= x < 2^16 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 16) = 0.
Proof.
  intros x Hx. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2, Z.div_small by lia. apply swrap32_small. lia.
Qed.

Lemma land_ffff_small : forall x, 0 <= x < 2^16 -> Z.land x 65535 = x.
Proof. intros x Hx. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma land_7fffffff_small : forall x, 0 <= x < 2^31 -> Z.land x 2147483647 = x.
Proof. intros x Hx. change 2147483647 with (Z.ones 31). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FIND.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (d : depot) (h : Z) (m1 : word -> option byte).
  Hypothesis WF : d_wf d.
  Hypothesis DM : depot_mem asegs d m1.
  Hypothesis HR : 0 <= h < 2^64.
  Hypothesis MI : mem_inv asegs m1.

  Let b := bucket h.

  Lemma find_loop_code : forall (l2 l1 : list Z) Q
      (x1 x2 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x25 x26 x27 x28 x29 x30 x31 : word),
    d_chain d b = l1 ++ l2 -> (forall x, In x l1 -> d_hash d x <> h) ->
    (forall a1 a2, d_find d h <> 0 ->
       evt asegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (wz (d_find d h)) a1 a2 x13 x14 x15 x16 x17 x18 (wz h) x20 x21 (wz 65535) x23 (wz DEP_MAP1) x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x1e13c0) fc None m1 (seg_rom asegs))) ->
    (forall a0 a2, d_find d h = 0 ->
       evt asegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 a0 (wz 0) a2 x13 x14 x15 x16 x17 x18 (wz h) x20 x21 (wz 65535) x23 (wz DEP_MAP1) x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x1e1314) fc None m1 (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (wz (hd 0 l2)) x12 x13 x14 x15 x16 x17 x18 (wz h) x20 x21 (wz 65535) x23 (wz DEP_MAP1) x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x1e12bc) fc None m1 (seg_rom asegs)).
  Proof.
    induction l2 as [|x l2 IH]; intros l1 Q x1 x2 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x25 x26 x27 x28 x29 x30 x31 CH NH KF KN.
    - (* [comment removed for export] *)
      cbn [hd]. unfold wz in *.
      step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
      apply KN. unfold d_find. fold b. rewrite CH, find_hash_app_skip by exact NH. reflexivity.
    - cbn [hd]. unfold wz in *.
      assert (XIN : In x (d_chain d b)) by (rewrite CH; apply in_or_app; right; left; reflexivity).
      pose proof (wf_chain d WF b x XIN) as [XR XB].
      pose proof (wf_ids d WF) as IR. pose proof (wf_nb d WF) as NBR. pose proof (wf_hash d WF x XR) as XH.
      pose proof (dm_map1 asegs d m1 DM) as MAP1. pose proof (dm_node asegs d m1 DM x XR) as ND. unfold wz in MAP1, ND.
      rewrite XB, CH in ND.
      pose proof (wf_nodup d WF b) as NDP. rewrite CH in NDP. pose proof (NoDup_app_cons _ _ _ NDP) as [XN1 _].
      rewrite (link_of_app l1 x l2 XN1) in ND.
      assert (L2R : 0 <= hd 0 l2 < 65536).
      { destruct l2 as [|y l2']; cbn; [lia|]. assert (YIN : In y (d_chain d b)) by (rewrite CH; apply in_or_app; right; right; left; reflexivity).
        pose proof (wf_chain d WF b y YIN). lia. }
      (* [comment removed for export] *)
      step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
      step. zstep. rewrite srliw16_small by lia. zstep. zstep. step.
      step. if_cases K1; zify_cond K1. { exfalso. unfold AIMG_TOP in NBR. lia. }
      (* [comment removed for export] *)
      zstep. zstep. rewrite (Z.mod_small x 4294967296) by lia. zstep. rewrite land_ffff_small by lia.
      zstep. zstep. rewrite (Z.shiftl_mul_pow2 x 4) by lia. replace (d_nb d + x * 2^4) with (d_nb d + 16 * x) by lia.
      remember (d_nb d + 16 * x) as NA eqn:ENA.
      step. step. rewrite sx32_wz by lia. unfold wz. subst NA.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (IH (l1 ++ [x])).
        * rewrite CH, <- app_assoc. reflexivity.
        * intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [apply NH; exact Hy| lia].
        * exact KF.
        * exact KN.
      + (* [comment removed for export] *)
        step.
        assert (FD : d_find d h = x).
        { unfold d_find. fold b. rewrite CH, find_hash_app_skip by exact NH. cbn [find_hash].
          rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
        rewrite <- FD. apply KF. lia.
  Qed.
End FIND.


Lemma shl44_shr42 : forall h, 0 <= h -> Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = 4 * bucket h.
Proof.
  intros h Hh. unfold bucket. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^20 * 2^44). rewrite Z.mul_mod_distr_r by lia.
  change (2^44) with (4 * 2^42). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DEPOT_PUT : Z := 0x1e119c.

Definition put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (d : depot) (h n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (d_putid d h)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, bv_unsigned sp) :: depot_W d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ DEPOT asegs (d_put d h n) m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section PUT.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo TR n h : Z) (T : list Z) (rest : list word) (d : depot) (m : word -> option byte).
  Hypothesis NT   : n = Z.of_nat (length T).
  Hypothesis HH   : h = depot_hash T.
  Hypothesis NR   : 1 <= n <= 254.
  Hypothesis RNG  : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LO   : lo + 224 <= bv_unsigned sp.
  Hypothesis IMGLO: AIMG_TOP <= lo.
  Hypothesis TRR  : bv_unsigned sp <= TR /\ TR + 8 * n <= 2^64.
  Hypothesis CAP  : d_ids d + 1 < LIM_IDS /\ d_frames d + n + 1 <= LIM_FRAMES.
  Hypothesis BELOW: d_nb d + 16 * LIM_IDS <= lo /\ d_sb d + 8 * LIM_FRAMES <= lo.

  Theorem put_spec : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    DEPOT asegs d m ->
    u64arr asegs m TR (map wz T ++ rest) ->
    stk asegs m lo (bv_unsigned sp) ->
    mem_inv asegs m ->
    evt asegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d h n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz DEP) (wz TR) (wz n) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DEPOT_PUT) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros [W DM] BUF ST MI.
    pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2. pose proof (wf_nb d W) as I3. pose proof (wf_sb d W) as I4. pose proof (wf_nbsb d W) as I5.
    pose proof (bucket_range h) as BR. pose proof (chain_hd_range d (bucket h) W) as V0R.
    assert (HR : 0 <= h < 2^64) by (rewrite HH; apply depot_hash_range).
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof DM as DM0. destruct DM as [TTAB NUI MAP1 TNODE TSID TFREE TF DATA STO TSPACE].
    destruct TSPACE as (junk & SPACE & LJ).
    (* [comment removed for export] *)
    pose proof (TTAB (bucket h) BR) as TAB0. remember (7915480 + 4 * bucket h) as PB eqn:EPB.
    destruct (TFREE (d_ids d + 1) ltac:(lia)) as (j1 & j2 & j3 & NDC). remember (d_nb d + 16 * (d_ids d + 1)) as ND eqn:END.
    unfold DEPOT_PUT, AIMG_TOP, wz in *.
    carve_frame 112%nat ST.
    (* [comment removed for export] *)
    do 12 step. step. step. step. step.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    zstep. rewrite Z.add_0_r, (swrap32_small n) by lia.
    step. step. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
    step. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (DM1 : depot_mem asegs d mm) by (eapply depot_mem_stack; [exact W|exact DM0|exact MU|exact WM|lia|lia|lia]) end.
    (* [comment removed for export] *)
    eapply hash_phase_code; [exact NT|exact BUF|lia|exact RNG|assumption|lia|].
    intros a0' a1' a2' a4' a5' a6'. rewrite <- HH. unfold wz.
    (* [comment removed for export] *)
    zstep. zstep. rewrite shl44_shr42 by lia. zstep. rewrite <- EPB.
    step. rewrite sx32_wz by lia. unfold wz.
    (* [comment removed for export] *)
    zstep. zstep. step. zstep. rewrite land_7fffffff_small by lia. zstep. zstep. step.
    (* [comment removed for export] *)
    eapply (find_loop_code gp tp F fc d h _ W DM1 HR (d_chain d (bucket h)) []); [reflexivity| intros x [] |  | ].
    { (* [comment removed for export] *)
      intros a1_ a2_ FNZ. unfold wz.
      do 12 step. release_frame FR ST (bv_unsigned sp). step.
      apply evt_done. unfold put_post. do 15 eexists.
      split. { unfold d_putid. rewrite (proj2 (Z.eqb_neq _ _) FNZ). reflexivity. }
      split. { eapply munch_weaken; [|exact MU]. unfold sub_fp, depot_W. cbn [outside]. intros x Hx. (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]). }
      split; [exact WM|]. split; [assumption|].
      split. { unfold d_put. rewrite (proj2 (Z.eqb_neq _ _) FNZ). split; [exact W|].
               eapply depot_mem_stack; [exact W|exact DM0|exact MU|exact WM|lia|lia|lia]. }
      exact ST. }
    (* [comment removed for export] *)
    intros a0_ a2_ FZ. unfold wz.
    apply (munch_weaken _ (put_W lo (bv_unsigned sp) (bucket h) (d_nb d) (d_ids d + 1) (d_sb d) (d_frames d) n)) in MU.
    2:{ unfold sub_fp, put_W. cbn [outside]. intros x Hx. (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]). }
    unfold put_W in MU. rewrite <- EPB, <- END in MU.
    (* [comment removed for export] *)
    step. step.
    callU (lock_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ PB (hd 0 (d_chain d (bucket h))) lo).
    all: try (rewrite ?unsigned_lit by lia; first [eassumption | reflexivity | lia]).
    subst x2. unfold wz in *. rename PC into TAB0.
    (* [comment removed for export] *)
    step. step. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    remember 7849928 as ATF eqn:ETF in TF. remember 7849944 as ADATA eqn:EDATA in DATA. remember 7849952 as ASTO eqn:ESTO in STO.
    step. zstep. step. astep. rewrite ?sx32_wz by lia. rewrite ?unsigned_lit, ?low32_lit in NUI by lia. unfold wz in *.
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (d_ids d + 1)) by lia.
    zstep. zstep. rewrite (Z.mod_small (d_ids d + 1) 4294967296) by lia.
    step. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. }
    step.
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftr_div_pow2 (d_ids d + 1) 16), (Z.div_small (d_ids d + 1) (2^16)) by lia.
    zstep. zstep. step. step. if_cases K5; zify_cond K5. { exfalso. lia. }
    (* [comment removed for export] *)
    zstep. rewrite land_ffff_small by lia. zstep. zstep.
    rewrite (Z.shiftl_mul_pow2 (d_ids d + 1) 4) by lia. replace (d_nb d + (d_ids d + 1) * 2^4) with ND by lia.
    (* [comment removed for export] *)
    zstep. step. step. step. step.
    subst ATF ADATA ASTO.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_C8_C4C4 asegs _ _ [CB 8 _; C8 _] n _ ltac:(lia))) in FR.
    rewrite (Z.shiftr_div_pow2 n 32), (Z.div_small n (2^32)) in FR by lia. cbn [app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [CB 8 _] _)) in FR. destruct FR as [FR0 FR1].
    cbn [cells_size csize Nat.add] in FR1. change (Z.of_nat 8) with 8 in FR1.
    apply (proj1 (rw_cells_app _ _ _ [C8 _; C4 _; C4 _] _)) in FR1. destruct FR1 as [ARGC FR2].
    cbn [cells_size csize Nat.add] in FR2. change (Z.of_nat 16) with 16 in FR2.
    replace (bv_unsigned sp + -112 + 8 + 16) with (bv_unsigned sp + -88) in FR2 by lia.
    replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in ARGC by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SRC : bytes_at asegs mm TR (u64s (map wz T))) end.
    { lazymatch type of BUF with u64arr _ ?mm _ _ => pose proof (proj1 (u64arr_u8arr asegs mm TR _) BUF) as U end.
      rewrite u64s_app in U. apply u8arr_app in U. destruct U as [[U _] _]. exact U. }
    assert (LSRC : Z.of_nat (length (u64s (map wz T))) = 8 * n) by (rewrite u64s_length, length_map; lia).
    callU (nstore_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ F fc lo (bv_unsigned sp + -104) ND TR (d_sb d) (d_frames d) n h (u64s (map wz T)) junk).
    all: try (rewrite ?unsigned_lit by lia; unfold AIMG_TOP; first [eassumption | reflexivity | lia]).
    destruct PC2 as (junk' & SPACE' & LJ'). rename PC into NDC. rename PC0 into TF. rename PC1 into STO. unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step.
    step. if_cases K6; zify_cond K6. 2:{ exfalso. revert K6. rewrite ?unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FR : rw_cells asegs mm (bv_unsigned sp + -112)
                ([CB 8 (firstn 8 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 (firstn 80 (firstn 88 (firstn 96 (firstn 104 junk0))))))))))))]
                 ++ [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] ++ [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) end.
    { apply rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
      apply rw_cells_app. split; [replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact ARGC|].
      cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16.
      replace (bv_unsigned sp + -112 + 8 + 16) with (bv_unsigned sp + -88) by lia. exact FR2. }
    clear FR0 ARGC FR2. cbn [app] in FR.
    do 12 step.
    lazymatch goal with ST : stk asegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end. step.
    (* [comment removed for export] *)
    apply evt_done. unfold put_post. do 15 eexists.
    split. { unfold d_putid. rewrite FZ. cbn [Z.eqb]. reflexivity. }
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp, depot_W. cbn [outside]. intros y Hy. repeat split; try exact I; (first [clear - Hy EPB BR END V0R CAP I2; lia | lia]). }
    split; [exact WM|]. split; [assumption|].
    split. { unfold d_put. rewrite FZ. cbn [Z.eqb]. split.
             - apply d_insert_wf; try assumption; lia.
             - eapply (depot_insert_mem asegs d h n m _ lo (bv_unsigned sp)); try eassumption; try lia.
               all: try (unfold put_W; rewrite <- ?EPB, <- ?END; eassumption).
               all: try (rewrite <- EPB; exact TAB0). all: try (rewrite <- END; exact NDC). all: try (rewrite LJ'; exact LJ).
               }
    assumption.
  Qed.
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STACK_DEPOT_PUT : Z := 0x1e117c.

Theorem depot_put_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo TR : Z) (T : list Z) (rest : list word) (d : depot) (m : word -> option byte),
  let n := Z.of_nat (length T) in
  1 <= n <= 254 -> Forall (fun x => 0 <= x < 2^64) T ->
  lo + 224 <= bv_unsigned sp -> AIMG_TOP <= lo -> bv_unsigned sp <= TR -> TR + 8 * n <= 2^64 ->
  d_ids d + 1 < LIM_IDS -> d_frames d + n + 1 <= LIM_FRAMES ->
  d_nb d + 16 * LIM_IDS <= lo -> d_sb d + 8 * LIM_FRAMES <= lo ->
  DEPOT asegs d m ->
  u64arr asegs m TR (map wz T ++ rest) ->
  stk asegs m lo (bv_unsigned sp) ->
  mem_inv asegs m ->
  evt asegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d (depot_hash T) n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz TR) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STACK_DEPOT_PUT) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros n NR RNG LO IMGLO TR1 TR2 C1 C2 B1 B2 DEPO BUF ST MI. unfold STACK_DEPOT_PUT, wz.
  step. step. zstep. step. step. step. step. step.
  eapply (put_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo TR n (depot_hash T) T rest d m); try eassumption; try reflexivity; try lia.
Qed.
