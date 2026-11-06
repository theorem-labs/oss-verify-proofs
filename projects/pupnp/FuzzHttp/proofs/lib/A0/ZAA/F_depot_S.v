(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import ADepot ATacA ACells F_imemcpy F_depot_L.
Import ListNotations.
Open Scope Z_scope.

Lemma amo_addw_bytes : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= a + b < 2^64 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (wz a)))) (low32 (wz b)))) = le4 (wz (a + b)).
Proof.
  intros a b Ha Hb Hab. cbn [amo_val]. rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite low32_unsigned. rewrite !unsigned_lit by lia. change (2 ^ Z.of_N 32) with (2^32).
  unfold le4. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite <- (Z_to_le_bytes_mod 4 (a + b) 32) by (cbn; lia). f_equal.
  rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma amo_addw_bytes_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^32 -> 0 <= a + b < 2^64 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (wz a)))) (Z_to_bv 32 b))) = le4 (wz (a + b)).
Proof.
  intros a b Ha Hb Hab. cbn [amo_val]. rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  unfold le4. rewrite !unsigned_lit by lia. rewrite Z_to_bv_unsigned. change (2 ^ Z.of_N 32) with (2^32).
  unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite <- (Z_to_le_bytes_mod 4 (a + b) 32) by (cbn; lia). f_equal.
  rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.

Definition imemcpy_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (src : list byte) (S : Z) (a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src.
Lemma imemcpy_spec_z :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n : Z) (src junk : list byte),
    rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> length src = Z.to_nat n ->
    (S + n <= D \/ D + n <= S) -> 0 <= D -> D + n < 2^64 -> 0 <= S -> S + n < 2^64 -> 0 <= n < 2^63 ->
    mem_inv asegs m ->
    evt asegs (imemcpy_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n src S a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz imemcpy_entry) fc None m (seg_rom asegs)).
Proof.
  intros. pose proof (imemcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as P.
  rewrite !unsigned_lit in P by lia.
  eapply evt_mono; [apply P; first [assumption| lia]|].
  intros ms' Q. unfold imemcpy_post, imemcpy_post_z in *. rewrite !unsigned_lit in Q by lia. exact Q.
Qed.

Section STO.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q SS0v total ARGS PACKP TR : Z) (R : Z) (m0 : mem) (ws : list word) (tr : list Z).
  Notation n := (Z.of_nat (length tr)).
  Notation W := [(q - 80, q); (SSA, SSA + 8); (SSD + 8, SSD + 12); (PACKP, PACKP + 8); (SS0v + 8 * total, SS0v + 8 * total + 8 + 8 * n)].

  Definition ssstore_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a3 a4 t0 t1 m' junk', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (total + 1)) (wz total) (wz 0) a3 a4 (wz (n + 1)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' SSA [C8 (wz (total + n + 1))] /\ rw_cells asegs m' SSD [C8 (wz SS0v); C4 (wz (total + n + 1))]
      /\ rw_cells asegs m' PACKP [C8 (wz 0)]
      /\ rw_cells asegs m' ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)]
      /\ rw_cells asegs m' (SS0v + 8 * (total + n + 1)) [CB (Z.to_nat (R - 8 - 8 * n)) junk']
      /\ u64arr asegs m' TR ws
      /\ stk asegs m' lo q.

  #[using="Type"] Lemma ssstore_spec : forall lo (pk : word) (junk : list byte) t0 t1 a3 a4 a5,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 80 -> q mod 16 = 0 -> q <= 2^47 ->
    rw_cells asegs m0 SSA [C8 (wz total)] -> rw_cells asegs m0 SSD [C8 (wz SS0v); C4 (wz total)] ->
    rw_cells asegs m0 PACKP [C8 pk] -> q <= PACKP -> PACKP + 8 <= ARGS ->
    rw_cells asegs m0 ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)] -> ARGS + 16 <= TR ->
    u64arr asegs m0 TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    (1 <= length tr <= 30)%nat ->
    rw_cells asegs m0 (SS0v + 8 * total) [CB (Z.to_nat R) junk] -> 8 + 8 * n <= R -> SS0v + 8 * total + R <= alloc_ceiling ->
    0 <= total -> total + n + 1 < 2^20 -> 0x609000 <= SS0v ->
    mem_inv asegs m0 ->
    evt asegs (ssstore_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz SSA) (wz ARGS) (wz PACKP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x75f38) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo pk junk t0 t1 a3 a4 a5 ST CLO LO AL QH CT CD CP PQ PA CA ATR BUF TRW LEN TRH LTR SB RB SBC T0 TB S0L MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB.

    pose proof SB as SBT0.
    apply (rw_cells_split_CB asegs m0 _ [] (Z.to_nat R) junk [] [(8 + Z.to_nat (8 * n))%nat; (Z.to_nat R - 8 - Z.to_nat (8 * n))%nat]) in SBT0; [cbn [mk_CB_cells app] in SBT0| cbn [sum_nat]; lia].
    split_chunk SBT0 1%nat SBH0 SBT1. clear SBH0. rename SBT1 into SBT0.
    match type of SBT0 with rw_cells _ _ ?a _ => replace a with (SS0v + 8 * (total + n + 1)) in SBT0 by lia end.
    replace (Z.to_nat R - 8 - Z.to_nat (8 * n))%nat with (Z.to_nat (R - 8 - 8 * n)) in SBT0 by lia.
    match type of SBT0 with ?P => change P with (id P) in SBT0 end.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    do 8 sstep.
    zstep.
    zstep.   rewrite (sx32_lit n) by lia.
    zstep.   change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep.   rewrite Z.lor_0_r.
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0 LTR. clear. intros. rewrite ?unsigned_lit in K0 by lia. lia. }
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. rewrite ?unsigned_lit in K1 by lia. lia. }
    zstep. zstep.
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2 LTR. clear. intros. rewrite ?unsigned_lit in K2 by lia. lia. }
    sstep.
    sstep.
    zstep. zstep. zstep. zstep. zstep.
    zstep.
    split_chunk FR 1%nat FI FR2.
    call (ssalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -64) SS0v total (n + 1) (q + -64) _ lo).
    all: side (try (first [ eassumption | lia ])).
    zstep. if_cases K3; zify_cond K3. { exfalso. revert K3 S0L T0 SBC ACR. clear. intros. rewrite ?unsigned_lit in K3 by lia. lia. }
    zstep.   change (bv_swrap 32 (Z.shiftl 0 8)) with 0.
    zstep.
    zstep.   rewrite Z.lor_0_l.

    set (sb := SS0v + 8 * total) in *. assert (Hsb : sb = SS0v + 8 * total) by reflexivity. clearbody sb.
    match goal with H : rw_cells asegs ?mm sb [CB _ junk] |- _ =>
      apply (rw_cells_split_CB asegs mm sb [] (Z.to_nat R) junk [] [8%nat; Z.to_nat (8 * n); (Z.to_nat R - 8 - Z.to_nat (8 * n))%nat]) in H;
      [ cbn [mk_CB_cells app] in H | cbn [sum_nat]; lia ] end.
    sstep.
    zstep.
    zstep.   rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. replace (n * 8) with (8 * n) by lia.
    zstep.
    match goal with H : rw_cells asegs ?mm sb _ |- _ => split_chunk H 1%nat SBH SB2 end.
    split_chunk SB2 1%nat SBP SBR. clear SBR.
    match goal with H : u64arr asegs ?mm TR ws |- _ =>
      pose proof (proj1 H) as SRC; rewrite <- (firstn_skipn (length tr) ws) in SRC; rewrite u64s_app in SRC;
      apply bytes_at_app in SRC; destruct SRC as [SRC _]; rewrite TRW in SRC end.
    call (imemcpy_spec_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc _ (sb + 8) TR (8 * n) (u64s (map wz tr))).
    all: side (try (first [ eassumption | lia ])).
    { rewrite u64s_length, length_map. lia. }
    zstep.
    zstep.
    zstep.
    match goal with |- context [Z.land (Z.shiftr total 16) ?c] =>
      replace (Z.land (Z.shiftr total 16) c) with 0
        by (change c with (Z.shiftl 1152921504606846975 4); symmetry; apply land_low_shiftl; [lia|];
            rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) end.
    zstep. zstep.
    replace (SSA + 0 + 24) with 1595360 by reflexivity.
    amo_step.
    rewrite (amo_addw_bytes total (n + 1)) by lia. mem_after_store.
    rewrite (sx32_lit total) by lia.
    zstep. zstep. zstep.
    rewrite (Z.mod_small total 4294967296) by lia.
    zstep.
    zstep.
    zstep.
    match goal with H : rw_cells asegs ?mm (q + -64) [C8 (wz total)] |- _ =>
      apply (rw_cells_C8_C4C4 mm (q + -64) [] total []) in H; [cbn [app] in H| lia] end.
    zstep.   rewrite (sx32_lit total) by lia.
    zstep.
    match goal with |- context [Z.b2z ?c] =>
      replace (Z.b2z c) with 0 by (change 1048576 with (2^20); rewrite (zb_lxor_pow2_small (n + 1 + total) 20) by lia;
                                 symmetry; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.
    zstep.
    sstep.
    zstep.   rewrite (STRW_merge.swrap32_small (total + 1)) by lia.

    match goal with H : rw_cells asegs ?mm (q + -64) [C4 (wz total); C4 (wz 0)] |- _ =>
      apply (rw_cells_C4C4_C8 mm (q + -64) [] total []) in H; [cbn [app] in H| lia]; join_chunks H FR2 FR end.
    do 7 zstep. zstep. replace (q + -64 + 64) with q by lia. zstep.
    match goal with H : stk asegs _ lo _ |- _ => release_frame FR H q end.
    unfold id in SBT0.
    lazymatch goal with MUf : munch _ m0 ?mf, WMf : wmono asegs m0 ?mf |- _ =>
      pose proof (rw_cells_transport asegs _ m0 mf _ _ SBT0 MUf WMf ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as SBT end.
    subst sb.
    apply evt_done. unfold ssstore_post. eexists _, _, _, _, _, _. split; [reflexivity|].
    replace (total + (n + 1)) with (total + n + 1) in * by lia.
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End STO.

Section NST.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (HV : word).
  Variables (q SS0v total ARGS TR ND : Z) (R : Z) (m0 : mem) (ws : list word) (tr : list Z).
  Notation n := (Z.of_nat (length tr)).
  Notation W := [(q - 112, q); (SSA, SSA + 8); (SSD + 8, SSD + 12); (ND, ND + 16); (SS0v + 8 * total, SS0v + 8 * total + 8 + 8 * n)].

  Definition nstore_post (lo : Z) (j2 : list byte) : machine_state -> Prop :=
    fun ms' => exists a2 a3 a4 t0 t1 m' junk', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (total + 1)) (wz 0) a2 a3 a4 (wz (n + 1)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' SSA [C8 (wz (total + n + 1))] /\ rw_cells asegs m' SSD [C8 (wz SS0v); C4 (wz (total + n + 1))]
      /\ rw_cells asegs m' ND [C8 HV; CB 4 j2; C4 (wz (total + 1))]
      /\ rw_cells asegs m' ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)]
      /\ rw_cells asegs m' (SS0v + 8 * (total + n + 1)) [CB (Z.to_nat (R - 8 - 8 * n)) junk']
      /\ u64arr asegs m' TR ws
      /\ stk asegs m' lo q.

  #[using="Type"] Lemma nstore_spec : forall lo (j1 j2 j3 junk : list byte) t0 t1 a1 a4 a5,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 112 -> q mod 16 = 0 -> q <= 2^47 ->
    rw_cells asegs m0 SSA [C8 (wz total)] -> rw_cells asegs m0 SSD [C8 (wz SS0v); C4 (wz total)] ->
    rw_cells asegs m0 ND [CB 8 j1; CB 4 j2; CB 4 j3] -> 0x609000 <= ND -> ND + 16 <= alloc_ceiling ->
    rw_cells asegs m0 ARGS [C8 (wz TR); C4 (wz n); C4 (wz 0)] -> q + 8 <= ARGS -> ARGS + 16 <= TR ->
    u64arr asegs m0 TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    (1 <= length tr <= 30)%nat ->
    rw_cells asegs m0 (SS0v + 8 * total) [CB (Z.to_nat R) junk] -> 8 + 8 * n <= R -> SS0v + 8 * total + R <= alloc_ceiling ->
    0 <= total -> total + n + 1 < 2^20 -> 0x609000 <= SS0v ->
    (ND + 16 <= SS0v + 8 * total \/ SS0v + 8 * total + R <= ND) ->
    mem_inv asegs m0 ->
    evt asegs (nstore_post lo j2)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz ND) a1 (wz ARGS) HV a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x7824c) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo j1 j2 j3 junk t0 t1 a1 a4 a5 ST CLO LO AL QH CT CD CN NDL NDH CA AQ ATR BUF TRW LEN TRH LTR SB RB SBC T0 TB S0L NDS MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 32%nat ST. rewrite !E in *.
    do 3 sstep.
    zstep. zstep.
    sstep.
    sstep.
    zstep. zstep. zstep.
    zstep.
    split_chunk FR 1%nat F0 F1. split_chunk F1 1%nat FP F2.
    call (ssstore_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -32) SS0v total ARGS (q + -24) TR R _ ws tr lo).
    all: side (try (first [ eassumption | lia ])).
    zstep.
    sstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. clear. intros K0. rewrite ?unsigned_lit in K0 by lia. lia. }
    match goal with H : rw_cells asegs ?mm (q + -24) _ |- _ => join_chunks H F2 F1'; join_chunks F0 F1' FR end.
    zstep. zstep. zstep. replace (q + -32 + 32) with q by lia. zstep.
    match goal with H : stk asegs _ lo _ |- _ => release_frame FR H q end.
    apply evt_done. unfold nstore_post. eexists _, _, _, _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End NST.
