(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_leaves I_ikit R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_allocate1 R_prim_kit R_asan_malloc R_alalloc1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
    | H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition aligned_pc : Z := 0x8365c.

Definition aligned_A_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n T lo : Z) (tr : list Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp jq j0 : list byte) (mp m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x5b908) (Z_to_bv 64 (bv_unsigned sp + -2304)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 16) (Z_to_bv 64 (needed n + 16))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp + -2136))
                  (Z_to_bv 64 (0 + - (16))) (Z_to_bv 64 15) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x5fdc0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m mp /\ wmono asegs m mp
    /\ munch [(T + 3168, T + 3169); (bv_unsigned sp - 2320, bv_unsigned sp - 64)]%Z mp m' /\ wmono asegs mp m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [CB 8 jp]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))]
    /\ u64arr asegs m' (bv_unsigned sp + -2120) (wr_trace tr tb) /\ length tb = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -2136)
         [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 jq]
    /\ rw_cells asegs m' (bv_unsigned sp + -2176)
         [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x836cc)]
    /\ alloc_frame32 m' (bv_unsigned sp + -2304) (Z_to_bv 64 0x5c248) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 16) (Z_to_bv 64 16) (Z_to_bv 64 aligned_pc)
         (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11
    /\ rw_cells asegs m' (bv_unsigned sp + -2304) [CB 8 j0]
    /\ rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk asegs m' lo (bv_unsigned sp + -2304).

Lemma aligned_A_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n TCX T top bot lo : Z) (ch : list (Z * Z)) (tr : list Z),
  (1 <= n <= 2^31)%Z -> (n mod 16 = 0)%Z -> (rounded n mod 16 = 0)%Z -> (needed n + 16 <= 65536)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^63)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
  unwind_trace aligned_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  rw_cells asegs m 0x16a210 [C8 (Z_to_bv 64 0x2036e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x2036e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6ca000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (aligned_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x835c4) fc None m (seg_rom asegs)).
Proof.
  intros until tr. intros Hn HNm HR16 HN16 ST HLO HLOH HSP Hbt Htop CH TR G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl HT0 HT HTl HTT SC UW MI.
  apply box in CH.
  unfold kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell,
    g_rss_limit_exceeded in *.
  change (2119528 + 34)%Z with 2119562%Z in FUM.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
  move G60 at bottom. move GCF at bottom. move MX at bottom. move RZ at bottom. move KI at bottom. move K0 at bottom.
  move AI at bottom. move MCS at bottom. move RSS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
  move T0 at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)]%Z m) as MU0.
  pose proof (wmono_refl asegs m) as WM0.
  carve_frame 64%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
  carve_frame 8%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle_beginZ SP 64%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.

  apply box in MU0. apply box in WM0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(T + 3168, T + 3169); (SP - 2320, SP - 64)]%Z mm) as MU; pose proof (wmono_refl asegs mm) as WM;
    assert (CHm : chain_cells [(SP - 64, SP)]%Z mm (bv_unsigned s0) ch)
      by (apply (fun X => chain_cells_frame _ m mm _ _ X (unbox _ MU0) (unbox _ WM0));
          apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
    apply box in CHm
  end.
  do 5 zstep.
  sp_factsZ SP.
  do 5 zstep.
  zstep; fix_lit_store.
  zstep.
  zstep; fix_lit_store.
  zstep.
  call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
  all: try lia; try eassumption.
  zstep. zstep. ifT.
  zstep. zstep. zstep.
  do 5 zstep.
  call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
  all: try lia; try eassumption.
  do 5 zstep.
  assert (EB : Z.land (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) SP = SP).
  { change (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity. }
  rewrite EB. clear EB.
  zstep. zstep. ifT.
  do 6 zstep.
  zstep.

  apply (rw_cells_c8_split _ _ [] [] 0 ltac:(lia)) in FR3. cbn [app] in FR3.
  apply (rwc_app asegs _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)]) in FR3. destruct FR3 as (FR3a & FR3b).
  cbn [cells_size csize] in FR3b. replace (SP + -2128 + Z.of_nat (4 + 0))%Z with (SP + -2124)%Z in FR3b by lia.
  change 2040%nat with (8 * 255)%nat in FR2. apply ma_rw_cells_u64arr in FR2.
  apply (rwc_app asegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) in FR. destruct FR as (FRa & FRb).
  cbn [cells_size csize Nat.add] in FRb. replace (SP + -64 + Z.of_nat 48)%Z with (SP + -16)%Z in FRb by lia.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  unfold bv_modulus in RRA, RS0. cbn [Z.of_N] in RRA, RS0.
  sp_factsZ SP.
  lazymatch goal with H : rw_cells asegs ?mm (SP + -16) _ |- _ =>
    assert (CHw : chain_cells [(T + 3168, T + 3169); (SP - 2320, SP)]%Z m (bv_unsigned s0) ch)
      by (apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
    assert (MUw : munch [(T + 3168, T + 3169); (SP - 2320, SP)]%Z m mm)
      by (apply (munch_trans _ m m1 mm); [eapply munch_weaken; [| exact (unbox _ MU0)]; intros xw Hxw; cbn [outside] in *; lia
                                         | eapply munch_weaken; [| exact MU]; intros xw Hxw; cbn [outside] in *; lia]);
    apply (fun X => chain_cells_frame _ m mm _ _ X MUw (wmono_trans asegs _ _ _ (unbox _ WM0) WM)) in CHw;
    apply (chain_cells_weaken _ (uwi_W (SP + -2136) T (SP + -2144))) in CHw;
      [| intros a HDa; unfold uwi_W; cbn [disjoint_from] in *; lia];
    assert (CC : chain_cells (uwi_W (SP + -2136) T (SP + -2144)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
      by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
          split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia| exact CHw]) end.
  call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2136) 0x8365c SP top bot 30 lo TCX T
          ((bv_unsigned ra, bv_unsigned s0) :: ch) (ma_dec64 255 junk2) (Z_to_bv 64 0) _ tr).
  all: rewrite ?Esp; try lia; try eassumption; try apply ma_dec64_length.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- stack_cells _ _ _ _ => unfold stack_cells, off_t_stack_top, off_t_stack_switching; split; assumption
       | |- rw_cells _ _ (?X + -2136 + 8)%Z _ => replace (X + -2136 + 8)%Z with (X + -2128)%Z by lia; exact FR3a
       | |- u64arr _ _ (?X + -2136 + 16)%Z _ => replace (X + -2136 + 16)%Z with (X + -2120)%Z by lia; exact FR2
       | |- rw_cells _ _ (?X + -2136 + 2056)%Z _ => replace (X + -2136 + 2056)%Z with (X + -80)%Z by lia; exact FR1
       | |- evt _ _ _ => idtac
       end.
  rewrite ?Esp in *.
  do 4 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => carve_frame 32%nat H end end.
  zstep. do 4 (zstep; fix_lit_store). do 2 zstep.
  zstep. zstep. zstep. ifF.
  zstep. replace (Z.land n 15) with 0%Z by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; change (2 ^ 4)%Z with 16%Z; lia).
  zstep. ifF.
  do 6 zstep. zstep.
  clear MUw CHw CC.
  sp_factsZ SP.
  call (allocate_p1al_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n (SP + -2136) TCX T lo).
  all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  rewrite ?Esp2 in *.
  unfold aligned_A_post, aligned_pc. rewrite (unsigned_lit SP) by lia.
  replace (SP + -2176 + -128)%Z with (SP + -2304)%Z in * by lia.
  apply evt_done.
  lazymatch goal with H : exists j, rw_cells asegs _ _ [CB 8 j] |- _ => destruct H as (j0 & HJ0) end.
  do 11 eexists. exists (ma_dec64 255 junk2), junk0, junk5, j0, m1. eexists.
  split; [reflexivity|].
  pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
  split; [exact (unbox _ MU0)|]. split; [exact (unbox _ WM0)|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split.
  { apply (proj2 (rwc_app asegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
  split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. split; [apply ma_dec64_length|].
  split.
  { apply (proj2 (rwc_app asegs _ _ [C8 (Z_to_bv 64 (SP + -2120))] [C8 (Z_to_bv 64 (Z.of_nat (length tr)))])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add].
    apply (rw_cells_c44_join _ _ [] [] (Z.of_nat (length tr))); [lia|]. cbn [app].
    apply (proj2 (rwc_app asegs _ _ [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] [C4 (Z_to_bv 64 0)])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
  split; [exact_addr|]. split; [exact_addr|].
  split; [unfold alloc_frame32 in *; exact_addr|].
  split; [exact_addr|]. split; [exact_addr|]. exact_addr.
Qed.

Definition aligned_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma aligned_B_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 (F : bvmap 5 word) fc (m : mem) (UB lo : Z) (ws : list word) (w w16 wn : word) (jp jq : list byte),
  (0 < UB < 2^64)%Z ->
  stk asegs m lo (bv_unsigned sp + -2176) -> (lo <= bv_unsigned sp + -2176)%Z -> (0x6ca000 <= lo)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jp] ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
  u64arr asegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
  rw_cells asegs m (bv_unsigned sp + -2176) [C8 w16; C8 wn; C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x836cc)] ->
  mem_inv asegs m ->
  evt asegs (aligned_B_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c248) fc None m (seg_rom asegs)).
Proof.
  intros until jq. intros HUB ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2176, SP)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  zstep. ifF.
  do 4 zstep. zstep.
  release_frame FRa ST (SP + -2144)%Z.
  zstep.
  zstep.
  do 8 zstep.
  release_frame FRq ST (SP + -2136)%Z. release_frame FRb ST (SP + -2120)%Z. release_frame TB ST (SP + -80)%Z.
  release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
  zstep.
  zstep.
  finish.
  all: rewrite (unsigned_lit SP) by lia; assumption.
Qed.
