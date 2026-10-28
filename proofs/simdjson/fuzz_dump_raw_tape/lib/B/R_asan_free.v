(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_leaves R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_prim_kit R_intalloc R_asan_malloc R_deallocate.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Definition zpk (P : Prop) : Prop := P.
Local Ltac zpark H := let T := type of H in change (zpk T) in H.
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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma ia_state_frame : forall b W (m m' : mem), ia_state b m -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W 0x16e750 (0x207668 - 0x16e750) -> ia_state b m'.
Proof.
  intros b W m m' IS MU WM HD. unfold ia_state, g_ia_word, IAP in *. destruct b.
  - destruct IS as (W1 & MAP). split.
    + apply (rw_cells_transport bsegs W m m' _ _ W1 MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
    + apply (u8arr_transport bsegs W m m' _ _ MAP MU WM). rewrite repeat_length. eapply dep_disj_sub; [exact HD| |]; lia.
  - destruct IS as (W1 & (j & J) & (b1 & L1 & B1) & (b2 & L2 & B2) & (b3 & L3 & B3) & (j4 & J4) & G & P).
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    + apply (rw_cells_transport bsegs W m m' _ _ W1 MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
    + exists j. apply (rw_cells_transport bsegs W m m' _ _ J MU WM). cbn [cells_size csize Nat.add].
      eapply dep_disj_sub; [exact HD| |]; lia.
    + exists b1. split; [exact L1|]. apply (u8arr_transport bsegs W m m' _ _ B1 MU WM). eapply dep_disj_sub; [exact HD| |]; lia.
    + exists b2. split; [exact L2|]. apply (u8arr_transport bsegs W m m' _ _ B2 MU WM). eapply dep_disj_sub; [exact HD| |]; lia.
    + exists b3. split; [exact L3|]. apply (u8arr_transport bsegs W m m' _ _ B3 MU WM). eapply dep_disj_sub; [exact HD| |]; lia.
    + exists j4. apply (rw_cells_transport bsegs W m m' _ _ J4 MU WM). cbn [cells_size csize Nat.add].
      eapply dep_disj_sub; [exact HD| |]; lia.
    + apply (rw_cells_transport bsegs W m m' _ _ G MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
    + apply (rw_cells_transport bsegs W m m' _ _ P MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
Qed.

Definition ia_post' (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1543616) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (2127432, 2127436); (1543616, 2072048)]%Z m m' /\ wmono bsegs m m'
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ia_state true m'.

Lemma intalloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (b : bool) (lo : Z),
  ia_state b m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x6ce000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (ia_post' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros IS ST HLO HIMG MI.
  eapply evt_mono; [destruct b; [apply intalloc_fast_spec| apply intalloc_init_spec]; eassumption|].
  intros ms' P. unfold ia_post, ia_W, g_ia_word, IAP in P. exact P.
Qed.

Definition free_pc : Z := 0x80b64.

Definition free_pre_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p T lo : Z) (tr : list Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp : list byte) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x80bd4) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) a6' a7'
                  (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 deallocate_entry) fc None m' (seg_rom bsegs)
    /\ munch [(T + 3168, T + 3169); (2127432, 2127436); (1543616, 2072048); (bv_unsigned sp - 2288, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ ia_state true m'
    /\ rw_cells bsegs m' (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 jp]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp))]
    /\ u64arr bsegs m' (bv_unsigned sp + -2112) (wr_trace tr tb) /\ length tb = 255%nat
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128)
         [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' lo (bv_unsigned sp + -2128).

Lemma free_pre_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p TCX T top bot lo : Z) (b : bool) (ch : list (Z * Z)) (tr : list Z),
  (0 <= p < 2^47)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->

  chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
  unwind_trace free_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  ia_state b m ->
  rw_cells bsegs m 0x16e750 [C8 (Z_to_bv 64 0x207660)] ->
  rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x207660 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0x6ce000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6ce000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (free_pre_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_free_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros Hp ST HLO HLOH HSP Hbt Htop CH TR IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW MI.
  apply box in CH.
  unfold wrap_free_entry, kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell in *.
  change (2135784 + 34)%Z with 2135818%Z in FUM.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
  move G60 at bottom. move GCF at bottom. move KI at bottom. move K0 at bottom.
  move AI at bottom. move MCS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
  move T0 at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(T + 3168, T + 3169); (2127432, 2127436); (1543616, 2072048); (SP - 2288, SP)]%Z m) as MU.
  pose proof (munch_refl [(SP - 2288, SP)]%Z m) as MUs.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 56%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
  carve_frame 8%nat ST.
  zhide.
  zstep.
  zidle_beginZ SP 2128%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  do 4 zstep. zstep.
  let mm := amem in
  pose proof (ia_state_frame b _ m mm IS MUs WM ltac:(cbn [disjoint_from]; lia)) as IS'.
  clear MUs IS.
  sp_factsZ SP.
  call (intalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ b lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  lazymatch goal with H : ia_state true ?mm |- _ =>
    pose proof H as (IW & MAP); apply box in H; rename H into IST;
    pose proof (munch_refl [(T + 3168, T + 3169); (SP - 2288, SP)]%Z mm) as MUa; pose proof (wmono_refl bsegs mm) as WMa end.
  eapply pim_spec; [lia| exact MAP| eassumption|]. intros a1' a2' a3'. clear IW MAP.
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
  apply (rwc_app bsegs _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)]) in FR3. destruct FR3 as (FR3a & FR3b).
  cbn [cells_size csize] in FR3b. replace (SP + -2120 + Z.of_nat (4 + 0))%Z with (SP + -2116)%Z in FR3b by lia.
  change 2040%nat with (8 * 255)%nat in FR2. apply ma_rw_cells_u64arr in FR2.
  apply (rwc_app bsegs _ _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) in FR. destruct FR as (FRa & FRb).
  cbn [cells_size csize Nat.add] in FRb. replace (SP + -56 + Z.of_nat 40)%Z with (SP + -16)%Z in FRb by lia.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
  unfold bv_modulus in RRA, RS0. cbn [Z.of_N] in RRA, RS0.
  sp_factsZ SP.
  lazymatch goal with H : rw_cells bsegs ?mm (SP + -16) _ |- _ =>
    assert (CHm : chain_cells [(T + 3168, T + 3169); (2127432, 2127436); (1543616, 2072048); (SP - 2288, SP)]%Z m (bv_unsigned s0) ch)
      by (apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
    apply (fun X => chain_cells_frame _ m mm _ _ X MU WM) in CHm;
    apply (chain_cells_weaken _ (uwi_W (SP + -2128) T (SP + -2128))) in CHm;
      [| intros a HDa; unfold uwi_W; cbn [disjoint_from] in *; lia];
    assert (CC : chain_cells (uwi_W (SP + -2128) T (SP + -2128)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
      by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
          split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia| exact CHm]) end.
  all: try zpark FR1; try zpark FR2; try zpark FR3a; try zpark UW.
  call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2128) 527204 SP top bot 30 lo TCX T
          ((bv_unsigned ra, bv_unsigned s0) :: ch) (ma_dec64 255 junk2) (Z_to_bv 64 0) _ tr).
  all: rewrite ?Esp; try lia; try eassumption; try apply ma_dec64_length.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- stack_cells _ _ _ _ => unfold stack_cells, off_t_stack_top, off_t_stack_switching; split; assumption
       | |- rw_cells _ _ (?X + -2128 + 8)%Z _ => replace (X + -2128 + 8)%Z with (X + -2120)%Z by lia; exact FR3a
       | |- u64arr _ _ (?X + -2128 + 16)%Z _ => replace (X + -2128 + 16)%Z with (X + -2112)%Z by lia; exact FR2
       | |- rw_cells _ _ (?X + -2128 + 2056)%Z _ => replace (X + -2128 + 2056)%Z with (X + -72)%Z by lia; exact FR1
       | |- evt _ _ _ => idtac
       end.
  rewrite ?Esp in *.
  do 5 zstep.
  do 10 zstep.
  let mm := amem in
  pose proof (ia_state_frame true _ _ mm (unbox _ IST) MUa WMa ltac:(cbn [disjoint_from]; lia)) as ISF.
  clear MUa WMa IST.
  unfold free_pre_post. rewrite (unsigned_lit SP) by lia.
  apply evt_done.
  do 9 eexists. exists (ma_dec64 255 junk2), junk0. eexists.
  split; [reflexivity|].
  pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split.
  { apply (proj2 (rwc_app bsegs _ _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
  split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. split; [apply ma_dec64_length|].
  split.
  { apply (proj2 (rwc_app bsegs _ _ [C8 (Z_to_bv 64 (SP + -2112))] [C8 (Z_to_bv 64 (Z.of_nat (length tr)))])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add].
    apply (rw_cells_c44_join _ _ [] [] (Z.of_nat (length tr))); [lia|]. cbn [app].
    apply (proj2 (rwc_app bsegs _ _ [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] [C4 (Z_to_bv 64 0)])).
    split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
  split; [exact_addr|]. exact_addr.
Qed.

Definition free_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2128, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma free_B_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 (F : bvmap 5 word) fc (m : mem) (lo : Z) (ws : list word) (w : word) (jp : list byte),
  stk bsegs m lo (bv_unsigned sp + -2128) -> (lo <= bv_unsigned sp + -2128)%Z -> (0x6ce000 <= lo)%Z ->
  rw_cells bsegs m (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 jp] ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
  u64arr bsegs m (bv_unsigned sp + -2112) ws -> length ws = 255%nat ->
  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 w] ->
  mem_inv bsegs m ->
  evt bsegs (free_B_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x80bd4) fc None m (seg_rom bsegs)).
Proof.
  intros until jp. intros ST HLO HIMG FRs FRp FRt TB HTB FRb MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2128, SP)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  do 9 zstep.
  release_frame FRb ST (SP + -2112)%Z. release_frame TB ST (SP + -72)%Z.
  release_frame FRt ST (SP + -64)%Z. release_frame FRp ST (SP + -56)%Z. release_frame FRs ST SP.
  zstep.
  finish.
  all: rewrite (unsigned_lit SP) by lia; assumption.
Qed.

Definition free_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(T + 3168, T + 3169); (2127432, 2127436); (1543616, 2072048); (bv_unsigned sp - 2288, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ ia_state true m' /\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma free_null_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T top bot lo : Z) (b : bool) (ch : list (Z * Z)) (tr : list Z),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
  unwind_trace free_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  ia_state b m ->
  rw_cells bsegs m 0x16e750 [C8 (Z_to_bv 64 0x207660)] ->
  rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x207660 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0x6ce000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6ce000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (free_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_free_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros ST HLO HLOH HSP Hbt Htop CH TR IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (RLO : (17594333495303 <= lo)%Z) by (unfold kHighShadowEnd in HLOH; lia).
  pose proof (munch_refl [(T + 3168, T + 3169); (2127432, 2127436); (1543616, 2072048); (bv_unsigned sp - 2288, bv_unsigned sp)]%Z m)
    as MU.
  pose proof (wmono_refl bsegs m) as WM.
  eapply evt_cut; [eapply (free_pre_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m 0 TCX T top bot lo b ch tr);
                   try eassumption; lia|].
  intros ms1 P1. unfold free_pre_post in P1.
  destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & tb & jp & m1 & E1 & MU1 & WM1 & MI1 & IS1 & FRs & FRp & FRt & TB & HTB
                  & FRb & UW1 & ST1). subst ms1.
  clear MU WM.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2288, SP)]%Z m1) as MUa. pose proof (wmono_refl bsegs m1) as WMa.
  apply box in IS1.
  sp_factsZ SP.
  call (deallocate_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
  subst SP.
  all: try zpark FRb; try zpark FRp; try zpark FRs; try zpark FRt; try zpark TB.
  call (free_B_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (wr_trace tr tb) _ jp).
  all: rewrite ?Esp in *; try lia; try eassumption.
  1: { rewrite wr_trace_length; [exact HTB| lia]. }
  apply evt_done. unfold free_null_post. rewrite Z_to_bv_bv_unsigned.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| split; [eassumption| eassumption]].
  lazymatch goal with |- ia_state true ?mm => exact (ia_state_frame true _ m1 mm (unbox _ IS1) MUa WMa ltac:(cbn [disjoint_from]; lia)) end.
Qed.
