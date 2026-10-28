(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_leaves R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_prim_kit R_intalloc R_asan_malloc R_deallocate.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import R_asan_free R_asan_malloc_k R_allocate1 I_ikit F_memcpy.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Definition zpk (P : Prop) : Prop := P.
Local Ltac zpark H := let T := type of H in change (zpk T) in H.
Open Scope bv_scope.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Open Scope Z_scope.
Lemma pim_R_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  0 <= p < 2 ^ 47 ->
  u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv asegs m ->
  (forall a1' a2' a3', evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (Z_to_bv 64 0x1c36f8) fc None m (seg_rom asegs))) ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x1c3668) fc None m (seg_rom asegs)).
Proof.
  intros until fc. intros HP MAP MI K. unfold IAP in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (E47 : Z.shiftr p 47 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  zstep. rewrite E47. zstep. ifF.
  assert (HQ : 0 <= Z.shiftr p 32 < 32768).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  do 3 zstep.
  assert (SH3 : (p ≫ 32) ≪ 3 = 8 * (p ≫ 32)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
  pose proof (zero_run_read8 m (6741312 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
  replace (6741312 + 8 + 8 * (p ≫ 32)) with (6741312 + 8 * (p ≫ 32) + 8) in RD by lia.
  zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
  zstep. zstep. ifT.
  apply K.
Qed.

Open Scope bv_scope.
Definition wrap_realloc_entry : Z := 0x1c2fec%Z.
Definition icpt_realloc_entry : Z := 0x1c3624%Z.
Definition asan_realloc_entry : Z := 0x19b6d4%Z.
Definition reallocate_entry : Z := 0x19b780%Z.
Definition realloc_pc : Z := 0x1c3760%Z.

Definition realloc_A_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n T lo : Z) (tr : list Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp jq ja j0 : list byte) (r1 r2 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19af0c) (Z_to_bv 64 (bv_unsigned sp + -2336)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp + -2136))
                  (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x19f4cc) fc None m' (seg_rom asegs)
    /\ munch [(T + 3168, T + 3169); (T + 2856, T + 2872); (7325128, 7325132); (6741312, 7269744); (bv_unsigned sp - 2352, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ia_state true m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [CB 8 jp]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))]
    /\ u64arr asegs m' (bv_unsigned sp + -2120) (wr_trace tr tb) /\ length tb = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -2136)
         [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 jq]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 ja; C8 (Z_to_bv 64 0x1c37d0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2208)
         [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x1c3760); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp));
          C8 (Z_to_bv 64 0x19b770)]
    /\ alloc_frame m' (bv_unsigned sp + -2336) (Z_to_bv 64 0x19b7ec) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
         (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
         s7 s8 s9 s10 s11
    /\ rw_cells asegs m' (bv_unsigned sp + -2336) [CB 8 j0]
    /\ rw_cells asegs m' (T + 2856) [C8 r1; C8 r2]
    /\ rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk asegs m' lo (bv_unsigned sp + -2336).
Lemma realloc_Ak_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p n TCX T top bot lo : Z) (ch : list (Z * Z)) (b : bool) (tr : list Z) (r1 r2 : word),
  (0 < p < 2^47)%Z -> (1 <= n <= 2^31)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2352)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  chain_cells [(T + 3168, T + 3169); (T + 2856, T + 2872); (7325128, 7325132); (6741312, 7269744); (bv_unsigned sp - 2352, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
  unwind_trace realloc_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  ia_state b m ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0xbc6000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (T + 2856) [C8 r1; C8 r2] ->
  mem_inv asegs m ->
  evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_realloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until r2. intros Hp Hn ST HLO HLOH HSP Hbt Htop CCH TR IS G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW STS MI.
  unfold wrap_realloc_entry, kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell,
    g_rss_limit_exceeded in *.
  change (7333480 + 34)%Z with 7333514%Z in FUM.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
  move G60 at bottom. move GCF at bottom. move MX at bottom. move RZ at bottom. move KI at bottom. move K0 at bottom.
  move AI at bottom. move MCS at bottom. move RSS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
  move T0 at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(T + 3168, T + 3169); (T + 2856, T + 2872); (7325128, 7325132); (6741312, 7269744); (SP - 2352, SP)]%Z m) as MU.
  pose proof (munch_refl [(SP - 2352, SP)]%Z m) as MUs.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
  carve_frame 8%nat ST. carve_frame 8%nat ST.
  zhide.
  zstep.
  zidle_beginZ SP 2144%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 4 zstep. zstep.
  zstep.
  sp_factsZ SP.
  call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
  zstep.
  let mm := amem in
  pose proof (ia_state_frame b _ m mm IS MUs WM ltac:(cbn [disjoint_from]; lia)) as IS'.
  clear MUs IS.
  sp_factsZ SP.
  call (intalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ b lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  lazymatch goal with H : ia_state true ?mm |- _ =>
    pose proof H as (IW & MAP); apply box in H; rename H into IST;
    pose proof (munch_refl [(T + 3168, T + 3169); (T + 2856, T + 2872); (SP - 2352, SP)]%Z mm) as MUa; pose proof (wmono_refl asegs mm) as WMa end.
  eapply pim_R_spec; [lia| exact MAP| eassumption|]. intros a1' a2' a3'. clear IW MAP.
  do 7 zstep.
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
    assert (CC : chain_cells (uwi_W (SP + -2136) T (SP + -2144)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
      by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
          split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia|];
          apply (chain_cells_sub [(T + 3168, T + 3169); (T + 2856, T + 2872); (7325128, 7325132); (6741312, 7269744); (SP - 2352, SP)]%Z); [unfold uwi_W; cbn [disjoint_from]; intros; lia|];
          exact (chain_cells_frame _ m mm _ ch CCH MU WM)) end.
  all: try zpark FR1; try zpark FR2; try zpark FR3a; try zpark UW.
  call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2136) 1849184 SP top bot 30 lo TCX T
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
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => carve_frame 16%nat H end end.
  zstep. zstep; fix_lit_store. zstep. zstep.
  zstep. ifF.
  zstep. zstep. ifT.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => carve_frame 48%nat H end end.
  zstep.
  do 6 (zstep; fix_lit_store).
  zstep. ifF.
  zstep. zstep. ifF.
  do 3 zstep.
  zstep.
  sp_factsZ SP.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3 in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  do 4 zstep.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  do 6 zstep.
  zstep.
  sp_factsZ SP.
  call (allocate_p1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n (SP + -2136) TCX T lo).
  all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3, ?Esp4, ?Esp5 in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  let mm := amem in
  pose proof (ia_state_frame true _ _ mm (unbox _ IST) MUa WMa ltac:(cbn [disjoint_from]; lia)) as ISF.
  clear MUa WMa IST.
  unfold realloc_A_post. rewrite (unsigned_lit SP) by lia.
  replace (SP + -2208 + -128)%Z with (SP + -2336)%Z in * by lia.
  apply evt_done.
  lazymatch goal with H : exists j, rw_cells asegs _ _ [CB 8 j] |- _ => destruct H as (j0 & HJ0) end.
  do 11 eexists. exists (ma_dec64 255 junk2), junk0, junk5, (firstn 8 junk6), j0. do 3 eexists.
  split; [reflexivity|].
  pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
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
  split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|].
  split; [unfold alloc_frame, INST, g_instance in *; exact_addr|].
  split; [exact_addr|]. split; [eassumption|]. split; [exact_addr|]. exact_addr.
Qed.

(* [comment removed for export] *)
Definition realloc_mid_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (M q k Bt : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19b880) sp gp tp t0' t1' t2' (Z_to_bv 64 Bt) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 INST)
                  (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 Bt) (Z_to_bv 64 1) a6' a7'
                  (Z_to_bv 64 INST) (Z_to_bv 64 k) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 deallocate_entry) fc None m' (seg_rom asegs)
    /\ munch [(q, q + k)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' q [CB (Z.to_nat k) src]
    /\ bytes_at asegs m' (M + 16) src.

Lemma realloc_mid_tail : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M q k Bt : Z) (src junk : list byte),
  (0 <= k < 2^64)%Z -> (0 <= q < 2^64)%Z -> (0 <= M + 16 < 2^64)%Z ->
  bytes_at asegs m (M + 16) src -> length src = Z.to_nat k ->
  rw_cells asegs m q [CB (Z.to_nat k) junk] ->
  (M + 16 + k <= q \/ q + k <= M + 16)%Z ->
  mem_inv asegs m ->
  evt asegs (realloc_mid_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc M q k Bt src m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 Bt) (Z_to_bv 64 (M + 16)) a0 a1 a2 (Z_to_bv 64 0x5264e0) a4 a5 a6 a7
             (Z_to_bv 64 INST) (Z_to_bv 64 k) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19b854) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros Hk Hq HM SRC LEN DST SEP MI.
  pose proof (munch_refl [(q, q + k)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 zstep.
  zstep.
  assert (EUd : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (M + 16)) = (M + 16)%Z) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  call memcpy_spec;
      [ rewrite EUs; exact SRC
      | rewrite EUn; exact LEN
      | rewrite EUd, EUn; exact DST
      | rewrite EUd, EUs, EUn; lia| assumption|].
  rewrite EUd, EUn in *. rewrite EUs in *.
  do 6 zstep.
  zstep.
  unfold realloc_mid_post, deallocate_entry. apply evt_done.
  do 10 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma realloc_mid_spec : forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M q n n0 b1 Bt : Z) (ctx : word) (src junk : list byte),
  (1 <= n < 2^32)%Z -> (1 <= n0 < 2^32)%Z -> (0 < q < 2^64)%Z -> (0 <= M)%Z -> (M + 16 < 2^64)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells asegs m M [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n0); C8 ctx] ->
  ro_cells asegs m 0x5a45e0 [C8 (Z_to_bv 64 0x5a77e8)] -> ro_cells asegs m 0x5a77e8 [C8 (Z_to_bv 64 0x5264e0)] ->
  bytes_at asegs m (M + 16) src -> length src = Z.to_nat (Z.min n n0) ->
  rw_cells asegs m q [CB (Z.to_nat (Z.min n n0)) junk] ->
  (M + 16 + Z.min n n0 <= q \/ q + Z.min n n0 <= M + 16)%Z ->
  mem_inv asegs m ->
  evt asegs (realloc_mid_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc M q (Z.min n n0) Bt src m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 Bt) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 INST) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19b7ec) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros Hn Hn0 Hq HM HM2 Hb1 HD G1 G2 SRC LEN DST SEP MI.
  pose proof (munch_refl [(q, q + Z.min n n0)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. ifF.
  zstep. zstep. zstep.
  change (sxb (Z_to_bv 8 2)) with (Z_to_bv 64 2).
  zstep. ifT.
  do 3 zstep.
  zstep. ifF.
  do 4 zstep.
  rewrite (zx32_small n0) by lia.
  change (Z.land (bv_unsigned (zx16 (Z_to_bv 64 0)) ≪ 32) 18446744073709551615) with 0%Z.
  rewrite Z.lor_0_l. rewrite (unsigned_lit n0) by lia.
  destruct (Z.ltb_spec n n0) as [LT|GE].
  - zstep. ifT.
    rewrite (Z.min_l n n0) in * by lia.
    eapply realloc_mid_tail; try eassumption; lia.
  - zstep. ifF. zstep.
    rewrite (Z.min_r n n0) in * by lia.
    eapply realloc_mid_tail; try eassumption; lia.
Qed.

(* [comment removed for export] *)
Definition realloc_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma realloc_B_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 (w0 w1 w2 w3 w4 : word) (F : bvmap 5 word) fc (m : mem) (q lo : Z) (ws : list word) (w tf : word)
    (jp jq ja : list byte),
  (0 < q < 2^64)%Z ->
  stk asegs m lo (bv_unsigned sp + -2208) -> (lo <= bv_unsigned sp + -2208)%Z -> (0xbc6000 <= lo)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jp] ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 tf] ->
  u64arr asegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
  rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 ja; C8 (Z_to_bv 64 0x1c37d0)] ->
  rw_cells asegs m (bv_unsigned sp + -2208) [C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 (Z_to_bv 64 0x19b770)] ->
  mem_inv asegs m ->
  evt asegs (realloc_B_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' (Z_to_bv 64 q) s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19b880) fc None m (seg_rom asegs)).
Proof.
  intros until ja. intros HQ ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa FRr MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2208, SP)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  zstep.
  do 6 zstep.
  zstep. zstep.
  zstep. ifF.
  do 3 zstep.
  do 10 zstep.
  release_frame FRr ST (SP + -2160)%Z. release_frame FRa ST (SP + -2144)%Z. release_frame FRq ST (SP + -2136)%Z.
  release_frame FRb ST (SP + -2120)%Z. release_frame TB ST (SP + -80)%Z.
  release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
  zstep.
  finish.
  all: rewrite (unsigned_lit SP) by lia; assumption.
Qed.
