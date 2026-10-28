(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread R_cache_defs R_prim_defs R_sizeclass R_leaves I_ikit R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_allocate1 R_prim_kit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Fixpoint ma_dec64 (k : nat) (bs : list byte) : list word :=
  match k with O => [] | S k' => le_bytes_to_word (firstn 8 bs) :: ma_dec64 k' (skipn 8 bs) end.

Lemma ma_dec64_length : forall k bs, length (ma_dec64 k bs) = k.
Proof. induction k as [|k IH]; intros bs; cbn [ma_dec64 length]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma ma_u64s_dec64 : forall k bs, length bs = (8 * k)%nat -> u64s (ma_dec64 k bs) = bs.
Proof.
  induction k as [|k IH]; intros bs H; [destruct bs; [reflexivity| cbn in H; lia]|].
  cbn [ma_dec64 u64s]. rewrite dep_le8_of_bytes by (rewrite firstn_length; lia).
  rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma ma_rw_cells_u64arr : forall (m : mem) A k bs, rw_cells bsegs m A [CB (8 * k) bs] -> u64arr bsegs m A (ma_dec64 k bs).
Proof.
  intros m A k bs [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (HL & _).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  split.
  - rewrite ma_u64s_dec64 by lia. exact HB.
  - rewrite ma_dec64_length. cbn [cells_size csize] in HW. replace (8 * Z.of_nat k)%Z with (Z.of_nat (8 * k + 0)) by lia. exact HW.
Qed.

Lemma u64arr_rw_ma : forall (m : mem) A ws, u64arr bsegs m A ws -> rw_cells bsegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [HB HW]. split.
  - split; [cbn; split; [rewrite u64s_length; reflexivity| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws))%Z by lia. exact HW.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_c44_join : forall (m : mem) A pre post v, (0 <= v < 2 ^ 32)%Z ->
  rw_cells bsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> rw_cells bsegs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros m A pre post v Hv [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ [_ W2]]].
  split; [split|].
  - apply cells_wf_app. split; [exact W1| split; [exact I| exact W2]].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_split_small by exact Hv.
    rewrite <- app_assoc. exact B.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.

(* [comment removed for export] *)
Ltac exact_addr := lazymatch goal with
  | |- rw_cells ?s ?mm ?A ?cs => match goal with H : rw_cells s mm ?A' cs |- _ => replace A with A' by lia; exact H end
  | |- u64arr ?s ?mm ?A ?ws => match goal with H : u64arr s mm ?A' ws |- _ => replace A with A' by lia; exact H end
  | |- stk ?s ?mm ?lo ?A => match goal with H : stk s mm lo ?A' |- _ => replace A with A' by lia; exact H end
  end.

(* [comment removed for export] *)
Ltac sp_factsZ SP :=
  repeat match goal with
  | |- context [Z_to_bv 64 (SP + ?k)] =>
      lazymatch goal with
      | _ : bv_unsigned (Z_to_bv 64 (SP + k)) = _ |- _ => fail
      | _ => let E := fresh "Esp" in assert (E : bv_unsigned (Z_to_bv 64 (SP + k)) = (SP + k)%Z) by (apply unsigned_lit; lia)
      end
  end.

(* [comment removed for export] *)
Definition malloc_pc : Z := 0x1be5a8.

Lemma malloc_trace_ex : forall bot top usp raC s0C, (4096 <= top)%Z -> (top <= 2^63)%Z -> (usp mod 8 = 0)%Z ->
  (4096 <= raC)%Z -> raC <> malloc_pc -> (s0C < usp \/ s0C mod 8 <> 0 \/ 2^63 <= s0C)%Z ->
  exists tr, unwind_trace malloc_pc 4096 bot top 30 usp [(raC, s0C)] = Some tr /\ (1 <= length tr <= 2)%nat.
Proof.
  intros bot top usp raC s0C H1 H2 H3 H4 H5 H6. unfold malloc_pc in *.
  destruct (fr_ok bot (top - 16) usp) eqn:FB.
  - unfold fr_ok in FB. apply andb_prop in FB. destruct FB as (FB & E8). apply andb_prop in FB. destruct FB as (B1 & B2).
    apply Z.ltb_lt in B1. apply Z.ltb_lt in B2. apply Z.eqb_eq in E8.
    exists [0x1be5a8; raC]%Z. split; [| cbn; lia].
    unfold unwind_trace.
    rewrite (proj2 (Z.eqb_neq (top / 4096) 0)) by (Z.div_mod_to_equations; lia).
    assert (FB' : fr_ok bot (top - 16) usp = true).
    { unfold fr_ok. rewrite (proj2 (Z.ltb_lt bot usp)) by lia. rewrite (proj2 (Z.ltb_lt usp (top - 16))) by lia.
      rewrite E8. reflexivity. }
    rewrite FB'. cbn [uw_loop length Z.of_nat].
    rewrite (proj2 (Z.leb_gt 30 1)) by lia. rewrite (proj2 (Z.ltb_ge raC 4096)) by lia.
    rewrite (proj2 (Z.eqb_neq raC 0x1be5a8)) by exact H5. cbn [app].
    assert (FS : fr_ok usp (top - 16) s0C = false).
    { unfold fr_ok. destruct H6 as [H6|[H6|H6]].
      - rewrite (proj2 (Z.ltb_ge usp s0C)) by lia. reflexivity.
      - rewrite (proj2 (Z.eqb_neq (s0C mod 8) 0)) by exact H6. rewrite !andb_false_r. reflexivity.
      - rewrite (proj2 (Z.ltb_ge s0C (top - 16))) by lia. rewrite andb_false_r. reflexivity. }
    rewrite FS. reflexivity.
  - exists [0x1be5a8]%Z. split; [| cbn; lia]. unfold unwind_trace.
    rewrite (proj2 (Z.eqb_neq (top / 4096) 0)) by (Z.div_mod_to_equations; lia). rewrite FB. reflexivity.
Qed.

(* [comment removed for export] *)
Definition malloc_A_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n T lo : Z) (tr : list Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp j0 : list byte) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x195ec8) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
                  (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp + -2128))
                  (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x19a488) fc None m' (seg_rom bsegs)
    /\ munch [(T + 3168, T + 3169); (bv_unsigned sp - 2288, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 jp]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp))]
    /\ u64arr bsegs m' (bv_unsigned sp + -2112) (wr_trace tr tb) /\ length tb = 255%nat
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128)
         [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x1be614)]
    /\ alloc_frame m' (bv_unsigned sp + -2272) (Z_to_bv 64 0x195bf8) (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 n)
         (Z_to_bv 64 0x1be5a8) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
         s6 s7 s8 s9 s10 s11
    /\ rw_cells bsegs m' (bv_unsigned sp + -2272) [CB 8 j0]
    /\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' lo (bv_unsigned sp + -2272).

Lemma malloc_A_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n TCX T top bot lo : Z) (ch : list (Z * Z)) (tr : list Z),
  (1 <= n <= 2^31)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^63)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  (* [comment removed for export] *)
  chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
  unwind_trace malloc_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  rw_cells bsegs m 0x5e0cb8 [C8 (Z_to_bv 64 0x7334a0)] ->
  rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x7334a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbfd000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (malloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_malloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros Hn ST HLO HLOH HSP Hbt Htop CH TR G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl HT0 HT HTl HTT SC UW MI.
  apply box in CH.
  unfold wrap_malloc_entry, kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell,
    g_rss_limit_exceeded in *.
  change (7558440 + 34)%Z with 7558474%Z in FUM.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
  move G60 at bottom. move GCF at bottom. move MX at bottom. move RZ at bottom. move KI at bottom. move K0 at bottom.
  move AI at bottom. move MCS at bottom. move RSS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
  move T0 at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(T + 3168, T + 3169); (SP - 2288, SP)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 56%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
  carve_frame 8%nat ST.
  zhide.
  zidle_beginZ SP 2128%Z MUz WMz.
  zstep.
  do 8 zstep.
  do 4 zstep. zstep.
  zidle_end MUz WMz.
  sp_factsZ SP.
  call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
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
  (* [comment removed for export] *)
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
    assert (CHm : chain_cells [(T + 3168, T + 3169); (SP - 2288, SP)]%Z m (bv_unsigned s0) ch)
      by (apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
    apply (fun X => chain_cells_frame _ m mm _ _ X MU WM) in CHm;
    apply (chain_cells_weaken _ (uwi_W (SP + -2128) T (SP + -2128))) in CHm;
      [| intros a HDa; unfold uwi_W; cbn [disjoint_from] in *; lia];
    assert (CC : chain_cells (uwi_W (SP + -2128) T (SP + -2128)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
      by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
          split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia| exact CHm]) end.
  call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2128) 1828264 SP top bot 30 lo TCX T
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
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => carve_frame 16%nat H end end.
  zstep. zstep; fix_lit_store. zstep.
  do 8 zstep.
  sp_factsZ SP.
  call (allocate_p1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n (SP + -2128) TCX T lo).
  all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  unfold malloc_A_post. rewrite (unsigned_lit SP) by lia.
  replace (SP + -2144 + -128)%Z with (SP + -2272)%Z in * by lia.
  apply evt_done.
  lazymatch goal with H : exists j, rw_cells bsegs _ _ [CB 8 j] |- _ => destruct H as (j0 & HJ0) end.
  do 11 eexists. exists (ma_dec64 255 junk2), junk0, j0. eexists.
  split; [reflexivity|].
  pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
  split; [assumption|]. split; [assumption|]. split; [assumption|].
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
  split; [exact_addr|].
  split; [unfold alloc_frame in *; exact_addr|].
  split; [exact_addr|]. split; [exact_addr|]. exact_addr.
Qed.

(* [comment removed for export] *)
Definition malloc_B_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma malloc_B_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 (F : bvmap 5 word) fc (m : mem) (UB lo : Z) (ws : list word) (w : word) (jp : list byte),
  (0 < UB < 2^64)%Z ->
  stk bsegs m lo (bv_unsigned sp + -2144) -> (lo <= bv_unsigned sp + -2144)%Z -> (0xbfd000 <= lo)%Z ->
  rw_cells bsegs m (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 jp] ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
  u64arr bsegs m (bv_unsigned sp + -2112) ws -> length ws = 255%nat ->
  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 w] ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x1be614)] ->
  mem_inv bsegs m ->
  evt bsegs (malloc_B_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x195bf8) fc None m (seg_rom bsegs)).
Proof.
  intros until jp. intros HUB ST HLO HIMG FRs FRp FRt TB HTB FRb FRa MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2144, SP)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  zstep. ifF.
  do 4 zstep.
  do 9 zstep.
  release_frame FRa ST (SP + -2128)%Z. release_frame FRb ST (SP + -2112)%Z. release_frame TB ST (SP + -72)%Z.
  release_frame FRt ST (SP + -64)%Z. release_frame FRp ST (SP + -56)%Z. release_frame FRs ST SP.
  zstep.
  finish.
  all: rewrite (unsigned_lit SP) by lia; assumption.
Qed.
