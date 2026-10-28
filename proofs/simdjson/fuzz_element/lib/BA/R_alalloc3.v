(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_setshadow. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_classid R_leaves F_memset R_depot_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_alalloc1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

Local Definition zmin (x y : Z) : Z := Z.min x y.
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

Ltac ifT_p p := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota| symmetry; unfold_cond; fold_lit_ux; rewrite (unsigned_lit p) by lia; solve_cond_rec] end.
Ltac ifF_p p := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; unfold_cond; fold_lit_ux; rewrite (unsigned_lit p) by lia; solve_cond_rec] end.

Lemma allocate_p3a_tail_al : forall sp gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s2v s4v s5v s6v s7v s8v s9v s11v
    fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12
    (F : bvmap 5 word) fc (m : mem) (n TCX T lo : Z),
  (1 <= n <= 2^31)%Z ->
  alloc_frame32 m (bv_unsigned sp) fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= lo)%Z ->
  p3_stats m T ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x6ca000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (p3a_tail_post sp gp (Z_to_bv 64 tpA) F fc s0v (Z_to_bv 64 n) s2v (Z_to_bv 64 (needed n + 16)) s4v s5v s6v s7v s8v s9v
               (Z_to_bv 64 T) s11v T lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2v (Z_to_bv 64 (needed n + 16))
             s4v s5v s6v s7v s8v s9v (Z_to_bv 64 T) s11v t3 t4 t5 t6)
        F (Z_to_bv 64 0x5bbb4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hn FR TC HTCX HTCXl HT HTl SC ST HLO HIMG HSP MI.
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  assert (NB : needed n = (rounded n + rz_size n)%Z) by reflexivity. pose proof (rounded_range n ltac:(lia)) as (RR1 & RR2 & RR3).
  unfold alloc_frame32 in FR.
  destruct SC as ((st0 & st1 & st2 & SC0) & (st13 & SC13) & (mbs & MBS & Hmbs)).
  pose proof (munch_refl [(T + 2800, T + 2824); (T + 2904, T + 2912 + 256); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zhide.
  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: try lia; try eassumption.
  do 12 zstep.
  zstep.
  destruct (Z.ltb_spec (needed n + 16) 65537) as [C|C].
  - ifT.
    eapply evt_cut; [apply classid_31fx_spec; [lia| lia| assumption]|].
    intros ms' (a2' & a3' & a4' & a5' & a6' & ->).
    pose proof (ClassID_props (needed n + 16) ltac:(lia)) as [Hc _].
    remember (ClassID (needed n + 16)) as c eqn:Ec.
    destruct (nth_error mbs (Z.to_nat c)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
    zstep. replace (T + 2800 + 112 + c * 8)%Z with (T + 2912 + 8 * c)%Z by lia.
    pose proof (u64arr_read asegs _ (T + 2912) mbs c w (Z_to_bv 64 (T + 2912 + 8 * c)) MBS ltac:(exact Hw) ltac:(lia)
                  ltac:(reflexivity)) as RD.
    zstep. clear RD. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with TB0 : u64arr asegs mm (T + 2912) _ |- _ =>
        pose proof (u64arr_store_ok asegs mm (T + 2912) _ c (Z_to_bv 64 (T + 2912 + 8 * c)) TB0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO;
        zstep;
        pose proof (u64arr_write asegs mm (T + 2912) _ c (Z_to_bv 64 (bv_unsigned w + 1)) TB0 ltac:(lia)) as TB';
        clear TB0 end end.
    store_done.
    zstep. zstep. ifF.
    finish.
    unfold p3_stats. split; [do 3 eexists; eassumption| split; [eexists; eassumption|]].
    eexists. split; [eassumption| rewrite upd_length; exact Hmbs].
  - ifF. do 5 zstep. ifT.
    finish.
    unfold p3_stats. split; [do 3 eexists; eassumption| split; [eexists; eassumption|]].
    eexists. split; [eassumption| exact Hmbs].
Qed.

Definition allocate_p3a_al_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (s0v s9v : word) (n AB B T lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0v (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16))
                  (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0) s9v
                  (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6') F (Z_to_bv 64 0x5bd14) fc None m' (seg_rom asegs)
    /\ munch [(shad (AB + rz_size n + size_rd n), shad (AB + rz_size n + size_rd n) + (if n mod 8 =? 0 then 0 else 1)); (T + 2800, T + 2824);
             (T + 2904, T + 2912 + 256); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ p3_stats m' T
    /\ (n mod 8 <> 0 -> rw_cells asegs m' (shad (AB + rz_size n + size_rd n)) [C1 (Z_to_bv 8 (n mod 8))])%Z
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma allocate_p3a_al_spec : forall sp gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s9v
    fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12
    (F : bvmap 5 word) fc (m : mem) (n AB B TCX T lo : Z) (pb : byte),
  (1 <= n <= 2^31)%Z -> (kHighShadowEnd < AB)%Z -> (AB + needed2 n <= kHighMemEnd + 1)%Z ->
  alloc_frame32 m (bv_unsigned sp) fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 ->
  m2s_cells m -> rw_cells asegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] ->
  rw_cells asegs m (g_asan_flags + 85) [C1 (Z_to_bv 8 1)] -> rw_cells asegs m g_can_poison_memory [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad (AB + rz_size n + size_rd n)) [C1 pb])%Z ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x7fff7000 \/ 0x10007fff8000 <= TCX)%Z ->
  (TCX + 0xa0 <= 0x10000 \/ 0x6ca000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T)%Z -> (T + 4096 <= 0x10000 \/ 0x6ca000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  p3_stats m T ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x10007fff8000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_p3a_al_post sp gp (Z_to_bv 64 tpA) F fc s0v s9v n AB B T lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16))
             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 B) (Z_to_bv 64 0) s9v
             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x5bb20) fc None m (seg_rom asegs)).
Proof.
  intros until pb. intros Hn HAB HABl FR M2S GAF PP CP PB TC HTCX HTCXs HTCXi HTCXl HT HTs HTi HTl SC ST HLO HIMG HSP MI.
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  assert (NB : needed n = (rounded n + rz_size n)%Z) by reflexivity. pose proof (rounded_range n ltac:(lia)) as (RR1 & RR2 & RR3).
  pose proof FR as FR'. unfold alloc_frame32 in FR'. destruct M2S as (M2a & M2b & M2c). apply box in TC. apply box in SC. apply box in FR'.
  unfold kHighShadowEnd, kHighMemEnd, g_GOT_asan_flags, g_asan_flags, g_can_poison_memory in *.
  unfold SHB in M2b.
  move GAF at bottom. move M2a at bottom. move PP at bottom. move CP at bottom.
  move M2b at bottom. move M2c at bottom.
  change (1512504 + 85)%Z with 1512589%Z in PP.
  pose proof (munch_refl [(shad (AB + rz_size n + size_rd n), shad (AB + rz_size n + size_rd n) + 1); (T + 2800, T + 2824);
                          (T + 2904, T + 2912 + 256); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RRD : (size_rd n <= n < size_rd n + 8 /\ size_rd n mod 8 = 0)%Z).
  { unfold size_rd. split; [Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia]. }
  zhide.
  zstep.
  destruct (Z.eq_dec n (size_rd n)) as [E0|N0].
  - ifT.
    eapply evt_mono; [eapply allocate_p3a_tail_al with (TCX := TCX); try exact (unbox _ TC); try exact (unbox _ SC); eassumption || lia|].
    intros ms' P. destruct P as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                                 E & MU' & WM' & MI' & SC' & ST').
    unfold allocate_p3a_post. do 17 eexists. exists m'. split; [exact E|].
    assert (Hm0 : (n mod 8 = 0)%Z) by (rewrite E0; unfold size_rd; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
    rewrite (proj2 (Z.eqb_eq (n mod 8) 0) Hm0).
    split; [eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM'| split; [exact MI'| split; [exact SC'| split; [| exact ST']]]].
    intros Hm8. exfalso. apply Hm8. rewrite E0. unfold size_rd. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
  - ifF.
    assert (Nm8 : (n mod 8 <> 0)%Z) by (intro Hm; apply N0; unfold size_rd; Z.div_mod_to_equations; lia).
    pose proof (PB Nm8) as PBC. clear PB.
    pose proof (munch_refl [(shad (AB + rz_size n + size_rd n), shad (AB + rz_size n + size_rd n) + 1)]%Z m) as MUp.
    zstep.
    call (can_poison_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
    all: try eassumption.
    zstep. ifF.
    do 9 zstep.
    fold_reg 12%Z. ifF.
    do 8 zstep. ifT_p (AB + rz_size n + size_rd n)%Z.
    do 6 zstep. ifF_p (AB + rz_size n + size_rd n)%Z. zstep. ifF_p (AB + rz_size n + size_rd n)%Z.
    do 8 zstep.
    replace (2147450880 + Z.shiftr (AB + rz_size n + size_rd n) 3)%Z with (shad (AB + rz_size n + size_rd n))
      by (unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; lia).
    replace (Z.land (Z.land n 18446744073709551615) 7) with (n mod 8)%Z
      by (change 18446744073709551615%Z with (Z.ones 64); change 7%Z with (Z.ones 3); rewrite !Z.land_ones by lia;
          rewrite (Z.mod_small n (2^64)) by lia; reflexivity).
    remember (shad (AB + rz_size n + size_rd n)) as SPB eqn:ESPB.
    assert (RSPB : (2147450880 <= SPB <= 17594333495295)%Z) by (rewrite ESPB; unfold shad, SHB; Z.div_mod_to_equations; lia).
    zstep. sb_fix.
    let mm := amem in
    pose proof (thread_cells_frame TCX T _ m mm (unbox _ TC) MUp WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)
                  ltac:(cbn [disjoint_from]; lia)) as TCm;
    pose proof (p3_stats_frame T _ m mm (unbox _ SC) MUp WM ltac:(cbn [disjoint_from]; lia)) as SCm;
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ FR') MUp WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRm.
    clear MUp.
    eapply evt_mono; [eapply allocate_p3a_tail_al with (TCX := TCX); try exact TCm; try exact SCm; try (unfold alloc_frame32; exact FRm);
                      eassumption || lia|].
    intros ms' P. destruct P as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                                 E & MU' & WM' & MI' & SC' & ST').
    subst SPB.
    unfold allocate_p3a_post. do 17 eexists. exists m'. split; [exact E|].
    rewrite (proj2 (Z.eqb_neq (n mod 8) 0) Nm8).
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia]|].
    split; [eapply wmono_trans; eassumption| split; [exact MI'| split; [exact SC'| split; [| exact ST']]]].
    intros _. lazymatch goal with H : rw_cells asegs ?m1 (shad _) [C1 (Z_to_bv 8 (n mod 8))] |- _ =>
      apply (rw_cells_transport asegs _ m1 m' _ _ H MU' WM'); cbn [disjoint_from cells_size csize Nat.add]; lia end.
Qed.

Ltac p3b_hooks sp FR FRj ST :=
  do 3 zstep;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => carve_frame 32%nat H end end;
  let MUz := fresh "MUz" in let WMz := fresh "WMz" in
  zidle_begin sp 32%Z MUz WMz; zstep; do 4 (zstep; fix_lit_store); zidle_end MUz WMz; do 3 zstep; do 2 zstep; do 3 zstep; ifT;
  do 5 zstep;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ =>
      match goal with FR0 : rw_cells asegs mm (bv_unsigned sp + -32)%Z _ |- _ => release_frame FR0 H (bv_unsigned sp) end end end;
  zstep;
  do 15 zstep;
  release_frame FRj ST (bv_unsigned sp + 8)%Z;
  release_frame FR ST (bv_unsigned sp + 128)%Z;
  zstep;
  finish.

Lemma allocate_p3b_fill_al : forall sp gp ra0 t0 t1 t2 a1 a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
    fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12
    (F : bvmap 5 word) fc (m : mem) (n AB B T lo b1 : Z) (h0 uj lj j0 : list byte) (ctx : word),
  a2v = Z_to_bv 64 (Z.min n 4096) ->
  (1 <= n <= 2^31)%Z -> (kHighShadowEnd < AB)%Z -> (AB + needed2 n <= kHighMemEnd + 1)%Z -> (0 <= b1 < 256)%Z ->
  alloc_frame32 m (bv_unsigned sp) fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 -> rw_cells asegs m (bv_unsigned sp) [CB 8 j0] ->
  rw_cells asegs m (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells asegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [CB 16 lj])%Z ->
  rw_cells asegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] ->
  rw_cells asegs m (g_asan_flags + 44) [C4 (Z_to_bv 64 4096)] -> rw_cells asegs m (g_asan_flags + 52) [C4 (Z_to_bv 64 190)] ->
  setshadow_cells m ->
  rw_cells asegs m 0x16ae90 [C8 (Z_to_bv 64 16)] -> rw_cells asegs m (tpA + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m g_MFHooks [C8 (Z_to_bv 64 0)] ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x6ca000 <= lo)%Z -> (bv_unsigned sp + 128 <= 2^63)%Z ->
  (AB + needed2 n <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_post fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 sp gp (Z_to_bv 64 tpA) F fc n AB b1 ctx lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) (Z_to_bv 64 1512504) a1 a2v a3 a4 a5
             a6 a7 (Z_to_bv 64 AB) s3v
             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v (Z_to_bv 64 B) (Z_to_bv 64 0) s9v
             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x5bd30) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros Ea2 Hn HAB HABl Hb1 FR FRj HD UJ LJ GAF FL1 FL2 SS GLS TLS MFH ST HLO HIMG HSP HABlo MI. subst a2v.
  change (Z.min n 4096) with (zmin n 4096) in *.
  assert (Hzmn : (1 <= zmin n 4096 <= 4096 /\ zmin n 4096 <= n)%Z) by (unfold zmin; lia).
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  pose proof (rz_size_mod16 n) as RZM.
  unfold alloc_frame32 in FR. destruct SS as (SS1 & SS2).
  unfold kHighShadowEnd, kHighMemEnd, g_GOT_asan_flags, g_asan_flags, g_MFHooks, tpA, g_got_real_memset, g_real_memset,
    musl_memset_entry in *.
  change (1512504 + 44)%Z with 1512548%Z in FL1. change (1512504 + 52)%Z with 1512556%Z in FL2. change (6979176 + 16)%Z with 6979192%Z in TLS.
  move GAF at bottom. move SS1 at bottom. move GLS at bottom. move SS2 at bottom. move FL1 at bottom. move FL2 at bottom.
  move MFH at bottom. move TLS at bottom.
  pose proof (munch_refl [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (bv_unsigned sp - 32, bv_unsigned sp + 128)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (bv_unsigned sp - 32, bv_unsigned sp + 128)]%Z m) as MU3.
  zhide.
  do 6 zstep. rewrite (sx32_small_A 190) by lia.
  call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (AB + rz_size n)%Z 190 (Z.min n 4096) uj).
  all: try lia; try eassumption.
  do 6 zstep. fold_reg 10%Z.
  zstep.
  do 6 zstep.
  replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256%Z;
                                                   rewrite Z.mod_small by lia; reflexivity).
  zstep. sb_fix.
  zstep. zstep; fix_lit_store.
  zstep.
  destruct (Z.eq_dec (rz_size n) 16) as [R16|R16].
  - ifT. p3b_hooks sp FR FRj ST.
    rewrite R16 in *. lia.
  - ifF.
    pose proof (rw_cells_transport asegs _ m _ AB _ (LJ ltac:(lia)) MU3 WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as LJC.
    clear LJ MU3.
    zstep. zstep. ifF.
    let mm := amem in
    let bs := eval vm_compute in (option.default [] (image_bytes asegs 0x10378 8)) in
    assert (RCM : ro_cells asegs mm 0x10378 [CB (length bs) bs])
      by (apply ro_cells_image; [eassumption| vm_compute; reflexivity| lia| cbn; lia]).
    cbn [length] in RCM.
    zstep. zstep. fold_reg 10%Z. clear RCM.
    zstep. zstep. zstep; fix_lit_store.
    p3b_hooks sp FR FRj ST.
    all: try (intros _; eassumption).
Qed.

Lemma allocate_p3b_al_spec : forall sp gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
    fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12
    (F : bvmap 5 word) fc (m : mem) (n AB B T lo b1 : Z) (h0 uj lj j0 : list byte) (ctx : word),
  (1 <= n <= 2^31)%Z -> (kHighShadowEnd < AB)%Z -> (AB + needed2 n <= kHighMemEnd + 1)%Z -> (0 <= b1 < 256)%Z ->
  alloc_frame32 m (bv_unsigned sp) fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 -> rw_cells asegs m (bv_unsigned sp) [CB 8 j0] ->
  rw_cells asegs m (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells asegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [CB 16 lj])%Z ->
  rw_cells asegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] ->
  rw_cells asegs m (g_asan_flags + 44) [C4 (Z_to_bv 64 4096)] -> rw_cells asegs m (g_asan_flags + 52) [C4 (Z_to_bv 64 190)] ->
  setshadow_cells m ->
  rw_cells asegs m 0x16ae90 [C8 (Z_to_bv 64 16)] -> rw_cells asegs m (tpA + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m g_MFHooks [C8 (Z_to_bv 64 0)] ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x6ca000 <= lo)%Z -> (bv_unsigned sp + 128 <= 2^63)%Z ->
  (AB + needed2 n <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_post fr0 fr1 fr2 fr3 fr4 fr5 fr6 fr7 fr8 fr9 fr10 fr11 fr12 sp gp (Z_to_bv 64 tpA) F fc n AB b1 ctx lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AB) s3v
             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v (Z_to_bv 64 B) (Z_to_bv 64 0) s9v
             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x5bd14) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros Hn HAB HABl Hb1 FR FRj HD UJ LJ GAF FL1 FL2 SS GLS TLS MFH ST HLO HIMG HSP HABlo MI.
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  unfold alloc_frame32 in FR.
  unfold kHighShadowEnd, kHighMemEnd, g_GOT_asan_flags, g_asan_flags, g_MFHooks, tpA, g_got_real_memset, g_real_memset,
    musl_memset_entry in *.
  change (1512504 + 44)%Z with 1512548%Z in FL1. change (1512504 + 52)%Z with 1512556%Z in FL2. change (6979176 + 16)%Z with 6979192%Z in TLS.
  move GAF at bottom. move GLS at bottom. move FL1 at bottom. move FL2 at bottom.
  move MFH at bottom. move TLS at bottom.
  pose proof (munch_refl [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (bv_unsigned sp - 32, bv_unsigned sp + 128)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zhide.
  do 4 zstep. ifF.
  do 2 zstep. rewrite (sx32_small_A 4096) by lia.
  destruct (Z.ltb_spec n 4096) as [C|C].
  - ifT. eapply allocate_p3b_fill_al; try eassumption. rewrite Z.min_l by lia. reflexivity.
  - ifF. zstep. eapply allocate_p3b_fill_al; try eassumption. rewrite Z.min_r by lia. reflexivity.
Qed.
