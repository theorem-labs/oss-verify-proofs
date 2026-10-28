(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr R_leaves R_fs2 R_gc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_na H A a
    | H : ro_cells segs m ?A _ |- _ => zidle_na H A a
    | H : u8arr segs m ?A _ |- _ => zidle_na H A a
    | H : u32arr segs m ?A _ |- _ => zidle_na H A a
    | H : u64arr segs m ?A _ |- _ => zidle_na H A a
    | H : bytes_at segs m ?A _ |- _ => zidle_na H A a
    | H : u8ro segs m ?A _ |- _ => zidle_na H A a
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
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.

Lemma stack_malloc_2_tail : forall (rax : word) ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB h : Z) (fl : list Z) (lo : Z),
  fs_const FSB m -> fs_hint FSB 2 m h -> fs_flags FSB 2 m fl -> flags_ok 2 fl -> (nbusy fl < 4096)%nat -> 0 <= h < 2 ^ 61 ->
  fs_free_frames FSB 2 m fl -> rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)] ->
  m2s_cells m ->
  FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  rw_cells bsegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> stk bsegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 208 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv bsegs m ->
  evt bsegs (sm2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 tpA) t0 t1 t2 sp (Z_to_bv 64 FSB) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a6a0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC HI FL OK NB HH FF TLS M2S FSOK HLO FSL FR ST LO SPH MI.
  pose proof OK as (LEN & _). rewrite NF_2 in LEN.
  destruct (scan_target_exists fl 4096 h LEN ltac:(lia)) as (j & SC).
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  set (pos := (h + Z.of_nat j) mod 4096) in *.
  assert (Hpos : 0 <= pos < 4096) by (apply Z.mod_pos_bound; lia).
  destruct (FF pos ltac:(rewrite NF_2; lia) Hfree) as [[junkF FRm] [junkS SHm]].
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. rewrite fsz_2 in FRm, SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in FRm, SHm.
  unfold frame_addr, fsz in FRm, SHm.
  change (2 * 2 ^ 20) with 2097152 in FRm. change (64 * 2 ^ 2) with 256 in FRm. change (Z.to_nat 256) with 256%nat in FRm.
  change (2 * 2 ^ 17) with 262144 in SHm. change (256 / 8) with 32 in SHm. change (Z.to_nat 32) with 32%nat in SHm.
  replace (FSB + 36864 + 2097152 + pos * 256) with (FSB + 2134016 + pos * 256) in FRm by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 262144 + pos * 32) with (F8 + pos * 32 + 2147717632) in SHm by (unfold SHB; lia).
  unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 2)) with 24576 in FL.
  replace (FSB + 4096 + 24576) with (FSB + 28672) in FL by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 4096) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm2_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (sm_W 2 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
  change (2 * 2 ^ 20) with 2097152 in MU. change (64 * 2 ^ 2) with 256 in MU. change (2 * 2 ^ 17) with 262144 in MU.
  change (256 / 8) with 32 in MU. change (32768 - 2 ^ (15 - 2)) with 24576 in MU. unfold SHB in MU.
  replace (FSB + 36864 + 2097152 + pos * 256) with (FSB + 2134016 + pos * 256) in MU by lia.
  replace (FSB + 4096 + 24576) with (FSB + 28672) in MU by lia.
  replace (2147450880 + FSB / 8 + 4608 + 262144 + pos * 32) with (F8 + pos * 32 + 2147717632) in MU
    by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
  replace (FSB + 8 * 2) with (FSB + 16) in MU, HI by lia.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  unfold tpA.
  do 5 zstep. ifF.
  zhide. do 15 zstep.
  replace (Z_to_bv 64 (FSB + 28672)) with (Z_to_bv 64 (fl_base FSB 2)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
  eapply (fs2_scan0 _ m FSB h fl j).
  1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 2)) with 24576.
      replace (FSB + 4096 + 24576) with (FSB + 28672) by lia. exact FL. }
  all: try assumption; try lia.
  1:{ unfold fl_base, flags_off. cbn. lia. }
  intros t0' a0'.
  change ((h + Z.of_nat j) mod 4096) with pos.
  replace (fl_base FSB 2) with (FSB + 28672) by (unfold fl_base, flags_off; cbn; lia).
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok bsegs mm (FSB + 28672) (map b8 fl) pos (wa (FSB + 28672 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write bsegs mm (FSB + 28672) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
  do 7 zstep.
  assert (SH8 : pos ≪ 8 = pos * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH8.
  replace (FSB + 36864 + (2097152 + pos * 256)) with (FSB + 2134016 + pos * 256) by lia.
  do 2 zstep.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 2134016 + pos * 256)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 2134016 + pos * 256) = F8 + pos * 32 + 2147717632).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 2134016 + pos * 256) with ((F8 + 266752 + pos * 32) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite ESH. clear TLS M2a M2b M2c.
  do 3 zstep.
  zidle_begin_at (F8 + pos * 32 + 2147717632)%Z 32%Z MUz WMz.
  do 4 lstep.
  zidle_end MUz WMz.
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  assert (EFR : FSB + 2134016 + pos * 256 = frame_addr FSB 2 pos) by (unfold frame_addr, fsz; cbn; lia).
  rewrite EFR.
  apply evt_done. unfold sm2_post. change ((h + Z.of_nat j) mod 4096) with pos.
  do 15 eexists. exists m1. do 2 eexists.
  split; [reflexivity|]. change ((h + Z.of_nat j) mod 4096) with pos.
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (MU' : munch (sm_W 2 FSB pos (bv_unsigned sp)) m m1).
  { replace (sm_W 2 FSB pos (bv_unsigned sp)) with
      [(FSB + 16, FSB + 16 + 8); (FSB + 28672 + pos, FSB + 28672 + pos + 1);
       (FSB + 2134016 + pos * 256, FSB + 2134016 + pos * 256 + 256);
       (F8 + pos * 32 + 2147717632, F8 + pos * 32 + 2147717632 + 32);
       (bv_unsigned sp - 208, bv_unsigned sp)]; [exact MU|].
    unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (2 * 2 ^ 20) with 2097152. change (64 * 2 ^ 2) with 256. change (2 * 2 ^ 17) with 262144.
    change (256 / 8) with 32. change (32768 - 2 ^ (15 - 2)) with 24576.
    repeat (f_equal; try lia). }
  split; [exact MU'|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv _ _ |- _ => exact H end|]. split; [exact ST|].
  split; [change (Z.to_nat 4096) with 4096%nat in Hj; exact Hj|]. split; [exact Hfree|].
  split; [exact HI|]. split; [exact FC|].
  split.
  { unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 2) with (FSB + 28672) by (unfold fl_base, flags_off; cbn; lia).
    exact FL2. }
  split.
  { rewrite <- EFR. replace (fl_base FSB 2 + pos) with (FSB + 28672 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FRm. }
  split.
  { rewrite <- EFR, ESH. exact SHm. }
  apply (fs_free_frames_transport FSB 2 m m1 _ _ (fs_free_frames_take FSB 2 m fl (Z.to_nat pos) FF) MU' WM).
  intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. rewrite NF_2 in Hp.
  assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
  unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
  change (2 * 2 ^ 20) with 2097152. change (64 * 2 ^ 2) with 256. change (2 * 2 ^ 17) with 262144.
  change (256 / 8) with 32. change (32768 - 2 ^ (15 - 2)) with 24576.
  cbn [disjoint_from]. split; repeat split; lia.
Qed.

Definition sm2_gc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB h : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists mg : mem,
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (FSB + 0x60, FSB + 0x61)] m mg /\ wmono bsegs m mg /\ fs_const FSB mg
    /\ sm2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo mg ms'.

Lemma stack_malloc_2_gc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB h : Z) (fl : list Z) (DTV dtvbeg TCX T lo : Z) (tb te : word) (top bottom : Z) (gfl : word),
  rw_cells bsegs m (FSB + 0x58) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 1)] -> fs_hint FSB 2 m h -> fs_flags FSB 2 m fl -> flags_ok 2 fl -> (nbusy fl < 4096)%nat -> 0 <= h < 2 ^ 61 ->
  fs_free_frames FSB 2 m fl -> rw_cells bsegs m tpA [C8 (Z_to_bv 64 FSB)] ->
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
  FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> bv_unsigned sp <= 2 ^ 47 ->
  stack_cells T top bottom m -> 0 <= bottom < top -> bottom <= bv_unsigned sp <= top -> top < 2 ^ 63 ->
  (forall c, 0 <= c <= 10 -> u8arr bsegs m (fl_base FSB c) (repeat (b8 0) (Z.to_nat (NF c)))) -> ro_cells bsegs m 0x17fec0 [C8 gfl] ->
  mem_inv bsegs m ->
  evt bsegs (sm2_gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sm2_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until gfl. intros FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH SC B0 RS TOP FLZ GF MI.
  pose proof OK as (LEN & _). rewrite NF_2 in LEN.
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 2)) with 24576 in FL.
  replace (FSB + 4096 + 24576) with (FSB + 28672) in FL by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 4096) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
  destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm2_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  replace (FSB + 8 * 2) with (FSB + 16) in HI by lia.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (FSB + 0x60, FSB + 0x61)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct SC as [SC1 SC2]. unfold off_t_stack_top, off_t_stack_switching in SC1, SC2.
  carve_frame 32%nat ST.
  zidle_begin sp 32%Z MUz WMz.
  zhide.
  zhide. do 9 zstep.
  zidle_end MUz WMz.
  sp_facts.
  call (tls_get_addr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ DTV dtvbeg TCX T lo tb te).
  1: exact (conj AI (conj RL (conj DP (conj D1 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 G8))))))))))).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  1: exact TT.
  all: rewrite ?Esp; try lia; try assumption.
  rewrite Esp in POST. rename POST into ST.
  clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 TT.
  unfold tpA. zstep. zstep. ifF.

  do 3 zstep. ifF. zstep. zstep. zstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FLZ' : forall c, 0 <= c <= 10 -> u8arr bsegs mm (fl_base FSB c) (repeat (b8 0) (Z.to_nat (NF c))))
      by (intros c Hc; pose proof (fl_range FSB c Hc) as R; apply (u8arr_transport bsegs _ m mm _ _ (FLZ c Hc) MU WM);
          rewrite repeat_length, Z2Nat.id by (unfold NF; apply Z.pow_nonneg; lia); cbn [disjoint_from fst snd]; unfold kFakeStackSize in *; clear_big; lia) end.
  clear FLZ. change 7070696 with tpA.
  call (gc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ sp FSB TCX T top bottom lo (Z_to_bv 8 1) gfl).
  1: exact (conj (conj KI (conj K (conj TS T0))) TX).
  1: exact (conj SC1 SC2).
  all: rewrite ?Esp; try lia; try assumption; try exact (conj M2a (conj M2b M2c)); try (unfold kFakeStackSize in *; lia).
  rewrite ?Esp in *. clear FLZ'. try clear KI. try clear K. try clear TS. try clear T0. try clear TX. try clear SC1. try clear SC2. try clear GF.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
    eapply evt_mono; [ eapply (stack_malloc_2_tail _ ra sp gp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mg FSB h fl lo) |] end.
  all: try eassumption.
  all: try (unfold kFakeStackSize in *; lia).
  all: lazymatch goal with
       | |- m2s_cells _ => exact (conj M2a (conj M2b M2c))
       | |- fs_flags _ _ _ _ =>
           unfold fs_flags; lazymatch type of FL with u8arr _ _ ?B _ => lazymatch goal with |- u8arr _ _ ?B' _ =>
             replace B' with B by (unfold fl_base, flags_off; cbn; lia) end end; exact FL
       | |- fs_free_frames _ _ _ _ =>

           apply (fs_free_frames_transport FSB 2 m _ _ _ FF MU WM); intros p Hp Hf;
           pose proof (frame_addr_range FSB 2 p ltac:(lia) Hp) as [FA1 FA2];
           unfold shad; rewrite fsz_2 in *; change (fsz 2) with 256 in *; change (256 / 8) with 32;
           cbn [disjoint_from fst snd]; unfold kFakeStackSize, kHighShadowEnd, SHB in *; clear_big;
           repeat split; try exact I; Z.div_mod_to_equations; lia
       | |- forall _, _ -> _ => intros ms' POST'; eexists; split; [exact MU|]; split; [exact WM|]; split; [assumption | exact POST']
       | |- ?g => fail "GC arm: premise of the tail not discharged:" g
       end.
Qed.
