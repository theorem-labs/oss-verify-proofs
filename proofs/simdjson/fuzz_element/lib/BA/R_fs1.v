(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Lemma land8191 : forall x, 0 <= x -> Z.land x 8191 = x mod 8192.
Proof. intros x Hx. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fs1_scan : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 1 m fl -> Z.of_nat (length fl) = 8192 -> flags_ok 1 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 1 + 8192 <= 2 ^ 47 ->
  scan_from fl 8192 h (Z.to_nat 8192) = Some j ->
  (forall t0 a0, evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 1)) (Z_to_bv 64 8191)
               (Z_to_bv 64 (fl_base FSB 1 + (h + Z.of_nat j) mod 8192)) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 8192))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x66f30) fc None m (seg_rom asegs))) ->
  mem_inv asegs m ->
  forall (k : nat), (k <= j)%nat -> forall t0 a5 a7,
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (8192 - Z.of_nat (j - k))) a1 (Z_to_bv 64 (h + Z.of_nat (j - k)))
             (Z_to_bv 64 (fl_base FSB 1)) (Z_to_bv 64 8191) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x66eb8) fc None m (seg_rom asegs)).
Proof.
  intros until fc. intros FL LEN OK HH HF HB SC K MI.
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  induction k as [|k IH]; intros Hk t0 a5 a7.
  - rewrite Nat.sub_0_r.
    assert (E1 : Z.land (h + Z.of_nat j) 8191 = (h + Z.of_nat j) mod 8192) by (apply land8191; lia).
    zhide.
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat j) mod 8192) in *.
    assert (Hpos : 0 <= pos < 8192) by (apply Z.mod_pos_bound; lia).
    pose proof (u8arr_read asegs m (fl_base FSB 1) (map b8 fl) pos (b8 0) (Z_to_bv 64 (fl_base FSB 1 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hfree in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
    zstep. ifT.
    exact (K _ _).
  - set (i := (j - S k)%nat) in *.
    assert (Hi : (i < j)%nat) by (unfold i; lia).
    assert (E1 : Z.land (h + Z.of_nat i) 8191 = (h + Z.of_nat i) mod 8192) by (apply land8191; lia).
    do 2 zstep. rewrite E1.
    set (pos := (h + Z.of_nat i) mod 8192) in *.
    assert (Hpos : 0 <= pos < 8192) by (apply Z.mod_pos_bound; lia).
    assert (Hb1 : nth (Z.to_nat pos) fl 1 = 1).
    { destruct (flags_ok_nth 1 fl (Z.to_nat pos) OK ltac:(lia)) as [H0|H0]; [|exact H0].
      exfalso. exact (Hbusy i Hi H0). }
    pose proof (u8arr_read asegs m (fl_base FSB 1) (map b8 fl) pos (b8 1) (Z_to_bv 64 (fl_base FSB 1 + pos)) FL) as RD.
    rewrite nth_error_map_b8, Hb1 in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 1)) with (Z_to_bv 64 1).
    zstep. ifF.
    do 2 zstep.
    replace (bv_swrap 32 (8192 - Z.of_nat i + -1)) with (8192 - Z.of_nat (j - k)).
    2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. unfold i in *. lia. }
    replace (h + Z.of_nat i + 1) with (h + Z.of_nat (j - k)) by (unfold i in *; lia).
    zstep. ifT.
    apply IH. lia.
Qed.

Corollary fs1_scan0 : forall (Q : machine_state -> Prop) (m : mem) (FSB h : Z) (fl : list Z) (j : nat)
    ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
  fs_flags FSB 1 m fl -> Z.of_nat (length fl) = 8192 -> flags_ok 1 fl ->
  0 <= h < 2 ^ 61 -> 0 < FSB -> fl_base FSB 1 + 8192 <= 2 ^ 47 ->
  scan_from fl 8192 h (Z.to_nat 8192) = Some j ->
  (forall t0 a0, evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (h + Z.of_nat j)) (Z_to_bv 64 (fl_base FSB 1)) (Z_to_bv 64 8191)
               (Z_to_bv 64 (fl_base FSB 1 + (h + Z.of_nat j) mod 8192)) a6 (Z_to_bv 64 ((h + Z.of_nat j) mod 8192))
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x66f30) fc None m (seg_rom asegs))) ->
  mem_inv asegs m ->
  forall t0 a5 a7,
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 8192) a1 (Z_to_bv 64 h)
             (Z_to_bv 64 (fl_base FSB 1)) (Z_to_bv 64 8191) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x66eb8) fc None m (seg_rom asegs)).
Proof.
  intros. pose proof (fs1_scan Q m FSB h fl j ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    H H0 H1 H2 H3 H4 H5 H6 H7 j ltac:(lia) t0 a5 a7) as X.
  rewrite Nat.sub_diag in X. cbn [Z.of_nat] in X. rewrite Z.sub_0_r, Z.add_0_r in X. exact X.
Qed.

Definition sm1_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB h : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (j : nat) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) junk1 junk2,
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 (Z_to_bv 64 (frame_addr FSB 1 ((h + Z.of_nat j) mod 8192)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm_W 1 FSB ((h + Z.of_nat j) mod 8192) (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ (j < Z.to_nat 8192)%nat /\ nth (Z.to_nat ((h + Z.of_nat j) mod 8192)) fl 1 = 0
    /\ fs_hint FSB 1 m' (h + Z.of_nat j + 1) /\ fs_const FSB m'
    /\ fs_flags FSB 1 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 8192)) 1)
    /\ rw_cells asegs m' (frame_addr FSB 1 ((h + Z.of_nat j) mod 8192))
         [CB 24 junk1; C8 sp; CB 88 junk2; C8 (Z_to_bv 64 (fl_base FSB 1 + (h + Z.of_nat j) mod 8192))]
    /\ rw_cells asegs m' (shad (frame_addr FSB 1 ((h + Z.of_nat j) mod 8192)))
         [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ fs_free_frames FSB 1 m' (upd fl (Z.to_nat ((h + Z.of_nat j) mod 8192)) 1).

Definition sm1_entry : Z := 0x66e24.

Lemma stack_malloc_1_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FSB h : Z) (fl : list Z) (DTV dtvbeg TCX T lo : Z) (tb te : word),
  fs_const FSB m -> fs_hint FSB 1 m h -> fs_flags FSB 1 m fl -> flags_ok 1 fl -> (nbusy fl < Z.to_nat 8192)%nat -> 0 <= h < 2 ^ 61 ->
  fs_free_frames FSB 1 m fl -> rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)] ->
  tga_cells DTV dtvbeg m -> thread_cells TCX T m -> ttls_cells T m tb te -> m2s_cells m ->
  FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
  0 < DTV -> DTV + 4096 <= lo -> 0 < dtvbeg < 2 ^ 64 -> 0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (sm1_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB h fl lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 sm1_entry) fc None m (seg_rom asegs)).
Proof.
  intros until te. intros FC HI FL OK NB HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL HB HX HXL HT HTL ST LO SPH MI.
  pose proof OK as (LEN & _). rewrite NF_1 in LEN.
  destruct (scan_target_exists fl 8192 h LEN ltac:(lia)) as (j & SC).
  destruct (scan_from_spec _ _ _ _ _ SC) as (Hj & Hfree & Hbusy).
  set (pos := (h + Z.of_nat j) mod 8192) in *.
  assert (Hpos : 0 <= pos < 8192) by (apply Z.mod_pos_bound; lia).
  destruct (FF pos ltac:(rewrite NF_1; lia) Hfree) as [[junkF FRm] [junkS SHm]].
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
  rewrite shad_frame in SHm by lia. rewrite fsz_1 in FRm, SHm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in FRm, SHm.
  unfold frame_addr, fsz in FRm, SHm.
  change (1 * 2 ^ 20) with 1048576 in FRm. change (64 * 2 ^ 1) with 128 in FRm. change (Z.to_nat 128) with 128%nat in FRm.
  change (1 * 2 ^ 17) with 131072 in SHm. change (128 / 8) with 16 in SHm. change (Z.to_nat 16) with 16%nat in SHm.
  replace (FSB + 36864 + 1048576 + pos * 128) with (FSB + 1085440 + pos * 128) in FRm by lia.
  set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
  clearbody F8.
  replace (SHB + F8 + 4608 + 131072 + pos * 16) with (F8 + pos * 16 + 2147586560) in SHm by (unfold SHB; lia).
  unfold fs_flags, fl_base, flags_off in FL. change (32768 - 2 ^ (15 - 1)) with 16384 in FL.
  replace (FSB + 4096 + 16384) with (FSB + 20480) in FL by lia.
  assert (LENM : Z.of_nat (length (map b8 fl)) = 8192) by (rewrite length_map; exact LEN).
  destruct M2S as (M2a & M2b & M2c).
  destruct TGA as (AI & RL & DP & D1 & DC). destruct TC as (TS & TX). destruct TS as (KI & K & TS & T0).
  destruct DC as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold fs_const, fs_hint, ttls_cells, tpA, g_real_tls_get_addr, musl_tls_get_addr_entry, g_tls_index, g_dtv_ptr, g_dtv, g_dtv1,
    dtv1_val, g_got_common_flags, g_common_flags, g_intercept_tls_get_addr, g_got_verbosity, g_current_verbosity,
    g_got_dtls_off, g_tls_dtls, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, sm1_entry in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (sm_W 1 FSB pos (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold sm_W in MU. rewrite shad_frame in MU by lia. unfold frame_addr, fsz, fl_base, flags_off in MU.
  change (1 * 2 ^ 20) with 1048576 in MU. change (64 * 2 ^ 1) with 128 in MU. change (1 * 2 ^ 17) with 131072 in MU.
  change (128 / 8) with 16 in MU. change (32768 - 2 ^ (15 - 1)) with 16384 in MU. unfold SHB in MU.
  replace (FSB + 36864 + 1048576 + pos * 128) with (FSB + 1085440 + pos * 128) in MU by lia.
  replace (FSB + 4096 + 16384) with (FSB + 20480) in MU by lia.
  replace (2147450880 + FSB / 8 + 4608 + 131072 + pos * 16) with (F8 + pos * 16 + 2147586560) in MU
    by (rewrite EF8, (Z.mul_comm 8 F8), Z.div_mul by lia; lia).
  replace (FSB + 8 * 1) with (FSB + 8) in MU, HI by lia.
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
  clear AI RL DP D1 G1 G2 G3 G4 G5 G6 G7 G8 KI K TS T0 TX TT.
  unfold tpA. zstep. zstep. ifF.
  do 3 zstep. ifT.
  do 5 zstep. ifF.
  zhide. do 15 zstep.
  replace (Z_to_bv 64 (FSB + 20480)) with (Z_to_bv 64 (fl_base FSB 1)) by (unfold fl_base, flags_off; f_equal; cbn; lia).
  eapply (fs1_scan0 _ x13 FSB h fl j).
  1:{ unfold fs_flags, fl_base, flags_off. change (32768 - 2 ^ (15 - 1)) with 16384.
      replace (FSB + 4096 + 16384) with (FSB + 20480) by lia. exact FL. }
  all: try assumption; try lia.
  1:{ unfold fl_base, flags_off. cbn. lia. }
  intros t0' a0'.
  change ((h + Z.of_nat j) mod 8192) with pos.
  replace (fl_base FSB 1) with (FSB + 20480) by (unfold fl_base, flags_off; cbn; lia).
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok asegs mm (FSB + 20480) (map b8 fl) pos (wa (FSB + 20480 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
    pose proof (u8arr_write asegs mm (FSB + 20480) (map b8 fl) pos (b8 1) FL ltac:(lia)) as FL2 end.
  zstep. change (le1 (Z_to_bv 64 1)) with [b8 1]. clear FL. store_done.
  do 5 zstep.
  assert (SH7 : pos ≪ 7 = pos * 128) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). rewrite SH7.
  replace (FSB + 36864 + (1048576 + pos * 128)) with (FSB + 1085440 + pos * 128) by lia.
  do 2 zstep.
  zstep. zstep.
  call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 1085440 + pos * 128)).
  1: reflexivity.
  1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
  1: exact (conj M2a (conj M2b M2c)).
  1: assumption.
  assert (ESH : shad (FSB + 1085440 + pos * 128) = F8 + pos * 16 + 2147586560).
  { unfold shad, SHB. rewrite EF8. replace (8 * F8 + 1085440 + pos * 128) with ((F8 + 135680 + pos * 16) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite ESH. clear TLS M2a M2b M2c.
  do 3 zstep.
  zidle_begin_at (F8 + pos * 16 + 2147586560)%Z 16%Z MUz WMz.
  do 2 lstep.
  zidle_end MUz WMz.
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  assert (EFR : FSB + 1085440 + pos * 128 = frame_addr FSB 1 pos) by (unfold frame_addr, fsz; cbn; lia).
  rewrite EFR.
  apply evt_done. unfold sm1_post. change ((h + Z.of_nat j) mod 8192) with pos.
  do 15 eexists. exists m1. do 2 eexists.
  split; [reflexivity|]. change ((h + Z.of_nat j) mod 8192) with pos.
  assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (MU' : munch (sm_W 1 FSB pos (bv_unsigned sp)) m m1).
  { replace (sm_W 1 FSB pos (bv_unsigned sp)) with
      [(FSB + 8, FSB + 8 + 8); (FSB + 20480 + pos, FSB + 20480 + pos + 1);
       (FSB + 1085440 + pos * 128, FSB + 1085440 + pos * 128 + 128);
       (F8 + pos * 16 + 2147586560, F8 + pos * 16 + 2147586560 + 16);
       (bv_unsigned sp - 208, bv_unsigned sp)]; [exact MU|].
    unfold sm_W. rewrite shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
    change (1 * 2 ^ 20) with 1048576. change (64 * 2 ^ 1) with 128. change (1 * 2 ^ 17) with 131072.
    change (128 / 8) with 16. change (32768 - 2 ^ (15 - 1)) with 16384.
    repeat (f_equal; try lia). }
  split; [exact MU'|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact Hj|]. split; [exact Hfree|].
  split; [exact HI|]. split; [exact FC|].
  split.
  { unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 1) with (FSB + 20480) by (unfold fl_base, flags_off; cbn; lia).
    exact FL2. }
  split.
  { rewrite <- EFR. replace (fl_base FSB 1 + pos) with (FSB + 20480 + pos) by (unfold fl_base, flags_off; cbn; lia). exact FRm. }
  split.
  { rewrite <- EFR, ESH. exact SHm. }
  apply (fs_free_frames_transport FSB 1 m m1 _ _ (fs_free_frames_take FSB 1 m fl (Z.to_nat pos) FF) MU' WM).
  intros p Hp Hf. pose proof (nth_upd_free_other _ _ _ Hf) as Hne. rewrite NF_1 in Hp.
  assert (Hne' : p <> pos) by (intro E; apply Hne; rewrite E; reflexivity).
  unfold sm_W. rewrite !shad_frame by lia. rewrite EQ8. unfold frame_addr, fsz, fl_base, flags_off, SHB.
  change (1 * 2 ^ 20) with 1048576. change (64 * 2 ^ 1) with 128. change (1 * 2 ^ 17) with 131072.
  change (128 / 8) with 16. change (32768 - 2 ^ (15 - 1)) with 16384.
  cbn [disjoint_from]. split; repeat split; lia.
Qed.

End GWIN.
