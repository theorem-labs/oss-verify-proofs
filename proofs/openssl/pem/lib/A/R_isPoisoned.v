(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs I_consts R_memiszero.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma sxb_small : forall b : byte, (bv_unsigned b < 128)%Z -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb. f_equal. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2)%Z with 128%Z. change (2 ^ 8)%Z with 256%Z.
  rewrite Z.mod_small; lia.
Qed.

Lemma signed_lit64 : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63)%Z. lia.
Qed.

Lemma land7 : forall x, (0 <= x)%Z -> Z.land x 7 = (x mod 8)%Z.
Proof. intros x Hx. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac ifT_s := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota| symmetry; unfold_cond; rewrite ?signed_lit64 by lia; rewrite ?unsigned_lit by lia;
                                  solve_cond_rec] end.
Ltac ifF_s := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; unfold_cond; rewrite ?signed_lit64 by lia; rewrite ?unsigned_lit by lia;
                                   solve_cond_rec] end.

(* [comment removed for export] *)
Lemma acc_transport1 : forall L H (m m' : mem) a n, acc asegs m a n -> munch [(L, H)] m m' -> (0 <= a)%Z -> (0 <= n)%Z ->
  (shad (a + n) < L)%Z -> acc asegs m' a n.
Proof.
  intros L H m m' a n ACC MU Ha Hn HL i Hi. destruct (ACC i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_transport asegs [(L, H)] m m' _ _ Hb MU). cbn [disjoint_from length Z.of_nat].
  assert (shad (a + i) <= shad (a + n))%Z by (unfold shad; pose proof (Z.div_le_mono (a + i) (a + n) 8 ltac:(lia) ltac:(lia)); lia).
  split; [left; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros_of : forall (m : mem) a n, (0 <= a)%Z -> (0 <= n)%Z -> (a + n <= 2^64)%Z ->
  (forall j, (0 <= j < n)%Z -> bytes_at asegs m (a + j) [z8]) -> bytes_at asegs m a (repeat z8 (Z.to_nat n)).
Proof.
  intros m a n Ha Hn Hb H. split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & Hr). specialize (Hr 0%nat ltac:(cbn; lia)).
  rewrite Z.add_0_r in Hr. rewrite Hr. cbn [nth_error]. rewrite nth_error_repeat by lia. reflexivity.
Qed.

Lemma acc_full_granules : forall (m : mem) beg size, acc asegs m beg size -> (0 <= beg)%Z -> (0 <= size)%Z ->
  (beg + size <= 2^60)%Z ->
  bytes_at asegs m (shad ((beg + 7) / 8 * 8))
    (repeat z8 (Z.to_nat (shad ((beg + size) / 8 * 8) - shad ((beg + 7) / 8 * 8)))).
Proof.
  intros m beg size ACC Hb Hs Hend.
  assert (E1 : shad ((beg + 7) / 8 * 8) = ((beg + 7) / 8 + SHB)%Z) by (unfold shad; rewrite Z.div_mul by lia; reflexivity).
  assert (E2 : shad ((beg + size) / 8 * 8) = ((beg + size) / 8 + SHB)%Z) by (unfold shad; rewrite Z.div_mul by lia; reflexivity).
  rewrite E1, E2.
  destruct (Z.le_gt_cases ((beg + size) / 8) ((beg + 7) / 8)) as [C|C].
  - replace (Z.to_nat ((beg + size) / 8 + SHB - ((beg + 7) / 8 + SHB))) with 0%nat by lia.
    apply bytes_at_nil. unfold SHB. pose proof (Z.div_pos (beg + 7) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (beg + 7) 8 (2^61) ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_pos (beg + 7) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (beg + size) 8 (2^61) ltac:(lia) ltac:(lia)).
    apply bytes_at_zeros_of; [unfold SHB; lia| lia| unfold SHB; lia|].
    intros j Hj.
    assert (G : ((beg + 7) / 8 + SHB + j)%Z = shad (((beg + 7) / 8 + j) * 8)).
    { unfold shad. rewrite Z.div_mul by lia. lia. }
    rewrite G. apply acc_granule_zero; [apply Z.mod_mul; lia|].
    pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + size) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)).
    apply (acc_sub asegs m beg size); [exact ACC| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma acc_read : forall (m : mem) beg size i, acc asegs m beg size -> (0 <= i < size)%Z ->
  exists b, ov_read_bytes asegs m (Z_to_bv 64 (2147450880 + (beg + i) ≫ 3)) 1 = Some [b] /\ sh_ok b (beg + i).
Proof.
  intros m beg size i ACC Hi. destruct (ACC i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  pose proof (bytes_at_ov_read asegs m _ [b] 0 1 Hb ltac:(cbn; lia)) as R. cbn [firstn skipn] in R.
  rewrite <- R. unfold wa. f_equal. f_equal. unfold shad, SHB. rewrite Z.shiftr_div_pow2 by lia. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma rip_j55338 : forall ra ra' sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (beg size lo : Z) junk,
  acc asegs m0 beg size -> (0 < size <= 2^40)%Z -> region_in_mem beg size ->
  rw_cells asegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 80)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m0)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 beg) (Z_to_bv 64 size)
             (Z_to_bv 64 (shad ((beg + size) / 8 * 8))) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (shad ((beg + 7) / 8 * 8))) s4 (Z_to_bv 64 6736696) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c503c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ACC HSZ HRIM FR ST HLO HLOH MU WM MI.
  assert (HR : (0 <= beg /\ beg + size + 8 <= kHighMemEnd)%Z) by (unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in *; lia).
  unfold kHighMemEnd, kHighShadowEnd in *.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = (bv_unsigned sp - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (beg + size) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)) as D4.
  assert (SHR : (0x7fff8000 <= shad ((beg + 7) / 8 * 8) <= 0x10007fff8000 /\
                 0x7fff8000 <= shad ((beg + size) / 8 * 8) <= 0x10007fff8000)%Z).
  { unfold shad, SHB. rewrite !Z.div_mul by lia.
    pose proof (Z.div_pos (beg + 7) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (beg + size) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (beg + 7) 8 (2^47) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (beg + size) 8 (2^47) ltac:(lia) ltac:(lia)). lia. }
  zstep.
  destruct (Z.le_gt_cases (shad ((beg + size) / 8 * 8)) (shad ((beg + 7) / 8 * 8))) as [C|C].
  - ifT.
    do 10 zstep.
    replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
  - ifF.
    pose proof (acc_transport1 _ _ m0 m beg size ACC MU ltac:(lia) ltac:(lia)
                  ltac:(unfold shad, SHB; pose proof (Z.div_le_upper_bound (beg + size) 8 (2^47) ltac:(lia) ltac:(lia)); lia)) as ACCm.
    pose proof (acc_full_granules m beg size ACCm ltac:(lia) ltac:(lia) ltac:(lia)) as ZG.
    clear ACCm.
    do 3 zstep.
    call (memiszero_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad ((beg + 7) / 8 * 8))
            (shad ((beg + size) / 8 * 8) - shad ((beg + 7) / 8 * 8))%Z lo).
    all: rewrite ?Esp; try assumption; try lia.
    1:{ unfold shad, SHB in *. rewrite !Z.div_mul in * by lia. lia. }
    zstep. ifF.
    do 10 zstep.
    replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    rewrite Esp in POST.
    release_frame FR POST (bv_unsigned sp).
    zstep.
    finish.
Qed.

(* [comment removed for export] *)
Lemma rip_j552e4 : forall ra ra' sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (beg size lo : Z) junk,
  acc asegs m0 beg size -> (0 < size <= 2^40)%Z -> region_in_mem beg size ->
  rw_cells asegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 80)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m0)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 beg) (Z_to_bv 64 size)
             (Z_to_bv 64 (shad ((beg + size) / 8 * 8))) (Z_to_bv 64 2147450880) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (beg + size)) (Z_to_bv 64 (shad ((beg + 7) / 8 * 8))) s4 (Z_to_bv 64 6736696) s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c4fe8) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ACC HSZ HRIM FR ST HLO HLOH MU WM MI.
  assert (HR : (0 <= beg /\ beg + size + 8 <= kHighMemEnd)%Z) by (unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in *; lia).
  unfold kHighMemEnd, kHighShadowEnd in *.
  pose proof (acc_transport1 _ _ m0 m beg size ACC MU ltac:(lia) ltac:(lia)
                ltac:(unfold shad, SHB; pose proof (Z.div_le_upper_bound (beg + size) 8 (2^47) ltac:(lia) ltac:(lia)); lia)) as ACCm.
  destruct (acc_read m beg size (size - 1) ACCm ltac:(lia)) as (b & RD & OK). clear ACCm.
  replace (beg + (size - 1))%Z with (beg + size + -1)%Z in RD, OK by lia.
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn [Z.of_N] in Rb.
  destruct OK as [B0|[B1 B2]].
  - assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite B0; reflexivity). subst b.
    do 4 zstep. clear RD.
    zstep. ifT.
    eapply rip_j55338; eassumption.
  - do 4 zstep. clear RD.
    rewrite sxb_small by lia.
    zstep. ifF.
    zstep. rewrite land7 by lia.
    zstep. ifT_s.
    eapply rip_j55338; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rip_j552a8 : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (beg size lo : Z) junk,
  acc asegs m0 beg size -> (0 < size <= 2^40)%Z -> region_in_mem beg size -> m2s_cells m ->
  rw_cells asegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 80)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 beg) (Z_to_bv 64 size) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (beg + size)) s3 s4 (Z_to_bv 64 6736696) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c4fac) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ACC HSZ HRIM M2S FR ST HLO HLOH MU WM MI.
  assert (HR : (0 <= beg /\ beg + size + 8 <= kHighMemEnd)%Z) by (unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in *; lia).
  destruct M2S as (GOT & SH & HM).
  unfold SHB, kHighMemEnd, kHighShadowEnd in *.
  apply box in ACC.
  zstep. ifF.
  do 3 zstep.
  rewrite !land_m8 by lia.
  pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (beg + size) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (beg + size) 8 ltac:(lia)) as D4.
  zstep.
  call (m2s_54d48_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ ((beg + 7) / 8 * 8)%Z).
  1:{ reflexivity. }
  1:{ unfold addr_in_mem, region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. lia. }
  1:{ unfold m2s_cells, SHB, kHighMemEnd. split; [assumption| split; assumption]. }
  1:{ assumption. }
  do 3 zstep.
  call (m2s_54d48_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ ((beg + size) / 8 * 8)%Z).
  1:{ reflexivity. }
  1:{ unfold addr_in_mem, region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. lia. }
  1:{ unfold m2s_cells, SHB, kHighMemEnd. split; [assumption| split; assumption]. }
  1:{ assumption. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_transport1 _ _ m0 mm beg size (unbox _ ACC) MU ltac:(lia) ltac:(lia)
                  ltac:(unfold shad, SHB; pose proof (Z.div_le_upper_bound (beg + size) 8 (2^47) ltac:(lia) ltac:(lia)); lia)) as ACCm;
    destruct (acc_read mm beg size 0 ACCm ltac:(lia)) as (b & RD & OK); clear ACCm end.
  replace (beg + 0)%Z with beg in RD, OK by lia.
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn [Z.of_N] in Rb.
  destruct OK as [B0|[B1 B2]].
  - assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite B0; reflexivity). subst b.
    do 4 zstep. clear RD.
    zstep. ifT.
    eapply rip_j552e4; eassumption.
  - do 4 zstep. clear RD.
    rewrite sxb_small by lia.
    zstep. ifF.
    zstep. rewrite land7 by lia.
    zstep. ifF_s.
    eapply rip_j552e4; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rip_j55260 : forall ra sp gp tp t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (beg size lo : Z) junk,
  acc asegs m0 beg size -> (0 < size <= 2^40)%Z -> region_in_mem beg size -> m2s_cells m ->
  rw_cells asegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 80)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)]%Z lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 beg) (Z_to_bv 64 size) a0
             (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 6736696) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c4f64) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ACC HSZ HRIM M2S FR ST HLO HLOH MU WM MI.
  pose proof M2S as (GOT & SH & HM).
  unfold SHB, kHighMemEnd, kHighShadowEnd in *.
  zstep.
  replace (size + beg)%Z with (beg + size)%Z by lia.
  assert (HR : (0 <= beg /\ beg + size + 8 <= 140737488355327)%Z) by (unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in *; lia).
  pose proof HRIM as HRIM'. unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in HRIM'.
  destruct HRIM' as [HL|HH].
  - zstep. ifT. eapply rip_j552a8; eassumption.
  - zstep. ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (beg + size))) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit (beg + size)) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifF.
    eapply rip_j552a8; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rip_proof : rip_stmt.
Proof.
  unfold rip_stmt. intros until lo. intros -> -> ACC HSZ HRIM M2S ST HLO HLOH MI.
  pose proof M2S as (GOT & SH & HM).
  unfold e_region_is_poisoned, SHB, kHighMemEnd, kHighShadowEnd in *.
  assert (HR : (0 <= beg /\ beg + size + 8 <= 140737488355327)%Z) by (unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  apply box in ACC, M2S.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  do 1 zstep.
  ifF.
  do 9 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879)%Z with 2147450879%Z
    by reflexivity.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z in * by lia.
  pose proof HRIM as HRIM'. unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd in HRIM'.
  destruct HRIM' as [HL|HH].
  - zstep. ifT.
    eapply rip_j55260; try eassumption.
    unfold m2s_cells, SHB, kHighMemEnd. split; [assumption| split; assumption].
  - zstep. ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 beg)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit beg) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifF.
    eapply rip_j55260; try eassumption.
    unfold m2s_cells, SHB, kHighMemEnd. split; [assumption| split; assumption].
Qed.
