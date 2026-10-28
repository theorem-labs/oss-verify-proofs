(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_depot_defs R_depot_put R_asan_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition run_free_hooks_entry' : Z := 0x1d2c50.

(* [comment removed for export] *)
Lemma run_free_hooks_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells ctasegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)] ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0xbcb000 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 32, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 run_free_hooks_entry') fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros FH ST HLO HIMG MI. unfold run_free_hooks_entry', g_MFHooks in *.
  change (7355136 + 8)%Z with 7355144%Z in FH.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 32%nat ST.
  zhide.
  zidle_begin sp 32%Z MUz WMz.
  do 5 zstep.
  zidle_end MUz WMz.
  do 3 zstep. zstep. ifT.
  do 7 zstep. ifT.
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma z8_eq : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. exact H.
Qed.

Lemma le4_hdr : forall s b, (0 <= s < 256)%Z -> (0 <= b < 256)%Z ->
  le4 (Z_to_bv 64 (s + 256 * b)) = [Z_to_bv 8 s; Z_to_bv 8 b] ++ le2 (Z_to_bv 64 0).
Proof.
  intros s b Hs Hb. unfold le4, le2. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
  f_equal; [apply z8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [apply z8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [apply z8_eq; Z.div_mod_to_equations; lia|].
  f_equal. apply z8_eq. Z.div_mod_to_equations; lia.
Qed.

Lemma hdr3_to_c4 : forall (m : mem) A s b post, (0 <= s < 256)%Z -> (0 <= b < 256)%Z ->
  rw_cells ctasegs m A (C1 (Z_to_bv 8 s) :: C1 (Z_to_bv 8 b) :: C2 (Z_to_bv 64 0) :: post) ->
  rw_cells ctasegs m A (C4 (Z_to_bv 64 (s + 256 * b)) :: post).
Proof.
  intros m A s b post Hs Hb [[W B] R]. destruct W as (_ & _ & _ & W).
  split; [split|].
  - split; [exact I| exact W].
  - cbn [cells_bytes cbytes] in *. rewrite le4_hdr by assumption. rewrite <- app_assoc. exact B.
  - cbn [cells_size csize] in *. exact R.
Qed.

Lemma c4_to_hdr3 : forall (m : mem) A s b post, (0 <= s < 256)%Z -> (0 <= b < 256)%Z ->
  rw_cells ctasegs m A (C4 (Z_to_bv 64 (s + 256 * b)) :: post) ->
  rw_cells ctasegs m A (C1 (Z_to_bv 8 s) :: C1 (Z_to_bv 8 b) :: C2 (Z_to_bv 64 0) :: post).
Proof.
  intros m A s b post Hs Hb [[W B] R]. destruct W as (_ & W).
  split; [split|].
  - split; [exact I| split; [exact I| split; [exact I| exact W]]].
  - cbn [cells_bytes cbytes] in *. rewrite le4_hdr in B by assumption. rewrite <- app_assoc in B. exact B.
  - cbn [cells_size csize] in *. exact R.
Qed.

(* [comment removed for export] *)
Lemma tb_split : forall r q i, (0 <= r < 256)%Z -> (0 <= q)%Z -> (0 <= i)%Z ->
  Z.testbit (r + 256 * q) i = if (i <? 8)%Z then Z.testbit r i else Z.testbit q (i - 8).
Proof.
  intros r q i Hr Hq Hi. destruct (Z.ltb_spec i 8) as [L|L].
  - rewrite <- (Z.mod_pow2_bits_low (r + 256 * q) 8 i) by lia. change (2 ^ 8)%Z with 256%Z.
    replace ((r + 256 * q) mod 256)%Z with r by (Z.div_mod_to_equations; lia). reflexivity.
  - replace i with ((i - 8) + 8)%Z at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2 ^ 8)%Z with 256%Z.
    replace ((r + 256 * q) / 256)%Z with q by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma lxor_low : forall r q c, (0 <= r < 256)%Z -> (0 <= q)%Z -> (0 <= c < 256)%Z -> (0 <= Z.lxor r c < 256)%Z ->
  Z.lxor (r + 256 * q) c = (Z.lxor r c + 256 * q)%Z.
Proof.
  intros r q c Hr Hq Hc Hx. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !tb_split by lia.
  destruct (Z.ltb_spec i 8) as [L|L]; [rewrite Z.lxor_spec; reflexivity|].
  replace c with (c + 256 * 0)%Z by lia. rewrite tb_split by lia. rewrite (proj2 (Z.ltb_ge i 8)) by lia.
  rewrite Z.testbit_0_l. apply xorb_false_r.
Qed.

Lemma land255_low : forall r q, (0 <= r < 256)%Z -> (0 <= q)%Z -> Z.land (r + 256 * q) 255 = r.
Proof.
  intros r q Hr Hq. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
  Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma hdr_cas : forall b, (0 <= b < 256)%Z ->
  (Z.land (2 + 256 * b) 255 = 2 /\ Z.lxor (2 + 256 * b) (Z.land (Z.lxor (2 + 256 * b) 3) 255) = 3 + 256 * b)%Z.
Proof.
  intros b Hb. split; [apply (land255_low 2 b); lia|].
  rewrite (lxor_low 2 b 3); [| lia| lia| lia| change (Z.lxor 2 3) with 1%Z; lia]. change (Z.lxor 2 3) with 1%Z.
  rewrite (land255_low 1 b) by lia.
  rewrite (lxor_low 2 b 1); [change (Z.lxor 2 1) with 3%Z; reflexivity| lia| lia| lia| change (Z.lxor 2 1) with 3%Z; lia].
Qed.

Lemma land_m4 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x 18446744073709551612 = (4 * (x / 4))%Z.
Proof.
  intros x Hx.
  assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  assert (E2 : Z.ones 64 = Z.lor 18446744073709551612 3) by reflexivity.
  rewrite E2, Z.land_lor_distr_r in E1.
  pose proof (Z.add_lor_land (Z.land x 18446744073709551612) (Z.land x 3)) as E3.
  assert (E4 : Z.land (Z.land x 18446744073709551612) (Z.land x 3) = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
    assert (B : Z.testbit 18446744073709551612 i && Z.testbit 3 i = false)
      by (rewrite <- Z.land_spec; change (Z.land 18446744073709551612 3) with 0%Z; apply Z.bits_0).
    destruct (Z.testbit x i), (Z.testbit 18446744073709551612 i), (Z.testbit 3 i); cbn in *; congruence. }
  rewrite E4, Z.add_0_r, E1 in E3.
  change 3%Z with (Z.ones 2) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 2)%Z with 4%Z in E3.
  pose proof (Z.div_mod x 4 ltac:(lia)). lia.
Qed.

Definition qchunk_entry' : Z := 0x1a0070.

(* [comment removed for export] *)
Definition dealloc_p1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (M n b1 B T lo : Z) (ctx : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fr fd : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 M) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 B)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qchunk_entry') fc None m' (seg_rom ctasegs)
    /\ munch [(M, M + 24); (T + 2824, T + 2840); (bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m'
    /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx]
    /\ rw_cells ctasegs m' (M + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ rw_cells ctasegs m' (T + 2824) [C8 fr; C8 fd]
    /\ stk ctasegs m' lo (bv_unsigned sp).

Lemma dealloc_p1_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M n b1 B TCX T lo : Z) (ctx fr fd : word) (uw : list byte),
  (kHighShadowEnd < M)%Z -> (M mod 16 = 0)%Z -> (M + 24 <= lo)%Z -> (1 <= n < 2^32)%Z ->
  (0 <= b1 < 256)%Z -> (b1 mod 4 = 1)%Z ->
  rw_cells ctasegs m M [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells ctasegs m (M + 16) [CB 8 uw] ->
  rw_cells ctasegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbcb000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  rw_cells ctasegs m (T + 2824) [C8 fr; C8 fd] ->
  (M + 24 <= T + 2824 \/ T + 2840 <= M)%Z -> (M + 24 <= TCX + 152 \/ TCX + 160 <= M)%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (dealloc_p1_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc M n b1 B T lo ctx m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 B) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until uw. intros HM HM16 HMl Hn Hb1 Hb14 HD UW FH TC HTCX HTCXl HT HTi HTl STS HMT HMX ST HLO HSP MI.
  unfold deallocate_entry, kHighShadowEnd, g_MFHooks, INST, g_instance in *.
  change (7355136 + 8)%Z with 7355144%Z in FH.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  move KI at bottom. move K0 at bottom. move FH at bottom. move TS at bottom. move T0 at bottom.
  pose proof (hdr_cas b1 Hb1) as (HC1 & HC2).
  assert (RM : (17594333495295 < M < 2^47)%Z) by lia.
  pose proof (munch_refl [(M, M + 24); (T + 2824, T + 2840); (bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 64%nat ST.
  zhide.
  zidle_begin sp 64%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  zstep. ifF.
  do 8 zstep.
  zstep. sp_facts.
  call (run_free_hooks_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  zstep. ifT.
  do 8 zstep.
  assert (ESH : (Z.land (Z.shiftl M 3) 18446744073709551615 mod 32 = 0)%Z).
  { clear - RM HM16. unfold zal in HM16. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
    rewrite Z.land_ones by lia. rewrite (Z.mod_small (M * 2 ^ 3) (2 ^ 64)) by lia.
    change (2 ^ 3)%Z with 8%Z. Z.div_mod_to_equations; lia. }
  rewrite ESH. fold_reg 14%Z. fold_reg 15%Z. fold_reg 16%Z.
  rewrite land_m4 by (clear - RM; lia). replace (4 * (M / 4))%Z with M by (clear - RM HM16; unfold zal in HM16; Z.div_mod_to_equations; lia).
  apply (hdr3_to_c4 _ _ 2 b1 [C4 (Z_to_bv 64 n); C8 ctx]) in HD; [| lia| lia].
  assert (AMO : amo_aligned AW (Z_to_bv 64 M) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. Z.div_mod_to_equations; lia. }
  amo_step AMO. rewrite (sx32_small_A (2 + 256 * b1)) by lia.
  zstep. rewrite ?HC1. zstep. ifF.
  do 3 zstep. rewrite ?HC2.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 2 zstep. fold_reg 10%Z.
  zstep; fix_lit_store.
  apply (c4_to_hdr3 _ _ 3 b1 [C4 (Z_to_bv 64 n); C8 ctx]) in HD; [| lia| lia].
  zstep. cbv beta.
  replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256%Z;
                                                   rewrite Z.mod_small by lia; reflexivity).
  assert (E3 : Z.land b1 3 = 1%Z) by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; exact Hb14).
  zstep. rewrite E3. zstep. ifF.
  do 3 zstep. dIf_closed.
  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  do 10 zstep.
  do 12 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk ctasegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep. zstep.
  finish.
  all: eassumption.
Qed.

(* [comment removed for export] *)
Lemma qc_depot_ok_put_ok : forall D tr DNB SSB lo, depot_ok D DNB SSB lo -> (d_n D + 2 < 2^16)%Z ->
  (d_tot D + Z.of_nat (length tr) + 1 < 2^20)%Z -> depot_ok (fst (depot_put D tr)) DNB SSB lo.
Proof.
  intros D tr DNB SSB lo (HF & Hn & Ht & R) Hn2 Hroom. unfold depot_put.
  destruct (find_of (d_hs D) (depot_hash tr) =? 0)%Z; cbn [fst]; [| exact (conj HF (conj Hn (conj Ht R)))].
  unfold depot_ok, d_n in *. cbn [d_hs d_tot]. rewrite app_length. cbn [length].
  split; [apply Forall_app; split; [exact HF| constructor; [apply depot_hash_range| constructor]]|].
  split; [lia| split; [lia| exact R]].
Qed.

Definition qput_entry' : Z := 0x1a01e8.

(* [comment removed for export] *)
Definition qchunk_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (M n B T : Z) (D : depot) (BK : list Z) (DNB SSB : Z) (ws rest : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 B) (Z_to_bv 64 M) (Z_to_bv 64 n) a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qput_entry') fc None m' (seg_rom ctasegs)
    /\ munch [(M + 16, M + 24); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8);
             (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 272, bv_unsigned sp)]%Z m m'
    /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' (M + 16) [C8 (Z_to_bv 64 (snd (depot_put D (map bv_unsigned ws))))]
    /\ depot_rep (fst (depot_put D (map bv_unsigned ws))) BK DNB SSB m'
    /\ u64arr ctasegs m' (B + 16) (ws ++ rest)
    /\ stk ctasegs m' lo (bv_unsigned sp).

Lemma qchunk_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M n b1 B TCX T lo : Z) (ctx w : word) (D : depot) (BK : list Z) (DNB SSB : Z)
    (ws rest : list word),
  (kHighShadowEnd < M)%Z -> (M + 24 <= lo)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells ctasegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells ctasegs m (M + 16) [C8 w] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbcb000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  rw_cells ctasegs m T [C8 (Z_to_bv 64 TCX)] -> rw_cells ctasegs m (TCX + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells ctasegs m B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length ws)))] ->
  u64arr ctasegs m (B + 16) (ws ++ rest) -> length (ws ++ rest) = 255%nat -> (1 <= Z.of_nat (length ws) <= 254)%Z ->
  depot_ok D DNB SSB lo -> depot_rep D BK DNB SSB m -> (d_tot D + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  In (bkt (depot_hash (map bv_unsigned ws))) BK -> (d_n D + 2 < 2^16)%Z ->
  (M + 24 <= DNB \/ DNB + 2 ^ 20 <= M)%Z -> (M + 24 <= SSB \/ SSB + 2 ^ 23 <= M)%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 272)%Z -> (bv_unsigned sp <= B)%Z -> (B + 2064 <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (qchunk_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc M n B T D BK DNB SSB ws rest lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 M) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 B)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qchunk_entry') fc None m (seg_rom ctasegs)).
Proof.
  intros until rest. intros HM HMl Hn Hb1 HD UW TC HTCX HTCXl HT HTi HTl TC0 TC8 BC TB HL255 Hsz OK REP Hroom HBK Hn2 HMD HMS
    ST HLO HB HB2 MI.
  unfold qchunk_entry', kHighShadowEnd, INST, g_instance in *.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  move KI at bottom. move K0 at bottom. move TS at bottom. move T0 at bottom.
  apply box in REP.
  pose proof OK as (_ & _ & _ & HD1 & HD2 & HS1 & HS2 & _).
  pose proof (munch_refl [(M + 16, M + 24); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8);
             (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MUh.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 7 zstep.
  zidle_end MUz WMz.
  do 3 zstep. zstep. ifF.
  do 3 zstep.
  sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  zstep. ifF.
  do 6 zstep.
  zstep.
  let mm := amem in
  pose proof (depot_rep_frame D BK DNB SSB lo _ m mm (unbox _ REP) OK MUh WM ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)) as REPm.
  clear MUh REP.
  call (depot_put_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ D BK DNB SSB (B + 16)%Z lo ws rest).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  let mm := amem in
  pose proof (munch_refl [(M + 16, M + 24)]%Z mm) as MUd; pose proof (wmono_refl ctasegs mm) as WMd.
  assert (RID : (0 <= snd (depot_put D (map bv_unsigned ws)) < 2^16)%Z).
  { pose proof (depot_put_id D (map bv_unsigned ws)) as P. pose proof (depot_put_n D (map bv_unsigned ws)) as P2.
    destruct (depot_put D (map bv_unsigned ws)) as [D' id] eqn:E. cbn [fst snd] in *. unfold d_n in *. lia. }
  assert (EZ : Z.shiftr (Z.land (Z.shiftl (snd (depot_put D (map bv_unsigned ws))) 32) 18446744073709551615) 32
               = snd (depot_put D (map bv_unsigned ws))).
  { rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
  assert (EZ2 : Z.land (snd (depot_put D (map bv_unsigned ws))) 4294967295 = snd (depot_put D (map bv_unsigned ws))).
  { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  do 3 zstep. fold_reg 19%Z. rewrite ?EZ, ?EZ2.
  zstep. rewrite ?Z.lor_0_l, ?EZ2.
  zstep.
  do 10 zstep.
  change (Z.land (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 0))) 32) 18446744073709551615) with 0%Z.
  rewrite Z.lor_0_l, zx32_small, unsigned_lit by lia.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk ctasegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep. zstep.
  finish.
  lazymatch goal with H : depot_rep _ BK DNB SSB ?m2 |- depot_rep _ BK DNB SSB ?mm =>
    apply (depot_rep_frame _ BK DNB SSB lo _ m2 mm H
             (qc_depot_ok_put_ok D (map bv_unsigned ws) DNB SSB lo OK Hn2 ltac:(rewrite map_length; lia)) MUd WMd);
      cbn [disjoint_from]; lia end.
Qed.

(* [comment removed for export] *)
Lemma deallocate_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (0xbcb000 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc INST [(bv_unsigned sp - 64, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST HLO HIMG MI. unfold deallocate_entry.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 64%nat ST.
  zhide.
  zidle_begin sp 64%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  zstep. ifT.
  do 9 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
