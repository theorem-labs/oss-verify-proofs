(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_setshadow R_thread R_cache_defs R_prim_defs R_asan_defs R_poison R_prim_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition qput_entry : Z := 0x5d9e4.
Definition qenq_entry : Z := 0x5db94.
Definition qdrain_entry : Z := 0x5b2ec.

Notation QUAR := (1525808%Z) (only parsing).
Notation q_max := (1525872%Z) (only parsing).
Notation q_cmax := (1525888%Z) (only parsing).

Ltac qexact_addr := lazymatch goal with
  | |- rw_cells ?s ?mm ?A ?cs => match goal with H : rw_cells s mm ?A' cs |- _ => replace A with A' by lia; exact H end
  | |- u64arr ?s ?mm ?A ?ws => match goal with H : u64arr s mm ?A' ws |- _ => replace A with A' by lia; exact H end
  | |- stk ?s ?mm ?lo ?A => match goal with H : stk s mm lo ?A' |- _ => replace A with A' by lia; exact H end
  end.

Definition ru8' (n : Z) : Z := 8 * ((n + 7) / 8).

Lemma ru8'_range : forall n, (1 <= n)%Z -> (n <= ru8' n <= n + 7 /\ ru8' n mod 8 = 0 /\ 8 <= ru8' n)%Z.
Proof. intros n Hn. unfold ru8'. split; [| split]; [Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia|].
  pose proof (Z.div_le_mono 8 (n + 7) 8 ltac:(lia) ltac:(lia)). change (8 / 8)%Z with 1%Z in H. lia. Qed.

Lemma roundup8_machine : forall n, (0 <= n < 2^48)%Z -> Z.land (n + 7) 18446744073709551608 = ru8' n.
Proof.
  intros n Hn. rewrite land_m8 by lia. reflexivity.
Qed.

Definition qput_frame (m : mem) (A : Z) (cache stack ra s0 s1 s2 s3 s4 s5 s6 : word) : Prop :=
  rw_cells bsegs m A [C8 cache; C8 stack; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition qput_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c cache stack M n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x5db88) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 c)
                  (Z_to_bv 64 c) (Z_to_bv 64 cache) (Z_to_bv 64 stack) (Z_to_bv 64 M) (Z_to_bv 64 n) a5' a6' a7'
                  (Z_to_bv 64 n) (Z_to_bv 64 stack) (Z_to_bv 64 cache) (Z_to_bv 64 M) (Z_to_bv 64 0x100000)
                  s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qenq_entry) fc None m' (seg_rom bsegs)
    /\ munch [(shad (M + 16), shad (M + 16) + ru8' n / 8); (bv_unsigned sp - 144, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (shad (M + 16)) [CB (Z.to_nat (ru8' n / 8)) (repeat (Z_to_bv 8 253) (Z.to_nat (ru8' n / 8)))]
    /\ qput_frame m' (bv_unsigned sp - 80) (Z_to_bv 64 cache) (Z_to_bv 64 stack) ra s0 s1 s2 s3 s4 s5 s6
    /\ stk bsegs m' lo (bv_unsigned sp - 80).

Lemma qput_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c cache stack M n b1 lo : Z) (ctx : word) (shj : list byte),
  (kHighShadowEnd < M)%Z -> (M mod 16 = 0)%Z -> (M + 16 + ru8' n <= kHighMemEnd + 1)%Z -> (M + 16 + ru8' n <= lo)%Z ->
  (1 <= n <= 2^28)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells bsegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells bsegs m (shad (M + 16)) [CB (Z.to_nat (ru8' n / 8)) shj] ->
  rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] -> rw_cells bsegs m q_cmax [C8 (Z_to_bv 64 0x100000)] ->
  rw_cells bsegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] -> rw_cells bsegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)] ->
  ps_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qput_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c cache stack M n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) (Z_to_bv 64 cache) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qput_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros HM HM16 HMe HMl Hn Hb1 HD SH QM QC GAF FF PS ST HLO HLOH MI.
  pose proof (ru8'_range n ltac:(lia)) as RU.
  assert (PA : ps_args_ok (M + 16) (ru8' n)).
  { unfold ps_args_ok. split; [split; [Z.div_mod_to_equations; lia| lia]| right; lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4).
  unfold qput_entry, kHighShadowEnd, kHighMemEnd, g_GOT_asan_flags, g_asan_flags in *.
  change (1528760 + 48)%Z with 1528808%Z in FF.
  move GAF at bottom. move QM at bottom. move QC at bottom. move FF at bottom.
  pose proof (munch_refl [(shad (M + 16), shad (M + 16) + ru8' n / 8); (bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MUp.
  pose proof (wmono_refl bsegs m) as WM.
  apply box in PS.
  carve_frame 64%nat ST. carve_frame 16%nat ST.
  zhide.
  zidle_begin_rw sp 80%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 5 zstep. zstep. ifF.
  zstep. zstep. ifT.
  do 6 zstep. zstep. ifT.
  do 9 zstep.
  rewrite (Z.mod_small n 4294967296) by lia. rewrite roundup8_machine by lia.
  zstep.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ (unbox _ PS) MUp WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
  clear MUp PS.
  sp_facts.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (M + 16)%Z (ru8' n) 253 lo shj).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 6 zstep.
  apply evt_done. unfold qput_A_post.
  do 11 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| qexact_addr].
  unfold qput_frame. apply (proj2 (rwc_app bsegs _ _ [C8 (Z_to_bv 64 cache); C8 (Z_to_bv 64 stack)]
                                  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  split; [qexact_addr|]. cbn [cells_size csize Nat.add]. qexact_addr.
Qed.

Definition qput_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma qput_C_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 cache stack (F : bvmap 5 word) fc (m : mem) (lo : Z),
  qput_frame m (bv_unsigned sp - 80) cache stack ra s0 s1 s2 s3 s4 s5 s6 ->
  stk bsegs m lo (bv_unsigned sp - 80) -> (lo <= bv_unsigned sp - 80)%Z -> (0x6ce000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qput_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6'
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5dac0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FR ST HLO HIMG MI. unfold qput_frame in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  replace (bv_unsigned sp - 80)%Z with (bv_unsigned sp + -80)%Z in FR, ST by lia.
  zhide.
  do 9 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

Lemma qput_B_ret_spec : forall ra sp gp tp t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 cache stack (F : bvmap 5 word) fc (m : mem) (c bytes lo : Z) (w0 w1 w2 : word),
  rw_cells bsegs m c [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 bytes)] -> (0 <= bytes <= 0x100000)%Z ->
  qput_frame m (bv_unsigned sp - 80) cache stack ra s0 s1 s2 s3 s4 s5 s6 ->
  stk bsegs m lo (bv_unsigned sp - 80) -> (lo <= bv_unsigned sp - 80)%Z -> (0x6ce000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qput_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5db88) fc None m (seg_rom bsegs)).
Proof.
  intros until w2. intros QC HB FR ST HLO HIMG MI.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  zstep. zstep. ifF. zstep.
  eapply evt_mono; [eapply qput_C_spec; eassumption|].
  intros ms' P. exact P.
Qed.

Definition qput_drain_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c cache stack lo : Z) (m : mem) (s2' s3' s4' s5' : word) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR (Z_to_bv 64 0x5dac0) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 c)
                  (Z_to_bv 64 QUAR) (Z_to_bv 64 c) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4' a5' a6' a7'
                  s2' s3' s4' s5' (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs).

Lemma qput_B_drain_spec : forall ra sp gp tp t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 ra0 (F : bvmap 5 word) fc (m : mem) (c cache stack bytes lo : Z) (w0 w1 w2 : word),
  rw_cells bsegs m c [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 bytes)] -> (0x100000 < bytes < 2^63)%Z ->
  qput_frame m (bv_unsigned sp - 80) (Z_to_bv 64 cache) (Z_to_bv 64 stack) ra s0 s1 s2 s3 s4 s5 s6 ->
  mem_inv bsegs m ->
  evt bsegs (qput_drain_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c cache stack lo m s2' s3' s4' s5')
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5db88) fc None m (seg_rom bsegs)).
Proof.
  intros until w2. intros QC HB FR MI. unfold qput_frame in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  replace (bv_unsigned sp - 80)%Z with (bv_unsigned sp + -80)%Z in FR by lia.
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  zstep. zstep. ifT.
  do 5 zstep.
  apply evt_done. unfold qput_drain_post. do 11 eexists. reflexivity.
Qed.

Definition qput_P_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (c cache stack M lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x5daa4) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' (Z_to_bv 64 QUAR) (Z_to_bv 64 c)
                  (Z_to_bv 64 (bv_unsigned sp + -80)) (Z_to_bv 64 M) a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x5b930) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ qput_frame m' (bv_unsigned sp - 80) (Z_to_bv 64 cache) (Z_to_bv 64 stack) ra s0 s1 s2 s3 s4 s5 s6
    /\ stk bsegs m' lo (bv_unsigned sp - 80).

Lemma qput_P_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c cache stack M n SB lo : Z),
  (0x10000000 < n < 2^48)%Z -> (0 <= M < 2^48)%Z -> (0 <= SB < 2^48)%Z -> (M < SB \/ SB + 2^37 <= M)%Z ->
  rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] -> rw_cells bsegs m q_cmax [C8 (Z_to_bv 64 0x100000)] ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qput_P_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c cache stack M lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) (Z_to_bv 64 cache) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qput_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hn HM HSB HOUT QM QC SBC ST HLO HLOH MI.
  unfold qput_entry, kHighShadowEnd in *. unfold i_spacebeg, g_instance in SBC. change (1525080 + 32)%Z with 1525112%Z in SBC.
  move QM at bottom. move QC at bottom. move SBC at bottom.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST. carve_frame 16%nat ST.
  zhide.
  zidle_begin_rw sp 80%Z MUz WMz.
  do 9 zstep.
  zidle_end MUz WMz.
  do 5 zstep. zstep. ifF.
  zstep. zstep. ifF.
  do 2 zstep. zstep.
  destruct HOUT as [HLT|HGE]; [ifT | ifF; do 3 zstep; zstep; ifT].
  all: do 3 zstep.
  all: apply evt_done; unfold qput_P_post.
  all: do 14 eexists; split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [| qexact_addr].
  all: unfold qput_frame; apply (proj2 (rwc_app bsegs _ _ [C8 (Z_to_bv 64 cache); C8 (Z_to_bv 64 stack)]
                                  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  all: split; [qexact_addr|]; cbn [cells_size csize Nat.add]; qexact_addr.
Qed.

Lemma qput_P_ret_spec : forall ra sp gp tp t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 cache stack (F : bvmap 5 word) fc (m : mem) (c bytes lo : Z) (w0 w1 w2 : word),
  rw_cells bsegs m c [C8 w0; C8 w1; C8 w2; C8 (Z_to_bv 64 bytes)] -> (0 <= bytes <= 0x100000)%Z ->
  qput_frame m (bv_unsigned sp - 80) cache stack ra s0 s1 s2 s3 s4 s5 s6 ->
  stk bsegs m lo (bv_unsigned sp - 80) -> (lo <= bv_unsigned sp - 80)%Z -> (0x6ce000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qput_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5daa4) fc None m (seg_rom bsegs)).
Proof.
  intros until w2. intros QC HB FR ST HLO HIMG MI.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  zstep. zstep. ifT.
  eapply evt_mono; [eapply qput_C_spec; eassumption|].
  intros ms' P. exact P.
Qed.
