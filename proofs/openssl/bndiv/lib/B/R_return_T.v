(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread R_cache_defs R_sizeclass R_classid R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_popfree R_getfrom R_return.
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

(* [comment removed for export] *)
Lemma rta_head : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R mapper stat CH cb n lo : Z) (Q : machine_state -> Prop),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  inst_cells SB m -> ri_lock m R 0 ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 128)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  (forall (m1 : mem) (junk : list byte),
     rw_cells bsegs m1 (bv_unsigned sp - 128)
       [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
        C8 s0; C8 ra] ->
     rw_cells bsegs m1 R [C8 (Z_to_bv 64 1152921504606846976)] ->
     stk bsegs m1 lo (bv_unsigned sp - 128) ->
     munch [(R, R + 8); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
     evt bsegs Q
       (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 16140901064495857663)
                (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0) (Z_to_bv 64 1500) (Z_to_bv 64 c) (Z_to_bv 64 mapper)
                (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 1099511627776)
                (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1152921504607895551)
                (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6)
           F (Z_to_bv 64 0x198ac8) fc None m1 (seg_rom bsegs))) ->
  evt bsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 mapper) (Z_to_bv 64 stat) (Z_to_bv 64 c)
             (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rta_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HSB Hc ER IC LK ST HLO HLOH HLO2 HSP MI K.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2).
  unfold i_spacebeg, i_premapped, INST, g_instance, rta_entry, kHighShadowEnd, rinfo, RIS_of, ri_lock in *.
  change (6947736 + 32)%Z with 6947768%Z in IC1. change (6947736 + 56)%Z with 6947792%Z in IC2.
  pose proof (munch_refl [(R, R + 8); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 128%nat ST.
  zhide.
  zidle_begin sp 128%Z MUz WMz.
  do 14 zstep.
  zidle_end MUz WMz.
  do 20 zstep.
  replace (SB + 137438953472 + c ≪ 7)%Z with R by (rewrite ER, Z.shiftl_mul_pow2 by lia; lia).
  replace (SB + c ≪ 32)%Z with (rb SB c) by (unfold rb; rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 2 zstep.
  replace (rb SB c + 3758096384)%Z with (fa SB c) by (unfold fa; lia).
  do 3 zstep; try fix_lit_store.
  do 4 zstep.
  zstep. zstep. ifF.
  do 2 zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 R) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. rewrite ER. Z.div_mod_to_equations. lia. }
  amo_step AMO.
  zstep. ifF.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. ifT.
  eapply K; eassumption.
Qed.

Definition rta_tail_W (sp : word) (SB c R nfree n : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (fa SB c + 4 * nfree, fa SB c + 4 * (nfree + n));
   (bv_unsigned sp - 208, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition rta_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R nfree n mfa auser muser : Z) (ws' : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (rta_tail_W sp SB c R nfree n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ ri_lock m' R 0
    /\ ri_core m' R (nfree + n) mfa auser muser
    /\ ri_tail m' R rand exh pad nalloc (nfreed + n) r0 r1 r2 r3
    /\ fl_arr m' SB c ws'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section RTAIL.
Variables (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word) (fc : bv 32).
Variables (ACEIL SB c R CH cb n nfree mfa auser muser mapper lo : Z) (ws chs : list word) (rand : word) (exh : byte)
          (pad : list byte) (nalloc nfreed r0 r1 r2 r3 : Z) (m0 : mem).
Hypothesis HSB : SB_ok ACEIL SB.
Hypothesis Hc : (1 <= c <= 31)%Z.
Hypothesis ER : R = rinfo (RIS_of SB) c.
Hypothesis Hn : (1 <= n <= 16)%Z.
Hypothesis Hcb : (0 <= cb /\ cb + n <= 16)%Z.
Hypothesis Hnf : (0 <= nfree < 2^32)%Z.
Hypothesis Hws : (4 * (nfree + n) <= 4 * Z.of_nat (length ws) /\ 4 * Z.of_nat (length ws) = mfa /\ mfa <= 2^29)%Z.
Hypothesis Hchs : length chs = 16%nat.
Hypothesis HCH : (0 < CH /\ CH + 64 <= ACEIL /\ (CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH))%Z.
Hypothesis Hrng : (0 <= nfreed < 2^64 /\ 0 <= r0 < 2^64 /\ 0 <= auser < 2^64 /\ 0 <= muser < 2^64)%Z.
Hypothesis HLO : (ACEIL <= lo)%Z.
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO2 : (lo <= bv_unsigned sp - 208)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.

Definition rta_Q : machine_state -> Prop :=
  rta_ret_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F fc SB c R nfree n mfa auser muser
    (dest2 ws chs nfree cb (Z.to_nat n)) rand exh pad nalloc nfreed r0 r1 r2 r3 lo m0.

(* [comment removed for export] *)
Lemma rta_t34490 : forall ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s9 s10 t3 t4 t5 t6 (m : mem) junk,
  rw_cells bsegs m (bv_unsigned sp - 128)
    [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o;
     C8 s1o; C8 s0o; C8 ra] ->
  rw_cells bsegs m R [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells bsegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  u32arr bsegs m (fa SB c) (dest2 ws chs nfree cb (Z.to_nat n)) ->
  inst_cells SB m -> mm_gcells m ->
  stk bsegs m lo (bv_unsigned sp - 128) ->
  munch (rta_tail_W sp SB c R nfree n) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  evt bsegs rta_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 c) (Z_to_bv 64 mapper) (Z_to_bv 64 INST) (Z_to_bv 64 n) s6 (Z_to_bv 64 (nfree + n))
             (Z_to_bv 64 2305843009213693952) s9 s10 (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6)
        F (Z_to_bv 64 0x198b0c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros FR LK RC RT FL IC GC ST MU WM MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2). destruct GC as (G1 & G2 & G3 & G4 & G5).
  move IC1 after G2. move IC2 after IC1.
  unfold i_spacebeg, i_premapped, INST, g_instance in IC1, IC2.
  change (6947736 + 32)%Z with 6947768%Z in IC1. change (6947736 + 56)%Z with 6947792%Z in IC2.
  unfold rinfo, RIS_of, kHighShadowEnd, rta_tail_W in *.
  pose proof (dest2_length ws chs nfree cb (Z.to_nat n)) as DL.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  zhide.
  do 4 zstep.
  do 4 zstep.
  zstep.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  assert (EM : Z_to_bv 64 (nfreed + n) = Z_to_bv 64 ((nfreed + n) mod 2^64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity. }
  pose proof (Z.mod_pos_bound (nfreed + n) (2^64) ltac:(lia)) as EMR.
  rewrite EM in *.
  call (mrto_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ ACEIL SB c R mapper (nfree + n) mfa auser muser
          rand exh pad nalloc ((nfreed + n) mod 2^64) r0 r1 r2 r3 lo).
  all: first [ assumption | (unfold rinfo, RIS_of; lia) | lia | (rewrite Esp; assumption) | (rewrite Esp; lia)
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (unfold mm_gcells; repeat (split; [assumption|]); assumption) | idtac ].
  (* [comment removed for export] *)
  do 15 zstep.
  do 2 zstep. zstep. ifF.
  zstep. zstep. ifT.
  do 7 zstep. zstep. ifT.
  assert (AMO : amo_aligned AD (Z_to_bv 64 R) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. rewrite ER. Z.div_mod_to_equations. lia. }
  amo_step AMO.
  zstep. ifF.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. ifT.
  zstep. ifF.
  do 14 zstep.
  replace (bv_unsigned sp - 128 + 128)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  rewrite Esp in POST.
  release_frame FR POST (bv_unsigned sp).
  zstep.
  rewrite <- EM in *.
  finish.
Qed.

(* [comment removed for export] *)
Lemma rta_loop : forall (k : nat) (i : Z) ra' t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 (m : mem) junk,
  i = (n - Z.of_nat k)%Z -> (0 <= i)%Z -> (1 <= k)%nat ->
  rw_cells bsegs m (bv_unsigned sp - 128)
    [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o;
     C8 s1o; C8 s0o; C8 ra] ->
  rw_cells bsegs m R [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells bsegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)] ->
  u32arr bsegs m (fa SB c) (dest2 ws chs nfree cb (Z.to_nat i)) ->
  u32arr bsegs m CH chs ->
  inst_cells SB m -> mm_gcells m ->
  stk bsegs m lo (bv_unsigned sp - 128) ->
  munch (rta_tail_W sp SB c R nfree n) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  evt bsegs rta_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 (Z_to_bv 64 (CH + 4 * cb + 4 * n))
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 c) (Z_to_bv 64 mapper) (Z_to_bv 64 INST) (Z_to_bv 64 n)
             (Z_to_bv 64 (CH + 4 * (cb + i))) (Z_to_bv 64 (nfree + n)) (Z_to_bv 64 2305843009213693952)
             (Z_to_bv 64 (fa SB c + 4 * (nfree + i))) s10 (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6)
        F (Z_to_bv 64 0x198af8) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros i ra' t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 m junk
    Ei Hi Hk FR LK RC RT FL CHS IC GC ST MU WM MI; [lia|].
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct IC as (IC1 & IC2). destruct GC as (G1 & G2 & G3 & G4 & G5).
  move IC1 after G2. move IC2 after IC1.
  unfold i_spacebeg, i_premapped, INST, g_instance in IC1, IC2.
  change (6947736 + 32)%Z with 6947768%Z in IC1. change (6947736 + 56)%Z with 6947792%Z in IC2.
  unfold rinfo, RIS_of, kHighShadowEnd, rta_tail_W in *.
  pose proof (dest2_length ws chs nfree cb (Z.to_nat i)) as DL.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  destruct (nth_error_ex chs (Z.to_nat (cb + i)) ltac:(lia)) as [w Hw].
  pose proof (u32arr_read bsegs m CH chs (cb + i) w (Z_to_bv 64 (CH + 4 * (cb + i))) CHS Hw ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zhide.
  zstep. clear RD.
  zstep.
  pose proof (u32arr_store_ok bsegs m (fa SB c) _ (nfree + i) (Z_to_bv 64 (fa SB c + 4 * (nfree + i))) FL ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as SO.
  zstep.
  pose proof (u32arr_write bsegs m (fa SB c) _ (nfree + i) (sx32 w) FL ltac:(lia)) as FL'.
  clear FL.
  store_done.
  assert (EW : w = nth (Z.to_nat cb + Z.to_nat i) chs (Z_to_bv 64 0)).
  { rewrite <- Z2Nat.inj_add by lia. symmetry. apply nth_error_nth. exact Hw. }
  replace (upd (dest2 ws chs nfree cb (Z.to_nat i)) (Z.to_nat (nfree + i)) (sx32 w))
    with (dest2 ws chs nfree cb (Z.to_nat (i + 1))) in FL'
    by (replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; cbn [dest2]; rewrite <- EW;
        rewrite Z2Nat.inj_add by lia; reflexivity).
  zstep.
  replace (CH + 4 * (cb + i) + 4)%Z with (CH + 4 * (cb + (i + 1)))%Z by lia.
  replace (fa SB c + 4 * (nfree + i) + 4)%Z with (fa SB c + 4 * (nfree + (i + 1)))%Z by lia.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC : inst_cells SB mm) by (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption);
    assert (GC : mm_gcells mm) by (unfold mm_gcells; repeat (split; [assumption|]); assumption) end.
  clear IC1 IC2 G1 G2 G3 G4 G5.
  destruct k as [|k].
  - ifF.
    replace (i + 1)%Z with n in FL' by lia.
    eapply rta_t34490; eassumption.
  - ifT.
    eapply (IH (i + 1)%Z); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Definition rta_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (R : Z) : Prop :=
  exists junk, rw_cells bsegs m (bv_unsigned sp - 128)
    [CB 16 junk; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
     C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma rta_tail_spec : forall ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6,
  rta_frame m0 sp ra s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o R ->
  ri_lock m0 R 1152921504606846976 ->
  ri_core m0 R nfree mfa auser muser ->
  ri_tail m0 R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m0 SB c ws -> u32arr bsegs m0 CH chs ->
  inst_cells SB m0 -> mm_gcells m0 ->
  stk bsegs m0 lo (bv_unsigned sp - 128) ->
  mem_inv bsegs m0 ->
  evt bsegs rta_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 nfree) (Z_to_bv 64 1)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 c) (Z_to_bv 64 mapper) (Z_to_bv 64 INST) (Z_to_bv 64 n)
             (Z_to_bv 64 (CH + 4 * cb)) (Z_to_bv 64 (nfree + n)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c))
             s10 (Z_to_bv 64 1152921504606846976) t3 t4 t5 t6)
        F (Z_to_bv 64 0x198ae0) fc None m0 (seg_rom bsegs)).
Proof.
  intros until t6. intros FR LK RC RT FL CHS IC GC ST MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  unfold ri_lock, ri_core, ri_tail, fl_arr, rta_frame in *.
  destruct FR as (junk & FR).
  pose proof (munch_refl (rta_tail_W sp SB c R nfree n) m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
  pose proof (dest2_length ws chs nfree cb 0) as DL.
  zhide.
  zstep. ifF.
  zstep. ifF.
  do 4 zstep.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2)%Z with 4%Z.
  replace (fa SB c + nfree * 4)%Z with (fa SB c + 4 * (nfree + 0))%Z by lia.
  replace (CH + 4 * cb + n * 4)%Z with (CH + 4 * cb + 4 * n)%Z by lia.
  assert (E0 : Z_to_bv 64 (CH + 4 * cb) = Z_to_bv 64 (CH + 4 * (cb + 0))) by (f_equal; lia). rewrite E0.
  eapply (rta_loop (Z.to_nat n) 0%Z); try eassumption; try lia.
Qed.
End RTAIL.
