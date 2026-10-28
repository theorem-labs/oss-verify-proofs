(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_mmapfixed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

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

Definition efs_entry : Z := 0x5bf48.
Definition efs_retB : Z := 0x5bfe8.
Definition str_freearray : Z := 0x19bef.

Definition efs_frame (m : mem) (sp : word) (ra s0 s1 s2 s3 : word) : Prop :=
  exists junk, rw_cells bsegs m (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma efs_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (R num nfree mfa auser muser lo : Z),
  ri_core m R nfree mfa auser muser ->
  (0 <= nfree < 2^64)%Z -> (0 <= mfa <= 2^29)%Z -> (0 <= auser < 2^64)%Z -> (0 <= muser < 2^64)%Z ->
  (0 <= num < 2^32)%Z -> (4 * num <= mfa)%Z ->
  (0 < R)%Z -> (R + 64 <= lo)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 48, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 R) a2 (Z_to_bv 64 num) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 efs_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros RC Hnf Hmfa Hau Hmu Hnum Hfast HR HRlo ST HLO HSP MI.
  unfold ri_core, efs_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin_rw sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 num 2) by lia. change (2 ^ 2)%Z with 4%Z.
  zstep. ifT.
  do 7 zstep.
  replace (bv_unsigned sp + -48 + 48)%Z with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

Lemma round_fa_code : forall num, (0 <= num < 2^32)%Z -> Z.land (num * 4 + 262143) 18446744073709289472 = round_fa (4 * num).
Proof.
  intros num Hn. rewrite land_famask by lia. unfold round_fa. f_equal. f_equal. lia.
Qed.

Definition efs_A_cells (m : mem) (sp ra s0 s1 s2 s3 s4 : word) (R fam n new lo : Z) : Prop :=
  rmap_frame m (Z_to_bv 64 (bv_unsigned sp - 48)) (Z_to_bv 64 efs_retB) (Z_to_bv 64 new) (Z_to_bv 64 fam) (Z_to_bv 64 n)
            (Z_to_bv 64 R) s4
  /\ efs_frame m sp ra s0 s1 s2 s3
  /\ stk bsegs m lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) - 128)
  /\ mm_gcells m.

Definition efs_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R fam n new lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' a6' fam n
                          (Z_to_bv 64 str_freearray) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 448, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ efs_A_cells m' sp ra s0 s1 s2 s3 s4 R fam n new lo.

Lemma efs_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R num nfree mfa auser muser lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  ri_core m R nfree mfa auser muser -> inst_cells SB m -> mm_gcells m ->
  (0 <= nfree < 2^64)%Z -> (0 <= mfa <= 2^29)%Z -> (mfa mod 2^18 = 0)%Z -> (0 <= auser < 2^64)%Z -> (0 <= muser < 2^64)%Z ->
  (0 <= num < 2^32)%Z -> (mfa < 4 * num)%Z -> (round_fa (4 * num) <= 2^29)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 448)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (efs_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R (fa SB c + mfa) (round_fa (4 * num) - mfa)
               (round_fa (4 * num)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 R) (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 num) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 efs_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HSB Hc ER RC IC GC Hnf Hmfa Hmfal Hau Hmu Hnum Hslow Hnew ST HLO HLOH HLO2 HSP MI.
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  destruct GC as (G1 & G2 & G3 & G4 & G5). destruct IC as (IC1 & IC2).
  move IC1 after G2. move IC2 after IC1.
  unfold ri_core, efs_entry, rinfo, RIS_of, i_spacebeg, i_premapped, INST, g_instance, kHighShadowEnd in *.
  change (1522392 + 32)%Z with 1522424%Z in IC1. change (1522392 + 56)%Z with 1522448%Z in IC2.
  pose proof (round_fa_ge (4 * num) ltac:(lia)) as RG. pose proof (round_fa_aligned (4 * num)) as RA.
  remember (round_fa (4 * num)) as new eqn:Enew.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin_rw sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 num 2) by lia. change (2 ^ 2)%Z with 4%Z.
  zstep. ifF.
  do 5 zstep.
  rewrite (round_fa_code num Hnum), <- Enew.
  do 2 zstep. zstep. ifF.
  zstep.
  change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 0)) with (Z_to_bv 64 0).
  do 4 zstep.
  zstep. ifT.
  do 6 zstep.
  replace (mfa + (rb SB c + 3758096384))%Z with (fa SB c + mfa)%Z by (unfold fa; lia).
  replace (new + - mfa)%Z with (new - mfa)%Z by lia.
  zstep.
  sp_facts.
  call (rmap_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (fa SB c + mfa) (new - mfa) _ lo).
  1:{ unfold fa, rb. lia. }
  1:{ unfold fa, rb. Z.div_mod_to_equations. lia. }
  1:{ lia. }
  1:{ Z.div_mod_to_equations. lia. }
  1:{ unfold fa, rb. lia. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  all: rewrite ?Esp; try lia; try assumption.
  apply evt_done. unfold efs_A_post, efs_A_cells, efs_frame.
  do 9 eexists. split; [reflexivity|].
  split; [exact MU|split; [exact WM| split; [exact MI0| split; [exact PC| split; [eexists; exact FR| split; [exact PC0| exact POST]]]]]].
Qed.

