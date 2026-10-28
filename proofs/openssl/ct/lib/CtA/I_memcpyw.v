(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck F_memcpy X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
(* [comment removed for export] *)
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Notation IMEMCPY_DEPTH := 2240%Z (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icells (m : mem) : Prop :=
  ro_cells ctasegs m 0x5a9238 [C8 (Z_to_bv 64 0x672038)]            (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5a9dc0 [C8 (Z_to_bv 64 0x672d19)]         (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5ac4a8 [C8 (Z_to_bv 64 0x52b0ac)]         (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x672038 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x672d19 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)

Lemma imemcpy_prologue : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo sp -> lo <= sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 <= n -> d + n < 2^64 -> s + n < 2^64 -> (d + n <= s \/ s + n <= d) ->
  icells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (junk : list byte) (a3' a4' s5' : word),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5 a6 a7 s2 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) s5'
                    s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1c376c) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2160, sp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ rw_cells ctasegs m' (sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells ctasegs m' (sp + -2160) [CB 2080 junk]
      /\ stk ctasegs m' lo (sp + -2160))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c370c) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN OV (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2160, sp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUsn : bv_unsigned (Z_to_bv 64 (s + n)) = s + n) by (apply unsigned_lit; lia).
  assert (EUdn : bv_unsigned (Z_to_bv 64 (d + n)) = d + n) by (apply unsigned_lit; lia).
  carve_frame 80%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  zidle_beginz sp 2160%Z MUz1 WMz1.
  do 12 lstep.
  zidle_end MUz1 WMz1.
  do 5 astep.
  do 4 astep.
  lstep.
  destruct (Z.eq_dec d s) as [Eds|Nds].
  - subst s. replace (bv_eqb (Z_to_bv 64 d) (Z_to_bv 64 d)) with true by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity). cbv iota.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
  - if_false. lstep. if_cases K; zify_cond K.
    + apply evt_done. do 5 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
    + lstep. if_false.
      apply evt_done. do 5 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

(* [comment removed for export] *)
Lemma imemcpy_src_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1c3a9c) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c3a8c) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma imemcpy_src_rip : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2160) -> lo <= sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 < n -> d + n < 2^63 -> s + n < 2^63 ->
  acc ctasegs m s n -> rng_ok s n -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s7' s8' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' (Z_to_bv 64 (d + n)) s5
                    s6 s7' s8' s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c37b8) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2160))
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (d + n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c3aa4) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN AC RO M2S MI.
  idtac.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 6 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma imemcpy_src : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2160) -> lo <= sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 <= n -> d + n < 2^63 -> s + n < 2^63 ->
  chk_ok m s n -> m2s_cells m -> icells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s7' s8' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' (Z_to_bv 64 (d + n)) s5
                    (Z_to_bv 64 (n + -65)) s7' s8' s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c37b8) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2160))
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c376c) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN (AC & QW & RO) M2S (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 s) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (imemcpy_src_rip sp d s n); try assumption; lia.
  - (* [comment removed for export] *)
    subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + s ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((s / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (s + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((s + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (s + n + -1) with (s + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (s + n + -1) / 8) with ((s + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m s n AC ltac:(lia) S0) as SB. unfold shad, SHB in SB.
      destruct (SB ((s + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemcpy_src_rip sp d s n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (imemcpy_src_loop (Z.to_nat ((s + n + -1) / 8 + 2147450880 - (s / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemcpy_src_rip sp d s n); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End WithRIP.
