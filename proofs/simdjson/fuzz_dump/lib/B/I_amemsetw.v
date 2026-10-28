(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck F_memcpy X_atexit F_memset D_kit I_memsetw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Notation AMEMSET_DEPTH := 2208%Z (only parsing).

Lemma amemset_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x7eee0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7eed0) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    zhide.
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma amemset_rip : forall (sp d n : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2128) -> lo <= sp - AMEMSET_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 < n -> d + n < 2^63 ->
  acc bsegs m d n -> rng_ok d n -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2128)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) a1 (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' s3' s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x7eda4) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2208, sp - 2128)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2128))
    (MS (mkR ra (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7eee8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2208, sp - 2128)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2128)) = sp + -2128) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  zhide.
  do 5 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma amemset_chk : forall (sp d n : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2128) -> lo <= sp - AMEMSET_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= n -> d + n < 2^63 ->
  chk_ok m d n -> m2s_cells m -> icells_ms m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2128)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) a1 (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x7eda4) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2208, sp - 2128)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2128))
    (MS (mkR ra (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7ed4c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2208, sp - 2128)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  zhide.
  lstep. lstep. lstep. rewrite (lxor_ones64 d) by lia.
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - d)) = 18446744073709551615 - d) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    eapply evt_mono; [apply (amemset_rip sp d n); first [exact ST| try assumption; unfold kHighShadowEnd; lia]|].
    intros ms' (m' & ra' & t0' & t1' & t2' & s1' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s5' & t3' & t4' & t5' & t6' & -> & REST).
    do 19 eexists. split; [reflexivity| exact REST].
  -
    subst n. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + d ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((d / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (d + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((d + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (d + n + -1) with (d + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    +
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (d + n + -1) / 8) with ((d + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m d n AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((d + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      Local Ltac rip_tail sp d n := eapply evt_mono; [apply (amemset_rip sp d n); first [eassumption| try assumption; unfold kHighShadowEnd; lia]|];
        intros ?ms' (?m' & ?ra' & ?t0' & ?t1' & ?t2' & ?s1' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?s2' & ?s3' & ?s5' & ?t3' & ?t4' & ?t5' & ?t6' & -> & ?REST);
        do 19 eexists; split; [reflexivity| eassumption].
      if_cases K2.
      *
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- rip_tail sp d n.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (amemset_loop (Z.to_nat ((d + n + -1) / 8 + 2147450880 - (d / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- rip_tail sp d n.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d C n : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(d, d + n); (bv_unsigned sp - AMEMSET_DEPTH, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat n))].

Theorem amemset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d C n : Z) (junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 C -> a2 = Z_to_bv 64 n ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMSET_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= n -> d + n <= 2^47 -> 0 <= C < 2^64 -> (n = 0 \/ d + n <= lo \/ bv_unsigned sp <= d) ->
  rw_cells bsegs m d [CB (Z.to_nat n) junk] ->
  chk_ok m d n -> m2s_cells m -> icells_ms m -> mem_inv bsegs m ->
  evt bsegs (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d C n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7ed14) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 N0 DH HC SEPD DST CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + n); (usp - 2208, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(usp - 2208, usp)] m) as MUf.
  pose proof IC as (G2 & G1 & RM & SHC & RI).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (DST0 : keep (rw_cells bsegs m d [CB (Z.to_nat n) junk])) by exact DST. clear DST.
  carve_frame 56%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  zhide.
  do 14 lstep. if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CD1 : chk_ok mm d n)
      by (apply (chk_ok_agree m mm d n CD D0 DH); apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree bsegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree bsegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree bsegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia ]);
    assert (IC1 : icells_ms mm) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]])
  end.
  call (amemset_chk usp d n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
        | exact CD1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk bsegs _ lo (usp + -2128) |- _ => rename H into ST3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST : rw_cells bsegs mm d [CB (Z.to_nat n) junk])
      by (unfold keep in DST0; apply (rw_cells_agree bsegs m mm _ _ DST0); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; cbn [cells_size csize] in Hy; rewrite Nat.add_0_r, Z2Nat.id in Hy by lia; (split; [lia| exact I]))
  end.
  clear CD1 IC1 M2S1 MUf DST0.

  do 3 lstep.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  -
    eapply evt_cut; [eapply memset_callZ; [exact DST| assumption| lia| lia| lia| lia]|].
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    rewrite NZ0, Z.add_0_r in MUc.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (MUe : munch [] m1 m2) by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MUc; transport_after_call bsegs m1 m2 MUe WMc; clear MUe WMc end.
    replace (ret_pc (Z_to_bv 64 0x7edb0)) with (Z_to_bv 64 0x7edb0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 9 lstep.
    release_frame FR ST3 (usp + -56). release_frame FRs ST3 usp.
    lstep.
    unfold amemset_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
  - call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
    do 9 lstep.
    release_frame FR ST3 (usp + -56). release_frame FRs ST3 usp.
    lstep.
    unfold amemset_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
Qed.

End WithRIP.
