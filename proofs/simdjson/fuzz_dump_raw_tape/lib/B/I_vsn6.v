(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_pcd6 I_pcfmt6 I_vprintfw I_vfsn6.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import FX_lib F_memset F_memcpy F_fwritex Fe_pop_arg Fe_printf_iface Fe_printf_core Fe_printf_snsink F_sn_write F_towrite Fe_vfprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Fe_pkit F_achk I_memsetw Fe_icalls Fe_vsnprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad PrintfModel.
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

Lemma ivsn_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6ef38) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6ef28) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
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

Definition ivsn_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lts_small6 : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.
Ltac br_is6 b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition ivsn_pre_epi (usp r : Z) (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6ee08) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 2240, usp - 2160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2160).

Lemma ivsn_rip : forall (usp D n' r : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 0 < n' -> D + n' < 2^63 ->
  acc bsegs m D n' -> rng_ok D n' -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (ivsn_pre_epi usp r gp tp s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6ef40) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| rewrite EUsp; lia
             | unfold kHighShadowEnd in *; lia | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. unfold ivsn_pre_epi. do 24 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma ivsn_chk : forall (usp D n n' r : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 <= D -> 1 <= n' < 2^31 -> D + n' < 2^63 -> 1 <= n < 2^63 ->
  chk_ok m D n' -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (ivsn_pre_epi usp r gp tp s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n') (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6edc0) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN NN (AC & QW & RO) M2S MI.
  pose proof M2S as (G1 & SHC & _).
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n') = n') by (apply unsigned_lit; lia).
  assert (EUnn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUu : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n') as [BIG|SMALL].
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n' + -65)) = n' - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (ivsn_rip usp D n' r); try assumption; lia.
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n' + -65)) = n' - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2. unfold SHB.
    assert (E1 : Z.land (Z.land (2147450880 + D ≫ 3) 18446744073709551615) 18446744073709551608 = 8 * ((D / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (Z.div_mod_to_equations; lia).
      rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land (Z.land (2147450880 + (D + n' + -1) ≫ 3) 18446744073709551615) 18446744073709551608 = 8 * (((D + n' - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (Z.div_mod_to_equations; lia).
      rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (D + n' + -1) with (D + n' - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    +
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (D + n' + -1) / 8) with ((D + n' - 1) / 8 + 2147450880) by lia.
      replace (2147450880 + D / 8) with (D / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m D n' AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((D + n' - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      *
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold ivsn_pre_epi. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (ivsn_rip usp D n' r); try assumption; try lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (ivsn_loop (Z.to_nat ((D + n' - 1) / 8 + 2147450880 - (D / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold ivsn_pre_epi. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (ivsn_rip usp D n' r); try assumption; try lia.
    + apply evt_done. unfold ivsn_pre_epi. do 24 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Definition ivsnA_post (usp D n A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j8 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x6eda0) (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 A)
                  (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 0x2096e8)
                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15e928) fc None m' (seg_rom bsegs)
    /\ munch [(usp - 4480, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -2160)
    /\ rw_cells bsegs m' (usp + -2160) ([CB 2064 j1; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8] ++ ivsn_saved ra s0 s1 s2 s3 s4 s5 s6 s7).

Lemma ivsn_walkA : forall (usp D n A VA lo : Z) (f : list Z)
    ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 4480 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= n < 2^64 ->
  FMT6 f -> cstr_at m A (zb8 f) -> (A + Z.of_nat (length f) + 1 <= lo \/ usp <= A) -> A + 8 <= 2^47 -> chk_ok m A (Z.of_nat (length f) + 1) ->
  0 <= VA -> VA + 16 < 2^63 ->
  pctx m -> pfcells6 m -> mem_inv bsegs m ->
  evt bsegs (ivsnA_post usp D n A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a5bc) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 DD NN FM CSA AB AH CHKA VA0 VAH PCX (PFC & RVS) MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - 4480, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -2032)) = usp + -2032) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof (cstr_bound _ _ _ CSA) as (A0 & _).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 2160%nat ST. rename FR into FRf.
  apply (rw_cells_split_CB bsegs _ _ [] 2160 _ [] [2064; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
  zhide.
  xsteps_to 0x87dac%Z.
  call try_init_spec; [exact AI | rewrite EU2; exact ST | rewrite EU2; lia | lia | assumption |].
  xsteps_to 0x6e190%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CSA1 : cstr_at mm A (zb8 f)) by
      (apply (cstr_agree m mm _ _ CSA); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; rewrite ?length_zb8 in Hx; lia);
    assert (CHKA1 : chk_ok mm A (Z.of_nat (length f) + 1)) by
      (eapply chk_ok_agree; [exact CHKA | lia | destruct FM as [(?c & _ & ->) | ->]; cbn [length]; lia
       | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  call (pcom6_spec RIP A f VA lo);
    [ reflexivity | reflexivity | exact FM | exact CSA1 | rewrite EU2; lia | exact AH
    | exact ST | rewrite EU2; lia | (unfold kHighShadowEnd; lia) | rewrite EU2; lia
    | rewrite EU2; Z.div_mod_to_equations; lia | lia | lia | exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 PCX1. rename POST into ST. rewrite EU2 in ST.
  xsteps_to 0x15e928%Z.
  apply evt_done. unfold ivsnA_post, ivsn_saved. cbn [app]. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FRf.
Qed.

Lemma ivsn_walkC : forall (usp D n A VA r lo : Z) (j1 j8 : list byte)
    (ra' ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 ->
  0 <= D -> 0 <= r -> r + 1 <= n -> r + 1 < 2^31 -> D + r + 1 < 2^63 -> n < 2^63 ->
  chk_ok m D (r + 1) -> m2s_cells m ->
  rw_cells bsegs m (usp + -2160) ([CB 2064 j1; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8] ++ ivsn_saved ra s0 s1 s2 s3 s4 s5 s6 s7) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(usp - 2240, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 A) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 0x2096e8) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6eda0) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH D0 R0 RN R31 DN NH CHK M2S FRf MI.
  unfold kHighShadowEnd in LOLO. unfold ivsn_saved in FRf. cbn [app] in FRf.
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  zhide.
  lstep. br_is6 false ltac:(change Startup_glue.z64 with (Z_to_bv 64 0); rewrite lts_small6 by lia; apply Z.ltb_ge; lia).
  lstep. rewrite swrap32_small by lia.
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  lstep. lstep. if_true.
  lstep. lstep. lstep. lstep. rewrite zb_lxor_ones by lia.
  assert (EUx : bv_unsigned (Z_to_bv 64 (18446744073709551615 - D)) = 18446744073709551615 - D) by (apply unsigned_lit; lia).
  lstep. if_true.
  eapply evt_cut.
  { apply (ivsn_chk usp D n (r + 1) r) with (lo := lo); try assumption; try lia; unfold kHighShadowEnd; lia. }
  cbv beta. intros ms1 P. unfold ivsn_pre_epi in P.
  destruct P as (m1 & ra1 & u0 & u1 & u2 & v0 & v1 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MU1 & WM1 & MI1 & ST1).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRf MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRf1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m mm MU1 WM1 end.
  do 11 lstep.
  release_frame FRf1 ST1 usp.
  lstep.
  apply evt_done. do 15 eexists. split; [first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia] |].
  split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  split; [exact WM1|]. split; [exact MI1| exact ST1].
Qed.
End WithRIP.

Definition MOK_el (fmt : list Z) (args : list parg) : Prop :=
  forall (r : Z) (o : list Z), printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (ITree.Exc.Ok (r, o)) -> 0 <= r /\ r = zlength o /\ r < 2^31 - 1.
Definition PCOK2_el (fmt : list Z) (args : list parg) (slots : list word) (A VA lo : Z) (m : mem) : Prop :=
  PCOK_el fmt args slots A VA lo m /\ MOK_el fmt args.

Lemma ivfsn_mono : forall (P1 P2 : list Z -> list parg -> list word -> Z -> Z -> Z -> mem -> Prop),
  (forall fmt args slots A VA lo m, P2 fmt args slots A VA lo m -> P1 fmt args slots A VA lo m) ->
  ivfsn_stmt P1 -> ivfsn_stmt P2.
Proof.
  intros P1 P2 HP H1. unfold ivfsn_stmt in *. intros until o. cbv zeta. intros.
  eapply H1; try eassumption. apply HP. assumption.
Qed.

Lemma args_ok_sp_mono : forall Fp B BS m lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> args_ok Fp B BS m lo sp' ap ws args.
Proof.
  intros Fp B BS m lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH ws H2 Hsp)].
  destruct a; cbn [arg_ok] in H1 |- *; try exact H1.
  destruct H1 as (slack & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). exists slack.
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [lia|]. split; [exact B6|]. split; [exact B7|]. split; [exact B8| exact B9].
Qed.

Section Proof6.
Hypothesis RIP : rip_stmt.
Local Ltac tr_chk C MU := apply (chkr_munch _ _ _ _ _ C MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.

Theorem ivsn_proof : ivsn_stmt PCOK2_el.
Proof using RIP.
  pose proof (vsnprintf_proof RIP PCOK2_el (ivfsn_mono PCOK_el PCOK2_el (fun fmt args slots A VA lo m H => proj1 H) (ivfsn_proof RIP))) as REAL.
  unfold ivsn_stmt. intros until ap0. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA DFMT QVA VAHI DD1 DVA GD
    HQ47 HQ16 HSH IC STKC FMTC ROD CHD DSH RODFP IFX PCO.
  set (q := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (PCO m (munch_refl _ m) (wmono_refl bsegs m)) as (((f & FM & EF) & VA0 & VAH & PCX & PFC) & MOK).
  destruct (MOK r o MODEL) as (R0 & ER & R31).
  unfold IVSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd, e_vsnprintf_stub in *.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (FMT6_txt f FM) as (_ & FL).
  assert (LF : zlength fmt = Z.of_nat (length f) + 1) by (rewrite EF; unfold zlength; rewrite length_app; cbn [length]; lia).
  assert (CSA : cstr_at m A (zb8 f)) by (apply (FMT6_cstr m A f FM); rewrite <- EF; exact BY).
  pose proof (chkr_bound m A _ FMTC) as (_ & AHI). unfold kHighMemEnd in AHI.
  assert (CHKA : chk_ok m A (Z.of_nat (length f) + 1)) by (rewrite <- LF; exact (chkr_chk_ok m A _ FMTC)).
  assert (AB : A + Z.of_nat (length f) + 1 <= lo \/ q <= A) by (clear - HA LF QVA GLO; unfold zlength in HA, LF; lia).

  eapply evt_cut.
  { rewrite ESP. eapply (ivsn_walkA RIP q D n A VA lo f);
      first [exact ST | exact FM | exact CSA | exact AB | exact CHKA | exact PCX | exact PFC | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms1 P. unfold ivsnA_post in P.
  destruct P as (m1 & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j1 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FRf).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (q + -2160)) = q + -2160) by (apply unsigned_lit; lia).
  unfold VSN_W in *.

  assert (AOK1 : forall m', munch [(lo, q + -2160); (D, D + Z.of_nat dn)] m1 m' -> args_ok F0 B0 BS0 m' lo (q + -2160) ap0 slots args).
  { intros m' MU'. apply (args_ok_sp_mono F0 B0 BS0 m' lo q); [| lia]. apply AOK.
    apply (munch_trans _ m m1 m'); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU']];
      unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  assert (PCO1 : forall m', munch [(lo, q + -2160); (D, D + Z.of_nat dn)] m1 m' -> wmono bsegs m1 m' -> PCOK2_el fmt args slots A VA lo m').
  { intros m' MU' WM'. apply PCO; [| exact (wmono_trans _ _ _ _ WM1 WM')].
    apply (munch_trans _ m m1 m'); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU']];
      unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  assert (STK1 : forall p n, lo <= p -> p + n <= q + -2160 -> chkr m1 p n).
  { intros p n' Hp1 Hp2. apply (chkr_munch _ m m1 p n' (STKC p n' Hp1 ltac:(lia)) MU1).
    intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia. }
  assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; lia).
  assert (FMTC1 : chkr m1 A (zlength fmt)) by tr_chk FMTC MU1.
  assert (ROD1 : rod_chk m1).
  { destruct ROD as (R1 & R2 & R3). split; [| split]; [tr_chk R1 MU1 | tr_chk R2 MU1 | tr_chk R3 MU1]. }
  assert (RODFP1 : rod_chk_fp m1).
  { destruct RODFP as (R1 & R2 & R3 & R4 & R5 & R6).
    split; [| split; [| split; [| split; [| split]]]]; [tr_chk R1 MU1 | tr_chk R2 MU1 | tr_chk R3 MU1 | tr_chk R4 MU1 | tr_chk R5 MU1 | tr_chk R6 MU1]. }
  pose proof (chkr_bound m D _ CHD) as (D0 & _).
  assert (CHD1 : chkr m1 D (zlength o)).
  { apply (chkr_munch _ m m1 D _ (chkr_sub m D (zlength o + 1) D (zlength o) CHD ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) MU1).
    intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia. }
  destruct SSP as (SSP1 & SSP2). unfold got_ssp, ssp_guard in SSP1, SSP2. unfold va_area in VAA. unfold ifx_real in IFX.
  pose proof (u64s_length slots) as LU. pose proof (bytes_at_bound _ _ _ _ BY) as BYB. rewrite zb_length in BYB.
  assert (BY1 : bytes_at bsegs m1 A (zb fmt)).
  { apply (bytes_at_agree bsegs _ _ _ _ BY). apply (agree_of_munch _ _ _ _ MU1). intros ?x ?Hx. rewrite zb_length in Hx.
    clear - Hx HA QVA LF LO GLO. cbn [outside]. unfold zlength in *. lia. }
  clear BY.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m mm MU1 WM1 end.
  eapply evt_cut.
  { eapply REAL with (D := D) (n := n) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := slots) (args := args)
      (lo := lo) (canary := canary) (r := r) (o := o) (F0 := F0) (B0 := B0) (BS0 := BS0) (ap0 := ap0);
      rewrite ?EU2; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd, VSN_W, ifx_real.
    all: try first [ reflexivity | exact DST | exact BY1 | exact HF | exact P1 | exact VAA | exact AOK1 | exact MODEL | exact FPF | exact ROOM
               | exact Hn | exact Hn1 | exact ST1 | split; [exact SSP1 | exact SSP2] | exact MI1 | exact FRM | exact HA0 | exact IC1
               | exact STK1 | exact FMTC1 | exact ROD1 | exact RODFP1 | exact CHD1 | exact DSH | exact IFX | exact PCO1 | lia ].
  }
  cbv beta. intros ms2 P. unfold vsnprintf_post in P. rewrite ?EU2 in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2
                 & FOK & ST2 & SSP' & DST2).
  unfold ivsn_saved in FRf. cbn [app] in FRf.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRf MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRf2.
  replace (ret_pc (Z_to_bv 64 0x6eda0)) with (Z_to_bv 64 0x6eda0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (CHK2 : chk_ok m2 D (r + 1)).
  { apply chkr_chk_ok. rewrite ER.
    apply (chkr_munch _ m1 m2 D _ ltac:(apply (chkr_munch _ m m1 D _ CHD MU1); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia) MU2).
    intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia. }
  assert (IC2 : ictx m2) by (apply (ictx_munch _ m1 m2 IC1 MU2 WM2); intros ?x ?Hx; cbn [in_rl ICR outside] in *; lia).
  destruct IC2 as (_ & _ & _ & M2S2).
  pose proof (chkr_bound m D _ CHD) as (_ & DRB). unfold kHighMemEnd in DRB.

  eapply evt_mono.
  { eapply (ivsn_walkC RIP q D n A VA r lo j1 j8); first [exact ST2 | exact CHK2 | exact M2S2 | exact FRf2 | exact MI2 | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms3 (m3 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & -> & MU3 & WM3 & MI3 & ST3).
  unfold vsnprintf_post. rewrite <- ESP.
  exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, Ft, fc', m3.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2) |].
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia.
           - eapply munch_weaken; [| exact MU3]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)|]. split; [exact MI3|]. split; [exact FRM2|]. split; [exact FOK|].
  split; [exact ST3|].
  destruct SSP' as (X1 & X2). unfold got_ssp, ssp_guard in X1, X2 |- *.
  assert (AG3 : agree_on (fun x => x < q - 2240 \/ q <= x) m2 m3).
  { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. lia. }
  split. { split; [ first [ apply (ro_cells_agree bsegs m2 m3 _ _ X1) | apply (rw_cells_agree bsegs m2 m3 _ _ X1); [| exact WM3] ]
                  | first [ apply (ro_cells_agree bsegs m2 m3 _ _ X2) | apply (rw_cells_agree bsegs m2 m3 _ _ X2); [| exact WM3] ] ];
           apply (agree_sub _ _ _ _ AG3); cbn [cells_size csize Nat.add]; intros ?x ?Hx; lia. }
  apply (rw_cells_agree bsegs m2 m3 _ _ DST2); [| exact WM3]. apply (agree_sub _ _ _ _ AG3); cbn [cells_size csize Nat.add]; intros ?x ?Hx; lia.
Qed.
End Proof6.
