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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pck I_pcbits I_pcseg I_pchead I_pcdint.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcrr I_pcdstr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcxa I_pcxdir I_pcxchk I_pcxprec F_achk.
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



Local Ltac ck_head_cs :=
  xsteps_to 0x1d5ff0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x1d5ff0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x1d5ff0%Z; strchr_call;                 (* [comment removed for export] *)
  xsteps_to 0x1d5ff0%Z; strchr_call.                 (* [comment removed for export] *)

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma istrnlen_loop : forall (n : nat) (k : nat) (s J : Z) (str : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  cstr_at m s str -> (length str = k + n)%nat -> Z.of_nat k < J -> J < 2^63 -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists a3' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.min J (Z.of_nat (length str)))) (Z_to_bv 64 J) (Z_to_bv 64 s) a3' a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1d6318) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 J) (Z_to_bv 64 s) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d6300) fc None m (seg_rom ctasegs)).
Proof.
  induction n as [|n IH]; intros k s J str ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    CS LEN KJ JH MI.
  - pose proof (cstr_bound m s str CS) as (S0 & SB).
    pose proof (cstr_nul m s str CS) as NUL. rewrite LEN, Nat.add_0_r in NUL. pose proof (ro_C1_of_bytes m _ _ NUL) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
    assert (EUJ : bv_unsigned (Z_to_bv 64 J) = J) by (apply unsigned_lit; lia).
    assert (EUsk : bv_unsigned (Z_to_bv 64 (s + Z.of_nat k)) = s + Z.of_nat k) by (apply unsigned_lit; lia).
    lstep. setreg 13%Z (Z_to_bv 64 (s + Z.of_nat k)) ltac:(first [reflexivity | f_equal; lia]).
    set (p := s + Z.of_nat k) in *. lstep. lstep. change (bv_unsigned z8) with 0 in *. br2 K.
    apply evt_done. eexists. rewrite LEN, Nat.add_0_r. replace (Z.min J (Z.of_nat k)) with (Z.of_nat k) by lia. reflexivity.
  - pose proof (cstr_bound m s str CS) as (S0 & SB).
    destruct (cstr_byte m s str k CS ltac:(lia)) as (b & Hb & Bnz & _). pose proof (ro_C1_of_bytes m _ _ Hb) as CB0.
    pose proof (z8_neq b Bnz) as BNZ. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia).
    assert (EUJ : bv_unsigned (Z_to_bv 64 J) = J) by (apply unsigned_lit; lia).
    assert (EUsk : bv_unsigned (Z_to_bv 64 (s + Z.of_nat k)) = s + Z.of_nat k) by (apply unsigned_lit; lia).
    lstep. setreg 13%Z (Z_to_bv 64 (s + Z.of_nat k)) ltac:(first [reflexivity | f_equal; lia]).
    set (p := s + Z.of_nat k) in *. lstep. lstep. br2 K. subst p.
    lstep. lstep.
    if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      apply (IH (S k) s J str); [exact CS | lia | rewrite ?unsigned_lit in K2 by lia; lia | exact JH | exact MI].
    + (* [comment removed for export] *)
      lstep. apply evt_done. eexists. replace (Z.min J (Z.of_nat (length str))) with J by (rewrite ?unsigned_lit in K2 by lia; lia). reflexivity.
Qed.

Lemma internal_strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s J : Z) (str : list byte),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 J -> 0 < J < 2^63 -> cstr_at m s str -> mem_inv ctasegs m ->
  evt ctasegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.min J (Z.of_nat (length str))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d62f4) fc None m (seg_rom ctasegs)).
Proof.
  intros until str. intros -> -> HJ CS MI.
  pose proof (cstr_bound m s str CS) as (S0 & SB).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUJ : bv_unsigned (Z_to_bv 64 J) = J) by (apply unsigned_lit; lia).
  lstep. if_cases K0; zify_cond K0; [ exfalso; rewrite ?unsigned_lit in K0 by lia; lia |].
  lstep. lstep. change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)).
  eapply evt_cut; [eapply (istrnlen_loop (length str) 0 s J str); [exact CS | lia | lia | lia | exact MI] |].
  intros ms (a3' & ->).
  lstep.
  apply evt_done. unfold leaf_post. do 14 eexists. exists m.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_ck_nullP_spec : forall (q p ap lo : Z) (fw fp : word) (bg en ws sp : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  spr = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) -> (sp = 0 \/ sp = 1) ->
  rw_cells ctasegs m (q + -2216) (DIRXP fw fp bg en ws sp 0 115) ->
  ro_cells ctasegs m (ap + zws ws + zws sp) [C8 (Z_to_bv 64 0)] ->
  stk ctasegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q <= ap -> ap + 24 < 2^63 ->
  mem_inv ctasegs m ->
  evt ctasegs (pck_post q p (ap + zws ws + zws sp + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1c14) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS SP DIR SLOT ST LO LOLO QHI APQ APH MI. unfold DIRXP in DIR.
  unfold kHighShadowEnd in LOLO. pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (EUap8 : bv_unsigned (Z_to_bv 64 (ap + 8)) = ap + 8) by (apply unsigned_lit; lia).
  assert (EUap16 : bv_unsigned (Z_to_bv 64 (ap + 16)) = ap + 16) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; destruct SP as [-> | ->]; cbn [zws Z.eqb] in SLOT |- *.
  3: xsteps_to 0x1d5ff0%Z; strchr_call.
  4: xsteps_to 0x1d5ff0%Z; strchr_call.
  2: xsteps_to 0x1d5ff0%Z; strchr_call.
  4: xsteps_to 0x1d5ff0%Z; strchr_call.
  all: ck_head_cs.
  all: try rewrite Z.add_0_r in SLOT.
  all: try replace (ap + 8 + 8) with (ap + 16) in SLOT by lia.
  all: xsteps_to 0x1b1a64%Z.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| eexists; exact DIR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_ck_strstar_spec : forall (q p ap lo S : Z) (fw fp : word) (bg en ws : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  spr = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) ->
  rw_cells ctasegs m (q + -2216) (DIRXP fw fp bg en ws 1 0 115) ->
  ro_cells ctasegs m (ap + zws ws + 8) [C8 (Z_to_bv 64 S)] -> 0 < S < 2^64 ->
  stk ctasegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q <= ap -> ap + 24 < 2^63 ->
  mem_inv ctasegs m ->
  evt ctasegs (pck_post q p (ap + zws ws + 8 + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1c14) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS DIR SLOT SNZ ST LO LOLO QHI APQ APH MI. unfold DIRXP in DIR.
  unfold kHighShadowEnd in LOLO. pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (EUap8 : bv_unsigned (Z_to_bv 64 (ap + 8)) = ap + 8) by (apply unsigned_lit; lia).
  assert (EUap16 : bv_unsigned (Z_to_bv 64 (ap + 16)) = ap + 16) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; cbn [zws Z.eqb] in SLOT |- *.
  2: xsteps_to 0x1d5ff0%Z; strchr_call.
  all: xsteps_to 0x1d5ff0%Z; strchr_call.          (* [comment removed for export] *)
  all: ck_head_cs.
  all: try rewrite Z.add_0_l in SLOT; try replace (ap + 0 + 8) with (ap + 8) in SLOT by lia; try replace (ap + 8 + 8) with (ap + 16) in SLOT by lia.
  all: xsteps_to 0x1b1a64%Z.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST| eexists; exact DIR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_ck_strnum_spec : forall (q p ap lo S : Z) (str : list byte) (fw fp : word) (bg en ws : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  spr = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s3 = Z_to_bv 64 p -> s5 = Z_to_bv 64 ap -> s8 = Z_to_bv 64 (q + -2184) ->
  s10 = Z_to_bv 64 (-1) ->
  (ws = 0 \/ ws = 1) ->
  rw_cells ctasegs m (q + -2216) (DIRXP fw fp bg en ws 0 0 115) ->
  ro_cells ctasegs m (ap + zws ws) [C8 (Z_to_bv 64 S)] ->
  cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ q <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
  chkr m S (Z.of_nat (length str) + 1) -> pctx m ->
  stk ctasegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q <= ap -> ap + 16 < 2^63 ->
  mem_inv ctasegs m ->
  evt ctasegs (pck_post q p (ap + zws ws + 8) gp tp s0 s2 s4 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1c14) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros -> -> -> -> -> -> WS DIR SLOT CS S0 SSEP SH CHK PCX ST LO LOLO QHI APQ APH MI. unfold DIRXP in DIR.
  unfold kHighShadowEnd in LOLO. pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(q + -2320, q + -2240)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
  assert (EUap8 : bv_unsigned (Z_to_bv 64 (ap + 8)) = ap + 8) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zhide.
  destruct WS as [-> | ->]; cbn [zws Z.eqb] in SLOT |- *.
  2: xsteps_to 0x1d5ff0%Z; strchr_call.
  all: ck_head_cs.
  all: try rewrite Z.add_0_r in SLOT.
  all: xsteps_to 0x1b1e10%Z.
  all: lstep.                                      (* [comment removed for export] *)
  all: if_cases KJ; zify_cond KJ.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1777172) _ _ _ _) =>
    xsteps_to 0x1d62f4%Z;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (CS1 : cstr_at mm S str) by
           (apply (cstr_agree m mm S str CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia) end;
    setreg 11%Z (Z_to_bv 64 (bv_unsigned (sx32 fp))) ltac:(first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]);
    call (internal_strnlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S (bv_unsigned (sx32 fp)) str);
       [reflexivity | reflexivity | lia | exact CS1 | assumption |];
    lstep; lstep; lstep; lstep;
    setreg 23%Z (Z_to_bv 64 (Z.min (bv_unsigned (sx32 fp)) (Z.of_nat (length str) + 1)))
      ltac:(f_equal; destruct (Z.ltb_spec0 (Z.min (bv_unsigned (sx32 fp)) (Z.of_nat (length str))) (bv_unsigned (sx32 fp))); cbn [Z.b2z]; lia)
  | _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1777276) _ _ _ _) =>
    xsteps_to 0x1d6090%Z;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (CS1 : cstr_at mm S str) by
           (apply (cstr_agree m mm S str CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia) end;
    call internal_strlen_spec; [reflexivity| exact CS1| assumption|];
    xsteps_to 0x1b1e88%Z
  | _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         let n := reg_val 23%Z in
         lazymatch n with Z_to_bv 64 ?nz =>
         assert (CHK1 : chk_ok mm S nz) by
           (apply chkr_chk_ok; apply (chkr_sub mm S (Z.of_nat (length str) + 1)); [| lia | lia | lia];
            eapply chkr_munch; [exact CHK | exact MU | intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia]);
         assert (PCX1 : pctx mm) by
           (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
         destruct PCX1 as (M2S1 & PC1);
         call (pcs_check RIP (q + -2240) S nz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)
         end end.
  all: try first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | lia ].
  all: xsteps_to 0x1b1a64%Z.
  all: lazymatch goal with H : stk ctasegs _ ?lo0 (bv_unsigned (Z_to_bv 64 (?qq + -2240))) |- _ => rewrite EUs in H; rename H into ST2 end.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: lazymatch goal with |- evt _ (pck_post _ _ ?apv _ _ _ _ _ _ _ _ _ _ _ _ _) _ => setreg 21%Z (Z_to_bv 64 apv) ltac:(f_equal; lia) end.
  all: apply evt_done; unfold pck_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2| eexists; exact DIR].
Qed.

End WithRIP.
