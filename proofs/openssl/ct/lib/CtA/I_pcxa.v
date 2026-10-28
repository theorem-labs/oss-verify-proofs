(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_thread I_qck X_atexit I_pck I_pcbits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition is_digit (c : Z) : Prop := 48 <= c <= 57.
Lemma u8_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Ltac brWF K := if_cases K; zify_cond K;
  [ exfalso; rewrite ?u8_lit in K by lia; rewrite ?unsigned_lit_wrap in K; change (2^64)%Z with 18446744073709551616%Z in K;
    Z.div_mod_to_equations; lia | ].
(* [comment removed for export] *)
Lemma land_ones64 : forall x, Z.land x 18446744073709551615 = x mod 18446744073709551616.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac brk K := exfalso; try (change (bv_unsigned z8) with 0 in K); rewrite ?u8_lit in K by lia; rewrite ?unsigned_lit_wrap in K;
  rewrite ?land_ones64 in K; change (2^64)%Z with 18446744073709551616%Z in K; Z.div_mod_to_equations; lia.
Ltac br2 K := if_cases K; zify_cond K; [ try brk K | try brk K ].
Ltac brWT K := if_cases K; zify_cond K;
  [ | exfalso; rewrite ?u8_lit in K by lia; rewrite ?unsigned_lit_wrap in K; change (2^64)%Z with 18446744073709551616%Z in K;
    Z.div_mod_to_equations; lia ].

Lemma zb8_cons : forall c l, zb8 (c :: l) = Z_to_bv 8 c :: zb8 l.
Proof. reflexivity. Qed.
Lemma zb8_app : forall l1 l2, zb8 (l1 ++ l2) = zb8 l1 ++ zb8 l2.
Proof. intros. unfold zb8. apply map_app. Qed.
Lemma length_zb8 : forall l, length (zb8 l) = length l.
Proof. intros. unfold zb8. apply length_map. Qed.

(* [comment removed for export] *)
Lemma bytes_uncons : forall m p c l, bytes_at ctasegs m p (zb8 (c :: l)) ->
  ro_cells ctasegs m p [C1 (Z_to_bv 8 c)] /\ bytes_at ctasegs m (p + 1) (zb8 l).
Proof.
  intros m p c l BY. rewrite zb8_cons in BY. change (Z_to_bv 8 c :: zb8 l) with ([Z_to_bv 8 c] ++ zb8 l) in BY.
  apply (proj1 (bytes_at_app ctasegs m p [_] _)) in BY. destruct BY as [B1 BY]. cbn [length Z.of_nat Pos.of_succ_nat] in BY.
  split; [exact (ro_C1_of_bytes m p _ B1) | exact BY].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac out_lia := cbn [outside]; repeat match goal with |- _ /\ _ => split end; first [ exact I | lia ].

(* [comment removed for export] *)
Definition leafw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'.

(* [comment removed for export] *)
Notation C_TENTH := 1844674407370955162 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma atoll_loop : forall (ds : list Z) (p c : Z)
    ra sp gp tp t0 t1 t2 s0 s1 (acc cur tmp : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  Forall is_digit ds -> 0 <= c < 256 -> ~ is_digit c ->
  bytes_at ctasegs m p (zb8 (ds ++ [c])) -> p + Z.of_nat (length ds) + 1 < 2^63 -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists acc' tmp' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat (length ds) + 1)) acc' (Z_to_bv 64 1) (Z_to_bv 64 c)
                    (Z_to_bv 64 C_TENTH) (Z_to_bv 64 10) (Z_to_bv 64 47) tmp' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1d5cd8) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) acc (Z_to_bv 64 1) cur (Z_to_bv 64 C_TENTH) (Z_to_bv 64 10) (Z_to_bv 64 47) tmp
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d5ca0) fc None m (seg_rom ctasegs)).
Proof.
  induction ds as [|d ds IH]; intros p c ra sp gp tp t0 t1 t2 s0 s1 acc cur tmp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    DS Hc NDc BY PH MI.
  - cbn [app] in BY. destruct (bytes_uncons m p c [] BY) as [CB0 _].
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map] in PB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    pose proof (u8_lit c Hc) as EUc. unfold is_digit in NDc.
    do 7 lstep. lstep. do 5 lstep. lstep. brWF K.
    rewrite EUc. apply evt_done. do 2 eexists. cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - apply Forall_cons_iff in DS. destruct DS as [Dd DS]. unfold is_digit in Dd.
    cbn [app] in BY. destruct (bytes_uncons m p d (ds ++ [c]) BY) as [CB0 BY'].
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map] in PB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    pose proof (u8_lit d ltac:(lia)) as EUd.
    do 7 lstep. lstep. do 5 lstep. lstep. brWT K.
    eapply evt_mono.
    { apply (IH (p + 1) c); try assumption; try lia. cbn [length] in PH |- *. lia. }
    intros ms (acc' & tmp' & ->). exists acc', tmp'. cbn [length]. rewrite Nat2Z.inj_succ.
    replace (p + Z.succ (Z.of_nat (length ds)) + 1) with (p + 1 + Z.of_nat (length ds) + 1) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma atoll_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p d0 c : Z) (ds : list Z),
  a0 = Z_to_bv 64 p -> is_digit d0 -> Forall is_digit ds -> 0 <= c < 256 -> ~ is_digit c ->
  bytes_at ctasegs m p (zb8 (d0 :: ds ++ [c])) -> p + Z.of_nat (length ds) + 2 < 2^63 -> mem_inv ctasegs m ->
  evt ctasegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d5c20) fc None m (seg_rom ctasegs)).
Proof.
  intros until ds. intros -> D0 DS Hc NDc BY PH MI. unfold is_digit in D0.
  destruct (bytes_uncons m p d0 (ds ++ [c]) BY) as [CB0 BY'].
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB. rewrite length_app in PB. cbn [length] in PB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  pose proof (u8_lit d0 ltac:(lia)) as EUd.
  (* [comment removed for export] *)
  do 6 lstep. brWF K1. lstep. brWF K2. lstep. lstep. brWF K3. lstep. lstep. brWT K4.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. brWF K5.
  lstep. xsteps_to 0x1d5ca0%Z.
  eapply evt_cut.
  { apply (atoll_loop ds (p + 1) c); try assumption; lia. }
  cbv beta. intros ms' (acc' & tmp' & ->).
  assert (EUq : bv_unsigned (Z_to_bv 64 (p + 1 + Z.of_nat (length ds) + 1)) = p + 1 + Z.of_nat (length ds) + 1) by (apply unsigned_lit; lia).
  lstep. brWF K6. lstep. lstep. lstep.
  if_cases K7.
  - lstep. lstep. apply evt_done. unfold leafw_post. do 15 eexists. exists m.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
  - lstep. lstep. lstep. apply evt_done. unfold leafw_post. do 15 eexists. exists m.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pcx_iconv (c : Z) : Prop := c = 100 \/ c = 105 \/ c = 117 \/ c = 120 \/ c = 88.

Lemma fgvs_spec2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c qa lm lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 qa -> a2 = Z_to_bv 64 1 -> pcx_iconv c -> (lm = 0 \/ lm = 108) ->
  bytes_at ctasegs m qa [Z_to_bv 8 lm] -> bv_unsigned sp <= qa < 2^64 ->
  stk ctasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> mem_inv ctasegs m ->
  evt ctasegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if lm =? 0 then 4 else 8)
               [(bv_unsigned sp - 32, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b88dc) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros -> -> -> CC LM QAb QA0 ST LO SPH MI.
  pose proof (ro_C1_of_bytes m qa _ QAb) as QA. clear QAb.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 qa) = qa) by (apply unsigned_lit; lia).
  destruct LM as [-> | ->]; cbn [Z.eqb].
  - pose proof (u8_lit 0 ltac:(lia)) as EUl.
    carve_frame 32%nat ST.
    do 12 lstep.
    destruct CC as [-> | [-> | [-> | [-> | ->]]]].
    all: call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_dioux; assumption| assumption|].
    all: match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
    all: lstep; if_false.
    all: lstep; lstep; lstep; lstep; if_true.
    all: lstep; if_true.
    all: do 6 lstep.
    all: release_frame FR ST usp.
    all: lstep.
    all: apply evt_done; unfold frame_post; do 15 eexists; split; [rewrite ESP; reflexivity|].
    all: rewrite EU; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST].
  - pose proof (u8_lit 108 ltac:(lia)) as EUl.
    carve_frame 32%nat ST.
    do 12 lstep.
    destruct CC as [-> | [-> | [-> | [-> | ->]]]].
    all: call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_dioux; assumption| assumption|].
    all: match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
    all: lstep; if_false.
    all: lstep. all: lstep. all: lstep. all: lstep. all: if_false.
    all: xsteps_to 0x1b8934%Z. all: lstep. all: if_false.
    all: do 6 lstep.
    all: release_frame FR ST usp.
    all: lstep.
    all: apply evt_done; unfold frame_post; do 15 eexists; split; [rewrite ESP; reflexivity|].
    all: rewrite EU; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST].
Qed.
