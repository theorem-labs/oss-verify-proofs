(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_thread I_qck X_atexit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import I_pck I_pcbits I_pcseg I_pcdint.
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

Lemma fgvs_l_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c qa lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 qa -> a2 = Z_to_bv 64 1 -> (c = 100 \/ c = 117 \/ c = 120) ->
  bytes_at bsegs m qa [Z_to_bv 8 108] -> bv_unsigned sp <= qa < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 8 [(bv_unsigned sp - 32, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74e58) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> CC QAb QA0 ST LO SPH MI.
  pose proof (ro_C1_of_bytes m qa _ QAb) as QA. clear QAb.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 qa) = qa) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  do 12 lstep.
  destruct CC as [-> | [-> | ->]].
  all: call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_dioux; assumption| assumption|].
  all: match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
  all: lstep; if_false.
  all: lstep; lstep; lstep; lstep; if_false.
  all: lstep; lstep; lstep; lstep; lstep; lstep; if_false.
  all: do 6 lstep.
  all: release_frame FR ST usp.
  all: lstep.
  all: apply evt_done; unfold frame_post; do 15 eexists; split; [rewrite ESP; reflexivity|].
  all: rewrite EU; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST].
Qed.

Lemma fgvs_g_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c qa lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 qa -> a2 = Z_to_bv 64 1 -> c = 103 ->
  bytes_at bsegs m qa [z8] -> bv_unsigned sp <= qa < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 8 [(bv_unsigned sp - 32, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74e58) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> -> QAb QA0 ST LO SPH MI.
  pose proof (ro_C1_of_bytes m qa z8 QAb) as QA. clear QAb.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 qa) = qa) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  do 12 lstep.
  call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_dioux; assumption| assumption|].
  match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
  lstep; if_true.
  xsteps_to 0x921dc%Z.
  call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_flt; assumption| assumption|].
  match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
  lstep; if_false.
  lstep. lstep. lstep. lstep; if_false.
  lstep; if_true.
  lstep; if_true.
  do 6 lstep.
  release_frame FR ST usp.
  lstep.
  apply evt_done; unfold frame_post; do 15 eexists; split; [rewrite ESP; reflexivity|].
  rewrite EU; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST].
Qed.

Lemma pcom_epi_spec : forall (q : Z) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) ->
  rw_cells bsegs m (q + -104) (pcom_saved ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
  2240 <= q < 2^63 -> mem_inv bsegs m ->
  evt bsegs (pcom_end_post q ra0 gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6ea7c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> SV QR MI. unfold pcom_saved in SV.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  do 16 lstep.
  apply evt_done. unfold pcom_end_post. do 16 eexists. split; [ first [reflexivity | f_equal; f_equal; f_equal; lia] |].
  split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Definition pcx_post (q : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x6ea7c) fc None m' (seg_rom bsegs)
    /\ munch [(q + -2320, q + -2240); (q + -2216, q + -2176)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (q + -2240)
    /\ (exists junk, rw_cells bsegs m' (q + -2216) [CB 40 junk]).

Lemma pcom_dl0_spec : forall (q p ap c lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 89415 ->
  s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
  (c = 100 \/ c = 117 \/ c = 120) ->
  bytes_at bsegs m p (zb8 [37; 108; c] ++ [z8]) -> rw_cells bsegs m (q + -2216) DIR0 ->
  stk bsegs m lo (q + -2240) -> 0 <= lo <= q + -2320 -> p + 4 <= lo \/ q <= p -> p + 4 < 2^63 -> q <= 2^47 -> 0 <= ap -> ap + 16 < 2^63 ->
  mem_inv bsegs m ->
  evt bsegs (pcx_post q gp tp F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e2d0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> -> -> -> -> -> -> -> -> -> CC BY DIR ST LO PLO PH QH AP AP2 MI.
  apply dir0_split in DIR. unfold DIRS in DIR. cbn [repeat] in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map app] in PB.
  unfold zb8 in BY. cbn [map app] in BY.
  pose proof (bytes_at_nth1 bsegs m p _ 0 _ BY eq_refl) as B0. pose proof (bytes_at_nth1 bsegs m p _ 1 _ BY eq_refl) as B1.
  pose proof (bytes_at_nth1 bsegs m p _ 2 _ BY eq_refl) as B2. pose proof (bytes_at_nth1 bsegs m p _ 3 _ BY eq_refl) as B3. clear BY.
  change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. change (Z.of_nat 3) with 3 in B3.
  rewrite Z.add_0_r in B0.
  apply ro_C1_of_bytes in B0. apply ro_C1_of_bytes in B1. apply ro_C1_of_bytes in B2. apply ro_C1_of_bytes in B3.
  pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  destruct CC as [-> | [-> | ->]].
  zhide.
  all: xsteps_to 0x921dc%Z.
  all: strchr_call.
  all: xsteps_to 0x921dc%Z.
  all: strchr_call.
  all: xsteps_to 0x921dc%Z.
  all: strchr_call.
  all: xsteps_to 0x74e58%Z.
  all: call fgvs_l_spec;
    [ reflexivity | reflexivity | reflexivity | first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]
    | eapply (cells_byte _ _ _ 34%nat (Z_to_bv 8 108)); [exact DIR | reflexivity | lia] | rewrite EUs; lia | rewrite EUs; exact ST | rewrite EUs; lia | rewrite EUs; lia
    | assumption | ].
  all: xsteps_to 0x921dc%Z.
  all: strchr_call.
  all: xsteps_to 0x6ea7c%Z.
  all: rewrite EUs in POST.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: apply evt_done; unfold pcx_post; do 29 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption| split; [exact POST| eexists; exact DIR]].
Qed.

Lemma pcom_dg0_spec : forall (q p ap lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 89415 ->
  s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
  bytes_at bsegs m p (zb8 [37; 46; 42; 103] ++ [z8]) -> rw_cells bsegs m (q + -2216) DIR0 ->
  stk bsegs m lo (q + -2240) -> 0 <= lo <= q + -2320 -> p + 5 <= lo \/ q <= p -> p + 5 < 2^63 -> q <= 2^47 -> 0 <= ap -> ap + 16 < 2^63 ->
  mem_inv bsegs m ->
  evt bsegs (pcx_post q gp tp F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e2d0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> -> -> -> -> -> -> -> -> -> BY DIR ST LO PLO PH QH AP AP2 MI.
  apply dir0_split in DIR. unfold DIRS in DIR. cbn [repeat] in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map app] in PB.
  unfold zb8 in BY. cbn [map app] in BY.
  pose proof (bytes_at_nth1 bsegs m p _ 0 _ BY eq_refl) as B0. pose proof (bytes_at_nth1 bsegs m p _ 1 _ BY eq_refl) as B1.
  pose proof (bytes_at_nth1 bsegs m p _ 2 _ BY eq_refl) as B2. pose proof (bytes_at_nth1 bsegs m p _ 3 _ BY eq_refl) as B3.
  pose proof (bytes_at_nth1 bsegs m p _ 4 _ BY eq_refl) as B4. clear BY.
  change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. change (Z.of_nat 3) with 3 in B3.
  change (Z.of_nat 4) with 4 in B4. rewrite Z.add_0_r in B0.
  apply ro_C1_of_bytes in B0. apply ro_C1_of_bytes in B1. apply ro_C1_of_bytes in B2. apply ro_C1_of_bytes in B3. apply ro_C1_of_bytes in B4.
  pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  zhide.
  xsteps_to 0x921dc%Z. strchr_call.
  xsteps_to 0x921dc%Z. strchr_call.
  xsteps_to 0x921dc%Z. strchr_call.
  xsteps_to 0x921dc%Z. strchr_call.
  xsteps_to 0x74e58%Z.
  call fgvs_g_spec;
    [ reflexivity | reflexivity | reflexivity | reflexivity
    | eapply (cells_byte _ _ _ 34%nat z8); [exact DIR | reflexivity | lia] | rewrite EUs; lia | rewrite EUs; exact ST | rewrite EUs; lia | rewrite EUs; lia
    | assumption | ].
  xsteps_to 0x921dc%Z. strchr_call.
  xsteps_to 0x6ea7c%Z.
  rewrite EUs in POST.
  apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  apply evt_done; unfold pcx_post; do 29 eexists; split; [reflexivity|].
  split; [exact MU|]; split; [exact WM|]; split; [assumption| split; [exact POST| eexists; exact DIR]].
Qed.
