(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_thread I_qck X_atexit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import I_pck I_pcbits I_pcseg.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  cells_size cs' = cells_size cs -> rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[_ B] W] WF EB ES. split; [split; [exact WF | rewrite EB; exact B] | rewrite ES; exact W]. Qed.

(* [comment removed for export] *)
Definition DIRS : list cell :=
  [CB 8 (repeat z8 8); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); CB 8 (repeat z8 8); CB 8 (repeat z8 8);
   CB 1 [z8]; CB 1 [z8]; CB 1 [z8]; CB 1 [z8]; CB 1 [z8]; CB 3 (repeat z8 3)].

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma dir0_split : forall m q, rw_cells asegs m (q + -2216) DIR0 -> rw_cells asegs m (q + -2216) DIRS.
Proof.
  intros m q H. apply (rw_cells_recast m _ DIR0 DIRS H); [cbn; tauto | apply map_unsigned_inj; vm_compute; reflexivity | reflexivity].
Qed.

Lemma internal_strchr_spec' : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s c : Z) (str : list byte),
  a0 = Z_to_bv 64 s -> bv_unsigned a1 = c -> 0 < c < 256 -> cstr_at m s str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strchr_res s c str) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d4f40) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros E0 E1 C0 CS MI. replace a1 with (Z_to_bv 64 c) by (rewrite <- E1; apply Z_to_bv_bv_unsigned).
  exact (internal_strchr_spec ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m s c str E0 eq_refl C0 CS MI).
Qed.

(* [comment removed for export] *)
Ltac strchr_call :=
  call internal_strchr_spec';
  [ reflexivity | vm_compute; reflexivity | lia
  | first [ apply cstr_s_flags | apply cstr_s_qual | apply cstr_s_ccss | apply cstr_s_cs | apply cstr_s_csb | apply cstr_s_ss
          | apply cstr_s_flt | apply cstr_s_dioux ]; assumption
  | assumption | ];
  match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.

(* [comment removed for export] *)
Definition pcd_post (q p ap : Z) (gp tp s0 s2 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 ap)
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1b09bc) fc None m' (seg_rom asegs)
    /\ munch [(q + -2320, q + -2240); (q + -2216, q + -2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -2240)
    /\ (exists junk, rw_cells asegs m' (q + -2216) [CB 40 junk]).

Lemma pcom_dint_spec : forall (q p ap c nx lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 134383 ->
  s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
  (c = 100 \/ c = 117) -> 0 < nx < 256 ->
  bytes_at asegs m p (zb8 [37; c; nx]) -> rw_cells asegs m (q + -2216) DIR0 ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> p + 3 <= lo -> q <= 2^47 -> 0 <= ap < 2^63 ->
  mem_inv asegs m ->
  evt asegs (pcd_post q (p + 2) (ap + 8) gp tp s0 s2 s4 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b09e8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros -> -> -> -> -> -> -> -> -> -> CC NX BY DIR ST LO PLO QH AP MI.
  apply dir0_split in DIR. unfold DIRS in DIR. cbn [repeat] in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map] in PB.
  unfold zb8 in BY. cbn [map] in BY.
  pose proof (bytes_at_nth1 asegs m p _ 0 _ BY eq_refl) as B0. pose proof (bytes_at_nth1 asegs m p _ 1 _ BY eq_refl) as B1.
  pose proof (bytes_at_nth1 asegs m p _ 2 _ BY eq_refl) as B2. clear BY.
  change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. rewrite Z.add_0_r in B0.
  apply ro_C1_of_bytes in B0. apply ro_C1_of_bytes in B1. apply ro_C1_of_bytes in B2.
  pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 8 nx) = nx) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
  destruct CC as [-> | ->].
  zhide.
  all: xsteps_to 0x1d4f40%Z.
  all: strchr_call.
  all: xsteps_to 0x1d4f40%Z.
  all: strchr_call.
  all: xsteps_to 0x1d4f40%Z.
  all: strchr_call.
  all: xsteps_to 0x1b782c%Z.
  all: call fgvs_int_spec;
    [ reflexivity | reflexivity | reflexivity | first [left; reflexivity | right; reflexivity]
    | eapply (cells_byte _ _ _ 34%nat z8); [exact DIR | reflexivity | lia] | rewrite EUs; lia | rewrite EUs; exact ST | rewrite EUs; lia | rewrite EUs; lia
    | assumption | ].
  all: xsteps_to 0x1d4f40%Z.
  all: strchr_call.
  all: xsteps_to 0x1b09bc%Z.
  all: brF K.
  all: rewrite EUs in POST.
  all: apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
  all: apply evt_done; unfold pcd_post; do 19 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact POST| eexists; exact DIR].
Qed.
