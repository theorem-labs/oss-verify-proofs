(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_thread R_cache_defs R_prim_defs R_leaves R_rzlog R_depot_defs R_asan_defs R_allocate1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
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
Local Ltac zidle_begin sp n :=
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
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)

Ltac print_regs := let show k := (let e := getreg k in idtac k ":=" e) in
  show 8%Z; show 9%Z; show 10%Z; show 11%Z; show 12%Z; show 13%Z; show 18%Z; show 19%Z; show 20%Z; show 21%Z; show 24%Z; show 25%Z;
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc :=" pc end.

(* [comment removed for export] *)
Definition alloc_frame64_cf (cfw : word) (m : mem) (A : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells ctasegs m (A + 8) [C8 cfw; C8 (Z_to_bv 64 64); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                             C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition alloc_frame64 (m : mem) (A : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells ctasegs m (A + 8) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 64); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                             C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition PM_N : Z := 32768.
Definition PM_NEEDED : Z := 33856.

(* [comment removed for export] *)
Definition pmalloc_p1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 1) (Z_to_bv 64 PM_N) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
                  (Z_to_bv 64 PM_NEEDED) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 64) (Z_to_bv 64 PM_NEEDED)
                  (Z_to_bv 64 1024) (Z_to_bv 64 PM_N) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (-64))
                  (Z_to_bv 64 63) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
             F (Z_to_bv 64 0x1a057c) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ (exists j, rw_cells ctasegs m' (bv_unsigned sp + -128) [CB 8 j])
    /\ alloc_frame64 m' (bv_unsigned sp + -128) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk ctasegs m' lo (bv_unsigned sp + -128).

(* [comment removed for export] *)
Lemma pmalloc_p1_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B TCX T lo : Z),
  (0 < B < 2^63)%Z ->
  rw_cells ctasegs m g_asan_inited [C1 (Z_to_bv 8 1)] -> rw_cells ctasegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells ctasegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells ctasegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T < 2^63)%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (0xbcb000 <= lo)%Z -> (bv_unsigned sp <= 2^63)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (pmalloc_p1_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 PM_N) (Z_to_bv 64 64) (Z_to_bv 64 B)
             (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HB AI RS MX RZ TC HTCX HTCXl HT ST HLO HIMG HSP MI. unfold allocate_entry, PM_N.
  destruct TC as [(KI & K & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  unfold g_asan_inited, g_rss_limit_exceeded, INST, g_instance in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 120%nat ST. carve_frame 8%nat ST.
  zhide.
  zidle1 AI. zidle1 RS. zidle1 MX. zidle1 RZ. zidle1 KI. zidle1 K. zidle1 TS. zidle1 T0. zidle1 TT.
  do 21 zstep.
  zidle_end_m m.
  call (asan_inited_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep.
  call (rss_limit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try eassumption.
  zstep. ifF.
  zstep. ifF.
  ro_debruijn MI.
  zstep. zstep. ifT.
  do 3 zstep. ifT.
  do 3 zstep. ifF.
  do 9 zstep. fold_reg 11%Z.
  do 6 zstep. ifF.            (* [comment removed for export] *)
  do 4 zstep. ifF.            (* [comment removed for export] *)
  zstep. zstep. zstep; fix_lit_store. zstep; fix_lit_store.
  eapply rz_cascade; [lia|]. intros a0'.
  do 6 zstep.
  sp_facts.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 5 zstep.
  call (rzlog_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 7%Z lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  (* [comment removed for export] *)
  zstep. ifT. zstep. ifT. do 3 zstep. ifT.
  do 9 zstep.
  fold_reg 10%Z. fold_reg 24%Z. fold_reg 11%Z.
  zstep. ifF.
  do 15 zstep.
  fold_reg 9%Z. fold_reg 20%Z. fold_reg 19%Z. fold_reg 8%Z. fold_reg 12%Z. fold_reg 10%Z. fold_reg 13%Z.
  ifF. zstep. ifF.
  do 2 zstep. ifT.
  zstep.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [assumption| split; [assumption| split; assumption]]| assumption]. }
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  do 2 zstep. ifF.
  do 5 zstep.
  finish.
  - eexists. eassumption.
  - unfold alloc_frame64. replace (bv_unsigned sp + -128 + 8)%Z with (bv_unsigned sp + -120)%Z by lia. eassumption.
Qed.
