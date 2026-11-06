(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC.
Open Scope Z_scope.

Module LXSEM.

Definition w64 (z : Z) : word := Z_to_bv 64 z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmp_holds (rho : valuation) (k : cmpk) (a b : lin) : bool :=
  match k with
  | CK_LTU | CK_LT => Z.ltb (evl rho a) (evl rho b)
  | CK_EQ => Z.eqb ((evl rho a) mod two64z) ((evl rho b) mod two64z)
  end.

Definition val_ok (rho : valuation) (v : aval) (w : word) : Prop :=
  match v with
  | Top => True
  | LV l => w = w64 (evl rho l)
  | CV neg k a b => w = w64 (if xorb neg (cmp_holds rho k a b) then 1 else 0)
  | XV a b => w = bv_xor (w64 (evl rho a)) (w64 (evl rho b))
  end.

Lemma val_ok_top : forall rho w, val_ok rho Top w.
Proof. intros; exact I. Qed.

(* [comment removed for export] *)
Definition val_bytes_ok (rho : valuation) (v : aval) (w : Z) (bs : list byte) : Prop :=
  Z.of_nat (length bs) = w /\
  match v with
  | Top => True
  | LV l => bytes_le_to_Z bs = (evl rho l) mod 2 ^ (8 * w)
  | CV neg k a b => bytes_le_to_Z bs = (if xorb neg (cmp_holds rho k a b) then 1 else 0) mod 2 ^ (8 * w)
  | XV a b => bytes_le_to_Z bs = bv_unsigned (bv_xor (w64 (evl rho a)) (w64 (evl rho b))) mod 2 ^ (8 * w)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regs_ok (rho : valuation) (ars : list aval) (regs : bvmap 5 word) : Prop :=
  forall r : nat, (1 <= r < 32)%nat -> val_ok rho (list_get ars r Top) (reg_get regs (Z_to_bv 5 (Z.of_nat r))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
  Variable U : uenv.
  Let segs := ue_segs U.

  (* [comment removed for export] *)
  Definition rd1 (mem : word -> option byte) (a : Z) : option byte :=
    match rdn segs mem (w64 a) 1 with Some [b] => Some b | _ => None end.

  Definition stack_cell_ok (rho : valuation) (mem : word -> option byte) (sp0 : Z) (c : cell) : Prop :=
    - ue_fr U <= c_off c /\ c_off c + c_w c <= 0 /\ 0 < c_w c /\
    exists bs, rdn segs mem (w64 (sp0 + c_off c)) (Z.to_nat (c_w c)) = Some bs /\ val_bytes_ok rho (c_val c) (c_w c) bs.

  (* [comment removed for export] *)
  Definition afact_ok (rho : valuation) (mem : word -> option byte) (sp0 : Z) (lo hi : Z) (f : afact) : Prop :=
    (forall j, 0 <= j < evl rho (af_len f) ->
      lo + j < hi /\ exists b, rd1 mem (sp0 + lo + j) = Some b /\ af_blo f <= bv_unsigned b <= af_bhi f)
    /\ (1 <= evl rho (af_len f) -> exists b, rd1 mem (sp0 + lo) = Some b /\ in_itv (bv_unsigned b) (af_first f)).

  Definition arr_ok (rho : valuation) (mem : word -> option byte) (sp0 : Z) (a : arr) : Prop :=
    - ue_fr U <= ar_lo a /\ ar_hi a <= 0 /\
    match ar_fact a with Some f => 0 <= af_blo f /\ af_bhi f <= 127 /\ afact_ok rho mem sp0 (ar_lo a) (ar_hi a) f | None => True end.

  (* [comment removed for export] *)
  Definition window_ok (mem : word -> option byte) (sp0 : Z) : Prop :=
    (forall a, sp0 - ue_fr U <= a < sp0 -> exists b, mem (w64 a) = Some b) /\
    (forall a, sp0 - ue_fr U <= a < sp0 -> find_segment segs a 1 = None).

  (* [comment removed for export] *)
  Definition payload_ok (rho : valuation) (mem : word -> option byte) (pcache : list (lin * Z * sym)) (pay : list (lin * itv)) : Prop :=
    (forall i, 0 <= i < rho SYM_N -> exists b, rd1 mem (rho SYM_DATA + i) = Some b) /\
    (rho SYM_DATA + rho SYM_N <= rho SYM_SP0 - ue_fr U \/ rho SYM_SP0 <= rho SYM_DATA) /\
    (forall off sx x, In (off, sx, x) pcache ->
       0 <= evl rho off < rho SYM_N /\
       exists b, rd1 mem (rho SYM_DATA + evl rho off) = Some b /\
                 rho x = (if Z.eqb sx 1 then bv_signed b else bv_unsigned b)) /\
    (forall off i, In (off, i) pay ->
       0 <= evl rho off < rho SYM_N /\
       exists b, rd1 mem (rho SYM_DATA + evl rho off) = Some b /\ in_itv (bv_unsigned b) i).

  (* [comment removed for export] *)
  Definition in_rangesZ (a : Z) (rs : list (Z * Z)) : Prop := exists r, In r rs /\ fst r <= a < snd r.
  Definition abs_ok (mem : word -> option byte) (bm : list (Z * Z)) : Prop :=
    (forall a b, bm_get bm a = Some b -> in_rangesZ a (ue_rw U) /\ 0 <= b < 256 /\ mem (w64 a) = Some (Z_to_bv 8 b)) /\
    (forall a, in_rangesZ a (ue_rw U) -> bm_get bm a = None -> mem (w64 a) = None) /\
    (forall a b, in_rangesZ a (ue_ro U) -> mem (w64 a) = Some b -> memory_read segs (w64 a) 1%N = Some [b]).

  (* [comment removed for export] *)
  Record uenv_ok : Prop := UenvOk {
    uo_rw_w : forall a m, in_rangesZ a (ue_rw U) -> store_ok segs m (w64 a) 1 = true;       (* [comment removed for export] *)
    uo_rw_r : forall a, in_rangesZ a (ue_rw U) -> exists b, memory_read segs (w64 a) 1%N = Some [b];
    uo_small : forall a, (in_rangesZ a (ue_rw U) \/ in_rangesZ a (ue_ro U)) -> 0 <= a < 2 ^ 32;
    uo_disj : forall a, in_rangesZ a (ue_rw U) -> ~ in_rangesZ a (ue_ro U);
    uo_fr : 0 <= ue_fr U;
    uo_tabs : tables_validb U = true;                                                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    uo_scells : forall a x, In (a, x) (ue_scells U) ->
                  x = SYM_SC0 /\ 0 <= a /\ a + 8 <= 2 ^ 32 /\ (forall i, 0 <= i < 8 -> ~ in_rangesZ (a + i) (ue_rw U))
  }.

  (* [comment removed for export] *)
  Definition scells_ok (G : sym -> Z) (M0 : word -> option byte) : Prop :=
    forall a x, In (a, x) (ue_scells U) ->
      exists bs, rdn segs M0 (w64 a) 8 = Some bs /\ (bytes_le_to_Z bs) mod 2 ^ 64 = (G x) mod 2 ^ 64.

  Definition resv_ok (r : option Z) (cr : option word) : Prop :=
    match r, cr with
    | None, None => True
    | Some a, Some w => w = w64 a /\ 0 <= a < two64z
    | _, _ => False
    end.

  (* [comment removed for export] *)
  Definition frame_ok (M0 mem : word -> option byte) (sp0 : Z) : Prop :=
    (forall a : word, ~ (sp0 - ue_fr U <= bv_unsigned a < sp0) -> ~ in_rangesZ (bv_unsigned a) (ue_rw U) -> mem a = M0 a) /\
    (forall (a : word) b, M0 a = Some b -> exists b', mem a = Some b').
End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frm_ok (fcsr : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fcsr) 5) 7 = 0.

Record R (U : uenv) (G : sym -> Z) (M0 : word -> option byte) (rho : valuation) (st : astate) (ms : machine_state) : Prop := MkR {
  r_glob  : forall x, (x < NGLOB)%nat -> rho x = G x;
  r_pc    : ms_pc_val ms = w64 (s_pc st);
  r_svc   : ms_svc_pending ms = None;
  r_regs  : regs_ok rho (s_regs st) (ms_regs ms);
  r_vs    : ctx_ok rho (s_ctx st) /\ ctx_below (s_ctx st) (s_next st) = true;
  r_stk   : Forall (stack_cell_ok U rho (ms_mem ms) (rho SYM_SP0)) (s_stk st);
  r_arrs  : Forall (arr_ok U rho (ms_mem ms) (rho SYM_SP0)) (s_arrs st);
  r_win   : window_ok U (ms_mem ms) (rho SYM_SP0);
  r_pay   : payload_ok U rho (ms_mem ms) (s_pcache st) (s_pay st);
  r_abs   : abs_ok U (ms_mem ms) (s_abs st);
  r_resv  : resv_ok (s_resv st) (ms_resv ms);
  r_frm   : frm_ok (ms_fcsr ms);
  r_frame : frame_ok U M0 (ms_mem ms) (rho SYM_SP0);
  r_sp0   : 2 ^ 32 <= rho SYM_SP0 - ue_fr U /\ rho SYM_SP0 < 2 ^ 62;
  r_align : rho SYM_SP0 mod 16 = 0 /\ rho SYM_DATA mod 16 = 0;
  r_ra    : 0 <= rho SYM_RA < 2 ^ 64 /\ rho SYM_RA mod 4 = 0;
  r_data  : 0 <= rho SYM_DATA /\ rho SYM_DATA + rho SYM_N < 2 ^ 62 /\ 0 <= rho SYM_N
}.

(* [comment removed for export] *)
Definition ms_with_mem (ms : machine_state) (m : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := m; ms_rom := ms_rom ms |}.
Definition ms_with_regs (ms : machine_state) (r : bvmap 5 word) : machine_state :=
  {| ms_regs := r; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Definition ms_with_pc (ms : machine_state) (p : word) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := p; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Definition ms_with_resv (ms : machine_state) (r : option word) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := r; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition agree (n : nat) (rho rho' : valuation) : Prop := forall x, (x < n)%nat -> rho' x = rho x.

Lemma agree_refl : forall n rho, agree n rho rho.
Proof. intros n rho x _; reflexivity. Qed.
Lemma agree_trans : forall n m rho1 rho2 rho3, (n <= m)%nat -> agree n rho1 rho2 -> agree m rho2 rho3 -> agree n rho1 rho3.
Proof. intros n m r1 r2 r3 Hle H1 H2 x Hx. rewrite H2 by lia. apply H1; exact Hx. Qed.

End LXSEM.
