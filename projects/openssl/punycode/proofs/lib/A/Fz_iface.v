(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface Fz_defs.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit AShadow ARt ACode ARtIc AIface AFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Section Iface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition no_cls0 (frs : list (Z * nat)) : Prop := forall f k, In (f, k) frs -> k <> 0%nat.

(* [comment removed for export] *)
Definition liba_rt (m : mem) (fs T ctx thr : Z) : Prop :=
  ARt.rt_ok m /\ ARtIc.ic_ok m /\ AFakeStack.fsrt_ok m fs T ctx thr /\ AFakeStack.fsrt_wf fs T ctx thr /\ AIface.uar_on m
  /\ AIface.fs_wf fs.

(* [comment removed for export] *)
Definition dom_cell (Σ : rts RT) (fs c len : Z) : Prop :=
  c + len <= rt_sp0 RT Σ - STACK_WIN
  /\ (c + len <= fs \/ fs + AIface.FS_SIZE <= c) /\ (c + len <= AShadow.SB \/ AShadow.HIMEM_BEG <= c).

(* [comment removed for export] *)
Definition ring_geo (Σ : rts RT) (fs T ctx thr : Z) : Prop :=
  fs + AIface.FS_SIZE <= rt_sp0 RT Σ - STACK_WIN
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> p + n <= fs \/ fs + AIface.FS_SIZE <= p)
  /\ (forall f k, In (f, k) (rt_frames RT Σ) -> k <> 0%nat -> fs + 1085440 <= f /\ f + fs_size k <= fs + AIface.FS_SIZE)
  /\ dom_cell Σ fs (T + 24) 8 /\ dom_cell Σ fs (ctx + 152) 8 /\ dom_cell Σ fs (thr + 48) 16.

(* [comment removed for export] *)
Definition same_off (Σ : rts RT) (sp : Z) (X : word -> Prop) (m m' : mem) : Prop :=
  forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> ~ X a -> m' a = m a.

Record ring0_facts : Prop := mkR0 {
  (* [comment removed for export] *)
  r0_view : forall Σ m, ART RT Σ m -> mem_inv asegs m -> no_cls0 (rt_frames RT Σ) ->
    exists fs T ctx thr h,
      liba_rt m fs T ctx thr /\ ring_geo Σ fs T ctx thr
      /\ 0 <= h < 2^64 /\ LibKit.cell ACode.ASEGS m fs 8 (W h) /\ AShadow.zeros m (fs + 4096) 16384 /\ AIface.ring_wr m fs
      (* [comment removed for export] *)
      /\ (forall x : word, AIface.ring_FP fs x ->
            ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (rt_sp0 RT Σ - STACK_WIN) (bv_unsigned x))
      (* [comment removed for export] *)
      /\ (forall m' sp, rt_sp0 RT Σ - STACK_WIN <= sp -> same_off Σ sp (AIface.ring_FP fs) m m' -> StoreOk.mem_grows m m' ->
            (exists h', 0 <= h' < 2^64 /\ LibKit.cell ACode.ASEGS m' fs 8 (W h')) -> AShadow.zeros m' (fs + 4096) 16384 ->
            ART RT Σ m')
      (* [comment removed for export] *)
      /\ (forall m' sp, rt_sp0 RT Σ - STACK_WIN <= sp -> (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
            same_off Σ sp (AIface.ring_FP fs) m m' -> StoreOk.mem_grows m m' ->
            let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
            LibKit.cell ACode.ASEGS m' fs 8 (W (h + 1)) -> LibKit.cell ACode.ASEGS m' (fs + 4096 + k) 1 (W 1) ->
            AShadow.zeros m' (fs + 4096) k -> AShadow.zeros m' (fs + 4096 + k + 1) (16383 - k) ->
            LibKit.cell ACode.ASEGS m' (FB + 56) 8 (W (fs + 4096 + k)) ->
            exists Σ', ART RT Σ' m' /\ rt_frames RT Σ' = (FB, 0%nat) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ
              /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ
              /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo));
  (* [comment removed for export] *)
  r0_view1 : forall Σ m FB fr, ART RT Σ m -> rt_frames RT Σ = (FB, 0%nat) :: fr -> no_cls0 fr ->
    exists fs k,
      AIface.fs_wf fs /\ 0 <= k < 16384 /\ FB = fs + 36864 + 64 * k
      /\ fs + AIface.FS_SIZE <= rt_sp0 RT Σ - STACK_WIN
      /\ (forall f j, In (f, j) fr -> fs + 1085440 <= f /\ f + fs_size j <= fs + AIface.FS_SIZE)
      /\ (forall p n, In (p, n) (rt_live RT Σ) -> p + n <= fs \/ fs + AIface.FS_SIZE <= p)
      /\ LibKit.cell ACode.ASEGS m (FB + 56) 8 (W (fs + 4096 + k))
      /\ AShadow.zeros m (fs + 4096) k /\ AShadow.zeros m (fs + 4096 + k + 1) (16383 - k)
      /\ LibKit.wr_ok ACode.ASEGS m FB 8 /\ LibKit.wr_ok ACode.ASEGS m (AShadow.sha FB) 8
      /\ LibKit.wr_ok ACode.ASEGS m (fs + 4096 + k) 1
      /\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (rt_sp0 RT Σ - STACK_WIN) (fs + 4096 + k)
      (* [comment removed for export] *)
      /\ (forall m' sp, rt_sp0 RT Σ - STACK_WIN <= sp -> same_off Σ sp (fun a => LibKit.inr a (fs + 4096 + k) 1) m m' ->
            StoreOk.mem_grows m m' -> AShadow.zeros m' (fs + 4096) 16384 ->
            exists Σ', ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
              /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo));
  (* [comment removed for export] *)
  r0_live_mem : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    AShadow.memrange p (n + 8) /\ (0 < n -> AShadow.shw_ok m p n);
  (* [comment removed for export] *)
  r0_xn_shadow : forall Σ m, ART RT Σ m -> stk asegs m 0x80010f08 0x80010f10
}.

End Iface.
