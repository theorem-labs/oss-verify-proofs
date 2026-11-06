(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.A Require Export X_gdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.punycode.lib.A Require Export X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition XENV_FPA : list (Z * Z) :=
  [(0xba7e28, 0xba7e2c); (0xbc7f20, 0xbc7f50); (0xbc8040, 0xbc8050); (0xbc8140, 0xbc8144); (0xbc8160, 0xbc8168);
   (0xbc85c8, 0xbc85d0); (0x5ae830, 0x5ae838); (0x5aea10, 0x5aea18); (0x5ae838, 0x5ae928); (0x5aea40, 0x66d488); (0x66d4d0, 0x66d4d1);
   (ODR_LO, ODR_HI); (0xba3660, 0xba3661); (0xba3190, 0xba3191); (0xba3194, 0xba3195)].

Definition XENVA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0xba7e28 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ (exists (k : bool) (fin : byte) (p1 p2 : list byte), AXA k fin p1 p2 m)                       (* [comment removed for export] *)
  /\ rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)]                                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xbc8140 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0xbc8160 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0xbc85c8 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5ae830 [C8 (Z_to_bv 64 0x5ae748)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5aea10 [C8 (Z_to_bv 64 0x5ae928)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0x5ae920 [C8 (Z_to_bv 64 0x5ae838)]                           (* [comment removed for export] *)
  /\ gtab_at m                                                                                   (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x66d480 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66d4d0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ stk asegs m ODR_LO ODR_HI                                                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xba3660 [C1 (Z_to_bv 8 0)].                                               (* [comment removed for export] *)

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof.
  intros m m' (TID & ATX & INCB & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba7e28 0xba7e2c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (k & f & p1 & p2 & C1' & C2' & C3'); exists k, f, p1, p2; split; [| split];
          [apply (R 0xbc7f20 0xbc7f50); [cbn; tauto| lia| | exact C1']; unfold ax_cells; cbn [cells_size csize]; lia
          |apply (R 0xbc8040 0xbc8050); [cbn; tauto| lia| cbn; lia| exact C2']
          |apply (R 0xba3190 0xba3191); [cbn; tauto| unfold AX_LATCH; lia| cbn; unfold AX_LATCH; lia| exact C3']]|].
  split; [apply (R 0xba3194 0xba3195); [cbn; tauto| unfold AX_INCB; lia| cbn; unfold AX_INCB; lia| exact INCB]|].
  split; [apply (R 0xbc8140 0xbc8144); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc8160 0xbc8168); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbc85c8 0xbc85d0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5ae830 0x5ae838); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5aea10 0x5aea18); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5ae838 0x5ae928); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5ae838 0x5ae928); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA 0x5aea40 0x66d488); [cbn; tauto|];
          unfold GT_LO, GT_HI in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5aea40 0x66d488); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x66d4d0 0x66d4d1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split.
  - apply (stk_agree_nw asegs m m' _ _ ODR). intros a Ha. apply AG. apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha].
  - apply (R 0xba3660 0xba3661); [cbn; tauto| lia| cbn; lia| exact BI].
Qed.

(* [comment removed for export] *)
Lemma XENVA_ax : forall m, XENVA m -> exists k fin p1 p2, AXA k fin p1 p2 m.
Proof. intros m (_ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma XENVA_libc : forall m, XENVA m ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0xbc8160 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros m (_ & _ & _ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma XENVA_incb : forall m, XENVA m -> rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)].
Proof. intros m (_ & _ & H & _). exact H. Qed.

Lemma XENVA_upd : forall m m', XENVA m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbc7f20 <= x < 0xbc7f50) /\ ~ (0xbc8040 <= x < 0xbc8050) /\ x <> AX_LATCH /\ x <> AX_INCB) m m' ->
  (exists k fin p1 p2, AXA k fin p1 p2 m') ->
  rw_cells asegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA m'.
Proof.
  intros m m' (TID & _ & _ & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG ATX' INCB'.
  unfold AX_LATCH, AX_INCB in AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            (hi <= 0xbc7f20 \/ 0xbc7f50 <= lo) -> (hi <= 0xbc8040 \/ 0xbc8050 <= lo) -> (hi <= 0xba3190 \/ 0xba3195 <= lo) ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 D1 D2 D3 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. split; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba7e28 0xba7e2c); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact INCB'|].
  split; [apply (R 0xbc8140 0xbc8144); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc8160 0xbc8168); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]|].
  split; [apply (R 0xbc85c8 0xbc85d0); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact OFL]|].
  split; [apply (R 0x5ae830 0x5ae838); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SEU]|].
  split; [apply (R 0x5aea10 0x5aea18); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5ae838 0x5ae928); [cbn; tauto| lia| | lia| lia| lia| exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5ae838 0x5ae928); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; unfold GT_LO, GT_HI in Ha;
          split; [apply (in_XENV_FPA 0x5aea40 0x66d488); [cbn; tauto| lia]| lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5aea40 0x66d488); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [apply (R 0x66d4d0 0x66d4d1); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact CPL]|].
  split.
  - apply (stk_agree_nw asegs m m' _ _ ODR). intros a Ha. apply AG.
    split; [apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha]| lia].
  - apply (R 0xba3660 0xba3661); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact BI].
Qed.
(* [comment removed for export] *)

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.   (* [comment removed for export] *)
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells asegs m 0x532838 [C8 (Z_to_bv 64 0x1f3428); C8 (Z_to_bv 64 0x199b38); C8 (Z_to_bv 64 0x20b954)]
                                                     (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5aa530 [C8 (Z_to_bv 64 0x532850); C8 (Z_to_bv 64 0x532838)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a8568 [C8 (Z_to_bv 64 0x51ef1c); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0x5ab5a0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5aa4e8 [C8 (Z_to_bv 64 0x5aea40); C8 (Z_to_bv 64 0x66d480)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a8578 [C8 (Z_to_bv 64 0x7005e0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a8588 [C8 (Z_to_bv 64 0x702668); C8 (Z_to_bv 64 0x66e338); C8 (Z_to_bv 64 0x670b38);
                               C8 (Z_to_bv 64 0x671828); C8 (Z_to_bv 64 0x671830); C8 (Z_to_bv 64 0x671820);
                               C8 (Z_to_bv 64 0x5ab7d0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66e350 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66e3f0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x670b38 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x671818 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x67039c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x7026e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5ab7d0 [C8 (Z_to_bv 64 0x52a8ec)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x7029e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m SHW_LO SHW_HI.                                                  (* [comment removed for export] *)
