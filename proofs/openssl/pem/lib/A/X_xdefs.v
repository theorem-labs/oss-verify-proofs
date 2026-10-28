(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Export X_gdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Export X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition XENV_FPA : list (Z * Z) :=
  [(0xba3e48, 0xba3e4c); (0xbc3f40, 0xbc3f70); (0xbc4060, 0xbc4070); (0xbc4160, 0xbc4164); (0xbc4180, 0xbc4188);
   (0xbc45e8, 0xbc45f0); (0x5aa850, 0x5aa858); (0x5aaa30, 0x5aaa38); (0x5aa858, 0x5aa948); (0x5aaa60, 0x669488); (0x6694d0, 0x6694d1);
   (ODR_LO, ODR_HI); (0xb9f1e0, 0xb9f1e1); (0xb9f194, 0xb9f195)].

Definition XENVA (k : bool) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0xba3e48 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ (exists (fin : byte) (p1 p2 : list byte), AXA k fin p1 p2 m)                                  (* [comment removed for export] *)
  /\ rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)]                                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xbc4160 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0xbc45e8 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5aa850 [C8 (Z_to_bv 64 0x5aa768)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5aaa30 [C8 (Z_to_bv 64 0x5aa948)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0x5aa940 [C8 (Z_to_bv 64 0x5aa858)]                           (* [comment removed for export] *)
  /\ gtab_at m                                                                                   (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x669480 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0x6694d0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ stk asegs m ODR_LO ODR_HI                                                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xb9f1e0 [C1 (Z_to_bv 8 0)].                 (* [comment removed for export] *)

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma XENV_locA : forall k, fp_local XENV_FPA (XENVA k).
Proof.
  intros k m m' (TID & ATX & INCB & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba3e48 0xba3e4c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (f & p1 & p2 & C1' & C2'); exists f, p1, p2; split;
          [apply (R 0xbc3f40 0xbc3f70); [cbn; tauto| lia| | exact C1']; unfold ax_cells; cbn [cells_size csize]; lia
          |apply (R 0xbc4060 0xbc4070); [cbn; tauto| lia| cbn; lia| exact C2']]|].
  split; [apply (R 0xb9f194 0xb9f195); [cbn; tauto| unfold AX_INCB; lia| cbn; unfold AX_INCB; lia| exact INCB]|].
  split; [apply (R 0xbc4160 0xbc4164); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc4180 0xbc4188); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbc45e8 0xbc45f0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5aa850 0x5aa858); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5aaa30 0x5aaa38); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5aa858 0x5aa948); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5aa858 0x5aa948); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA 0x5aaa60 0x669488); [cbn; tauto|];
          unfold GT_LO, GT_HI in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5aaa60 0x669488); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6694d0 0x6694d1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split.
  - apply (stk_agree_nw asegs m m' _ _ ODR). intros a Ha. apply AG. apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha].
  - apply (R 0xb9f1e0 0xb9f1e1); [cbn; tauto| lia| cbn; lia| exact BI].
Qed.

(* [comment removed for export] *)
Lemma XENVA_ax : forall k m, XENVA k m -> exists fin p1 p2, AXA k fin p1 p2 m.
Proof. intros k m (_ & H & _). exact H. Qed.

Lemma XENVA_libc : forall k m, XENVA k m ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros k m (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma XENVA_incb : forall k m, XENVA k m -> rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)].
Proof. intros k m (_ & _ & H & _). exact H. Qed.

Lemma XENVA_repack : forall k k' m m', XENVA k m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA k' fin p1 p2 m') ->
  rw_cells asegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA k' m'.
Proof.
  intros k k' m m' (TID & _ & _ & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG ATX' INCB'.
  unfold AX_INCB in AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            (hi <= 0xbc3f40 \/ 0xbc3f70 <= lo) -> (hi <= 0xbc4060 \/ 0xbc4070 <= lo) -> (hi <= 0xb9f194 \/ 0xb9f195 <= lo) ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 D1 D2 D3 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. split; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba3e48 0xba3e4c); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact INCB'|].
  split; [apply (R 0xbc4160 0xbc4164); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc4180 0xbc4188); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]|].
  split; [apply (R 0xbc45e8 0xbc45f0); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact OFL]|].
  split; [apply (R 0x5aa850 0x5aa858); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SEU]|].
  split; [apply (R 0x5aaa30 0x5aaa38); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5aa858 0x5aa948); [cbn; tauto| lia| | lia| lia| lia| exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5aa858 0x5aa948); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; unfold GT_LO, GT_HI in Ha;
          split; [apply (in_XENV_FPA 0x5aaa60 0x669488); [cbn; tauto| lia]| lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5aaa60 0x669488); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [apply (R 0x6694d0 0x6694d1); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact CPL]|].
  split.
  - apply (stk_agree_nw asegs m m' _ _ ODR). intros a Ha. apply AG.
    split; [apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha]| lia].
  - apply (R 0xb9f1e0 0xb9f1e1); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact BI].
Qed.

Lemma XENVA_upd : forall k m m', XENVA k m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA k fin p1 p2 m') ->
  rw_cells asegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA k m'.
Proof. intros k m m'. apply XENVA_repack. Qed.

Lemma XENVA_step : forall m m', XENVA false m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA true fin p1 p2 m') ->
  rw_cells asegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA true m'.
Proof. intros m m'. apply XENVA_repack. Qed.
(* [comment removed for export] *)

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rw1 (z : Z) : bool :=
  match find_segment asegs z 1 with
  | Some s => (seg_writable s && seg_readable s &&
               match segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s))) with Some _ => true | None => false end)%bool
  | None => false
  end.
Lemma seg_rw1_b9f000 : seg_rw1 0xb9f1c0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw1_sound : forall m z, 0 <= z < 2 ^ 64 -> seg_rw1 z = true ->
  wview asegs m (wa z) <> None /\ exists b, mrd asegs m (wa z) = Some b.
Proof.
  intros m z Hz H. unfold seg_rw1 in H.
  destruct (find_segment asegs z 1) as [s|] eqn:F; [|discriminate].
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [Hw Hr].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) as [bb|] eqn:Hby; [|discriminate].
  assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; exact Hz).
  unfold wview, mrd. destruct (m (wa z)) as [b0|].
  - split; [discriminate| exists b0; reflexivity].
  - match goal with |- context [find_segment asegs ?x 1] => assert (Ex : x = z) by exact Hu; rewrite Ex end.
    rewrite F, Hw, Hby. split; [discriminate|].
    exists bb. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Common.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
    match goal with |- context [find_segment asegs ?x 1] => assert (Ex2 : x = z) by exact Hu; rewrite Ex2 end.
    rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hby. reflexivity.
Qed.
Lemma base_inited_any : forall m, exists b : byte, rw_cells asegs m 0xb9f1c0 [C1 b].
Proof.
  intros m. destruct (seg_rw1_sound m 0xb9f1c0 ltac:(lia) seg_rw1_b9f000) as (W & b & R).
  exists b. split.
  - split; [exact (conj I I)|]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i; [| lia]. cbn [nth_error cells_bytes]. rewrite Z.add_0_r. exact R.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace (0xb9f1c0 + i) with 0xb9f1c0 by lia. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells asegs m 0x52e860 [C8 (Z_to_bv 64 0x1f34cc); C8 (Z_to_bv 64 0x199adc); C8 (Z_to_bv 64 0x1f34fc)]
                                                     (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a6548 [C8 (Z_to_bv 64 0x52e878); C8 (Z_to_bv 64 0x52e860)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a4588 [C8 (Z_to_bv 64 0x51af44); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0x5a75c0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a6500 [C8 (Z_to_bv 64 0x5aaa60); C8 (Z_to_bv 64 0x669460)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a45a8 [C8 (Z_to_bv 64 0x6fe668); C8 (Z_to_bv 64 0x66a338); C8 (Z_to_bv 64 0x66cb38);
                               C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820);
                               C8 (Z_to_bv 64 0x5a77f0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66a3f0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x6fe9e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m SHW_LO SHW_HI.                                                  (* [comment removed for export] *)
