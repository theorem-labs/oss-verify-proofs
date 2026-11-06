(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.B Require Export X_gdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.B Require Export X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition XENV_FPA : list (Z * Z) :=
  [(0xbd6648, 0xbd664c); (0xbf6740, 0xbf6770); (0xbf6860, 0xbf6870); (0xbf6960, 0xbf6964); (0xbf6980, 0xbf6988);
   (0xbf6de8, 0xbf6df0); (0x5e2d90, 0x5e2d98); (0x5e2f70, 0x5e2f78); (0x5e2d98, 0x5e2e88); (0x5e2fa0, 0x69bc88); (0x69bcd0, 0x69bcd1);
   (ODR_LO, ODR_HI); (0xbd19e0, 0xbd19e1); (0xbd1994, 0xbd1995)].

Definition XENVA (k : bool) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0xbd6648 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ (exists (fin : byte) (p1 p2 : list byte), AXA k fin p1 p2 m)                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m AX_INCB [C1 (Z_to_bv 8 0)]                                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbf6960 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0xbf6980 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbf6de8 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e2d90 [C8 (Z_to_bv 64 0x5e2ca8)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e2f70 [C8 (Z_to_bv 64 0x5e2e88)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells bsegs m 0x5e2e80 [C8 (Z_to_bv 64 0x5e2d98)]                           (* [comment removed for export] *)
  /\ gtab_at m                                                                                   (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x69bc80 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x69bcd0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ stk bsegs m ODR_LO ODR_HI                                                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbd19e0 [C1 (Z_to_bv 8 0)].                 (* [comment removed for export] *)

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma XENV_locA : forall k, fp_local XENV_FPA (XENVA k).
Proof.
  intros k m m' (TID & ATX & INCB & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbd6648 0xbd664c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (f & p1 & p2 & C1' & C2'); exists f, p1, p2; split;
          [apply (R 0xbf6740 0xbf6770); [cbn; tauto| lia| | exact C1']; unfold ax_cells; cbn [cells_size csize]; lia
          |apply (R 0xbf6860 0xbf6870); [cbn; tauto| lia| cbn; lia| exact C2']]|].
  split; [apply (R 0xbd1994 0xbd1995); [cbn; tauto| unfold AX_INCB; lia| cbn; unfold AX_INCB; lia| exact INCB]|].
  split; [apply (R 0xbf6960 0xbf6964); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbf6980 0xbf6988); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbf6de8 0xbf6df0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5e2d90 0x5e2d98); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5e2f70 0x5e2f78); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e2d98 0x5e2e88); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e2d98 0x5e2e88); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA 0x5e2fa0 0x69bc88); [cbn; tauto|];
          unfold GT_LO, GT_HI in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5e2fa0 0x69bc88); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x69bcd0 0x69bcd1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split.
  - apply (stk_agree_nw bsegs m m' _ _ ODR). intros a Ha. apply AG. apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha].
  - apply (R 0xbd19e0 0xbd19e1); [cbn; tauto| lia| cbn; lia| exact BI].
Qed.

(* [comment removed for export] *)
Lemma XENVA_ax : forall k m, XENVA k m -> exists fin p1 p2, AXA k fin p1 p2 m.
Proof. intros k m (_ & H & _). exact H. Qed.

Lemma XENVA_libc : forall k m, XENVA k m ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells bsegs m 0xbf6980 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros k m (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma XENVA_incb : forall k m, XENVA k m -> rw_cells bsegs m AX_INCB [C1 (Z_to_bv 8 0)].
Proof. intros k m (_ & _ & H & _). exact H. Qed.

Lemma XENVA_repack : forall k k' m m', XENVA k m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbf6740 <= x < 0xbf6770) /\ ~ (0xbf6860 <= x < 0xbf6870) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA k' fin p1 p2 m') ->
  rw_cells bsegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA k' m'.
Proof.
  intros k k' m m' (TID & _ & _ & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & BI) AG ATX' INCB'.
  unfold AX_INCB in AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            (hi <= 0xbf6740 \/ 0xbf6770 <= lo) -> (hi <= 0xbf6860 \/ 0xbf6870 <= lo) -> (hi <= 0xbd1994 \/ 0xbd1995 <= lo) ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 D1 D2 D3 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. split; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbd6648 0xbd664c); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact INCB'|].
  split; [apply (R 0xbf6960 0xbf6964); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbf6980 0xbf6988); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]|].
  split; [apply (R 0xbf6de8 0xbf6df0); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact OFL]|].
  split; [apply (R 0x5e2d90 0x5e2d98); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SEU]|].
  split; [apply (R 0x5e2f70 0x5e2f78); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e2d98 0x5e2e88); [cbn; tauto| lia| | lia| lia| lia| exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e2d98 0x5e2e88); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact SINU]|].
  split; [apply (gtab_at_agree m m' GDS); intros a Ha; apply AG; unfold GT_LO, GT_HI in Ha;
          split; [apply (in_XENV_FPA 0x5e2fa0 0x69bc88); [cbn; tauto| lia]| lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x5e2fa0 0x69bc88); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact C]]|].
  split; [apply (R 0x69bcd0 0x69bcd1); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact CPL]|].
  split.
  - apply (stk_agree_nw bsegs m m' _ _ ODR). intros a Ha. apply AG.
    split; [apply (in_XENV_FPA ODR_LO ODR_HI); [cbn; tauto| exact Ha]| lia].
  - apply (R 0xbd19e0 0xbd19e1); [cbn; tauto| lia| cbn; lia| lia| lia| lia| exact BI].
Qed.

Lemma XENVA_upd : forall k m m', XENVA k m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbf6740 <= x < 0xbf6770) /\ ~ (0xbf6860 <= x < 0xbf6870) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA k fin p1 p2 m') ->
  rw_cells bsegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA k m'.
Proof. intros k m m'. apply XENVA_repack. Qed.

Lemma XENVA_step : forall m m', XENVA false m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbf6740 <= x < 0xbf6770) /\ ~ (0xbf6860 <= x < 0xbf6870) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA true fin p1 p2 m') ->
  rw_cells bsegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
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
  match find_segment bsegs z 1 with
  | Some s => (seg_writable s && seg_readable s &&
               match segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s))) with Some _ => true | None => false end)%bool
  | None => false
  end.
Lemma seg_rw1_b9f000 : seg_rw1 0xbd19c0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw1_sound : forall m z, 0 <= z < 2 ^ 64 -> seg_rw1 z = true ->
  wview bsegs m (wa z) <> None /\ exists b, mrd bsegs m (wa z) = Some b.
Proof.
  intros m z Hz H. unfold seg_rw1 in H.
  destruct (find_segment bsegs z 1) as [s|] eqn:F; [|discriminate].
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [Hw Hr].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) as [bb|] eqn:Hby; [|discriminate].
  assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; exact Hz).
  unfold wview, mrd. destruct (m (wa z)) as [b0|].
  - split; [discriminate| exists b0; reflexivity].
  - match goal with |- context [find_segment bsegs ?x 1] => assert (Ex : x = z) by exact Hu; rewrite Ex end.
    rewrite F, Hw, Hby. split; [discriminate|].
    exists bb. unfold OSSVerify.Proofs.openssl.pem.lib.Common.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
    match goal with |- context [find_segment bsegs ?x 1] => assert (Ex2 : x = z) by exact Hu; rewrite Ex2 end.
    rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hby. reflexivity.
Qed.
Lemma base_inited_any : forall m, exists b : byte, rw_cells bsegs m 0xbd19c0 [C1 b].
Proof.
  intros m. destruct (seg_rw1_sound m 0xbd19c0 ltac:(lia) seg_rw1_b9f000) as (W & b & R).
  exists b. split.
  - split; [exact (conj I I)|]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i; [| lia]. cbn [nth_error cells_bytes]. rewrite Z.add_0_r. exact R.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace (0xbd19c0 + i) with 0xbd19c0 by lia. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells bsegs m 0x566f58 [C8 (Z_to_bv 64 0x1eef1c); C8 (Z_to_bv 64 0x194a94); C8 (Z_to_bv 64 0x1ee498)]
                                                     (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5de7d0 [C8 (Z_to_bv 64 0x566f70); C8 (Z_to_bv 64 0x566f58)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5dc808 [C8 (Z_to_bv 64 0x553640); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells bsegs m 0x5df840 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5de788 [C8 (Z_to_bv 64 0x5e2fa0); C8 (Z_to_bv 64 0x69bc60)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5dc818 [C8 (Z_to_bv 64 0x72ede0)]                           (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5dc828 [C8 (Z_to_bv 64 0x730e68); C8 (Z_to_bv 64 0x69cb38); C8 (Z_to_bv 64 0x69f338);
                               C8 (Z_to_bv 64 0x6a0028); C8 (Z_to_bv 64 0x6a0030); C8 (Z_to_bv 64 0x6a0020);
                               C8 (Z_to_bv 64 0x5dfa70)]                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x69cb50 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x69cbf0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x69f338 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x6a0018 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x69eb9c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x730ee0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5dfa70 [C8 (Z_to_bv 64 0x55f010)]                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x7311e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk bsegs m SHW_LO SHW_HI.                                                  (* [comment removed for export] *)
