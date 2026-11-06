(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.A Require Export X_gdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.A Require Export X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition XENV_FPA : list (Z * Z) :=
  [(0xba3e48, 0xba3e4c); (0xbc3f40, 0xbc3f70); (0xbc4060, 0xbc4070); (0xb9f194, 0xb9f195); (0xbc4160, 0xbc4164);
   (0xbc4180, 0xbc4188); (0xbc45e8, 0xbc45f0); (0x5aa850, 0x5aa858); (0x5aaa30, 0x5aaa38); (0x5aa858, 0x5aa940);
   (0x5aa940, 0x5aa948); (0x5aaa60, 0x669460); (0x669480, 0x669488); (0x6694d0, 0x6694d1); (0xb9faa0, 0xba356d);
   (0xb9f1e0, 0xb9f1e1)].

Definition XENVA (k : bool) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0xba3e48 [C4 (Z_to_bv 64 tid)])
  /\ (exists fin p1 p2, AXA k fin p1 p2 m)
  /\ rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xbc4160 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells asegs m 0xbc45e8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x5aa850 [C8 (Z_to_bv 64 RSTDERR)]
  /\ rw_cells asegs m 0x5aaa30 [C8 (Z_to_bv 64 RSTDOUT)]
  /\ stdin_file m
  /\ rw_cells asegs m 0x5aa940 [C8 (Z_to_bv 64 RSTDIN)]
  /\ gtab_at m
  /\ (exists flag : word, bv_unsigned flag <> 0 /\ rw_cells asegs m 0x669480 [C8 flag])
  /\ rw_cells asegs m 0x6694d0 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m ODR_LO ODR_HI
  /\ rw_cells asegs m 0xb9f1e0 [C1 (Z_to_bv 8 0)].

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma XENV_locA : forall k, fp_local XENV_FPA (XENVA k).
Proof.
  intros k m m' Env Same.
  pose (covered := fun A B => existsb (fun r => (fst r <=? A) && (B <=? snd r)) XENV_FPA).
  assert (Win : forall A B, covered A B = true -> agree_on (fun x => A <= x < B) m m').
  { intros A B Cov a InAB. cbv beta in InAB. unfold covered in Cov. cbv beta in Cov.
    apply existsb_exists in Cov as ([lo hi] & Mem & Fit). cbn [fst snd] in Fit.
    apply Same. apply (in_XENV_FPA lo hi); [exact Mem | lia]. }
  assert (Carry : forall A cs, rw_cells asegs m A cs -> covered A (A + Z.of_nat (cells_size cs)) = true ->
                  rw_cells asegs m' A cs).
  { intros A cs Cells Ok. exact (rw_cells_agree_nw asegs m m' A cs Cells (Win _ _ Ok)). }
  destruct Env as ((tid & TidOk & TidAt) & (fin & p1 & p2 & AtxAt & AuxAt) & IncbAt & LockAt
                   & (cdt & thr & sec & tm1 & LibcAt) & OflAt & ErrPtrAt & OutPtrAt
                   & (j0 & j1 & j2 & j3 & j4 & InFileAt) & InPtrAt & GlobAt & (flag & RegNz & RegAt)
                   & DoneAt & OdrAt & ClosedAt).
  pose proof (Carry _ _ TidAt eq_refl) as TidNow.
  pose proof (Carry _ _ AtxAt eq_refl) as AtxNow.
  pose proof (Carry _ _ AuxAt eq_refl) as AuxNow.
  pose proof (Carry _ _ LockAt eq_refl) as LockNow.
  pose proof (Carry _ _ IncbAt eq_refl) as IncbNow.
  pose proof (Carry _ _ LibcAt eq_refl) as LibcNow.
  pose proof (Carry _ _ OflAt eq_refl) as OflNow.
  pose proof (Carry _ _ InPtrAt eq_refl) as InPtrNow.
  pose proof (Carry _ _ InFileAt eq_refl) as InFileNow.
  pose proof (Carry _ _ OutPtrAt eq_refl) as OutPtrNow.
  pose proof (Carry _ _ ErrPtrAt eq_refl) as ErrPtrNow.
  pose proof (gtab_at_agree m m' GlobAt (Win GT_LO GT_HI eq_refl)) as GlobNow.
  pose proof (Carry _ _ RegAt eq_refl) as RegNow.
  pose proof (Carry _ _ DoneAt eq_refl) as DoneNow.
  pose proof (stk_agree_nw asegs m m' ODR_LO ODR_HI OdrAt (Win ODR_LO ODR_HI eq_refl)) as OdrNow.
  pose proof (Carry _ _ ClosedAt eq_refl) as ClosedNow.
  exact (conj (ex_intro _ tid (conj TidOk TidNow))
        (conj (ex_intro _ fin (ex_intro _ p1 (ex_intro _ p2 (conj AtxNow AuxNow))))
        (conj IncbNow (conj LockNow
        (conj (ex_intro _ cdt (ex_intro _ thr (ex_intro _ sec (ex_intro _ tm1 LibcNow))))
        (conj OflNow (conj ErrPtrNow (conj OutPtrNow
        (conj (ex_intro _ j0 (ex_intro _ j1 (ex_intro _ j2 (ex_intro _ j3 (ex_intro _ j4 InFileNow)))))
        (conj InPtrNow (conj GlobNow
        (conj (ex_intro _ flag (conj RegNz RegNow))
        (conj DoneNow (conj OdrNow ClosedNow)))))))))))))).
Qed.

(* [comment removed for export] *)
Lemma XENVA_ax : forall k m, XENVA k m -> exists fin p1 p2, AXA k fin p1 p2 m.
Proof. intros k m (_ & H & _). exact H. Qed.

Lemma XENVA_libc : forall k m, XENVA k m ->
  exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof. intros k m (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma XENVA_incb : forall k m, XENVA k m -> rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)].
Proof. intros k m Env. exact (proj1 (proj2 (proj2 Env))). Qed.

Lemma XENVA_repack : forall k k' m m', XENVA k m ->
  agree_on (fun x => in_ranges XENV_FPA x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> AX_INCB) m m' ->
  (exists fin p1 p2, AXA k' fin p1 p2 m') ->
  rw_cells asegs m' AX_INCB [C1 (Z_to_bv 8 0)] ->
  XENVA k' m'.
Proof.
  intros k k' m m' Env Keep AxNow IncbNow.
  pose (apart := fun A B => existsb (fun r => (fst r <=? A) && (B <=? snd r)) XENV_FPA
                            && ((B <=? 0xbc3f40) || (0xbc3f70 <=? A)) && ((B <=? 0xbc4060) || (0xbc4070 <=? A))
                            && ((B <=? AX_INCB) || (AX_INCB <? A))).
  assert (Win : forall A B, apart A B = true -> agree_on (fun x => A <= x < B) m m').
  { intros A B Ok a InAB. cbv beta in InAB. unfold apart in Ok. cbv beta in Ok.
    apply andb_prop in Ok as [Ok AwayIncb]. apply andb_prop in Ok as [Ok AwayAux].
    apply andb_prop in Ok as [Cov AwayAtx].
    apply existsb_exists in Cov as ([lo hi] & Mem & Fit). cbn [fst snd] in Fit.
    apply Keep. unfold AX_INCB in *.
    split; [apply (in_XENV_FPA lo hi); [exact Mem | lia] | lia]. }
  assert (Carry : forall A cs, rw_cells asegs m A cs -> apart A (A + Z.of_nat (cells_size cs)) = true ->
                  rw_cells asegs m' A cs).
  { intros A cs Cells Ok. exact (rw_cells_agree_nw asegs m m' A cs Cells (Win _ _ Ok)). }
  destruct AxNow as (fin & p1 & p2 & AxCells).
  destruct Env as ((tid & TidOk & TidAt) & _ & _ & LockAt & (cdt & thr & sec & tm1 & LibcAt) & OflAt & ErrPtrAt
                   & OutPtrAt & (j0 & j1 & j2 & j3 & j4 & InFileAt) & InPtrAt & GlobAt & (flag & RegNz & RegAt)
                   & DoneAt & OdrAt & ClosedAt).
  pose proof (stk_agree_nw asegs m m' ODR_LO ODR_HI OdrAt (Win ODR_LO ODR_HI eq_refl)) as OdrNow.
  pose proof (gtab_at_agree m m' GlobAt (Win GT_LO GT_HI eq_refl)) as GlobNow.
  pose proof (Carry _ _ ClosedAt eq_refl) as ClosedNow.
  pose proof (Carry _ _ DoneAt eq_refl) as DoneNow.
  pose proof (Carry _ _ RegAt eq_refl) as RegNow.
  pose proof (Carry _ _ ErrPtrAt eq_refl) as ErrPtrNow.
  pose proof (Carry _ _ OutPtrAt eq_refl) as OutPtrNow.
  pose proof (Carry _ _ InFileAt eq_refl) as InFileNow.
  pose proof (Carry _ _ InPtrAt eq_refl) as InPtrNow.
  pose proof (Carry _ _ OflAt eq_refl) as OflNow.
  pose proof (Carry _ _ LibcAt eq_refl) as LibcNow.
  pose proof (Carry _ _ LockAt eq_refl) as LockNow.
  pose proof (Carry _ _ TidAt eq_refl) as TidNow.
  exact (conj (ex_intro _ tid (conj TidOk TidNow))
        (conj (ex_intro _ fin (ex_intro _ p1 (ex_intro _ p2 AxCells)))
        (conj IncbNow (conj LockNow
        (conj (ex_intro _ cdt (ex_intro _ thr (ex_intro _ sec (ex_intro _ tm1 LibcNow))))
        (conj OflNow (conj ErrPtrNow (conj OutPtrNow
        (conj (ex_intro _ j0 (ex_intro _ j1 (ex_intro _ j2 (ex_intro _ j3 (ex_intro _ j4 InFileNow)))))
        (conj InPtrNow (conj GlobNow
        (conj (ex_intro _ flag (conj RegNz RegNow))
        (conj DoneNow (conj OdrNow ClosedNow)))))))))))))).
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
  match wview asegs (fun _ => None) (wa z), seg_rom asegs (wa z) with
  | Some _, Some _ => true
  | _, _ => false
  end.
Lemma seg_rw1_b9f000 : seg_rw1 0xb9f1c0 = true.
Proof. exact (eq_refl true <: seg_rw1 0xb9f1c0 = true). Qed.
Lemma seg_rw1_sound : forall m z, 0 <= z < 2 ^ 64 -> seg_rw1 z = true ->
  wview asegs m (wa z) <> None /\ exists b, mrd asegs m (wa z) = Some b.
Proof.
  intros m z _. unfold seg_rw1.
  destruct (wview asegs (fun _ => None) (wa z)) as [w0|] eqn:Bare; [|intros Bad; discriminate Bad].
  destruct (seg_rom asegs (wa z)) as [r0|] eqn:Img; [|intros Bad; discriminate Bad].
  intros _.
  destruct (m (wa z)) as [cur|] eqn:Cur.
  - unfold wview, mrd. rewrite Cur. split; [discriminate | exists cur; reflexivity].
  - assert (ViewEq : wview asegs m (wa z) = wview asegs (fun _ => None) (wa z))
      by (unfold wview; rewrite Cur; reflexivity).
    split.
    + rewrite ViewEq, Bare. discriminate.
    + exists r0. unfold mrd. rewrite Cur. exact Img.
Qed.
Lemma base_inited_any : forall m, exists b : byte, rw_cells asegs m 0xb9f1c0 [C1 b].
Proof.
  intros m.
  destruct (seg_rw1_sound m 0xb9f1c0 ltac:(lia) seg_rw1_b9f000) as [Wr [b0 Rd]].
  exists b0. split; [split|].
  - exact (conj I I).
  - split; [lia|]. split; [cbn; lia|].
    intros i Below. cbn in Below. assert (Zero : i = 0%nat) by lia. subst i. exact Rd.
  - split; [lia|]. split; [cbn; lia|].
    intros i Below. cbn in Below. assert (Zero : i = 0) by lia. subst i. exact Wr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells asegs m 0x52e860 [C8 (Z_to_bv 64 0x1f34cc); C8 (Z_to_bv 64 0x199adc); C8 (Z_to_bv 64 0x1f34fc)]
  /\ ro_cells asegs m 0x5a6548 [C8 (Z_to_bv 64 0x52e878); C8 (Z_to_bv 64 0x52e860)]
  /\ ro_cells asegs m 0x5a4588 [C8 (Z_to_bv 64 0x51af44); C8 (Z_to_bv 64 0)]
  /\ (exists dso : word, ro_cells asegs m 0x5a75c0 [C8 dso])
  /\ ro_cells asegs m 0x5a6500 [C8 (Z_to_bv 64 0x5aaa60); C8 (Z_to_bv 64 0x669460)]
  /\ ro_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)]
  /\ ro_cells asegs m 0x5a45a8 [C8 (Z_to_bv 64 0x6fe668); C8 (Z_to_bv 64 0x66a338); C8 (Z_to_bv 64 0x66cb38);
                                C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820);
                                C8 (Z_to_bv 64 0x5a77f0)]
  /\ ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x66a3f0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)]
  /\ ro_cells asegs m 0x6fe9e0 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m SHW_LO SHW_HI.
