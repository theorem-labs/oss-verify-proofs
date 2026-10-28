(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts2 AsAtomics AsDepotInv AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma mb_u64arr_cons : forall m A w ws,
  u64arr asegs m A (w :: ws) <-> rw_cells asegs m A [C8 w] /\ u64arr asegs m (A + 8) ws.
Proof.
  intros m A w ws. unfold u64arr, rw_cells, cells_at. change (u64s (w :: ws)) with (le8 w ++ u64s ws).
  cbn [map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
  rewrite app_nil_r. rewrite bytes_at_app, length_le8. cbn [length].
  replace (8 * Z.of_nat (S (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
  rewrite wr_at_app by lia. change (Z.of_nat (8 + 0)) with 8. change (Z.of_nat 8) with 8. tauto.
Qed.
Lemma mb_u64arr_app : forall m A ws1 ws2,
  u64arr asegs m A (ws1 ++ ws2) <-> u64arr asegs m A ws1 /\ u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2. rewrite !u64arr_u8arr, u64s_app, u8arr_app, u64s_length.
  replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) by lia. tauto.
Qed.
Lemma mb_u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof.
  intros m A H0 H1. unfold u64arr. cbn [u64s length map concat Z.of_nat Z.mul]. unfold bytes_at, wr_at. cbn [length Z.of_nat].
  change (8 * 0) with 0. rewrite Z.add_0_r. repeat split; lia.
Qed.

Lemma land64_id : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mb_copy_post (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (SRC DST n : Z) (ws : list word) : machine_state -> Prop :=
  fun ms' => exists (t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 (wz (SRC + 8 * n)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (DST + 8 * n)) (wz (SRC + 8 * n)) t5 t6)
             F (Z_to_bv 64 0x198fdc) fc None m' (seg_rom asegs)
    /\ munch [(DST, DST + 8 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u64arr asegs m' DST ws /\ u64arr asegs m' SRC ws.
End HCW.

Section CopyLoop.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (SRC DST n : Z) (ws : list word).
  Hypothesis SRCR : AHI_LO <= SRC /\ SRC + 8 * n <= aceil /\ SRC mod 8 = 0.
  Hypothesis DSTR : AHI_LO <= DST /\ DST + 8 * n <= aceil /\ DST mod 8 = 0.
  Hypothesis DISJ : SRC + 8 * n <= DST \/ DST + 8 * n <= SRC.
  Hypothesis NR : 0 < n. Hypothesis WSL : length ws = Z.to_nat n.

  Lemma mb_copy : forall (k : nat) (i : Z) (t5 : word) (m1 : mem),
    Z.to_nat (n - i) = k -> 0 <= i < n ->
    mem_inv asegs m1 -> munch [(DST, DST + 8 * n)]%Z m m1 -> wmono asegs m m1 ->
    stk asegs m1 (DST + 8 * i) (DST + 8 * n) ->
    u64arr asegs m1 DST (firstn (Z.to_nat i) ws) -> u64arr asegs m1 SRC ws ->
    evt asegs (mb_copy_post ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m SRC DST n ws)
      (MS (mkR ra sp gp tp t0 t1 (wz (SRC + 8 * i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (DST + 8 * i)) (wz (SRC + 8 * n)) t5 t6)
          F (Z_to_bv 64 0x198fc8) fc None m1 (seg_rom asegs)).
  Proof.
    unfold AHI_LO in *. acb.
    induction k as [|k IH]; intros i t5 m1 HK HI MI1 MU1 WM1 JK ARR SRCA. { exfalso. clear - HK HI; lia. }
    unfold wz.
    (* [comment removed for export] *)
    assert (NTH : exists w, nth_error ws (Z.to_nat i) = Some w).
    { destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:E; [exists w; reflexivity|]. exfalso. apply nth_error_None in E. clear - E HI WSL. lia. }
    destruct NTH as [w NTH].
    pose proof (u64arr_read asegs _ _ _ i w (Z_to_bv 64 (SRC + 8 * i)) SRCA NTH ltac:(hci; clear - HI; lia) ltac:(hci; symmetry; apply wa_of_Z_to_bv; clear - SRCR HI ACEILB; lia)) as RD.
    (* [comment removed for export] *)
    step. clear RD. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (DST + 8 * i + 8) _ JK ltac:(hci; clear - HI; lia)) as [SK1 SK2]. clear JK.
    destruct (stk_cells _ _ _ SK1 ltac:(hci; clear; lia)) as [jw JW]. clear SK1.
    replace (DST + 8 * i + 8 - (DST + 8 * i)) with 8 in JW by lia. change (Z.to_nat 8) with 8%nat in JW.
    assert (LF : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length_le; [reflexivity| clear - WSL HI; lia]).
    remember (DST + 8 * i) as DD eqn:ED in JW |- *.
    (* [comment removed for export] *)
    step. subst DD.
    (* [comment removed for export] *)
    step. step.
    assert (ARR' : u64arr asegs m0 DST (firstn (Z.to_nat (i + 1)) ws)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HI; lia).
      rewrite (firstn_S_nth _ _ w NTH). apply (proj2 (u64arr_snoc asegs _ _ _ _)). rewrite LF.
      replace (DST + 8 * Z.of_nat (Z.to_nat i)) with (DST + 8 * i) by (clear - HI; lia). split; [exact ARR| exact JW]. }
    clear ARR JW LF.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (SRC + 8 * i + 8) with (SRC + 8 * (i + 1)) in * by (clear; lia).
      replace (DST + 8 * i + 8) with (DST + 8 * (i + 1)) in * by (clear; lia).
      eapply (IH (i + 1)); try eassumption. { clear - HK HI K; lia. }
      { revert K. rewrite ?unsigned_lit by (clear - HI NR SRCR DSTR ACEILB; lia). clear - HI. intros K. lia. }
    - (* [comment removed for export] *)
      assert (i + 1 = n) as EQ by (revert K; rewrite ?unsigned_lit by (clear - HI NR SRCR DSTR ACEILB; lia); clear - HI; intros K; lia).
      replace (SRC + 8 * i + 8) with (SRC + 8 * (i + 1)) in * by (clear; lia).
      replace (DST + 8 * i + 8) with (DST + 8 * (i + 1)) in * by (clear; lia).
      rewrite EQ in ARR' |- *. rewrite <- WSL, firstn_all in ARR'.
      apply evt_done. unfold mb_copy_post. do 2 eexists.
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ARR'| exact SRCA].
  Qed.
End CopyLoop.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Segs.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  (* [comment removed for export] *)
  Fixpoint bseg (m : mem) (l : list qbatch) (nx : Z) : Prop :=
    match l with
    | [] => True
    | b :: r => batch_rep m b (hd nx (map qb_addr r)) /\ bseg m r nx
    end.
  Lemma bseg_batches : forall m l, bseg m l 0 <-> batches_rep m l.
  Proof. intros m l. induction l as [|b r IH]; cbn [bseg batches_rep]; [tauto|]. rewrite IH. destruct r; cbn [hd map]; tauto. Qed.
  Lemma hd_map_app : forall (l1 l2 : list qbatch) nx, hd nx (map qb_addr (l1 ++ l2)) = hd (hd nx (map qb_addr l2)) (map qb_addr l1).
  Proof. intros [|b r] l2 nx; reflexivity. Qed.
  Lemma bseg_app : forall m l1 l2 nx, bseg m (l1 ++ l2) nx <-> bseg m l1 (hd nx (map qb_addr l2)) /\ bseg m l2 nx.
  Proof.
    intros m l1. induction l1 as [|b r IH]; intros l2 nx; cbn [bseg app]; [tauto|].
    rewrite IH, hd_map_app. tauto.
  Qed.
  (* [comment removed for export] *)
  Definition bok (b : qbatch) : Prop :=
    AHI_LO <= qb_addr b /\ qb_addr b + kBatchSize <= aceil /\ qb_addr b mod 16 = 0
    /\ 0 <= qb_count b <= kBatchCount /\ qb_count b = zlen (qb_chunks b) /\ kBatchSize <= qb_size b
    /\ Forall (fun x => 0 <= x < 2^64) (qb_chunks b).
  (* [comment removed for export] *)
  Lemma batch_rep_transport : forall (P : Z -> Prop) m m' b nx,
    agree_on P m m' -> wmono asegs m m' ->
    (forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    0 <= qb_count b -> 24 + 8 * qb_count b <= kBatchSize -> qb_count b = zlen (qb_chunks b) ->
    batch_rep m b nx -> batch_rep m' b nx.
  Proof.
    intros P m m' b nx AG WM HP C1 C2 C3 (B1 & B2 & B3 & B4). unfold batch_rep. unfold zlen in C3. unfold kBatchSize in *.
    split; [|split; [|split]].
    - eapply (rw_cells_transport_pt P m m' AG WM); [exact B1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HP. left; lia.
    - eapply (u64arr_transport_pt P m m' AG WM); [exact B2|]. unfold wlist. rewrite length_map. intros a Ha. apply HP. left; lia.
    - eapply (junk_transport_pt P m m' AG WM); [exact B3|]. intros a Ha. apply HP. left; lia.
    - eapply (poisoned_transport_pt P m m' AG WM); [exact B4|]. intros a Ha. apply HP. right.
      change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. lia.
  Qed.
  Lemma bseg_transport : forall (P : Z -> Prop) m m' l nx,
    agree_on P m m' -> wmono asegs m m' ->
    (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    Forall bok l -> bseg m l nx -> bseg m' l nx.
  Proof.
    intros P m m' l nx AG WM HP OKl. induction l as [|b r IH]; [exact (fun x => x)|].
    cbn [bseg]. intros [HB HR]. apply Forall_cons_iff in OKl. destruct OKl as [OKb OKr].
    split; [| apply IH; [intros b0 a Hb0 Ha; apply (HP b0 a); [right; exact Hb0| exact Ha]| exact OKr| exact HR]].
    destruct OKb as (_ & _ & _ & K1 & K2 & _). unfold kBatchCount, kBatchSize in *.
    apply (batch_rep_transport P m m' b _ AG WM); [intros a Ha; apply (HP b a); [left; reflexivity| exact Ha]| clear - K1; lia| clear - K1; unfold kBatchSize; lia| exact K2| exact HB].
  Qed.
  Lemma junk_stk0 : forall m lo n, junk m lo n -> 0 <= lo -> lo + n <= 2^64 -> 0 <= n -> stk asegs m lo (lo + n).
  Proof.
    intros m lo n J H1 H2 H3. destruct (Z.eq_dec n 0) as [->|NZ]; [rewrite Z.add_0_r; apply stk_empty; lia| apply J; lia].
  Qed.
  Lemma stk_junk0 : forall m lo hi n, stk asegs m lo hi -> hi = lo + n -> junk m lo n.
  Proof. intros m lo hi n SK -> POS. exact SK. Qed.
  (* [comment removed for export] *)
  Lemma batch_open : forall m b nx, bok b -> batch_rep m b nx ->
       rw_cells asegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
    /\ u64arr asegs m (qb_addr b + 24) (wlist (qb_chunks b))
    /\ stk asegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize)
    /\ poisoned m (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.
  Proof.
    intros m b nx (O1 & O2 & O3 & O4 & O5 & O6 & O7) (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [| exact B4].
    pose proof (junk_stk0 m _ _ B3) as SK. replace (qb_addr b + 24 + 8 * qb_count b + (kBatchSize - 24 - 8 * qb_count b)) with (qb_addr b + kBatchSize) in SK by lia.
    apply SK; acb; unfold AHI_LO, kBatchSize, kBatchCount in *; lia.
  Qed.
  Lemma batch_close : forall m b nx,
    rw_cells asegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))] ->
    u64arr asegs m (qb_addr b + 24) (wlist (qb_chunks b)) ->
    stk asegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize) ->
    poisoned m (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic ->
    batch_rep m b nx.
  Proof. intros m b nx B1 B2 B3 B4. split; [exact B1|]. split; [exact B2|]. split; [| exact B4]. eapply stk_junk0; [exact B3| lia]. Qed.
End Segs.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

Definition bext (b : qbatch) : ivl := (qb_addr b, qb_addr b + kBatchSize).
Definition bsum (l : list qbatch) : Z := fold_right Z.add 0 (map qb_size l).

(* [comment removed for export] *)
Definition thdr (f0 l0 : word) (ex : list qbatch) : word * word :=
  match ex with [] => (f0, l0) | b :: _ => (wz (qb_addr b), wz (qb_addr (last ex b))) end.

(* [comment removed for export] *)
Definition merge_batches_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo A T qbytes tb : Z) (f0 l0 : word) (l l' ex : list qbatch) (xb : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((bv_unsigned sp + -16, bv_unsigned sp) :: (A, A + 32) :: (T, T + 32) :: map bext l) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' A [C8 (wz (zlen l')); C8 (wz (hd 0 (map qb_addr l'))); C8 (wz (last (map qb_addr l') 0)); C8 (wz (qbytes - xb))]
    /\ batches_rep m' l'
    /\ rw_cells asegs m' T [C8 (wz (zlen ex)); C8 (fst (thdr f0 l0 ex)); C8 (snd (thdr f0 l0 ex)); C8 (wz (tb + xb))]
    /\ batches_rep m' ex
    /\ Forall bok l' /\ Forall bok ex /\ Forall (fun b => qb_count b = 0 /\ qb_size b = kBatchSize) ex
    /\ (forall b, In b (l' ++ ex) -> In (qb_addr b) (map qb_addr l)) /\ xb = kBatchSize * zlen ex
    /\ List.NoDup (map qb_addr (l' ++ ex)).
End HCW.

Section Loop.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo A T qbytes tb : Z) (f0 l0 : word) (l : list qbatch) (jr : list byte).
  (* [comment removed for export] *)
  Variables (lF exF : list qbatch) (xbF : Z).
  Let Wtot : list ivl := (bv_unsigned sp + -16, bv_unsigned sp) :: (A, A + 32) :: (T, T + 32) :: map bext l.
  Let POST := merge_batches_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m lo A T qbytes tb f0 l0 l lF exF xbF.

  Hypothesis LO : aceil <= lo. Hypothesis HI : lo + 16 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : 0 <= A /\ A + 32 <= AIMG_TOP /\ A mod 8 = 0.
  Hypothesis TR : bv_unsigned sp <= T /\ T + 32 <= 2^47 /\ T mod 8 = 0.
  Hypothesis QBR : 0 <= qbytes /\ qbytes < 2^61. Hypothesis TBR : 0 <= tb /\ tb + qbytes < 2^62.
  Hypothesis OKL : Forall bok l.
  Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
  Hypothesis A6 : a6 = Z_to_bv 64 (-8192) \/ a6 = Z_to_bv 64 (2^64 - 8192).   (* [comment removed for export] *)
  Hypothesis LLEN : kBatchSize * zlen l <= qbytes.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mb_mem (m1 : mem) (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
       rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jr; C8 ra]
    /\ rw_cells asegs m1 A [C8 (wz (zlen done + 2 + zlen rest)); C8 (wz (qb_addr (hd cur done))); C8 (wz (qb_addr (last rest nx))); C8 (wz qbytes)]
    /\ rw_cells asegs m1 T [C8 (wz (zlen ex)); C8 (fst (thdr f0 l0 ex)); C8 (snd (thdr f0 l0 ex)); C8 (wz (tb + xb))]
    /\ bseg m1 done (qb_addr cur)
    /\ rw_cells asegs m1 (qb_addr cur) [C8 (wz (qb_addr nx)); C8 (wz (qb_size cur)); C8 (wz (qb_count cur))]
    /\ u64arr asegs m1 (qb_addr cur + 24) (wlist (qb_chunks cur))
    /\ stk asegs m1 (qb_addr cur + 24 + 8 * qb_count cur) (qb_addr cur + kBatchSize)
    /\ poisoned m1 (qb_addr cur) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic
    /\ bseg m1 (nx :: rest) 0
    /\ bseg m1 ex 0.
  Definition mb_pure (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
       (exists fuel, merge_batches_aux fuel cur (nx :: rest) (rev done) (rev ex) xb = Some (lF, exF, xbF))
    /\ Forall bok done /\ bok cur /\ Forall bok (nx :: rest) /\ Forall bok ex /\ Forall (fun b => qb_count b = 0 /\ qb_size b = kBatchSize) ex
    /\ (forall b, In b (done ++ cur :: nx :: rest ++ ex) -> In (qb_addr b) (map qb_addr l))
    /\ List.NoDup (map qb_addr (done ++ cur :: nx :: rest ++ ex))
    /\ qb_size cur + bsum (nx :: rest) <= qbytes /\ xb = kBatchSize * zlen ex /\ xb + kBatchSize * (1 + zlen rest) <= qbytes
    /\ zlen done + 2 + zlen rest + zlen ex <= zlen l.

  (* [comment removed for export] *)
  Lemma zlen_app1 : forall (d : list qbatch) b, zlen (d ++ [b]) = zlen d + 1.
  Proof. intros d b. unfold zlen. rewrite length_app. cbn [length]. clear. lia. Qed.
  Lemma hd_map_app1 : forall (d : list qbatch) b, hd 0 (map qb_addr (d ++ [b])) = qb_addr (hd b d).
  Proof. intros [|x d] b; reflexivity. Qed.
  Lemma last_map_app1 : forall (d : list qbatch) b, last (map qb_addr (d ++ [b])) 0 = qb_addr b.
  Proof. intros d b. rewrite map_app. cbn [map]. rewrite last_last. reflexivity. Qed.
  Lemma hd_app1 : forall (d : list qbatch) b x, hd x (d ++ [b]) = hd b d.
  Proof. intros [|y d] b x; reflexivity. Qed.
  Lemma last_cons_any : forall (r : list qbatch) x y, r <> [] -> last r x = last r y.
  Proof. intros r. induction r as [|z r IH]; intros x y NE; [exfalso; exact (NE eq_refl)|]. destruct r as [|q r']; [reflexivity|]. apply (IH x y). discriminate. Qed.
  Lemma last_cons : forall (r : list qbatch) x d, last (x :: r) d = last r x.
  Proof. intros r x d. destruct r as [|y r]; [reflexivity|]. cbn [last]. apply (last_cons_any (y :: r)). discriminate. Qed.
  Lemma stk_of_u64arr : forall m1 A ws, u64arr asegs m1 A ws -> stk asegs m1 A (A + 8 * Z.of_nat (length ws)).
  Proof.
    intros m1 A0 ws [B W].
    assert (U8 : u8arr asegs m1 A0 (u64s ws)). { split; [exact B|]. rewrite u64s_length, Nat2Z.inj_mul. exact W. }
    pose proof (rw_cells_of_u8arr asegs m1 A0 (u64s ws) U8) as RC.
    pose proof (stk_of_rw_cells asegs _ _ _ RC) as SK. cbn [cells_size csize] in SK. rewrite Nat.add_0_r, u64s_length, Nat2Z.inj_mul in SK. exact SK.
  Qed.

(* [comment removed for export] *)
Lemma thdr_ne : forall ex d, ex <> [] -> thdr f0 l0 ex = (wz (qb_addr (hd d ex)), wz (qb_addr (last ex d))).
Proof.
  intros [|b r] d NE; [exfalso; exact (NE eq_refl)|]. cbn [thdr hd]. rewrite (last_cons_any (b :: r) b d) by discriminate. reflexivity.
Qed.
Lemma thdr_snd_snoc : forall exi lx, snd (thdr f0 l0 (exi ++ [lx])) = wz (qb_addr lx).
Proof. intros exi lx. rewrite (thdr_ne (exi ++ [lx]) lx) by (destruct exi; discriminate). cbn [snd]. rewrite last_last. reflexivity. Qed.
Lemma thdr_fst_snoc : forall ex b, ex <> [] -> fst (thdr f0 l0 (ex ++ [b])) = fst (thdr f0 l0 ex).
Proof. intros [|x r] b NE; [exfalso; exact (NE eq_refl)|]. reflexivity. Qed.
Lemma nd_facts : forall (d r : list Z) c n, List.NoDup (d ++ c :: n :: r) -> c <> n /\ (forall a, In a (d ++ r) -> a <> c /\ a <> n).
Proof.
  intros d r c n ND. pose proof (NoDup_remove_2 d (n :: r) c ND) as NC. pose proof (NoDup_remove_1 d (n :: r) c ND) as ND1.
  pose proof (NoDup_remove_2 d r n ND1) as NN. split.
  - intros E. apply NC. apply in_or_app. right. left. symmetry. exact E.
  - intros a Ha. apply in_app_or in Ha. split; intros E; subst a.
    + apply NC. apply in_or_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right; right; exact Ha].
    + apply NN. apply in_or_app. exact Ha.
Qed.
Lemma nd_move : forall (d r : list Z) c n, List.NoDup (d ++ c :: n :: r) -> List.NoDup (d ++ c :: r ++ [n]).
Proof.
  intros d r c n ND. eapply Permutation_NoDup; [| exact ND]. apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
Qed.
Lemma outside_bext : forall (L : list qbatch) x a, outside (map bext L) x -> In a (map qb_addr L) -> ~ (a <= x < a + kBatchSize).
Proof.
  intros L x a. induction L as [|b L IH]; cbn [map outside bext In]; [tauto|].
  intros [O1 O2] [E|Hin]; [subst a; exact O1| exact (IH O2 Hin)].
Qed.
Lemma bsum_cons : forall b r, bsum (b :: r) = qb_size b + bsum r. Proof. reflexivity. Qed.
Lemma zlen_cons' : forall (b : qbatch) r, zlen (b :: r) = 1 + zlen r. Proof. intros b r. unfold zlen. cbn [length]. clear. lia. Qed.
Lemma zlen_nil' : zlen (@nil qbatch) = 0. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mb_exit : forall dn lb ex xb (t0 t1 t2 t3 t4 t5 a1 a3 a4 : word) m1,
    lF = dn ++ [lb] -> exF = ex -> xbF = xb ->
    Forall bok dn -> bok lb -> Forall bok ex -> Forall (fun b => qb_count b = 0 /\ qb_size b = kBatchSize) ex ->
    (forall b, In b (dn ++ lb :: ex) -> In (qb_addr b) (map qb_addr l)) ->
    List.NoDup (map qb_addr (dn ++ lb :: ex)) ->
    xb = kBatchSize * zlen ex -> 0 <= xb <= qbytes ->
    mem_inv asegs m1 -> munch Wtot m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -16) ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jr; C8 ra] ->
    rw_cells asegs m1 A [C8 (wz (zlen dn + 1)); C8 (wz (qb_addr (hd lb dn))); C8 (wz (qb_addr lb)); C8 (wz qbytes)] ->
    rw_cells asegs m1 T [C8 (wz (zlen ex)); C8 (fst (thdr f0 l0 ex)); C8 (snd (thdr f0 l0 ex)); C8 (wz (tb + xb))] ->
    bseg m1 dn (qb_addr lb) ->
    rw_cells asegs m1 (qb_addr lb) [C8 (wz 0); C8 (wz (qb_size lb)); C8 (wz (qb_count lb))] ->
    u64arr asegs m1 (qb_addr lb + 24) (wlist (qb_chunks lb)) ->
    stk asegs m1 (qb_addr lb + 24 + 8 * qb_count lb) (qb_addr lb + kBatchSize) ->
    poisoned m1 (qb_addr lb) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic ->
    bseg m1 ex 0 ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (wz A) a1 (wz xb) a3 a4 (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199074) fc None m1 (seg_rom asegs)).
  Proof.
    intros dn lb ex xb t0 t1 t2 t3 t4 t5 a1 a3 a4 m1 ELF EEX EXB OKD OKB OKE EXE SUBL ND XBE XBR MI1 MU1 WM1 ST1 FR HA HT DONE LBC LBA LBJ LBP EX.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof OKB as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    pose proof (munch_refl [(A + 24, A + 32)] m1) as MUL. pose proof (wmono_refl asegs m1) as WML.
    unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *. unfold Wtot in MU1. acb.
    assert (LENB : Z.of_nat (length (wlist (qb_chunks lb))) = qb_count lb) by (unfold wlist; rewrite length_map; unfold zlen in C5; clear - C5; lia).
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    rewrite !unsigned_lit in HA by (clear - QBR XBR; lia).
    release_frame FR ST1 (bv_unsigned sp).
    pose proof (munch_agree _ _ _ MUL) as AGL.
    apply evt_done. unfold POST, merge_batches_post. unfold kBatchSize, wz. subst lF exF xbF.
    do 14 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split. { rewrite zlen_app1, hd_map_app1, last_map_app1. exact HA. }
    split. { apply bseg_batches. apply bseg_app. cbn [map hd bseg]. split; [| split; [| exact I]].
             - eapply (bseg_transport _ m1 _ _ _ AGL WML); [| exact OKD| exact DONE].
               intros b a Hb Ha. pose proof (proj1 (Forall_forall _ _) OKD b Hb) as (Q1 & _). cbn [outside]. unfold kBatchSize, AHI_LO in *. clear - Ha Q1 AR.
               split; [| exact I]. destruct Ha as [Ha|Ha]; [lia| unfold sh, ASHADOW_BASE in Ha; lia].
             - apply batch_close; [exact LBC| exact LBA| exact LBJ|].
               eapply (poisoned_transport_pt _ m1 _ AGL WML); [exact LBP|]. intros a Ha. cbn [outside]. clear - Ha C1 AR. split; [unfold sh, ASHADOW_BASE in Ha; lia| exact I]. }
    split; [exact HT|].
    split. { apply bseg_batches. eapply (bseg_transport _ m1 _ _ _ AGL WML); [| exact OKE| exact EX].
             intros b a Hb Ha. pose proof (proj1 (Forall_forall _ _) OKE b Hb) as (Q1 & _). cbn [outside]. unfold kBatchSize, AHI_LO in *. clear - Ha Q1 AR.
             split; [| exact I]. destruct Ha as [Ha|Ha]; [lia| unfold sh, ASHADOW_BASE in Ha; lia]. }
    split; [apply Forall_app; split; [exact OKD| constructor; [exact OKB| constructor]]|].
    split; [exact OKE|]. split; [exact EXE|].
    split; [intros b Hb; apply SUBL; rewrite <- app_assoc in Hb; exact Hb|]. split; [exact XBE|]. rewrite <- app_assoc. exact ND.
  Qed.

  (* [comment removed for export] *)
  Definition mcur (cur nx : qbatch) : qbatch :=
    mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx) (qb_chunks cur ++ qb_chunks nx).
  Definition mnx (nx : qbatch) : qbatch := mkQB (qb_addr nx) kBatchSize 0 [].
  (* [comment removed for export] *)
  Definition mq_pure (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
       (exists fuel, merge_batches_aux fuel (mcur cur nx) rest (rev done) (rev (ex ++ [mnx nx])) (xb + kBatchSize) = Some (lF, exF, xbF))
    /\ Forall bok done /\ bok cur /\ bok nx /\ Forall bok rest /\ Forall bok ex /\ Forall (fun b => qb_count b = 0 /\ qb_size b = kBatchSize) ex
    /\ (forall b, In b (done ++ cur :: nx :: rest ++ ex) -> In (qb_addr b) (map qb_addr l))
    /\ List.NoDup (map qb_addr (done ++ cur :: nx :: rest ++ ex))
    /\ qb_count cur + qb_count nx <= kBatchCount
    /\ qb_size cur + (qb_size nx + bsum rest) <= qbytes /\ xb = kBatchSize * zlen ex /\ xb + kBatchSize * (1 + zlen rest) <= qbytes
    /\ zlen done + 2 + zlen rest + zlen ex <= zlen l.
  (* [comment removed for export] *)
  Definition mq_mem1 (m1 : mem) (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
       rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jr; C8 ra]
    /\ rw_cells asegs m1 A [C8 (wz (zlen done + 2 + zlen rest)); C8 (wz (qb_addr (hd cur done))); C8 (wz (qb_addr (last rest nx))); C8 (wz qbytes)]
    /\ rw_cells asegs m1 T [C8 (wz (zlen ex)); C8 (fst (thdr f0 l0 ex)); C8 (snd (thdr f0 l0 ex)); C8 (wz (tb + xb))]
    /\ bseg m1 done (qb_addr cur)
    /\ rw_cells asegs m1 (qb_addr cur) [C8 (wz (qb_addr nx)); C8 (wz (qb_size cur)); C8 (wz (qb_count cur))]
    /\ u64arr asegs m1 (qb_addr cur + 24) (wlist (qb_chunks cur ++ qb_chunks nx))
    /\ stk asegs m1 (qb_addr cur + 24 + 8 * (qb_count cur + qb_count nx)) (qb_addr cur + kBatchSize)
    /\ poisoned m1 (qb_addr cur) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic
    /\ rw_cells asegs m1 (qb_addr nx) [C8 (wz (hd 0 (map qb_addr rest))); C8 (wz (qb_size nx)); C8 (wz (qb_count nx))]
    /\ u64arr asegs m1 (qb_addr nx + 24) (wlist (qb_chunks nx))
    /\ stk asegs m1 (qb_addr nx + 24 + 8 * qb_count nx) (qb_addr nx + kBatchSize)
    /\ poisoned m1 (qb_addr nx) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic
    /\ bseg m1 rest 0
    /\ bseg m1 ex 0.
  (* [comment removed for export] *)
  Definition mq_memK (hf : word) (lk : Z) (m1 : mem) (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
       rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jr; C8 ra]
    /\ rw_cells asegs m1 A [C8 (wz (zlen done + 2 + zlen rest - 1)); C8 (wz (qb_addr (hd cur done))); C8 (wz (qb_addr (last rest cur))); C8 (wz qbytes)]
    /\ rw_cells asegs m1 T [C8 (wz (zlen ex)); C8 hf; C8 (snd (thdr f0 l0 ex)); C8 (wz (tb + xb))]
    /\ bseg m1 done (qb_addr cur)
    /\ rw_cells asegs m1 (qb_addr cur) [C8 (wz (hd 0 (map qb_addr rest))); C8 (wz (qb_size cur + (qb_size nx - kBatchSize))); C8 (wz (qb_count cur + qb_count nx))]
    /\ u64arr asegs m1 (qb_addr cur + 24) (wlist (qb_chunks cur ++ qb_chunks nx))
    /\ stk asegs m1 (qb_addr cur + 24 + 8 * (qb_count cur + qb_count nx)) (qb_addr cur + kBatchSize)
    /\ poisoned m1 (qb_addr cur) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic
    /\ rw_cells asegs m1 (qb_addr nx) [C8 (wz 0); C8 (wz kBatchSize); C8 (wz 0)]
    /\ stk asegs m1 (qb_addr nx + 24) (qb_addr nx + kBatchSize)
    /\ poisoned m1 (qb_addr nx) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic
    /\ bseg m1 rest 0
    /\ bseg m1 ex lk.
  Definition mq_mem2 (m1 : mem) (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
    mq_memK (fst (thdr f0 l0 ex)) 0 m1 done cur nx rest ex xb.
  Definition mq_mem3 (m1 : mem) (done : list qbatch) (cur nx : qbatch) (rest ex : list qbatch) (xb : Z) : Prop :=
    mq_memK (fst (thdr f0 l0 (ex ++ [mnx nx]))) (qb_addr nx) m1 done cur nx rest ex xb.
  (* [comment removed for export] *)
  Definition mq_kont (n : nat) : Prop :=
    forall done cur nx rest ex xb (t1 t2 t3 t4 t5 a3 : word) (m1 : mem),
      (length rest < n)%nat ->
      mb_pure done cur nx rest ex xb ->
      mem_inv asegs m1 -> munch Wtot m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -16) ->
      mb_mem m1 done cur nx rest ex xb ->
      evt asegs POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) t1 t2 s0 s1 (wz A) (wz T) (wz xb) a3 (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x198f90) fc None m1 (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma far_batch : forall (x : Z) (b : qbatch) a k,
    In x (map qb_addr l) -> In (qb_addr b) (map qb_addr l) -> qb_addr b <> x -> 0 <= k <= kBatchSize ->
    (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> ~ (x <= a < x + k).
  Proof.
    intros x b a k Hx Hb NE Hk Ha.
    assert (XR : AHI_LO <= x).
    { apply in_map_iff in Hx. destruct Hx as (b' & E & Hin). subst x. exact (proj1 (proj1 (Forall_forall _ _) OKL b' Hin)). }
    assert (BR : qb_addr b + kBatchSize <= aceil).
    { apply in_map_iff in Hb. destruct Hb as (b' & E & Hin). rewrite <- E. exact (proj1 (proj2 (proj1 (Forall_forall _ _) OKL b' Hin))). }
    destruct Ha as [Ha|Ha].
    - destruct (PW _ _ Hb Hx NE) as [D|D]; clear - D Ha Hk; unfold kBatchSize in *; lia.
    - clear - Ha XR BR Hk. acb. unfold kBatchSize, AHI_LO, sh, ASHADOW_BASE in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma far_low : forall (b : qbatch) a x k, bok b -> x + k <= AIMG_TOP ->
    (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> ~ (x <= a < x + k).
  Proof. intros b a x k (B1 & _) Hx Ha. clear - B1 Hx Ha. unfold kBatchSize, AHI_LO, AIMG_TOP, sh, ASHADOW_BASE in *. lia. Qed.
  Lemma far_high : forall (b : qbatch) a x k, bok b -> aceil <= x ->
    (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> ~ (x <= a < x + k).
  Proof. intros b a x k (B1 & B2 & _) Hx Ha. clear - B1 B2 Hx Ha. acb. unfold kBatchSize, AHI_LO, sh, ASHADOW_BASE in *. lia. Qed.
  (* [comment removed for export] *)
  Definition ifar (L : list qbatch) (i : ivl) : Prop :=
    let (ilo, ihi) := i in
    ihi <= AIMG_TOP \/ aceil <= ilo \/ exists x, In x (map qb_addr l) /\ x <= ilo /\ ihi <= x + kBatchSize /\ forall b, In b L -> qb_addr b <> x.
  Lemma outside_far : forall W L a b, Forall (ifar L) W -> In b L -> bok b -> In (qb_addr b) (map qb_addr l) ->
    (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> outside W a.
  Proof.
    intros W L a b FW Hb OK Hin Ha. induction W as [|[ilo ihi] W IH]; [exact I|].
    apply Forall_cons_iff in FW. destruct FW as [F1 FW]. cbn [outside]. split; [| exact (IH FW)]. unfold ifar in F1.
    destruct F1 as [F1|[F1|(x & X1 & X2 & X3 & X4)]].
    - pose proof (far_low b a ilo (ihi - ilo) OK ltac:(clear - F1; lia) Ha) as Q. clear - Q. lia.
    - pose proof (far_high b a ilo (ihi - ilo) OK F1 Ha) as Q. clear - Q. lia.
    - pose proof (far_batch x b a kBatchSize X1 Hin (X4 b Hb) ltac:(unfold kBatchSize; lia) Ha) as Q. clear - Q X2 X3. lia.
  Qed.
  Lemma bseg_far : forall W m1 m2 L z, Forall (ifar L) W -> Forall bok L -> (forall b, In b L -> In (qb_addr b) (map qb_addr l)) ->
    agree_on (outside W) m1 m2 -> wmono asegs m1 m2 -> bseg m1 L z -> bseg m2 L z.
  Proof.
    intros W m1 m2 L z FW OK SUB AG WM B. eapply (bseg_transport _ m1 m2 L z AG WM); [| exact OK| exact B].
    intros b a Hb Ha. eapply (outside_far W L a b FW Hb); [exact (proj1 (Forall_forall _ _) OK b Hb)| exact (SUB b Hb)| exact Ha].
  Qed.
  Lemma pois_far : forall W m1 m2 b, Forall (ifar [b]) W -> bok b -> In (qb_addr b) (map qb_addr l) ->
    agree_on (outside W) m1 m2 -> wmono asegs m1 m2 ->
    poisoned m1 (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic ->
    poisoned m2 (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.
  Proof.
    intros W m1 m2 b FW OK Hin AG WM P. eapply (poisoned_transport_pt _ m1 m2 AG WM); [exact P|].
    intros a Ha. eapply (outside_far W [b] a b FW); [left; reflexivity| exact OK| exact Hin|]. right.
    unfold kBatchSize in *. change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. exact Ha.
  Qed.
  Lemma pois_far2 : forall W m1 m2 b, Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) W -> bok b ->
    agree_on (outside W) m1 m2 -> wmono asegs m1 m2 ->
    poisoned m1 (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic ->
    poisoned m2 (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.
  Proof.
    intros W m1 m2 b FP OK AG WM P. eapply (poisoned_transport_pt _ m1 m2 AG WM); [exact P|].
    intros a Ha. clear AG WM P. revert FP. induction W as [|[ilo ihi] W IH]; intros FP; [exact I|].
    apply Forall_cons_iff in FP. destruct FP as [F1 FP]. cbn [outside fst snd] in F1 |- *. split; [| exact (IH FP)].
    destruct OK as (B1 & B2 & _). clear - F1 B1 B2 Ha. acb. unfold kBatchSize, AHI_LO, AIMG_TOP, sh, ASHADOW_BASE in *. lia.
  Qed.
  Lemma hd_addr : forall (d : list qbatch) x y, qb_addr x = qb_addr y -> qb_addr (hd x d) = qb_addr (hd y d).
  Proof. intros [|b d] x y E; [exact E| reflexivity]. Qed.
  Lemma bsum_nonneg : forall r, Forall bok r -> 0 <= bsum r.
  Proof.
    intros r OK. induction r as [|b r IH]; [change (bsum []) with 0; clear; lia|]. apply Forall_cons_iff in OK. destruct OK as [(_ & _ & _ & _ & _ & Q6 & _) Hr].
    rewrite bsum_cons. specialize (IH Hr). clear - Q6 IH. unfold kBatchSize in Q6. lia.
  Qed.
  Lemma bok_mcur : forall cur nx, bok cur -> bok nx -> qb_count cur + qb_count nx <= kBatchCount -> bok (mcur cur nx).
  Proof.
    intros cur nx (C1 & C2 & C3 & C4 & C5 & C6 & C7) (N1 & N2 & N3 & N4 & N5 & N6 & N7) K. unfold bok, mcur. cbn [qb_addr qb_size qb_count qb_chunks].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [clear - C4 N4 K; lia|].
    split; [unfold zlen in *; rewrite length_app; clear - C5 N5; lia|]. split; [clear - C6 N6; unfold kBatchSize in *; lia|].
    apply Forall_app. split; [exact C7| exact N7].
  Qed.
  Lemma bok_mnx : forall nx, bok nx -> bok (mnx nx).
  Proof.
    intros nx (N1 & N2 & N3 & N4 & N5 & N6 & N7). unfold bok, mnx. cbn [qb_addr qb_size qb_count qb_chunks].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [unfold kBatchCount; clear; lia|]. split; [reflexivity|]. split; [clear; lia| constructor].
  Qed.
  Lemma subl_m : forall done cur nx rest ex,
    (forall b, In b (done ++ cur :: nx :: rest ++ ex) -> In (qb_addr b) (map qb_addr l)) ->
    forall b, In b (done ++ mcur cur nx :: rest ++ ex ++ [mnx nx]) -> In (qb_addr b) (map qb_addr l).
  Proof.
    intros done cur nx rest ex SUBL b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply SUBL; apply in_or_app; left; exact Hb|].
    destruct Hb as [<-|Hb]; [apply (SUBL cur); apply in_or_app; right; left; reflexivity|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply SUBL; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb|].
    destruct Hb as [<-|[]]. apply (SUBL nx). apply in_or_app; right; right; left; reflexivity.
  Qed.
  Lemma nd_m : forall done cur nx rest ex,
    List.NoDup (map qb_addr (done ++ cur :: nx :: rest ++ ex)) -> List.NoDup (map qb_addr (done ++ mcur cur nx :: rest ++ ex ++ [mnx nx])).
  Proof.
    intros done cur nx rest ex ND. rewrite map_app in ND. cbn [map] in ND. rewrite map_app in ND.
    rewrite map_app. cbn [map]. rewrite !map_app. cbn [map mcur mnx qb_addr]. rewrite app_assoc. exact (nd_move _ _ _ _ ND).
  Qed.

  (* [comment removed for export] *)
  Lemma mb_tail3 : forall done cur nx rest ex xb (t1 t2 t3 t4 t5 : word) (m3 : mem),
    mq_kont (length rest) ->
    mq_pure done cur nx rest ex xb ->
    mem_inv asegs m3 -> munch Wtot m m3 -> wmono asegs m m3 -> stk asegs m3 lo (bv_unsigned sp + -16) ->
    mq_mem3 m3 done cur nx rest ex xb ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) t1 t2 s0 s1 (wz A) (wz T) (wz xb) (wz (zlen ex + 1)) (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199054) fc None m3 (seg_rom asegs)).
  Proof.
    intros done cur nx rest ex xb t1 t2 t3 t4 t5 m3 KONT PURE MI1 MU1 WM1 ST1 MEM.
    destruct PURE as ([fuel MODEL] & OKD & OKC & OKN & OKR & OKE & EXE & SUBL & ND & K & SZB & XBE & XBB & LENB).
    destruct MEM as (FR & HA & HT & DONE & CUR & CURA & CURJ & CURP & NXC & NXJ & NXP & RESTS & EX).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof OKC as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof OKN as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    assert (Z0 : 0 <= zlen done /\ 0 <= zlen rest /\ 0 <= zlen ex /\ 0 <= zlen l) by (unfold zlen; clear; lia).
    pose proof (bsum_nonneg rest OKR) as BS0.
    assert (LENC : Z.of_nat (length (wlist (qb_chunks cur ++ qb_chunks nx))) = qb_count cur + qb_count nx).
    { unfold wlist. rewrite length_map, length_app. unfold zlen in C5, N5. clear - C5 N5. lia. }
    assert (INC : In (qb_addr cur) (map qb_addr l)) by (apply (SUBL cur); apply in_or_app; right; left; reflexivity).
    assert (INN : In (qb_addr nx) (map qb_addr l)) by (apply (SUBL nx); apply in_or_app; right; right; left; reflexivity).
    assert (SUBD : forall b, In b done -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; left; exact Hb).
    assert (SUBR : forall b, In b rest -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
    assert (SUBE : forall b, In b ex -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    hide_hyp MU1. pose proof (munch_refl [(T, T + 32)] m3) as MUL. pose proof (wmono_refl asegs m3) as WML.
    assert (FW : forall L, Forall (ifar L) [(T, T + 32)]) by (intros L; constructor; [unfold ifar; right; left; clear - TR HI LO; lia| constructor]).
    assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(T, T + 32)]) by (constructor; [cbn [fst snd]; right; clear - TR HI LO; acb; unfold AHI_LO; lia| constructor]).
    unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *. acb.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU1.
    match type of MUL with munch _ _ ?mN => assert (MU3 : munch Wtot m mN) by (eapply munch_trans; [exact MU1|]; eapply munch_weaken; [| exact MUL]; intros x Hx; unfold Wtot in Hx; cbn [outside] in Hx |- *; clear - Hx; tauto) end.
    if_cases Kz; zify_cond Kz.
    - (* [comment removed for export] *)
      destruct rest as [|nx2 rest2]. { exfalso. revert Kz. cbn [map hd]. rewrite ?unsigned_lit by (clear; lia). intros Kz'; apply Kz'; reflexivity. }
      cbn [map hd] in CUR |- *.
      eapply (KONT done (mcur cur nx) nx2 rest2 (ex ++ [mnx nx]) (xb + 8192)); clear KONT.
      + cbn [length]. clear. lia.
      + split. { exists fuel. exact MODEL. }
        split; [exact OKD|]. split; [apply bok_mcur; [exact OKC| exact OKN| exact K]|]. split; [exact OKR|].
        split; [apply Forall_app; split; [exact OKE| constructor; [apply bok_mnx; exact OKN| constructor]]|].
        split; [apply Forall_app; split; [exact EXE| constructor; [split; reflexivity| constructor]]|].
        split; [exact (subl_m _ _ _ _ _ SUBL)|].
        split; [exact (nd_m _ _ _ _ _ ND)|].
        unfold mcur; cbn [qb_size qb_addr qb_count]. unfold kBatchSize.
        split; [clear - SZB; lia|]. split; [rewrite zlen_app1; clear - XBE; lia|]. split; [rewrite zlen_cons' in XBB; clear - XBB; lia|].
        rewrite zlen_app1. rewrite zlen_cons' in LENB. clear - LENB. lia.
      + assumption.
      + exact MU3.
      + exact WM1.
      + assumption.
      + unfold mb_mem. cbn [qb_addr qb_size qb_count qb_chunks mcur mnx]. unfold kBatchSize.
        split; [exact FR|].
        split. { rewrite zlen_cons', last_cons in HA. rewrite (hd_addr done cur (mcur cur nx) eq_refl) in HA.
                 replace (zlen done + 2 + (1 + zlen rest2) - 1) with (zlen done + 2 + zlen rest2) in HA by (clear; lia). exact HA. }
        split. { rewrite zlen_app1, thdr_snd_snoc. replace (tb + (xb + 8192)) with (tb + xb + 8192) by (clear; lia). exact HT. }
        split. { eapply (bseg_far _ m3); [apply FW| exact OKD| exact SUBD| exact AGL| assumption| exact DONE]. }
        split; [exact CUR|]. split; [exact CURA|]. split; [exact CURJ|].
        split. { eapply (pois_far2 _ m3 _ cur); [exact FP| exact OKC| exact AGL| exact WML| exact CURP]. }
        split. { eapply (bseg_far _ m3); [apply FW| exact OKR| exact SUBR| exact AGL| assumption| exact RESTS]. }
        apply bseg_app. unfold mnx. cbn [map hd bseg qb_addr]. split.
        { eapply (bseg_far _ m3); [apply FW| exact OKE| exact SUBE| exact AGL| assumption| exact EX]. }
        split; [| exact I]. apply batch_close; cbn [qb_addr qb_size qb_count qb_chunks wlist map].
        * exact NXC.
        * apply mb_u64arr_nil; clear - N1 N2 ACEILB; lia.
        * replace (qb_addr nx + 24 + 8 * 0) with (qb_addr nx + 24) by (clear; lia). exact NXJ.
        * eapply (pois_far2 _ m3 _ nx); [exact FP| exact OKN| exact AGL| exact WML| exact NXP].
    - (* [comment removed for export] *)
      destruct rest as [|nx2 rest2].
      2: { exfalso. apply Forall_cons_iff in OKR. destruct OKR as [(Q1 & Q2 & _) _]. revert Kz. cbn [map hd]. unfold AHI_LO, kBatchSize in Q1, Q2.
           rewrite land64_id by (clear - Q1 Q2 ACEILB; lia). clear - Q1. lia. }
      cbn [map hd last] in HA, CUR |- *.
      destruct fuel as [|fuel]; [discriminate MODEL|]. cbn [merge_batches_aux] in MODEL.
      injection MODEL as ELF EEX EXB. cbn [rev] in ELF. rewrite rev_involutive in ELF. rewrite rev_involutive in EEX.
      eapply (mb_exit done (mcur cur nx) (ex ++ [mnx nx]) (xb + 8192)).
      + rewrite <- ELF. reflexivity.
      + symmetry; exact EEX.
      + symmetry; exact EXB.
      + exact OKD.
      + apply bok_mcur; [exact OKC| exact OKN| exact K].
      + apply Forall_app; split; [exact OKE| constructor; [apply bok_mnx; exact OKN| constructor]].
      + apply Forall_app; split; [exact EXE| constructor; [split; reflexivity| constructor]].
      + intros b Hb. apply (subl_m done cur nx [] ex SUBL b). exact Hb.
      + exact (nd_m done cur nx [] ex ND).
      + rewrite zlen_app1. unfold kBatchSize. clear - XBE; lia.
      + rewrite zlen_nil' in XBB. clear - XBB XBE Z0; lia.
      + assumption.
      + exact MU3.
      + exact WM1.
      + assumption.
      + exact FR.
      + rewrite (hd_addr done cur (mcur cur nx) eq_refl) in HA. rewrite zlen_nil' in HA.
        replace (zlen done + 2 + 0 - 1) with (zlen done + 1) in HA by (clear; lia). exact HA.
      + rewrite zlen_app1, thdr_snd_snoc. replace (tb + (xb + 8192)) with (tb + xb + 8192) by (clear; lia). exact HT.
      + unfold mcur; cbn [qb_addr]. eapply (bseg_far _ m3); [apply FW| exact OKD| exact SUBD| exact AGL| assumption| exact DONE].
      + unfold mcur; cbn [qb_addr qb_size qb_count]. unfold kBatchSize. exact CUR.
      + unfold mcur; cbn [qb_addr qb_chunks]. exact CURA.
      + unfold mcur; cbn [qb_addr qb_count]. unfold kBatchSize. exact CURJ.
      + unfold mcur; cbn [qb_addr]. eapply (pois_far2 _ m3 _ cur); [exact FP| exact OKC| exact AGL| exact WML| exact CURP].
      + apply bseg_app. unfold mnx. cbn [map hd bseg qb_addr]. split.
        { eapply (bseg_far _ m3); [apply FW| exact OKE| exact SUBE| exact AGL| assumption| exact EX]. }
        split; [| exact I]. apply batch_close; cbn [qb_addr qb_size qb_count qb_chunks wlist map].
        * exact NXC.
        * apply mb_u64arr_nil; clear - N1 N2 ACEILB; lia.
        * replace (qb_addr nx + 24 + 8 * 0) with (qb_addr nx + 24) by (clear; lia). exact NXJ.
        * eapply (pois_far2 _ m3 _ nx); [exact FP| exact OKN| exact AGL| exact WML| exact NXP].
  Qed.

  (* [comment removed for export] *)
  Lemma mb_pushB : forall done cur nx rest ex xb (t1 t2 t3 t4 t5 : word) (m3 : mem),
    mq_kont (length rest) ->
    mq_pure done cur nx rest ex xb -> ex = [] ->
    mem_inv asegs m3 -> munch Wtot m m3 -> wmono asegs m m3 -> stk asegs m3 lo (bv_unsigned sp + -16) ->
    mq_mem2 m3 done cur nx rest ex xb ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) t1 t2 s0 s1 (wz A) (wz T) (wz xb) (wz (zlen ex)) (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19904c) fc None m3 (seg_rom asegs)).
  Proof.
    intros done cur nx rest ex xb t1 t2 t3 t4 t5 m3 KONT PURE EXN MI1 MU1 WM1 ST1 MEM. pose proof PURE as PURE0.
    destruct PURE as (_ & OKD & OKC & OKN & OKR & OKE & EXE & SUBL & ND & K & SZB & XBE & XBB & LENB).
    unfold mq_mem2, mq_memK in MEM. destruct MEM as (FR & HA & HT & DONE & CUR & CURA & CURJ & CURP & NXC & NXJ & NXP & RESTS & EX).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof OKC as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof OKN as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    assert (LENC : Z.of_nat (length (wlist (qb_chunks cur ++ qb_chunks nx))) = qb_count cur + qb_count nx).
    { unfold wlist. rewrite length_map, length_app. unfold zlen in C5, N5. clear - C5 N5. lia. }
    assert (SUBD : forall b, In b done -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; left; exact Hb).
    assert (SUBR : forall b, In b rest -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
    hide_hyp MU1. pose proof (munch_refl [(T, T + 32)] m3) as MUL. pose proof (wmono_refl asegs m3) as WML.
    assert (FW : forall L, Forall (ifar L) [(T, T + 32)]) by (intros L; constructor; [unfold ifar; right; left; clear - TR HI LO; lia| constructor]).
    assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(T, T + 32)]) by (constructor; [cbn [fst snd]; right; clear - TR HI LO; acb; unfold AHI_LO; lia| constructor]).
    subst ex. unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *. acb.
    (* [comment removed for export] *)
    step. step.
    pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU1.
    match type of MUL with munch _ _ ?mN => assert (MU3 : munch Wtot m mN) by (eapply munch_trans; [exact MU1|]; eapply munch_weaken; [| exact MUL]; intros x Hx; unfold Wtot in Hx; cbn [outside] in Hx |- *; clear - Hx; tauto) end.
    eapply (mb_tail3 done cur nx rest [] xb); [exact KONT| exact PURE0| assumption| exact MU3| exact WM1| exact ST1|].
    unfold mq_mem3, mq_memK. unfold kBatchSize.
    split; [exact FR|]. split; [exact HA|]. split; [exact HT|].
    split; [eapply (bseg_far _ m3); [apply FW| exact OKD| exact SUBD| exact AGL| exact WML| exact DONE]|].
    split; [exact CUR|]. split; [exact CURA|]. split; [exact CURJ|].
    split; [eapply (pois_far2 _ m3 _ cur); [exact FP| exact OKC| exact AGL| exact WML| exact CURP]|].
    split; [exact NXC|]. split; [exact NXJ|].
    split; [eapply (pois_far2 _ m3 _ nx); [exact FP| exact OKN| exact AGL| exact WML| exact NXP]|].
    split; [eapply (bseg_far _ m3); [apply FW| exact OKR| exact SUBR| exact AGL| exact WML| exact RESTS]| exact I].
  Qed.


  (* [comment removed for export] *)
  Lemma nd_last : forall (d : list Z) c n (r : list qbatch) (exi : list qbatch) lx,
    List.NoDup (d ++ c :: n :: map qb_addr (r ++ exi ++ [lx])) ->
    forall a, (In a d \/ a = c \/ a = n \/ In a (map qb_addr r) \/ In a (map qb_addr exi)) -> a <> qb_addr lx.
  Proof.
    intros d c n r exi lx ND a Ha E. subst a. rewrite !map_app in ND. cbn [map] in ND.
    assert (ND' : List.NoDup ((d ++ c :: n :: map qb_addr r ++ map qb_addr exi) ++ qb_addr lx :: [])).
    { rewrite <- app_assoc. cbn [app]. rewrite <- !app_assoc. exact ND. }
    apply (NoDup_remove_2 _ [] _ ND'). rewrite app_nil_r. apply in_or_app.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [left; exact Ha| right; left; symmetry; exact Ha| right; right; left; symmetry; exact Ha| right; right; right; apply in_or_app; left; exact Ha| right; right; right; apply in_or_app; right; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma mb_pushA : forall done cur nx rest ex xb (t1 t2 t3 t4 t5 : word) (m3 : mem),
    mq_kont (length rest) ->
    mq_pure done cur nx rest ex xb -> ex <> [] ->
    mem_inv asegs m3 -> munch Wtot m m3 -> wmono asegs m m3 -> stk asegs m3 lo (bv_unsigned sp + -16) ->
    mq_mem2 m3 done cur nx rest ex xb ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) t1 t2 s0 s1 (wz A) (wz T) (wz xb) (wz (zlen ex)) (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199024) fc None m3 (seg_rom asegs)).
  Proof.
    intros done cur nx rest ex xb t1 t2 t3 t4 t5 m3 KONT PURE NE MI1 MU1 WM1 ST1 MEM. pose proof PURE as PURE0.
    destruct PURE as (_ & OKD & OKC & OKN & OKR & OKE & EXE & SUBL & ND & K & SZB & XBE & XBB & LENB).
    unfold mq_mem2, mq_memK in MEM. destruct MEM as (FR & HA & HT & DONE & CUR & CURA & CURJ & CURP & NXC & NXJ & NXP & RESTS & EX).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof OKC as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof OKN as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    assert (Z0 : 0 <= zlen done /\ 0 <= zlen rest /\ 0 <= zlen ex /\ 0 <= zlen l) by (unfold zlen; clear; lia).
    assert (LENC : Z.of_nat (length (wlist (qb_chunks cur ++ qb_chunks nx))) = qb_count cur + qb_count nx).
    { unfold wlist. rewrite length_map, length_app. unfold zlen in C5, N5. clear - C5 N5. lia. }
    assert (INC : In (qb_addr cur) (map qb_addr l)) by (apply (SUBL cur); apply in_or_app; right; left; reflexivity).
    assert (INN : In (qb_addr nx) (map qb_addr l)) by (apply (SUBL nx); apply in_or_app; right; right; left; reflexivity).
    assert (SUBD : forall b, In b done -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; left; exact Hb).
    assert (SUBR : forall b, In b rest -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
    assert (SUBE : forall b, In b ex -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    pose proof (app_removelast_last nx NE) as EXS. set (exi := removelast ex) in EXS. set (lx := last ex nx) in EXS. clearbody exi lx.
    assert (INLX : In lx ex) by (rewrite EXS; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) OKE lx INLX) as OKX. pose proof OKX as (L1 & L2 & L3 & L4 & L5 & L6 & L7). pose proof (SUBE lx INLX) as INL.
    assert (SUBI : forall b, In b exi -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBE; rewrite EXS; apply in_or_app; left; exact Hb).
    assert (OKI : Forall bok exi) by (apply (proj2 (Forall_forall _ _)); intros b Hb; apply (proj1 (Forall_forall _ _) OKE); rewrite EXS; apply in_or_app; left; exact Hb).
    rewrite map_app in ND. cbn [map] in ND. rewrite EXS in ND. pose proof (nd_last _ _ _ _ _ _ ND) as NDL.
    assert (XC : qb_addr cur <> qb_addr lx) by (apply NDL; right; left; reflexivity).
    assert (XN : qb_addr nx <> qb_addr lx) by (apply NDL; right; right; left; reflexivity).
    (* [comment removed for export] *)
    pose proof (PW _ _ INC INL XC) as DXC; pose proof (PW _ _ INN INL XN) as DXN.
    all: rewrite EXS in EX; apply bseg_app in EX; destruct EX as [EXI LXB]; cbn [map hd bseg] in EXI, LXB; destruct LXB as [LXB _].
    all: destruct (batch_open m3 lx 0 OKX LXB) as (LXC & LXA & LXJ & LXP); clear LXB.
    all: assert (LENX : Z.of_nat (length (wlist (qb_chunks lx))) = qb_count lx) by (unfold wlist; rewrite length_map; unfold zlen in L5; clear - L5; lia).
    all: assert (TS : snd (thdr f0 l0 ex) = wz (qb_addr lx)) by (rewrite EXS; apply thdr_snd_snoc); rewrite TS in HT.
    all: hide_hyp MU1; pose proof (munch_refl [(qb_addr lx, qb_addr lx + 8)] m3) as MUL; pose proof (wmono_refl asegs m3) as WML.
    all: assert (FW : forall L, (forall b, In b L -> qb_addr b <> qb_addr lx) -> Forall (ifar L) [(qb_addr lx, qb_addr lx + 8)]) by (intros L HL; constructor; [unfold ifar; right; right; exists (qb_addr lx); split; [exact INL| split; [clear; lia| split; [unfold kBatchSize; clear; lia| exact HL]]]| constructor]).
    all: assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(qb_addr lx, qb_addr lx + 8)]) by (constructor; [cbn [fst snd]; right; exact L1| constructor]).
    all: unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *; acb.
    (* [comment removed for export] *)
    all: step; step; step; step.
    all: pose proof (munch_agree _ _ _ MUL) as AGL; unhide_hyp MU1.
    all: match type of MUL with munch _ _ ?mN => assert (MU3 : munch Wtot m mN) by (eapply munch_trans; [exact MU1|]; eapply munch_weaken; [| exact MUL]; intros x Hx; unfold Wtot in Hx; cbn [outside] in Hx |- *; destruct Hx as (_ & _ & _ & Hx); split; [| exact I]; pose proof (outside_bext l x _ Hx INL) as Q; clear - Q; unfold kBatchSize in Q; lia) end.
    all: eapply (mb_tail3 done cur nx rest ex xb); [exact KONT| exact PURE0| assumption| exact MU3| exact WM1| exact ST1|].
    all: unfold mq_mem3, mq_memK; unfold kBatchSize; rewrite (thdr_fst_snoc ex _ NE), TS.
    all: split; [exact FR|]; split; [exact HA|]; split; [exact HT|].
    all: split; [eapply (bseg_far _ m3); [apply FW; intros b Hb; apply NDL; left; apply in_map; exact Hb| exact OKD| exact SUBD| exact AGL| exact WML| exact DONE]|].
    all: split; [exact CUR|]; split; [exact CURA|]; split; [exact CURJ|].
    all: split; [eapply (pois_far2 _ m3 _ cur); [exact FP| exact OKC| exact AGL| exact WML| exact CURP]|].
    all: split; [exact NXC|]; split; [exact NXJ|].
    all: split; [eapply (pois_far2 _ m3 _ nx); [exact FP| exact OKN| exact AGL| exact WML| exact NXP]|].
    all: split; [eapply (bseg_far _ m3); [apply FW; intros b Hb; apply NDL; right; right; right; left; apply in_map; exact Hb| exact OKR| exact SUBR| exact AGL| exact WML| exact RESTS]|].
    all: rewrite EXS; apply bseg_app; cbn [map hd bseg]; split; [eapply (bseg_far _ m3); [apply FW; intros b Hb; apply NDL; right; right; right; right; apply in_map; exact Hb| exact OKI| exact SUBI| exact AGL| exact WML| exact EXI]|].
    all: split; [| exact I]; apply batch_close; [exact LXC| exact LXA| exact LXJ|].
    all: eapply (poisoned_transport_pt _ m3 _ AGL WML); [exact LXP|]; intros a Ha; cbn [outside]; split; [| exact I]; clear - Ha L1 L2 ACEILB; unfold sh, ASHADOW_BASE, kBatchSize in *; lia.
  Qed.


  Lemma last_in : forall (r : list qbatch) d, r <> [] -> In (last r d) r.
  Proof.
    intros r. induction r as [|x r IH]; intros d NE; [exact (NE eq_refl)|].
    destruct r as [|y r']; [left; reflexivity|]. right. apply (IH d). discriminate.
  Qed.

  (* [comment removed for export] *)
  Ltac mb_tail_leaf cur nx PUSH HNE MUL MU1 INC INN KONT PURE0 WM1 ST1 FR HA HT FW NDD OKD SUBD DONE CUR CURA CURJ FP OKC CURP NXC NXJ OKN NXP NDR OKR SUBR RESTS NDE OKE SUBE EX :=
    let AGL := fresh "AGL" in let MU3 := fresh "MU3" in
    pose proof (munch_agree _ _ _ MUL) as AGL; unhide_hyp MU1;
    lazymatch type of MUL with munch _ _ ?mN =>
      assert (MU3 : munch Wtot m mN)
        by (eapply munch_trans; [exact MU1|]; eapply munch_weaken; [| exact MUL];
            let x := fresh "x" in let Hx := fresh "Hx" in let HxA := fresh "HxA" in let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in
            intros x Hx; unfold Wtot in Hx; cbn [outside] in Hx |- *;
            destruct Hx as (_ & HxA & _ & Hx); pose proof (outside_bext l x _ Hx INC) as Q1; pose proof (outside_bext l x _ Hx INN) as Q2;
            clear - HxA Q1 Q2; unfold kBatchSize in Q1, Q2; lia)
    end;
    eapply PUSH; [exact KONT| exact PURE0| exact HNE| assumption| exact MU3| exact WM1| exact ST1|];
    unfold mq_mem2, mq_memK; unfold kBatchSize;
    split; [exact FR|]; split; [exact HA|]; split; [exact HT|];
    split; [eapply (bseg_far _ _); [apply FW; exact NDD| exact OKD| exact SUBD| exact AGL| assumption| exact DONE]|];
    split; [exact CUR|]; split; [exact CURA|]; split; [exact CURJ|];
    split; [eapply (pois_far2 _ _ _ cur); [exact FP| exact OKC| exact AGL| assumption| exact CURP]|];
    split; [exact NXC|]; split; [exact NXJ|];
    split; [eapply (pois_far2 _ _ _ nx); [exact FP| exact OKN| exact AGL| assumption| exact NXP]|];
    split; [eapply (bseg_far _ _); [apply FW; exact NDR| exact OKR| exact SUBR| exact AGL| assumption| exact RESTS]|];
    eapply (bseg_far _ _); [apply FW; exact NDE| exact OKE| exact SUBE| exact AGL| assumption| exact EX].

  (* [comment removed for export] *)
  Lemma mb_tail : forall done cur nx rest ex xb (t2 t3 t4 t5 : word) (m2 : mem),
    mq_kont (length rest) ->
    mq_pure done cur nx rest ex xb ->
    mem_inv asegs m2 -> munch Wtot m m2 -> wmono asegs m m2 -> stk asegs m2 lo (bv_unsigned sp + -16) ->
    mq_mem1 m2 done cur nx rest ex xb ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) (wz (qb_count nx + qb_count cur)) t2 s0 s1 (wz A) (wz T) (wz xb) (wz (qb_size cur)) (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x198fdc) fc None m2 (seg_rom asegs)).
  Proof.
    intros done cur nx rest ex xb t2 t3 t4 t5 m2 KONT PURE MI1 MU1 WM1 ST1 MEM. pose proof PURE as PURE0.
    destruct PURE as (_ & OKD & OKC & OKN & OKR & OKE & EXE & SUBL & ND & K & SZB & XBE & XBB & LENB).
    destruct MEM as (FR & HA & HT & DONE & CUR & CURA & CURJ & CURP & NXC & NXA & NXJ & NXP & RESTS & EX).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof OKC as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof OKN as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    assert (Z0 : 0 <= zlen done /\ 0 <= zlen rest /\ 0 <= zlen ex /\ 0 <= zlen l) by (unfold zlen; clear; lia).
    pose proof (bsum_nonneg rest OKR) as BS0.
    assert (LENC : Z.of_nat (length (wlist (qb_chunks cur ++ qb_chunks nx))) = qb_count cur + qb_count nx).
    { unfold wlist. rewrite length_map, length_app. unfold zlen in C5, N5. clear - C5 N5. lia. }
    assert (LENN : Z.of_nat (length (wlist (qb_chunks nx))) = qb_count nx) by (unfold wlist; rewrite length_map; unfold zlen in N5; clear - N5; lia).
    assert (INC : In (qb_addr cur) (map qb_addr l)) by (apply (SUBL cur); apply in_or_app; right; left; reflexivity).
    assert (INN : In (qb_addr nx) (map qb_addr l)) by (apply (SUBL nx); apply in_or_app; right; right; left; reflexivity).
    assert (SUBD : forall b, In b done -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; left; exact Hb).
    assert (SUBR : forall b, In b rest -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
    assert (SUBE : forall b, In b ex -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb).
    rewrite map_app in ND. cbn [map] in ND. rewrite map_app in ND. destruct (nd_facts _ _ _ _ ND) as [CN NDF].
    pose proof (PW _ _ INC INN CN) as DCN.
    assert (NDD : forall b, In b done -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF; apply in_or_app; left; apply in_map; exact Hb).
    assert (NDR : forall b, In b rest -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF; apply in_or_app; right; apply in_or_app; left; apply in_map; exact Hb).
    assert (NDE : forall b, In b ex -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF; apply in_or_app; right; apply in_or_app; right; apply in_map; exact Hb).
    (* [comment removed for export] *)
    pose proof (stk_of_u64arr _ _ _ NXA) as NXS; rewrite LENN in NXS; clear NXA; pose proof (stk_merge asegs _ _ _ _ NXS NXJ ltac:(clear - N4; unfold kBatchCount, kBatchSize in *; lia)) as NXJ'; clear NXS NXJ; rename NXJ' into NXJ.
    hide_hyp MU1; pose proof (munch_refl [(qb_addr cur, qb_addr cur + 24); (qb_addr nx, qb_addr nx + 24); (A, A + 32)] m2) as MUL; pose proof (wmono_refl asegs m2) as WML.
    assert (FW : forall L, (forall b, In b L -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) -> Forall (ifar L) [(qb_addr cur, qb_addr cur + 24); (qb_addr nx, qb_addr nx + 24); (A, A + 32)]) by (intros L HL; constructor; [unfold ifar; right; right; exists (qb_addr cur); split; [exact INC| split; [clear; lia| split; [unfold kBatchSize; clear; lia| intros b Hb; exact (proj1 (HL b Hb))]]]| constructor; [unfold ifar; right; right; exists (qb_addr nx); split; [exact INN| split; [clear; lia| split; [unfold kBatchSize; clear; lia| intros b Hb; exact (proj2 (HL b Hb))]]]| constructor; [unfold ifar; left; exact (proj1 (proj2 AR))| constructor]]]).
    assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(qb_addr cur, qb_addr cur + 24); (qb_addr nx, qb_addr nx + 24); (A, A + 32)]) by (constructor; [cbn [fst snd]; right; exact C1| constructor; [cbn [fst snd]; right; exact N1| constructor; [cbn [fst snd]; left; exact (proj1 (proj2 AR))| constructor]]]).
    assert (A6U : bv_unsigned a6 = 2^64 - 8192) by (clear - A6; destruct A6 as [-> | ->]; rewrite unsigned_lit_wrap; reflexivity).
    replace (qb_count nx + qb_count cur) with (qb_count cur + qb_count nx) by (clear; lia).
    unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *; acb.
    (* [comment removed for export] *)
    step. step. step. step.
    replace (Z_to_bv 64 (qb_size cur + qb_size nx + bv_unsigned a6)) with (Z_to_bv 64 (qb_size cur + (qb_size nx - 8192))) by (apply Z_to_bv_eqm; rewrite A6U; replace (qb_size cur + qb_size nx + (2 ^ 64 - 8192)) with (qb_size cur + (qb_size nx - 8192) + 1 * 2 ^ 64) by (clear; lia); rewrite Z_mod_plus_full; reflexivity).
    (* [comment removed for export] *)
    step. step. step; fix_lit_store. step; fix_lit_store. step.
    if_cases Ka; zify_cond Ka; [exfalso; revert Ka; rewrite ?unsigned_lit, ?land64_id by (clear - Z0 LENB LLEN QBR; lia); clear - Z0 LENB; lia|]; clear Ka.
    (* [comment removed for export] *)
    step. step. step. step.
    if_cases Kr; zify_cond Kr.
    - (* [comment removed for export] *)
      destruct rest as [|nx2 rest2].
      2: { exfalso. pose proof (last_in (nx2 :: rest2) nx ltac:(discriminate)) as IL. pose proof (proj1 (Forall_forall _ _) OKR _ IL) as (Q1 & Q2 & _).
           unfold AHI_LO, kBatchSize in Q1, Q2. rewrite land64_id in Kr by (clear - Q1 Q2 ACEILB; lia). exact (proj2 (NDR _ IL) Kr). }
      cbn [map hd last] in HA, CUR, NXC, KONT, PURE0 |- *.
      (* [comment removed for export] *)
      step. step. step. step. step; fix_lit_store. step.
      match type of HA with rw_cells _ _ _ (C8 (Z_to_bv 64 ?v) :: _) => replace v with (zlen done + 2 + zlen (@nil qbatch) - 1) in HA by (clear; lia) end.
      if_cases Ke; zify_cond Ke; rewrite ?land64_id in Ke by (clear - Z0 LENB LLEN QBR; lia).
      + assert (NE : ex <> []) by (intros E; subst ex; exact (Ke eq_refl)).
        mb_tail_leaf cur nx (mb_pushA done cur nx [] ex xb) NE MUL MU1 INC INN KONT PURE0 WM1 ST1 FR HA HT FW NDD OKD SUBD DONE CUR CURA CURJ FP OKC CURP NXC NXJ OKN NXP NDR OKR SUBR RESTS NDE OKE SUBE EX.
      + assert (EXN : ex = []) by (destruct ex as [|b ex']; [reflexivity| exfalso; revert Ke; unfold zlen; cbn [length]; clear; lia]).
        mb_tail_leaf cur nx (mb_pushB done cur nx [] ex xb) EXN MUL MU1 INC INN KONT PURE0 WM1 ST1 FR HA HT FW NDD OKD SUBD DONE CUR CURA CURJ FP OKC CURP NXC NXJ OKN NXP NDR OKR SUBR RESTS NDE OKE SUBE EX.
    - (* [comment removed for export] *)
      assert (NE' : rest <> []) by (intros E; subst rest; cbn [last] in Kr; rewrite land64_id in Kr by (clear - N1 N2 ACEILB; lia); exact (Kr eq_refl)).
      rewrite (last_cons_any rest nx cur NE') in HA.
      (* [comment removed for export] *)
      step. step. step. step; fix_lit_store. step.
      match type of HA with rw_cells _ _ _ (C8 (Z_to_bv 64 ?v) :: _) => replace v with (zlen done + 2 + zlen rest - 1) in HA by (clear; lia) end.
      if_cases Ke; zify_cond Ke; rewrite ?land64_id in Ke by (clear - Z0 LENB LLEN QBR; lia).
      + assert (EXN : ex = []) by (destruct ex as [|b ex']; [reflexivity| exfalso; revert Ke; unfold zlen; cbn [length]; clear; lia]).
        mb_tail_leaf cur nx (mb_pushB done cur nx rest ex xb) EXN MUL MU1 INC INN KONT PURE0 WM1 ST1 FR HA HT FW NDD OKD SUBD DONE CUR CURA CURJ FP OKC CURP NXC NXJ OKN NXP NDR OKR SUBR RESTS NDE OKE SUBE EX.
      + assert (NE : ex <> []) by (intros E; subst ex; exact (Ke eq_refl)).
        mb_tail_leaf cur nx (mb_pushA done cur nx rest ex xb) NE MUL MU1 INC INN KONT PURE0 WM1 ST1 FR HA HT FW NDD OKD SUBD DONE CUR CURA CURJ FP OKC CURP NXC NXJ OKN NXP NDR OKR SUBR RESTS NDE OKE SUBE EX.
  Qed.
  Lemma mb_loop : forall (k : nat) done cur nx rest ex xb (t1 t2 t3 t4 t5 a3 : word) (m1 : mem),
    (length rest < k)%nat ->
    mb_pure done cur nx rest ex xb ->
    mem_inv asegs m1 -> munch Wtot m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -16) ->
    mb_mem m1 done cur nx rest ex xb ->
    evt asegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (wz (qb_addr nx)) t1 t2 s0 s1 (wz A) (wz T) (wz xb) a3 (wz (qb_addr cur)) (wz 1021) a6 (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x198f90) fc None m1 (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros done cur nx rest ex xb t1 t2 t3 t4 t5 a3 m1 HK PURE MI1 MU1 WM1 ST1 MEM. { exfalso. clear - HK. lia. }
    destruct PURE as ([fuel MODEL] & OKD & OKC & OKR & OKE & EXE & SUBL & ND & SZB & XBE & XBB & LENB).
    destruct MEM as (FR & HA & HT & DONE & CUR & CURA & CURJ & CURP & NXS & EX).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    cbn [bseg] in NXS. destruct NXS as [NXB RESTS].
    pose proof OKR as OKR0. apply Forall_cons_iff in OKR. destruct OKR as [OKN OKR'].
    destruct (batch_open m1 nx _ OKN NXB) as (NXC & NXA & NXJ & NXP). clear NXB.
    pose proof OKC as (C1 & C2 & C3 & C4 & C5 & C6 & C7). pose proof OKN as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
    (* [comment removed for export] *)
    destruct fuel as [|fuel]; [discriminate MODEL|]. cbn [merge_batches_aux] in MODEL.
    unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP, wz in *. unfold Wtot in MU1. acb.
    assert (LENC : Z.of_nat (length (wlist (qb_chunks cur))) = qb_count cur) by (unfold wlist; rewrite length_map; unfold zlen in C5; clear - C5; lia).
    assert (LENN : Z.of_nat (length (wlist (qb_chunks nx))) = qb_count nx) by (unfold wlist; rewrite length_map; unfold zlen in N5; clear - N5; lia).
    assert (BS0 : 0 <= bsum rest).
    { clear - OKR'. induction rest as [|b r IHr]; [change (bsum []) with 0; lia|]. apply Forall_cons_iff in OKR'. destruct OKR' as [(_ & _ & _ & _ & _ & Q6 & _) Hr].
      change (bsum (b :: r)) with (qb_size b + bsum r). specialize (IHr Hr). clear - Q6 IHr. unfold kBatchSize in Q6. lia. }
    change (bsum (nx :: rest)) with (qb_size nx + bsum rest) in SZB.
    (* [comment removed for export] *)
    step. step. step. step.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (qb_count cur + qb_count nx <=? 1021) with false in MODEL by (symmetry; apply Z.leb_gt; clear - K; lia).
      (* [comment removed for export] *)
      step. step.
      assert (DONE' : bseg m1 (done ++ [cur]) (qb_addr nx)).
      { apply bseg_app. cbn [map hd bseg]. split; [exact DONE|]. split; [| exact I]. apply batch_close; assumption. }
      destruct rest as [|nx2 rest2].
      + (* [comment removed for export] *)
        cbn [map hd last] in *. step. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. } clear K2.
        destruct fuel as [|fuel]; [discriminate MODEL|]. cbn [merge_batches_aux] in MODEL.
        injection MODEL as ELF EEX EXB. cbn [rev] in ELF. rewrite rev_involutive in ELF. rewrite rev_involutive in EEX.
        eapply (mb_exit (done ++ [cur]) nx ex xb); try eassumption.
        * rewrite <- ELF. reflexivity.
        * symmetry; exact EEX.
        * symmetry; exact EXB.
        * apply Forall_app. split; [exact OKD| constructor; [exact OKC| constructor]].
        * intros b Hb. apply SUBL. rewrite <- app_assoc in Hb. exact Hb.
        * rewrite <- app_assoc. exact ND.
        * clear - XBB XBE BS0; unfold zlen in *; cbn [length] in *; lia.
        * rewrite zlen_app1, hd_app1. replace (zlen done + 1 + 1) with (zlen done + 2 + 0) by (clear; lia). exact HA.
      + (* [comment removed for export] *)
        cbn [map hd] in NXC |- *. step. if_cases K2; zify_cond K2. { exfalso. apply Forall_cons_iff in OKR'. destruct OKR' as [(Q1 & Q2 & _) _]. unfold AHI_LO, kBatchSize in Q1, Q2. revert K2. rewrite ?unsigned_lit, ?land64_id by (clear - Q1 Q2 ACEILB; lia). clear - Q1. lia. } clear K2.
        eapply (IH (done ++ [cur]) nx nx2 rest2 ex xb); try eassumption.
        * cbn [length] in HK. clear - HK. lia.
        * split; [exists fuel; rewrite rev_app_distr; cbn [rev app]; exact MODEL|].
          split; [apply Forall_app; split; [exact OKD| constructor; [exact OKC| constructor]]|].
          split; [exact OKN|]. split; [exact OKR'|]. split; [exact OKE|]. split; [exact EXE|].
          split; [intros b Hb; apply SUBL; rewrite <- app_assoc in Hb; exact Hb|].
          split; [rewrite <- app_assoc; exact ND|].
          split; [clear - SZB C6; lia|].
          split; [exact XBE|]. unfold kBatchSize. split; [clear - XBB; unfold zlen in *; cbn [length] in *; lia|].
          rewrite zlen_app1. rewrite zlen_cons' in LENB. clear - LENB. lia.
        * split; [exact FR|]. split.
          { rewrite zlen_app1, hd_app1. replace (zlen done + 1 + 2 + zlen rest2) with (zlen done + 2 + zlen (nx2 :: rest2)) by (unfold zlen; cbn [length]; clear; lia).
            rewrite last_cons in HA. exact HA. }
          split; [exact HT|]. split; [exact DONE'|]. split; [exact NXC|]. split; [exact NXA|]. split; [exact NXJ|]. split; [exact NXP|]. split; [exact RESTS| exact EX].
    - (* [comment removed for export] *)
      replace (qb_count cur + qb_count nx <=? 1021) with true in MODEL by (symmetry; apply Z.leb_le; clear - K; lia).
      replace (qb_size cur <? 8192) with false in MODEL by (symmetry; apply Z.ltb_ge; clear - C6; lia).
      assert (INC : In (qb_addr cur) (map qb_addr l)) by (apply (SUBL cur); apply in_or_app; right; left; reflexivity).
      assert (INN : In (qb_addr nx) (map qb_addr l)) by (apply (SUBL nx); apply in_or_app; right; right; left; reflexivity).
      assert (CN : qb_addr cur <> qb_addr nx).
      { pose proof ND as ND'. rewrite map_app in ND'. cbn [map] in ND'. rewrite map_app in ND'. exact (proj1 (nd_facts _ _ _ _ ND')). }
      pose proof (PW _ _ INC INN CN) as DCN.
      assert (PUREQ : mq_pure done cur nx rest ex xb).
      { split; [exists fuel; rewrite rev_app_distr; cbn [rev app]; exact MODEL|].
        split; [exact OKD|]. split; [exact OKC|]. split; [exact OKN|]. split; [exact OKR'|]. split; [exact OKE|]. split; [exact EXE|].
        split; [exact SUBL|]. split; [exact ND|]. split; [clear - K; unfold kBatchCount; lia|].
        unfold kBatchSize. split; [clear - SZB; lia|]. split; [exact XBE|]. split; [exact XBB| exact LENB]. }
      assert (KONT : mq_kont (length rest)).
      { intros done' cur' nx' rest' ex' xb' t1' t2' t3' t4' t5' a3' m1' HL. apply IH. clear - HL HK. cbn [length] in HK. lia. }
      (* [comment removed for export] *)
      step. step. step. if_cases K1; zify_cond K1.
      { exfalso. revert K1. rewrite ?unsigned_lit, ?land64_id by (clear - C6 SZB QBR BS0 N6; lia). rewrite Z.shiftr_div_pow2 by (clear; lia). clear - C6 SZB QBR BS0 N6. intros K1. Z.div_mod_to_equations. lia. }
      clear K1. step. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        assert (CH0 : qb_chunks nx = []) by (destruct (qb_chunks nx) as [|c cs]; [reflexivity| exfalso; unfold zlen in N5; cbn [length] in N5; clear - N5 K0; lia]).
        eapply (mb_tail done cur nx rest ex xb); [exact KONT| exact PUREQ| exact MI1| exact MU1| exact WM1| exact ST1|].
        split; [exact FR|]. split; [exact HA|]. split; [exact HT|]. split; [exact DONE|]. split; [exact CUR|].
        split; [rewrite CH0, app_nil_r; exact CURA|]. split; [rewrite K0, Z.add_0_r; exact CURJ|]. split; [exact CURP|].
        split; [exact NXC|]. split; [exact NXA|]. split; [exact NXJ|]. split; [exact NXP|]. split; [exact RESTS| exact EX].
      + (* [comment removed for export] *)
        (* [comment removed for export] *)
        step. step. step. step. step. step.
        rewrite !unsigned_lit by (clear - C4 N4; lia). rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
        replace (Z_to_bv 64 (qb_addr nx + 24)) with (Z_to_bv 64 (qb_addr nx + 24 + 8 * 0)) by (f_equal; clear; lia).
        replace (Z_to_bv 64 (qb_addr cur + qb_count cur * 8 + 24)) with (Z_to_bv 64 (qb_addr cur + 24 + 8 * qb_count cur + 8 * 0)) by (f_equal; clear; lia).
        replace (Z_to_bv 64 (qb_addr nx + 24 + qb_count nx * 8)) with (Z_to_bv 64 (qb_addr nx + 24 + 8 * qb_count nx)) by (f_equal; clear; lia).
        destruct (stk_split asegs _ _ (qb_addr cur + 24 + 8 * qb_count cur + 8 * qb_count nx) _ CURJ ltac:(clear - C4 N4 K; lia)) as [JK CURJ']. clear CURJ.
        assert (NDF' : forall a, In a (map qb_addr done ++ map qb_addr rest ++ map qb_addr ex) -> a <> qb_addr cur /\ a <> qb_addr nx).
        { pose proof ND as ND'. rewrite map_app in ND'. cbn [map] in ND'. rewrite map_app in ND'. exact (proj2 (nd_facts _ _ _ _ ND')). }
        assert (NDD : forall b, In b done -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF'; apply in_or_app; left; apply in_map; exact Hb).
        assert (NDR : forall b, In b rest -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF'; apply in_or_app; right; apply in_or_app; left; apply in_map; exact Hb).
        assert (NDE : forall b, In b ex -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) by (intros b Hb; apply NDF'; apply in_or_app; right; apply in_or_app; right; apply in_map; exact Hb).
        assert (SUBD : forall b, In b done -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; left; exact Hb).
        assert (SUBR : forall b, In b rest -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
        assert (SUBE : forall b, In b ex -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUBL; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb).
        assert (FW : forall L, (forall b, In b L -> qb_addr b <> qb_addr cur /\ qb_addr b <> qb_addr nx) -> Forall (ifar L) [(qb_addr cur, qb_addr cur + 8192)]) by (intros L HL; constructor; [unfold ifar; right; right; exists (qb_addr cur); split; [exact INC| split; [clear; lia| split; [unfold kBatchSize; clear; lia| intros b Hb; exact (proj1 (HL b Hb))]]]| constructor]).
        assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(qb_addr cur, qb_addr cur + 8192)]) by (constructor; [cbn [fst snd]; right; unfold AHI_LO; exact C1| constructor]).
        assert (WSL : length (wlist (qb_chunks nx)) = Z.to_nat (qb_count nx)) by (unfold wlist; rewrite length_map; unfold zlen in N5; clear - N5; lia).
        hide_hyp MU1. pose proof (munch_refl [(qb_addr cur, qb_addr cur + 8192)] m1) as MUL. pose proof (wmono_refl asegs m1) as WML.
        eapply evt_cut.
        { eapply mb_copy.
          - unfold AHI_LO; clear - N1 N2 N3 N4; lia.
          - unfold AHI_LO; clear - C1 C2 C3 C4 N4 K; lia.
          - clear - DCN C4 N4 K; lia.
          - clear - N4 K0; lia.
          - exact WSL.
          - rewrite Z.sub_0_r. reflexivity.
          - clear - N4 K0; lia.
          - exact MI1.
          - apply munch_refl.
          - apply wmono_refl.
          - rewrite Z.add_0_r. exact JK.
          - change (Z.to_nat 0) with 0%nat. cbn [firstn]. apply mb_u64arr_nil; clear - C1 C2 C4 ACEILB; lia.
          - exact NXA. }
        intros ms' PC. unfold mb_copy_post in PC. destruct PC as (t5' & m' & -> & MUc & WMc & MIc & ARRD & ARRS).
        transport_after_call asegs m1 m' MUc WMc. clear MI1.
        pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU1.
        assert (MU3 : munch Wtot m m').
        { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MUL]. intros x Hx. unfold Wtot in Hx. cbn [outside] in Hx |- *.
          destruct Hx as (_ & _ & _ & Hx). pose proof (outside_bext l x _ Hx INC) as Q1. clear - Q1. unfold kBatchSize in Q1. split; [lia| exact I]. }
        eapply (mb_tail done cur nx rest ex xb); [exact KONT| exact PUREQ| exact MIc| exact MU3| exact WM1| exact ST1|].
        split; [exact FR|]. split; [exact HA|]. split; [exact HT|].
        split; [eapply (bseg_far _ m1); [apply FW; exact NDD| exact OKD| exact SUBD| exact AGL| exact WML| exact DONE]|].
        split; [exact CUR|].
        split. { unfold wlist. rewrite map_app. apply (proj2 (mb_u64arr_app _ _ _ _)). split; [exact CURA|]. fold (wlist (qb_chunks cur)). rewrite LENC. exact ARRD. }
        split. { replace (qb_addr cur + 24 + 8 * (qb_count cur + qb_count nx)) with (qb_addr cur + 24 + 8 * qb_count cur + 8 * qb_count nx) by (clear; lia). exact CURJ'. }
        split; [eapply (pois_far2 _ m1 _ cur); [exact FP| exact OKC| exact AGL| exact WML| exact CURP]|].
        split; [exact NXC|]. split; [exact ARRS|]. split; [exact NXJ|].
        split; [eapply (pois_far2 _ m1 _ nx); [exact FP| exact OKN| exact AGL| exact WML| exact NXP]|].
        split; [eapply (bseg_far _ m1); [apply FW; exact NDR| exact OKR'| exact SUBR| exact AGL| exact WML| exact RESTS]|].
        eapply (bseg_far _ m1); [apply FW; exact NDE| exact OKE| exact SUBE| exact AGL| exact WML| exact EX].
  Qed.
End Loop.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Top.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo A T qbytes tb : Z) (f0 l0 : word) (l lF exF : list qbatch) (xbF qbF : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo. Hypothesis HI : lo + 16 <= bv_unsigned sp.
  Hypothesis AR : 0 <= A /\ A + 32 <= AIMG_TOP /\ A mod 8 = 0.          (* [comment removed for export] *)
  Hypothesis TR : bv_unsigned sp <= T /\ T + 32 <= 2^47 /\ T mod 8 = 0.   (* [comment removed for export] *)
  Hypothesis QBR : 0 <= qbytes /\ qbytes < 2^61. Hypothesis TBR : 0 <= tb /\ tb + qbytes < 2^62.
  Hypothesis OKL : Forall bok l.
  Hypothesis NDL : List.NoDup (map qb_addr l).
  Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
  Hypothesis QB : bsum l <= qbytes.
  Hypothesis Ha0 : a0 = wz A. Hypothesis Ha1 : a1 = wz T.
  Hypothesis HQ : rw_cells asegs m A [C8 (wz (zlen l)); C8 (wz (hd 0 (map qb_addr l))); C8 (wz (last (map qb_addr l) 0)); C8 (wz qbytes)].
  Hypothesis BR : batches_rep m l.
  Hypothesis HT : rw_cells asegs m T [C8 (wz 0); C8 f0; C8 l0; C8 (wz tb)].
  Hypothesis MB : merge_batches (mkQC l qbytes) = Some (mkQC lF qbF, exF, xbF).

  Lemma bsum_len : forall r, Forall bok r -> kBatchSize * zlen r <= bsum r.
  Proof.
    intros r OK. induction r as [|b r IH]; [change (bsum []) with 0; rewrite zlen_nil'; clear; lia|].
    apply Forall_cons_iff in OK. destruct OK as [(_ & _ & _ & _ & _ & Q6 & _) Hr]. rewrite bsum_cons, zlen_cons'. specialize (IH Hr). clear - Q6 IH. lia.
  Qed.
  Lemma last_cons_gen : forall {X : Type} (r : list X) (x d : X), last (x :: r) d = last r x.
  Proof. intros X r. induction r as [|y r IH]; intros x d; [reflexivity|]. cbn [last]. destruct r as [|z r']; [reflexivity| exact (IH x d)]. Qed.
  Lemma last_map_gen : forall (r : list qbatch) d, last (map qb_addr r) (qb_addr d) = qb_addr (last r d).
  Proof. intros r. induction r as [|x r IH]; intros d; [reflexivity|]. cbn [map]. rewrite 2!last_cons_gen. apply IH. Qed.
  Lemma last_map2 : forall (r : list qbatch) b c, last (map qb_addr (b :: c :: r)) 0 = qb_addr (last r c).
  Proof. intros r b c. cbn [map]. rewrite 2!last_cons_gen, last_map_gen. reflexivity. Qed.

  Theorem merge_batches_spec :
    evt asegs (merge_batches_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m lo A T qbytes tb f0 l0 l lF exF xbF)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x198f58) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (munch_refl ((bv_unsigned sp + -16, bv_unsigned sp) :: (A, A + 32) :: (T, T + 32) :: map bext l) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (A, A + 32)] m) as MUF.
    pose proof (bsum_len l OKL) as LLEN.
    assert (Z0 : 0 <= zlen l) by (unfold zlen; clear; lia).
    assert (FW : forall L, Forall (ifar l L) [(bv_unsigned sp + -16, bv_unsigned sp); (A, A + 32)]) by (intros L; constructor; [unfold ifar; right; left; clear - LO HI; lia| constructor; [unfold ifar; left; clear - AR; unfold AIMG_TOP in *; lia| constructor]]).
    assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(bv_unsigned sp + -16, bv_unsigned sp); (A, A + 32)]) by (constructor; [cbn [fst snd]; right; clear - LO HI; acb; unfold AHI_LO; lia| constructor; [cbn [fst snd]; left; clear - AR; unfold AIMG_TOP in *; lia| constructor]]).
    subst a0 a1. unfold kBatchSize, AHI_LO, AIMG_TOP, wz in *. acb.
    destruct l as [|b [|c r']].
    - (* [comment removed for export] *)
      cbn [map hd last zlen length Z.of_nat] in HQ |- *. cbn [merge_batches qc_list] in MB. injection MB as E1 E2 E3 E4. subst lF qbF exF xbF.
      (* [comment removed for export] *)
      step. carve_frame 16%nat ST. step. step. step.
      if_cases K; zify_cond K. 2: { exfalso. clear - K. rewrite ?unsigned_lit, ?land64_id in K by lia. lia. } clear K.
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      rewrite ?unsigned_lit in HQ by (clear - QBR; lia). rewrite ?Z.sub_0_r in HQ.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold merge_batches_post. unfold wz. do 14 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { cbn [map hd last zlen length Z.of_nat]. rewrite ?Z.sub_0_r. exact HQ. }
      split; [exact I|]. split; [cbn [thdr fst snd zlen length Z.of_nat]; rewrite Z.add_0_r; exact HT|]. split; [exact I|].
      split; [constructor|]. split; [constructor|]. split; [constructor|]. split; [intros b0 [] |]. split; [reflexivity| constructor].
    - (* [comment removed for export] *)
      pose proof BR as BR0. cbn [batches_rep] in BR0. destruct BR0 as [BB _].
      pose proof OKL as OKL0. apply Forall_cons_iff in OKL0. destruct OKL0 as [OKB _]. pose proof OKB as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      destruct (batch_open m b _ OKB BB) as (BC & BA & BJ & BP). clear BB.
      assert (LENB : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in C5; clear - C5; lia).
      unfold kBatchSize, kBatchCount, AHI_LO in *.
      cbn [map hd last zlen length Z.of_nat Pos.of_succ_nat] in HQ, BC |- *.
      cbn [merge_batches qc_list length merge_batches_aux rev app] in MB. injection MB as E1 E2 E3 E4. subst lF qbF exF xbF.
      (* [comment removed for export] *)
      step. carve_frame 16%nat ST. step. step. step.
      if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - C1 C2 ACEILB; lia). clear - C1. lia. } clear K.
      (* [comment removed for export] *)
      step. step.
      if_cases K; zify_cond K. 2: { exfalso. clear - K. rewrite ?unsigned_lit, ?land64_id in K by lia. lia. } clear K.
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      rewrite ?unsigned_lit in HQ by (clear - QBR; lia). rewrite ?Z.sub_0_r in HQ.
      release_frame FR ST (bv_unsigned sp).
      pose proof (munch_agree _ _ _ MUF) as AGL.
      apply evt_done. unfold merge_batches_post. unfold wz. do 14 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { cbn [map hd last zlen length Z.of_nat Pos.of_succ_nat]. rewrite ?Z.sub_0_r. exact HQ. }
      split. { apply bseg_batches. eapply (bseg_far _ OKL PW _ m); [apply FW| exact OKL| intros b0 Hb0; apply in_map; exact Hb0| exact AGL| exact WM| apply bseg_batches; exact BR]. }
      split; [cbn [thdr fst snd zlen length Z.of_nat]; rewrite Z.add_0_r; exact HT|]. split; [exact I|].
      split; [exact OKL|]. split; [constructor|]. split; [constructor|]. split; [intros b0 Hb0; rewrite app_nil_r in Hb0; apply in_map; exact Hb0|]. split; [reflexivity|]. exact NDL.
    - (* [comment removed for export] *)
      pose proof BR as BR0. cbn [batches_rep] in BR0. destruct BR0 as [BB BRR].
      pose proof OKL as OKL0. apply Forall_cons_iff in OKL0. destruct OKL0 as [OKB OKR]. pose proof OKB as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      apply Forall_cons_iff in OKR. destruct OKR as [OKC OKR']. pose proof OKC as (N1 & N2 & _).
      destruct (batch_open m b _ OKB BB) as (BC & BA & BJ & BP). clear BB.
      assert (LENB : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in C5; clear - C5; lia).
      unfold kBatchSize, kBatchCount, AHI_LO in *.
      cbn [map hd] in HQ, BC |- *.
      (* [comment removed for export] *)
      step. carve_frame 16%nat ST. step. step. step.
      if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - C1 C2 ACEILB; lia). clear - C1. lia. } clear K.
      (* [comment removed for export] *)
      step. step.
      if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - N1 N2 ACEILB; lia). clear - N1. lia. } clear K.
      (* [comment removed for export] *)
      step. step. step. step. step.
      pose proof (munch_agree _ _ _ MUF) as AGL.
      eapply (mb_loop ra sp gp tp s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m lo A T qbytes tb f0 l0 (b :: c :: r') _ lF exF xbF LO HI AR TR QBR TBR OKL PW ltac:(first [left; reflexivity| right; reflexivity]) ltac:(exact (Z.le_trans _ _ _ LLEN QB)) (S (length r')) [] b c r' [] 0).
      + clear. cbn [length]. lia.
      + split. { exists (S (length (c :: r'))). cbn [rev]. unfold merge_batches in MB. cbn [qc_list qc_bytes] in MB.
                 destruct (merge_batches_aux (S (length (c :: r'))) b (c :: r') [] [] 0) as [[[l' ex'] xb']|]; [| discriminate MB].
                 injection MB as E1 E2 E3 E4. subst. reflexivity. }
        split; [constructor|]. split; [exact OKB|]. split; [apply Forall_cons_iff; split; [exact OKC| exact OKR']|]. split; [constructor|]. split; [constructor|].
        split; [intros b0 Hb0; rewrite app_nil_r in Hb0; apply in_map; exact Hb0|].
        split; [rewrite app_nil_r; exact NDL|].
        pose proof (bsum_nonneg r' OKR') as BS0. rewrite 2!bsum_cons in QB. rewrite 2!bsum_cons in LLEN. rewrite !zlen_cons' in LLEN. rewrite zlen_nil', !zlen_cons', bsum_cons. unfold kBatchSize.
        pose proof OKC as (_ & _ & _ & _ & _ & N6 & _). unfold kBatchSize in N6.
        split; [clear - QB; lia|]. split; [reflexivity|]. split; [clear - QB LLEN C6 N6 BS0; lia| clear; lia].
      + assumption.
      + exact MU.
      + exact WM.
      + exact ST.
      + split; [exact FR|].
        split. { rewrite ?zlen_cons', 2!last_cons_gen, last_map_gen in HQ. cbn [hd]. replace (zlen [] + 2 + zlen r') with (1 + (1 + zlen r')) by (rewrite zlen_nil'; clear; lia). exact HQ. }
        split; [cbn [thdr fst snd]; rewrite zlen_nil', Z.add_0_r; exact HT|].
        split; [exact I|]. split; [exact BC|]. split; [exact BA|]. split; [exact BJ|].
        split. { eapply (pois_far2 _ m _ b); [exact FP| exact OKB| exact AGL| assumption| exact BP]. }
        split; [| exact I].
        eapply (bseg_far _ OKL PW _ m); [apply FW| apply Forall_cons_iff; split; [exact OKC| exact OKR']| intros b0 Hb0; apply in_map; right; exact Hb0| exact AGL| assumption| apply bseg_batches; exact BRR].
  Qed.
End Top.
