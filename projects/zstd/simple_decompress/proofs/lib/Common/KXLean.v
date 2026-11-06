(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint cshape (cs : list cell) (k : Z) : list (Z * nat) :=
  match cs with
  | [] => []
  | C8 _ :: cs' => (k, 8%nat) :: cshape cs' (k + 8)
  | C4 _ :: cs' => (k, 4%nat) :: cshape cs' (k + 4)
  | C2 _ :: cs' => (k, 2%nat) :: cshape cs' (k + 2)
  | C1 _ :: cs' => (k, 1%nat) :: cshape cs' (k + 1)
  | CB n _ :: cs' => cshape cs' (k + Z.of_nat n)
  end.

(* [comment removed for export] *)
Definition cval_ok (zs : list Z) (c : cell) (v : zexp) : Prop :=
  match c with
  | C8 V | C4 V | C2 V => V = Z_to_bv 64 (zden zs v)
  | C1 b => b = Z_to_bv 8 (zden zs v)
  | CB _ _ => True
  end.

(* [comment removed for export] *)
Fixpoint ctyped (cs : list cell) : list cell :=
  match cs with
  | [] => []
  | CB _ _ :: cs' => ctyped cs'
  | c :: cs' => c :: ctyped cs'
  end.

Fixpoint citems (eA : zexp) (sh : list (Z * nat)) (vs : list zexp) : list zk :=
  match sh, vs with
  | (k, w) :: sh', v :: vs' => ZKWord (ZAdd eA (ZL k)) w v :: citems eA sh' vs'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition coff_ok (eA : zexp) (sh : list (Z * nat)) : bool :=
  forallb (fun p => Z.eqb (zoff (ZAdd eA (ZL (fst p)))) (zoff eA + fst p)) sh.

Section Lean.
Variable segs : list Segment.
Variable m : word -> option byte.

Lemma kxl_w1 : forall z, word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. rewrite Z_to_bv_unsigned.
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 64 z) with (z mod 2^64). change (bv_wrap 8 ?x) with (x mod 2^8).
  rewrite (Z.mod_mod_divide z (2^64) (2^8)); [reflexivity | exists (2^56); reflexivity].
Qed.

Lemma kxl_cells_tl : forall A c cs, cells_at segs m A (c :: cs) -> cells_at segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros A c cs [[Wc Ws] Hb]. split; [exact Ws|].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cbytes_length in Hb by exact Wc. exact Hb.
Qed.

Lemma kxl_cells_rng : forall A c cs, cells_at segs m A (c :: cs) ->
  0 <= A /\ A + Z.of_nat (csize c) <= 2^64.
Proof.
  intros A c cs [[Wc Ws] (H0 & H1 & _)]. cbn [cells_bytes] in H1. rewrite length_app, cbytes_length in H1 by exact Wc. lia.
Qed.

Lemma kxl_cell_rd : forall A c cs, cells_at segs m A (c :: cs) -> rdn segs m (wa A) (csize c) = Some (cbytes c).
Proof.
  intros A c cs H. pose proof (cells_at_read segs m A (c :: cs) 0 c H eq_refl) as R.
  rewrite Z.add_0_r, ov_rdn in R. exact R.
Qed.

Lemma kxl_item : forall zs eA k A c cs v (w : nat),
  cells_at segs m (A + k) (c :: cs) -> zden zs eA = A -> 0 <= A -> 0 <= k ->
  zoff (ZAdd eA (ZL k)) = zoff eA + k -> (zoff eA = 0 \/ 0 <= A - zoff eA < 2^64) ->
  csize c = w -> (1 <= w)%nat -> cbytes c = word_to_le_bytes w (Z_to_bv 64 (zden zs v)) ->
  zk_prop segs m zs (ZKWord (ZAdd eA (ZL k)) w v).
Proof.
  intros zs eA k A c cs v w HC HA HA0 Hk HO HR Hw Hw1 HB.
  pose proof (kxl_cells_rng _ _ _ HC) as (R0 & R1). pose proof (kxl_cell_rd _ _ _ HC) as RD.
  rewrite Hw in R1, RD. rewrite HB in RD.
  cbn [zk_prop zden]. rewrite HO, HA.
  split; [destruct HR as [HZ|HR]; [rewrite HZ; lia | lia] |].
  split; [lia|]. split; [lia|]. exact RD.
Qed.

Lemma citems_gen : forall zs eA cs k A vs,
  cells_at segs m (A + k) cs -> zden zs eA = A -> 0 <= A -> 0 <= k ->
  coff_ok eA (cshape cs k) = true -> (zoff eA = 0 \/ 0 <= A - zoff eA < 2^64) ->
  Forall2 (cval_ok zs) (ctyped cs) vs ->
  Forall (zk_prop segs m zs) (citems eA (cshape cs k) vs).
Proof.
  intros zs eA cs. induction cs as [|c cs IH]; intros k A vs HC HA HA0 Hk HO HR HV; [constructor|].
  pose proof (kxl_cells_tl _ _ _ HC) as HT.
  destruct c as [V|V|V|b|n bs]; cbn [cshape ctyped csize] in HT, HO, HV |- *.
  5: { replace (A + k + Z.of_nat n) with (A + (k + Z.of_nat n)) in HT by lia.
       apply (IH _ A); [exact HT|exact HA|exact HA0|lia|exact HO|exact HR|exact HV]. }
  all: destruct vs as [|v vs']; [exfalso; inversion HV|].
  all: match type of HV with Forall2 _ (?c :: _) _ => assert (HV12 : cval_ok zs c v /\ Forall2 (cval_ok zs) (ctyped cs) vs') by (inversion HV; subst; split; assumption) end.
  all: destruct HV12 as [HV1 HV2]; cbn [citems].
  all: cbn [coff_ok forallb fst] in HO; apply andb_prop in HO as [HO1 HO2]; apply Z.eqb_eq in HO1.
  all: cbn [cval_ok] in HV1.
  all: constructor.
  1,3,5,7: eapply kxl_item; [exact HC|exact HA|exact HA0|exact Hk|exact HO1|exact HR|reflexivity|cbn; lia|].
  1: (cbn [cbytes]; unfold le8; rewrite HV1; reflexivity).
  1: (cbn [cbytes]; unfold le4, word_to_le_bytes; rewrite HV1; reflexivity).
  1: (cbn [cbytes]; unfold le2, word_to_le_bytes; rewrite HV1; reflexivity).
  1: (cbn [cbytes]; rewrite kxl_w1, HV1; reflexivity).
  all: change (Z.of_nat 8) with 8 in HT; change (Z.of_nat 4) with 4 in HT; change (Z.of_nat 2) with 2 in HT; change (Z.of_nat 1) with 1 in HT.
  all: rewrite <- Z.add_assoc in HT; apply (IH _ A); [exact HT|exact HA|exact HA0|lia|exact HO2|exact HR|exact HV2].
Qed.

(* [comment removed for export] *)
Lemma citems_ro : forall zs eA A cs sh vs, ro_cells segs m A cs ->
  zden zs eA = A -> cshape cs 0 = sh -> coff_ok eA sh = true -> (zoff eA = 0 \/ 0 <= A - zoff eA < 2^64) ->
  Forall2 (cval_ok zs) (ctyped cs) vs -> Forall (zk_prop segs m zs) (citems eA sh vs).
Proof.
  intros zs eA A cs sh vs H HA <- HO HR HV.
  destruct cs as [|c cs']; [constructor|].
  pose proof (kxl_cells_rng A c cs' H) as (R0 & _).
  apply (citems_gen zs eA (c :: cs') 0 A vs); [rewrite Z.add_0_r; exact H|exact HA|exact R0|lia|exact HO|exact HR|exact HV].
Qed.

Lemma citems_rw : forall zs eA A cs sh vs, rw_cells segs m A cs ->
  zden zs eA = A -> cshape cs 0 = sh -> coff_ok eA sh = true -> (zoff eA = 0 \/ 0 <= A - zoff eA < 2^64) ->
  Forall2 (cval_ok zs) (ctyped cs) vs -> Forall (zk_prop segs m zs) (citems eA sh vs).
Proof. intros zs eA A cs sh vs H. exact (citems_ro zs eA A cs sh vs (proj1 H)). Qed.

Lemma kxl_b8 : forall b : byte, b = Z_to_bv 8 (bv_unsigned b).
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma kxl_rd_rw : forall A cs N, rw_cells segs m A cs -> Z.of_nat (cells_size cs) = N -> rd_at segs m A N.
Proof. intros A cs N H <-. exact (rd_at_rw_cells segs m A cs H). Qed.
Lemma kxl_rd_ro : forall A cs N, ro_cells segs m A cs -> Z.of_nat (cells_size cs) = N -> rd_at segs m A N.
Proof. intros A cs N H <-. exact (rd_at_ro_cells segs m A cs H). Qed.

End Lean.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kxl_cells l cs k :=
  lazymatch cs with
  | @nil _ => constr:((l, @nil (Z * nat), @nil zexp))
  | @cons _ ?c ?rest =>
      lazymatch c with
      | C8 ?v => kxl_cellw l v 8%nat k rest
      | C4 ?v => kxl_cellw l v 4%nat k rest
      | C2 ?v => kxl_cellw l v 2%nat k rest
      | C1 ?b => kxl_cellb l b k rest
      | CB ?n _ => let k' := eval vm_compute in (k + Z.of_nat n) in kxl_cells l rest k'
      end
  end
with kxl_cellw l v w k rest :=
  let r := kx_rw l v in
  lazymatch r with (?l1, ?ev) =>
    let k' := eval vm_compute in (k + Z.of_nat w) in
    let r2 := kxl_cells l1 rest k' in
    lazymatch r2 with (?l2, ?sh, ?vs) => constr:((l2, @cons (Z * nat) (k, w) sh, @cons zexp ev vs)) end end
with kxl_cellb l b k rest :=
  let r := lazymatch b with
           | Z_to_bv 8 ?z => kx_rz l z
           | _ => kx_atom l (bv_unsigned b)
           end in
  lazymatch r with (?l1, ?ev) =>
    let k' := eval vm_compute in (k + 1) in
    let r2 := kxl_cells l1 rest k' in
    lazymatch r2 with (?l2, ?sh, ?vs) => constr:((l2, @cons (Z * nat) (k, 1%nat) sh, @cons zexp ev vs)) end end.

Ltac kxl_chunk l H :=
  let T := type of H in
  let AC := lazymatch T with
            | rw_cells _ _ ?A ?cs => constr:((A, cs))
            | ro_cells _ _ ?A ?cs => constr:((A, cs))
            | _ => fail 100 "kx_autoL: named chunk is not an rw_cells / ro_cells hypothesis:" H
            end in
  lazymatch AC with (?A, ?cs) =>
    let r1 := kx_rz l A in
    lazymatch r1 with (?l1, ?eA) =>
      let r2 := kxl_cells l1 cs 0%Z in
      lazymatch r2 with (?l2, ?sh, ?vs) => constr:((l2, eA, sh, vs)) end end end.

(* [comment removed for export] *)
Ltac kxl_named l CH :=
  lazymatch CH with
  | tt => constr:((l, @nil zk, tt))
  | ((?a, ?b), ?c) => kxl_named l (a, (b, c))
  | (?H, ?rest) =>
      let r := kxl_chunk l H in
      lazymatch r with (?l1, ?eA, ?sh, ?vs) =>
        let r2 := kxl_named l1 rest in
        lazymatch r2 with (?l2, ?cp, ?ds) => constr:((l2, citems eA sh vs ++ cp, ((H, eA, sh, vs), ds))) end end
  | ?H =>
      let r := kxl_chunk l H in
      lazymatch r with (?l1, ?eA, ?sh, ?vs) => constr:((l1, citems eA sh vs ++ @nil zk, ((H, eA, sh, vs), tt))) end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kxl_val1 :=
  lazymatch goal with
  | |- cval_ok _ (C8 (Z_to_bv 64 _)) _ => exact eq_refl
  | |- cval_ok _ (C4 (Z_to_bv 64 _)) _ => exact eq_refl
  | |- cval_ok _ (C2 (Z_to_bv 64 _)) _ => exact eq_refl
  | |- cval_ok _ (C1 (Z_to_bv 8 _)) _ => exact eq_refl
  | |- cval_ok _ (C8 ?V) _ => exact (eq_sym (Z_to_bv_bv_unsigned V))
  | |- cval_ok _ (C4 ?V) _ => exact (eq_sym (Z_to_bv_bv_unsigned V))
  | |- cval_ok _ (C2 ?V) _ => exact (eq_sym (Z_to_bv_bv_unsigned V))
  | |- cval_ok _ (C1 ?b) _ => exact (kxl_b8 b)
  end.
Ltac kxl_vals :=
  cbv beta iota delta [ctyped];
  repeat (apply Forall2_cons; [kxl_val1 |]); apply Forall2_nil.

Ltac kxl_bcert :=
  lazymatch goal with
  | |- ?c = true =>
      let v := eval vm_compute in c in
      lazymatch v with
      | true => vm_cast_no_check (@eq_refl bool true)
      | _ => fail 100 "kx_autoL: a named chunk's base has no uniform offset form (coff_ok):" c
      end
  end.

Ltac kxl_chunk_solve H eA :=
  lazymatch goal with
  | |- Forall (zk_prop ?segs ?m ?zs) (citems eA ?sh ?vs) =>
      let z := eval vm_compute in (zoff eA) in
      let HR := lazymatch z with
                | 0%Z => constr:(@or_introl (zoff eA = 0) (0 <= zden zs eA - zoff eA < 2^64) (@eq_refl Z 0))
                | _ => constr:(@or_intror (zoff eA = 0) (0 <= zden zs eA - zoff eA < 2^64)
                                 ltac:(change (zoff eA) with z; cbv beta iota zeta delta [zden znth]; kx_lia))
                end in
      lazymatch type of H with
      | rw_cells _ _ ?A ?cs => refine (citems_rw segs m zs eA A cs sh vs H eq_refl eq_refl ltac:(kxl_bcert) HR _); kxl_vals
      | ro_cells _ _ ?A ?cs => refine (citems_ro segs m zs eA A cs sh vs H eq_refl eq_refl ltac:(kxl_bcert) HR _); kxl_vals
      end
  end.

Ltac kxl_cells_solve ds :=
  lazymatch ds with
  | tt => apply Forall_nil
  | ((?H, ?eA, _, _), ?rest) => apply Forall_app; split; [ kxl_chunk_solve H eA | kxl_cells_solve rest ]
  end.

(* [comment removed for export] *)
Ltac kxl_is_lin T :=
  lazymatch T with
  | context [Z.div _ _] => fail | context [Z.modulo _ _] => fail | context [Z.land _ _] => fail
  | context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail | context [Z.pow _ ?e] => lazymatch e with Z.pos _ => idtac | _ => fail end
  | _ => idtac
  end;
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac
  | and ?A ?B => kxl_is_lin A; kxl_is_lin B
  end.
Ltac kxl_pull := repeat match goal with H : ?T |- ?G => kxl_is_lin T; kx_shares T G; revert H end.
Ltac kxl_lia_small := kxl_pull; repeat match goal with H : ?T |- _ => kx_is_arith T; clear H end; intros; lia.
Ltac kxl_lia := first [ solve [kxl_lia_small] | kx_lia ].

(* [comment removed for export] *)
Ltac kxl_wr_exact :=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          lazymatch n with N => exact (proj2 H) end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp := lazymatch goal with |- ?G => match goal with H : G |- _ => exact H end end.
Ltac kxl_zk1 :=
  first [ kxl_hyp
        | lazymatch goal with
          | |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ =>
              split; [kxl_lia | split; [kxl_lia | split; [kxl_lia | first [kxl_hyp | kx_word_cell]]]]
          | |- _ /\ _ /\ wr_at _ _ _ _ /\ mem_inv _ _ /\ _ = true =>
              split; [kxl_lia | split; [kxl_lia | split; [first [kxl_wr_exact | kx_wr_at] | split; [kxl_hyp | vm_compute; reflexivity]]]]
          | |- _ /\ wr_at _ _ _ _ => split; [kxl_lia | first [kxl_wr_exact | kx_wr_at]]
          | |- ?lo <= _ <= ?hi => kxl_lia
          | |- _ /\ _ /\ (_ \/ _) => split; [kxl_lia | split; [kxl_lia | first [kxl_hyp | kxl_lia]]]
          | |- _ /\ _ mod _ = 0 => split; [kxl_lia | first [kxl_hyp | kxl_lia]]
          | |- _ /\ _ /\ forall i, _ => split; [kxl_lia | split; [kxl_lia | kx_zk_solve]]
          end
        | kx_zk_solve ].
Ltac kxl_zks_solve :=
  repeat (apply Forall_cons; [kx_zk_pre; try solve [kxl_zk1]|]); try apply Forall_nil.

(* [comment removed for export] *)
Ltac kxl_rd_exact :=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
      | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
      end
  end.
Ltac kxl_zregs_solve :=
  repeat (apply Forall_cons; [kx_zreg_pre; try solve [split; [kxl_lia | first [kxl_rd_exact | kx_rd_at]]]|]); try apply Forall_nil.

(* [comment removed for export] *)
Ltac kxl_rng :=
  first [ kxl_hyp
        | lazymatch goal with
          | |- rng ?RNG ?A ?N =>
              match goal with
              | H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small]
              end
          end
        | kx_rng ].
Ltac kxl_zwins_solve :=
  repeat (apply Forall_cons; [kx_zwin_pre; try solve [split; [kxl_lia | kxl_rng]]|]); try apply Forall_nil.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_autoFL_core VMAX STOPS FUEL SCALLS CH KZS RRS WWS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kxl_named l2a CH in
      lazymatch r2b with (?l2, ?cp, ?ds) =>
      let extra := kx_add_wrimgs segs m l2 KZS (@nil zk) in
      let zks := constr:(zks0 ++ (cp ++ extra)) in
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?l3, ?rs) =>
      let r4 := kx_rrs l3 WWS in
      lazymatch r4 with (?zs, ?ws) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let res := kx_trun_fix segs VMAX FUEL stops SCALLS pcv rz zks (@nil kentry) rs ws nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          change (evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_tree_evtF segs F fc RNG Q VMAX FUEL stops SCALLS zs rz xs zks rk pcv m rom t r reads rs ws _ _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktree t)
          | kx_cert
          | kx_regs_eqs
          | apply Forall_app; split; [ kxl_zks_solve | apply Forall_app; split; [ kxl_cells_solve ds | kxl_zks_solve ] ]
          | kxl_zregs_solve
          | kxl_zwins_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end end
  end.

Ltac kx_autoL_core VMAX STOPS FUEL SCALLS CH KZS RRS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kxl_named l2a CH in
      lazymatch r2b with (?l2, ?cp, ?ds) =>
      let extra := kx_add_wrimgs segs m l2 KZS (@nil zk) in
      let zks := constr:(zks0 ++ (cp ++ extra)) in
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?zs, ?rs) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let res := kx_trun_fix segs VMAX FUEL stops SCALLS pcv rz zks (@nil kentry) rs (@nil zreg) nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          change (evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_tree_evt segs F fc Q VMAX FUEL stops SCALLS zs rz xs zks rk pcv m rom t r reads rs _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktree t)
          | kx_cert
          | kx_regs_eqs
          | apply Forall_app; split; [ kxl_zks_solve | apply Forall_app; split; [ kxl_cells_solve ds | kxl_zks_solve ] ]
          | kxl_zregs_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end
  end.

Tactic Notation "kx_autoFL" constr(CH) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFL_core 0 stops (FUEL : nat) true CH kzs rrs wws.
Tactic Notation "kx_autoFL_nocall" constr(CH) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFL_core 0 stops (FUEL : nat) false CH kzs rrs wws.
Tactic Notation "kx_autoL" constr(CH) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_autoL_core 0 stops (FUEL : nat) true CH kzs rrs.
Tactic Notation "kx_autoL_nocall" constr(CH) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_autoL_core 0 stops (FUEL : nat) false CH kzs rrs.
