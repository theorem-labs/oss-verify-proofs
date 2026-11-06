(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnZX BnZXTac BnMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ZX BM.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition bn_at (m : word -> option byte) (o : Z) (b : bn) : Prop :=
  cellN segs m o 2 (zlen (cells b)) /\ cellN segs m (o + 2) 2 (ex b) /\ arr32 segs m (o + 4) (cells b)
  /\ 0 <= ex b < 2 ^ 15 /\ zlen (cells b) <= 128.

Lemma bn_at_unch : forall m m' o b rs,
  unch m m' rs -> 0 <= o -> o + 516 <= M64 -> (forall r, In r rs -> o + 516 <= fst r \/ snd r <= o) ->
  bn_at m o b -> bn_at m' o b.
Proof.
  intros m m' o b rs Hu Ho Hb Hd (H1 & H2 & H3 & H4 & H5). unfold zlen in H5.
  split; [|split; [|split; [|split; [exact H4|unfold zlen; lia]]]].
  - eapply cellN_unch; eauto; cbn; try lia. intros r Hr; specialize (Hd r Hr); lia.
  - eapply cellN_unch; eauto; cbn; try lia. intros r Hr; specialize (Hd r Hr); lia.
  - eapply arr32_unch; eauto; try lia. intros r Hr; specialize (Hd r Hr); lia.
Qed.

Section WithFP.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma step_ret : forall regs p m rom ret w (rd rs1 : reg) (imm : bv 12),
  fetch_word segs (Z_to_bv 64 p) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4) ->
  bv_unsigned rd = 0 -> bv_unsigned rs1 = 1 -> bv_unsigned imm = 0 ->
  getr regs 1%bv = ret -> ret_ok ret ->
  RiscvSemantics.step segs (mkst regs (Z_to_bv 64 p) m rom) = MachineOk (mkst regs ret m rom).
Proof.
  intros regs p m rom ret w rd rs1 imm Hf He Hd Hrd Hrs Himm Hr Hok.
  assert (rd = 0%bv) as -> by (apply bv_eq; exact Hrd).
  assert (rs1 = 1%bv) as -> by (apply bv_eq; exact Hrs).
  assert (imm = 0%bv) as -> by (apply bv_eq; exact Himm).
  rewrite (step_jalr_gen segs regs (Z_to_bv 64 p) m rom _ 0%bv 1%bv 0%bv Hf He Hd).
  cbn [bv_eqb Z.eqb bv_unsigned]. rewrite Hr.
  change (jalr_tgt ret (bv_signed (0%bv : bv 12))) with (v_jalr ret 0). rewrite Hok. reflexivity.
Qed.

Lemma msteps_ret : forall regs p m rom ret w (rd rs1 : reg) (imm : bv 12),
  fetch_word segs (Z_to_bv 64 p) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4) ->
  bv_unsigned rd = 0 -> bv_unsigned rs1 = 1 -> bv_unsigned imm = 0 ->
  getr regs 1%bv = ret -> ret_ok ret ->
  msteps segs (mkst regs (Z_to_bv 64 p) m rom) (mkst regs ret m rom).
Proof.
  intros. eapply mst_step; [reflexivity | eapply step_ret; eauto | apply mst_refl].
Qed.

(* [comment removed for export] *)
Lemma reg_kept : forall regs vals rs regs' (r : reg),
  regs_ok (Eof regs vals) rs regs' -> zx_eqb (sr_get rs r) (ZV (ridx r)) = true ->
  getr regs' r = getr regs r.
Proof.
  intros regs vals rs regs' r Hr He. apply zx_eqb_eq in He.
  rewrite (Hr r), He. unfold wd. cbn [ev]. unfold Eof.
  pose proof (ridx_range r) as Hlt.
  replace (Nat.ltb (ridx r) 32) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
  rewrite ridx_roundtrip. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E rs regs' (r : reg) e,
  regs_ok E rs regs' -> sr_get rs r = e -> getr regs' r = Z_to_bv 64 (ev E e).
Proof. intros E rs regs' r e Hr <-. apply Hr. Qed.

End WithFP.
End WithSegs.

(* [comment removed for export] *)
Definition keeps (l : list Z) (regs regs' : bvmap 5 word) : Prop :=
  forall r, In r l -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).

Lemma keeps_refl : forall l regs, keeps l regs regs.
Proof. intros l regs r _. reflexivity. Qed.

Lemma keeps_trans : forall l r1 r2 r3, keeps l r1 r2 -> keeps l r2 r3 -> keeps l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_sub : forall l l' r1 r2, keeps l r1 r2 -> incl l' l -> keeps l' r1 r2.
Proof. intros l l' r1 r2 K Hi r Hr. apply K, Hi, Hr. Qed.

Lemma keeps_sub_dec : forall l l' r1 r2, keeps l r1 r2 -> forallb (fun x => existsb (Z.eqb x) l) l' = true -> keeps l' r1 r2.
Proof.
  intros l l' r1 r2 K H r Hr. apply K.
  pose proof (proj1 (forallb_forall _ _) H r Hr) as Hx. apply existsb_exists in Hx as (y & Hy & E).
  apply Z.eqb_eq in E. subst y. exact Hy.
Qed.

Section KeepsZX.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma keeps_of_zx : forall l E rs0 regs rs regs',
  regs_ok E rs0 regs -> regs_ok E rs regs' ->
  forallb (fun r => zx_eqb (sr_get rs (Z_to_bv 5 r)) (sr_get rs0 (Z_to_bv 5 r))) l = true ->
  keeps l regs regs'.
Proof.
  intros l E rs0 regs rs regs' H0 H1 Hall r Hin.
  pose proof (proj1 (forallb_forall _ l) Hall r Hin) as He. apply zx_eqb_eq in He.
  rewrite (H1 (Z_to_bv 5 r)), (H0 (Z_to_bv 5 r)), He. reflexivity.
Qed.
End KeepsZX.

(* [comment removed for export] *)
Definition CS : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Ltac zx_ret segs :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?p) _ _) _ =>
      let f := eval vm_compute in (fetch_word segs (Z_to_bv 64 p)) in
      lazymatch f with
      | Some ?w =>
          let d := eval vm_compute in (decode_any w) in
          lazymatch d with
          | Some (Jalr ?rd ?rs1 ?imm, 4%Z) =>
              eapply (msteps_ret segs _ p _ _ _ w rd rs1 imm);
              [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | | ]
          end
      end
  end.

(* [comment removed for export] *)
Ltac zwidth :=
  cbn [length];
  repeat match goal with
  | |- context [Z.of_nat 0%nat] => change (Z.of_nat 0%nat) with 0
  | |- context [Z.of_nat 1%nat] => change (Z.of_nat 1%nat) with 1
  | |- context [Z.of_nat 2%nat] => change (Z.of_nat 2%nat) with 2
  | |- context [Z.of_nat 3%nat] => change (Z.of_nat 3%nat) with 3
  | |- context [Z.of_nat 4%nat] => change (Z.of_nat 4%nat) with 4
  | |- context [Z.of_nat 8%nat] => change (Z.of_nat 8%nat) with 8
  | |- context [Z.of_nat 16%nat] => change (Z.of_nat 16%nat) with 16
  | |- context [2 ^ (8 * 1)] => change (2 ^ (8 * 1)) with 256
  | |- context [2 ^ (8 * 2)] => change (2 ^ (8 * 2)) with 65536
  | |- context [2 ^ (8 * 4)] => change (2 ^ (8 * 4)) with 4294967296
  | |- context [2 ^ (8 * 8)] => change (2 ^ (8 * 8)) with 18446744073709551616
  end.

(* [comment removed for export] *)
Ltac kc1 H := split; [apply (kc_intro _ _ _ _ _ _ _ _ _ H); zx_cbn; unfold zlen in *; zwidth; lia |].
(* [comment removed for export] *)
Ltac kw1 H :=
  lazymatch type of H with
  | RiscvSemantics.store_ok ?segs ?m (Z_to_bv 64 ?base) ?N = true =>
      lazymatch goal with
      | |- (0 <= ZX.ev ?E ?b + ?lo /\ _) /\ _ =>
          split; [apply (kw_intro' segs E m b lo _ base N H); zx_cbn; zwidth; lia |]
      end
  end.

(* [comment removed for export] *)
Ltac zx_scs ts :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [first [zwidth; lia | ts] | zx_scs ts]
  end.

(* [comment removed for export] *)
Ltac cellx :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 _) (word_to_le_bytes _ _)) _ _ _ =>
      first
        [ assumption
        | apply cellN_store_same';
          [ cbn; lia | lia | zwidth; lia
          | rewrite ?ZX.u_Z2bv64; zwidth;
            first [ reflexivity | lia
                  | rewrite (Z.mod_small _ 18446744073709551616) by lia; first [apply Z.mod_small; lia | rewrite Z.mod_small by lia; lia | idtac]
                  | idtac ] ]
        | apply cellN_store_skip; [ lia | zwidth; lia | lia | zwidth; lia | zwidth; lia | cellx ]
        | idtac ]
  | |- cellN _ _ _ _ _ => first [assumption | eassumption | idtac]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac in_list_tac := cbn [In]; intuition congruence.
Ltac unch_store1 :=
  lazymatch goal with
  | |- unch _ (wbytes _ (Z_to_bv 64 ?a) (word_to_le_bytes ?n _)) ?rs =>
      let rec go l :=
        lazymatch l with
        | (?lo, ?hi) :: ?t =>
            first [ apply (unch_store _ a n _ rs lo hi); [lia | zwidth; lia | cbn [In]; tauto | lia | zwidth; lia]
                  | go t ]
        end in go rs
  end.
Ltac unchx :=
  lazymatch goal with
  | |- unch ?m ?m _ => apply unch_refl
  | |- unch ?m (wbytes ?M ?a ?bs) ?rs =>
      apply (unch_trans m M (wbytes M a bs) rs); [unchx | unch_store1]
  end.
Ltac growsx :=
  lazymatch goal with
  | |- mem_grows ?m ?m => apply mem_grows_refl
  | |- mem_grows ?m (wbytes ?M ?a ?bs) => apply (mem_grows_trans m M (wbytes M a bs)); [growsx | apply grows_store]
  end.

Section Cells.
Variable segs : list Segment.
Lemma cellN_eqa : forall m a a' n v v', cellN segs m a n v -> a = a' -> v = v' -> cellN segs m a' n v'.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma kc_of_arr32 : forall m a done x t a' ,
  arr32 segs m a (done ++ x :: t) -> a' = a + 4 * Z.of_nat (length done) ->
  exists bs, rdn segs m (Z_to_bv 64 a') 4 = Some bs /\ bytes_le_to_Z bs = x.
Proof.
  intros m a done x t a' H ->. specialize (H (length done) ltac:(rewrite length_app; cbn; lia)).
  rewrite nth_middle in H. exact H.
Qed.

Lemma kc_of_arr32_i : forall m a l i a' v,
  arr32 segs m a l -> (i < length l)%nat -> a' = a + 4 * Z.of_nat i -> v = nth i l 0 ->
  exists bs, rdn segs m (Z_to_bv 64 a') 4 = Some bs /\ bytes_le_to_Z bs = v.
Proof. intros m a l i a' v H Hi -> ->. exact (H i Hi). Qed.
End Cells.

(* [comment removed for export] *)
Tactic Notation "zx_reg" constr(ZR) constr(r) "as" ident(H) :=
  pose proof (ZR r) as H;
  lazymatch type of H with
  | getr _ _ = ZX.wd _ (ZX.sr_get ?rs ?rr) =>
      let e := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with e in H
  end;
  zx_cbn_in H.

(* [comment removed for export] *)
Definition magic28 (n : Z) : Z :=
  bv_swrap 32 ((n * -1840700269) mod 2 ^ 64 / 2 ^ 32 + n) / 2 ^ 4
  + ((n * -1840700269) mod 2 ^ 64 / 2 ^ 32 + n) mod 2 ^ 32 / 2 ^ 31.

Lemma magic28_table : forallb (fun k => magic28 (Z.of_nat k) =? Z.of_nat k / 28) (seq 0 2048) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma magic28_ok : forall n, 0 <= n < 2048 -> magic28 n = n / 28.
Proof.
  intros n Hn.
  pose proof (proj1 (forallb_forall _ _) magic28_table (Z.to_nat n)) as H. cbn beta in H.
  replace (Z.of_nat (Z.to_nat n)) with n in H by lia.
  apply Z.eqb_eq, H. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition CS' : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma keeps_CS_of : forall regs regs', keeps CS' regs regs' -> getr regs' 2%bv = getr regs 2%bv -> keeps CS regs regs'.
Proof.
  intros regs regs' K H2 r Hr. cbn in Hr.
  destruct Hr as [<-|Hr]; [exact H2|]. apply K. cbn. exact Hr.
Qed.

(* [comment removed for export] *)
Ltac zx_regv ZR :=
  lazymatch goal with |- getr _ _ = _ => idtac end;
  etransitivity; [apply ZR |];
  lazymatch goal with
  | |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ =>
      let e := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with e
  end;
  unfold ZX.wd; zx_cbn; first [reflexivity | f_equal; lia | rewrite Z_to_bv_bv_unsigned; first [reflexivity | assumption] | idtac].

(* [comment removed for export] *)
Section Chunks.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma chunks_0 : chunks 3 0 = []. Proof. reflexivity. Qed.
Lemma chunks_1 : forall v, 1 <= v < B -> chunks 3 v = [v].
Proof.
  intros v Hv. cbn [chunks]. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.div_small v B), (Z.mod_small v B) by lia. reflexivity.
Qed.
Lemma chunks_2 : forall v, B <= v < B * B -> chunks 3 v = [v mod B; v / B].
Proof.
  intros v Hv. cbn [chunks]. unfold B in *. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (1 <= v / 268435456 < 268435456) by lia.
  replace (v / 268435456 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.div_small (v / 268435456) 268435456), (Z.mod_small (v / 268435456) 268435456) by lia. reflexivity.
Qed.
Lemma chunks_3 : forall v, B * B <= v < M64 -> chunks 3 v = [v mod B; (v / B) mod B; v / B / B].
Proof.
  intros v Hv. cbn [chunks]. unfold B in *. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (268435456 <= v / 268435456 < 268435456 * 268435456) by lia.
  replace (v / 268435456 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (1 <= v / 268435456 / 268435456 < 268435456) by lia.
  replace (v / 268435456 / 268435456 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small (v / 268435456 / 268435456) 268435456) by lia. reflexivity.
Qed.

End Chunks.
