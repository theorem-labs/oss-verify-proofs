(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal.
Import ListNotations.
Import W64 Val Mem St MemP UB HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module TD.

Definition CM_TD : Z := 5.

Definition decode_td (ca : list word) : option (Z * Z) :=
  match ca with
  | [cur; cnt] => Some (bv_unsigned cur, bv_unsigned cnt)
  | _ => None
  end.

Definition tchunk_ok (c : Z * Z) : Prop := fst c <> 0 /\ fst c mod 16 = 0 /\ CHUNK_SIZE0 <= snd c.

Definition hd_addr (cs : list (Z * Z)) : Z := match cs with [] => 0 | (c, _) :: _ => c end.

Section WithSegs.
Variable segs : list Segment.

Definition td_inv (cur cnt : Z) (LB : blocks) (ws : list window) (bm : bmem) (cs : list (Z * Z)) : Prop :=
  cur = hd_addr cs /\ cnt = Z.of_nat (length cs) /\
  Forall tchunk_ok cs /\ ForallOrdPairs chunk_disj cs /\
  (forall c, In c cs -> In (chunk_block c) LB) /\
  Forall (fun w => w_kind w <> K_STACK -> forall c, In c cs -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ws /\
  chunks_at bm cs /\
  Seal.seal_ok ws cs.

Definition td_client0 (ca : list word) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  match decode_td ca with
  | Some (cur, cnt) => exists cs, td_inv cur cnt LB ws (bmem_of segs m) cs
  | None => False
  end.

Definition nosub (ws : list window) : Prop := Forall (fun w => ~ (K_SUB <= w_kind w < K_GHOST)) ws.
Definition td_client (ca : list word) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop := td_client0 ca LB ws m /\ nosub ws.
Lemma nosub_app : forall a b, nosub a -> nosub b -> nosub (a ++ b).
Proof. intros a b A B. apply Forall_app. split; assumption. Qed.
Lemma nosub_one : forall b n kd, kd < K_SUB \/ K_GHOST <= kd -> nosub [Win b n kd].
Proof. intros b n kd K. constructor; [cbn [w_kind]; lia| constructor]. Qed.
Lemma nosub_sub : forall ws ws', nosub ws -> (forall w, In w ws' -> In w ws) -> nosub ws'.
Proof. intros ws ws' N I. apply Forall_forall. intros w Hw. exact (proj1 (Forall_forall _ _) N w (I w Hw)). Qed.
Lemma nosub_kinds : forall ws, (forall w, In w ws -> w_kind w < K_SUB \/ K_GHOST <= w_kind w) -> nosub ws.
Proof. intros ws H. apply Forall_forall. intros w Hw. pose proof (H w Hw). lia. Qed.

Lemma chunk_block_pos : forall c, tchunk_ok c -> 0 < snd (chunk_block c).
Proof. intros c (_ & _ & S). unfold chunk_block, CHUNK_HDR, CHUNK_SIZE0 in *. cbn [snd]. lia. Qed.

Lemma td0_grow : forall ca LB ws m b n, td_client0 ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  td_client0 ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m.
Proof.
  intros ca LB ws m b n H FR. unfold td_client0 in *. destruct (decode_td ca) as [[cur cnt]|]; [|exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SEALt). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [| split; [| split; [exact Hat|]]].
  3: { apply Seal.seal_ok_app; [exact SEALt|]. constructor; [|constructor]. cbn [w_kind]. unfold K_BLOCK, Seal.K_TWIN. lia. }
  - intros c Hc. right. exact (Hlb c Hc).
  - apply Forall_app. split; [exact Hws|]. constructor; [|constructor]. intros _ c Hc a Ha Hb.
    apply (FR a Ha). unfold in_user. apply in_ivs_In. exists (chunk_block c). split; [exact (Hlb c Hc)| exact Hb].
Qed.

Lemma td0_free : forall ca LB ws m b n ws', td_client0 ca LB ws m -> In (Win b n K_BLOCK) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
  td_client0 ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros ca LB ws m b n ws' H Hin Hws'. unfold td_client0 in *. destruct (decode_td ca) as [[cur cnt]|]; [|exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SEALt). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [| split; [| split; [exact Hat|]]].
  3: { apply (Seal.seal_ok_ws ws); [exact SEALt|]. intros w Hw _. exact (proj1 (proj1 (Hws' w) Hw)). }
  - intros c Hc. apply in_in_remove; [| exact (Hlb c Hc)]. intros E.
    pose proof (chunk_block_pos c (proj1 (Forall_forall _ _) Hok c Hc)) as POS.
    pose proof (proj1 (Forall_forall _ _) Hws _ Hin ltac:(cbn [w_kind]; discriminate) c Hc b) as D.
    rewrite E in D, POS. cbn [snd] in POS.
    apply D; unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
  - apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Hws w Hw).
Qed.

Lemma td0_frame : forall ca LB ws m m', td_client0 ca LB ws m ->
  (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  td_client0 ca LB ws m'.
Proof.
  intros ca LB ws m m' H FR. unfold td_client0 in *. destruct (decode_td ca) as [[cur cnt]|]; [|exact H].
  destruct H as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SEALt). exists cs.
  split; [exact Hcur|]. split; [exact Hcnt|]. split; [exact Hok|]. split; [exact Hdisj|]. split; [exact Hlb|]. split; [exact Hws|].
  split; [| exact SEALt].
  apply (chunks_at_frame (bmem_of segs m)); [| exact Hat].
  intros c Hc x Hx. unfold bmem_of.
  destruct ((0 <=? x) && (x <? two64)) eqn:RG; [|reflexivity].
  apply andb_prop in RG as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  pose proof (proj1 (Forall_forall _ _) Hok c Hc) as (_ & _ & OK3).
  assert (INB : in_iv (chunk_block c) x).
  { unfold in_iv, chunk_block, CHUNK_HDR, CHUNK_SIZE0 in *. cbn [fst snd]. lia. }
  unfold rb. rewrite (FR x ltac:(lia)); [reflexivity| |].
  - unfold in_user. apply in_ivs_In. exists (chunk_block c). split; [exact (Hlb c Hc)| exact INB].
  - intros X. unfold in_ws, heap_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    apply filter_In in Hw as [Hw NK]. destruct (Z.eqb_spec (w_kind w) K_STACK) as [|NK']; [discriminate|].
    exact (proj1 (Forall_forall _ _) Hws w Hw NK' c Hc x Hin INB).
Qed.

Lemma td_grow : forall ca LB ws m b n, td_client ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  td_client ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m.
Proof. intros ca LB ws m b n [H NS] FR. split; [exact (td0_grow ca LB ws m b n H FR)|]. apply nosub_app; [exact NS|]. apply nosub_one. left. unfold K_BLOCK, K_SUB. lia. Qed.
Lemma td_free : forall ca LB ws m b n ws', td_client ca LB ws m -> In (Win b n K_BLOCK) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
  td_client ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof. intros ca LB ws m b n ws' [H NS] Hin Hws'. split; [exact (td0_free ca LB ws m b n ws' H Hin Hws')|]. apply (nosub_sub ws); [exact NS|]. intros w Hw. exact (proj1 (proj1 (Hws' w) Hw)). Qed.
Lemma td_frame : forall ca LB ws m m', td_client ca LB ws m ->
  (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  td_client ca LB ws m'.
Proof. intros ca LB ws m m' [H NS] FR. split; [exact (td0_frame ca LB ws m m' H FR)| exact NS]. Qed.

End WithSegs.
End TD.
