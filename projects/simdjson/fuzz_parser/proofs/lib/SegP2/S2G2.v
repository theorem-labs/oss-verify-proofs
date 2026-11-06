(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2Dig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition mbytes (M : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

Fixpoint u32bytes (l : list Z) : list byte :=
  match l with [] => [] | x :: r => word_to_le_bytes 4 (Z_to_bv 64 x) ++ u32bytes r end.

Definition bufbytes (d : list Z) : list byte := map (Z_to_bv 8) (d ++ repeat 0 64).

(* [comment removed for export] *)
Definition mcell (M : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop := mbytes M a (Z_to_le_bytes w v).

Lemma u32bytes_length : forall l, length (u32bytes l) = (4 * length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [u32bytes length]; [reflexivity|]. rewrite length_app, IH. unfold word_to_le_bytes.
  rewrite length_Z_to_le_bytes. lia.
Qed.

Lemma bufbytes_length : forall d, Z.of_nat (length (bufbytes d)) = zlength d + 64.
Proof. intros d. unfold bufbytes, zlength. rewrite length_map, length_app, repeat_length. lia. Qed.

Lemma u_rng2 : forall (w : word), 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma u_lit2 : forall z, 0 <= z < 2 ^ 64 -> u (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma mbytes_frame : forall M M' a bs, (forall x : word, a <= u x < a + Z.of_nat (length bs) -> M' x = M x) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> mbytes M a bs -> mbytes M' a bs.
Proof.
  intros M M' a bs HF H0 H1 H i Hi. rewrite HF; [exact (H i Hi)|].
  rewrite u_lit2 by lia. lia.
Qed.

(* [comment removed for export] *)
Section Fam.
  Variable segs : list Segment.
  Variables (data idxs : list Z).
  Local Notation len := (zlength data).
  Local Notation n := (zlength idxs - 3).

  Definition gp2 (id : nat) (args : list word) (M : word -> option byte) : Prop :=
    match id, args with
    | 0%nat, [b; l; p; ko] =>
        u b + u l + 64 < 2 ^ 64 /\ u ko mod 4 = 0 /\ u ko / 4 + 1 <= n + 2 /\
        exists q, q < u l /\ bpath (mdata segs M (u b) (u l)) (u l) (u p) q /\ q < znth idxs (u ko / 4 + 1)
    | 1%nat, [b; l] =>
        u l = len /\ u b + u l + 64 < 2 ^ 64 /\ Forall (fun c => 0 <= c < 256) data /\ mbytes M (u b) (bufbytes data)
    | 2%nat, [x; nn] =>
        u nn = n /\ S1OUT data idxs n /\ u x + 4 * (n + 3) < 2 ^ 64 /\ mbytes M (u x) (u32bytes idxs)
    | 3%nat, [ko; v] => u ko mod 4 = 0 /\ u ko / 4 <= n + 2 /\ u v = znth idxs (u ko / 4)
    | 4%nat, [ko; e] => u ko mod 4 = 0 /\ u ko / 4 <= n + 2 /\ u e <= znth idxs (u ko / 4)
    | 5%nat, [oc; d; bw] =>
        u oc + 8 * u d + 8 < 2 ^ 64 /\ forall i, 0 <= i <= u d -> exists t, 0 <= t /\ 8 * t < u bw /\ mcell M (u oc + 8 * i) 4 t
    | 6%nat, [ia; d] =>
        u ia + u d + 1 < 2 ^ 64 /\
        forall i, 1 <= i <= u d -> M (Z_to_bv 64 (u ia + i)) = Some (Z_to_bv 8 0) \/ M (Z_to_bv 64 (u ia + i)) = Some (Z_to_bv 8 1)
    | 7%nat, [ko; ol; c] => u ko mod 4 = 0 /\ u ko / 4 <= n + 2 /\ 3 * u ol + u c <= 5 * znth idxs (u ko / 4)
    | 8%nat, [] => is_numstart (byte_at data (znth idxs 0)) = false
    | 9%nat, [] => is_numstart (byte_at data (znth idxs 0)) = true
    | 10%nat, [s; p; x] =>
        u s <= u p /\ u p <= len /\ (forall i, u s <= i < u p -> isdig (byte_at data i)) /\ u x = decval data (u s) (u p) mod 2 ^ 64
    | 11%nat, [p; dd] => u p < len /\ byte_at data (u p) = u dd + 48 /\ u dd <= 9
    | 12%nat, [s; s2; p; x] =>
        u s <= u s2 /\ u s2 <= u p /\ u p <= len /\ (forall i, u s <= i < u s2 -> byte_at data i = 48) /\
        (forall i, u s2 <= i < u p -> isdig (byte_at data i)) /\ ~ isdig (byte_at data (u p)) /\
        u x = decval data (u s) (u p) mod 2 ^ 64
    | _, _ => False
    end.
End Fam.

Definition eadd (a b : expr) : expr := EAlu ALU_ADD a b.
Definition emul (k : Z) (a : expr) : expr := EMd M_MUL (ELit k) a.

Definition gfp2 (id : nat) (args : list expr) : list SG.gwin :=
  match id, args with
  | 0%nat, [b; l; _; _] => [(b, 0, l)]
  | 1%nat, [b; l] => [(b, 0, eadd l (ELit 64))]
  | 2%nat, [x; nn] => [(x, 0, eadd (emul 4 nn) (ELit 12))]
  | 5%nat, [oc; d; _] => [(oc, 0, eadd (emul 8 d) (ELit 4))]
  | 6%nat, [ia; d] => [(ia, 1, d)]
  | _, _ => []
  end.

(* [comment removed for export] *)
Lemma u_eadd : forall E a b, u (edenot E (eadd a b)) = (u (edenot E a) + u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. cbn [eadd edenot alu64 alu]. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma u_emul : forall E k a, u (edenot E (emul k a)) = (u (Z_to_bv 64 k) * u (edenot E a)) mod 2 ^ 64.
Proof.
  intros E k a. unfold emul. change (edenot E (EMd M_MUL (ELit k) a)) with (mul_div M_MUL (edenot E (ELit k)) (edenot E a)).
  rewrite edenot_lit. cbn [mul_div]. rewrite bv_mul_unsigned. reflexivity.
Qed.

Lemma win1' : forall (E : env) (M M' : word -> option byte) w0,
  (forall x : word, (exists w, In w [w0] /\ let '(lo, hi) := SG.win_den E w in (lo <= u x < hi)%Z) -> M' x = M x) ->
  forall x : word, fst (SG.win_den E w0) <= u x < snd (SG.win_den E w0) -> M' x = M x.
Proof. intros E M M' w0 H x Hx. apply H. exists w0. split; [left; reflexivity|]. destruct (SG.win_den E w0). exact Hx. Qed.

Lemma gp2_frame : forall segs data idxs, SG.gp_frameP (gp2 segs data idxs) gfp2.
Proof.
  intros segs data idxs id args E M M' HF HG.
  destruct id as [|[|[|[|[|[|[|[|id]]]]]]]]; cbn [gp2 gfp2] in HG, HF |- *;
    try (destruct args as [|x0 [|x1 [|x2 [|x3 [|x4 r]]]]]; cbn [map] in HG |- *; exact HG);
    destruct args as [|x0 [|x1 [|x2 [|x3 [|x4 r]]]]]; cbn [map gp2 gfp2] in HG, HF |- *; try contradiction;
    pose proof (win1' E M M' _ HF) as W; cbn [SG.win_den fst snd] in W; clear HF;
    pose proof (u_rng2 (edenot E x0)); pose proof (u_rng2 (edenot E x1)).
  - (* [comment removed for export] *)
    destruct HG as (HB & HK & HK1 & q & Hq & Hp & Hqi). split; [exact HB|]. split; [exact HK|]. split; [exact HK1|].
    exists q. split; [exact Hq|]. split; [|exact Hqi].
    rewrite (mdata_ext segs M M'); [exact Hp | lia | lia | lia |]. intros x Hx. apply W. lia.
  - (* [comment removed for export] *)
    destruct HG as (HL & HB & HD & HM). split; [exact HL|]. split; [exact HB|]. split; [exact HD|].
    rewrite u_eadd, edenot_lit, u_lit2 in W by lia. rewrite Z.mod_small in W by lia.
    eapply mbytes_frame; [| lia | rewrite bufbytes_length; lia | exact HM].
    intros x Hx. apply W. rewrite bufbytes_length in Hx. lia.
  - (* [comment removed for export] *)
    destruct HG as (HN & HS & HB & HM). split; [exact HN|]. split; [exact HS|]. split; [exact HB|].
    rewrite u_eadd, u_emul, edenot_lit, !u_lit2 in W by lia. rewrite HN in W.
    assert (Lz : Z.of_nat (length (u32bytes idxs)) = 4 * (zlength idxs - 3 + 3)) by (rewrite u32bytes_length; unfold zlength; lia).
    rewrite (Z.mod_small (4 * _)) in W by lia. rewrite Z.mod_small in W by lia.
    eapply mbytes_frame; [| lia | lia | exact HM].
    intros x Hx. apply W. lia.
  - (* [comment removed for export] *)
    destruct HG as (HB & HC). split; [exact HB|]. pose proof (u_rng2 (edenot E x2)).
    rewrite u_eadd, u_emul, edenot_lit, !u_lit2 in W by lia.
    rewrite (Z.mod_small (8 * _)) in W by lia. rewrite Z.mod_small in W by lia.
    intros i Hi. destruct (HC i Hi) as (t & Ht & Ht' & Hm). exists t. split; [exact Ht|]. split; [exact Ht'|].
    unfold mcell in *. eapply mbytes_frame; [| lia | rewrite length_Z_to_le_bytes; lia | exact Hm].
    intros x Hx. apply W. rewrite length_Z_to_le_bytes in Hx. lia.
  - (* [comment removed for export] *)
    destruct HG as (HB & HC). split; [exact HB|]. intros i Hi.
    rewrite (W (Z_to_bv 64 (u (edenot E x0) + i))); [exact (HC i Hi)|]. rewrite u_lit2 by lia. lia.
Qed.
