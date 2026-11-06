(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjS1Lem SjS1Bytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Family.
Variable d : list Z.
Notation len := (zlength d).
Local Notation u := bv_unsigned.

Definition errb (er : word) : bool := negb (u er =? 0).

Definition g_buf (M : word -> option byte) (buf lenw : word) : Prop :=
  u lenw = len /\ len + 64 <= 2^20 /\ u buf + len + 64 <= 2^64 /\ Forall (fun c => 0 <= c < 256) d /\ mbytes M (u buf) (s1buf d).
Definition g_tab (M : word -> option byte) (sp : word) : Prop :=
  400 <= u sp /\ mbytes M (u sp - 400) ctab_bytes.
Definition g_main (M : word -> option byte) (a1 j dd er : word) : Prop :=
  exists acc, 4 * zlength acc = u dd /\ u a1 + u dd < 2^64 /\ mbytes M (u a1) (u32bytes (rev acc))
    /\ scan d = S1C d (u j) acc (errb er).
Definition g_str (M : word -> option byte) (a1 i k dd er : word) : Prop :=
  exists acc, 4 * zlength acc = u dd /\ u a1 + u dd + 4 < 2^64 /\ mbytes M (u a1) (u32bytes (rev (u i :: acc)))
    /\ scan d = SRES d (u i) acc (VSC d (u k) (errb er)).
Definition g_prim (M : word -> option byte) (a1 i k dd er : word) : Prop :=
  exists acc, 4 * zlength acc = u dd /\ u a1 + u dd + 4 < 2^64 /\ mbytes M (u a1) (u32bytes (rev (u i :: acc)))
    /\ u k + 1 < len /\ primc (byte_at d (u k + 1)) = true
    /\ scan d = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er).
Definition g_prim0 (M : word -> option byte) (a1 i k dd er : word) : Prop :=
  exists acc, 4 * zlength acc = u dd /\ u a1 + u dd + 4 < 2^64 /\ mbytes M (u a1) (u32bytes (rev (u i :: acc)))
    /\ scan d = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er).
Definition g_exit (M : word -> option byte) (a1 rc n this : word) : Prop :=
  (u rc = 0 <-> fst (scan d) = true) /\
  (u rc = 0 -> u n = zlength (snd (scan d)) /\ u a1 + 4 * u n + 12 < 2^64
               /\ mbytes M (u a1) (u32bytes (snd (scan d) ++ [len; len; 0]))
               /\ u this + 28 < 2^64 /\ mbytes M (u this + 24) (word_to_le_bytes 4 (Z_to_bv 64 0))).

(* [comment removed for export] *)
Definition s1_gp (id : nat) (vs : list word) (M : word -> option byte) : Prop :=
  match id, vs with
  | 1%nat, [buf; lenw] => g_buf M buf lenw
  | 2%nat, [sp] => g_tab M sp
  | 3%nat, [a1; j; dd; er] => g_main M a1 j dd er
  | 4%nat, [a1; i; k; dd; er] => g_str M a1 i k dd er
  | 5%nat, [a1; i; k; dd; er] => g_prim M a1 i k dd er
  | 6%nat, [a1; rc; n; this] => g_exit M a1 rc n this
  | 7%nat, [a1; i; k; dd; er] => g_prim0 M a1 i k dd er
  | _, _ => False
  end.
End Family.

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := EAlu ALU_ADD a b.
Definition s1_gfp (id : nat) (args : list expr) : list SG.gwin :=
  match id, args with
  | 1%nat, [buf; lenw] => [(buf, 0, eadd lenw (ELit 64))]
  | 2%nat, [sp] => [(sp, -400, ELit 256)]
  | 3%nat, [a1; j; dd; er] => [(a1, 0, dd)]
  | 4%nat, [a1; i; k; dd; er] => [(a1, 0, eadd dd (ELit 4))]
  | 5%nat, [a1; i; k; dd; er] => [(a1, 0, eadd dd (ELit 4))]
  | 6%nat, [a1; rc; n; this] => [(a1, 0, eadd (EMd M_MUL (ELit 4) n) (ELit 12)); (this, 24, ELit 4)]
  | 7%nat, [a1; i; k; dd; er] => [(a1, 0, eadd dd (ELit 4))]
  | _, _ => []
  end.

(* [comment removed for export] *)
Lemma u_add : forall x y : word, bv_unsigned (alu64 ALU_ADD x y) = (bv_unsigned x + bv_unsigned y) mod 2^64.
Proof. intros x y. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma u_mul : forall x y : word, bv_unsigned (mul_div M_MUL x y) = (bv_unsigned x * bv_unsigned y) mod 2^64.
Proof. intros x y. cbn [mul_div]. rewrite bv_mul_unsigned. reflexivity. Qed.
Lemma u_range : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_small. exact Hz. Qed.

Lemma win1 : forall (E : env) (M M' : word -> option byte) w0,
  (forall x : word, (exists w, In w [w0] /\ let '(lo, hi) := SG.win_den E w in (lo <= bv_unsigned x < hi)%Z) -> M' x = M x) ->
  forall x : word, fst (SG.win_den E w0) <= bv_unsigned x < snd (SG.win_den E w0) -> M' x = M x.
Proof. intros E M M' w0 H x Hx. apply H. exists w0. split; [left; reflexivity|]. destruct (SG.win_den E w0). exact Hx. Qed.

Lemma s1_gp_frame : forall d, SG.gp_frameP (s1_gp d) s1_gfp.
Proof.
  intros d id args E M M' HF HG.
  destruct id as [|[|[|[|[|[|[|[|id]]]]]]]]; try contradiction;
    (destruct args as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 r]]]]]]; cbn [map s1_gp s1_gfp] in HG, HF |- *; try contradiction;
     try (pose proof (win1 E M M' _ HF) as W; cbn [SG.win_den fst snd eadd edenot] in W; clear HF;
          repeat rewrite ?u_add, ?u_mul, ?u_lit in W by lia)).
  - (* [comment removed for export] *)
    destruct HG as (HL & HL20 & HB & HD & HM). split; [exact HL|]. split; [exact HL20|]. split; [exact HB|]. split; [exact HD|].
    assert (L : Z.of_nat (length (s1buf d)) = zlength d + 64) by (unfold s1buf, zlength; rewrite length_map, length_app, repeat_length; lia).
    eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
    intros x Hx. apply W. rewrite HL. pose proof (u_range (edenot E x0)). rewrite Z.mod_small by (unfold zlength in *; lia). lia.
  - (* [comment removed for export] *)
    destruct HG as (H4 & HM). split; [exact H4|].
    assert (L : Z.of_nat (length ctab_bytes) = 256) by (unfold ctab_bytes; rewrite length_map, length_seq; reflexivity).
    eapply mbytes_frame; [| lia | pose proof (u_range (edenot E x0)); lia | exact HM].
    intros x Hx. apply W. lia.
  - (* [comment removed for export] *)
    destruct HG as (acc & HD & HB & HM & HS). exists acc. split; [exact HD|]. split; [exact HB|]. split; [|exact HS].
    assert (L : Z.of_nat (length (u32bytes (rev acc))) = bv_unsigned (edenot E x2)) by (rewrite u32bytes_length, length_rev; unfold zlength in HD; lia).
    eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
    intros x Hx. apply W. lia.
  - (* [comment removed for export] *)
    destruct HG as (acc & HD & HB & HM & HS). exists acc. split; [exact HD|]. split; [exact HB|]. split; [|exact HS].
    assert (L : Z.of_nat (length (u32bytes (rev (bv_unsigned (edenot E x1) :: acc)))) = bv_unsigned (edenot E x3) + 4)
      by (rewrite u32bytes_length, length_rev; cbn [length]; unfold zlength in HD; lia).
    eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
    intros x Hx. apply W. pose proof (u_range (edenot E x3)). pose proof (u_range (edenot E x0)). rewrite Z.mod_small by lia. lia.
  - (* [comment removed for export] *)
    destruct HG as (acc & HD & HB & HM & HK). exists acc. split; [exact HD|]. split; [exact HB|]. split; [|exact HK].
    assert (L : Z.of_nat (length (u32bytes (rev (bv_unsigned (edenot E x1) :: acc)))) = bv_unsigned (edenot E x3) + 4)
      by (rewrite u32bytes_length, length_rev; cbn [length]; unfold zlength in HD; lia).
    eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
    intros x Hx. apply W. pose proof (u_range (edenot E x3)). pose proof (u_range (edenot E x0)). rewrite Z.mod_small by lia. lia.
  - (* [comment removed for export] *)
    destruct HG as (HC & HR). split; [exact HC|]. intros H0. destruct (HR H0) as (HN & HB & HM & HT & HZ).
    split; [exact HN|]. split; [exact HB|].
    assert (L : Z.of_nat (length (u32bytes (snd (scan d) ++ [zlength d; zlength d; 0]))) = 4 * bv_unsigned (edenot E x2) + 12).
    { rewrite u32bytes_length, length_app. cbn [length]. unfold zlength in HN. lia. }
    assert (L4 : Z.of_nat (length (word_to_le_bytes 4 (Z_to_bv 64 0))) = 4) by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
    split.
    + eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
      intros x Hx. apply HF. exists (x0, 0, eadd (EMd M_MUL (ELit 4) x2) (ELit 12)). split; [left; reflexivity|].
      cbn [SG.win_den eadd edenot]. rewrite u_add, u_mul, !u_lit by lia.
      pose proof (u_range (edenot E x2)). pose proof (u_range (edenot E x0)).
      rewrite (Z.mod_small (4 * _)) by lia. rewrite Z.mod_small by lia. lia.
    + split; [exact HT|].
      eapply mbytes_frame; [| pose proof (u_range (edenot E x3)); lia | lia | exact HZ].
      intros x Hx. apply HF. exists (x3, 24, ELit 4). split; [right; left; reflexivity|].
      cbn [SG.win_den edenot]. rewrite u_lit by lia. lia.
  - (* [comment removed for export] *)
    destruct HG as (acc & HD & HB & HM & HS). exists acc. split; [exact HD|]. split; [exact HB|]. split; [|exact HS].
    assert (L : Z.of_nat (length (u32bytes (rev (bv_unsigned (edenot E x1) :: acc)))) = bv_unsigned (edenot E x3) + 4)
      by (rewrite u32bytes_length, length_rev; cbn [length]; unfold zlength in HD; lia).
    eapply mbytes_frame; [| pose proof (u_range (edenot E x0)); lia | lia | exact HM].
    intros x Hx. apply W. pose proof (u_range (edenot E x3)). pose proof (u_range (edenot E x0)). rewrite Z.mod_small by lia. lia.
Qed.
