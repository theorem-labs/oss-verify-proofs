(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KSC : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition TP : Z := 0xba7ed0.

(* [comment removed for export] *)
Lemma andi_m32_W : forall x, 0 <= x < 2 ^ 64 -> v_andi (W x) (-32) = W (x / 32 * 32).
Proof.
  intros x Hx. unfold v_andi. rewrite Wu by lia.
  change (bv_wrap 64 (-32)) with (2 ^ 64 - 2 ^ 5). rewrite land_high_mask by lia. reflexivity.
Qed.

Lemma andi_m32_aligned : forall x, 0 <= x < 2 ^ 64 -> x mod 32 = 0 -> v_andi (W x) (-32) = W x.
Proof.
  intros x Hx Hm. rewrite andi_m32_W by lia. f_equal.
  pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition FS_SIZE : Z := 11571200.
Definition ring_FP (fs : Z) (x : word) : Prop :=
  inr x fs 8 \/ inr x (fs + 4096) 16384 \/ inr x (fs + 36864) 1048576 \/ inr x (sha (fs + 36864)) 131072.

(* [comment removed for export] *)
Definition ring_idle (M : mem) (fs : Z) : Prop :=
  (exists h, 0 <= h < 2 ^ 64 /\ cell ASEGS M fs 8 (W h)) /\ zeros M (fs + 4096) 16384.

Definition ring_wr (M : mem) (fs : Z) : Prop :=
  wr_ok ASEGS M fs 8 /\ wr_ok ASEGS M (fs + 4096) 16384 /\ wr_ok ASEGS M (fs + 36864) 1048576
  /\ wr_ok ASEGS M (sha (fs + 36864)) 131072.

(* [comment removed for export] *)
Definition fs_wf (fs : Z) : Prop :=
  (A_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)) /\ fs + FS_SIZE <= HIMEM_END /\ fs mod 8 = 0.

Lemma ring_wr_grows : forall M M' fs, mem_grows M M' -> ring_wr M fs -> ring_wr M' fs.
Proof. intros M M' fs HG (H1 & H2 & H3 & H4). repeat split; eapply wr_ok_grows; eassumption. Qed.

(* [comment removed for export] *)
Lemma sha_frame : forall fs k, sha (fs + 36864 + 64 * k) = sha (fs + 36864) + 8 * k.
Proof. intros fs k. replace (fs + 36864 + 64 * k) with (fs + 36864 + 8 * (8 * k)) by lia. apply sha_add8. Qed.

(* [comment removed for export] *)
Definition G_UAR : Z := 0x5a85f0.
Definition C_UAR : Z := 0x670b40.
Definition uar_on (M : mem) : Prop := cell ASEGS M G_UAR 8 (W C_UAR) /\ cell ASEGS M C_UAR 4 (W 1).

Lemma uar_on_unch : forall M0 M (P : word -> Prop),
  unch M0 M P -> (forall y, P y -> A_IMG_END <= bv_unsigned y) -> uar_on M0 -> uar_on M.
Proof.
  intros M0 M P HU HP (H1 & H2). unfold uar_on, G_UAR, C_UAR, A_IMG_END in *.
  split; (eapply cell_unch; [exact HU | lia | (cbn; lia) | | eassumption]);
    intros x Hx HPx; apply HP in HPx; unfold inr in Hx; cbn in Hx; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record rt_iface (RTX : mem -> Prop) (RTXD : word -> Prop) (RSEP : Z -> Z -> Prop) (fs : Z) : Prop := {
  if_sep_dom : forall lo n x, RSEP lo n -> inr x lo n -> ~ RTXD x;
  if_sep_sub : forall lo n lo' n', RSEP lo n -> lo <= lo' -> lo' + n' <= lo + n -> RSEP lo' n';

  (* [comment removed for export] *)
  if_unch : forall M M' (P : word -> Prop), RTX M -> unch M M' P ->
      (forall x, P x -> A_IMG_END <= bv_unsigned x /\ ~ RTXD x) -> RTX M';

  (* [comment removed for export] *)
  if_malloc0 : forall rom (Post : word -> regfile -> mem -> Prop) M h S l,
      rt_ok M -> RTX M -> cell ASEGS M fs 8 (W h) -> 0 <= h < 2 ^ 64 -> zeros M (fs + 4096) 16384 ->
      (A_IMG_END <= fs /\ (fs + FS_SIZE <= SB \/ HIMEM_BEG <= fs)) /\ fs + FS_SIZE <= HIMEM_END ->
      wr_ok ASEGS M fs 8 -> wr_ok ASEGS M (fs + 4096) 16384 -> wr_ok ASEGS M (fs + 36864) 1048576 ->
      wr_ok ASEGS M (sha (fs + 36864)) 131072 ->
      A_IMG_END <= S - 208 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 208) -> wr_ok ASEGS M (S - 208) 208 ->
      RSEP (S - 208) 208 -> (fs + FS_SIZE <= S - 208 \/ S <= fs) ->
      length l = 32%nat -> rget l 2 = W S -> rget l 4 = W TP ->
      (forall l' M', let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
         length l' = 32%nat -> same_except KSC l l' -> rget l' 10 = W FB ->
         cell ASEGS M' fs 8 (W (h + 1)) -> cell ASEGS M' (fs + 4096 + k) 1 (W 1) ->
         cell ASEGS M' (FB + 24) 8 (W S) -> cell ASEGS M' (FB + 56) 8 (W (fs + 4096 + k)) -> zeros M' (sha FB) 8 ->
         unch M M' (fun x => inr x (S - 208) 208 \/ inr x fs 8 \/ inr x (fs + 4096 + k) 1 \/ inr x (FB + 24) 8
                             \/ inr x (FB + 56) 8 \/ inr x (sha FB) 8) -> mem_grows M M' ->
         reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
      reach ASEGS rom (W 0x1a6418) l M Post;

  (* [comment removed for export] *)
  if_amemcpy : forall rom (Post : word -> regfile -> mem -> Prop) M d s n S l,
      rt_ok M -> RTX M -> 0 <= n < 32 -> memrange s n -> memrange d n ->
      addr_ok M s n -> addr_ok M d n -> (0 < n -> shw_ok M s n) -> (0 < n -> shw_ok M d n) ->
      rd_ok M s n -> wr_ok ASEGS M d n -> A_IMG_END <= d -> (d + n <= s \/ s + n <= d) ->
      A_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok ASEGS M (S - 2224) 2224 ->
      (d + n <= S - 2224 \/ S <= d) ->
      length l = 32%nat -> rget l 2 = W S -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
      (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
         unch M M' (fun x => inr x (S - 2224) 2224 \/ inr x d n) -> mem_grows M M' ->
         reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
      reach ASEGS rom (W 0x1c197c) l M Post;

  (* [comment removed for export] *)
  if_strlen : forall rom (Post : word -> regfile -> mem -> Prop) M p N B k z S l,
      rt_ok M -> RTX M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= z -> z < N -> z - k < 2 ^ 31 ->
      bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) -> (p + z) / 8 * 8 + 8 <= p + N ->
      memrange (p + k) (z - k + 1) -> addr_ok M (p + k) (z - k + 1) -> shw_ok M (p + k) (z - k + 1) ->
      A_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok ASEGS M (S - 2224) 2224 ->
      (p + N <= S - 2224 \/ S <= p) ->
      length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) ->
      (forall l' M', length l' = 32%nat -> same_except KSC l l' -> rget l' 10 = W (z - k) ->
         unch M M' (fun x => inr x (S - 2224) 2224) -> mem_grows M M' ->
         reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
      reach ASEGS rom (W 0x1ac5c4) l M Post;

  (* [comment removed for export] *)
  if_strchr : forall rom (Post : word -> regfile -> mem -> Prop) M p N B k r c S l,
      rt_ok M -> RTX M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= r -> r < N -> r - k < 2 ^ 31 -> 0 < c < 256 ->
      (bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c) ->
      (forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c) ->
      (p + r) / 8 * 8 + 8 <= p + N ->
      memrange (p + k) (r - k + 1) -> addr_ok M (p + k) (r - k + 1) -> shw_ok M (p + k) (r - k + 1) ->
      A_IMG_END <= S - 2224 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2224) -> wr_ok ASEGS M (S - 2224) 2224 ->
      (p + N <= S - 2224 \/ S <= p) ->
      length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
      (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
         rget l' 10 = W (if Z.eqb (bv_unsigned (B r)) c then p + r else 0) ->
         unch M M' (fun x => inr x (S - 2224) 2224) -> mem_grows M M' ->
         reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
      reach ASEGS rom (W 0x1ac5d4) l M Post;

  (* [comment removed for export] *)
  if_strncmp : forall rom (Post : word -> regfile -> mem -> Prop) M p N B k z q n RB S l,
      rt_ok M -> RTX M -> bytes_at M p N B -> 0 < p /\ p + N < 2 ^ 63 -> 0 <= k <= z -> z < N ->
      bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
      0 < n <= 64 -> 0 < q /\ q + n < 2 ^ 63 ->
      (forall i, 0 <= i < n -> load_ok ASEGS M (W (q + i)) 1 (W (bv_unsigned (RB i)))) ->
      (forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0) ->
      memrange (p + k) (Z.min (z - k + 1) n) -> addr_ok M (p + k) (Z.min (z - k + 1) n) ->
      shw_ok M (p + k) (Z.min (z - k + 1) n) ->
      memrange q n -> addr_ok M q n -> shw_ok M q n ->
      A_IMG_END <= S - 2256 /\ S < 2 ^ 63 -> (S <= SB \/ HIMEM_BEG <= S - 2256) -> wr_ok ASEGS M (S - 2256) 2256 ->
      (p + N <= S - 2256 \/ S <= p) -> (q + n <= S - 2256 \/ S <= q) ->
      length l = 32%nat -> rget l 2 = W S -> rget l 10 = W (p + k) -> rget l 11 = W q -> rget l 12 = W n ->
      (forall l' M', length l' = 32%nat -> same_except KSC l l' ->
         (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
         unch M M' (fun x => inr x (S - 2256) 2256) -> mem_grows M M' ->
         reach ASEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
      reach ASEGS rom (W 0x1ac5d0) l M Post
}.
