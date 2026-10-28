(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs U.S0EnframeBase.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition img_clear_ivs : list (Z * Z) :=
  [(0, 0x1000); (0x10000,0x34090); (0x34091,0x340d9); (0x440d9,0x44110); (0x641e8,0x64208); (0x44144,0x44190); (0x44198,0x441b0);
   (0x441b8,0x441d0); (0x441e0,0x441f0); (0x441f8,0x641e8); (0x64220,0x64450); (0x64458,0x64460); (0x64471,0x64478);
   (0x64480,0x64488); (0x64498,0x644a0); (0x644a8,0x644d8); (0x644e0,0x644e8);
   (0x64538,0x64698); (0x646a0,0x64818); (0x64820,0x64878); (0x64879,0x64880); (0x64890,0x66000)].

(* [comment removed for export] *)
Definition CTX : Z := 0x644e8.
Definition ctx_secret : Z := CTX.            (* [comment removed for export] *)
Definition ctx_init_done : Z := CTX + 8.     (* [comment removed for export] *)
Definition ctx_mmap_counter : Z := CTX + 12. (* [comment removed for export] *)
Definition ctx_free_meta_head : Z := CTX + 16.
Definition ctx_avail_meta : Z := CTX + 24.
Definition ctx_avail_meta_count : Z := CTX + 32.
Definition ctx_avail_meta_area_count : Z := CTX + 40.
Definition ctx_meta_alloc_shift : Z := CTX + 48.
Definition ctx_meta_area_head : Z := CTX + 56.
Definition ctx_meta_area_tail : Z := CTX + 64.
Definition ctx_avail_meta_areas : Z := CTX + 72.
Definition ctx_active (sc : Z) : Z := CTX + 80 + 8 * sc.          (* [comment removed for export] *)
Definition ctx_usage (sc : Z) : Z := CTX + 80 + 384 + 8 * sc.     (* [comment removed for export] *)
Definition ctx_unmap_seq : Z := CTX + 80 + 768.                    (* [comment removed for export] *)
Definition ctx_bounces : Z := CTX + 80 + 800.                      (* [comment removed for export] *)
Definition ctx_seq : Z := CTX + 80 + 832.                          (* [comment removed for export] *)
Definition ctx_brk : Z := CTX + 80 + 840.                          (* [comment removed for export] *)
Definition CTX_END : Z := 0x64888.

Lemma ctx_active_44 : ctx_active 44 = 0x64698. Proof. reflexivity. Qed.
Lemma ctx_usage_44 : ctx_usage 44 = 0x64818. Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W64K : Z := 17 * 4096 + 44 * 64 + 32.
Lemma W64K_val : W64K = 0x11b20. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record main_frame (sp0 : Z) (M : word -> option byte) : Prop := {
  mf_ra : cell M (sp0 - 56) 8 0x28c48;
  mf_s0 : cell M (sp0 - 64) 8 (sp0 + 8);       (* [comment removed for export] *)
  mf_s1 : cell M (sp0 - 72) 8 2;               (* [comment removed for export] *)
  mf_s2 : cell M (sp0 - 80) 8 0x13580;         (* [comment removed for export] *)
  mf_s3 : cell M (sp0 - 88) 8 (sp0 + 32);      (* [comment removed for export] *)
  mf_s4 : cell M (sp0 - 96) 8 0;
  mf_s5 : cell M (sp0 - 104) 8 0;
  mf_s6 : cell M (sp0 - 112) 8 0;
  mf_s7 : cell M (sp0 - 120) 8 0
}.

(* [comment removed for export] *)
Record world0 (area gm brkv mas tid hw : Z) (M : word -> option byte) : Prop := {
  (* [comment removed for export] *)
  w_secret  : cell M ctx_secret 8 run_secret;
  w_init    : cell M ctx_init_done 4 1;
  w_ctr     : cell M ctx_mmap_counter 4 1;
  w_fmh     : cell M ctx_free_meta_head 8 0;
  w_am      : cell M ctx_avail_meta 8 (area + 64);
  w_amc     : cell M ctx_avail_meta_count 8 100;
  w_amac    : cell M ctx_avail_meta_area_count 8 0;
  w_mas     : cell M ctx_meta_alloc_shift 8 mas;
  w_mah     : cell M ctx_meta_area_head 8 area;
  w_mat     : cell M ctx_meta_area_tail 8 area;
  w_amas    : cell M ctx_avail_meta_areas 8 (area + 4096);
  w_active44: cell M (ctx_active 44) 8 (area + 24);
  w_usage44 : cell M (ctx_usage 44) 8 1;
  w_seq     : cell M ctx_seq 1 1;
  w_brk     : cell M ctx_brk 8 brkv;
     (* [comment removed for export] *)
  (* [comment removed for export] *)
  w_area_chk  : cell M area 8 run_secret;     (* [comment removed for export] *)
  w_area_next : cell M (area + 8) 8 0;
  w_area_ns   : cell M (area + 16) 8 101;
  w_slot0_prev: cell M (area + 24) 8 (area + 24);
  w_slot0_next: cell M (area + 32) 8 (area + 24);
  w_slot0_mem : cell M (area + 40) 8 gm;
  w_slot0_msk : cell M (area + 48) 8 0;          (* [comment removed for export] *)
  w_slot0_W   : cell M (area + 56) 8 W64K;
  w_area_rest : zero_bytes M (area + 64) (4096 - 64);   (* [comment removed for export] *)
  w_area_def  : forall i, 0 <= i < 4096 -> M (Z_to_bv 64 (area + i)) <> None;
  (* [comment removed for export] *)
  w_grp_meta  : cell M gm 8 (area + 24);
  w_grp_aidx  : cell M (gm + 8) 1 0;             (* [comment removed for export] *)
  w_grp_pad   : zero_bytes M (gm + 9) 4;          (* [comment removed for export] *)
  w_enframe   : enframe_post M 0 65536 69616 (gm + 16) 1;
  w_grp_tail  : zero_bytes M (gm + 69628) 4;     (* [comment removed for export] *)
  w_grp_def   : forall i, 0 <= i < 69632 -> M (Z_to_bv 64 (gm + i)) <> None;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  w_area_al : area mod 4096 = 0;
  w_gm_al   : gm mod 4096 = 0;
  w_area_rng: 0x2000 <= area /\ area + 4096 <= alloc_ceiling;   (* [comment removed for export] *)
  w_area_img: area + 4096 <= 0x10000 \/ 0x67000 <= area;   (* [comment removed for export] *)
  w_gm_rng  : 0x66000 <= gm /\ gm + 69632 <= alloc_ceiling;
  w_disj    : area + 4096 <= gm \/ gm + 69632 <= area;   (* [comment removed for export] *)
  w_brkv    : brkv = area + 4096 \/ brkv = 2 ^ 64 - 1;
  w_masv    : mas = 0 \/ mas = 1;
  w_ghs     : 0 <= hw < 2 ^ 64;
  (* [comment removed for export] *)
  w_tid     : cell M 0x44138 4 tid;
  w_tidr    : 0 < tid < 2 ^ 22;
  w_errno   : exists e, 0 <= e < 2 ^ 32 /\ cell M 0x4413c 4 e;
  w_self    : cell M 0x44118 8 0x44118;
  w_canary  : cell M 0x64450 8 run_guard;
  w_pagesz  : cell M 0x644a0 8 4096;
  w_lock80  : cell M 0x644d8 8 hw;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  w_img     : Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs
}.

(* [comment removed for export] *)
Definition world0_fp (area gm : Z) (i : Z) : Prop :=
  (0 <= i < 0x1000) \/ (0x10000 <= i < 0x340d9) \/ (0x440d9 <= i < 0x66000) \/ (area <= i < area + 4096)
  \/ (gm <= i < gm + 32) \/ (gm + 65568 <= i < gm + 69632).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_agree : forall M M' a n v,
  a + Z.of_nat n < 2 ^ 64 -> 0 <= a ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  cell M a n v -> cell M' a n v.
Proof.
  intros M M' a n v Hnw Ha Hag Hc. unfold cell in *. rewrite <- Hc.
  apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia.
  replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
  apply Hag. lia.
Qed.

Lemma zero_bytes_agree : forall M M' a n,
  (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  zero_bytes M a n -> zero_bytes M' a n.
Proof.
  intros M M' a n Hag Hz i Hi. rewrite Hag by lia. apply Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma enframe_post_agree64K : forall M M' gm,
  0x66000 <= gm -> gm + 69632 < 2 ^ 64 ->
  (forall i, gm <= i < gm + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, gm + 65568 <= i < gm + 69632 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  enframe_post M 0 65536 69616 (gm + 16) 1 -> enframe_post M' 0 65536 69616 (gm + 16) 1.
Proof.
  intros M M' gm Hlo Hnw AG AT H.
  destruct H as [P_p P_e P_r P_q Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst P_p P_e P_r P_q.
  assert (AG2 : forall a k, (gm <= a /\ a + Z.of_nat k <= gm + 32) \/ (gm + 65568 <= a /\ a + Z.of_nat k <= gm + 69632) ->
            rdn RSEGS M' (Z_to_bv 64 a) k = rdn RSEGS M (Z_to_bv 64 a) k).
  { intros a k Hk. apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
    destruct Hk; [apply AG | apply AT]; lia. }
  constructor; cbn zeta; intros.
  - rewrite AG by lia. exact Pm4.
  - rewrite AG by lia. exact Pm3.
  - rewrite AG2 by (cbn; lia). exact Pm2.
  - rewrite AT by lia. apply Pzr. lia.
  - rewrite AT by lia. apply Pe5. lia.
  - rewrite AG2 by (cbn; lia). apply Pe4. lia.
  - rewrite AG by lia. apply Ps3. lia.
  - rewrite AG2 by (cbn; lia). apply Ps2. lia.
  - exact Pr.
Qed.

Theorem world0_frame : forall area gm brkv mas tid hw M M',
  world0 area gm brkv mas tid hw M ->
  (forall i, world0_fp area gm i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, 0 <= i < 69632 -> M' (Z_to_bv 64 (gm + i)) <> None) ->
  world0 area gm brkv mas tid hw M'.
Proof.
  intros area gm brkv mas tid hw M M' W Hag Hdef. pose proof alloc_ceiling_range as ACR.
  destruct W. unfold world0_fp in Hag.
  assert (AX : forall a (k : nat) , (0x10000 <= a /\ a + Z.of_nat k <= 0x340d9) \/ (0x440d9 <= a /\ a + Z.of_nat k <= 0x66000) \/ (area <= a /\ a + Z.of_nat k <= area + 4096)
            \/ (gm <= a /\ a + Z.of_nat k <= gm + 32) \/ (gm + 65568 <= a /\ a + Z.of_nat k <= gm + 69632) ->
            forall i, a <= i < a + Z.of_nat k -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros a k Hk i Hi. apply Hag. lia. }
  constructor.
  all: unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
    ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas,
    ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX, CTX_END in *.
  all: try assumption.
  all: try (eapply cell_agree; [ | | | eassumption]; [lia | lia | apply AX; lia]).
  - eapply zero_bytes_agree; [|exact w_area_rest0]. intros; apply Hag. lia.
  - intros i Hi. rewrite Hag by lia. apply w_area_def0. lia.
  - eapply zero_bytes_agree; [|exact w_grp_pad0]. intros; apply Hag. lia.
  - eapply enframe_post_agree64K; [ | | | | exact w_enframe0]; [lia | lia | |]; intros; apply Hag; lia.
  - eapply zero_bytes_agree; [|exact w_grp_tail0]. intros; apply Hag. lia.
  - cps_destruct w_errno0 as (e & He & Hc). exists e. split; [exact He|].
    eapply cell_agree; [ | | | exact Hc]; [lia | lia | apply AX; lia].
  - apply Forall_forall. intros [lo hi] Hin i Hi. cbn [fst snd] in Hi.
    pose proof (proj1 (Forall_forall _ _) w_img0 (lo, hi) Hin) as Hc. cbn [fst snd] in Hc.
    assert ((lo = 0 /\ hi = 0x1000) \/ (0x10000 <= lo /\ hi <= 0x340d9) \/ (0x440d9 <= lo /\ hi <= 0x66000)).
    { unfold img_clear_ivs in Hin. cbn in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; lia|]). destruct Hin. }
    rewrite Hag by lia. apply Hc. lia.
Qed.

Theorem main_frame_frame : forall sp0 M M',
  128 <= sp0 -> sp0 <= 2 ^ 64 ->
  (forall i, sp0 - 128 <= i < sp0 - 48 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  main_frame sp0 M -> main_frame sp0 M'.
Proof.
  intros sp0 M M' Hlo Hhi Hag [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  constructor; (eapply cell_agree; [ | | | eassumption]; [cbn; lia | lia | intros; apply Hag; cbn in *; lia]).
Qed.

End ACeilS1.
