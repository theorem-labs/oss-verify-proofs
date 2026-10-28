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

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs HUEnframeBase HUWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition capk (k : Z) : Z := 65536 * 2 ^ k.            (* [comment removed for export] *)
Definition nbk (k : Z) : Z := capk k + 4096.             (* [comment removed for export] *)
Definition offk (k : Z) : Z := 16 * (k + 2).             (* [comment removed for export] *)
Definition Wk (k : Z) : Z := nbk k + 4064.               (* [comment removed for export] *)
Definition resk (k : Z) : Z := 4060 - 16 * k.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition slotC (k area : Z) : Z := area + 24 + 40 * (k mod 2).
Definition slotF (k area : Z) : Z := area + 64 - 40 * (k mod 2).

Lemma capk_pos : forall k, 0 <= k -> 65536 <= capk k.
Proof. intros k Hk. unfold capk. pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) Hk). change (2 ^ 0) with 1 in H. lia. Qed.

Lemma capk_le : forall k, 0 <= k <= 10 -> capk k <= 67108864.
Proof. intros k Hk. unfold capk. pose proof (Z.pow_le_mono_r 2 k 10 ltac:(lia) ltac:(lia)). change (2 ^ 10) with 1024 in H. lia. Qed.

Lemma slotCF : forall k area, 0 <= k ->
  (slotC k area = area + 24 /\ slotF k area = area + 64) \/ (slotC k area = area + 64 /\ slotF k area = area + 24).
Proof.
  intros k area Hk. unfold slotC, slotF. pose proof (Z.mod_pos_bound k 2 ltac:(lia)). 
  destruct (Z.eq_dec (k mod 2) 0); [left|right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record world_k (sp0 k area B brkv mas tid can sec : Z) (M : word -> option byte) : Prop := {
  wk_k      : 1 <= k <= 10;
  (* [comment removed for export] *)
  wk_secret : cell M ctx_secret 8 sec;
  wk_init   : cell M ctx_init_done 4 1;
  wk_ctr    : cell M ctx_mmap_counter 4 (1 + k);
  wk_fmh    : cell M ctx_free_meta_head 8 (slotF k area);
  wk_am     : cell M ctx_avail_meta 8 (area + 104);          (* [comment removed for export] *)
  wk_amc    : cell M ctx_avail_meta_count 8 99;
  wk_amac   : cell M ctx_avail_meta_area_count 8 0;
  wk_mas    : cell M ctx_meta_alloc_shift 8 mas;
  wk_mah    : cell M ctx_meta_area_head 8 area;
  wk_mat    : cell M ctx_meta_area_tail 8 area;
  wk_amas   : cell M ctx_avail_meta_areas 8 (area + 4096);
  wk_active44 : cell M (ctx_active 44) 8 0;                  (* [comment removed for export] *)
  wk_usage44  : cell M (ctx_usage 44) 8 0;
  wk_seq    : cell M ctx_seq 1 (1 + 2 * k);
  wk_brk    : cell M ctx_brk 8 brkv;
     (* [comment removed for export] *)
  (* [comment removed for export] *)
  wk_area_chk  : cell M area 8 sec;
  wk_area_next : cell M (area + 8) 8 0;
  wk_area_ns   : cell M (area + 16) 4 101;                    (* [comment removed for export] *)
  wk_cur_prev  : cell M (slotC k area) 8 0;
  wk_cur_next  : cell M (slotC k area + 8) 8 0;
  wk_cur_mem   : cell M (slotC k area + 16) 8 B;
  wk_cur_avail : cell M (slotC k area + 24) 4 0;
  wk_cur_freed : cell M (slotC k area + 28) 4 0;
  wk_cur_W     : cell M (slotC k area + 32) 8 (Wk k);
  wk_free_prev : cell M (slotF k area) 8 (slotF k area);
  wk_free_next : cell M (slotF k area + 8) 8 (slotF k area);
  wk_free_mem  : cell M (slotF k area + 16) 8 0;
  wk_free_msk  : cell M (slotF k area + 24) 8 0;
  wk_free_W    : cell M (slotF k area + 32) 8 0;
  wk_area_rest : zero_bytes M (area + 104) (4096 - 104);      (* [comment removed for export] *)
  wk_area_def  : forall i, 0 <= i < 4096 -> M (Z_to_bv 64 (area + i)) <> None;
  (* [comment removed for export] *)
  wk_grp_meta : cell M B 8 (slotC k area);
  wk_grp_aidx : cell M (B + 8) 1 0;
  wk_grp_pad  : zero_bytes M (B + 9) 4;
  wk_enframe  : enframe_post M 0 (capk k) (nbk k - 16) (B + 16) (k + 1);
  wk_grp_tail : zero_bytes M (B + nbk k - 4) 4;
  wk_grp_def  : forall i, 0 <= i < nbk k -> M (Z_to_bv 64 (B + i)) <> None;
  (* [comment removed for export] *)
  wk_area_al : area mod 4096 = 0;
  wk_B_al    : B mod 4096 = 0;
  wk_sp0     : 0x7fff80000000 <= sp0 <= 0x800000000000;
  wk_area_rng: 0x2000 <= area /\ area + 4096 <= sp0 - 8388608;
  wk_area_img: area + 4096 <= 0x10000 \/ 0x355000 <= area;
  wk_B_rng   : 0x354000 <= B /\ B + nbk k <= sp0 - 8388608;
  wk_disj    : area + 4096 <= B \/ B + nbk k <= area;
  wk_brkv    : brkv = area + 4096 \/ brkv = 2 ^ 64 - 1;
  wk_masv    : mas = 0 \/ mas = 1;
  (* [comment removed for export] *)
  wk_tid     : cell M 0x331a40 4 tid;
  wk_tidr    : 0 < tid < 2 ^ 22;
  wk_errno   : exists e, 0 <= e < 2 ^ 32 /\ cell M 0x331a44 4 e;
  wk_self    : cell M 0x331a20 8 0x331a20;
  wk_canary  : cell M 0x351b28 8 can;
  wk_pagesz  : cell M 0x351da8 8 4096;
  (* [comment removed for export] *)
  wk_img     : Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs;
  (* [comment removed for export] *)
  wk_world   : (brkv = area + 4096 /\ mas = 0) \/ (brkv = 2 ^ 64 - 1 /\ mas = 1)
}.

(* [comment removed for export] *)
Definition world_k_fp (k area B : Z) (i : Z) : Prop :=
  (0 <= i < 0x1000) \/ (0x10000 <= i < 0x31ef09) \/ (0x32ef09 <= i < 0x354000) \/ (area <= i < area + 4096)
  \/ (B <= i < B + offk k) \/ (B + offk k + capk k <= i < B + nbk k).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma enframe_post_agree_k : forall M M' k B,
  1 <= k <= 10 -> 0x354000 <= B -> B + nbk k < 2 ^ 64 ->
  (forall i, B <= i < B + offk k -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, B + offk k + capk k <= i < B + nbk k -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  enframe_post M 0 (capk k) (nbk k - 16) (B + 16) (k + 1) ->
  enframe_post M' 0 (capk k) (nbk k - 16) (B + 16) (k + 1).
Proof.
  intros M M' k B Hk Hlo Hnw AG AT H.
  pose proof (capk_pos k ltac:(lia)) as Hc. unfold nbk, offk in *.
  destruct H as [P_p P_e P_r P_q Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst P_p P_e P_r P_q.
  assert (AG2 : forall a n, (B <= a /\ a + Z.of_nat n <= B + 16 * (k + 2))
                            \/ (B + 16 * (k + 2) + capk k <= a /\ a + Z.of_nat n <= B + (capk k + 4096)) ->
            rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n).
  { intros a n Hn. apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
    destruct Hn; [apply AG | apply AT]; lia. }
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

Theorem world_k_frame : forall sp0 k area B brkv mas tid can sec M M',
  world_k sp0 k area B brkv mas tid can sec M ->
  (forall i, world_k_fp k area B i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall i, 0 <= i < nbk k -> M' (Z_to_bv 64 (B + i)) <> None) ->
  world_k sp0 k area B brkv mas tid can sec M'.
Proof.
  intros sp0 k area B brkv mas tid can sec M M' W Hag Hdef.
  destruct W. unfold world_k_fp in Hag.
  pose proof (capk_pos k ltac:(lia)) as Hc. pose proof (slotCF k area ltac:(lia)) as HCF.
  assert (AX : forall a (n : nat) , (0x10000 <= a /\ a + Z.of_nat n <= 0x31ef09) \/ (0x32ef09 <= a /\ a + Z.of_nat n <= 0x354000) \/ (area <= a /\ a + Z.of_nat n <= area + 4096)
            \/ (B <= a /\ a + Z.of_nat n <= B + offk k) \/ (B + offk k + capk k <= a /\ a + Z.of_nat n <= B + nbk k) ->
            forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros a n Hn i Hi. apply Hag. lia. }
  constructor.
  all: unfold nbk, offk in *.
  all: unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
    ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas,
    ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX, CTX_END in *.
  all: try assumption.
  all: try (eapply cell_agree; [ | | | eassumption]; [cbn; lia | lia | apply AX; cbn; lia]).
  - eapply zero_bytes_agree; [|exact wk_area_rest0]. intros; apply Hag. lia.
  - intros i Hi. rewrite Hag by lia. apply wk_area_def0. lia.
  - eapply zero_bytes_agree; [|exact wk_grp_pad0]. intros; apply Hag. lia.
  - pose proof (enframe_post_agree_k M M' k B) as EA. unfold nbk, offk in EA.
    eapply EA; [ | | | | | exact wk_enframe0]; [lia | lia | lia | |]; intros; apply Hag; lia.
  - eapply zero_bytes_agree; [|exact wk_grp_tail0]. intros; apply Hag. lia.
  - destruct wk_errno0 as (e & He & Hce). exists e. split; [exact He|].
    eapply cell_agree; [ | | | exact Hce]; [cbn; lia | lia | apply AX; cbn; lia].
  - apply Forall_forall. intros [lo hi] Hin i Hi. cbn [fst snd] in Hi.
    pose proof (proj1 (Forall_forall _ _) wk_img0 (lo, hi) Hin) as Hcl. cbn [fst snd] in Hcl.
    assert ((lo = 0 /\ hi = 0x1000) \/ (0x10000 <= lo /\ hi <= 0x31ef09) \/ (0x32ef09 <= lo /\ hi <= 0x354000)).
    { unfold img_clear_ivs in Hin. cbn in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; lia|]). destruct Hin. }
    rewrite Hag by lia. apply Hcl. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_defined : forall M a m,
  0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat m -> M (Z_to_bv 64 i) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof.
  intros M a m Ha Hm Hdef. destruct m as [|m]; [reflexivity|].
  apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x) Hx). rewrite Z_to_bv_bv_unsigned in Hdef.
  destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

Lemma world_k_area_wr : forall sp0 k area B brkv mas tid can sec M d m,
  world_k sp0 k area B brkv mas tid can sec M -> 0 <= d -> d + Z.of_nat m <= 4096 ->
  store_ok RSEGS M (Z_to_bv 64 (area + d)) m = true.
Proof.
  intros sp0 k area B brkv mas tid can sec M d m W Hd Hm.
  pose proof (wk_area_rng _ _ _ _ _ _ _ _ _ _ W). pose proof (wk_sp0 _ _ _ _ _ _ _ _ _ _ W).
  apply store_ok_of_defined; [lia | lia |]. intros i Hi.
  replace i with (area + (i - area)) by lia. apply (wk_area_def _ _ _ _ _ _ _ _ _ _ W). lia.
Qed.

Lemma world_k_grp_wr : forall sp0 k area B brkv mas tid can sec M d m,
  world_k sp0 k area B brkv mas tid can sec M -> 0 <= d -> d + Z.of_nat m <= nbk k ->
  store_ok RSEGS M (Z_to_bv 64 (B + d)) m = true.
Proof.
  intros sp0 k area B brkv mas tid can sec M d m W Hd Hm.
  pose proof (wk_B_rng _ _ _ _ _ _ _ _ _ _ W). pose proof (wk_sp0 _ _ _ _ _ _ _ _ _ _ W).
  apply store_ok_of_defined; [lia | lia |]. intros i Hi.
  replace i with (B + (i - B)) by lia. apply (wk_grp_def _ _ _ _ _ _ _ _ _ _ W). lia.
Qed.
