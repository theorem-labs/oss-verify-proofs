(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Fs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim StoreOk Frame Hoare RefMemcpyLib AgentLib FuzzMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require Import TSet MstepsGrows ZStep ZMem ZPrune ZTac ZArr ZCall ZCallL ZRegKeys.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkModel CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint zlift (t : tree word) : tree Z :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => TNode (zlift l) (match v with Some x => Some (bv_unsigned x) | None => None end) (zlift r)
  end.

Lemma zden_zlift : forall t, zden (zlift t) = t.
Proof.
  induction t as [|l IHl v r IHr]; cbn; [reflexivity|].
  rewrite IHl, IHr. destruct v as [x|]; [|reflexivity]. rewrite w64_of_word. reflexivity.
Qed.

Lemma tget_zlift : forall k t,
  tget k (zlift t) = match tget k t with Some x => Some (bv_unsigned x) | None => None end.
Proof. induction k as [k IH|k IH|]; intros [|l v r]; cbn; auto. Qed.

Lemma zget_zlift : forall regs (r : reg), zget (zlift regs) (bv_key r) = bv_unsigned (reg_get regs r).
Proof.
  intros regs r. unfold zget, reg_get, bvmap_get. rewrite tget_zlift.
  destruct (tget (bv_key r) regs); reflexivity.
Qed.

Definition zpick (e : Z) (x : word) : Z := if bv_eqb (w64 e) x then e else bv_unsigned x.

Lemma w64_zpick : forall e x, w64 (zpick e x) = x.
Proof.
  intros e x. unfold zpick. destruct (bv_eqb (w64 e) x) eqn:E.
  - apply (proj1 (Fs.bv_eqb_eq _ _)) in E. exact E.
  - apply w64_of_word.
Qed.

Lemma zpick_hit : forall e, zpick e (w64 e) = e.
Proof. intros e. unfold zpick. rewrite bv_eqb_refl. reflexivity. Qed.

Fixpoint zback (g : positive -> Z) (t : tree word) : tree Z :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r =>
      TNode (zback (fun k => g (xO k)) l)
            (match v with Some x => Some (zpick (g xH) x) | None => None end)
            (zback (fun k => g (xI k)) r)
  end.

Lemma zden_zback : forall g t, zden (zback g t) = t.
Proof.
  intros g t. revert g. induction t as [|l IHl v r IHr]; intros g; cbn; [reflexivity|].
  rewrite IHl, IHr. destruct v as [x|]; [|reflexivity]. rewrite w64_zpick. reflexivity.
Qed.

Lemma tget_zback : forall t g k,
  tget k (zback g t) = match tget k t with Some x => Some (zpick (g k) x) | None => None end.
Proof.
  induction t as [|l IHl v r IHr]; intros g k; [destruct k; reflexivity|].
  destruct k as [k|k|]; cbn; [rewrite IHr | rewrite IHl |]; reflexivity.
Qed.

Lemma zget_zback : forall t g k,
  zget (zback g t) k = match tget k t with Some x => zpick (g k) x | None => 0 end.
Proof. intros t g k. unfold zget. rewrite tget_zback. destruct (tget k t); reflexivity. Qed.

Lemma getr_zkey : forall R (r : reg), bv_eqb r 0%bv = false -> getr (zden R) r = w64 (zget R (bv_key r)).
Proof. intros R r Hr. rewrite getr_zden. unfold zrd. rewrite <- bv_eqb0_is_x0, Hr. reflexivity. Qed.

Lemma getr_zupd : forall Rb l (r : reg), bv_eqb r 0%bv = false ->
  getr (zden (zupd Rb l)) r = w64 (zget_l Rb l (bv_key r)).
Proof. intros Rb l r Hr. rewrite (getr_zkey _ r Hr), zget_zupd. reflexivity. Qed.

Lemma getr_reg_get : forall regs (r : reg), bv_eqb r 0%bv = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.

Lemma zback_kept : forall R regs' g (r : reg),
  bv_eqb r 0%bv = false -> rkeys (zden R) regs' ->
  getr regs' r = getr (zden R) r -> g (bv_key r) = zget R (bv_key r) ->
  zget (zback g regs') (bv_key r) = zget R (bv_key r).
Proof.
  intros R regs' g r Hr RK EQ Hg. rewrite zget_zback.
  rewrite (getr_reg_get regs' r Hr), (getr_zkey R r Hr) in EQ. unfold reg_get, bvmap_get in EQ.
  destruct (tget (bv_key r) regs') as [x|] eqn:T.
  - subst x. rewrite Hg. apply zpick_hit.
  -
    destruct (tget (bv_key r) (zden R)) as [y|] eqn:T0.
    + exfalso. apply (RK (bv_key r)); [rewrite T0; discriminate | exact T].
    + rewrite tget_zden in T0. unfold zget. destruct (tget (bv_key r) R); [discriminate | reflexivity].
Qed.

Lemma zback_val : forall regs' g (r : reg) v,
  bv_eqb r 0%bv = false -> getr regs' r = w64 v -> 0 <= v < two64 -> g (bv_key r) = v ->
  zget (zback g regs') (bv_key r) = v.
Proof.
  intros regs' g r v Hr EQ Hv Hg. rewrite zget_zback.
  rewrite (getr_reg_get regs' r Hr) in EQ. unfold reg_get, bvmap_get in EQ.
  destruct (tget (bv_key r) regs') as [x|].
  - subst x. rewrite Hg. apply zpick_hit.
  - apply (f_equal bv_unsigned) in EQ. rewrite w64_unsigned, mod_small_u64 in EQ by exact Hv.
    rewrite <- EQ. reflexivity.
Qed.

Definition gres (R : tree Z) (res : Z) (k : positive) : Z := if (k =? 11)%positive then res else zget R k.


Lemma even_of_land : forall ret, Z.land ret (-2) = ret -> ret mod 2 = 0.
Proof.
  intros ret H.
  assert (E : Z.testbit ret 0 = false).
  { rewrite <- H. rewrite Z.land_spec. cbn. apply Bool.andb_false_r. }
  rewrite Z.bit0_odd in E. rewrite Zmod_odd. rewrite E. reflexivity.
Qed.

Lemma mod_two64_mod2 : forall a, (a mod two64) mod 2 = a mod 2.
Proof. intros a. apply Z.mod_mod_divide. exists 9223372036854775808. reflexivity. Qed.

Lemma ret_ok_of_land : forall ret, Z.land ret (-2) = ret -> ret_ok (w64 ret).
Proof.
  intros ret H. apply ret_ok_even. rewrite w64_unsigned, mod_two64_mod2. apply even_of_land. exact H.
Qed.



Lemma mem_wr_of_store_ok : forall segs M a (k : nat),
  store_ok segs M (Z_to_bv 64 a) k = true -> mem_wr segs M a (Z.of_nat k).
Proof.
  intros segs M a k. revert a. induction k as [|k IH]; intros a H i Hi; [lia|].
  cbn [store_ok] in H. change (Z_to_bv 64 a) with (w64 a) in H.
  destruct (wview segs M (w64 a)) eqn:Hv; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r, Hv. discriminate.
  - replace (a + i) with ((a + 1) + (i - 1)) by lia. apply IH; [|lia].
    rewrite word1_nat, w64_add_nat in H. exact H.
Qed.


Lemma readable_of_mem_arr : forall segs M a n f,
  mem_arr 1 segs M a n f ->
  forall i, 0 <= i < n -> exists b : byte, rdn segs M (Z_to_bv 64 (a + i)) 1 = Some [b].
Proof.
  intros segs M a n f H i Hi. exists (Z_to_bv 8 (f i)).
  pose proof (mem_arr_get segs 1 M a n f i H Hi) as E. unfold mem_is in E.
  replace (a + 1 * i) with (a + i) in E by lia. exact E.
Qed.

Lemma mem_arr_of_readable : forall segs M a n,
  0 <= a -> 0 <= n -> a + n <= two64 ->
  (forall i, 0 <= i < n -> exists b : byte, rdn segs M (Z_to_bv 64 (a + i)) 1 = Some [b]) ->
  exists f, mem_arr 1 segs M a n f /\ forall i, 0 <= i < n -> 0 <= f i < 256.
Proof.
  intros segs M a n Ha Hn Han H.
  exists (fun i => byte_at segs M (a + i)). split.
  - repeat split; try lia. intros i Hi. destruct (H i Hi) as [b Hb].
    unfold mem_is. change (Z.to_nat 1) with 1%nat. cbn [Z_to_le_bytes length].
    rewrite (byte_at_rdn segs M (a + i) b Hb), Z_to_bv_bv_unsigned.
    replace (a + 1 * i) with (a + i) by lia. exact Hb.
  - intros i Hi. apply byte_at_range.
Qed.

Definition flist (f : Z -> Z) (n : Z) : list Z := map f (zseq 0 (Z.to_nat n)).


Lemma zseq_In : forall s m x, In x (zseq s m) -> s <= x < s + Z.of_nat m.
Proof.
  intros s m. revert s. induction m as [|m IH]; intros s x H; cbn in H; [destruct H|].
  destruct H as [<-|H]; [lia|]. apply IH in H. lia.
Qed.

Lemma flist_bytes : forall f n, (forall i, 0 <= i < n -> 0 <= f i < 256) -> bytes (flist f n).
Proof.
  intros f n Hf. unfold bytes, flist. apply Forall_forall. intros b Hb.
  apply in_map_iff in Hb as (i & <- & Hi). apply zseq_In in Hi. apply Hf. lia.
Qed.

Lemma bytes_at_of_mem_arr : forall segs M a n f,
  mem_arr 1 segs M a n f -> (forall i, 0 <= i < n -> 0 <= f i < 256) ->
  bytes_at segs M a (Z.to_nat n) = flist f n.
Proof.
  intros segs M a n f H Hf. unfold flist.
  assert (G : forall (m : nat) s, 0 <= s -> s + Z.of_nat m <= n ->
            bytes_at segs M (a + s) m = map f (zseq s m)).
  { induction m as [|m IH]; intros s Hs Hm; [reflexivity|].
    cbn [bytes_at zseq map]. f_equal.
    - pose proof (mem_arr_get segs 1 M a n f s H ltac:(lia)) as E. unfold mem_is in E.
      change (Z.to_nat 1) with 1%nat in E. cbn [Z_to_le_bytes length] in E.
      replace (a + 1 * s) with (a + s) in E by lia.
      rewrite (byte_at_rdn segs M (a + s) _ E). rewrite Z_to_bv_unsigned. unfold bv_wrap.
      pose proof (Hf s ltac:(lia)). apply Z.mod_small. change (bv_modulus 8) with 256. lia_std.
    - replace (a + s + 1) with (a + (s + 1)) by lia. apply IH; lia. }
  pose proof (mem_arr_bounds segs 1 M a n f H) as (_ & Hn & _).
  replace a with (a + 0) at 1 by lia. apply G; [lia|]. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma rom_hyp_of_okG : forall lo hi (M : mem),
  0 <= lo -> hi <= two64 ->
  (forall x : word, lo <= bv_unsigned x < hi -> M x = None) ->
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros lo hi M Hlo Hhi H i Hi. apply H. change (Z_to_bv 64 i) with (w64 i).
  rewrite w64_unsigned, mod_small_u64 by lia. exact Hi.
Qed.

Lemma mpost_of_wbytes : forall segs M d bs,
  0 <= d -> d + Z.of_nat (length bs) <= two64 ->
  mpost segs M (wbytes M (w64 d) bs) d (d + Z.of_nat (length bs)) 0 0.
Proof.
  intros segs M d bs Hd Hn. split.
  - intros x Hx _. apply wbytes_out; assumption.
  - intros a n H. apply mem_wr_frame. exact H.
Qed.

Lemma mpost_of_frame_mod : forall segs M M' lo n,
  0 <= lo < two64 -> lo + n <= two64 ->
  frame_mod M M' [(Z_to_bv 64 lo, n)] -> mpost segs M M' lo (lo + n) 0 0.
Proof.
  intros segs M M' lo n Hlo Hhi [Ho Hg]. split.
  - intros x Hx _. apply Ho. cbn [outside]. split; [|exact I]. unfold in_rng.
    rewrite u64_lit by (rewrite <- two64_eq; exact Hlo). exact Hx.
  - intros a k H i Hi. apply (wview_grows segs M M' _ Hg). apply H. exact Hi.
Qed.

Lemma frame_mod_of_magree : forall M M' lo hi,
  0 <= lo < two64 -> lo <= hi ->
  magree M M' lo hi 0 0 -> mem_grows M M' -> frame_mod M M' [(Z_to_bv 64 lo, hi - lo)].
Proof.
  intros M M' lo hi Hlo Hhi HA HG. split; [|exact HG].
  intros a [Ha _]. unfold in_rng in Ha. rewrite u64_lit in Ha by (rewrite <- two64_eq; exact Hlo).
  apply HA; lia.
Qed.

Lemma frame_mod_of_mpost : forall segs M M' lo hi,
  0 <= lo < two64 -> lo <= hi ->
  mpost segs M M' lo hi 0 0 -> mem_grows M M' -> frame_mod M M' [(Z_to_bv 64 lo, hi - lo)].
Proof. intros segs M M' lo hi Hlo Hhi [HA _] HG. apply frame_mod_of_magree; assumption. Qed.

Fixpoint wranges (rs : list (Z * Z)) : list (word * Z) :=
  match rs with [] => [] | (lo, n) :: rs' => (Z_to_bv 64 lo, n) :: wranges rs' end.

Fixpoint ranges_lt (rs : list (Z * Z)) : Prop :=
  match rs with [] => True | (lo, n) :: rs' => 0 <= lo < two64 /\ ranges_lt rs' end.

Lemma outside_wranges : forall rs a, ranges_lt rs -> outside a (wranges rs) -> outside_all (bv_unsigned a) rs.
Proof.
  induction rs as [|[lo n] rs IH]; intros a Hr Ho; cbn in *; [exact I|].
  destruct Hr as [Hlo Hr]. destruct Ho as [H1 H2]. unfold in_rng in H1.
  rewrite u64_lit in H1 by (rewrite <- two64_eq; exact Hlo).
  split; [exact H1 | apply IH; assumption].
Qed.

Lemma frame_mod_of_mpostL : forall segs M M' rs,
  ranges_lt rs -> mpostL segs M M' rs -> mem_grows M M' -> frame_mod M M' (wranges rs).
Proof.
  intros segs M M' rs Hr [HA _] HG. split; [|exact HG].
  intros a Ha. apply HA. apply outside_wranges; assumption.
Qed.


Definition msteps_memcpy (segs : list Segment) (pc : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) rom,
    0 <= n < 2 ^ 64 -> length bs = Z.to_nat n ->
    rdn segs mem0 src (length bs) = Some bs ->
    store_ok segs mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    forall regs (ret : word), ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (w64 pc) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.

Definition memcpy_spec_at (segs : list Segment) (pc : Z) : Prop := forall Rb l M MD T d s bs n ret,
  m_halted MD = None ->
  zget_l Rb l 11%positive = d -> zget_l Rb l 12%positive = s -> zget_l Rb l 13%positive = n ->
  zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  mem_is segs M s bs -> Z.of_nat (length bs) = n -> mem_wr segs M d n ->
  0 <= d -> d + n < two64 -> 0 <= s -> s + n < two64 -> (d + n <= s \/ s + n <= d) ->
  (forall M' R',
     mpost segs M M' d (d + n) 0 0 ->
     mem_is segs M' d bs -> mem_is segs M' s bs -> mem_wr segs M' d n ->
     zget R' 11%positive = d ->
     zget R' 3%positive = zget_l Rb l 3%positive -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Lemma kept_back : forall Rb l regs' res (r : reg) (k : positive),
  bv_eqb r 0%bv = false -> bv_key r = k -> (k =? 11)%positive = false ->
  rkeys (zden (zupd Rb l)) regs' -> getr regs' r = getr (zden (zupd Rb l)) r ->
  zget (zback (gres (zupd Rb l) res) regs') k = zget_l Rb l k.
Proof.
  intros Rb l regs' res r k Hr Hk H11 RK EQ. subst k.
  rewrite (zback_kept (zupd Rb l) regs' _ r Hr RK EQ); [apply zget_zupd|].
  unfold gres. rewrite H11. reflexivity.
Qed.

Ltac key_norm := repeat match goal with |- context [bv_key ?x] => let k := eval cbv in (bv_key x) in change (bv_key x) with k end.

Theorem memcpy_glue : forall segs pc, msteps_memcpy segs pc -> memcpy_spec_at segs pc.
Proof.
  intros segs pc MC Rb l M MD T d s bs n ret Hh Ld Ls Ln Lr Hret HS Hlen HW Hd Hdn Hs Hsn Hdisj K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G10 : getr regs 10 = w64 d) by (subst regs R; rewrite (getr_zupd Rb l 10) by reflexivity; key_norm; rewrite Ld; reflexivity).
  assert (G11 : getr regs 11 = w64 s) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite Ls; reflexivity).
  assert (G12 : getr regs 12 = w64 n) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite Ln; reflexivity).
  assert (Hn : 0 <= n < 2 ^ 64) by (rewrite <- two64_eq; lia).
  assert (Hbs : length bs = Z.to_nat n) by lia.
  pose proof HS as HS'. unfold mem_is in HS'.
  assert (ST : store_ok segs M (w64 d) (length bs) = true)
    by (apply (store_ok_of_mem_wr segs M d n d (length bs) HW); lia).
  destruct (MC M (w64 d) (w64 s) n bs (seg_rom segs) Hn Hbs HS' ST
              ltac:(rewrite !w64_unsigned, !mod_small_u64 by lia; lia)
              ltac:(rewrite w64_unsigned, mod_small_u64 by lia; rewrite <- two64_eq; lia)
              ltac:(rewrite w64_unsigned, mod_small_u64 by lia; rewrite <- two64_eq; lia)
              regs (w64 ret) (ret_ok_of_land ret Hret) G1 G10 G11 G12)
    as (regs' & RUN & KP).
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  set (R' := zback (gres R d) regs').
  specialize (K (wbytes M (w64 d) bs) R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - rewrite <- Hlen. apply mpost_of_wbytes; lia.
  - apply mem_is_stored; lia.
  - apply mem_is_frame; [exact HS | unfold zdisj; lia].
  - apply mem_wr_frame. exact HW.
  -
    subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R d) 10 d); [reflexivity | | lia | reflexivity].
    rewrite (KP 10%bv) by (cbv; tauto). exact G10.
  - subst R' R. apply (kept_back Rb l regs' d 2); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 3); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 4); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 8); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 9); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 18); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 19); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 20); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 21); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 22); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 23); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 24); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 25); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 26); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - subst R' R. apply (kept_back Rb l regs' d 27); [reflexivity | reflexivity | reflexivity | exact RK | apply KP; cbv; tauto].
  - exists ms''. split; [| exact HQ].
    eapply msteps_trans; [exact RUN | exact RUN2].
Qed.


Definition msteps_adler32 (segs : list Segment) (pc FR : Z) (ROM : mem -> Prop) : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> FR <= usp < 2 ^ 64 ->
    store_ok segs m (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true ->
    (1 <= len -> adr + len <= usp - FR) ->
    ROM m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn segs m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps segs (mkst regs (w64 pc) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at segs m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - FR), FR)].

Definition adler32_spec_at (segs : list Segment) (pc FR : Z) (ROM : mem -> Prop) : Prop :=
  forall Rb l M MD T a adr v len usp ret f,
  m_halted MD = None ->
  zget_l Rb l 11%positive = a -> zget_l Rb l 12%positive = adr -> zget_l Rb l 13%positive = v ->
  zget_l Rb l 3%positive = usp -> zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  0 <= a < two64 -> 0 <= v < two64 -> v mod 4294967296 = len ->
  1 <= adr -> adr + len < two64 -> FR <= usp -> usp < two64 ->
  mem_wr segs M (usp - FR) FR -> (1 <= len -> adr + len <= usp - FR) ->
  ROM M ->
  mem_arr 1 segs M adr len f -> (forall i, 0 <= i < len -> 0 <= f i < 256) ->
  (forall M' R',
     mpost segs M M' (usp - FR) usp 0 0 ->
     zget R' 11%positive = adler32_z_model a (flist f len) ->
     zget R' 3%positive = usp -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Lemma kept_back_cs : forall Rb l regs' res (r : reg) (k : positive),
  bv_eqb r 0%bv = false -> bv_key r = k -> (k =? 11)%positive = false -> In r callee_saved ->
  rkeys (zden (zupd Rb l)) regs' -> keeps_cs (zden (zupd Rb l)) regs' ->
  zget (zback (gres (zupd Rb l) res) regs') k = zget_l Rb l k.
Proof.
  intros Rb l regs' res r k Hr Hk H11 Hin RK KC.
  apply (kept_back Rb l regs' res r k Hr Hk H11 RK). apply KC. exact Hin.
Qed.

Ltac kept_cs r := apply (kept_back_cs _ _ _ _ r); [reflexivity | reflexivity | reflexivity | cbv; tauto | assumption | assumption].

Theorem adler32_glue : forall segs pc FR ROM, 0 <= FR ->
  msteps_adler32 segs pc FR ROM -> adler32_spec_at segs pc FR ROM.
Proof.
  intros segs pc FR ROM HFR AD Rb l M MD T a adr v len usp ret f
         Hh La Ladr Lv Lsp Lr Hret Ha Hv Hlen Hadr Hnw Hfr Husp HW Hapart HROM HARR Hf K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G2 : getr regs 2 = w64 usp) by (subst regs R; rewrite (getr_zupd Rb l 2) by reflexivity; key_norm; rewrite Lsp; reflexivity).
  assert (G10 : getr regs 10 = w64 a) by (subst regs R; rewrite (getr_zupd Rb l 10) by reflexivity; key_norm; rewrite La; reflexivity).
  assert (G11 : getr regs 11 = w64 adr) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite Ladr; reflexivity).
  assert (G12 : getr regs 12 = w64 v) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite Lv; reflexivity).
  pose proof (mem_arr_bounds segs 1 M adr len f HARR) as (_ & Hlen0 & _ & _).
  assert (ST : store_ok segs M (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true).
  { apply (store_ok_of_mem_wr segs M (usp - FR) FR (usp - FR) (Z.to_nat FR) HW); [lia|]. rewrite Z2Nat.id by exact HFR. lia. }
  destruct (AD regs M (seg_rom segs) (w64 ret) usp a adr v len G1 (ret_ok_of_land ret Hret) G2 G10 G11 G12
              ltac:(rewrite <- two64_eq; exact Hv) ltac:(change (2 ^ 32) with 4294967296; exact Hlen)
              ltac:(rewrite <- two64_eq; exact Ha) Hadr ltac:(rewrite <- two64_eq; exact Hnw)
              ltac:(rewrite <- two64_eq; lia) ST Hapart HROM (readable_of_mem_arr segs M adr len f HARR))
    as (regs' & M' & RUN & RES & KC & FM).
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  rewrite (bytes_at_of_mem_arr segs M adr len f HARR Hf) in RES.
  set (res := adler32_z_model a (flist f len)) in RES.
  assert (Hres : 0 <= res < two64).
  { subst res. pose proof (adler32_z_model_range a (flist f len) (flist_bytes f len Hf)) as X. cbn in X |- *. lia_std. }
  set (R' := zback (gres R res) regs').
  specialize (K M' R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - replace usp with (usp - FR + FR) at 2 by lia. apply mpost_of_frame_mod; [lia | lia | exact FM].
  - subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R res) 10 res); [reflexivity | exact RES | exact Hres | reflexivity].
  - rewrite <- Lsp. subst R' R. kept_cs (2%bv : reg).
  - subst R' R. kept_cs (3%bv : reg).
  - subst R' R. kept_cs (4%bv : reg).
  - subst R' R. kept_cs (8%bv : reg).
  - subst R' R. kept_cs (9%bv : reg).
  - subst R' R. kept_cs (18%bv : reg).
  - subst R' R. kept_cs (19%bv : reg).
  - subst R' R. kept_cs (20%bv : reg).
  - subst R' R. kept_cs (21%bv : reg).
  - subst R' R. kept_cs (22%bv : reg).
  - subst R' R. kept_cs (23%bv : reg).
  - subst R' R. kept_cs (24%bv : reg).
  - subst R' R. kept_cs (25%bv : reg).
  - subst R' R. kept_cs (26%bv : reg).
  - subst R' R. kept_cs (27%bv : reg).
  - exists ms''. split; [| exact HQ]. eapply msteps_trans; [exact RUN | exact RUN2].
Qed.


Definition msteps_adler32_null0 (segs : list Segment) (pc : Z) : Prop :=
  forall regs m rom (retw : word),
    getr regs 1 = retw -> ret_ok retw -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    exists r,
      msteps segs (mkst regs (w64 pc) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r.

Definition adler32_null0_spec_at (segs : list Segment) (pc : Z) : Prop :=
  forall Rb l M MD T ret,
  m_halted MD = None ->
  zget_l Rb l 12%positive = 0 -> zget_l Rb l 13%positive = 0 ->
  zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  (forall R',
     zget R' 11%positive = 1 ->
     zget R' 3%positive = zget_l Rb l 3%positive -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Theorem adler32_null0_glue : forall segs pc, msteps_adler32_null0 segs pc -> adler32_null0_spec_at segs pc.
Proof.
  intros segs pc AD Rb l M MD T ret Hh L11 L12 Lr Hret K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G11 : getr regs 11 = w64 0) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite L11; reflexivity).
  assert (G12 : getr regs 12 = w64 0) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite L12; reflexivity).
  destruct (AD regs M (seg_rom segs) (w64 ret) G1 (ret_ok_of_land ret Hret) G11 G12) as (regs' & RUN & RES & KC).
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  set (R' := zback (gres R 1) regs').
  specialize (K R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R 1) 10 1); [reflexivity | exact RES | cbn; lia | reflexivity].
  - subst R' R. kept_cs (2%bv : reg).
  - subst R' R. kept_cs (3%bv : reg).
  - subst R' R. kept_cs (4%bv : reg).
  - subst R' R. kept_cs (8%bv : reg).
  - subst R' R. kept_cs (9%bv : reg).
  - subst R' R. kept_cs (18%bv : reg).
  - subst R' R. kept_cs (19%bv : reg).
  - subst R' R. kept_cs (20%bv : reg).
  - subst R' R. kept_cs (21%bv : reg).
  - subst R' R. kept_cs (22%bv : reg).
  - subst R' R. kept_cs (23%bv : reg).
  - subst R' R. kept_cs (24%bv : reg).
  - subst R' R. kept_cs (25%bv : reg).
  - subst R' R. kept_cs (26%bv : reg).
  - subst R' R. kept_cs (27%bv : reg).
  - exists ms''. split; [| exact HQ]. eapply msteps_trans; [exact RUN | exact RUN2].
Qed.

Definition msteps_adler32_nullF (segs : list Segment) (pc FR : Z) : Prop :=
  forall regs m rom (retw : word) (usp : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 ->
    FR <= usp < 2 ^ 64 ->
    store_ok segs m (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true ->
    exists r m',
      msteps segs (mkst regs (w64 pc) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 1
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - FR), FR)].

Definition adler32_nullF_spec_at (segs : list Segment) (pc FR : Z) : Prop :=
  forall Rb l M MD T usp ret,
  m_halted MD = None ->
  zget_l Rb l 12%positive = 0 -> zget_l Rb l 13%positive = 0 ->
  zget_l Rb l 3%positive = usp -> zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  FR <= usp -> usp < two64 -> mem_wr segs M (usp - FR) FR ->
  (forall M' R',
     mpost segs M M' (usp - FR) usp 0 0 ->
     zget R' 11%positive = 1 ->
     zget R' 3%positive = usp -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Theorem adler32_nullF_glue : forall segs pc FR, 0 <= FR ->
  msteps_adler32_nullF segs pc FR -> adler32_nullF_spec_at segs pc FR.
Proof.
  intros segs pc FR HFR AD Rb l M MD T usp ret Hh L11 L12 Lsp Lr Hret Hfr Husp HW K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G2 : getr regs 2 = w64 usp) by (subst regs R; rewrite (getr_zupd Rb l 2) by reflexivity; key_norm; rewrite Lsp; reflexivity).
  assert (G11 : getr regs 11 = w64 0) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite L11; reflexivity).
  assert (G12 : getr regs 12 = w64 0) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite L12; reflexivity).
  assert (ST : store_ok segs M (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true).
  { apply (store_ok_of_mem_wr segs M (usp - FR) FR (usp - FR) (Z.to_nat FR) HW); [lia|]. rewrite Z2Nat.id by exact HFR. lia. }
  destruct (AD regs M (seg_rom segs) (w64 ret) usp G1 (ret_ok_of_land ret Hret) G2 G11 G12
              ltac:(rewrite <- two64_eq; lia) ST) as (regs' & M' & RUN & RES & KC & FM).
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  set (R' := zback (gres R 1) regs').
  specialize (K M' R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - replace usp with (usp - FR + FR) at 2 by lia. apply mpost_of_frame_mod; [lia | lia | exact FM].
  - subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R 1) 10 1); [reflexivity | exact RES | cbn; lia | reflexivity].
  - rewrite <- Lsp. subst R' R. kept_cs (2%bv : reg).
  - subst R' R. kept_cs (3%bv : reg).
  - subst R' R. kept_cs (4%bv : reg).
  - subst R' R. kept_cs (8%bv : reg).
  - subst R' R. kept_cs (9%bv : reg).
  - subst R' R. kept_cs (18%bv : reg).
  - subst R' R. kept_cs (19%bv : reg).
  - subst R' R. kept_cs (20%bv : reg).
  - subst R' R. kept_cs (21%bv : reg).
  - subst R' R. kept_cs (22%bv : reg).
  - subst R' R. kept_cs (23%bv : reg).
  - subst R' R. kept_cs (24%bv : reg).
  - subst R' R. kept_cs (25%bv : reg).
  - subst R' R. kept_cs (26%bv : reg).
  - subst R' R. kept_cs (27%bv : reg).
  - exists ms''. split; [| exact HQ]. eapply msteps_trans; [exact RUN | exact RUN2].
Qed.
