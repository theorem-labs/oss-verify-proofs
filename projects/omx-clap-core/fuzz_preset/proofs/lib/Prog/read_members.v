From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame pj_get_c pj_get_str_c read_members_c.
Import ListNotations.
Open Scope Z_scope.

(* read_members (fuzz_preset.c:784-798 of the #102 source), out of line at READ_MEMBERS: the body walk against
   read_members_contract. Frame: sp - 80 .. sp holds ra, s0-s6 (sp - 64 .. sp) and `seen` (sp - 72); the callees
   pj_get (frame 48) and pj_get_str (frame 64) run below it, so every write is in (sp - 144, sp). The six key
   pointers of `top` are a table of 32-bit offsets at 0x104a0; the key strings and the table are read from the
   image (vm_compute), never assumed. The loop invariant and the call steps are ported from the inline walks
   EntD1_Call / EntD2_Lem / EntD2_Loop / EntSegD1 / EntSegD2. pj_get_str's contract asks (o, o + 56) to be apart
   from its frame even when o = 0, which this contract cannot give when sp < 200, so the two calls whose object
   can be NULL (plugin's "id", state's "encoding" / "bytes") take pj_get_str's own NULL path (rm_gs_null, nine
   instructions of the image) when the object is 0, and the contract otherwise. *)

Definition rm_blk (lblk : Z -> Z -> Prop) (S : Z) : Prop :=
  forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 144) 144.

Definition rm_key (k : Z) (K : list Z) : Prop :=
  0 <= k /\ k + Z.of_nat (length K) + 1 <= 2 ^ 64 /\
  forallb (fun c => (0 <? c) && (c <? 256)) K = true /\
  ro_bytes_b rsegs k (map (Z_to_bv 8) (K ++ [0])) = true.

Ltac rm_keyok :=
  unfold rm_key; refine (conj _ (conj _ (conj _ _)));
  first [apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].

Ltac rm_lit := first [reflexivity | apply bv_eq; vm_compute; reflexivity].

Ltac rm_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* an object pointer a callee may get: NULL, or a node whose footprint is outside the window *)
Definition rm_obj (m0 : word -> option byte) (L : Z -> Z -> Prop) (S z : Z) : Prop :=
  z = 0 \/ exists v Dz, pj_node rsegs m0 L z v Dz /\ (forall x, pj_foot z Dz x -> outside [(S - 144, S)] x).

Definition rm_hide (P : Prop) : Prop := P.

Lemma rm_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rm_apart : forall a n lo hi, 0 < n -> lo < hi -> (forall x, a <= x < a + n -> ~ (lo <= x < hi)) ->
  a + n <= lo \/ hi <= a.
Proof.
  intros a n lo hi Hn Hl H. destruct (Z_le_dec (a + n) lo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec hi a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max a lo)); lia.
Qed.

Lemma rm_cb : forall m k s, mem_inv rsegs m -> 0 <= k -> k + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  ro_bytes_b rsegs k (map (Z_to_bv 8) (s ++ [0])) = true -> pj_cbytes rsegs m k s.
Proof.
  intros m k s MI H0 H1 HF HB. split.
  - apply Forall_forall. intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc).
    apply andb_prop in HF as [A B]. apply Z.ltb_lt in A. apply Z.ltb_lt in B. lia.
  - apply ro_bytes_at; [exact MI | exact H0 | rewrite length_map, length_app; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact HB.
Qed.

Lemma rm_rng : forall m L o u Du, pj_node rsegs m L o u Du -> 0 <= o /\ o + 56 <= 2 ^ 64.
Proof.
  intros m L o u Du H. destruct (pj_view rsegs m L o u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  destruct Hh as ((_ & H0 & H1 & _) & _). lia.
Qed.

Lemma rm_hit_foot : forall m L o members D i kname v kids x,
  pj_node rsegs m L o (JObj members) D -> nth_error members i = Some (kname, v) -> pj_u64 rsegs m (o + 24) kids ->
  kids + 56 * Z.of_nat i <= x < kids + 56 * Z.of_nat i + 56 -> pj_foot o D x.
Proof.
  intros m L o members D i kname v kids x HN Ei Hk Hx.
  assert (Es : nth_error (slots (JObj members)) i = Some (Some kname, v))
    by (cbn [slots]; rewrite nth_error_map, Ei; reflexivity).
  destruct (pj_slot rsegs m L o (JObj members) D i (Some kname) v HN Es)
    as (num & str & kids' & keys & n & cap & D1 & Hh & _ & _ & _ & HF1 & _).
  pose proof Hh as (_ & _ & _ & _ & Hk' & _).
  rewrite (pj_u64_uniq rsegs m (o + 24) kids' kids Hk' Hk) in HF1.
  apply HF1. left. exact Hx.
Qed.

Lemma rm_get_sub : forall m L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  z = 0 \/ exists v Dz, pj_node rsegs m L z v Dz /\ (forall x, pj_foot z Dz x -> pj_foot o D x).
Proof.
  intros m L o t D kname z HN HR.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR; try (left; exact HR).
  destruct HR as [(_ & Hz)|(i & v & kids & Di & Ei & _ & Hk & Ez & Hv & Hinc)]; [left; exact Hz|]. right.
  exists v, Di. split; [subst z; exact Hv|].
  intros x [Hx|(b & Hb & Hx)].
  - subst z. exact (rm_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Lemma rm_node_tr : forall W m m' L p u Du, pj_node rsegs m L p u Du -> munch W m m' ->
  (forall x, pj_foot p Du x -> outside W x) -> pj_node rsegs m' L p u Du.
Proof.
  intros W m m' L p u Du H MU HO.
  exact (pj_node_munch rsegs W m L m' L p u Du H (pj_node_blocks rsegs u m L p Du H) MU HO).
Qed.

Lemma rm_res_tr : forall W m m' L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  munch W m m' -> (forall x, pj_foot o D x -> outside W x) -> pj_get_res m' L o t D kname z.
Proof.
  intros W m m' L o t D kname z HN HR MU HO.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR |- *; try exact HR.
  destruct HR as [HR|(i & v & kids & Di & Ei & Hf & Hk & Ez & Hv & Hinc)]; [left; exact HR|right].
  exists i, v, kids, Di. split; [exact Ei|]. split; [exact Hf|].
  split; [apply (pj_u64_eq rsegs m m'); [exact Hk | intros x Hx; apply MU; apply HO; left; lia]|].
  split; [exact Ez|]. split; [|exact Hinc].
  apply (rm_node_tr W m m' L z v Di Hv MU).
  intros x [Hx|(b & Hb & Hx)]; apply HO.
  - subst z. exact (rm_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Lemma rm_arr : forall m L p items Du i u, pj_node rsegs m L p (JArr items) Du -> nth_error items i = Some u ->
  exists kids cap D1, pj_u64 rsegs m (p + 24) kids /\ Z.of_nat i < cap /\ L kids (56 * cap) /\
    pj_node rsegs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> pj_foot p Du x).
Proof.
  intros m L p items Du i u HN Ei.
  assert (Es : nth_error (slots (JArr items)) i = Some (None, u))
    by (cbn [slots]; rewrite nth_error_map, Ei; reflexivity).
  destruct (pj_slot rsegs m L p (JArr items) Du i None u HN Es)
    as (num & str & kids & keys & n & cap & D1 & Hh & Hic & HLk & HP1 & HF1 & _).
  pose proof Hh as (_ & _ & _ & _ & Hk & _).
  exists kids, cap, D1. auto.
Qed.

Lemma rm_arr_hdr : forall m L p items Du, pj_node rsegs m L p (JArr items) Du ->
  pj_u32 rsegs m p 5 /\ pj_u64 rsegs m (p + 40) (Z.of_nat (length items)) /\
  exists kids cap, pj_u64 rsegs m (p + 24) kids /\ Z.of_nat (length items) <= cap /\
    (cap = 0 \/ L kids (56 * cap)).
Proof.
  intros m L p items Du HN. cbn [pj_node] in HN.
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & _).
  pose proof Hh as (_ & Ht & _ & _ & Hk & _ & Hn & _). subst n.
  split; [exact Ht|]. split; [exact Hn|]. exists kids, cap. split; [exact Hk|]. split; [lia|].
  destruct Hcap as [(C0 & _)|(_ & HL)]; [left; exact C0 | right; exact HL].
Qed.

Lemma rm_tag5 : forall m L p u Du, pj_node rsegs m L p u Du -> tag u = 5 -> exists items, u = JArr items.
Proof. intros m L p u Du _ H. destruct u; cbn in H; try lia. eexists; reflexivity. Qed.

Lemma rm_ty : forall m L p u Du, pj_node rsegs m L p u Du -> pj_u32 rsegs m p (tag u).
Proof.
  intros m L p u Du H. destruct (pj_view rsegs m L p u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  exact (proj1 (proj2 Hh)).
Qed.

Lemma rm_ro_out : forall m lo hi k bs, mem_inv rsegs m -> stk rsegs m lo hi -> ro_bytes rsegs k bs ->
  forall x, k <= x < k + Z.of_nat (length bs) -> ~ (lo <= x < hi).
Proof.
  intros m lo hi k bs MI (_ & _ & HS) HR x Hx Hin.
  destruct (nth_error bs (Z.to_nat (x - k))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  pose proof (ro_bytes_nth rsegs bs k _ b HR E) as (_ & Hro).
  replace (k + Z.of_nat (Z.to_nat (x - k))) with x in Hro by lia.
  destruct (HS x Hin) as (Hw & _).
  destruct (m (wa x)) as [b'|] eqn:Em.
  - pose proof (MI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa x) Hw Em). congruence.
Qed.

Lemma rm_key_apart : forall m lo S w k K, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - w -> 0 < w -> rm_key k K ->
  k + Z.of_nat (length K) + 1 <= S - w \/ S <= k.
Proof.
  intros m lo S w k K MI ST HL Hw (H0 & H1 & HF & HB).
  pose proof (ro_bytes_b_sound rsegs _ _ HB) as HR.
  assert (HA : forall x, k <= x < k + (Z.of_nat (length K) + 1) -> ~ (S - w <= x < S)).
  { intros x Hx Hin. apply (rm_ro_out m lo S k (map (Z_to_bv 8) (K ++ [0])) MI ST HR x);
      [rewrite length_map, length_app; cbn [length]; lia | lia]. }
  destruct (rm_apart k (Z.of_nat (length K) + 1) (S - w) S ltac:(lia) ltac:(lia) HA) as [E|E]; [left|right]; lia.
Qed.

Lemma rm_key_cb : forall m k K, mem_inv rsegs m -> rm_key k K -> pj_cbytes rsegs m k K.
Proof. intros m k K MI (H0 & H1 & HF & HB). exact (rm_cb m k K MI H0 H1 HF HB). Qed.

Lemma rm_root_out : forall m L S o t D, rm_blk L S -> pj_node rsegs m L o t D ->
  (S - 144 + 144 <= o \/ o + 56 <= S - 144) ->
  forall x, pj_foot o D x -> outside [(S - 144, S)] x.
Proof.
  intros m L S o t D HB HN HD x [Hx|((a & n) & Hin & Hx)]; cbn [outside].
  - split; [intros [C1 C2]; lia | exact I].
  - pose proof (pj_node_blocks rsegs t m L o D HN a n Hin) as HL.
    destruct (HB a n HL) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
    unfold pj_holds in Hx. cbn [fst snd] in Hx.
    split; [intros [C1 C2]; lia | exact I].
Qed.

Lemma rm_kid : forall m L z4 items D4 kids i u,
  pj_node rsegs m L z4 (JArr items) D4 -> pj_u64 rsegs m (z4 + 24) kids -> nth_error items i = Some u ->
  forall W, (forall x, pj_foot z4 D4 x -> outside W x) ->
  exists D1, pj_node rsegs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> outside W x).
Proof.
  intros m L z4 items D4 kids i u HN HK Ei W HO.
  destruct (rm_arr m L z4 items D4 i u HN Ei) as (kids' & cap & D1 & HK' & _ & _ & HP & HF).
  rewrite (pj_u64_uniq rsegs m (z4 + 24) kids' kids HK' HK) in HP, HF.
  exists D1. split; [exact HP|]. intros x Hx. exact (HO x (HF x Hx)).
Qed.

Lemma rm_hdr : forall W m0 m L z4 items D4 kids,
  pj_node rsegs m0 L z4 (JArr items) D4 -> (forall x, pj_foot z4 D4 x -> outside W x) -> munch W m0 m ->
  pj_u64 rsegs m0 (z4 + 24) kids ->
  ov_read_bytes rsegs m (wa z4) 4 = Some (le4 (Z_to_bv 64 5)) /\
  ov_read_bytes rsegs m (wa (z4 + 40)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length items)))) /\
  ov_read_bytes rsegs m (wa (z4 + 24)) 8 = Some (le8 (Z_to_bv 64 kids)).
Proof.
  intros W m0 m L z4 items D4 kids HN HO MU HK.
  pose proof (rm_node_tr W m0 m L z4 (JArr items) D4 HN MU HO) as HN'.
  destruct (rm_arr_hdr m L z4 items D4 HN') as (H5 & H40 & _).
  assert (HK' : pj_u64 rsegs m (z4 + 24) kids).
  { apply (pj_u64_eq rsegs m0 m); [exact HK|]. intros x Hx. apply MU. apply HO. left. lia. }
  split; [exact (rd4 rsegs m z4 5 H5)|]. split; [exact (rd8 rsegs m (z4 + 40) _ H40)|].
  exact (rd8 rsegs m (z4 + 24) kids HK').
Qed.

Lemma rm_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the window facts after a callee that wrote only (sq - w, sq), with sq = sp - 80 *)
Lemma rm_munch_call : forall (S w : Z) m0 m m', 0 <= w <= 64 ->
  munch [(S - 144, S)] m0 m -> munch [(S + -80 - w, S + -80)] m m' -> munch [(S - 144, S)] m0 m'.
Proof.
  intros S w m0 m m' Hw H1 H2. apply (munch_trans _ m0 m m' H1).
  apply (munch_weaken [(S + -80 - w, S + -80)]); [|exact H2].
  intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A & _).
  split; [intros [C1 C2]; apply A; split; lia | exact I].
Qed.

(* pj_get_str (PJ_GET_STR of the #102 image, 0x15d48) on a NULL object: it calls pj_get, whose first instruction
   returns 0 for NULL, and returns 0; it writes only ra into its own 16-byte frame. *)
Lemma rm_gs_null : forall (ra sq gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A : Z) (cs : list cell),
  stk rsegs m lo (bv_unsigned sq) -> lo <= bv_unsigned sq - 16 -> mem_inv rsegs m ->
  rw_cells rsegs m A cs -> disjoint_from [(bv_unsigned sq - 16, bv_unsigned sq)] A (Z.of_nat (cells_size cs)) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra sq gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sq - 16, bv_unsigned sq)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sq) /\ rw_cells rsegs m' A cs)
    (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x15d48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sq gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A cs
    ST LO MI FR FD.
  assert (FRh : rm_hide (rw_cells rsegs m A cs)) by exact FR. clear FR.
  pose proof (bv_unsigned_in_range 64 sq) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sq - 16, bv_unsigned sq)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.
  step. try if_true.
  step.
  step. try if_true.
  step. step. step.
  release_frame FR ST (bv_unsigned sq).
  unfold rm_hide in FRh.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  eapply rw_cells_transport; [exact FRh | exact MU | exact WM | exact FD].
Qed.

(* a call of pj_get_str from read_members' frame: the frame cells survive, the window grows by nothing *)
Lemma rm_gs : pj_get_str_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo o k : Z)
    (K : list Z) (cs : list cell),
  a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k -> bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) ->
  rm_obj m0 L (bv_unsigned sp) o -> rm_key k K ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 144 ->
  rw_cells rsegs m (bv_unsigned sp + -80) cs -> cells_size cs = 80%nat ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp + -80) /\ rw_cells rsegs m' (bv_unsigned sp + -80) cs)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PJ_GET_STR) fc None m (seg_rom rsegs)).
Proof.
  intros HG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    L lo o k K cs E0 E1 H16 HL HO HK MU WM MI ST LO FR FS.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rw_cells_bound rsegs m _ cs FR) as SB. rewrite FS in SB. change (Z.of_nat 80) with 80 in SB.
  assert (SU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  pose proof (rm_key_apart m lo (bv_unsigned sp + -80) 64 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  destruct HO as [O0|(u & Du & HNu & HFu)].
  - subst o a0. change (Z_to_bv 64 PJ_GET_STR) with (Z_to_bv 64 0x15d48).
    eapply evt_mono.
    { apply (rm_gs_null ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (bv_unsigned sp + -80) cs); rewrite ?SU.
      - exact ST.
      - lia.
      - exact MI.
      - exact FR.
      - rewrite FS. change (Z.of_nat 80) with 80. cbn [disjoint_from]. split; [lia | exact I]. }
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
                MU' & WM' & MI' & ST' & FR').
    rewrite SU in MU', ST'.
    exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [exact (rm_munch_call (bv_unsigned sp) 16 m0 m m' ltac:(lia) MU MU')|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
    split; [exact MI'|]. split; [exact ST' | exact FR'].
  - pose proof (rm_node_tr _ m0 m L o u Du HNu MU HFu) as HNm.
    pose proof (rm_rng m0 L o u Du HNu) as RG.
    assert (Hod : o + 56 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= o).
    { apply (rm_apart o 56 (bv_unsigned sp - 144) (bv_unsigned sp)); [lia | lia |].
      intros x Hx Hw. destruct (HFu x (or_introl Hx)) as (Hx1 & _). exact (Hx1 Hw). }
    eapply evt_cut.
    { apply (HG ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L o k K u Du lo E0 E1 (or_intror HNm)
               (rm_key_cb m k K MI HK)); rewrite ?SU.
      - intros a n Hl. destruct (HL a n Hl) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      - Z.div_mod_to_equations. lia.
      - exact ST.
      - lia.
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - exact MI. }
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
                MU' & WM' & MI' & ST' & _ & _).
    rewrite SU in MU', ST'.
    apply evt_done. exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [exact (rm_munch_call (bv_unsigned sp) 64 m0 m m' ltac:(lia) MU MU')|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
    split; [exact MI'|]. split; [exact ST'|].
    eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |].
    rewrite FS. change (Z.of_nat 80) with 80. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* a call of pj_get on a node of the tree: the result is NULL or a node whose footprint is in the parent's *)
Lemma rm_pg : pj_get_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo o k : Z)
    (K : list Z) (u : jv) (Du : list (Z * Z)) (cs : list cell),
  a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k -> bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) ->
  pj_node rsegs m0 L o u Du -> (forall x, pj_foot o Du x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  rm_key k K ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 144 ->
  rw_cells rsegs m (bv_unsigned sp + -80) cs -> cells_size cs = 80%nat ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte) (z : Z),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp + -80) /\ rw_cells rsegs m' (bv_unsigned sp + -80) cs /\
      r = Z_to_bv 64 z /\ rm_obj m0 L (bv_unsigned sp) z)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PJ_GET) fc None m (seg_rom rsegs)).
Proof.
  intros HG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    L lo o k K u Du cs E0 E1 H16 HL HNu HFu HK MU WM MI ST LO FR FS.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rw_cells_bound rsegs m _ cs FR) as SB. rewrite FS in SB. change (Z.of_nat 80) with 80 in SB.
  assert (SU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  pose proof (rm_key_apart m lo (bv_unsigned sp + -80) 64 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  pose proof (rm_node_tr _ m0 m L o u Du HNu MU HFu) as HNm.
  pose proof (rm_rng m0 L o u Du HNu) as RG.
  assert (Hod : o + 56 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= o).
  { apply (rm_apart o 56 (bv_unsigned sp - 144) (bv_unsigned sp)); [lia | lia |].
    intros x Hx Hw. destruct (HFu x (or_introl Hx)) as (Hx1 & _). exact (Hx1 Hw). }
  eapply evt_cut.
  { apply (HG ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L o k K u Du lo E0 E1 (or_intror HNm)
             (rm_key_cb m k K MI HK)); rewrite ?SU.
    - intros a n Hl. destruct (HL a n Hl) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - Z.div_mod_to_equations. lia.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
              MU' & WM' & MI' & ST' & _ & Hr).
  rewrite SU in MU', ST'.
  pose proof (rm_munch_call (bv_unsigned sp) 48 m0 m m' ltac:(lia) MU MU') as MU2.
  apply evt_done.
  destruct Hr as [(Ho & Er)|(_ & HN' & z & Er & HR)].
  - exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', 0.
    split; [exact E|]. split; [exact MU2|]. split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
    split; [exact MI'|]. split; [exact ST'|].
    split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |];
            rewrite FS; change (Z.of_nat 80) with 80; cbn [disjoint_from]; split; [lia | exact I]|].
    split; [exact Er | left; reflexivity].
  - exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', z.
    split; [exact E|]. split; [exact MU2|]. split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
    split; [exact MI'|]. split; [exact ST'|].
    split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |];
            rewrite FS; change (Z.of_nat 80) with 80; cbn [disjoint_from]; split; [lia | exact I]|].
    split; [exact Er|].
    assert (MUs : munch [(bv_unsigned sp - 144, bv_unsigned sp)] m' m0) by (intros x Hx; symmetry; exact (MU2 x Hx)).
    pose proof (rm_res_tr _ m' m0 L o u Du K z HN' HR MUs HFu) as HR0.
    destruct (rm_get_sub m0 L o u Du K z HNu HR0) as [Hz|(v & Dz & Hv & Hf)]; [left; exact Hz|right].
    exists v, Dz. split; [exact Hv|]. intros x Hx. exact (HFu x (Hf x Hx)).
Qed.

(* the loop over params->kids: the head of the loop (0x13f38) at index i, and the state after it (0x13f84) *)
Definition rm_head (m0 : word -> option byte) (lo : Z) (sp gp tp s0 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word) (z4 i : Z) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c : word) (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 (i - 1))
                 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
    stk rsegs m lo (bv_unsigned sp + -80) /\
    rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra].

Definition rm_out (m0 : word -> option byte) (lo : Z) (sp gp tp s0 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 c : word) (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f84) fc None m (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
    stk rsegs m lo (bv_unsigned sp + -80) /\
    rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra].

(* the contract's postcondition, for the saved registers xra, x0-x6 *)
Definition rm_post (m0 : word -> option byte) (L : Z -> Z -> Prop) (o : Z) (t : jv) (D : list (Z * Z)) (lo : Z)
    (xra sp gp tp x0 x1 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR xra sp gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                  x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc xra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ pj_node rsegs m' L o t D.

Ltac rm_ret_gs MU WM MI ST FR :=
  let msx := fresh "msx" in let P := fresh "P" in
  intros msx P; destruct_exs P;
  let E := fresh "E" in destruct P as [E P]; subst msx;
  clear MU WM MI ST FR;
  destruct P as (MU & WM & MI & ST & FR);
  try rewrite ret_pc_even by first [lia | reflexivity].

Ltac rm_ret_pg MU WM MI ST FR zn Hzn :=
  let msx := fresh "msx" in let P := fresh "P" in
  intros msx P; destruct_exs P;
  let E := fresh "E" in destruct P as [E P]; subst msx;
  clear MU WM MI ST FR;
  let Er := fresh "Er" in
  destruct P as (MU & WM & MI & ST & FR & Er & Hzn);
  lazymatch type of Er with ?r = Z_to_bv 64 ?zz => subst r; rename zz into zn end;
  try rewrite ret_pc_even by first [lia | reflexivity].

Ltac rm_side :=
  first [ eassumption
        | lazymatch goal with
          | |- rm_key _ _ => rm_keyok
          | |- cells_size _ = _ => reflexivity
          | |- _ = Z_to_bv 64 _ => rm_lit
          end ].

Section RM.
Hypothesis PJ_GET : pj_get_contract.
Hypothesis PJ_GET_STR : pj_get_str_contract.

Lemma rm_join : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 kids i : Z)
    (items : list jv) (D4 : list (Z * Z)) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  s6 = Z_to_bv 64 (i + 1 - 1) ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_head m0 lo sp gp tp s0 s7 s8 s9 s10 s11 F fc J x0 x1 x2 x3 x4 x5 x6 xra z4 (i + 1))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 kids i
    items D4 J x0 x1 x2 x3 x4 x5 x6 xra E6 HN HO HK MU WM MI ST FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  step. step. step.
  let mm := rm_mem in destruct (rm_hdr _ m0 mm L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
  step. try rewrite rm_sx32 by lia. step. step. try if_true.
  replace (56 * i + 56) with (56 * (i + 1)) by lia.
  subst s6.
  apply evt_done. unfold rm_head. do 17 eexists. eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

Lemma rm_body : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 kids i : Z)
    (items : list jv) (D4 : list (Z * Z)) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids -> 0 <= i < Z.of_nat (length items) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_head m0 lo sp gp tp s0 s7 s8 s9 s10 s11 F fc J x0 x1 x2 x3 x4 x5 x6 xra z4 (i + 1))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 (i - 1))
             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 kids i
    items D4 J x0 x1 x2 x3 x4 x5 x6 xra H16 HB LO HN HO HK HI MU WM MI ST FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  destruct (rm_arr_hdr m0 L z4 items D4 HN) as (_ & (C0 & _) & _).
  destruct (nth_error items (Z.to_nat i)) as [u|] eqn:Eu; [| apply nth_error_None in Eu; lia].
  destruct (rm_kid m0 L z4 items D4 kids (Z.to_nat i) u HN HK Eu _ HO) as (D1 & HP & HF).
  rewrite Z2Nat.id in HP, HF by lia.
  assert (HOBJ : rm_obj m0 L (bv_unsigned sp) (kids + 56 * i)) by (right; exists u, D1; split; [exact HP | exact HF]).
  destruct (rm_hdr _ m0 m L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
  step. step. step.
  rewrite rm_ltu by lia.
  replace (i - 1 + 1 <? Z.of_nat (length items)) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb].
  step. step. step. step.
  clear R0 R40 R24.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m0) (L := L) (lo := lo) (o := kids + 56 * i) (k := 0x10383)
      (K := [115; 121; 109; 98; 111; 108]); rm_side. }
  rm_ret_gs MU WM MI ST FR.
  step. if_cases HR.
  - eapply rm_join; [f_equal; lia | exact HN | exact HO | exact HK | exact MU | exact WM | exact MI | exact ST
                    | exact FR].
  - let mm := rm_mem in destruct (rm_hdr _ m0 mm L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
    step. step. step. step.
    clear R0 R40 R24.
    eapply evt_cut.
    { eapply (rm_pg PJ_GET) with (m0 := m0) (L := L) (lo := lo) (o := kids + 56 * i) (k := 0x1038a)
        (K := [118; 97; 108; 117; 101]) (u := u) (Du := D1); rm_side. }
    rm_ret_pg MU WM MI ST FR zv Hzv.
    step.
    eapply rm_join; [f_equal; lia | exact HN | exact HO | exact HK | exact MU | exact WM | exact MI | exact ST
                    | exact FR].
Qed.

Lemma rm_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 kids i : Z)
    (items : list jv) (D4 : list (Z * Z)) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  Z.to_nat (Z.of_nat (length items) - i) = n ->
  bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids -> 0 <= i <= Z.of_nat (length items) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_out m0 lo sp gp tp s0 s7 s8 s9 s10 s11 F fc J x0 x1 x2 x3 x4 x5 x6 xra)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 (i - 1))
             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 kids i
      items D4 J x0 x1 x2 x3 x4 x5 x6 xra En H16 HB LO HN HO HK HI MU WM MI ST FR.
  - pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ST as (LO0 & _ & _).
    destruct (rm_arr_hdr m0 L z4 items D4 HN) as (_ & (C0 & _) & _).
    destruct (rm_hdr _ m0 m L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
    step. step. step.
    rewrite rm_ltu by lia.
    replace (i - 1 + 1 <? Z.of_nat (length items)) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [negb].
    apply evt_done. unfold rm_out. do 23 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
  - eapply evt_cut.
    { eapply rm_body; [exact H16 | exact HB | exact LO | exact HN | exact HO | exact HK | lia | exact MU | exact WM
                      | exact MI | exact ST | exact FR]. }
    intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & c' &
                m' & E & MU' & WM' & MI' & ST' & FR').
    subst ms'.
    eapply IH; [| exact H16 | exact HB | exact LO | exact HN | exact HO | exact HK | lia | exact MU' | exact WM'
               | exact MI' | exact ST' | exact FR'].
    lia.
Qed.

Lemma rm_params : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c
                          : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 : Z)
    (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  rm_obj m0 L (bv_unsigned sp) z4 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_out m0 lo sp gp tp s0 s7 s8 s9 s10 s11 F fc J x0 x1 x2 x3 x4 x5 x6 xra)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L
    lo z4 J x0 x1 x2 x3 x4 x5 x6 xra H16 HB LO Hz4 MU WM MI ST FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  destruct (Z.eq_dec z4 0) as [Z4|Z4].
  { assert (B : bv_eqb (Z_to_bv 64 z4) (Z_to_bv 64 0) = true) by (subst z4; reflexivity).
    step. rewrite B. cbv iota.
    apply evt_done. unfold rm_out. do 23 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR. }
  destruct Hz4 as [Z4'|(v4 & D4 & HP4 & HF4)]; [lia|].
  pose proof (rm_rng m0 L z4 v4 D4 HP4) as RG4.
  assert (B4 : bv_eqb (Z_to_bv 64 z4) (Z_to_bv 64 0) = false) by (rewrite bv_eqb_lit by lia; apply Z.eqb_neq; exact Z4).
  step. rewrite B4. cbv iota.
  pose proof (rm_node_tr _ m0 m L z4 v4 D4 HP4 MU HF4) as HP4m.
  pose proof (rd4 rsegs m z4 (tag v4) (rm_ty m L z4 v4 D4 HP4m)) as RT.
  pose proof (tag_range v4) as TG.
  step. try rewrite rm_sx32 by lia. step. step.
  destruct (Z.eq_dec (tag v4) 5) as [T5|T5].
  - assert (B5 : negb (bv_eqb (Z_to_bv 64 (tag v4)) (Z_to_bv 64 5)) = false)
      by (rewrite bv_eqb_lit by lia; rewrite T5; reflexivity).
    rewrite B5. cbv iota.
    destruct (rm_tag5 m0 L z4 v4 D4 HP4 T5) as (items & ->).
    destruct (rm_arr_hdr m0 L z4 items D4 HP4) as (_ & _ & kids & cap & HK24 & _).
    clear RT. step. step. step. step. step. step.
    eapply (rm_loop (Z.to_nat (Z.of_nat (length items) - 0)) _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11
              _ _ _ _ c F fc m0 _ L lo z4 kids 0 items D4 J x0 x1 x2 x3 x4 x5 x6 xra);
      [reflexivity | exact H16 | exact HB | exact LO | exact HP4 | exact HF4 | exact HK24 | lia | exact MU | exact WM
      | exact MI | exact ST | exact FR].
  - assert (B5 : negb (bv_eqb (Z_to_bv 64 (tag v4)) (Z_to_bv 64 5)) = true)
      by (rewrite bv_eqb_lit by lia; apply negb_true_iff, Z.eqb_neq; exact T5).
    rewrite B5. cbv iota.
    apply evt_done. unfold rm_out. do 23 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

Lemma rm_fin : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c
                       : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo o : Z) (t : jv)
    (D : list (Z * Z)) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  pj_node rsegs m0 L o t D -> (forall x, pj_foot o D x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 144 ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_post m0 L o t D lo xra sp gp tp x0 x1 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13fac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L
    lo o t D J x0 x1 x2 x3 x4 x5 x6 xra HN HO MU WM MI ST LO FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  do 14 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rm_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  exact (rm_node_tr _ m0 _ L o t D HN MU HO).
Qed.

Lemma rm_tail : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c
                        : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo o z3 : Z) (t : jv)
    (D : list (Z * Z)) (J : list byte) (x0 x1 x2 x3 x4 x5 x6 xra : word),
  bv_unsigned sp mod 16 = 0 -> rm_blk L (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  pj_node rsegs m0 L o t D -> (forall x, pj_foot o D x -> outside [(bv_unsigned sp - 144, bv_unsigned sp)] x) ->
  rm_obj m0 L (bv_unsigned sp) z3 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 J; C8 c; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra] ->
  evt rsegs (rm_post m0 L o t D lo xra sp gp tp x0 x1 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 z3) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f84) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L
    lo o z3 t D J x0 x1 x2 x3 x4 x5 x6 xra H16 HB LO HN HO Hz3 MU WM MI ST FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  step. step. step. step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m0) (L := L) (lo := lo) (o := z3) (k := 0x102ac)
      (K := [101; 110; 99; 111; 100; 105; 110; 103]); rm_side. }
  rm_ret_gs MU WM MI ST FR.
  step. if_cases HR.
  - eapply rm_fin; [exact HN | exact HO | exact MU | exact WM | exact MI | exact ST | exact LO | exact FR].
  - step. step. step. step.
    eapply evt_cut.
    { eapply (rm_gs PJ_GET_STR) with (m0 := m0) (L := L) (lo := lo) (o := z3) (k := 0x10431)
        (K := [98; 121; 116; 101; 115]); rm_side. }
    rm_ret_gs MU WM MI ST FR.
    step.
    eapply rm_fin; [exact HN | exact HO | exact MU | exact WM | exact MI | exact ST | exact LO | exact FR].
Qed.

Theorem read_members_holds : read_members_contract.
Proof.
  unfold read_members_contract, READ_MEMBERS, RM_K, RM_F.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lblk o t D lo E0 HN LB SP16 ST LO SD MI.
  change (80 + 64) with 144 in *.
  subst a0. cbn [disjoint_from] in SD. destruct SD as (SD & _).
  assert (HB : rm_blk lblk (bv_unsigned sp)) by exact LB. clear LB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  pose proof (rm_root_out m lblk (bv_unsigned sp) o t D HB HN SD) as HO.
  assert (HDOC : rm_obj m lblk (bv_unsigned sp) o) by (right; exists t, D; split; [exact HN | exact HO]).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  (* prologue; params = pj_get(doc, "params") *)
  do 14 step.
  eapply evt_cut.
  { eapply (rm_pg PJ_GET) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x1033b)
      (K := [112; 97; 114; 97; 109; 115]) (u := t) (Du := D); rm_side. }
  rm_ret_pg MU WM MI ST FR z4 Hz4.
  (* state = pj_get(doc, "state") *)
  do 5 step.
  eapply evt_cut.
  { eapply (rm_pg PJ_GET) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x102fc)
      (K := [115; 116; 97; 116; 101]) (u := t) (Du := D); rm_side. }
  rm_ret_pg MU WM MI ST FR z3 Hz3.
  (* seen = 0; the six keys of top *)
  do 6 step.
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x10396)
      (K := [102; 111; 114; 109; 97; 116]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x10359)
      (K := [105; 100]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x103a2)
      (K := [110; 97; 109; 101]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x102b5)
      (K := [99; 97; 114; 114; 105; 101; 115]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x102f2)
      (K := [99; 114; 101; 97; 116; 101; 100; 65; 116]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  do 4 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x1034e)
      (K := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 6 step. try first [if_true | if_false].
  (* pj_get_str(pj_get(doc, "plugin"), "id") *)
  do 4 step.
  eapply evt_cut.
  { eapply (rm_pg PJ_GET) with (m0 := m) (L := lblk) (lo := lo) (o := o) (k := 0x10342)
      (K := [112; 108; 117; 103; 105; 110]) (u := t) (Du := D); rm_side. }
  rm_ret_pg MU WM MI ST FR zp Hzp.
  do 3 step.
  eapply evt_cut.
  { eapply (rm_gs PJ_GET_STR) with (m0 := m) (L := lblk) (lo := lo) (o := zp) (k := 0x10359)
      (K := [105; 100]); rm_side. }
  rm_ret_gs MU WM MI ST FR. do 4 step.
  (* the params loop, then state's "encoding" / "bytes" and the epilogue *)
  eapply evt_cut.
  { eapply rm_params; [exact SP16 | exact HB | exact LO | exact Hz4 | exact MU | exact WM | exact MI | exact ST
                      | exact FR]. }
  intros ms' (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
              s6' & t3' & t4' & t5' & t6' & c' & m' & E & MU' & WM' & MI' & ST' & FR').
  subst ms'.
  eapply evt_mono.
  { eapply rm_tail; [exact SP16 | exact HB | exact LO | exact HN | exact HO | exact Hz3 | exact MU' | exact WM'
                    | exact MI' | exact ST' | exact FR']. }
  intros ms' H. exact H.
Qed.

End RM.
