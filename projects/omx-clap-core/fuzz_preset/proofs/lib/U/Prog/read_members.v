From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import pj_get_c pj_get_str_c read_members_c.
Import ListNotations.
Open Scope Z_scope.

(* read_members of the #102 ubsan image (fuzz_preset.c:784-798), out of line at READ_MEMBERS 0x13e94, against the entry's
   read_members_contract. The body: pj_get (0x16468) of "params" and "state"; pj_get_str (0x16594) of the six keys of the
   static `top` table (int32 offsets from 0x10490 in the image); pj_get_str (pj_get (doc, "plugin"), "id"); the params
   loop, whose UBSan checks (alignment of params, pointer overflow of &kids[i]) trap to `unimp` at 0x14088; the state
   pair. The frame is 96 bytes at sp - 96 (saves ra, s0-s8; `seen` at sp - 88); the callees' frames lie in
   (sp - 192, sp - 96). The key strings and the table are read from the image (vm_compute), never assumed.
   A NULL argument (plugin or state absent) goes through the callee's own NULL path in the image (stepped below): the
   callee contracts ask (o, o + 56) apart from their frame, which a NULL o near a low stack need not be. *)

(* ---------- generic facts (ported from the entry's inline walk, EntUD1_Base / EntUD2_Lem) ---------- *)

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

Lemma rm_apart : forall a n lo hi, 0 < n -> lo < hi -> (forall x, a <= x < a + n -> ~ (lo <= x < hi)) ->
  a + n <= lo \/ hi <= a.
Proof.
  intros a n lo hi Hn Hl H. destruct (Z_le_dec (a + n) lo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec hi a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max a lo)); lia.
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

Lemma rm_munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. exact (H x Hx). Qed.

Lemma rm_munch_in : forall lo hi lo' hi' m0 m m', lo <= lo' -> hi' <= hi ->
  munch [(lo, hi)] m0 m -> munch [(lo', hi')] m m' -> munch [(lo, hi)] m0 m'.
Proof.
  intros lo hi lo' hi' m0 m m' H1 H2 MU MU'. apply (munch_trans _ m0 m m' MU).
  apply (munch_weaken [(lo', hi')]); [|exact MU'].
  intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A & _).
  split; [intros [C1 C2]; apply A; split; lia | exact I].
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

(* a key string of the image: NUL-free bytes then 0, read-only *)
Definition rm_key (k : Z) (K : list Z) : Prop :=
  0 <= k /\ k + Z.of_nat (length K) + 1 <= 2 ^ 64 /\
  forallb (fun c => (0 <? c) && (c <? 256)) K = true /\
  ro_bytes_b rsegs k (map (Z_to_bv 8) (K ++ [0])) = true.

Ltac rm_keyok :=
  unfold rm_key; refine (conj _ (conj _ (conj _ _)));
  first [apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].

Ltac rm_lit := first [reflexivity | apply bv_eq; vm_compute; reflexivity].

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

Lemma rm_rng : forall m L o u Du, pj_node rsegs m L o u Du -> 0 <= o /\ o + 56 <= 2 ^ 64.
Proof.
  intros m L o u Du H. destruct (pj_view rsegs m L o u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  destruct Hh as ((_ & H0 & H1 & _) & _). lia.
Qed.

Lemma rm_al : forall m L o u Du, pj_node rsegs m L o u Du -> o mod 8 = 0.
Proof.
  intros m L o u Du H. destruct (pj_view rsegs m L o u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  destruct Hh as ((A & _) & _). exact A.
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

Lemma rm_kid : forall m L z4 items D4 kids i u,
  pj_node rsegs m L z4 (JArr items) D4 -> pj_u64 rsegs m (z4 + 24) kids -> nth_error items i = Some u ->
  forall W, (forall x, pj_foot z4 D4 x -> outside W x) ->
  exists D1 cap, Z.of_nat i < cap /\ L kids (56 * cap) /\ pj_node rsegs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> outside W x).
Proof.
  intros m L z4 items D4 kids i u HN HK Ei W HO.
  destruct (rm_arr m L z4 items D4 i u HN Ei) as (kids' & cap & D1 & HK' & Hic & HLk & HP & HF).
  rewrite (pj_u64_uniq rsegs m (z4 + 24) kids' kids HK' HK) in HP, HF, HLk.
  exists D1, cap. split; [exact Hic|]. split; [exact HLk|]. split; [exact HP|].
  intros x Hx. exact (HO x (HF x Hx)).
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

Lemma rm_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rm_signed_lit : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2^63). lia.
Qed.

Lemma rm_mulh : forall z, 0 <= z -> 56 * z < 2 ^ 63 ->
  Z.lxor (Z.modulo (Z.shiftr (bv_signed (Z_to_bv 64 z) * 56) 64) 18446744073709551616)
         (Z.modulo (Z.shiftr (bv_signed (Z_to_bv 64 (Z.modulo (Z.shiftl z 6) 18446744073709551616 -
                                                     Z.modulo (Z.shiftl z 3) 18446744073709551616))) 63)
                   18446744073709551616) = 0.
Proof.
  intros z H0 H1.
  rewrite (rm_signed_lit z) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (z * 64)) by lia. rewrite (Z.mod_small (z * 8)) by lia.
  replace (z * 64 - z * 8) with (56 * z) by lia.
  rewrite (rm_signed_lit (56 * z)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.div_small (z * 56)) by lia. rewrite (Z.div_small (56 * z)) by lia. reflexivity.
Qed.

Ltac rm_has_cmp x := idtac; match x with context [Z.eqb _ _] => idtac | context [Z.ltb _ _] => idtac | context [Z.leb _ _] => idtac end.

Ltac rm_is_binop f :=
  lazymatch f with
  | Z.add => idtac | Z.sub => idtac | Z.mul => idtac | Z.modulo => idtac | Z.div => idtac | Z.pow => idtac
  | Z.lxor => idtac | Z.lor => idtac | Z.land => idtac | Z.shiftr => idtac | Z.shiftl => idtac
  | Z.eqb => idtac | Z.ltb => idtac | Z.leb => idtac
  end.

Ltac rm_fold_lits :=
  repeat match goal with
  | |- context [?f ?a ?b] => rm_is_binop f; is_Zlit_zb a; is_Zlit_zb b;
                             let v := eval vm_compute in (f a b) in change (f a b) with v
  end.

Ltac rm_solve_c :=
  unfold bv_eqb, bv_ltu, bv_leu;
  rewrite ?unsigned_lit_wrap, ?rm_land7;
  rewrite ?Z.shiftl_mul_pow2 by lia;
  repeat (cbn [Z.b2z]; rm_fold_lits;
          match goal with
          | |- context [Z.eqb ?a ?b] => assert_fails (rm_has_cmp a); assert_fails (rm_has_cmp b); destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => assert_fails (rm_has_cmp a); assert_fails (rm_has_cmp b); destruct (Z.ltb_spec a b)
          | |- context [Z.leb ?a ?b] => assert_fails (rm_has_cmp a); assert_fails (rm_has_cmp b); destruct (Z.leb_spec a b)
          end);
  cbn [Z.b2z]; rm_fold_lits;
  first [reflexivity | exfalso; Z.div_mod_to_equations; lia].

(* a UBSan check that does not fire: its branch to the trap is not taken *)
Ltac rm_trapfree :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; rm_solve_c); cbv beta iota
  end.

Ltac rm_br_true :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by (symmetry; rm_solve_c); cbv beta iota
  end.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* ---------- the frame ---------- *)

(* the blocks of the tree: placed, aligned, and apart from the 192-byte window below sp *)
Definition rm_blk (lblk : Z -> Z -> Prop) (sp : word) : Prop :=
  forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\
    disjoint_from [(a, a + n)] (bv_unsigned sp - 192) 192.

(* the state during the body, relative to the entry memory m0: only the window changed, and the frame (sp - 96, sp)
   holds the cells cs *)
Definition rm_st (m0 m : word -> option byte) (sp : word) (lo : Z) (cs : list cell) : Prop :=
  munch [(bv_unsigned sp - 192, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp + -96) /\ rw_cells rsegs m (bv_unsigned sp + -96) cs.

(* a pointer the body passes on: NULL, or a node of the entry memory whose foot is outside the window *)
Definition rm_sub (m0 : word -> option byte) (lblk : Z -> Z -> Prop) (sp : word) (p : Z) : Prop :=
  p = 0 \/ exists v Dv, pj_node rsegs m0 lblk p v Dv /\
    (forall x, pj_foot p Dv x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x).

Lemma rm_root : forall m lblk sp o t D, rm_blk lblk sp -> disjoint_from [(o, o + 56)] (bv_unsigned sp - 192) 192 ->
  pj_node rsegs m lblk o t D -> forall x, pj_foot o D x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x.
Proof.
  intros m lblk sp o t D HB HD HN x [Hx|((a & n) & Hin & Hx)]; cbn [outside].
  - cbn [disjoint_from] in HD. split; [lia | exact I].
  - pose proof (pj_node_blocks rsegs t m lblk o D HN a n Hin) as HL.
    destruct (HB a n HL) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
    unfold pj_holds in Hx. cbn [fst snd] in Hx. split; [lia | exact I].
Qed.

Lemma rm_sub_apart : forall m0 lblk (sp : word) p v Dv, pj_node rsegs m0 lblk p v Dv ->
  (forall x, pj_foot p Dv x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  bv_unsigned sp - 192 < bv_unsigned sp ->
  p + 56 <= bv_unsigned sp - 192 \/ bv_unsigned sp <= p.
Proof.
  intros m0 lblk sp p v Dv HN HO HL.
  apply (rm_apart p 56 (bv_unsigned sp - 192) (bv_unsigned sp)); [lia | exact HL |].
  intros x Hx. pose proof (HO x (or_introl Hx)) as Hq. cbn [outside] in Hq. exact (proj1 Hq).
Qed.

(* ---------- the callees' NULL paths, stepped in the image ---------- *)

Lemma rm_get0 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P lo : Z),
  P < 2 ^ 64 -> stk rsegs m lo P -> lo <= P - 80 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(P - 80, P)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo P)
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16468) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P lo
    HP ST LO MI.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (munch_refl [(P - 80, P)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.
  step. if_true.
  do 12 step.
  release_frame FR ST P.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST.
Qed.

Section RM.
Hypothesis PJ_GET : pj_get_contract.
Hypothesis PJ_GET_STR : pj_get_str_contract.

Lemma rm_gstr0 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P lo : Z),
  P < 2 ^ 64 -> stk rsegs m lo P -> lo <= P - 96 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(P - 96, P)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo P)
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16594) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P lo
    HP ST LO MI.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (munch_refl [(P - 96, P)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.
  let mm := cur_mem in rename mm into m1.
  eapply evt_cut.
  { eapply rm_get0; [lia | exact ST | lia | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E &
              MU2 & WM2 & MI2 & ST2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x165a0)) with (Z_to_bv 64 0x165a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
    as FR2.
  clear FR.
  assert (MU3 : munch [(P - 96, P)] m m2) by (eapply rm_munch_in; [| | exact MU | exact MU2]; lia).
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
  clear MU MU2 WM WM2 ST MI.
  step. if_true.
  do 3 step.
  release_frame FR2 ST2 P.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU3|]. split; [exact WM3|]. split; [exact MI2|]. exact ST2.
Qed.

(* ---------- the two call steps of the body ---------- *)

Lemma rm_get : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo p k : Z) (K : list Z)
    (cs : list cell),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k ->
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk lblk sp -> rm_st m0 m sp lo cs ->
  rm_sub m0 lblk sp p -> rm_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte) (z : Z),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      rm_st m0 m' sp lo cs /\ r = Z_to_bv 64 z /\ rm_sub m0 lblk sp z)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16468) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    lo p k K cs E0 E1 H16 HLo HB (MU & WM & MI & ST & FR) HP HK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  assert (HSU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec p 0) as [P0|P0].
  - subst p a0.
    eapply evt_mono.
    { eapply rm_get0; [lia | exact ST | lia | exact MI]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
                MU' & WM' & MI' & ST').
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', 0.
    split; [exact E|]. split; [|split; [reflexivity | left; reflexivity]].
    split; [eapply rm_munch_in; [| | exact MU | exact MU']; lia|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact ST'|].
    eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | cbn [disjoint_from]; lia].
  - destruct HP as [HP|(v & Dv & HNv & HOv)]; [contradiction|].
    pose proof (rm_node_tr _ m0 m lblk p v Dv HNv MU HOv) as HNm.
    pose proof (rm_sub_apart m0 lblk sp p v Dv HNv HOv ltac:(lia)) as HPA.
    pose proof (rm_key_apart m lo (bv_unsigned sp + -96) 80 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
    eapply evt_mono.
    { apply (PJ_GET ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lblk p k K v Dv lo E0 E1 (or_intror HNm)
               (rm_key_cb m k K MI HK)); rewrite ?HSU.
      - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
      - Z.div_mod_to_equations. lia.
      - exact ST.
      - lia.
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - exact MI. }
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU' & WM' & MI' & ST' & _ & Hr).
    rewrite HSU in MU', ST'.
    destruct Hr as [(Ho & _)|(_ & HN' & z & Er & HR)]; [contradiction|].
    assert (MU2 : munch [(bv_unsigned sp - 192, bv_unsigned sp)] m0 m')
      by (eapply rm_munch_in; [| | exact MU | exact MU']; lia).
    exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', z.
    split; [exact E|]. split; [|split; [exact Er|]].
    + split; [exact MU2|]. split; [exact (wmono_trans rsegs _ _ _ WM WM')|]. split; [exact MI'|].
      split; [exact ST'|].
      eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | cbn [disjoint_from]; lia].
    + destruct (rm_get_sub m' lblk p v Dv K z HN' HR) as [Hz|(v' & Dz & HNz & HFz)]; [left; exact Hz|right].
      exists v', Dz.
      assert (HOz : forall x, pj_foot z Dz x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x)
        by (intros x Hx; exact (HOv x (HFz x Hx))).
      split; [|exact HOz].
      exact (rm_node_tr _ m' m0 lblk z v' Dz HNz (rm_munch_sym _ m0 m' MU2) HOz).
Qed.

Lemma rm_gstr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo p k : Z) (K : list Z)
    (cs : list cell),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k ->
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk lblk sp -> rm_st m0 m sp lo cs ->
  rm_sub m0 lblk sp p -> rm_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      rm_st m0 m' sp lo cs)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16594) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    lo p k K cs E0 E1 H16 HLo HB (MU & WM & MI & ST & FR) HP HK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  assert (HSU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec p 0) as [P0|P0].
  - subst p a0.
    eapply evt_mono.
    { eapply rm_gstr0; [lia | exact ST | lia | exact MI]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
                MU' & WM' & MI' & ST').
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [eapply rm_munch_in; [| | exact MU | exact MU']; lia|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact ST'|].
    eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | cbn [disjoint_from]; lia].
  - destruct HP as [HP|(v & Dv & HNv & HOv)]; [contradiction|].
    pose proof (rm_node_tr _ m0 m lblk p v Dv HNv MU HOv) as HNm.
    pose proof (rm_sub_apart m0 lblk sp p v Dv HNv HOv ltac:(lia)) as HPA.
    pose proof (rm_key_apart m lo (bv_unsigned sp + -96) 96 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
    eapply evt_mono.
    { apply (PJ_GET_STR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lblk p k K v Dv lo E0 E1 (or_intror HNm)
               (rm_key_cb m k K MI HK)); rewrite ?HSU.
      - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
      - Z.div_mod_to_equations. lia.
      - exact ST.
      - lia.
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - exact MI. }
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU' & WM' & MI' & ST' & _ & _).
    rewrite HSU in MU', ST'.
    exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    split; [eapply rm_munch_in; [| | exact MU | exact MU']; lia|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact ST'|].
    eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | cbn [disjoint_from]; lia].
Qed.

(* ---------- the `top` table: one key per pass ---------- *)

(* from `mv a0, s2` (a1 holds the key read from the table at A) to the loop's `bne s5, s4` *)
Lemma rm_top_body : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c
      : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo o k A A' : Z)
    (K : list Z) (j : list byte) (rest : list cell),
  a1 = Z_to_bv 64 k -> s2 = Z_to_bv 64 o -> 0 <= A < 2 ^ 32 -> A' = A + 4 ->
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk lblk sp ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: rest) -> rm_sub m0 lblk sp o -> rm_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' c' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x13f10) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0 s1
                    a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (Z_to_bv 64 A') s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13f24) fc None m' (seg_rom rsegs) /\
      rm_st m0 m' sp lo (CB 8 j :: C8 c' :: rest))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m lblk
    lo o k A A' K j rest E1 E2 HA EA H16 HLo HB INV HP HK.
  subst a1 s2 A'.
  do 2 step.
  eapply evt_cut.
  { eapply rm_gstr with (m0 := m0) (lblk := lblk) (lo := lo) (p := o) (k := k) (K := K);
      [reflexivity | reflexivity | exact H16 | exact HLo | exact HB | exact INV | exact HP | exact HK]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & INV1).
  subst ms'. rewrite ret_pc_even by first [lia | reflexivity].
  clear INV. destruct INV1 as (MU & WM & MI & ST & FR).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  do 5 step.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption.
Qed.

(* ---------- the params loop ---------- *)

(* the loop head (0x13f88) at index i: s1 = params, s2 / s3 = "symbol" / "value", s4 = PJ_ARRAY, s5 = 56 i, s6 = i *)
Definition rm_head (m0 : word -> option byte) (sp : word) (lo z4 i : Z) (gp tp s0 s9 s10 s11 : word)
    (j : list byte) (rest : list cell) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 c : word) (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 i)
                 (Z_to_bv 64 56) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f88) fc None m (seg_rom rsegs) /\
    rm_st m0 m sp lo (CB 8 j :: C8 c :: rest).

(* the state pair (0x14020): s0 = state *)
Definition rm_out (m0 : word -> option byte) (sp : word) (lo : Z) (gp tp s0 s9 s10 s11 : word)
    (j : list byte) (rest : list cell) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 c : word) (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14020) fc None m (seg_rom rsegs) /\
    rm_st m0 m sp lo (CB 8 j :: C8 c :: rest).

(* from 0x14004 (seen += ...) to the head of pass i + 1 *)
Lemma rm_join : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 i kids : Z)
    (items : list jv) (D4 : list (Z * Z)) (j : list byte) (rest : list cell),
  lo <= bv_unsigned sp - 192 -> 0 <= i -> 56 * (i + 1) < 2 ^ 64 ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: rest) ->
  evt rsegs (rm_head m0 sp lo z4 (i + 1) gp tp s0 s9 s10 s11 j rest F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 i)
             (Z_to_bv 64 56) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14004) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 i kids
    items D4 j rest HLo HI0 HI1 HN HO HK (MU & WM & MI & ST & FR).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rm_rng m0 L z4 _ D4 HN) as RG.
  step. step. step.
  let mm := cur_mem in destruct (rm_hdr _ m0 mm L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
  step. try rewrite sx32_small by lia. step. step. step. if_true.
  replace (56 * i + 56) with (56 * (i + 1)) by lia.
  apply evt_done. unfold rm_head. do 19 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption.
Qed.

(* one pass, i < n: pj_get_str (&params->kids[i], "symbol"), then pj_get (&params->kids[i], "value"); every UBSan
   check of &kids[i] passes because kids is a placed block of 56 * cap bytes and i < cap *)
Lemma rm_body : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 i kids : Z)
    (items : list jv) (D4 : list (Z * Z)) (j : list byte) (rest : list cell),
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk L sp ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids -> 0 <= i < Z.of_nat (length items) ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: rest) ->
  evt rsegs (rm_head m0 sp lo z4 (i + 1) gp tp s0 s9 s10 s11 j rest F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 i)
             (Z_to_bv 64 56) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 i kids
    items D4 j rest H16 HLo HL HN HO HK HI INV.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof INV as (MU & WM & MI & ST & FR).
  pose proof ST as (ST0 & ST1 & _).
  destruct (rm_arr_hdr m0 L z4 items D4 HN) as (_ & (C0 & _) & _).
  destruct (nth_error items (Z.to_nat i)) as [u|] eqn:Eu; [| apply nth_error_None in Eu; lia].
  destruct (rm_kid m0 L z4 items D4 kids (Z.to_nat i) u HN HK Eu _ HO) as (D1 & cap & IC & LK & HP & HF).
  rewrite Z2Nat.id in HP, HF, IC by lia.
  destruct (HL _ _ LK) as (K0 & _ & K47 & _).
  pose proof (proj1 HK) as RK.
  destruct (rm_hdr _ m0 m L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
  zstep. zstep. rm_trapfree.
  do 8 zstep. rm_trapfree.
  zstep. rm_trapfree.
  do 5 zstep.
  rewrite (rm_mulh i) by lia.
  if_false.
  do 3 zstep.
  eapply evt_cut.
  { eapply rm_gstr with (m0 := m0) (lblk := L) (lo := lo) (p := kids + 56 * i) (k := 0x10383)
      (K := [115; 121; 109; 98; 111; 108]);
      [word_eq_tac | reflexivity | exact H16 | exact HLo | exact HL | exact INV
      | right; exists u, D1; split; [exact HP | exact HF] | rm_keyok]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & INV').
  subst ms'. clear R0 R40 R24 MU WM MI ST FR.
  replace (ret_pc (Z_to_bv 64 0x13fd4)) with (Z_to_bv 64 0x13fd4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. if_cases HR.
  - eapply rm_join; [exact HLo | lia | lia | exact HN | exact HO | exact HK | exact INV'].
  - pose proof INV' as (MU' & _).
    destruct (rm_hdr _ m0 m' L z4 items D4 kids HN HO MU' HK) as (R0 & R40 & R24).
    do 3 zstep. rm_trapfree.
    do 4 zstep. rm_trapfree.
    do 3 zstep.
    eapply evt_cut.
    { eapply rm_get with (m0 := m0) (lblk := L) (lo := lo) (p := kids + 56 * i) (k := 0x1038a)
        (K := [118; 97; 108; 117; 101]);
        [word_eq_tac | reflexivity | exact H16 | exact HLo | exact HL | exact INV'
        | right; exists u, D1; split; [exact HP | exact HF] | rm_keyok]. }
    intros ms' (t0'' & t1'' & t2'' & r' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                m'' & z & E' & INV'' & _ & _).
    subst ms'. clear R0 R40 R24.
    replace (ret_pc (Z_to_bv 64 0x14000)) with (Z_to_bv 64 0x14000) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zstep.
    eapply rm_join; [exact HLo | lia | lia | exact HN | exact HO | exact HK | exact INV''].
Qed.

Lemma rm_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (lo z4 i kids : Z)
    (items : list jv) (D4 : list (Z * Z)) (j : list byte) (rest : list cell),
  Z.to_nat (Z.of_nat (length items) - i) = n ->
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk L sp ->
  pj_node rsegs m0 L z4 (JArr items) D4 ->
  (forall x, pj_foot z4 D4 x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  pj_u64 rsegs m0 (z4 + 24) kids -> 0 <= i <= Z.of_nat (length items) ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: rest) ->
  evt rsegs (rm_out m0 sp lo gp tp s0 s9 s10 s11 j rest F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x10383) (Z_to_bv 64 0x1038a) (Z_to_bv 64 5) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 i)
             (Z_to_bv 64 56) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f88) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m L lo z4 i kids
      items D4 j rest En H16 HLo HL HN HO HK HI INV.
  - pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof INV as (MU & WM & MI & ST & FR).
    pose proof ST as (ST0 & ST1 & _).
    destruct (rm_arr_hdr m0 L z4 items D4 HN) as (_ & (C0 & _) & _).
    destruct (rm_hdr _ m0 m L z4 items D4 kids HN HO MU HK) as (R0 & R40 & R24).
    zstep. zstep. rm_br_true.
    apply evt_done. unfold rm_out. do 26 eexists. split; [reflexivity | exact INV].
  - eapply evt_cut.
    { eapply rm_body; [exact H16 | exact HLo | exact HL | exact HN | exact HO | exact HK | lia | exact INV]. }
    intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & t3' & t4' & t5' & t6' &
                c' & m' & E & INV').
    subst ms'.
    eapply IH; [| exact H16 | exact HLo | exact HL | exact HN | exact HO | exact HK | lia | exact INV'].
    lia.
Qed.

(* from `beqz s1` (0x13f54) to the state pair: params NULL, not aligned (trap, never), not an array, or the loop *)
Lemma rm_params : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      c : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo z4 : Z)
    (j : list byte) (rest : list cell),
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk lblk sp ->
  rm_sub m0 lblk sp z4 -> rm_st m0 m sp lo (CB 8 j :: C8 c :: rest) ->
  evt rsegs (rm_out m0 sp lo gp tp s0 s9 s10 s11 j rest F fc)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 z4) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c F fc m0 m lblk
    lo z4 j rest H16 HLo HL Hz INV.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof INV as (MU & WM & MI & ST & FR).
  pose proof ST as (ST0 & ST1 & _).
  destruct (Z.eq_dec z4 0) as [Z4|Z4].
  { assert (B : bv_eqb (Z_to_bv 64 z4) (Z_to_bv 64 0) = true) by (subst z4; reflexivity).
    step. rewrite B. cbv iota.
    apply evt_done. unfold rm_out. do 26 eexists. split; [reflexivity | exact INV]. }
  destruct Hz as [Z4'|(v4 & D4 & HP4 & HF4)]; [lia|].
  pose proof (rm_rng m0 lblk z4 v4 D4 HP4) as RG4.
  pose proof (rm_al m0 lblk z4 v4 D4 HP4) as AL4.
  pose proof (rm_node_tr _ m0 m lblk z4 v4 D4 HP4 MU HF4) as HPm.
  assert (B4 : bv_eqb (Z_to_bv 64 z4) (Z_to_bv 64 0) = false) by (rewrite bv_eqb_lit by lia; apply Z.eqb_neq; exact Z4).
  step. rewrite B4. cbv iota.
  step. step. rm_trapfree.
  pose proof (rd4 rsegs m z4 (tag v4) (rm_ty m lblk z4 v4 D4 HPm)) as RT.
  pose proof (tag_range v4) as TG.
  step. try rewrite sx32_small by lia. step. step.
  destruct (Z.eq_dec (tag v4) 5) as [T5|T5].
  - assert (B5 : negb (bv_eqb (Z_to_bv 64 (tag v4)) (Z_to_bv 64 5)) = false)
      by (rewrite bv_eqb_lit by lia; rewrite T5; reflexivity).
    rewrite B5. cbv iota.
    destruct (rm_tag5 m0 lblk z4 v4 D4 HP4 T5) as (items & ->).
    destruct (rm_arr_hdr m0 lblk z4 items D4 HP4) as (_ & _ & kids & cap & HK24 & _).
    clear RT. do 7 step.
    eapply (rm_loop (Z.to_nat (Z.of_nat (length items) - 0))) with (i := 0) (kids := kids) (items := items) (D4 := D4)
      (L := lblk) (m0 := m0);
      [reflexivity | exact H16 | exact HLo | exact HL | exact HP4 | exact HF4 | exact HK24 | lia | exact INV].
  - assert (B5 : negb (bv_eqb (Z_to_bv 64 (tag v4)) (Z_to_bv 64 5)) = true)
      by (rewrite bv_eqb_lit by lia; apply negb_true_iff, Z.eqb_neq; exact T5).
    rewrite B5. cbv iota.
    apply evt_done. unfold rm_out. do 26 eexists. split; [reflexivity | exact INV].
Qed.

(* ---------- the state pair and the return ---------- *)

(* the contract's postcondition, with the entry memory m0 *)
Definition rm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : jv) (D : list (Z * Z)) (lo : Z)
    (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - (96 + 96), bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ pj_node rsegs m' lblk o t D.

(* from 0x14048 (seen += ...): the volatile read of seen, the restores, the return *)
Lemma rm_fin : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      c xra x0 x1 x2 x3 x4 x5 x6 x7 x8 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo o : Z) (t : jv)
    (D : list (Z * Z)) (j : list byte),
  lo <= bv_unsigned sp - 192 ->
  pj_node rsegs m0 lblk o t D -> (forall x, pj_foot o D x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: [C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra]) ->
  evt rsegs (rm_post xra sp gp tp x0 x1 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 F fc m0 lblk o t D lo)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14048) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c xra x0 x1 x2 x3 x4 x5 x6 x7 x8 F fc m0 m lblk lo o t D j HLo HN HO (MU & WM & MI & ST & FR).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  do 16 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rm_post. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  eapply rm_node_tr; [exact HN | eassumption | exact HO].
Qed.

(* from 0x14020: pj_get_str (state, "encoding") != NULL && pj_get_str (state, "bytes") != NULL *)
Lemma rm_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      c xra x0 x1 x2 x3 x4 x5 x6 x7 x8 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (lo o z3 : Z) (t : jv)
    (D : list (Z * Z)) (j : list byte),
  s0 = Z_to_bv 64 z3 ->
  bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 192 -> rm_blk lblk sp ->
  pj_node rsegs m0 lblk o t D -> (forall x, pj_foot o D x -> outside [(bv_unsigned sp - 192, bv_unsigned sp)] x) ->
  rm_sub m0 lblk sp z3 ->
  rm_st m0 m sp lo (CB 8 j :: C8 c :: [C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra]) ->
  evt rsegs (rm_post xra sp gp tp x0 x1 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 F fc m0 lblk o t D lo)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14020) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c xra x0 x1 x2 x3 x4 x5 x6 x7 x8 F fc m0 m lblk lo o z3 t D j E0 H16 HLo HB HN HO Hz INV.
  subst s0.
  do 4 step.
  eapply evt_cut.
  { eapply rm_gstr with (m0 := m0) (lblk := lblk) (lo := lo) (p := z3) (k := 0x102ac)
      (K := [101; 110; 99; 111; 100; 105; 110; 103]);
      [reflexivity | rm_lit | exact H16 | exact HLo | exact HB | exact INV | exact Hz | rm_keyok]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & INV').
  subst ms'. clear INV.
  replace (ret_pc (Z_to_bv 64 0x14030)) with (Z_to_bv 64 0x14030) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_cases HR.
  - eapply rm_fin; [exact HLo | exact HN | exact HO | exact INV'].
  - do 4 step.
    eapply evt_cut.
    { eapply rm_gstr with (m0 := m0) (lblk := lblk) (lo := lo) (p := z3) (k := 0x10420) (K := [98; 121; 116; 101; 115]);
        [reflexivity | rm_lit | exact H16 | exact HLo | exact HB | exact INV' | exact Hz | rm_keyok]. }
    intros ms' (t0'' & t1'' & t2'' & r' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                m'' & E' & INV'').
    subst ms'. clear INV'.
    replace (ret_pc (Z_to_bv 64 0x14044)) with (Z_to_bv 64 0x14044) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    eapply rm_fin; [exact HLo | exact HN | exact HO | exact INV''].
Qed.

(* ---------- read_members ---------- *)

Theorem read_members_holds : read_members_contract.
Proof.
  unfold read_members_contract, READ_MEMBERS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lblk o t D lo E0 HN LB SP16 ST LO SD MI.
  unfold RM_K, RM_F in *.
  assert (HB : rm_blk lblk sp) by exact LB. clear LB.
  assert (HLo : lo <= bv_unsigned sp - 192) by lia. clear LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rm_root m lblk sp o t D HB SD HN) as HO.
  assert (HSUB : rm_sub m lblk sp o) by (right; exists t, D; split; [exact HN | exact HO]).
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  (* prologue: saves ra, s0-s8; s2 = doc *)
  do 12 step.
  (* params = pj_get (doc, "params") *)
  do 4 step.
  eapply evt_cut.
  { eapply rm_get with (m0 := m) (lblk := lblk) (lo := lo) (p := o) (k := 0x1033b) (K := [112; 97; 114; 97; 109; 115]);
      [exact E0 | rm_lit | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & r & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & z4 & E & INV & Er & H4).
  subst ms' r. rewrite ret_pc_even by first [lia | reflexivity].
  clear MU WM MI ST FR.
  (* state = pj_get (doc, "state") *)
  do 5 step.
  eapply evt_cut.
  { eapply rm_get with (m0 := m) (lblk := lblk) (lo := lo) (p := o) (k := 0x102fc) (K := [115; 116; 97; 116; 101]);
      [exact E0 | rm_lit | exact SP16 | exact HLo | exact HB | exact INV | exact HSUB | rm_keyok]. }
  clear INV.
  intros ms' (? & ? & ? & r & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & z3 & E & INV & Er & H3).
  subst ms' r. rewrite ret_pc_even by first [lia | reflexivity].
  destruct INV as (MU & WM & MI & ST & FR).
  (* seen = 0; the table pointers *)
  do 6 step.
  (* the six keys of `top` *)
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x10396) (A := 0x10490) (A' := 0x10494)
      (K := [102; 111; 114; 109; 97; 116]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x10359) (A := 0x10494) (A' := 0x10498)
      (K := [105; 100]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x103a2) (A := 0x10498) (A' := 0x1049c)
      (K := [110; 97; 109; 101]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x102b5) (A := 0x1049c) (A' := 0x104a0)
      (K := [99; 97; 114; 114; 105; 101; 115]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x102f2) (A := 0x104a0) (A' := 0x104a4)
      (K := [99; 114; 101; 97; 116; 101; 100; 65; 116]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  do 2 step.
  eapply evt_cut.
  { eapply rm_top_body with (m0 := m) (lblk := lblk) (lo := lo) (o := o) (k := 0x1034e) (A := 0x104a4) (A' := 0x104a8)
      (K := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116]);
      [rm_lit | exact E0 | lia | reflexivity | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & E & INV).
  subst ms'. clear MU WM MI ST FR. destruct INV as (MU & WM & MI & ST & FR).
  step. try first [if_true | if_false].
  (* pj_get_str (pj_get (doc, "plugin"), "id") *)
  do 4 step.
  eapply evt_cut.
  { eapply rm_get with (m0 := m) (lblk := lblk) (lo := lo) (p := o) (k := 0x10342) (K := [112; 108; 117; 103; 105; 110]);
      [exact E0 | rm_lit | exact SP16 | exact HLo | exact HB | | exact HSUB | rm_keyok].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  intros ms' (? & ? & ? & r & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & z & E & INV & Er & Hz).
  subst ms' r. rewrite ret_pc_even by first [lia | reflexivity].
  clear MU WM MI ST FR.
  do 3 step.
  eapply evt_cut.
  { eapply rm_gstr with (m0 := m) (lblk := lblk) (lo := lo) (p := z) (k := 0x10359) (K := [105; 100]);
      [reflexivity | rm_lit | exact SP16 | exact HLo | exact HB | exact INV | exact Hz | rm_keyok]. }
  clear INV.
  intros ms' (? & ? & ? & r & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & E & INV).
  subst ms'. rewrite ret_pc_even by first [lia | reflexivity].
  destruct INV as (MU & WM & MI & ST & FR).
  do 4 step.
  (* the params loop *)
  eapply evt_cut.
  { eapply rm_params with (m0 := m) (lblk := lblk) (lo := lo) (z4 := z4);
      [exact SP16 | exact HLo | exact HB | exact H4 |].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; eassumption. }
  clear MU WM MI ST FR.
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m12 & E &
              INV).
  subst ms'.
  (* the state pair, the restores, the return *)
  eapply evt_mono.
  { eapply rm_tail with (z3 := z3) (o := o) (t := t) (D := D);
      [reflexivity | exact SP16 | exact HLo | exact HB | exact HN | exact HO | exact H3 | exact INV]. }
  intros ms' H. exact H.
Qed.

End RM.
