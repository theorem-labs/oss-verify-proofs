(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib GWin PkStack.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GWinA.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL PkStack.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkAux.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma even_len_even : forall (A : Type) (l : list A), even_len l = true -> Z.of_nat (length l) mod 2 = 0.
Proof.
  intros A l. remember (length l) as n eqn:EN. revert l EN.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros l EN H.
  destruct l as [|x [|y l']]; cbn in H; [subst; reflexivity| discriminate|].
  cbn [length] in EN. subst n. specialize (IH (length l') ltac:(lia) l' eq_refl H).
  rewrite !Nat2Z.inj_succ. replace (Z.succ (Z.succ (Z.of_nat (length l')))) with (Z.of_nat (length l') + 1 * 2) by lia.
  rewrite Z_mod_plus_full. exact IH.
Qed.

Lemma u64_of_Z : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. exact Hz. Qed.
Lemma env_upd_other : forall E n w k, k <> n -> ev (env_upd E n w) k = ev E k.
Proof. intros E n w k NE. cbn [env_upd ev]. destruct (PrimInt63.eqb k n) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. contradiction. Qed.

Lemma deq_sound : forall E fs a b, facts_hold E fs -> dec_true (decide_eq fs a b) = true -> den E a = den E b.
Proof.
  intros E fs a b Hfs H. unfold dec_true in H. destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (eqb_iff _ _ true) (decide_eq_sound E fs Hfs _ _ _ D)).
Qed.
Lemma dnz_sound : forall E fs a, facts_hold E fs -> dec_false (decide_eq0 fs a) = true -> bv_unsigned (den E a) <> 0.
Proof.
  intros E fs a Hfs H X. unfold dec_false in H. destruct (decide_eq0 fs a) as [[|]|] eqn:D; try discriminate.
  apply (proj1 (eqb_iff _ _ false) (decide_eq0_sound E fs Hfs _ _ D)). apply bv_eq. rewrite X. reflexivity.
Qed.
Lemma dltu_sound : forall E fs a b, facts_hold E fs -> dec_true (decide_ltu fs a b) = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold dec_true in H. destruct (decide_ltu fs a b) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (ltu_iff _ _ true) (decide_ltu_sound E fs Hfs _ _ _ D)).
Qed.
Lemma lit01_sound : forall E v b, lit01 v = Some b -> bv_unsigned (den E v) = b2Z b.
Proof.
  intros E v b H. unfold lit01 in H. destruct v; try discriminate.
  destruct (weqb w wzero) eqn:W0; [apply (proj1 (weqb_ok _ _)) in W0; subst; injection H as <-; cbn [den b2Z]; rewrite wbv_unsigned, wzero_ok; reflexivity|].
  destruct (weqb w (wlit 1)) eqn:W1; [|discriminate]. apply (proj1 (weqb_ok _ _)) in W1; subst; injection H as <-.
  cbn [den b2Z]. rewrite wbv_unsigned, wlit_ok. reflexivity.
Qed.
Lemma den_b2v : forall E b, bv_unsigned (den E (b2v b)) = b2Z b.
Proof. intros E [|]; cbn [den b2v b2Z]; rewrite wbv_unsigned, ?wlit_ok, ?wzero_ok; reflexivity. Qed.
Lemma den_add_lit : forall E x i, bv_unsigned (den E (sv_alu ALU_ADD x (VL (wlit i)))) = (bv_unsigned (den E x) + to_Z i) mod two64.
Proof. intros E x i. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.
Lemma den_sub_lit : forall E x i, bv_unsigned (den E (sv_alu ALU_SUB x (VL (wlit i)))) = (bv_unsigned (den E x) - to_Z i) mod two64.
Proof. intros E x i. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_sub_unsigned, wbv_unsigned, wlit_ok. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.

Lemma etop_win_den : forall E k len, wden E (etop_win k len) = Win (bv_unsigned (ev E k)) (to_Z len) 6.
Proof.
  intros E k len. unfold etop_win, wden. rewrite (den_VP0 E k wzero (weqb_refl _)). cbn [den]. unfold ETOP. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.

Lemma only_kind_sound : forall E kd w0 ws, only_kind kd w0 ws = true ->
  forall x, In x ws -> w_kind (wden E x) = kd -> w0 = Some x.
Proof.
  intros E kd w0 ws H x Hx K. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [k'|] eqn:KO; [|discriminate]. rewrite (kind_of_sound E x k' KO) in K. subst k'. rewrite Z.eqb_refl in Q.
  destruct w0 as [w0|]; [|discriminate]. apply win3_eqb_eq in Q. congruence.
Qed.

Lemma block_keep_evidence : forall LB (W' : list window) vb vbytes lo_old wnew,
  In (vb, vbytes) LB -> vb <= lo_old < vb + vbytes ->
  In wnew W' -> heap_kind wnew -> 0 < w_len wnew -> vb <= w_lo wnew < vb + vbytes ->
  exists o, In o LB /\ in_iv o lo_old /\ (~ c24 (snd o) \/ exists w', In w' W' /\ heap_kind w' /\ 0 < w_len w' /\ in_iv o (w_lo w')).
Proof.
  intros LB W' vb vbytes lo_old wnew HLB OLD HW HK LEN NEW. exists (vb, vbytes). split; [exact HLB|]. split; [unfold in_iv; cbn [fst snd]; lia|].
  right. exists wnew. split; [exact HW|]. split; [exact HK|]. split; [exact LEN|]. unfold in_iv. cbn [fst snd]. lia.
Qed.
Lemma etop_untied : forall E k len, ~ aw_tied (wden E (etop_win k len)).
Proof. intros E k len. rewrite etop_win_den. unfold aw_tied, K_STACK, K_GHOST. cbn [w_kind]. lia. Qed.
Lemma etop_heap_kind : forall E k len, heap_kind (wden E (etop_win k len)).
Proof. intros E k len. rewrite etop_win_den. unfold heap_kind, K_BLOCK, K_GHOST. cbn [w_kind]. lia. Qed.

Lemma pk_owned_byte_props : forall segs IMGX (AW : alloc_world segs IMGX) A LB m mo g ws ob a,
  aw_holds segs IMGX AW A LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) -> own_pk g LB -> wins_pk g ws ->
  In ob (owned g) -> in_iv ob a -> PK.safe g ws a ->
  (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws ws a /\ m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None.
Proof.
  intros segs IMGX AW A LB m mo g ws ob a HA WF O W Hob Ha SF.
  pose proof (proj1 O ob Hob) as HLB.
  destruct (aw_blocks_ok segs IMGX AW A LB _ m mo ob HA HLB) as (B1 & B2 & B3 & B4 & B5).
  destruct (aw_user_ok segs IMGX AW A LB _ m mo ob a HA HLB Ha) as [MAT NS].
  unfold in_iv in Ha.
  split; [lia|]. split; [exact (B5 a Ha)|]. split; [| split; [exact MAT| exact NS]].
  intros X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  destruct (Z.eq_dec (w_kind w) K_STACK) as [K|NK].
  - pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & [[_ S]|[[K' _]|[K' _]]]).
    + unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
    + rewrite K in K'. discriminate.
    + rewrite K in K'. unfold K_SUB, K_STACK in K'. lia.
  - destruct (proj1 (Forall_forall _ _) W w Hw NK) as [[_ D]|[NB SO]].
    + exact (D ob Hob a Hin Ha).
    + exact (SF w Hw SO Hin).
Qed.

Lemma owned_evec : forall g, v_begin (k_evec g) <> 0 -> In (v_begin (k_evec g), v_bytes (k_evec g)) (owned g).
Proof. intros g NE. unfold owned, evec_blocks. rewrite (proj2 (Z.eqb_neq _ _) NE). apply in_app_iff. left. left. reflexivity. Qed.

Definition vec_dec (v : vecg) : vecg := mkVec (v_begin v) (v_size v - 1) (v_cap v) (v_elt v).
Definition vec_inc (v : vecg) : vecg := mkVec (v_begin v) (v_size v + 1) (v_cap v) (v_elt v).
Lemma vec_dec_valid : forall v, vec_valid v -> 1 <= v_size v -> vec_valid (vec_dec v) /\ v_end (vec_dec v) = v_end v - v_elt v.
Proof. intros v V H. unfold vec_valid, vec_dec, v_end in *; cbn. split; [lia|lia]. Qed.
Lemma vec_inc_valid : forall v, vec_valid v -> v_size v + 1 <= v_cap v -> vec_valid (vec_inc v) /\ v_end (vec_inc v) = v_end v + v_elt v.
Proof. intros v V H. unfold vec_valid, vec_inc, v_end in *; cbn. split; [lia|lia]. Qed.

Lemma pelems_at_app : forall m a es1 es2,
  pelems_at m a (es1 ++ es2) <-> (pelems_at m a es1 /\ pelems_at m (a + ELEM_SIZE * Z.of_nat (length es1)) es2).
Proof.
  intros m a es1. revert a. induction es1 as [|e es1 IH]; intros a es2.
  - cbn [app pelems_at length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. tauto.
  - cbn [app pelems_at length]. rewrite (IH (a + ELEM_SIZE) es2). rewrite Nat2Z.inj_succ.
    replace (a + ELEM_SIZE * Z.succ (Z.of_nat (length es1))) with (a + ELEM_SIZE + ELEM_SIZE * Z.of_nat (length es1)) by lia. tauto.
Qed.

Lemma top_region_find : forall p n m k g gr, IMap.find g (rg_cells (top_region p n m k)) = Some gr ->
  (g = 0%uint63 /\ gr = Gran true [Cell 0%uint63 8%uint63 p]) \/ (g = 1%uint63 /\ gr = Gran true [Cell 0%uint63 8%uint63 n]) \/
  (g = 2%uint63 /\ gr = Gran true [Cell 0%uint63 1%uint63 (b2v m); Cell 1%uint63 1%uint63 (b2v k)]).
Proof.
  intros p n m k g gr F. cbn [top_region rg_cells] in F.
  assert (B0 : IMap.bst (IMap.add 0%uint63 (Gran true [Cell 0%uint63 8%uint63 p]) IMap.empty)) by (apply IMap.bst_add; exact I).
  assert (B1 : IMap.bst (IMap.add 1%uint63 (Gran true [Cell 0%uint63 8%uint63 n]) (IMap.add 0%uint63 (Gran true [Cell 0%uint63 8%uint63 p]) IMap.empty))) by (apply IMap.bst_add; exact B0).
  destruct (Uint63.eqb 2 g) eqn:G2.
  { apply Uint63.eqb_correct in G2. subst g. rewrite IMap.find_add_same in F by exact B1. injection F as <-. right; right; auto. }
  apply Uint63.eqb_false_correct in G2. rewrite IMap.find_add_other in F by (exact B1 || exact G2).
  destruct (Uint63.eqb 1 g) eqn:G1.
  { apply Uint63.eqb_correct in G1. subst g. rewrite IMap.find_add_same in F by exact B0. injection F as <-. right; left; auto. }
  apply Uint63.eqb_false_correct in G1. rewrite IMap.find_add_other in F by (exact B0 || exact G1).
  destruct (Uint63.eqb 0 g) eqn:G0.
  { apply Uint63.eqb_correct in G0. subst g. rewrite IMap.find_add_same in F by exact I. injection F as <-. left; auto. }
  apply Uint63.eqb_false_correct in G0. rewrite IMap.find_add_other in F by (exact I || exact G0). rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma elem_of_bounds : forall (bm : bmem) z lo sp,
  is_cont lo = true -> 0 <= sp -> sp < Z.of_nat (length (okids lo)) -> tree_wf bm z lo ->
  exists ch, In ch (z_chunks z) /\ in_chunk ch (pe_ptr (elem_of (lo, sp))) OBJ_SIZE /\
    1 <= pe_rest (elem_of (lo, sp)) <= 1000 /\ pe_ptr (elem_of (lo, sp)) mod 8 = 0.
Proof.
  intros bm z lo sp IC S0 SLT TWL.
  destruct lo as [| | | | | | | | |p kids|p kids]; try discriminate IC; cbn [okids] in SLT.
  - apply tree_wf_arr in TWL. destruct TWL as (LIM & KP & X & _).
    assert (NE : kids <> []) by (intros ->; cbn in SLT; lia). destruct (X NE) as [AL (ch & Hch & ICH)].
    exists ch. split; [exact Hch|]. unfold elem_of. cbn [pe_rest pe_ptr obj_ptr okids length].
    unfold in_chunk, OBJ_SIZE, LIMIT in *. split; [nia|]. split; [lia|].
    apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (p / 8 + 3 * sp). pose proof (Z.div_mod p 8 ltac:(lia)). lia.
  - apply tree_wf_map in TWL. destruct TWL as (EVN & LIM & KP & X & _).
    assert (NE : kids <> []) by (intros ->; cbn in SLT; lia). destruct (X NE) as [AL (ch & Hch & ICH)].
    pose proof (even_len_even _ kids EVN) as EVn.
    pose proof (Z.div_mod sp 2 ltac:(lia)) as DVs. pose proof (Z.mod_pos_bound sp 2 ltac:(lia)) as MBs.
    pose proof (Z.div_mod (Z.of_nat (length kids)) 2 ltac:(lia)) as DVn.
    exists ch. split; [exact Hch|]. unfold elem_of. cbn [pe_rest pe_ptr obj_ptr okids].
    unfold in_chunk, OBJ_SIZE, LIMIT in *. split; [nia|]. split; [lia|].
    apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (p / 8 + 6 * (sp / 2)). pose proof (Z.div_mod p 8 ltac:(lia)). lia.
Qed.

Lemma u64_at_bytes01 : forall (bm : bmem) a V, (forall x y, bm x = Some y -> 0 <= y < 256) -> u64_at bm a V ->
  u8_at bm a (V mod 256) /\ u8_at bm (a + 1) ((V / 256) mod 256).
Proof.
  intros bm a V BR H. unfold u64_at in H. pose proof (rdZ_bytes bm 8 a V BR H) as B.
  pose proof (B 0 ltac:(cbn; lia)) as B0. pose proof (B 1 ltac:(cbn; lia)) as B1. rewrite Z.add_0_r in B0.
  unfold u8_at. cbn [rdZ]. rewrite B0, B1. replace (a + 1 + 1) with (a + 2) by lia.
  unfold zbyte. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. change (2 ^ (8 * 1)) with 256. split; f_equal; lia.
Qed.

Lemma low16_bytes : forall V F, 0 <= F -> V mod 65536 = F -> V mod 256 = F mod 256 /\ (V / 256) mod 256 = (F / 256) mod 256.
Proof.
  intros V F HF H. pose proof (Z.div_mod V 65536 ltac:(lia)) as DM. rewrite H in DM. set (q := V / 65536) in DM. clearbody q.
  rewrite DM. replace (65536 * q + F) with (F + (256 * q) * 256) by lia. split.
  - rewrite Z_mod_plus_full. reflexivity.
  - rewrite Z.div_add by lia. replace (F / 256 + 256 * q) with (F / 256 + q * 256) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma obj_type_cont : forall fo, (obj_type fo = 7 \/ obj_type fo = 8) -> is_cont fo = true /\ (is_mapo fo = true <-> obj_type fo = 8).
Proof.
  intros fo H. destruct fo; cbn [obj_type is_cont is_mapo] in *; unfT; (split; [first [reflexivity| exfalso; lia]| split; intros; first [reflexivity| lia| discriminate]]).
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma st_ok_rf_map : forall E st ms mo (f : sv -> sv),
  st_ok segs OPS E st ms mo -> (forall v, den E (f v) = den E v) -> f (VL wzero) = VL wzero ->
  st_ok segs OPS E (SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st)) ms mo.
Proof.
  intros E st ms mo f HS HF H0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - rewrite rf_get_map, Px0. exact H0.
  - intros r. rewrite rf_get_map, HF. exact (Pregs r).
Qed.

Lemma flags_sound : forall E priv m k r off f ismap fs,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> 0 <= off -> off + 1 < two62Z ->
  facts_hold E fs -> flags_at r off = Some f -> flags_ok fs f ismap = true ->
  u8_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (b2Z ismap) /\ u8_at (bmem_of segs m) (bv_unsigned (ev E k) + off + 1) (b2Z ismap).
Proof.
  intros E priv m k r off f ismap fs RO K0 H0 H62 HF FA FO. unfold flags_at in FA.
  destruct (cell_at r off 8%uint63) as [w|] eqn:C8.
  - injection FA as <-. cbn [flags_ok] in FO.
    pose proof (proj1 (cell_at_u64 segs priv E m k r off w RO K0 H0 ltac:(lia) C8)) as Uf.
    pose proof (deq_sound E _ _ _ HF FO) as FQ.
    rewrite (den_sv_ext E false 0%uint63 2%uint63 w ltac:(unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 2%uint63) with 2; lia)) in FQ.
    apply (f_equal bv_unsigned) in FQ. unfold ext_word, ext_Z in FQ. cbn [den] in FQ. rewrite wbv_unsigned, wlit_ok, Z_to_bv_unsigned in FQ.
    change (to_Z 0%uint63) with 0 in FQ. change (to_Z 2%uint63) with 2 in FQ. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in FQ. change (2 ^ (8 * 2)) with 65536 in FQ.
    pose proof (Z.mod_pos_bound (bv_unsigned (den E w)) 65536 ltac:(lia)) as MB.
    unfold bv_wrap in FQ. rewrite bv_modulus_64, (Z.mod_small _ two64) in FQ by (unfold two64; lia).
    set (flags2 := if ismap then 257%uint63 else 0%uint63) in *.
    assert (FL2 : to_Z flags2 mod 256 = b2Z ismap /\ (to_Z flags2 / 256) mod 256 = b2Z ismap) by (subst flags2; clear; destruct ismap; split; reflexivity).
    destruct (low16_bytes (bv_unsigned (den E w)) (to_Z flags2) ltac:(pose proof (to_Z_bounded flags2); lia) FQ) as [FB0 FB1]. rewrite (proj1 FL2) in FB0. rewrite (proj2 FL2) in FB1.
    destruct (u64_at_bytes01 _ _ _ (bmem_of_bytes_range segs m) Uf) as [Ufl0 Ufl1]. rewrite FB0 in Ufl0. rewrite FB1 in Ufl1. split; assumption.
  - destruct (cell_at r off 1%uint63) as [b0|] eqn:C0; [|discriminate]. destruct (cell_at r (off + 1) 1%uint63) as [b1|] eqn:C1; [|discriminate].
    injection FA as <-. cbn [flags_ok] in FO. apply andb_prop in FO as [F0 F1].
    pose proof (proj1 (cell_at_u8 segs priv E m k r off b0 RO K0 H0 ltac:(lia) C0)) as U0.
    pose proof (proj1 (cell_at_u8 segs priv E m k r (off + 1) b1 RO K0 ltac:(lia) ltac:(lia) C1)) as U1.
    assert (BY : forall b, dec_true (decide_eq fs (sv_ext false 0%uint63 1%uint63 b) (b2v ismap)) = true -> bv_unsigned (den E b) mod 2 ^ 8 = b2Z ismap).
    { intros b DB. pose proof (deq_sound E _ _ _ HF DB) as FQ.
      rewrite (den_sv_ext E false 0%uint63 1%uint63 b ltac:(unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia)) in FQ.
      apply (f_equal bv_unsigned) in FQ. unfold ext_word, ext_Z in FQ. unfold b2v in FQ. cbn [den] in FQ. rewrite wbv_unsigned, Z_to_bv_unsigned in FQ.
      change (to_Z 0%uint63) with 0 in FQ. change (to_Z 1%uint63) with 1 in FQ. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r in FQ. change (2 ^ (8 * 1)) with 256 in FQ.
      pose proof (Z.mod_pos_bound (bv_unsigned (den E b)) 256 ltac:(lia)) as MB.
      unfold bv_wrap in FQ. rewrite bv_modulus_64, (Z.mod_small _ two64) in FQ by (unfold two64; lia).
      change (2 ^ 8) with 256. rewrite FQ. destruct ismap; [rewrite wlit_ok| rewrite wzero_ok]; reflexivity. }
    rewrite (BY b0 F0) in U0. rewrite (BY b1 F1) in U1. rewrite Z.add_assoc in U1. split; assumption.
Qed.

Lemma repoint_g_sound : forall all E st ms mo old new,
  st_ok segs OPS E st ms mo -> den E new = den E old -> sv_eqb (VL wzero) old = false ->
  st_ok segs OPS E (repoint_g all old new st) ms mo.
Proof.
  intros all E st ms mo old new HS HD H0. unfold repoint_g.
  set (f := fun v : sv => if sv_eqb v old then new else v).
  assert (HF : forall v, den E (f v) = den E v).
  { intros v. subst f. cbn beta. destruct (sv_eqb v old) eqn:Q; [apply sv_eqb_eq in Q; subst; exact HD| reflexivity]. }
  assert (F0 : f (VL wzero) = VL wzero) by (subst f; cbn beta; rewrite H0; reflexivity).
  destruct all.
  {
    pose proof (GWA.st_ok_subst_cells_all segs OPS E st ms mo f HS HF) as HSA.
    exact (st_ok_rf_map E (setregs st (GWA.subst_all f (s_regs st))) ms mo f HSA HF F0). }
  destruct (IMap.find 1%uint63 (s_regs st)) as [r1|] eqn:F1.
  - pose proof (st_ok_subst_cells segs OPS E st ms mo 1%uint63 r1 f HS F1 eq_refl HF) as HS1.
    exact (st_ok_rf_map E (setregs st (IMap.add 1%uint63 (subst_cells f r1) (s_regs st))) ms mo f HS1 HF F0).
  - exact (st_ok_rf_map E st ms mo f HS HF F0).
Qed.

Lemma repoint_sound : forall E st ms mo old new,
  st_ok segs OPS E st ms mo -> den E new = den E old -> sv_eqb (VL wzero) old = false ->
  st_ok segs OPS E (repoint old new st) ms mo.
Proof. intros E st ms mo old new. exact (repoint_g_sound false E st ms mo old new). Qed.

End WithSegs.

End PkAux.
