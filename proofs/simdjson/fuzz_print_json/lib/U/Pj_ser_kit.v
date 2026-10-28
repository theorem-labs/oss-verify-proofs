(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Pj_defs Pj_kit Pj_copy Pj_ser_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma stk_store_ok_at : forall segs (m : mem) lo hi x (j : nat) a,
  stk segs m lo hi -> (lo <= x)%Z -> (x + Z.of_nat j <= hi)%Z -> a = wa x -> store_ok segs m a j = true.
Proof.
  intros segs m lo hi x j a (H0 & H1 & H) Hx Hj ->.
  assert (W : wr_at segs m lo (hi - lo)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (H (lo + i)%Z). lia. }
  replace x with (lo + (x - lo))%Z by lia. apply (wr_at_store_ok segs m lo (hi - lo) (x - lo) j W); lia.
Qed.

Lemma stk_CB : forall segs (m : mem) lo hi, stk segs m lo hi -> (lo <= hi)%Z ->
  exists bs, rw_cells segs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros segs m lo hi H Hle.
  destruct (stk_carve segs m lo hi (Z.to_nat (hi - lo)) H ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (hi - Z.of_nat (Z.to_nat (hi - lo)))%Z with lo in J by lia. exact J.
Qed.

Ltac pj_solve_store0 :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in addr_near_cells k cs0 n;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv_concl_beta_iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv_concl_beta_iota
    end
  end.

Ltac pj_store_wr :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let Ea := addr_expr a in
      match goal with
      | H : stk segs m ?lo ?hi |- _ =>
          rewrite (stk_store_ok_at segs m lo hi Ea n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia));
          cbv beta iota
      end
  end.

Ltac pj_store_done :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      (match goal with
       | H : stk segs m ?lo ?hi |- _ =>
           let n := lazymatch bs with
                    | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                    | Z_to_le_bytes 8 _ => constr:(8%nat) | Z_to_le_bytes 4 _ => constr:(4%nat)
                    | Z_to_le_bytes 2 _ => constr:(2%nat) | Z_to_le_bytes 1 _ => constr:(1%nat)
                    | [_] => constr:(1%nat) end in
           let HS := fresh "HSOK" in
           assert (HS : store_ok segs m a n = true)
             by (apply (stk_store_ok_at segs m lo hi Ea n a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
       end);
      store_done
  | _ => idtac
  end.

Lemma pj_shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma pj_shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma pj_land64 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma pj_zxb_small : forall x, (0 <= x < 256)%Z -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. exact Sj_stage1_kit.zxb_small. Qed.
Lemma pj_u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. exact Sj_stage1_kit.u8_small. Qed.

Ltac pjnorm :=
  cbv beta;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (pj_shl1 x)
  | |- context [Z.shiftl ?x 3] => rewrite (pj_shl3 x)
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (pj_zxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (pj_u8_small c) by lia
  | |- context [Z.land ?x 18446744073709551615] => rewrite (pj_land64 x) by lia
  end.
Ltac pjnorm_in H :=
  repeat match type of H with
  | context [Z.shiftl ?x 1] => rewrite (pj_shl1 x) in H
  | context [Z.shiftl ?x 3] => rewrite (pj_shl3 x) in H
  | context [bv_unsigned (Z_to_bv 64 ?c)] => rewrite (unsigned_lit c) in H by lia
  | context [Z.land ?x 18446744073709551615] => rewrite (pj_land64 x) in H by lia
  end.

Ltac pj_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Ltac pj_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; pj_st_eq_tree
  | |- Some _ = Some _ => f_equal; pj_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac pj_st_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; pj_st_eq_tree
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma in_blocks_in_block : forall LB A n a, in_blocks LB A n -> A <= a < A + n -> in_block LB a.
Proof. intros LB A n a (b & Hb & H1 & H2) Ha. exists b. split; [exact Hb| lia]. Qed.

Lemma blocks_below : forall s LB m a, RHEAP s LB m -> in_block LB a -> 0 < a < alloc_ceiling.
Proof.
  intros s LB m a H (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Lemma sb_pure_ranges : forall E st, senv_ok E -> sb_pure E st ->
  0 < sb_buf st /\ 64 <= sb_cap st <= 134217728 /\ sb_buf st + sb_cap st <= e_SB E + 64
  /\ (sb_buf st + sb_cap st <= e_lo E \/ e_q E <= sb_buf st)
  /\ (sb_buf st + sb_cap st <= 0x10000 \/ 0x110000 <= sb_buf st).
Proof.
  intros E st OK (HF & HC & HB). destruct OK as [_ _ _ _ _ _ HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _].
  pose proof (PJ_CAPMAX_bound (e_len E) HLEN) as CMB.
  pose proof (sb_k_range st HF) as K. assert (0 < 2 ^ sb_k st) by (apply Z.pow_pos_nonneg; lia).
  unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  destruct (sb_blk st) as [b|].
  - destruct HB as (A0 & A16 & N0 & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in AC. lia.
  - destruct HB as (-> & -> & _). lia.
Qed.

Lemma serW_out_block : forall E st s m a, senv_ok E -> SREF E st s m -> in_block (e_LB0 E) a -> outside (serW E st) a.
Proof.
  intros E st s m a OK (HEAP & _ & _ & _ & _ & _ & _ & _ & _ & PURE) HB.
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  assert (BL : 0 < a < alloc_ceiling).
  { eapply blocks_below; [exact HEAP|]. destruct HB as (b & Hb & Hr). exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
  destruct OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold serW. cbn [outside]. split; [lia|]. split; [| split; [lia| exact I]].
  destruct PURE as (_ & _ & PB). unfold sbblocks in HEAP. destruct (sb_blk st) as [b|].
  - cbn [app] in HEAP. pose proof (LH_head_disj _ _ _ _ _ _ HEAP a HB). lia.
  - destruct PB as (EB & EC & _). lia.
Qed.

Lemma serW_out_doc : forall E st a, senv_ok E -> sb_pure E st -> e_DOC E <= a < e_DOC E + 16 -> outside (serW E st) a.
Proof.
  intros E st a OK PURE Ha. pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  destruct OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _ _]. unfold PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold serW. cbn [outside]. split; [lia|]. split; [| split; [lia| exact I]].
  destruct PURE as (_ & _ & PB).
  destruct (sb_blk st) as [b|];
    [destruct PB as (A0 & A16 & N0 & AC & AS); unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in AC; lia
    | destruct PB as (EB & EC & _); lia].
Qed.

Lemma serW_out_image : forall E st a, senv_ok E -> sb_pure E st -> 0x10000 <= a < 0x110000 -> outside (serW E st) a.
Proof.
  intros E st a OK PURE Ha. pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  destruct OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold serW. cbn [outside]. split; [lia|]. split; [lia| split; [lia| exact I]].
Qed.

Lemma ser_ranges : forall E e64 e72 e80 spill isobj st s m, senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  0 < e_TAPE E /\ e_TAPE E + 8 * e_n E <= alloc_ceiling /\ 0 < e_SBUF E /\ e_SBUF E + e_sn E <= alloc_ceiling.
Proof.
  intros E e64 e72 e80 spill isobj st s m OK [(HEAP & _) _]. destruct OK as [_ _ _ _ (bt & Bt & Bt1 & Bt2) (bs & Bs & Bs1 & Bs2) _ _ _ _ _ _ _ _ _ _].
  pose proof (LH_block_range _ _ _ _ HEAP (in_or_app _ _ _ (or_intror Bt))) as (T1 & _ & T3 & T4 & _).
  pose proof (LH_block_range _ _ _ _ HEAP (in_or_app _ _ _ (or_intror Bs))) as (S1 & _ & S3 & S4 & _).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in *. lia.
Qed.

Lemma ser_sep : forall E e64 e72 e80 spill isobj st s m, senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  (e_TAPE E + 8 * e_n E <= sb_buf st \/ sb_buf st + sb_cap st <= e_TAPE E)
  /\ (e_SBUF E + e_sn E <= sb_buf st \/ sb_buf st + sb_cap st <= e_SBUF E).
Proof.
  intros E e64 e72 e80 spill isobj st s m OK HSM.
  pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (T0 & T1 & S0 & S1).
  destruct HSM as [(HEAP & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & PB)) _].
  pose proof OK as [_ _ _ _ (bt & Bt & Bt1 & Bt2) (bs & Bs & Bs1 & Bs2) _ [L1 L2] [Q1 Q2] B63 [SS1 SS2] _ _ _ _ _].
  unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold sbblocks in HEAP. destruct (sb_blk st) as [b|].
  - cbn [app] in HEAP. destruct bt as [[pt At] nt]. destruct bs as [[ps As] ns]. cbn [blk_addr blk_size fst snd] in *.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP Bt) as D1. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP Bs) as D2. lia.
  - destruct PB as (EB & EC & _). lia.
Qed.

Lemma sbblocks_resize : forall st size, sbblocks (sb_resize st size) = sbblocks st.
Proof. intros [buf sz cap blk fuel] size. reflexivity. Qed.

Lemma sb_pure_resize : forall E st size, sb_pure E st -> sb_pure E (sb_resize st size).
Proof. intros E [buf sz cap blk fuel] size H. exact H. Qed.

Lemma SREF_munch : forall E st s m m' size, senv_ok E -> SREF E st s m ->
  munch (serW E st) m m' -> wmono usegs m m' -> SREF E (sb_resize st size) s m'.
Proof.
  intros E st s m m' size OK HR MU WM.
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  pose proof OK as [_ _ _ _ OKT OKS _ [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold SREF. rewrite sbblocks_resize.
  split.
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. unfold serW.
    constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
    destruct PURE as (_ & _ & PB). unfold sbblocks. destruct (sb_blk st) as [b|].
    - eapply (W_ok_block _ (b, sb_buf st, sb_cap st)); [left; reflexivity| cbn; lia| cbn; lia].
    - destruct PB as (EB & EC & _). apply W_ok_stack. cbn. lia. }
  split.
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold serW.
    constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split.
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX.
    destruct HC as [HC|[HC|HC]].
    - unfold serW. cbn [outside]. split; [lia|]. split; [| split; [lia| exact I]].
      destruct PURE as (_ & _ & PB).
      destruct (sb_blk st) as [b|];
        [destruct PB as (A0 & A16 & N0 & AC & AS); unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in AC; lia
        | destruct PB as (EB & EC & _); lia].
    - eapply serW_out_block; eassumption.
    - apply serW_out_image; [exact OK| exact PURE| lia]. }
  split.
  { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
    eapply serW_out_block; [exact OK| exact HR|]. eapply in_blocks_in_block; [exact OKT| lia]. }
  split.
  { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
    eapply serW_out_block; [exact OK| exact HR|]. eapply in_blocks_in_block; [exact OKS| lia]. }
  split.
  { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    apply serW_out_doc; [exact OK| exact PURE| lia]. }
  split.
  { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    apply serW_out_image; [exact OK| exact PURE|]. unfold LX_ERRNO, RATP in Ha. lia. }
  split; [exact FA|]. split; [exact SO|]. apply sb_pure_resize. exact PURE.
Qed.

Lemma u64s_read : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 8 (skipn (8 * i) (u64s ws)) = le8 (nth i ws (Z_to_bv 64 0)).
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul skipn u64s]. rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - replace (8 * S i)%nat with (8 + 8 * i)%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.

Lemma tape_read : forall m TAPE (tws : list Z) (i : Z),
  bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes usegs m (wa (TAPE + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  rewrite (bytes_at_read usegs m TAPE _ (8 * i) 8 HB); [| lia| rewrite u64s_length, length_map; lia].
  replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
  rewrite u64s_read by (rewrite length_map; lia). f_equal. f_equal.
  unfold Tf. apply (map_nth (Z_to_bv 64)).
Qed.

Lemma sbuf_read1 : forall m SBUF (sbs : list Z) (o : Z),
  bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o < Z.of_nat (length sbs) ->
  ov_read_bytes usegs m (wa (SBUF + o)) 1 = Some [Z_to_bv 8 (Tf sbs o)].
Proof.
  intros m SBUF sbs o HB Ho.
  rewrite (bytes_at_read usegs m SBUF _ o 1 HB); [| lia| rewrite length_map; lia]. f_equal.
  unfold Tf. rewrite <- (map_nth (Z_to_bv 8)).
  remember (map (Z_to_bv 8) sbs) as l eqn:El.
  assert (HL : (Z.to_nat o < length l)%nat) by (subst l; rewrite length_map; lia). clear El HB Ho.
  revert l HL. generalize (Z.to_nat o) as k. clear o.
  induction k as [|k IH]; intros [|c l] HL; cbn [length] in HL; try lia; [reflexivity|].
  cbn [drop nth]. apply IH. lia.
Qed.

Lemma tape_read_mu : forall E st s mr m i, senv_ok E -> SREF E st s mr ->
  munch (serW E st) mr m -> wmono usegs mr m -> 0 <= i < e_n E ->
  ov_read_bytes usegs m (wa (e_TAPE E + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (e_T E i))).
Proof.
  intros E st s mr m i OK HR MU WM Hi.
  pose proof (SREF_munch E st s mr m (sb_size st) OK HR MU WM) as (_ & _ & _ & TAPEB & _).
  apply tape_read; assumption.
Qed.

Lemma sbuf_read_mu : forall E st s mr m o, senv_ok E -> SREF E st s mr ->
  munch (serW E st) mr m -> wmono usegs mr m -> 0 <= o < e_sn E ->
  ov_read_bytes usegs m (wa (e_SBUF E + o)) 1 = Some [Z_to_bv 8 (e_S E o)].
Proof.
  intros E st s mr m o OK HR MU WM Ho.
  pose proof (SREF_munch E st s mr m (sb_size st) OK HR MU WM) as (_ & _ & _ & _ & SBUFB & _).
  apply sbuf_read1; assumption.
Qed.

Lemma doc_cells_mu : forall E st s mr m, senv_ok E -> SREF E st s mr ->
  munch (serW E st) mr m -> wmono usegs mr m ->
  rw_cells usegs m (e_DOC E) [C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_SBUF E))].
Proof.
  intros E st s mr m OK HR MU WM.
  pose proof (SREF_munch E st s mr m (sb_size st) OK HR MU WM) as (_ & _ & _ & _ & _ & DOCC & _). exact DOCC.
Qed.

Lemma S_range : forall E o, senv_ok E -> 0 <= e_S E o < 256.
Proof.
  intros E o OK. destruct OK as [_ SB _ _ _ _ _ _ _ _ _ _ _ _ _ _]. unfold Tf.
  destruct (Nat.lt_ge_cases (Z.to_nat o) (length (e_sbs E))) as [L|L].
  - rewrite Forall_forall in SB. apply SB. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma land7_mod8 : forall x k, x mod 8 = 0 -> Z.land (x + 8 * k) 7 = 0.
Proof.
  intros x k H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  replace (x + 8 * k) with (x + k * 8) by lia. rewrite Z_mod_plus_full. exact H.
Qed.

Lemma tape_ref_call : forall (P : machine_state -> Prop) (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (DOC TAPE i rpc : Z) (w2 : word),
  rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 w2] -> TAPE mod 8 = 0 -> 0 < TAPE -> TAPE + 8 * i < 2^64 -> 0 <= i < 2^60 ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  evt usegs P (MS (mkR (Z_to_bv 64 rpc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (TAPE + 8 * i)) (Z_to_bv 64 0) (Z_to_bv 64 TAPE)
                       (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 rpc) fc None m (seg_rom usegs)) ->
  evt usegs P (MS (mkR (Z_to_bv 64 rpc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 PJ_TAPE_REF) fc None m (seg_rom usegs)).
Proof.
  intros until w2. intros DOCC T8 T0 THI Hi RP0 RP2 HK.
  pose proof (rw_cells_bound usegs m DOC _ DOCC) as DB. cbn [cells_size csize Nat.add] in DB.
  unfold PJ_TAPE_REF.

  zstep. zstep. pjnorm. zstep.

  zstep. zstep. unz. zstep. if_false.

  zstep. zstep. zstep. zstep.
  replace (Z.shiftr (i + 1152921504606846976) 61) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  zstep. if_false.

  gtrap. gtrap.

  zstep. rewrite (land7_mod8 TAPE i T8). zstep. if_false.
  zstep. rewrite (ret_pc_even rpc RP0 RP2). exact HK.
Qed.

Lemma land_tmask : forall w, 0 <= w < 2^64 -> Z.land w PJ_TMASK = ttype w * 72057594037927936.
Proof.
  intros w Hw. unfold PJ_TMASK, ttype. change (2 ^ 56) with 72057594037927936.
  replace 18374686479671623680 with (Z.shiftl (Z.ones 8) 56) by reflexivity.
  replace (w / 72057594037927936 * 72057594037927936) with (Z.shiftl (Z.shiftr w 56) 56)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. rewrite !Z.shiftl_spec by lia.
  destruct (Z_lt_le_dec n 56) as [L|L].
  - rewrite !(Z.testbit_neg_r _ (n - 56)) by lia. apply Bool.andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (n - 56 + 56) with n by lia.
    destruct (Z_lt_le_dec n 64) as [M|M].
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
      destruct (Z.eq_dec w 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hw)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma tmask_eq : forall w t, 0 <= w < 2^64 -> (ttype w * 72057594037927936 = t * 72057594037927936 <-> ttype w = t).
Proof. intros w t Hw. split; intros H; lia. Qed.

Lemma SERM_intro : forall E e64 e72 e80 spill isobj st s mr m size (j0 : list byte),
  senv_ok E -> SREF E st s mr -> munch (serW E st) mr m -> wmono usegs mr m ->
  rw_cells usegs m (e_q E + -256) (CB 8 j0 :: C8 spill :: ser_consts E e64 e72 e80) ->
  u8arr usegs m (e_q E + -160) isobj -> length isobj = 16%nat ->
  stk usegs m (e_q E + -144) (e_q E + -104) ->
  rw_cells usegs m (e_q E + -104) (ser_saved E) ->
  rw_cells usegs m (e_SB E + 64) [C8 (Z_to_bv 64 (sb_buf st)); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (sb_cap st))] ->
  0 <= size <= sb_cap st ->
  stk usegs m (sb_buf st) (sb_buf st + sb_cap st) -> stk usegs m (e_SB E) (e_SB E + 64) ->
  mem_inv usegs m -> stk usegs m (e_lo E) (e_q E + -256) ->
  SERM E e64 e72 e80 spill isobj (sb_resize st size) s m.
Proof.
  intros E e64 e72 e80 spill isobj st s mr m size j0 OK HR MU WM FRA FRI FRIL FRT FRS SV SZ BUFS INLS MI ST.
  split; [apply (SREF_munch E st s mr m size OK HR MU WM)|].
  unfold SCUR. destruct st as [buf sz cap blk fuel]. cbn [sb_resize sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
  split; [exists j0; exact FRA|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma SBINV_of_SERM : forall E e64 e72 e80 spill isobj st s m, SERM E e64 e72 e80 spill isobj st s m -> SBINV m (e_SB E) (e_len E) st.
Proof.
  intros E e64 e72 e80 spill isobj st s m [HR HC].
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HF & HCAP & HB)).
  destruct HC as (_ & _ & _ & _ & _ & SV & SZ & BUFS & INLS & _ & _).
  unfold SBINV. split; [exact SV|]. split; [exact SZ|].
  split. { destruct (stk_CB usegs m _ _ BUFS ltac:(lia)) as (bs & HBS). exists bs.
           replace (sb_buf st + sb_cap st - sb_buf st) with (sb_cap st) in HBS by lia. exact HBS. }
  split. { destruct (stk_CB usegs m _ _ INLS ltac:(lia)) as (bs & HBS). exists bs.
           replace (Z.to_nat (e_SB E + 64 - e_SB E)) with 64%nat in HBS by lia. exact HBS. }
  split; [exact HF|]. split; [exact HCAP| exact HB].
Qed.

Lemma sb_pure_of_SBINV : forall E m st, SBINV m (e_SB E) (e_len E) st -> sb_pure E st.
Proof. intros E m st (_ & _ & _ & _ & HF & HC & HB). split; [exact HF|]. split; [exact HC| exact HB]. Qed.

Lemma u8arr_stk : forall (m : mem) A bs, u8arr usegs m A bs -> stk usegs m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs [HB HW].
  assert (RW : rw_cells usegs m A [CB (length bs) bs]).
  { split; [split; [cbn; auto|]|].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW. }
  pose proof (stk_of_rw_cells usegs m A _ RW) as S. cbn [cells_size csize] in S. rewrite Nat.add_0_r in S. exact S.
Qed.

Definition ne_val (b : Z) : Z := nth (Z.to_nat b) pj_ne_table 0.
Definition esc_byte (o : Z) : Z := nth (Z.to_nat o) pj_esc_table 0.

Lemma ne_image : ro_bytes_b usegs PJ_NE_TAB (map (Z_to_bv 8) pj_ne_table) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_image : ro_bytes_b usegs PJ_ESC_TAB (map (Z_to_bv 8) pj_esc_table) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_Forall_range : forall (l : list Z) o, Forall (fun c => 0 <= c < 256) l -> 0 <= nth (Z.to_nat o) l 0 < 256.
Proof.
  intros l o H. destruct (Nat.lt_ge_cases (Z.to_nat o) (length l)) as [L|L].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.
Lemma ne_val_range : forall b, 0 <= ne_val b < 256.
Proof. intros b. apply table_Forall_range. unfold pj_ne_table. repeat (constructor; [lia|]). constructor. Qed.
Lemma esc_byte_range : forall o, 0 <= esc_byte o < 256.
Proof. intros o. apply table_Forall_range. unfold pj_esc_table. repeat (constructor; [lia|]). constructor. Qed.

Lemma zbytes_read1 : forall (m : mem) A (l : list Z) (k : Z),
  bytes_at usegs m A (map (Z_to_bv 8) l) -> 0 <= k < Z.of_nat (length l) ->
  ov_read_bytes usegs m (wa (A + k)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) l 0)].
Proof. intros m A l k HB Hk. exact (sbuf_read1 m A l k HB Hk). Qed.

Lemma ne_read : forall (m : mem) b, mem_inv usegs m -> 0 <= b < 256 ->
  ov_read_bytes usegs m (wa (PJ_NE_TAB + b)) 1 = Some [Z_to_bv 8 (ne_val b)].
Proof.
  intros m b MI Hb. apply zbytes_read1; [| rewrite pj_ne_table_length; lia].
  apply ro_bytes_at; [exact MI| unfold PJ_NE_TAB; lia| rewrite length_map, pj_ne_table_length; unfold PJ_NE_TAB; lia|].
  apply ro_bytes_b_sound. exact ne_image.
Qed.
Lemma esc_read : forall (m : mem) o, mem_inv usegs m -> 0 <= o < 256 ->
  ov_read_bytes usegs m (wa (PJ_ESC_TAB + o)) 1 = Some [Z_to_bv 8 (esc_byte o)].
Proof.
  intros m o MI Ho. apply zbytes_read1; [| rewrite pj_esc_table_length; lia].
  apply ro_bytes_at; [exact MI| unfold PJ_ESC_TAB; lia| rewrite length_map, pj_esc_table_length; unfold PJ_ESC_TAB; lia|].
  apply ro_bytes_b_sound. exact esc_image.
Qed.
Lemma esc_len_byte : forall c, esc_byte (8 * c) = esc_len c.
Proof. reflexivity. Qed.

End WithCeiling0.

Ltac ser_env OK :=
  let OK' := fresh "OKx" in
  pose proof OK as OK';
  destruct OK' as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _];
  unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in L2, Q1.

Ltac ser_open HM OK :=
  let HCUR := fresh "HCUR" in
  let SZ := fresh "SZ" in let R0 := fresh "R0" in let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in
  unfold SERM, sb_grown, sb_resize in HM; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel Nat.pred] in HM;
  destruct HM as [HREF HCUR];
  unfold SCUR, ser_consts in HCUR; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in HCUR;
  destruct HCUR as ((?j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST);
  unfold ser_saved in FRS;
  lazymatch type of HREF with
  | SREF ?E ?st ?s ?m =>
      pose proof (munch_refl (serW E st) m) as MU; pose proof (wmono_refl usegs m) as WM;
      unfold serW in MU; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in MU;
      let PU := fresh "PU" in
      assert (PU : sb_pure E st) by (apply HREF);
      pose proof (sb_pure_ranges E st OK PU) as (R0 & R1 & R2 & R3 & _);
      cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in R0, R1, R2, R3; clear PU
  end.

Ltac ser_close HM OK :=
  match goal with
  | HREF : SREF ?E ?st ?s ?mr, MU : munch _ ?mr ?m, WM : wmono _ ?mr ?m,
    FRA : rw_cells _ ?m _ [CB 8 ?j0; C8 ?spill; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 ?e64; C8 ?e72; C8 ?e80; C8 _],
    FRI : u8arr _ ?m _ ?isobj, FRIL : length ?isobj = 16%nat,
    FRT : stk _ ?m (e_q ?E + -144) _, FRS : rw_cells _ ?m (e_q ?E + -104) _,
    SV : rw_cells _ ?m (e_SB ?E + 64) [C8 (Z_to_bv 64 ?buf); C8 (Z_to_bv 64 ?size); C8 (Z_to_bv 64 ?cap)],
    BUFS : stk _ ?m ?buf (?buf + ?cap), INLS : stk _ ?m (e_SB ?E) (e_SB ?E + 64),
    MI : mem_inv _ ?m, ST : stk _ ?m (e_lo ?E) _ |- _ =>
      let SZ' := fresh "SZc" in
      first [ assert (SZ' : 0 <= size <= sb_cap st) by (cbn [sb_cap]; lia) | fail 100 "ser_close: cannot prove 0 <= size <= cap" ];
      first [ pose proof (SERM_intro E e64 e72 e80 spill isobj st s mr m size j0 OK HREF MU WM FRA FRI FRIL FRT FRS SV SZ' BUFS INLS MI ST) as HM
            | fail 100 "ser_close: SERM_intro does not apply" ];
      unfold sb_resize in HM; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in HM;
      clear SZ' MU WM; clear FRA FRI FRT FRS SV; try clear BUFS; try clear INLS; clear ST; clear MI; clear HREF; clear FRIL
  | _ => fail 100 "ser_close: the open context is incomplete"
  end.
