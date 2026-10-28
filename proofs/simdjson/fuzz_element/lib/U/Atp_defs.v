(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ATP_ELEM : Z := 0x3dad0.
Definition ATP_OBJ : Z := 0x3f058.
Definition ATP_ATKEY : Z := 0x3f658.
Definition ATP_ARR : Z := 0x3f3e0.
Definition ATP_ARRAT : Z := 0x3f904.
Definition ATP_TIX : Z := 0x3e064.
Definition ATP_SVFIND : Z := 0x3f5f4.
Definition STR_REPLACE : Z := 0x7d698.
Definition STR_REPLACE4 : Z := 0x7d2f8.
Definition STR_FIND : Z := 0x7dc00.
Definition LIT_TILDE : Z := 0x137b1.
Definition LIT_SLASH : Z := 0x10c43.
Definition ARR_DIV10 : Z := 0x14028.

Definition ATP_LEAFX : Z := 16 + RMALLOC_STACK.
Definition elem_need (d : nat) : Z := 272 * Z.of_nat d + 64 + ATP_LEAFX.
Definition obj_need (d : nat) : Z := 208 + elem_need d.
Definition arr_need (d : nat) : Z := 80 + elem_need d.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Record aenv : Type := mkAE {
  ae_LB : list block;  ae_lo : Z;  ae_B : Z;
  ae_DOC : Z;  ae_TAPE : Z;  ae_SBUF : Z;  ae_tws : list Z;  ae_sbs : list Z;
  ae_PTR : Z;  ae_p1 : list Z }.

Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Definition in_blocks (LB : list block) (A n : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b.

Record aenv_ok (E : aenv) : Prop := mkAEok {
  ok_wf : tape_wf (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E);
  ok_sbs : Forall (fun c => 0 <= c < 256) (ae_sbs E);
  ok_p1 : Forall (fun c => 0 <= c < 256) (ae_p1 E);
  ok_p1len : zlength (ae_p1 E) < 2^26;
  ok_tape : in_blocks (ae_LB E) (ae_TAPE E) (8 * ae_n E);
  ok_sbuf : in_blocks (ae_LB E) (ae_SBUF E) (ae_sn E);
  ok_ptr : ae_p1 E = [] \/ in_blocks (ae_LB E) (ae_PTR E) (zlength (ae_p1 E));
  ok_ptr0 : 0 <= ae_PTR E /\ ae_PTR E + zlength (ae_p1 E) < 2^63;
  ok_lo : alloc_ceiling <= ae_lo E /\ GLOBALS_TOP <= ae_lo E;
  ok_B : ae_B E < 2^63;
  ok_doc : ae_lo E <= ae_DOC E /\ ae_DOC E + 24 <= ae_B E;
  ok_al : ae_DOC E mod 8 = 0 /\ ae_TAPE E mod 8 = 0 }.

Definition AINV (E : aenv) (m : mem) : Prop :=
  bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E)))
  /\ bytes_at usegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E))
  /\ bytes_at usegs m (ae_PTR E) (map (Z_to_bv 8) (ae_p1 E))
  /\ rw_cells usegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))].

Lemma AINV_agree : forall E (P : Z -> Prop) m m',
  AINV E m -> agree_on P m m' ->
  (forall a, in_block (ae_LB E) a -> P a) -> (forall a, ae_DOC E <= a < ae_DOC E + 16 -> P a) ->
  aenv_ok E -> AINV E m'.
Proof.
  intros E P m m' (A1 & A2 & A3 & A4) AG HB HD OK.
  destruct OK as [_ _ _ _ (bt & Bt1 & Bt2 & Bt3) (bsb & Bs1 & Bs2 & Bs3) BP _ _ _ _ _].
  assert (X : forall A bs b, In b (ae_LB E) -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b ->
              bytes_at usegs m A bs -> bytes_at usegs m' A bs).
  { intros A bs b Hb H1 H2 H. eapply bytes_at_agree; [exact AG| exact H|]. intros a Ha. apply HB. exists b. split; [exact Hb| lia]. }
  split; [| split; [| split]].
  - eapply X; [exact Bt1| exact Bt2| | exact A1]. rewrite u64s_length, length_map. lia.
  - eapply X; [exact Bs1| exact Bs2| | exact A2]. rewrite length_map. lia.
  - destruct BP as [E0|(bp & Bp1 & Bp2 & Bp3)].
    + rewrite E0 in A3 |- *. destruct A3 as (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn in Hi. lia.
    + eapply X; [exact Bp1| exact Bp2| | exact A3]. rewrite length_map. unfold zlength in Bp3. lia.
  - eapply rw_cells_agree; [exact AG| exact A4|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HD. lia.
Qed.

Lemma in_blocks_range : forall s LB m A n, RHEAP s LB m -> in_blocks LB A n -> 0 <= n ->
  0 < A /\ A + n <= alloc_ceiling.
Proof.
  intros s LB m A n H (b & Hb & H1 & H2) Hn.
  pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Lemma in_blocks_in_block : forall LB A n a, in_blocks LB A n -> A <= a < A + n -> in_block LB a.
Proof. intros LB A n a (b & Hb & H1 & H2) Ha. exists b. split; [exact Hb| lia]. Qed.

Lemma blocks_below : forall s LB m a, RHEAP s LB m -> in_block LB a -> 0 < a < alloc_ceiling.
Proof.
  intros s LB m a H (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Lemma aenv_ranges : forall E s m, aenv_ok E -> RHEAP s (ae_LB E) m ->
  (0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling)
  /\ (0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling)
  /\ (0 <= ae_PTR E /\ ae_PTR E + zlength (ae_p1 E) < 2^63 /\ (ae_p1 E = [] \/ ae_PTR E + zlength (ae_p1 E) <= alloc_ceiling)).
Proof.
  intros E s m OK H. destruct OK as [_ _ _ _ BT BS BP BP0 _ _ _ _].
  split; [eapply in_blocks_range; [exact H| exact BT| lia]|].
  split; [eapply in_blocks_range; [exact H| exact BS| lia]|].
  split; [lia|]. split; [lia|].
  destruct BP as [BP|BP]; [left; exact BP| right]. eapply in_blocks_range; [exact H| exact BP| unfold zlength; lia].
Qed.

Definition out_rec (E : aenv) (m' : mem) (out : Z) : Prop :=
  exists (r0 : word) (j code : Z) (jn : list byte),
    rw_cells usegs m' out [C8 r0; C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 code); CB 4 jn] /\ 0 <= code < 64
    /\ (code = 0 -> r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= j /\ exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd j jj).
Definition lvl_R (E : aenv) (q out : Z) (m : mem) : word -> PState -> mem -> Prop :=
  fun _ s' m' => RHEAP s' (ae_LB E) m' /\ lx_pres (ae_LB E) q [(out, out + 24)] m m'
                 /\ out_rec E m' out.

Lemma out_rec_forget : forall E m' out, out_rec E m' out -> exists j, rw_cells usegs m' out [CB 24 j].
Proof.
  intros E m' out (r0 & j & code & jn & H & _). destruct (rw_cells_forget _ _ _ _ H) as [j' H']. cbn [cells_size csize Nat.add] in H'. exists j'. exact H'.
Qed.

Definition ptr_at (E : aenv) (P : Z) (ptr : list Z) : Prop :=
  exists pre, ae_p1 E = pre ++ ptr /\ P = ae_PTR E + zlength pre.

Lemma ptr_at_skip : forall E P ptr k, ptr_at E P ptr -> (k <= length ptr)%nat -> ptr_at E (P + Z.of_nat k) (skipn k ptr).
Proof.
  intros E P ptr k (pre & Ep & EP) Hk. exists (pre ++ firstn k ptr). split.
  - rewrite <- app_assoc, firstn_skipn. exact Ep.
  - rewrite EP. unfold zlength. rewrite length_app, length_firstn. lia.
Qed.

Lemma seg_split : forall l cnt, (cnt <= length l)%nat -> (forall j, (j < cnt)%nat -> nth j l 0 <> 47) ->
  take_seg l = firstn cnt l ++ take_seg (skipn cnt l) /\ drop_seg l = drop_seg (skipn cnt l).
Proof.
  induction l as [|c l IH]; intros cnt Hc Hn.
  - destruct cnt; [split; reflexivity| cbn in Hc; lia].
  - destruct cnt as [|cnt]; [split; reflexivity|]. cbn [length] in Hc.
    pose proof (Hn O ltac:(lia)) as H0. cbn [nth] in H0.
    cbn [take_seg drop_seg firstn skipn app]. destruct (Z.eqb_spec c 47); [lia|].
    destruct (IH cnt ltac:(lia) ltac:(intros j Hj; exact (Hn (S j) ltac:(lia)))) as [E1 E2].
    rewrite E1, E2. split; reflexivity.
Qed.

Lemma skipn_cons_nth : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
  induction l as [|c l IH]; intros [|k] Hk; cbn in Hk |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_cons : forall (c : Z) l, zlength (c :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.
Lemma zlength_skipn : forall (l : list Z) k, (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma zlength_nonneg : forall (l : list Z), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Definition atp_elem_stmt (E : aenv) (d : nat) : Prop :=
  forall (ptr : list Z) (i j : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (errv : word) (jo : list byte),
    AINV E m -> ptr_at E P ptr ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    rw_cells usegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E ->
    (node + 16 <= out \/ out + 24 <= node) ->
    rw_cells usegs m out [CB 24 jo] -> q <= out -> (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out) -> out + 24 <= ae_B E ->
    RHEAP s (ae_LB E) m -> rauxv_ok m (ae_B E) -> q <= ae_DOC E ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - elem_need d -> q mod 16 = 0 ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    implM usegs (atp_walk lops (ptr_segs ptr)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m))
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
               (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_ELEM) fc None m (seg_rom usegs)).

Definition atp_obj_stmt (E : aenv) (d : nat) : Prop :=
  forall (ptr : list Z) (i e c : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (errv : word) (jo : list byte),
    AINV E m -> ptr_at E P ptr ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 -> ae_T E e = tword t_obj_end i ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    (exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd i jj) ->
    rw_cells usegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E ->
    (node + 16 <= out \/ out + 24 <= node) ->
    rw_cells usegs m out [CB 24 jo] -> q <= out -> (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out) -> out + 24 <= ae_B E ->
    RHEAP s (ae_LB E) m -> rauxv_ok m (ae_B E) -> q <= ae_DOC E ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - obj_need d -> q mod 16 = 0 ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    implM usegs (atp_walk lops (ptr_segs ptr)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m))
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
               (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_OBJ) fc None m (seg_rom usegs)).

Definition atp_arr_stmt (E : aenv) (d : nat) : Prop :=
  forall (ptr : list Z) (i e c : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (errv : word) (jo : list byte),
    AINV E m -> ptr_at E P ptr ->
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> ae_T E e = tword t_arr_end i ->
    tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    (exists dd jj, elem (ae_T E) (ae_S E) (ae_sn E) ck_any dd i jj) ->
    rw_cells usegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_B E ->
    (node + 16 <= out \/ out + 24 <= node) ->
    rw_cells usegs m out [CB 24 jo] -> q <= out -> (out + 24 <= ae_DOC E \/ ae_DOC E + 24 <= out) -> out + 24 <= ae_B E ->
    RHEAP s (ae_LB E) m -> rauxv_ok m (ae_B E) -> q <= ae_DOC E ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - arr_need d -> q mod 16 = 0 ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    implM usegs (atp_walk lops (ptr_segs ptr)) s
      (fun _ => hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (ae_lo E) (ae_B E) (lvl_R E q out m))
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
               (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_ARR) fc None m (seg_rom usegs)).

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

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) <->
  rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Lemma zbytes_read1 : forall m A (l : list Z) (k : Z),
  bytes_at usegs m A (map (Z_to_bv 8) l) -> 0 <= k < zlength l ->
  ov_read_bytes usegs m (wa (A + k)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) l 0)].
Proof.
  intros m A l k HB Hk. unfold zlength in Hk.
  rewrite (bytes_at_read usegs m A _ k 1 HB); [| lia| rewrite length_map; lia]. f_equal.
  rewrite <- (map_nth (Z_to_bv 8)).
  remember (map (Z_to_bv 8) l) as ml eqn:El.
  assert (HL : (Z.to_nat k < length ml)%nat) by (subst ml; rewrite length_map; lia). clear El HB Hk.
  revert ml HL. generalize (Z.to_nat k) as n. clear k.
  induction n as [|n IH]; intros [|c ml] HL; cbn [length] in HL; try lia; [reflexivity|].
  cbn [drop nth]. apply IH. lia.
Qed.

Lemma Forall_nth_Z : forall (P : Z -> Prop) l k, Forall P l -> (k < length l)%nat -> P (nth k l 0).
Proof.
  intros P l k H Hk. apply (Forall_nth (fun x => P x) l); [exact H| exact Hk].
Qed.

Lemma tword_range : forall t v, 0 <= t < 256 -> 0 <= v < 2^56 -> 0 <= tword t v < 2^64.
Proof. intros t v Ht Hv. unfold tword. lia. Qed.

Lemma cword_range : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX -> 0 <= cword t nxt cv < 2^64.
Proof. intros t nxt cv Ht Hn Hc. unfold cword. apply tword_range; [lia|]. unfold CNT_MAX in Hc. lia. Qed.

Lemma elem_word_range : forall (T S : Z -> Z) (sn : Z) (d : nat) (i j : Z),
  elem T S sn ck_any d i j -> 0 <= i -> j < 2^32 -> sn < 2^56 -> 0 <= T i < 2^64.
Proof.
  intros T S sn d i j EL Hi Hj Hsn. pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (SC : scalar T S sn i j -> 0 <= T i < 2^64).
  { intros [[_ [X|[X|X]]]|[[_ [X|[X|X]]]|[_ (o & l & X & (Y1 & Y2 & Y3 & _))]]]; rewrite X;
      try (apply tword_range; [unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl; lia| lia]).
    apply tword_range; [unfold t_str; lia| lia]. }
  destruct d as [|d']; cbn [elem] in EL; fold (elem T S sn ck_any) in EL.
  - destruct EL as [EL|[]]. exact (SC EL).
  - destruct EL as [EL|(e & c & cv & Ej & CK & CS)]; [exact (SC EL)|].
    unfold ck_any in CK.
    destruct CS as [(X & _ & _)|(X & _ & _)]; rewrite X; (apply cword_range; [unfold t_arr, t_obj; lia| lia| exact CK]).
Qed.

Lemma close_word_range : forall t i, 0 <= t < 256 -> 0 <= i < 2^32 -> 0 <= tword t i < 2^64.
Proof. intros t i Ht Hi. apply tword_range; lia. Qed.

Lemma key_word_range : forall (T S : Z -> Z) (sn i : Z), is_str T S sn i -> sn < 2^56 ->
  0 <= T i < 2^64 /\ Z.land (T i) 72057594037927935 = tval (T i) /\ ttype (T i) = t_str.
Proof.
  intros T S sn i (o & l & X & (Y1 & Y2 & Y3 & _)) Hsn. rewrite X.
  split; [apply tword_range; [unfold t_str; lia| lia]|].
  split; [| apply ttype_tword; lia].
  change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
  unfold tval. reflexivity.
Qed.

End WithCeiling0.

Lemma a_zxb_small : forall x, (0 <= x < 256)%Z -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma a_u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma a_u64_small : forall c, (0 <= c < 2^64)%Z -> bv_unsigned (Z_to_bv 64 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma a_zx32_small : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite a_u64_small by lia. apply Z.mod_small. lia. Qed.
Lemma a_swrap32_small : forall x, (-2147483648 <= x < 2147483648)%Z -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma a_sx32_small : forall x, (0 <= x < 2^31)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. f_equal. rewrite a_u64_small by lia. apply a_swrap32_small. lia. Qed.
Lemma a_shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma a_shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma a_shr56 : forall w, Z.shiftr w 56 = ttype w.
Proof. intros. unfold ttype. apply Z.shiftr_div_pow2. lia. Qed.

Lemma a_shl32_shr32 : forall x, (0 <= x)%Z -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = tnext x.
Proof.
  intros x H. unfold tnext. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^32 * 2^32)%Z. rewrite Zmult_mod_distr_r.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac anorm :=
  cbv beta;
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (a_zxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (a_u8_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?c)] => rewrite (a_u64_small c) by lia
  | |- context [zx32 (Z_to_bv 64 ?c)] => rewrite (a_zx32_small c) by lia
  | |- context [sx32 (Z_to_bv 64 ?c)] => rewrite (a_sx32_small c) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (a_swrap32_small x) by lia
  | |- context [Z.modulo ?x 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
  | |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia
  | |- context [Z.shiftr (Z.modulo (Z.shiftl ?x 32) 18446744073709551616) 32] => rewrite (a_shl32_shr32 x) by lia
  | |- context [Z.shiftr ?w 56] => rewrite (a_shr56 w)
  | |- context [Z.shiftl ?x 3] => rewrite (a_shl3 x)
  | |- context [Z.shiftl ?x 1] => rewrite (a_shl1 x)
  end.
Ltac astep := zstep; anorm.

Lemma ttype_range : forall w t, ttype w = t -> (0 <= t)%Z -> (t < 256)%Z -> (0 <= w < 2^64)%Z.
Proof.
  intros w t H Ht0 Ht1. unfold ttype in H.
  pose proof (Z.div_mod w (2^56) ltac:(lia)) as D. pose proof (Z.mod_pos_bound w (2^56) ltac:(lia)) as R. rewrite H in D. lia.
Qed.

Lemma land32_tnext : forall w, (0 <= w)%Z -> Z.land w 4294967295 = tnext w.
Proof. intros w H. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land64_mod : forall x, Z.land x 18446744073709551615 = (x mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma Z_to_bv64_eqm : forall a b, (a mod 2^64 = b mod 2^64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. exact H. Qed.

Ltac atp_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia | apply Z_to_bv64_eqm; rewrite ?land64_mod; lia]
  | |- _ => reflexivity
  end.
Ltac atp_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; atp_st_eq_tree
  | |- Some _ = Some _ => f_equal; atp_st_eq_leaf
  | |- _ => atp_st_eq_leaf
  end.
Ltac atp_st_eq :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; atp_st_eq_tree
  end.

Ltac atp_st_eq_goal :=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; atp_st_eq_tree
  | |- _ => reflexivity
  end.

Ltac to_implM_at Q :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost _) ?ms => change (Monad.implM segs c st Q ms) end.
Ltac name_mem mx := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => rename m into mx end.

Ltac stop_now :=
  apply evt_done;
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost (fun p => ?H (snd p))) ?ms =>
    change (Monad.implM segs c st (fun _ : unit => H) ms); apply implM_atp_walk_stop; cbv beta end.

Ltac if_lia :=
  let K := fresh "Kc" in
  if_cases K; zify_cond K; rewrite ?land64_mod in K; try (exfalso; lia); [try clear K].
