(* The slot's ENTRY (arm `en`, prefix LE): the tail of interfaces() (fuzz_link.c:97-99),
   the instructions 0x13928 .. 0x13984 of the plain image, as one evt lemma `le_oloop`.

     13928 .. 13944   a0 = 101, a1 = 0x42000, a2 = g_nl + 0x42000, a3 = &odd[1], a4 = &odd[5],
                      and `sd a4, 8(sp)` stores &odd[0] into the frame cell at +8
     13948 .. 13984   four rounds: if_name[n_if] = odd[i], n_if = n_if + 1, if_index[old n_if] = a0,
                      a0 = a0 + 1, a3 = a3 + 8, `bne a3, a4` back to 0x13948

   The four rounds add the rows (odd[1], 101) .. (odd[4], 104) (LEDefs' o_ps / o_ixs).  One round is
   `le_oround`; its memory facts are `round_mem`.  Every store of a round lands in g_nl at or above
   NK_IF_NAME; the frame store lands at S - 472.  Addresses are read from the plain image
   (link/ct/dis/plain/LLVMFuzzerTestOneInput.s): g_nl = 0x31b80 (203648), so g_nl + 0x42000 = 473984,
   &if_name[0] = 474672, &if_index[0] = 475312, &n_if = 475632; odd = 0x207c0 (133056). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Small facts
   ========================================================================== *)

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity. lia.
Qed.

Lemma lr_len : forall R, length (lr_bytes R) = 104%nat.
Proof. intros R. unfold lr_bytes, saved_bytes. rewrite !length_app, !length_le8. reflexivity. Qed.

Lemma firstn_snoc : forall {A : Type} (l : list A) t d, (t < length l)%nat ->
  firstn (S t) l = firstn t l ++ [nth t l d].
Proof.
  intros A l. induction l as [|x l IH]; intros t d H; [cbn in H; lia|].
  destruct t as [|t]; [reflexivity|]. cbn [firstn nth app]. cbn [length] in H.
  rewrite (IH t d) by lia. reflexivity.
Qed.

Lemma nth_snoc : forall (l : list Z) x k, k = length l -> nth k (l ++ [x]) 0 = x.
Proof. intros l x k ->. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma g_ps_len : length (g_ps 64) = 60%nat.
Proof. unfold g_ps. rewrite length_map. exact kept_64_length. Qed.

Lemma g_ixs_len : length (g_ixs 64) = 60%nat.
Proof. unfold g_ixs. rewrite length_map. exact kept_64_length. Qed.

Lemma o_ps_nth : forall t, (t < 4)%nat -> nth (S t) odd_ptrs 0 = nth t o_ps 0.
Proof. intros t Ht. do 4 (destruct t as [|t]; [reflexivity|]). lia. Qed.

Lemma o_ixs_nth : forall t, (t < 4)%nat -> nth t o_ixs 0 = 101 + Z.of_nat t.
Proof. intros t Ht. do 4 (destruct t as [|t]; [reflexivity|]). lia. Qed.

Ltac zle := apply Z.leb_le; vm_compute; reflexivity.

(* the six odd[] strings sit in .rodata, below g_nl *)
Lemma odd_lo : forall i, (i < 6)%nat ->
  nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [] ++ [zb 0])) <= A_G_NL.
Proof. intros i Hi. do 6 (destruct i as [|i]; [zle|]). lia. Qed.

(* reading a u32 / u64 the memory view states *)
Lemma rd_u32 : forall m a v e, u32_at m a v -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m a v e H ->. unfold u32_at in H.
  pose proof (bytes_at_read rsegs m a (le4 (wz v)) 0 4 H ltac:(lia)
                ltac:(rewrite length_le4; lia)) as R.
  rewrite Z.add_0_r in R.
  change (skipn (Z.to_nat 0) (le4 (wz v))) with (le4 (wz v)) in R.
  rewrite firstn_all2 in R by (rewrite length_le4; lia). exact R.
Qed.

Lemma rd_u64 : forall m a v e, u64_at m a v -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v e H ->. unfold u64_at in H.
  pose proof (bytes_at_read rsegs m a (le8 (wz v)) 0 8 H ltac:(lia)
                ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R.
  change (skipn (Z.to_nat 0) (le8 (wz v))) with (le8 (wz v)) in R.
  rewrite firstn_all2 in R by (rewrite length_le8; lia). exact R.
Qed.

(* a store g_nl's window allows *)
Lemma st_ok_nl : forall m a j, wr_at rsegs m A_G_NL NK_SIZE -> A_G_NL <= a ->
  a + Z.of_nat j <= A_G_NL + NK_SIZE -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m a j W H1 H2. replace a with (A_G_NL + (a - A_G_NL)) by lia.
  apply (wr_at_store_ok rsegs m A_G_NL NK_SIZE); [exact W | lia | lia].
Qed.

(* a store store_ok allows keeps task_mem *)
Lemma task_mem_store : forall m a bs, MemNorm.task_mem rsegs m ->
  store_ok rsegs m a (length bs) = true -> MemNorm.task_mem rsegs (write_to_mem m a bs).
Proof.
  intros m a bs T Hok x b Hx.
  destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hi & ->)].
  - exact (T _ _ H).
  - pose proof (store_ok_wview rsegs _ _ _ _ Hok Hi) as W.
    destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E.
    + exact (T _ _ E).
    + left. intro HF. apply W. unfold wview. rewrite E, HF. reflexivity.
Qed.

(* ==========================================================================
   2. What a store keeps
   ========================================================================== *)

(* the two kinds of store of this segment: into the table part of g_nl, or into the stack window *)
Definition o_ok (G : lent) (a n : Z) : Prop :=
  0 <= a /\ a + n <= 2 ^ 64 /\
  ((A_G_NL + NK_IF_NAME <= a /\ a + n <= A_G_NL + NK_SIZE) \/ n_S G - SLOT_STACK_Z <= a).

Lemma bw : forall G m a bs c cs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  bytes_at rsegs m c cs ->
  c + Z.of_nat (length cs) <= A_G_NL + NK_IF_NAME \/
  (A_G_NAMES <= c /\ c + Z.of_nat (length cs) <= 0x960e0) ->
  bytes_at rsegs (write_to_mem m (wa a) bs) c cs.
Proof.
  intros G m a bs c cs (P1 & P2 & _ & _ & _) (O1 & O2 & O3) H Hc.
  apply bytes_at_write_other; [exact H | exact O1 | exact O2 |].
  unfold SLOT_STACK_Z, A_G_NL, NK_IF_NAME, NK_SIZE, A_G_NAMES in *. lia.
Qed.

Lemma rcw : forall G m a bs c cs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  rw_cells rsegs m c cs ->
  c + Z.of_nat (cells_size cs) <= A_G_NL + NK_IF_NAME \/
  (A_G_NAMES <= c /\ c + Z.of_nat (cells_size cs) <= 0x960e0) ->
  rw_cells rsegs (write_to_mem m (wa a) bs) c cs.
Proof.
  intros G m a bs c cs (P1 & P2 & _ & _ & _) (O1 & O2 & O3) H Hc.
  apply rw_cells_frame; [exact H | exact O1 | exact O2 |].
  unfold SLOT_STACK_Z, A_G_NL, NK_IF_NAME, NK_SIZE, A_G_NAMES in *. lia.
Qed.

(* a store into the stack window keeps every byte view below 0x960e0 *)
Lemma bw_hi : forall G m a bs c cs, le_place G -> n_S G - SLOT_STACK_Z <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m c cs -> c + Z.of_nat (length cs) <= 0x960e0 ->
  bytes_at rsegs (write_to_mem m (wa a) bs) c cs.
Proof.
  intros G m a bs c cs (P1 & P2 & _ & _ & _) Ha Hl H Hc.
  apply bytes_at_write_other; [exact H | unfold SLOT_STACK_Z in *; lia | exact Hl |].
  unfold SLOT_STACK_Z in *. lia.
Qed.

Lemma img_keep : forall G m a bs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  le_img m -> le_img (write_to_mem m (wa a) bs).
Proof.
  intros G m a bs HP OK (OD & TX & PR & GD). split; [|split; [|split]].
  - intros i Hi. destruct (OD i Hi) as [U [C N]]. split; [|split; [|exact N]].
    + apply (bw G m a bs _ _ HP OK U). left. rewrite length_le8.
      unfold A_ODD, A_G_NL, NK_IF_NAME. lia.
    + apply (bw G m a bs _ _ HP OK C). left. pose proof (odd_lo i Hi).
      unfold NK_IF_NAME. lia.
  - intros i Hi. apply (bw G m a bs _ _ HP OK (TX i Hi)). left. rewrite length_le8.
    unfold A_TEXTS, A_G_NL, NK_IF_NAME. lia.
  - destruct PR as ([P1 N1] & [P2 N2] & [P3 N3] & [P4 N4]).
    split; [split; [apply (bw G m a bs _ _ HP OK P1); left; zle | exact N1]|].
    split; [split; [apply (bw G m a bs _ _ HP OK P2); left; zle | exact N2]|].
    split; [split; [apply (bw G m a bs _ _ HP OK P3); left; zle | exact N3]|].
    split; [apply (bw G m a bs _ _ HP OK P4); left; zle | exact N4].
  - destruct GD as [G1 [c G2]]. split.
    + apply (bw G m a bs _ _ HP OK G1). left. rewrite length_le8.
      unfold A_GOT_GUARD_S, A_G_NL, NK_IF_NAME. lia.
    + exists c. apply (bw G m a bs _ _ HP OK G2). right. rewrite length_le8.
      unfold A_GUARD_S, A_G_NAMES. lia.
Qed.

Lemma la_keep : forall G m a bs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  la_ok m -> la_ok (write_to_mem m (wa a) bs).
Proof.
  intros G m a bs HP OK (la & sl & R & S & L). exists la, sl. split; [|split; [|exact L]].
  - apply (rcw G m a bs _ _ HP OK R). right. cbn [cells_size csize].
    change (Z.to_nat 300) with 300%nat. unfold A_LONG_ALIAS, A_G_NAMES. lia.
  - apply (bw G m a bs _ _ HP OK S). right. rewrite L.
    unfold A_LONG_ALIAS, LONG_ALIAS_SIZE, A_G_NAMES. lia.
Qed.

Lemma base_keep : forall G m a bs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  store_ok rsegs m (wa a) (length bs) = true ->
  le_base G m -> le_base G (write_to_mem m (wa a) bs).
Proof.
  intros G m a bs HP OK SO (IM & LA & PL & ER & MI & TM).
  split; [exact (img_keep G m a bs HP OK IM)|].
  split; [exact (la_keep G m a bs HP OK LA)|].
  split.
  { destruct OK as (O1 & O2 & O3).
    apply (pay_keep_w G m a bs HP PL O1 O2).
    destruct O3 as [[Q1 Q2]|Q];
      [left; unfold A_G_NL, NK_IF_NAME, NK_SIZE in *; lia | right; exact Q]. }
  split; [apply wr_at_write; exact ER|].
  split; [apply mem_inv_store; assumption|].
  apply task_mem_store; assumption.
Qed.

Lemma gnames_keep : forall G m a bs, le_place G -> o_ok G a (Z.of_nat (length bs)) ->
  le_gnames m 64 -> le_gnames (write_to_mem m (wa a) bs) 64.
Proof.
  intros G m a bs HP OK (GA & (jg & GR)). split.
  - intros j Hj. destruct (GA j Hj) as (rest & BA & L). exists rest. split; [|exact L].
    apply (bw G m a bs _ _ HP OK BA). right. rewrite L. unfold A_G_NAMES. lia.
  - exists jg. apply (rcw G m a bs _ _ HP OK GR). right. cbn [cells_size csize].
    unfold G_NAMES_SIZE, A_G_NAMES. lia.
Qed.

Lemma zf_keep : forall m m',
  (forall off v, 0 <= off -> off + 4 <= NK_IF_NAME ->
     u32_at m (A_G_NL + off) v -> u32_at m' (A_G_NL + off) v) ->
  le_zfields m -> le_zfields m'.
Proof.
  intros m m' H (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10). unfold le_zfields.
  refine (conj (H _ _ _ _ Z1) (conj (H _ _ _ _ Z2) (conj (H _ _ _ _ Z3) (conj (H _ _ _ _ Z4)
    (conj (H _ _ _ _ Z5) (conj (H _ _ _ _ Z6) (conj (H _ _ _ _ Z7) (conj (H _ _ _ _ Z8)
    (conj (H _ _ _ _ Z9) (H _ _ _ _ Z10))))))))));
  unfold NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPEN, NK_OPENED,
    NK_CLOSED, NK_MISUSE, NK_N_SENT, NK_IF_NAME; lia.
Qed.

Lemma u32_nl : forall m a bs off v, A_G_NL + NK_IF_NAME <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= off -> off + 4 <= NK_IF_NAME ->
  u32_at m (A_G_NL + off) v -> u32_at (write_to_mem m (wa a) bs) (A_G_NL + off) v.
Proof.
  intros m a bs off v H1 H2 H3 H4 U. unfold u32_at in *.
  apply bytes_at_write_other; [exact U | unfold A_G_NL, NK_IF_NAME in *; lia | exact H2 |].
  left. rewrite length_le4. lia.
Qed.

Lemma fr1_keep : forall G m a bs j0 j1 j2, le_place G -> 0 <= a ->
  a + Z.of_nat (length bs) <= A_G_NAMES ->
  rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells1 (n_p0 G) j0 j1 j2) ->
  rw_cells rsegs (write_to_mem m (wa a) bs) (n_S G - SLOT_FRAME) (fr_cells1 (n_p0 G) j0 j1 j2).
Proof.
  intros G m a bs j0 j1 j2 (P1 & P2 & _ & _ & _) Ha Hl H.
  apply rw_cells_frame; [exact H | exact Ha | unfold A_G_NAMES in Hl; lia |].
  right. unfold SLOT_STACK_Z, SLOT_FRAME, A_G_NAMES in *. lia.
Qed.

Lemma sv_keep : forall G m a bs, le_place G -> 0 <= a ->
  a + Z.of_nat (length bs) <= n_S G - 104 ->
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) ->
  bytes_at rsegs (write_to_mem m (wa a) bs) (n_S G - 104) (lr_bytes (n_R G)).
Proof.
  intros G m a bs (P1 & P2 & _ & _ & _) Ha Hl H.
  apply bytes_at_write_other; [exact H | exact Ha | lia | right; exact Hl].
Qed.

(* ==========================================================================
   3. The memory the odd loop carries: le_if_mem without the table, and the table
   ========================================================================== *)

Definition le_if_rest (G : lent) (m : word -> option byte) : Prop :=
  le_base G m /\
  (exists kb, Z.of_nat (length kb) = NK_SIZE /\ bytes_at rsegs m A_G_NL kb) /\
  wr_at rsegs m A_G_NL NK_SIZE /\ le_zfields m /\ le_gnames m 64 /\
  (exists j0 j1 j2, rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells1 (n_p0 G) j0 j1 j2)) /\
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) /\
  wr_at rsegs m (n_S G - 104) 104 /\
  stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME).

Lemma to_rest : forall G ps ixs m, le_if_mem G 64 ps ixs m -> le_if_rest G m /\ le_tabl m ps ixs.
Proof.
  intros G ps ixs m (B & (K & W & Z & T) & N & Fr & Sv & Sw & St). split; [|exact T].
  exact (conj B (conj K (conj W (conj Z (conj N (conj Fr (conj Sv (conj Sw St)))))))).
Qed.

Lemma of_rest : forall G ps ixs m, le_if_rest G m -> le_tabl m ps ixs -> le_if_mem G 64 ps ixs m.
Proof.
  intros G ps ixs m (B & K & W & Z & N & Fr & Sv & Sw & St) T.
  exact (conj B (conj (conj K (conj W (conj Z T))) (conj N (conj Fr (conj Sv (conj Sw St)))))).
Qed.

(* a store into the table part of g_nl keeps everything but the table *)
Lemma rest_nl_store : forall G m a bs, le_place G ->
  A_G_NL + NK_IF_NAME <= a -> a + Z.of_nat (length bs) <= A_G_NL + NK_SIZE ->
  le_if_rest G m -> le_if_rest G (write_to_mem m (wa a) bs).
Proof.
  intros G m a bs HP H1 H2 (B & (kb & KL & KB) & W & ZF & GN & (j0 & j1 & j2 & FR) & SV & SW & ST).
  pose proof HP as (P1 & P2 & _ & _ & _).
  assert (H0 : 0 <= a) by (unfold A_G_NL, NK_IF_NAME in H1; lia).
  assert (H3 : a + Z.of_nat (length bs) <= 2 ^ 64) by (unfold A_G_NL, NK_SIZE in H2; lia).
  assert (H4 : a + Z.of_nat (length bs) <= A_G_NAMES) by (unfold A_G_NL, NK_SIZE, A_G_NAMES in *; lia).
  assert (H5 : a + Z.of_nat (length bs) <= n_S G - 104)
    by (unfold A_G_NL, NK_SIZE, SLOT_STACK_Z in *; lia).
  assert (OK : o_ok G a (Z.of_nat (length bs))) by (unfold o_ok; lia).
  assert (SO : store_ok rsegs m (wa a) (length bs) = true)
    by (apply st_ok_nl; [exact W | unfold NK_IF_NAME in H1; lia | exact H2]).
  split; [exact (base_keep G m a bs HP OK SO B)|].
  split.
  { exists (upd_bytes kb (Z.to_nat (a - A_G_NL)) bs). split.
    - rewrite upd_bytes_length; [exact KL|]. unfold NK_IF_NAME in H1. lia.
    - pose proof (bytes_at_write_inside rsegs m A_G_NL kb (a - A_G_NL) bs KB) as KW.
      replace (A_G_NL + (a - A_G_NL)) with a in KW by lia.
      apply KW; unfold NK_IF_NAME in H1; lia. }
  split; [apply wr_at_write; exact W|].
  split; [apply (zf_keep m); [intros off v Ho1 Ho2 U; apply u32_nl; assumption | exact ZF]|].
  split; [exact (gnames_keep G m a bs HP OK GN)|].
  split; [exists j0, j1, j2; exact (fr1_keep G m a bs j0 j1 j2 HP H0 H4 FR)|].
  split; [exact (sv_keep G m a bs HP H0 H5 SV)|].
  split; [apply wr_at_write; exact SW|].
  apply stk_write; [exact ST | exact H0 | exact H3].
Qed.

(* the three stores of one round add one row to the table *)
Lemma tabl_round : forall m ps ixs p ix n,
  le_tabl m ps ixs -> Z.of_nat (length ps) = n -> n < 80 ->
  le_tabl (write_to_mem (write_to_mem (write_to_mem m
             (Z_to_bv 64 (474672 + 8 * n)) (le8 (Z_to_bv 64 p)))
             (Z_to_bv 64 475632) (le4 (Z_to_bv 64 (n + 1))))
             (Z_to_bv 64 (475312 + 4 * n)) (le4 (Z_to_bv 64 ix)))
    (ps ++ [p]) (ixs ++ [ix]).
Proof.
  intros m ps ixs p ix n (HL & HN & HR) Hn Hb.
  assert (Hn0 : 0 <= n) by lia.
  split; [rewrite !length_app, HL; reflexivity|].
  split.
  - unfold u32_at.
    apply bytes_at_write_other;
      [ | lia | rewrite length_le4; lia | rewrite !length_le4; unfold A_G_NL, NK_N_IF; lia ].
    replace (wz (Z.of_nat (length (ps ++ [p])))) with (Z_to_bv 64 (n + 1))
      by (unfold wz; f_equal; rewrite length_app; cbn [length]; lia).
    replace (A_G_NL + NK_N_IF) with 475632 by reflexivity.
    apply bytes_at_write_same; rewrite ?length_le4; lia.
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    unfold le_ifrow, u64_at, u32_at.
    destruct (Nat.lt_ge_cases i (length ps)) as [Hlt|Hge].
    + rewrite !app_nth1 by lia. destruct (HR i Hlt) as [U1 U2]. unfold u64_at, u32_at in U1, U2.
      split.
      * apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_NAME; lia ].
        apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_NAME; lia ].
        apply bytes_at_write_other;
          [ exact U1 | lia | rewrite length_le8; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_NAME; lia ].
      * apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_INDEX; lia ].
        apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_INDEX; lia ].
        apply bytes_at_write_other;
          [ exact U2 | lia | rewrite length_le8; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_INDEX; lia ].
    + assert (Ei : i = length ps) by lia. subst i.
      rewrite (nth_snoc ps p (length ps) eq_refl), (nth_snoc ixs ix (length ps) HL).
      split.
      * apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_NAME; lia ].
        apply bytes_at_write_other;
          [ | lia | rewrite length_le4; lia
            | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_IF_NAME; lia ].
        replace (A_G_NL + NK_IF_NAME + 8 * Z.of_nat (length ps)) with (474672 + 8 * n)
          by (unfold A_G_NL, NK_IF_NAME; lia).
        apply bytes_at_write_same; rewrite ?length_le8; lia.
      * replace (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length ps)) with (475312 + 4 * n)
          by (unfold A_G_NL, NK_IF_INDEX; lia).
        apply bytes_at_write_same; rewrite ?length_le4; lia.
Qed.

(* a store into the stack window keeps the table *)
Lemma tabl_hi : forall G m a bs ps ixs, le_place G -> n_S G - SLOT_STACK_Z <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> (length ps <= 80)%nat ->
  le_tabl m ps ixs -> le_tabl (write_to_mem m (wa a) bs) ps ixs.
Proof.
  intros G m a bs ps ixs HP Ha Hl Hn (HL & HN & HR). split; [exact HL|]. split.
  - apply (bw_hi G m a bs _ _ HP Ha Hl HN). rewrite length_le4. unfold A_G_NL, NK_N_IF. lia.
  - intros i Hi. destruct (HR i Hi) as [U1 U2]. split.
    + apply (bw_hi G m a bs _ _ HP Ha Hl U1). rewrite length_le8. unfold A_G_NL, NK_IF_NAME. lia.
    + apply (bw_hi G m a bs _ _ HP Ha Hl U2). rewrite length_le4. unfold A_G_NL, NK_IF_INDEX. lia.
Qed.

(* the frame store `sd a4, 8(sp)`: &odd[0] into the frame cell at +8 *)
Lemma fr_write : forall m A p j0 j1 v,
  rw_cells rsegs m A (fr_cells0 p j0 j1) ->
  rw_cells rsegs (write_to_mem m (wa (A + 8)) (le8 v)) A
    [CB 8 (firstn 8 j0); C8 v; CB 48 (skipn 16 j0); C8 (wz p); CB 304 j1].
Proof.
  intros m A p j0 j1 v H. unfold fr_cells0 in H.
  assert (H2 : rw_cells rsegs m A [CB 8 (firstn 8 j0); CB 8 (firstn 8 (skipn 8 j0));
                                   CB 48 (skipn 16 j0); C8 (wz p); CB 304 j1]).
  { eapply (rw_cells_cb_split rsegs m A _ _ 8 8); [exact H | reflexivity | reflexivity]. }
  exact (rw_cells_write rsegs m A _ 8 (CB 8 (firstn 8 (skipn 8 j0))) (C8 v) H2 eq_refl eq_refl I).
Qed.

(* ==========================================================================
   4. The odd loop's invariant after t of its 4 rounds
   ========================================================================== *)

Definition ole (G : lent) (m0 : word -> option byte) (t : nat) (m : word -> option byte) : Prop :=
  le_if_mem G 64 (g_ps 64 ++ firstn t o_ps) (g_ixs 64 ++ firstn t o_ixs) m /\
  munch (le_W0 G) m0 m /\ wmono rsegs m0 m.

(* the lead-in: the frame store turns le_if_mem0 into the invariant at t = 0 *)
Lemma frame_store_mem : forall G m0 m, le_place G ->
  le_if_mem0 G 64 (g_ps 64) (g_ixs 64) m -> munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  store_ok rsegs m (Z_to_bv 64 (n_S G - SLOT_FRAME + 8)) 8 = true /\
  (forall m1, m1 = write_to_mem m (Z_to_bv 64 (n_S G - SLOT_FRAME + 8)) (le8 (Z_to_bv 64 133056)) ->
   ole G m0 0 m1).
Proof.
  intros G m0 m HP (B & (K & W & ZF & TB) & GN & (j0 & j1 & FR) & SV & SW & ST) MU WM.
  pose proof HP as (P1 & P2 & _ & _ & _).
  set (a := n_S G - SLOT_FRAME + 8).
  assert (Ha0 : 0 <= a) by (unfold a, SLOT_FRAME, SLOT_STACK_Z in *; lia).
  assert (HaS : n_S G - SLOT_STACK_Z <= a) by (unfold a, SLOT_FRAME, SLOT_STACK_Z in *; lia).
  assert (Hl : a + Z.of_nat (length (le8 (Z_to_bv 64 133056))) <= 2 ^ 64)
    by (rewrite length_le8; unfold a, SLOT_FRAME, SLOT_STACK_Z in *; lia).
  assert (HlS : a + Z.of_nat (length (le8 (Z_to_bv 64 133056))) <= n_S G - 104)
    by (rewrite length_le8; unfold a, SLOT_FRAME, SLOT_STACK_Z in *; lia).
  assert (OK : o_ok G a (Z.of_nat (length (le8 (Z_to_bv 64 133056))))) by (unfold o_ok; lia).
  assert (SO : store_ok rsegs m (wa a) (length (le8 (Z_to_bv 64 133056))) = true).
  { rewrite length_le8. destruct FR as [_ FW]. unfold a.
    apply (wr_at_store_ok rsegs m (n_S G - SLOT_FRAME) _ 8 8 FW); [lia|].
    unfold fr_cells0. cbn [cells_size csize]. lia. }
  split; [rewrite length_le8 in SO; exact SO|].
  intros m1 ->. unfold ole. cbn [firstn]. rewrite !app_nil_r.
  split; [|split].
  - split; [exact (base_keep G m a _ HP OK SO B)|].
    split.
    { split; [|split; [|split]].
      - destruct K as (kb & KL & KB). exists kb. split; [exact KL|].
        apply (bw_hi G m a _ _ _ HP HaS Hl KB). rewrite KL. unfold A_G_NL, NK_SIZE. lia.
      - apply wr_at_write. exact W.
      - apply (zf_keep m); [|exact ZF]. intros off v Ho1 Ho2 U.
        apply (bw_hi G m a _ _ _ HP HaS Hl U). rewrite length_le4.
        unfold A_G_NL, NK_IF_NAME in *. lia.
      - apply (tabl_hi G m a _ _ _ HP HaS Hl); [rewrite g_ps_len; lia | exact TB]. }
    split; [exact (gnames_keep G m a _ HP OK GN)|].
    split; [exists (firstn 8 j0), (skipn 16 j0), j1; unfold a; apply fr_write; exact FR|].
    split; [exact (sv_keep G m a _ HP Ha0 HlS SV)|].
    split; [apply wr_at_write; exact SW|].
    apply stk_write; [exact ST | exact Ha0 | exact Hl].
  - apply munch_write; [exact MU | exact Ha0 | exact Hl |].
    unfold le_W0. cbn [inside]. left. rewrite length_le8.
    unfold a, SLOT_FRAME, SLOT_STACK_Z in *. lia.
  - apply wmono_write. exact WM.
Qed.

Ltac mw := apply munch_write;
  [ | lia | rewrite ?length_le4, ?length_le8; lia
    | unfold le_W0; cbn [inside]; right; left; rewrite ?length_le4, ?length_le8;
      unfold A_G_NL, NK_SIZE; lia ].

Ltac rns := apply rest_nl_store;
  [ assumption | unfold A_G_NL, NK_IF_NAME; lia
  | rewrite ?length_le4, ?length_le8; unfold A_G_NL, NK_SIZE; lia | ].

(* the memory facts of round t (t < 4): the two loads, the three stores, the invariant at t + 1 *)
Lemma round_mem : forall G m0 m t, (t < 4)%nat -> le_place G -> ole G m0 t m ->
  ov_read_bytes rsegs m (Z_to_bv 64 475632) 4 = Some (le4 (Z_to_bv 64 (60 + Z.of_nat t))) /\
  ov_read_bytes rsegs m (Z_to_bv 64 (133064 + 8 * Z.of_nat t)) 8 =
    Some (le8 (Z_to_bv 64 (nth t o_ps 0))) /\
  store_ok rsegs m (Z_to_bv 64 (474672 + 8 * (60 + Z.of_nat t))) 8 = true /\
  (forall m1, m1 = write_to_mem m (Z_to_bv 64 (474672 + 8 * (60 + Z.of_nat t)))
                                  (le8 (Z_to_bv 64 (nth t o_ps 0))) ->
   ov_read_bytes rsegs m1 (Z_to_bv 64 475632) 4 = Some (le4 (Z_to_bv 64 (60 + Z.of_nat t))) /\
   store_ok rsegs m1 (Z_to_bv 64 475632) 4 = true /\
   (forall m2, m2 = write_to_mem m1 (Z_to_bv 64 475632) (le4 (Z_to_bv 64 (60 + Z.of_nat t + 1))) ->
    store_ok rsegs m2 (Z_to_bv 64 (475312 + 4 * (60 + Z.of_nat t))) 4 = true /\
    ole G m0 (S t)
      (write_to_mem m2 (Z_to_bv 64 (475312 + 4 * (60 + Z.of_nat t)))
                    (le4 (Z_to_bv 64 (101 + Z.of_nat t)))))).
Proof.
  intros G m0 m t Ht HP (IM & MU & WM).
  apply to_rest in IM. destruct IM as [RS TB].
  pose proof RS as (B & K & W & ZF & GN & FR & SV & SW & ST).
  pose proof B as ((OD & TX & PR & GD) & LA & PL & ER & MI & TM).
  assert (LP : Z.of_nat (length (g_ps 64 ++ firstn t o_ps)) = 60 + Z.of_nat t).
  { rewrite length_app, g_ps_len, length_firstn. change (length o_ps) with 4%nat. lia. }
  pose proof TB as (HL & HN & HRW). rewrite LP in HN.
  destruct (OD (S t) ltac:(lia)) as [U _]. rewrite (o_ps_nth t Ht) in U.
  split; [apply (rd_u32 m _ _ _ HN); reflexivity|].
  split; [apply (rd_u64 m _ _ _ U); unfold A_ODD; lia|].
  split; [apply (st_ok_nl m _ 8 W); unfold A_G_NL, NK_SIZE; lia|].
  intros m1 E1.
  assert (HN1 : u32_at m1 (A_G_NL + NK_N_IF) (60 + Z.of_nat t)).
  { subst m1. unfold u32_at in *.
    apply bytes_at_write_other; [exact HN | lia | rewrite length_le8; lia |].
    rewrite length_le4, length_le8. unfold A_G_NL, NK_N_IF. lia. }
  assert (W1 : wr_at rsegs m1 A_G_NL NK_SIZE) by (subst m1; apply wr_at_write; exact W).
  split; [apply (rd_u32 m1 _ _ _ HN1); reflexivity|].
  split; [apply (st_ok_nl m1 _ 4 W1); unfold A_G_NL, NK_SIZE; lia|].
  intros m2 E2.
  assert (W2 : wr_at rsegs m2 A_G_NL NK_SIZE) by (subst m2; apply wr_at_write; exact W1).
  split; [apply (st_ok_nl m2 _ 4 W2); unfold A_G_NL, NK_SIZE; lia|].
  subst m2 m1. unfold ole. split; [|split].
  - apply of_rest.
    + rns. rns. rns. exact RS.
    + rewrite (firstn_snoc o_ps t 0) by (change (length o_ps) with 4%nat; lia).
      rewrite (firstn_snoc o_ixs t 0) by (change (length o_ixs) with 4%nat; lia).
      rewrite !app_assoc. rewrite (o_ixs_nth t Ht).
      apply (tabl_round m _ _ _ _ (60 + Z.of_nat t) TB LP). lia.
  - mw. mw. mw. exact MU.
  - apply wmono_write. apply wmono_write. apply wmono_write. exact WM.
Qed.

(* ==========================================================================
   5. One round of the odd loop: 0x13948 -> 0x13948 (or 0x13988 after the 4th)
   ========================================================================== *)

Lemma le_oround : forall (t : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (G : lent) (m0 m : word -> option byte),
  (t < 4)%nat -> le_place G ->
  s3 = Z_to_bv 64 203648 -> a0 = Z_to_bv 64 (101 + Z.of_nat t) -> a1 = Z_to_bv 64 270336 ->
  a2 = Z_to_bv 64 473984 -> a3 = Z_to_bv 64 (133064 + 8 * Z.of_nat t) -> a4 = Z_to_bv 64 133096 ->
  ole G m0 t m ->
  evt rsegs (fun ms' => exists (a0' a3' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3' a4 a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if Nat.eqb t 3 then 0x13988 else 0x13948)) fc None m' (seg_rom rsegs) /\
      a0' = Z_to_bv 64 (101 + Z.of_nat (S t)) /\
      a3' = Z_to_bv 64 (133064 + 8 * Z.of_nat (S t)) /\
      ole G m0 (S t) m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13948) fc None m (seg_rom rsegs)).
Proof.
  intros t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc G m0 m Ht HP E3 E10 E11 E12 E13 E14 OL.
  subst s3 a0 a1 a2 a3 a4.
  destruct (round_mem G m0 m t Ht HP OL) as (HR1 & HR2 & HS1 & K1). clear OL.
  (* 13948 lw a5, 0x670(a2) *)
  step. clear HR1.
  rewrite (sx32_small (60 + Z.of_nat t)) by lia.
  (* 1394c ld a6, 0(a3); 13950 add a7, s3, a1; 13954 slli a5, a5, 3 *)
  step. clear HR2.
  step. step.
  rewrite (unsigned_lit (60 + Z.of_nat t)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  (* 13958 add a5, a7, a5; 1395c sd a6, 0x2b0(a5) *)
  step. step. clear HS1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (K1 mm eq_refl) as (HR3 & HS2 & K2) end.
  clear K1.
  (* 13960 lw a5, 0x670(a2) *)
  step. clear HR3.
  rewrite (sx32_small (60 + Z.of_nat t)) by lia.
  (* 13964 add a6, s3, a1; 13968 addi a3, a3, 8; 1396c addi a7, a5, 1; 13970 slli a5, a5, 2 *)
  step. step. step. step.
  rewrite (unsigned_lit (60 + Z.of_nat t)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  (* 13974 sw a7, 0x670(a2) *)
  step. clear HS2.
  (* 13978 add a5, a6, a5 *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (K2 mm eq_refl) as (HS3 & OL) end.
  clear K2.
  (* 1397c sw a0, 0x530(a5); 13980 addi a0, a0, 1; 13984 bne a3, a4 *)
  step. clear HS3.
  step. step.
  replace (bv_eqb (Z_to_bv 64 (133064 + 8 * Z.of_nat t + 8)) (Z_to_bv 64 133096))
    with (Nat.eqb t 3).
  2: { unfold bv_eqb. rewrite !unsigned_lit by lia.
       destruct (Nat.eqb_spec t 3) as [E|E]; symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; lia. }
  destruct (Nat.eqb t 3); cbn [negb]; apply evt_done;
    do 6 eexists; (split; [reflexivity|]);
    (split; [f_equal; lia|]); (split; [f_equal; lia|]); exact OL.
Qed.

(* ==========================================================================
   6. The segment 0x13928 -> 0x13988
   ========================================================================== *)

Lemma le_oloop : forall (G : lent)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte),
  le_place G -> frm0 fc ->
  le_if_mem0 G 64 (g_ps 64) (g_ixs 64) m ->
  munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (fc' : bv 32) (m' : word -> option byte),
       ms' = MS (mkR ra' (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0' t1' t2'
                     (wz (A_G_NAMES + G_NAMES_SIZE)) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42)
                     (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3' t4' t5' t6')
                F (wz L_ODD_DONE) fc' None m' (seg_rom rsegs) /\
       frm0 fc' /\ le_if_mem G 64 link_ptrs (g_ixs 64 ++ o_ixs) m' /\
       munch (le_W0 G) m0 m' /\ wmono rsegs m0 m')
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
             (wz (A_G_NAMES + G_NAMES_SIZE)) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42)
             (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
        F (wz 0x13928) fc None m (seg_rom rsegs)).
Proof.
  intros G ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 F fc m m0 HP FC IM MU WM.
  destruct (frame_store_mem G m0 m HP IM MU WM) as [SO K0]. clear IM.
  unfold wz, A_G_NL.
  (* 13928 auipc a2; 1392c addi a0; 13930 lui a1; 13934 addi a4; 13938 add a2; 1393c addi a3 *)
  do 6 step.
  (* 13940 sd a4, 8(sp) *)
  step. clear SO.
  (* 13944 addi a4, a4, 0x28 *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (K0 mm eq_refl) as O0 end.
  clear K0.
  eapply evt_cut.
  { eapply (le_oround 0); first [exact HP | exact O0 | reflexivity | lia]. }
  intros ms (a0' & a3' & a5' & a6' & a7' & m1 & -> & -> & -> & O1). clear O0.
  eapply evt_cut.
  { eapply (le_oround 1); first [exact HP | exact O1 | reflexivity | lia]. }
  intros ms (a0'' & a3'' & a5'' & a6'' & a7'' & m2 & -> & -> & -> & O2). clear O1.
  eapply evt_cut.
  { eapply (le_oround 2); first [exact HP | exact O2 | reflexivity | lia]. }
  intros ms (b0 & b3 & b5 & b6 & b7 & m3 & -> & -> & -> & O3). clear O2.
  eapply evt_cut.
  { eapply (le_oround 3); first [exact HP | exact O3 | reflexivity | lia]. }
  intros ms (c0 & c3 & c5 & c6 & c7 & m4 & -> & -> & -> & O4). clear O3.
  apply evt_done.
  destruct O4 as (IM4 & MU4 & WM4).
  do 16 eexists. exists fc, m4.
  split; [reflexivity|]. split; [exact FC|].
  split; [|split; [exact MU4 | exact WM4]].
  rewrite link_ptrs_eq. exact IM4.
Qed.
