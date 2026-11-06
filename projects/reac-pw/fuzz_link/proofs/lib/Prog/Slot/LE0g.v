(* The slot's ENTRY (arm `en`, prefix LE): the 64-round name loop of interfaces()
   (fuzz_link.c:86-96), the slot's instructions 0x138cc .. 0x13924, as ONE evt lemma.

   Round k (0 <= k <= 63), read from link/ct/dis/plain/LLVMFuzzerTestOneInput.s:
     138cc addiw s4, s6, -2 ; addi a1, zero, 8 ; mv a0, s0 ; mv a2, s1 ; mv a3, s4
     138e0 jal snprintf                       snprintf(g_names + 8k, 8, "nl%d", k)
     138e4 andi a0, s4, 0xf ; beq a0, s7 (15) -> 0x1391c
     138ec lw a0, 0x670(s9) ; ... ; sd s0, 0x2b0(a0)     if_name[n_if] = g_names + 8k
     13900 lw a0, 0x670(s9) ; addi a1, a0, 1 ; sw a1, 0x670(s9)   n_if = n_if + 1
     1390c ... ; sw s6, 0x530(a0)                        if_index[old n_if] = k + 2
     1391c addiw s6, s6, 1 ; addi s0, s0, 8 ; bne s6, s8 (66) -> 0x138cc

   The proof is split as the round is:
     g0_call         the snprintf call, from snprintf_img_contract (the only Section hypothesis);
     g0_after_call   the memory facts after it (the new name in slot k);
     g0_tail         the instructions 0x138e4 .. 0x13924, with the three table stores as g0_mem;
     g0_after_stores the memory facts after the stores (the table holds one more row);
     g0_round        one round, from the loop head to the next loop head or to 0x13928;
     le_gloop        the 64 rounds, by induction on the rounds left.
   The memory facts move across a call or a store with `g0_kp P m m'`: m' differs from m only at
   addresses in P. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  printf_facts_c snprintf_c snprintf_img_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Memories that agree outside a set of addresses
   ========================================================================== *)

Definition g0_kp (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall x : word, ~ P (bv_unsigned x) -> m' x = m x.

Lemma g0_kp_refl : forall P m, g0_kp P m m.
Proof. intros P m x _. reflexivity. Qed.

Lemma g0_kp_trans : forall P m1 m2 m3, g0_kp P m1 m2 -> g0_kp P m2 m3 -> g0_kp P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(* a write inside P, after a run that kept everything outside P *)
Lemma g0_kp_write : forall (P : Z -> Prop) m m1 a bs,
  g0_kp P m m1 -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat (length bs) -> P z) -> g0_kp P m (write_to_mem m1 (wa a) bs).
Proof.
  intros P m m1 a bs K Ha Hl HP x Hx. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs)));
    cbn [andb]; try exact (K x Hx).
  exfalso. apply Hx. apply HP. lia.
Qed.

Lemma g0_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. intros [H3 _]. apply H3. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H3]. exact (H H3).
Qed.

Lemma g0_kp_munch : forall (P : Z -> Prop) W m m', munch W m m' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ outside W z -> P z) -> g0_kp P m m'.
Proof.
  intros P W m m' MU HW x Hx. apply MU.
  destruct (g0_outside_dec W (bv_unsigned x)) as [H|H]; [exact H|].
  exfalso. apply Hx. apply HW; [|exact H].
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.

Lemma g0_munch_kp : forall (P : Z -> Prop) W m m', g0_kp P m m' ->
  (forall z, P z -> ~ outside W z) -> munch W m m'.
Proof. intros P W m m' K HW x Ho. apply K. intros HP. exact (HW _ HP Ho). Qed.

Lemma g0_bytes_kp : forall (P : Z -> Prop) m m' A bs, g0_kp P m m' -> bytes_at rsegs m A bs ->
  (forall z, A <= z < A + Z.of_nat (length bs) -> ~ P z) -> bytes_at rsegs m' A bs.
Proof.
  intros P m m' A bs K (Ha & Hl & H) HP. split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite K; [reflexivity|].
  rewrite wa_unsigned by lia. apply HP. lia.
Qed.

Lemma g0_rw_kp : forall (P : Z -> Prop) m m' A cs, g0_kp P m m' -> wmono rsegs m m' ->
  rw_cells rsegs m A cs ->
  (forall z, A <= z < A + Z.of_nat (cells_size cs) -> ~ P z) -> rw_cells rsegs m' A cs.
Proof.
  intros P m m' A cs K WM [[Hwf Hb] Hw] HP. split; [split; [exact Hwf|]|].
  - eapply g0_bytes_kp; [exact K | exact Hb |]. rewrite cells_bytes_length by exact Hwf. exact HP.
  - eapply wr_at_transport; [exact Hw | exact WM].
Qed.

Lemma g0_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W12 HB] (Ha & Hn & HW)].
  apply cells_wf_app in W12. destruct W12 as [W1 W2].
  rewrite cells_bytes_app in HB. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Hn, HW.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply HW. lia.
Qed.

(* ==========================================================================
   2. The facts no piece of a round changes
   ========================================================================== *)

Lemma g0_lr_len : forall R, length (lr_bytes R) = 104%nat.
Proof. intros R. unfold lr_bytes, saved_bytes. rewrite !app_length, !length_le8. reflexivity. Qed.

Lemma g0_odd_bound : forall i, (i < 6)%nat ->
  0 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [] ++ [zb 0])) <= 0x10600.
Proof.
  intros i Hi. unfold odd_ptrs, odd_strs, S_ENP, S_ETH0, S_WLAN0, S_VETH, S_GONE0.
  do 6 (destruct i as [|i]; [cbn [nth length app map]; lia|]). lia.
Qed.

(* the image's read-only facts: all below the table of g_nl, except the stack guard *)
Lemma g0_img_kp : forall (P : Z -> Prop) m m',
  (forall z, P z -> 474672 <= z /\ ~ (612472 <= z < 612480)) -> g0_kp P m m' -> le_img m -> le_img m'.
Proof.
  intros P m m' HO K (OD & TX & PR & GD).
  split; [|split; [|split]].
  - intros i Hi. destruct (OD i Hi) as [U [C N]]. pose proof (g0_odd_bound i Hi) as OB.
    split; [|split; [|exact N]].
    + eapply g0_bytes_kp; [exact K | exact U |]. rewrite length_le8.
      intros z Hz Pz. destruct (HO z Pz) as [H1 _]. unfold A_ODD in Hz. lia.
    + eapply g0_bytes_kp; [exact K | exact C |].
      intros z Hz Pz. destruct (HO z Pz) as [H1 _]. lia.
  - intros i Hi. eapply g0_bytes_kp; [exact K | exact (TX i Hi) |]. rewrite length_le8.
    intros z Hz Pz. destruct (HO z Pz) as [H1 _]. unfold A_TEXTS in Hz. lia.
  - destruct PR as ([P1 N1] & [P2 N2] & [P3 N3] & [P4 N4]).
    split; [|split; [|split]]; (split; [|assumption]); (eapply g0_bytes_kp; [exact K | eassumption |]);
      intros z Hz Pz; destruct (HO z Pz) as [H1 _];
      unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, S_PREFIX, S_SERVED, S_VLAN in Hz;
      rewrite ?app_length, ?map_length in Hz; cbn [length] in Hz; lia.
  - destruct GD as [G1 (c & G2)]. split.
    + eapply g0_bytes_kp; [exact K | exact G1 |]. rewrite length_le8.
      intros z Hz Pz. destruct (HO z Pz) as [H1 _]. unfold A_GOT_GUARD_S in Hz. lia.
    + exists c. eapply g0_bytes_kp; [exact K | exact G2 |]. rewrite length_le8.
      intros z Hz Pz. destruct (HO z Pz) as [_ H2]. unfold A_GUARD_S in Hz. lia.
Qed.

(* the name slots j < k *)
Definition g0_slots (m : word -> option byte) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists rest,
    bytes_at rsegs m (A_G_NAMES + 8 * Z.of_nat j) (gname (Z.of_nat j) ++ zb 0 :: rest) /\
    length (gname (Z.of_nat j) ++ zb 0 :: rest) = 8%nat.

Definition g0_stable (G : lent) (k : nat) (m : word -> option byte) : Prop :=
  le_img m /\ la_ok m /\ bytes_at rsegs m (n_p0 G) (n_pl G) /\ wr_at rsegs m A_ERRNO 4 /\
  bytes_at rsegs m (n_S G - 104) (lr_bytes (n_R G)) /\ wr_at rsegs m (n_S G - 104) 104 /\
  le_zfields m /\ wr_at rsegs m A_G_NL NK_SIZE /\ g0_slots m k.

(* where a piece of round k may write: the table of g_nl and above, never the guard, long_alias,
   the payload, the frame, the saved registers or the slots before k *)
Definition g0_out (G : lent) (k : nat) (z : Z) : Prop :=
  474672 <= z /\ ~ (612472 <= z < 612480) /\ ~ (476152 <= z < 476456) /\
  ~ (n_p0 G <= z < n_p0 G + n_len G) /\ z < n_S G - 480 /\
  (z < 475640 \/ 475640 + 8 * Z.of_nat k <= z).

Lemma g0_place : forall G, le_place G ->
  0x960e0 + 65536 <= n_S G /\ n_S G <= 2 ^ 47 /\
  (n_pl G = [] \/ (n_p0 G + n_len G <= 0x10000 \/ 0x97000 <= n_p0 G)) /\
  (n_pl G = [] \/ n_p0 G + n_len G <= n_S G - 65536).
Proof.
  intros G HP. pose proof HP as (H1 & H2 & _ & _ & _).
  destruct (le_pay_cases G HP) as [HE | (HN & HB1 & HB2 & HB3)];
    unfold SLOT_STACK_Z in *; repeat split; try lia; try (left; exact HE); right; lia.
Qed.

(* what snprintf may change: its stack window and the first L bytes at D *)
Definition g0_creg (G : lent) (D L z : Z) : Prop :=
  (n_S G - SLOT_STACK_Z <= z < n_S G - SLOT_FRAME) \/ (D <= z < D + L).

Lemma g0_stable_kp : forall (G : lent) (k : nat) (P : Z -> Prop) m m',
  (forall z, P z -> g0_out G k z) -> g0_kp P m m' -> wmono rsegs m m' ->
  g0_stable G k m -> g0_stable G k m'.
Proof.
  intros G k P m m' HO K WM (IM & LA & PL & ER & SV & SW & ZF & NW & SL).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply (g0_img_kp P m m'); [|exact K|exact IM].
    intros z Pz. destruct (HO z Pz) as (H1 & H2 & _). split; assumption.
  - destruct LA as (la & sl & LR & LB & LL). exists la, sl. split; [|split; [|exact LL]].
    + eapply g0_rw_kp; [exact K | exact WM | exact LR |].
      assert (E : Z.of_nat (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)]) = 301) by reflexivity.
      rewrite E. intros z Hz Pz. destruct (HO z Pz) as (_ & _ & H3 & _). unfold A_LONG_ALIAS in Hz. lia.
    + eapply g0_bytes_kp; [exact K | exact LB |]. rewrite LL.
      intros z Hz Pz. destruct (HO z Pz) as (_ & _ & H3 & _).
      unfold A_LONG_ALIAS, LONG_ALIAS_SIZE in Hz. lia.
  - eapply g0_bytes_kp; [exact K | exact PL |].
    intros z Hz Pz. destruct (HO z Pz) as (_ & _ & _ & H4 & _). unfold n_len in H4. lia.
  - eapply wr_at_transport; [exact ER | exact WM].
  - eapply g0_bytes_kp; [exact K | exact SV |]. rewrite g0_lr_len.
    intros z Hz Pz. destruct (HO z Pz) as (_ & _ & _ & _ & H5 & _). lia.
  - eapply wr_at_transport; [exact SW | exact WM].
  - assert (T4 : forall a v, a + 4 <= 474672 -> u32_at m a v -> u32_at m' a v).
    { intros a v Ha U. eapply g0_bytes_kp; [exact K | exact U |]. rewrite length_le4.
      intros z Hz Pz. destruct (HO z Pz) as (H1 & _). lia. }
    destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
    unfold le_zfields.
    repeat match goal with |- _ /\ _ => split end;
      (apply T4; [unfold A_G_NL, NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO,
                    NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_N_SENT; lia | assumption]).
  - eapply wr_at_transport; [exact NW | exact WM].
  - intros j Hj. destruct (SL j Hj) as (rest & B & L). exists rest. split; [|exact L].
    eapply g0_bytes_kp; [exact K | exact B |]. rewrite L.
    intros z Hz Pz. destruct (HO z Pz) as (_ & _ & _ & _ & _ & H6). unfold A_G_NAMES in Hz. lia.
Qed.

(* the frame below the saved registers: 376 bytes at S - 480 *)
Lemma g0_frame_kp : forall (G : lent) (P : Z -> Prop) m m',
  (forall z, P z -> z < n_S G - SLOT_FRAME) -> g0_kp P m m' -> wmono rsegs m m' ->
  (exists j0 j1, rw_cells rsegs m (n_S G - SLOT_FRAME) (fr_cells0 (n_p0 G) j0 j1)) ->
  (exists j0 j1, rw_cells rsegs m' (n_S G - SLOT_FRAME) (fr_cells0 (n_p0 G) j0 j1)).
Proof.
  intros G P m m' HO K WM (j0 & j1 & FR). exists j0, j1.
  eapply g0_rw_kp; [exact K | exact WM | exact FR |].
  intros z Hz Pz. specialize (HO z Pz). lia.
Qed.

(* the table of g_nl, when a piece writes only above g_nl *)
Lemma g0_tabl_kp : forall (P : Z -> Prop) m m' ps ixs,
  (forall z, P z -> A_G_NL + NK_SIZE <= z) -> g0_kp P m m' -> (length ps <= 80)%nat ->
  le_tabl m ps ixs -> le_tabl m' ps ixs.
Proof.
  intros P m m' ps ixs HO K Hl (L & N & R). split; [exact L|]. split.
  - eapply g0_bytes_kp; [exact K | exact N |]. rewrite length_le4.
    intros z Hz Pz. specialize (HO z Pz). unfold NK_N_IF, NK_SIZE in *. lia.
  - intros i Hi. destruct (R i Hi) as [R1 R2]. split.
    + eapply g0_bytes_kp; [exact K | exact R1 |]. rewrite length_le8.
      intros z Hz Pz. specialize (HO z Pz). unfold NK_IF_NAME, NK_SIZE in *. lia.
    + eapply g0_bytes_kp; [exact K | exact R2 |]. rewrite length_le4.
      intros z Hz Pz. specialize (HO z Pz). unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

(* ==========================================================================
   3. Small facts about the instructions' values
   ========================================================================== *)

Lemma g0_addiw : forall e d r, 0 <= e < 2 ^ 31 -> e + d = r -> 0 <= r < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 e) + d)) = Z_to_bv 64 r.
Proof.
  intros e d r He Hr Hr'. rewrite unsigned_lit by lia. rewrite Hr.
  rewrite (bv_swrap_small 32) by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma g0_sx32 : forall c, 0 <= c < 2 ^ 31 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold sx32. rewrite unsigned_lit by lia.
  rewrite (bv_swrap_small 32) by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma g0_shl3 : forall c, 0 <= c < 2 ^ 32 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c)) 3) = Z_to_bv 64 (8 * c).
Proof.
  intros c Hc. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. f_equal. lia.
Qed.

Lemma g0_shl2 : forall c, 0 <= c < 2 ^ 32 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c)) 2) = Z_to_bv 64 (4 * c).
Proof.
  intros c Hc. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 2) with 4. f_equal. lia.
Qed.

(* `andi a0, s4, 0xf ; beq a0, s7` with s4 = k, s7 = 15 branches exactly when k is skipped *)
Lemma g0_keep_eqb : forall k, (k < 64)%nat ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.of_nat k))) 15)) (Z_to_bv 64 15) = negb (keep k).
Proof.
  intros k Hk. unfold bv_eqb, keep. rewrite Bool.negb_involutive.
  rewrite (unsigned_lit (Z.of_nat k)) by lia.
  assert (HL : Z.land (Z.of_nat k) 15 = Z.of_nat (k mod 16)).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. rewrite Nat2Z.inj_mod. reflexivity. }
  pose proof (Nat.mod_upper_bound k 16 ltac:(lia)) as HM.
  rewrite HL. rewrite !unsigned_lit by lia.
  destruct (Nat.eqb_spec (k mod 16) 15) as [E|E]; [rewrite E; reflexivity|].
  apply Z.eqb_neq. lia.
Qed.

(* `bne s6, s8` with s6 = k + 3, s8 = 66 falls through exactly after round 63 *)
Lemma g0_bne : forall k, (k < 64)%nat ->
  bv_eqb (Z_to_bv 64 (Z.of_nat (S k) + 2)) (Z_to_bv 64 66) = Nat.eqb (S k) 64.
Proof.
  intros k Hk. unfold bv_eqb. rewrite !unsigned_lit by lia.
  destruct (Nat.eqb_spec (S k) 64) as [E|E]; [rewrite E; reflexivity|].
  apply Z.eqb_neq. lia.
Qed.

Lemma g0_read4 : forall m a v, bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H.
  assert (HL : (Z.to_nat 0 + 4 <= length (le4 v))%nat) by (rewrite length_le4; lia).
  assert (FA : firstn 4 (le4 v) = le4 v) by (apply firstn_all2; rewrite length_le4; lia).
  pose proof (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia) HL) as R.
  change (skipn (Z.to_nat 0) (le4 v)) with (le4 v) in R.
  rewrite FA, Z.add_0_r in R. exact R.
Qed.

(* ==========================================================================
   4. The three table stores of a kept round
   ========================================================================== *)

Definition g0_m3 (k : nat) (c : Z) (m : word -> option byte) : word -> option byte :=
  write_to_mem
    (write_to_mem
       (write_to_mem m (wa (A_G_NL + (NK_IF_NAME + 8 * c))) (le8 (wz (A_G_NAMES + 8 * Z.of_nat k))))
       (wa (A_G_NL + NK_N_IF)) (le4 (wz (c + 1))))
    (wa (A_G_NL + (NK_IF_INDEX + 4 * c))) (le4 (wz (Z.of_nat k + 2))).

Definition g0_mem (k : nat) (c : Z) (m : word -> option byte) : word -> option byte :=
  if keep k then g0_m3 k c m else m.

Definition g0_tab (z : Z) : Prop := A_G_NL + NK_IF_NAME <= z < A_G_NL + NK_SIZE.

Ltac g0_side :=
  rewrite ?length_le8, ?length_le4;
  unfold g0_tab, A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF, NK_SIZE; intros; lia.

Lemma g0_m3_kp : forall m k c, 0 <= c <= 63 -> g0_kp g0_tab m (g0_m3 k c m).
Proof.
  intros m k c Hc. unfold g0_m3.
  apply g0_kp_write; [apply g0_kp_write; [apply g0_kp_write; [apply g0_kp_refl|..]|..]|..]; g0_side.
Qed.

Lemma g0_m3_wmono : forall m k c, wmono rsegs m (g0_m3 k c m).
Proof.
  intros m k c. unfold g0_m3.
  apply wmono_write, wmono_write, wmono_write, wmono_refl.
Qed.

Lemma g0_m3_mem_inv : forall m k c, 0 <= c <= 63 -> wr_at rsegs m A_G_NL NK_SIZE ->
  mem_inv rsegs m -> mem_inv rsegs (g0_m3 k c m).
Proof.
  intros m k c Hc W MI. unfold g0_m3.
  apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store; [exact MI|]|]|].
  - rewrite length_le8. apply (wr_at_store_ok rsegs m A_G_NL NK_SIZE); [exact W | g0_side | g0_side].
  - rewrite length_le4. apply (wr_at_store_ok rsegs _ A_G_NL NK_SIZE); [apply wr_at_write; exact W | g0_side | g0_side].
  - rewrite length_le4. apply (wr_at_store_ok rsegs _ A_G_NL NK_SIZE);
      [apply wr_at_write, wr_at_write; exact W | g0_side | g0_side].
Qed.

Lemma g0_task_write : forall m a bs, MemNorm.task_mem rsegs m -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 47 -> MemNorm.task_mem rsegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs T Ha Hl x b Hx.
  destruct (write_to_mem_some bs m (wa a) x b Hx) as [H | (i & Hi & ->)]; [exact (T x b H)|].
  right. assert (TS : TASK_SIZE = 2 ^ 47) by reflexivity. rewrite TS.
  rewrite (wa_unsigned a) by lia. rewrite wa_unsigned by lia. lia.
Qed.

Lemma g0_m3_task : forall m k c, 0 <= c <= 63 -> MemNorm.task_mem rsegs m ->
  MemNorm.task_mem rsegs (g0_m3 k c m).
Proof.
  intros m k c Hc T. unfold g0_m3.
  apply g0_task_write; [apply g0_task_write; [apply g0_task_write; [exact T|..]|..]|..]; g0_side.
Qed.

Lemma g0_m3_stk : forall m k c lo hi, 0 <= c <= 63 -> stk rsegs m lo hi -> stk rsegs (g0_m3 k c m) lo hi.
Proof.
  intros m k c lo hi Hc ST. unfold g0_m3.
  apply stk_write; [apply stk_write; [apply stk_write; [exact ST|..]|..]|..]; g0_side.
Qed.

Lemma g0_inside : forall m kb off bs, bytes_at rsegs m A_G_NL kb -> Z.of_nat (length kb) = NK_SIZE ->
  0 <= off -> off + Z.of_nat (length bs) <= NK_SIZE ->
  exists kb', Z.of_nat (length kb') = NK_SIZE /\ bytes_at rsegs (write_to_mem m (wa (A_G_NL + off)) bs) A_G_NL kb'.
Proof.
  intros m kb off bs HB HL Ho Hb. exists (upd_bytes kb (Z.to_nat off) bs).
  split; [rewrite upd_bytes_length by lia; exact HL|].
  apply bytes_at_write_inside; [exact HB | lia | lia].
Qed.

Lemma g0_m3_kb : forall m k c kb, 0 <= c <= 63 -> Z.of_nat (length kb) = NK_SIZE ->
  bytes_at rsegs m A_G_NL kb ->
  exists kb', Z.of_nat (length kb') = NK_SIZE /\ bytes_at rsegs (g0_m3 k c m) A_G_NL kb'.
Proof.
  intros m k c kb Hc HL HB. unfold g0_m3.
  destruct (g0_inside m kb (NK_IF_NAME + 8 * c) (le8 (wz (A_G_NAMES + 8 * Z.of_nat k))) HB HL
              ltac:(g0_side) ltac:(g0_side)) as (kb1 & L1 & B1).
  destruct (g0_inside _ kb1 NK_N_IF (le4 (wz (c + 1))) B1 L1 ltac:(g0_side) ltac:(g0_side)) as (kb2 & L2 & B2).
  destruct (g0_inside _ kb2 (NK_IF_INDEX + 4 * c) (le4 (wz (Z.of_nat k + 2))) B2 L2
              ltac:(g0_side) ltac:(g0_side)) as (kb3 & L3 & B3).
  exists kb3. split; [exact L3 | exact B3].
Qed.

(* a fact away from the three stores *)
Lemma g0_m3_other : forall m k c A bs, 0 <= c <= 63 -> bytes_at rsegs m A bs ->
  (A + Z.of_nat (length bs) <= A_G_NL + NK_IF_NAME + 8 * c \/
   (A_G_NL + NK_IF_NAME + 8 * c + 8 <= A /\ A + Z.of_nat (length bs) <= A_G_NL + NK_IF_INDEX + 4 * c) \/
   (A_G_NL + NK_IF_INDEX + 4 * c + 4 <= A /\ A + Z.of_nat (length bs) <= A_G_NL + NK_N_IF) \/
   A_G_NL + NK_N_IF + 4 <= A) ->
  bytes_at rsegs (g0_m3 k c m) A bs.
Proof.
  intros m k c A bs Hc HB HD. pose proof (bytes_at_bound rsegs m A bs HB) as HBB. unfold g0_m3.
  apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other; [exact HB|..]|..]|..];
    rewrite ?length_le8, ?length_le4;
    unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF in *; lia.
Qed.

Lemma g0_tabl_step : forall m ps ixs (k : nat),
  le_tabl m ps ixs -> (length ps <= 63)%nat ->
  le_tabl (g0_m3 k (Z.of_nat (length ps)) m)
          (ps ++ [A_G_NAMES + 8 * Z.of_nat k]) (ixs ++ [Z.of_nat k + 2]).
Proof.
  intros m ps ixs k (L & N & R) Hl.
  assert (Hc : 0 <= Z.of_nat (length ps) <= 63) by lia.
  split; [rewrite !app_length, L; reflexivity|]. split.
  - rewrite app_length. cbn [length].
    replace (Z.of_nat (length ps + 1)) with (Z.of_nat (length ps) + 1) by lia.
    unfold u32_at, g0_m3. apply bytes_at_write_other.
    + apply bytes_at_write_same; unfold A_G_NL, NK_N_IF; rewrite ?length_le4; lia.
    + unfold A_G_NL, NK_IF_INDEX; lia.
    + rewrite length_le4. unfold A_G_NL, NK_IF_INDEX; lia.
    + rewrite !length_le4. unfold A_G_NL, NK_IF_INDEX, NK_N_IF; lia.
  - intros i Hi. rewrite app_length in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length ps)) as [Hi'|Hi'].
    + rewrite !app_nth1 by lia. destruct (R i Hi') as [R1 R2]. split.
      * apply g0_m3_other; [exact Hc | exact R1 |]. rewrite length_le8.
        unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF; lia.
      * apply g0_m3_other; [exact Hc | exact R2 |]. rewrite length_le4.
        unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF; lia.
    + assert (Ei : i = length ps) by lia. subst i.
      assert (E1 : nth (length ps) (ps ++ [A_G_NAMES + 8 * Z.of_nat k]) 0 = A_G_NAMES + 8 * Z.of_nat k)
        by (rewrite app_nth2, Nat.sub_diag by lia; reflexivity).
      assert (E2 : nth (length ps) (ixs ++ [Z.of_nat k + 2]) 0 = Z.of_nat k + 2)
        by (rewrite app_nth2 by lia; replace (length ps - length ixs)%nat with 0%nat by lia; reflexivity).
      rewrite E1, E2. split.
      * unfold u64_at, g0_m3.
        replace (A_G_NL + NK_IF_NAME + 8 * Z.of_nat (length ps))
          with (A_G_NL + (NK_IF_NAME + 8 * Z.of_nat (length ps))) by lia.
        apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_same|..]|..];
          rewrite ?length_le8, ?length_le4; unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX, NK_N_IF; lia.
      * unfold u32_at, g0_m3.
        replace (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length ps))
          with (A_G_NL + (NK_IF_INDEX + 4 * Z.of_nat (length ps))) by lia.
        apply bytes_at_write_same; rewrite ?length_le4; unfold A_G_NL, NK_IF_INDEX; lia.
Qed.

(* ==========================================================================
   5. The memory after the stores
   ========================================================================== *)

Lemma g0_after_stores : forall (G : lent) (k : nat) (m m0 : word -> option byte),
  le_place G -> (k < 64)%nat ->
  le_if_mem0 G (S k) (g_ps k) (g_ixs k) m -> munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  le_if_mem0 G (S k) (g_ps (S k)) (g_ixs (S k)) (g0_mem k (Z.of_nat (length (kept k))) m) /\
  munch (le_W0 G) m0 (g0_mem k (Z.of_nat (length (kept k))) m) /\
  wmono rsegs m0 (g0_mem k (Z.of_nat (length (kept k))) m).
Proof.
  intros G k m m0 HP Hk MEM MU WM.
  destruct (g0_place G HP) as (P1 & P2 & P3 & P4).
  unfold g0_mem, g_ps, g_ixs. rewrite kept_S.
  destruct (keep k) eqn:HK.
  2:{ rewrite !app_nil_r. split; [exact MEM|]. split; [exact MU | exact WM]. }
  rewrite !map_app. cbn [map].
  pose proof (kept_le k) as KL.
  assert (Hc : 0 <= Z.of_nat (length (kept k)) <= 63) by lia.
  set (c := Z.of_nat (length (kept k))) in *.
  destruct MEM as (BASE & NLK & GN & FR & SV & SW & ST).
  destruct BASE as (IMG & LA & PL & ER & MI & TM).
  destruct NLK as ((kb & KBL & KB) & NW & ZF & TB).
  destruct GN as (SL & (jg & RC)).
  pose proof (g0_m3_kp m k c Hc) as K.
  pose proof (g0_m3_wmono m k c) as WM3.
  assert (HO : forall z, g0_tab z -> g0_out G (S k) z).
  { intros z Hz. unfold g0_tab, g0_out, A_G_NL, NK_IF_NAME, NK_SIZE in *.
    pose proof HP as (Q1 & _ & _ & _ & _). unfold SLOT_STACK_Z in Q1.
    assert (HPZ : n_len G = 0 \/ (n_p0 G + n_len G <= n_S G - 65536 /\
                   (n_p0 G + n_len G <= 474672 \/ 618496 <= n_p0 G)))
      by (destruct (le_pay_cases G HP) as [HE0 | (HN0 & Ha0 & Hb0 & Hc0)];
          [ left; unfold n_len; rewrite HE0; reflexivity
          | right; unfold n_len, SLOT_STACK_Z in *; split; [lia|]; destruct Hc0; lia ]).
    destruct HPZ as [Qz | (Qs & [Qa | Qa])];
      lia. }
  assert (STB : g0_stable G (S k) (g0_m3 k c m)).
  { apply (g0_stable_kp G (S k) g0_tab m); [exact HO | exact K | exact WM3 |].
    exact (conj IMG (conj LA (conj PL (conj ER (conj SV (conj SW (conj ZF (conj NW SL)))))))). }
  destruct STB as (IM' & LA' & PL' & ER' & SV' & SW' & ZF' & NW' & SL').
  split; [|split].
  - split; [exact (conj IM' (conj LA' (conj PL' (conj ER' (conj (g0_m3_mem_inv m k c Hc NW MI)
                                                                (g0_m3_task m k c Hc TM)))))) |].
    split; [|split; [|split; [|split; [|split]]]].
    + split; [exact (g0_m3_kb m k c kb Hc KBL KB)|]. split; [exact NW'|]. split; [exact ZF'|].
      unfold g_ps, g_ixs in TB.
      replace c with (Z.of_nat (length (map (fun j => A_G_NAMES + 8 * Z.of_nat j) (kept k))))
        by (rewrite map_length; reflexivity).
      apply g0_tabl_step; [exact TB | rewrite map_length; lia].
    + split; [exact SL'|]. exists jg.
      eapply g0_rw_kp; [exact K | exact WM3 | exact RC |].
      intros z Hz Pz. unfold g0_tab, A_G_NL, NK_IF_NAME, NK_SIZE, A_G_NAMES in *. lia.
    + apply (g0_frame_kp G g0_tab m); [|exact K | exact WM3 | exact FR].
      intros z Hz. destruct (HO z Hz) as (_ & _ & _ & _ & H5 & _). unfold SLOT_FRAME. lia.
    + exact SV'.
    + exact SW'.
    + apply g0_m3_stk; [exact Hc | exact ST].
  - eapply munch_trans; [exact MU|]. eapply (g0_munch_kp g0_tab); [exact K|].
    intros z Hz Ho. unfold le_W0 in Ho. cbn [outside] in Ho. destruct Ho as (_ & O2 & _).
    apply O2. unfold g0_tab, A_G_NL, NK_IF_NAME, NK_SIZE in *. lia.
  - eapply wmono_trans; [exact WM | exact WM3].
Qed.

(* ==========================================================================
   6. The memory after snprintf
   ========================================================================== *)

Lemma g0_split : forall m (k : nat) jg, (k < 64)%nat ->
  rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k) [CB (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat k)) jg] ->
  exists j8 jr, rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k) [CB 8 j8] /\
    rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k + 8)
      [CB (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat (S k))) jr].
Proof.
  intros m k jg Hk H.
  assert (E : Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat k)
              = (8 + Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat (S k)))%nat) by (unfold G_NAMES_SIZE; lia).
  rewrite E in H.
  pose proof (rw_cells_split_CB rsegs m _ [] _ jg [] [8%nat; Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat (S k))]
                H ltac:(cbn [sum_nat]; lia)) as H2.
  cbn [app mk_CB_cells] in H2.
  apply (g0_rw_app m _ [CB 8 (firstn 8 jg)]) in H2. destruct H2 as [H8 HR].
  exists (firstn 8 jg), (firstn (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat (S k))) (skipn 8 jg)).
  split; [exact H8|]. exact HR.
Qed.

Lemma g0_pf_bytes : forall k, pf_bytes (gname_z k ++ [0]) = gname k ++ [zb 0].
Proof. intros k. unfold pf_bytes, gname. rewrite map_app. reflexivity. Qed.

Lemma g0_after_call : forall (G : lent) (k : nat) (m m' m0 : word -> option byte) (j8 jr : list byte),
  le_place G -> (k < 64)%nat ->
  le_if_mem0 G k (g_ps k) (g_ixs k) m -> munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k) [CB 8 j8] ->
  rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k + 8) [CB (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat (S k))) jr] ->
  munch [(n_S G - SLOT_STACK_Z, n_S G - SLOT_FRAME);
         (A_G_NAMES + 8 * Z.of_nat k,
          A_G_NAMES + 8 * Z.of_nat k + Z.of_nat (length (gname_z (Z.of_nat k))) + 1)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME) ->
  bytes_at rsegs m' (A_G_NAMES + 8 * Z.of_nat k) (pf_bytes (gname_z (Z.of_nat k) ++ [0])) ->
  le_if_mem0 G (S k) (g_ps k) (g_ixs k) m' /\ munch (le_W0 G) m0 m' /\ wmono rsegs m0 m'.
Proof.
  intros G k m m' m0 j8 jr HP Hk MEM MU0 WM0 R8 RR MUc WMc MI' TM' ST' BY.
  destruct MEM as (BASE & NLK & GN & FR & SV & SW & ST).
  destruct BASE as (IMG & LA & PL & ER & MI & TM).
  destruct NLK as ((kb & KBL & KB) & NW & ZF & TB).
  destruct GN as (SL & _).
  destruct (g0_place G HP) as (P1 & P2 & P3 & P4).
  pose proof (gname_length (Z.of_nat k) ltac:(lia)) as GL.
  assert (GZ : length (gname_z (Z.of_nat k)) = length (gname (Z.of_nat k)))
    by (unfold gname; rewrite map_length; reflexivity).
  rewrite GZ in MUc.
  set (D := A_G_NAMES + 8 * Z.of_nat k) in *.
  set (L := length (gname (Z.of_nat k))) in *.
  assert (HD : D = 475640 + 8 * Z.of_nat k) by reflexivity.
  assert (K : g0_kp (g0_creg G D (Z.of_nat L + 1)) m m').
  { eapply g0_kp_munch; [exact MUc|]. intros z Hz Ho. cbn [outside] in Ho. unfold g0_creg. lia. }
  assert (HO : forall z, g0_creg G D (Z.of_nat L + 1) z -> g0_out G k z).
  { intros z Hz. unfold g0_creg, g0_out, SLOT_STACK_Z, SLOT_FRAME in *.
    pose proof HP as (Q1 & _ & _ & _ & _). unfold SLOT_STACK_Z in Q1.
    assert (HPZ : n_len G = 0 \/ (n_p0 G + n_len G <= n_S G - 65536 /\
                   (n_p0 G + n_len G <= 474672 \/ 618496 <= n_p0 G)))
      by (destruct (le_pay_cases G HP) as [HE0 | (HN0 & Ha0 & Hb0 & Hc0)];
          [ left; unfold n_len; rewrite HE0; reflexivity
          | right; unfold n_len, SLOT_STACK_Z in *; split; [lia|]; destruct Hc0; lia ]).
    destruct HPZ as [Qz | (Qs & [Qa | Qa])];
      lia. }
  assert (STB : g0_stable G k m').
  { eapply (g0_stable_kp G k _ m); [exact HO | exact K | exact WMc |].
    exact (conj IMG (conj LA (conj PL (conj ER (conj SV (conj SW (conj ZF (conj NW SL)))))))). }
  destruct STB as (IM' & LA' & PL' & ER' & SV' & SW' & ZF' & NW' & SL').
  split; [|split].
  - split; [exact (conj IM' (conj LA' (conj PL' (conj ER' (conj MI' TM'))))) |].
    split; [|split; [|split; [|split; [|split]]]].
    + split; [|split; [exact NW'|split; [exact ZF'|]]].
      * exists kb. split; [exact KBL|]. eapply g0_bytes_kp; [exact K | exact KB |].
        rewrite KBL. intros z Hz Pz. unfold g0_creg, A_G_NL, NK_SIZE, SLOT_STACK_Z, SLOT_FRAME in *. lia.
      * eapply (g0_tabl_kp _ m); [| exact K | | exact TB].
        -- intros z Pz. unfold g0_creg, A_G_NL, NK_SIZE, SLOT_STACK_Z, SLOT_FRAME in *. lia.
        -- unfold g_ps. rewrite map_length. pose proof (kept_le k). lia.
    + split.
      * intros j Hj. destruct (Nat.lt_ge_cases j k) as [Hj'|Hj']; [exact (SL' j Hj')|].
        assert (Ej : j = k) by lia. subst j. fold D.
        destruct R8 as [[R8wf R8b] _]. cbn [cells_bytes cbytes] in R8b. rewrite app_nil_r in R8b.
        cbn [cells_wf cell_wf] in R8wf. destruct R8wf as [J8L _].
        destruct (bytes_at_split m D j8 (L + 1) R8b) as [_ TL].
        rewrite firstn_length in TL. replace (Nat.min (L + 1) (length j8)) with (L + 1)%nat in TL by lia.
        apply (g0_bytes_kp _ m m' _ _ K) in TL.
        2:{ intros z Hz Pz. rewrite skipn_length in Hz. unfold g0_creg, SLOT_STACK_Z, SLOT_FRAME in *. lia. }
        exists (skipn (L + 1) j8).
        replace (gname (Z.of_nat k) ++ zb 0 :: skipn (L + 1) j8)
          with ((gname (Z.of_nat k) ++ [zb 0]) ++ skipn (L + 1) j8) by (rewrite <- app_assoc; reflexivity).
        split.
        -- apply (proj2 (bytes_at_app rsegs m' D _ _)). split.
           ++ rewrite <- g0_pf_bytes. exact BY.
           ++ rewrite app_length. cbn [length]. fold L. exact TL.
        -- rewrite !app_length, skipn_length. cbn [length]. fold L. lia.
      * exists jr. replace (A_G_NAMES + 8 * Z.of_nat (S k)) with (D + 8) by (rewrite HD; unfold A_G_NAMES; lia).
        eapply g0_rw_kp; [exact K | exact WMc | exact RR |].
        intros z Hz Pz. cbn [cells_size csize] in Hz.
        unfold g0_creg, G_NAMES_SIZE, SLOT_STACK_Z, SLOT_FRAME in *. lia.
    + eapply (g0_frame_kp G _ m); [| exact K | exact WMc | exact FR].
      intros z Hz. unfold g0_creg, SLOT_STACK_Z, SLOT_FRAME in *. lia.
    + exact SV'.
    + exact SW'.
    + exact ST'.
  - eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MUc].
    intros x Ho. unfold le_W0 in Ho. cbn [outside] in Ho |- *. destruct Ho as (O1 & O2 & O3 & _).
    unfold A_G_NAMES, G_NAMES_SIZE, A_G_NL, NK_SIZE, SLOT_STACK_Z, SLOT_FRAME in *.
    split; [lia | split; [lia | exact I]].
  - eapply wmono_trans; [exact WM0 | exact WMc].
Qed.

(* ==========================================================================
   7. The instructions after the call: 0x138e4 .. 0x13924
   ========================================================================== *)

Lemma g0_tail : forall (G : lent) (k : nat) (c : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (k < 64)%nat -> 0 <= c <= 63 ->
  u32_at m (A_G_NL + NK_N_IF) c -> wr_at rsegs m A_G_NL NK_SIZE ->
  evt rsegs (fun ms' => exists a0' a1' : word,
     ms' = MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
                (wz (A_G_NAMES + 8 * Z.of_nat (S k))) (wz A_FMT_NL) a0' a1' a2 a3 a4 a5 a6 a7
                (wz (n_len G)) (wz A_G_NL) (wz (Z.of_nat k)) (wz GNL_OFF) (wz (Z.of_nat (S k) + 2))
                (wz 15) (wz 0x42) (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
              F (wz (if Nat.eqb (S k) 64 then L_IF_DONE else L_IF_HEAD)) fc None
              (g0_mem k c m) (seg_rom rsegs))
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
             (wz (A_G_NAMES + 8 * Z.of_nat k)) (wz A_FMT_NL) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (n_len G)) (wz A_G_NL) (wz (Z.of_nat k)) (wz GNL_OFF) (wz (Z.of_nat k + 2))
             (wz 15) (wz 0x42) (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
        F (wz 0x138e4) fc None m (seg_rom rsegs)).
Proof.
  intros G k c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m Hk Hc HN HW.
  assert (HR : ov_read_bytes rsegs m (Z_to_bv 64 (A_G_NL + NK_N_IF)) 4 = Some (le4 (Z_to_bv 64 c)))
    by exact (g0_read4 m _ _ HN).
  unfold u32_at in HN.
  unfold g0_mem, g0_m3, wz, L_IF_DONE, L_IF_HEAD, GNL42, GNL_OFF, A_G_NL, A_G_NAMES,
    NK_N_IF, NK_IF_NAME, NK_IF_INDEX, NK_SIZE in *.
  step. (* andi a0, s4, 0xf *)
  step. (* beq a0, s7 *)
  rewrite (g0_keep_eqb k Hk).
  destruct (keep k) eqn:HK; cbn [negb].
  - (* kept: the three stores *)
    step. (* lw a0, 0x670(s9) *)
    rewrite (g0_sx32 c) by lia.
    step. (* add a1, s3, s5 *)
    step. (* slli a0, a0, 3 *)
    rewrite (g0_shl3 c) by lia.
    step. (* add a0, a1, a0 *)
    assert (HS1 : store_ok rsegs m (Z_to_bv 64 (203648 + (271024 + 8 * c))) 8 = true)
      by exact (wr_at_store_ok rsegs m 203648 271992 (271024 + 8 * c) 8 HW ltac:(lia) ltac:(lia)).
    clear HR.
    step. (* sd s0, 0x2b0(a0) *)
    clear HS1.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HR2 : ov_read_bytes rsegs mm (Z_to_bv 64 (203648 + 271984)) 4 = Some (le4 (Z_to_bv 64 c)))
    end.
    { apply g0_read4. apply bytes_at_write_other; [exact HN | lia | rewrite length_le8; lia |].
      rewrite length_le8, length_le4. lia. }
    step. (* lw a0, 0x670(s9) *)
    clear HR2.
    rewrite (g0_sx32 c) by lia.
    step. (* addi a1, a0, 1 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS2 : store_ok rsegs mm (Z_to_bv 64 (203648 + 271984)) 4 = true)
    end.
    { exact (wr_at_store_ok rsegs _ 203648 271992 271984 4 (wr_at_write rsegs _ _ _ _ _ HW) ltac:(lia) ltac:(lia)). }
    step. (* sw a1, 0x670(s9) *)
    clear HS2.
    step. (* add a1, s3, s5 *)
    step. (* slli a0, a0, 2 *)
    rewrite (g0_shl2 c) by lia.
    step. (* add a0, a1, a0 *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS3 : store_ok rsegs mm (Z_to_bv 64 (203648 + (271664 + 4 * c))) 4 = true)
    end.
    { exact (wr_at_store_ok rsegs _ 203648 271992 (271664 + 4 * c) 4
               (wr_at_write rsegs _ _ _ _ _ (wr_at_write rsegs _ _ _ _ _ HW)) ltac:(lia) ltac:(lia)). }
    step. (* sw s6, 0x530(a0) *)
    clear HS3.
    step. (* addiw s6, s6, 1 *)
    step. (* addi s0, s0, 8 *)
    step. (* bne s6, s8 *)
    rewrite (g0_addiw (Z.of_nat k + 2) 1 (Z.of_nat (S k) + 2)) by lia.
    replace (475640 + 8 * Z.of_nat k + 8) with (475640 + 8 * Z.of_nat (S k)) by lia.
    rewrite (g0_bne k Hk).
    destruct (Nat.eqb (S k) 64); cbn [negb]; apply evt_done; cbv beta; do 2 eexists; reflexivity.
  - (* skipped: k mod 16 = 15 *)
    step. (* addiw s6, s6, 1 *)
    step. (* addi s0, s0, 8 *)
    step. (* bne s6, s8 *)
    rewrite (g0_addiw (Z.of_nat k + 2) 1 (Z.of_nat (S k) + 2)) by lia.
    replace (475640 + 8 * Z.of_nat k + 8) with (475640 + 8 * Z.of_nat (S k)) by lia.
    rewrite (g0_bne k Hk).
    destruct (Nat.eqb (S k) 64); cbn [negb]; apply evt_done; cbv beta; do 2 eexists; reflexivity.
Qed.

(* ==========================================================================
   8. The call, one round, the loop
   ========================================================================== *)

Lemma g0_fmt : forall m, mem_inv rsegs m -> bytes_at rsegs m A_FMT_NL (pf_bytes (FMT_NL ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_NL; lia | |].
  { change (length (pf_bytes (FMT_NL ++ [0]))) with 5%nat. unfold A_FMT_NL. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Section G.
Hypothesis SNP : snprintf_img_contract.

(* snprintf (g_names + 8k, 8, "nl%d", k) at 0x138e0 *)
Lemma g0_call : forall (G : lent) (k : nat)
    (ra gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j8 : list byte),
  le_place G -> (k < 64)%nat -> frm0 fc ->
  rw_cells rsegs m (A_G_NAMES + 8 * Z.of_nat k) [CB 8 j8] ->
  stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G - SLOT_FRAME) ->
  mem_inv rsegs m -> MemNorm.task_mem rsegs m -> guard_m m ->
  evt rsegs (printf_post ra (wz (n_S G - SLOT_FRAME)) gp tp (wz (A_G_NAMES + 8 * Z.of_nat k)) s1
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (n_S G - SLOT_STACK_Z) (A_G_NAMES + 8 * Z.of_nat k)
               (Z.of_nat (length (gname_z (Z.of_nat k)))) (gname_z (Z.of_nat k)) m)
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) gp tp t0 t1 t2 (wz (A_G_NAMES + 8 * Z.of_nat k)) s1
             (wz (A_G_NAMES + 8 * Z.of_nat k)) (wz 8) (wz A_FMT_NL) (wz (Z.of_nat k)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros G k ra gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j8
    HP Hk FC R8 ST MI TM GD.
  destruct GD as [GG (cn & GC)].
  pose proof (gname_length (Z.of_nat k) ltac:(lia)) as GL.
  unfold gname in GL. rewrite map_length in GL.
  assert (HPl := HP). unfold le_place, SLOT_STACK_Z in HPl.
  pose proof (SNP ra (wz (n_S G - SLOT_FRAME)) gp tp t0 t1 t2 (wz (A_G_NAMES + 8 * Z.of_nat k)) s1
                (wz (A_G_NAMES + 8 * Z.of_nat k)) (wz 8) (wz A_FMT_NL) (wz (Z.of_nat k)) a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (n_S G - SLOT_STACK_Z) cn
                FMT_NL [PLit 110; PLit 108; Pd] [AInt (Z.of_nat k)] (gname_z (Z.of_nat k)) j8) as H.
  cbv zeta in H. unfold wz in H.
  assert (U1 : bv_unsigned (Z_to_bv 64 (n_S G - SLOT_FRAME)) = n_S G - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (A_G_NAMES + 8 * Z.of_nat k)) = A_G_NAMES + 8 * Z.of_nat k)
    by (apply unsigned_lit; unfold A_G_NAMES; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 8) = 8) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 A_FMT_NL) = A_FMT_NL) by (apply unsigned_lit; unfold A_FMT_NL; lia).
  assert (U5 : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
  rewrite ?U1, ?U2, ?U3, ?U4 in H.
  rewrite (firstn_all2 (n := Z.to_nat (8 - 1)) (gname_z (Z.of_nat k))) in H
    by (change (Z.to_nat (8 - 1)) with 7%nat; lia).
  apply H; clear H.
  - apply g0_fmt. exact MI.
  - unfold RO_LO, A_FMT_NL. lia.
  - change (length FMT_NL) with 4%nat. unfold RO_END, A_FMT_NL. lia.
  - reflexivity.
  - cbn [pf_args_ok pf_arg_ok]. rewrite U5. split; [|exact I]. split; [lia | reflexivity].
  - apply gname_of_text. lia.
  - exact R8.
  - lia.
  - lia.
  - unfold A_G_NAMES. lia.
  - left. unfold A_G_NAMES, SLOT_STACK_Z. lia.
  - unfold GOT_GUARD, A_G_NAMES. lia.
  - unfold GUARD, A_G_NAMES. lia.
  - exact ST.
  - unfold SNPRINTF_K, SLOT_STACK_Z, SLOT_FRAME. lia.
  - unfold IMG_END, SLOT_STACK_Z. lia.
  - unfold SLOT_FRAME. lia.
  - exact FC.
  - exact MI.
  - exact TM.
  - exact GG.
  - exact GC.
Qed.

(* one round: from the loop head of round k to the loop head of round k + 1, or to 0x13928 *)
Lemma g0_round : forall (G : lent) (k : nat)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte),
  le_place G -> (k < 64)%nat -> frm0 fc ->
  le_if_mem0 G k (g_ps k) (g_ixs k) m -> munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       ms' = MS (mkR ra' (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0' t1' t2'
                     (wz (A_G_NAMES + 8 * Z.of_nat (S k))) (wz A_FMT_NL) a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz (n_len G)) (wz A_G_NL) (wz (Z.of_nat k)) (wz GNL_OFF) (wz (Z.of_nat (S k) + 2))
                     (wz 15) (wz 0x42) (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3' t4' t5' t6')
                F' (wz (if Nat.eqb (S k) 64 then L_IF_DONE else L_IF_HEAD)) fc' None m' (seg_rom rsegs) /\
       frm0 fc' /\ le_if_mem0 G (S k) (g_ps (S k)) (g_ixs (S k)) m' /\
       munch (le_W0 G) m0 m' /\ wmono rsegs m0 m')
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
             (wz (A_G_NAMES + 8 * Z.of_nat k)) (wz A_FMT_NL) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (n_len G)) (wz A_G_NL) s4 (wz GNL_OFF) (wz (Z.of_nat k + 2)) (wz 15) (wz 0x42)
             (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
        F (wz L_IF_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros G k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m m0 HP Hk FC MEM MU WM.
  pose proof MEM as MEM0.
  destruct MEM0 as ((IMG & LA & PL & ER & MI & TM) & NLK & (SL & (jg & RC)) & FR & SV & SW & ST).
  destruct (g0_split m k jg Hk RC) as (j8 & jr & R8 & RR).
  unfold L_IF_HEAD, wz.
  do 6 step.
  rewrite (g0_addiw (Z.of_nat k + 2) (-2) (Z.of_nat k)) by lia.
  eapply evt_cut.
  { eapply g0_call; [exact HP | exact Hk | exact FC | exact R8 | exact ST | exact MI | exact TM |
                     exact (proj2 (proj2 (proj2 IMG)))]. }
  intros ms1 PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                  Ft & fc' & m' & EQ & MUc & WMc & MI' & TM' & FC' & _ & ST' & BY).
  subst ms1.
  assert (U1 : bv_unsigned (wz (n_S G - SLOT_FRAME)) = n_S G - SLOT_FRAME)
    by (unfold wz; apply unsigned_lit; destruct (g0_place G HP) as (P1 & P2 & _); unfold SLOT_FRAME; lia).
  rewrite U1 in MUc, ST'.
  destruct (g0_after_call G k m m' m0 j8 jr HP Hk MEM MU WM R8 RR MUc WMc MI' TM' ST' BY)
    as (MEM1 & MU1 & WM1).
  pose proof MEM1 as MEM2.
  destruct MEM2 as (_ & (_ & NW1 & _ & (_ & NI1 & _)) & _).
  unfold g_ps in NI1. rewrite map_length in NI1.
  rewrite (ret_pc_even 80100) by first [lia | reflexivity].
  eapply evt_mono.
  { eapply (g0_tail G k (Z.of_nat (length (kept k)))); [exact Hk | pose proof (kept_le k); lia | exact NI1 | exact NW1]. }
  intros ms2 (a0'' & a1'' & EQ2). subst ms2.
  destruct (g0_after_stores G k m' m0 HP Hk MEM1 MU1 WM1) as (MEM3 & MU3 & WM3).
  cbv beta. do 16 eexists. exists Ft, fc', (g0_mem k (Z.of_nat (length (kept k))) m').
  split; [reflexivity|]. split; [exact FC'|]. split; [exact MEM3|]. split; [exact MU3 | exact WM3].
Qed.

Lemma le_gloop : forall (G : lent) (k : nat)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte),
  le_place G -> (k < 64)%nat -> frm0 fc ->
  le_if_mem0 G k (g_ps k) (g_ixs k) m ->
  munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       ms' = MS (mkR ra' (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0' t1' t2'
                     (wz (A_G_NAMES + G_NAMES_SIZE)) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42)
                     (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3' t4' t5' t6')
                F' (wz L_IF_DONE) fc' None m' (seg_rom rsegs) /\
       frm0 fc' /\ le_if_mem0 G 64 (g_ps 64) (g_ixs 64) m' /\
       munch (le_W0 G) m0 m' /\ wmono rsegs m0 m')
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
             (wz (A_G_NAMES + 8 * Z.of_nat k)) (wz A_FMT_NL) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (n_len G)) (wz A_G_NL) s4 (wz GNL_OFF) (wz (Z.of_nat k + 2)) (wz 15) (wz 0x42)
             (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
        F (wz L_IF_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros G k. remember (64 - k)%nat as n eqn:Hn. revert k Hn.
  induction n as [|n IH];
    intros k Hn ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc m m0 HP Hk FC MEM MU WM;
    [lia|].
  eapply evt_cut; [eapply g0_round; eassumption|].
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
              F' & fc' & m' & EQ & FC' & MEM' & MU' & WM').
  subst ms'.
  destruct (Nat.eqb_spec (S k) 64) as [E|E].
  - assert (Ek : k = 63%nat) by lia. subst k.
    apply evt_done. cbv beta.
    exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', (wz A_FMT_NL), t3', t4', t5', t6', F', fc', m'.
    split; [reflexivity|]. split; [exact FC'|]. split; [exact MEM'|]. split; [exact MU' | exact WM'].
  - eapply (IH (S k)); [lia | exact HP | lia | exact FC' | exact MEM' | exact MU' | exact WM'].
Qed.

End G.

Print Assumptions le_gloop.
