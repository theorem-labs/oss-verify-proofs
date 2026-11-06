(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac AEvt.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mo_frame (mo mo' : Model) : Prop :=
  m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\ m_proc mo' = m_proc mo
  /\ m_lim mo' = m_lim mo /\ m_time mo' = m_time mo.  (* [comment removed for export] *)

Lemma mo_frame_refl : forall mo, mo_frame mo mo.
Proof. intros; repeat split; reflexivity. Qed.
Lemma mo_frame_trans : forall a b c, mo_frame a b -> mo_frame b c -> mo_frame a c.
Proof. unfold mo_frame; intros a b c H1 H2; intuition congruence. Qed.
Lemma mo_frame_fs : forall mo mo', mo_frame mo mo' -> m_fs mo' = m_fs mo.
Proof. unfold mo_frame, m_fs; intros mo mo' H; intuition congruence. Qed.
Lemma mo_frame_halted : forall mo mo', mo_frame mo mo' -> m_halted mo' = m_halted mo.
Proof. unfold mo_frame, m_halted; intros mo mo' H; intuition congruence. Qed.

(* [comment removed for export] *)

Definition blk := (Z * Z)%type.     (* [comment removed for export] *)

Definition in_block (LB : list blk) (a : Z) : Prop :=
  exists b, In b LB /\ fst b <= a < fst b + snd b.

Fixpoint lb_remove (A : Z) (LB : list blk) : list blk :=
  match LB with
  | [] => []
  | b :: r => if Z.eqb (fst b) A then r else b :: lb_remove A r
  end.

Fixpoint lb_remove_all (nodes : list Z) (LB : list blk) : list blk :=
  match nodes with [] => LB | a :: r => lb_remove_all r (lb_remove a LB) end.

Lemma In_lb_remove : forall b A LB, In b (lb_remove A LB) -> In b LB.
Proof.
  induction LB as [|x r IH]; cbn; intros H; [exact H|].
  destruct (Z.eqb (fst x) A); [right; exact H|]. destruct H as [H|H]; [left; exact H| right; apply IH, H].
Qed.

Lemma In_lb_remove_all : forall nodes b LB, In b (lb_remove_all nodes LB) -> In b LB.
Proof.
  induction nodes as [|a r IH]; cbn; intros b LB H; [exact H|]. apply In_lb_remove with a. apply IH. exact H.
Qed.

Lemma In_lb_remove_keep : forall A n B LB, In (B, n) LB -> B <> A -> In (B, n) (lb_remove A LB).
Proof.
  induction LB as [|x r IH]; cbn; intros H NE; [exact H|].
  destruct H as [->|H].
  - cbn. destruct (Z.eqb_spec B A); [contradiction|]. left; reflexivity.
  - destruct (Z.eqb (fst x) A); [exact H|]. right. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Record heap_layout := HL {
  hl_malloc : Z; hl_calloc : Z; hl_free : Z;   (* [comment removed for export] *)
  hl_tp : Z;                                   (* [comment removed for export] *)
  hl_stack : Z;                                (* [comment removed for export] *)
  hl_data_lo : Z; hl_data_hi : Z;              (* [comment removed for export] *)
  hl_static : Z -> Prop;                       (* [comment removed for export] *)
  hl_written : Z -> Prop;                      (* [comment removed for export] *)
  hl_img_lo : Z; hl_img_hi : Z;                (* [comment removed for export] *)
  (* [comment removed for export] *)
  hl_ceil : Z;
  hl_ceil_lo : 0x7fff7f800000 <= hl_ceil;     (* [comment removed for export] *)
  hl_ceil_hi : hl_ceil <= 0x7fffff800000      (* [comment removed for export] *)
}.
Existing Class heap_layout.

(* [comment removed for export] *)
Definition alloc_ceiling {L : heap_layout} : Z := hl_ceil L.

Lemma alloc_ceiling_lo {L : heap_layout} : 0x7fff7f800000 <= alloc_ceiling.
Proof. exact (hl_ceil_lo L). Qed.
Lemma alloc_ceiling_hi {L : heap_layout} : alloc_ceiling <= 0x7fffff800000.
Proof. exact (hl_ceil_hi L). Qed.
Lemma alloc_ceiling_bounds {L : heap_layout} : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. split; [exact (hl_ceil_lo L) | exact (hl_ceil_hi L)]. Qed.
(* [comment removed for export] *)
Lemma alloc_ceiling_window {L : heap_layout} :
  sp_window_lo - stack_max_size <= alloc_ceiling <= sp_window_hi - stack_max_size.
Proof. unfold alloc_ceiling, sp_window_lo, sp_window_hi, stack_max_size. pose proof (hl_ceil_lo L). pose proof (hl_ceil_hi L). lia. Qed.
Lemma alloc_ceiling_pos {L : heap_layout} : 4096 < alloc_ceiling.
Proof. pose proof (hl_ceil_lo L). unfold alloc_ceiling. lia. Qed.

Section Iface.
Variable segs : list Segment.
Variable L : heap_layout.

(* [comment removed for export] *)
Definition client_addr (LB : list blk) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (hl_data_lo L <= a < hl_data_hi L /\ ~ hl_static L a) \/ in_block LB a.

Definition client_range (LB : list blk) (SP : Z) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> client_addr LB SP a.

(* [comment removed for export] *)
Definition client_waddr (LB : list blk) (SP TOP : Z) (a : Z) : Prop :=
  (SP <= a < TOP) \/ (hl_data_lo L <= a < hl_data_hi L /\ ~ hl_static L a) \/ in_block LB a.

Definition client_wrange (LB : list blk) (SP TOP : Z) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> client_waddr LB SP TOP a.

(* [comment removed for export] *)
Definition heap_pres (LB : list blk) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> client_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma heap_pres_refl : forall LB SP m, heap_pres LB SP m m.
Proof. intros LB SP m a _ _; auto. Qed.

Definition block_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A).

Fixpoint blocks_apart (LB : list blk) : Prop :=
  match LB with
  | [] => True
  | (A, n) :: r => (forall B k, In (B, k) r -> A + n <= B \/ B + k <= A) /\ blocks_apart r
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : word (* [comment removed for export] *) -> mem -> Model -> Prop) : config -> Prop :=
  fun c' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' mo',
    c' = mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom segs)) mo'
    /\ P a0 m' mo'.

Record heap_iface := HI {
  HST : Type;
  HEAP : HST -> list blk -> mem -> Model -> Prop;
  heap_top : HST -> Z;      (* [comment removed for export] *)

  (* [comment removed for export] *)
  heap_mok : forall h LB m mo, HEAP h LB m mo -> MOK mo;
  heap_blocks : forall h LB m mo, HEAP h LB m mo ->
      Forall (fun b => block_range (fst b) (snd b)) LB /\ blocks_apart LB;
  (* [comment removed for export] *)
  heap_frame : forall h LB m m' mo (SP : Z),
      HEAP h LB m mo -> alloc_ceiling <= SP ->
      (forall a, 0 <= a < 2^64 -> ~ client_waddr LB SP (heap_top h) a -> m' (wa a) = m (wa a)) ->
      wmono segs m m' ->
      HEAP h LB m' mo;

  (* [comment removed for export] *)
  heap_mo : forall h LB m mo mo',
      HEAP h LB m mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = m_halted mo ->
      HEAP h LB m mo';

  (* [comment removed for export] *)
  heap_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB : list blk) (n lo : Z),
      HEAP h LB m mo ->
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
      mem_inv segs m ->
      tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned sp <= heap_top h ->
      a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      aevt segs
        (call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' mo' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
            /\ heap_pres LB (bv_unsigned sp) m m'
            /\ exists h', heap_top h' = heap_top h /\
                         ( (r = Z_to_bv 64 0 /\ HEAP h' LB m' mo')
                         \/ (exists A junk, r = Z_to_bv 64 A /\ block_range A n
                              /\ HEAP h' ((A, n) :: LB) m' mo'
                              /\ rw_cells segs m' A [CB (Z.to_nat n) junk]) )))
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)) mo);

  (* [comment removed for export] *)
  heap_calloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB : list blk) (cnt sz lo : Z),
      HEAP h LB m mo ->
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
      mem_inv segs m ->
      tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned sp <= heap_top h ->
      a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt -> 0 <= sz -> cnt * sz < 2^32 ->
      aevt segs
        (call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' mo' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
            /\ heap_pres LB (bv_unsigned sp) m m'
            /\ exists h', heap_top h' = heap_top h /\
                         ( (r = Z_to_bv 64 0 /\ HEAP h' LB m' mo')
                         \/ (exists A, r = Z_to_bv 64 A /\ block_range A (cnt * sz)
                              /\ HEAP h' ((A, cnt * sz) :: LB) m' mo'
                              /\ rw_cells segs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]) )))
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs)) mo);

  (* [comment removed for export] *)
  heap_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB : list blk) (A n lo : Z),
      HEAP h LB m mo -> In (A, n) LB ->
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
      mem_inv segs m ->
      tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned sp <= heap_top h ->
      a0 = Z_to_bv 64 A ->
      aevt segs
        (call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' mo' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
            /\ heap_pres (lb_remove A LB) (bv_unsigned sp) m m'
            /\ exists h', heap_top h' = heap_top h /\ HEAP h' (lb_remove A LB) m' mo'))
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs)) mo);

  (* [comment removed for export] *)
  heap_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
      a0 = Z_to_bv 64 0 ->
      evt segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom segs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs))
}.

End Iface.

(* [comment removed for export] *)

Section Transport.
Variable segs : list Segment.
Variable L : heap_layout.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_write : forall (HI : heap_iface segs L) h LB m mo (SP a : Z) (bs : list byte),
  HEAP segs L HI h LB m mo -> alloc_ceiling <= SP ->
  client_wrange L LB SP (heap_top segs L HI h) a (Z.of_nat (length bs)) -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  HEAP segs L HI h LB (write_to_mem m (wa a) bs) mo.
Proof.
  intros HI h LB m mo SP a bs HH HSP HR Ha Hl.
  eapply (heap_frame segs L HI); [exact HH| exact HSP| | apply wmono_write; apply wmono_refl].
  intros x Hx Hnc. rewrite (write_to_mem_spec bs m a (wa x)) by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  exfalso. apply Hnc. apply HR. lia.
Qed.

#[using="Type"] Lemma client_range_stack : forall LB SP A n, SP <= A -> client_range L LB SP A n.
Proof. intros LB SP A n H a Ha. left. lia. Qed.

#[using="Type"] Lemma client_wrange_stack : forall LB SP TOP A n, SP <= A -> A + n <= TOP -> client_wrange L LB SP TOP A n.
Proof. intros LB SP TOP A n H1 H2 a Ha. left. lia. Qed.

#[using="Type"] Lemma client_wrange_block : forall LB SP TOP A n B k,
  In (B, k) LB -> B <= A -> A + n <= B + k -> client_wrange L LB SP TOP A n.
Proof. intros LB SP TOP A n B k HB H1 H2 a Ha. right; right. exists (B, k). split; [exact HB| cbn; lia]. Qed.

#[using="Type"] Lemma client_range_block : forall LB SP A n B k,
  In (B, k) LB -> B <= A -> A + n <= B + k -> client_range L LB SP A n.
Proof. intros LB SP A n B k HB H1 H2 a Ha. right; right. exists (B, k). split; [exact HB| cbn; lia]. Qed.

#[using="Type"] Lemma heap_pres_bytes_at : forall LB SP m m' A bs,
  heap_pres segs L LB SP m m' -> bytes_at segs m A bs -> client_range L LB SP A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma heap_pres_wr_at : forall LB SP m m' A n,
  heap_pres segs L LB SP m m' -> wr_at segs m A n -> client_range L LB SP A n -> wr_at segs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma heap_pres_rw_cells : forall LB SP m m' A cs,
  heap_pres segs L LB SP m m' -> rw_cells segs m A cs -> client_range L LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply heap_pres_wr_at; eauto.
Qed.

#[using="Type"] Lemma heap_pres_ro_cells : forall LB SP m m' A cs,
  heap_pres segs L LB SP m m' -> ro_cells segs m A cs -> client_range L LB SP A (Z.of_nat (cells_size cs)) ->
  ro_cells segs m' A cs.
Proof.
  intros LB SP m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
  eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

#[using="Type"] Lemma heap_pres_u8arr : forall LB SP m m' A xs,
  heap_pres segs L LB SP m m' -> u8arr segs m A xs -> client_range L LB SP A (Z.of_nat (length xs)) ->
  u8arr segs m' A xs.
Proof.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells segs m' A (length xs)).
  eapply heap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

#[using="Type"] Lemma heap_pres_trans_sub : forall LB1 LB2 SP m m1 m2,
  heap_pres segs L LB1 SP m m1 -> heap_pres segs L LB2 SP m1 m2 ->
  (forall b, In b LB2 -> In b LB1) -> heap_pres segs L LB2 SP m m2.
Proof.
  intros LB1 LB2 SP m m1 m2 H1 H2 HS a Ha Hc.
  assert (Hc1 : client_addr L LB1 SP a).
  { destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H| right; right].
    exists b. split; [apply HS, Hb| exact Hr]. }
  destruct (H1 a Ha Hc1) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence| auto].
Qed.

#[using="Type"] Lemma heap_pres_sub : forall LB1 LB2 SP m m1,
  heap_pres segs L LB1 SP m m1 -> (forall b, In b LB2 -> In b LB1) -> heap_pres segs L LB2 SP m m1.
Proof.
  intros LB1 LB2 SP m m1 H1 HS a Ha Hc. apply H1; [exact Ha|].
  destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma heap_pres_stk : forall LB SP m m' lo hi,
  heap_pres segs L LB SP m m' -> stk segs m lo hi -> SP <= lo -> stk segs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

End Transport.
