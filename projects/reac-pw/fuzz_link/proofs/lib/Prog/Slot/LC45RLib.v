(* op_refused (arm 5 of the slot's loop, fuzz_link.c:756-762), plain image: the three straight-line
   walks of its first segment (LC45R0.v), each stated with a continuation K so that its proof context
   holds only what the instructions touch.

   c45r_pb  0x13bf4 with N = 1: `beqz a1` taken, 0x13c30 `mv a0, zero`, on to 0x13c34
   c45r_pa  0x13bf4 with N >= 2: `beqz a1` not taken, s2 = N - 2, a0 = the payload byte at P + 1,
            a2 = P + 2, the cursor cells := (P + 2, N - 2), `j` to 0x13c34
   c45r_mb  0x13c34 - 0x13c70: model_begin (fuzz_link.c:668-675) and the two arguments of
            mark_quietly, up to the `jal` (pc 0x15d88, ra 0x13c74) *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Loads and stores the walks make
   ========================================================================== *)

Lemma c45r_bytes4_range : forall bs : list byte, length bs = 4%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof.
  intros bs L. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as R.
  rewrite length_map, L in R. exact R.
Qed.

(* `lw` of a non-negative int32 *)
Lemma c45r_lw_val : forall bs : list byte, length bs = 4%nat -> bytes_le_to_Z bs < 2 ^ 31 ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L H. pose proof (c45r_bytes4_range bs L) as R.
  rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma c45r_u8_store_ok : forall m A bs k n, u8arr rsegs m A bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> store_ok rsegs m (wa (A + k)) n = true.
Proof. intros m A bs k n [_ Hw] Hk Hn. exact (wr_at_store_ok rsegs m A _ k n Hw Hk Hn). Qed.

Lemma c45r_u8_write : forall m A bs k xs, u8arr rsegs m A bs -> 0 <= k ->
  (Z.to_nat k + length xs <= length bs)%nat ->
  u8arr rsegs (write_to_mem m (wa (A + k)) xs) A (upd_bytes bs (Z.to_nat k) xs).
Proof.
  intros m A bs k xs [Hb Hw] Hk Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma c45r_st : forall m0 m W A bs k xs x,
  u8arr rsegs m A bs -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
  x = wa (A + k) -> 0 <= k -> (Z.to_nat k + length xs <= length bs)%nat ->
  inside W (A + k) (Z.of_nat (length xs)) ->
  u8arr rsegs (write_to_mem m x xs) A (upd_bytes bs (Z.to_nat k) xs) /\ mem_inv rsegs (write_to_mem m x xs) /\
  munch W m0 (write_to_mem m x xs) /\ wmono rsegs m0 (write_to_mem m x xs).
Proof.
  intros m0 m W A bs k xs x U MI MU WM -> Hk Hl Hin.
  pose proof (u8arr_bound rsegs m A bs U) as B.
  split; [|split; [|split]].
  - apply c45r_u8_write; assumption.
  - apply mem_inv_store; [exact MI|]. apply (c45r_u8_store_ok m A bs k (length xs) U); lia.
  - apply munch_write; [exact MU | lia | lia | exact Hin].
  - apply wmono_write. exact WM.
Qed.

Lemma c45r_rw_frame : forall m A cs x a bs, rw_cells rsegs m A cs -> x = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A) ->
  rw_cells rsegs (write_to_mem m x bs) A cs.
Proof. intros; subst; apply rw_cells_frame; assumption. Qed.

Lemma c45r_u8_frame : forall m A bs0 x a bs, u8arr rsegs m A bs0 -> x = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (A + Z.of_nat (length bs0) <= a \/ a + Z.of_nat (length bs) <= A) ->
  u8arr rsegs (write_to_mem m x bs) A bs0.
Proof. intros; subst; apply u8arr_frame; assumption. Qed.

(* the writes of model_begin (0x13c34 - 0x13c64) *)
Definition c45r_Wmb (md : Z) : list ivl :=
  [(md, md + 12); (md + MD_N_REQ, md + MD_N_REQ + 4); (A_G_NL + NK_N_SENT, A_G_NL + NK_N_SENT + 4)].

(* the fake kernel and the model after model_begin *)
Definition c45r_kbs (kbs : list byte) : list byte :=
  upd_bytes kbs (Z.to_nat NK_N_SENT) (le4 (Z_to_bv 64 0)).
Definition c45r_mbs (mbs : list byte) (se sd : Z) : list byte :=
  upd_bytes (upd_bytes (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se)))
                                  (Z.to_nat 4) (le4 (Z_to_bv 64 sd)))
                       (Z.to_nat 8) (le4 (Z_to_bv 64 0)))
            (Z.to_nat MD_N_REQ) (le4 (Z_to_bv 64 0)).

Ltac c45r_side :=
  first [ reflexivity
        | (unfold wa; f_equal; first [reflexivity | lia])
        | (let H := fresh in
           (try match goal with AP : apart _ _ _ _ |- _ => pose proof AP as H; unfold apart in H end);
           cbn [inside c45r_Wmb cells_size csize Nat.add];
           rewrite ?length_le4;
           unfold MD_SIZE, NK_SIZE, NK_N_SENT, MD_N_REQ, A_G_NL, GNL42, GNL40 in *;
           lia) ].

(* a store through the u8arr fact U at offset k: the u8arr, mem_inv, munch and wmono move to the
   new memory, and every other rw_cells / u8arr fact about the old memory is carried across it *)
Ltac ust U k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?x ?xs) _) =>
    lazymatch type of U with
    | u8arr _ m ?A ?bs =>
      lazymatch goal with
      | MI : mem_inv _ m, MU : munch ?W ?m0 m, WM : wmono _ ?m0 m |- _ =>
        let Hst := fresh "Hst" in let HL := fresh "HL" in
        assert (Hst : u8arr rsegs (write_to_mem m x xs) A (upd_bytes bs (Z.to_nat k) xs) /\
                      mem_inv rsegs (write_to_mem m x xs) /\
                      munch W m0 (write_to_mem m x xs) /\ wmono rsegs m0 (write_to_mem m x xs))
          by (apply (c45r_st m0 m W A bs k xs x U MI MU WM); c45r_side);
        assert (HL : length (upd_bytes bs (Z.to_nat k) xs) = length bs)
          by (apply upd_bytes_length; c45r_side);
        let U' := fresh "U" in let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
        destruct Hst as (U' & MI' & MU' & WM');
        clear U MI MU WM;
        repeat match goal with
        | H : rw_cells _ m ?A2 ?cs2 |- _ =>
            let H' := fresh "R" in
            assert (H' : rw_cells rsegs (write_to_mem m x xs) A2 cs2)
              by (apply (c45r_rw_frame m A2 cs2 x (A + k) xs H); c45r_side);
            clear H
        | H : u8arr _ m ?A2 ?bs2 |- _ =>
            let H' := fresh "V" in
            assert (H' : u8arr rsegs (write_to_mem m x xs) A2 bs2)
              by (apply (c45r_u8_frame m A2 bs2 x (A + k) xs H); c45r_side);
            clear H
        | H : store_ok _ m _ _ = true |- _ => clear H
        | H : ov_read_bytes _ m _ _ = _ |- _ => clear H
        end;
        let m' := fresh "m" in
        remember (write_to_mem m x xs) as m' eqn:Em'; clear Em'; try clear m
      end
    end
  end.

(* ==========================================================================
   2. The two arguments of mark_quietly (0x13c38 - 0x13c6c), by computation over the byte w
   ========================================================================== *)

Lemma c45r_bf : forall (P : Z -> bool), forallb (fun k => P (Z.of_nat k)) (seq 0 256) = true ->
  forall w, 0 <= w < 256 -> P w = true.
Proof.
  intros P H w Hw. rewrite forallb_forall in H. specialize (H (Z.to_nat w)).
  rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia.
Qed.

Lemma c45r_odd_mask : forall w, 0 <= w < 256 ->
  (Z.land w 1 + -1) mod 18446744073709551616 = if Z.odd w then 0 else 18446744073709551615.
Proof.
  intros w Hw. apply Z.eqb_eq. revert w Hw.
  apply (c45r_bf (fun w => Z.eqb ((Z.land w 1 + -1) mod 18446744073709551616)
                                 (if Z.odd w then 0 else 18446744073709551615))).
  vm_compute. reflexivity.
Qed.

(* a0 = (w & 1 ? NULL : marks) *)
Lemma c45r_a0_val : forall w mk, 0 <= w < 256 -> 0 <= mk < 2 ^ 64 ->
  Z.land ((Z.land w 1 + -1) mod 18446744073709551616) mk = if Z.odd w then 0 else mk.
Proof.
  intros w mk Hw Hmk. rewrite c45r_odd_mask by exact Hw. destruct (Z.odd w).
  - apply Z.land_0_l.
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
Qed.

(* a1 = (w & 2 ? "" : NULL) *)
Lemma c45r_a1_val : forall w, 0 <= w < 256 ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl w 62))) 63 mod 18446744073709551616)
         (A_EMPTY mod 18446744073709551616) = c45_mq_a1 w.
Proof.
  intros w Hw. apply Z.eqb_eq. revert w Hw.
  apply (c45r_bf (fun w => Z.eqb (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl w 62))) 63
                                            mod 18446744073709551616)
                                         (A_EMPTY mod 18446744073709551616))
                                 (c45_mq_a1 w))).
  vm_compute. reflexivity.
Qed.

(* ==========================================================================
   3. The walks
   ========================================================================== *)

Lemma c45r_eqb_lit : forall z w, 0 <= z < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 w) = (z =? w).
Proof. intros z w Hz Hw. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Section Walks.
Variables (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 t3 t4 t5 t6 gp : word) (F : bvmap 5 word) (fc : bv 32).

(* model_begin and the call of mark_quietly *)
Lemma c45r_mb : forall (SP md mk i w : Z) (j0 kbs mbs : list byte) m (Q : machine_state -> Prop),
  0 <= w < 256 -> 0x960e0 <= SP -> SP + 480 <= 2 ^ 47 -> 4096 <= md -> md + 8856 <= SP ->
  0 <= mk < 2 ^ 64 -> 0 <= i <= 47 -> apart md MD_SIZE A_G_NL NK_SIZE ->
  rw_cells rsegs m SP [CB 8 j0; C8 (Z_to_bv 64 A_ODD); C8 (Z_to_bv 64 (md + MD_MARK)); C8 (Z_to_bv 64 A_EMPTY);
                       C8 (Z_to_bv 64 mk); C8 (Z_to_bv 64 A_G_NAMES); C8 (Z_to_bv 64 A_JT); C8 (Z_to_bv 64 GNL42)] ->
  u8arr rsegs m A_G_NL kbs -> Z.of_nat (length kbs) = NK_SIZE ->
  u8arr rsegs m md mbs -> Z.of_nat (length mbs) = MD_SIZE ->
  0 <= nk_socket_errno kbs < 2 ^ 31 -> 0 <= nk_send_errno kbs < 2 ^ 31 ->
  mem_inv rsegs m ->
  (forall m' (x12 x13 : word), mem_inv rsegs m' -> munch (c45r_Wmb md) m m' -> wmono rsegs m m' ->
     u8arr rsegs m' A_G_NL (c45r_kbs kbs) ->
     u8arr rsegs m' md (c45r_mbs mbs (nk_socket_errno kbs) (nk_send_errno kbs)) ->
     Q (MS (mkR (Z_to_bv 64 C45_MQ_RA) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 md)
                (Z_to_bv 64 GNL40) (Z_to_bv 64 (if Z.odd w then 0 else mk)) (Z_to_bv 64 (c45_mq_a1 w))
                x12 x13 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 46) (Z_to_bv 64 A_JT) (Z_to_bv 64 mk) (Z_to_bv 64 0xab)
                (Z_to_bv 64 4) (Z_to_bv 64 (md + MD_N_REQ)) (Z_to_bv 64 i) t3 t4 t5 t6)
           F (Z_to_bv 64 P_mark_quietly) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 md) (Z_to_bv 64 GNL40)
                       (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 46) (Z_to_bv 64 A_JT) (Z_to_bv 64 mk)
                       (Z_to_bv 64 0xab) (Z_to_bv 64 4) (Z_to_bv 64 (md + MD_N_REQ)) (Z_to_bv 64 i) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c34) fc None m (seg_rom rsegs)).
Proof.
  intros SP md mk i w j0 kbs mbs m Q Hw HS1 HS2 Hmd1 Hmd2 Hmk Hi APg PT KU KL MD ML Hse Hsd MI K.
  pose proof (munch_refl (c45r_Wmb md) m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* lw a1, 0x20c(s1): g_nl.socket_errno *)
  assert (HR1 : ov_read_bytes rsegs m (wa (GNL40 + 524)) 4 = Some (slice kbs NK_SOCKET_ERRNO 4)).
  { replace (GNL40 + 524) with (A_G_NL + NK_SOCKET_ERRNO) by reflexivity.
    apply (bytes_at_read rsegs m A_G_NL kbs NK_SOCKET_ERRNO 4 (proj1 KU)).
    - unfold NK_SOCKET_ERRNO; lia.
    - unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia. }
  assert (L1 : length (slice kbs NK_SOCKET_ERRNO 4) = 4%nat).
  { unfold slice. rewrite length_firstn, length_skipn. unfold NK_SOCKET_ERRNO, NK_SIZE in *. lia. }
  zstep.
  rewrite (c45r_lw_val (slice kbs NK_SOCKET_ERRNO 4) L1 ltac:(exact (proj2 Hse))).
  change (bytes_le_to_Z (slice kbs NK_SOCKET_ERRNO 4)) with (nk_socket_errno kbs).
  (* andi a2, a0, 1; slli a0, a0, 0x3e *)
  zstep. zstep.
  (* sw a1, 0(s0) *)
  assert (HSa : store_ok rsegs m (wa (md + 0)) 4 = true)
    by (apply (c45r_u8_store_ok m md mbs 0 4 MD); unfold MD_SIZE in *; lia).
  zstep.
  ust MD 0.
  (* lw a1, 0x210(s1): g_nl.send_errno *)
  match goal with H : u8arr _ ?mm A_G_NL kbs |- _ =>
    assert (HR2 : ov_read_bytes rsegs mm (wa (GNL40 + 528)) 4 = Some (slice kbs NK_SEND_ERRNO 4));
    [ replace (GNL40 + 528) with (A_G_NL + NK_SEND_ERRNO) by reflexivity;
      apply (bytes_at_read rsegs mm A_G_NL kbs NK_SEND_ERRNO 4 (proj1 H));
      [ unfold NK_SEND_ERRNO; lia | unfold NK_SEND_ERRNO, NK_SIZE in *; lia ] | ] end.
  assert (L2 : length (slice kbs NK_SEND_ERRNO 4) = 4%nat).
  { unfold slice. rewrite length_firstn, length_skipn. unfold NK_SEND_ERRNO, NK_SIZE in *. lia. }
  zstep.
  rewrite (c45r_lw_val (slice kbs NK_SEND_ERRNO 4) L2 ltac:(exact (proj2 Hsd))).
  change (bytes_le_to_Z (slice kbs NK_SEND_ERRNO 4)) with (nk_send_errno kbs).
  (* addi a2, a2, -1; srai a3, a0, 0x3f; and a0, a2, s7 *)
  zstep. zstep. zstep.
  (* sw a1, 4(s0) *)
  match goal with H : u8arr _ ?mm md ?bs |- _ =>
    assert (HSb : store_ok rsegs mm (wa (md + 4)) 4 = true)
      by (apply (c45r_u8_store_ok mm md bs 4 4 H); c45r_side) end.
  zstep.
  match goal with H : u8arr _ _ md _ |- _ => ust H 4 end.
  (* sw zero, 8(s0) *)
  match goal with H : u8arr _ ?mm md ?bs |- _ =>
    assert (HSc : store_ok rsegs mm (wa (md + 8)) 4 = true)
      by (apply (c45r_u8_store_ok mm md bs 8 4 H); c45r_side) end.
  zstep.
  match goal with H : u8arr _ _ md _ |- _ => ust H 8 end.
  (* sw zero, 0(s10) *)
  match goal with H : u8arr _ ?mm md ?bs |- _ =>
    assert (HSd : store_ok rsegs mm (wa (md + MD_N_REQ)) 4 = true)
      by (apply (c45r_u8_store_ok mm md bs MD_N_REQ 4 H); c45r_side) end.
  zstep.
  match goal with H : u8arr _ _ md _ |- _ => ust H MD_N_REQ end.
  (* ld a1, 0x38(sp); sw zero, 0x2a8(a1): g_nl.n_sent *)
  zstep.
  match goal with H : u8arr _ ?mm A_G_NL ?bs |- _ =>
    assert (HSe : store_ok rsegs mm (wa (A_G_NL + NK_N_SENT)) 4 = true)
      by (apply (c45r_u8_store_ok mm A_G_NL bs NK_N_SENT 4 H); c45r_side) end.
  zstep.
  match goal with H : u8arr _ _ A_G_NL _ |- _ => ust H NK_N_SENT end.
  (* ld a1, 0x18(sp); and a1, a3, a1; jal mark_quietly *)
  zstep. zstep. zstep.
  rewrite (c45r_a0_val w mk Hw Hmk), (c45r_a1_val w Hw).
  apply evt_done. apply K; assumption.
Qed.

(* N >= 2: the byte w and the cursor (P + 2, N - 2) *)
Lemma c45r_pa : forall (s0 s1 s5 s6 s7 s8 s9 s10 s11 tp : word) (SP P N : Z) (b : byte) m (Q : machine_state -> Prop),
  0x960e0 <= SP -> SP + 480 <= 2 ^ 47 -> 0 <= P -> P + 2 <= 2 ^ 47 -> 2 <= N < 2 ^ 26 ->
  rw_cells rsegs m (SP + 64) [C8 (Z_to_bv 64 (P + 1)); C8 (Z_to_bv 64 (N - 1))] ->
  ov_read_bytes rsegs m (wa (P + 1)) 1 = Some [b] ->
  mem_inv rsegs m ->
  (forall m' (x12 x18 : word), rw_cells rsegs m' (SP + 64) [C8 (Z_to_bv 64 (P + 2)); C8 (Z_to_bv 64 (N + -2))] ->
     mem_inv rsegs m' -> munch [(SP + 64, SP + 80)] m m' -> wmono rsegs m m' ->
     evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (N - 1))
                          x12 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13c34) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (N - 1)) (Z_to_bv 64 P)
                       a3 a4 a5 a6 a7 (Z_to_bv 64 N) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13bf4) fc None m (seg_rom rsegs)).
Proof.
  intros s0 s1 s5 s6 s7 s8 s9 s10 s11 tp SP P N b m Q HS1 HS2 HP1 HP2 HN CU HRb MI K.
  pose proof (munch_refl [(SP + 64, SP + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  zstep. rewrite c45r_eqb_lit by lia.
  replace (N - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply K; eassumption.
Qed.

(* N = 1: the byte is 0 and the cursor stays (P + 1, 0) *)
Lemma c45r_pb : forall (s0 s1 s2' s5 s6 s7 s8 s9 s10 s11 tp : word) (SP P N : Z) m (Q : machine_state -> Prop),
  N = 1 -> 0 <= P < 2 ^ 47 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (N - 1)) (Z_to_bv 64 P)
                       a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c34) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (N - 1)) (Z_to_bv 64 P)
                       a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13bf4) fc None m (seg_rom rsegs)).
Proof.
  intros s0 s1 s2' s5 s6 s7 s8 s9 s10 s11 tp SP P N m Q HN HP K. subst N.
  zstep. rewrite c45r_eqb_lit by lia.
  match goal with |- context [if ?c then _ else _] =>
    replace c with true by (symmetry; apply Z.eqb_eq; lia) end.
  cbv iota.
  zstep.
  exact K.
Qed.
End Walks.
