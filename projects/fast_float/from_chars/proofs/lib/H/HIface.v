(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
Import ListNotations.

Module Hstr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Section Str.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_rebyte : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf'|]|].
  - rewrite Heq. exact Hb.
  - rewrite <- (cells_bytes_length cs' Hwf'), Heq, (cells_bytes_length cs Hwf). exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd_byte0_C8 : forall m A w cs,
  rw_cells segs m A (C8 w :: cs) -> ov_read_bytes segs m (wa A) 1 = Some [Z_to_bv 8 (bv_unsigned w)].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A w cs [[_ Hb] _].
  eapply (u8ro_read segs m A _ 0); [exact Hb | reflexivity | lia | f_equal; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_sub : forall m A bs k n,
  bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs k n (Ha & Hl & H) Hkn. split; [lia|]. split.
  - rewrite firstn_length_le by (rewrite skipn_length; lia). lia.
  - intros i Hi. rewrite firstn_length_le in Hi by (rewrite skipn_length; lia).
    rewrite nth_error_firstn. rewrite nth_error_skipn.
    destruct (Nat.ltb_spec i n); [|lia].
    rewrite <- Z.add_assoc, <- Nat2Z.inj_add. apply H. lia.
Qed.

#[using="Type"] Lemma cells_bytes_of_rw : forall m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs [[_ Hb] _]. exact Hb. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fresh_short : forall m o,
  rw_cells segs m o [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells segs m o [C1 (Z_to_bv 8 0)] /\ u8arr segs m (o + 1) (repeat (Z_to_bv 8 0) 23).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m o H.
  assert (H2 : rw_cells segs m o ([C1 (Z_to_bv 8 0)] ++ [CB 23 (repeat (Z_to_bv 8 0) 23)])).
  { eapply rw_cells_rebyte; [exact H | cbn; repeat split; reflexivity | reflexivity]. }
  apply rw_cells_app in H2. destruct H2 as [H1 H2]. split; [exact H1|].
  apply (u8arr_of_rw_cells segs m _ 23). exact H2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma long_split : forall m o w0 w1 w2,
  rw_cells segs m o [C8 w0; C8 w1; C8 w2] ->
  rw_cells segs m o [C1 (Z_to_bv 8 (bv_unsigned w0))] /\ u8arr segs m (o + 1) (skipn 1 (le8 w0) ++ le8 w1 ++ le8 w2).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m o w0 w1 w2 H.
  assert (H2 : rw_cells segs m o ([C1 (Z_to_bv 8 (bv_unsigned w0))] ++ [CB 23 (skipn 1 (le8 w0) ++ le8 w1 ++ le8 w2)])).
  { eapply rw_cells_rebyte; [exact H | | reflexivity].
    cbn [cells_wf cell_wf]. split; [reflexivity|]. split; [|exact I]. unfold le8, word_to_le_bytes. cbn. reflexivity. }
  apply rw_cells_app in H2. destruct H2 as [H1 H2]. split; [exact H1|].
  apply (u8arr_of_rw_cells segs m _ 23). exact H2.
Qed.

End Str.
End Hstr.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition md_ok (md : Model) : Prop := m_halted md = None /\ m_vm_lazy md = [].

Definition Qrz (segs : list Segment) (cfg : SpuriousCfg) (md : Model) (K : TSet) : machine_state -> Prop :=
  fun s => forall s', ms_eqv s s' -> realizes_cfg segs cfg (mkCfg s' md) K.

Lemma catsim_isteps : forall segs a b, CatSim.msteps segs a b -> isteps segs a b.
Proof.
  intros segs a b H. induction H as [ms | ms ms1 ms2 Hsvc Hst Hrest IH].
  - apply ist_refl.
  - eapply ist_step; eassumption.
Qed.

Lemma rz_of_evt : forall segs cfg md K (fx : FPState) regs pc mem rom,
  md_ok md ->
  evt segs (Qrz segs cfg md K) (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem rom) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc mem rom) md) K.
Proof.
  intros segs cfg md K fx regs pc mem rom [Hh Hl] Hevt.
  destruct (evt_bridge segs fx regs pc mem rom _ Hevt) as (s & RUN & s0 & HQ & EQV).
  eapply rzc_isteps; [exact Hh | exact Hl | apply catsim_isteps; exact RUN | ].
  apply HQ. exact EQV.
Qed.

(* [comment removed for export] *)
Lemma evt_exit_rz : forall segs cfg md K R F pc fc m rom,
  (forall (fx : FPState) regs, (forall r, getr regs r = getr R r) -> @fp_csr fx = fc ->
     realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K) ->
  evt segs (Qrz segs cfg md K) (MS R F pc fc None m rom).
Proof.
  intros segs cfg md K R F pc fc m rom H. apply evt_done. intros s' EQV.
  destruct (ms_eqv_MS_inv R F pc fc m rom s' EQV) as (fx' & regs' & -> & HR & HF & Hfc).
  apply H; assumption.
Qed.

Lemma ret_pc_even_w : forall w : word, (bv_unsigned w mod 2 = 0)%Z -> ret_pc w = w.
Proof.
  intros w H. rewrite <- (Z_to_bv_bv_unsigned w). apply ret_pc_even; [apply bv_unsigned_in_range | exact H].
Qed.

(* [comment removed for export] *)
Definition callee_saved (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\
  getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\
  getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\
  getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
  getr regs' 27 = getr regs 27.

Lemma callee_saved_refl : forall regs, callee_saved regs regs.
Proof. intros regs. repeat split. Qed.

Lemma callee_saved_trans : forall r1 r2 r3, callee_saved r1 r2 -> callee_saved r2 r3 -> callee_saved r1 r3.
Proof.
  intros r1 r2 r3 (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10&A11&A12&A13&A14&A15) (B1&B2&B3&B4&B5&B6&B7&B8&B9&B10&B11&B12&B13&B14&B15).
  repeat split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
Variable segs : list Segment.

#[using="Type"] Lemma wr_at_transport_munch : forall W m m' A n,
  wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A n (Ha & Hn & H) MU Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold wview. rewrite MU.
  - apply H, Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rw_cells_transport_munch : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A cs [[Hwf Hb] Hw] MU Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport_munch; eauto.
Qed.

#[using="Type"] Lemma u8arr_transport_munch : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A bs [Hb Hw] MU Hd. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transport_munch; eauto.
Qed.

#[using="Type"] Lemma stk_transport_munch : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' lo hi (H1 & H2 & H) MU Hd. split; [lia|]. split; [lia|].
  intros a Ha. assert (Ho : outside W (bv_unsigned (wa a))).
  { eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia. }
  unfold wview, mrd. rewrite (MU _ Ho). apply H, Ha.
Qed.

End Transport.

(* [comment removed for export] *)
Ltac transport_cps segs m m' MU :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping (not disjoint from callee footprint):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport_munch segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping (not disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport_munch segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping (not disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_munch segs W m m' loq hiq) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | cbn [disjoint_from]; slia ]
            | idtac "note: dropping (not disjoint from callee footprint):" H; clear H ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition U (md : Model) : Z :=
  (vm_backing_used md + 4096 * Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))))%Z.
Definition UBOUND : Z := (2 ^ 30)%Z.
Definition MCHARGE (n : Z) : Z := (n + 2 ^ 21)%Z.
Definition FUZZ_CHARGE : Z := (6 * MCHARGE 136)%Z.

Definition blocks_add (B B' : list (Z * Z)) (x : Z * Z) : Prop := forall y, In y B' <-> y = x \/ In y B.
Definition blocks_del (B B' : list (Z * Z)) (x : Z * Z) : Prop := forall y, In y B' <-> In y B /\ y <> x.
Definition blocks_same (B B' : list (Z * Z)) : Prop := forall y, In y B' <-> In y B.

Section HeapIface.
  Variable segs : list Segment.
  Variable cfg : SpuriousCfg.
  (* [comment removed for export] *)
  Variable HS : Type.
  Variable Heap : HS -> (word -> option byte) -> Model -> Prop.
  Variable blocks : HS -> list (Z * Z).              (* [comment removed for export] *)
  Variable owned : HS -> list ivl.                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables GP TP : word.
  (* [comment removed for export] *)
  Variables IMG_LO IMG_END HTOP : Z.
  Variable STATIC : list ivl.
  (* [comment removed for export] *)
  Variable KEEP : list ivl.

  Definition sp_of (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 2).

  (* [comment removed for export] *)
  Definition malloc_contract (PCM NEED : Z) : Prop :=
    forall (fx : FPState) regs m md hs (n : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + MCHARGE n <= UBOUND)%Z ->
      getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 2^26)%Z ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
      getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - NEED)%Z ->
      stk segs m (sp_of regs - NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs' (p : Z),
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
         (forall a, ~ outside KEEP a -> m' (wa a) = m (wa a)) ->
         getr regs' 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
         blocks_add (blocks hs) (blocks hs') (p, n) -> ~ In (p, n) (blocks hs) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(p, p + n); (sp_of regs - NEED, sp_of regs)]%Z) m m' ->
         stk segs m' (sp_of regs - NEED) (sp_of regs) ->
         realizes_cfg segs cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom segs)) md') K) ->
      realizes_cfg segs cfg (mkCfg (@mkst fx regs (Z_to_bv 64 PCM) m (seg_rom segs)) md) K.

  (* [comment removed for export] *)
  Definition free_contract (PCF NEED : Z) : Prop :=
    forall (fx : FPState) regs m md hs (p k : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md ->
      getr regs 10 = Z_to_bv 64 p -> (p = 0%Z \/ In (p, k) (blocks hs)) ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
      getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - NEED)%Z ->
      stk segs m (sp_of regs - NEED) (sp_of regs) ->
      (forall (fx' : FPState) regs' m' md' hs',
         @fp_csr fx' = @fp_csr fx -> Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md)%Z ->
         (forall a, ~ outside KEEP a -> m' (wa a) = m (wa a)) ->
         (if (p =? 0)%Z then blocks_same (blocks hs) (blocks hs') else blocks_del (blocks hs) (blocks hs') (p, k)) ->
         callee_saved regs regs' ->
         munch (owned hs ++ owned hs' ++ [(p, p + k); (sp_of regs - NEED, sp_of regs)]%Z) m m' ->
         stk segs m' (sp_of regs - NEED) (sp_of regs) ->
         realizes_cfg segs cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom segs)) md') K) ->
      realizes_cfg segs cfg (mkCfg (@mkst fx regs (Z_to_bv 64 PCF) m (seg_rom segs)) md) K.

  (* [comment removed for export] *)
  Definition heap_frame : Prop :=
    forall hs m m' md (W : list ivl), Heap hs m md -> munch W m m' -> wmono segs m m' ->
      (forall x : Z, ~ outside W x -> outside (owned hs) x) -> Heap hs m' md.

  (* [comment removed for export] *)
  Definition heap_blocks_ok : Prop :=
    forall hs m md, Heap hs m md ->
      (forall p n, In (p, n) (blocks hs) ->
         (1 <= n)%Z /\ ((16 <= p /\ p + n <= IMG_LO) \/ (IMG_END <= p /\ p + n <= HTOP))%Z /\
         stk segs m p (p + n) /\ disjoint_from (owned hs) p n /\
         (forall q k, In (q, k) (blocks hs) -> (q, k) <> (p, n) -> (p + n <= q \/ q + k <= p)%Z)) /\
      (forall x : Z, ~ outside (owned hs) x ->
         (0 <= x < HTOP)%Z /\ (~ outside STATIC x \/ (x < IMG_LO)%Z \/ (IMG_END <= x)%Z)).

  (* [comment removed for export] *)
  Definition fuzz_contract (PCZ NEEDZ : Z) (RO : list (Z * Z)) : Prop :=
    forall (fx : FPState) regs m md hs (size : Z) (ret : word) (K : TSet),
      Heap hs m md -> md_ok md -> (U md + FUZZ_CHARGE <= UBOUND)%Z ->
      getr regs 11 = Z_to_bv 64 size -> (0 <= size < 2^26)%Z ->
      (size = 0%Z \/ In (bv_unsigned (getr regs 10), size) (blocks hs)) ->
      getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
      getr regs 3 = GP -> getr regs 4 = TP ->
      (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - NEEDZ)%Z ->
      stk segs m (sp_of regs - NEEDZ) (sp_of regs) ->
      frm0 (@fp_csr fx) ->
      Forall (fun r => pristine m (fst r) (snd r)) RO ->
      (forall (fx' : FPState) regs' m' md' hs',
         Heap hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + FUZZ_CHARGE)%Z ->
         (forall a, ~ outside KEEP a -> m' (wa a) = m (wa a)) ->
         getr regs' 10 = Z_to_bv 64 0 -> callee_saved regs regs' -> frm0 (@fp_csr fx') ->
         blocks_same (blocks hs) (blocks hs') ->
         munch (STATIC ++ [(0, IMG_LO); (IMG_END, HTOP); (sp_of regs - NEEDZ, sp_of regs)]%Z) m m' ->
         (forall p n, In (p, n) (blocks hs) -> forall a, (p <= a < p + n)%Z -> m' (wa a) = m (wa a)) ->
         stk segs m' (sp_of regs - NEEDZ) (sp_of regs) ->
         realizes_cfg segs cfg (mkCfg (@mkst fx' regs' ret m' (seg_rom segs)) md') K) ->
      realizes_cfg segs cfg (mkCfg (@mkst fx regs (Z_to_bv 64 PCZ) m (seg_rom segs)) md) K.
End HeapIface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record heap_iface : Type := HeapIface {
  hi_HS : Type;
  hi_Heap : hi_HS -> (word -> option byte) -> Model -> Prop;
  hi_blocks : hi_HS -> list (Z * Z);
  hi_owned : hi_HS -> list ivl }.

(* [comment removed for export] *)
Definition heap_ok (segs : list Segment) (cfg : SpuriousCfg) (HI : heap_iface) (GP TP : word)
    (IMG_LO IMG_END HTOP : Z) (STATIC KEEP : list ivl) (PCM MNEED PCF FNEED : Z) : Prop :=
  ((IMG_LO <= IMG_END <= HTOP)%Z /\ (forall x, ~ outside STATIC x -> (IMG_LO <= x < IMG_END)%Z)) /\
  malloc_contract segs cfg (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) GP TP HTOP KEEP PCM MNEED /\
  free_contract segs cfg (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) GP TP HTOP KEEP PCF FNEED /\
  heap_frame segs (hi_HS HI) (hi_Heap HI) (hi_owned HI) /\
  heap_blocks_ok segs (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (hi_owned HI) IMG_LO IMG_END HTOP STATIC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (m m' : word -> option byte) (a k : Z) : Prop :=
  forall i, (0 <= i < k)%Z -> m' (wa (a + i)) = m (wa (a + i)).

Lemma outside_app : forall (A B : list ivl) x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x; cbn; [tauto|].
  rewrite IH. tauto.
Qed.

(* [comment removed for export] *)
Lemma munch_cps_trans : forall (O1 O2 W1 L W : list ivl) m m1 m2,
  munch W1 m m1 -> munch (O1 ++ O2 ++ L) m1 m2 ->
  (forall x, outside W x -> outside W1 x) ->
  (forall x, outside W x -> outside O1 x /\ outside O2 x /\ outside L x) ->
  munch W m m2.
Proof.
  intros O1 O2 W1 L W m m1 m2 M1 M2 S1 S2 x Hx.
  rewrite (M2 x); [apply M1, S1, Hx|]. destruct (S2 _ Hx) as (A & B & C).
  apply outside_app. split; [exact A|]. apply outside_app. split; assumption.
Qed.

Lemma outside_dec : forall (W : list ivl) x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [A|A]; [left; split; [lia|exact A] | right; intros [_ B]; exact (A B)].
  - destruct (IH x) as [A|A]; [left; split; [lia|exact A] | right; intros [_ B]; exact (A B)].
Qed.

Section Agree.
Variable segs : list Segment.

#[using="Type"] Lemma bytes_at_agree : forall m m' a bs, bytes_at segs m a bs -> agree_on m m' a (Z.of_nat (length bs)) -> bytes_at segs m' a bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' a bs (Ha & Hl & H) AG. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite AG by lia. apply H, Hi.
Qed.

#[using="Type"] Lemma wr_at_agree : forall m m' a n, wr_at segs m a n -> agree_on m m' a n -> wr_at segs m' a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' a n (Ha & Hn & H) AG. split; [lia|]. split; [lia|].
  intros i Hi. unfold wview. rewrite AG by lia. apply H, Hi.
Qed.

#[using="Type"] Lemma rw_cells_agree : forall m m' A cs, rw_cells segs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' A cs [[Hwf Hb] Hw] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact Hb|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

#[using="Type"] Lemma u8arr_agree : forall m m' A bs, u8arr segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m m' A bs [Hb Hw] AG. split; [eapply bytes_at_agree | eapply wr_at_agree]; eauto. Qed.

#[using="Type"] Lemma stk_agree : forall m m' lo hi, stk segs m lo hi -> agree_on m m' lo (hi - lo) -> stk segs m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' lo hi (H1 & H2 & H) AG. split; [lia|]. split; [lia|].
  intros a Ha. replace a with (lo + (a - lo))%Z by lia.
  unfold wview, mrd. rewrite AG by lia. apply H. lia.
Qed.

#[using="Type"] Lemma pristine_agree : forall m m' lo hi, pristine m lo hi -> agree_on m m' lo (hi - lo) -> pristine m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' lo hi (Hlo & Hhi & Hp) AG. split; [lia|]. split; [lia|].
  intros i Hi. replace i with (lo + (i - lo))%Z by lia. rewrite AG by lia. apply Hp. lia.
Qed.

#[using="Type"] Lemma agree_on_of_munch : forall W m m' a k, munch W m m' -> disjoint_from W a k -> (0 <= a)%Z -> (a + k <= 2^64)%Z ->
  agree_on m m' a k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' a k MU Hd Ha Hk i Hi. apply MU. eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma agree_on_sub : forall m m' a k a' k', agree_on m m' a k -> (a <= a')%Z -> (a' + k' <= a + k)%Z -> agree_on m m' a' k'.
Proof. LiaFast.lf_pins LiaFast.u0. intros m m' a k a' k' AG H1 H2 i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply AG. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cps_agree : forall HS (Heap : HS -> (word -> option byte) -> Model -> Prop) blocks owned IMG_LO IMG_END HTOP STATIC
    hs hs' m m' md md' (L : list ivl) a k,
  heap_blocks_ok segs HS Heap blocks owned IMG_LO IMG_END HTOP STATIC ->
  Heap hs m md -> Heap hs' m' md' ->
  munch (owned hs ++ owned hs' ++ L) m m' ->
  disjoint_from L a k -> (0 <= a)%Z -> (a + k <= 2^64)%Z ->
  ((HTOP <= a)%Z \/ exists p n, In (p, n) (blocks hs) /\ In (p, n) (blocks hs') /\ (p <= a)%Z /\ (a + k <= p + n)%Z) ->
  agree_on m m' a k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HS Heap blocks owned IMG_LO IMG_END HTOP STATIC hs hs' m m' md md' L a k BOK H1 H2 MU HL Ha Hk WHERE i Hi.
  apply MU. rewrite wa_unsigned by lia.
  destruct (BOK _ _ _ H1) as [B1 O1]. destruct (BOK _ _ _ H2) as [B2 O2].
  assert (HLo : outside L (a + i)) by (eapply disjoint_outside; [exact HL | lia]).
  assert (Ho : forall o : list ivl, (forall x : Z, ~ outside o x -> (0 <= x < HTOP)%Z) ->
                 (forall p n, (exists q : Z * Z, q = (p, n)) -> (p <= a)%Z -> (a + k <= p + n)%Z -> disjoint_from o p n -> True) ->
                 True) by (intros; exact I).
  clear Ho.
  assert (OUT : forall o : list ivl, (forall x : Z, ~ outside o x -> (0 <= x < HTOP)%Z) ->
                  (forall p n, In (p, n) (blocks hs) -> In (p, n) (blocks hs') -> (p <= a)%Z -> (a + k <= p + n)%Z ->
                     disjoint_from o p n) ->
                  outside o (a + i)).
  { intros o Hbelow Hblk.
    destruct WHERE as [Hst | (p & n & Hp1 & Hp2 & Hpa & Hpk)].
    - destruct (outside_dec o (a + i)) as [Hc|Hc]; [exact Hc|].
      specialize (Hbelow _ Hc). lia.
    - eapply disjoint_outside; [apply (Hblk p n Hp1 Hp2 Hpa Hpk) | lia]. }
  assert (Happ : forall o1 o2, outside o1 (a + i) -> outside o2 (a + i) -> outside (o1 ++ o2) (a + i)).
  { induction o1 as [|[lo hi] o1 IH]; cbn; intros o2 A1 A2; [exact A2|]. destruct A1 as [A1a A1b]. split; [exact A1a|]. apply IH; assumption. }
  apply Happ; [|apply Happ; [|exact HLo]].
  - apply OUT; [intros x Hx; exact (proj1 (O1 x Hx))|]. intros p n Hp1 _ _ _. exact (proj1 (proj2 (proj2 (proj2 (B1 p n Hp1))))).
  - apply OUT; [intros x Hx; exact (proj1 (O2 x Hx))|]. intros p n _ Hp2 _ _. exact (proj1 (proj2 (proj2 (proj2 (B2 p n Hp2))))).
Qed.

#[using="Type"] Lemma owned_out : forall HS (Heap : HS -> (word -> option byte) -> Model -> Prop) blocks owned IMG_LO IMG_END HTOP STATIC hs m md x,
  heap_blocks_ok segs HS Heap blocks owned IMG_LO IMG_END HTOP STATIC -> Heap hs m md ->
  outside STATIC x -> ~ (0 <= x < IMG_LO)%Z -> ~ (IMG_END <= x < HTOP)%Z -> outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HS Heap blocks owned IMG_LO IMG_END HTOP STATIC hs m md x BOK H Hs H1 H2.
  destruct (BOK _ _ _ H) as [_ O]. destruct (outside_dec (owned hs) x) as [A|A]; [exact A|].
  exfalso. destruct (O _ A) as (B1 & [B2 | [B2 | B2]]); [exact (B2 Hs) | lia | lia].
Qed.

(* [comment removed for export] *)
Definition keep_eq (KEEP : list ivl) (m m' : word -> option byte) : Prop := forall a, ~ outside KEEP a -> m' (wa a) = m (wa a).

#[using="Type"] Lemma keep_refl : forall KEEP m, keep_eq KEEP m m.
Proof. LiaFast.lf_pins LiaFast.u0. intros KEEP m a _. reflexivity. Qed.

#[using="Type"] Lemma keep_trans : forall KEEP m1 m2 m3, keep_eq KEEP m1 m2 -> keep_eq KEEP m2 m3 -> keep_eq KEEP m1 m3.
Proof. LiaFast.lf_pins LiaFast.u0. intros KEEP m1 m2 m3 A B a Ha. rewrite (B a Ha). exact (A a Ha). Qed.

#[using="Type"] Lemma not_outside_cons : forall lo hi (W : list ivl) a, ~ outside ((lo, hi) :: W) a -> (lo <= a < hi)%Z \/ ~ outside W a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros lo hi W a H. destruct (Z_le_gt_dec lo a) as [H1|H1]; [destruct (Z_lt_ge_dec a hi) as [H2|H2]|].
  - left. lia.
  - right. intros Ho. apply H. cbn. split; [lia | exact Ho].
  - right. intros Ho. apply H. cbn. split; [lia | exact Ho].
Qed.

#[using="Type"] Lemma not_outside_2 : forall l1 h1 l2 h2 a, ~ outside [(l1, h1); (l2, h2)] a -> (l1 <= a < h1 \/ l2 <= a < h2)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l1 h1 l2 h2 a H. destruct (not_outside_cons _ _ _ _ H) as [A|A]; [left; exact A|].
  destruct (not_outside_cons _ _ _ _ A) as [B|B]; [right; exact B|]. exfalso. apply B. exact I.
Qed.

#[using="Type"] Lemma not_outside_4 : forall l1 h1 l2 h2 l3 h3 l4 h4 a, ~ outside [(l1, h1); (l2, h2); (l3, h3); (l4, h4)] a ->
  (l1 <= a < h1 \/ l2 <= a < h2 \/ l3 <= a < h3 \/ l4 <= a < h4)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l1 h1 l2 h2 l3 h3 l4 h4 a H. destruct (not_outside_cons _ _ _ _ H) as [A|A]; [left; exact A|].
  destruct (not_outside_cons _ _ _ _ A) as [B|B]; [right; left; exact B|].
  destruct (not_outside_cons _ _ _ _ B) as [C|C]; [right; right; left; exact C|].
  destruct (not_outside_cons _ _ _ _ C) as [E|E]; [right; right; right; exact E|]. exfalso. apply E. exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ro_munch_keep : forall (KEEP W : list ivl) m m' (RO : list (Z * Z)),
  Forall (fun r => pristine m (fst r) (snd r)) RO -> munch W m m' -> keep_eq KEEP m m' ->
  (forall r x, In r RO -> (fst r <= x < snd r)%Z -> outside W x \/ ~ outside KEEP x) ->
  Forall (fun r => pristine m' (fst r) (snd r)) RO.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros KEEP W m m' RO H MU KP HO. induction H as [|r RO Hr H IH]; constructor.
  - destruct Hr as (A & B & C). split; [exact A|]. split; [exact B|].
    intros i Hi. destruct (HO r i ltac:(left; reflexivity) Hi) as [Ho|Hk].
    + rewrite MU; [apply C, Hi|]. rewrite wa_unsigned by lia. exact Ho.
    + rewrite (KP i Hk). apply C, Hi.
  - apply IH. intros r' x Hin Hx. apply (HO r'); [right; exact Hin | exact Hx].
Qed.

#[using="Type"] Lemma keep_munch : forall (KEEP W : list ivl) m m',
  (forall a, ~ outside KEEP a -> (0 <= a < 2^64)%Z /\ outside W a) -> munch W m m' -> keep_eq KEEP m m'.
Proof. LiaFast.lf_pins LiaFast.u0. intros KEEP W m m' H MU a Ha. destruct (H a Ha) as [Ra Wa]. apply MU. rewrite wa_unsigned by lia. exact Wa. Qed.

#[using="Type"] Lemma agree_on_trans : forall m1 m2 m3 a k, agree_on m1 m2 a k -> agree_on m2 m3 a k -> agree_on m1 m3 a k.
Proof. LiaFast.lf_pins LiaFast.u0. intros m1 m2 m3 a k A1 A2 i Hi. rewrite A2 by exact Hi. apply A1, Hi. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_coarsen : forall HS (Heap : HS -> (word -> option byte) -> Model -> Prop) blocks owned IMG_LO IMG_END HTOP STATIC
    hs hs' m m' md md' (L L' : list ivl),
  heap_blocks_ok segs HS Heap blocks owned IMG_LO IMG_END HTOP STATIC ->
  Heap hs m md -> Heap hs' m' md' ->
  munch (owned hs ++ owned hs' ++ L) m m' ->
  (forall x, outside ([(0, IMG_LO); (IMG_END, HTOP)] ++ L')%Z x -> outside L x) ->
  munch (STATIC ++ [(0, IMG_LO); (IMG_END, HTOP)] ++ L')%Z m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HS Heap blocks owned IMG_LO IMG_END HTOP STATIC hs hs' m m' md md' L L' BOK H1 H2 MU HL x Hx.
  apply MU. rewrite outside_app in Hx. destruct Hx as [Hs Hx].
  destruct (BOK _ _ _ H1) as [_ O1]. destruct (BOK _ _ _ H2) as [_ O2].
  assert (Hr : ~ (0 <= bv_unsigned x < IMG_LO)%Z /\ ~ (IMG_END <= bv_unsigned x < HTOP)%Z) by (cbn [outside app] in Hx; tauto).
  assert (Ho : forall o : list ivl, (forall z, ~ outside o z -> (0 <= z < HTOP)%Z /\ (~ outside STATIC z \/ (z < IMG_LO)%Z \/ (IMG_END <= z)%Z)) ->
                 outside o (bv_unsigned x)).
  { intros o Hz. destruct (outside_dec o (bv_unsigned x)) as [A|A]; [exact A|]. exfalso.
    destruct (Hz _ A) as (B1 & [B2 | [B2 | B2]]); [exact (B2 Hs) | lia | lia]. }
  apply outside_app. split; [apply Ho, O1|]. apply outside_app. split; [apply Ho, O2|]. apply HL, Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma static_agree : forall (STATIC L : list ivl) IMG_LO IMG_END HTOP m m' a k,
  (forall x, ~ outside STATIC x -> (IMG_LO <= x < IMG_END)%Z) ->
  munch (STATIC ++ [(0, IMG_LO); (IMG_END, HTOP)] ++ L)%Z m m' ->
  disjoint_from L a k -> (HTOP <= a)%Z -> (0 <= IMG_LO)%Z -> (IMG_LO <= IMG_END <= HTOP)%Z -> (a + k <= 2^64)%Z -> agree_on m m' a k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros STATIC L IMG_LO IMG_END HTOP m m' a k SOK MU HL Ha H0 He Hk i Hi. apply MU. rewrite wa_unsigned by lia.
  apply outside_app. split.
  - destruct (outside_dec STATIC (a + i)) as [A|A]; [exact A|]. specialize (SOK _ A). lia.
  - cbn [app outside]. split; [lia|]. split; [lia|]. eapply disjoint_outside; [exact HL | lia].
Qed.

End Agree.
