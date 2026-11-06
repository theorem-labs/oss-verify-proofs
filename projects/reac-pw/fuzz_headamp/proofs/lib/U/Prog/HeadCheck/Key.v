(** The walk of one pair with the prefix (UBSan LLVMFuzzerTestOneInput, 0x14354 -> 0x144f4 / 0x146fc:
    U/Prog/HeadCheck/Cut.v [key_stmt]), from strcmp's contract and [near_stmt] (the inlined pod_nearest, taken as a
    hypothesis). Section KeyWalk fixes key_stmt's frame (sp, gp, tp, the saved registers, the FP registers F, the
    entry memory m), the key k at K, the value e = ent[v], the two continuations, and the two sub-pieces of
    U/Prog/HeadCheck/KeyCut.v ([rc_stmt]: read_channel up to the byte after the digits; [val_stmt]: &ent[v],
    cell_value and value <= top). Walked backwards: the exits (0x144f4 refusal, 0x146fc cell), the value piece
    (0x14554), big / ch > 47 (0x14540), the strcmp chain (0x14478 -> 0x14540 / 0x144f4), the used / '.' tests and
    the sign (0x14438), read_channel (0x14374) and keys++ (0x14354). The verdict agrees with Pod/Headamp.v
    [expect_cell] because each test the code makes decides one step of read_channel / expect_key / cell_value
    (Prog/HeadCheck/KeyFacts.v). [key_holds_of] takes the two sub-pieces as premises; [key_holds] discharges them
    with U/Prog/HeadCheck/KeyRc.v [rc_holds] and U/Prog/HeadCheck/KeyVal.v [val_holds]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c strcmp_c
  ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut KeyCut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require KeyRc KeyVal.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a lemma's entry. *)
Ltac weq := first [ reflexivity
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

(** ** MemNorm.task_mem of the UBSan library across a store *)
Lemma wview_task_u : forall m x, MemNorm.task_mem rsegs m -> wview rsegs m x <> None ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x T W. destruct (m x) as [b|] eqn:E.
  - exact (T x b E).
  - left. unfold wview in W. rewrite E in W.
    destruct (find_segment rsegs (bv_unsigned x) 1); [discriminate | exfalso; apply W; reflexivity].
Qed.

Lemma task_mem_write_u : forall m a bs, MemNorm.task_mem rsegs m -> store_ok rsegs m a (length bs) = true ->
  MemNorm.task_mem rsegs (write_to_mem m a bs).
Proof.
  intros m a bs T S x b E. destruct (write_to_mem_some _ _ _ _ _ E) as [E' | (i & Hi & ->)].
  - exact (T x b E').
  - exact (wview_task_u m _ T (store_ok_wview rsegs m a (length bs) i S Hi)).
Qed.

(** ** Reads of byte runs *)
Lemma bytes_at_suffix : forall m A l i, bytes_at rsegs m A l -> (i <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat i) (skipn i l).
Proof.
  intros m A l i H Hi. rewrite <- (firstn_skipn i l) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length l)) with i in H by lia. exact H.
Qed.

Lemma byte_read : forall m A l i, bytes_at rsegs m A l -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [nth i l NUL].
Proof.
  intros m A l i H Hi. rewrite (bytes_at_ov_read rsegs m A l i 1 H) by lia.
  rewrite (skipn_nth_cons l i NUL Hi). reflexivity.
Qed.

Lemma len_ent_mem : forall e, ent_wf e -> length (ent_mem e) = 104%nat.
Proof. intros e (_ & Hb & Hs). unfold ent_mem. rewrite !length_app, !length_le32, length_zeros. lia. Qed.

(** A suffix of l ++ r that starts inside l. *)
Lemma skipn_app_in : forall (l r : list byte) i, (i <= length l)%nat -> skipn i (l ++ r) = skipn i l ++ r.
Proof. intros l r i H. rewrite skipn_app. replace (i - length l)%nat with O by lia. reflexivity. Qed.

(** `beq x, -1` on a value below 2^64 - 1. *)
Lemma eqb_m1 : forall x, 0 <= x < 2^64 - 1 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small x) by lia.
  change ((-1) mod 2^64) with (2^64 - 1). apply Z.eqb_neq. lia.
Qed.

Section KeyWalk.
Variables (Q : machine_state -> Prop) (sp gp tp s1 s2 s3 s4 s5 s6 s9n : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo pp K keys : Z) (k : list byte) (v : nat) (e : ent)
          (w68 w98 wa8 wb0 : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation RS := (skipn 13 k).
Local Abbreviation EA := (pp + OFF_ENT + ENT_SIZE * Z.of_nat v).
Local Abbreviation S8 := (Z_to_bv 64 (pp + OFF_ENT)).
Local Abbreviation S0 := (Z_to_bv 64 (2^64 - 1 - (pp + OFF_ENT))).
Local Abbreviation S10 := (Z_to_bv 64 (Z.of_nat v)).
Local Abbreviation S7 := (Z_to_bv 64 (ENT_SIZE * Z.of_nat v)).
Local Abbreviation A7 := (Z_to_bv 64 (pp + OFF_ENT + 8)).

Hypothesis HKB : bytes_at rsegs m K (k ++ [NUL]).
Hypothesis HKN : ~ In NUL k.
Hypothesis HPF : ha_prefix k = true.
Hypothesis HK0 : 0 < K.
Hypothesis HKLO : K + Z.of_nat (length k) + 1 <= lo.
Hypothesis HV : (v < 32)%nat.
Hypothesis HEB : bytes_at rsegs m EA (ent_mem e).
Hypothesis HEW : ent_wf e.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis H68 : bytes_at rsegs m (SP + 0x68) (le8 w68).
Hypothesis H88 : bytes_at rsegs m (SP + 0x88) (le8 (Z_to_bv 64 RC_BIG)).
Hypothesis H98 : bytes_at rsegs m (SP + 0x98) (le8 w98).
Hypothesis HA0 : bytes_at rsegs m (SP + 0xa0) (le8 A7).
Hypothesis HA8 : bytes_at rsegs m (SP + 0xa8) (le8 wa8).
Hypothesis HB0 : bytes_at rsegs m (SP + 0xb0) (le8 wb0).
Hypothesis H138 : bytes_at rsegs m (SP + 0x138) (le4 (Z_to_bv 64 keys)).
Hypothesis HKEYS : 0 <= keys < 2^31 - 1.
Hypothesis HF9 : Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1).
Hypothesis HF18 : Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).
Hypothesis HF19 : Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63).
Hypothesis H48 : bytes_at rsegs m (SP + 0x48) (le8 (Z_to_bv 64 MHALF_HI)).
Hypothesis H50 : bytes_at rsegs m (SP + 0x50) (le8 (Z_to_bv 64 HALF_HI)).
Hypothesis H58 : bytes_at rsegs m (SP + 0x58) (le8 (Z_to_bv 64 C2_HI)).
Hypothesis H60 : bytes_at rsegs m (SP + 0x60) (le8 (Z_to_bv 64 C2_LO)).
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HFC : frm0 fc.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.

(** The FP registers an exit may hold: F off f8 / f10. *)
Definition Fok (F' : bvmap 5 word) : Prop :=
  forall r : bv 5, bv_unsigned r <> 8 -> bv_unsigned r <> 10 -> Sem.reg_get F' r = Sem.reg_get F r.

Lemma Fok_refl : Fok F.
Proof. intros r _ _. reflexivity. Qed.

Hypothesis HBAD : forall (t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' : word) (F' : bvmap 5 word)
            (fc' : bv 32) (m' : word -> option byte) (bad : Z),
       expect_cell k e = inl bad ->
       frm0 fc' -> Fok F' ->
       munch (KEY_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       bytes_at rsegs m' (SP + 0x138) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (SP + 0x40) (le8 s9n) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 bad) w98 A7
                  s2 s3 s4 s5 s6 s7' S8 s9' s10' s11' t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs)).

Hypothesis HCELL : forall (t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
            (m' : word -> option byte) (ch p val : Z),
       expect_cell k e = inr (ch, p, val) ->
       frm0 fc' -> Fok F' ->
       munch (KEY_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
       stk rsegs m' lo (SP + FRAME_LOCALS) ->
       bytes_at rsegs m' (SP + 0x138) (le4 (Z_to_bv 64 (keys + 1))) ->
       bytes_at rsegs m' (SP + 0x40) (le8 s9n) ->
       evt rsegs Q
         (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5' w98 A7
                  s2 s3 s4 s5 s6 (Z_to_bv 64 val) S8 (Z_to_bv 64 ch) s10' s11' t3' t4' (Z_to_bv 64 8) wb0)
             F' (Z_to_bv 64 0x146fc) fc' None m' (seg_rom rsegs)).

Hypothesis RC : rc_stmt.
Hypothesis VAL : val_stmt.
Hypothesis STRC : strcmp_contract.

(** ** The memory the piece carries *)
(** Changed only in KEY_W; x->keys incremented; n at sp + 0x40; the key, ent[v] and the frame cells it reads. *)
Definition MemK (m1 : word -> option byte) : Prop :=
  munch (KEY_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\ bytes_at rsegs m1 (SP + 0x138) (le4 (Z_to_bv 64 (keys + 1))) /\
  bytes_at rsegs m1 (SP + 0x40) (le8 s9n) /\
  bytes_at rsegs m1 K (k ++ [NUL]) /\ bytes_at rsegs m1 EA (ent_mem e) /\
  bytes_at rsegs m1 (SP + 0x48) (le8 (Z_to_bv 64 MHALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 HALF_HI)) /\
  bytes_at rsegs m1 (SP + 0x58) (le8 (Z_to_bv 64 C2_HI)) /\
  bytes_at rsegs m1 (SP + 0x60) (le8 (Z_to_bv 64 C2_LO)) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 w68) /\
  bytes_at rsegs m1 (SP + 0x88) (le8 (Z_to_bv 64 RC_BIG)) /\
  bytes_at rsegs m1 (SP + 0x98) (le8 w98) /\
  bytes_at rsegs m1 (SP + 0xa0) (le8 A7) /\
  bytes_at rsegs m1 (SP + 0xa8) (le8 wa8) /\
  bytes_at rsegs m1 (SP + 0xb0) (le8 wb0).

(** With big at sp + 0x38 (from 0x14478 on). *)
Definition MemK2 (m1 : word -> option byte) (big : bool) : Prop :=
  MemK m1 /\ bytes_at rsegs m1 (SP + 0x38) (le8 (Z_to_bv 64 (if big then 1 else 0))).

Lemma kbounds : 0 <= lo /\ SP + FRAME_LOCALS <= 2^64 /\ EA + 104 <= lo /\ (13 <= length k)%nat /\
  lo + 48 <= SP /\ SP + 0x1d8 <= 2^64 /\ 0 <= Z.of_nat v < 32.
Proof.
  pose proof HST as (ST0 & ST1 & _). pose proof (ha_prefix_len k HPF) as L.
  unfold POD_PROPS, OFF_ENT, ENT_SIZE, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

Lemma len_k_nul : length (k ++ [NUL]) = S (length k).
Proof. rewrite length_app. cbn [length]. lia. Qed.

(** 0x144f4: the refusal exit. *)
Lemma bad_exit : forall (t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' : word) (F' : bvmap 5 word)
                        (fc' : bv 32) (m1 : word -> option byte) (bad : Z),
  expect_cell k e = inl bad -> frm0 fc' -> Fok F' -> MemK m1 ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 bad) w98 A7
             s2 s3 s4 s5 s6 s7' S8 s9' s10' s11' t3' t4' (Z_to_bv 64 8) wb0)
        F' (Z_to_bv 64 0x144f4) fc' None m1 (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' F' fc' m1 bad E HF HFk
    (MU & WM & MI & TM & ST & C138 & C40 & _).
  exact (HBAD t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' F' fc' m1 bad E HF HFk MU WM MI TM ST C138 C40).
Qed.

(** 0x146fc: the cell exit. *)
Lemma cell_exit : forall (t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
                         (m1 : word -> option byte) (ch p val : Z),
  expect_cell k e = inr (ch, p, val) -> frm0 fc' -> Fok F' -> MemK m1 ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0' t1' t2' S0 s1 a0' a1' w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5' w98 A7
             s2 s3 s4 s5 s6 (Z_to_bv 64 val) S8 (Z_to_bv 64 ch) s10' s11' t3' t4' (Z_to_bv 64 8) wb0)
        F' (Z_to_bv 64 0x146fc) fc' None m1 (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' F' fc' m1 ch p val E HF HFk
    (MU & WM & MI & TM & ST & C138 & C40 & _).
  exact (HCELL t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' F' fc' m1 ch p val E HF HFk MU WM MI TM ST C138 C40).
Qed.

Ltac tr_near MU2 C :=
  apply (bytes_at_transport rsegs _ _ _ _ _ C MU2); unfold NEAR_W, NEAR_STACK; cbn [disjoint_from];
  rewrite ?length_le8, ?length_le4; repeat split; lia.

(** The nearest piece's writes ([NEAR_W]) miss every cell MemK names. *)
Lemma MemK_near : forall m1 m2, MemK m1 ->
  munch (NEAR_W SP) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 ->
  stk rsegs m2 lo (SP + FRAME_LOCALS) -> MemK m2.
Proof.
  intros m1 m2 (MU & WM & MI & TM & ST & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)
    MU2 WM2 MI2 TM2 ST2.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). pose proof (len_ent_mem e HEW) as LE.
  pose proof len_k_nul as LK.
  unfold FRAME_LOCALS, NEAR_STACK in *.
  split.
  { apply (munch_trans _ m m1 m2 MU). eapply munch_weaken; [|exact MU2].
    unfold sub_fp, KEY_W, NEAR_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _).
    split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
  split; [tr_near MU2 C1|]. split; [tr_near MU2 C2|].
  split; [apply (bytes_at_transport rsegs _ _ _ _ _ C3 MU2); unfold NEAR_W, NEAR_STACK; cbn [disjoint_from];
          rewrite LK; repeat split; lia|].
  split; [apply (bytes_at_transport rsegs _ _ _ _ _ C4 MU2); unfold NEAR_W, NEAR_STACK; cbn [disjoint_from];
          rewrite LE; repeat split; lia|].
  split; [tr_near MU2 C5|]. split; [tr_near MU2 C6|]. split; [tr_near MU2 C7|]. split; [tr_near MU2 C8|].
  split; [tr_near MU2 C9|]. split; [tr_near MU2 C10|]. split; [tr_near MU2 C11|]. split; [tr_near MU2 C12|].
  split; [tr_near MU2 C13|]. tr_near MU2 C14.
Qed.

(** 0x14554: the value piece ([val_stmt]) on a key whose verdict is the cell (ch, p) when the value fits. *)
Lemma val_go : forall (t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 : word) (m1 : word -> option byte) (ch p : Z),
  MemK m1 -> expect_key RS = KCell ch p ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 a7
             s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x14554) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 m1 ch p MK EK.
  pose proof MK as (MU & WM & MI & TM & ST & C138 & C40 & CK & CE & C48 & C50 & C58 & C60 & C68 & C88 & C98 & CA0 &
                    CA8 & CB0).
  eapply (VAL Q wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 (Z_to_bv 64 9) (Z_to_bv 64 p) (Z_to_bv 64 5) a6 a7
            s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0 F fc m1 lo pp p v e
            w68 w98 wa8 wb0);
    try reflexivity; try exact HV; try exact HEW; try exact HPP0; try exact HPPLO; try exact HLO; try exact HSPA;
    try exact HROM; try exact HFC; try exact HF9; try exact HF18; try exact HF19; try eassumption.
  - intros t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' F' fc' m' Hv HF' HFk MU' WM' MI' TM' ST'.
    apply (bad_exit t0' t1' t2' a0' a1' a3' a4' s7' (Z_to_bv 64 ch) s10' (Z_to_bv 64 (ktop p)) t3' t4' F' fc' m'
             REFUSE_OUT_OF_RANGE); [| exact HF' | exact HFk | exact (MemK_near m1 m' MK MU' WM' MI' TM' ST')].
    rewrite expect_cell_key, EK, Hv. reflexivity.
  - intros t0' t1' t2' a0' a1' a5' s10' t3' t4' F' fc' m' Hv HF' HFk MU' WM' MI' TM' ST'.
    apply (cell_exit t0' t1' t2' a0' a1' a5' s10' (Z_to_bv 64 (ktop p)) t3' t4' F' fc' m' ch p (cell_value e));
      [| exact HF' | exact HFk | exact (MemK_near m1 m' MK MU' WM' MI' TM' ST')].
    rewrite expect_cell_key, EK, Hv. reflexivity.
Qed.

(** 0x14540 .. 0x14550: a5 = OUT_OF_RANGE; big (sp + 0x38) refuses; ch > 47 unsigned refuses. *)
Lemma range_ok : forall (t0 t1 t2 a0 a1 a5 t3 t4 : word) (m1 : word -> option byte) (big : bool) (ch p : Z),
  MemK2 m1 big -> -2^63 <= ch < 2^63 ->
  expect_key RS = (if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p) ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 w68 (Z_to_bv 64 9) (Z_to_bv 64 p) a5 w98 A7
             s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 (Z_to_bv 64 (ktop p)) t3 t4 (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x14540) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a5 t3 t4 m1 big ch p (MK & C38) Hch EK.
  (* 0x14540 addi a5,zero,5; ld a0,0x38(sp); bnez a0 *)
  step.
  pose proof (read_le8 rsegs m1 (SP + 0x38) _ C38) as HR. step. clear HR.
  step. destruct big.
  - if_true.
    apply (bad_exit _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 REFUSE_OUT_OF_RANGE); [| exact HFC | exact Fok_refl | exact MK].
    rewrite expect_cell_key, EK. reflexivity.
  - if_false.
    (* 0x1454c addi a0,zero,0x2f; bltu a0,s9 *)
    step. step. rewrite range_gtu47 by lia. cbn [orb] in EK.
    destruct ((ch <? 0) || (HA_CHANNELS <=? ch)) eqn:R; cbv beta iota.
    + apply (bad_exit _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 REFUSE_OUT_OF_RANGE); [| exact HFC | exact Fok_refl | exact MK].
      rewrite expect_cell_key, EK. reflexivity.
    + eapply val_go; [exact MK | exact EK].
Qed.

(** 0x144e8 .. 0x144f0: the refusal BAD_KEY with a2, a6, a7 reloaded. *)
Lemma bad_e8 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s7 s9 s10 s11 t3 t4 : word) (m1 : word -> option byte),
  MemK m1 -> expect_cell k e = inl REFUSE_BAD_KEY ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 4) a6 a7
             s2 s3 s4 s5 s6 s7 S8 s9 s10 s11 t3 t4 (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x144e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s7 s9 s10 s11 t3 t4 m1 MK E.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C68 & _ & C98 & CA0 & _).
  pose proof (read_le8 rsegs m1 (SP + 0x68) _ C68) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 0x98) _ C98) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 0xa0) _ CA0) as HR. step. clear HR.
  apply (bad_exit _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 REFUSE_BAD_KEY); [exact E | exact HFC | exact Fok_refl | exact MK].
Qed.

Ltac tr_st C := apply bytes_at_write_other; [exact C | lia | lia | rewrite ?length_le8, ?length_le4; lia].

(** A store into [sp + 0x28, sp + 0x40) (big at sp + 0x38). *)
Lemma MemK_store : forall m1 a bs, MemK m1 -> SP + 0x28 <= a -> a + Z.of_nat (length bs) <= SP + 0x40 ->
  MemK (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & TM & ST & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)
    H1 H2.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). pose proof (len_ent_mem e HEW) as LE.
  pose proof len_k_nul as LK. unfold FRAME_LOCALS, NEAR_STACK in *.
  assert (HS : store_ok rsegs m1 (wa a) (length bs) = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + 0x1d8)); [exact ST | lia | lia]).
  split; [apply munch_write; [exact MU | lia | lia | unfold KEY_W, NEAR_STACK; cbn [inside]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply task_mem_write_u; [exact TM | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [tr_st C1|]. split; [tr_st C2|].
  split; [apply bytes_at_write_other; [exact C3 | lia | lia | rewrite LK; lia]|].
  split; [apply bytes_at_write_other; [exact C4 | lia | lia | rewrite LE; lia]|].
  split; [tr_st C5|]. split; [tr_st C6|]. split; [tr_st C7|]. split; [tr_st C8|]. split; [tr_st C9|].
  split; [tr_st C10|]. split; [tr_st C11|]. split; [tr_st C12|]. split; [tr_st C13|]. tr_st C14.
Qed.

Lemma MemK2_init : forall m1 (big : bool), MemK m1 ->
  MemK2 (write_to_mem m1 (wa (SP + 0x38)) (le8 (Z_to_bv 64 (if big then 1 else 0)))) big.
Proof.
  intros m1 big MK. pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). unfold FRAME_LOCALS in *.
  split; [apply MemK_store; [exact MK | lia | rewrite length_le8; lia]|].
  apply bytes_at_write_same; rewrite ?length_le8; lia.
Qed.

(** 0x14524 .. 0x1453c: the reloads after "phantom" or "pad" matched (top 1). *)
Lemma name_join : forall (ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte)
                         (big : bool) (ch p : Z),
  MemK2 m1 big -> -2^63 <= ch < 2^63 ->
  expect_key RS = (if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 (Z_to_bv 64 p) a5 a6 a7
             s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 (Z_to_bv 64 (ktop p)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14524) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 m1 big ch p MK2 Hch EK.
  pose proof MK2 as (MK & _).
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C68 & _ & C98 & CA0 & CA8 & CB0).
  (* 0x14524 ld a2,0x68(sp); addi t5,zero,8; addi a3,zero,9; ld t6,0xb0(sp); ld a6,0x98(sp); ld a7,0xa0(sp);
     ld ra,0xa8(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 0x68) _ C68) as HR. step. clear HR.
  step. step.
  pose proof (read_le8 rsegs m1 (SP + 0xb0) _ CB0) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 0x98) _ C98) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 0xa0) _ CA0) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 0xa8) _ CA8) as HR. step. clear HR.
  eapply range_ok; [exact MK2 | exact Hch | exact EK].
Qed.

Lemma nm_neq : forall nm l, bytes_eqb nm l = false -> nm <> l.
Proof. intros nm l H E. subst nm. rewrite (proj2 (bytes_eqb_eq l l) eq_refl) in H. discriminate H. Qed.

Lemma r_nonzero : forall (r : word) (sx sy : list byte), (r = Z_to_bv 64 0 <-> sx = sy) -> sx <> sy ->
  bv_eqb r (Z_to_bv 64 0) = false.
Proof.
  intros r sx sy Hr Hn. destruct (bv_eqb r (Z_to_bv 64 0)) eqn:X; [|reflexivity].
  apply bv_eqb_true in X. exfalso. exact (Hn (proj1 Hr X)).
Qed.

(** 0x14478 .. 0x144e4: big to sp + 0x38; name = rest + used + 1 (s11 = a6 + 14 with a6 = K + used); strcmp against
    "phantom" (top 1, p 0), "pad" (top 1, p 1), "sens" (top 55, p 2); none of them refuses BAD_KEY. *)
Lemma name_ok : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s11 t3 : word) (m1 : word -> option byte) (big : bool)
                       (ch U : Z) (nm : list byte),
  MemK m1 -> -2^63 <= ch < 2^63 -> 0 <= U ->
  bytes_at rsegs m1 (K + U + 14) (nm ++ [NUL]) -> ~ In NUL nm -> K + U + 14 + Z.of_nat (length nm) + 1 <= lo ->
  expect_key RS = match param_of_name nm with
                  | None => KBad
                  | Some p => if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p
                  end ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (K + U)) a7
             s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 s11 t3 (Z_to_bv 64 (if big then 1 else 0)) (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x14478) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s11 t3 m1 big ch U nm MK Hch HU HN HNN HNL EK.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). unfold FRAME_LOCALS in *.
  pose proof MK as (_ & _ & _ & _ & ST & _).
  (* 0x14478 sd t4,0x38(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 0x38)) 8 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + 0x1d8)); [exact ST | lia | lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0x38));
    assert (MK2 : MemK2 (write_to_mem m1 (wa (SP + 0x38)) BS) big) by (apply MemK2_init; exact MK);
    assert (HN2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x38)) BS) (K + U + 14) (nm ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?length_app; cbn [length];
          [exact HN | lia | lia | lia]);
    revert MK2 HN2; generalize (write_to_mem m1 (wa (SP + 0x38)) BS) as m2; intros m2 MK2 HN2
  end.
  clear HS HN ST. pose proof MK2 as ((_ & _ & MI2 & _) & _).
  destruct (lits_at m2 MI2) as (_ & LPH & LPA & LSE).
  pose proof names_no_nul as (NPH & NPA & NSE).
  (* 0x1447c addi s11,a6,0xe; auipc a0; addi a1,a0,-0x151; mv a0,s11; jal strcmp *)
  step. step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := nm) (sy := NAME_PHANTOM).
    - rewrite unsigned_lit by lia. replace (K + U + 14) with (K + U + 14) by lia. exact HN2.
    - exact HNN.
    - exact LPH.
    - exact NPH. }
  intros ms' (r1 & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  (* 0x14490 beqz a0 *)
  destruct (bytes_eqb nm NAME_PHANTOM) eqn:E1.
  { apply bytes_eqb_eq in E1. rewrite (proj2 Hr E1).
    step. if_true.
    (* 0x14510 mv a4,zero; addi s11,zero,1; j 0x14524 *)
    step. step. step.
    rewrite (param_phantom nm E1) in EK.
    apply (name_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 big ch HA_PHANTOM MK2 Hch EK). }
  apply nm_neq in E1. step. rewrite (r_nonzero r1 nm NAME_PHANTOM Hr E1). cbv beta iota.
  (* 0x14494 auipc a0; addi a1,a0,-0x35; mv a0,s11; jal strcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := nm) (sy := NAME_PAD).
    - rewrite unsigned_lit by lia. exact HN2.
    - exact HNN.
    - exact LPA.
    - exact NPA. }
  intros ms' (r2 & y11 & y12 & y13 & E & Hr2). subst ms'. ret_even.
  (* 0x144a4 beqz a0 *)
  destruct (bytes_eqb nm NAME_PAD) eqn:E2.
  { apply bytes_eqb_eq in E2. rewrite (proj2 Hr2 E2).
    step. if_true.
    (* 0x1451c addi s11,zero,1; addi a4,zero,1 *)
    step. step.
    rewrite (param_pad nm E1 E2) in EK.
    apply (name_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 big ch HA_PAD MK2 Hch EK). }
  apply nm_neq in E2. step. rewrite (r_nonzero r2 nm NAME_PAD Hr2 E2). cbv beta iota.
  (* 0x144a8 auipc a0; addi a1,a0,-0x1f0; mv a0,s11; jal strcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := nm) (sy := NAME_SENS).
    - rewrite unsigned_lit by lia. exact HN2.
    - exact HNN.
    - exact LSE.
    - exact NSE. }
  intros ms' (r3 & z11 & z12 & z13 & E & Hr3). subst ms'. ret_even.
  pose proof MK2 as (MK' & _).
  pose proof MK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C68 & _ & C98 & CA0 & CA8 & CB0).
  (* 0x144b8 ld a2,0x68(sp); addi t5,zero,8; addi a3,zero,9; ld t6,0xb0(sp); ld a6,0x98(sp); ld a7,0xa0(sp);
     ld ra,0xa8(sp); addi a5,zero,4; bnez a0 *)
  pose proof (read_le8 rsegs m2 (SP + 0x68) _ C68) as HR. step. clear HR.
  step. step.
  pose proof (read_le8 rsegs m2 (SP + 0xb0) _ CB0) as HR. step. clear HR.
  pose proof (read_le8 rsegs m2 (SP + 0x98) _ C98) as HR. step. clear HR.
  pose proof (read_le8 rsegs m2 (SP + 0xa0) _ CA0) as HR. step. clear HR.
  pose proof (read_le8 rsegs m2 (SP + 0xa8) _ CA8) as HR. step. clear HR.
  step.
  destruct (bytes_eqb nm NAME_SENS) eqn:E3.
  { apply bytes_eqb_eq in E3. rewrite (proj2 Hr3 E3).
    step. if_false.
    (* 0x144dc addi a4,zero,2; addi s11,zero,0x37; j 0x14540 *)
    step. step. step.
    rewrite (param_sens nm E1 E2 E3) in EK.
    apply (range_ok _ _ _ _ _ _ _ _ m2 big ch HA_SENS MK2 Hch EK). }
  apply nm_neq in E3. step. rewrite (r_nonzero r3 nm NAME_SENS Hr3 E3). cbn [negb]. cbv beta iota.
  rewrite (param_none nm E1 E2 E3) in EK.
  apply (bad_exit _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 REFUSE_BAD_KEY); [| exact HFC | exact Fok_refl | exact MK'].
  rewrite expect_cell_key, EK. reflexivity.
Qed.

Lemma len_rs : length RS = (length k - 13)%nat.
Proof. apply length_skipn. Qed.

(** The name after the '.': rest[used + 1 ..], NUL-terminated at K + used + 14, without a NUL. *)
Lemma name_bytes : forall m1 used, bytes_at rsegs m1 K (k ++ [NUL]) -> (used < length RS)%nat ->
  bytes_at rsegs m1 (K + Z.of_nat used + 14) (skipn (S used) RS ++ [NUL]).
Proof.
  intros m1 used HK Hu. rewrite len_rs in Hu.
  pose proof (bytes_at_suffix m1 K (k ++ [NUL]) (13 + S used) HK) as H.
  rewrite len_k_nul in H. specialize (H ltac:(lia)).
  rewrite skipn_app_in in H by lia. rewrite skipn_skipn.
  replace (S used + 13)%nat with (13 + S used)%nat by lia.
  replace (K + Z.of_nat used + 14) with (K + Z.of_nat (13 + S used)) by lia. exact H.
Qed.

(** 0x1444c .. 0x14474: used = d + digits (not 0), the rest + used checks (traps not taken), rest[used] == '.'. *)
Lemma dot_tail : forall (t0 t1 t2 a2 a3 t3 : word) (m1 : word -> option byte) (d nd : nat) (ch : Z) (big : bool),
  MemK m1 -> (1 <= nd)%nat -> (d + nd <= length RS)%nat -> -2^63 <= ch < 2^63 ->
  read_channel RS = ((d + nd)%nat, ch, big) ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 t1 t2 S0 s1 (Z_to_bv 64 (K + 13)) (Z_to_bv 64 (Z.of_nat d)) a2 a3
             (Z_to_bv 64 (Z.of_nat nd)) (Z_to_bv 64 4) (Z_to_bv 64 (K + Z.of_nat (d + nd)))
             (zxb (nth (d + nd) RS NUL)) s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 ch) S10 (Z_to_bv 64 K) t3
             (Z_to_bv 64 (if big then 1 else 0)) (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x1444c) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 t3 m1 d nd ch big MK Hnd Hl Hch ER.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). pose proof len_rs as LRS. unfold FRAME_LOCALS in *.
  pose proof (expect_key_read RS _ _ _ ER) as EK.
  replace ((d + nd =? 0)%nat) with false in EK by (symmetry; apply Nat.eqb_neq; lia). cbn [orb] in EK.
  (* 0x1444c add a1,a1,a4; beqz a1 *)
  step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14454 addi a2,a6,0xd; bltu a2,a0 *)
  step. step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1445c addi a0,zero,0x2e; bne a7,a0 *)
  step. step. rewrite zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth (d + nd) RS NUL)) 46) as [Ed|Ed]; cbn [negb]; cbv beta iota.
  2:{ apply (bad_e8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 MK).
      rewrite expect_cell_key, EK. reflexivity. }
  cbn [negb] in EK.
  assert (Hu : (d + nd < length RS)%nat) by (apply nth_nonnul_lt; lia).
  (* 0x14464 beqz a2; add a1,a1,s11; addi a1,a1,0xd; addi a0,zero,-1; beq a1,a0 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. step. step. step.
  rewrite eqb_m1 by lia. cbv beta iota.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & CK & _).
  pose proof (name_bytes m1 (d + nd) CK Hu) as HN.
  rewrite (cstr_id _ (no_nul_skipn _ _ (no_nul_skipn k 13 HKN))) in EK.
  eapply (name_ok _ _ _ _ _ _ _ _ _ _ _ _ m1 big ch (Z.of_nat (d + nd)) (skipn (S (d + nd)) RS) MK Hch);
    [lia | exact HN | exact (no_nul_skipn _ _ (no_nul_skipn k 13 HKN)) | | exact EK].
  rewrite length_skipn. lia.
Qed.

(** 0x14438 .. 0x14448: a5 = BAD_KEY; no digit refuses; ch = -acc after a '-'. *)
Lemma dot_ok : forall (t0 a5 : word) (m1 : word -> option byte) (neg : bool) (sn nd : nat) (acc : Z) (big : bool),
  MemK m1 ->
  rc_sign (skipn (rc_blanks RS) RS) = (neg, sn) ->
  rc_digits 0 false (skipn (rc_blanks RS + sn) RS) = (acc, big, nd) ->
  0 <= acc <= 10000009 -> (rc_blanks RS + sn + nd <= length RS)%nat ->
  evt rsegs Q
    (MS (mkR wa8 sp gp tp t0 (Z_to_bv 64 9) (Z_to_bv 64 10) S0 s1 (Z_to_bv 64 (K + 13))
             (Z_to_bv 64 (Z.of_nat (rc_blanks RS + sn))) (Z_to_bv 64 (2^64 - 1 - (K + 13)))
             (Z_to_bv 64 (if neg then 0 else 1)) (Z_to_bv 64 (Z.of_nat nd)) a5
             (Z_to_bv 64 (K + Z.of_nat (rc_blanks RS + sn + nd))) (zxb (nth (rc_blanks RS + sn + nd) RS NUL))
             s2 s3 s4 s5 s6 S7 S8 (Z_to_bv 64 acc) S10 (Z_to_bv 64 K) (Z_to_bv 64 RC_BIG)
             (Z_to_bv 64 (if big then 1 else 0)) (Z_to_bv 64 8) wb0)
        F (Z_to_bv 64 0x14438) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 a5 m1 neg sn nd acc big MK ES ED HA HL.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). pose proof len_rs as LRS. unfold FRAME_LOCALS in *.
  pose proof (read_channel_eq RS neg sn acc big nd ES ED) as ER.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C68 & _).
  (* 0x14438 addi a5,zero,4; beqz a4 *)
  step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (Z.of_nat nd) 0) as [N0|N0]; cbv beta iota.
  { assert (Hn : nd = O) by lia. subst nd. cbn [Nat.eqb] in ER.
    apply (bad_e8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 MK).
    rewrite expect_cell_key, (expect_key_read RS _ _ _ ER). reflexivity. }
  replace ((nd =? 0)%nat) with false in ER by (symmetry; apply Nat.eqb_neq; lia).
  (* 0x14440 ld a2,0x68(sp); bnez a3 *)
  pose proof (read_le8 rsegs m1 (SP + 0x68) _ C68) as HR. step. clear HR.
  step. destruct neg.
  - if_false.
    (* 0x14448 neg s9,s9 *)
    step.
    replace (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 acc))) with (Z_to_bv 64 (- acc))
      by (rewrite unsigned_lit by lia; f_equal; lia).
    eapply (dot_tail _ _ _ _ _ _ m1 (rc_blanks RS + sn) nd (- acc) big MK); [lia | lia | lia |].
    now rewrite ER.
  - if_true.
    eapply (dot_tail _ _ _ _ _ _ m1 (rc_blanks RS + sn) nd acc big MK); [lia | lia | lia |].
    now rewrite ER.
Qed.

Ltac tr2 C := apply bytes_at_write_other; [apply bytes_at_write_other; [exact C | lia | rewrite ?length_le8; lia |
              rewrite ?length_le8, ?length_le4; lia] | lia | rewrite ?length_le4; lia |
              rewrite ?length_le8, ?length_le4; lia].

(** The memory after n to sp + 0x40 (0x14354) and keys + 1 to sp + 0x138 (0x14370). *)
Lemma MemK_init : MemK (write_to_mem (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) (wa (SP + 0x138))
                        (le4 (Z_to_bv 64 (keys + 1)))).
Proof.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). pose proof (len_ent_mem e HEW) as LE.
  pose proof len_k_nul as LK. unfold FRAME_LOCALS in *.
  assert (HS1 : store_ok rsegs m (wa (SP + 0x40)) (length (le8 s9n)) = true)
    by (apply (stk_store_ok rsegs m lo (SP + 0x1d8)); [exact HST | lia | rewrite length_le8; lia]).
  set (m1 := write_to_mem m (wa (SP + 0x40)) (le8 s9n)).
  assert (ST1 : stk rsegs m1 lo (SP + 0x1d8)) by (apply stk_write; [exact HST | lia | rewrite length_le8; lia]).
  assert (HS2 : store_ok rsegs m1 (wa (SP + 0x138)) (length (le4 (Z_to_bv 64 (keys + 1)))) = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + 0x1d8)); [exact ST1 | lia | rewrite length_le4; lia]).
  split.
  { apply munch_write; [apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |] | lia |
                        rewrite length_le4; lia |];
      unfold KEY_W, NEAR_STACK; cbn [inside]; rewrite ?length_le8, ?length_le4; lia. }
  split; [apply wmono_write, wmono_write, wmono_refl|].
  split; [apply mem_inv_store; [apply mem_inv_store; [exact HMI | exact HS1] | exact HS2]|].
  split; [apply task_mem_write_u; [apply task_mem_write_u; [exact HTM | exact HS1] | exact HS2]|].
  split; [apply stk_write; [exact ST1 | lia | rewrite length_le4; lia]|].
  split; [apply bytes_at_write_same; rewrite ?length_le4; lia|].
  split; [apply bytes_at_write_other; [apply bytes_at_write_same; rewrite ?length_le8; lia | lia |
          rewrite length_le4; lia | rewrite length_le8, length_le4; lia]|].
  split; [apply bytes_at_write_other; [apply bytes_at_write_other; [exact HKB | lia | rewrite length_le8; lia |
          rewrite LK, length_le8; lia] | lia | rewrite length_le4; lia | rewrite LK, length_le4; lia]|].
  split; [apply bytes_at_write_other; [apply bytes_at_write_other; [exact HEB | lia | rewrite length_le8; lia |
          rewrite LE, length_le8; lia] | lia | rewrite length_le4; lia | rewrite LE, length_le4; lia]|].
  split; [tr2 H48|]. split; [tr2 H50|]. split; [tr2 H58|]. split; [tr2 H60|]. split; [tr2 H68|].
  split; [tr2 H88|]. split; [tr2 H98|]. split; [tr2 HA0|]. split; [tr2 HA8|]. tr2 HB0.
Qed.

(** 0x14354 .. 0x14370: n to sp + 0x40; x->keys + 1 (trap 0x1436c not taken: keys < 2^31 - 1); t5 = 8, t6 and ra
    reloaded; then read_channel ([rc_stmt]) and the rest. *)
Lemma key_go : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 S7 S8 s9n S10 (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14354) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof kbounds as (B0 & B1 & B2 & B3 & B4 & B5 & B6). unfold FRAME_LOCALS in *.
  (* 0x14354 sd s9,0x40(sp) *)
  assert (HS : store_ok rsegs m (wa (SP + 0x40)) 8 = true)
    by (apply (stk_store_ok rsegs m lo (SP + 0x1d8)); [exact HST | lia | lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?A _) _) => change A with (wa (SP + 0x40)) end.
  assert (C138 : bytes_at rsegs (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) (SP + 0x138) (le4 (Z_to_bv 64 keys)))
    by (apply bytes_at_write_other; rewrite ?length_le8, ?length_le4; [exact H138 | lia | lia | lia]).
  assert (CB0 : bytes_at rsegs (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) (SP + 0xb0) (le8 wb0))
    by (apply bytes_at_write_other; rewrite ?length_le8; [exact HB0 | lia | lia | lia]).
  assert (CA8 : bytes_at rsegs (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) (SP + 0xa8) (le8 wa8))
    by (apply bytes_at_write_other; rewrite ?length_le8; [exact HA8 | lia | lia | lia]).
  assert (ST1 : stk rsegs (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) lo (SP + 0x1d8))
    by (apply stk_write; [exact HST | lia | rewrite length_le8; lia]).
  (* 0x14358 lw a1,0x138(sp); addiw a0,a1,1; addi t5,zero,8; ld t6,0xb0(sp); ld ra,0xa8(sp); blt a0,a1 *)
  pose proof (read_le4_cell rsegs _ (SP + 0x138) _ C138) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite addiw1_small by lia.
  step.
  pose proof (read_le8 rsegs _ (SP + 0xb0) _ CB0) as HR. step. clear HR.
  pose proof (read_le8 rsegs _ (SP + 0xa8) _ CA8) as HR. step. clear HR.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14370 sw a0,0x138(sp) *)
  assert (HS2 : store_ok rsegs (write_to_mem m (wa (SP + 0x40)) (le8 s9n)) (wa (SP + 0x138)) 4 = true)
    by (apply (stk_store_ok rsegs _ lo (SP + 0x1d8)); [exact ST1 | lia | lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) => change A with (wa (SP + 0x138)) end.
  pose proof MemK_init as MK.
  pose proof MK as (_ & _ & _ & _ & _ & _ & _ & CK & _ & _ & _ & _ & _ & _ & C88 & _).
  eapply RC with (K := K) (k := k);
    [reflexivity | exact CK | exact HKN | exact B3 | exact HK0 | lia | exact C88 |].
  intros t0' a5' neg sn nd acc big ES ED HA HL.
  eapply dot_ok; [exact MK | exact ES | exact ED | exact HA | exact HL].
Qed.

End KeyWalk.

(** [key_stmt] from its two sub-pieces and strcmp's contract. *)
Theorem key_holds_of : rc_stmt -> val_stmt -> strcmp_contract -> key_stmt.
Proof.
  intros RC VAL STRC. unfold key_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo pp K keys k v e w68 w98 wa8 wb0 E11 HKB HKN HPF HK0 HKLO E8 E0 E10 E7 HV HEB HEW HPP0 HPPLO H68 H88 H98 HA0
    HA8 HB0 H138 HKEYS HF9 HF18 HF19 H48 H50 H58 H60 HST HLO HSPA HROM HFC HMI HTM HBAD HCELL.
  subst s11 s8 s0 s10 s7.
  eapply key_go; eassumption.
Qed.

(** U/Prog/HeadCheck/Cut.v [key_stmt]: one pair with the prefix, from strcmp's contract and the nearest piece. *)
Theorem key_holds : strcmp_contract -> near_stmt -> key_stmt.
Proof. intros STRC NEAR. exact (key_holds_of KeyRc.rc_holds (KeyVal.val_holds NEAR) STRC). Qed.
