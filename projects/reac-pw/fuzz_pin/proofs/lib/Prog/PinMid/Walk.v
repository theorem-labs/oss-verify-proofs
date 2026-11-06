(** The walk of reac-pw/fuzz_pin's LLVMFuzzerTestOneInput (plain) from malloc's return (0x12d1c) to the join before
    free (0x12de4), against pin_mid_contract (Prog/LLVMFuzzerTestOneInput_c.v), with the callee contracts as Section
    hypotheses. Section Mid fixes the contract's frame (sp, gp, tp, s5-s11, F, fc, the entry memory m), the spec s
    with its slack, fl, phi, lo and the guard word; QM is the contract's postcondition. Walked backwards from the
    join: tail_ok (0x12d7c: the out cells, reac_box_pin_parse, check_known, check_row, check_label), z_ok
    (0x12d74), disp_ok (0x12e40), cat_ok (0x12d6c: fuzz_catalogue_row and want_label), scan_ok (0x12d54, by
    induction on the bytes left), nul_ok (0x12d38: the NUL store and strlen), head_ok (0x12d1c: memcpy). MemH is the
    memory the walk carries after strlen: the spec bytes, the footprint so far, and the facts the parse needs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec memcpy_c strlen_c fuzz_catalogue_row_c
  reac_box_pin_parse_c check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinMid Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

(** A disjunction lia does not split. *)
Definition or_h (P Q : Prop) : Prop := P \/ Q.

Section Mid.
Variables (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
          (s slack : list byte) (fl phi lo : Z) (can : word).

Definition QM : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 PIN_JOIN) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + MID_OUT); (phi, phi + Z.of_nat (length s) + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition W0 : list (Z * Z) := [(bv_unsigned sp - 176, bv_unsigned sp + 16); (phi, phi + Z.of_nat (length s) + 1)].

Definition slack_ok : Prop := (- (phi + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
Definition spa_ok : Prop := bv_unsigned sp mod 16 = 0.

Hypothesis HFL : 0 <= fl < 256.
Hypothesis HNN : ~ In NUL s.
Hypothesis HPHI : 0 < phi.
Hypothesis HBND : phi + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= 2 ^ 64.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 176 <= bv_unsigned sp.
Hypothesis HSPT : bv_unsigned sp + 16 <= 2 ^ 64.
Hypothesis HBROM : forall a, phi <= a < phi + Z.of_nat (length s) + 1 -> seg_rom rsegs (wa a) = None.
Hypothesis HSROM : forall a, lo <= a < bv_unsigned sp + 16 -> seg_rom rsegs (wa a) = None.
Hypothesis HSEP : or_h (phi + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo)
                       (bv_unsigned sp + 16 <= phi).
Hypothesis HSLK : slack_ok.
Hypothesis HSPA : spa_ok.

Variables (src : Z) (junk : list byte).
Hypothesis HSRC : bytes_at rsegs m src s.
Hypothesis HBLK : rw_cells rsegs m phi [CB (S (length s)) junk].
Hypothesis HSLKB : bytes_at rsegs m (phi + Z.of_nat (length s) + 1) slack.
Hypothesis HDJ : or_h (src + Z.of_nat (length s) <= phi) (phi + Z.of_nat (length s) <= src).
Hypothesis HST : stk rsegs m lo (bv_unsigned sp).
Hypothesis HWR : wr_at rsegs m (bv_unsigned sp) 16.
Hypothesis HTB : tbl m.
Hypothesis HGOT : bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)).
Hypothesis HGRD : bytes_at rsegs m PARSE_SSP_GUARD (le8 can).
Hypothesis HMI : mem_inv rsegs m.

Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.
Hypothesis FCR : fuzz_catalogue_row_contract.

(** ** What is apart from what *)
Lemma str_apart : forall x y, lo <= x -> y <= bv_unsigned sp + 16 ->
  disjoint_from [(x, y)] phi (Z.of_nat (length (s ++ NUL :: slack))).
Proof.
  intros x y H1 H2. rewrite length_str. cbn [disjoint_from]. split; [|exact I].
  unfold or_h in HSEP. destruct HSEP; lia.
Qed.

Lemma table_out : forall x y, lo <= x -> y <= bv_unsigned sp + 16 ->
  forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> outside [(x, y)] a.
Proof.
  intros x y H1 H2 a Ha. cbn [outside]. split; [|exact I]. intros Hx.
  apply (rom_apart lo (bv_unsigned sp + 16) _ _ HSROM table_rom a Ha). lia.
Qed.

Lemma table_out_blk : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES ->
  outside [(phi, phi + Z.of_nat (length s) + 1)] a.
Proof.
  intros a Ha. cbn [outside]. split; [|exact I].
  exact (rom_apart _ _ _ _ HBROM table_rom a Ha).
Qed.

Lemma cell_apart : forall A x y, (forall a, A <= a < A + 8 -> seg_rom rsegs (wa a) <> None) ->
  lo <= x -> x < y -> y <= bv_unsigned sp + 16 -> disjoint_from [(x, y)] A 8.
Proof.
  intros A x y HR H1 H2 H3. cbn [disjoint_from]. split; [|exact I].
  apply ivl_apart; [|lia|lia]. intros a Ha Hx.
  apply (rom_apart lo (bv_unsigned sp + 16) A (A + 8) HSROM HR a Ha). lia.
Qed.

Lemma cell_apart_blk : forall A, (forall a, A <= a < A + 8 -> seg_rom rsegs (wa a) <> None) ->
  disjoint_from [(phi, phi + Z.of_nat (length s) + 1)] A 8.
Proof.
  intros A HR. cbn [disjoint_from]. split; [|exact I].
  apply ivl_apart; [|lia|lia]. intros a Ha Hx.
  exact (rom_apart _ _ _ _ HBROM HR a Ha Hx).
Qed.

(** ** The memory the walk carries from strlen's return to the join *)
Definition MemH (m1 : word -> option byte) : Prop :=
  bytes_at rsegs m1 phi (s ++ NUL :: slack) /\
  munch W0 m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp) /\
  wr_at rsegs m1 (bv_unsigned sp) 16 /\ tbl m1 /\
  bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can).

Lemma MemH_stack : forall m1 m2 x y, MemH m1 -> munch [(x, y)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo (bv_unsigned sp) -> lo <= x -> bv_unsigned sp - 176 <= x -> x < y -> y <= bv_unsigned sp + 16 ->
  MemH m2.
Proof.
  intros m1 m2 x y (HB & MU & WM & MI & ST & WR & TB & HG & HU) MU2 WM2 MI2 ST2 H1 H2 H3 H4.
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ HB MU2 (str_apart x y H1 H4))|].
  split.
  { apply (munch_trans W0 m m1 m2 MU). apply (munch_weaken [(x, y)] W0 m1 m2); [|exact MU2].
    unfold sub_fp, W0. cbn [outside]. intros z (O1 & O2 & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|].
  split; [exact (wr_at_transport rsegs _ _ _ _ WR WM2)|].
  split; [exact (tbl_munch _ _ _ TB MU2 (table_out x y H1 H4))|].
  split.
  - apply (bytes_at_transport rsegs _ _ _ _ _ HG MU2). rewrite length_le8.
    exact (cell_apart PARSE_SSP_GOT x y got_rom H1 H3 H4).
  - apply (bytes_at_transport rsegs _ _ _ _ _ HU MU2). rewrite length_le8.
    exact (cell_apart PARSE_SSP_GUARD x y guard_rom H1 H3 H4).
Qed.

Lemma MemH_store : forall m1 a bs, MemH m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  lo <= a -> bv_unsigned sp - 176 <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp + 16 -> (0 < length bs)%nat ->
  MemH (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs MH HS H1 H2 H3 H4. pose proof MH as (_ & _ & _ & MI & ST & _).
  apply (MemH_stack m1 _ a (a + Z.of_nat (length bs)) MH); [| | | | lia | lia | lia | lia].
  - apply munch_write; [apply munch_refl | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. apply wmono_refl.
  - apply mem_inv_store; assumption.
  - apply stk_write; [exact ST | lia | lia].
Qed.

Hypothesis PARSE : reac_box_pin_parse_contract.
Hypothesis CKN : check_known_contract.
Hypothesis CKR : check_row_contract.
Hypothesis CKL : check_label_contract.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).

(** The join's end: from 0x12d7c with s1 = want and s2 = want_label, to 0x12de4 (QM). *)
Lemma QM_done : forall (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word)
                       (m3 m4 : word -> option byte) (W : list (Z * Z)),
  MemH m3 -> munch W m3 m4 -> sub_fp W [(bv_unsigned sp - 176, bv_unsigned sp + 16)] ->
  wmono rsegs m3 m4 -> mem_inv rsegs m4 -> stk rsegs m4 lo (bv_unsigned sp) ->
  evt rsegs QM
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
             s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12de4) fc None m4 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' m3 m4 W
    (_ & MU & WM & _) MU4 SUB WM4 MI4 ST4.
  apply evt_done. unfold QM. do 21 eexists. split; [reflexivity|].
  split; [|split; [exact (wmono_trans rsegs _ _ _ WM WM4)|split; [exact MI4 | exact ST4]]].
  apply (munch_trans W0 m m3 m4 MU). refine (munch_weaken _ _ m3 m4 _ MU4).
  unfold sub_fp, W0 in *. intros x Hx. apply SUB. cbn [outside] in *. destruct Hx as (H1 & _). split; [exact H1 | exact I].
Qed.

Lemma tail_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (w wl : Z)
                       (m1 : word -> option byte),
  MemH m1 -> w = want_ptr FUZZ_CATALOGUE fl s -> wl = want_label phi fl s ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) (Z_to_bv 64 w) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 wl) (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d7c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 w wl m1 MH -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof MH as (_ & _ & _ & _ & _ & WR & _).
  assert (HS8 : store_ok rsegs m1 (wa (bv_unsigned sp + 8)) 8 = true)
    by (apply (wr_at_store_ok rsegs m1 (bv_unsigned sp) 16 8 8 WR); lia).
  (* 0x12d7c sd zero,8(sp) *)
  step.
  assert (MH2 : MemH (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 8)) (le8 (Z_to_bv 64 0)))).
  { apply (MemH_store m1 (bv_unsigned sp + 8)); rewrite ?length_le8; [exact MH | exact HS8 | lia | lia | lia | lia]. }
  clear WR HS8 MH.
  revert MH2. generalize (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 8)) (le8 (Z_to_bv 64 0))) as m2.
  intros m2 MH2. clear m1.
  pose proof MH2 as (_ & _ & _ & _ & _ & WR2 & _).
  assert (HS0 : store_ok rsegs m2 sp 8 = true).
  { pose proof (wr_at_store_ok rsegs m2 (bv_unsigned sp) 16 0 8 WR2 ltac:(lia) ltac:(lia)) as X.
    rewrite Z.add_0_r in X. unfold wa in X. rewrite Z_to_bv_lit_self in X. exact X. }
  (* 0x12d80 sd zero,0(sp) *)
  step.
  assert (MH3 : MemH (write_to_mem m2 sp (le8 (Z_to_bv 64 0)))).
  { rewrite <- (Z_to_bv_lit_self sp) at 1.
    apply (MemH_store m2 (bv_unsigned sp)); rewrite ?length_le8; [exact MH2 | | lia | lia | lia | lia].
    unfold wa. rewrite Z_to_bv_lit_self. exact HS0. }
  clear HS0 WR2 MH2.
  revert MH3. generalize (write_to_mem m2 sp (le8 (Z_to_bv 64 0))) as m3. intros m3 MH3. clear m2.
  (* 0x12d84 .. 0x12db4: the arguments *)
  do 13 step.
  rewrite (mask0 fl HFL), (mask1 fl HFL), (mask2 fl HFL).
  rewrite (unsigned_lit phi) by lia. rewrite (unsigned_lit (bv_unsigned sp + 8)) by lia.
  rewrite !land_mask by lia.
  (* 0x12db8 jal reac_box_pin_parse *)
  step.
  pose proof MH3 as (HB & MU & WM & MI & ST & WR & TB & HG & HU).
  eapply evt_cut.
  { eapply PARSE with (str := s) (slack := slack) (lo := lo) (can := can).
    - rewrite live_eq by lia. intros HL. destruct (live_bits fl HL) as (B0 & B1 & B2).
      rewrite B0, B1, B2. cbv iota. rewrite !unsigned_lit by lia.
      unfold parse_args. split; [exact HB|]. split; [exact HNN|]. split; [exact HSLK|].
      split; [unfold or_h in HSEP; lia|].
      split; [apply (wr_at_sub m3 (bv_unsigned sp) 16); [exact WR | lia | lia | lia]|].
      split; [apply (wr_at_sub m3 (bv_unsigned sp) 16); [exact WR | lia | lia | lia]|].
      split; [lia|]. split; lia.
    - exact ST.
    - unfold PARSE_STACK. lia.
    - exact HSPA.
    - intros a Ha. apply HSROM. lia.
    - exact TB.
    - exact HG.
    - exact HU.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 &
              E & WM4 & MI4 & ST4 & PM).
  subst ms'.
  rewrite live_eq in PM by lia. rewrite live_eq by lia. rewrite po_eq in PM by lia. rewrite po_eq by lia.
  ret_even.
  (* 0x12dbc mv s3,a0; mv a1,s1; jal check_known *)
  do 3 step.
  eapply evt_cut; [eapply CKN; apply known_iff; [exact HFL | exact HNN]|].
  intros ms' (a0x & a1x & ->). ret_even.
  destruct (parse_out FUZZ_CATALOGUE phi (fl_live fl) s) as [[row lab]|] eqn:EPO.
  - (* accepted: rc = 0 *)
    pose proof (live_out _ _ _ _ _ EPO) as HL. destruct (live_bits fl HL) as (B0 & B1 & B2).
    rewrite B1, B2 in PM. cbv iota in PM. rewrite !unsigned_lit in PM by lia.
    unfold parse_mem in PM. destruct PM as (PMU & PR & PL).
    destruct (harness_row_label FUZZ_CATALOGUE phi fl s row lab HFL HNN EPO) as (ER & EL).
    change (parse_rc (Some (row, lab))) with 0.
    (* 0x12dc8 bnez s3 *)
    step. if_false.
    assert (HR8 : ov_read_bytes rsegs m4 (wa (bv_unsigned sp + 8)) 8 = Some (le8 (Z_to_bv 64 row)))
      by (apply bytes_at_read8; [exact PR | apply length_le8]).
    (* 0x12dcc ld a0,8(sp); mv a1,s1; jal check_row *)
    do 3 step. clear HR8.
    eapply evt_cut; [eapply CKR; rewrite ER; reflexivity|].
    intros ms' ->. ret_even.
    assert (HR0 : ov_read_bytes rsegs m4 sp 8 = Some (le8 (Z_to_bv 64 lab))).
    { pose proof (bytes_at_read8 m4 (bv_unsigned sp) _ PL (length_le8 _)) as X.
      unfold wa in X. rewrite Z_to_bv_lit_self in X. exact X. }
    (* 0x12dd8 ld a0,0(sp); mv a1,s2; jal check_label *)
    do 3 step. clear HR0.
    eapply evt_cut; [eapply CKL; rewrite EL; reflexivity|].
    intros ms' ->. ret_even.
    apply (QM_done _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 m4 _ MH3 PMU); [|exact WM4 | exact MI4 | exact ST4].
    unfold sub_fp, PARSE_STACK. cbn [outside]. intros x (H1 & _). repeat split; try exact I; lia.
  - (* refused: rc = -1 *)
    unfold parse_mem in PM. cbv beta iota in PM.
    change (parse_rc None) with (-1).
    (* 0x12dc8 bnez s3 *)
    step. if_true.
    apply (QM_done _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 m4 _ MH3 PM); [|exact WM4 | exact MI4 | exact ST4].
    unfold sub_fp, PARSE_STACK. cbn [outside]. intros x (H1 & _). repeat split; try exact I; lia.
Qed.

(** 0x12d74 `mv s1,zero; mv s2,zero`: no expectation (want = NULL, want_label = NULL). *)
Lemma z_ok : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word) (m1 : word -> option byte),
  MemH m1 -> harness_want fl s = None ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 fl) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d74) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 m1 MH HW.
  destruct (want_none FUZZ_CATALOGUE phi fl s HW) as (E1 & E2).
  step. step.
  eapply tail_ok; [exact MH | symmetry; exact E1 | symmetry; exact E2].
Qed.

(** 0x12e40 `ld s2,8(s1)` (s1 = row i of the table): want_label is the row's display pointer. *)
Lemma disp_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word) (i : nat)
                       (m1 : word -> option byte),
  MemH m1 -> (i < CAT_N)%nat -> harness_want fl s = Some i -> harness_label_off s = None ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) (Z_to_bv 64 (row_addr FUZZ_CATALOGUE i)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12e40) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 i m1 MH Hi HW HL.
  pose proof MH as (_ & _ & _ & _ & _ & _ & TB & _).
  pose proof (row_addr_range i Hi) as (Ra1 & Ra2).
  assert (HR : ov_read_bytes rsegs m1 (wa (row_addr FUZZ_CATALOGUE i + 8)) 8 = Some (le8 (Z_to_bv 64 (disp_ptr i))))
    by (apply disp_read; [exact TB | exact Hi]).
  (* 0x12e40 ld s2,8(s1); j 0x12d7c *)
  step. clear HR. step.
  eapply tail_ok; [exact MH | |].
  - unfold want_ptr. rewrite HW. reflexivity.
  - unfold want_label. rewrite HW, HL. reflexivity.
Qed.

(** 0x12d6c `andi a0,s3,7`: when fl & 7 = 0, want = fuzz_catalogue_row(spec, tok) and want_label (0x12e10 ..
    0x12e44); else none. tok = c = colon_idx s, s4 the last byte the scan read. *)
Lemma cat_ok : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (c : nat)
                      (m1 : word -> option byte),
  MemH m1 -> c = colon_idx s -> length s <> 0%nat -> (bv_unsigned s4 = 58 <-> (c < length s)%nat) ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat c))
             (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d6c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 c m1 MH Hc Hn HS4.
  pose proof (colon_idx_le s) as Hcl.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof MH as (HB & _ & _ & MI & ST & _ & TB & _).
  (* 0x12d6c andi a0,s3,7; beqz a0 *)
  step. step. if_cases E; zify_cond E.
  - (* fl & 7 = 0: 0x12e10 mv a0,s0; mv a1,s2; jal fuzz_catalogue_row *)
    step. step. step.
    eapply evt_cut.
    { eapply FCR with (sb := firstn c s) (lo := lo); rewrite ?unsigned_lit by lia.
      - rewrite <- (firstn_str s slack c) by lia. apply bytes_at_firstn. exact HB.
      - rewrite length_firstn. lia.
      - exact ST.
      - unfold FCR_STACK. lia.
      - intros a Ha. apply HSROM. lia.
      - rewrite length_firstn. unfold or_h in HSEP. destruct HSEP; lia.
      - exact TB.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                E2 & MU2 & WM2 & MI2 & ST2).
    subst ms'. ret_even.
    assert (MH2 : MemH m2).
    { apply (MemH_stack m1 m2 (bv_unsigned sp - FCR_STACK) (bv_unsigned sp) MH MU2 WM2 MI2 ST2);
        unfold FCR_STACK; lia. }
    clear MU2 WM2 MI2 ST2.
    pose proof (want_on fl s ltac:(lia) Hn) as HW. rewrite <- Hc in HW.
    destruct (row_of (firstn c s)) as [i|] eqn:ER.
    + (* row i *)
      pose proof (row_of_some _ _ ER) as (Hi & _ & _).
      pose proof (row_addr_range i Hi) as (Ra1 & Ra2).
      replace (row_ptr FUZZ_CATALOGUE (firstn c s)) with (row_addr FUZZ_CATALOGUE i)
        by (unfold row_ptr; rewrite ER; reflexivity).
      (* 0x12e1c beqz a0 *)
      step. if_cases E3; zify_cond E3; [exfalso; lia|].
      (* 0x12e20 mv s1,a0; addi a0,zero,58; bne s4,a0 *)
      step. step. step. if_cases E4; zify_cond E4.
      * (* no ':' : display *)
        assert (Hce : c = length s).
        { destruct (Nat.lt_ge_cases c (length s)) as [Hlt|Hge]; [apply HS4 in Hlt; contradiction | lia]. }
        eapply disp_ok; [exact MH2 | exact Hi | exact HW | apply label_off_end; congruence].
      * (* ':' at c: 0x12e2c add s2,s0,s2; lbu a0,1(s2) *)
        assert (Hlt : (c < length s)%nat) by (apply HS4; exact E4).
        step.
        assert (HR1 : ov_read_bytes rsegs m2 (wa (phi + Z.of_nat c + 1)) 1 = Some [nth (S c) (s ++ NUL :: slack) NUL]).
        { pose proof MH2 as (HB2 & _).
          replace (phi + Z.of_nat c + 1) with (phi + Z.of_nat (S c)) by lia.
          apply bytes_at_byte; [exact HB2 | rewrite length_str; lia]. }
        step. clear HR1.
        rewrite (nth_str_le s slack (S c)) by lia.
        (* 0x12e34 beqz a0 *)
        step. if_cases E5; zify_cond E5; rewrite ?byte_lit in E5.
        -- (* nothing after the ':' : display *)
           eapply disp_ok; [exact MH2 | exact Hi | exact HW |].
           rewrite (label_off_lt s) by lia. rewrite <- Hc. rewrite E5. reflexivity.
        -- (* label = spec + tok + 1: 0x12e38 addi s2,s2,1; j 0x12d7c *)
           step. step.
           eapply tail_ok; [exact MH2 | unfold want_ptr; rewrite HW; reflexivity |].
           unfold want_label. rewrite HW. rewrite (label_off_lt s) by lia. rewrite <- Hc.
           replace (bv_unsigned (nth (S c) (s ++ [NUL]) NUL) =? 0) with false
             by (symmetry; apply Z.eqb_neq; exact E5).
           cbv iota. lia.
    + (* no row: 0x12e1c beqz a0 to 0x12d74 *)
      replace (row_ptr FUZZ_CATALOGUE (firstn c s)) with 0 by (unfold row_ptr; rewrite ER; reflexivity).
      step. first [if_true | idtac].
      eapply z_ok; [exact MH2 | exact HW].
  - (* fl & 7 <> 0: 0x12d74 *)
    eapply z_ok; [exact MH | apply want_off; exact E].
Qed.

(** The scan 0x12d54 .. 0x12d68 (`while (tok < len && spec[tok] != ':') tok++`), by induction on the bytes left. *)
Lemma scan_ok : forall n j (ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (m1 : word -> option byte),
  (length s - j <= n)%nat -> (j < length s)%nat -> (j <= colon_idx s)%nat -> MemH m1 ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) s1 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 58)
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d54) fc None m1 (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 m1 Hn Hj Hc MH; [lia|].
  pose proof MH as (HB & _).
  assert (HR : ov_read_bytes rsegs m1 (wa (phi + Z.of_nat j)) 1 = Some [nth j s NUL]).
  { rewrite <- (nth_str_lt s slack j Hj). apply bytes_at_byte; [exact HB | rewrite length_str; lia]. }
  (* 0x12d54 add a2,s0,s2; lbu s4,0(a2) *)
  step. step. clear HR.
  (* 0x12d5c beq s4,a1 *)
  step. if_cases E; zify_cond E; rewrite ?byte_lit in E.
  - (* ':' at j *)
    eapply cat_ok; [exact MH | symmetry; apply colon_idx_hit; [lia | lia | exact E] | lia |].
    rewrite zxb_unsigned. split; intros _; [exact Hj | exact E].
  - (* 0x12d60 addi s2,s2,1; bne a0,s2 *)
    step. step. if_cases E2; zify_cond E2.
    + replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
      apply IH; [lia | lia | apply colon_idx_miss; [lia | lia | exact E] | exact MH].
    + (* 0x12d68 mv s2,a0: tok = len *)
      step.
      eapply cat_ok; [exact MH | | lia |].
      * symmetry. apply colon_idx_end. pose proof (colon_idx_miss s j Hc Hj E). lia.
      * rewrite zxb_unsigned. split; [intros X; contradiction | lia].
Qed.

Lemma MemH_nil : forall m2 m3, MemH m2 -> munch [] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> MemH m3.
Proof.
  intros m2 m3 (HB & MU & WM & MI & ST & WR & TB & HG & HU) MU3 WM3 MI3.
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ HB MU3 I)|].
  split; [apply (munch_trans W0 m m2 m3 MU); exact (munch_weaken [] W0 m2 m3 (fun x _ => I) MU3)|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM3)|].
  split; [exact MI3|].
  split; [exact (stk_transport_disjoint rsegs _ _ _ _ _ ST MU3 WM3 I)|].
  split; [exact (wr_at_transport rsegs _ _ _ _ WR WM3)|].
  split; [exact (tbl_munch _ _ _ TB MU3 (fun _ _ => I))|].
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ HG MU3 I) | exact (bytes_at_transport rsegs _ _ _ _ _ HU MU3 I)].
Qed.

(** MemH of a memory changed only in the block [phi, phi + k + 1). *)
Lemma MemH_blk : forall m2, munch [(phi, phi + Z.of_nat (length s) + 1)] m m2 -> wmono rsegs m m2 ->
  mem_inv rsegs m2 -> bytes_at rsegs m2 phi (s ++ NUL :: slack) -> MemH m2.
Proof.
  intros m2 MU2 WM2 MI2 HB2. split; [exact HB2|].
  split.
  { apply (munch_weaken [(phi, phi + Z.of_nat (length s) + 1)] W0 m m2); [|exact MU2].
    unfold sub_fp, W0. cbn [outside]. intros x (O1 & O2 & _). split; [exact O2 | exact I]. }
  split; [exact WM2|]. split; [exact MI2|].
  split.
  { apply (stk_transport_disjoint rsegs _ m m2 _ _ HST MU2 WM2). cbn [disjoint_from]. split; [|exact I].
    unfold or_h in HSEP. destruct HSEP; lia. }
  split; [exact (wr_at_transport rsegs _ _ _ _ HWR WM2)|].
  split; [exact (tbl_munch _ _ _ HTB MU2 table_out_blk)|].
  split.
  - apply (bytes_at_transport rsegs _ _ _ _ _ HGOT MU2). rewrite length_le8.
    exact (cell_apart_blk PARSE_SSP_GOT got_rom).
  - apply (bytes_at_transport rsegs _ _ _ _ _ HGRD MU2). rewrite length_le8.
    exact (cell_apart_blk PARSE_SSP_GUARD guard_rom).
Qed.

(** 0x12d38 .. 0x12d48: phi[k] = 0 (`sb zero,0(s1)` at phi + k, inside the block), strlen(phi) = k; then len = 0
    to 0x12d74, else the scan from tok = 0. *)
Lemma nul_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word) (m1 : word -> option byte),
  bytes_at rsegs m1 phi s -> munch [(phi, phi + Z.of_nat (length s))] m m1 -> wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 phi) (Z_to_bv 64 (Z.of_nat (length s))) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d38) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 m1 HB1 MU1 WM1 MI1.
  pose proof (rw_cells_CB_wr _ _ _ _ HBLK) as WB.
  assert (HS : store_ok rsegs m1 (wa (phi + Z.of_nat (length s))) 1 = true).
  { apply (wr_at_store_ok rsegs m1 phi (Z.of_nat (S (length s))) (Z.of_nat (length s)) 1);
      [exact (wr_at_transport rsegs _ _ _ _ WB WM1) | lia | lia]. }
  (* 0x12d38 add s1,s0,s1; sb zero,0(s1) *)
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?a ?bs) _) =>
    replace bs with [NUL] by reflexivity;
    replace a with (wa (phi + Z.of_nat (length s))) by (unfold wa; first [reflexivity | f_equal; lia])
  end.
  assert (MH2 : MemH (write_to_mem m1 (wa (phi + Z.of_nat (length s))) [NUL])).
  { apply MemH_blk.
    - apply (munch_trans _ m m1).
      + apply (munch_weaken [(phi, phi + Z.of_nat (length s))] _ m m1); [|exact MU1].
        unfold sub_fp. cbn [outside]. intros x (O1 & _). split; [lia | exact I].
      + apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia].
    - apply wmono_write. exact WM1.
    - apply mem_inv_store; [exact MI1 | exact HS].
    - apply bytes_at_app. split.
      + apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | cbn [length]; lia].
      + change (NUL :: slack) with ([NUL] ++ slack). apply bytes_at_app. split.
        * apply bytes_at_write_same; cbn [length]; lia.
        * change (Z.of_nat (length [NUL])) with 1.
          apply bytes_at_write_other; [| lia | cbn [length]; lia | cbn [length]; lia].
          apply (bytes_at_transport rsegs [(phi, phi + Z.of_nat (length s))] m m1 _ _ HSLKB MU1).
          cbn [disjoint_from]. split; [lia | exact I]. }
  revert MH2. generalize (write_to_mem m1 (wa (phi + Z.of_nat (length s))) [NUL]) as m2. intros m2 MH2.
  clear HS.
  (* 0x12d40 mv a0,s0; jal strlen *)
  step. step.
  pose proof MH2 as (HB2 & _ & _ & MI2 & _).
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack).
    - rewrite unsigned_lit by lia. exact HB2.
    - exact HNN.
    - rewrite unsigned_lit by lia. exact HSLK.
    - exact MI2. }
  intros ms' Hpost. unfold strlen_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
                     E & MU3 & WM3 & MI3 & _).
  subst ms'. ret_even.
  pose proof (MemH_nil m2 m3 MH2 MU3 WM3 MI3) as MH3.
  (* 0x12d48 beqz a0 *)
  step. if_cases E0; zify_cond E0.
  - eapply z_ok; [exact MH3 | apply want_nil; lia].
  - (* 0x12d4c mv s2,zero; addi a1,zero,58 *)
    step. step.
    eapply (scan_ok (length s) 0); [lia | lia | lia | exact MH3].
Qed.

(** 0x12d1c .. 0x12d34: phi <> 0; memcpy(phi, src, k) when k <> 0. *)
Lemma head_ok : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  evt rsegs QM
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 src) (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12d1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6.
  pose proof (bytes_at_bound rsegs m src s HSRC) as BS.
  (* 0x12d1c beqz a0 *)
  step. if_cases E0; zify_cond E0; [exfalso; lia|].
  (* 0x12d20 mv s0,a0; beqz s1 *)
  step. step. if_cases E1; zify_cond E1.
  - (* k = 0 *)
    assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
    eapply nul_ok; [rewrite Hs; apply bytes_at_nil; lia | apply munch_refl | apply wmono_refl | exact HMI].
  - (* 0x12d28 mv a0,s0; mv a1,s2; mv a2,s1; jal memcpy *)
    step. step. step. step.
    eapply evt_cut.
    { eapply MCPY with (src := s) (junk := firstn (length s) junk); rewrite ?unsigned_lit by lia.
      - exact HSRC.
      - lia.
      - rewrite Nat2Z.id. exact (rw_cells_CB_prefix _ _ _ _ (length s) HBLK ltac:(lia)).
      - unfold or_h in HDJ. lia.
      - exact HMI. }
    intros ms' Hpost. unfold memcpy_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                       E & MU1 & WM1 & MI1 & CB1 & _).
    subst ms'. rewrite !unsigned_lit in MU1 by lia. rewrite !unsigned_lit in CB1 by lia.
    rewrite Nat2Z.id in CB1. ret_even.
    eapply nul_ok; [exact (rw_cells_CB_bytes _ _ _ _ CB1) | exact MU1 | exact WM1 | exact MI1].
Qed.

(** The contract's evt, with its postcondition spelled out. *)
Lemma mid_ok : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 PIN_JOIN) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + MID_OUT); (phi, phi + Z.of_nat (length s) + 1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 src) (Z_to_bv 64 fl) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PIN_MID) fc None m (seg_rom rsegs)).
Proof. intros. exact (head_ok ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6). Qed.

End Mid.
