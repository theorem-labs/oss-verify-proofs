(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpSess CmpSess2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRMB (cx : cctx) (ob on : Z) (dbza dbzfr : Z) (z : zstrm) (nin : Z) (p1 p2 : word) : list cell :=
  [C8 (Z_to_bv 64 nin); C4 (Z_to_bv 64 (z_avail_in z)); C4 (Z_to_bv 64 (z_tin_lo z)); C4 (Z_to_bv 64 (z_tin_hi z)); C4 p1;
   C8 (Z_to_bv 64 (ob + (on - z_avail_out z))); C4 (Z_to_bv 64 (z_avail_out z));
   C4 (Z_to_bv 64 (z_tout_lo z)); C4 (Z_to_bv 64 (z_tout_hi z)); C4 p2;
   C8 (Z_to_bv 64 (c_E cx)); C8 (Z_to_bv 64 dbza); C8 (Z_to_bv 64 dbzfr); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition strm_okB (cx : cctx) (usp : Z) : Prop :=
  usp <= c_bz cx + BZF_STRM /\ c_bz cx + BZF_STRM + 80 <= 2 ^ 64 /\ (c_bz cx + BZF_STRM) mod 8 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ci_stepF (e : est) (z : zstrm) : est * zstrm :=
  let '(e', z') := ci_step e z in (est_set_modes e' (e_mode e') (e_state e') (e_avail_in_expect e' - 1), z').

Lemma copy_input_S_fin : forall f e z p,
  copy_input (S f) e z p =
  if NBLOCKMAX <=? e_nblock e then (e, z, p) else
  if z_avail_in z =? 0 then (e, z, p) else
  if e_mode e =? BZ_M_RUNNING then let '(e1, z1) := ci_step e z in copy_input f e1 z1 true
  else if e_avail_in_expect e =? 0 then (e, z, p)
  else let '(e1, z1) := ci_stepF e z in copy_input f e1 z1 true.
Proof. intros. unfold ci_stepF. cbn [copy_input]. destruct (ci_step e z). reflexivity. Qed.

(* [comment removed for export] *)
Lemma ci_stepF_eq : forall e z c rest, z_in z = c :: rest ->
  ci_stepF e z = (let e' := est_set_rl e (add_char_to_block (est_rl e) c) in
                  est_set_modes e' (e_mode e') (e_state e') (e_avail_in_expect e' - 1), z_adv z rest).
Proof. intros e z c rest H. unfold ci_stepF. rewrite (ci_step_eq e z c rest H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma copy_input_S_finF : forall f e z p, e_mode e = BZ_M_FINISHING ->
  copy_input (S f) e z p =
  if NBLOCKMAX <=? e_nblock e then (e, z, p) else
  if z_avail_in z =? 0 then (e, z, p) else
  if e_avail_in_expect e =? 0 then (e, z, p)
  else copy_input f (fst (ci_stepF e z)) (snd (ci_stepF e z)) true.
Proof.
  intros f e z p M. rewrite copy_input_S_fin, M. cbn [Z.eqb BZ_M_FINISHING BZ_M_RUNNING Pos.eqb].
  destruct (ci_stepF e z). reflexivity.
Qed.

Lemma copy_input_modes : forall f e z p,
  e_mode (fst (fst (copy_input f e z p))) = e_mode e /\ e_state (fst (fst (copy_input f e z p))) = e_state e.
Proof.
  induction f as [|f IH]; intros e z p; cbn [copy_input]; [split; reflexivity|].
  destruct (NBLOCKMAX <=? e_nblock e); [split; reflexivity|]. destruct (z_avail_in z =? 0); [split; reflexivity|].
  destruct (e_mode e =? BZ_M_RUNNING).
  - destruct (ci_step e z) as [e1 z1] eqn:CI. rewrite (proj1 (IH _ _ _)), (proj2 (IH _ _ _)).
    unfold ci_step in CI. destruct (z_in z); [injection CI as <- <-; split; reflexivity|]. destruct (inc64 _ _). injection CI as <- <-. split; reflexivity.
  - destruct (e_avail_in_expect e =? 0); [split; reflexivity|].
    destruct (ci_step e z) as [e1 z1] eqn:CI. rewrite (proj1 (IH _ _ _)), (proj2 (IH _ _ _)). cbn [e_mode e_state est_set_modes].
    unfold ci_step in CI. destruct (z_in z); [injection CI as <- <-; split; reflexivity|]. destruct (inc64 _ _). injection CI as <- <-. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HCIB (cx : cctx) (on : Z) (g : eg) (e : est) (z : zstrm) : Prop :=
  est_ok e /\
  ((e_state_in_ch e = 256 /\ e_state_in_len e = 0) \/ (e_state_in_ch e < 256 /\ 1 <= e_state_in_len e)) /\
  zdefr (e_inUse e) 0 256 /\
  (* [comment removed for export] *)
  (e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = z_avail_in z) /\
  (* [comment removed for export] *)
  z_avail_in z = Z.of_nat (length (z_in z)) /\ z_avail_in z < 2147483648 /\
  0 <= z_avail_out z <= on /\ Z.of_nat (length (z_outr z)) = on - z_avail_out z /\
  (e_state e = BZ_S_OUTPUT ->
     g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) /\ e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE /\
     (forall k, 0 <= k < bw_numZ (e_bw e) -> zget (e_arr2 e) (e_nblock e + k) = zget (bw_zb (e_bw e)) k)) /\
  e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE.

Section HCIBacc.
  Variables (cx : cctx) (on : Z) (g : eg) (e : est) (z : zstrm).
  Hypothesis H : HCIB cx on g e z.
  Lemma HCIB_est_ok : est_ok e. Proof. exact (proj1 H). Qed.
  Lemma HCIB_rl : (e_state_in_ch e = 256 /\ e_state_in_len e = 0) \/ (e_state_in_ch e < 256 /\ 1 <= e_state_in_len e).
  Proof. exact (proj1 (proj2 H)). Qed.
  Lemma HCIB_inUse : zdefr (e_inUse e) 0 256. Proof. exact (proj1 (proj2 (proj2 H))). Qed.
  Lemma HCIB_mode : e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = z_avail_in z.
  Proof. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
  Lemma HCIB_avail_in : z_avail_in z = Z.of_nat (length (z_in z)) /\ z_avail_in z < 2147483648.
  Proof. pose proof H as H'. unfold HCIB in H'. tauto. Qed.
  Lemma HCIB_avail_out : 0 <= z_avail_out z <= on /\ Z.of_nat (length (z_outr z)) = on - z_avail_out z.
  Proof. pose proof H as H'. unfold HCIB in H'. tauto. Qed.
  Lemma HCIB_output : e_state e = BZ_S_OUTPUT ->
     g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) /\ e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE /\
     (forall k, 0 <= k < bw_numZ (e_bw e) -> zget (e_arr2 e) (e_nblock e + k) = zget (bw_zb (e_bw e)) k).
  Proof. pose proof H as H'. unfold HCIB in H'. tauto. Qed.
  Lemma HCIB_numZ : e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE.
  Proof. pose proof H as H'. unfold HCIB in H'. tauto. Qed.
End HCIBacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record hc_lawsB (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop) : Prop := HLB {
  hlB_hci : forall cx on g e z, HCXB cx on g e z -> HCIB cx on g e z;
  (* [comment removed for export] *)
  hlB_co : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> z_avail_out z <> 0 ->
            e_state_out_pos e < bw_numZ (e_bw e) -> HCXB cx on g (fst (co_step e z)) (snd (co_step e z));
  (* [comment removed for export] *)
  hlB_ci : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT ->
            e_nblock e < NBLOCKMAX -> z_avail_in z <> 0 -> HCXB cx on g (fst (ci_stepF e z)) (snd (ci_stepF e z));
  (* [comment removed for export] *)
  hlB_prep : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> bw_numZ (e_bw e) <= e_state_out_pos e ->
            (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e = false ->
            HCXB cx on g (hc_prep e) z;
  (* [comment removed for export] *)
  hlB_cbM : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e <> 0 -> NBLOCKMAX <= e_nblock e ->
            cb_pre g e /\ CBFACTS e /\ HCXB cx on (eg_after_cb cx g e) (hc_cbR e) z;
  (* [comment removed for export] *)
  hlB_cbF : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e = 0 ->
            cb_pre g (hc_flush e) /\ CBFACTS (hc_flush e) /\ HCXB cx on (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z;
  (* [comment removed for export] *)
  hlB_term : forall cx on g e z, HCXB cx on g e z -> hc_breaks (hc_fuel z) znew e z false false;
  (* [comment removed for export] *)
  hlB_cb_mode : forall e b, e_mode (fst (compressBlock e b znew)) = e_mode e
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pay_okB (cx : cctx) (ob on : Z) (nin n : Z) : Prop :=
  0 < nin /\ 0 <= n /\ nin + n <= CEIL /\
  apart nin n (c_E cx) ESTATE_SIZE /\ apart nin n (c_A1 cx) ARR1_SIZE /\ apart nin n (c_A2 cx) ARR2_SIZE /\
  apart nin n (c_FT cx) (4 * FTAB_WORDS) /\ apart nin n ob on.
Definition pay_condB (cx : cctx) (ob on : Z) (nin : Z) (pl : list byte) : Prop :=
  pl <> [] -> pay_okB cx ob on nin (Z.of_nat (length pl)).

(* [comment removed for export] *)
Definition out_okB (I : cimg) (cx : cctx) (ob on : Z) : Prop :=
  0 < ob /\ 0 < on /\ ob + on <= CEIL /\ on < 2147483648 /\
  apart ob on (c_E cx) ESTATE_SIZE /\ apart ob on (c_A1 cx) ARR1_SIZE /\ apart ob on (c_A2 cx) ARR2_SIZE /\
  apart ob on (c_FT cx) (4 * FTAB_WORDS) /\ img_apart (ci_hi I) ob on.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition handle_compress_WB (cx : cctx) (ob on usp : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
   (ob, ob + on); (c_bz cx + BZF_STRM, c_bz cx + BZF_STRM + 80); (usp - HC_STACK, usp)].
Lemma pay_disj_hcB : forall cx ob on nin n usp lo, pay_okB cx ob on nin n -> CEIL <= lo -> lo + HC_STACK <= usp -> usp <= c_bz cx + BZF_STRM ->
  disjoint_from (handle_compress_WB cx ob on usp) nin n.
Proof. intros cx ob on nin n usp lo P HL HS SA. unfold pay_okB, apart in P. unfold handle_compress_WB. cbn [disjoint_from]. bz_ceil; bz_params; unfold BZF_STRM, HC_STACK, CEIL in *. repeat split; lia. Qed.

(* [comment removed for export] *)
Definition hc_WlocB (cx : cctx) (ob on usp : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + 384); (c_E cx + 640, c_E cx + 672); (c_A2 cx, c_A2 cx + ARR2_SIZE);
   (ob, ob + on); (c_bz cx + BZF_STRM, c_bz cx + BZF_STRM + 80); (usp - HC_STACK, usp)].

Lemma erest_transportB : forall I cx ob on e sv m m' usp,
  hid (erest I cx e sv m) -> munch (hc_WlocB cx ob on usp) m m' -> wmono (ci_segs I) m m' ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> out_okB I cx ob on -> CEIL <= usp - HC_STACK -> usp <= c_bz cx + BZF_STRM ->
  I = S0C ->
  hid (erest I cx e sv m').
Proof.
  intros I cx ob on e sv m m' usp ER MU WM CX SEP IMG OOK LO SA HI. apply hid_e in ER. apply hid_i.
  unfold cctx_ok in CX; cbv zeta in CX. unfold cctx_sep, apart in SEP; cbv zeta in SEP. unfold cctx_img, img_apart in IMG.
  unfold out_okB, apart, img_apart in OOK.
  bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL, IMG_LO3, IMG_HI3, HC_STACK, BZF_STRM in *.
  cps_destruct CX as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & _).
  cps_destruct SEP as (S1 & S2 & S3 & _ & _ & S6 & S7 & _ & _ & S10 & _ & _ & _ & _ & _).
  cps_destruct IMG as (I1 & I2 & I3 & I4 & _ & _).
  cps_destruct OOK as (O1 & O2 & O3 & O4 & OE & OA1 & OA2 & OFT & OI).
  assert (HCI' : 0x10000 <= ci_got I /\ ci_got I + 32 <= ci_hi I /\ 0x10000 <= ci_stderrp I /\ ci_stderrp I + 8 <= ci_hi I /\
                 0x10000 <= ci_crc I /\ ci_crc I + 1024 <= ci_hi I /\ ci_hi I <= 0x68000).
  { subst I; cbn; lia. }
  cps_destruct HCI' as (G1 & G2 & G3 & G4 & G5 & G6 & G0).
  cps_destruct ER as (UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP & AR1 & FTB & (CM1 & CM2 & CM3 & CM4)).
  unfold erest, cimg_mem, hc_WlocB, BZF_STRM, HC_STACK.
  Local Ltac dj := unfold hc_WlocB, BZF_STRM, HC_STACK, FTAB_WORDS, ESTATE_SIZE; cbn [disjoint_from cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; lia.
  Local Ltac trE H MU WM := first [eapply u8arr_transport | eapply u32arr_transport]; [exact H| exact MU| exact WM|];
    rewrite ?ovb_length_nat, ?ovw_length_nat by lia.
  split. { trE UNS MU WM. clear - S2 OE RE1 RE2 LO SA. dj. } split. { trE MTF MU WM. clear - S2 OE RE1 RE2 LO SA. dj. }
  split. { trE SEL MU WM. clear - S2 OE RE1 RE2 LO SA. dj. } split. { trE SLM MU WM. clear - S2 OE RE1 RE2 LO SA. dj. }
  split. { trE LEN MU WM. clear - S2 OE RE1 RE2 LO SA. dj. } split. { trE COD MU WM. clear - S2 OE RE1 RE2 LO SA. dj. }
  split. { trE RFQ MU WM. clear - S2 OE RE1 RE2 LO SA. dj. } split. { trE LNP MU WM. clear - S2 OE RE1 RE2 LO SA. dj. }
  split. { eapply u8arr_transport; [exact AR1| exact MU| exact WM|]. rewrite zb8_length_nat by lia. clear - S1 S6 OA1 RA1 RA1' LO SA. dj. }
  split. { eapply u32arr_transport; [exact FTB| exact MU| exact WM|]. rewrite zw32_length_nat by lia. clear - S3 S10 OFT RFT RFT' LO SA. dj. }
  split. { eapply rw_cells_transport; [exact CM1| exact MU| exact WM|]. clear - I1 I3 OI O1 G1 G2 G0 LO SA RE1 RA2. dj. }
  split. { eapply rw_cells_transport; [exact CM2| exact MU| exact WM|]. clear - I1 I3 OI O1 G1 G2 G0 LO SA RE1 RA2. dj. }
  split. { eapply rw_cells_transport; [exact CM3| exact MU| exact WM|]. clear - I1 I3 OI O1 G3 G4 G0 LO SA RE1 RA2. dj. }
  eapply rw_cells_transport; [exact CM4| exact MU| exact WM|]. clear - I1 I3 OI O1 G5 G6 G0 LO SA RE1 RA2 HI.
  assert (SZ : Z.of_nat (cells_size (CB 1024 bz_crc_table_bytes :: ci_crcx I)) <= 1080 /\ ci_crc I + 1080 <= ci_hi I)
    by (subst I; cbn; lia).
  revert SZ. generalize (Z.of_nat (cells_size (CB 1024 bz_crc_table_bytes :: ci_crcx I))). intros sz SZ.
  unfold hc_WlocB, BZF_STRM, HC_STACK, FTAB_WORDS, ESTATE_SIZE; cbn [disjoint_from]. lia.
Qed.

Definition handle_compress_postB (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (segs : list Segment) (I : cimg) (cx : cctx)
    (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : zstrm)
    (nin : Z) (pl OB : list byte) (p1 p2 sv : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' g',
    let '(e', z', pr) := handle_compress znew e z in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if pr then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ emem cx segs g' e' m' /\ amem cx segs e' m' /\ cimg_mem I m' sv
    /\ rw_cells segs m' (c_bz cx + BZF_STRM) (STRMB cx ob on dbza dbzfr z' (nin + (z_avail_in z - z_avail_in z')) p1 p2)
    /\ u8arr segs m' ob (outb (z_outr z') OB)
    /\ u8ro segs m' nin pl
    /\ z_in z' = skipn (Z.to_nat (z_avail_in z - z_avail_in z')) (z_in z)
    /\ HCXB cx on g' e' z'.

Definition handle_compress_specB (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : zstrm)
         (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_bz cx + BZF_STRM) ->
  emem cx segs g e m -> amem cx segs e m -> cimg_mem I m sv ->
  rw_cells segs m (c_bz cx + BZF_STRM) (STRMB cx ob on dbza dbzfr z nin p1 p2) -> strm_okB cx (bv_unsigned sp) ->
  u8arr segs m ob OB -> Z.of_nat (length OB) = on -> out_okB I cx ob on ->
  u8ro segs m nin pl -> z_in z = map bv_unsigned pl -> pay_condB cx ob on nin pl ->
  z_outr z = [] -> z_avail_out z = on ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + HC_STACK <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> hc_lawsB HCXB CBFACTS -> HCXB cx on g e z ->
  evt segs (handle_compress_postB HCXB segs I cx ob on dbza dbzfr g e z nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo
              (handle_compress_WB cx ob on (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_handle_compress I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BZC_STACKB : Z := 16528.   (* [comment removed for export] *)
Definition bzCompress_WB (cx : cctx) (ob on usp : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
   (ob, ob + on); (c_bz cx + BZF_STRM, c_bz cx + BZF_STRM + 80); (usp - BZC_STACKB, usp)].
Lemma pay_disj_bzcB : forall cx ob on nin n usp lo, pay_okB cx ob on nin n -> CEIL <= lo -> lo + BZC_STACKB <= usp -> usp <= c_bz cx + BZF_STRM ->
  disjoint_from (bzCompress_WB cx ob on usp) nin n.
Proof. intros cx ob on nin n usp lo P HL HS SA. unfold pay_okB, apart in P. unfold bzCompress_WB. cbn [disjoint_from]. bz_ceil; bz_params; unfold BZF_STRM, BZC_STACKB, HC_STACK, CEIL in *. repeat split; lia. Qed.

Definition bzCompress_postB (segs : list Segment) (I : cimg) (cx : cctx) (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : zstrm)
    (nin : Z) (pl OB : list byte) (p1 p2 sv : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' g',
    let '(ret, e', z') := bzCompress znew e z BZ_FINISH in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ emem cx segs g' e' m' /\ amem cx segs e' m' /\ cimg_mem I m' sv
    /\ rw_cells segs m' (c_bz cx + BZF_STRM) (STRMB cx ob on dbza dbzfr z' (nin + (z_avail_in z - z_avail_in z')) p1 p2)
    /\ u8arr segs m' ob (outb (z_outr z') OB)
    /\ u8ro segs m' nin pl
    /\ (0 <= z_avail_out z' <= on /\ Z.of_nat (length (z_outr z')) = on - z_avail_out z')
    /\ est_ok e'.   (* [comment removed for export] *)

Definition bzCompress_specB (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop) (I : cimg) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (ob on dbza dbzfr : Z) (g : eg) (e : est) (z : zstrm)
         (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z),
  let segs := ci_segs I in
  a0 = Z_to_bv 64 (c_bz cx + BZF_STRM) -> a1 = Z_to_bv 64 BZ_FINISH ->
  (* [comment removed for export] *)
  e_mode e = BZ_M_RUNNING -> e_state e = BZ_S_INPUT ->
  z_avail_in z = Z.of_nat (length pl) -> z_outr z = [] -> z_avail_out z = on ->
  emem cx segs g e m -> amem cx segs e m -> cimg_mem I m sv ->
  rw_cells segs m (c_bz cx + BZF_STRM) (STRMB cx ob on dbza dbzfr z nin p1 p2) -> strm_okB cx (bv_unsigned sp) ->
  u8arr segs m ob OB -> Z.of_nat (length OB) = on -> out_okB I cx ob on ->
  u8ro segs m nin pl -> z_in z = map bv_unsigned pl -> pay_condB cx ob on nin pl ->
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> lo + BZC_STACKB <= bv_unsigned sp -> CEIL <= lo -> bv_unsigned sp mod 16 = 0 ->
  cctx_ok cx -> cctx_sep cx -> cctx_img I cx -> hc_lawsB HCXB CBFACTS ->
  (* [comment removed for export] *)
  HCXB cx on (eg_set_aie g) (e_finish e z) z ->
  evt segs (bzCompress_postB segs I cx ob on dbza dbzfr g e z nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo
              (bzCompress_WB cx ob on (bv_unsigned sp)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (ci_bzCompress I)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bzCompress_finish_runningB : forall lj e z, e_mode e = BZ_M_RUNNING ->
  bzCompress lj e z BZ_FINISH = let '(e', z', pr) := handle_compress lj (e_finish e z) z in bzc_finish_tail e' z' pr.
Proof.
  intros lj e z M. unfold bzCompress, e_finish, bzc_finish_tail. rewrite M.
  cbn [Z.eqb Pos.eqb BZ_M_RUNNING BZ_M_FINISHING BZ_M_IDLE BZ_M_FLUSHING BZ_FINISH BZ_RUN BZ_FLUSH negb e_avail_in_expect est_set_modes].
  rewrite Z.eqb_refl. cbn [negb]. destruct (handle_compress lj _ z) as [[e' z'] pr]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma strm_okB_frame : forall cx usp k, strm_okB cx usp -> 0 <= k -> strm_okB cx (usp - k).
Proof. (intros cx usp k; cps_intros (A & B & C); intros K). unfold strm_okB. split; [lia|]. split; [lia| exact C]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
