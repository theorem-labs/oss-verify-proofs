(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 MemRel DSLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Deflate TreeModel InflateState Inflate InflateRc InflateSync
     InflateInv InflateInvCall HarnessKit HarnessFacts HarnessSmallFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u DeflInst6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflCtx6 IRep6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Tgt_example_flush_fuzzer_ubsan.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition fl_dsp (q : dptrs) : ds_ptrs := DSP (dp_strm q) (dp_wnd q) (dp_prv q) (dp_hd q) (dp_pb q).

Definition DSIZES (s : deflate_state) : Prop :=
  ds_w_size s = 32768 /\ ds_hash_size s = 32768 /\ ds_lit_bufsize s = 16384
  /\ arr_len (ds_window s) = 65536 /\ arr_len (ds_prev s) = 32768 /\ arr_len (ds_head s) = 32768 /\ arr_len (ds_pending_buf s) = 65536.

Definition DRANGES (q : dptrs) : Prop :=
  0 <= dp_s q /\ dp_s q + FL_DSTATE_N <= 2 ^ 63 /\ 0 <= dp_wnd q /\ dp_wnd q + FL_DBLK_N <= 2 ^ 63
  /\ 0 <= dp_prv q /\ dp_prv q + FL_DBLK_N <= 2 ^ 63 /\ 0 <= dp_hd q /\ dp_hd q + FL_DBLK_N <= 2 ^ 63 /\ 0 <= dp_pb q /\ dp_pb q + FL_DBLK_N <= 2 ^ 63.

Definition FL_DREP (m : word -> option byte) (q : dptrs) (s : deflate_state) : Prop :=
  ds6u_scalars m (dp_s q) (fl_dsp q) s /\ ds6u_arrays m (dp_s q) s /\ tree_lens s
  /\ ds6u_windowA m (fl_dsp q) s /\ ds6u_prevA m (fl_dsp q) s /\ ds6u_headA m (fl_dsp q) s /\ ds6u_pendA m (fl_dsp q) s
  /\ DSIZES s /\ DRANGES q.

Definition IRANGES (q : iptrs) : Prop :=
  0 <= ip_p q /\ ip_p q + FL_ISTATE_N <= 2 ^ 63 /\ 0 <= ip_w q /\ ip_w q + FL_WIN_N <= 2 ^ 63.

Definition FL_IREP (m : word -> option byte) (q : iptrs) (s : inflate_state) : Prop :=
  ISREP6 m (ip_p q) (ip_strm q) (ip_w q) s /\ HEAD <= is_mode s <= SYNC /\ IRANGES q.

Definition FL_MSGA : Z -> Z := msg6_addr.
Lemma FL_MSGA_null : FL_MSGA MSG_NULL = 0.
Proof. reflexivity. Qed.

Definition FL_DS0 : deflate_state := ds0.
Definition FL_IS0 : inflate_state := is0 7.
Lemma FL_IS0_nowin : is_window_blk FL_IS0 = None.
Proof. vm_compute. reflexivity. Qed.

Definition FL_DPOST (ds : deflate_state) (f : Z) : Prop :=
  let X := fst (deflate_core ds f) in let rc := snd (deflate_core ds f) in
  0 <= rc <= 1 /\ 0 <= cs_next_in (ds_strm X) /\ 0 <= cs_avail_in (ds_strm X)
  /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = cs_next_in (ds_strm ds) + cs_avail_in (ds_strm ds).

Definition FL_DSAFE (ds : deflate_state) (f : Z) : Prop := DSAFE6u ds f /\ 0 <= f <= 4 /\ FL_DPOST ds f.

Definition LXS4 (s : inflate_state) : Prop :=
  (is_wrap s = 5 \/ is_wrap s = 1) /\ is_wbits s = 15 /\ live_mode (is_mode s)
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD)))
  /\ is_havedict s = 0
  /\ bk_ok (is_mode s) (is_back s).

Definition FL_ISAFE (s : inflate_state) (zc : ZCall) (f : Z) : Prop :=
  UI s /\ zcall_ok zc /\ LXS4 s /\ - 1 <= zs_msg (zc_strm zc) <= 27 /\ 0 <= f <= 4.


Definition cpl (b k : Z) : franges := [(0, b); (b + k, 2 ^ 64 - (b + k))].

Lemma agree_cpl : forall (m m' : word -> option byte) b k,
  (forall a : word, b <= bv_unsigned a < b + k -> m' a = m a) -> agree_out (cpl b k) m m'.
Proof.
  intros m m' b k H x Hx. apply H. pose proof (u64_range x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  unfold cpl, in_franges in Hx. lia.
Qed.

Lemma disj_cpl : forall b k P n, b <= P -> P + n <= b + k -> disj_franges (cpl b k) P n.
Proof. intros b k P n H1 H2 x Hx. unfold cpl, in_franges. lia. Qed.

Section Laws.
Let RS := RSX.

Lemma FL_DREP_strm : forall m q s cs, FL_DREP m q s -> FL_DREP m q (set_strm s cs).
Proof. intros m q s cs H. destruct s; exact H. Qed.
Lemma FL_DREP_strm' : forall m q s cs, FL_DREP m q (set_strm s cs) -> FL_DREP m q s.
Proof. intros m q s cs H. destruct s; exact H. Qed.

Local Ltac cag A := eapply (cells_agree_out s6u_segs _ _ _ _ _ _ _ _ A); [apply disj_cpl; cbn; lia | cbn; lia | lia | lia | assumption].

Lemma FL_DREP_frame : forall m m' q s, FL_DREP m q s ->
  (forall (a : word) b k, In (b, k) (dblocks q) -> b <= bv_unsigned a < b + k -> m' a = m a) -> FL_DREP m' q s.
Proof.
  intros m m' q s (Hsc & Har & Htl & Hw & Hp & Hh & Hb & Hsz & Hrg) Hag.
  pose proof Hsz as (Zws & Zhs & Zlbs & Lw & Lp & Lh & Lb).
  pose proof Hrg as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold FL_DSTATE_N, FL_DBLK_N in *.
  assert (AS : agree_out (cpl (dp_s q) 5968) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (dp_s q) 5968); [cbn; tauto | exact Ha]).
  assert (AW : agree_out (cpl (dp_wnd q) 65536) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (dp_wnd q) 65536); [cbn; tauto | exact Ha]).
  assert (AP : agree_out (cpl (dp_prv q) 65536) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (dp_prv q) 65536); [cbn; tauto | exact Ha]).
  assert (AH : agree_out (cpl (dp_hd q) 65536) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (dp_hd q) 65536); [cbn; tauto | exact Ha]).
  assert (AB : agree_out (cpl (dp_pb q) 65536) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (dp_pb q) 65536); [cbn; tauto | exact Ha]).
  split; [apply (ds6u_scalars_agree _ _ _ _ _ _ Hsc AS); [apply disj_cpl; unfold ds6u_SIZE; lia | lia | unfold ds6u_SIZE; lia]|].
  split.
  { unfold ds6u_arrays, dsl_arrays in *. destruct Har as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    repeat match goal with |- _ /\ _ => split end; cag AS. }
  split; [exact Htl|].
  unfold ds6u_windowA, ds6u_prevA, ds6u_headA, ds6u_pendA in *. cbn [fl_dsp p_window p_prev p_head p_pending_buf] in *.
  rewrite Lw, Lp, Lh, Lb in *.
  split; [cag AW|]. split; [cag AP|]. split; [cag AH|]. split; [cag AB|]. split; [exact Hsz | exact Hrg].
Qed.

Lemma FL_DREP_cells : forall m q s, FL_DREP m q s ->
  cell8 RS m (dp_s q) (dp_strm q) /\ cell4 RS m (dp_s q + 8) (ds_status s) /\ cell8 RS m (dp_s q + 16) (dp_pb q) /\
  cell8 RS m (dp_s q + 96) (dp_wnd q) /\ cell8 RS m (dp_s q + 112) (dp_prv q) /\ cell8 RS m (dp_s q + 120) (dp_hd q).
Proof.
  intros m q s (Hsc & _).
  pose proof (ds6u_strm _ _ _ _ Hsc) as C0. rewrite Z.add_0_r in C0.
  split; [exact C0|]. split; [exact (ds6u_status _ _ _ _ Hsc)|]. split; [exact (ds6u_pending_buf _ _ _ _ Hsc)|].
  split; [exact (ds6u_window _ _ _ _ Hsc)|]. split; [exact (ds6u_prev _ _ _ _ Hsc) | exact (ds6u_head _ _ _ _ Hsc)].
Qed.

Lemma FL_IREP_frame : forall m m' q s, FL_IREP m q s ->
  (forall (a : word) b k, In (b, k) (iblocks q) -> b <= bv_unsigned a < b + k -> m' a = m a) -> FL_IREP m' q s.
Proof.
  intros m m' q s ((Hsc & Hl & Hwk & Hc & Hwin & Hwb & Hwn) & Hmode & Hrg) Hag.
  pose proof Hrg as (R1 & R2 & R3 & R4). unfold FL_ISTATE_N, FL_WIN_N in *.
  assert (AS : agree_out (cpl (ip_p q) 7176) m m') by (apply agree_cpl; intros a Ha; apply (Hag a (ip_p q) 7176); [cbn; tauto | exact Ha]).
  split; [| split; [exact Hmode | exact Hrg]].
  split; [apply (is6_scalars_agree _ _ _ _ _ _ Hsc AS); [apply disj_cpl; unfold is6_SIZE; lia | lia | unfold is6_SIZE; lia]|].
  split; [cag AS|]. split; [cag AS|]. split; [cag AS|].
  split; [| split; [exact Hwb | exact Hwn]].
  intros HWB. specialize (Hwin HWB). rewrite (Hwn HWB) in *.
  assert (AW : agree_out (cpl (ip_w q) 32768) m m').
  { apply agree_cpl; intros a Ha; apply (Hag a (ip_w q) 32768); [| exact Ha].
    unfold iblocks. replace (ip_w q =? 0) with false by (symmetry; apply Z.eqb_neq; exact HWB). cbn. tauto. }
  cag AW.
Qed.

Lemma FL_IREP_cells : forall m q s, FL_IREP m q s ->
  cell8 RS m (ip_p q) (ip_strm q) /\ cell4 RS m (ip_p q + 8) (is_mode s) /\ 16180 <= is_mode s <= 16211 /\ cell8 RS m (ip_p q + 88) (ip_w q).
(* 1.4: state->window at 88 (1.3.1: 72), as fl_irep_cells in FlLibStmtU *)
Proof.
  intros m q s ((Hsc & _) & Hmode & _).
  pose proof (is6_strm _ _ _ _ Hsc) as C0. rewrite Z.add_0_r in C0. cbn [q_strm] in C0.
  split; [exact C0|]. split; [exact (is6_mode _ _ _ _ Hsc)|]. split; [unfold HEAD, SYNC in Hmode; exact Hmode|].
  exact (is6_window _ _ _ _ Hsc).
Qed.
End Laws.

Section IFACE.
Variable FL_TW : bvmap 5 word -> bvmap 5 word -> iptrs -> Z -> Z -> inflate_state -> ZCall -> Z -> (word -> option byte) -> Prop.
Variable FL_SSAFE : inflate_state -> ZCall -> Prop.

Hypothesis TW_LOCAL6 : forall (R0 RW : bvmap 5 word) q inp outp s zc f (M M' : word -> option byte),
      let sp := bv_unsigned (getr R0 2) in
      (forall a, (sp - FL_ZWD <= bv_unsigned a < sp \/ ip_p q <= bv_unsigned a < ip_p q + FL_ISTATE_N \/
                  ip_strm q <= bv_unsigned a < ip_strm q + 112 \/ outp <= bv_unsigned a < outp + zc_avail_out zc \/
                  inp <= bv_unsigned a < inp + zlength (zc_input zc)) -> M' a = M a) ->
      (forall a, sp - FL_FRA <= bv_unsigned a < sp - FL_ZWD -> M' a <> None) ->
      FL_TW R0 RW q inp outp s zc f M -> FL_TW R0 RW q inp outp s zc f M'.

Hypothesis L_DI6 : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (zc ra v16 v24 v32 : Z) (sv20 sv21 sv22 sv23 : word) (fa ff : Z),
    let h := dp_strm q - 8 in let s := dp_s q in
    getr regs 2 = Z_to_bv 64 (h - 80) -> getr regs 8 = Z_to_bv 64 (dp_strm q) -> getr regs 9 = Z_to_bv 64 s ->
    getr regs 10 = Z_to_bv 64 (dp_pb q) -> getr regs 18 = Z_to_bv 64 (s + 5888) ->
    getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 6 -> getr regs 21 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 8 ->
    h mod 16 = 0 -> zc + FL_FRA <= h -> h + 120 <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (dblocks q) -> all_apart (dblocks q) -> img_clear mem ->
    store_ok RSX mem (Z_to_bv 64 (h - FL_FRA)) (Z.to_nat (FL_FRA + 120)) = true ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RSX mem (dp_wnd q) FL_DBLK_N -> zeros_at RSX mem (dp_prv q) FL_DBLK_N -> zeros_at RSX mem (dp_hd q) FL_DBLK_N -> zeros_at RSX mem (dp_pb q) FL_DBLK_N ->
    zeros_at RSX mem (s + 12) 36 -> zeros_at RSX mem (s + 52) 4 -> zeros_at RSX mem (s + 64) 16 -> zeros_at RSX mem (s + 92) 4 ->
    zeros_at RSX mem (s + 104) 8 -> zeros_at RSX mem (s + 128) 4 -> zeros_at RSX mem (s + 148) 5748 -> zeros_at RSX mem (s + 5900) 52 ->
    zeros_at RSX mem (s + 5960) 8 ->
    cell8 RSX mem s (dp_strm q) -> cell4 RSX mem (s + 8) 42 -> cell4 RSX mem (s + 48) 1 -> cell8 RSX mem (s + 56) 0 ->
    cell4 RSX mem (s + 80) 32768 -> cell4 RSX mem (s + 84) 15 -> cell4 RSX mem (s + 88) 32767 ->
    cell8 RSX mem (s + 96) (dp_wnd q) -> cell8 RSX mem (s + 112) (dp_prv q) -> cell8 RSX mem (s + 120) (dp_hd q) ->
    cell4 RSX mem (s + 132) 32768 -> cell4 RSX mem (s + 136) 15 -> cell4 RSX mem (s + 140) 32767 -> cell4 RSX mem (s + 144) 5 ->
    cell4 RSX mem (s + 5896) 16384 -> cell8 RSX mem (s + 5952) 0 ->
    cell8 RSX mem (h - 8) ra -> cell8 RSX mem (h - 16) v16 -> cell8 RSX mem (h - 24) v24 -> cell8 RSX mem (h - 32) v32 -> cell8 RSX mem (h - 40) FL_DATALEN ->
    cellw RSX mem (h - 48) sv20 -> cellw RSX mem (h - 56) sv21 -> cellw RSX mem (h - 64) sv22 -> cellw RSX mem (h - 72) sv23 ->
    cell8 RSX mem (h + 56) 0 -> cell8 RSX mem (h + 64) s -> cell8 RSX mem (h + 72) fa -> cell8 RSX mem (h + 80) ff -> cell8 RSX mem (h + 88) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_DI) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (h - FL_FRA), FL_FRA) :: (Z_to_bv 64 (h + 8), 112) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 h
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32 /\ getr regs' 19 = Z_to_bv 64 FL_DATALEN
      /\ getr regs' 20 = sv20 /\ getr regs' 21 = sv21 /\ getr regs' 22 = sv22 /\ getr regs' 23 = sv23
      /\ rkeep regs regs' [3; 4; 24; 25; 26; 27]%bv
      /\ cell8 RSX mem' (h + 24) 0 /\ cell8 RSX mem' (h + 48) 0 /\ cell8 RSX mem' (h + 56) 0 /\ cell8 RSX mem' (h + 64) s
      /\ cell8 RSX mem' (h + 72) fa /\ cell8 RSX mem' (h + 80) ff /\ cell8 RSX mem' (h + 88) 0 /\ cell4 RSX mem' (h + 96) 2 /\ cell8 RSX mem' (h + 104) 1
      /\ FL_DREP mem' q FL_DS0.

Hypothesis L_DFL6 : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (s : deflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z),
    let ds := set_strm s (cstrm_of_call zc) in
    let X  := fst (deflate_core ds f) in let rc := snd (deflate_core ds f) in
    let nout := Z.of_nat (length (cs_out_rev (ds_strm X))) in
    getr regs 10 = Z_to_bv 64 (dp_strm q) -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (dblocks q) -> img_clear mem ->
    0 < dp_strm q -> dp_strm q + 112 <= 2 ^ 63 -> dp_strm q mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RSX mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true ->
    store_ok RSX mem (Z_to_bv 64 (dp_strm q)) 112%nat = true ->
    store_ok RSX mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: dblocks q) ->
    (forall a n, In (a, n) ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: dblocks q) -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 ->
    FL_DREP mem q s -> holds RSX mem inp (zc_input zc) ->
    zs_cells FL_MSGA mem (dp_strm q) inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) (dp_s q) fa ff ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    FL_DSAFE ds f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_DEFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_FRA), FL_FRA) :: (Z_to_bv 64 (dp_strm q), 112) :: (Z_to_bv 64 outp, nout) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 rc /\ 0 <= rc <= 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ FL_DREP mem' q X
      /\ 0 <= nout <= zc_avail_out zc /\ 0 <= cs_next_in (ds_strm X) <= zlength (zc_input zc)
      /\ zs_cells FL_MSGA mem' (dp_strm q) (inp + cs_next_in (ds_strm X)) (zlength (zc_input zc) - cs_next_in (ds_strm X))
                      (outp + nout) (zc_avail_out zc - nout)
                      (zr_strm (zret_of_cs (ds_strm X) rc)) (dp_s q) fa ff
      /\ holds RSX mem' outp (cs_output (ds_strm X)).

Hypothesis L_II6 : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (zc t ra v16 v24 v32 fa ff ni ai : Z),
    let p := ip_p q in let strm := ip_strm q in
    ip_w q = 0 ->
    getr regs 2 = Z_to_bv 64 (t - 32) -> getr regs 10 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 strm ->
    getr regs 9 = Z_to_bv 64 FL_ISTATE_N ->   (* 1.4 UBSan: as fl_ii in FlLibStmtU *)
    t mod 16 = 0 -> zc + FL_FRA <= t -> t <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (iblocks q) -> img_clear mem -> 0 < strm -> strm mod 8 = 0 -> strm + 112 <= 2 ^ 47 ->
    store_ok RSX mem (Z_to_bv 64 (t - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart [(t - FL_FRA, FL_FRA); (strm, 112); (p, FL_ISTATE_N)] -> (strm + 112 <= FL_RO_LO \/ FL_IMG_TOP <= strm) ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RSX mem p FL_ISTATE_N ->
    cell8 RSX mem (t - 8) ra -> cell8 RSX mem (t - 16) v16 -> cell8 RSX mem (t - 24) v24 -> cell8 RSX mem (t - 32) v32 ->
    cell8 RSX mem (strm + 48) 0 -> cell8 RSX mem (strm + 64) fa -> cell8 RSX mem (strm + 72) ff -> cell8 RSX mem (strm + 80) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    cell8 RSX mem strm ni -> cell4 RSX mem (strm + 8) ai ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_II) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' [(Z_to_bv 64 (t - FL_FRA), FL_FRA); (Z_to_bv 64 strm, 112); (Z_to_bv 64 p, FL_ISTATE_N)]
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32
      /\ rkeep regs regs' [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
      /\ cell8 RSX mem' (strm + 16) 0 /\ cell8 RSX mem' (strm + 40) 0 /\ cell8 RSX mem' (strm + 48) 0 /\ cell8 RSX mem' (strm + 56) p
      /\ cell8 RSX mem' (strm + 64) fa /\ cell8 RSX mem' (strm + 72) ff /\ cell8 RSX mem' (strm + 80) 0 /\ cell8 RSX mem' (strm + 96) 1
      /\ FL_IREP mem' q FL_IS0
      /\ cell8 RSX mem' strm ni /\ cell4 RSX mem' (strm + 8) ai.

Hypothesis L_INF6 : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z) (ans : option (blk * (Z -> Z))),
    let p := ip_p q in let strm := ip_strm q in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 47 -> strm mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RSX mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    store_ok RSX mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - FL_FRA, FL_FRA); (strm, 112); (outp, zc_avail_out zc); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 -> zc_avail_out zc < 2 ^ 31 -> zlength (zc_input zc) < 2 ^ 31 ->
    FL_IREP mem q s -> (ip_w q = 0 <-> is_window_blk s = None) -> holds RSX mem inp (zc_input zc) ->
    izs_cells FL_MSGA mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    FL_ISAFE s zc f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q))
      /\ match snd (inflate_p ivar_ref ans s zc f) with
         | None =>
             let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
             msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
             /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
             /\ (~ RR (zr_rc r) ->
                 nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
                 /\ FL_IREP mem' q s'
                 /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout)
                              (zr_strm r) p fa ff
                 /\ holds RSX mem' outp (zr_output r)
                 /\ (ip_w q = 0 <-> is_window_blk s' = None))
         | Some sz =>
             sz = FL_WIN_N /\ ip_w q = 0 /\
             msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 FL_A_ZW) mem' (seg_rom RSX))
             /\ getr regs' 13 = Z_to_bv 64 fa /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 FL_WIN_N /\ getr regs' 12 = Z_to_bv 64 1
             /\ getr regs' 2 = Z_to_bv 64 (sp - FL_ZWD) /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
             /\ FL_TW regs regs' q inp outp s zc f mem'
         end.

Hypothesis L_INB6 : forall (R0 RW regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff w : Z) (b : blk),
    let p := ip_p q in let strm := ip_strm q in let q' := IP strm p w in
    let ans := Some (b, fun _ => 0) in
    FL_TW R0 RW q inp outp s zc f mem -> rkeep RW regs FL_KEEP ->
    getr R0 2 = Z_to_bv 64 sp -> getr R0 1 = Z_to_bv 64 ra -> getr R0 11 = Z_to_bv 64 f ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 2 = Z_to_bv 64 (sp - FL_ZWD) ->
    zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> img_clear mem ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    blk_okz RSX mem FL_IMG_TOP zcl w FL_WIN_N -> zeros_at RSX mem w FL_WIN_N ->
    all_apart ((w, FL_WIN_N) :: (sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    snd (inflate_p ivar_ref ans s zc f) = Some FL_WIN_N ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_ZB) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ 0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q'))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep R0 regs' FL_KEEP
      /\ (~ RR (zr_rc r) ->
          nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
          /\ FL_IREP mem' q' s'
          /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout) (zr_strm r) p fa ff
          /\ holds RSX mem' outp (zr_output r)).

Hypothesis L_ISY6 : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall)
                  (sp ra inp outp zcl fa ff : Z),
    let p := ip_p q in let strm := ip_strm q in
    let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 63 -> strm mod 8 = 0 -> 0 < inp ->
    store_ok RSX mem (Z_to_bv 64 (sp - 96)) 96%nat = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart ((sp - 96, 96) :: (strm, 112) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - 96, 96); (strm, 112); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> zlength (zc_input zc) < 2 ^ 32 ->
    FL_IREP mem q s -> holds RSX mem inp (zc_input zc) ->
    izs_cells FL_MSGA mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    FL_SSAFE s zc ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_ISY) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 strm, 112) :: wz (iblocks q))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ zr_output r = [] /\ 0 <= zr_consumed r <= zlength (zc_input zc)
      /\ FL_IREP mem' q s'
      /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) p fa ff
      /\ (ip_w q = 0 <-> is_window_blk s' = None) .

Definition fl_lib_ok : fl_lib :=
  FL_LIB FL_DREP FL_IREP FL_TW FL_MSGA FL_MSGA_null FL_DSAFE FL_ISAFE FL_SSAFE FL_DS0 FL_IS0 FL_IS0_nowin
         FL_DREP_frame FL_IREP_frame FL_DREP_strm FL_DREP_strm' FL_DREP_cells FL_IREP_cells
         TW_LOCAL6 L_DI6 L_DFL6 L_II6 L_INF6 L_INB6 L_ISY6.

Lemma fl_ds0_eq : fl_ds0 fl_lib_ok = ds0.            Proof. reflexivity. Qed.
Lemma fl_is0_eq : fl_is0 fl_lib_ok = is0 7.          Proof. reflexivity. Qed.
Lemma fl_dsafe_eq : fl_dsafe fl_lib_ok = FL_DSAFE.   Proof. reflexivity. Qed.
Lemma fl_isafe_eq : fl_isafe fl_lib_ok = FL_ISAFE.   Proof. reflexivity. Qed.
Lemma fl_ssafe_eq : fl_ssafe fl_lib_ok = FL_SSAFE.   Proof. reflexivity. Qed.
End IFACE.
End FXG.
