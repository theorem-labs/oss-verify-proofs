(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 702 of its 749 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/pj_write.v, with its module paths and module names changed; 445 of its 495 lines of code are new or changed and 699 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition rm (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Lemma rm_refl : forall m, rm m m.
Proof. intros m x H. exact H. Qed.

Lemma rm_trans : forall m1 m2 m3, rm m1 m2 -> rm m2 m3 -> rm m1 m3.
Proof. intros m1 m2 m3 H1 H2 x H. exact (H2 x (H1 x H)). Qed.

Lemma write_keep : forall bs m a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate | exact H].
Qed.

Lemma rm_write : forall m a bs, rm m (write_to_mem m a bs).
Proof. intros m a bs x Hx. apply write_keep. exact Hx. Qed.

Lemma interp_rm : forall t m r, interp_eff_accesses rsegs t m = MachineOk r -> rm m (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn in H; try discriminate.
  - injection H as <-. cbn. apply rm_refl.
  - destruct (ov_read_bytes rsegs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses rsegs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    injection H as <-. cbn. exact (IH _ _ _ E).
  - destruct (store_ok rsegs m a (width_bytes n)) eqn:S; [|discriminate].
    destruct (interp_eff_accesses rsegs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:E;
      try discriminate.
    injection H as <-. cbn. eapply rm_trans; [|exact (IH _ _ E)].
    apply rm_write.
Qed.

Lemma decode_rm : forall st w r, decode_exec_accesses rsegs st w = MachineOk r ->
  rm (ms_mem st) (ms_mem (@access_value _ r)).
Proof.
  intros st w r H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - injection H as <-. cbn. apply rm_refl.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses rsegs _ (ms_mem st)) as [rep| |] eqn:E; try discriminate.
    pose proof (interp_rm _ _ _ E) as K.
    destruct (@access_value _ rep) as [c m'] eqn:E2. cbn in K.
    injection H as <-. cbn. exact K.
Qed.

Lemma fetch_failure_not_ok : forall m a x, fetch_failure rsegs m a <> MachineOk x.
Proof.
  intros m a x. unfold fetch_failure. cbv zeta.
  destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma step_rm : forall ms ms', RiscvSemantics.step rsegs ms = MachineOk ms' -> rm (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. unfold RiscvSemantics.step, RiscvSemantics.step_accesses in H.
  destruct (fetch_word rsegs (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses rsegs ms w) as [rep| |] eqn:E; cbn in H; try discriminate.
    injection H as <-. exact (decode_rm _ _ _ E). }
  destruct (fetch_word_ov rsegs (ms_mem ms) (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses rsegs ms w) as [rep| |] eqn:E; cbn in H; try discriminate.
    injection H as <-. exact (decode_rm _ _ _ E). }
  destruct (fetch_tail_any rsegs (ms_mem ms) (ms_pc ms)) as [w|].
  { destruct (decode_exec_accesses rsegs ms w) as [rep| |] eqn:E; cbn in H; try discriminate.
    injection H as <-. exact (decode_rm _ _ _ E). }
  destruct (fetch_failure rsegs (ms_mem ms) (ms_pc ms)) as [st| |] eqn:E; cbn in H; try discriminate.
  exfalso. exact (fetch_failure_not_ok _ _ _ E).
Qed.

Lemma msteps_rm : forall ms ms', Exec.msteps rsegs ms ms' -> rm (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 [_ HS] _ IH]; [apply rm_refl|].
  exact (rm_trans _ _ _ (step_rm _ _ HS) IH).
Qed.

Lemma evt_rm : forall (Q : machine_state -> Prop) ms,
  Exec.evt rsegs Q ms -> Exec.evt rsegs (fun x => Q x /\ rm (ms_mem ms) (ms_mem x)) ms.
Proof.
  intros Q ms (ms' & HS & HQ). exists ms'. split; [exact HS|]. split; [exact HQ|]. exact (msteps_rm _ _ HS).
Qed.

Definition IMG_TOP : Z := 0x60000.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_TOP) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_top : forall segs a n seg,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_TOP) segs = true ->
  find_segment segs a n = Some seg -> a + n <= IMG_TOP.
Proof.
  induction segs as [|s segs IH]; intros a n seg H E; cbn in E; [discriminate|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:C.
  - apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C2. lia.
  - exact (IH a n seg H2 E).
Qed.

Lemma find_segment_rsegs_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= IMG_TOP.
Proof. intros a n seg. apply find_segment_top. exact rsegs_top. Qed.

Lemma find_segment_hi : forall a, IMG_TOP <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a H. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  apply find_segment_rsegs_top in E. lia.
Qed.

Lemma wview_hi : forall m a, IMG_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a H. unfold wview. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by (unfold IMG_TOP in *; lia). rewrite find_segment_hi by lia. reflexivity.
Qed.

Lemma writable_hi_some : forall m a, IMG_TOP <= a < 2 ^ 64 -> writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a H W. unfold writable_at in W. rewrite wview_hi in W by exact H.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma stk_hi : forall m lo hi, IMG_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. unfold IMG_TOP in Hlo. split; [lia|]. split; [lia|]. intros a Ha. split.
  - exact (H a Ha).
  - destruct (writable_hi_some m a ltac:(unfold IMG_TOP; lia) (H a Ha)) as [b Hb].
    exists b. unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma ro_addr_low : forall a, ro_addr rsegs (wa a) = true -> 0 <= a -> a < 2 ^ 64 -> a + 1 <= IMG_TOP.
Proof.
  intros a H H0 H1. unfold ro_addr in H. rewrite wa_unsigned in H by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|discriminate].
  exact (find_segment_rsegs_top _ _ _ E).
Qed.

Lemma fs_some : forall segs a n s, find_segment segs a n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 segs IH]; intros a n s H; cbn in H; [discriminate|].
  destruct (Z.of_N (seg_base s0) <=? a) eqn:E1; destruct (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) eqn:E2;
    cbn in H;
    try (destruct (IH _ _ _ H) as (I1 & I2 & I3); split; [right; exact I1 | split; assumption]).
  inversion H; subst. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | split; assumption].
Qed.

Lemma rsegs_seg_top : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= IMG_TOP.
Proof. intros s H. pose proof rsegs_top as T. rewrite forallb_forall in T. apply Z.leb_le. exact (T s H). Qed.

Lemma ro_unsigned_low : forall x, ro_addr rsegs x = true -> 0 <= bv_unsigned x /\ bv_unsigned x + 1 <= IMG_TOP.
Proof.
  intros x H. pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  split; [lia|]. apply ro_addr_low; [|lia|lia]. unfold wa. rewrite Z_to_bv_bv_unsigned. exact H.
Qed.

Lemma ro_false_hi : forall a, IMG_TOP <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (ro_addr_low a E ltac:(unfold IMG_TOP in Ha; lia) ltac:(lia)). lia.
Qed.

Lemma ro_munch_hi : forall lo hi m m', ro_agree rsegs m -> munch [(lo, hi)] m m' -> IMG_TOP <= lo -> ro_agree rsegs m'.
Proof.
  intros lo hi m m' RO MU Hlo. apply (ro_agree_same rsegs m m' RO). intros x Hx. apply MU.
  pose proof (ro_unsigned_low x Hx). cbn [outside]. split; [lia | exact I].
Qed.

Lemma nth_Z_to_le : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma le_byte_bv : forall v w k, Z_to_bv 8 (le_byte v w k) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)).
Proof. intros. unfold le_byte. apply Z_to_bv8_mod. apply Z.mod_mod. lia. Qed.

Lemma mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. reflexivity. Qed.

Lemma word_mem_iff : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (word_mem rsegs m a v <-> bytes_at rsegs m a (le8 (Z_to_bv 64 v))).
Proof.
  intros m a v Ha Hb. unfold word_mem. split.
  - intros H. split; [lia|]. split; [rewrite length_le8; lia|].
    intros i Hi. rewrite length_le8 in Hi. rewrite <- mbyte_mrd, H by exact Hi.
    unfold le8, word_to_le_bytes. rewrite nth_Z_to_le by exact Hi. rewrite le_byte_bv.
    rewrite Z_to_bv_unsigned. reflexivity.
  - intros (_ & _ & H) k Hk. rewrite mbyte_mrd, H by (rewrite length_le8; exact Hk).
    unfold le8, word_to_le_bytes. rewrite nth_Z_to_le by exact Hk. rewrite le_byte_bv.
    rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma le4_byte : forall v k, (k < 4)%nat ->
  Z_to_bv 8 (Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat 4)) (8 * Z.of_nat k)).
Proof.
  intros v k Hk. apply Z_to_bv8_mod. change (8 * Z.of_nat 4) with 32.
  rewrite !shiftr_mod_mod8 by lia. reflexivity.
Qed.

Lemma zbytes_core : forall m a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ((forall i, 0 <= i < Z.of_nat (length l) -> mbyte rsegs m (a + i) = Some (Z_to_bv 8 (nth (Z.to_nat i) l 0))) <->
   bytes_at rsegs m a (map (Z_to_bv 8) l)).
Proof.
  intros m a l Ha Hb. split.
  - intros H. split; [lia|]. split; [rewrite length_map; lia|].
    intros i Hi. rewrite length_map in Hi. rewrite <- mbyte_mrd, H by lia.
    rewrite nth_error_map, (nth_error_nth' l 0) by exact Hi. rewrite Nat2Z.id. reflexivity.
  - intros (_ & _ & H) i Hi. rewrite mbyte_mrd.
    replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
    rewrite H by (rewrite length_map; lia).
    rewrite nth_error_map, (nth_error_nth' l 0) by lia. reflexivity.
Qed.

Lemma eqv_getr : forall R F pc fc rv m ro x r, ms_eqv (MS R F pc fc rv m ro) x -> getr (ms_regs x) r = getr R r.
Proof.
  intros R F pc fc rv m ro x r (HR & _). unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  cbn in HR. symmetry. apply HR. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma seg_rom_same : forall segs, YK11.seg_rom segs = PropExec.seg_rom segs.
Proof. intros. unfold YK11.seg_rom, PropExec.seg_rom. reflexivity. Qed.

Section F.
Context {fx : FPState}.

Lemma eqv_shape : forall R pc m x,
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (PropExec.seg_rom rsegs)) x ->
  x = @YK11.mkst fx (ms_regs x) pc m (YK11.seg_rom rsegs).
Proof using.
  intros R pc m x (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  rewrite seg_rom_same. unfold mkst.
  destruct x; cbn in *; subst. reflexivity.
Qed.

Lemma kA_lift : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem (PropExec.seg_rom rsegs)) ->
  (forall x y, Q y -> ms_eqv y x -> rm mem (ms_mem x) -> SR rsegs (mkCfg x md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof using.
  intros regs pc mem md Q P Hh Hl HE K.
  apply (evt_SR_canon rsegs (@YK11.mkst fx regs pc mem (YK11.seg_rom rsegs)) (fun x => Q x /\ rm mem (ms_mem x)) md P);
    [| exact Hh | exact Hl |].
  - replace (canonical_register_state (@YK11.mkst fx regs pc mem (YK11.seg_rom rsegs)))
      with (MS (mkR_of regs) (@fp_regs fx) pc (@fp_csr fx) None mem (PropExec.seg_rom rsegs))
      by (unfold canonical_register_state, YK11.mkst, MS; cbn; rewrite ?seg_rom_same; reflexivity).
    exact (evt_rm Q _ HE).
  - intros ms' (can & [HQ HR] & HEQ). apply (K ms' can HQ HEQ).
    destruct HEQ as (_ & _ & _ & _ & _ & _ & HM & _). rewrite <- HM. exact HR.
Qed.

End F.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [right; lia | left; split; [lia|exact H] ..].
Qed.

Lemma pairwise_In : forall {T} (R : T -> T -> Prop) l a b, pairwise R l -> In a l -> In b l -> a <> b -> R a b \/ R b a.
Proof.
  intros T R l. induction l as [|x l IH]; intros a b H Ha Hb Hne; [destruct Ha|].
  destruct H as [H1 H2]. destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb].
  - congruence.
  - left. apply H1, Hb.
  - right. apply H1, Ha.
  - exact (IH a b H2 Ha Hb Hne).
Qed.

Lemma pairwise_mid : forall {T} (R : T -> T -> Prop) l1 e l2 f, pairwise R (l1 ++ e :: l2) -> In f (l1 ++ l2) -> R e f \/ R f e.
Proof.
  intros T R l1. induction l1 as [|x l1 IH]; intros e l2 f H Hf; cbn in *.
  - destruct H as [H1 _]. left. apply H1, Hf.
  - destruct H as [H1 H2]. destruct Hf as [<-|Hf].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH e l2 f H2 Hf).
Qed.

Lemma raw_mbyte : forall segs m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold mbyte, writable_at, wview. rewrite H. tauto. Qed.

Lemma munch_raw : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha Ho. apply H. rewrite unsigned_lit by lia. exact Ho. Qed.

Lemma present_rm : forall m m' a, rm m m' -> present m a -> present m' a.
Proof.
  intros m m' a H (b & Hb). unfold present. destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply (H (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
Qed.

Lemma reserved_top : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? IMG_TOP) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma model_eta : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros [fd [h lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma ceil_big : forall {rc : RunCeil}, IMG_TOP < alloc_ceiling < 2 ^ 47.
Proof. intros rc. pose proof alloc_ceiling_val. pose proof alloc_ceiling_lt. unfold IMG_TOP. lia. Qed.

Section KB.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Let MR := aa_MR API.

Lemma scratch_dec : forall stk regs a, scratch_k B stk regs a \/ ~ scratch_k B stk regs a.
Proof using.
  intros stk regs a. unfold scratch_k.
  destruct (Z_le_gt_dec (spZ regs - stk) a); destruct (Z_lt_ge_dec a (spZ regs));
  destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4));
  first [left; lia | right; lia].
Qed.

Lemma in_img_low : forall a, in_img B a -> 0 <= a < IMG_TOP.
Proof using SEGS.
  intros a (_ & s & Hs & Ha). rewrite SEGS in Hs. pose proof reserved_top as T.
  rewrite forallb_forall in T. specialize (T s Hs). apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). pose proof (bv_unsigned_in_range 64 (snd s)). unfold IMG_TOP in *. lia.
Qed.

Lemma blocks_user : forall L A x k, In (x, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = x.
Proof using.
  intros L A x k H. unfold blocks in H. apply in_map_iff in H. destruct H as ([q n] & E & Hq).
  cbn in E. injection E as <- <-. exists q. split; [exact Hq | reflexivity].
Qed.

Lemma block_facts : forall L A mem md x k i, MR L A mem md -> In (x, k) (blocks L A) -> 0 <= i < k ->
  present mem (x + i) /\ 4096 <= x /\ x + k <= alloc_ceiling /\ ~ owned B L A (x + i).
Proof using API.
  intros L A mem md x k i HM Hin Hi. destruct (blocks_user L A x k Hin) as (q & Hq & <-).
  exact (mr_blocks _ _ (aa_laws API) _ _ _ _ q k i HM Hq Hi).
Qed.

Lemma block_range : forall L A mem md x k, MR L A mem md -> In (x, k) (blocks L A) -> 4096 <= x /\ x + k <= alloc_ceiling.
Proof using API.
  intros L A mem md x k HM Hin. destruct (blocks_user L A x k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq).
Qed.

Lemma blocks_disj : forall L A mem md x k y j, MR L A mem md -> In (x, k) (blocks L A) -> In (y, j) (blocks L A) ->
  x <> y -> x + k <= y \/ y + j <= x.
Proof using API.
  intros L A mem md x k y j HM Hx Hy Hne. pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as P.
  destruct (pairwise_In _ _ _ _ P Hx Hy ltac:(congruence)) as [H|H]; unfold ranges_disjoint in H; cbn in H; lia.
Qed.

Lemma owned_low : forall L A mem md a, MR L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof using API. intros L A mem md a HM H. exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM H). Qed.

Lemma ro_in_img : forall z, 0 <= z < 2 ^ 64 -> ro_addr rsegs (wa z) = true -> in_img B z.
Proof using SEGS.
  intros z Hz H. unfold ro_addr in H. rewrite wa_unsigned in H by lia.
  destruct (find_segment rsegs z 1) as [s|] eqn:F; [|discriminate].
  destruct (fs_some _ _ _ _ F) as (Hin & H1 & H2). pose proof (rsegs_seg_top s Hin) as T. unfold IMG_TOP in T.
  unfold in_img. rewrite SEGS.
  split; [intros E; rewrite E in Hin; exact Hin|].
  exists (segment_reservation s). split; [apply in_map; exact Hin|].
  unfold segment_reservation. cbn [fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold page_round_down_Z, page_round_up_Z, page_size.
  rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma ro_false_noimg : forall z, 0 <= z < 2 ^ 64 -> ~ in_img B z -> ro_addr rsegs (wa z) = false.
Proof using SEGS.
  intros z Hz H. destruct (ro_addr rsegs (wa z)) eqn:E; [|reflexivity]. exfalso. exact (H (ro_in_img z Hz E)).
Qed.

Lemma got_low : forall L A mem md i, MR L A mem md -> 0 <= i < 8 ->
  owned B L A (ms_got_guard B + i) /\ 0 <= ms_got_guard B + i < alloc_ceiling.
Proof using API.
  intros L A mem md i HM Hi.
  assert (Ho : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
  split; [exact Ho | exact (owned_low L A mem md _ HM Ho)].
Qed.

Lemma guard_munch : forall L A mem0 md W m m', MR L A mem0 md -> munch W m m' ->
  (forall i, 0 <= i < 8 -> outside W (ms_got_guard B + i)) -> guard_kept B m m'.
Proof using API.
  intros L A mem0 md W m m' HM MU HO. unfold guard_kept. intros i Hi.
  destruct (got_low L A mem0 md i HM Hi) as [_ G]. pose proof ceil_big as CB. unfold IMG_TOP in CB.
  exact (proj1 (raw_mbyte (ms_segs B) m m' (ms_got_guard B + i)
    (munch_raw W m m' (ms_got_guard B + i) MU ltac:(lia) (HO i Hi)))).
Qed.

Lemma guard_trans : forall m1 m2 m3, guard_kept B m1 m2 -> guard_kept B m2 m3 -> guard_kept B m1 m3.
Proof using. intros m1 m2 m3 H1 H2. unfold guard_kept in *. intros i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.

Lemma mr_munch : forall L A mem md W mem', MR L A mem md -> munch W mem mem' -> rm mem mem' ->
  (forall a, owned B L A a -> outside W a) -> MR L A mem' md.
Proof using API.
  intros L A mem md W mem' HM MU RM OW.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ho. pose proof (owned_low _ _ _ _ _ HM Ho). pose proof ceil_big.
    apply raw_mbyte. apply (munch_raw W); [exact MU | unfold IMG_TOP in *; lia | exact (OW a Ho)].
  - intros a _ Hp. exact (present_rm _ _ _ RM Hp).
  - intros p n i Hp Hi. apply (present_rm _ _ _ RM). exact (proj1 (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi)).
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Lemma post_nocall : forall K E gone L A regs mem md W mem' regs',
  call_pre_k B MR K L A regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> rm mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (spZ regs - K <= x < spZ regs) \/ E x) ->
  (forall a, owned B L A a -> outside W a) ->
  regs_preserved regs regs' ->
  call_post_e B API K L A regs mem md E gone L A regs' mem' md.
Proof using SEGS.
  intros K E gone L A regs mem md W mem' regs' PRE MU WM RM WS OW RP.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof ceil_big as CB. unfold IMG_TOP in CB. rewrite <- SEGS in WM.
  unfold call_post_e.
  split; [exact (mr_munch _ _ _ _ _ _ HM MU RM OW)|].
  split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [intros p n0 Hp _; split; [exact Hp | reflexivity]|]. split; [exact RP|].
  split; [exists (m_vmmaps md); apply model_eta|].
  split.
  { intros a Hr Ho1 Ho2 Hs He.
    assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low a Hr); unfold IMG_TOP in *; lia]).
    destruct (outside_dec W a) as [Out|NOut].
    - apply raw_mbyte. exact (munch_raw W mem mem' a MU Ra Out).
    - exfalso. destruct (WS a Ra NOut) as [Hst|HE]; [apply Hs; left; exact Hst | exact (He HE)]. }
  split.
  { intros p n i Hp1 Hp2 Hi He.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp1 Hi) as (_ & R1 & R2 & _).
    destruct (outside_dec W (ptr_addr L p + i)) as [Out|NOut].
    - apply raw_mbyte. apply (munch_raw W); [exact MU | lia | exact Out].
    - exfalso. destruct (WS (ptr_addr L p + i) ltac:(lia) NOut) as [Hst|HE]; [lia | exact (He HE)]. }
  intros a [Hs|Hs]; apply WM; [apply HWs | apply HWe]; exact Hs.
Qed.

Lemma post_call : forall K E gone L A regs mem md W1 mem1 regs1 K2 E2 L' A' regs2 mem2 md' W3 mem3 regs3 gk,
  call_pre_k B MR K L A regs mem md ->
  munch W1 mem mem1 -> wmono rsegs mem mem1 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W1 x -> (spZ regs - K <= x < spZ regs) \/ E x) ->
  spZ regs - K <= spZ regs1 - K2 -> spZ regs1 <= spZ regs ->
  (forall a, E2 a -> E a) -> (forall a, E2 a -> a < alloc_ceiling) ->
  call_post_k B MR K2 L A regs1 mem1 md E2 L' A' regs2 mem2 md' -> ublocks_kept L A A' (gone, gk) ->
  munch W3 mem2 mem3 -> wmono rsegs mem2 mem3 -> rm mem2 mem3 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W3 x -> (spZ regs - K <= x < spZ regs) \/ E x) ->
  (forall a, owned B L' A' a -> outside W3 a) ->
  regs_preserved regs regs3 ->
  call_post_e B API K L A regs mem md E gone L' A' regs3 mem3 md'.
Proof using SEGS.
  intros K E gone L A regs mem md W1 mem1 regs1 K2 E2 L' A' regs2 mem2 md' W3 mem3 regs3 gk
    PRE MU1 WM1 WS1 SK1 SK2 EE EL POST UK MU3 WM3 RM3 WS3 OW3 RP.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof POST as (HM2 & HWF2 & HB2 & HLL & HPT & HRP2 & HMD & HFR & HBK & HSW).
  pose proof ceil_big as CB. unfold IMG_TOP in CB. rewrite <- SEGS in WM1, WM3.
  unfold call_post_e.
  split; [exact (mr_munch _ _ _ _ _ _ HM2 MU3 RM3 OW3)|].
  split; [exact HWF2|]. split; [exact HB2|]. split; [exact HLL|].
  split; [intros p n0 Hp Hg; pose proof (UK p n0 Hp (fun E0 => Hg (f_equal fst E0))) as Hp';
    split; [exact Hp' | exact (HPT p n0 Hp Hp')]|].
  split; [exact RP|].
  split; [destruct HMD as [vm' ->]; exists vm'; reflexivity|].
  split.
  { intros a Hr Ho1 Ho2 Hs He.
    assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low a Hr); unfold IMG_TOP in *; lia]).
    assert (O1 : outside W1 a).
    { destruct (outside_dec W1 a) as [Out|NOut]; [exact Out|].
      exfalso. destruct (WS1 a Ra NOut) as [Hst|HE]; [apply Hs; left; exact Hst | exact (He HE)]. }
    assert (O3 : outside W3 a).
    { destruct (outside_dec W3 a) as [Out|NOut]; [exact Out|].
      exfalso. destruct (WS3 a Ra NOut) as [Hst|HE]; [apply Hs; left; exact Hst | exact (He HE)]. }
    destruct (HFR a Hr Ho1 Ho2) as [F1 F2].
    { intros [Hs'|Hs']; apply Hs; [left; lia | right; exact Hs']. }
    { intros HE2. exact (He (EE a HE2)). }
    destruct (raw_mbyte (ms_segs B) mem mem1 a (munch_raw W1 mem mem1 a MU1 Ra O1)) as [G1 G2].
    destruct (raw_mbyte (ms_segs B) mem2 mem3 a (munch_raw W3 mem2 mem3 a MU3 Ra O3)) as [G3 G4].
    split; [congruence|]. split; intros HW.
    - exact (proj1 G4 (proj1 F2 (proj1 G2 HW))).
    - exact (proj2 G2 (proj2 F2 (proj2 G4 HW))). }
  split.
  { intros p n i Hp1 Hp2 Hi He.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp1 Hi) as (_ & R1 & R2 & _).
    assert (O1 : outside W1 (ptr_addr L p + i)).
    { destruct (outside_dec W1 (ptr_addr L p + i)) as [Out|NOut]; [exact Out|].
      exfalso. destruct (WS1 (ptr_addr L p + i) ltac:(lia) NOut) as [Hst|HE]; [lia | exact (He HE)]. }
    assert (O3 : outside W3 (ptr_addr L p + i)).
    { destruct (outside_dec W3 (ptr_addr L p + i)) as [Out|NOut]; [exact Out|].
      exfalso. destruct (WS3 (ptr_addr L p + i) ltac:(lia) NOut) as [Hst|HE]; [lia | exact (He HE)]. }
    pose proof (HBK p n i Hp1 Hp2 Hi) as K2'.
    destruct (raw_mbyte (ms_segs B) mem mem1 _ (munch_raw W1 mem mem1 (ptr_addr L p + i) MU1 ltac:(lia) O1)) as [G1 _].
    destruct (raw_mbyte (ms_segs B) mem2 mem3 _ (munch_raw W3 mem2 mem3 (ptr_addr L p + i) MU3 ltac:(lia) O3)) as [G3 _].
    congruence. }
  intros a Hs. apply WM3.
  assert (W0 : writable_at (ms_segs B) mem1 a) by (apply WM1; destruct Hs as [Hs|Hs]; [apply HWs | apply HWe]; exact Hs).
  destruct (scratch_dec K2 regs1 a) as [S2|S2]; [exact (HSW a S2)|].
  destruct Hs as [Hs|Hs]; [|exfalso; apply S2; right; exact Hs].
  assert (NO1 : ~ owned B L A a) by (intros Ho; pose proof (owned_low _ _ _ _ _ HM Ho); lia).
  assert (NO2 : ~ owned B L' A' a) by (intros Ho; pose proof (owned_low _ _ _ _ _ HM2 Ho); lia).
  assert (NE2 : ~ E2 a) by (intros HE2; pose proof (EL a HE2); lia).
  destruct (HFR a ltac:(left; lia) NO1 NO2 S2 NE2) as [_ F2]. exact (proj1 F2 W0).
Qed.

Lemma keeps_munch : forall L A m0 md mem W mem' gone, MR L A m0 md -> munch W mem mem' ->
  (forall a k i, In (a, k) (blocks L A) -> a <> gone -> 0 <= i < k -> outside W (a + i)) ->
  keeps B L A mem mem' gone.
Proof using API.
  intros L A m0 md mem W mem' gone HM MU H a k i Hin Hne Hi.
  destruct (block_range _ _ _ _ _ _ HM Hin) as [R1 R2]. pose proof ceil_big. unfold IMG_TOP in *.
  apply raw_mbyte. apply (munch_raw W); [exact MU | lia | exact (H a k i Hin Hne Hi)].
Qed.

Lemma keeps_trans : forall L A m1 m2 m3 gone, keeps B L A m1 m2 gone -> keeps B L A m2 m3 gone -> keeps B L A m1 m3 gone.
Proof using. intros L A m1 m2 m3 gone H1 H2 a k i Hin Hne Hi. rewrite (H2 a k i Hin Hne Hi). exact (H1 a k i Hin Hne Hi). Qed.

Lemma word_mem_munch : forall W m m' a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall k, 0 <= k < 8 -> outside W (a + k)) -> word_mem (ms_segs B) m a v -> word_mem (ms_segs B) m' a v.
Proof using.
  intros W m m' a v MU Ha Hb HO H k Hk. rewrite <- (H k Hk).
  apply raw_mbyte. apply (munch_raw W); [exact MU | lia | apply HO; lia].
Qed.

Lemma ledger_munch : forall L A mem md Lam peak cnt fail W mem', MR L A mem md ->
  ledger B L A mem Lam peak cnt fail -> munch W mem mem' ->
  (forall a, alloc_statics a -> outside W a) ->
  (forall x k i, In (x, k) Lam -> 0 <= i < 16 -> outside W (x - 16 + i)) ->
  ledger B L A mem' Lam peak cnt fail.
Proof using API.
  intros L A mem md Lam peak cnt fail W mem' HM HL MU HS HH.
  pose proof HL as ((W1 & W2 & W3 & W4) & R1 & R2 & R3 & ND & HF).
  unfold ledger. split.
  { unfold alloc_words.
    split; [|split; [|split]]; (eapply word_mem_munch; [exact MU | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia
      | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | | eassumption]);
    intros k Hk; apply HS; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact ND|].
  rewrite Forall_forall in HF |- *. intros [x k] Hin. specialize (HF _ Hin). cbn [fst snd] in *.
  destruct HF as (Hk & Hb & Hw & Hni). split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hni].
  destruct (block_range _ _ _ _ _ _ HM Hb) as [R4 R5]. pose proof ceil_big. unfold IMG_TOP in *.
  eapply word_mem_munch; [exact MU | lia | lia | | exact Hw].
  intros j Hj. apply (HH x k j Hin). lia.
Qed.

End KB.
