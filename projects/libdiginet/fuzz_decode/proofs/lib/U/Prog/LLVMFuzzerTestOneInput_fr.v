(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and addresses changed; 5 of its 528 lines of code are new or changed and 4 lines of the source are left out. *)
(* Modified by Theorem Labs: libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_fr.v for
   libdiginet/fuzz_decode, module paths changed and the one image value moved: the stack-guard GOT slot 0x1d948
   (LLVM_GUARD_GOT, inside the PT_LOAD [0x1d878, 0x1e000) of fuzz_decode.ubsan). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Mem Frame MState Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition LF_RES_TOP : Z := 0x50000.

Lemma lf_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma lf_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? LF_RES_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lf_rsegs_nonnil : rsegs <> [].
Proof. intros H. vm_compute in H. discriminate H. Qed.

Lemma lf_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= LF_RES_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) lf_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma lf_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= LF_RES_TOP.
Proof.
  intros a n seg E. destruct (lf_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (lf_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma lf_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < LF_RES_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (lf_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma lf_find_img : forall B a seg, ms_segs B = rsegs -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros B a seg HS E. destruct (lf_find_segment_in rsegs a 1 seg E) as (Hin & H1 & H2).
  destruct (lf_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; exact lf_rsegs_nonnil|].
  exists (segment_reservation seg). split; [rewrite HS; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

Lemma lf_wview_out : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros B m a HS Hn Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (lf_find_img B a seg HS E)).
Qed.

Lemma lf_wview_hi : forall m a, LF_RES_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold LF_RES_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (lf_find_top a 1 seg E). unfold LF_RES_TOP in *. lia.
Qed.

Lemma lf_present_of_writable : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  writable_at rsegs m a -> present m a.
Proof.
  intros B m a HS Hn Ha W. unfold writable_at in W. rewrite (lf_wview_out B m a HS Hn Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; exact E | contradiction].
Qed.

Lemma lf_stk : forall m lo hi, LF_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold LF_RES_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (lf_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (lf_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma lf_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma lf_munch_at : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha O. apply H. rewrite (MState.unsigned_lit a Ha). exact O. Qed.

Lemma lf_ret_pc : forall k, YK0s.ret_ok k -> MState.ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range _ k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  assert (Ev : bv_unsigned k mod 2 = 0).
  { pose proof (f_equal bv_unsigned H) as H2. rewrite MState.unsigned_lit_wrap in H2.
    assert (T : Z.testbit (bv_unsigned k) 0 = false).
    { rewrite <- H2. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec. apply andb_false_r. }
    rewrite Z.bit0_odd in T. rewrite Zmod_odd, T. reflexivity. }
  rewrite <- (MState.Z_to_bv_bv_unsigned k). apply MState.ret_pc_even; [lia | exact Ev].
Qed.

Lemma lf_eqv_mkst : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MState.MS R F pc fc None m ro) ms' ->
  ms' = @mkst (mkFP F fc) (ms_regs ms') pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m ro ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct ms' as [r f p s v c mm rr]; cbn in *. subst. split; [reflexivity | exact H1].
Qed.

Lemma lf_getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma lf_room : forall b n, sb_live b <= 70 -> 0 <= sb_bytes b <= 2 ^ 30 -> sb_cap b = CAPMAX ->
  0 <= n <= 2 ^ 26 -> room_slots b n.
Proof.
  intros b n Hl Hb Hc Hn. apply room_slots_big; rewrite ?Hc; unfold CAPMAX in *; lia.
Qed.

Lemma lf_not_img_res : forall B a, ms_segs B = rsegs -> ~ in_img B a ->
  forall s, In s (segments_reserved rsegs) -> ~ (bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s)).
Proof.
  intros B a HS Hn s Hs Hr. apply Hn. split; [rewrite HS; exact lf_rsegs_nonnil|].
  exists s. rewrite HS. split; [exact Hs | exact Hr].
Qed.

Lemma lf_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lf_ro_addr_out : forall B a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros B a HS Hn Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (lf_find_img B a seg HS E)).
Qed.

Lemma lf_rw_cells_norm : forall B m A cs, ms_segs B = rsegs -> ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) -> ~ in_img B (A + i)) ->
  Step.rw_cells rsegs m A cs -> Step.rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros B m A cs HS Hro Hn [[Hwf Hb] Hw]. pose proof (Mem.bytes_at_bound rsegs _ _ _ Hb) as Hbd.
  rewrite Cells.cells_bytes_length in Hbd by exact Hwf.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ Hro Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m Hro) Hw).
  intros i Hi. unfold Mem.wa. apply (lf_ro_addr_out B); [exact HS | apply Hn; exact Hi | lia].
Qed.

Lemma lf_rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 ->
  Step.rw_cells rsegs m0 A cs -> Step.rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb)]|].
  exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma llvm_run_norm : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SR rsegs (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize; [exact lf_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (lf_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma llvm_run_norm_cj : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel_cj rsegs m' m0' -> cj_same rsegs mem m' ->
     SR rsegs (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize_cj; [exact lf_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (lf_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma llvm_run : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m', Q (MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
     forall regs', Regs6ss.xregs_eqv R regs' ->
     SR rsegs (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl HE Hform HK.
  apply (evt_SR_canon rsegs _ Q md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQ & Heq). destruct (Hform can HQ) as (R & F & pc' & fc & m' & ->).
  destruct (lf_eqv_mkst R F pc' fc m' (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
  exact (HK R F pc' fc m' HQ _ Hx).
Qed.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition lf_sink_addr (a : Z) : Prop :=
  (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4).

Definition lf_sink_env : Prop :=
  forall a, lf_sink_addr a ->
    in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
    ~ (errno_addr B <= a < errno_addr B + 4).

Lemma lf_sink_none_kept : forall mem mem' md,
  (forall a, lf_sink_addr a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  sink_none B mem md -> sink_none B mem' md.
Proof.
  intros mem mem' md Hfr ((Ht & Hl) & Hhead & Hn).
  split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply Hfr. right. left. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply Hfr. right. right. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. left. cbn in Hx. lia.
Qed.

Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis SINK : lf_sink_env.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.

Lemma lf_guard_img : forall i, 0 <= i < 8 -> in_img B (ms_got_guard B + i).
Proof.
  intros i Hi. rewrite HGG. unfold LLVM_GUARD_GOT.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct (find_segment rsegs (0x1d948 + i) 1) as [seg|] eqn:E; [exact (lf_find_img B _ seg SEGS E)|].
  exfalso. repeat (destruct Hc as [-> | Hc]; [vm_compute in E; discriminate E|]). subst i. vm_compute in E. discriminate E.
Qed.

Definition lf_fr (stk S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - stk <= a < S) ->
     mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\
     (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\
     (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall a k, In (a, k) (blocks L0 A0) -> In (a, k) (blocks L A)) /\
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k ->
     mbyte (ms_segs B) mem (a + i) = mbyte (ms_segs B) mem0 (a + i)) /\
  (forall a, S - stk <= a < S -> writable_at (ms_segs B) mem a) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) /\
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem (ms_got_guard B + i) = mbyte (ms_segs B) mem0 (ms_got_guard B + i)) /\
  ro_agree rsegs mem.

Definition lf_mine (L0 : layout) (A0 : astate) (L : layout) (A : astate) (x k : Z) : Prop :=
  In (x, k) (blocks L A) /\ 0 < k /\ forall a j, In (a, j) (blocks L0 A0) -> a + j <= x \/ x + k <= a.

Definition llvm_sr_post (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ra p n : Z) (b : sbound) (j : nat) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' /\
    sink_none B mem' md' /\
    res_ok_slots A' b /\
    (forall i, 0 <= i < n -> mbyte (ms_segs B) mem' (p + i) = mbyte (ms_segs B) mem (p + i)) /\
    ro_agree rsegs mem' /\
    llvm_GI (S j) mem'.

Lemma lf_ceiling : LF_RES_TOP < alloc_ceiling.
Proof. pose proof YM05.alloc_ceiling_value. unfold LF_RES_TOP. lia. Qed.

Lemma lf_errno_low : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling.
Proof. intros a Ha. lia. Qed.

Lemma lf_mine_bytes : forall L0 A0 L A mem md x k y,
  aa_MR API L A mem md -> lf_mine L0 A0 L A x k -> x <= y < x + k ->
  ~ owned B L A y /\ ~ in_img B y /\ 4096 <= y < alloc_ceiling /\ present mem y /\
  forall a j, In (a, j) (blocks L0 A0) -> ~ (a <= y < a + j).
Proof.
  intros L0 A0 L A mem md x k y HM (Hin & Hk & Hd) Hy.
  apply blocks_In in Hin as (p & Hp & Hpin).
  destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md p k (y - x) HM Hpin ltac:(lia)) as (Hpr & H1 & H2 & Hno).
  pose proof (ax_blocks_img AX L A mem md p k (y - x) HM Hpin ltac:(lia)) as Himg.
  rewrite Hp in Hpr, H1, H2, Hno, Himg. replace (x + (y - x)) with y in Hpr, Hno, Himg by lia.
  split; [exact Hno|]. split; [exact Himg|]. split; [lia|]. split; [exact Hpr|].
  intros a j Ha Hr. destruct (Hd a j Ha); lia.
Qed.

Lemma lf_fr_init : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> ro_agree rsegs mem ->
  lf_fr stk (spZ regs) L A mem md L A mem md.
Proof.
  intros stk empty L A regs mem md ra p n
    (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & _) MI.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self|].
  split; [intros a _ _; split; [reflexivity | tauto]|].
  split; [intros a _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros a k H; exact H|]. split; [intros a k i _ _; reflexivity|].
  split; [exact Hstw|]. split; [exact Herr|]. split; [intros i _; reflexivity | exact MI].
Qed.

Lemma lf_fr_evt : forall stk S L0 A0 mem0 md0 L A mem md mem' W,
  lf_fr stk S L0 A0 mem0 md0 L A mem md ->
  alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (S - stk <= x < S) \/ exists y k, lf_mine L0 A0 L A y k /\ y <= x < y + k) ->
  lf_fr stk S L0 A0 mem0 md0 L A mem' md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md mem' W
    (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI) Hceil HS MU WM MI' HWin.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (S - stk <= x < S) \/ (~ owned B L A x /\ ~ in_img B x /\ x < alloc_ceiling /\
        forall a j, In (a, j) (blocks L0 A0) -> ~ (a <= x < a + j))).
  { intros x Hx NO. destruct (HWin x Hx NO) as [Hs | (y & k & Hm & Hy)]; [left; exact Hs | right].
    destruct (lf_mine_bytes L0 A0 L A mem md y k x HM Hm Hy) as (N1 & N2 & N3 & _ & N4).
    split; [exact N1|]. split; [exact N2|]. split; [lia | exact N4]. }
  assert (EQ : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx O. pose proof (lf_munch_at W mem mem' x MU Hx O) as E.
    split; [apply mbyte_eq_of; exact E | apply writable_iff_of; exact E]. }
  assert (WM' : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x Hw. unfold writable_at in *. rewrite SEGS in *. apply WM. exact Hw. }
  split.
  { destruct (mr_model B (aa_MR API) (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      destruct (lf_outside_dec W a) as [O|NO]; [apply (EQ a ltac:(lia) O)|].
      destruct (HOUT a ltac:(lia) NO) as [Hs | (N1 & _)]; [lia | contradiction].
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      destruct (lf_outside_dec W a) as [O|NO].
      + exists bb. rewrite (lf_munch_at W mem mem' a MU ltac:(lia) O). exact Hb.
      + destruct (HOUT a ltac:(lia) NO) as [Hs | (N1 & _)]; [lia | contradiction].
    - intros p n i Hin Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md p n i HM Hin Hi) as (Hpr & H1 & H2 & _).
      pose proof (ax_blocks_img AX L A mem md p n i HM Hin Hi) as Himgx.
      apply (lf_present_of_writable B mem' _ SEGS Himgx ltac:(lia)).
      rewrite <- SEGS. apply WM'. apply YL01.present_writable. exact Hpr. }
  split; [exact HW|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns. destruct (lf_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Hhigh a Ha Hns) as [F1 F2].
      split; [rewrite E1; exact F1 | rewrite F2; exact E2].
    - destruct (HOUT a ltac:(lia) NO) as [Hs | (_ & _ & N3 & _)]; [contradiction | lia]. }
  split.
  { intros a H1 H2 H3 H4. pose proof (lf_in_img_top B a SEGS H1) as Ht.
    destruct (lf_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Himg a H1 H2 H3 H4) as [F1 F2].
      split; [rewrite E1; exact F1 | rewrite F2; exact E2].
    - destruct (HOUT a ltac:(lia) NO) as [Hs | (_ & N2 & _)]; [lia | contradiction]. }
  split; [exact Hblk|].
  split.
  { intros a k i Hin Hi. pose proof (Hblk a k Hin) as Hin'.
    apply blocks_In in Hin' as (p & Hp & Hpin).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md p k i HM Hpin Hi) as (_ & H1 & H2 & _).
    rewrite Hp in H1, H2.
    destruct (lf_outside_dec W (a + i)) as [O|NO].
    - rewrite (proj1 (EQ (a + i) ltac:(lia) O)). exact (Hbyt a k i Hin Hi).
    - destruct (HOUT (a + i) ltac:(lia) NO) as [Hs | (_ & _ & _ & N4)]; [lia|].
      exfalso. apply (N4 a k Hin). lia. }
  split; [intros a Ha; apply WM'; exact (Hstw a Ha)|].
  split; [intros a Ha; apply WM'; exact (Herr a Ha)|].
  split; [|exact MI'].
  intros i Hi. pose proof (lf_guard_img i Hi) as Hg. pose proof (lf_in_img_top B _ SEGS Hg) as Ht.
  unfold LF_RES_TOP in Ht.
  destruct (lf_outside_dec W (ms_got_guard B + i)) as [O|NO].
  - rewrite (proj1 (EQ (ms_got_guard B + i) ltac:(lia) O)). exact (Hgd i Hi).
  - destruct (HOUT (ms_got_guard B + i) ltac:(lia) NO) as [Hs | (_ & N2 & _)]; [lia | contradiction].
Qed.

Lemma lf_fr_call : forall stk S L0 A0 mem0 md0 L A mem md K regs E L' A' regs' mem' md',
  lf_fr stk S L0 A0 mem0 md0 L A mem md ->
  alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  S - stk <= spZ regs - K -> spZ regs <= S ->
  (forall a, E a -> (S - stk <= a < S) \/ (a < alloc_ceiling /\ ~ in_img B a)) ->
  (forall a, S - stk <= a < S -> E a \/ ~ E a) ->
  (forall a, E a -> S - stk <= a < S -> writable_at (ms_segs B) mem' a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> In (a, k) (blocks L' A')) ->
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
  st_init_done A' = true -> ro_agree rsegs mem' ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)) ->
  lf_fr stk S L0 A0 mem0 md0 L' A' mem' md'.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md K regs E L' A' regs' mem' md'
    (HM & HW & HB & HID & (vm & Hmd) & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI) Hceil HS
    (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & (vm2 & Hvm2) & Hfr & Hkeep & Hscr)
    Hlo Hhi HE HEd HEw Hblk2 Hbyt2 HID2 MI2 Hgd2.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  assert (Hnown : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho.
    - pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho). lia.
    - pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM2 Ho). lia. }
  assert (Hhigh2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - stk <= a < S) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hns. destruct (Hnown a ltac:(lia)) as [N1 N2]. apply Hfr; [left; exact Ha | exact N1 | exact N2 | |].
    - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low a Hs); lia].
    - intros He. destruct (HE a He) as [Hs | [Hs _]]; lia. }
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|]. split; [exact HID2|].
  split; [exists vm2; rewrite Hvm2, Hmd; apply with_vmmaps_twice|].
  split.
  { intros a Ha Hns. destruct (Hhigh2 a Ha Hns) as [E1 E2]. destruct (Hhigh a Ha Hns) as [F1 F2].
    split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
  split.
  { intros a H1 H2 H3 H4. pose proof (lf_in_img_top B a SEGS H1) as Ht.
    assert (Hno : forall L1 A1 mem1 md1, aa_MR API L1 A1 mem1 md1 -> ~ owned B L1 A1 a).
    { intros L1 A1 mem1 md1 HM1 [Ho|Ho]; [exact (H3 (ax_img AX L1 A1 mem1 md1 a HM1 H1 Ho)) | exact (H2 Ho)]. }
    destruct (Hfr a (or_intror H1) (Hno _ _ _ _ HM) (Hno _ _ _ _ HM2)) as [E1 E2].
    - unfold scratch_k. intros [Hs|Hs]; [lia | exact (H4 Hs)].
    - intros He. destruct (HE a He) as [Hs | [_ Hs]]; [lia | exact (Hs H1)].
    - destruct (Himg a H1 H2 H3 H4) as [F1 F2]. split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
  split; [exact Hblk2|].
  split; [intros a k i Hin Hi; rewrite (Hbyt2 a k i Hin Hi); exact (Hbyt a k i Hin Hi)|].
  split.
  { intros a Ha. destruct (Z_lt_le_dec a (spZ regs - K)) as [L1|L1]; [|destruct (Z_lt_le_dec a (spZ regs)) as [L2|L2]].
    - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
      destruct (Hnown a ltac:(lia)) as [N1 N2]. assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      apply (proj2 (Hfr a (or_introl Hh) N1 N2 ltac:(unfold scratch_k; intros [Hs|Hs]; [lia | pose proof (lf_errno_low a Hs); lia]) He)).
      exact (Hstw a Ha).
    - apply Hscr. unfold scratch_k. left. lia.
    - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
      destruct (Hnown a ltac:(lia)) as [N1 N2]. assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      apply (proj2 (Hfr a (or_introl Hh) N1 N2 ltac:(unfold scratch_k; intros [Hs|Hs]; [lia | pose proof (lf_errno_low a Hs); lia]) He)).
      exact (Hstw a Ha). }
  split; [intros a Ha; apply Hscr; unfold scratch_k; right; exact Ha|].
  split; [intros i Hi; rewrite (Hgd2 i Hi); exact (Hgd i Hi) | exact MI2].
Qed.

Lemma lf_post : forall stk empty L0 A0 regs0 mem0 md0 ra p n L A regs mem md,
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> sink_none B mem0 md0 ->
  lf_fr stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved regs0 regs ->
  lib_post B API llvm_G stk L0 A0 regs0 mem0 md0 p L A regs mem md /\ sink_none B mem md /\
  (forall i, 0 <= i < n -> mbyte (ms_segs B) mem (p + i) = mbyte (ms_segs B) mem0 (p + i)) /\
  ro_agree rsegs mem.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n L A regs mem md
    (HM0 & HW0 & HB0 & HID0 & Hra & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn & Hpl & Hro) Hsn
    (HM & HW & HB & HID & (vm & Hmd) & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & _ & MI) Ha0 Hrp.
  split.
  { split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
    split; [exact Ha0|]. split; [exact Hrp|]. split; [exists vm; exact Hmd|].
    split.
    { intros q k Hq. assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      apply Hblk in Hb. apply blocks_In in Hb as (q' & Hq' & Hin). exists q'. auto. }
    split.
    { intros a Ha Hns. destruct (Hhigh a Ha ltac:(unfold lib_scratch in Hns; tauto)) as [E1 E2].
      split; [exact E1 | exact E2]. }
    split; [intros a T1 T2 T3 T4 _; exact (Himg a T1 T2 T3 T4)|].
    split.
    { intros q k i Hq _ Hi. assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      exact (Hbyt _ k i Hb Hi). }
    intros a [Hs|Hs]; [exact (Hstw a Hs) | exact (Herr a Hs)]. }
  split.
  { assert (Hs1 : sink_none B mem md0).
    { apply (lf_sink_none_kept mem0 mem md0); [|exact Hsn].
      intros a Ha. destruct (SINK a Ha) as (T1 & T2 & T3 & T4). exact (proj1 (Himg a T1 T2 T3 T4)). }
    rewrite Hmd. destruct Hs1 as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    destruct md0. exact H3. }
  split; [|exact MI].
  intros i Hi. destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  assert (Hb : In (p, n) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
  exact (Hbyt p n i Hb Hi).
Qed.

Lemma lf_fr_refl : forall stk S L A mem md,
  aa_MR API L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  (forall a, S - stk <= a < S -> writable_at (ms_segs B) mem a) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  ro_agree rsegs mem ->
  lf_fr stk S L A mem md L A mem md.
Proof.
  intros stk S L A mem md HM HW HB HID Hstw Herr MI.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self|].
  split; [intros a _ _; split; [reflexivity | tauto]|].
  split; [intros a _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros a k H; exact H|]. split; [intros a k i _ _; reflexivity|].
  split; [exact Hstw|]. split; [exact Herr|]. split; [intros i _; reflexivity | exact MI].
Qed.

Lemma lf_fr_trans : forall stk S stk' S' L0 A0 mem0 md0 L1 A1 mem1 md1 L2 A2 mem2 md2,
  lf_fr stk S L0 A0 mem0 md0 L1 A1 mem1 md1 ->
  lf_fr stk' S' L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  S - stk <= S' - stk' -> S' <= S -> alloc_ceiling <= S - stk -> S <= 2 ^ 64 ->
  lf_fr stk S L0 A0 mem0 md0 L2 A2 mem2 md2.
Proof.
  intros stk S stk' S' L0 A0 mem0 md0 L1 A1 mem1 md1 L2 A2 mem2 md2
    (HM1 & HW1 & HB1 & HID1 & (vm1 & Hmd1) & Hhigh1 & Himg1 & Hblk1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & MI1)
    (HM2 & HW2 & HB2 & HID2 & (vm2 & Hmd2) & Hhigh2 & Himg2 & Hblk2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & MI2)
    H1 H2 H3 H4.
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|]. split; [exact HID2|].
  split; [exists vm2; rewrite Hmd2, Hmd1; apply with_vmmaps_twice|].
  split.
  { intros a Ha Hns. destruct (Hhigh1 a Ha Hns) as [E1 F1]. destruct (Hhigh2 a Ha ltac:(lia)) as [E2 F2].
    split; [rewrite E2; exact E1 | rewrite F1; exact F2]. }
  split.
  { intros a T1 T2 T3 T4. destruct (Himg1 a T1 T2 T3 T4) as [E1 F1]. destruct (Himg2 a T1 T2 T3 T4) as [E2 F2].
    split; [rewrite E2; exact E1 | rewrite F1; exact F2]. }
  split; [intros a k Hin; exact (Hblk2 a k (Hblk1 a k Hin))|].
  split; [intros a k i Hin Hi; rewrite (Hbyt2 a k i (Hblk1 a k Hin) Hi); exact (Hbyt1 a k i Hin Hi)|].
  split.
  { intros a Ha. destruct (Z_lt_le_dec a (S' - stk')) as [L|L]; [|destruct (Z_lt_le_dec a S') as [L'|L']].
    - apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). exact (Hstw1 a Ha).
    - exact (Hstw2 a ltac:(lia)).
    - apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). exact (Hstw1 a Ha). }
  split; [exact Herr2|].
  split; [intros i Hi; rewrite (Hgd2 i Hi); exact (Hgd1 i Hi) | exact MI2].
Qed.

End F.
