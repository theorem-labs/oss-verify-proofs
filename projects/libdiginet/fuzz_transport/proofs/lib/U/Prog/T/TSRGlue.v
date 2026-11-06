(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 703 of its 956 lines of code are new or changed and 274 lines of the source are left out. *)
(* The ubsan twin of Prog/T/TSRGlue.v (same statements over the ubsan image, U/ modules). The SR glue of the harness functions that allocate (receive, build_and_receive, LLVMFuzzerTestOneInput), ubsan
   image: a frame relation sr_fr that an SR walk carries across its malloc and free calls (SR, the kit's
   malloc_contract / free_contract), across a callee whose post is call_post_k (sr_fr_call), and across its evt runs
   (the callee contracts of Prog/T, on the normalized memory); and h_post's call_post_k from it (sr_post).
   Shape and proofs follow libdiginet/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_fr.v and _glue.v.
   Changes for this unit: the walk writes the world (image .bss), so sr_fr's image clause leaves out h_world, which h_binds keeps apart from what the
   allocator owns; sr_fr's high clause leaves out errno and the allocator ctx, which a callee's footprint may hold;
   and sr_fr carries layout_le, the region count and the entry's user blocks with their addresses, which h_post's
   call_post_k asks of the whole run. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require YK14 YO10.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame MState Regs6ss RegisterBridge Exec Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require RoAdapt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract receive_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- the image (no allocator) *)

(* Every reservation of the ubsan image ends at or below SR_RES_TOP (PT_LOAD 4 ends at 0x63ef8). *)
Definition SR_RES_TOP : Z := 0x64000.

Lemma sr_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma sr_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? SR_RES_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sr_rsegs_nonnil : rsegs <> [].
Proof. intros H. vm_compute in H. discriminate H. Qed.

Lemma sr_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= SR_RES_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) sr_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma sr_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= SR_RES_TOP.
Proof.
  intros a n seg E. destruct (sr_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (sr_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma sr_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < SR_RES_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (sr_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma sr_find_img : forall B a seg, ms_segs B = rsegs -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros B a seg HS E. destruct (sr_find_segment_in rsegs a 1 seg E) as (Hin & H1 & H2).
  destruct (sr_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; exact sr_rsegs_nonnil|].
  exists (segment_reservation seg). split; [rewrite HS; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

Lemma sr_wview_out : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros B m a HS Hn Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (sr_find_img B a seg HS E)).
Qed.

Lemma sr_wview_hi : forall m a, SR_RES_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold SR_RES_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sr_find_top a 1 seg E). unfold SR_RES_TOP in *. lia.
Qed.

Lemma sr_present_of_writable : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  writable_at rsegs m a -> present m a.
Proof.
  intros B m a HS Hn Ha W. unfold writable_at in W. rewrite (sr_wview_out B m a HS Hn Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; exact E | contradiction].
Qed.

Lemma sr_stk : forall m lo hi, SR_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold SR_RES_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (sr_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (sr_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma sr_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma sr_munch_at : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha O. apply H. rewrite (MState.unsigned_lit a Ha). exact O. Qed.

Lemma sr_ret_pc : forall k, YK0s.ret_ok k -> MState.ret_pc k = k.
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

Lemma sr_eqv_mkst : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MState.MS R F pc fc None m ro) ms' ->
  ms' = @mkst (mkFP F fc) (ms_regs ms') pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m ro ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct ms' as [r f p s v c mm rr]; cbn in *. subst. split; [reflexivity | exact H1].
Qed.

Lemma sr_getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma sr_ro_addr_out : forall B a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros B a HS Hn Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (sr_find_img B a seg HS E)).
Qed.

Lemma sr_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sr_rw_cells_norm : forall B m A cs, ms_segs B = rsegs -> ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) -> ~ in_img B (A + i)) ->
  Step.rw_cells rsegs m A cs -> Step.rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros B m A cs HS Hro Hn [[Hwf Hb] Hw]. pose proof (Mem.bytes_at_bound rsegs _ _ _ Hb) as Hbd.
  rewrite Cells.cells_bytes_length in Hbd by exact Hwf.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ Hro Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m Hro) Hw).
  intros i Hi. unfold Mem.wa. apply (sr_ro_addr_out B); [exact HS | apply Hn; exact Hi | lia].
Qed.

Lemma sr_rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 ->
  Step.rw_cells rsegs m0 A cs -> Step.rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb)]|].
  exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

(* An SR config whose machine state runs, as an evt run on the normalized memory (the form the Prog/T contracts,
   which ask mem_inv, are used in), to Q; the continuation sees each end state in SR form, with registers, memory
   (mem_rel) and read-only bytes (ro_same) related. *)
Lemma sr_run_norm : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
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
    apply evt_normalize; [exact sr_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (sr_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

(* rw_cells survives a memory change that keeps the bytes and their writability (the donor's lf_rw_cells_frame). *)
Lemma sr_rw_cells_frame : forall m m' A cs,
  Step.rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (Cells.cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite Cells.cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite Cells.cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite Cells.cells_bytes_length in Hi by exact Hwf.
    change (Mem.mrd rsegs m' (Mem.wa (A + Z.of_nat i)) = Mem.mrd rsegs m (Mem.wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.


(* ---------------------------------------------------------------- the world and .data.rel.ro are writable *)

(* Every segment that meets [lo, hi) is writable (checked by computation over the image's segments). *)
Definition sr_seg_rw_over (lo hi : Z) : bool :=
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo) || (hi <=? Z.of_N (seg_base s))) rsegs.

Lemma sr_ro_over : forall lo hi x, sr_seg_rw_over lo hi = true -> lo <= x < hi -> 0 <= x < 2 ^ 64 ->
  Mem.ro_addr rsegs (Z_to_bv 64 x) = false.
Proof.
  intros lo hi x H Hx Hb. unfold Mem.ro_addr. rewrite (MState.unsigned_lit x Hb).
  destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|reflexivity].
  destruct (sr_find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbv beta in Hs.
  destruct (seg_writable seg); [reflexivity|].
  cbn [orb] in Hs. apply orb_true_iff in Hs as [Hs|Hs]; apply Z.leb_le in Hs; lia.
Qed.

Lemma sr_world_rw : sr_seg_rw_over W_BASE_UBSAN (W_BASE_UBSAN + W_LEN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sr_relro_rw : sr_seg_rw_over RELRO_BASE (RELRO_BASE + RELRO_LEN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sr_ro_world : forall x, W_BASE_UBSAN <= x < W_BASE_UBSAN + W_LEN -> Mem.ro_addr rsegs (Z_to_bv 64 x) = false.
Proof. intros x Hx. apply (sr_ro_over _ _ x sr_world_rw Hx). unfold W_BASE_UBSAN, W_LEN in *. lia. Qed.

Lemma sr_ro_relro : forall x, RELRO_BASE <= x < RELRO_BASE + RELRO_LEN -> Mem.ro_addr rsegs (Z_to_bv 64 x) = false.
Proof. intros x Hx. apply (sr_ro_over _ _ x sr_relro_rw Hx). unfold RELRO_BASE, RELRO_LEN in *. lia. Qed.

(* wmem and relro_img survive normalize (they are about bytes at no read-only address). *)
Lemma sr_wmem_norm : forall mem Bw, ro_agree rsegs mem -> wmem rsegs mem Bw -> wmem rsegs (normalize rsegs mem) Bw.
Proof.
  intros mem Bw Hro H. apply RoAdapt.rw_cells_norm; [exact Hro | exact H |].
  intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi. unfold Mem.wa.
  apply sr_ro_world. rewrite Nat.add_0_r, Z2Nat.id in Hi by (unfold W_LEN; lia). lia.
Qed.

Lemma sr_wmem_back : forall mem m0 Bw, mem_rel rsegs mem m0 -> wmem rsegs m0 Bw -> wmem rsegs mem Bw.
Proof. intros mem m0 Bw HR H. exact (RoAdapt.rw_cells_back rsegs mem m0 _ _ HR H). Qed.

Lemma sr_relro_norm : forall mem, ro_agree rsegs mem -> relro_img mem -> relro_img (normalize rsegs mem).
Proof.
  intros mem Hro H i Hi. rewrite <- (H i Hi). symmetry.
  exact (mrd_rel rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)).
Qed.

Lemma sr_relro_back : forall mem m0, mem_rel rsegs mem m0 -> relro_img m0 -> relro_img mem.
Proof. intros mem m0 HR H i Hi. rewrite <- (H i Hi). exact (mrd_rel rsegs mem m0 _ HR). Qed.

(* ---------------------------------------------------------------- lists *)

Lemma sr_nodup_fst_in : forall {X Y : Type} (l : list (X * Y)) a b c, List.NoDup (map fst l) -> In (a, b) l -> In (a, c) l ->
  b = c.
Proof.
  intros X Y l a b c ND. revert a b c ND.
  induction l as [|[x y] l IH]; intros a b c ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hn ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as <- <-. injection E2 as <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, c). auto.
  - injection E2 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, b). auto.
  - exact (IH a b c ND H1 H2).
Qed.

Lemma sr_app_mid_inv : forall {X : Type} (x : X) b1 b2 c1 c2,
  ~ In x b1 -> ~ In x c1 -> b1 ++ x :: b2 = c1 ++ x :: c2 -> b1 = c1 /\ b2 = c2.
Proof.
  intros X x b1. induction b1 as [|y b1 IH]; intros b2 c1 c2 H1 H2 E; destruct c1 as [|z c1]; cbn in E.
  - injection E as E. auto.
  - injection E as <- _. exfalso. apply H2. left. reflexivity.
  - injection E as -> _. exfalso. apply H1. left. reflexivity.
  - injection E as <- E. destruct (IH b2 c1 c2 ltac:(intros h; apply H1; right; exact h)
      ltac:(intros h; apply H2; right; exact h) E) as [-> ->]. auto.
Qed.

Lemma sr_nonempty_not_twice : forall b1 b2 x n, pairwise ranges_disjoint (b1 ++ (x, n) :: b2) -> 0 < n ->
  ~ In (x, n) (b1 ++ b2).
Proof.
  intros b1 b2 x n HP Hn Hin. destruct (pairwise_app_mid _ b1 (x, n) b2 (x, n) HP Hin) as [H|H];
    unfold ranges_disjoint in H; cbn [fst snd] in H; lia.
Qed.

Lemma sr_disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

(* layout_le composes when the region count does not shrink. *)
Lemma sr_layout_le_trans : forall A0 A L0 L L',
  layout_le A0 L0 L -> layout_le A L L' -> (length (st_regions A0) <= length (st_regions A))%nat ->
  layout_le A0 L0 L'.
Proof.
  intros A0 A L0 L L' (C1 & S1 & K1 & R1) (C2 & S2 & K2 & R2) Hlen.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (R2 r ltac:(lia)). exact (R1 r Hr).
Qed.

(* ---------------------------------------------------------------- the frame relation *)

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGG : ms_got_guard B = H_GUARD_GOT.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis WORLD : forall a, h_world a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

Hypothesis RELRO : forall a, RELRO_BASE <= a < RELRO_BASE + RELRO_LEN ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

(* The bytes the allocator never owns and the walk keeps track of itself: the world and .data.rel.ro. *)
Definition sr_kept (a : Z) : Prop := h_world a \/ RELRO_BASE <= a < RELRO_BASE + RELRO_LEN.

Lemma sr_kept_facts : forall a, sr_kept a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof. intros a [H|H]; [exact (WORLD a H) | exact (RELRO a H)]. Qed.

Lemma sr_kept_unowned : forall L A mem md a, aa_MR API L A mem md -> sr_kept a -> ~ owned B L A a.
Proof.
  intros L A mem md a HM Hk [Ho|Ho]; destruct (sr_kept_facts a Hk) as (Hi & Hs & Hc & _).
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

(* A call whose post is call_post_k with footprint E off the kept bytes, and whose window lies above the ceiling,
   keeps the world and .data.rel.ro. *)
Lemma sr_call_kept : forall K L A regs mem md E L' A' regs' mem' md',
  aa_MR API L A mem md -> call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  YM05.alloc_ceiling <= spZ regs - K -> (forall a, E a -> ~ sr_kept a) ->
  forall a, sr_kept a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' HM (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) Hk HE a Ha.
  pose proof (sr_kept_facts a Ha) as (Hi & _ & _ & He). pose proof (sr_in_img_top B a SEGS Hi) as Ht.
  pose proof YM05.alloc_ceiling_value as Hc. unfold SR_RES_TOP in Ht.
  apply Hfr; [right; exact Hi | exact (sr_kept_unowned L A mem md a HM Ha) | exact (sr_kept_unowned L' A' mem' md' a HM2 Ha)
    | unfold scratch_k; intros [Hs|Hs]; [lia | exact (He Hs)] | intros HEa; exact (HE a HEa Ha)].
Qed.

Lemma sr_guard_img : forall i, 0 <= i < 8 -> in_img B (ms_got_guard B + i).
Proof.
  intros i Hi. rewrite HGG. unfold H_GUARD_GOT.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct (find_segment rsegs (0x22050 + i) 1) as [seg|] eqn:E; [exact (sr_find_img B _ seg SEGS E)|].
  exfalso. repeat (destruct Hc as [-> | Hc]; [vm_compute in E; discriminate E|]). subst i. vm_compute in E. discriminate E.
Qed.

Lemma sr_ceiling : SR_RES_TOP < alloc_ceiling.
Proof. pose proof YM05.alloc_ceiling_value. unfold SR_RES_TOP. lia. Qed.

(* A world byte is in the image, below the ceiling, owned by no allocator state. *)
Lemma sr_world_unowned : forall L A mem md a, aa_MR API L A mem md -> h_world a -> ~ owned B L A a.
Proof.
  intros L A mem md a HM Hw [Ho|Ho]; destruct (WORLD a Hw) as (Hi & Hs & Hc & _).
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma sr_world_img : forall a, h_world a -> in_img B a /\ 0 <= a < SR_RES_TOP.
Proof. intros a Hw. destruct (WORLD a Hw) as (Hi & _). split; [exact Hi | exact (sr_in_img_top B a SEGS Hi)]. Qed.

(* The relation between the walk's entry state (L0, A0, mem0, md0) and a later state, for a walk whose own window is
   [S - stk, S): the allocator invariant; the high bytes outside that window, errno and ctx kept; the image bytes the
   allocator does not own statically, its ctx, errno and the world kept; the entry's blocks and their bytes kept, with
   their pointers; the window and errno writable; the stack guard kept; read-only memory intact; the layout grown. *)
Definition sr_fr (stk S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - stk <= a < S) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\
     (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ h_world a ->
     mbyte (ms_segs B) mem a = mbyte (ms_segs B) mem0 a /\
     (writable_at (ms_segs B) mem0 a <-> writable_at (ms_segs B) mem a)) /\
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A) /\ ptr_addr L p = ptr_addr L0 p) /\
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k ->
     mbyte (ms_segs B) mem (a + i) = mbyte (ms_segs B) mem0 (a + i)) /\
  (forall a, S - stk <= a < S -> writable_at (ms_segs B) mem a) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) /\
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem (ms_got_guard B + i) = mbyte (ms_segs B) mem0 (ms_got_guard B + i)) /\
  ro_agree rsegs mem /\
  layout_le A0 L0 L /\ (length (st_regions A0) <= length (st_regions A))%nat.

(* The entry's blocks, as addresses, are still blocks. *)
Lemma sr_fr_blocks : forall stk S L0 A0 mem0 md0 L A mem md,
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> forall a k, In (a, k) (blocks L0 A0) -> In (a, k) (blocks L A).
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md (_ & _ & _ & _ & _ & _ & _ & Hub & _) a k Hin.
  apply blocks_In in Hin as (q & Hq & Hqin). destruct (Hub q k Hqin) as [Hin2 Hp].
  apply blocks_In. exists q. split; [rewrite Hp; exact Hq | exact Hin2].
Qed.

(* A block born after the entry state: the walk may write it. *)
Definition sr_mine (L0 : layout) (A0 : astate) (L : layout) (A : astate) (x k : Z) : Prop :=
  In (x, k) (blocks L A) /\ 0 < k /\ forall a j, In (a, j) (blocks L0 A0) -> a + j <= x \/ x + k <= a.

Lemma sr_mine_bytes : forall L0 A0 L A mem md x k y,
  aa_MR API L A mem md -> sr_mine L0 A0 L A x k -> x <= y < x + k ->
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

(* A world byte is in no block of an allocator state (blocks lie off the image). *)
Lemma sr_world_not_block : forall L A mem md a k y, aa_MR API L A mem md -> In (a, k) (blocks L A) -> h_world y ->
  ~ (a <= y < a + k).
Proof.
  intros L A mem md a k y HM Hin Hw Hy. apply blocks_In in Hin as (p & Hp & Hpin).
  pose proof (ax_blocks_img AX L A mem md p k (y - a) HM Hpin ltac:(lia)) as Himg.
  rewrite Hp in Himg. replace (a + (y - a)) with y in Himg by lia.
  exact (Himg (proj1 (WORLD y Hw))).
Qed.

Lemma sr_fr_refl : forall stk S L A mem md,
  aa_MR API L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  (forall a, S - stk <= a < S -> writable_at (ms_segs B) mem a) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  ro_agree rsegs mem ->
  sr_fr stk S L A mem md L A mem md.
Proof.
  intros stk S L A mem md HM HW HB HID Hstw Herr MI.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self|].
  split; [intros a _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros a _ _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros p n H; split; [exact H | reflexivity]|]. split; [intros a k i _ _; reflexivity|].
  split; [exact Hstw|]. split; [exact Herr|]. split; [intros i _; reflexivity|].
  split; [exact MI|]. split; [apply layout_le_refl | lia].
Qed.

(* The entry state of a walk under h_pre: sr_fr from itself, with the whole window K. *)
Lemma sr_fr_init : forall K L A regs mem md b Bw,
  h_pre B API K L A regs mem md b Bw -> sr_fr K (spZ regs) L A mem md L A mem md.
Proof.
  intros K L A regs mem md b Bw
    ((HM & HW & HB & _ & _ & _ & _ & Hstw & _ & Herr & _) & HID & _ & _ & Hro & _).
  apply sr_fr_refl; try assumption. rewrite <- SEGS. exact Hro.
Qed.

(* An evt run whose footprint W lies in the window, the world, and blocks born after the entry keeps sr_fr. *)
Lemma sr_fr_evt : forall stk S L0 A0 mem0 md0 L A mem md mem' W,
  sr_fr stk S L0 A0 mem0 md0 L A mem md ->
  alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (S - stk <= x < S) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k) ->
  sr_fr stk S L0 A0 mem0 md0 L A mem' md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md mem' W FR Hceil HS MU WM MI' HWin.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof sr_ceiling as Hrt.
  pose proof (sr_fr_blocks _ _ _ _ _ _ _ _ _ _ FR) as Hblk.
  (* every byte the run may write: the window, or an unowned byte below the ceiling in no entry block, which is
     either a world byte (in the image) or a byte of a block born later (off the image) *)
  assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (S - stk <= x < S) \/ (~ owned B L A x /\ x < alloc_ceiling /\
        (h_world x \/ ~ in_img B x) /\ forall a j, In (a, j) (blocks L0 A0) -> ~ (a <= x < a + j))).
  { intros x Hx NO. destruct (HWin x Hx NO) as [Hs | [Hw | (y & k & Hm & Hy)]]; [left; exact Hs | right | right].
    - pose proof (sr_world_img x Hw) as [_ Ht].
      split; [exact (sr_world_unowned L A mem md x HM Hw)|]. split; [lia|]. split; [left; exact Hw|].
      intros a j Ha. exact (sr_world_not_block L A mem md a j x HM (Hblk a j Ha) Hw).
    - destruct (sr_mine_bytes L0 A0 L A mem md y k x HM Hm Hy) as (N1 & N2 & N3 & _ & N4).
      split; [exact N1|]. split; [lia|]. split; [right; exact N2 | exact N4]. }
  assert (EQ : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx O. pose proof (sr_munch_at W mem mem' x MU Hx O) as E.
    split; [apply mbyte_eq_of; exact E | apply writable_iff_of; exact E]. }
  assert (WM' : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x Hw. unfold writable_at in *. rewrite SEGS in *. apply WM. exact Hw. }
  split.
  { destruct (mr_model B (aa_MR API) (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      destruct (sr_outside_dec W a) as [O|NO]; [apply (EQ a ltac:(lia) O)|].
      destruct (HOUT a ltac:(lia) NO) as [Hs | (N1 & _)]; [lia | contradiction].
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      destruct (sr_outside_dec W a) as [O|NO].
      + exists bb. rewrite (sr_munch_at W mem mem' a MU ltac:(lia) O). exact Hb.
      + destruct (HOUT a ltac:(lia) NO) as [Hs | (N1 & _)]; [lia | contradiction].
    - intros p n i Hin Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md p n i HM Hin Hi) as (Hpr & H1 & H2 & _).
      pose proof (ax_blocks_img AX L A mem md p n i HM Hin Hi) as Himgx.
      apply (sr_present_of_writable B mem' _ SEGS Himgx ltac:(lia)).
      rewrite <- SEGS. apply WM'. apply YL01.present_writable. exact Hpr. }
  split; [exact HW|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne Hnc. destruct (sr_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Hhigh a Ha Hns Hne Hnc) as [F1 F2].
      split; [rewrite E1; exact F1 | rewrite F2; exact E2].
    - destruct (HOUT a ltac:(lia) NO) as [Hs | (_ & N3 & _)]; [contradiction | lia]. }
  split.
  { intros a H1 H2 H3 H4 H5. pose proof (sr_in_img_top B a SEGS H1) as Ht.
    destruct (sr_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Himg a H1 H2 H3 H4 H5) as [F1 F2].
      split; [rewrite E1; exact F1 | rewrite F2; exact E2].
    - destruct (HOUT a ltac:(lia) NO) as [Hs | (_ & _ & [Hw | Hn] & _)]; [lia | contradiction | contradiction]. }
  split; [exact Hub|].
  split.
  { intros a k i Hin Hi. pose proof (Hblk a k Hin) as Hin'.
    apply blocks_In in Hin' as (p & Hp & Hpin).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md p k i HM Hpin Hi) as (_ & H1 & H2 & _).
    rewrite Hp in H1, H2.
    destruct (sr_outside_dec W (a + i)) as [O|NO].
    - rewrite (proj1 (EQ (a + i) ltac:(lia) O)). exact (Hbyt a k i Hin Hi).
    - destruct (HOUT (a + i) ltac:(lia) NO) as [Hs | (_ & _ & _ & N4)]; [lia|].
      exfalso. apply (N4 a k Hin). lia. }
  split; [intros a Ha; apply WM'; exact (Hstw a Ha)|].
  split; [intros a Ha; apply WM'; exact (Herr a Ha)|].
  split.
  { intros i Hi. pose proof (sr_guard_img i Hi) as Hg. pose proof (sr_in_img_top B _ SEGS Hg) as Ht.
    unfold SR_RES_TOP in Ht.
    destruct (sr_outside_dec W (ms_got_guard B + i)) as [O|NO].
    - rewrite (proj1 (EQ (ms_got_guard B + i) ltac:(lia) O)). exact (Hgd i Hi).
    - destruct (HOUT (ms_got_guard B + i) ltac:(lia) NO) as [Hs | (_ & _ & [Hw | Hn] & _)]; [lia | | contradiction].
      exfalso. destruct (WORLD _ Hw) as (_ & Hs & _). apply Hs. unfold static_owned. right. right. right. right. left. lia. }
  split; [exact MI'|]. split; [exact Hle | exact Hlen].
Qed.

(* A call (malloc, free, or a harness function under h_pre / h_post) whose post is call_post_k with footprint E:
   E holds only window bytes, bytes below the ceiling off the image, world bytes and ctx bytes. The caller gives what
   call_post_k does not: the entry's user blocks, their bytes, the region count, the guard, read-only memory. *)
Lemma sr_fr_call : forall stk S L0 A0 mem0 md0 L A mem md K regs E L' A' regs' mem' md',
  sr_fr stk S L0 A0 mem0 md0 L A mem md ->
  alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  S - stk <= spZ regs - K -> spZ regs <= S ->
  (forall a, E a -> (S - stk <= a < S) \/ (a < alloc_ceiling /\ ~ in_img B a) \/ h_world a \/
     (ms_ctx B <= a < ms_ctx B + CTX_SIZE)) ->
  (forall a, S - stk <= a < S -> E a \/ ~ E a) ->
  (forall a, E a -> S - stk <= a < S -> writable_at (ms_segs B) mem' a) ->
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A')) ->
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
  st_init_done A' = true -> ro_agree rsegs mem' ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  sr_fr stk S L0 A0 mem0 md0 L' A' mem' md'.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md K regs E L' A' regs' mem' md'
    (HM & HW & HB & HID & (vm & Hmd) & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen) Hceil HS
    (HM2 & HW2 & HB2 & Hle2 & Hstab & Hregs & (vm2 & Hvm2) & Hfr & Hkeep & Hscr)
    Hlo Hhi HE HEd HEw Hub2 Hbyt2 HID2 MI2 Hgd2 Hlen2.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof sr_ceiling as Hrt.
  assert (Hnown : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho.
    - pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho). lia.
    - pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM2 Ho). lia. }
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|]. split; [exact HID2|].
  split; [exists vm2; rewrite Hvm2, Hmd; apply with_vmmaps_twice|].
  split.
  { intros a Ha Hns Hne Hnc. destruct (Hnown a ltac:(lia)) as [N1 N2].
    destruct (Hfr a (or_introl Ha) N1 N2) as [E1 E2].
    - unfold scratch_k. intros [Hs|Hs]; [lia | exact (Hne Hs)].
    - intros He. destruct (HE a He) as [Hs | [[Hs _] | [Hw | Hc]]]; [lia | lia | | exact (Hnc Hc)].
      pose proof (sr_world_img a Hw). lia.
    - destruct (Hhigh a Ha Hns Hne Hnc) as [F1 F2]. split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
  split.
  { intros a H1 H2 H3 H4 H5. pose proof (sr_in_img_top B a SEGS H1) as Ht.
    assert (Hno : forall L1 A1 mem1 md1, aa_MR API L1 A1 mem1 md1 -> ~ owned B L1 A1 a).
    { intros L1 A1 mem1 md1 HM1 [Ho|Ho]; [exact (H3 (ax_img AX L1 A1 mem1 md1 a HM1 H1 Ho)) | exact (H2 Ho)]. }
    destruct (Hfr a (or_intror H1) (Hno _ _ _ _ HM) (Hno _ _ _ _ HM2)) as [E1 E2].
    - unfold scratch_k. intros [Hs|Hs]; [lia | exact (H4 Hs)].
    - intros He. destruct (HE a He) as [Hs | [[_ Hs] | [Hw | Hc]]]; [lia | exact (Hs H1) | exact (H5 Hw) | exact (H3 Hc)].
    - destruct (Himg a H1 H2 H3 H4 H5) as [F1 F2]. split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
  split.
  { intros p n Hin. destruct (Hub p n Hin) as [Hin1 Hp1]. pose proof (Hub2 p n Hin) as Hin2.
    split; [exact Hin2|]. rewrite (Hstab p n Hin1 Hin2). exact Hp1. }
  split; [intros a k i Hin Hi; rewrite (Hbyt2 a k i Hin Hi); exact (Hbyt a k i Hin Hi)|].
  split.
  { intros a Ha. destruct (Z_lt_le_dec a (spZ regs - K)) as [L1|L1]; [|destruct (Z_lt_le_dec a (spZ regs)) as [L2|L2]].
    - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
      destruct (Hnown a ltac:(lia)) as [N1 N2]. assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      apply (proj2 (Hfr a (or_introl Hh) N1 N2 ltac:(unfold scratch_k; intros [Hs|Hs]; [lia | lia]) He)).
      exact (Hstw a Ha).
    - apply Hscr. unfold scratch_k. left. lia.
    - destruct (HEd a Ha) as [He|He]; [exact (HEw a He Ha)|].
      destruct (Hnown a ltac:(lia)) as [N1 N2]. assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      apply (proj2 (Hfr a (or_introl Hh) N1 N2 ltac:(unfold scratch_k; intros [Hs|Hs]; [lia | lia]) He)).
      exact (Hstw a Ha). }
  split; [intros a Ha; apply Hscr; unfold scratch_k; right; exact Ha|].
  split; [intros i Hi; rewrite (Hgd2 i Hi); exact (Hgd i Hi)|].
  split; [exact MI2|].
  split; [exact (sr_layout_le_trans A0 A L0 L L' Hle Hle2 Hlen) | lia].
Qed.

(* ---------------------------------------------------------------- the steps *)

(* A call site inside the walk's window: the allocator's call_pre_k with the callee window K. *)
Lemma g_pre : forall stk S L0 A0 mem0 md0 L A mem md regs K,
  sr_fr stk S L0 A0 mem0 md0 L A mem md ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - K -> spZ regs <= S -> 0 <= K ->
  YM05.alloc_ceiling + stk <= S -> spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  call_pre_k B (aa_MR API) K L A regs mem md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md regs K
    (HM & HW & HB & HID & _ & _ & _ & _ & _ & Hstw & Herr & _) Hra Hal H1 H2 HK Hc H63 Htp.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
  split; [exact Hal|]. split; [lia|]. split; [exact H63|].
  split; [intros a Ha; apply Hstw; lia|]. split; [exact Htp|]. split; [exact Herr|].
  intros E. rewrite HID in E. discriminate.
Qed.

(* After a call with footprint E below the ceiling, the caller's frame above the callee's sp is kept. *)
Lemma g_above : forall stk S L A regs mem md K E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  (forall a, E a -> a < YM05.alloc_ceiling) ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K E L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 HE a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; lia.
  - intros He. pose proof (HE a He). lia.
Qed.

(* malloc at a call site of the walk: the continuation gets the block res of n bytes, born after the entry. *)
Lemma g_malloc : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A n bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @malloc_contract fx'' rc B API) ->
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 n ->
  res_ok_slots A bres -> room_slots bres n ->
  (forall L' A' regs' mem' md' res,
     sr_fr stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> 4096 <= res -> res + n <= YM05.alloc_ceiling -> res mod 16 = 0 ->
     (forall i, 0 <= i < n -> ~ in_img B (res + i)) ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     res_ok_slots A' (sb_malloc bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     (forall a, sr_kept a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (ms_malloc B)) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A n bres P MALLOC FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  pose proof (sr_fr_blocks _ _ _ _ _ _ _ _ _ _ FR) as Hblk.
  eapply SR_bind.
  { apply (MALLOC fx' L A regs mem md n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact H10.
    - exact Hres.
    - exact Hroom. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10 & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
    & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub2 & Hidt & Hlen2 & Hres2).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle2 & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : sr_fr stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply sr_fr_call; [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | | exact Hlen2].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros p k Hin. exact (Hub2 p k (proj1 (Hub p k Hin))).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 res FR2 Hrp G10 ltac:(lia) ltac:(lia) Hal16 Hf3 (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2)))
    Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
    + apply call_post_k_alloc. exact Hpost.
    + exact Hc.
    + exact H1.
    + exact HS.
    + unfold ALLOC_STACK; lia.
    + intros a Ha. destruct Ha.
  - exact Hkept.
  - apply (sr_call_kept ALLOC_STACK L A regs mem md (fun _ => False) L2 A2 regs2 mem2 md2 HM
      ltac:(apply call_post_k_alloc; exact Hpost) ltac:(unfold ALLOC_STACK in *; lia)).
    intros a Hf. destruct Hf.
Qed.

(* free of a block x of n > 0 bytes born after the entry (it misses every entry block). *)
Lemma g_free : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A x n bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @free_contract fx'' rc B API) ->
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 x ->
  In (x, n) (blocks L A) -> 0 < n -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= x \/ x + n <= a) ->
  res_ok_slots A bres ->
  (forall L' A' regs' mem' md',
     sr_fr stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     (exists b1 b2, blocks L A = b1 ++ (x, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     res_ok_slots A' (sb_free bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun a => a = x) ->
     (forall a, sr_kept a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (ms_free B)) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A x n bres P FREE FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hin Hn Hd Hres K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  pose proof (sr_fr_blocks _ _ _ _ _ _ _ _ _ _ FR) as Hblk.
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, x <= a < x + n -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Himgx.
    rewrite Hq in R1, R2, Himgx. replace (x + (a - x)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  (* no entry user block is the freed one: an entry block at x would have 0 bytes, and the freed pointer holds n *)
  assert (Hne : forall p k, In (p, k) (user_blocks A0) -> p <> q).
  { intros p k Hpk Epq. subst p. destruct (Hub q k Hpk) as [HinA Hpa].
    assert (HB0 : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
    rewrite <- Hpa, Hq in HB0. destruct (Hd x k HB0) as [Hk|Hk]; [|lia].
    assert (Ek : k = n) by exact (sr_nodup_fst_in _ q k n (YO10.user_block_ptrs_NoDup A HW) HinA Hqin). lia. }
  eapply SR_bind.
  { apply (FREE fx' L A regs mem md q n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite H10, Hq. reflexivity.
    - exact Hres. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub2 & Hidt
    & Hlen2 & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle2 & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  rewrite Hq in Eb1, Hkept.
  assert (FR2 : sr_fr stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply sr_fr_call; [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | | exact Hlen2].
    - intros a Ha. right. left. rewrite Hq in Ha. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a Hf Ha. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros p k Hpk. exact (Hub2 p k (proj1 (Hub p k Hpk)) (Hne p k Hpk)).
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. subst a0. destruct (Hd _ _ Hin0); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 FR2 Hrp (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
  - apply (sr_call_kept ALLOC_STACK L A regs mem md (fun a => ptr_addr L q <= a < ptr_addr L q + n) L2 A2 regs2 mem2 md2
      HM Hpost ltac:(unfold ALLOC_STACK in *; lia)).
    intros a Ha Hk. rewrite Hq in Ha. destruct (Hfreed a Ha) as [_ Hn']. exact (Hn' (proj1 (sr_kept_facts a Hk))).
Qed.

(* An evt run from an SR state of the walk, on the normalized memory, with footprint in the window, the world and
   blocks born after the entry; the continuation sees the end state related to the run's (mem_rel) and sr_fr kept. *)
Lemma g_run : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
        (S - stk <= x < S) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     sr_fr stk S L0 A0 mem0 md0 L A m' md ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (sr_run_norm fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : Frame.munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : Frame.wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    exact (sr_fr_evt stk S L0 A0 mem0 md0 L A mem md m' W FR Hc HS MU' WM' Hro' HW).
Qed.

(* A block's bytes, in the normalized memory, as one cell a callee may write (memcpy's destination). *)
Lemma norm_blk : forall L A mem md x n, aa_MR API L A mem md -> In (x, n) (blocks L A) -> 0 < n ->
  ro_agree rsegs mem -> exists junk, Step.rw_cells rsegs (normalize rsegs mem) x [Cells.CB (Z.to_nat n) junk].
Proof.
  intros L A mem md x n HM Hin Hn Hro. pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hqin) as (R1 & R2). rewrite Hq in R1, R2.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ST : Frame.stk rsegs (normalize rsegs mem) x (x + n)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as ((v & Hv) & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Hni.
    rewrite Hq in Hv, Hni. replace (x + (a - x)) with a in Hv, Hni by lia.
    assert (E : normalize rsegs mem (Z_to_bv 64 a) = Some v).
    { rewrite (mem_rel_rw rsegs mem (normalize rsegs mem) (Z_to_bv 64 a) (mem_rel_normalize rsegs mem Hro)
        (sr_ro_addr_out B a SEGS Hni ltac:(lia))). exact Hv. }
    unfold Mem.wa. split.
    - unfold wview. rewrite E. discriminate.
    - exists v. unfold Mem.mrd. rewrite E. reflexivity. }
  destruct (Frame.stk_carve rsegs _ x (x + n) (Z.to_nat n) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [_ [junk HR]].
  rewrite Z2Nat.id in HR by lia. replace (x + n - n) with x in HR by lia. exists junk. exact HR.
Qed.

(* The walk's window above the image, in the normalized memory, as a stack the callees run on. *)
Lemma norm_stk : forall mem lo hi, ro_agree rsegs mem -> SR_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) -> Frame.stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hro Hlo Hhi H. apply sr_stk; [exact Hlo | exact Hhi |]. intros a Ha.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (sr_in_img_top B a SEGS Hi); lia).
  unfold writable_at. rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
    (sr_ro_addr_out B a SEGS Hni ltac:(unfold SR_RES_TOP in Hlo; lia))).
  pose proof (H a Ha) as W. rewrite SEGS in W. exact W.
Qed.

(* The walk's end: sr_fr from the entry state under call_pre_k with the whole window K gives h_post's call_post_k,
   for any footprint E that holds the world and ctx (and whatever the walk freed). *)
Lemma sr_post : forall K E L0 A0 regs0 mem0 md0 L A regs mem md,
  sr_fr K (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  regs_preserved regs0 regs ->
  (forall a, h_world a -> E a) -> (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> E a) ->
  call_post_k B (aa_MR API) K L0 A0 regs0 mem0 md0 E L A regs mem md.
Proof.
  intros K E L0 A0 regs0 mem0 md0 L A regs mem md
    (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen) Hrp HEw HEc.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hle|].
  split; [intros p n H0 _; exact (proj2 (Hub p n H0))|].
  split; [exact Hrp|]. split; [exact Hmd|].
  split.
  { intros a [Hh|Hi] N0 N1 Nsc NE.
    - destruct (Hhigh a Hh ltac:(intros Hs; apply Nsc; left; exact Hs) ltac:(intros Hs; apply Nsc; right; exact Hs)
        ltac:(intros Hc; apply NE; exact (HEc a Hc))) as [E1 E2].
      split; [exact E1 | tauto].
    - destruct (Himg a Hi ltac:(intros Hs; apply N0; right; exact Hs) ltac:(intros Hc; apply NE; exact (HEc a Hc))
        ltac:(intros Hs; apply Nsc; right; exact Hs) ltac:(intros Hw; apply NE; exact (HEw a Hw))) as [E1 E2].
      split; [exact E1 | tauto]. }
  split.
  { intros p n i H0 _ Hi. assert (Hb : In (ptr_addr L0 p, n) (blocks L0 A0)) by (apply blocks_In; exists p; auto).
    exact (Hbyt _ n i Hb Hi). }
  intros a [Hs|Hs]; [exact (Hstw a Hs) | exact (Herr a Hs)].
Qed.

(* ---------------------------------------------------------------- the cut-free (SRcf) forms, for receive_contract_cf *)

(* sr_run_norm with SRcf (U/AgreeLift.v evt_SRcf_canon: the evt run is also cut-free). *)
Lemma sr_run_norm_cf : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SRcf B (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  pose proof (evt_SRcf_canon B) as EC. cbv zeta in EC. rewrite SEGS in EC.
  apply (EC _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize; [exact sr_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (sr_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

(* malloc at a call site of the walk: the continuation gets the block res of n bytes, born after the entry. *)
Lemma g_malloc_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A n bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @malloc_contract_cf fx'' rc B API) ->
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 n ->
  res_ok_slots A bres -> room_cf md bres n ->
  (forall L' A' regs' mem' md' res,
     sr_fr stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> 4096 <= res -> res + n <= YM05.alloc_ceiling -> res mod 16 = 0 ->
     (forall i, 0 <= i < n -> ~ in_img B (res + i)) ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     res_ok_slots A' (sb_malloc bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     (forall a, sr_kept a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SRcf B (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (ms_malloc B)) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A n bres P MALLOC FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  pose proof (sr_fr_blocks _ _ _ _ _ _ _ _ _ _ FR) as Hblk.
  eapply (SRcf_bind B).
  { apply (MALLOC fx' L A regs mem md n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact H10.
    - exact Hres.
    - exact Hroom. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10 & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
    & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub2 & Hidt & Hlen2 & Hres2).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle2 & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : sr_fr stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply sr_fr_call; [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | | exact Hlen2].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros p k Hin. exact (Hub2 p k (proj1 (Hub p k Hin))).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 res FR2 Hrp G10 ltac:(lia) ltac:(lia) Hal16 Hf3 (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2)))
    Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
    + apply call_post_k_alloc. exact Hpost.
    + exact Hc.
    + exact H1.
    + exact HS.
    + unfold ALLOC_STACK; lia.
    + intros a Ha. destruct Ha.
  - exact Hkept.
  - apply (sr_call_kept ALLOC_STACK L A regs mem md (fun _ => False) L2 A2 regs2 mem2 md2 HM
      ltac:(apply call_post_k_alloc; exact Hpost) ltac:(unfold ALLOC_STACK in *; lia)).
    intros a Hf. destruct Hf.
Qed.

(* free of a block x of n > 0 bytes born after the entry (it misses every entry block). *)
Lemma g_free_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A x n bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @free_contract_cf fx'' rc B API) ->
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 x ->
  In (x, n) (blocks L A) -> 0 < n -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= x \/ x + n <= a) ->
  res_ok_slots A bres ->
  (forall L' A' regs' mem' md',
     sr_fr stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     (exists b1 b2, blocks L A = b1 ++ (x, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     res_ok_slots A' (sb_free bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun a => a = x) ->
     (forall a, sr_kept a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SRcf B (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (ms_free B)) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A x n bres P FREE FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hin Hn Hd Hres K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  pose proof (sr_fr_blocks _ _ _ _ _ _ _ _ _ _ FR) as Hblk.
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, x <= a < x + n -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Himgx.
    rewrite Hq in R1, R2, Himgx. replace (x + (a - x)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  (* no entry user block is the freed one: an entry block at x would have 0 bytes, and the freed pointer holds n *)
  assert (Hne : forall p k, In (p, k) (user_blocks A0) -> p <> q).
  { intros p k Hpk Epq. subst p. destruct (Hub q k Hpk) as [HinA Hpa].
    assert (HB0 : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
    rewrite <- Hpa, Hq in HB0. destruct (Hd x k HB0) as [Hk|Hk]; [|lia].
    assert (Ek : k = n) by exact (sr_nodup_fst_in _ q k n (YO10.user_block_ptrs_NoDup A HW) HinA Hqin). lia. }
  eapply (SRcf_bind B).
  { apply (FREE fx' L A regs mem md q n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite H10, Hq. reflexivity.
    - exact Hres. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub2 & Hidt
    & Hlen2 & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle2 & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  rewrite Hq in Eb1, Hkept.
  assert (FR2 : sr_fr stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply sr_fr_call; [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | | exact Hlen2].
    - intros a Ha. right. left. rewrite Hq in Ha. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a Hf Ha. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros p k Hpk. exact (Hub2 p k (proj1 (Hub p k Hpk)) (Hne p k Hpk)).
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. subst a0. destruct (Hd _ _ Hin0); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 FR2 Hrp (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
  - apply (sr_call_kept ALLOC_STACK L A regs mem md (fun a => ptr_addr L q <= a < ptr_addr L q + n) L2 A2 regs2 mem2 md2
      HM Hpost ltac:(unfold ALLOC_STACK in *; lia)).
    intros a Ha Hk. rewrite Hq in Ha. destruct (Hfreed a Ha) as [_ Hn']. exact (Hn' (proj1 (sr_kept_facts a Hk))).
Qed.

(* An evt run from an SR state of the walk, on the normalized memory, with footprint in the window, the world and
   blocks born after the entry; the continuation sees the end state related to the run's (mem_rel) and sr_fr kept. *)
Lemma g_run_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  sr_fr stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
        (S - stk <= x < S) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     sr_fr stk S L0 A0 mem0 md0 L A m' md ->
     SRcf B (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (sr_run_norm_cf fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : Frame.munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : Frame.wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    exact (sr_fr_evt stk S L0 A0 mem0 md0 L A mem md m' W FR Hc HS MU' WM' Hro' HW).
Qed.

End F.
