(* ARM 4 (op_decide) glue, part 1: the facts the SR chain of LG4.v uses that do not depend on one cut.
   - CUT up to eqv_cl, and the pure part of a cut predicate;
   - lg4_seg: LFrRun.cut_evt with a memory fact X that every c45 segment keeps (its seg_fp leaves X's bytes);
   - the loop-head environment lg_E g md mk: S, the payload (in the entry blocks), lh_reg inside lkeep;
   - the room of hb with the temporary text_of blocks (opt_hb), and the hp side condition;
   - bytes carried by a read-only range ([A_RO_LO, A_RO_END) is one r-- segment of the image), by seg_fp,
     and by lcarry (the c45 cut memory: c45_kmg, c45_keep and the frame cells). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrLo LFrEn LGlue
  LC45Defs LC45Call LC45ComLib.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Facts of one memory or one list
   ========================================================================== *)

(* the 8-byte words of two cells at one address *)
Lemma lg4_cell2 : forall m A v w, rw_cells rsegs m A [C8 v; C8 w] ->
  bytes_at rsegs m A (le8 v) /\ bytes_at rsegs m (A + 8) (le8 w).
Proof.
  intros m A v w [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B1 B2].
  rewrite length_le8 in B2. change (Z.of_nat 8) with 8 in B2.
  apply bytes_at_app in B2 as [B2 _]. split; [exact B1 | exact B2].
Qed.

Lemma lg4_word_det : forall m A v w, bytes_at rsegs m A (le8 v) -> bytes_at rsegs m A (le8 w) -> v = w.
Proof.
  intros m A v w Hv Hw.
  pose proof (c45c_bytes_at_det m A _ _ Hv Hw ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Lemma lg4_cells2_det : forall m A v w v' w', rw_cells rsegs m A [C8 v; C8 w] -> rw_cells rsegs m A [C8 v'; C8 w'] ->
  v = v' /\ w = w'.
Proof.
  intros m A v w v' w' H H'. destruct (lg4_cell2 m A v w H) as [H1 H2].
  destruct (lg4_cell2 m A v' w' H') as [H1' H2'].
  split; [exact (lg4_word_det m A v v' H1 H1') | exact (lg4_word_det m (A + 8) w w' H2 H2')].
Qed.

(* the suffix of a byte run *)
Lemma lg4_bytes_skip : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (skipn (Z.to_nat k) bs) /\
  Z.of_nat (length (skipn (Z.to_nat k) bs)) = Z.of_nat (length bs) - k.
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) bs) in H.
  apply bytes_at_app in H as [_ H2]. rewrite length_firstn in H2.
  assert (Hle : (Z.to_nat k <= length bs)%nat) by lia.
  rewrite (Nat.min_l _ _ Hle) in H2. rewrite Z2Nat.id in H2 by lia.
  split; [exact H2|]. rewrite length_skipn. lia.
Qed.

(* a read-only range: the first PT_LOAD of the plain image, r-- *)
Lemma lg4_ro_chk : zall (fun a => Mem.ro_addr rsegs (Z_to_bv 64 a)) A_RO_LO (Z.to_nat (A_RO_END - A_RO_LO)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lg4_ro_addr : forall a, A_RO_LO <= a < A_RO_END -> Mem.ro_addr rsegs (Z_to_bv 64 a) = true.
Proof.
  intros a Ha. apply (zall_ok _ (Z.to_nat (A_RO_END - A_RO_LO)) A_RO_LO lg4_ro_chk).
  rewrite Z2Nat.id by (unfold A_RO_LO, A_RO_END; lia). lia.
Qed.

(* two memories without read-only bytes of their own read the same read-only bytes *)
Lemma lg4_ro_bytes : forall m m' a bs, mem_inv rsegs m -> mem_inv rsegs m' ->
  A_RO_LO <= a -> a + Z.of_nat (length bs) <= A_RO_END -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs M M' H1 H2 (Ha & Hl & H). split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi).
  assert (R : Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true) by (apply lg4_ro_addr; lia).
  unfold Mem.mrd, Mem.wa.
  destruct (m (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:E1.
  { exfalso. rewrite (M _ b E1) in R. discriminate R. }
  destruct (m' (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:E2.
  { exfalso. rewrite (M' _ b E2) in R. discriminate R. }
  reflexivity.
Qed.

Lemma lg4_ro_cstr : forall m m' a s, mem_inv rsegs m -> mem_inv rsegs m' ->
  A_RO_LO <= a -> a + Z.of_nat (length s) + 1 <= A_RO_END -> cstr_at m a s -> cstr_at m' a s.
Proof.
  intros m m' a s M M' H1 H2 [Hb Hn]. split; [|exact Hn].
  apply (lg4_ro_bytes m m' a _ M M' H1); [rewrite length_app; cbn [length]; lia | exact Hb].
Qed.

(* a segment's footprint leaves every byte outside own_w *)
Lemma lg4_fp_bytes : forall S hp m m' a bs, seg_fp S hp m m' -> bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ own_w S hp x) -> bytes_at rsegs m' a bs.
Proof.
  intros S hp m m' a bs (W & MU & _ & HW) (Ha & Hl & H) Hn. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi).
  assert (Ho : Frame.outside W (a + Z.of_nat i)).
  { destruct (lfr_outside_dec W (a + Z.of_nat i)) as [O|O]; [exact O|].
    exfalso. apply (Hn (a + Z.of_nat i)); [lia|]. apply HW; [lia | exact O]. }
  pose proof (lfr_munch_at W m m' (a + Z.of_nat i) MU ltac:(lia) Ho) as E.
  unfold Mem.mrd, Mem.wa. rewrite E. reflexivity.
Qed.

Lemma lg4_fp_cstr : forall S hp m m' a s, seg_fp S hp m m' -> cstr_at m a s ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> ~ own_w S hp x) -> cstr_at m' a s.
Proof.
  intros S hp m m' a s Hfp [Hb Hn] Hx. split; [|exact Hn].
  apply (lg4_fp_bytes S hp m m' a _ Hfp Hb). rewrite length_app. cbn [length]. intros x Hr. apply Hx. lia.
Qed.

(* bytes and cells carried by lcarry over a region that covers them *)
Lemma lg4_rw : forall (U : Z -> Prop) m m' A cs, lcarry U m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> U x) -> rw_cells rsegs m A cs -> rw_cells rsegs m' A cs.
Proof. intros U m m' A cs C HU H. exact (ml_use _ U _ m m' (ml_rw_cells A cs) C HU H). Qed.

Lemma lg4_bytes : forall (U : Z -> Prop) m m' a bs, lcarry U m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> U x) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. intros U m m' a bs C HU H. exact (ml_use _ U _ m m' (ml_bytes_at a bs) C HU H). Qed.

Lemma lg4_cstr : forall (U : Z -> Prop) m m' a s, lcarry U m m' ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> U x) -> cstr_at m a s -> cstr_at m' a s.
Proof.
  intros U m m' a s C HU H. apply (ml_use _ U _ m m' (ml_cstr_at a s) C); [|exact H].
  intros x Hx. apply HU. unfold lo_rng in Hx. lia.
Qed.

(* the c45 cut memory outside the frame: the fake kernel, the model, the marks, the image views, the
   payload; errno and the guard words come from the allocator call's post *)
Lemma lg4_kk : forall E i kbs mbs gbs (U : Z -> Prop) m m', lenv_ok E ->
  (forall x, lh_reg E x -> x < e_S E - SLOT_FRAME -> U x) -> lcarry U m m' ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  c45_kmg E i kbs mbs gbs m -> c45_keep E m -> c45_kmg E i kbs mbs gbs m' /\ c45_keep E m'.
Proof.
  intros E i kbs mbs gbs U m m' HE HU C Er Gu
    (NL & NW & IT & O1 & O2 & O3 & O4 & MD & MW & MK & KW & KA) (GN & OD & PR & LA & TX & IP & _ & _ & PL).
  pose proof HE as (HS1 & _ & _ & (Bmd1 & Bmd2 & _) & (Bmk1 & Bmk2 & _) & _ & _ & _ & _ & (Bp1 & Bp2 & _) & _).
  assert (LO : forall x, x < 0x960e0 -> x < e_S E - SLOT_FRAME)
    by (intros x Hx; unfold SLOT_FRAME, SLOT_STACK_Z in *; lia).
  assert (K : forall (V : Z -> Prop), (forall x, V x -> lh_reg E x /\ x < e_S E - SLOT_FRAME) -> lcarry V m m').
  { intros V HV. apply (lcarry_mono V U m m'); [|exact C]. intros x Hx. destruct (HV x Hx) as [H1 H2].
    exact (HU x H1 H2). }
  assert (NL' : nlk_at m' kbs).
  { apply (ml_nlk_at kbs m m'); [|exact NL]. apply K. intros x Hx. split; [apply lh_reg_gnl; exact Hx|].
    apply LO. unfold lo_rng, A_G_NL, NK_SIZE in Hx. lia. }
  assert (IT' : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_iftab kbs m m'); [|split; [exact IT | exact IP]]. apply K. intros x Hx.
    split; [apply lo_iftab_lh; exact Hx|]. apply LO.
    unfold lo_iftab_reg, lo_odd_str, lo_rng, A_G_NL, NK_IF_NAME, NK_IF_INDEX, A_G_NAMES, G_NAMES_SIZE in Hx. lia. }
  assert (MD' : model_at m' (e_md E) mbs).
  { apply (ml_model_at (e_md E) mbs m m'); [|exact MD]. apply K. intros x Hx.
    split; [apply lh_reg_md; exact Hx|]. unfold lo_rng, SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  assert (MK' : marks_at m' (e_mk E) gbs).
  { apply (ml_marks_at (e_mk E) gbs m m'); [|exact MK]. apply K. intros x Hx.
    split; [apply lh_reg_mk; exact Hx|]. unfold lo_rng, SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  assert (GN' : gnames_at m').
  { apply (ml_gnames_at m m'); [|exact GN]. apply K. intros x Hx. split; [apply lh_reg_gnames; exact Hx|].
    apply LO. unfold lo_rng, A_G_NAMES, G_NAMES_SIZE in Hx. lia. }
  assert (OD' : odd_at m').
  { apply (ml_odd_at m m'); [|exact OD]. apply K. intros x [Hx|Hx].
    - split; [apply lh_reg_oddtab; exact Hx|]. apply LO. unfold lo_rng, A_ODD in Hx. lia.
    - split; [apply lh_reg_oddstr; exact Hx|]. apply LO. unfold lo_odd_str, lo_rng in Hx. lia. }
  assert (PR' : policy_ro m').
  { apply (ml_policy_ro m m'); [|exact PR]. apply K. intros x Hx. split; [apply lh_reg_pol; exact Hx|].
    apply LO. unfold lo_pol_reg, lo_rng, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in Hx. lia. }
  assert (LA' : la_ok m').
  { apply (ml_la_ok m m'); [|exact LA]. apply K. intros x Hx. split; [apply lh_reg_la; exact Hx|].
    apply LO. unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. lia. }
  assert (TX' : texts_at m').
  { apply (ml_texts_at m m'); [|exact TX]. apply K. intros x Hx. split; [apply lh_reg_texts; exact Hx|].
    apply LO. unfold lo_rng, A_TEXTS in Hx. lia. }
  assert (PL' : bytes_at rsegs m' (e_p0 E) (e_pl E)).
  { apply (lg4_bytes (fun x => lh_reg E x /\ x < e_S E - SLOT_FRAME) m m' _ _ (K _ (fun x H => H)));
      [|exact PL].
    intros x Hx. split; [apply lh_reg_pl; exact Hx|]. unfold SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  destruct IT' as [IT' IP'].
  split.
  - repeat (split; [assumption|]). assumption.
  - repeat (split; [assumption|]). assumption.
Qed.

(* ==========================================================================
   2. hb with the temporary blocks
   ========================================================================== *)

Lemma lg4_hb_bytes_perm : forall h h', Permutation h h' -> hb_bytes h = hb_bytes h'.
Proof.
  intros h h' HP. induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
  - reflexivity.
  - rewrite IH. reflexivity.
  - ring.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma lg4_hx : forall g T, (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  (length (hx g T) <= 1)%nat /\ 0 <= hb_bytes (hx g T) <= MF_BLOCK.
Proof.
  intros g T HT. unfold hx, hb_bytes, MF_BLOCK in *. destruct (lg_T g) as [|t l].
  - destruct HT as [-> | (f & ->)]; cbn; split; lia.
  - cbn. split; lia.
Qed.

Lemma lg4_room0 : forall g E hb T, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  (length hb <= 3)%nat /\ 0 <= hb_bytes hb <= MD_SIZE + MK_SIZE + MF_BLOCK.
Proof.
  intros g E hb T HI HT. unfold hb_inv in HI. rewrite (Permutation_length HI), (lg4_hb_bytes_perm _ _ HI).
  destruct (lg4_hx g T HT) as [H1 H2]. cbn [length]. rewrite !hb_bytes_cons. cbn [snd].
  unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; lia.
Qed.

Lemma lg4_room1 : forall hb r n, (length hb <= 3)%nat -> 0 <= hb_bytes hb <= MD_SIZE + MK_SIZE + MF_BLOCK ->
  (r <> 0 -> 0 <= n <= 320) -> lroom_hb (opt_hb r n hb) /\ (length (opt_hb r n hb) <= 4)%nat /\
  0 <= hb_bytes (opt_hb r n hb) <= MD_SIZE + MK_SIZE + MF_BLOCK + 320.
Proof.
  intros hb r n HL HB Hn. unfold lroom_hb, opt_hb. destruct (Z.eqb_spec r 0) as [E|E].
  - unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; [split; lia | split; lia].
  - specialize (Hn E). cbn [length]. rewrite hb_bytes_cons. cbn [snd].
    unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; [split; lia | split; lia].
Qed.

Lemma lg4_room2 : forall hb r n, (length hb <= 4)%nat -> 0 <= hb_bytes hb <= MD_SIZE + MK_SIZE + MF_BLOCK + 320 ->
  (r <> 0 -> 0 <= n <= 320) -> lroom_hb (opt_hb r n hb).
Proof.
  intros hb r n HL HB Hn. unfold lroom_hb, opt_hb. destruct (Z.eqb_spec r 0) as [E|E].
  - unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; lia.
  - specialize (Hn E). cbn [length]. rewrite hb_bytes_cons. cbn [snd].
    unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; lia.
Qed.

Lemma lg4_opt_incl : forall r n hb, incl hb (opt_hb r n hb).
Proof. intros r n hb t Ht. unfold opt_hb. destruct (r =? 0); [exact Ht | right; exact Ht]. Qed.

Lemma lg4_opt_nz : forall r n hb, r <> 0 -> opt_hb r n hb = (r, n) :: hb.
Proof. intros r n hb H. unfold opt_hb. destruct (Z.eqb_spec r 0); [contradiction | reflexivity]. Qed.

Lemma lg4_opt_z : forall n hb, opt_hb 0 n hb = hb.
Proof. reflexivity. Qed.

Lemma lg4_opt_app : forall r n hb, opt_hb r n hb = opt_hb r n [] ++ hb.
Proof. intros r n hb. unfold opt_hb. destruct (r =? 0); reflexivity. Qed.

Lemma lg4_room_hb0 : forall hb, (length hb <= 3)%nat -> 0 <= hb_bytes hb <= MD_SIZE + MK_SIZE + MF_BLOCK ->
  lroom_hb hb.
Proof. intros hb HL HB. unfold lroom_hb. unfold MD_SIZE, MK_SIZE, MF_BLOCK in *. split; lia. Qed.

(* md and mk are in every hb that holds the loop head's, and never kept *)
Lemma lg4_hp : forall g E hb0 hb T, hb_inv g E hb0 T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  incl hb0 hb -> forall t, In t (c45_hp E) -> In t hb /\ ~ In t T.
Proof.
  intros g E hb0 hb T HI HT Hinc t Ht. destruct (hp_md_mk g E hb0 T HI HT t Ht) as [H1 H2].
  split; [exact (Hinc _ H1) | exact H2].
Qed.

Lemma lg4_md_in : forall g E hb T, hb_inv g E hb T -> In (e_md E, MD_SIZE) hb /\ In (e_mk E, MK_SIZE) hb.
Proof.
  intros g E hb T HI. unfold hb_inv in HI. split.
  - apply (Permutation_in _ (Permutation_sym HI)). left. reflexivity.
  - apply (Permutation_in _ (Permutation_sym HI)). right. left. reflexivity.
Qed.

(* a block of at most 320 bytes is not the kept FILE *)
Lemma lg4_not_T : forall (T : list (Z * Z)) (a n : Z), (T = [] \/ exists f, T = [(f, MF_BLOCK)]) -> n <= 320 ->
  ~ In (a, n) T.
Proof.
  intros T a n [-> | (f & ->)] Hn H; [exact H|]. destruct H as [H|[]]. injection H as _ E.
  unfold MF_BLOCK in E. lia.
Qed.

(* ==========================================================================
   3. The SR frame
   ========================================================================== *)

Lemma lg4_eqv_canon : forall (Q : machine_state -> Prop) R F pc fc m ro,
  Q (MS (Regs6ss.mkR_of R) F pc fc None m ro) -> eqv_cl Q (MS R F pc fc None m ro).
Proof.
  intros Q R F pc fc m ro H. exists (MS (Regs6ss.mkR_of R) F pc fc None m ro). split; [exact H|].
  unfold Regs6ss.ms_eqv. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS].
  split; [exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv R))|]. repeat split.
Qed.

(* the program points of the arm's two ends *)
Lemma lg4_lh_pc : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lg4_ex_pc : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s8
                  & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Section L4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).

Lemma lg4_cut_eqv : forall g pc hb T (Q : machine_state -> Prop) c,
  CUT B API g pc hb T (eqv_cl Q) c -> CUT B API g pc hb T Q c.
Proof.
  intros g pc hb T Q c (fx' & L & A & regs & mem & md & E & Hf & HL & HE).
  exists fx', L, A, regs, mem, md. split; [exact E|]. split; [exact Hf|]. split; [exact HL|].
  exact (c45_eqv_cl_idem Q _ HE).
Qed.

Lemma lg4_cut_pure : forall g pc hb T (Q : machine_state -> Prop) (X : Prop) c,
  CUT B API g pc hb T (fun ms => Q ms /\ X) c -> X /\ CUT B API g pc hb T Q c.
Proof.
  intros g pc hb T Q X c (fx' & L & A & regs & mem & md & E & Hf & HL & (c0 & (HQ & HX) & He)).
  split; [exact HX|]. exists fx', L, A, regs, mem, md. split; [exact E|]. split; [exact Hf|]. split; [exact HL|].
  exists c0. split; [exact HQ | exact He].
Qed.

(* a c45 segment (post eqv_cl (c45_post E m0 Q')) as a cut-to-cut step, carrying a memory fact X that
   every c45 segment footprint keeps *)
Lemma lg4_seg : forall g E pc hb T (Q : machine_state -> Prop) pc' (Q' : machine_state -> Prop)
    (X : (word -> option byte) -> Prop) c,
  e_S E = lg_S g ->
  CUT B API g pc hb T (fun ms => Q ms /\ X (ms_mem ms)) c ->
  (forall t, In t (c45_hp E) -> In t hb /\ ~ In t T) ->
  (forall ms, Q ms -> evt rsegs (eqv_cl (c45_post E (ms_mem ms) Q')) ms) ->
  (forall m m', seg_fp (e_S E) (c45_hp E) m m' -> X m -> X m') ->
  (forall ms', Q' ms' -> exists R F fc m, ms' = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\ frm0 fc) ->
  SR segs c (CUT B API g pc' hb T (fun ms => Q' ms /\ X (ms_mem ms))).
Proof.
  intros g E pc hb T Q pc' Q' X c HS HC Hhp Hseg HX Hform.
  apply (cut_evt B API FF g pc hb T (c45_hp E) _ pc' _ c HC Hhp).
  - intros ms (HQ & HXm). eapply evt_mono; [exact (Hseg ms HQ)|].
    intros ms' (c1 & (HQ' & Hfp) & Heq). exists c1. split; [|exact Heq].
    split; [split; [exact HQ' | exact (HX _ _ Hfp HXm)]|]. rewrite <- HS. exact Hfp.
  - intros ms' (HQ' & _). exact (Hform ms' HQ').
Qed.

(* the loop head's environment *)
Lemma lg4_pay : forall g md mk, LGV B API g -> lenv_ok (lg_E g md mk) ->
  0 < lg_n g /\ e_p0 (lg_E g md mk) = lg_p g /\ Z.of_nat (length (e_pl (lg_E g md mk))) = lg_n g /\
  (forall y, e_p0 (lg_E g md mk) <= y < e_p0 (lg_E g md mk) + Z.of_nat (length (e_pl (lg_E g md mk))) ->
     in_blk0 g y).
Proof.
  intros g md mk HV HE.
  pose proof (len_ghost_ok B API FF g HV) as (_ & _ & _ & Hn & _ & Hp).
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  change (e_pl (lg_E g md mk)) with (lg_pl g) in *. change (e_p0 (lg_E g md mk)) with (len_p0 g).
  assert (Hn0 : 0 < lg_n g) by lia.
  destruct (Hp Hn0) as (Hp0 & _).
  split; [exact Hn0|]. split; [exact Hp0|]. split; [lia|].
  rewrite Hp0, <- Hn. intros y Hy.
  destruct HV as ((Hpre & _) & _).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcase & _).
  destruct Hcase as [(Hz & _) | (_ & q & Hq & Hq2)]; [lia|].
  exists (lg_p g), (lg_n g). split; [|lia].
  unfold blocks. apply in_map_iff. exists (q, lg_n g). cbn [fst snd]. rewrite Hq2. split; [reflexivity | exact Hq].
Qed.

Lemma lg4_lkeep_mono : forall g hb hb' x, incl hb' hb -> lkeep B g hb' x -> lkeep B g hb x.
Proof.
  intros g hb hb' x Hi [H|[H|[(t & k & Hin & Hx)|H]]];
    [left; exact H | right; left; exact H | | right; right; right; exact H].
  right; right; left. exists t, k. split; [exact (Hi _ Hin) | exact Hx].
Qed.

Lemma lg4_keep : forall g md mk hb0 hb T x, LGV B API g -> lenv_ok (lg_E g md mk) ->
  hb_inv g (lg_E g md mk) hb0 T -> incl hb0 hb -> lh_reg (lg_E g md mk) x -> lkeep B g hb x.
Proof.
  intros g md mk hb0 hb T x HV HE HI Hinc Hx.
  apply (lg4_lkeep_mono g hb hb0 x Hinc).
  destruct (lg4_pay g md mk HV HE) as (_ & _ & _ & Hpl).
  destruct (lg4_md_in g _ hb0 T HI) as [Hmd Hmk].
  exact (lh_reg_keep_ok B API SH SK g hb0 (lg_E g md mk) x FF HE eq_refl Hmd Hmk Hpl Hx).
Qed.

(* a fresh block apart from md / mk keeps a string inside it across any c45 segment *)
Definition lg4_x1 (own k : Z) (m : word -> option byte) : Prop :=
  own <> 0 -> exists t, cstr_at m own t /\ Z.of_nat (length t) + 1 <= k.

Lemma lg4_x1_fp : forall g E hb own k m m', e_S E = lg_S g ->
  In (e_md E, MD_SIZE) hb -> In (e_mk E, MK_SIZE) hb ->
  (own <> 0 -> lfresh B g hb own k) ->
  seg_fp (e_S E) (c45_hp E) m m' -> lg4_x1 own k m -> lg4_x1 own k m'.
Proof.
  intros g E hb own k m m' HS Hmd Hmk Hf Hfp HX Hnz.
  destruct (HX Hnz) as (t & Hc & Hl). exists t. split; [|exact Hl].
  destruct (Hf Hnz) as (_ & H4096 & Htop & Himg & Hhb & _).
  apply (lg4_fp_cstr _ _ m m' own t Hfp Hc). intros x Hx Hw.
  assert (IW : lfr_iw x -> False).
  { intros Hi. apply (Himg (x - own)); [lia|]. replace (own + (x - own)) with x by lia.
    exact (proj1 (lfr_iw_facts B API FF x Hi)). }
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|(a & n & Hin & Hw)]]]]].
  - rewrite HS in Hw. unfold SLOT_STACK, SLOT_STACK_Z in *. lia.
  - apply IW. left. unfold A_G_NL, NK_SIZE in Hw. lia.
  - apply IW. left. unfold A_G_NAMES, G_NAMES_SIZE in Hw. lia.
  - apply IW. left. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE in Hw. lia.
  - apply IW. right. unfold A_ERRNO, A_TP, ERRNO_TP_OFF in Hw. lia.
  - destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-.
    + destruct (Hhb _ _ Hmd); lia.
    + destruct (Hhb _ _ Hmk); lia.
Qed.

Lemma lg4_fresh_out : forall g hb r n, lfresh B g hb r n -> 4096 <= r /\ r + n <= lg_S g - SLOT_STACK_Z.
Proof. intros g hb r n (_ & H1 & H2 & _). unfold SLOT_STACK, SLOT_STACK_Z in *. split; lia. Qed.

End L4.
