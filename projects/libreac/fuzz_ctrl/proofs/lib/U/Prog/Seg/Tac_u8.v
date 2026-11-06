(* Frame helpers for batch u8 (C01-C06, W01-W04, X01, X02) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan), ported
   from the u4 helpers (a working branch Tac_u4.v: the bundle transport, u4_mid, the block bound), the u1 helpers
   (a working branch Tac_u1.v: the allocator transport) and the plain b8 helpers (a working branch Tac_b8.v:
   b8_run_to, the free call, Post from FR). Ubsan stack offsets on libreac v1.9.0: M7 sp+8, TF sp+16, FC sp+24,
   first (FS: have, n, body) sp+36..63, ID sp+76, OUR sp+114, FG sp+120, B sp+1752; OVF is s0 = sp+128; the low
   slots are [sp+8, sp+192). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Regs6ss RegisterBridge Exec Cells Step Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m.
Import ListNotations.
Open Scope Z_scope.

(* ---- Memory and registers ---- *)

Lemma u8_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia | exact (IH a n a' n' H4 H1 H2)].
Qed.

Lemma u8_ba : forall W mem m' a bs, bytes_at rsegs mem a bs -> Frame.munch W mem m' ->
  disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof. intros W mem m' a bs H MU D. exact (bytes_at_transport rsegs W mem m' a bs H MU D). Qed.

Lemma u8_q64 : forall W mem m' a v, q64 mem a v -> Frame.munch W mem m' -> disjoint_from W a 8 -> q64 m' a v.
Proof. unfold q64. intros W mem m' a v H MU D. apply (u8_ba W mem); [exact H | exact MU|]. rewrite length_le8. exact D. Qed.

Lemma u8_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma u8_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. unfold rg. intros regs regs' r v E H. rewrite E. exact H. Qed.

Lemma u8_c_bytes : forall m A c, Step.rw_cells rsegs m A [c] -> bytes_at rsegs m A (Cells.cbytes c).
Proof.
  intros m A c H. pose proof (sl_cells_bytes m A [c] H) as Hb. cbn [Cells.cells_bytes] in Hb.
  rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma u8_stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi ->
  Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H3) H4 H5. split; [lia|]. split; [lia|]. intros a Ha. apply H3. lia. Qed.

(* The normalized memory agrees with the image on every read-only byte. *)
Lemma u8_ro_norm : forall m, ro_agree rsegs (normalize rsegs m).
Proof. intros m a Hro. unfold Mem.mrd, normalize. rewrite Hro. reflexivity. Qed.

(* Loads from known bytes. *)
Lemma u8_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  rewrite Z.add_0_r, skipn_O, firstn_all in E. exact E.
Qed.

Lemma u8_ld8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (u8_ovr m a _ H) as E. rewrite length_le8 in E. exact E. Qed.

(* A stored word cell is the cell of its bytes. *)
Lemma u8_rw_c4 : forall m A v, Step.rw_cells rsegs m A [Cells.C4 v] -> Step.rw_cells rsegs m A [Cells.CB 4 (le4 v)].
Proof.
  intros m A v [[_ Hb] Hw]. split; [split; [cbn [Cells.cells_wf Cells.cell_wf]; split; [apply length_le4 | exact I]
  | exact Hb] | exact Hw].
Qed.

Lemma u8_rw_c8 : forall m A v, Step.rw_cells rsegs m A [Cells.C8 v] -> Step.rw_cells rsegs m A [Cells.CB 8 (le8 v)].
Proof.
  intros m A v [[_ Hb] Hw]. split; [split; [cbn [Cells.cells_wf Cells.cell_wf]; split; [apply length_le8 | exact I]
  | exact Hb] | exact Hw].
Qed.

(* Slices of known bytes: the frame's block blk = Φ[18 .. 50) at Φ + 18. *)
Lemma u8_at_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H1 & H2 & H3) Hk.
  assert (L : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n) as [_|]; [|lia].
  rewrite nth_error_skipn. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H3. lia.
Qed.

Lemma u8_blk_at : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m (phi + 18) (t_blk inp j).
Proof.
  intros m phi inp j H Hl.
  assert (HG : bytes_at rsegs m phi (t_g inp j)).
  { rewrite (u8_g_bytes inp j Hl). pose proof (u8_at_slice m phi (t_phi inp j) 0 50 H) as E.
    cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r in E. apply E. rewrite u8_phi_length. lia. }
  pose proof (u8_at_slice m phi (t_g inp j) 18 32 HG) as E. rewrite u8_tg_len in E.
  exact (E ltac:(lia)).
Qed.

(* Stack addresses lie above every image segment. *)
Lemma u8_rom_none : forall a, SL_TOP <= a < 2 ^ 64 -> PropExec.seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha. destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:Ef.
  - apply sl_find_top in Ef. unfold SL_TOP in *. rewrite wa_unsigned in Ef by lia. lia.
  - exact (seg_rom_unmapped rsegs (wa a) Ef).
Qed.

Lemma u8_in_relro : forall a, 0x1fc48 <= a < 0x20b18 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 0x1fc48, 3792. split; [left; reflexivity | lia]. Qed.

Lemma u8_in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma u8_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

(* ---- The turn-j bundles across a run that writes only in W ---- *)

(* LK: j in s1, OVF = s0 = sp+128, S2 = s2 = 1 (registers); our and the -7 pair in the low slots. *)
Lemma u8_LK_keep : forall g j regs regs' mem m' W,
  LK g j regs mem -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  Frame.munch W mem m' -> disjoint_from W (spk g 8) 184 -> LK g j regs' m'.
Proof.
  intros g j regs regs' mem m' W (Hj & H9 & HOUR & HM7 & HOVF & H18) E8 E9 E18 MU D.
  split; [exact Hj|]. split; [exact (u8_rg _ _ _ _ E9 H9)|].
  split; [unfold OURb in *; apply (u8_ba W mem); [exact HOUR | exact MU|]; rewrite OUR_length;
          apply (u8_dj_sub W _ _ _ _ D); unfold spk; lia|].
  split; [unfold M7 in *; apply (u8_q64 W mem m' _ _ HM7 MU); apply (u8_dj_sub W _ _ _ _ D); unfold spk; lia|].
  split; [unfold OVF in *; exact (u8_rg _ _ _ _ E8 HOVF)|].
  unfold S2 in *. exact (u8_rg _ _ _ _ E18 H18).
Qed.

Lemma u8_FC_keep : forall g j regs regs' mem m' W,
  FC g j regs mem -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> Frame.munch W mem m' ->
  disjoint_from W (spk g 8) 184 -> FC g j regs' m'.
Proof.
  intros g j regs regs' mem m' W (H24 & H21 & H22) E21 E22 MU D.
  split; [apply (u8_q64 W mem m' _ _ H24 MU); apply (u8_dj_sub W _ _ _ _ D); unfold spk; lia|].
  split; [exact (u8_rg _ _ _ _ E21 H21) | exact (u8_rg _ _ _ _ E22 H22)].
Qed.

(* s0, s1, s2, s5, s6, s7 kept: the registers of FT; s8 too for VC (CC7). *)
Definition CK (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\
  getr regs' 24 = getr regs 24.

Lemma u8_FT_keep : forall g j phi regs regs' mem m' W,
  FT g j phi regs mem -> CK regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 184 -> FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HLK & HFC & H23 & Hphi & H18) (E8 & E9 & E18 & E21 & E22 & E23 & E24)
    MU Dp D.
  split; [exact (u8_LK_keep g j regs regs' mem m' W HLK E8 E9 E18 MU D)|].
  split; [exact (u8_FC_keep g j regs regs' mem m' W HFC E21 E22 MU D)|].
  split; [exact (u8_rg _ _ _ _ E23 H23)|].
  split; [|exact (u8_rg _ _ _ _ E18 H18)].
  pose proof (u8_t_facts (g_in g) j) as (_ & _ & _ & _ & HL & _).
  apply (u8_ba W mem); [exact Hphi | exact MU|]. rewrite u8_phi_length, Z2Nat.id by lia. exact Dp.
Qed.

Lemma u8_VC_keep : forall g j phi regs regs' mem m' W,
  VC g j phi regs mem -> getr regs' 24 = getr regs 24 -> Frame.munch W mem m' ->
  disjoint_from W (spk g 8) 184 -> disjoint_from W (spk g 1752) 36 -> VC g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (H24 & H16 & HB) E24 MU D DB.
  split; [exact (u8_rg _ _ _ _ E24 H24)|].
  split; [apply (u8_q64 W mem m' _ _ H16 MU); apply (u8_dj_sub W _ _ _ _ D); unfold spk; lia|].
  apply (u8_ba W mem); [exact HB | exact MU|]. rewrite u8_B_length. exact DB.
Qed.

(* A memory bundle taken apart along its own shape: a conjunction conjunct by conjunct, an implication under its
   premise, a byte fact (q64 / u32 / u16 / b8 / bytes_at, unfolded) by the tactic leaf, any other fact as it is.
   The goal is the same bundle over the new memory. *)
Ltac u8_bundle H leaf :=
  lazymatch type of H with
  | _ /\ _ =>
      let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2];
      split; [u8_bundle H1 leaf | u8_bundle H2 leaf]
  | ?A -> _ => let h := fresh "h" in intro h; specialize (H h); u8_bundle H leaf
  | bytes_at rsegs _ _ _ => leaf H
  | _ => exact H
  end.

(* IFS(j): id at sp+76, frag at sp+120, the frame state over `first` [sp+36, sp+63) (its body has at most 22
   bytes, u8_tbody_len); all in the low slots. *)
Lemma u8_IFS_keep : forall g j mem m' W, IFS g j mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 8) 184 -> IFS g j m'.
Proof.
  intros g j mem m' W HI MU D. pose proof (u8_tbody_len (g_in g) j) as Hbl.
  unfold IFS, IDj, IDb, IDB, FGj, FGb, FGB, FSj, FSb, q64, u32, u16, b8 in *.
  u8_bundle HI ltac:(fun H => apply (u8_ba W mem _ _ _ H MU);
    rewrite ?length_le8, ?length_le4, ?length_le2, ?u8_tID_len, ?u8_tFG_len; cbn [length];
    apply (u8_dj_sub W _ _ _ _ D); unfold spk; lia).
Qed.

Lemma u8_IDj_keep : forall g j mem m' W, IDj g j mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 76) 38 -> IDj g j m'.
Proof.
  intros g j mem m' W (HI & Hok) MU D. split; [|exact Hok]. unfold IDB in *.
  apply (u8_ba W mem); [exact HI | exact MU|]. rewrite u8_tID_len. exact D.
Qed.

Lemma u8_CC7_keep : forall g j phi regs regs' mem m' W,
  CC7 g j phi regs mem -> CK regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 184 -> disjoint_from W (spk g 1752) 36 ->
  CC7 g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HFT & HVC & HIFS) HK MU Dp D DB.
  pose proof HK as (_ & _ & _ & _ & _ & _ & E24).
  split; [exact (u8_FT_keep g j phi regs regs' mem m' W HFT HK MU Dp D)|].
  split; [exact (u8_VC_keep g j phi regs regs' mem m' W HVC E24 MU D DB)|].
  exact (u8_IFS_keep g (S j) mem m' W HIFS MU D).
Qed.

Lemma u8_CC_keep : forall g j phi regs regs' mem m' W,
  CC g j phi regs mem -> CK regs regs' -> getr regs' 20 = getr regs 20 -> getr regs' 25 = getr regs 25 ->
  Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 184 -> disjoint_from W (spk g 1752) 36 ->
  CC g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HC7 & H20 & H25) HK E20 E25 MU Dp D DB.
  split; [exact (u8_CC7_keep g j phi regs regs' mem m' W HC7 HK MU Dp D DB)|].
  unfold V2, V7 in *. split; [exact (u8_rg _ _ _ _ E20 H20) | exact (u8_rg _ _ _ _ E25 H25)].
Qed.

(* A disjointness goal over a literal W: every bound is linear in g_S g, phi and the model lengths. *)
Ltac u8_dj := cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME in *; repeat split; try exact I; lia.

(* Every interval of W lies in [S - K, S - 104): so does every address a run writes. *)
Lemma u8_fp : forall g W, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W HW. induction HW as [|[lo hi] W Hh HW IH]; intros x Hx O; cbn [Frame.outside] in O.
  - exfalso. apply O. exact I.
  - cbn [fst snd] in Hh.
    destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
      [lia | | |]; apply IH; try exact Hx; intros O'; apply O; split; try exact O'; lia.
Qed.

Ltac u8_fp_tac := apply u8_fp; repeat constructor; cbn [fst snd]; unfold SLOT_K, SLOT_STACK in *; lia.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

(* frame_facts taken apart by the TYPE of each conjunct, never by its position (an inserted or moved conjunct of
   frame_facts cannot shift a binding); frame_allocator likewise. *)
Ltac u8_ff := let H := fresh "FFd" in pose proof FF as H; red in H; decompose [and] H.

(* The input block: p and p + n are small (GV with PB; n = 0 gives p = empty). *)
Lemma u8_p_range : forall g, GV B empty g -> 0 <= g_p g /\ g_p g + g_n g < 2 ^ 62 /\ 0 <= g_n g < 2 ^ 26.
Proof.
  intros g (Hn & Hp & _ & _ & _ & _ & _ & _ & _ & HPB).
  pose proof YM05.alloc_ceiling_lt as Hlt.
  assert (Hem : empty = 0x31da0) by (u8_ff; assumption).
  destruct HPB as [E|(H1 & H2)].
  - destruct Hp as [(_ & Ep)|(Hn0 & _)]; [|lia]. rewrite E, Ep, Hem. lia.
  - lia.
Qed.

(* Φ, a block of the allocator (hb1 Φ n), lies in [4096, S - K) (HBR). *)
Lemma u8_phi_bnd : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  4096 <= phi /\ phi + n <= g_S g - SLOT_K.
Proof.
  intros g phi n L A regs mem md HFR HP.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  assert (Hin : In (phi, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. left. reflexivity. }
  apply blocks_In in Hin as (p & Hp & Hpin).
  destruct (mr_blocks_range B (aa_MR (APIf rc)) (aa_laws (APIf rc)) L A mem md p n HM Hpin) as (H1 & H2).
  lia.
Qed.

Lemma u8_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP).
    + exact MU'.
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* A straight run that changes no memory: the continuation gets the final registers. *)
Lemma u8_run_to : forall g hb L A regs mem md pc R' pc' (Q : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Exec.evt rsegs (fun ms => ms = MState.MS R' fp_regs pc' fp_csr None mem (seg_rom rsegs))
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall regs', (forall r, getr regs' r = getr R' r) ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' mem (seg_rom (ms_segs B))) md) Q) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb L A regs mem md pc R' pc' Q HF HE HK.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hl].
  apply (kb_run B regs pc mem md (fun R p m => R = R' /\ p = pc' /\ m = mem) Q Hh Hl).
  - rewrite ES. eapply Exec.evt_mono; [exact HE|]. intros ms ->. exists R', pc', mem.
    split; [reflexivity | repeat split].
  - intros R p m regs' (-> & -> & ->) HG. exact (HK regs' HG).
Qed.

Lemma u8_cut_close : forall g pc hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
  CUTST B APIf ra empty g pc hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md).
Proof.
  intros g pc hb P L A regs mem md H1 H2 H3. exists L, A, regs, mem, md. split; [reflexivity|].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma u8_FR_regs : forall g hb L A regs regs' mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem md.
Proof.
  intros g hb L A regs regs' mem md (H0 & H2 & H3 & H4 & HR) E2 E3 E4.
  split; [exact H0|]. rewrite E2, E3, E4. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact HR].
Qed.

(* The RELRO bytes (the catalogue among them) read through the normalized memory are the image's. *)
Lemma u8_relro_mrd : forall mem a, relro B mem -> 0x1fc48 <= a < 0x20b18 ->
  Mem.mrd rsegs (normalize rsegs mem) (wa a) = PropExec.seg_rom rsegs (wa a).
Proof.
  intros mem a HR Ha. unfold relro, G_img_c in HR.
  pose proof (HR a (u8_in_relro a Ha)) as E. rewrite (sl_segs B APIf ra empty FF) in E.
  unfold Mem.mrd, normalize. destruct (Mem.ro_addr rsegs (wa a)); [reflexivity|].
  unfold mbyte in E. unfold wa. exact E.
Qed.

Lemma u8_image_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> PropExec.seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  cbn [Image.image_bytes] in H.
  destruct (PropExec.seg_rom rsegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. replace (A + Z.of_nat 0) with A by lia. exact E.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E' | lia].
Qed.

(* Image bytes of [0x1fc48, 0x20b18) (frame_RELRO) are present in the normalized memory. *)
Lemma u8_relro_bytes : forall mem a n bs, relro B mem -> Image.image_bytes rsegs a n = Some bs ->
  0x1fc48 <= a -> a + Z.of_nat n <= 0x20b18 -> bytes_at rsegs (normalize rsegs mem) a bs.
Proof.
  intros mem a n bs HR HI H0 H1. pose proof (Image.image_bytes_length rsegs n a bs HI) as L.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
  rewrite <- (u8_image_nth n a bs HI i Hi).
  exact (u8_relro_mrd mem (a + Z.of_nat i) HR ltac:(lia)).
Qed.

(* ---- The allocator: free of the live harness block, and Post ---- *)

Lemma u8_alloc : frame_allocator B API.
Proof. u8_ff. match goal with H : _ |- _ => exact (H rc fx) end. Qed.

Lemma u8_ax : AllocExtra B (aa_MR API).
Proof. pose proof u8_alloc as H. red in H. decompose [and] H. assumption. Qed.

Lemma u8_nodup : blocks_nodup B API.
Proof. pose proof u8_alloc as H. red in H. decompose [and] H. assumption. Qed.

(* free's contract: the one use of frame_allocator's free_contract in this file (u8_free_call). *)
Lemma u8_free_c : free_contract B API.
Proof. pose proof u8_alloc as H. red in H. decompose [and] H. assumption. Qed.

Lemma u8_free_addr : ms_free B = 0x17280.
Proof. u8_ff. assumption. Qed.

Lemma u8_relro_full : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. u8_ff.
  match goal with H : _ |- _ => exact (H a Ha) end.
Qed.

Lemma u8_syms : ms_ctx B = 0x52198 /\ ms_lock B = 0x52190 /\ ms_libc B = 0x52120 /\ ms_guard B = 0x52100 /\
  ms_got_guard B = 0x20b18 /\ ms_size_classes B = 0x10750 /\ ms_small_cnt B = 0x107b0 /\ ms_med_cnt B = 0x106f0 /\
  ms_debruijn B = 0x106cc /\ ms_vmlock B = None /\ @sk_ofl_head SH = 0x52550 /\ @sk_ofl_lock SK = 0x52548 /\
  @sk_threaded SK = 0x52120 + 1.
Proof. u8_ff. repeat split; assumption. Qed.

Lemma u8_ra_even : ra mod 2 = 0.
Proof. u8_ff. assumption. Qed.

Lemma u8_resv_ok : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x52120) &&
    (0x52558 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u8_img_sink : forall x, 0x52120 <= x < 0x52558 -> in_img B x.
Proof.
  intros x Hx. pose proof u8_resv_ok as H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold in_img. rewrite (sl_segs B APIf ra empty FF). split; [discriminate|]. exists s. split; [exact Hs | lia].
Qed.

Lemma u8_sink_addr : forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x52558) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof u8_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  split; [apply u8_img_sink; lia|].
  rewrite Ev. unfold static_owned, vml_lo, vml_len. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  rewrite (sl_debruijn_len B APIf ra empty FF).
  cbv iota. unfold CTX_SIZE. lia.
Qed.

Lemma u8_sink_frame : forall mem mem' md md',
  (forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x52558) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4).
  pose proof u8_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

Lemma u8_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> getr regs_c 2 = getr regs 2 ->
  getr regs_c 4 = getr regs 4 -> YK0s.ret_ok (getr regs_c 1) -> call_pre B (aa_MR API) L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0 & _).
  pose proof alloc_ceiling_value as HAC. unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  unfold call_pre. rewrite HSP. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSW; lia|].
  split; [rewrite E4, Htp; exact HTP0|].
  split; [exact HER|].
  intros H. rewrite HIN in H. discriminate.
Qed.

(* free of the one live harness block (p, n): FR with hb = [(p, n)] becomes FR with hb = [], and the frame bytes
   [sp, S) are unchanged. *)
Lemma u8_FR_free : forall g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g [(ptr_addr L p, n)] L A regs mem md ->
  Permutation (blocks L A) ([(ptr_addr L p, n)] ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  call_post B (aa_MR API) L A regs_c mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
  blocks L A = b1 ++ (ptr_addr L p, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) ->
  ro_agree (ms_segs B) mem' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  res_ok_slots A' (sb_free (sb_hb (g_b g) [(ptr_addr L p, n)]) n) ->
  FR B APIf ra empty g [] L' A' regs' mem' md' /\
  Permutation (blocks L' A') ([] ++ blocks (g_L g) (g_A g)) /\
  (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a).
Proof.
  intros g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES'.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0 & _).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof (sl_errno B APIf ra empty FF) as HEC.
  pose proof (sl_errno_val B APIf ra empty FF) as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  assert (HEimg : forall a, ptr_addr L p <= a < ptr_addr L p + n -> ~ in_img B a).
  { intros a Ha. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
    apply (ax_blocks_img u8_ax L A mem md p n); [exact HMR | exact Hpn | lia]. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < YM05.alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha H1 H2 H3. pose proof (sl_in_img_top B a ES Ha) as Hl. unfold SL_TOP in Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img u8_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img u8_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros He. exact (HEimg a He Ha). }
  assert (HH : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 1936 - 8192 <= a < g_S g - 1936) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. pose proof (mr_blocks_range B _ (aa_laws API) _ _ _ _ p n HMR Hpn) as [Hp1 Hp2].
    apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - lia. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 1936 - 8192)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 1936)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  assert (HND : List.NoDup (map fst ((ptr_addr L p, n) :: blocks (g_L g) (g_A g)))).
  { apply (Permutation_NoDup (Permutation_map fst HP)). apply NoDup_ListNoDup. exact (u8_nodup L A mem md HMR). }
  cbn [map fst] in HND. apply List.NoDup_cons_iff in HND as [HNI _].
  split; [|split].
  2:{ rewrite EB'. cbn [app]. apply (Permutation_app_inv b1 b2 [] (blocks (g_L g) (g_A g)) (ptr_addr L p, n)).
      rewrite <- EB. exact HP. }
  2:{ intros a Ha. unfold fsp, SLOT_FRAME in Ha. rewrite <- ES. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (u8_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (u8_relro_full a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact (INIT Hin)|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [F1 F2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [F1 F2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi). unfold blocks_kept in KEPT. apply (KEPT a k i); [| |exact Hi].
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak.
    - intros Ea. subst a. apply HNI. apply in_map_iff. exists (ptr_addr L p, k). split; [reflexivity | exact Hak]. }
  split; [intros a Ha; apply SCW; unfold scratch; right; exact Ha|].
  split.
  { apply (u8_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (u8_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) [(ptr_addr L p, n)] [] A' (ptr_addr L p) n (Permutation_refl _) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma u8_free_call : forall g L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g [(ptr_addr L p, n)] L A regs mem md ->
  Permutation (blocks L A) ([(ptr_addr L p, n)] ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g [] L' A' regs' mem' md' ->
     Permutation (blocks L' A') ([] ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regs_c 1) mem' (seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (mkst regs_c (Z_to_bv 64 0x17280) mem (seg_rom (ms_segs B))) md) Q.
Proof.
  intros g L A regs mem md regs_c p n Q HF HP Hpn E2 E3 E4 Hra H10 K.
  pose proof (u8_call_pre g _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof u8_free_c as FREE.
  rewrite <- u8_free_addr.
  eapply SR_bind; [exact (FREE L A regs_c mem md p n (sb_hb (g_b g) [(ptr_addr L p, n)]) CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (u8_FR_free g L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES') as (HF' & HP' & HK).
  exact (K L' A' regs' mem' md' HF' HP' RP' HK).
Qed.

Lemma u8_GV_S : forall g, GV B empty g -> spZ (g_regs g) = g_S g /\ YM05.alloc_ceiling + SLOT_K <= g_S g <= 2 ^ 47.
Proof.
  intros g (_ & _ & _ & _ & H1 & H2 & _ & H3 & _). unfold spZ. rewrite H3.
  pose proof alloc_ceiling_value. unfold SLOT_K, SLOT_STACK in *. rewrite MState.unsigned_lit by lia. lia.
Qed.

(* RET from FR with no live harness block. *)
Lemma u8_post_FR : forall g L A regs0 regs mem md,
  FR B APIf ra empty g [] L A regs0 mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (g_regs g) regs ->
  Post B APIf ra g (mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom (ms_segs B))) md).
Proof.
  intros g L A regs0 regs mem md HF HP H10 HRP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & HWF & HBD & HIN & HVM & HFA & HFI & HFB & HER & HSN & HRES
    & HSW).
  destruct (u8_GV_S g HGV) as [HSP HS].
  exists L, A, regs, mem, md. split; [reflexivity|].
  split.
  - unfold lib_post. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
    split; [exact H10|]. split; [exact HRP|]. split; [exact HVM|].
    split.
    { intros q k Hq. pose proof (u8_blocks_in (g_L g) (g_A g) q k Hq) as Hb.
      apply (Permutation_in _ (Permutation_sym HP)) in Hb.
      destruct (u8_in_blocks L A _ _ Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
    split.
    { intros a Ha Hn. unfold lib_scratch in Hn. rewrite HSP in Hn.
      assert (N1 : ~ (g_S g - SLOT_K <= a < g_S g)) by (unfold SLOT_K; tauto).
      assert (N2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (HFA a Ha N1 N2) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros a H1 H2 H3 H4. destruct (HFI a H1 H2 H3 H4) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq _ Hi. apply (HFB (ptr_addr (g_L g) q) k i); [apply u8_blocks_in; exact Hq | exact Hi]. }
    intros a [Ha|Ha]; [apply HSW; rewrite HSP in Ha; unfold SLOT_K; exact Ha | apply HER; exact Ha].
  - split; [exact HSN|]. split; [exact HMI|].
    split.
    + exact (resb_end (g_b g) A HRES).
    + intros i Hi. destruct HGV as (_ & [[Hn _]|[_ Hp]] & _); [lia|].
      apply (HFB (g_p g) (g_n g) i Hp Hi).
Qed.

End S.
