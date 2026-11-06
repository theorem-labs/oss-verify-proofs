(* Helpers for the segment lemmas of batch b3 (R19-R24, P01-P06, R00) of fuzz_ctrl LLVMFuzzerTestOneInput (plain):
   b3_mid, sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the continuation, so that
   every bytes_at fact outside W crosses the run by bytes_at_transport. *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. Numerals moved (plain segment table v190-segment-table-plain.md
   (a working note, not in this delivery) 7a / 7c, SlotInv.v frame_facts = lib/FrameAPI.v frame_plain):
   - the RB slots our / id / frag sp+60 / sp+138 / sp+66 -> sp+76 / sp+154 / sp+82 (b3_RB, b3_RB_bytes, b3_RB_S);
     RB's registers are the same set (CUR: s5 21, n - c s11 27; RT: s0 8, s2 18, s3 19, s7..s10 23..26; b s1 9);
   - the frame size 1920 -> 1936 (b3_call_pre, b3_FR_free, b3_free_call's continuation);
   - free 0x16328 -> 0x1635c (b3_free_addr, b3_free_call); b3_syms: __stack_chk_guard 0x51140 -> 0x51170,
     .got guard 0x1fb50 -> 0x1fb80, __malloc_context 0x511d8 -> 0x51208, __malloc_lock 0x511d0 -> 0x51200, __libc
     0x51160 -> 0x51190 (the .rodata tables 0x10788 / 0x107e8 / 0x10728 / 0x10704 unchanged); b3_sink_addr:
     __libc.threaded 0x51161 -> 0x51191, ofl_lock 0x51588 -> 0x515b8, ofl_head 0x51590 -> 0x515c0.
   Statements changed only in those numerals. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

Lemma b3_munch_join : forall W W' m1 m2 m3, Frame.munch W m1 m2 -> Frame.munch W' m2 m3 ->
  (forall x, Frame.outside W x -> Frame.outside W' x) -> Frame.munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 Hs x Hx. rewrite (H2 x (Hs _ Hx)). exact (H1 x Hx). Qed.

(* A write set inside [S - K, S - 104), interval by interval. *)
Lemma b3_fp : forall g W x, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W x HF Hx. induction HF as [|[lo hi] W' [H1 H2] HF IH]; cbn [Frame.outside]; intros O.
  - exfalso; exact (O I).
  - cbn [fst snd] in *. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi).
    + lia.
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
    + apply IH. intros O'. apply O. split; [lia | exact O'].
Qed.

(* RB (round-trip registers and slots) from the old registers and the bytes in the new memory. *)
Lemma b3_RB : forall g b idb fgb regs mem regs' m',
  RB g b idb fgb regs mem ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  bytes_at rsegs m' (spk g 76) (OUR (g_in g)) -> bytes_at rsegs m' (spk g 154) idb ->
  bytes_at rsegs m' (spk g 82) fgb ->
  RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs mem regs' m' (Hb & (Hc & H21 & H27) & _ & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & _)
    E8 E9 E18 E19 E21 E23 E24 E25 E26 E27 B1 B2 B3.
  unfold RB, CUR, RT, OURb, IDB, FGB, rg in *.
  rewrite E8, E9, E18, E19, E21, E23, E24, E25, E26, E27. tauto.
Qed.

(* The three slots of RB, across a munch that misses them. *)
Lemma b3_RB_bytes : forall g b idb fgb regs mem m' W,
  RB g b idb fgb regs mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 76) 6 -> disjoint_from W (spk g 154) (Z.of_nat (length idb)) ->
  disjoint_from W (spk g 82) (Z.of_nat (length fgb)) ->
  bytes_at rsegs m' (spk g 76) (OUR (g_in g)) /\ bytes_at rsegs m' (spk g 154) idb /\
  bytes_at rsegs m' (spk g 82) fgb.
Proof.
  intros g b idb fgb regs mem m' W (_ & _ & HO & _ & _ & HI & HF) MU D1 D2 D3.
  split; [|split].
  - apply (bytes_at_transport rsegs W mem m' _ _ HO MU). rewrite OUR_length. exact D1.
  - exact (bytes_at_transport rsegs W mem m' _ _ HI MU D2).
  - exact (bytes_at_transport rsegs W mem m' _ _ HF MU D3).
Qed.

(* n_b <> 0 gives n_b >= 1 (em_wok: 2 <= uw). *)
Lemma b3_rnb_pos : forall g b, rnb g b <> 0 -> 1 <= rnb g b.
Proof.
  intros g b H. unfold rnb, rt_n in *. destruct (rt_E (g_in g) (Z.of_nat b)) eqn:E; [|lia].
  unfold rt_E, reac_ctrl_build_as_c.ba_E, RcEmit.em_wok in E.
  apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
  apply Z.leb_le in E. lia.
Qed.

Lemma b3_pairwise_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros T R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|exact (IH H2)].
    intros y Hy. apply H1. apply (Permutation_in y (Permutation_sym HP) Hy).
  - destruct H as [Hy [Hx Hl]]. split.
    + intros z [<-|Hz]; [apply Hs, Hy; left; reflexivity | exact (Hx z Hz)].
    + split; [intros z Hz; apply Hy; right; exact Hz | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.

Lemma b3_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

Lemma b3_pw_app : forall (T : Type) (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) -> pairwise R l2.
Proof. intros T R l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H | exact (IH (proj2 H))]. Qed.

Lemma b3_in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma b3_ba_mbyte : forall (m m' : word -> option byte) a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma b3_ba_hi : forall (m m' : word -> option byte) lo a bs, bytes_at rsegs m a bs -> lo <= a ->
  (forall x, lo <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo a bs HB Hlo HK. apply (b3_ba_mbyte m); [exact HB|]. intros i Hi.
  destruct HB as (H1 & H2 & _). apply HK. lia.
Qed.

Lemma b3_in_img_b : forall B a, ms_segs B = rsegs ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) && (a <? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true -> in_img B a.
Proof.
  intros B a ES H. unfold in_img. rewrite ES. split; [discriminate|].
  apply existsb_exists in H as (s & Hs & E). apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exists s. split; [exact Hs | lia].
Qed.

Lemma b3_swrap32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma b3_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

(* RB at turn b + 1 (R22's latch: s1 = b + 1). *)
Lemma b3_RB_S : forall g b idb fgb regs mem regs' m',
  RB g b idb fgb regs mem -> (S b <= 6)%nat ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = Z_to_bv 64 (Z.of_nat (S b)) -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  bytes_at rsegs m' (spk g 76) (OUR (g_in g)) -> bytes_at rsegs m' (spk g 154) idb ->
  bytes_at rsegs m' (spk g 82) fgb ->
  RB g (S b) idb fgb regs' m'.
Proof.
  intros g b idb fgb regs mem regs' m' (Hb & (Hc & H21 & H27) & _ & (H8 & H18 & H19 & H23 & H24 & H25 & H26) & H9 & _)
    HS E8 E9 E18 E19 E21 E23 E24 E25 E26 E27 B1 B2 B3.
  unfold RB, CUR, RT, OURb, IDB, FGB, rg in *.
  rewrite E8, E9, E18, E19, E21, E23, E24, E25, E26, E27. tauto.
Qed.

(* n_b <> 0 gives n_b >= 124 (52 + 36 uw with 2 <= uw), so F_b has at least 92 bytes. *)
Lemma b3_rnb_ge : forall g b, rnb g b <> 0 -> 124 <= rnb g b.
Proof.
  intros g b H. unfold rnb, rt_n in *. destruct (rt_E (g_in g) (Z.of_nat b)) eqn:E; [|lia].
  unfold rt_E, reac_ctrl_build_as_c.ba_E, RcEmit.em_wok in E.
  apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
  apply Z.leb_le in E. lia.
Qed.

Lemma b3_rF_len : forall g b, rnb g b <> 0 -> (92 <= length (rFb g b))%nat.
Proof.
  intros g b H. pose proof (b3_rnb_ge g b H) as Hge. unfold rnb in Hge.
  unfold rFb, rt_F, RcEmit.em_fr, RcEmit.em_hdr. rewrite !length_app, OUR_length, repeat_length.
  cbn [length box6 map]. lia.
Qed.

Lemma b3_bv_eqb_u : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b3_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma b3_psum_rng : forall bs i, 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
  intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
  pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma b3_nth_skipn : forall m (l : list byte) n d, nth n (skipn m l) d = nth (m + n) l d.
Proof. induction m as [|m IH]; intros [|x l] n d; cbn; try reflexivity; [destruct n; reflexivity | apply IH]. Qed.

Lemma b3_nth_firstn : forall m n (l : list byte) d, (n < m)%nat -> nth n (firstn m l) d = nth n l d.
Proof.
  induction m as [|m IH]; intros n [|x l] d Hn; [lia | lia | destruct n; reflexivity |].
  destruct n as [|n]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma b3_first1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* Byte j of the block X = bytes 18 .. 49 of a frame's first 50 bytes, read from the frame in memory. *)
Lemma b3_rd_blk : forall m phi F j, bytes_at rsegs m phi F -> (50 <= length F)%nat -> (j < 32)%nat ->
  ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j (skipn 18 (fr50 F)) (Z_to_bv 8 0)].
Proof.
  intros m phi F j HB HL Hj. rewrite <- Z.add_assoc.
  rewrite (bytes_at_read rsegs m phi F (18 + Z.of_nat j) 1 HB) by lia.
  replace (Z.to_nat (18 + Z.of_nat j)) with (18 + j)%nat by lia.
  rewrite (b3_first1 F (18 + j) (Z_to_bv 8 0)) by lia.
  rewrite b3_nth_skipn. unfold fr50. rewrite b3_nth_firstn by lia. rewrite app_nth1 by lia. reflexivity.
Qed.

(* The round-trip state does not change at b = 1, 2. *)
Lemma b3_rt_keep : forall inp b, (b = 1 \/ b = 2)%nat -> rt_st inp (S b) = rt_st inp b.
Proof.
  intros inp b Hb.
  change (rt_st inp (S b)) with
    (let s := rt_st inp b in let x := Z.of_nat b in let n := rt_n inp x in let g := rt_g inp x in
     if n =? 0 then s
     else if (x =? 3) || (x =? 4) then (rp_id (fst s) n g, snd s)
     else if (x =? 5) || (x =? 6) then (fg_id (fst s) n (snd s) g, fg_st n (snd s) g)
     else s).
  cbv zeta. destruct Hb as [-> | ->]; cbn [Z.of_nat Pos.of_succ_nat Z.eqb Pos.eqb orb];
    destruct (rt_n inp _ =? 0); reflexivity.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma b3_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
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

(* ---- free (Kind B) at 0x1635c from a cut state: call_pre, then FR after the call ---- *)

Lemma b3_alloc : frame_allocator B (APIf rc).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma b3_free_addr : ms_free B = 0x1635c.
Proof. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma b3_ax : AllocExtra B (aa_MR (APIf rc)).
Proof. destruct b3_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma b3_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & H & _). exact H.
Qed.

Lemma b3_syms : ms_ctx B = 0x51208 /\ ms_lock B = 0x51200 /\ ms_libc B = 0x51190 /\ ms_guard B = 0x51170 /\
  ms_got_guard B = 0x1fb80 /\ ms_size_classes B = 0x10788 /\ ms_small_cnt B = 0x107e8 /\ ms_med_cnt B = 0x10728 /\
  ms_debruijn B = 0x10704 /\ ms_vmlock B = None.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _ & _ & _ & H20 & _).
  repeat split; assumption.
Qed.

Lemma b3_sink_addr : forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515bc \/ 0x515c0 <= a < 0x515c8) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof b3_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  rewrite (sl_errno_val B APIf ra empty FF). unfold static_owned, vml_lo, vml_len. rewrite E10.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. unfold CTX_SIZE.
  assert (DBL : ms_debruijn_len B = 132) by (pose proof FF as FF'; unfold frame_facts in FF'; tauto).
  rewrite DBL.
  split; [|lia]. apply (b3_in_img_b B a (sl_segs B APIf ra empty FF)).
  destruct Ha as [Ha|[Ha|Ha]];
    [ assert (a = 0x51191) by lia; subst a
    | assert (a = 0x515b8 \/ a = 0x515b9 \/ a = 0x515ba \/ a = 0x515bb) as [->|[->|[->| ->]]] by lia
    | assert (a = 0x515c0 \/ a = 0x515c1 \/ a = 0x515c2 \/ a = 0x515c3 \/ a = 0x515c4 \/ a = 0x515c5 \/ a = 0x515c6 \/
        a = 0x515c7) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia ];
    vm_compute; reflexivity.
Qed.

Lemma b3_sink_keep : forall (m m' : word -> option byte) md md',
  (forall a, (0x51191 <= a < 0x51192 \/ 0x515b8 <= a < 0x515bc \/ 0x515c0 <= a < 0x515c8) ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  m_fds md' = m_fds md -> sink_none B m md -> sink_none B m' md'.
Proof.
  intros m m' md md' HM Hfd (Henv & Hhead & Hn). destruct (sl_sink B APIf ra empty FF) as (E1 & E2 & E3).
  destruct Henv as [Ht Hl]. split; [split|split].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. lia.
  - rewrite Hfd. exact Hn.
Qed.

Lemma b3_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> getr regs_c 2 = getr regs 2 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> call_pre B (aa_MR (APIf rc)) L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0).
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

Lemma b3_FR_free : forall g hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  call_post B (aa_MR (APIf rc)) L A regs_c mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
  blocks L A = b1 ++ (ptr_addr L p, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) ->
  ro_agree (ms_segs B) mem' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  res_ok_slots A' (sb_free (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2)) n) ->
  FR B APIf ra empty g (hb1 ++ hb2) L' A' regs' mem' md' /\
  Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) /\
  (forall a, g_S g - 1936 <= a < 2 ^ 64 -> mbyte rsegs mem' a = mbyte rsegs mem a).
Proof.
  intros g hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES'.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  pose proof b3_ax as AX.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof (sl_errno B APIf ra empty FF) as HEC.
  pose proof (sl_errno_val B APIf ra empty FF) as HEV. pose proof (sl_ceil (rc := rc)) as HCE.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (HSP : spZ regs_c = g_S g - 1936).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  pose proof (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ p n HMR Hpn) as [Hp1 Hp2].
  assert (HEimg : forall a, ptr_addr L p <= a < ptr_addr L p + n -> ~ in_img B a).
  { intros a Ha. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
    apply (ax_blocks_img AX L A mem md p n); [exact HMR | exact Hpn | lia]. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR (APIf rc) L0 A0 m0 md0 -> owned B L0 A0 a -> a < alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws (APIf rc)) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha H1 H2 H3. pose proof (sl_in_img_top B a ES Ha) as Hl. unfold SL_TOP in Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img AX L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img AX L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros He. exact (HEimg a He Ha). }
  assert (HH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 1936 - 8192 <= a < g_S g - 1936) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply MEM.
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
  assert (HPW : pairwise ranges_disjoint (hb1 ++ (ptr_addr L p, n) :: hb2 ++ blocks (g_L g) (g_A g))).
  { rewrite app_comm_cons, app_assoc. apply (b3_pairwise_perm _ _ b3_rd_sym (blocks L A)); [exact HP|].
    exact (mr_blocks_disjoint _ _ (aa_laws (APIf rc)) _ _ _ _ HMR). }
  apply b3_pw_app in HPW. destruct HPW as [HPW _].
  split; [|split].
  2:{ rewrite EB'. rewrite <- app_assoc. apply (Permutation_app_inv b1 b2 hb1 (hb2 ++ blocks (g_L g) (g_A g))
        (ptr_addr L p, n)). rewrite <- EB. rewrite app_comm_cons, app_assoc. exact HP. }
  2:{ intros a Ha. rewrite <- ES. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (b3_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b3_relro_img a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
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
    - intros Ea. subst a. pose proof (HPW (ptr_addr L p, k) ltac:(apply in_or_app; right; exact Hak)) as D.
      unfold ranges_disjoint in D. cbn in D. lia. }
  split; [intros a Ha; apply SCW; unfold scratch; right; exact Ha|].
  split.
  { apply (b3_sink_keep mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (b3_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2) (hb1 ++ hb2) A' (ptr_addr L p) n
                   (Permutation_sym (Permutation_middle hb1 hb2 (ptr_addr L p, n))) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma b3_free_call : forall g hb1 hb2 L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     (forall a, g_S g - 1936 <= a < 2 ^ 64 -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regs_c 1) mem' (seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (mkst regs_c (Z_to_bv 64 0x1635c) mem (seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb1 hb2 L A regs mem md regs_c p n Q HF HP Hpn Hn E2 E3 E4 Hra H10 K.
  pose proof (b3_call_pre g _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof b3_alloc as (_ & FREE & _).
  rewrite <- b3_free_addr.
  eapply SR_bind; [exact (FREE L A regs_c mem md p n (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2))
                            CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (b3_FR_free g hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES') as (HF' & HP' & HK).
  exact (K L' A' regs' mem' md' HF' HP' RP' HK).
Qed.

End S.

Ltac b3_rp RP Hx r := etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|];
  rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.
