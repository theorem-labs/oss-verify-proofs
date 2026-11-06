(* Segment R21 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13644, 0x13648], U13644 -> U1364c
   (free(Φ) at 0x17280, Kind B through free_contract (U/Contract.v:92) of FF; the live harness block goes).
   The free helpers are the plain Tac_b3 ones with frame_ubsan's values (free 0x17280, the 1936 frame, ctx
   0x52198, lock 0x52190, libc 0x52120, sink cells 0x52121, 0x52548, 0x52550). The frame_facts conjuncts are taken
   by their statement (decompose, then assumption), not by their position. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

Lemma r21_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1364c) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x17280) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13644) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. step. apply evt_done. reflexivity.
Qed.

(* A write set inside [S - K, S - 104), interval by interval. *)
Lemma r21_fp : forall g W x, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
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
Lemma r21_RB : forall g b idb fgb regs mem regs' m',
  RB g b idb fgb regs mem ->
  YK11.getr regs' 8 = YK11.getr regs 8 -> YK11.getr regs' 9 = YK11.getr regs 9 ->
  YK11.getr regs' 18 = YK11.getr regs 18 -> YK11.getr regs' 19 = YK11.getr regs 19 ->
  YK11.getr regs' 22 = YK11.getr regs 22 -> YK11.getr regs' 23 = YK11.getr regs 23 ->
  YK11.getr regs' 24 = YK11.getr regs 24 -> YK11.getr regs' 25 = YK11.getr regs 25 ->
  YK11.getr regs' 26 = YK11.getr regs 26 -> YK11.getr regs' 27 = YK11.getr regs 27 ->
  bytes_at rsegs m' (spk g 114) (OUR (g_in g)) -> bytes_at rsegs m' (spk g 24) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m' (spk g 36) idb -> bytes_at rsegs m' (spk g 120) fgb ->
  RB g b idb fgb regs' m'.
Proof.
  intros g b idb fgb regs mem regs' m'
    (Hb & (Hc & H22 & H23) & _ & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & _ & H9 & _)
    E8 E9 E18 E19 E22 E23 E24 E25 E26 E27 B1 B0 B2 B3.
  unfold RB, CUR, RT, OURb, M8, q64, RIDB, FGB, rg in *.
  rewrite E8, E9, E18, E19, E22, E23, E24, E25, E26, E27. tauto.
Qed.

(* The four slots of RB, across a munch that misses them. *)
Lemma r21_RB_bytes : forall g b idb fgb regs mem m' W,
  RB g b idb fgb regs mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 114) 6 -> disjoint_from W (spk g 24) 8 ->
  disjoint_from W (spk g 36) (Z.of_nat (length idb)) -> disjoint_from W (spk g 120) (Z.of_nat (length fgb)) ->
  bytes_at rsegs m' (spk g 114) (OUR (g_in g)) /\ bytes_at rsegs m' (spk g 24) (le8 (Z_to_bv 64 0)) /\
  bytes_at rsegs m' (spk g 36) idb /\ bytes_at rsegs m' (spk g 120) fgb.
Proof.
  intros g b idb fgb regs mem m' W (_ & _ & HO & _ & HM8 & _ & HI & HF) MU D1 D0 D2 D3.
  unfold M8, q64 in HM8.
  split; [|split; [|split]].
  - apply (bytes_at_transport rsegs W mem m' _ _ HO MU). rewrite OUR_length. exact D1.
  - apply (bytes_at_transport rsegs W mem m' _ _ HM8 MU). rewrite length_le8. exact D0.
  - exact (bytes_at_transport rsegs W mem m' _ _ HI MU D2).
  - exact (bytes_at_transport rsegs W mem m' _ _ HF MU D3).
Qed.

Lemma r21_pairwise_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
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

Lemma r21_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

Lemma r21_pw_app : forall (T : Type) (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) -> pairwise R l2.
Proof. intros T R l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H | exact (IH (proj2 H))]. Qed.

Lemma r21_in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma r21_ba_mbyte : forall (m m' : word -> option byte) a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma r21_ba_hi : forall (m m' : word -> option byte) lo a bs, bytes_at rsegs m a bs -> lo <= a ->
  (forall x, lo <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo a bs HB Hlo HK. apply (r21_ba_mbyte m); [exact HB|]. intros i Hi.
  destruct HB as (H1 & H2 & _). apply HK. lia.
Qed.

Lemma r21_in_img_b : forall B a, ms_segs B = rsegs ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) && (a <? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true -> in_img B a.
Proof.
  intros B a ES H. unfold in_img. rewrite ES. split; [discriminate|].
  apply existsb_exists in H as (s & Hs & E). apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exists s. split; [exact Hs | lia].
Qed.

Ltac r21_rp RP Hx r := etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|];
  rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma r21_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' pc' m' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) P.
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

(* ---- free (Kind B) at 0x17280 from a cut state: call_pre, then FR after the call ---- *)

Lemma r21_alloc : frame_allocator B (APIf rc).
Proof.
  pose proof FF as H. unfold frame_facts in H. decompose [and] H.
  match goal with Hx : _ |- _ => exact (Hx rc fx) end.
Qed.

Lemma r21_free_addr : ms_free B = 0x17280.
Proof. pose proof FF as H. unfold frame_facts in H. decompose [and] H. assumption. Qed.

Lemma r21_ax : AllocExtra B (aa_MR (APIf rc)).
Proof. destruct r21_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma r21_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. pose proof FF as H. unfold frame_facts in H. decompose [and] H. assumption. Qed.

Lemma r21_syms : ms_ctx B = 0x52198 /\ ms_lock B = 0x52190 /\ ms_libc B = 0x52120 /\ ms_guard B = 0x52100 /\
  ms_got_guard B = 0x20b18 /\ ms_size_classes B = 0x10750 /\ ms_small_cnt B = 0x107b0 /\ ms_med_cnt B = 0x106f0 /\
  ms_debruijn B = 0x106cc /\ ms_vmlock B = None.
Proof.
  pose proof FF as H. unfold frame_facts in H. decompose [and] H.
  repeat split; assumption.
Qed.

Lemma r21_sink_addr : forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x5254c \/ 0x52550 <= a < 0x52558) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof r21_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  rewrite (sl_errno_val B APIf ra empty FF). unfold static_owned, vml_lo, vml_len. rewrite E10.
  rewrite (sl_debruijn_len B APIf ra empty FF).
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. unfold CTX_SIZE.
  split; [|lia]. apply (r21_in_img_b B a (sl_segs B APIf ra empty FF)).
  destruct Ha as [Ha|[Ha|Ha]];
    [ assert (a = 0x52121) by lia; subst a
    | assert (a = 0x52548 \/ a = 0x52549 \/ a = 0x5254a \/ a = 0x5254b) as [->|[->|[->| ->]]] by lia
    | assert (a = 0x52550 \/ a = 0x52551 \/ a = 0x52552 \/ a = 0x52553 \/ a = 0x52554 \/ a = 0x52555 \/ a = 0x52556 \/
        a = 0x52557) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia ];
    vm_compute; reflexivity.
Qed.

Lemma r21_sink_keep : forall (m m' : word -> option byte) md md',
  (forall a, (0x52121 <= a < 0x52122 \/ 0x52548 <= a < 0x5254c \/ 0x52550 <= a < 0x52558) ->
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

Lemma r21_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> YK11.getr regs_c 2 = YK11.getr regs 2 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  YK0s.ret_ok (YK11.getr regs_c 1) -> call_pre B (aa_MR (APIf rc)) L A regs_c mem md.
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

Lemma r21_FR_free : forall g hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
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
  pose proof r21_ax as AX.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0 & HPB0).
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
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR (APIf rc) L0 A0 m0 md0 -> owned B L0 A0 a -> a < YM05.alloc_ceiling).
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
  assert (HH : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 1936 - 8192 <= a < g_S g - 1936) ->
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
  { rewrite app_comm_cons, app_assoc. apply (r21_pairwise_perm _ _ r21_rd_sym (blocks L A)); [exact HP|].
    exact (mr_blocks_disjoint _ _ (aa_laws (APIf rc)) _ _ _ _ HMR). }
  apply r21_pw_app in HPW. destruct HPW as [HPW _].
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
  { apply (r21_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (r21_relro_img a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
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
  { apply (r21_sink_keep mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (r21_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2) (hb1 ++ hb2) A' (ptr_addr L p) n
                   (Permutation_sym (Permutation_middle hb1 hb2 (ptr_addr L p, n))) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma r21_free_call : forall g hb1 hb2 L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  YK0s.ret_ok (YK11.getr regs_c 1) -> YK11.getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     (forall a, g_S g - 1936 <= a < 2 ^ 64 -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' (YK11.getr regs_c 1) mem' (YK11.seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs_c (Z_to_bv 64 0x17280) mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb1 hb2 L A regs mem md regs_c p n Q HF HP Hpn Hn E2 E3 E4 Hra H10 K.
  pose proof (r21_call_pre g _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof r21_alloc as (_ & FREE & _).
  rewrite <- r21_free_addr.
  eapply SR_bind; [exact (FREE L A regs_c mem md p n (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2))
                            CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (r21_FR_free g hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES') as (HF' & HP' & HK).
  exact (K L' A' regs' mem' md' HF' HP' RP' HK).
Qed.

Lemma seg_R21 : forall b : nat, Hat B APIf ra (Inv_U1364c_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_U13644_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRB & Hn & H20).
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hn) as (_ & Hn1 & _).
  pose proof (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & HSK & HS47 & _).
  destruct (u2_RS_len (g_in g) (S b)) as (LI & LF).
  assert (Hin : In (phi, rnb g b) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (r21_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (r21_mid g (hb1 phi (rnb g b)) L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (r21_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of. apply r21_evt.
  - intros ms ->.
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs_c m1 HQ Hx Hrel MU' HFR'.
    injection HQ as E1 E2 E3. subst R pc' m0'.
    apply (r21_free_call g [] [] L A regs_c m1 md regs_c p (rnb g b)).
    + rewrite Ep. exact HFR'.
    + rewrite Ep. exact HP.
    + exact Hp.
    + unfold rnb in *. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). apply YK0s.ret_ok_even. vm_compute. reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). rewrite Ep. exact H20.
    + intros L' A' regs' mem' md' HF' HP' RP' HK.
      replace (YK11.getr regs_c 1) with (Z_to_bv 64 0x1364c) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply H. exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact HF'|]. split; [exact HP'|].
      destruct (r21_RB_bytes g b _ _ regs mem m1 [] HRB MU' I I I I) as (B1 & B0 & B2 & B3).
      unfold spk, fsp, SLOT_FRAME in B1, B0, B2, B3.
      apply (r21_RB g b _ _ regs mem regs' mem' HRB);
        [ r21_rp RP' Hx 8 | r21_rp RP' Hx 9 | r21_rp RP' Hx 18 | r21_rp RP' Hx 19 | r21_rp RP' Hx 22
        | r21_rp RP' Hx 23 | r21_rp RP' Hx 24 | r21_rp RP' Hx 25 | r21_rp RP' Hx 26 | r21_rp RP' Hx 27 | | | | ];
        unfold spk, fsp, SLOT_FRAME; (eapply r21_ba_hi; [eassumption | | exact HK]); lia.
Qed.

End S.
