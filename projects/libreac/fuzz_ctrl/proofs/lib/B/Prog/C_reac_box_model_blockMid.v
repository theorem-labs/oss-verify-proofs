(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): MID, the step between the class-0 request (E0, mbB_E0
   in C_reac_box_model_blockPf.v) and stretch B (mb_post_rebaseRB in C_reac_box_model_blockRBLib.v).  A Theorem Labs
   lane; plan of record row MID (pb_reac_box_model_block.plan.md (a working note, not in this delivery)).

   mbB_mid concludes the premises of mb_post_rebaseRB at mb := mem2 (the memory at the return of
   __asan_stack_malloc_0), j := pos, fr := fs_frame (ly_F lyc) 0 pos, FS := ly_F lyc, RNG := RNG_W (w_H W), in its
   order, except Efr (reflexivity) and the six callee footprint contracts (asan_stack_malloc_0_contract_F ..
   name_field_contract_F), closed hypotheses of the top Section that the composer passes to mb_post_rebaseRB itself.
   The last one, mbF_rng, is a Theorem Labs lane's mbB_rngW (C_reac_box_model_blockVis.v) at the journal over S2; mbB_rngW states it
   with reac_box_model_blockF.mbF_rng, the RB copy's C_reac_box_model_blockRBF.mbF_rng has the same text.
   Sources at mem2:
     - the journal J2 at ((0, pos) :: own) (mbB_E0's continuation): AR at S2 over mem2 and the window's presence;
     - ProgWorld at mem2: ctl_rt_C_of_AR (route (C): asan_cells, the shadow of the cut's own state and of the image
       hull, ro_agree; no VIS0, no OWNED_RO; the run's region R is inside them by C_reac_box_model_blockCover.mbB_R_on;
       its arodata_okP at mem2 is the spec's
       arodata_okS at memc carried by acall_kept's image clause), ctl_fp_of_AR (fp [0%nat]), fp_tls_apart (the
       thread cells apart from the class-0 words and the window's shadow), ctl_fs_of_AR (the class-0 hint word),
       ctl_stack_shadow_of_AR (the window addressable, and o's when o is on the machine stack);
     - CtrlRo at mem2: ro_usable_glob (the row and the name, registered globals: HGM) and ro_usable (the JOIN
       blocks: HZS_J13 / HZS_J14);
     - the bytes of the row, the name and o, carried from memc: memc -> m1 by stretch A's munch of its own window
       (mb_pre_facts, mem_rel m1 mc, ro_same memc m1), m1 -> mem2 by E0's acall_kept (the image clause for the row
       and the name, the frame clause or the high-memory clause for o); o's shadow by the frame clause or by
       ctl_stack_shadow_of_AR;
     - the saved registers at sp - 88 from mb_pre_facts, by mem_rel and acall_kept's high-memory clause;
     - the footprint mbF_rng: mbB_rngW, with the row / name garr8 at mem2 (acall_kept's image clause), their shadow
       covers (CtrlRo.ro_hull, HIMGSH) and o's presence and shadow cover (am_areas / am_zshadow at S2);
     - the class-0 frame (pos bound, the back-pointer word at fr + 56) from ProgWorld's ctl_fs_of_astack at cid 0,
       whose premises are mbB_E0's continuation (through the core's YCbqMalloc.aj_stack_malloc_at_fc: ecall_pre at
       the call state, the frame condition and the two presence clauses) and, for [sp - 4272, A - 4096), the
       journal at m1 (mbB_to_E0's continuation).
   The spec's premises are taken in the form of treac_box_model_block_spec (lib/B/Prog/C_reac_box_model_block.v,
   5487787da37, image A's form of record) with its definitions unfolded (bmb_z, tbmb_o_home, CtrlCallerJ.twr_ok /
   tsrc_ok at PI_ctrl_B, whose pa_segs is rsegs), so the composer passes them by conversion.

   rule 24: no function proved (glue of the proved run reac_box_model_block_holds_F). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_model_block_c reac_box_model_block reac_box_model_blockF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YM05 YI16 YI00 YA0n
  YG00 YG01 YG0f YG0d YG0n YG0v YG0s YP09 YCbq YF0m YE01 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgWorld ProgWorldCtlRtC ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld_Fs ProgWorldTlsApart ProgWorldShadow ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlRo GlueLift
  C_reac_box_model_blockVis reac_box_model_block_c_on C_reac_box_model_blockCover.
Import ListNotations.
Open Scope Z_scope.

(* ---- Helpers (image B, any world) ---------------------------------------------------------------------------- *)

(* Outside stretch A's window the real end memory m1 is the caller's memory (as rrB_journal_free's OFF). *)
Lemma mid_off : forall (memc m1 mc : word -> option byte) (lo hi : Z),
  munch [(lo, hi)] (B.MemNorm.normalize rsegs memc) mc ->
  B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m1 x = memc x.
Proof.
  intros memc m1 mc lo hi MU [REL1 _] ROS x Hx.
  destruct (ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
  pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
  assert (Ho : outside [(lo, hi)] (bv_unsigned x)) by (cbn [outside]; split; [exact Hx | exact I]).
  pose proof (MU x Ho) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2. rewrite <- E1, E2. reflexivity.
Qed.

Lemma mid_view_off : forall (H : word -> bool) (memc m1 : word -> option byte) (lo hi : Z),
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m1 x = memc x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  lib.Reusable.YG0n.aview rsegs H m1 a = lib.Reusable.YG0n.aview rsegs H memc a.
Proof.
  intros H memc m1 lo hi OFF a Ha Hn. apply lib.Reusable.YCbq.aview_eq_of.
  unfold lib.Reusable.YK04.mrestrict. rewrite (OFF (Z_to_bv 64 a)); [reflexivity|].
  rewrite (B.ProgWorld.pws_u64 a Ha). exact Hn.
Qed.

(* ProgWorld's aview_vis_mrd, stated over rsegs (ProgWorld's segs is YB1v.tfibsegs, the same list by
   ProgBridge.tfibsegs_rsegs, but rewrite needs the syntactic form). *)
Lemma mid_vis_mrd : forall (W : lib.Reusable.YA0n.world rsegs) (mem : word -> option byte) (a : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem a =
    option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (Z_to_bv 64 a)).
Proof. intros W mem a Hh. exact (B.ProgWorld.aview_vis_mrd W mem a Hh). Qed.

(* A visible address with the same view in two memories has the same mrd byte (as ctl_post_acall_kept). *)
Lemma mid_mrd_eq : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a ->
  mrd rsegs m' (Z_to_bv 64 a) = mrd rsegs m (Z_to_bv 64 a).
Proof.
  intros W m m' a Hh E.
  rewrite (mid_vis_mrd W m' a Hh), (mid_vis_mrd W m a Hh) in E.
  destruct (mrd rsegs m' (Z_to_bv 64 a)) as [b'|], (mrd rsegs m (Z_to_bv 64 a)) as [b|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

Lemma mid_bytes_at : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z) (bs : list byte),
  bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     lib.Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false /\
     lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' (a + i) =
       lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (K (Z.of_nat i) ltac:(lia)) as [Hh E].
  unfold wa. rewrite (mid_mrd_eq W m m' (a + Z.of_nat i) Hh E). exact (H i Hi).
Qed.

(* lib/Lib/MState's Z_to_bv_bv_unsigned (Imported here) is the 64-bit one; the byte twin. *)
Lemma mid_byte_id : forall x : byte, Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* garr8 over the restricted memory moves with the view (YCbq.val_mem_kept). *)
Lemma mid_garr8 : forall (H : word -> bool) (m m' : word -> option byte) (a : Z) (l : list Z),
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict H m) a l ->
  (forall i, 0 <= i < Z.of_nat (length l) ->
     lib.Reusable.YG0n.aview rsegs H m' (a + i) = lib.Reusable.YG0n.aview rsegs H m (a + i)) ->
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict H m') a l.
Proof.
  intros H m m' a l G K j Hj. destruct (G j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (lib.Reusable.YCbq.val_mem_kept rsegs H H m m' _ 1 _); [|exact Hv].
  intros k Hk. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply K. lia.
Qed.

(* garr8 over the restricted memory, at visible addresses, is bytes_at. *)
Lemma mid_bytes_of_garr8 : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (a : Z) (bs : list byte),
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m) a
    (map (fun x : byte => bv_unsigned x) bs) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false) ->
  bytes_at rsegs m a bs.
Proof.
  intros W m a bs G Ha Hb Hv. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  assert (Hi' : (i < length (map (fun x : byte => bv_unsigned x) bs))%nat) by (rewrite length_map; exact Hi).
  pose proof (lib.Reusable.YI00.garr8_mbyte rsegs _ _ _ i G Hi') as E.
  destruct (nth_error bs i) as [x|] eqn:En; [|apply nth_error_None in En; lia].
  assert (Enth : nth i (map (fun x : byte => bv_unsigned x) bs) 0 = bv_unsigned x)
    by (apply nth_error_nth; rewrite nth_error_map, En; reflexivity).
  rewrite Enth, mid_byte_id in E.
  assert (Ev : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m (a + Z.of_nat i) = Some (bv_unsigned x))
    by (unfold lib.Reusable.YG0n.aview; rewrite E; reflexivity).
  rewrite (mid_vis_mrd W m _ (Hv (Z.of_nat i) ltac:(lia))) in Ev.
  unfold wa. destruct (mrd rsegs m (Z_to_bv 64 (a + Z.of_nat i))) as [y|]; cbn [option_map] in Ev; [|discriminate Ev].
  injection Ev as Ey. f_equal. apply bv_eq. exact Ey.
Qed.

Lemma mid_stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* Above the image the read byte is the raw byte. *)
Lemma mid_present_of_mrd : forall (m : word -> option byte) (a : Z) (b : byte), ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  mrd rsegs m (Z_to_bv 64 a) = Some b -> m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a b Ha E. unfold mrd in E. destruct (m (Z_to_bv 64 a)) as [c|]; [exact E|].
  change (Z_to_bv 64 a) with (wa a) in E.
  rewrite (B.Prog.GlueLift.rrB_seg_rom_above a Ha) in E. discriminate E.
Qed.

(* The core's shadow view of a range (range_addressable over aview) is ctrl's addressable; the shadow bytes lie above
   the image, so a hidden one would read None. *)
Lemma mid_addressable : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (p n : Z),
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF p n ->
  0 <= p -> 0 <= n -> p + n <= APPMEM_END -> (forall i, 0 <= i < n -> app_mem (p + i)) ->
  addressable m p n.
Proof.
  intros W m p n RA Hp Hn Hpn Happ. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (RA (p + i) ltac:(lia)) as (s & Hs & Hok).
  unfold lib.Reusable.YG0v.shadow_of_addr in Hs.
  assert (Esa : shadow_addr (p + i) = lib.Reusable.YG0f.SHADOW_OFF + (p + i) / 8)
    by (unfold shadow_addr, ASAN_K, lib.Reusable.YG0f.SHADOW_OFF; lia).
  rewrite Esa. set (sa := lib.Reusable.YG0f.SHADOW_OFF + (p + i) / 8) in *.
  assert (Hsa : ImgBounds.IMG_HI <= sa < 2 ^ 64).
  { unfold sa, lib.Reusable.YG0f.SHADOW_OFF, ImgBounds.IMG_HI. unfold APPMEM_END in Hpn.
    Z.div_mod_to_equations. lia. }
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 sa)) eqn:Eh.
  - exfalso.
    assert (E0 : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m sa =
                 option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (wa sa))).
    { unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, wa.
      rewrite Eh. reflexivity. }
    rewrite E0, (B.Prog.GlueLift.rrB_seg_rom_above sa Hsa) in Hs. discriminate Hs.
  - rewrite (mid_vis_mrd W m sa Eh) in Hs.
    destruct (mrd rsegs m (Z_to_bv 64 sa)) as [bb|] eqn:Em; cbn [option_map] in Hs; [|discriminate Hs].
    injection Hs as Hbs. exists bb. split; [unfold wa; exact Em|].
    pose proof (bv_unsigned_in_range 8 bb) as R.
    unfold lib.Reusable.YG0v.saddr_ok in Hok.
    assert (Es : bv_signed bb = s).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
      change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128. rewrite Hbs in *.
      Z.div_mod_to_equations. lia. }
    rewrite Es. unfold shadow_ok. lia.
Qed.

Lemma mid_img_bounds : forall a, lib.Reusable.YG0d.in_img rsegs a -> ImgBounds.IMG_LO <= a < ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hin & Hr).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs sg Hin) as Hm.
  rewrite B.ProgBridge.rsegs_spans in Hm. cbn [In] in Hm. unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI.
  destruct Hm as [E | [E | [E | [E | []]]]]; injection E as E1 E2; lia.
Qed.

Lemma mid_img_vis : forall (W : lib.Reusable.YA0n.world rsegs) a, lib.Reusable.YG0d.in_img rsegs a ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a Hi. destruct (B.ProgBridge.img_vis_W W) as (_ & _ & H). apply H.
  pose proof (mid_img_bounds a Hi). lia.
Qed.

Lemma mid_img_of_roP : forall (RLO RHI : Z), (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a) ->
  forall a, lib.Reusable.APostBase.in_roP rsegs RLO RHI a -> lib.Reusable.YG0d.in_img rsegs a.
Proof.
  intros RLO RHI RI a [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RI a Hg)].
Qed.

Lemma mid_rw_cells : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z) (cs : list cell),
  rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     lib.Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false /\
     lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' (a + i) =
       lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m (a + i) /\
     m' (Z_to_bv 64 (a + i)) <> None) ->
  rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs [[Hwf Hb] (Hw0 & Hw1 & _)] K.
  split; [split; [exact Hwf|] | split; [exact Hw0 | split; [exact Hw1|]]].
  - apply (mid_bytes_at W m m' a _ Hb). intros i Hi. rewrite (cells_bytes_length cs Hwf) in Hi.
    destruct (K i Hi) as (K1 & K2 & _). split; assumption.
  - intros i Hi. destruct (K i Hi) as (_ & _ & K3). unfold wa, wview.
    destruct (m' (Z_to_bv 64 (a + i))); [discriminate | contradiction].
Qed.

(* ---- Arithmetic of the class-0 words, the layout and the frames' shadow (small contexts for lia) -------------- *)
Lemma mid_c0 : forall F : Z,
  fs_hint F 0 = F /\ fs_flag F 0 0 = F + 4096 /\ fs_M 0 = 16384 /\
  fs_frame F 0 0 = F + 36864 /\ fs_frame F 0 16384 = F + 36864 + 1048576.
Proof.
  intros F. unfold fs_hint, fs_flag, fs_frame.
  replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. replace (fs_B 0) with 64 by reflexivity.
  replace (2 ^ 15) with 32768 by reflexivity. replace (2 ^ (15 - Z.of_nat 0)) with 32768 by reflexivity.
  replace (8 * Z.of_nat 0) with 0 by reflexivity.
  split; [lia|]. split; [lia|]. split; [reflexivity|]. split; lia.
Qed.

Lemma mid_frame_shadow_low : forall fa n a c : Z,
  4096 <= fa -> 0 <= n -> fa + n <= c -> 0x7fff7f800000 <= c <= 0x7fffff800000 ->
  lib.Reusable.YG0f.SHADOW_OFF + fa / 8 <= a < lib.Reusable.YG0f.SHADOW_OFF + fa / 8 + n / 8 -> 0 <= a < c.
Proof. intros fa n a c H1 H2 H3 H4 H5. unfold lib.Reusable.YG0f.SHADOW_OFF in H5. Z.div_mod_to_equations. lia. Qed.

Lemma mid_shadow_in_frame : forall F off n x : Z,
  F mod 4096 = 0 -> off mod 64 = 0 -> n mod 64 = 0 -> F + off <= x < F + off + n ->
  lib.Reusable.YG0f.SHADOW_OFF + (F + off) / 8 <= lib.Reusable.YG0f.SHADOW_OFF + x / 8 <
    lib.Reusable.YG0f.SHADOW_OFF + (F + off) / 8 + n / 8.
Proof. intros F off n x H1 H2 H3 H4. Z.div_mod_to_equations. lia. Qed.

(* ctl_fp_of_AR's two apartness premises for model_block's W and D (RcAsanFP.fp_dj), at the layout's values. *)
Lemma mid_wdj : forall (F T C D sp o ce : Z),
  ImgBounds.IMG_HI <= F -> F + lib.Reusable.YG0f.kFakeStackSize <= ce ->
  4096 <= T -> T + 4096 <= ce -> 4096 <= C -> C + 256 <= ce -> 4096 <= D -> D + 4096 <= ce ->
  (T + 4096 <= F \/ F + lib.Reusable.YG0f.kFakeStackSize <= T) ->
  (F + lib.Reusable.YG0f.kFakeStackSize <= C \/ C + 256 <= F) ->
  (F + lib.Reusable.YG0f.kFakeStackSize <= D \/ D + 4096 <= F) ->
  ce <= sp - 4272 -> sp < 2 ^ 64 ->
  (o <> 0 -> (F + 36864 + 1048576 <= o /\ o + 32 <= F + lib.Reusable.YG0f.kFakeStackSize) \/ ce <= o) ->
  fp_dj (reac_box_model_block_W o sp)
    (fp_tls RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 0x5fd9f8) (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 D) 0 ++
     [(F, fs_frame F 0 0)]).
Proof.
  intros F T C D sp o ce HF HFc HT0 HT1 HC0 HC1 HD0 HD1 DTF DFC DFD Hce Hsp HO.
  destruct (mid_c0 F) as (_ & _ & _ & EF0 & _).
  unfold fp_dj, reac_box_model_block_W, fp_tls, REAC_BOX_MODEL_BLOCK_K. rewrite EF0.
  rewrite (B.ProgWorld.pws_u64 T) by lia. rewrite (B.ProgWorld.pws_u64 D) by lia.
  rewrite (B.ProgWorld.pws_u64 C) by lia. rewrite (B.ProgWorld.pws_u64 0x5fd9f8) by lia.
  rewrite (B.ProgWorld.pws_u64 (RT_TP + 32)) by (unfold RT_TP; lia).
  unfold TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF,
    RT_TP, ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeStackSize in *.
  destruct (o =? 0) eqn:Eo; [apply Z.eqb_eq in Eo | apply Z.eqb_neq in Eo];
    cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold ly_dj; cbn [fst snd]; try lia.
  all: destruct (HO Eo) as [Of | Os]; lia.
Qed.

Lemma mid_ddj : forall (F p o ce : Z),
  ImgBounds.IMG_HI <= F -> F + lib.Reusable.YG0f.kFakeStackSize <= ce ->
  (F + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YG0f.kLowShadowBeg \/ lib.Reusable.YG0f.kHighMemBeg <= F) ->
  0x7fff7f800000 <= ce <= 0x7fffff800000 ->
  (p <> 0 -> 0 <= p /\ p + 296 <= ImgBounds.IMG_HI) ->
  (o <> 0 -> (F + 36864 + 1048576 <= o /\ o + 32 <= F + lib.Reusable.YG0f.kFakeStackSize) \/ ce <= o) ->
  fp_dj (reac_box_model_block_D p o) (fp_w [0%nat] F).
Proof.
  intros F p o ce HF HFc HFz Hce HP HO.
  destruct (mid_c0 F) as (EH & EFL & EM & EF0 & EFM).
  unfold fp_dj, reac_box_model_block_D, fp_w, fp_w1. cbn [flat_map app].
  rewrite EH, EFL, EF0, EM, EFM.
  unfold shadow_addr, ASAN_K, ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg in *.
  destruct (p =? 0) eqn:Ep; [apply Z.eqb_eq in Ep | apply Z.eqb_neq in Ep];
    destruct (o =? 0) eqn:Eo; [apply Z.eqb_eq in Eo | apply Z.eqb_neq in Eo | apply Z.eqb_eq in Eo |
                               apply Z.eqb_neq in Eo];
    cbn [app]; repeat (apply Forall_cons || apply Forall_nil); unfold ly_dj; cbn [fst snd].
  all: try (destruct (HP Ep) as [Pl Ph]).
  all: try (destruct (HO Eo) as [Of | Os]).
  all: Z.div_mod_to_equations; lia.
Qed.

Lemma mid_ndj : forall (F a n : Z), ImgBounds.IMG_HI <= F -> 0 <= a -> a + n <= ImgBounds.IMG_HI ->
  fp_dj [(a, a + n)] (fp_w [0%nat] F).
Proof.
  intros F a n HF Ha Hn. destruct (mid_c0 F) as (EH & EFL & EM & EF0 & EFM).
  unfold fp_dj, fp_w, fp_w1. cbn [flat_map app]. rewrite EH, EFL, EF0, EM, EFM.
  unfold shadow_addr, ASAN_K, ImgBounds.IMG_HI in *.
  repeat (apply Forall_cons || apply Forall_nil); unfold ly_dj; cbn [fst snd].
  all: Z.div_mod_to_equations; lia.
Qed.

(* ---- MID ------------------------------------------------------------------------------------------------------ *)
Section Mid.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* the spec's Section variables: its read-only window and its registered globals *)
Variables RLO RHI : Z.
Variable GLOBS : list (Z * Z).
(* core (the TfibLib record, pending the record core, YCeg.v:25) *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis TSY : lib.Reusable.YF0m.CtrlTSyms B.
(* the spec's Section hypothesis (cgif lib/YC20.v:56) *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a.
(* B ProgWorld statements, PROVED on image B and cited (L3 rule, two Theorem Labs lanes 13:12Z; a Theorem Labs lane's db8a86df2da) *)
Let ctl_fp_of_AR : B.ProgWorld.ctl_fp_of_AR_stmt B := lib.B.ProgWorld_Fs.ctl_fp_of_AR B.
Let fp_tls_apart : B.ProgWorld.fp_tls_apart_stmt B := lib.B.ProgWorldTlsApart.fp_tls_apart B.
Let ctl_fs_of_AR : B.ProgWorld.ctl_fs_of_AR_stmt B := lib.B.ProgWorld_Fs.ctl_fs_of_AR B.
Let ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B :=
  lib.B.ProgWorldShadow.ctl_stack_shadow_of_AR B.
Let ctl_fs_of_astack : B.ProgWorld.ctl_fs_of_astack_stmt B 0 := lib.B.ProgWorldAstack.ctl_fs_of_astack B 0.
(* the image's registered globals and the JOIN blocks' shadow (CtrlRo; the image-A twin's HGM / HZS_J13 / HZS_J14) *)
Hypothesis HGM : B.Prog.CtrlRo.globs_marked rsegs B GLOBS.
Hypothesis HZS_J13 : B.Prog.CtrlRo.in_zs B JOIN_0013 32.
Hypothesis HZS_J14 : B.Prog.CtrlRo.in_zs B JOIN_0014 32.
(* the shadow of the image's read range is mapped (CtrlRo; the image-A twin's HIMGSH), for mbB_rngW's row / name
   shadow covers at mem2 *)
Hypothesis HIMGSH : B.Prog.CtrlRo.img_shadow_vis rsegs B.

Lemma mbB_mid :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
         memc mdc k (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (p b o A : Z) (row nb : list byte)
         (m1 mc : word -> option byte) mdc1 S2 (regsT regs2 : bvmap 5 word) (mem2 : word -> option byte) md2
         (pos : Z),
    (* ---- the spec's premises at memc (image A's form of record) ---- *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) ->
    tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
    0 <= p < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
    bv_unsigned sp mod 16 = 0 -> sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 ->
    A = (bv_unsigned sp - 160) / 32 * 32 ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
       lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) p
         (map (fun x : byte => bv_unsigned x) row) /\
       (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
       B.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= B.Prog.CtrlRo.IMG_HI /\
       (forall x, p <= x < p + 296 -> lib.Reusable.APostBase.in_roP rsegs RLO RHI x /\
          ~ Exists (lib.Reusable.YG0n.in_zr x) (lib.Reusable.YG0f.as_owned_static B) /\
          ~ (lib.Reusable.YG0f.as_errno B <= x < lib.Reusable.YG0f.as_errno B + 4)) /\
       (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       name_ok nb /\
       lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) (rname row)
         (map (fun x : byte => bv_unsigned x) nb) /\
       (exists q sz, In (q, sz) GLOBS /\ q <= rname row /\ rname row + Z.of_nat (length nb) <= q + sz) /\
       B.Prog.CtrlRo.IMG_LO + 64 <= rname row /\
       rname row + Z.of_nat (length nb) + 64 <= B.Prog.CtrlRo.IMG_HI /\
       (forall x, rname row <= x < rname row + Z.of_nat (length nb) ->
          lib.Reusable.APostBase.in_roP rsegs RLO RHI x /\
          ~ Exists (lib.Reusable.YG0n.in_zr x) (lib.Reusable.YG0f.as_owned_static B) /\
          ~ (lib.Reusable.YG0f.as_errno B <= x < lib.Reusable.YG0f.as_errno B + 4)) /\
       (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 ->
       ((exists cid pc, In (cid, pc) (lib.Reusable.YG01.frames Sc) /\ cid <> 0 /\
           forall x, o <= x < o + 32 -> lib.Reusable.YG0n.in_zr x (lib.Reusable.YCbq.frame_rng lyc (cid, pc))) \/
        (lib.Reusable.YG0f.ly_stk_lo lyc <= o /\ o + 32 <= lib.Reusable.YG0f.ly_stk_hi lyc)) /\
       (forall x, o <= x < o + 32 -> ~ lib.Reusable.YG0d.in_img rsegs x) /\
       (forall a, o <= a < o + 32 ->
          lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0) (lib.Reusable.YG0d.ablocks B lyc Sc)
            lyc own a /\
          lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memc a /\ ~ lib.Reusable.YG0n.aowned B lyc Sc a /\
          ~ (bv_unsigned sp - lib.Reusable.YG0d.ESTACK <= a < bv_unsigned sp)) /\
       ((forall a, o <= a < o + 32 ->
           lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a <> None /\
           ~ (bv_unsigned sp - lib.Reusable.YG0d.ESTACK <= a < bv_unsigned sp)) /\
        lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
          lib.Reusable.YG0f.SHADOW_OFF o 32 /\
        lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) o 32 /\
        lib.Reusable.YG0d.amem_range o 32 /\ 0 <= o /\ o + 32 <= 2 ^ 63) /\
       (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272)) ->
    (* ---- stretch A (mbB_to_E0's continuation) ---- *)
    mb_pre_facts ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (B.MemNorm.normalize rsegs memc) mc ->
    B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
    (* ---- E0 (mbB_E0's continuation, 8d5b2e35119) ---- *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
    lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr lyc 0 pos) ->
    lib.Reusable.YG01.frames S2 = (0, pos) :: lib.Reusable.YG01.frames Sc ->
    ~ In (0, pos) (lib.Reusable.YG01.frames Sc) ->
    lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
      lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 0 pos) (lib.Reusable.YG00.fs_frame_bytes 0) ->
    lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
      (lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0 - 8) =
      Some (lib.Reusable.YG0f.flag_addr lyc 0 pos) ->
    lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
      (sp0 + (A - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (A - sp0)) (fun _ => False) ->
    lib.Reusable.YG0d.ecall_pre rsegs B lyc Sc W regsT m1 mdc1 ->
    lib.Reusable.YG0d.spZ regsT = A ->
    (forall a, lib.Reusable.YG0f.frame_addr lyc 0 pos <= a <
               lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0 ->
               lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B lyc Sc a -> ~ lib.Reusable.YG0n.aowned B lyc S2 a ->
               ~ (A - lib.Reusable.YG0d.ESTACK <= a < A) ->
               lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a =
               lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a) ->
    (forall a, A - lib.Reusable.YG0d.ESTACK <= a < A -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
    (* ---- the premises of mb_post_rebaseRB at mb := mem2, j := pos, fr := fs_frame (ly_F lyc) 0 pos, FS := ly_F lyc
       (in its order; Efr is reflexivity, mbF_rng and the six contracts are not here) ---- *)
    exists ob : list byte,
    B.MemNorm.ro_agree rsegs mem2 /\
    A = (bv_unsigned sp - 160) / 32 * 32 /\
    bv_unsigned sp mod 16 = 0 /\
    stk rsegs mem2 (bv_unsigned sp - 4272) (bv_unsigned sp) /\
    asan_cells mem2 /\
    B.ShadowRwOn.shadow_rw_on
      (B.Prog.reac_box_model_block_c_on.reac_box_model_block_shadow_R (bv_unsigned sp) (lib.Reusable.YG0f.ly_F lyc)
         p b o row nb) mem2 /\
    HIGHMEM_BEG <= bv_unsigned sp - 4272 /\
    bv_unsigned sp <= APPMEM_END /\
    addressable mem2 (bv_unsigned sp - 4272) 4272 /\
    fp [0%nat] mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc) (bv_unsigned sp - 4272) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc)
      (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) /\
    0 <= p < 2^64 /\
    0 <= b < 2^64 /\
    0 <= o < 2^64 /\
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs mem2 p row /\
       (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) /\
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       name_ok nb /\ bytes_at rsegs mem2 (rname row) nb /\
       (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
       (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) /\
    (o <> 0 -> rw_cells rsegs mem2 o [CB 32 ob] /\
       (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) /\
    (o <> 0 -> forall i, 0 <= i < 32 -> ro_addr rsegs (wa (o + i)) = false) /\
    (p <> 0 -> addressable mem2 p 296) /\
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       addressable mem2 (rname row) (Z.of_nat (length nb))) /\
    (o <> 0 -> addressable mem2 o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) /\
    (b = 1 -> addressable mem2 JOIN_0014 32) /\
    (b = 2 -> addressable mem2 JOIN_0013 32) /\
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] (lib.Reusable.YG0f.ly_F lyc))) /\
    0 <= pos < fs_M 0 /\
    bytes_at rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 pos + 64 - 8)
      (le8 (Z_to_bv 64 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 0 pos))) /\
    (exists hh : word, bytes_at rsegs mem2 (fs_hint (lib.Reusable.YG0f.ly_F lyc) 0) (le8 hh)) /\
    rw_cells rsegs mem2 (bv_unsigned sp + -88)
      [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (* o lies at or above the image end (a fake frame of class >= 1 or the real stack, OPOS below): for the
       journal step after stretch B, whose write set must lie above IMG_HI *)
    (o <> 0 -> ImgBounds.IMG_HI <= o) /\
    B.Prog.reac_box_model_blockF.mbF_rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (B.MemNorm.normalize rsegs mem2)
      sp tp p b o (lib.Reusable.YG0f.ly_F lyc) row nb.
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 p b o A row nb
    m1 mc mdc1 S2 regsT regs2 mem2 md2 pos
    HJ0 HRO Etp Rp Rb Ro HS16 Hlo Hhi HA HROW HNAME HOB PF HREL HROS HJ1 HJ2 H10 HFR HNI HZ HFL HKEPT
    HPRE HspT HPRES HFC HWIN.
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* the caller's journal: AR, the layout, the stack bounds *)
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstat0 & _ & _).
  pose proof Hstat0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  pose proof HAR0 as (M0 & L0 & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M0) as LO.
  (* the journal after E0 *)
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
  assert (HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : bv_unsigned sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (HAb : bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160) by (rewrite HA; Z.div_mod_to_equations; lia).
  (* the class-0 frame: ctl_fs_of_astack at cid 0, lo := sp - 4272 (its presence at m1 from the journal at m1) *)
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _ & _ & _).
  pose proof (ctl_fs_of_astack B.ProgWorld.ctl_fs_geom LAWS ltac:(lia) lyc Sc S2 W regsT regs2 m1 mem2 mdc1 md2 pos
                (bv_unsigned sp - 4272) 64 HPRE ltac:(lia)
                ltac:(rewrite HspT; unfold lib.Reusable.YG0d.ESTACK; lia)
                ltac:(intros a Ha; apply Hpres1; rewrite HspT in Ha; unfold lib.Reusable.YG0d.ESTACK in Ha; lia)
                HFR HNI HAR2 H10 HZ HFL
                ltac:(rewrite HspT; exact HWIN)
                ltac:(rewrite HspT; exact HFC)
                ltac:(change (lib.Reusable.YG00.fs_frame_bytes 0) with 64; lia)) as HFS.
  cbv zeta in HFS. destruct HFS as (Hj & _ & _ & H56 & _).
  change (Z.to_nat 0) with 0%nat in Hj, H56. replace (fs_B 0%nat) with 64 in H56 by reflexivity.
  assert (Etp' : bv_unsigned tp = RT_TP).
  { rewrite Etp. unfold lib.Reusable.YG0d.w64. rewrite (B.ProgWorld.as_tp_RT_TP B TSY).
    apply B.ProgWorld.pws_u64. unfold RT_TP. lia. }
  (* stretch A: m1 is memc outside the window *)
  destruct PF as (MU & _ & _ & _ & FRc & _ & _).
  pose proof (mid_off memc m1 mc _ _ MU HREL HROS) as OFF.
  pose proof (mid_view_off (lib.Reusable.YA0n.w_H W) memc m1 _ _ OFF) as VOFF.
  (* E0's acall_kept, at [A - 4096, A) *)
  replace (sp0 + (A - sp0) - lib.Reusable.YG0d.ESTACK) with (A - 4096) in HKEPT by (unfold lib.Reusable.YG0d.ESTACK; lia).
  replace (sp0 + (A - sp0)) with A in HKEPT by lia.
  destruct HKEPT as (K1 & _ & K3 & K4 & K5 & _).
  (* the layout: the allocator's extents lie below the ceiling, the side stack above the image *)
  assert (EXT : forall e, In e (lib.Reusable.YG0f.owned_extents lyc) ->
            4096 <= fst e /\ fst e + snd e <= lib.Reusable.YM05.alloc_ceiling /\
            (fst e + snd e <= lib.Reusable.YG0f.kLowShadowBeg \/ lib.Reusable.YG0f.kHighMemBeg <= fst e)).
  { intros e He. pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO) e He) as [E0 E1].
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in *. lia. }
  destruct (EXT (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize)
              ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn; tauto)) as (F0 & F1 & F2).
  destruct (EXT (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)
              ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn; tauto)) as (T0 & T1 & _).
  destruct (EXT (lib.Reusable.YG0f.ly_C lyc, 256) ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn; tauto))
    as (CC0 & CC1 & _).
  destruct (EXT (lib.Reusable.YG0f.ly_D lyc, 4096) ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn; tauto))
    as (D0 & D1 & _).
  cbn [fst snd] in F0, F1, F2, T0, T1, CC0, CC1, D0, D1.
  pose proof (lib.Reusable.YG0f.lo_disj _ LO) as LD.
  assert (DTF : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)
                  (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize))
    by exact (lib.Reusable.YCbq.pairwise_In2 lib.Reusable.YG0f.zdisjoint _ _ _
                [(lib.Reusable.YG0f.ly_prim lyc, lib.Reusable.YG0f.kPrimResvSize);
                 (lib.Reusable.YG0f.ly_Q lyc, lib.Reusable.YG0f.kPtrArrayResv)] []
                [(lib.Reusable.YG0f.ly_NB lyc, lib.Reusable.YG0f.kNodesBlockSize);
                 (lib.Reusable.YG0f.ly_SB lyc, lib.Reusable.YG0f.kStoreBlockSize); (lib.Reusable.YG0f.ly_C lyc, 256);
                 (lib.Reusable.YG0f.ly_D lyc, 4096);
                 (lib.Reusable.YG0f.ly_stk_lo lyc, lib.Reusable.YG0f.ly_stk_hi lyc - lib.Reusable.YG0f.ly_stk_lo lyc);
                 lib.Reusable.YG0f.ly_img lyc] LD eq_refl).
  assert (DFC : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize)
                  (lib.Reusable.YG0f.ly_C lyc, 256))
    by exact (lib.Reusable.YCbq.pairwise_In2 lib.Reusable.YG0f.zdisjoint _ _ _
                [(lib.Reusable.YG0f.ly_prim lyc, lib.Reusable.YG0f.kPrimResvSize);
                 (lib.Reusable.YG0f.ly_Q lyc, lib.Reusable.YG0f.kPtrArrayResv);
                 (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)]
                [(lib.Reusable.YG0f.ly_NB lyc, lib.Reusable.YG0f.kNodesBlockSize);
                 (lib.Reusable.YG0f.ly_SB lyc, lib.Reusable.YG0f.kStoreBlockSize)]
                [(lib.Reusable.YG0f.ly_D lyc, 4096);
                 (lib.Reusable.YG0f.ly_stk_lo lyc, lib.Reusable.YG0f.ly_stk_hi lyc - lib.Reusable.YG0f.ly_stk_lo lyc);
                 lib.Reusable.YG0f.ly_img lyc] LD eq_refl).
  assert (DFD : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize)
                  (lib.Reusable.YG0f.ly_D lyc, 4096))
    by exact (lib.Reusable.YCbq.pairwise_In2 lib.Reusable.YG0f.zdisjoint _ _ _
                [(lib.Reusable.YG0f.ly_prim lyc, lib.Reusable.YG0f.kPrimResvSize);
                 (lib.Reusable.YG0f.ly_Q lyc, lib.Reusable.YG0f.kPtrArrayResv);
                 (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)]
                [(lib.Reusable.YG0f.ly_NB lyc, lib.Reusable.YG0f.kNodesBlockSize);
                 (lib.Reusable.YG0f.ly_SB lyc, lib.Reusable.YG0f.kStoreBlockSize); (lib.Reusable.YG0f.ly_C lyc, 256)]
                [(lib.Reusable.YG0f.ly_stk_lo lyc, lib.Reusable.YG0f.ly_stk_hi lyc - lib.Reusable.YG0f.ly_stk_lo lyc);
                 lib.Reusable.YG0f.ly_img lyc] LD eq_refl).
  assert (DFI : lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize)
                  (lib.Reusable.YG0f.ly_img lyc))
    by exact (lib.Reusable.YCbq.pairwise_In2 lib.Reusable.YG0f.zdisjoint _ _ _
                [(lib.Reusable.YG0f.ly_prim lyc, lib.Reusable.YG0f.kPrimResvSize);
                 (lib.Reusable.YG0f.ly_Q lyc, lib.Reusable.YG0f.kPtrArrayResv);
                 (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)]
                [(lib.Reusable.YG0f.ly_NB lyc, lib.Reusable.YG0f.kNodesBlockSize);
                 (lib.Reusable.YG0f.ly_SB lyc, lib.Reusable.YG0f.kStoreBlockSize); (lib.Reusable.YG0f.ly_C lyc, 256);
                 (lib.Reusable.YG0f.ly_D lyc, 4096);
                 (lib.Reusable.YG0f.ly_stk_lo lyc, lib.Reusable.YG0f.ly_stk_hi lyc - lib.Reusable.YG0f.ly_stk_lo lyc)]
                [] LD eq_refl).
  unfold lib.Reusable.YG0f.zdisjoint in DTF, DFC, DFD, DFI. cbn [fst snd] in DTF, DFC, DFD, DFI.
  (* the image lies inside ly_img (ALedger's al_img on the last segment), so the side stack is above it *)
  assert (HIMG : lib.Reusable.YG0f.kImgLo <= ImgBounds.IMG_HI <=
                 fst (lib.Reusable.YG0f.ly_img lyc) + snd (lib.Reusable.YG0f.ly_img lyc)).
  { assert (Hm : In (0xa2000, 0x55c000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
      by (rewrite B.ProgBridge.rsegs_spans; cbn [In]; tauto).
    apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as Eb Esz.
    pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L0 sg Hsg) as AI.
    unfold lib.Reusable.YG0f.kImgLo, ImgBounds.IMG_HI. lia. }
  destruct (lib.Reusable.YG0f.lo_img _ LO) as (Eimg & _ & Eimg2 & _).
  assert (HFimg : ImgBounds.IMG_HI <= lib.Reusable.YG0f.ly_F lyc)
    by (unfold lib.Reusable.YG0f.kImgLo, lib.Reusable.YG0f.kFakeStackSize, ImgBounds.IMG_HI in *; lia).
  assert (Hsklo : lib.Reusable.YM05.alloc_ceiling <= lib.Reusable.YG0f.ly_stk_lo lyc) by lia.
  (* where o lies *)
  assert (OPOS : o <> 0 ->
            (lib.Reusable.YG0f.ly_F lyc + 36864 + 1048576 <= o /\
             o + 32 <= lib.Reusable.YG0f.ly_F lyc + lib.Reusable.YG0f.kFakeStackSize) \/
            (lib.Reusable.YM05.alloc_ceiling <= o /\ o + 32 <= lib.Reusable.YG0f.ly_stk_hi lyc)).
  { intros Ho0. destruct (HOB Ho0) as ([(cid & pc & Hin & Hcid & Hx) | Hst] & _).
    - left. destruct (lib.Reusable.YG0s.frame_facts B lyc Sc _ cid pc M0 Hin)
        as (Hc10 & _ & _ & _ & _ & Hfo1 & Hfo2 & _).
      pose proof (Hx o ltac:(lia)) as X0. pose proof (Hx (o + 31) ltac:(lia)) as X1.
      unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0f.frame_addr in X0, X1.
      cbn [fst snd] in X0, X1. unfold lib.Reusable.YG0f.kFakeFramesOff in Hfo1.
      replace (2 ^ 20) with 1048576 in Hfo1 by reflexivity.
      pose proof (Z.mul_le_mono_nonneg_r 1 cid 1048576 ltac:(lia) ltac:(lia)). lia.
    - right. lia. }
  assert (OPOS' : o <> 0 ->
            (lib.Reusable.YG0f.ly_F lyc + 36864 + 1048576 <= o /\
             o + 32 <= lib.Reusable.YG0f.ly_F lyc + lib.Reusable.YG0f.kFakeStackSize) \/
            lib.Reusable.YM05.alloc_ceiling <= o)
    by (intros Ho0; destruct (OPOS Ho0) as [X | [X _]]; [left; exact X | right; exact X]).
  (* ctl_fp_of_AR's two apartness premises; the layout's disjunctions DTF / DFC / DFD / DFI / F2 are used only here
     and in HFimg, so they are cleared after (each disjunction doubles every later lia call) *)
  assert (WDJ : fp_dj (reac_box_model_block_W o (bv_unsigned sp))
                  (fp_tls RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd lyc))
                     (Z_to_bv 64 (lib.Reusable.YG0f.ly_C lyc)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_T lyc))
                     (Z_to_bv 64 (lib.Reusable.YG0f.ly_D lyc)) 0 ++
                   [(lib.Reusable.YG0f.ly_F lyc, fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 0)])).
  { assert (Etsd : lib.Reusable.YG0f.ly_tsd lyc = 0x5fd9f8).
    { rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ M0), (lib.Reusable.YF0m.ts_tsd B TSY). reflexivity. }
    rewrite Etsd.
    apply (mid_wdj (lib.Reusable.YG0f.ly_F lyc) (lib.Reusable.YG0f.ly_T lyc) (lib.Reusable.YG0f.ly_C lyc)
             (lib.Reusable.YG0f.ly_D lyc) (bv_unsigned sp) o lib.Reusable.YM05.alloc_ceiling HFimg F1 T0
             ltac:(unfold lib.Reusable.YG0f.kThreadObjSize in T1; lia) CC0 CC1 D0 D1
             ltac:(unfold lib.Reusable.YG0f.kThreadObjSize in DTF; lia) DFC DFD ltac:(lia) ltac:(lia) OPOS'). }
  assert (DDJ : fp_dj (reac_box_model_block_D p o) (fp_w [0%nat] (lib.Reusable.YG0f.ly_F lyc))).
  { refine (mid_ddj (lib.Reusable.YG0f.ly_F lyc) p o lib.Reusable.YM05.alloc_ceiling HFimg F1 F2 C1 _ OPOS').
    intros Ep. destruct (HROW Ep) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI, ImgBounds.IMG_HI in *. lia. }
  clear DTF DFC DFD DFI F2 LD.
  (* the image clause of acall_kept, moved back to memc through stretch A *)
  assert (KIMG : forall a, lib.Reusable.YG0d.in_img rsegs a ->
            ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) ->
            ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4) ->
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a = lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
  { intros a Hi Hs He. rewrite (K3 a Hi Hs He). pose proof (mid_img_bounds a Hi) as Hb.
    unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in Hb. apply VOFF; lia. }
  (* (a) the runtime facts at mem2 (ctlrt_of_AR); its read-only view by KIMG and the spec's arodata_okS *)
  assert (HROP : lib.Reusable.APostBase.arodata_okP rsegs RLO RHI B (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)).
  { intros a Hro Hs He. rewrite (KIMG a (mid_img_of_roP RLO RHI RELRO_IMG a Hro) Hs He). exact (HRO a Hro Hs He). }
  destruct (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TSY LAWS RLO RHI lyc S2 W mem2 md2 HAR2 HROP)
    as (AC2 & CUT2 & IMG2 & RO2).
  (* the class-0 hint word (ctl_fs_of_AR at mem2) *)
  destruct (ctl_fs_of_AR B.ProgWorld.ctl_fs_geom LAWS lyc S2 W mem2 md2 HAR2 ltac:(unfold ASAN_GT, ImgBounds.IMG_HI in *; lia))
    as (_ & _ & HHint).
  (* the window at mem2 *)
  assert (STW : stk rsegs mem2 (bv_unsigned sp - 4272) (bv_unsigned sp))
    by (apply (mid_stk_of_present (lib.Reusable.YA0n.w_H W)); [lia | lia | intros a Ha; apply Hpres2; lia]).
  assert (AWW : addressable mem2 (bv_unsigned sp - 4272) 4272)
    by exact (ctl_stack_shadow_of_AR LAWS lyc S2 W mem2 md2 (bv_unsigned sp - 4272) 4272 HAR2
                ltac:(lia) ltac:(lia) ltac:(lia)).
  (* route (C): the run's region R at mem2, inside the cut's shadow (F / Z / frames area) and the image hull's *)
  assert (SR2 : B.ShadowRwOn.shadow_rw_on
                  (B.Prog.reac_box_model_block_c_on.reac_box_model_block_shadow_R (bv_unsigned sp)
                     (lib.Reusable.YG0f.ly_F lyc) p b o row nb) mem2).
  { pose proof HAR2 as (M2 & _).
    apply (B.Prog.C_reac_box_model_blockCover.mbB_R_on B lyc S2 sp p b o row nb mem2 LO
             (lib.Reusable.YG0n.am_wf _ _ _ _ M2) ltac:(lia) ltac:(lia)); [| | | exact CUT2 | exact IMG2].
    - intros Hp0. destruct (HROW Hp0) as (_ & _ & _ & _ & P5 & P6 & _). exact (conj P5 P6).
    - intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (_ & _ & _ & Bn0 & Bn1 & _). exact (conj Bn0 Bn1).
    - intros Ho0. destruct (HOB Ho0) as ([(cid & pc & Hin & Hcid & Hx) | Hst] & _).
      + left. exists cid, pc. split; [rewrite HFR; right; exact Hin | split; [exact Hcid | exact Hx]].
      + right. exact Hst. }
  (* the frame clause of acall_kept for o's frame, moved back to memc *)
  assert (KFR : forall cid pc a, In (cid, pc) (lib.Reusable.YG01.frames Sc) ->
            (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pc)) \/
             lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pc),
                                        lib.Reusable.YG00.fs_frame_bytes cid / 8)) ->
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a = lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
  { intros cid pc a Hin Hr. rewrite (K4 cid pc a Hin Hr (fun F => F)).
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS _ _ _ _ _ cid pc HAR0 Hin) as (G1 & G2 & G3).
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg cid) as Gn.
    assert (Ha : 0 <= a < lib.Reusable.YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr; cbn [fst snd] in Hr;
        [lia|]. unfold lib.Reusable.YG0f.shadow_addr in Hr. exact (mid_frame_shadow_low _ _ _ _ G1 Gn G2 C1 Hr). }
    apply VOFF; lia. }
  (* o at mem2: its bytes are present (frame clause, or the high-memory presence clause) *)
  assert (OPR : o <> 0 -> forall i, 0 <= i < 32 -> mem2 (Z_to_bv 64 (o + i)) <> None).
  { intros Ho0 i Hi. destruct (HOB Ho0) as (Hhome & _ & Hwr & (Hsrc & _) & Hap).
    destruct (Hwr (o + i) ltac:(lia)) as (_ & Hpc & _ & _).
    destruct (OPOS Ho0) as [Of | Os]; destruct Hhome as [(cid & pc & Hin & Hcid & Hx) | Hst].
    - pose proof (KFR cid pc (o + i) Hin (or_introl (Hx (o + i) ltac:(lia)))) as E.
      destruct Hpc as [Hh (bc & Hbc)].
      rewrite (mid_vis_mrd W mem2 _ Hh), (mid_vis_mrd W memc _ Hh) in E.
      unfold mrd at 2 in E. rewrite Hbc in E.
      destruct (mrd rsegs mem2 (Z_to_bv 64 (o + i))) as [b2|] eqn:E2; cbn [option_map] in E; [|discriminate E].
      rewrite (mid_present_of_mrd mem2 (o + i) b2 ltac:(lia) E2). discriminate.
    - exfalso. lia.
    - exfalso. destruct (lib.Reusable.YG0s.frame_facts B lyc Sc _ cid pc M0 Hin) as (_ & _ & _ & _ & _ & Hfo1 & Hfo2 & _).
      pose proof (Hx o ltac:(lia)) as X0.
      unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0f.frame_addr in X0.
      cbn [fst snd] in X0. lia.
    - assert (Hp1 : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m1 (o + i)).
      { destruct Hpc as [Hh (bc & Hbc)]. split; [exact Hh|]. exists bc.
        rewrite (OFF (Z_to_bv 64 (o + i))); [exact Hbc|]. rewrite B.ProgWorld.pws_u64 by lia. lia. }
      destruct (K5 (o + i) ltac:(lia) ltac:(lia) Hp1) as [_ (b2 & Hb2)]. rewrite Hb2. discriminate. }
  (* o's shadow hull at mem2 (mbB_rngW's premise): the side stack's frame shadow (am_areas) or the stack's zero
     shadow (am_zshadow), both AR at S2 *)
  assert (OHULL : o <> 0 ->
            lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2) o 32).
  { intros Ho0. pose proof HAR2 as (M2 & _).
    pose proof (lib.Reusable.YG0f.lo_F_al _ LO) as HFal. unfold lib.Reusable.YG0f.page_aligned in HFal.
    pose proof (lib.Reusable.YG0f.lo_top _ LO) as (_ & _ & _ & _ & HALo & HAHi & _).
    unfold lib.Reusable.YG0f.page_aligned in HALo, HAHi.
    unfold lib.Reusable.YG0d.shadow_hull_vis, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    rewrite !(Z.add_comm 0x7fff8000).
    destruct (HOB Ho0) as ([(cid & pc & Hin & Hcid & Hx) | Hst] & _).
    - assert (Of : lib.Reusable.YG0f.ly_F lyc + 36864 + 1048576 <= o /\ o + 32 <= lib.Reusable.YG0f.ly_F lyc + 0xb09000).
      { destruct (OPOS Ho0) as [Of | Os]; [unfold lib.Reusable.YG0f.kFakeStackSize in Of; exact Of|].
        exfalso. destruct (lib.Reusable.YG0s.frame_facts B lyc Sc _ cid pc M0 Hin) as (_ & _ & _ & _ & _ & _ & Hfo2 & _).
        pose proof (Hx o ltac:(lia)) as X0.
        unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0f.frame_addr in X0.
        cbn [fst snd] in X0. lia. }
      pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ M2) as AA. rewrite Forall_forall in AA.
      pose proof (AA (lib.Reusable.YG0f.ASh (lib.Reusable.YG0f.AF lib.Reusable.YG0f.kFakeFramesOff),
                      (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8)
                    ltac:(unfold lib.Reusable.YG0n.aareas; do 3 (apply in_or_app; right); do 5 right; left;
                          reflexivity)) as ASH.
      unfold lib.Reusable.YG0f.range_vis in ASH. cbn [fst snd lib.Reusable.YG0f.aeval] in ASH.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
        lib.Reusable.YG0f.kFakeStackSize in ASH.
      replace (4096 + 32768) with 36864 in ASH by reflexivity.
      replace ((0xb09000 - 36864) / 8) with 1441792 in ASH by reflexivity.
      destruct (B.Prog.C_reac_box_model_blockVis.mbV_al (lib.Reusable.YG0f.ly_F lyc + 36864)
                  (lib.Reusable.YG0f.ly_F lyc + 0xb09000) o 32
                  (B.Prog.C_reac_box_model_blockVis.mbV_mod4096 _ 9 _ HFal eq_refl)
                  (B.Prog.C_reac_box_model_blockVis.mbV_mod4096 _ 2825 _ HFal eq_refl)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & P3).
      intros s Hs. destruct (P3 s Hs) as (I1 & I2 & _).
      replace (lib.Reusable.YG0f.ly_F lyc + 0xb09000 - (lib.Reusable.YG0f.ly_F lyc + 36864)) with 11534336 in I2
        by lia.
      change (11534336 / 8) with 1441792 in I2.
      replace s with (0x7fff8000 + (lib.Reusable.YG0f.ly_F lyc + 36864) / 8 +
                      (s - (0x7fff8000 + (lib.Reusable.YG0f.ly_F lyc + 36864) / 8))) by lia.
      apply ASH. lia.
    - pose proof (lib.Reusable.YG0n.am_zshadow _ _ _ _ M2) as ZS.
      unfold lib.Reusable.YG0n.zshadow_ok, lib.Reusable.YG0n.zero_shadow_ranges in ZS.
      pose proof (Forall_inv ZS) as ZSTK. cbn [fst snd] in ZSTK.
      unfold lib.Reusable.YG0v.zero_shadow, lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF in ZSTK.
      destruct Hst as [Hst1 Hst2].
      destruct (B.Prog.C_reac_box_model_blockVis.mbV_al (lib.Reusable.YG0f.ly_stk_lo lyc)
                  (lib.Reusable.YG0f.ly_stk_hi lyc) o 32 HALo HAHi ltac:(lia) Hst1 Hst2 ltac:(lia) ltac:(lia))
        as (_ & _ & P3).
      intros s Hs. destruct (P3 s Hs) as (I1 & I2 & _).
      replace s with (0x7fff8000 + lib.Reusable.YG0f.ly_stk_lo lyc / 8 +
                      (s - (0x7fff8000 + lib.Reusable.YG0f.ly_stk_lo lyc / 8))) by lia.
      rewrite (ZSTK _ (conj I1 I2)). discriminate. }
  (* the bytes of ob: what mem2 holds at o *)
  set (ob := map (fun i : nat => match mrd rsegs mem2 (Z_to_bv 64 (o + Z.of_nat i)) with
                                 | Some x => x | None => Z_to_bv 8 0 end) (seq 0 32)).
  exists ob.
  split; [exact RO2|].
  split; [exact HA|].
  split; [exact HS16|].
  split; [exact STW|].
  split; [exact AC2|].
  split; [exact SR2|].
  split; [exact HHM|].
  split; [exact HAE|].
  split; [exact AWW|].
  (* fp [0%nat] at mem2 *)
  split.
  { rewrite Etp'.
    apply (ctl_fp_of_AR TSY LAWS lyc S2 W mem2 md2 [0%nat] (bv_unsigned sp - 4272) (bv_unsigned sp) _ _ HAR2).
    - repeat constructor.
    - unfold FS_SIZE, lib.Reusable.YG0f.kFakeStackSize in *. lia.
    - intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
    - exact WDJ.
    - exact DDJ. }
  (* the thread cells apart (fp_tls_apart at mem2) *)
  split.
  { rewrite Etp'. unfold reac_box_model_block_tls, REAC_BOX_MODEL_BLOCK_K.
    exact (fp_tls_apart TSY LAWS lyc S2 W mem2 md2 [0%nat] (bv_unsigned sp - 4272) (bv_unsigned sp) HAR2
             ltac:(repeat constructor) ltac:(lia) ltac:(lia)). }
  split; [exact Rp|]. split; [exact Rb|]. split; [exact Ro|].
  (* the row's bytes at mem2 *)
  split.
  { intros Hp0. destruct (HROW Hp0) as (P1 & P2 & P3 & _ & P5 & P6 & P7 & P8).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in P5, P6.
    assert (Himg : forall i, 0 <= i < 296 -> lib.Reusable.YG0d.in_img rsegs (p + i))
      by (intros i Hi; exact (mid_img_of_roP RLO RHI RELRO_IMG _ (proj1 (P7 (p + i) ltac:(lia))))).
    split; [exact P1|]. split; [exact P2|].
    split; [|split; [right; unfold HIGHMEM_BEG in HHM; lia | exact P8]].
    rewrite P2 in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    assert (Bc : bytes_at rsegs memc p row).
    { apply (mid_bytes_of_garr8 W memc p row P3); [lia | rewrite P2; cbn; lia |].
      intros i Hi. rewrite P2 in Hi. exact (mid_img_vis W _ (Himg i ltac:(cbn in Hi; lia))). }
    apply (mid_bytes_at W memc mem2 p row Bc). intros i Hi. rewrite P2 in Hi. cbn in Hi.
    destruct (P7 (p + i) ltac:(lia)) as (_ & Hs & He).
    split; [exact (mid_img_vis W _ (Himg i ltac:(lia))) | exact (KIMG _ (Himg i ltac:(lia)) Hs He)]. }
  (* the name's bytes at mem2 *)
  split.
  { intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (N1 & N2 & _ & Bn0 & Bn1 & N4 & N5).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Bn0, Bn1.
    assert (Himg : forall i, 0 <= i < Z.of_nat (length nb) -> lib.Reusable.YG0d.in_img rsegs (rname row + i))
      by (intros i Hi; exact (mid_img_of_roP RLO RHI RELRO_IMG _ (proj1 (N4 (rname row + i) ltac:(lia))))).
    split; [exact N1|].
    split; [|split; [right; unfold HIGHMEM_BEG in HHM; lia | exact N5]].
    assert (Bc : bytes_at rsegs memc (rname row) nb).
    { apply (mid_bytes_of_garr8 W memc (rname row) nb N2); [lia | lia |].
      intros i Hi. exact (mid_img_vis W _ (Himg i Hi)). }
    apply (mid_bytes_at W memc mem2 (rname row) nb Bc). intros i Hi.
    destruct (N4 (rname row + i) ltac:(lia)) as (_ & Hs & He).
    split; [exact (mid_img_vis W _ (Himg i Hi)) | exact (KIMG _ (Himg i Hi) Hs He)]. }
  (* o's cells at mem2 *)
  split.
  { intros Ho0. destruct (OPOS Ho0) as [Of | Os].
    all: split; [|split; [destruct (HOB Ho0) as (_ & _ & _ & _ & Hap); exact Hap |
                          right; unfold JOIN_0013, JOIN_0014, ImgBounds.IMG_HI in *; lia]].
    all: apply (B.ProgWorld.rw_cells_CB_of_present mem2 o 32 ob);
           [unfold ob; rewrite length_map, length_seq; reflexivity | lia |
            unfold lib.Reusable.YG0f.kFakeStackSize in *; lia | | intros i Hi; exact (OPR Ho0 i Hi)].
    all: intros i Hi; unfold ob; rewrite nth_error_map, (nth_error_nth' (seq 0 32) 0%nat)
           by (rewrite length_seq; exact Hi);
         rewrite seq_nth by exact Hi; cbn [option_map]; rewrite Nat.add_0_l;
         destruct (mem2 (Z_to_bv 64 (o + Z.of_nat i))) as [bb|] eqn:Eb;
         [unfold mrd; rewrite Eb; reflexivity | exfalso; exact (OPR Ho0 (Z.of_nat i) ltac:(lia) Eb)]. }
  (* o is not read-only *)
  split.
  { intros Ho0 i Hi. apply B.MemNormTr.ro_addr_above_img.
    destruct (OPOS Ho0) as [Of | Os]; unfold lib.Reusable.YG0f.kFakeStackSize, ImgBounds.IMG_HI in *; lia. }
  (* the row addressable at mem2 (CtrlRo.ro_usable_glob) *)
  split.
  { intros Hp0. destruct (HROW Hp0) as (_ & _ & _ & (q & sz & Hq & Hq1 & Hq2) & P5 & P6 & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in P5, P6.
    apply (mid_addressable W mem2 p 296
             (B.Prog.CtrlRo.ro_usable_glob rsegs B GLOBS lyc S2 W mem2 md2 q sz p 296 HGM Hq HAR2 Hq1 Hq2));
      [lia | lia | unfold APPMEM_END; lia |].
    intros i Hi. unfold app_mem, LOWMEM_END. left. lia. }
  (* the name addressable at mem2 *)
  split.
  { intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (_ & _ & (q & sz & Hq & Hq1 & Hq2) & Bn0 & Bn1 & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Bn0, Bn1.
    apply (mid_addressable W mem2 (rname row) (Z.of_nat (length nb))
             (B.Prog.CtrlRo.ro_usable_glob rsegs B GLOBS lyc S2 W mem2 md2 q sz _ _ HGM Hq HAR2 Hq1 Hq2));
      [lia | lia | unfold APPMEM_END; lia |].
    intros i Hi. unfold app_mem, LOWMEM_END. left. lia. }
  (* o addressable at mem2 *)
  split.
  { intros Ho0. destruct (HOB Ho0) as (Hhome & _ & _ & (_ & RAc & _ & Hamr & Ho1 & Ho2) & _).
    unfold lib.Reusable.YG0d.amem_range, lib.Reusable.YG0f.kLowMemEnd, lib.Reusable.YG0f.kHighMemBeg,
      lib.Reusable.YG0f.kHighMemEnd in Hamr.
    split; [|split; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia |
                     right; destruct (OPOS Ho0) as [Of | Os]; unfold RT_HI, ImgBounds.IMG_HI in *; lia]].
    destruct Hhome as [(cid & pc & Hin & Hcid & Hx) | Hst].
    - apply (mid_addressable W mem2 o 32); [| lia | lia | unfold APPMEM_END; lia |
                                           intros i Hi; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia].
      destruct (lib.Reusable.YG0s.frame_facts B lyc Sc _ cid pc M0 Hin)
        as (_ & _ & _ & _ & HFal & _ & _ & Hfo64 & _ & Hfbm & _).
      intros x Hxr. destruct (RAc x Hxr) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite <- Hs. apply (KFR cid pc _ Hin). right.
      pose proof (Hx x Hxr) as Xr.
      unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0f.frame_addr in Xr.
      cbn [fst snd] in Xr.
      unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.shadow_addr,
        lib.Reusable.YG0f.frame_addr. cbn [fst snd].
      exact (mid_shadow_in_frame _ _ _ x HFal Hfo64 Hfbm Xr).
    - exact (ctl_stack_shadow_of_AR LAWS lyc S2 W mem2 md2 o 32 HAR2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the JOIN blocks addressable at mem2 (CtrlRo.ro_usable) *)
  split.
  { intros _. apply (mid_addressable W mem2 JOIN_0014 32
                       (B.Prog.CtrlRo.ro_usable rsegs B LAWS lyc S2 W mem2 md2 JOIN_0014 32 HAR2 HZS_J14));
      [unfold JOIN_0014; lia | lia | unfold JOIN_0014, APPMEM_END; lia |].
    intros i Hi. unfold app_mem, LOWMEM_END, JOIN_0014. left. lia. }
  split.
  { intros _. apply (mid_addressable W mem2 JOIN_0013 32
                       (B.Prog.CtrlRo.ro_usable rsegs B LAWS lyc S2 W mem2 md2 JOIN_0013 32 HAR2 HZS_J13));
      [unfold JOIN_0013; lia | lia | unfold JOIN_0013, APPMEM_END; lia |].
    intros i Hi. unfold app_mem, LOWMEM_END, JOIN_0013. left. lia. }
  (* the name apart from the class-0 words *)
  split.
  { intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (_ & _ & _ & Bn0 & Bn1 & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Bn0, Bn1.
    apply (mid_ndj _ _ _ HFimg); unfold ImgBounds.IMG_HI; lia. }
  split; [exact Hj|].
  split; [exact H56|].
  split; [exact (HHint 0%nat ltac:(lia))|].
  (* the saved registers: mb_pre_facts at mc, mem_rel, then acall_kept's high-memory clause *)
  split.
  { pose proof (B.MemNormTr.rw_cells_of_rel m1 mc _ _ HREL FRc) as FR1.
    apply (mid_rw_cells W m1 mem2 _ _ FR1).
    intros i Hi. cbn [cells_size csize Nat.add Z.of_nat] in Hi.
    destruct (Hpres2 (bv_unsigned sp + -88 + i) ltac:(lia)) as [Hh (b2 & Hb2)].
    split; [exact Hh|]. split; [apply K1; lia|]. rewrite Hb2. discriminate. }
  (* o at or above the image end, from where o lies (OPOS) *)
  split.
  { intros Ho0. destruct (OPOS Ho0) as [Of | Os]; unfold lib.Reusable.YG0f.kFakeStackSize, ImgBounds.IMG_HI in *; lia. }
  (* the footprint at RNG_W (w_H W) over normalize mem2: a Theorem Labs lane's mbB_rngW at the journal over S2 *)
  apply (B.Prog.C_reac_box_model_blockVis.mbB_rngW B TSY STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W
           mem2 md2 k sp tp p b o row nb HJ2 RO2 Hlo Hhi Etp').
  - intros Hp0. destruct (HROW Hp0) as (P1 & P2 & P3 & _ & P5 & P6 & P7 & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in P5, P6.
    split; [lia|]. split; [lia|]. split; [exact P2|]. split.
    + apply (mid_garr8 _ memc mem2 p _ P3). intros i Hi. rewrite length_map, P2 in Hi.
      destruct (P7 (p + i) ltac:(lia)) as (Hro & Hs & He).
      exact (KIMG _ (mid_img_of_roP RLO RHI RELRO_IMG _ Hro) Hs He).
    + apply (B.Prog.CtrlRo.ro_hull rsegs B lyc S2 W mem2 md2 p 296 HIMGSH HAR2);
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
  - intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (N1 & N2 & _ & Bn0 & Bn1 & N4 & _).
    pose proof N1 as (NL & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Bn0, Bn1.
    split; [lia|]. split.
    + apply (mid_garr8 _ memc mem2 (rname row) _ N2). intros i Hi. rewrite length_map in Hi.
      destruct (N4 (rname row + i) ltac:(lia)) as (Hro & Hs & He).
      exact (KIMG _ (mid_img_of_roP RLO RHI RELRO_IMG _ Hro) Hs He).
    + apply (B.Prog.CtrlRo.ro_hull rsegs B lyc S2 W mem2 md2 (rname row) (Z.of_nat (length nb)) HIMGSH HAR2);
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
  - intros _ Ho0. destruct (HOB Ho0) as (_ & _ & Hwr & _).
    split; [lia|]. split; [destruct (OPOS Ho0) as [Of | Os]; unfold lib.Reusable.YG0f.kFakeStackSize in *; lia|].
    split; [|exact (OHULL Ho0)].
    intros a Ha. destruct (Hwr a Ha) as (_ & [Hh _] & _ & _). split; [exact Hh|].
    destruct (mem2 (Z_to_bv 64 a)) as [bb|] eqn:Eb; [exists bb; reflexivity|].
    exfalso. apply (OPR Ho0 (a - o) ltac:(lia)). replace (o + (a - o)) with a by lia. exact Eb.
Qed.
End Mid.

Print Assumptions mbB_mid.
