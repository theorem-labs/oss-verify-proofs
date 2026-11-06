(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the conclusion of the cgif-form glue of a Theorem Labs lane.

   The two lifted stretches of A/Prog/ctrl_emit_asF2.v now end at `aQg mbz W` (:392) with NARROW munch windows
   (a Theorem Labs lane ca4c8f36aa1): the early return (EE = false) at `aQg m [(LO, SP0)]`, the stack window alone; when
   EE = true the first stretch at aAtLay with `munch aWL m mc`, aWL = [(LO, SP0); (o, o + LEN)], and the
   second stretch at `aQg m5 aWL`, m5 the memory ctrl_lay_block returns. No window holds a side-stack range
   or a shadow range, so every byte the caller-journal keeps (`tcj_kept`, A/Prog/CtrlCallerJ.v) is outside
   each window and is kept by each part.

   Three lemmas, on the REAL memories (the glue carries the normalized stretch facts back by MemNorm.munch_rel
   / wmono_rel / MemNormTr.stk_of_rel):
     - `ge_keep_ret`: the early return; one stretch at the call's own world W, memc -> m'.
     - `ge_keep_lay`: EE = true; stretch 1 at W (memc -> mc), a Theorem Labs lane's ctrl_lay_block contract (its
       tcj_kept, W / mc -> W2 / mem2, at sp := spZ regs + -128 and E := [p + 18, p + 50)), stretch 2 at W2
       (mem2 -> m'). Composed into the one tcj_kept of the statement's post.
     - `ge_post`: with that tcj_kept, the end journal, conjunct 4's two equalities and the result bytes of
       aRES, the end state IS `tctrl_emit_as_post` (A/Prog/C_ctrl_emit_as.v:108-125).

   The kept regions lie below the stack window: the caller's blocks and frames end at or below the allocation
   ceiling (AR_blocks_law, YCbq.frames_bounds), a frame's shadow is in the shadow band below it, the image is
   [0x10000, 0x5fe000); the window [spZ regs - 4640, spZ regs) starts at or above the ceiling (the caller's
   astk_ok). Presence above the ceiling travels by wmono (no segment there); presence in the window comes from
   the end stretch's stk and the caller's journal (the window is visible in W, so in W2 by wle).

   Names: run-side `getr` is lib.Lib.PropExec.getr (the run's register map, as GE_entry builds it); the
   contract reads lib.Reusable.YK11.getr. The two are convertible: pass contract facts by `exact` / as
   arguments, never `rewrite` one copy's getr equality into the other. The six modules that ctrl's
   lib/A/Reusable also holds are named in full, lib.Reusable.<X> (porter a Theorem Labs lane, 2026-10-29 04:03Z).

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): no _F file is Required here; ctrl's address-free
   model files are Required qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase GE_row.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmitLib RcFinLib RcSynthLib.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* ctrl_emit_asF2.v's derived values at row := CROW r, g := 0 (its Local Abbreviations EE, LEN, RR, BLK). *)
Local Abbreviation EEr r n mb :=
  (RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb)).
Local Abbreviation LENr r n := (RcEmit.em_len (RcFin.ubat (CROW r) 21) n).
Local Abbreviation RRr r n mb := (if EEr r n mb then LENr r n else 0).
Local Abbreviation BLKr r md mb nb tb gb :=
  (RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
     (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
        (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb)).

(* ---- small facts ---------------------------------------------------------------------------------------- *)

Lemma gp_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma gp_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

(* A return address the core accepts (lib.Reusable.YK0s.ret_ok, the copy C_ctrl_emit_as.v's premise binds, by
   About) is even, so the run's return pc is the address itself. *)
Lemma gp_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hm : bv_unsigned k mod 2 = 0).
  { rewrite <- Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite gp_mod2_land. apply gp_land_m2. }
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Lemma gp_yshadow_eq : forall x, YG0f.shadow_addr x = 2147450880 + x / 8.
Proof. intros x. reflexivity. Qed.

Lemma gp_hid : forall (W W2 : world SEGS) x, wle W W2 -> w_H W x = false -> w_H W2 x = false.
Proof.
  intros W W2 x Hle Hx. destruct (w_H W2 x) eqn:E; [|reflexivity].
  rewrite (Hle x E) in Hx. discriminate.
Qed.

Lemma gp_munch : forall (WIN : list ivl) (m m' : word -> option byte) a,
  munch WIN m m' -> 0 <= a < 2 ^ 64 -> outside WIN a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros WIN m m' a HM Ha Ho. apply HM. rewrite unsigned_lit by lia. exact Ho. Qed.

(* In one world, a byte that a run leaves alone looks the same before and after. *)
Lemma gp_keepm : forall (WIN : list ivl) (H : word -> bool) (m m' : word -> option byte) a,
  munch WIN m m' -> 0 <= a < 2 ^ 64 -> outside WIN a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros WIN H m m' a HM Ha Ho. pose proof (gp_munch WIN m m' a HM Ha Ho) as E.
  unfold aview, mbyte, mrestrict. cbv beta. rewrite E. reflexivity.
Qed.

Lemma gp_out1 : forall LO SP a, ~ (LO <= a < SP) -> outside [(LO, SP)] a.
Proof. intros LO SP a H. cbn [outside]. split; [exact H | exact I]. Qed.

Lemma gp_out2 : forall LO SP p R a, ~ (LO <= a < SP) -> ~ (p <= a < p + R) -> outside [(LO, SP); (p, p + R)] a.
Proof. intros LO SP p R a H1 H2. cbn [outside]. split; [exact H1 | split; [exact H2 | exact I]]. Qed.

Lemma gp_noimg : forall a, lib.Reusable.YM05.alloc_ceiling <= a -> ~ in_img SEGS a.
Proof.
  intros a Ha Hi. pose proof (ctrl_img_range a Hi). pose proof lib.Reusable.YM05.alloc_ceiling_value. lia.
Qed.

(* Above the ceiling there is no segment, so a byte there that wview shows is a byte the memory holds. *)
Lemma gp_present_of_wview : forall (m : word -> option byte) a,
  lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 ->
  wview rsegs m (Z_to_bv 64 a) <> None -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha Hw.
  assert (Ha' : 0 <= a < 2 ^ 64) by (pose proof lib.Reusable.YM05.alloc_ceiling_value; lia).
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|]. exfalso.
  apply Hw. unfold wview. rewrite E. rewrite (unsigned_lit a Ha').
  rewrite (YCbq.find_segment_none rsegs a (gp_noimg a (proj1 Ha))). reflexivity.
Qed.

Lemma gp_present_of_mrd : forall (m : word -> option byte) a,
  lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 ->
  (exists b, mrd rsegs m (wa a) = Some b) -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha (b & Hb).
  assert (Ha' : 0 <= a < 2 ^ 64) by (pose proof lib.Reusable.YM05.alloc_ceiling_value; lia).
  destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (Hs : seg_rom rsegs (wa a) = None) by exact (YCbq.seg_rom_none rsegs a Ha' (gp_noimg a (proj1 Ha))).
  unfold mrd, wa in Hb. unfold wa in Hs. rewrite E, Hs in Hb. discriminate.
Qed.

(* Presence above the ceiling survives a run that removes no byte. *)
Lemma gp_present_up : forall (H : word -> bool) (m m' : word -> option byte) a,
  lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 -> wmono rsegs m m' -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Ha WM (Hh & b & Hb). split; [exact Hh|].
  apply (gp_present_of_wview m' a Ha). apply WM. unfold wview. rewrite Hb. discriminate.
Qed.

(* A visible byte of a stack window that the run leaves present (stk). *)
Lemma gp_present_win : forall (H : word -> bool) (m : word -> option byte) LO SP a,
  lib.Reusable.YM05.alloc_ceiling <= LO -> SP <= 2 ^ 64 -> LO <= a < SP ->
  stk rsegs m LO SP -> H (Z_to_bv 64 a) = false -> apresent H m a.
Proof.
  intros H m LO SP a HLO HSP Ha (_ & _ & Hst) Hv. split; [exact Hv|].
  destruct (Hst a Ha) as (_ & Hm). apply gp_present_of_mrd; [lia | exact Hm].
Qed.

(* Every byte the caller-journal keeps outside the stack window lies below the window. *)
Lemma gp_below : forall (B : asyms) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
    (mdc : Model) (LO : Z),
  AR_laws SEGS B -> AR SEGS B lyc Sc W memc mdc -> lib.Reusable.YM05.alloc_ceiling <= LO ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> 0 <= b + i < LO) /\
  (forall a, in_img SEGS a -> 0 <= a < LO) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     in_zr a (frame_rng lyc (cid, pos)) \/
     in_zr a (YG0f.shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     0 <= a < LO).
Proof.
  intros B lyc Sc W memc mdc LO LAWS HAR HLO.
  pose proof lib.Reusable.YM05.alloc_ceiling_value as (HC1 & HC2).
  split; [|split].
  - intros b m i Hin Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hbc & _). lia.
  - intros a Hi. pose proof (ctrl_img_range a Hi). lia.
  - intros cid pos a Hin Hr.
    destruct (YCbq.frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
    pose proof (YCbq.fs_frame_bytes_nonneg cid) as Hnn.
    destruct Hr as [Hr | Hr].
    + assert (Hr2 : frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) by exact Hr.
      lia.
    + assert (Hr2 : YG0f.shadow_addr (frame_addr lyc cid pos) <= a <
                    YG0f.shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) by exact Hr.
      pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
      rewrite !gp_yshadow_eq in Hr2.
      rewrite (gp_yshadow_eq (frame_addr lyc cid pos)),
              (gp_yshadow_eq (frame_addr lyc cid pos + fs_frame_bytes cid)) in Hse.
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hfd.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Hfc) as Hd.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) (proj1 HC1)) as Hd2.
      pose proof (Z.mul_div_le lib.Reusable.YM05.alloc_ceiling 8 ltac:(lia)) as Hm.
      assert (E1 : 140735332483072 / 8 = 17591916560384) by reflexivity.
      lia.
Qed.

(* One byte read as a 1-byte little-endian value (Reusable/YI08.v val_mem1's arithmetic). *)
Lemma gp_le_byte1 : forall b : byte, Z_to_bv 8 (le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.

(* lib.Lib's bytes_at of visible bytes is the core's garr8 of the restricted memory. *)
Lemma gp_garr8 : forall (H : word -> bool) (m : word -> option byte) p (bs : list byte),
  bytes_at rsegs m p bs ->
  (forall j, (j < length bs)%nat -> H (Z_to_bv 64 (p + Z.of_nat j)) = false) ->
  garr8 SEGS (mrestrict H m) p (map bv_unsigned bs).
Proof.
  intros H m p bs (Hp & Hlen & Hb) Hv j Hj. rewrite length_map in Hj.
  rewrite (nth_indep (map bv_unsigned bs) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth.
  pose proof (Hb j Hj) as Hr.
  destruct (nth_error bs j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
  rewrite (nth_error_nth bs j (Z_to_bv 8 0) En).
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  split; [|exact Rb].
  intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
  replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) by lia.
  assert (Hm : mbyte SEGS (mrestrict H m) (p + Z.of_nat j) = mrd rsegs m (wa (p + Z.of_nat j))).
  { unfold mbyte, mrestrict, mrd, wa. cbv beta. rewrite (Hv j Hj). reflexivity. }
  rewrite Hm, Hr. f_equal. symmetry. exact (gp_le_byte1 b).
Qed.

(* The length of the result bytes: 18 header bytes, the 32-byte block, len - 52 zeros and the 2-byte trailer. *)
Lemma gp_fr_len : forall db sb c t0 t1 blk len,
  length db = 6%nat -> length sb = 6%nat -> length blk = 32%nat -> 52 <= len ->
  Z.of_nat (length (RcEmit.em_fr db sb c t0 t1 blk len)) = len.
Proof.
  intros db sb c t0 t1 blk len Hd Hs Hb Hl. unfold RcEmit.em_fr, RcEmit.em_hdr.
  rewrite !length_app, Hd, Hs, Hb, repeat_length. cbn [length]. lia.
Qed.

Lemma gp_blk_len : forall r md mb nb, length mb = 296%nat ->
  length (RcFin.fin (EM_C r) 0 0 (RcLay.ly_Z md mb nb (RcLay.ly_bb r))) = 32%nat.
Proof.
  intros r md mb nb Hmb.
  assert (HZ : length (RcLay.ly_Z md mb nb (RcLay.ly_bb r)) = 32%nat).
  { unfold RcLay.ly_Z. destruct (md =? 0); [reflexivity|].
    destruct (RcSynth.rc mb (RcLay.ly_bb r) =? 1); [exact (RcSynthLib.rs_synth_len mb _ nb Hmb) | reflexivity]. }
  pose proof (ge_em_bnd r) as (Hc & _).
  assert (Ec : EM_C r = 0 \/ EM_C r = 1) by lia.
  unfold RcFin.fin. destruct Ec as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - exact HZ.
  - exact (RcFinLib.rcf_stamp32_len _ HZ).
Qed.

(* ---- the caller-journal keep of the whole call ---------------------------------------------------------- *)

(* The early return (EE = false; the stretch's post is aQg m [(LO, SP0)]): one run at the call's own world,
   writing only the stack window. *)
Lemma ge_keep_ret :
  forall (B : asyms) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (E : Z -> Prop) (m' : word -> option byte),
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  munch [(spZ regs - 4640, spZ regs)] memc m' ->
  wmono rsegs memc m' ->
  stk rsegs m' (spZ regs - 4640) (spZ regs) ->
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W memc W m' (spZ regs) E.
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E m'
    LAWS HJc HSPa HSPb HMU HWM HSTK.
  pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_value as (HC1 & HC2).
  assert (HT : TEMIT_STK = 4640) by reflexivity. rewrite HT in HSPa.
  assert (HLO : lib.Reusable.YM05.alloc_ceiling <= spZ regs - 4640) by lia.
  destruct (gp_below B lyc Sc W memc mdc (spZ regs - 4640) LAWS HAR HLO) as (HBb & HBi & HBf).
  unfold tcj_kept. rewrite HT.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw _. apply (gp_keepm _ _ _ _ a HMU); [lia | exact (gp_out1 _ _ a Hw)].
  - intros b m i Hin Hi _. pose proof (HBb b m i Hin Hi) as Hb.
    apply (gp_keepm _ _ _ _ (b + i) HMU); [lia | apply gp_out1; lia].
  - intros a Hi _ _. pose proof (HBi a Hi) as Ha.
    apply (gp_keepm _ _ _ _ a HMU); [lia | apply gp_out1; lia].
  - intros cid pos a Hin Hr _. pose proof (HBf cid pos a Hin Hr) as Ha.
    apply (gp_keepm _ _ _ _ a HMU); [lia | apply gp_out1; lia].
  - intros a Ha _ Hp. exact (gp_present_up _ _ _ a Ha HWM Hp).
  - intros a Ha. destruct (Hwin a ltac:(lia)) as (Hv & _).
    exact (gp_present_win _ _ (spZ regs - 4640) (spZ regs) a HLO ltac:(lia) Ha HSTK Hv).
Qed.

(* EE = true: stretch 1 at W (memc -> mc), ctrl_lay_block's caller-journal keep (W / mc -> W2 / mem2), stretch
   2 at W2 (mem2 -> m'). Each part leaves every kept byte alone; the call's E is the output [p, p + LEN),
   which holds ctrl_lay_block's E = [p + 18, p + 50). *)
Lemma ge_keep_lay :
  forall (B : asyms) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (p n r : Z) (mb : list byte)
    (mc : word -> option byte) (W2 : world SEGS) (mem2 m' : word -> option byte),
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  EEr r n mb = true ->
  (* stretch 1, at W *)
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] memc mc -> wmono rsegs memc mc ->
  (* ctrl_lay_block (a Theorem Labs lane's tctrl_lay_block_post, its tcj_kept conjunct) *)
  wle W W2 ->
  tcj_kept (PI := PI_ctrl) B TLAY_STK lyc Sc W mc W2 mem2 (spZ regs + -128) (fun a => p + 18 <= a < p + 50) ->
  (* stretch 2, at W2 *)
  munch [(spZ regs - 4640, spZ regs); (p, p + LENr r n)] mem2 m' -> wmono rsegs mem2 m' ->
  stk rsegs m' (spZ regs - 4640) (spZ regs) ->
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W memc W2 m' (spZ regs) (fun a => p <= a < p + RRr r n mb).
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n r mb mc W2 mem2 m'
    LAWS HJc HSPa HSPb HPimg HE HMU1 HWM1 Hwle HKL HMU2 HWM2 HSTK.
  pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_value as (HC1 & HC2).
  assert (HT : TEMIT_STK = 4640) by reflexivity. rewrite HT in HSPa.
  assert (HTL : TLAY_STK = 4512) by reflexivity.
  assert (HLO : lib.Reusable.YM05.alloc_ceiling <= spZ regs - 4640) by lia.
  destruct (gp_below B lyc Sc W memc mdc (spZ regs - 4640) LAWS HAR HLO) as (HBb & HBi & HBf).
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as HL.
  assert (ER : RRr r n mb = LENr r n) by (rewrite HE; reflexivity).
  destruct HKL as (K1 & K2 & K3 & K4 & K5 & _).
  rewrite HTL in K1, K5. cbv beta in K1, K2, K4.
  unfold tcj_kept. rewrite HT, ER. cbv beta.
  split; [|split; [|split; [|split; [|split]]]].
  - (* above the ceiling, outside the window and the output *)
    intros a Ha Hw HEa.
    transitivity (aview SEGS (w_H W2) mem2 a).
    { apply (gp_keepm _ _ _ _ a HMU2); [lia | exact (gp_out2 _ _ _ _ a Hw HEa)]. }
    transitivity (aview SEGS (w_H W) mc a).
    { apply K1; [exact Ha | lia | lia]. }
    apply (gp_keepm _ _ _ _ a HMU1); [lia | exact (gp_out2 _ _ _ _ a Hw HEa)].
  - (* the caller's blocks *)
    intros b m i Hin Hi HEb. pose proof (HBb b m i Hin Hi) as Hb.
    transitivity (aview SEGS (w_H W2) mem2 (b + i)).
    { apply (gp_keepm _ _ _ _ (b + i) HMU2); [lia | apply gp_out2; lia]. }
    transitivity (aview SEGS (w_H W) mc (b + i)).
    { apply (K2 b m i Hin Hi). lia. }
    apply (gp_keepm _ _ _ _ (b + i) HMU1); [lia | apply gp_out2; lia].
  - (* the image *)
    intros a Hi Hns Herr. pose proof (HBi a Hi) as Ha.
    assert (Hnp : ~ (p <= a < p + LENr r n)) by (intros Hp; exact (HPimg a ltac:(lia) Hi)).
    transitivity (aview SEGS (w_H W2) mem2 a).
    { apply (gp_keepm _ _ _ _ a HMU2); [lia | apply gp_out2; [lia | exact Hnp]]. }
    transitivity (aview SEGS (w_H W) mc a).
    { exact (K3 a Hi Hns Herr). }
    apply (gp_keepm _ _ _ _ a HMU1); [lia | apply gp_out2; [lia | exact Hnp]].
  - (* the caller's frames and their shadow *)
    intros cid pos a Hin Hr HEa. pose proof (HBf cid pos a Hin Hr) as Ha.
    transitivity (aview SEGS (w_H W2) mem2 a).
    { apply (gp_keepm _ _ _ _ a HMU2); [lia | apply gp_out2; lia]. }
    transitivity (aview SEGS (w_H W) mc a).
    { apply (K4 cid pos a Hin Hr). lia. }
    apply (gp_keepm _ _ _ _ a HMU1); [lia | apply gp_out2; lia].
  - (* presence above the ceiling, outside the window *)
    intros a Ha Hw Hp.
    apply (gp_present_up _ mem2 m' a Ha HWM2).
    apply K5; [exact Ha | lia | exact (gp_present_up _ memc mc a Ha HWM1 Hp)].
  - (* presence in the window *)
    intros a Ha. destruct (Hwin a ltac:(lia)) as (Hv & _).
    exact (gp_present_win _ _ (spZ regs - 4640) (spZ regs) a HLO ltac:(lia) Ha HSTK (gp_hid W W2 _ Hwle Hv)).
Qed.

(* ---- the glue's conclusion ------------------------------------------------------------------------------ *)

Lemma ge_post :
  forall (B : asyms) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (p md c16 n r : Z) (mb nb db sb tb gb : list byte)
    (W2 : world SEGS) (ly2 : alayout) (S2 : astate) (m' : word -> option byte) (md2 : Model)
    (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  (* the call's own premises (tctrl_emit_as_spec) that the post reads *)
  lib.Reusable.YK0s.ret_ok (getr regs 1) ->
  getr regs 15 = w64 c16 -> 0 <= c16 < 2 ^ 64 ->
  3 <= r <= 9 ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  length mb = 296%nat -> length db = 6%nat -> length sb = 6%nat ->
  wle W W2 ->
  (* the result bytes of the run's post (ctrl_emit_asF2.aRES, at row := CROW r, g := 0, o := p) *)
  (EEr r n mb = true ->
     bytes_at rsegs m' p
       (RcEmit.em_fr db sb (bv_unsigned (getr regs 15) mod 65536) (nth 0 (CROW r) (Z_to_bv 8 0))
          (nth 1 (CROW r) (Z_to_bv 8 0)) (BLKr r md mb nb tb gb) (LENr r n))) ->
  (* conjuncts 2 and 4 of the post, which the glue builds *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m' md2
    (k + (if RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb) then EV_EMIT else 0)) ->
  frames S2 = frames Sc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  (* the caller-journal keep of the whole call (ge_keep_ret or ge_keep_lay) *)
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W memc W2 m' (spZ regs) (fun a => p <= a < p + RRr r n mb) ->
  tctrl_emit_as_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb W2
    (mkCfg (MS (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) t0' t1' t2' (getr regs 8) (getr regs 9)
                    (Z_to_bv 64 (RRr r n mb)) a1' a2' a3' a4' a5' a6' a7' (getr regs 18) (getr regs 19)
                    (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
                    (getr regs 26) (getr regs 27) t3' t4' t5' t6')
               lib.Reusable.YK11.fp_regs (ret_pc (getr regs 1)) lib.Reusable.YK11.fp_csr None m'
               (seg_rom rsegs)) md2).
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb tb gb
    W2 ly2 S2 m' md2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    Hret Hc16 Hc16r Hr HTW Hmb Hdb Hsb Hwle HRES HJ2 HFR HBL HK.
  unfold tctrl_emit_as_post. cbv beta zeta.
  rewrite (ge_row_E r n mb), (ge_row_LEN r n) in HK, HRES |- *.
  rewrite (ge_row_BLK r md mb nb tb gb Hr), ge_row_nth0, ge_row_nth1, Hc16 in HRES.
  unfold w64 in HRES. rewrite (unsigned_lit c16 Hc16r) in HRES.
  set (EE := RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb)) in *.
  set (LEN := RcEmit.em_len (EM_L r) n) in *.
  match goal with |- exists _ _ (regs2 : bvmap 5 word) _ _, mkCfg (MS ?X _ _ _ _ _ _) _ = _ /\ _ =>
    exists ly2, S2, X, m', md2 end.
  split; [rewrite (gp_ret_pc _ Hret); reflexivity|].
  split; [exact HJ2|].
  split.
  { intros r0 Hr0. unfold acallee_saved in Hr0.
    destruct Hr0 as [-> | [-> | [-> | [-> | [-> | Hr0]]]]]; [reflexivity .. |].
    assert (E : r0 = 18 \/ r0 = 19 \/ r0 = 20 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/
                r0 = 26 \/ r0 = 27) by lia.
    destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity. }
  split; [exact HFR|]. split; [exact HBL|].
  split; [reflexivity|].
  split; [|exact HK].
  (* the result bytes, through bytes_at -> garr8; each output byte is visible in W (twr_ok), so in W2 *)
  intros HE. pose proof (HRES HE) as Hb. apply gp_garr8; [exact Hb|].
  pose proof (RcEmitLib.em_len_rng _ _ _ _ HE) as HL. fold LEN in HL.
  pose proof (gp_fr_len db sb (c16 mod 65536) (Z_to_bv 8 0xcd) (Z_to_bv 8 0xea)
                (RcFin.fin (EM_C r) 0 0 (RcLay.ly_Z md mb nb (RcLay.ly_bb r))) LEN Hdb Hsb
                (gp_blk_len r md mb nb Hmb) ltac:(lia)) as HFl.
  intros j Hj. destruct (HTW (p + Z.of_nat j) ltac:(lia)) as (_ & (Hv & _) & _).
  exact (gp_hid W W2 _ Hwle Hv).
Qed.

End b.
