(* fuzz_ctrl image A, ctrl_emit_as (0x849d8), cgif-form glue of a Theorem Labs lane: the caller's OWN memory at the call.

   For the call state (W, memc) of A/Prog/C_ctrl_emit_as.v `tctrl_emit_as_spec`, this file turns the statement's
   world-form premises about the output buffer [p, p + 1492), the 6-byte source d and the stack window
   [spZ regs - 4640, spZ regs) into the lib.Lib forms that A/Prog/ctrl_emit_asF2.v `Section Emit` takes
   (glue instance o := p, d := d, m := memc, sp := getr regs 2, RNG := ProgBridge.RNG_W (w_H W)):

     ge_buf_rw     twr_ok                                  -> ROB, and HEo's rw_cells conjunct
     ge_buf_addr   afobj + amem_range + the not-image line -> AO
     ge_buf_shcov  AR (from ajournal) + AR_laws + tfr_hull -> ROBS
     ge_src_addr   tsrc_ok                                 -> Ad, first half of APD
     ge_src_app7   tsrc_ok + d mod 8 = 0                   -> APD (d mod 8 = 0 is NOT a premise of the statement)
     ge_src_bytes  garr8 + tsrc_ok                         -> HD
     ge_src_vis    tsrc_ok                                 -> RDB, RDBS
     ge_win        ajournal (presence clause, astk_ok)     -> RWIN, HST

   The buffer's length is a variable `len` with 0 <= len <= 1492; the glue takes len := LEN =
   RcEmit.em_len (ubat (CROW r) 21) n under EE = true.

   The one step from a world read to a lib.Lib read: a world never hides a segment byte (YA0n.w_Hoff), so a byte
   that `aview` reads is visible and is the byte `mrd` reads (YA0o.mbyte_mrestrict_some). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   World reads as lib.Lib reads. *)
Lemma ge_mrd_mbyte : forall m a, mrd rsegs m (wa a) = mbyte SEGS m a.
Proof. intros m a. reflexivity. Qed.

Lemma ge_vis_byte : forall (W : world SEGS) memc a v,
  aview SEGS (w_H W) memc a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs memc (wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W memc a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict (w_H W) memc) a) as [b|] eqn:E; [|discriminate].
  cbn [option_map] in Hv. injection Hv as <-.
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc a b (w_Hoff W) E) as [M Hh].
  split; [exact Hh|]. exists b. split; [rewrite ge_mrd_mbyte; exact M | reflexivity].
Qed.

Lemma ge_vis_some : forall (W : world SEGS) memc a,
  aview SEGS (w_H W) memc a <> None ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs memc (wa a) = Some b.
Proof.
  intros W memc a Hv. destruct (aview SEGS (w_H W) memc a) as [v|] eqn:E; [|congruence].
  destruct (ge_vis_byte W memc a v E) as (Hh & b & Hb & _). split; [exact Hh | exists b; exact Hb].
Qed.

Lemma ge_signed_byte : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A byte of an array that the world reads is the byte lib.Lib reads. *)
Lemma ge_bytes_of_garr8 : forall (W : world SEGS) memc a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) memc) a (map bv_unsigned bs) ->
  bytes_at rsegs memc a bs.
Proof.
  intros W memc a bs Ha Hl HG. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  assert (Hi' : (i < length (map bv_unsigned bs))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV _].
  pose proof (HV 0%nat ltac:(lia)) as H0.
  assert (En : nth i (map bv_unsigned bs) 0 = bv_unsigned b).
  { apply nth_error_nth. rewrite nth_error_map, Eb. reflexivity. }
  rewrite En in H0.
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in H0 by lia.
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc _ _ (w_Hoff W) H0) as [M _].
  rewrite ge_mrd_mbyte, M. f_equal.
  assert (R : 0 <= bv_unsigned b < 256) by exact (bv_unsigned_in_range 8 b).
  match goal with |- Z_to_bv 8 (?f _ _ _) = _ => unfold f end.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  rewrite (Z.mod_small (bv_unsigned b) 256) by exact R.
  apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned b)) with (bv_unsigned b mod 2 ^ 8).
  apply Z.mod_small. exact R.
Qed.

(* A range whose shadow bytes the world reads, each one allowing its byte, is lib.Lib-addressable. *)
Lemma ge_addressable : forall (W : world SEGS) memc q n,
  0 <= q -> 0 <= n -> q + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (q + i)) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n ->
  addressable memc q n.
Proof.
  intros W memc q n Hq Hn Hqn Happ HR. split; [exact Hq|]. split; [exact Hn|]. split; [exact Hqn|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (q + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (ge_vis_byte W memc _ s Hs) as (_ & b & Hb & Eb).
  exists b. split.
  - replace (AsanRT.shadow_addr (q + i)) with (shadow_of_addr SHADOW_OFF (q + i))
      by (unfold AsanRT.shadow_addr, shadow_of_addr, ASAN_K, SHADOW_OFF; lia).
    exact Hb.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
    unfold shadow_ok, saddr_ok in *. subst s.
    rewrite ge_signed_byte by (destruct Hok as [E | [E1 E2]]; lia).
    destruct Hok as [E | [E1 E2]]; [left; exact E | right; lia].
Qed.

Lemma ge_app_of_amem : forall q n i, 0 <= q -> amem_range q n -> 0 <= i <= n -> app_mem (q + i).
Proof.
  intros q n i Hq HA Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

Lemma ge_amem_end : forall q n, amem_range q n -> q + n <= APPMEM_END.
Proof. intros q n HA. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA. unfold APPMEM_END. lia. Qed.

(* Present bytes are visible bytes and stack bytes of lib.Lib. *)
Lemma ge_present_vis : forall (H : word -> bool) memc lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> apresent H memc a) -> range_visible H lo len.
Proof. intros H memc lo len H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros a Ha. exact (proj1 (HP a Ha)). Qed.

Lemma ge_present_stk : forall (H : word -> bool) memc lo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H memc a) -> stk rsegs memc lo hi.
Proof.
  intros H memc lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (HP a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* The 8-aligned shadow word of x, in both spellings of the shadow address. *)
Lemma ge_sh8 : forall x, AsanRT.shadow_addr x / 8 * 8 = ASAN_K + x / 64 * 8.
Proof.
  intros x. unfold AsanRT.shadow_addr, ASAN_K.
  replace (x / 8 + 0x7fff8000) with (x / 8 + 268431360 * 8) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.

Lemma ge_sh8c : forall x, YG0f.shadow_addr x / 8 * 8 = ASAN_K + x / 64 * 8.
Proof.
  intros x. unfold YG0f.shadow_addr, SHADOW_OFF, ASAN_K.
  replace (0x7fff8000 + x / 8) with (x / 8 + 268431360 * 8) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.

(* The runtime's data range [RT_LO, RT_HI) lies in the image's segments [0x9e000, 0xa1000) and
   [0xa1000, 0x5fe000) (A/ProgBridge.v rsegs_spans). *)
Lemma ge_rt_img : forall x, RT_LO <= x < RT_HI -> in_img SEGS x.
Proof.
  intros x Hx.
  assert (G : forall b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs) ->
    b <= x < b + sz -> in_img SEGS x).
  { intros b sz Hin Hb. apply in_map_iff in Hin as (sg & E & Hsg). injection E as <- <-.
    exists sg. split; [exact Hsg | exact Hb]. }
  rewrite rsegs_spans in G. unfold RT_LO, RT_HI in Hx.
  destruct (Z_lt_le_dec x 0xa1000) as [h | h].
  - apply (G 0x9e000 0x3000); [right; right; left; reflexivity | lia].
  - apply (G 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

Section e.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------
   The output buffer [p, p + len), len <= 1492. *)

(* ROB and HEo's rw_cells conjunct: the caller may write every byte of the buffer, so each byte is present. *)
Lemma ge_buf_rw : forall STK sp0 FP ly S lyc Sc own (W : world SEGS) memc (regs : bvmap 5 word) p len,
  0 < p -> p + 1492 <= 2 ^ 47 - 8 ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  0 <= len <= 1492 ->
  range_visible (w_H W) p len /\ exists junk, rw_cells rsegs memc p [CB (Z.to_nat len) junk].
Proof.
  intros STK sp0 FP ly S lyc Sc own W memc regs p len Hp Hpe HW Hlen.
  assert (HP : forall a, p <= a < p + len -> apresent (w_H W) memc a)
    by (intros a Ha; destruct (HW a ltac:(lia)) as (_ & HPa & _); exact HPa).
  split; [apply (ge_present_vis _ memc); [lia | lia | exact HP]|].
  pose proof (ge_present_stk (w_H W) memc p (p + len) ltac:(lia) ltac:(lia) HP) as Hstk.
  destruct (stk_carve rsegs memc p (p + len) (Z.to_nat len) Hstk ltac:(lia)) as (_ & junk & Hc).
  exists junk. replace (p + len - Z.of_nat (Z.to_nat len)) with p in Hc by lia. exact Hc.
Qed.

(* AO: the buffer is addressable, ends in application memory, and misses the runtime's data range (which is
   image memory, and the buffer holds no image byte). *)
Lemma ge_buf_addr : forall lyc Sc (W : world SEGS) memc p len,
  0 < p -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  0 <= len <= 1492 ->
  addressable memc p len /\ app_mem (p + len) /\ (p + len <= RT_LO \/ RT_HI <= p).
Proof.
  intros lyc Sc W memc p len Hp HAM HNI (_ & _ & HRA) Hlen.
  pose proof (ge_amem_end p 1492 HAM) as HE.
  split; [|split].
  - apply (ge_addressable W memc); [lia | lia | lia | |].
    + intros i Hi. apply (ge_app_of_amem p 1492 i); [lia | exact HAM | lia].
    + eapply range_addressable_sub; [exact HRA | lia | lia].
  - apply (ge_app_of_amem p 1492 len); [lia | exact HAM | lia].
  - destruct (Z_le_gt_dec (p + len) RT_LO) as [h | h]; [left; exact h|].
    destruct (Z_le_gt_dec RT_HI p) as [h' | h']; [right; exact h'|].
    exfalso. apply (HNI (Z.max p RT_LO)); [unfold RT_LO in *; lia|].
    apply ge_rt_img. unfold RT_LO, RT_HI in *. lia.
Qed.

(* ROBS: the 8-aligned shadow cover of the buffer is the shadow of tfr_hull's 64-byte envelope, which lies in a
   frame of the caller's state; AR keeps that frame's shadow present (YG0d.v AR_frames_law). *)
Lemma ge_buf_shcov : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p len,
  AR_laws SEGS B ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 < p -> p + 1492 <= 2 ^ 47 - 8 ->
  tfr_hull lyc Sc p 1492 ->
  0 <= len <= 1492 ->
  sh_cov_vis (w_H W) p (p + len - 1).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p len LAWS HJ Hp Hpe
    (cid & pos & Hin & _ & Hlo & Hhi) Hlen.
  pose proof HJ as (HAR & _).
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _ & _ & Hsh).
  set (F := frame_addr lyc cid pos) in *. set (FB := fs_frame_bytes cid) in *.
  pose proof (Z.div_mod F 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as B8.
  pose proof (Z.div_mod FB 8 ltac:(lia)) as DB. pose proof (Z.mod_pos_bound FB 8 ltac:(lia)) as BB.
  pose proof (Z.div_mod p 64 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 64 ltac:(lia)) as Bp.
  pose proof (Z.div_mod (p + 1492 - 1) 64 ltac:(lia)) as Dq.
  pose proof (Z.mod_pos_bound (p + 1492 - 1) 64 ltac:(lia)) as Bq.
  unfold sh_cov_vis. intros x y Hx Hy. rewrite !ge_sh8.
  pose proof (Z.div_le_mono p x 64 ltac:(lia) Hx) as Mx.
  pose proof (Z.div_le_mono y (p + 1492 - 1) 64 ltac:(lia) ltac:(lia)) as My.
  unfold range_visible, ASAN_K. split; [lia|]. split; [lia|].
  intros a Ha.
  assert (Hi : 0 <= a - YG0f.shadow_addr F < FB / 8).
  { unfold YG0f.shadow_addr, SHADOW_OFF. lia. }
  destruct (Hsh (a - YG0f.shadow_addr F) Hi) as [[Hh _] _].
  replace (YG0f.shadow_addr F + (a - YG0f.shadow_addr F)) with a in Hh by lia.
  exact Hh.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The 6-byte source d. *)

(* Ad and the first half of APD. *)
Lemma ge_src_addr : forall (W : world SEGS) memc (regs : bvmap 5 word) d,
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  addressable memc d 6 /\ app_mem (d + 6).
Proof.
  intros W memc regs d (_ & HRA & _ & HAM & H0 & _).
  pose proof (ge_amem_end d 6 HAM) as HE.
  split.
  - apply (ge_addressable W memc); [exact H0 | lia | exact HE | | exact HRA].
    intros i Hi. apply (ge_app_of_amem d 6 i); [exact H0 | exact HAM | lia].
  - apply (ge_app_of_amem d 6 6); [exact H0 | exact HAM | lia].
Qed.

(* APD. `amem_range d 6` leaves d + 7 = LOWMEM_END and d + 7 = APPMEM_END open; d's 8-alignment closes both.
   `d mod 8 = 0` is NOT a premise of tctrl_emit_as_spec. *)
Lemma ge_src_app7 : forall (W : world SEGS) memc (regs : bvmap 5 word) d,
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  d mod 8 = 0 ->
  app_mem (d + 6) /\ app_mem (d + 7).
Proof.
  intros W memc regs d (_ & _ & _ & HAM & H0 & _) Hd8.
  pose proof (Z.div_mod d 8 ltac:(lia)) as D.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* HD. *)
Lemma ge_src_bytes : forall (W : world SEGS) memc (regs : bvmap 5 word) d (db : list byte),
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  bytes_at rsegs memc d db.
Proof.
  intros W memc regs d db Hl HG (_ & _ & _ & _ & H0 & H63).
  apply (ge_bytes_of_garr8 W); [exact H0 | rewrite Hl; cbn [Z.of_nat Pos.of_succ_nat]; lia | exact HG].
Qed.

(* RDB and RDBS: every byte of d and of its 8-aligned shadow cover is read by the world, so it is visible. *)
Lemma ge_src_vis : forall (W : world SEGS) memc (regs : bvmap 5 word) d,
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 ->
  range_visible (w_H W) d 6 /\ sh_cov_vis (w_H W) d (d + 5).
Proof.
  intros W memc regs d (HS & _ & HHV & _ & H0 & H63).
  split.
  - split; [exact H0|]. split; [lia|]. intros a Ha.
    destruct (HS a Ha) as [Hv _]. exact (proj1 (ge_vis_some W memc a Hv)).
  - unfold sh_cov_vis. intros x y Hx Hy. rewrite !ge_sh8.
    pose proof (Z.div_le_mono d x 64 ltac:(lia) Hx) as Mx.
    pose proof (Z.div_le_mono y (d + 5) 64 ltac:(lia) Hy) as My.
    pose proof (Z.div_pos d 64 ltac:(lia) ltac:(lia)) as Pd.
    pose proof (Z.mul_div_le (d + 5) 64 ltac:(lia)) as Ud.
    unfold range_visible, ASAN_K. split; [lia|]. split; [lia|].
    intros a Ha. apply (ge_vis_some W memc a). apply HHV.
    replace (d + 6 - 1) with (d + 5) by lia. rewrite !ge_sh8c. unfold ASAN_K. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   RWIN and HST: the window [spZ regs - 4640, spZ regs) lies in the journal's stack [sp0 - STK, sp0), whose
   every byte the caller's journal keeps present (YCbq.v ajournal, presence clause), and above the
   allocation ceiling (astk_ok). *)
Lemma ge_win : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  range_visible (w_H W) (spZ regs - 4640) 4640 /\ stk rsegs memc (spZ regs - 4640) (spZ regs).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & HK & _).
  destruct HK as (_ & _ & HC & HL & HH & H47 & _).
  pose proof (proj1 (@lib.Reusable.YM05.alloc_ceiling_val rc)) as CV.
  assert (HT : 4640 <= TEMIT_STK) by (unfold TEMIT_STK; lia).
  split.
  - apply (ge_present_vis _ memc); [lia | lia | intros a Ha; apply HP; lia].
  - apply (ge_present_stk (w_H W) memc); [lia | lia | intros a Ha; apply HP; lia].
Qed.

End e.
End b.
