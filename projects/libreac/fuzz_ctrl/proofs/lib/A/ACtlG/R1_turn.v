(* lib/A/ACtlG/R1_turn.v -- GLUE for stage seg_R1_turn of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v, Hypothesis seg_R1_turn).  Written by a Theorem Labs lane's stage lane (tree (internal path)),
   following glue-pattern.md (a working note, not in this delivery).  rule 24: no function proved.

   WHAT IT PROVES
     glue_seg_R1_turn : forall POST (t : Z),
       (t < 5 -> CF POST (C_A81414_at (t + 1))) -> CF POST C_A81b14 -> CF POST C_A814f8 -> CF POST (C_A81414_at t)
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []) and ACtl.v's C_A81414_at (restated below
   as a notation with ACtl.v's definiens, so ACtl.v's hypothesis is this statement up to delta).  One turn of the
   our[] loop at 0x81414 (ctrl's r1_turn, Seg/R1.v:1275): the inline fuzz_u8 arm (our[t] = in[t] when t < n, else
   0), then the back edge to turn t + 1, or after turn 5 the tail to P3 (0x81b14) or, on the odd-mode arm, the
   three tail stages and the call of reac_box_catalogue to R2 (0x814f8).

   THE PROOF (glue-pattern.md steps G1-G5)
   G1  unfold the entry cut C_A81414_at t (its turn pin and C_A81414's 35 conjuncts, ACtlCutP.v:1173-1195).
   G2  the run's premises from visible state: the frame (AR_frames_law at the cut's own frame, frame law,
       layout_le), its fake-stack position (am_wf's wf_fakestack and am_layout's lo_app give fr >= 6328320),
       the stack window (the journal's present window), the input block (the core's pre, the body's Permutation,
       AR_blocks_law / AR_shadow_law / sep_block_frame), and the carried ctl_rt_C (route (C), a working branch 1899bed1aee),
       of which the run reads only asan_cells: no run of the turn takes a shadow premise (shadow-rw-consumers-A.md (a working note, not in this delivery);
       the odd-mode arm's runs are R1F's `_on` forms, whose shadow premise is dropped).
   G3  ProgBridge.cfg_at_MS and Reusable.YA0nR.SRr_xregs_eqv move the walk to the canonical map mkR_of regs3.
   G4  the whole turn is ONE footprint run r1g_turn_run at RNG := ProgBridge.RNG_W (w_H W3), composed from
       a Theorem Labs lane's Seg/R1F.v twins r1_z_evt_F, r1_ld_evt_F, r1_mode_evt_F and the route (C) forms r1_spill_evt_F_on,
       r1_shadow_evt_F_on, r1_call_evt_F_on (R1F.v at a working branch 71e9f40f70a, blob 2db2265bda2), and
       on the w = 0 mode arm the narrowed twin Seg/R1Fs.v r1_mode_evt_Fs (below); lifted once by
       Reusable.YA0nR.SRr_fevt_hid.  NO LIFT IS CITED: r1_call_evt_F_on carries reac_box_catalogue_contract_F_on as
       its own first premise and its run spans the call, so the glue supplies that premise with the callee's closed
       theorem reac_box_catalogueF.reac_box_catalogue_F_holds_on (a Theorem Labs lane 330e60af39d) and lifts the
       WHOLE run (route (a), a Theorem Labs lane 04:10Z); the caller obligations are the contract's premises, which
       r1_call_evt_F_on's own premises pay.
   G5  the three exits, each by the exit cut's ctl_from at the run's end map R and memory m': the journal by
       Reusable.YCbq.ajournal_exec with the write set Wr := not-outside the run's munch list (every written byte
       is the cut's own class-6 frame, its shadow, or the stack window [c_sp - LLVMF_STK, c_sp)), the hidden bytes
       from SRr_fevt_hid; ctl_rt_C at the same ly3 S3 (r1g_ctlrt_C): asan_cells from the run's post, the regions
       cut_shadow / img_shadow carried by the run's transport r1g_srw_tr (the our[t] write by
       ShadowRwOnT.shadow_rw_on_kept, the odd-mode arm by its three runs' own forall-P posts), ro_agree kept below
       IMG_HI; the body's memory
       conjuncts transported along the munch (every write lies in the zone r1g_zone).

   THE NARROWED TWIN Seg/R1Fs.v (agreed with two Theorem Labs lanes, 04:39Z): R1F.r1_mode_evt_F states its two
   footprint premises `ExecF.rng RNG (pm / 8 + K) 1` and `ExecF.rng RNG pm 1` UNGUARDED, though the run reads those
   bytes only when w <> 0.  At w = 0 (input length 6) pm = in + 6 is one byte past the 6-byte input block, which no
   core law makes visible, so R1F's twin cannot be met at RNG_W there.  R1Fs.r1_mode_evt_Fs guards both by
   `w <> 0 ->`, and R1Fs.r1_mode_evt_F_of_Fs re-derives R1F's twin from it under a constr_eq pin.

   SECTION HYPOTHESES: LAWS alone (the core's AR laws, YCbq Section a0's hypothesis), as ACtl.v:210 states it.
   No placeholder: the kit helpers are cited from A.ACtlG.Kit (kit_wx, kit_segs_low, kit_frac_move; Kit.v builds on
   the glue base 46eb24cd4b3).  No _hid placeholder: SRr_fevt_hid's own continuation carries the hidden bytes.

   NO LOCAL COPY OF A PROGWORLD FACT: the frame bound (a live fake frame lies above the image) is cited by name,
   A.ProgWorld_Fs.ctl_frame_above_img : A.ProgWorld.ctl_frame_above_img_stmt B (a Theorem Labs lane, premise-free, files taken
   by path from a working branch fec8db0a380).  The r1g_* lemmas are this stage's own memory and geometry
   steps (zone transports, the journal step, ctl_rt across the turn).

   CLOSURE: every project Require is qualified, no Import of a project module.
   SHADOWED NAMES: getr / seg_rom are the core's YK11 (alias YK, full path), cfg_at is Reusable.YG0d.cfg_at.

   BUILD STATE: on the stand-in-free glue base (5da74c9c931 merged) and a working branch 1899bed1aee; no stand-in
   anywhere in the closure.  No value or bound here depends on a core numeral that differs between planning and record. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACfn A.ACtlCut A.ACtlCutP A.ProgBridge A.BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
(* Lib.Mem / MState / Step / Cells / PropExec / Frame also exist under lib/A/Bz/Lib and lib/AZ/Lib: full paths. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel Prog.RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_box_catalogue_c A.Prog.reac_box_catalogueF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R1F A.Prog.Seg.R1Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

Module YK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module YM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module YO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module YKb := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module EF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module MSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module RG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RF1 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R1F.
Module RF1s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R1Fs.
Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module RBF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogueF.

(* The core's segment list (ACtlCut.v:74) and ctrl's runs' (A/Img0.v); ProgBridge.tfibsegs_rsegs is eq_refl. *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* =================================================================================================================
   1. Memory helpers, generic in the memory (no cut, no world). *)

Lemma r1g_out_dec : forall (W : list FRM.ivl) x, FRM.outside W x \/ ~ FRM.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [FRM.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [L|L]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [L2|L2]; [right; tauto | left; split; [lia | exact H]].
Qed.

Lemma r1g_tops : A.BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r1g_fs_none : forall a, 0x5fe000 <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (A.BzBridge.find_segment_below rsegs 0x5fe000 a 1 s r1g_tops E ltac:(lia)); lia.
Qed.

(* A byte at or above IMG_HI is in no segment, so a writable view of it is a stored byte. *)
Lemma r1g_some_of_wview : forall (m : word -> option byte) (x : word), 0x5fe000 <= bv_unsigned x ->
  wview rsegs m x <> None -> m x <> None.
Proof.
  intros m x Hx H. unfold wview in H. destruct (m x) as [b|] eqn:E; [discriminate|].
  rewrite (r1g_fs_none _ Hx) in H. exfalso. exact (H eq_refl).
Qed.

Lemma r1g_wview_of_some : forall (m : word -> option byte) (x : word) b, m x = Some b -> wview rsegs m x <> None.
Proof. intros m x b E. unfold wview. rewrite E. discriminate. Qed.

(* A stored byte at or above IMG_HI stays stored across a run that only grows the writable view. *)
Lemma r1g_some_after : forall (m m' : word -> option byte) a, FRM.wmono rsegs m m' -> 0x5fe000 <= a < 2 ^ 64 ->
  (exists b, m (Z_to_bv 64 a) = Some b) -> exists b, m' (Z_to_bv 64 a) = Some b.
Proof.
  intros m m' a WM Ha (b & E).
  pose proof (WM _ (r1g_wview_of_some m _ b E)) as V.
  assert (N : m' (Z_to_bv 64 a) <> None).
  { apply r1g_some_of_wview; [rewrite MSt.unsigned_lit by lia; lia | exact V]. }
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (N eq_refl)].
Qed.

Lemma r1g_present_after : forall H (m m' : word -> option byte) a, FRM.wmono rsegs m m' -> 0x5fe000 <= a < 2 ^ 64 ->
  Reusable.YG0n.apresent H m a -> Reusable.YG0n.apresent H m' a.
Proof.
  intros H m m' a WM Ha (Hh & E). split; [exact Hh|]. exact (r1g_some_after m m' a WM Ha E).
Qed.

Lemma r1g_present_munch : forall H W (m m' : word -> option byte) a, Reusable.YG0n.apresent H m a ->
  FRM.munch W m m' -> FRM.outside W a -> 0 <= a < 2 ^ 64 -> Reusable.YG0n.apresent H m' a.
Proof.
  intros H W m m' a (Hh & b & E) MU Ho Ha. split; [exact Hh|]. exists b.
  rewrite (MU (Z_to_bv 64 a)); [exact E|]. rewrite MSt.unsigned_lit by exact Ha. exact Ho.
Qed.

Lemma r1g_stk_some : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> exists b, m (Z_to_bv 64 a) = Some b) -> FRM.stk rsegs m lo hi.
Proof.
  intros m lo hi H0 H1 P. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (P a Ha) as (b & E). unfold MEM.wa. split.
  - exact (r1g_wview_of_some m _ b E).
  - exists b. unfold MEM.mrd. rewrite E. reflexivity.
Qed.

Lemma r1g_stk : forall H (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H m a) -> FRM.stk rsegs m lo hi.
Proof. intros H m lo hi H0 H1 P. apply r1g_stk_some; [exact H0 | exact H1 |]. intros a Ha. exact (proj2 (P a Ha)). Qed.

Lemma r1g_cbl : forall cs, CEL.cells_wf cs -> length (CEL.cells_bytes cs) = CEL.cells_size cs.
Proof.
  induction cs as [|c cs IH]; cbn [CEL.cells_wf CEL.cells_bytes CEL.cells_size]; [reflexivity|].
  intros [Hc Hr]. rewrite length_app, (CEL.cbytes_length c Hc), (IH Hr). reflexivity.
Qed.

(* An n-byte CB cell over present bytes. *)
Lemma r1g_rwcb : forall H (m : word -> option byte) a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> Reusable.YG0n.apresent H m x) ->
  exists xs, STP.rw_cells rsegs m a [CEL.CB n xs].
Proof.
  intros H m a n H0 H1 P. pose proof (r1g_stk H m a (a + Z.of_nat n) H0 H1 P) as S.
  destruct (FRM.stk_bytes rsegs m a (a + Z.of_nat n) S ltac:(lia)) as (xs & Hl & Hb).
  exists xs. split; [split|].
  - cbn [CEL.cells_wf CEL.cell_wf]. split; [lia | exact I].
  - cbn [CEL.cells_bytes CEL.cbytes]. rewrite app_nil_r. exact Hb.
  - destruct S as (_ & _ & S). split; [exact H0|].
    change (Z.of_nat (CEL.cells_size [CEL.CB n xs])) with (Z.of_nat (n + 0)). rewrite Nat.add_0_r.
    split; [exact H1|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Lemma r1g_store1 : forall H (m : word -> option byte) a, Reusable.YG0n.apresent H m a ->
  store_ok rsegs m (MEM.wa a) 1 = true.
Proof.
  intros H m a (_ & b & E). cbn [store_ok]. unfold MEM.wa. unfold wview. rewrite E. reflexivity.
Qed.

Lemma r1g_rd1 : forall (m : word -> option byte) a b, MEM.bytes_at rsegs m a [b] ->
  ov_read_bytes rsegs m (MEM.wa a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (MEM.bytes_at_read rsegs m a [b] 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Lemma r1g_rd_at : forall (m : word -> option byte) a bs i b, MEM.bytes_at rsegs m a bs -> 0 <= i ->
  nth_error bs (Z.to_nat i) = Some b -> ov_read_bytes rsegs m (MEM.wa (a + i)) 1 = Some [b].
Proof.
  intros m a bs i b H Hi E.
  assert (L : (Z.to_nat i < length bs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (MEM.bytes_at_read rsegs m a bs i 1 H Hi ltac:(lia)).
  rewrite <- (MEM.firstn_skipn_step bs (Z.to_nat i) 0 b E). reflexivity.
Qed.

Lemma r1g_ro_rd : forall (m : word -> option byte) a b, STP.ro_cells rsegs m a [CEL.C1 b] ->
  MEM.bytes_at rsegs m a [b].
Proof. intros m a b [_ H]. exact H. Qed.

(* The bytes at a, a byte of them overwritten at a + t, the rest kept: ctrl's r1_our_keep (Seg/R1.v:834). *)
Lemma r1g_our_keep : forall (m m' : word -> option byte) ou t (pre junk : list byte) (v : byte),
  MEM.bytes_at rsegs m ou (pre ++ junk) -> length pre = Z.to_nat t -> 0 <= t -> (1 <= length junk)%nat ->
  FRM.munch [(ou + t, ou + t + 1)] m m' -> MEM.bytes_at rsegs m' (ou + t) [v] ->
  MEM.bytes_at rsegs m' ou ((pre ++ [v]) ++ tl junk).
Proof.
  intros m m' ou t pre junk v H Hp Ht Hj MU HV.
  pose proof H as Hb. apply MEM.bytes_at_bound in Hb. rewrite length_app in Hb.
  apply MEM.bytes_at_app in H. destruct H as (H1 & H2).
  rewrite Hp, Z2Nat.id in H2 by lia.
  destruct junk as [|b0 junk']; [cbn in Hj; lia|].
  change (b0 :: junk') with ([b0] ++ junk') in H2.
  apply MEM.bytes_at_app in H2. destruct H2 as (H2a & H2b). cbn [length Z.of_nat] in H2b.
  apply MEM.bytes_at_app. split.
  - apply MEM.bytes_at_app. split.
    + apply (FRM.bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' ou pre H1 MU).
      rewrite Hp, Z2Nat.id by lia. cbn [FRM.disjoint_from]. split; [left; lia | exact I].
    + rewrite Hp, Z2Nat.id by lia. exact HV.
  - rewrite length_app. cbn [length tl]. rewrite Hp.
    replace (ou + Z.of_nat (Z.to_nat t + 1)) with (ou + t + 1) by lia.
    apply (FRM.bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' (ou + t + 1) junk' H2b MU).
    cbn [FRM.disjoint_from]. split; [right; lia | exact I].
Qed.

Lemma r1g_our_step : forall inp (k : nat), (k < 6)%nat ->
  firstn (S k) (SM.OUR inp) = firstn k (SM.OUR inp) ++ [RIM.nthb inp k].
Proof.
  intros inp k Hk. unfold SM.OUR.
  do 6 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma r1g_nth_past : forall inp (k : nat), (length inp <= k)%nat -> RIM.nthb inp k = Z_to_bv 8 0.
Proof. intros inp k H. unfold RIM.nthb, RIM.zb. apply nth_overflow. exact H. Qed.

Lemma r1g_nth_in : forall inp (k : nat), (k < length inp)%nat -> nth_error inp k = Some (RIM.nthb inp k).
Proof. intros inp k H. unfold RIM.nthb. apply nth_error_nth'. exact H. Qed.

Lemma r1g_Z64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. rewrite <- (MSt.unsigned_lit a Ha), <- (MSt.unsigned_lit b Hb), E. reflexivity.
Qed.

(* =================================================================================================================
   2. The whole turn as ONE footprint run at RNG_W H, composed from the R1F twins (and R1Fs.r1_mode_evt_Fs on the
   w = 0 arm), with the premises stated over visible, present bytes. *)

(* lia on the arithmetic core of the context (ctrl's r1_lean, Seg/R1.v:1216): the run's case disjunctions and
   guarded implications would make every call case-split exponentially, so they are dropped first; a goal that needs
   one of them falls back to the full lia. *)
Ltac r1g_lean :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?P -> ?Q |- _ =>
             lazymatch Q with
             | False => fail
             | _ => lazymatch type of P with Prop => clear H end
             end
         end.
Local Ltac lia := first [ (r1g_lean; Lia.lia) | Lia.lia ].

Lemma r1g_rng : forall H (m : word -> option byte) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YG0n.apresent H m a) -> EF.rng (PB.RNG_W H) lo len.
Proof. intros H m lo len H0 H1 P. apply PB.rng_RNG_W; [exact H0 | exact H1 |]. intros a Ha. exact (proj1 (P a Ha)). Qed.

(* Route (C): a run carries every shadow_rw_on region of its start memory to its end memory. *)
Definition r1g_srw_tr (m m' : word -> option byte) : Prop :=
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.

(* A run that writes only application bytes keeps every shadow byte (ShadowRwOnT.shadow_rw_on_kept). *)
Lemma r1g_srw_app : forall W (m m' : word -> option byte), FRM.munch W m m' -> FRM.wmono rsegs m m' ->
  ARF.all_app W -> r1g_srw_tr m m'.
Proof.
  intros W m m' MU WM AW P H. exact (A.ShadowRwOnT.shadow_rw_on_kept P m m' H (ARF.munch_meta W m m' MU AW) WM).
Qed.

(* asan_cells, and every shadow_rw_on region, across a run that writes one application byte above the runtime cells. *)
Lemma r1g_kept1 : forall (m m' : word -> option byte) d, ART.asan_cells m ->
  FRM.munch [(d, d + 1)] m m' -> FRM.wmono rsegs m m' -> ART.app_mem d -> 0xa9578 <= d ->
  ART.asan_cells m' /\ r1g_srw_tr m m'.
Proof.
  intros m m' d HAC MU WM Hd Hd0. split.
  - apply (ARF.asan_cells_kept _ m m' HAC MU). unfold ART.RT_LO, ART.RT_HI.
    cbn [FRM.disjoint_from]. split; [lia | exact I].
  - apply (r1g_srw_app _ m m' MU WM). cbn [ARF.all_app]. split; [| exact I].
    intros a Ha. replace a with d by lia. exact Hd.
Qed.

(* Every byte one turn may write. *)
Definition r1g_zone (fr A spv x : Z) : Prop :=
  (fr + 2624 <= x < fr + 2630) \/ (A + 48 <= x < A + 64) \/ (A + 72 <= x < A + 96) \/ (A + 128 <= x < A + 136) \/
  x = ART.shadow_addr fr + 332 \/ (fr + 2656 <= x < fr + 2664) \/ (spv - 16 <= x < spv).

Definition r1g_W1 (fr t : Z) : list FRM.ivl := [(fr + 2624 + t, fr + 2624 + t + 1)].

Definition r1g_Wall (fr A spv : Z) : list FRM.ivl :=
  [(fr + 2629, fr + 2630); (A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136);
   (ART.shadow_addr fr + 332, ART.shadow_addr fr + 333); (fr + 2656, fr + 2664); (spv - 16, spv)].

Section TurnRun.
Context {fx : YK.FPState}.

(* The end of one turn: the back edge (0x81414, turn t + 1), P3 (0x81b14, after turn 5), or R2 (0x814f8, the
   odd-mode arm after the catalogue call).  Register facts are the run's own, written over the start words. *)
Definition r1g_post (m : word -> option byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (t fr A spv p n : Z) (inp : list byte) (ms : machine_state) : Prop :=
  exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
    ms = MSt.MS R YK.fp_regs pc' YK.fp_csr None m' (YK.seg_rom rsegs) /\
    ART.asan_cells m' /\ r1g_srw_tr m m' /\ FRM.wmono rsegs m m' /\
    ((pc' = Z_to_bv 64 0x81414 /\ t < 5 /\
      YK.getr R 1 = ra /\ YK.getr R 2 = sp /\ YK.getr R 3 = gp /\ YK.getr R 4 = tp /\ YK.getr R 7 = t2 /\
      YK.getr R 8 = s0 /\ YK.getr R 9 = s1 /\ YK.getr R 12 = a2 /\ YK.getr R 13 = a3 /\ YK.getr R 18 = s2 /\
      YK.getr R 19 = s3 /\ YK.getr R 21 = s5 /\ YK.getr R 26 = s10 /\ YK.getr R 27 = s11 /\
      YK.getr R 28 = t3 /\ YK.getr R 29 = t4 /\ YK.getr R 30 = t5 /\ YK.getr R 31 = t6 /\
      YK.getr R 10 = Z_to_bv 64 (fr + 2624 + (t + 1)) /\ YK.getr R 11 = Z_to_bv 64 (t + 1 + 1) /\
      YK.getr R 14 = Z_to_bv 64 (fr + 2624 + (t + 1)) /\
      YK.getr R 22 = Z_to_bv 64 (p + Z.min (t + 1) n) /\ YK.getr R 25 = Z_to_bv 64 (n - Z.min (t + 1) n) /\
      FRM.munch (r1g_W1 fr t) m m' /\
      (exists junk', length junk' = Z.to_nat (6 - (t + 1)) /\
         MEM.bytes_at rsegs m' (fr + 2624) (firstn (Z.to_nat (t + 1)) (SM.OUR inp) ++ junk')))
     \/ (pc' = Z_to_bv 64 0x81b14 /\ t = 5 /\
      YK.getr R 2 = sp /\ YK.getr R 3 = gp /\ YK.getr R 4 = tp /\ YK.getr R 8 = s0 /\ YK.getr R 9 = s1 /\
      YK.getr R 19 = s3 /\ YK.getr R 26 = s10 /\ YK.getr R 27 = s11 /\
      YK.getr R 22 = Z_to_bv 64 (p + Z.min n 7) /\ YK.getr R 25 = Z_to_bv 64 (n - Z.min n 7) /\
      FRM.munch (r1g_W1 fr t) m m' /\ MEM.bytes_at rsegs m' (fr + 2624) (SM.OUR inp))
     \/ (pc' = Z_to_bv 64 0x814f8 /\ t = 5 /\ 7 <= n /\
      YK.getr R 2 = sp /\ YK.getr R 3 = gp /\ YK.getr R 4 = tp /\ YK.getr R 8 = s0 /\ YK.getr R 9 = s1 /\
      YK.getr R 18 = s2 /\ YK.getr R 19 = s3 /\ YK.getr R 21 = s5 /\ YK.getr R 26 = s10 /\
      YK.getr R 10 = Z_to_bv 64 SM.CAT /\
      YK.getr R 22 = Z_to_bv 64 (p + 7) /\ YK.getr R 25 = Z_to_bv 64 (n - 7) /\
      YK.getr R 23 = Z_to_bv 64 (SM.mode inp) /\
      FRM.munch (r1g_Wall fr A spv) m m' /\ MEM.bytes_at rsegs m' (fr + 2624) (SM.OUR inp) /\
      MEM.bytes_at rsegs m' (fr + 2656) (MEM.le8 (Z_to_bv 64 SM.CAT_N)) /\
      MEM.bytes_at rsegs m' (A + 48) (MEM.le8 (Z_to_bv 64 (fr + 2256))) /\
      MEM.bytes_at rsegs m' (A + 56) (MEM.le8 (Z_to_bv 64 (fr + 2368))) /\
      MEM.bytes_at rsegs m' (A + 72) (MEM.le8 (Z_to_bv 64 (fr + 2496))) /\
      MEM.bytes_at rsegs m' (A + 80) (MEM.le8 (Z_to_bv 64 (fr + 2464))) /\
      MEM.bytes_at rsegs m' (A + 88) (MEM.le8 (Z_to_bv 64 (fr + 2448))) /\
      MEM.bytes_at rsegs m' (A + 128) (MEM.le8 (Z_to_bv 64 (fr + 544))))).

Lemma r1g_turn_run :
  forall (H : word -> bool) (m : word -> option byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (t fr A spv csp ceil p n : Z) (inp junk : list byte),
    ra = Z_to_bv 64 (fr + 2496) -> sp = Z_to_bv 64 spv -> t2 = Z_to_bv 64 (fr + 544) -> s1 = Z_to_bv 64 A ->
    a0 = Z_to_bv 64 (fr + 2624 + t) -> a1 = Z_to_bv 64 (t + 1) -> a2 = Z_to_bv 64 6 -> a3 = Z_to_bv 64 7 ->
    a4 = Z_to_bv 64 (fr + 2624 + t) -> s2 = Z_to_bv 64 (fr + 2656) -> s3 = Z_to_bv 64 (ART.shadow_addr fr) ->
    s6 = Z_to_bv 64 (p + Z.min t n) -> s9 = Z_to_bv 64 (n - Z.min t n) -> s10 = Z_to_bv 64 ART.ASAN_K ->
    t3 = Z_to_bv 64 (fr + 2256) -> t4 = Z_to_bv 64 (fr + 2368) -> t5 = Z_to_bv 64 (fr + 2448) ->
    t6 = Z_to_bv 64 (fr + 2464) ->
    0 <= t <= 5 -> fr mod 32 = 0 -> 6283264 <= fr -> 140735332483072 <= ceil <= 140737479966720 ->
    fr + 4096 <= ceil ->
    (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
    fr + 3136 <= A -> A + 416 <= csp -> csp - 4096 < spv -> spv <= A ->
    ceil + 32768 <= csp -> csp <= 2 ^ 47 ->
    n = Z.of_nat (length inp) ->
    (0 < n -> 4096 <= p /\ p + n <= ceil) ->
    (0 < n -> p + n <= fr \/ fr + 4096 <= p) ->
    PB.range_visible H A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO) ->
    (forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent H m a) ->
    (forall i, 0 <= i < 512 -> Reusable.YG0n.apresent H m (ART.shadow_addr fr + i)) ->
    (forall a, csp - 32768 <= a < csp -> Reusable.YG0n.apresent H m a) ->
    (0 < n -> forall a, p <= a < p + n -> Reusable.YG0n.apresent H m a) ->
    (0 < n -> forall a, p <= a < p + n -> H (Z_to_bv 64 (ART.shadow_addr a)) = false) ->
    MEM.bytes_at rsegs m p inp -> (0 < n -> ART.addressable m p n) ->
    MEM.bytes_at rsegs m (fr + 2624) (firstn (Z.to_nat t) (SM.OUR inp) ++ junk) ->
    length junk = Z.to_nat (6 - t) ->
    MEM.bytes_at rsegs m (ART.shadow_addr fr + 328) [Z_to_bv 8 6] ->
    MEM.bytes_at rsegs m (A + 168) (MEM.le8 (Z_to_bv 64 (fr + 2624))) ->
    ART.asan_cells m ->
    EF.evtF rsegs (PB.RNG_W H)
      (r1g_post m ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         t fr A spv p n inp)
      (MSt.MS (FRM.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         YK.fp_regs (Z_to_bv 64 0x81414) YK.fp_csr None m (YK.seg_rom rsegs)).
Proof.
  intros H m ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    t fr A spv csp ceil p n inp junk Hra Hsp Ht2 Hs1 Ha0 Ha1 Ha2 Ha3 Ha4 Hs2 Hs3 Hs6 Hs9 Hs10 Ht3 Ht4 Ht5 Ht6
    Ht Hfr32 Hfrlo Hceil Hfrceil Hfrloc HfrA HA416 Hsplo HspA Hcsplo Hcsphi Hnlen Hpb Hdj VIMG PF PS PW PB VB
    BIN AIN BOUR Hjl B328 B168 HAC.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  assert (EK : ART.ASAN_K = 2147450880) by reflexivity.
  assert (ESh : ART.shadow_addr fr = fr / 8 + 2147450880) by reflexivity.
  (* the frame's shadow lies apart from the frame, below the stack, and below HIGHMEM_BEG *)
  assert (NSh : 2147450880 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= A /\
                ART.shadow_addr fr + 512 <= spv - 16 /\
                (ART.shadow_addr fr + 512 <= fr \/ fr + 4096 <= ART.shadow_addr fr) /\
                ART.shadow_addr fr + 512 <= 0x10007fff8000).
  { rewrite ESh. clear - Hfrlo Hceil Hfrceil Hfrloc HfrA HA416 Hsplo HspA Hcsplo. Z.div_mod_to_equations. lia. }
  destruct NSh as (NSh1 & NSh2 & NSh3 & NSh4 & NSh5).
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hdm : (fr + 2624 + t) mod 8 = t) by (clear - Hfr32 Ht; Z.div_mod_to_equations; lia).
  assert (HdSh : (fr + 2624 + t) / 8 + ART.ASAN_K = ART.shadow_addr fr + 328)
    by (rewrite EK, ESh; clear - Hfr32 Ht; Z.div_mod_to_equations; lia).
  assert (Hc8 : ART.shadow_addr (fr + 2656) = ART.shadow_addr fr + 332)
    by (unfold ART.shadow_addr; clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Happ : forall a, fr <= a < fr + 4096 -> ART.app_mem a).
  { intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END.
    clear - Ha Hfrloc Hfrlo Hceil Hfrceil. Lia.lia. }
  assert (HappA : forall a, A + 48 <= a < A + 136 -> ART.app_mem a).
  { intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  assert (Happw : forall a, spv - 16 <= a < spv -> ART.app_mem a).
  { intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. right. lia. }
  (* our[t]: its byte, its shadow byte (S(fr) + 328 = 06) *)
  assert (Pd : Reusable.YG0n.apresent H m (fr + 2624 + t)) by (apply PF; lia).
  pose proof (r1g_store1 H m _ Pd) as STd.
  assert (RDd : ov_read_bytes rsegs m (MEM.wa ((fr + 2624 + t) / 8 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 6])
    by (rewrite HdSh; exact (r1g_rd1 m _ _ B328)).
  assert (Hkd6 : bv_signed (Z_to_bv 8 6) = 6) by reflexivity.
  assert (OKd : bv_signed (Z_to_bv 8 6) = 0 \/ t < bv_signed (Z_to_bv 8 6)) by (right; rewrite Hkd6; lia).
  assert (Rd : EF.rng (PB.RNG_W H) (fr + 2624 + t) 1) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PF; lia]).
  assert (Rsd : EF.rng (PB.RNG_W H) ((fr + 2624 + t) / 8 + ART.ASAN_K) 1).
  { rewrite HdSh. apply (r1g_rng H m); [lia | lia |]. intros a Ha.
    replace a with (ART.shadow_addr fr + 328) by lia. apply PS. lia. }
  destruct (Z_lt_ge_dec t n) as [Hlt | Hge].
  - (* ---- t < n: our[t] = in[t] (r1_ld_evt) ---- *)
    assert (Hn0 : 0 < n) by lia.
    destruct (Hpb Hn0) as (Hp0 & Hpe).
    assert (Hmin : Z.min t n = t) by lia.
    rewrite Hmin in Hs6, Hs9.
    destruct (ARF.meta_byte m (p + t) 1
                (ARF.addressable_sub m p n t 1 (AIN Hn0) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
      as (kq & ROq & OKq & INq).
    assert (Eq3 : Z.shiftr (p + t) 3 = (p + t) / 8) by (apply Z.shiftr_div_pow2; lia).
    rewrite Eq3 in ROq, INq.
    pose proof (r1g_rd1 m _ _ (r1g_ro_rd m _ _ ROq)) as RDq.
    assert (OKq' : bv_signed kq = 0 \/ (p + t) mod 8 < bv_signed kq) by (destruct OKq as [E|E]; [left; exact E | right; lia]).
    assert (RDb : ov_read_bytes rsegs m (MEM.wa (p + t)) 1 = Some [RIM.nthb inp (Z.to_nat t)]).
    { apply (r1g_rd_at m p inp t); [exact BIN | lia |]. apply r1g_nth_in. lia. }
    assert (Rq : EF.rng (PB.RNG_W H) (p + t) 1) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply (PB Hn0); lia]).
    assert (Rsq : EF.rng (PB.RNG_W H) ((p + t) / 8 + ART.ASAN_K) 1).
    { apply PB.rng_RNG_W; [clear - Hp0 Hpe EK Ht; Z.div_mod_to_equations; lia |
                           rewrite EK; change (2 ^ 64) with 18446744073709551616; clear - Hp0 Hpe Ht Hlt Hceil; Z.div_mod_to_equations; lia |].
      intros a Ha. replace a with (ART.shadow_addr (p + t)) by (unfold ART.shadow_addr; lia). apply (VB Hn0). lia. }
    assert (Rsp : EF.rng (PB.RNG_W H) (A + 168) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
    assert (Nq : (p + t) / 8 + ART.ASAN_K + 1 < 2 ^ 64) by (rewrite EK, P64; clear - Hp0 Hpe Ht Hlt Hceil; Z.div_mod_to_equations; lia).
    assert (Nd : (fr + 2624 + t) / 8 + ART.ASAN_K + 1 < 2 ^ 64) by (rewrite HdSh; lia).
    pose proof (RF1.r1_ld_evt_F (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                  s10 s11 t3 t4 t5 t6 YK.fp_regs YK.fp_csr m (fr + 2624) t ART.ASAN_K A (p + t) (n - t)
                  (RIM.nthb inp (Z.to_nat t)) kq (Z_to_bv 8 6)
                  Ha0 Ha1 Ha2 Ha4 Hs1 Hs6 Hs9 Hs10 Ht ltac:(lia) ltac:(lia)
                  ltac:(clear - Hfr32; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) Nq Nd ltac:(lia) ltac:(lia) ltac:(lia) RDq OKq' RDd OKd RDb B168 STd Rsq Rsd Rq Rsp Rd)
      as RUNld.
    destruct (Z.eq_dec t 5) as [E5 | N5].
    + (* ---- turn 5: the mode byte ---- *)
      eapply EF.evtF_cut; [exact RUNld|].
      intros ms1 (x5 & x6 & x7 & m1 & Ems & MU1 & WM1 & HB1).
      rewrite (proj2 (Z.eqb_eq t 5) E5) in Ems. cbv iota in Ems. subst ms1.
      destruct (r1g_kept1 m m1 (fr + 2624 + t) HAC MU1 WM1 ltac:(apply Happ; lia) ltac:(lia)) as (HAC1 & HSW1).
      assert (P1 : forall a, Reusable.YG0n.apresent H m a -> 0 <= a < 2 ^ 64 -> ~ (fr + 2624 + t <= a < fr + 2624 + t + 1) ->
                     Reusable.YG0n.apresent H m1 a).
      { intros a Pa Ha Hn. apply (r1g_present_munch H _ m m1 a Pa MU1); [cbn [FRM.outside]; split; [exact Hn | exact I] | exact Ha]. }
      assert (HOUR1 : MEM.bytes_at rsegs m1 (fr + 2624) (SM.OUR inp)).
      { pose proof (r1g_our_keep m m1 (fr + 2624) t _ junk (RIM.nthb inp (Z.to_nat t)) BOUR
                      ltac:(rewrite length_firstn, SM.OUR_length; lia) ltac:(lia) ltac:(lia) MU1 HB1) as HH.
        replace (tl junk) with (@nil byte) in HH
          by (destruct junk as [|b0 [|b1 r']]; cbn [length] in Hjl; try lia; reflexivity).
        rewrite app_nil_r in HH. rewrite <- r1g_our_step in HH by lia.
        rewrite firstn_all2 in HH by (rewrite SM.OUR_length; lia). exact HH. }
      destruct (Z.eq_dec n 6) as [En6 | Nn6].
      * (* n = 6 (w = 0): the left = 0 arm to P3, through the narrowed twin R1Fs.r1_mode_evt_Fs (its footprint
           premises are guarded by w <> 0; here w = 0, so every guarded premise is vacuous) *)
        eapply EF.evtF_cut.
        { exact (RF1s.r1_mode_evt_Fs (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 2624 + t))
                   (Z_to_bv 64 (t + 1)) a2 a3 (Z_to_bv 64 (fr + 2624)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (p + t))
                   (Z_to_bv 64 (p + t + 1)) (Z_to_bv 64 (n - t - 1)) (Z_to_bv 64 (n - t)) s10 s11 t3 t4 t5 t6
                   YK.fp_regs YK.fp_csr m1 (p + 6) (n - 6) ART.ASAN_K (Z_to_bv 8 0) (Z_to_bv 8 0)
                   ltac:(f_equal; lia) ltac:(f_equal; lia) ltac:(f_equal; lia) ltac:(f_equal; lia) Hs10
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(rewrite EK, P64; clear - Hp0 Hpe En6 Hceil; Z.div_mod_to_equations; lia)
                   (fun Hw => False_ind _ (Hw ltac:(lia))) (fun Hw => False_ind _ (Hw ltac:(lia)))
                   (fun Hw => False_ind _ (Hw ltac:(lia))) (fun Hw => False_ind _ (Hw ltac:(lia)))
                   (fun Hw => False_ind _ (Hw ltac:(lia)))). }
        intros ms2 [ (R & E2 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25) | (_ & Hw & _) ];
          [| exfalso; lia].
        subst ms2. apply EF.evtF_done.
        rewrite (proj2 (Z.eqb_eq (n - 6) 0) ltac:(lia)) in K22, K25.
        unfold r1g_post. exists R, (Z_to_bv 64 0x81b14), m1. split; [reflexivity|].
        split; [exact HAC1|]. split; [exact HSW1|]. split; [exact WM1|].
        right; left.
        split; [reflexivity|]. split; [exact E5|].
        split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
        split; [exact K19|]. split; [exact K26|]. split; [exact K27|].
        split; [etransitivity; [exact K22 | f_equal; lia]|].
        split; [etransitivity; [exact K25 | f_equal; lia]|].
        split; [exact MU1 | exact HOUR1].
      * (* n >= 7: the mode byte in[6] decides *)
        assert (Hn7 : 7 <= n) by lia.
        destruct (ARF.meta_byte m (p + 6) 1
                    (ARF.addressable_sub m p n 6 1 (AIN Hn0) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
          as (km & ROm & OKm & INm).
        assert (Em3 : Z.shiftr (p + 6) 3 = (p + 6) / 8) by (apply Z.shiftr_div_pow2; lia).
        rewrite Em3 in ROm, INm.
        assert (Bkm1 : MEM.bytes_at rsegs m1 ((p + 6) / 8 + ART.ASAN_K) [km]).
        { apply (FRM.bytes_at_transport rsegs _ m m1 _ _ (r1g_ro_rd m _ _ ROm) MU1).
          cbn [FRM.disjoint_from length Z.of_nat Pos.of_succ_nat]. split; [| exact I].
          rewrite EK. clear - Hp0 Hpe Hfrlo Hceil Hfrceil Hfrloc Ht Hn7. Z.div_mod_to_equations. lia. }
        assert (BIN1 : MEM.bytes_at rsegs m1 p inp).
        { apply (FRM.bytes_at_transport rsegs _ m m1 _ _ BIN MU1).
          cbn [FRM.disjoint_from]. split; [| exact I]. destruct (Hdj Hn0); lia. }
        assert (RDm1 : ov_read_bytes rsegs m1 (MEM.wa (p + 6)) 1 = Some [RIM.nthb inp 6]).
        { apply (r1g_rd_at m1 p inp 6 _ BIN1 ltac:(lia)). apply r1g_nth_in. lia. }
        assert (OKm' : bv_signed km = 0 \/ (p + 6) mod 8 < bv_signed km) by (destruct OKm as [E|E]; [left; exact E | right; lia]).
        assert (Rsm : EF.rng (PB.RNG_W H) ((p + 6) / 8 + ART.ASAN_K) 1).
        { apply PB.rng_RNG_W; [clear - Hp0 Hpe EK; Z.div_mod_to_equations; lia |
                               rewrite EK; change (2 ^ 64) with 18446744073709551616; clear - Hp0 Hpe Hn7 Hceil; Z.div_mod_to_equations; lia |].
          intros a Ha. replace a with (ART.shadow_addr (p + 6)) by (unfold ART.shadow_addr; lia). apply (VB Hn0). lia. }
        assert (Rm : EF.rng (PB.RNG_W H) (p + 6) 1) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply (PB Hn0); lia]).
        eapply EF.evtF_cut.
        { exact (RF1.r1_mode_evt_F (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 2624 + t))
                   (Z_to_bv 64 (t + 1)) a2 a3 (Z_to_bv 64 (fr + 2624)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (p + t))
                   (Z_to_bv 64 (p + t + 1)) (Z_to_bv 64 (n - t - 1)) (Z_to_bv 64 (n - t)) s10 s11 t3 t4 t5 t6
                   YK.fp_regs YK.fp_csr m1 (p + 6) (n - 6) ART.ASAN_K (RIM.nthb inp 6) km
                   ltac:(f_equal; lia) ltac:(f_equal; lia) ltac:(f_equal; lia) ltac:(f_equal; lia) Hs10
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(rewrite EK, P64; clear - Hp0 Hpe Hn7 Hceil; Z.div_mod_to_equations; lia)
                   (fun _ => r1g_rd1 m1 _ _ Bkm1) (fun _ => OKm') (fun _ => RDm1) Rsm Rm). }
        intros ms2 [ (R & E2 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25)
                   | (Hodd & Hw & x0 & x1 & E2) ].
        -- (* even mode: P3 *)
           subst ms2. apply EF.evtF_done.
           unfold r1g_post. exists R, (Z_to_bv 64 0x81b14), m1. split; [reflexivity|].
           split; [exact HAC1|]. split; [exact HSW1|]. split; [exact WM1|].
           right; left.
           rewrite (proj2 (Z.eqb_neq (n - 6) 0) ltac:(lia)) in K22, K25.
           split; [reflexivity|]. split; [exact E5|].
           split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
           split; [exact K19|]. split; [exact K26|]. split; [exact K27|].
           split; [etransitivity; [exact K22 | f_equal; lia]|].
           split; [etransitivity; [exact K25 | f_equal; lia]|].
           split; [exact MU1 | exact HOUR1].
        -- (* odd mode: the spills, the count cell's shadow byte, the count cell and the catalogue call *)
           subst ms2.
           assert (PW1 : forall a, csp - 32768 <= a < csp -> Reusable.YG0n.apresent H m1 a).
           { intros a Ha. apply P1; [apply PW; exact Ha | lia | lia]. }
           assert (PF1 : forall a, fr + 2656 <= a < fr + 2664 -> Reusable.YG0n.apresent H m1 a).
           { intros a Ha. apply P1; [apply PF; lia | lia | lia]. }
           assert (PS1 : Reusable.YG0n.apresent H m1 (ART.shadow_addr fr + 332)).
           { apply P1; [apply PS; lia | lia | lia]. }
           destruct (r1g_rwcb H m1 (A + 48) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x48 & CH48).
           destruct (r1g_rwcb H m1 (A + 56) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x56 & CH56).
           destruct (r1g_rwcb H m1 (A + 72) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x72 & CH72).
           destruct (r1g_rwcb H m1 (A + 80) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x80 & CH80).
           destruct (r1g_rwcb H m1 (A + 88) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x88 & CH88).
           destruct (r1g_rwcb H m1 (A + 128) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PW1; lia)) as (x128 & CH128).
           destruct (r1g_rwcb H m1 (fr + 2656) 8 ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply PF1; lia)) as (cs & CHc).
           destruct (r1g_rwcb H m1 (ART.shadow_addr fr + 332) 1 ltac:(lia) ltac:(lia)
                       ltac:(intros x Hx; replace x with (ART.shadow_addr fr + 332) by lia; exact PS1)) as (sh1 & CHsh).
           assert (STA : FRM.stk rsegs m1 (A + 48) (A + 136)) by (apply (r1g_stk H); [lia | lia | intros a Ha; apply PW1; lia]).
           assert (STw : FRM.stk rsegs m1 (spv - 16) spv) by (apply (r1g_stk H); [lia | lia | intros a Ha; apply PW1; lia]).
           assert (R48 : EF.rng (PB.RNG_W H) (A + 48) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (R56 : EF.rng (PB.RNG_W H) (A + 56) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (R72 : EF.rng (PB.RNG_W H) (A + 72) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (R80 : EF.rng (PB.RNG_W H) (A + 80) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (R88 : EF.rng (PB.RNG_W H) (A + 88) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (R128 : EF.rng (PB.RNG_W H) (A + 128) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (Rsh : EF.rng (PB.RNG_W H) (ART.shadow_addr fr + 332) 1).
           { apply (r1g_rng H m); [lia | lia |]. intros a Ha. replace a with (ART.shadow_addr fr + 332) by lia. apply PS. lia. }
           assert (Rc : EF.rng (PB.RNG_W H) (fr + 2656) 8) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PF; lia]).
           assert (Rwin : EF.rng (PB.RNG_W H) (spv - 16) 16) by (apply (r1g_rng H m); [lia | lia | intros a Ha; apply PW; lia]).
           assert (Rgot : EF.rng (PB.RNG_W H) ART.GOT_CELL_K 8).
           { apply PB.rng_of_visible. apply (PB.range_visible_sub _ _ _ _ _ VIMG);
               unfold ART.GOT_CELL_K, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
           assert (Rcell : EF.rng (PB.RNG_W H) ART.CELL_K 8).
           { apply PB.rng_of_visible. apply (PB.range_visible_sub _ _ _ _ _ VIMG);
               unfold ART.CELL_K, A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
           eapply EF.evtF_cut.
           { exact (RF1.r1_spill_evt_F_on (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 (Z_to_bv 64 (fr + 2624))
                      x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (p + 6 + 1)) (MEM.zxb (RIM.nthb inp 6)) (Z_to_bv 64 (n - 6))
                      (Z_to_bv 64 (n - 6 - 1)) s10 s11 t3 t4 t5 t6 YK.fp_regs YK.fp_csr m1
                      A fr (ART.shadow_addr fr) spv x48 x56 x72 x80 x88 x128 sh1 cs
                      Hs1 Hra Ht2 Ht3 Ht4 Ht5 Ht6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      HappA CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA STw HAC1 R48 R56 R72 R80 R88 R128). }
           intros ms3 (m2 & E3 & MUs & WMs & ACs & SWs & STAs & STs & CHsh2 & CHc2 & H48s & H128s &
                       H56s & H72s & H80s & H88s).
           subst ms3.
           eapply EF.evtF_cut.
           { exact (RF1.r1_shadow_evt_F_on (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 (Z_to_bv 64 (fr + 2624))
                      x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (p + 6 + 1)) (MEM.zxb (RIM.nthb inp 6)) (Z_to_bv 64 (n - 6))
                      (Z_to_bv 64 (n - 6 - 1)) s10 s11 t3 t4 t5 t6 YK.fp_regs YK.fp_csr m2
                      A fr (ART.shadow_addr fr) spv sh1 cs
                      Hs3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear - NSh4; Lia.lia)
                      HappA Happw CHsh2 CHc2 STAs STs ACs H48s H128s Rsh). }
           intros ms4 (m3 & E4 & MUh & WMh & ACh & SWh & STAh & STh & CHc3 & HSHh & H48h & H128h).
           subst ms4.
           eapply EF.evtF_mono.
           { exact (RF1.r1_call_evt_F_on RBF.reac_box_catalogue_F_holds_on (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3
                      (Z_to_bv 64 (fr + 2624)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (p + 6 + 1)) (MEM.zxb (RIM.nthb inp 6))
                      (Z_to_bv 64 (n - 6)) (Z_to_bv 64 (n - 6 - 1)) s10 s11 t3 t4 t5 t6 YK.fp_regs YK.fp_csr m3
                      A fr (ART.shadow_addr fr) spv cs
                      Hsp Hs2 Hfrlo ltac:(lia) Hfr8 HfrA HspA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(clear - NSh4; Lia.lia) Hc8
                      ltac:(intros a Ha; apply Happ; lia) Happw HappA CHc3 HSHh STAh STh ACh H48h H128h
                      Rc Rwin Rgot Rcell Rsh). }
           intros ms5 (R & m4 & E6 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K25 & K26 & K10 &
                       MUc & WMc & SWc & STAc & STc & HZc & HZ48 & HZ128).
           subst ms5.
           assert (ACc : ART.asan_cells m4).
           { apply (ARF.asan_cells_kept _ m3 m4 ACh MUc). unfold ART.RT_LO, ART.RT_HI.
             cbn [FRM.disjoint_from]. split; [lia|]. split; [lia | exact I]. }
           assert (TR : forall a bs, MEM.bytes_at rsegs m2 a bs -> FRM.disjoint_from [(ART.shadow_addr fr + 332, ART.shadow_addr fr + 333)] a (Z.of_nat (length bs)) ->
                          FRM.disjoint_from [(fr + 2656, fr + 2664); (spv - 16, spv)] a (Z.of_nat (length bs)) ->
                          MEM.bytes_at rsegs m4 a bs).
           { intros a bs Hb D1 D2.
             exact (FRM.bytes_at_transport rsegs _ m3 m4 a bs (FRM.bytes_at_transport rsegs _ m2 m3 a bs Hb MUh D1) MUc D2). }
           unfold r1g_post. exists R, (Z_to_bv 64 0x814f8), m4. split; [reflexivity|].
           split; [exact ACc|].
           split.
           { (* every region across the four writes: our[5] (r1g_kept1), then the three runs' own transports *)
             intros P HP. exact (SWc P (SWh P (SWs P (HSW1 P HP)))). }
           split; [exact (FRM.wmono_trans rsegs _ _ _ WM1 (FRM.wmono_trans rsegs _ _ _ WMs (FRM.wmono_trans rsegs _ _ _ WMh WMc)))|].
           right; right.
           split; [reflexivity|]. split; [exact E5|]. split; [exact Hn7|].
           split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
           split; [exact K18|]. split; [exact K19|]. split; [exact K21|]. split; [exact K26|].
           split; [exact K10|].
           split; [etransitivity; [exact K22 | f_equal; lia]|].
           split; [etransitivity; [exact K25 | f_equal; lia]|].
           split.
           { etransitivity; [exact K23|]. unfold SM.mode, SM.inb, SM.nlen.
             rewrite <- Hnlen. replace (7 <=? n) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
           split.
           { intros x Hx. unfold r1g_Wall in Hx. cbn [FRM.outside] in Hx.
             destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
             rewrite (MUc x) by (cbn [FRM.outside]; repeat split; try exact I; lia).
             rewrite (MUh x) by (cbn [FRM.outside]; repeat split; try exact I; lia).
             rewrite (MUs x) by (cbn [FRM.outside]; repeat split; try exact I; lia).
             rewrite (MU1 x) by (cbn [FRM.outside]; repeat split; try exact I; lia).
             reflexivity. }
           split.
           { apply TR; [| cbn [FRM.disjoint_from]; rewrite SM.OUR_length; split; [clear - NSh4; Lia.lia | exact I]
                        | cbn [FRM.disjoint_from]; rewrite SM.OUR_length; repeat split; try exact I; lia].
             apply (FRM.bytes_at_transport rsegs _ m1 m2 _ _ HOUR1 MUs).
             cbn [FRM.disjoint_from]. rewrite SM.OUR_length. repeat split; try exact I; lia. }
           split; [exact HZc|].
           split; [exact HZ48|].
           split; [apply TR; [exact H56s | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; split; [lia | exact I] | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; repeat split; try exact I; lia]|].
           split; [apply TR; [exact H72s | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; split; [lia | exact I] | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; repeat split; try exact I; lia]|].
           split; [apply TR; [exact H80s | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; split; [lia | exact I] | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; repeat split; try exact I; lia]|].
           split; [apply TR; [exact H88s | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; split; [lia | exact I] | cbn [FRM.disjoint_from]; rewrite MEM.length_le8; repeat split; try exact I; lia]|].
           exact HZ128.
    + (* ---- t < 5: the back edge to turn t + 1 ---- *)
      eapply EF.evtF_mono; [exact RUNld|].
      intros ms' (x5 & x6 & x7 & m' & Ems & MU & WM & HB).
      rewrite (proj2 (Z.eqb_neq t 5) N5) in Ems. cbv iota in Ems. subst ms'.
      destruct (r1g_kept1 m m' (fr + 2624 + t) HAC MU WM ltac:(apply Happ; lia) ltac:(lia)) as (HAC' & HSW').
      unfold r1g_post. eexists; exists (Z_to_bv 64 0x81414), m'. split; [reflexivity|].
      split; [exact HAC'|]. split; [exact HSW'|]. split; [exact WM|].
      left.
      split; [reflexivity|]. split; [lia|].
      do 18 (split; [reflexivity|]).
      split; [transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 (t + 2)); [reflexivity | f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 (p + t + 1)); [reflexivity | f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 (n - t - 1)); [reflexivity | f_equal; lia]|].
      split; [exact MU|].
      exists (tl junk). split; [destruct junk as [|b0 junk']; cbn [length tl] in *; lia|].
      pose proof (r1g_our_keep m m' (fr + 2624) t _ junk (RIM.nthb inp (Z.to_nat t)) BOUR
                    ltac:(rewrite length_firstn, SM.OUR_length; lia) ltac:(lia) ltac:(lia) MU HB) as HH.
      rewrite <- r1g_our_step in HH by lia.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia. exact HH.
  - (* ---- t >= n: our[t] = 0 (r1_z_evt) ---- *)
    assert (Hmin : Z.min t n = n) by lia.
    rewrite Hmin in Hs6, Hs9. rewrite Z.sub_diag in Hs9.
    assert (Hv0 : RIM.nthb inp (Z.to_nat t) = Z_to_bv 8 0) by (apply r1g_nth_past; lia).
    assert (Nd : (fr + 2624 + t) / 8 + ART.ASAN_K + 1 < 2 ^ 64) by (rewrite HdSh; lia).
    pose proof (RF1.r1_z_evt_F (PB.RNG_W H) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                  s10 s11 t3 t4 t5 t6 YK.fp_regs YK.fp_csr m (fr + 2624 + t) ART.ASAN_K (t + 1) t (Z_to_bv 8 6)
                  Ha0 Ha1 Ha3 Ha4 Hs9 Hs10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Nd ltac:(lia) Hdm
                  RDd OKd STd Rsd Rd) as RUNz.
    eapply EF.evtF_mono; [exact RUNz|].
    intros ms' (y5 & y6 & m' & Ems & MU & WM & HB). subst ms'.
    destruct (r1g_kept1 m m' (fr + 2624 + t) HAC MU WM ltac:(apply Happ; lia) ltac:(lia)) as (HAC' & HSW').
    pose proof (r1g_our_keep m m' (fr + 2624) t _ junk (Z_to_bv 8 0) BOUR
                  ltac:(rewrite length_firstn, SM.OUR_length; lia) ltac:(lia) ltac:(lia) MU HB) as HH.
    rewrite <- Hv0 in HH. rewrite <- r1g_our_step in HH by lia.
    destruct (Z.eq_dec t 5) as [E5 | N5].
    + (* turn 5, left = 0: the 0x81440 arm to P3 *)
      rewrite (proj2 (Z.eqb_eq (t + 1) 6) ltac:(lia)).
      unfold r1g_post. eexists; exists (Z_to_bv 64 0x81b14), m'. split; [reflexivity|].
      split; [exact HAC'|]. split; [exact HSW'|]. split; [exact WM|].
      right; left.
      split; [reflexivity|]. split; [exact E5|].
      do 8 (split; [reflexivity|]).
      split; [transitivity s6; [reflexivity | rewrite Hs6; f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 0); [reflexivity | f_equal; lia]|].
      split; [exact MU|].
      replace (tl junk) with (@nil byte) in HH
        by (destruct junk as [|b0 [|b1 r']]; cbn [length] in Hjl; try lia; reflexivity).
      rewrite app_nil_r in HH. rewrite firstn_all2 in HH by (rewrite SM.OUR_length; lia). exact HH.
    + (* back edge to turn t + 1 *)
      rewrite (proj2 (Z.eqb_neq (t + 1) 6) ltac:(lia)).
      unfold r1g_post. eexists; exists (Z_to_bv 64 0x81414), m'. split; [reflexivity|].
      split; [exact HAC'|]. split; [exact HSW'|]. split; [exact WM|].
      left.
      split; [reflexivity|]. split; [lia|].
      do 18 (split; [reflexivity|]).
      split; [transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia]|].
      split; [reflexivity|].
      split; [transitivity (Z_to_bv 64 (fr + 2624 + t + 1)); [reflexivity | f_equal; lia]|].
      split; [transitivity s6; [reflexivity | rewrite Hs6; f_equal; lia]|].
      split; [transitivity (Z_to_bv 64 0); [reflexivity | f_equal; lia]|].
      split; [exact MU|].
      exists (tl junk). split; [destruct junk as [|b0 junk']; cbn [length tl] in *; lia|].
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia. exact HH.
Qed.

End TurnRun.

(* =================================================================================================================
   3. Moving the cut body's memory facts across the turn's writes.  Every byte one turn writes lies in r1g_zone; a
   fact whose bytes avoid the zone is kept. *)

Lemma r1g_notout : forall lo hi (W : list FRM.ivl) y, ~ FRM.outside ((lo, hi) :: W) y -> (lo <= y < hi) \/ ~ FRM.outside W y.
Proof.
  intros lo hi W y H. destruct (r1g_out_dec W y) as [Ho|Hno]; [left|right; exact Hno].
  destruct (Z_lt_le_dec y lo) as [L|L]; [exfalso; apply H; cbn [FRM.outside]; split; [lia | exact Ho]|].
  destruct (Z_lt_le_dec y hi) as [L2|L2]; [lia | exfalso; apply H; cbn [FRM.outside]; split; [lia | exact Ho]].
Qed.

Lemma r1g_W1_zone : forall fr A spv t y, 0 <= t <= 5 -> ~ FRM.outside (r1g_W1 fr t) y -> r1g_zone fr A spv y.
Proof.
  intros fr A spv t y Ht H. unfold r1g_W1 in H. apply r1g_notout in H. destruct H as [H|H]; [left; lia|].
  exfalso. apply H. exact I.
Qed.

Lemma r1g_Wall_zone : forall fr A spv y, ~ FRM.outside (r1g_Wall fr A spv) y -> r1g_zone fr A spv y.
Proof.
  intros fr A spv y H. unfold r1g_Wall in H. unfold r1g_zone.
  apply r1g_notout in H; destruct H as [H|H]; [left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; right; left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; right; right; left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; right; right; right; left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; right; right; right; right; left; lia|].
  apply r1g_notout in H; destruct H as [H|H]; [right; right; right; right; right; right; lia|].
  exfalso. apply H. exact I.
Qed.

Lemma r1g_bat_zone : forall (zone : Z -> Prop) Wl (m m' : word -> option byte) a bs,
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' -> MEM.bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ zone x) -> MEM.bytes_at rsegs m' a bs.
Proof.
  intros zone Wl m m' a bs HZ MU (H0 & H1 & Hb) Hx. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi). unfold MEM.mrd, MEM.wa.
  rewrite (MU (Z_to_bv 64 (a + Z.of_nat i))); [reflexivity|].
  rewrite MSt.unsigned_lit by lia.
  destruct (r1g_out_dec Wl (a + Z.of_nat i)) as [Ho|Hno]; [exact Ho|].
  exfalso. exact (Hx (a + Z.of_nat i) ltac:(lia) (HZ _ Hno)).
Qed.

Lemma r1g_rwc_zone : forall (zone : Z -> Prop) Wl (m m' : word -> option byte) a cs,
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' -> FRM.wmono rsegs m m' ->
  STP.rw_cells rsegs m a cs ->
  (forall x, a <= x < a + Z.of_nat (CEL.cells_size cs) -> ~ zone x) -> STP.rw_cells rsegs m' a cs.
Proof.
  intros zone Wl m m' a cs HZ MU WM [[Hwf Hb] Hw] Hx.
  split; [split; [exact Hwf|] | exact (FRM.wr_at_transport rsegs m m' a _ Hw WM)].
  apply (r1g_bat_zone zone Wl m m' a _ HZ MU Hb). rewrite (r1g_cbl cs Hwf). exact Hx.
Qed.

Lemma r1g_q64_zone : forall (zone : Z -> Prop) Wl (m m' : word -> option byte) a v,
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' -> ACtlCutP.q64 m a v ->
  (forall x, a <= x < a + 8 -> ~ zone x) -> ACtlCutP.q64 m' a v.
Proof.
  intros zone Wl m m' a v HZ MU Hq Hx. unfold ACtlCutP.q64 in *.
  apply (r1g_bat_zone zone Wl m m' a _ HZ MU Hq). rewrite MEM.length_le8. exact Hx.
Qed.

Lemma r1g_addr_zone : forall (zone : Z -> Prop) Wl (m m' : word -> option byte) p n,
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' -> ART.addressable m p n ->
  (forall i, 0 <= i < n -> ~ zone (ART.shadow_addr (p + i))) -> ART.addressable m' p n.
Proof.
  intros zone Wl m m' p n HZ MU (H0 & H1 & H2 & Ha) Hx. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (Ha i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  rewrite <- Hb. unfold MEM.mrd, MEM.wa.
  assert (Hs : 0 <= ART.shadow_addr (p + i) < 2 ^ 64).
  { unfold ART.shadow_addr, ART.ASAN_K. unfold ART.APPMEM_END in H2. change (2 ^ 64) with 18446744073709551616.
    clear - H0 H2 Hi. Z.div_mod_to_equations. Lia.lia. }
  rewrite (MU (Z_to_bv 64 (ART.shadow_addr (p + i)))); [reflexivity|].
  rewrite MSt.unsigned_lit by exact Hs.
  destruct (r1g_out_dec Wl (ART.shadow_addr (p + i))) as [Ho|Hno]; [exact Ho|].
  exfalso. exact (Hx i Hi (HZ _ Hno)).
Qed.

Lemma r1g_spill_zone : forall (zone : Z -> Prop) Wl (regs R : bvmap 5 word) (m m' : word -> option byte) A off v,
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' ->
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 4096 ->
  YK.getr R 9 = YK.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> ~ zone x) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v.
Proof.
  intros zone Wl regs R m m' A off v HZ MU HA HAr Hoff E9 Hx (A1 & HA1 & Hq).
  assert (EA : A1 = A).
  { unfold ACtlCut.rgv in HA, HA1. rewrite HA in HA1.
    pose proof (MEM.bytes_at_bound _ _ _ _ Hq) as Bq. rewrite MEM.length_le8 in Bq.
    assert (U : bv_unsigned (Z_to_bv 64 A) = bv_unsigned (Z_to_bv 64 A1)) by (rewrite HA1; reflexivity).
    rewrite !MSt.unsigned_lit_wrap in U. change (2 ^ 64) with 18446744073709551616 in *.
    change (2 ^ 47) with 140737488355328 in HAr.
    clear - U Bq HAr Hoff. Z.div_mod_to_equations. Lia.lia. }
  subst A1. exists A. split.
  - unfold ACtlCut.rgv in *. etransitivity; [exact E9 | exact HA].
  - exact (r1g_q64_zone zone Wl m m' _ _ HZ MU Hq Hx).
Qed.

(* The three exits keep only what the turn does not write: the geometry that separates the write zone from every
   body fact.  The frame lies above the image (A.ProgWorld_Fs.ctl_frame_above_img) and below the stack window; its
   shadow lies between. *)
Definition r1g_geo (ceil fr A spv csp : Z) : Prop :=
  140735332483072 <= ceil <= 140737479966720 /\ 6283264 <= fr /\ fr + 4096 <= ceil /\ fr mod 32 = 0 /\
  (fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) /\
  fr + 3136 <= A /\ A + 416 <= csp /\ csp - 4096 < spv /\ spv <= A /\ ceil + 32768 <= csp /\ csp <= 2 ^ 47.

Lemma r1g_nz_fr : forall ceil fr A spv csp x, r1g_geo ceil fr A spv csp -> fr <= x < fr + 4096 ->
  ~ (fr + 2624 <= x < fr + 2630) -> ~ (fr + 2656 <= x < fr + 2664) -> ~ r1g_zone fr A spv x.
Proof.
  intros ceil fr A spv csp x G Hx H1 H2 Z. unfold r1g_geo in G. unfold r1g_zone in Z.
  change (2 ^ 47) with 140737488355328 in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]; [lia | lia | lia | lia | | lia | lia].
  subst x. unfold ART.shadow_addr, ART.ASAN_K in Hx. clear - Hx G5. Z.div_mod_to_equations. Lia.lia.
Qed.

Lemma r1g_nz_stk : forall ceil fr A spv csp x, r1g_geo ceil fr A spv csp -> A <= x < csp ->
  ~ (A + 48 <= x < A + 64) -> ~ (A + 72 <= x < A + 96) -> ~ (A + 128 <= x < A + 136) -> ~ r1g_zone fr A spv x.
Proof.
  intros ceil fr A spv csp x G Hx H1 H2 H3 Z. unfold r1g_geo in G. unfold r1g_zone in Z.
  change (2 ^ 47) with 140737488355328 in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]; [lia | lia | lia | lia | | lia | lia].
  subst x. unfold ART.shadow_addr, ART.ASAN_K in Hx. clear - Hx G1 G3 G6 G7 G8 G9 G10. Z.div_mod_to_equations. Lia.lia.
Qed.

Lemma r1g_nz_sh : forall ceil fr A spv csp x, r1g_geo ceil fr A spv csp ->
  ART.shadow_addr fr <= x < ART.shadow_addr fr + 512 -> x <> ART.shadow_addr fr + 332 -> ~ r1g_zone fr A spv x.
Proof.
  intros ceil fr A spv csp x G Hx H1 Z. unfold r1g_geo in G. unfold r1g_zone in Z.
  change (2 ^ 47) with 140737488355328 in G. unfold ART.shadow_addr, ART.ASAN_K in Hx, H1, Z.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  clear - Hx H1 Z G1 G2 G3 G5 G6 G7 G8 G9 G10. Z.div_mod_to_equations. Lia.lia.
Qed.

(* A byte of the input block: below the ceiling, outside the frame, in one of the two application bands. *)
Lemma r1g_nz_blk : forall ceil fr A spv csp x, r1g_geo ceil fr A spv csp -> 0 <= x -> x < ceil ->
  (x < fr \/ fr + 4096 <= x) -> (x < 0x7fff7000 \/ 0x10007fff8000 <= x) -> ~ r1g_zone fr A spv x.
Proof.
  intros ceil fr A spv csp x G Hx0 Hx1 Hx2 Hx3 Z. unfold r1g_geo in G. unfold r1g_zone in Z.
  change (2 ^ 47) with 140737488355328 in G. unfold ART.shadow_addr, ART.ASAN_K in Z.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  clear - Hx0 Hx1 Hx2 Hx3 Z G1 G2 G3 G6 G7 G8 G9 G10. Z.div_mod_to_equations. Lia.lia.
Qed.

(* The shadow byte of an input byte y: in the shadow band, so apart from the frame, the stack and the spills,
   and not S(fr) + 332, whose granule is the frame's [fr + 2656, fr + 2664). *)
Lemma r1g_nz_bsh : forall ceil fr A spv csp y, r1g_geo ceil fr A spv csp -> 0 <= y -> y < ceil ->
  (y < fr \/ fr + 4096 <= y) -> ~ r1g_zone fr A spv (ART.shadow_addr y).
Proof.
  intros ceil fr A spv csp y G Hy0 Hy1 Hy2 Z. unfold r1g_geo in G. unfold r1g_zone in Z.
  change (2 ^ 47) with 140737488355328 in G. unfold ART.shadow_addr, ART.ASAN_K in Z.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  clear - Hy0 Hy1 Hy2 Z G1 G2 G3 G4 G5 G6 G7 G8 G9 G10. Z.div_mod_to_equations. Lia.lia.
Qed.

(* A hidden byte is no byte of the world's view (the image is never hidden, YA0n.w_Hoff). *)
Lemma r1g_vis_of_aview : forall {fx : YK.FPState} {rc : YM.RunCeil} (W : Reusable.YA0n.world segs)
    (mem : word -> option byte) a,
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a <> None -> Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros fx rc W mem a Hv. destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
  exfalso. apply Hv.
  unfold Reusable.YG0n.aview, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
  rewrite Hh. unfold YK.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite (Reusable.YA0n.w_Hoff W _ Hh).
  reflexivity.
Qed.

Section Moves.
Context {fx : YK.FPState} {rc : YM.RunCeil}.
Variable B : Reusable.YG0f.asyms.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* FRAC's spill base A is register 9's value (two 64-bit images of one register, the spill at A + 304 in range). *)
Lemma r1g_A_eq : forall (regs : bvmap 5 word) (m : word -> option byte) A A0 v,
  ACtlCut.rgv regs 9 A0 -> ACtlCut.rgv regs 9 A -> 0 <= A0 -> A0 < 140737488355328 ->
  ACtlCutP.q64 m (A + 304) v -> A = A0.
Proof.
  intros regs m A A0 v HA0 Hr9 H0 H1 Q304.
  unfold ACtlCut.rgv in HA0, Hr9. rewrite HA0 in Hr9.
  pose proof (MEM.bytes_at_bound _ _ _ _ Q304) as B304. rewrite MEM.length_le8 in B304.
  assert (U : bv_unsigned (Z_to_bv 64 A0) = bv_unsigned (Z_to_bv 64 A)) by (rewrite Hr9; reflexivity).
  rewrite !MSt.unsigned_lit_wrap in U. change (2 ^ 64) with 18446744073709551616 in *.
  clear - U B304 H0 H1. Z.div_mod_to_equations. Lia.lia.
Qed.

(* A range of the frame or of the stack above the spill base, off the turn's written cells, avoids the zone. *)
Ltac r1g_nz_any G :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx;
  first [ apply (r1g_nz_fr _ _ _ _ _ x G); lia | apply (r1g_nz_stk _ _ _ _ _ x G); lia ].

(* One conjunct of FRAC at m', from the destructed FRAC at m (see r1g_frac_mem). *)
Ltac r1g_frac_walk m m' Wl HZ MU G HSH fr :=
  first
    [ assumption
    | match goal with |- ACtlCutP.q64 m' ?a ?v =>
        match goal with Q : ACtlCutP.q64 m a v |- _ =>
          apply (r1g_q64_zone _ Wl m m' a v HZ MU Q); r1g_nz_any G
        end
      end
    | match goal with |- MEM.bytes_at _ m' ?a ?bs =>
        match goal with Q : MEM.bytes_at _ m a bs |- _ =>
          apply (r1g_bat_zone _ Wl m m' a bs HZ MU Q);
          try unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?MEM.length_le8; r1g_nz_any G
        end
      end
    | match goal with |- exists _, MEM.bytes_at _ m' _ _ /\ _ =>
        let FS := fresh "FS" in let Sk := fresh "Sk" in
        assert (FS : ACtlCutP.FRAME_SHADOW = 392) by reflexivity; rewrite FS;
        assert (Sk : FRM.stk rsegs m' (ART.shadow_addr fr) (ART.shadow_addr fr + 392))
          by (apply r1g_stk_some; [lia | change (2 ^ 64) with 18446744073709551616; lia |];
              let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
              replace a with (ART.shadow_addr fr + (a - ART.shadow_addr fr)) by lia; apply HSH; lia);
        let sh := fresh "sh" in let Hl := fresh "Hl" in let Hb := fresh "Hb" in
        destruct (FRM.stk_bytes rsegs m' _ _ Sk ltac:(lia)) as (sh & Hl & Hb);
        exists sh; split; [exact Hb | rewrite Hl; f_equal; lia]
      end ].

(* FRAC (ACtlCutP.v:982-997) RE-ESTABLISHED at the memory after the turn, same register map.  The step walks
   FRAC's conjuncts generically, so a conjunct appended to FRAC needs no edit when it is register-only or a q64 /
   bytes_at fact on the frame [fr, fr + 4096) or on the stack [A, c_sp) off the turn's written cells (e.g. a trailer
   word q64 m (fr + 4088) _): register and arithmetic conjuncts by assumption, each q64 / bytes_at by the zone
   transport (the turn writes only r1g_zone), the frame-shadow existential re-read from m' (S(fr) + 332 may be
   written). *)
Lemma r1g_frac_mem : forall ceil spv cx fr sel (regs : bvmap 5 word) (m m' : word -> option byte) Wl A0,
  r1g_geo ceil fr A0 spv (ACtlCut.c_sp cx) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A0 ->
  (forall y, ~ FRM.outside Wl y -> r1g_zone fr A0 spv y) -> FRM.munch Wl m m' ->
  (forall i, 0 <= i < 392 -> exists b, m' (Z_to_bv 64 (ART.shadow_addr fr + i)) = Some b) ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros ceil spv cx fr sel regs m m' Wl A0 G HF HA0 HZ MU HSH.
  pose proof G as G'. unfold r1g_geo in G'. change (2 ^ 47) with 140737488355328 in G'.
  destruct G' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (HA0lo : 0 <= A0) by lia.
  assert (HA0hi : A0 < 140737488355328) by lia.
  assert (Hsh0 : 0 <= ART.shadow_addr fr) by (unfold ART.shadow_addr, ART.ASAN_K; clear - G2; Z.div_mod_to_equations; Lia.lia).
  assert (Hsh1 : ART.shadow_addr fr + 392 <= 18446744073709551616)
    by (unfold ART.shadow_addr, ART.ASAN_K; clear - G3 G1; Z.div_mod_to_equations; Lia.lia).
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11.
  destruct HF as (A & sp & HF).
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (EA : A = A0).
  { match goal with
    | H9 : ACtlCut.rgv regs 9 A, Q : ACtlCutP.q64 m (A + 304) _ |- _ => exact (r1g_A_eq regs m A A0 _ HA0 H9 HA0lo HA0hi Q)
    end. }
  subst A0.
  unfold ACtlCutP.FRAC. exists A, sp.
  repeat match goal with |- _ /\ _ => split end.
  all: r1g_frac_walk m m' Wl HZ MU G HSH fr.
Qed.

(* PRO (ACtlCutP.v:468-478) across the writes and onto the end map (it reads register 9 only). *)
Lemma r1g_pro_move : forall cx fr (regs R : bvmap 5 word) (m m' : word -> option byte) (zone : Z -> Prop) Wl A0,
  ACtlCutP.PRO cx fr regs m -> ACtlCut.rgv regs 9 A0 -> 0 <= A0 < 2 ^ 47 ->
  (forall y, ~ FRM.outside Wl y -> zone y) -> FRM.munch Wl m m' ->
  YK.getr R 9 = YK.getr regs 9 ->
  (forall x, A0 + 32 <= x < A0 + 48 \/ A0 + 120 <= x < A0 + 128 \/ A0 + 136 <= x < A0 + 144 \/
             A0 + 160 <= x < A0 + 192 \/ A0 + 208 <= x < A0 + 216 \/ A0 + 248 <= x < A0 + 280 -> ~ zone x) ->
  (forall i, 0 <= i < 6 -> ~ zone (ART.shadow_addr (fr + 2624 + i))) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> ~ zone x) ->
  (forall i, 0 <= i < ACtlCut.c_n cx -> ~ zone (ART.shadow_addr (ACtlCut.c_p cx + i))) ->
  ACtlCut.c_n cx = Z.of_nat (length (ACtlCut.c_in cx)) ->
  ACtlCutP.PRO cx fr R m'.
Proof.
  intros cx fr regs R m m' zone Wl A0 HP HA0 HA0r HZ MU E9 HXs HXo HXb HXbs Hlen.
  destruct HP as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
    P272 & P32).
  assert (SP : forall off v, 0 <= off <= 4096 -> (forall x, A0 + off <= x < A0 + off + 8 -> ~ zone x) ->
                 ACtlCutP.spill regs m off v -> ACtlCutP.spill R m' off v)
    by (intros off v Ho Hx Hs; exact (r1g_spill_zone zone Wl regs R m m' A0 off v HZ MU HA0 HA0r Ho E9 Hx Hs)).
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P40]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P120]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P136]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P160]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P168]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P176]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P208]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P248]|].
  split; [exact (r1g_addr_zone zone Wl m m' _ _ HZ MU Pad HXo)|].
  split; [apply (r1g_bat_zone zone Wl m m' _ _ HZ MU Pin); rewrite <- Hlen; exact HXb|].
  split; [intros Hn0; exact (r1g_addr_zone zone Wl m m' _ _ HZ MU (Pg Hn0) HXbs)|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P184]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P256]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P264]|].
  split; [apply SP; [lia | intros x Hx; apply HXs; lia | exact P272]|].
  apply SP; [lia | intros x Hx; apply HXs; lia | exact P32].
Qed.

(* The journal across the turn (ajournal_exec, YCbq.v:636-643): every written byte is the cut's own class-6 frame,
   its shadow, or the stack window; the hidden bytes are SRr_fevt_hid's. *)
Lemma r1g_journal : forall (cx : ACtlCut.ctlcx) ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 mem' md' k
    (Wl : list FRM.ivl) fr,
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  FRM.munch Wl mem3 mem' -> FRM.wmono rsegs mem3 mem' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> mem' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) ->
  (forall a, ~ FRM.outside Wl a -> 0x5fe000 <= a /\
     ((fr <= a < fr + 4096) \/ (ART.shadow_addr fr <= a < ART.shadow_addr fr + 512) \/
      (ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx))) ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem' md' k.
Proof.
  intros cx ly3 S3 W3 mem3 md3 mem' md' k Wl fr HJ MU WM Hhid Hsbm Efr HW.
  eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun a => ~ FRM.outside Wl a).
  - exact HJ.
  - intros x Hx. unfold Reusable.YK04.mrestrict.
    destruct (r1g_out_dec Wl (bv_unsigned x)) as [Ho|Hno]; [rewrite (MU x Ho); reflexivity | contradiction].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (r1g_out_dec Wl (bv_unsigned x)) as [Ho|Hno]; [rewrite (MU x Ho); exact Hx|].
    destruct (mem3 x) as [b|] eqn:E; [| exfalso; exact (Hx eq_refl)].
    apply r1g_some_of_wview; [exact (proj1 (HW _ Hno)) |]. apply WM. exact (r1g_wview_of_some mem3 x b E).
  - exact Hhid.
  - exact Hsbm.
  - intros a Ha. destruct (HW a Ha) as (_ & [Hf | [Hs | Hw]]).
    + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. unfold ART.shadow_addr, ART.ASAN_K in Hs. lia.
    + left. unfold A.ACfn.LLVMF_STK. lia.
Qed.

(* ctl_rt_C across the turn (route (C)): the runtime cells from the run's post, the two regions (cut_shadow, img_shadow)
   carried by the run's transport at the same ly3 S3, ro_agree kept below IMG_HI. *)
Lemma r1g_ctlrt_C : forall ly S (mem3 mem' : word -> option byte) (Wl : list FRM.ivl),
  A.ACtlRtC.ctl_rt_C B ly S mem3 -> FRM.munch Wl mem3 mem' -> (forall a, ~ FRM.outside Wl a -> 0x5fe000 <= a) ->
  ART.asan_cells mem' -> r1g_srw_tr mem3 mem' -> A.ACtlRtC.ctl_rt_C B ly S mem'.
Proof.
  intros ly S mem3 mem' Wl (_ & HC & HI & RO) MU Hhi AC TR.
  split; [exact AC|]. split; [exact (TR _ HC)|]. split; [exact (TR _ HI)|].
  intros a Hro.
  assert (Hlo : bv_unsigned a < 0x5fe000).
  { unfold MEM.ro_addr in Hro. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
    destruct (A.BzBridge.find_segment_below rsegs 0x5fe000 (bv_unsigned a) 1 s r1g_tops E ltac:(lia)); lia. }
  destruct (r1g_out_dec Wl (bv_unsigned a)) as [Ho|Hno]; [| exfalso; pose proof (Hhi _ Hno); lia].
  pose proof (RO a Hro) as E. unfold MEM.mrd in E |- *. rewrite (MU a Ho). exact E.
Qed.

End Moves.

(* A spill read at the cut's own spill base (the existential base of `spill` is FRAC's A: both are 64-bit images of
   register 9 and the spill is in range). *)
Lemma r1g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) A off v,
  ACtlCut.rgv regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 4096 -> ACtlCutP.spill regs m off v ->
  ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v HA HAr Hoff (A1 & HA1 & Hq).
  assert (EA : A1 = A).
  { unfold ACtlCut.rgv in HA, HA1. rewrite HA in HA1.
    pose proof (MEM.bytes_at_bound _ _ _ _ Hq) as Bq. rewrite MEM.length_le8 in Bq.
    assert (U : bv_unsigned (Z_to_bv 64 A) = bv_unsigned (Z_to_bv 64 A1)) by (rewrite HA1; reflexivity).
    rewrite !MSt.unsigned_lit_wrap in U. change (2 ^ 64) with 18446744073709551616 in *.
    change (2 ^ 47) with 140737488355328 in HAr.
    clear - U Bq HAr Hoff. Z.div_mod_to_equations. Lia.lia. }
  subst A1. exact Hq.
Qed.

Lemma r1g_wr_some : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> exists b, m (Z_to_bv 64 x) = Some b) -> MEM.wr_at rsegs m a n.
Proof.
  intros m a n H0 H1 P. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (P (a + i) ltac:(lia)) as (b & E). unfold MEM.wa. exact (r1g_wview_of_some m _ b E).
Qed.

(* The write sets of the two run shapes: above the image, in the frame, its shadow, or the stack window. *)
Lemma r1g_W1_in : forall ceil fr A spv csp t a, r1g_geo ceil fr A spv csp -> 0 <= t <= 5 ->
  ~ FRM.outside (r1g_W1 fr t) a ->
  0x5fe000 <= a /\ ((fr <= a < fr + 4096) \/ (ART.shadow_addr fr <= a < ART.shadow_addr fr + 512) \/
                    (csp - 32768 <= a < csp)).
Proof.
  intros ceil fr A spv csp t a G Ht H. unfold r1g_W1 in H. apply r1g_notout in H.
  destruct H as [H|H]; [| exfalso; apply H; exact I].
  unfold r1g_geo in G. destruct G as (G1 & G2 & _). split; [lia | left; lia].
Qed.

Lemma r1g_Wall_in : forall ceil fr A spv csp a, r1g_geo ceil fr A spv csp ->
  ~ FRM.outside (r1g_Wall fr A spv) a ->
  0x5fe000 <= a /\ ((fr <= a < fr + 4096) \/ (ART.shadow_addr fr <= a < ART.shadow_addr fr + 512) \/
                    (csp - 32768 <= a < csp)).
Proof.
  intros ceil fr A spv csp a G H. pose proof (r1g_Wall_zone fr A spv a H) as Z. unfold r1g_zone in Z.
  unfold r1g_geo in G. change (2 ^ 47) with 140737488355328 in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (S0 : 2147450880 <= ART.shadow_addr fr) by (unfold ART.shadow_addr, ART.ASAN_K; clear - G2; Z.div_mod_to_equations; Lia.lia).
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]].
  - split; [lia | left; lia].
  - split; [lia | right; right; lia].
  - split; [lia | right; right; lia].
  - split; [lia | right; right; lia].
  - split; [lia | right; left; lia].
  - split; [lia | left; lia].
  - split; [lia | right; right; lia].
Qed.

(* Zone-freedom of a stack range, a frame range: the tactics the exits repeat. *)
Ltac r1g_nzs G :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; apply (r1g_nz_stk _ _ _ _ _ _ G); lia.
Ltac r1g_nzf G :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; try (cbn [CEL.cells_size CEL.csize] in Hx); apply (r1g_nz_fr _ _ _ _ _ _ G); lia.

(* =================================================================================================================
   4. The stage. *)
Section GlueR1Turn.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:261-262, :272-273, :296) and its definition of C_A81414_at (ACtl.v:374-377),
   verbatim; ACtl.v's C_A81414_at is a Definition with this body, so its seg_R1_turn is this statement up to delta. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81414 := (ACtlCutP.C_A81414 B).
Local Notation C_A814f8 := (ACtlCutP.C_A814f8 B).
Local Notation C_A81b14 := (ACtlCutP.C_A81b14 B).
Local Notation cut_pc := ACtlCut.cut_pc.
Local Notation cut_own := ACtlCut.cut_own.
Local Notation cut_kmax := ACtlCut.cut_kmax.
Local Notation cut_body := ACtlCut.cut_body.
Local Notation C_A81414_at t :=
  (ACtlCut.mkCtlCut (cut_pc C_A81414) (cut_own C_A81414) (cut_kmax C_A81414)
    (fun cx idx bl fr sel regs m =>
       (0 <= t <= 5 /\ ACtlCut.rgv regs 11 (t + 1)) /\ cut_body C_A81414 cx idx bl fr sel regs m)).

(* The core's AR laws (YCbq Section a0's hypothesis), as ACtl.v:210 states it. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_R1_turn : forall POST (t : Z),
  (t < 5 -> CF POST (C_A81414_at (t + 1))) -> CF POST C_A81b14 -> CF POST C_A814f8 -> CF POST (C_A81414_at t).
Proof.
  intros POST t HN HP3 HR2 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  (* ---- G1: the entry cut, C_A81414 at turn t (ACtlCutP.v:1173-1195) ---- *)
  destruct Hbody as [[Ht Hpin] Hb].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81414] in Hb.
  destruct Hb as (t' & HP & HFRAC & Hn26 & Ht' & R1 & R7 & R10 & R11 & R12 & R13 & R14 & R18 & R21 & R22 & R25 &
    R28 & R29 & R30 & R31 & S152 & HPRO & B328 & R27 & S144 & S192 & HIDB & HJNK & S280 & S240 & HJY & HSC &
    S200 & S216 & HOUR).
  assert (Et : t' = t).
  { unfold ACtlCut.rgv in R11, Hpin. rewrite R11 in Hpin.
    pose proof (r1g_Z64_inj (t' + 1) (t + 1) ltac:(lia) ltac:(lia) Hpin). lia. }
  subst t'. clear Hpin Ht'.
  pose proof HFRAC as (A & sp & Hr2 & Hsp16 & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA416 & HSsp & HSapp & _ & _ & _ & _ & _ & _ & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp.
  (* ---- G2: the journal's state, the frame, the stack window and the input block ---- *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & HASTK & _ & _).
  destruct HASTK as (_ & _ & HcL & HLs & _ & _ & _ & _ & _).
  unfold A.ACfn.LLVMF_STK in HSTK, HLs.
  pose proof (@YM.alloc_ceiling_value rc) as ((Hc0 & Hc1) & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; exact (or_introl eq_refl)).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Hfapp & Hfpres & Hfsh).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Hfceil & _).
  pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as Hfgt.
  rewrite <- Efr in Hfapp, Hfpres, Hfsh, Hfceil, Hfgt.
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite FB6 in Hfapp, Hfpres, Hfsh, Hfceil. change (4096 / 8) with 512 in Hfsh.
  assert (Hfrloc : fr + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= fr).
  { unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
    destruct Hfapp as (_ & [X | (X & _)]); [left | right]; lia. }
  assert (ESH : Reusable.YG0f.shadow_addr fr = ART.shadow_addr fr)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  rewrite ESH in Hfsh.
  pose proof HB as ((_ & _ & _ & _ & Hblk & Hlen & _) & _).
  assert (HBLK : 0 < ACtlCut.c_n cx ->
     4096 <= ACtlCut.c_p cx /\ ACtlCut.c_p cx + ACtlCut.c_n cx <= YM.alloc_ceiling /\
     (ACtlCut.c_p cx + ACtlCut.c_n cx <= 0x7fff7000 \/ 0x10007fff8000 <= ACtlCut.c_p cx) /\
     (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr \/ fr + 4096 <= ACtlCut.c_p cx) /\
     (forall a, ACtlCut.c_p cx <= a < ACtlCut.c_p cx + ACtlCut.c_n cx ->
        Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) /\
     (forall a, ACtlCut.c_p cx <= a < ACtlCut.c_p cx + ACtlCut.c_n cx ->
        Reusable.YA0n.w_H W3 (Z_to_bv 64 (ART.shadow_addr a)) = false)).
  { intros Hn0.
    assert (Hi : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { destruct Hblk as [(E0 & _) | (_ & Hi)]; [lia|]. exact (Permutation_in _ (Permutation_sym HP) Hi). }
    assert (Ereq : Reusable.YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
    { unfold Reusable.YG00.req_size. replace (ACtlCut.c_n cx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      reflexivity. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hi)
      as (_ & Hp4096 & Hpce & Hpapp & Hpres & _ & _).
    destruct (Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hi) as (_ & Hhull).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hi Hin)
      as Hsep.
    rewrite Ereq in Hpce, Hpapp, Hpres, Hhull, Hsep.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- Efr, FB6 in Hsep.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    split; [lia|]. split; [lia|].
    split; [destruct Hpapp as (_ & [X | (X & _)]); [left | right]; lia|].
    split; [exact Hsep|]. split; [intros a Ha; exact (proj1 (Hpres a Ha))|].
    intros a Ha. apply (r1g_vis_of_aview W3 mem3). apply Hhull.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K.
    clear - Ha Hn0. Z.div_mod_to_equations. Lia.lia. }
  destruct HOUR as (junk & Hjl & BOUR).
  pose proof HPRO as (_ & _ & _ & _ & P168 & _ & _ & _ & _ & BIN & AIN & _).
  assert (HAr : 0 <= A < 2 ^ 47) by lia.
  pose proof (r1g_spill_q64 regs3 mem3 A 168 _ Hr9 HAr ltac:(lia) P168) as B168.
  assert (GEO : r1g_geo YM.alloc_ceiling fr A sp (ACtlCut.c_sp cx)).
  { unfold r1g_geo. rewrite P47. split; [lia|]. split; [lia|]. split; [exact Hfceil|]. split; [exact Hfr32|].
    split; [exact Hfrloc|]. repeat split; lia. }
  assert (EO : forall i, 0 <= i < 6 -> ART.shadow_addr (fr + 2624 + i) = ART.shadow_addr fr + 328).
  { intros i Hi. unfold ART.shadow_addr. clear - Hi Hfr32. Z.div_mod_to_equations. Lia.lia. }
  assert (NSh : 2147450880 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= 0x10007fff8000).
  { unfold ART.shadow_addr, ART.ASAN_K. clear - Hfgt Hfceil Hc1. Z.div_mod_to_equations. Lia.lia. }
  (* ---- G3: the cut's configuration, moved to the run's canonical register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (C_A81414_at t)) with 0x81414.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (RG.mkR_of regs3) regs3 YK.fp_regs (Z_to_bv 64 0x81414) YK.fp_csr
           None mem3 (YK.seg_rom segs) md3 (POST cx));
    [| exact (RG.xregs_eqv_sym _ _ (RG.mkR_of_eqv regs3))].
  (* ---- G4: the turn as one footprint run, lifted once ---- *)
  pose proof (r1g_turn_run (Reusable.YA0n.w_H W3) mem3
    (YK.getr regs3 1) (YK.getr regs3 2) (YK.getr regs3 3) (YK.getr regs3 4) (YK.getr regs3 5) (YK.getr regs3 6)
    (YK.getr regs3 7) (YK.getr regs3 8) (YK.getr regs3 9) (YK.getr regs3 10) (YK.getr regs3 11) (YK.getr regs3 12)
    (YK.getr regs3 13) (YK.getr regs3 14) (YK.getr regs3 15) (YK.getr regs3 16) (YK.getr regs3 17)
    (YK.getr regs3 18) (YK.getr regs3 19) (YK.getr regs3 20) (YK.getr regs3 21) (YK.getr regs3 22)
    (YK.getr regs3 23) (YK.getr regs3 24) (YK.getr regs3 25) (YK.getr regs3 26) (YK.getr regs3 27)
    (YK.getr regs3 28) (YK.getr regs3 29) (YK.getr regs3 30) (YK.getr regs3 31)
    t fr A sp (ACtlCut.c_sp cx) YM.alloc_ceiling (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_in cx) junk
    R1 Hr2 R7 Hr9 R10 R11 R12 R13 R14 R18 Hr19 R22 R25 Hr26 R28 R29 R30 R31
    Ht Hfr32 ltac:(lia) ltac:(lia) Hfceil Hfrloc ltac:(lia) HA416 HSsp HspA ltac:(lia) ltac:(lia) Hlen
    ltac:(intros Hn0; destruct (HBLK Hn0) as (X1 & X2 & _); lia)
    ltac:(intros Hn0; destruct (HBLK Hn0) as (_ & _ & _ & X & _); exact X)
    (PB.img_vis_W W3)
    ltac:(intros a Ha; exact (proj1 (Hfpres a Ha)))
    ltac:(intros i Hi; exact (proj1 (Hfsh i Hi)))
    HSTK
    ltac:(intros Hn0; destruct (HBLK Hn0) as (_ & _ & _ & _ & X & _); exact X)
    ltac:(intros Hn0; destruct (HBLK Hn0) as (_ & _ & _ & _ & _ & X); exact X)
    BIN AIN BOUR Hjl B328 B168 (proj1 Hrt)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx) HFS).
  { exact (PB.fp_avoids_RNG_W _). }
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (R & pc' & m' & Ems & HAC' & HSW' & WM & ARMS).
  subst ms'.
  (* ---- G5: the three exits ---- *)
  (* the frame shadow and the stack window stay present (wmono, above the image) *)
  assert (HSH' : forall i, 0 <= i < 392 -> exists b, m' (Z_to_bv 64 (ART.shadow_addr fr + i)) = Some b).
  { intros i Hi. apply (r1g_some_after mem3 m' _ WM); [lia | exact (proj2 (proj1 (Hfsh i ltac:(lia))))]. }
  assert (HSTK' : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha. apply (r1g_some_after mem3 m' _ WM); [lia | exact (proj2 (HSTK a Ha))]. }
  assert (PROX : forall x, A + 32 <= x < A + 48 \/ A + 120 <= x < A + 128 \/ A + 136 <= x < A + 144 \/
                   A + 160 <= x < A + 192 \/ A + 208 <= x < A + 216 \/ A + 248 <= x < A + 280 ->
                   ~ r1g_zone fr A sp x).
  { intros x Hx. destruct Hx as [X|[X|[X|[X|[X|X]]]]]; apply (r1g_nz_stk _ _ _ _ _ _ GEO); lia. }
  assert (PROO : forall i, 0 <= i < 6 -> ~ r1g_zone fr A sp (ART.shadow_addr (fr + 2624 + i))).
  { intros i Hi. rewrite (EO i Hi). apply (r1g_nz_sh _ _ _ _ _ _ GEO); lia. }
  assert (PROB : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> ~ r1g_zone fr A sp x).
  { intros x Hx. destruct (Z_lt_le_dec 0 (ACtlCut.c_n cx)) as [Hn0|Hn0]; [|lia].
    destruct (HBLK Hn0) as (X1 & X2 & X3 & X4 & _). apply (r1g_nz_blk _ _ _ _ _ _ GEO); [lia | lia | |].
    - destruct X4; [left | right]; lia.
    - destruct X3; [left | right]; lia. }
  assert (PROBS : forall i, 0 <= i < ACtlCut.c_n cx -> ~ r1g_zone fr A sp (ART.shadow_addr (ACtlCut.c_p cx + i))).
  { intros i Hi. destruct (HBLK ltac:(lia)) as (X1 & X2 & X3 & X4 & _).
    apply (r1g_nz_bsh _ _ _ _ _ _ GEO); [lia | lia |]. destruct X4; [left | right]; lia. }
  destruct ARMS as [ARM | [ARM | ARM]].
  - (* ===== the back edge: the cut of turn t + 1 ===== *)
    destruct ARM as (Epc & Ht5 & K1 & K2 & K3 & K4 & K7 & K8 & K9 & K12 & K13 & K18 & K19 & K21 & K26 & K27 &
      K28 & K29 & K30 & K31 & K10 & K11 & K14 & K22 & K25 & MU & (junk' & Hjl' & HOUR')).
    subst pc'.
    assert (HZ : forall y, ~ FRM.outside (r1g_W1 fr t) y -> r1g_zone fr A sp y)
      by (intros y Hy; exact (r1g_W1_zone fr A sp t y Ht Hy)).
    assert (E9 : YK.getr R 9 = YK.getr regs3 9) by (etransitivity; [exact K9 | reflexivity]).
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (C_A81414_at (t + 1))) R m' md')
              (POST cx)).
    apply (HN Ht5 cx idx fr k ly3 S3 W3 R m' md' HB).
    + apply (r1g_journal B LAWS cx ly3 S3 W3 mem3 md3 m' md' k (r1g_W1 fr t) fr HJ MU WM
               (fun x Hx => Hhid x Hx) Hsbm Efr).
      intros a Ha. exact (r1g_W1_in _ _ _ _ _ t a GEO Ht Ha).
    + exact HF.
    + exact HL.
    + exact Hk.
    + split; [split; [lia | exact K11]|].
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81414].
      exists (t + 1).
      split; [exact HP|].
      split.
      { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'
                 (r1g_frac_mem B _ _ cx fr fr regs3 mem3 m' _ A GEO HFRAC Hr9 HZ MU HSH'));
          [etransitivity; [exact K2 | reflexivity] | etransitivity; [exact K3 | reflexivity]
          | etransitivity; [exact K4 | reflexivity] | etransitivity; [exact K8 | reflexivity] | exact E9
          | etransitivity; [exact K19 | reflexivity] | etransitivity; [exact K26 | reflexivity]]. }
      split; [exact Hn26|].
      split; [lia|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K1 | exact R1]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K7 | exact R7]|].
      split; [exact K10|].
      split; [exact K11|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K12 | exact R12]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K13 | exact R13]|].
      split; [exact K14|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K18 | exact R18]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K21 | exact R21]|].
      split; [exact K22|].
      split; [exact K25|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K28 | exact R28]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K29 | exact R29]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K30 | exact R30]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K31 | exact R31]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S152]|].
      split; [exact (r1g_pro_move cx fr regs3 R mem3 m' _ _ A HPRO Hr9 HAr HZ MU E9 PROX PROO PROB PROBS Hlen)|].
      split; [apply (r1g_bat_zone _ _ mem3 m' _ _ HZ MU B328); intros x Hx; cbn [length Z.of_nat] in Hx;
              unfold ACtlCutP.Sfr in Hx; apply (r1g_nz_sh _ _ _ _ _ _ GEO); lia|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K27 | exact R27]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S144]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S192]|].
      split; [destruct HIDB as (idb & Hidb); exists idb; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hidb); r1g_nzf GEO|].
      split; [destruct HJNK as (jk & Hjk); exists jk; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjk); r1g_nzf GEO|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S280]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S240]|].
      split; [destruct HJY as (jy & Hjy); exists jy; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjy); r1g_nzf GEO|].
      split; [destruct HSC as (sc & Hsc); exists sc; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hsc); r1g_nzf GEO|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S200]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S216]|].
      exists junk'. split; [exact Hjl' | exact HOUR'].
    + apply (r1g_ctlrt_C B ly3 S3 mem3 m' (r1g_W1 fr t) Hrt MU); [| exact HAC' | exact HSW'].
      intros a Ha. exact (proj1 (r1g_W1_in _ _ _ _ _ t a GEO Ht Ha)).
  - (* ===== P3: the cut 0x81b14 ===== *)
    destruct ARM as (Epc & E5 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25 & MU & HOUR').
    subst pc'.
    assert (HZ : forall y, ~ FRM.outside (r1g_W1 fr t) y -> r1g_zone fr A sp y)
      by (intros y Hy; exact (r1g_W1_zone fr A sp t y Ht Hy)).
    assert (E9 : YK.getr R 9 = YK.getr regs3 9) by (etransitivity; [exact K9 | reflexivity]).
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81b14) R m' md') (POST cx)).
    apply (HP3 cx idx fr k ly3 S3 W3 R m' md' HB).
    + apply (r1g_journal B LAWS cx ly3 S3 W3 mem3 md3 m' md' k (r1g_W1 fr t) fr HJ MU WM
               (fun x Hx => Hhid x Hx) Hsbm Efr).
      intros a Ha. exact (r1g_W1_in _ _ _ _ _ t a GEO Ht Ha).
    + exact HF.
    + exact HL.
    + assert (E14 : ACtlCut.cut_kmax C_A81b14 cx idx = 14) by reflexivity. rewrite E14.
      assert (Hk0 : k <= 0) by exact Hk. lia.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81b14].
      split; [exact HP|].
      split.
      { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'
                 (r1g_frac_mem B _ _ cx fr fr regs3 mem3 m' _ A GEO HFRAC Hr9 HZ MU HSH'));
          [etransitivity; [exact K2 | reflexivity] | etransitivity; [exact K3 | reflexivity]
          | etransitivity; [exact K4 | reflexivity] | etransitivity; [exact K8 | reflexivity] | exact E9
          | etransitivity; [exact K19 | reflexivity] | etransitivity; [exact K26 | reflexivity]]. }
      split; [exact Hn26|].
      split; [exact HOUR'|].
      split.
      { unfold ACtlCutP.CUR, SM.c0, SM.nlen. rewrite <- Hlen. split; [lia|]. split; [exact K22 | exact K25]. }
      split; [exact (r1g_pro_move cx fr regs3 R mem3 m' _ _ A HPRO Hr9 HAr HZ MU E9 PROX PROO PROB PROBS Hlen)|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S144]|].
      destruct HIDB as (idb & Hidb). destruct HJNK as (jk & Hjk).
      exists sp, A, idb, jk.
      split; [etransitivity; [exact K2 | exact Hr2]|].
      split; [etransitivity; [exact K9 | exact Hr9]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K27 | exact R27]|].
      split; [lia|]. split; [lia|].
      split.
      { pose proof (r1g_spill_q64 regs3 mem3 A 192 _ Hr9 HAr ltac:(lia) S192) as Q192.
        split; [split|].
        - cbn [CEL.cells_wf CEL.cell_wf]. split; exact I.
        - cbn [CEL.cells_bytes CEL.cbytes]. rewrite app_nil_r.
          exact (r1g_q64_zone _ _ mem3 m' _ _ HZ MU Q192 ltac:(r1g_nzs GEO)).
        - change (Z.of_nat (CEL.cells_size [CEL.C8 (Z_to_bv 64 (fr + 2768))])) with 8.
          apply r1g_wr_some; [lia | lia |]. intros x Hx. apply HSTK'. lia. }
      split; [apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hidb); r1g_nzf GEO|].
      split; [apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjk); r1g_nzf GEO|].
      split; [exact (r1g_q64_zone _ _ mem3 m' _ _ HZ MU (r1g_spill_q64 regs3 mem3 A 280 _ Hr9 HAr ltac:(lia) S280)
                       ltac:(r1g_nzs GEO))|].
      split; [exact (r1g_q64_zone _ _ mem3 m' _ _ HZ MU (r1g_spill_q64 regs3 mem3 A 240 _ Hr9 HAr ltac:(lia) S240)
                       ltac:(r1g_nzs GEO))|].
      destruct HJY as (jy & Hjy). destruct HSC as (sc & Hsc). exists jy, sc.
      split; [apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjy); r1g_nzf GEO|].
      apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hsc); r1g_nzf GEO.
    + apply (r1g_ctlrt_C B ly3 S3 mem3 m' (r1g_W1 fr t) Hrt MU); [| exact HAC' | exact HSW'].
      intros a Ha. exact (proj1 (r1g_W1_in _ _ _ _ _ t a GEO Ht Ha)).
  - (* ===== R2: the cut 0x814f8, after the catalogue call ===== *)
    destruct ARM as (Epc & E5 & Hn7 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K26 & K10 & K22 & K25 & K23 &
      MU & HOUR' & HZc & HZ48 & HZ56 & HZ72 & HZ80 & HZ88 & HZ128).
    subst pc'.
    assert (HZ : forall y, ~ FRM.outside (r1g_Wall fr A sp) y -> r1g_zone fr A sp y)
      by (intros y Hy; exact (r1g_Wall_zone fr A sp y Hy)).
    assert (E9 : YK.getr R 9 = YK.getr regs3 9) by (etransitivity; [exact K9 | reflexivity]).
    assert (SPN : forall off v, MEM.bytes_at rsegs m' (A + off) (MEM.le8 (Z_to_bv 64 v)) -> ACtlCutP.spill R m' off v).
    { intros off v Hb. exists A. split; [unfold ACtlCut.rgv; etransitivity; [exact K9 | exact Hr9] | exact Hb]. }
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A814f8) R m' md') (POST cx)).
    apply (HR2 cx idx fr k ly3 S3 W3 R m' md' HB).
    + apply (r1g_journal B LAWS cx ly3 S3 W3 mem3 md3 m' md' k (r1g_Wall fr A sp) fr HJ MU WM
               (fun x Hx => Hhid x Hx) Hsbm Efr).
      intros a Ha. exact (r1g_Wall_in _ _ _ _ _ a GEO Ha).
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A814f8].
      split; [exact HP|].
      split.
      { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'
                 (r1g_frac_mem B _ _ cx fr fr regs3 mem3 m' _ A GEO HFRAC Hr9 HZ MU HSH'));
          [etransitivity; [exact K2 | reflexivity] | etransitivity; [exact K3 | reflexivity]
          | etransitivity; [exact K4 | reflexivity] | etransitivity; [exact K8 | reflexivity] | exact E9
          | etransitivity; [exact K19 | reflexivity] | etransitivity; [exact K26 | reflexivity]]. }
      split; [exact Hn26|].
      split; [exact K10|].
      split; [exact HOUR'|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S152]|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K18 | exact R18]|].
      split; [exact HZc|].
      split; [unfold ACtlCut.rgv; etransitivity; [exact K21 | exact R21]|].
      split; [unfold ACtlCutP.CUR; split; [lia|]; split; [exact K22 | exact K25]|].
      split; [exact (SPN _ _ HZ48)|].
      split; [exact (SPN _ _ HZ128)|].
      split; [exact (r1g_pro_move cx fr regs3 R mem3 m' _ _ A HPRO Hr9 HAr HZ MU E9 PROX PROO PROB PROBS Hlen)|].
      split; [exact K23|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S144]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S192]|].
      split; [destruct HIDB as (idb & Hidb); exists idb; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hidb); r1g_nzf GEO|].
      split; [destruct HJNK as (jk & Hjk); exists jk; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjk); r1g_nzf GEO|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S280]|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S240]|].
      split; [destruct HJY as (jy & Hjy); exists jy; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hjy); r1g_nzf GEO|].
      split; [destruct HSC as (sc & Hsc); exists sc; apply (r1g_rwc_zone _ _ mem3 m' _ _ HZ MU WM Hsc); r1g_nzf GEO|].
      split; [exact (SPN _ _ HZ56)|].
      split; [exact (SPN _ _ HZ88)|].
      split; [exact (SPN _ _ HZ80)|].
      split; [exact (SPN _ _ HZ72)|].
      split; [apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S200]|].
      apply (r1g_spill_zone _ _ _ _ _ _ _ _ _ HZ MU Hr9 HAr); [lia | exact E9 | r1g_nzs GEO | exact S216].
    + apply (r1g_ctlrt_C B ly3 S3 mem3 m' (r1g_Wall fr A sp) Hrt MU); [| exact HAC' | exact HSW'].
      intros a Ha. exact (proj1 (r1g_Wall_in _ _ _ _ _ a GEO Ha)).
Qed.

End GlueR1Turn.
