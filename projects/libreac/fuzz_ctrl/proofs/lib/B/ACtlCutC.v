(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ACtlCutC.v (a working branch d4442b54c0b, blob d5fe365fb54; first twinned at ea8776b2302, blob 8fc6700d36e, then A's frames-area branch of cut_shadow_of_AR (am_areas; the core's aareas is the same blob in both images, so the row index `do 5 right` is A's) and img_shadow_of_AR's new disjunct index): the same Section, names, statements and proofs over image B (asan-ubsan).  Differences from A: (1) module paths: A.AsanRT / A.Img0 / A.ACtlK / A.ACtlCut / A.ACtlRtC / A.ProgWorldCtlRt / A.ProgWorld_Fs / A.ShadowRwOn / A.Prog.CtrlRo -> B.*, A.AB1v / A.AF0m -> lib.Reusable.YB1v / YF0m; (2) every Require names the full directory of the one copy a clean checkout binds (`From ...fuzz_ctrl.lib.Reusable Require ...`, `From ...fuzz_ctrl.lib.B Require ...`, `From ...fuzz_ctrl.lib.B.Prog Require CtrlRo asan_stack_malloc_c`), where A writes `From ...fuzz_ctrl.lib Require Reusable.X` / `A.X`; (3) in_shadow_high: A's literal 0x5fe000 is B.Prog.asan_stack_malloc_c.ASAN_GT by name (0x5fe000 in B as in A; the same value as B.Prog.ImgBounds.IMG_HI, the bound of B.ProgWorldCtlRt.mem_some_of_aview_high, so A's uses of that lemma stand unchanged, by conversion), and its proof unfolds ASAN_GT; (4) comments: line references point at B's files (ACtlCut.v:212-213 / 227-240 / 239 / 227-232, CtrlRo.v:45-47), "AF0m's tables" read "YF0m's tables", section 5 marks the 777216-byte count as image A's, and section 8 names a Theorem Labs lane's B lemma as the same fact in another module.  The literals kept from A are image-independent: 2^64 (18446744073709551616), the byte bound 256, and img_shadow_cover's walk fuel 1000. *)
(* lib/B/ACtlCutC.v -- route (C) (a Theorem Labs lane DECISION 09:20Z): the LEMMAS of the stage-variable cut form.
   ONE WRITER: a Theorem Labs lane.  A working branch on a Theorem Labs lane's announced glue base 29ddfc3ea99.  FROZEN NAMES
   (a Theorem Labs lane 09:20Z): ctl_rt_C_of_ctl_rt, cut_shadow_at_cut here; cut_shadow, img_shadow, ctl_rt_C in lib/B/ACtlRtC.v
   (below ACtlCut, a Theorem Labs lane 09:37Z); shadow_rw_on and shadow_rw_on_of_shadow_rw in the leaf lib/B/ShadowRwOn.v
   (a Theorem Labs lane 09:23Z).  Both moved text-unchanged.  rule 24: no function proved (bridge lemmas over the core's world
   and YF0m's tables).

   WHY.  ctl_rt (ACtlCut.v:212-213) carries `B.ACtlK.shadow_rw_at m` = `B.AsanRT.shadow_rw m`, presence and readability of
   EVERY in_shadow byte.  Route (C) narrows it to the regions the lifted runs read.  a Theorem Labs lane's table
   (shadow-rw-uses.md (a working note, not in this delivery)) lists them: the
   owned class-6 frame's shadow FS6 = [S(fr), S(fr)+512), the shadow-word covers of live blocks (phi), the PORTSC word and
   the catalogue rows (image), all in stage variables (fr, phi, rr), which an arity-(m) definition cannot name.

   THE FORM.  The regions are named by the CUT'S OWN STATE, which ctl_from already binds at the ctl_rt premise
   (ACtlCut.v:227-240: ly3 S3 W3 mem3, frames S3 = cut_own X cx, bl = ablocks B ly3 S3):
     ctl_rt_C ly3 S3 mem3 := asan_cells_at mem3 /\ shadow_rw_on (cut_shadow B ly3 S3) mem3
                             /\ shadow_rw_on img_shadow mem3 /\ ro_agree_at mem3
   with four region kinds in cut_shadow / img_shadow:
     (F) the shadow of every frame the cut owns, [shadow_addr (frame_addr ly cid pos), + fs_frame_bytes cid / 8)
         (a Theorem Labs lane's FS6 for the class-6 frame: fr = frame_addr (c_ly cx) 6 (c_fpos cx), ACtlCut.v:239);
     (L) the 8-aligned shadow-word cover of every live block (p, n) in ablocks B ly S (a Theorem Labs lane's phi rows: the record block);
     (Z) the shadow of every zero_shadow range (machine stack + as_zero_shadow, YG0n.v:188-189; the PORTSC zero granule);
     (I) the shadow of the image [IMG_LO, IMG_HI) (catalogue rows, PORTSC's const rows, KIND_NAME, BA_SW).
   No region names a fixed stage address; fr / phi / rr are reached through frames S3 / ablocks / the image range.

   WHAT RE-ESTABLISHES IT.  (F), (L), (Z) are CONSEQUENCES OF AR at the cut (cut_shadow_of_AR below: al_frames'
   fourth conjunct, al_shadow's shadow_hull_vis, al_zshadow), so ANY exit that applies its next cut's ctl_from - which
   must hand over that cut's ajournal, whose first conjunct is the cut's AR (YCbq.v:354) - can state them; no run post
   is needed (cut_shadow_at_cut).  (I) is AR-derived too, under CtrlTSyms (img_shadow_of_AR / img_shadow_at_cut): every
   image shadow byte is a Tfib_zero_shadow byte (region (Z), as_zero_shadow B = Tfib_zero_shadow by ts_zsh) or a 1-byte
   Tfib_const_shadow row (present by AR's am_const, ProgWorld_Fs.pw_row), checked by vm_compute over YF0m's concrete
   tables (img_shadow_cover, section 6); CtrlRo.img_shadow_vis is not used.  And the old universal form gives the new one
   (shadow_rw_on_of_shadow_rw), so every exit that today builds shadow_rw from a run post (a Theorem Labs lane's working note (iv), not in this delivery: F12 F13 F14
   F23 F34 P1_70 R8 Y1) states it unchanged. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YG0v YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT Img0 ACtlK ACtlCut ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld_Fs ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).
(* ONE shadow_rw_on: the leaf B.ShadowRwOn's (a Theorem Labs lane 09:23Z); these names only abbreviate it here. *)
Local Notation shadow_rw_on := B.ShadowRwOn.shadow_rw_on (only parsing).
Local Notation srw_byte_of_mem := B.ShadowRwOn.srw_byte_of_mem (only parsing).

Section CutC.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* The definitions live in B.ACtlRtC; these names only abbreviate them here. *)
Local Notation cut_shadow := (B.ACtlRtC.cut_shadow B) (only parsing).
Local Notation img_shadow := B.ACtlRtC.img_shadow (only parsing).
Local Notation ctl_rt_C := (B.ACtlRtC.ctl_rt_C B) (only parsing).


(* ---- 1. The old form gives the new one (B.ShadowRwOn.shadow_rw_on_of_shadow_rw): every exit that builds ctl_rt
   today builds ctl_rt_C. ---- *)

Lemma ctl_rt_C_of_ctl_rt : forall ly S m, B.ACtlCut.ctl_rt m -> ctl_rt_C ly S m.
Proof.
  intros ly S m (Hc & Hs & Hr). unfold B.ACtlRtC.ctl_rt_C. split; [exact Hc|].
  split; [exact (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ Hs)|].
  split; [exact (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ Hs) | exact Hr].
Qed.

(* A's literal 0x5fe000 is B.Prog.asan_stack_malloc_c.ASAN_GT (= 0x5fe000 in image B, the same value as
   B.Prog.ImgBounds.IMG_HI, B.ProgWorldCtlRt.mem_some_of_aview_high's bound, which the uses below meet by conversion). *)
Lemma in_shadow_high : forall a, B.AsanRT.in_shadow a -> B.Prog.asan_stack_malloc_c.ASAN_GT <= a < 2 ^ 64.
Proof.
  intros a Hsh. unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
    B.AsanRT.HIGHMEM_BEG in Hsh.
  unfold B.Prog.asan_stack_malloc_c.ASAN_GT.
  change (2 ^ 64) with 18446744073709551616. destruct Hsh as [[H1 H2]|[H1 H2]]; lia.
Qed.

(* ---- 3. (F), (L), (Z), (A) from AR at the cut. ---- *)
Lemma cut_shadow_of_AR : lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> shadow_rw_on (cut_shadow ly S) m.
Proof.
  intros LAWS ly S W m md HAR a Hreg Hsh. apply srw_byte_of_mem.
  pose proof (in_shadow_high a Hsh) as Hhigh.
  destruct Hreg as [(cid & pos & Hin & Hlo & Hhi) | [(p & n & Hin & Hlo & Hhi) | [(r & Hin & Hlo & Hhi) | (Hlo & Hhi)]]].
  - destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly S W m md cid pos HAR Hin) as (_ & _ & _ & Hsf).
    destruct (Hsf (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly cid pos)) ltac:(lia))
      as ((_ & b & Hb) & _).
    replace (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly cid pos) +
             (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly cid pos))) with a in Hb by lia.
    rewrite Hb. discriminate.
  - destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly S W m md p n HAR Hin) as [_ Hhull].
    apply (B.ProgWorldCtlRt.mem_some_of_aview_high W m a Hhigh).
    apply Hhull. lia.
  - pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W m md r HAR Hin) as Hz.
    apply (B.ProgWorldCtlRt.mem_some_of_aview_high W m a Hhigh).
    unfold lib.Reusable.YG0v.zero_shadow in Hz.
    assert (Hi : 0 <= a - lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) < snd r / 8) by lia.
    pose proof (Hz _ Hi) as Hv.
    replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) +
             (a - lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r))) with a in Hv by lia.
    rewrite Hv. discriminate.
  - (* (A): the frames-area row of aareas, (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8),
       is range_vis by am_areas *)
    pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ (proj1 HAR)) as HAr.
    rewrite Forall_forall in HAr.
    assert (Hrow : In (lib.Reusable.YG0f.ASh (lib.Reusable.YG0f.AF lib.Reusable.YG0f.kFakeFramesOff),
                       (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8)
                      (lib.Reusable.YG0n.aareas S)).
    { unfold lib.Reusable.YG0n.aareas. repeat (apply in_or_app; right). cbn [In]. do 5 right. left. reflexivity. }
    pose proof (HAr _ Hrow) as Hv. unfold lib.Reusable.YG0f.range_vis in Hv.
    cbn [fst snd lib.Reusable.YG0f.aeval] in Hv.
    assert (E : lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize) =
                lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff) +
                (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8).
    { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kFakeFramesOff.
      Z.div_mod_to_equations. lia. }
    apply (B.ProgWorldCtlRt.mem_some_of_aview_high W m a Hhigh).
    specialize (Hv (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff))
                   ltac:(lia)).
    replace (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff) +
             (a - lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff)))
      with a in Hv by lia.
    exact Hv.
Qed.

(* ---- 4. At ANY cut: ctl_from's own premise gives the cut's AR (YCbq.v:354), so the exit that hands over the next
   cut's ajournal can state (F), (L), (Z) there.  Binders as ctl_from (ACtlCut.v:227-232). ---- *)
Lemma cut_shadow_at_cut : lib.Reusable.YG0d.AR_laws segs B ->
  forall STK sp0 FP ly S (W : lib.Reusable.YA0n.world segs) mem md own ly3 S3 (W3 : lib.Reusable.YA0n.world segs)
         (mem3 : word -> option byte) md3 k,
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k ->
    shadow_rw_on (cut_shadow ly3 S3) mem3.
Proof.
  intros LAWS STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k HJ.
  exact (cut_shadow_of_AR LAWS ly3 S3 W3 mem3 md3 (proj1 HJ)).
Qed.

(* ---- 5. The (I) coverage fact: every shadow byte of the image hull is the shadow of a Tfib_zero_shadow range or a
   1-byte Tfib_const_shadow row (image A's count, a Theorem Labs lane's measure-C/img_shadow_cover.py on the record AF0m 44930bfd861:
   777216 bytes = 776430 zero + 786 row, 0 uncovered; image B's is decided by img_shadow_cover's vm_compute below).
   Closed: no B, no ly; the tables are YF0m's concrete lists.  The value bound
   is pw_row / pw_z1_row's premise shape (0 <= v < 256). ---- *)
Definition img_shadow_cover_stmt : Prop :=
  forall a, img_shadow a ->
    (exists r, In r lib.Reusable.YF0m.Tfib_zero_shadow /\
       lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) <= a <
       lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) + snd r / 8)
    \/ (exists v, In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum a) v) lib.Reusable.YF0m.Tfib_const_shadow /\ 0 <= v < 256).

(* ---- 6. Its proof: a gap-walking checker, proved sound once, run by vm_compute on the concrete tables. ---- *)
Definition row_of (c : lib.Reusable.YG0f.acell) : option (Z * Z) :=
  match c with
  | lib.Reusable.YG0f.ACell (lib.Reusable.YG0f.ANum s) (S O) (lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum v)) =>
      Some (s, v)
  | _ => None
  end.

Lemma row_of_sound : forall c s v, row_of c = Some (s, v) -> c = lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum s) v.
Proof.
  intros [ca cw cv] s v. destruct ca; try (intro H; discriminate H).
  destruct cw as [|[|cw]]; try (intro H; discriminate H).
  destruct cv as [e|mk w]; try (intro H; discriminate H).
  destruct e; try (intro H; discriminate H).
  intro H. cbn in H. injection H as <- <-. reflexivity.
Qed.

(* the 1-byte constant rows of a cell list, as (shadow address, value) *)
Definition z1rows (l : list lib.Reusable.YG0f.acell) : list (Z * Z) :=
  flat_map (fun c => match row_of c with Some p => p :: nil | None => nil end) l.

Lemma z1rows_in : forall l s v, In (s, v) (z1rows l) -> In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum s) v) l.
Proof.
  intros l s v H. unfold z1rows in H. apply in_flat_map in H as (c & Hc & Hin).
  destruct (row_of c) as [p|] eqn:E; [|destruct Hin].
  destruct Hin as [Ep|[]]. subst p. rewrite <- (row_of_sound c s v E). exact Hc.
Qed.

(* the covering intervals [lo, hi) of shadow bytes: zero ranges' shadow, then one byte per row *)
Definition cov_ivs : list (Z * Z) :=
  map (fun r => (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r),
                 lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) + snd r / 8))
      lib.Reusable.YF0m.Tfib_zero_shadow
  ++ map (fun p => (fst p, fst p + 1)) (z1rows lib.Reusable.YF0m.Tfib_const_shadow).

(* walk from cur to hi: at each step jump to the end of an interval that contains cur *)
Fixpoint walk (fuel : nat) (l : list (Z * Z)) (cur hi : Z) : bool :=
  if Z.leb hi cur then true else
  match fuel with
  | O => false
  | S f =>
      match find (fun iv => andb (Z.leb (fst iv) cur) (Z.ltb cur (snd iv))) l with
      | Some iv => walk f l (snd iv) hi
      | None => false
      end
  end.

Lemma walk_sound : forall fuel l cur hi, walk fuel l cur hi = true ->
  forall a, cur <= a < hi -> exists iv, In iv l /\ fst iv <= a < snd iv.
Proof.
  induction fuel as [|f IH]; intros l cur hi H a Ha; cbn [walk] in H.
  - destruct (Z.leb hi cur) eqn:E0; [apply Z.leb_le in E0; lia | discriminate H].
  - destruct (Z.leb hi cur) eqn:E0; [apply Z.leb_le in E0; lia|].
    match type of H with context [find ?g l] => destruct (find g l) as [iv|] eqn:E end; [|discriminate H].
    apply find_some in E as (Hin & Hb). apply andb_prop in Hb as (H1 & H2).
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (Z_lt_le_dec a (snd iv)).
    + exists iv. split; [exact Hin | lia].
    + exact (IH l (snd iv) hi H a ltac:(lia)).
Qed.

Lemma img_shadow_cover : img_shadow_cover_stmt.
Proof.
  intros a (x & Hx & ->).
  assert (W : walk 1000%nat cov_ivs (lib.Reusable.YG0f.SHADOW_OFF + B.Prog.CtrlRo.IMG_LO / 8)
                (lib.Reusable.YG0f.SHADOW_OFF + (B.Prog.CtrlRo.IMG_HI - 1) / 8 + 1) = true)
    by (vm_compute; reflexivity).
  assert (HV : forallb (fun p => andb (Z.leb 0 (snd p)) (Z.ltb (snd p) 256)) (z1rows lib.Reusable.YF0m.Tfib_const_shadow) = true)
    by (vm_compute; reflexivity).
  destruct (walk_sound _ _ _ _ W (lib.Reusable.YG0f.shadow_addr x)) as (iv & Hin & Hlo & Hhi).
  { unfold lib.Reusable.YG0f.shadow_addr. unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in *.
    Z.div_mod_to_equations. lia. }
  apply in_app_or in Hin as [Hz|Hr].
  - left. apply in_map_iff in Hz as (r & <- & Hr). exists r. split; [exact Hr|]. cbn [fst snd] in Hlo, Hhi. lia.
  - right. apply in_map_iff in Hr as (p & <- & Hp). destruct p as [s v]. cbn [fst snd] in Hlo, Hhi.
    assert (Ea : lib.Reusable.YG0f.shadow_addr x = s) by lia. rewrite Ea. exists v.
    split; [exact (z1rows_in _ s v Hp)|].
    pose proof (proj1 (forallb_forall _ _) HV _ Hp) as Hb. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
Qed.

(* ---- 7. (I) from AR alone, under CtrlTSyms. ---- *)
Lemma img_shadow_of_AR : lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> shadow_rw_on img_shadow m.
Proof.
  intros TS LAWS ly S W m md HAR a Ha Hsh.
  destruct (img_shadow_cover a Ha) as [(r & Hr & Hlo) | (v & Hrow & Hv)].
  - assert (HZ : In r (lib.Reusable.YG0n.zero_shadow_ranges B ly)).
    { unfold lib.Reusable.YG0n.zero_shadow_ranges. apply in_cons. rewrite (lib.Reusable.YF0m.ts_zsh B TS). exact Hr. }
    exact (cut_shadow_of_AR LAWS ly S W m md HAR a
             (or_intror (or_intror (or_introl (ex_intro _ r (conj HZ Hlo))))) Hsh).
  - apply srw_byte_of_mem. apply (B.ProgWorldCtlRt.mem_some_of_aview_high W m a (in_shadow_high a Hsh)).
    assert (Hin : In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum a) v) (lib.Reusable.YF0m.Tfib_const ly)).
    { unfold lib.Reusable.YF0m.Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hrow. }
    pose proof (B.ProgWorld_Fs.pw_row B TS ly S W m md _ HAR Hin) as Hc.
    unfold lib.Reusable.YG0f.cell_holds in Hc.
    cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z1
         lib.Reusable.YG0f.c1 lib.Reusable.YG0f.aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hc by lia.
    rewrite Hc. discriminate.
Qed.

(* At ANY cut, as cut_shadow_at_cut. *)
Lemma img_shadow_at_cut : lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall STK sp0 FP ly S (W : lib.Reusable.YA0n.world segs) mem md own ly3 S3 (W3 : lib.Reusable.YA0n.world segs)
         (mem3 : word -> option byte) md3 k,
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k ->
    shadow_rw_on img_shadow mem3.
Proof.
  intros TS LAWS STK sp0 FP ly S W mem md own ly3 S3 W3 mem3 md3 k HJ.
  exact (img_shadow_of_AR TS LAWS ly3 S3 W3 mem3 md3 (proj1 HJ)).
Qed.

(* ---- 8. Image B's twin of A's section 8; the same fact as a Theorem Labs lane's lib/B/ProgBridgeData.v (a version not in this delivery; written on a working branch 3c8b6fdc8a8)
   (another module, same name, same vm_compute coverage method; not Required here, a Theorem Labs lane via a Theorem Labs lane 09:4xZ):
   CtrlRo's img_shadow_vis premise (CtrlRo.v:45-47), from img_shadow_cover, so B's ro_hull users and stages carrying
   IMG_SHADOW_VIS can discharge it. ---- *)
Lemma ctrl_img_shadow_vis : lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  B.Prog.CtrlRo.img_shadow_vis segs B.
Proof.
  intros TS LAWS ly S W mem md a HAR Ha.
  destruct (img_shadow_cover (lib.Reusable.YG0f.shadow_addr a) (ex_intro _ a (conj Ha eq_refl)))
    as [(r & Hr & Hlo) | (v & Hrow & Hv)].
  - assert (HZ : In r (lib.Reusable.YG0n.zero_shadow_ranges B ly)).
    { unfold lib.Reusable.YG0n.zero_shadow_ranges. apply in_cons. rewrite (lib.Reusable.YF0m.ts_zsh B TS). exact Hr. }
    pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md r HAR HZ) as Hz.
    unfold lib.Reusable.YG0v.zero_shadow in Hz.
    pose proof (Hz (lib.Reusable.YG0f.shadow_addr a -
                    lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r)) ltac:(lia)) as Hv0.
    replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) +
             (lib.Reusable.YG0f.shadow_addr a -
              lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r)))
      with (lib.Reusable.YG0f.shadow_addr a) in Hv0 by lia.
    rewrite Hv0. discriminate.
  - assert (Hin : In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum (lib.Reusable.YG0f.shadow_addr a)) v)
                     (lib.Reusable.YF0m.Tfib_const ly)).
    { unfold lib.Reusable.YF0m.Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hrow. }
    pose proof (B.ProgWorld_Fs.pw_row B TS ly S W mem md _ HAR Hin) as Hc.
    unfold lib.Reusable.YG0f.cell_holds in Hc.
    cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.z1
         lib.Reusable.YG0f.c1 lib.Reusable.YG0f.aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)).
    replace (lib.Reusable.YG0f.shadow_addr a + Z.of_nat 0) with (lib.Reusable.YG0f.shadow_addr a) in Hc by lia.
    rewrite Hc. discriminate.
Qed.

End CutC.

Print Assumptions cut_shadow_at_cut.
Print Assumptions img_shadow_of_AR.
Print Assumptions ctl_rt_C_of_ctl_rt.
Print Assumptions img_shadow_at_cut.
Print Assumptions ctrl_img_shadow_vis.
