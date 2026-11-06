(* lib/B/Prog/C_reac_ctrl_parseW.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): world facts for the glue
   pb_reac_ctrl_parse, in lib/Lib terms, at the memory after the class-1 fake-stack call (state lyc S2 W mem2 md2 with
   (1, pos) in frames S2) and at the caller's journal.  They supply C_reac_ctrl_parseLib's Section RoFB hypotheses
   (the frame / flag byte layout, the footprint visibility of every range the re-based stretch reads or writes, the
   window, the runtime cells and the shadow region the callees write, with its covering facts W12-W13) and the
   premises of the acall_kept composition after the stretch (what the stretch writes is apart from the caller's
   blocks, the caller's frames and the image).  Sources: the AR laws (lib/Reusable/YG0d.v AR_laws), the core's AR
   facts (lib/Reusable/YG0s.v frame_facts, chunk_facts, frames_apart) and B ProgWorld's proved statements.  Every B
   module is named by its full lib.B path (the root lib/MemNorm.v and lib/Img0.v are twins of B's).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
(* GOT_CF / CF (asan_stack_malloc_c, bcmp_wrap_c: the same values), REAL_BCMP / BCMP / REAL_MEMCMP (bcmp_wrap_c),
   MEMCMP (memcmp_c): the names C_reac_ctrl_parseLib's hypotheses use, Imported as that file Imports them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YE01 YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0a YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldAstack ProgWorldCtlRtC ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldShadow ProgWorldVisWin ProgWorldVisFrame ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ACtlRtC ProgBridgeData.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds rng_asan sh_word_on.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.

(* The 8-aligned shadow cover of [a, b] in the form C_reac_ctrl_parseLib's shkov states (B.AsanRT.shadow_addr). *)
Definition rcpW_shk (RG : lib.Lib.ExecF.footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    lib.Lib.ExecF.rng RG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
(* Each shadow byte of [p, p + n), in the form C_reac_ctrl_parseLib's shcov states. *)
Definition rcpW_shc (RG : lib.Lib.ExecF.footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> lib.Lib.ExecF.rng RG (x / 8 + ASAN_K) 1.

(* ---- helpers (all Qed) ---- *)

(* alloc_ceiling's range (YG0f.v:16, ASAN_CEIL = alloc_ceiling). *)
Lemma rcpW_ceil : 0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling <= 0x7fffff800000.
Proof. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [H _]. unfold lib.Reusable.YG0f.ASAN_CEIL in H. exact H. Qed.

(* Every image byte lies below IMG_HI = 0x5fe000 (B ProgBridge.rsegs_spans). *)
Lemma rcpW_img_lt : forall a, lib.Reusable.YG0d.in_img rsegs a -> a < lib.B.Prog.ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hsg & Ha).
  assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by (apply in_map_iff; exists sg; split; [reflexivity | exact Hsg]).
  rewrite lib.B.ProgBridge.rsegs_spans in Hm. unfold lib.B.Prog.ImgBounds.IMG_HI.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

(* The image range ly_img ends at or above IMG_HI (ALedger's al_img at rsegs' last segment (0xa2000, 0x55c000)). *)
Lemma rcpW_img_end : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md,
  lib.Reusable.YG0n.AR rsegs B ly S W m md ->
  lib.B.Prog.ImgBounds.IMG_HI <= fst (lib.Reusable.YG0f.ly_img ly) + snd (lib.Reusable.YG0f.ly_img ly).
Proof.
  intros ly S W m md (_ & L & _).
  assert (Hm : In (0xa2000, 0x55c000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs)).
  { rewrite lib.B.ProgBridge.rsegs_spans. right; right; right; left. reflexivity. }
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L sg Hsg) as [_ J2].
  unfold lib.B.Prog.ImgBounds.IMG_HI. lia.
Qed.

(* The geometry of a live fake frame (c, q) and its flag byte inside the side stack [ly_F, ly_F + kFakeStackSize):
   YG0s.frame_facts (class, offsets, alignment, the side stack in application memory) and ProgWorldAstack.pwfs_F_above
   (the side stack above the image). *)
Lemma rcpW_fgeo : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md c q,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (c, q) (lib.Reusable.YG01.frames S) ->
  0 <= c <= 10 /\
  lib.B.Prog.ImgBounds.IMG_HI <= lib.Reusable.YG0f.ly_F ly /\
  lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff <= lib.Reusable.YG0f.frame_addr ly c q /\
  lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c <=
    lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize /\
  lib.Reusable.YG0f.frame_addr ly c q mod 64 = 0 /\ 64 <= lib.Reusable.YG00.fs_frame_bytes c /\
  lib.Reusable.YG00.fs_frame_bytes c mod 64 = 0 /\
  lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFlagsOff <= lib.Reusable.YG0f.flag_addr ly c q /\
  lib.Reusable.YG0f.flag_addr ly c q < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff /\
  (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YG0f.kLowShadowBeg \/
   (lib.Reusable.YG0f.kHighMemBeg <= lib.Reusable.YG0f.ly_F ly /\
    lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YM05.alloc_ceiling)).
Proof.
  intros ly S W m md c q HAR Hin.
  pose proof HAR as (M & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ c q M Hin)
    as (Hc & _ & [_ HFa] & _ & Hpg & Ho1 & Ho2 & Ho64 & Hb64 & Hbm & Hfl).
  pose proof (lib.B.ProgWorldAstack.pwfs_F_above B ly S W m md HAR) as Habove.
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT in Habove.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.flag_addr, lib.Reusable.YG0f.page_aligned,
    lib.Reusable.YG0f.ASAN_CEIL, lib.B.Prog.ImgBounds.IMG_HI in *.
  split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [Z.div_mod_to_equations; lia|].
  split; [exact Hb64|]. split; [exact Hbm|]. split; [lia|]. split; [lia|].
  exact HFa.
Qed.

(* The first byte of a caller's block lies above the image: a primary chunk lies in the primary region (high memory,
   YG0s.region_in_prim); a secondary chunk lies in its secondary mapping, which is longer than kMaxSize + kPage
   (YG0a.secondary_geometry), starts at or above 4096 (sec_placed's in_app) and is apart from ly_img = [0x10000, ..)
   (sec_placed's disjointness), so it starts at or above ly_img's end. *)
Lemma rcpW_block_above : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md p n,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
  lib.B.Prog.ImgBounds.IMG_HI <= p.
Proof.
  intros ly S W m md p n HAR Hin.
  pose proof (rcpW_img_end ly S W m md HAR) as Hend.
  pose proof HAR as (M & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (lib.Reusable.YG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  apply (lib.Reusable.YG0s.In_ablocks B) in Hin as (k & Hk & Hst & Hu & Hr).
  pose proof (lib.Reusable.YG0s.chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  rewrite <- Hu, G4.
  destruct (lib.Reusable.YG00.ck_beg k) as [|o|r o|c' p'] eqn:Eb; try solve [destruct GG].
  - cbv zeta in GG. destruct GG as (Gc & _ & _ & _ & Gbase & Gx & _).
    pose proof (lib.Reusable.YG0s.region_in_prim ly (lib.Reusable.YG00.prim_class o) LO ltac:(lia))
      as (_ & _ & _ & R4 & _).
    rewrite Gbase. unfold lib.Reusable.YG0f.kHighMemBeg, lib.B.Prog.ImgBounds.IMG_HI in *. lia.
  - destruct GG as (_ & Gfp & Gbase & _ & Gin & _).
    pose proof (lib.Reusable.YG0n.am_placed _ _ _ _ M) as [PL PD].
    pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & [K1 _] & _). cbn [fst snd] in K1.
    pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint _ _ (lib.Reusable.YG0f.ly_img ly) _ _
      eq_refl PD Gin ltac:(unfold lib.Reusable.YG0f.static_extents; apply in_app_iff; right; right; left; reflexivity))
      as D.
    pose proof (lib.Reusable.YG0a.secondary_geometry (lib.Reusable.YG00.ck_req k) ltac:(lia) Gfp)
      as (S1 & _ & _ & S4 & _).
    unfold lib.Reusable.YG0f.zdisjoint in D. cbn [fst snd] in D. rewrite Gbase.
    unfold lib.Reusable.YG00.kMaxSize, lib.Reusable.YG00.kPage, lib.Reusable.YG0f.kImgLo,
      lib.B.Prog.ImgBounds.IMG_HI in *.
    lia.
Qed.

(* The shadow word cover of every sub-range [a, b] of [p, p + n), visible, gives both shadow footprint forms. *)
Lemma rcpW_cover : forall (H : word -> bool) p n,
  (forall a b, p <= a -> a <= b -> b < p + n ->
     lib.B.ProgBridge.range_visible H (lib.B.Prog.rng_asan.sh_al8_lo a)
       (lib.B.Prog.rng_asan.sh_al8_hi a (b - a + 1) - lib.B.Prog.rng_asan.sh_al8_lo a)) ->
  rcpW_shc (lib.B.ProgBridge.RNG_W H) p n /\ rcpW_shk (lib.B.ProgBridge.RNG_W H) p n.
Proof.
  intros H p n Hc.
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi in Hc.
  split.
  - intros x Hx. apply lib.B.ProgBridge.rng_of_visible.
    pose proof (Hc x x ltac:(lia) ltac:(lia) ltac:(lia)) as V.
    replace (x + (x - x + 1) - 1) with x in V by ring. unfold shadow_addr in V.
    apply (lib.B.ProgBridge.range_visible_sub _ _ _ _ _ V); Z.div_mod_to_equations; lia.
  - intros a b Ha Hab Hb. apply lib.B.ProgBridge.rng_of_visible.
    pose proof (Hc a b Ha Hab Hb) as V.
    replace (a + (b - a + 1) - 1) with b in V by ring. unfold shadow_addr in V. exact V.
Qed.

(* The two shadow-address functions agree (B.AsanRT's x / 8 + ASAN_K, the core's SHADOW_OFF + x / 8; both offsets
   0x7fff8000). *)
Lemma rcpW_sh_eq : forall x, shadow_addr x = lib.Reusable.YG0f.shadow_addr x.
Proof.
  intros x. unfold shadow_addr, ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. lia.
Qed.

(* The aligned shadow word of an address is monotone in the address. *)
Lemma rcpW_al8_mono : forall x y, x <= y ->
  lib.Reusable.YG0f.shadow_addr x / 8 * 8 <= lib.Reusable.YG0f.shadow_addr y / 8 * 8.
Proof.
  intros x y H. unfold lib.Reusable.YG0f.shadow_addr.
  assert (H1 : x / 8 <= y / 8) by (apply Z.div_le_mono; lia).
  assert (H2 : (lib.Reusable.YG0f.SHADOW_OFF + x / 8) / 8 <= (lib.Reusable.YG0f.SHADOW_OFF + y / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* A shadow byte the checks of a callee may load for [p, p + k) (sh_word_on, the region of the callees' _on texts) lies
   in the aligned shadow-word cover of every [lo, hi) that holds [p, p + k). *)
Lemma rcpW_sh_word_cover : forall lo hi p k a, lo <= p -> p + k <= hi ->
  lib.B.Prog.sh_word_on.sh_word_on p k a ->
  lib.Reusable.YG0f.shadow_addr lo / 8 * 8 <= a < lib.Reusable.YG0f.shadow_addr (hi - 1) / 8 * 8 + 8.
Proof.
  intros lo hi p k a Hlo Hhi (_ & Ha1 & Ha2).
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi in Ha1, Ha2.
  rewrite rcpW_sh_eq in Ha1, Ha2.
  pose proof (rcpW_al8_mono lo p Hlo) as M1.
  pose proof (rcpW_al8_mono (p + k - 1) (hi - 1) ltac:(lia)) as M2.
  lia.
Qed.

(* For a 64-aligned range whose length is a multiple of 64 (a live fake frame, rcpW_fgeo), that cover is the range's
   shadow. *)
Lemma rcpW_sh_word_al64 : forall F L p k a, F mod 64 = 0 -> L mod 64 = 0 -> 0 < L ->
  F <= p -> p + k <= F + L -> lib.B.Prog.sh_word_on.sh_word_on p k a ->
  lib.Reusable.YG0f.shadow_addr F <= a < lib.Reusable.YG0f.shadow_addr F + L / 8.
Proof.
  intros F L p k a HF HL HL0 Hlo Hhi Hw.
  pose proof (rcpW_sh_word_cover F (F + L) p k a Hlo Hhi Hw) as [C1 C2].
  assert (E1 : lib.Reusable.YG0f.shadow_addr F / 8 * 8 = lib.Reusable.YG0f.shadow_addr F).
  { clear - HF. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia. }
  assert (E2 : lib.Reusable.YG0f.shadow_addr (F + L - 1) / 8 * 8 + 8 = lib.Reusable.YG0f.shadow_addr F + L / 8).
  { clear - HF HL HL0. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* ---- W1..W13 ---- *)

(* W1. The new class-1 frame and its flag byte: placement below alloc_ceiling and above the image, the flag byte
   present (so writable), visible and an application byte, the frame's 16 shadow bytes below alloc_ceiling and above
   the image. *)
Lemma rcpW_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  let Fr := lib.Reusable.YG0f.frame_addr ly 1 pos in
  let FL := lib.Reusable.YG0f.flag_addr ly 1 pos in
  4096 <= Fr /\ Fr + 128 <= lib.Reusable.YM05.alloc_ceiling /\
  lib.B.Prog.ImgBounds.IMG_HI <= FL /\ FL + 1 <= lib.Reusable.YM05.alloc_ceiling /\ app_mem FL /\
  stk rsegs m FL (FL + 1) /\ lib.B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) FL 1 /\
  lib.B.Prog.ImgBounds.IMG_HI <= shadow_addr Fr /\ shadow_addr Fr + 16 <= lib.Reusable.YM05.alloc_ceiling.
Proof.
  intros ly S W m md pos HAR Hin. cbv zeta.
  destruct (rcpW_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & Hl1 & Hl2 & Happ).
  destruct (lib.Reusable.YG0d.al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (Hpr & _ & _ & _).
  pose proof rcpW_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2.
  set (Fr := lib.Reusable.YG0f.frame_addr ly 1 pos) in *.
  set (FL := lib.Reusable.YG0f.flag_addr ly 1 pos) in *.
  unfold lib.B.Prog.ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff,
    lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia|].
  split.
  { apply (lib.B.ProgWorldAstack.pwfs_stk_of_present W); [lia | lia |].
    intros a Ha. replace a with FL by lia. exact Hpr. }
  split.
  { unfold lib.B.ProgBridge.range_visible. split; [lia|]. split; [lia|].
    intros a Ha. replace a with FL by lia. exact (proj1 Hpr). }
  unfold shadow_addr, ASAN_K. split; Z.div_mod_to_equations; lia.
Qed.

(* W2. What the stretch writes outside its window (the new frame, its shadow, its flag byte) is apart from every byte
   of a caller's block. *)
Lemma rcpW_apart_block : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos p n a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  In (p, n) (lib.Reusable.YG0d.ablocks B ly S) -> p <= a < p + lib.Reusable.YG00.req_size n ->
  let Fr := lib.Reusable.YG0f.frame_addr ly 1 pos in
  let FL := lib.Reusable.YG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (shadow_addr Fr <= a < shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos p n a HAR Hin Hb Ha. cbv zeta.
  destruct (rcpW_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & _ & _ & Happ).
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hb) as (_ & H4096 & Hbc & [_ Hbapp] & Hbo & _).
  destruct (lib.Reusable.YG0d.al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (_ & Hfo & _).
  destruct (lib.Reusable.YG0d.al_sep _ _ LAWS ly S W m md HAR) as [Hpw _].
  pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint _ (p, lib.Reusable.YG00.req_size n)
    (lib.Reusable.YG0f.frame_addr ly 1 pos, lib.Reusable.YG00.fs_frame_bytes 1) _ _ eq_refl Hpw) as D.
  assert (D' : lib.Reusable.YG0f.zdisjoint (p, lib.Reusable.YG00.req_size n)
                 (lib.Reusable.YG0f.frame_addr ly 1 pos, lib.Reusable.YG00.fs_frame_bytes 1)).
  { apply D.
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hb].
    - apply in_map_iff. exists (1, pos). split; [reflexivity | exact Hin]. }
  clear D. unfold lib.Reusable.YG0f.zdisjoint in D'. cbn [fst snd] in D'.
  pose proof rcpW_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D'.
  set (Fr := lib.Reusable.YG0f.frame_addr ly 1 pos) in *.
  unfold lib.B.Prog.ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize,
    lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in *.
  split; [lia|]. split.
  - intros E. apply (proj2 (Hbo a Ha)). rewrite E. exact Hfo.
  - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* W3. ... and apart from every byte of another frame and of that frame's shadow. *)
Lemma rcpW_apart_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos c q a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  In (c, q) (lib.Reusable.YG01.frames S) -> (c, q) <> (1, pos) ->
  (lib.Reusable.YG0f.frame_addr ly c q <= a < lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c \/
   shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) <= a <
     shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) + lib.Reusable.YG00.fs_frame_bytes c / 8) ->
  let Fr := lib.Reusable.YG0f.frame_addr ly 1 pos in
  let FL := lib.Reusable.YG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (shadow_addr Fr <= a < shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos c q a HAR Hin Hcq Hne Ha. cbv zeta.
  destruct (rcpW_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & Hfm & _ & _ & Hl1 & Hl2 & Happ).
  destruct (rcpW_fgeo ly S W m md c q HAR Hcq) as (_ & _ & Hg1 & Hg2 & Hgm & Hgb & Hgbm & _).
  pose proof HAR as (M & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ 1 pos M Hin) as (C1 & P1 & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ c q M Hcq) as (C2 & P2 & _).
  pose proof (lib.Reusable.YG0s.frames_apart c q 1 pos C2 P2 C1 P1 Hne) as D.
  unfold lib.Reusable.YG0f.zdisjoint in D. cbn [fst snd] in D.
  pose proof rcpW_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.flag_addr in *.
  unfold lib.B.Prog.ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff,
    lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
    shadow_addr, ASAN_K in *.
  destruct Ha as [Ha|Ha].
  - split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
  - split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    Z.div_mod_to_equations. lia.
Qed.

(* W4. ... and apart from every image byte. *)
Lemma rcpW_apart_img : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  lib.Reusable.YG0d.in_img rsegs a ->
  let Fr := lib.Reusable.YG0f.frame_addr ly 1 pos in
  let FL := lib.Reusable.YG0f.flag_addr ly 1 pos in
  ~ (Fr <= a < Fr + 128) /\ a <> FL /\ ~ (shadow_addr Fr <= a < shadow_addr Fr + 16).
Proof.
  intros ly S W m md pos a HAR Hin Himg. cbv zeta.
  pose proof (rcpW_img_lt a Himg) as Ha.
  destruct (rcpW_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & _ & _ & _ & _ & Hl1 & _).
  set (Fr := lib.Reusable.YG0f.frame_addr ly 1 pos) in *.
  set (FL := lib.Reusable.YG0f.flag_addr ly 1 pos) in *.
  unfold lib.B.Prog.ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff in *.
  split; [lia|]. split; [lia|]. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* W5. A byte range inside a frame of S (the caller's output object o lies in one, APostBase.afobj): below
   alloc_ceiling, above the image, not read-only, and apart from every byte of a block of S. *)
Lemma rcpW_in_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md c q lo len,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (c, q) (lib.Reusable.YG01.frames S) -> 0 <= len ->
  lib.Reusable.YG0f.frame_addr ly c q <= lo -> lo + len <= lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c ->
  lo + len <= lib.Reusable.YM05.alloc_ceiling /\ lib.B.Prog.ImgBounds.IMG_HI <= lo /\
  (forall i, 0 <= i < len -> ro_addr rsegs (wa (lo + i)) = false) /\
  (forall p n a, In (p, n) (lib.Reusable.YG0d.ablocks B ly S) -> p <= a < p + lib.Reusable.YG00.req_size n ->
     ~ (lo <= a < lo + len)) /\
  stk rsegs m lo (lo + len).
Proof.
  intros ly S W m md c q lo len HAR Hcq Hlen Hlo Hhi.
  destruct (rcpW_fgeo ly S W m md c q HAR Hcq) as (_ & HF & Hg1 & Hg2 & _ & _ & _ & _ & _ & Happ).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly S W m md c q HAR Hcq) as (_ & _ & Hby & _).
  destruct (lib.Reusable.YG0d.al_sep _ _ LAWS ly S W m md HAR) as [Hpw _].
  pose proof rcpW_ceil as Hce.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HB : forall p n a, In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
                 p <= a < p + lib.Reusable.YG00.req_size n -> ~ (lo <= a < lo + len)).
  { intros p n a Hb Ha.
    pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint _ (p, lib.Reusable.YG00.req_size n)
      (lib.Reusable.YG0f.frame_addr ly c q, lib.Reusable.YG00.fs_frame_bytes c) _ _ eq_refl Hpw) as D.
    assert (D' : lib.Reusable.YG0f.zdisjoint (p, lib.Reusable.YG00.req_size n)
                   (lib.Reusable.YG0f.frame_addr ly c q, lib.Reusable.YG00.fs_frame_bytes c)).
    { apply D.
      - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hb].
      - apply in_map_iff. exists (c, q). split; [reflexivity | exact Hcq]. }
    unfold lib.Reusable.YG0f.zdisjoint in D'. cbn [fst snd] in D'. lia. }
  set (F := lib.Reusable.YG0f.frame_addr ly c q) in *.
  unfold lib.B.Prog.ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize,
    lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ, HF, Hg1, Hg2.
  split; [lia|]. split; [unfold lib.B.Prog.ImgBounds.IMG_HI; lia|].
  split; [intros i Hi; apply lib.B.MemNormTr.ro_addr_above_img; unfold lib.B.Prog.ImgBounds.IMG_HI; lia|].
  split; [exact HB|].
  apply (lib.B.ProgWorldAstack.pwfs_stk_of_present W); [lia | lia |].
  intros a Ha. exact (proj1 (Hby a ltac:(lia))).
Qed.

(* W6. A caller's block: placement (as AR_blocks_law states it), above the image. *)
Lemma rcpW_block : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md p n,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
  4096 <= p /\ p + lib.Reusable.YG00.req_size n <= lib.Reusable.YM05.alloc_ceiling /\ lib.B.Prog.ImgBounds.IMG_HI <= p /\
  (forall i, 0 <= i < lib.Reusable.YG00.req_size n -> app_mem (p + i)).
Proof.
  intros ly S W m md p n HAR Hb.
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hb) as (_ & H4096 & Hbc & [_ Hbapp] & _).
  pose proof (rcpW_block_above ly S W m md p n HAR Hb) as Hab.
  pose proof rcpW_ceil as Hce.
  split; [exact H4096|]. split; [exact Hbc|]. split; [exact Hab|].
  intros i Hi. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in Hbapp.
  lia.
Qed.

(* W7. Footprint visibility, at RNG := RNG_W (w_H W), of a sub-range of the caller's stack window (ajournal's [sp0 -
   STK, sp0)): the bytes, each shadow byte, and every 8-aligned shadow cover.  The bytes from the journal's window
   presence (YCbq.v:368) and astk_ok (:369); the shadow from ProgWorldVisWin.win_sh_vis at the journal's AR (the
   stack bounds of lyc are ly's, layout_le). *)
Lemma rcpW_vis_win : forall STK sp0 FP ly S (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k lo len,
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 -> 0 <= len ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shc (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lo len HJ Hlo Hhi Hlen.
  destruct HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
  pose proof rcpW_ceil as Hce.
  change (2 ^ 47) with 140737488355328 in H47.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split.
  - apply lib.B.ProgBridge.rng_of_visible. unfold lib.B.ProgBridge.range_visible.
    split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
  - apply rcpW_cover. intros a b Ha Hab Hb.
    destruct (lib.B.ProgWorldVisWin.win_sh_vis B LAWS lyc Sc W memc mdc a (b - a + 1) HAR
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E|V]; [lia | exact V].
Qed.

(* W8. The same for a sub-range of a block of S (ProgWorldVisHeap.heap_vis / heap_sh_vis). *)
Lemma rcpW_vis_block : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md p n lo len,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
  p <= lo -> lo + len <= p + lib.Reusable.YG00.req_size n -> 0 <= len ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shc (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len.
Proof.
  intros ly S W m md p n lo len HAR Hb Hlo Hhi Hlen.
  split.
  - apply lib.B.ProgBridge.rng_of_visible.
    exact (lib.B.ProgWorldVisHeap.heap_vis B LAWS ly S W m md p n lo len HAR Hb Hlo Hhi).
  - apply rcpW_cover. intros a b Ha Hab Hb'.
    destruct (lib.B.ProgWorldVisHeap.heap_sh_vis B LAWS ly S W m md p n a (b - a + 1) HAR Hb
                ltac:(lia) ltac:(lia) ltac:(lia)) as [E|V]; [lia | exact V].
Qed.

(* W9. The same for a sub-range of a frame of S (ProgWorldVisFrame.frame_vis; its 64-byte hull premises hold since
   every live frame is 64-aligned and a multiple of 64 bytes, rcpW_fgeo). *)
Lemma rcpW_vis_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md c q lo len,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (c, q) (lib.Reusable.YG01.frames S) ->
  lib.Reusable.YG0f.frame_addr ly c q <= lo -> lo + len <= lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c ->
  0 <= len ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shc (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len /\
  rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) lo len.
Proof.
  intros ly S W m md c q lo len HAR Hcq Hlo Hhi Hlen.
  destruct (rcpW_fgeo ly S W m md c q HAR Hcq) as (_ & _ & _ & _ & Hfm & Hb64 & Hbm & _).
  split.
  - apply lib.B.ProgBridge.rng_of_visible.
    exact (proj1 (lib.B.ProgWorldVisFrame.frame_vis B LAWS ly S W m md c q lo len HAR Hcq Hlo Hhi)).
  - apply rcpW_cover. intros a b Ha Hab Hb.
    destruct (lib.B.ProgWorldVisFrame.frame_vis B LAWS ly S W m md c q a (b - a + 1) HAR Hcq
                ltac:(lia) ltac:(lia)) as [_ Hsh].
    destruct (Hsh ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as [E|V];
      [lia | exact V].
Qed.

(* W10. The caller's stack window at the current memory of a journal: present (stk) and shadow-zero (addressable),
   and above alloc_ceiling.  Presence from the journal (YCbq.v:368), the shadow from ProgWorldShadow's
   ctl_stack_shadow_of_AR at the journal's AR, the bounds from astk_ok (YCbq.v:333-335). *)
Lemma rcpW_win : forall STK sp0 FP ly S (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k lo hi,
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo <= hi -> hi <= sp0 ->
  stk rsegs memc lo hi /\ addressable memc lo (hi - lo) /\ lib.Reusable.YM05.alloc_ceiling <= lo /\
  HIGHMEM_BEG <= lo /\ hi <= APPMEM_END.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lo hi HJ Hlo Hlh Hhi.
  destruct HJ as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
  pose proof rcpW_ceil as Hce.
  change (2 ^ 47) with 140737488355328 in H47.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split.
  { apply (lib.B.ProgWorldAstack.pwfs_stk_of_present W); [lia | lia |].
    intros a Ha. apply Hpres. lia. }
  split.
  { exact (lib.B.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS lyc Sc W memc mdc lo (hi - lo) HAR
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  unfold HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* W11. The runtime cells, the read-only agreement, the bcmp wrapper's cells and the writable shadow region at a memory
   that AR describes, with no AR_states law: ProgWorldCtlRtC.ctl_rt_C_of_AR (asan_cells; the shadow of the state's own
   regions, ACtlRtC.cut_shadow, and of the image, ACtlRtC.img_shadow; ro_agree), joined by ShadowRwOn.shadow_rw_on_union,
   and ProgBridgeData.ctl_bcmp_cells_of_AR (REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254, CF + 255).  The premises are the
   bundle law CtrlTSyms B and the AR laws. *)
Lemma rcpW_rt : lib.Reusable.YF0m.CtrlTSyms B ->
  forall RLO RHI ly S (W : lib.Reusable.YA0n.world rsegs) m md,
  lib.Reusable.YG0n.AR rsegs B ly S W m md ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m) ->
  lib.B.MemNorm.ro_agree rsegs m /\ asan_cells m /\
  lib.B.ShadowRwOn.shadow_rw_on (fun a => lib.B.ACtlRtC.cut_shadow B ly S a \/ lib.B.ACtlRtC.img_shadow a) m /\
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\ bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\
  bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros HTS RLO RHI ly S W m md HAR Hro.
  destruct (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR B HTS LAWS RLO RHI ly S W m md HAR
              (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro (Z.le_refl _) (Z.le_refl _)))
    as (Hc & Hcut & Himg & Hra).
  destruct (lib.B.ProgBridgeData.ctl_bcmp_cells_of_AR B HTS ly S W m md HAR) as (H1 & H2 & H3 & H4 & H5).
  split; [exact Hra|]. split; [exact Hc|].
  split; [exact (lib.B.ShadowRwOn.shadow_rw_on_union _ _ m Hcut Himg)|].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

(* W12. The shadow words the checks load for a sub-range of a live frame lie in cut_shadow's frames region (the frame
   is 64-aligned and a multiple of 64 bytes, rcpW_fgeo). *)
Lemma rcpW_sh_word_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md c q p k a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (c, q) (lib.Reusable.YG01.frames S) ->
  lib.Reusable.YG0f.frame_addr ly c q <= p ->
  p + k <= lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c ->
  lib.B.Prog.sh_word_on.sh_word_on p k a -> lib.B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S W m md c q p k a HAR Hcq Hlo Hhi Hw.
  destruct (rcpW_fgeo ly S W m md c q HAR Hcq) as (_ & _ & _ & _ & Hfm & Hb64 & Hbm & _).
  unfold lib.B.ACtlRtC.cut_shadow. left. exists c, q. split; [exact Hcq|].
  exact (rcpW_sh_word_al64 _ _ p k a Hfm Hbm ltac:(lia) Hlo Hhi Hw).
Qed.

(* W13. ... and for a sub-range of a live block, in cut_shadow's blocks region (the block's aligned shadow-word
   cover). *)
Lemma rcpW_sh_word_block : forall ly S b nb p k a,
  In (b, nb) (lib.Reusable.YG0d.ablocks B ly S) -> b <= p -> p + k <= b + lib.Reusable.YG00.req_size nb ->
  lib.B.Prog.sh_word_on.sh_word_on p k a -> lib.B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S b nb p k a Hb Hlo Hhi Hw.
  unfold lib.B.ACtlRtC.cut_shadow. right. left. exists b, nb. split; [exact Hb|].
  exact (rcpW_sh_word_cover b (b + lib.Reusable.YG00.req_size nb) p k a Hlo Hhi Hw).
Qed.
End W.
