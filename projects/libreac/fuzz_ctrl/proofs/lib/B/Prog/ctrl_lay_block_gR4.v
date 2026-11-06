(* ctrl_lay_block (0x86104), fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): region R4 of pb_ctrl_lay_block's glue,
   from the class-1 flag store `sb zero,0(a0)` at pc 0x86440 = 549952 to the return.  rule 24: no function proved.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md section 3 (R4) (a working note, not in this delivery).
   lay_R4: from the descriptor D4 (ctrl_lay_block_gD4.lay_D4) to tctrl_lay_block_post (C_ctrl_lay_block.v).
     1. the run: ctrl_lay_block_cutsF.ly_store_tail (the store, the 12 restores, ret) on B.MemNorm.normalize rsegs
        mem3, lifted to the world by ctrl_lay_block_gbase.lay_SRr_norm at RNG := B.ProgBridge.RNG_W (w_H W3);
     2. the journal: ProgWorld.ctl_release_of_free_law_stmt 1 over that run, write set [(fa, fa + 1)],
        fa = fs_flag (ly_F lyc) 1 pos = flag_addr ly3 1 pos (ProgWorld.ctl_fs_geom), the flag byte 0 at the end;
     3. the post: frames / ablocks of stack_free_state 1 pos S3, the output block from D4 (the run writes only fa,
        which is outside it), acall_kept from D4's across the one byte fa (an allocator-owned flag byte of a frame of
        S3: no kept class holds it), the callee-saved registers from the restores, journal index k + 0.
   ly_store_tail is closed over Section CUTS: its statement takes Section variables and hypotheses it does not read
   (p f md g fr tb mb nb gb, m, and their facts Rp .. MDP); they are instantiated by closed values below
   (p := 1, f := md := g := 0, fr := 24 zero bytes, the others []), which meet those hypotheses trivially.

   CLOSURE: the _F files are Required QUALIFIED; lib.Lib is named lib.Lib.X; every B module is named B.X in full. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_ctrl_lay_block.
(* the _F closure and the bridges, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT BzBridge MemNorm MemNormF MemNormTr ProgBridge
  ProgWorld.
(* the proved B ProgWorld statement this file reads, by its lemma (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds asan_stack_malloc_c ctrl_lay_block_c
  ctrl_lay_blockF_on ctrl_lay_block_cutsF ctrl_lay_block_gbase ctrl_lay_block_gD4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
(* the class-1 flag byte of position pos *)
Local Notation FA lyc pos := (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos).

(* ================================================================================================================
   1. Image-level helpers (lib.Lib level)
   ================================================================================================================ *)
(* B's segments are not executable-and-writable across 2^64 (the core's decision procedure). *)
Lemma lay_R4_wx : lib.Reusable.YK04.wx_segs_nowrap B.Img0.rsegs.
Proof. apply lib.Reusable.YK04.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* A return address that passes ret_ok is its own ret_pc (B/KindBGlue.v kb_ret_pc, over the core's ret_ok). *)
Lemma lay_R4_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> lib.Lib.MState.ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0).
  { rewrite Hz. change ((Z.land (bv_unsigned k) (-2) mod 2 ^ 64) mod 2) with
      ((Z.land (bv_unsigned k) (-2) mod 2 ^ 64) mod 2 ^ 1).
    rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 64) (Z.ones 1)) with (Z.ones 1).
    rewrite <- Z.land_assoc. change (Z.land (-2) (Z.ones 1)) with 0. apply Z.land_0_r. }
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

(* No segment byte lies at or above IMG_HI (a Theorem Labs lane's rrB_seg_rom_above, lib/B/Prog/GlueLift.v:162). *)
Lemma lay_R4_seg_rom_above : forall a, B.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  lib.Lib.PropExec.seg_rom B.Img0.rsegs (lib.Lib.Mem.wa a) = None.
Proof.
  intros a Ha. unfold lib.Lib.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment B.Img0.rsegs (bv_unsigned (lib.Lib.Mem.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite (lib.Lib.Mem.wa_unsigned a ltac:(unfold B.Prog.ImgBounds.IMG_HI in Ha; lia)) in E.
  destruct (B.BzBridge.find_segment_below B.Img0.rsegs B.Prog.ImgBounds.IMG_HI a 1 s B.MemNormTr.rsegs_below_img E
              ltac:(lia)) as [L|L]; lia.
Qed.

(* Every image byte lies below IMG_HI (A glue lay_img_below, B's segments). *)
Lemma lay_R4_img_below : forall a, in_img SEGS a -> a < B.Prog.ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hin & Hb). pose proof B.MemNormTr.rsegs_below_img as H.
  unfold B.MemNormTr.seg_ends_below in H. rewrite forallb_forall in H. specialize (H sg Hin).
  apply Z.leb_le in H. lia.
Qed.

Lemma lay_R4_byte1 : forall b : byte, Z_to_bv 8 (lib.Reusable.YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  assert (E : lib.Reusable.YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
  { unfold lib.Reusable.YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
    rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ 8) with 256. rewrite (Z.mod_small _ 256) by lia.
    apply Z.mod_small. lia. }
  rewrite E. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* Bytes ctrl's run leaves at visible addresses are the core's garr8 over the restricted memory. *)
Lemma lay_R4_garr8 : forall (H : word -> bool) (m : word -> option byte) (a : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  B.ProgBridge.range_visible H a (Z.of_nat (length bs)) ->
  garr8 SEGS (mrestrict H m) a (map (fun x : byte => bv_unsigned x) bs).
Proof.
  intros H m a bs (H0 & H1 & Hb) (_ & _ & Hv) j Hj.
  rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
  assert (En : nth j (map (fun x : byte => bv_unsigned x) bs) 0 = bv_unsigned b).
  { apply nth_error_nth. rewrite nth_error_map, Eb. reflexivity. }
  rewrite En. split.
  - intros kk Hk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
    pose proof (Hb j Hj) as Hbj. rewrite Eb in Hbj.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in Hbj.
    unfold lib.Reusable.YP09.mbyte, mrestrict.
    rewrite (Hv (a + Z.of_nat j) ltac:(lia)).
    rewrite lay_R4_byte1.
    destruct (m (Z_to_bv 64 (a + Z.of_nat j))) as [c|]; [exact Hbj|].
    transitivity (Some b); [exact Hbj | reflexivity].
  - pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. lia.
Qed.

(* ================================================================================================================
   2. R4
   ================================================================================================================ *)
Section R4.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
(* core rules (the composition's) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
(* the class-1 inline release as a journal step: the B ProgWorld statement, PROVED (a Theorem Labs lane), cited by its lemma *)
Let RELF1 : B.ProgWorld.ctl_release_of_free_law_stmt (SK := SK) B 1 := B.ProgWorldAstack.ctl_release_of_free_law B 1.

(* The flag byte of a live frame (1, pos) of S is no byte of a kept class of Sc (frames Sc among frames S, the same
   side stack, the same blocks): AR_flag_law makes it allocator-owned, AR_frames_law / AR_blocks_law make the frame
   bytes, their shadow and the block bytes not owned. *)
Lemma lay_R4_flag_apart : forall ly S (W : world SEGS) m md lyc Sc pos,
  AR SEGS B ly S W m md -> In (1, pos) (frames S) -> ly_F ly = ly_F lyc ->
  (forall c, In c (frames Sc) -> In c (frames S)) -> ablocks B ly S = ablocks B lyc Sc ->
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     0 <= a < 2 ^ 64 /\ a <> flag_addr ly 1 pos) /\
  (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
     0 <= b + i < 2 ^ 64 /\ b + i <> flag_addr ly 1 pos).
Proof.
  intros ly S W m md lyc Sc pos HAR Hin HlyF Hsub Hab.
  destruct (al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (_ & Hown & _ & _).
  pose proof asan_consts as (C1 & _).
  split.
  - intros cid pos' a Hin' Hr.
    pose proof (Hsub _ Hin') as Hin3.
    destruct (al_frames _ _ LAWS ly S W m md cid pos' HAR Hin3) as (_ & _ & Hfb & Hsh).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos' HAR Hin3) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    assert (EF : frame_addr lyc cid pos' = frame_addr ly cid pos') by (unfold frame_addr; rewrite HlyF; reflexivity).
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; rewrite EF in Hr.
    + split; [lia|]. intros Heq. apply (proj2 (Hfb a ltac:(lia))). rewrite Heq. exact Hown.
    + split.
      * unfold shadow_addr, SHADOW_OFF in Hr. Z.div_mod_to_equations. lia.
      * intros Heq. apply (proj2 (Hsh (a - shadow_addr (frame_addr ly cid pos')) ltac:(lia))).
        replace (shadow_addr (frame_addr ly cid pos') + (a - shadow_addr (frame_addr ly cid pos'))) with a by lia.
        rewrite Heq. exact Hown.
  - intros b n i Hb Hi. rewrite <- Hab in Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb0 & Hb1 & _ & Hba & _).
    split; [lia|]. intros Heq. apply (proj2 (Hba (b + i) ltac:(lia))). rewrite Heq. exact Hown.
Qed.

(* acall_kept across a run that writes only the flag byte fa of a live frame (1, pos) of S (and leaves it present). *)
Lemma lay_R4_kept : forall ly S (W3 : world SEGS) m md lyc Sc (W : world SEGS) memc (m4 : word -> option byte)
    slo shi (E : Z -> Prop) pos,
  AR SEGS B ly S W3 m md -> In (1, pos) (frames S) -> ly_F ly = ly_F lyc ->
  (forall c, In c (frames Sc) -> In c (frames S)) -> ablocks B ly S = ablocks B lyc Sc ->
  B.Prog.ImgBounds.IMG_HI <= flag_addr ly 1 pos ->
  (forall x : word, bv_unsigned x <> flag_addr ly 1 pos -> m4 x = m x) ->
  (exists b, m4 (Z_to_bv 64 (flag_addr ly 1 pos)) = Some b) ->
  acall_kept SEGS B lyc Sc W memc W3 m slo shi E ->
  acall_kept SEGS B lyc Sc W memc W3 m4 slo shi E.
Proof.
  intros ly S W3 m md lyc Sc W memc m4 slo shi E pos HAR Hin HlyF Hsub Hab Himg HM Hfb (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (lay_R4_flag_apart ly S W3 m md lyc Sc pos HAR Hin HlyF Hsub Hab) as (AF & AB).
  destruct (al_flag _ _ LAWS ly S W3 m md 1 pos HAR Hin) as (_ & _ & _ & Hceil).
  pose proof asan_consts as (C1 & _).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> a <> flag_addr ly 1 pos ->
            aview SEGS (w_H W3) m4 a = aview SEGS (w_H W3) m a).
  { intros a Ha Hne. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact Hne. }
  assert (PR : forall a, apresent (w_H W3) m a -> apresent (w_H W3) m4 a).
  { intros a (Hh & b & Hb). split; [exact Hh|].
    destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 a)) (flag_addr ly 1 pos)) as [E1|E1].
    - assert (Ew : Z_to_bv 64 a = Z_to_bv 64 (flag_addr ly 1 pos))
        by (rewrite <- E1; symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
      rewrite Ew. exact Hfb.
    - exists b. rewrite (HM _ E1). exact Hb. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn. rewrite (EQ a ltac:(lia) ltac:(lia)). exact (K1 a Ha Hn).
  - intros b n i Hb Hi HE. destruct (AB b n i Hb Hi) as (Hr & Hne).
    rewrite (EQ (b + i) Hr Hne). exact (K2 b n i Hb Hi HE).
  - intros a Hi Hs He. pose proof (B.ProgWorld.pws_segs_low a Hi) as Hl. pose proof (lay_R4_img_below a Hi) as Hl2.
    unfold kLowMemEnd in Hl. rewrite (EQ a ltac:(lia) ltac:(lia)). exact (K3 a Hi Hs He).
  - intros cid pos' a Hin' Hr HE. destruct (AF cid pos' a Hin' Hr) as (Ha & Hne).
    rewrite (EQ a Ha Hne). exact (K4 cid pos' a Hin' Hr HE).
  - intros a Ha Hn Hp. exact (PR a (K5 a Ha Hn Hp)).
  - intros a Ha. exact (PR a (K6 a Ha)).
Qed.

(* The flag byte is outside the output block: by the block's home every block byte is an image byte (below IMG_HI,
   the flag byte above), a byte of a live block of Sc or a byte of a frame of class >= 2 of Sc (not owned, while the
   flag byte is: lay_R4_flag_apart). *)
Lemma lay_R4_flag_out : forall ly S (W : world SEGS) m md lyc Sc pos q n,
  AR SEGS B ly S W m md -> In (1, pos) (frames S) -> ly_F ly = ly_F lyc ->
  (forall c, In c (frames Sc) -> In c (frames S)) -> ablocks B ly S = ablocks B lyc Sc ->
  B.Prog.ImgBounds.IMG_HI <= flag_addr ly 1 pos ->
  tctrl_lay_block_home B lyc Sc q n ->
  forall a, q <= a < q + n -> a <> flag_addr ly 1 pos.
Proof.
  intros ly S W m md lyc Sc pos q n HAR Hin HlyF Hsub Hab Himg Hhome a Ha.
  destruct (lay_R4_flag_apart ly S W m md lyc Sc pos HAR Hin HlyF Hsub Hab) as (AF & AB).
  destruct (Hhome a Ha) as [(Hi & _) | [(b & n' & i & Hb & Hi & ->) | (cid & pos' & Hin' & _ & Hr)]].
  - pose proof (lay_R4_img_below a Hi). lia.
  - exact (proj2 (AB b n' i Hb Hi)).
  - exact (proj2 (AF cid pos' a Hin' (or_introl Hr))).
Qed.

(* The main lemma of region R4. *)
Lemma lay_R4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
    (p md g : Z) (fr tb mb nb gb : list byte) (pos : Z) ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model),
  B.Prog.ctrl_lay_block_gD4.lay_D4 (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g
    fr tb mb nb gb pos ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (mkCfg (lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 549952) mem3 (lib.Reusable.YK11.seg_rom SEGS)) md3)
    (tctrl_lay_block_post (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g
       fr tb mb nb gb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g fr tb mb nb gb pos ly3 S3 W3 regs3 mem3 md3 D4.
  destruct D4 as (HJ & Hfrs & Hab & HlyF & Hpos & HGT & Hhome & Hwlo & Hwhi & Hret & E3 & E4 & E8 & E9 & E10 &
    E24 & E25 & E26 & E27 & Hro & (fb & HFC) & HSV & HDJ & HBLK & HVB & HVF & HK).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (HSz : spZ regs = bv_unsigned (rget regs 2)) by reflexivity.
  assert (EK : B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  assert (ES : CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (rget regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  (* the flag byte *)
  assert (Hin1 : In (1, pos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hsub : forall c, In c (frames Sc) -> In c (frames S3)) by (intros c Hc; rewrite Hfrs; right; exact Hc).
  assert (Eflag : flag_addr ly3 1 pos = FA lyc pos).
  { destruct (B.ProgWorld.ctl_fs_geom (ly_F lyc) 1 pos ltac:(lia)) as (_ & _ & _ & Hfl & _).
    change (Z.to_nat 1) with 1%nat in Hfl. unfold flag_addr. rewrite HlyF, Hfl. reflexivity. }
  assert (Efa : FA lyc pos = ly_F lyc + 20480 + pos) by (unfold B.Prog.asan_stack_malloc_c.fs_flag; cbn; lia).
  replace (B.Prog.asan_stack_malloc_c.fs_M 1) with 8192 in Hpos by reflexivity.
  destruct (al_flag _ _ LAWS ly3 S3 W3 mem3 md3 1 pos HAR3 Hin1) as (_ & _ & _ & Hfceil).
  rewrite Eflag in Hfceil.
  unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT.
  (* the start configuration in ctrl's MS form, the store state's registers named *)
  change (lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 549952) mem3 (lib.Reusable.YK11.seg_rom SEGS)) with
    (lib.Lib.MState.MS regs3 lib.Reusable.YK11.fp_regs (Z_to_bv 64 549952) lib.Reusable.YK11.fp_csr None mem3
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold lib.Lib.Regs6ss.mkR_of.
  assert (F3 : reg_get regs3 3 = rget regs 3) by exact E3.
  assert (F4 : reg_get regs3 4 = rget regs 4) by exact E4.
  assert (F8 : reg_get regs3 8 = rget regs 2) by exact E8.
  assert (F9 : reg_get regs3 9 = Z_to_bv 64 ((bv_unsigned (rget regs 2) - 128) / 32 * 32)) by exact E9.
  assert (F10 : reg_get regs3 10 = Z_to_bv 64 (FA lyc pos)) by exact E10.
  assert (F24 : reg_get regs3 24 =
                Z_to_bv 64 (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)))
    by exact E24.
  assert (F25 : reg_get regs3 25 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) by exact E25.
  assert (F26 : reg_get regs3 26 = Z_to_bv 64 B.AsanRT.ASAN_K) by exact E26.
  assert (F27 : reg_get regs3 27 = rget regs 27) by exact E27.
  rewrite F3, F4, F8, F9, F10, F24, F25, F26, F27.
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned (reg_get regs3 2)).
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned (reg_get regs3 18)).
  (* ly_store_tail's facts at the normalized store memory *)
  assert (HHM : B.AsanRT.HIGHMEM_BEG <= bv_unsigned (rget regs 2) - B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
    by (unfold B.AsanRT.HIGHMEM_BEG; lia).
  assert (HAE : bv_unsigned (rget regs 2) <= B.AsanRT.APPMEM_END) by (unfold B.AsanRT.APPMEM_END; lia).
  assert (RWIN : lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (w_H W3))
                   (bv_unsigned (rget regs 2) - B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
                   B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K).
  { apply B.ProgBridge.rng_of_visible. rewrite EK. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (K6 a ltac:(lia))). }
  pose proof (B.ProgBridge.rng_of_visible _ _ _ HVF) as RFS.
  assert (HFCn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (FA lyc pos)
                   [lib.Lib.Cells.C1 fb]).
  { apply B.MemNormTr.rw_cells_normalize; [exact Hro | | exact HFC].
    intros i Hi. cbn in Hi. apply B.MemNormTr.ro_addr_above_img. unfold B.Prog.ImgBounds.IMG_HI. lia. }
  assert (HSf : store_ok B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3) (lib.Lib.Mem.wa (FA lyc pos)) 1 = true).
  { pose proof HFCn as (_ & _ & _ & Hw).
    apply (B.Prog.ctrl_lay_blockF_on.wv_store_ok (B.MemNorm.normalize B.Img0.rsegs mem3)
             (B.MemNorm.normalize B.Img0.rsegs mem3) (FA lyc pos) 1);
      [| apply lib.Lib.Frame.wmono_refl | lia | lia].
    intros i Hi. apply Hw. cbn. lia. }
  assert (HSVn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem3)
                   (bv_unsigned (rget regs 2) + -96)
                   (B.Prog.ctrl_lay_blockF_on.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18)
                      (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24)
                      (rget regs 25) (rget regs 26))).
  { apply B.MemNormTr.rw_cells_normalize; [exact Hro | | exact HSV].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add B.Prog.ctrl_lay_blockF_on.SAVES] in Hi.
    apply B.MemNormTr.ro_addr_above_img. unfold B.Prog.ImgBounds.IMG_HI. lia. }
  (* the closed run; the Section-CUTS values it does not read are closed values *)
  pose proof (B.Prog.ctrl_lay_block_cutsF.ly_store_tail
                (rget regs 1) (rget regs 2) (rget regs 3) (rget regs 4) (rget regs 8) (rget regs 9) (rget regs 18)
                (rget regs 19) (rget regs 20) (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24)
                (rget regs 25) (rget regs 26) (rget regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
                1 0 0 0 (ly_F lyc) (repeat (Z_to_bv 8 0) 24) [] [] [] []
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl
                ltac:(vm_compute; congruence) ltac:(intros Hk2; vm_compute in Hk2; discriminate Hk2)
                ltac:(lia) ltac:(intros (Hk3 & _); vm_compute in Hk3; exfalso; apply Hk3; reflexivity)
                HHM HAE (B.ProgBridge.RNG_W (w_H W3)) RWIN RFS
                (B.MemNorm.normalize B.Img0.rsegs mem3) fb
                (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) (bv_unsigned (reg_get regs3 18))
                (bv_unsigned (reg_get regs3 2)) pos
                (reg_get regs3 1) (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7) (reg_get regs3 11)
                (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
                (reg_get regs3 17) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
                (reg_get regs3 23) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
                ltac:(rewrite (eq_refl : B.Prog.asan_stack_malloc_c.fs_M 1 = 8192); lia)
                HFCn HSf (B.MemNorm.mem_inv_normalize B.Img0.rsegs mem3) HSVn HDJ) as RUN.
  eapply (B.Prog.ctrl_lay_block_gbase.lay_SRr_norm lay_R4_wx W3 _ md3 _ _ _ _ mem3 _ _
            (B.ProgBridge.fp_avoids_RNG_W _) Hro RUN).
  (* the continuation: the real end memory, the journal, the post *)
  intros ms' model' Hrun (s0 & HQ & HREL & HROS) Hhid Hsame.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    Es0 & MU & WM & RM & MI & (b0 & HF0 & Hb0)).
  subst s0.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems' HMR].
  pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ mem3 (B.MemNorm.normalize B.Img0.rsegs mem3) (ms_mem ms') m'
                (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem3 Hro) HMR HROS MU) as HMU.
  (* the flag byte 0 in the real end memory *)
  assert (HM0 : ms_mem ms' (Z_to_bv 64 (FA lyc pos)) = Some b0).
  { destruct HF0 as ((_ & HB) & _).
    apply (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs (ms_mem ms') m' _ _ HMR)) in HB.
    destruct HB as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)).
    cbn [nth_error lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes app Z.of_nat] in HB. rewrite Z.add_0_r in HB.
    unfold lib.Lib.Mem.mrd in HB. change (Z_to_bv 64 (FA lyc pos)) with (lib.Lib.Mem.wa (FA lyc pos)).
    destruct (ms_mem ms' (lib.Lib.Mem.wa (FA lyc pos))) as [c|]; [exact HB|].
    rewrite (lay_R4_seg_rom_above (FA lyc pos) ltac:(unfold B.Prog.ImgBounds.IMG_HI; lia)) in HB. discriminate HB. }
  assert (Eb0 : b0 = Z_to_bv 8 0) by (apply bv_eq; rewrite Hb0; reflexivity).
  (* the journal across the run: the class-1 release *)
  assert (HJ2 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 (stack_free_state 1 pos S3) W3
                  (ms_mem ms') model' k).
  { lazymatch type of Hrun with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      refine (RELF1 LAWS ASF lay_R4_wx ltac:(lia) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 ms0 ms' md3 model' k pos
                (B.ProgBridge.RNG_W (w_H W3)) [(FA lyc pos, FA lyc pos + 1)] HJ Hrun
                (B.ProgBridge.fp_avoids_RNG_W _) HMU Hsame _ _) end.
    - intros a _ Hout. right. rewrite Eflag.
      destruct (Z.eq_dec a (FA lyc pos)) as [Ea|Ea]; [exact Ea|].
      exfalso. apply Hout. cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
    - rewrite Eflag. unfold lib.Reusable.YP09.mbyte. rewrite HM0, Eb0. reflexivity. }
  (* the post *)
  rewrite Ems'.
  apply lib.Reusable.YA0n.SRr_ret.
  exists ly3, (stack_free_state 1 pos S3). eexists. exists (ms_mem ms'), model'.
  split; [rewrite (lay_R4_ret_pc _ Hret); reflexivity|].
  split; [unfold EV_CTRL_LAY_BLOCK; rewrite Z.add_0_r; exact HJ2|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [reflexivity .. |].
    assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      as Hr' by lia.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity. }
  split.
  { change (frames (stack_free_state 1 pos S3)) with (del_pos (frames S3) 1 pos).
    rewrite Hfrs. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  split; [exact Hab|].
  (* the outside-the-flag byte facts of the end memory *)
  assert (Hfa_img : B.Prog.ImgBounds.IMG_HI <= flag_addr ly3 1 pos)
    by (rewrite Eflag; unfold B.Prog.ImgBounds.IMG_HI; lia).
  assert (HMx : forall x : word, bv_unsigned x <> flag_addr ly3 1 pos -> ms_mem ms' x = mem3 x).
  { intros x Hx. apply HMU. rewrite Eflag in Hx. cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
  split.
  { (* the output block: D4's bytes, kept (fa is outside the block), visible in W3 *)
    destruct HBLK as ((Hwf & HBb) & _).
    cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf] in Hwf.
    cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HBb. rewrite app_nil_r in HBb.
    assert (HL : length (B.Prog.ctrl_lay_blockF_on.LAY md g fr tb mb nb gb) = 32%nat) by (destruct Hwf; assumption).
    assert (HB4 : lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem ms') (p + 18) (B.Prog.ctrl_lay_blockF_on.LAY md g fr tb mb nb gb)).
    { apply (B.Prog.ctrl_lay_blockF_on.bytes_keep mem3 _ _ _ HBb).
      intros x Hx. rewrite HL in Hx. destruct HVB as (V0 & V1 & _).
      unfold lib.Lib.Mem.mrd. rewrite (HMx (lib.Lib.Mem.wa x)); [reflexivity|].
      rewrite lib.Lib.Mem.wa_unsigned by lia.
      exact (lay_R4_flag_out ly3 S3 W3 mem3 md3 lyc Sc pos (p + 18) 32 HAR3 Hin1 HlyF Hsub Hab Hfa_img Hhome x
               ltac:(lia)). }
    apply (lay_R4_garr8 (w_H W3) (ms_mem ms') (p + 18) _ HB4). rewrite HL. exact HVB. }
  (* acall_kept: D4's, across the one byte fa *)
  apply (lay_R4_kept ly3 S3 W3 mem3 md3 lyc Sc W memc (ms_mem ms') _ _ _ pos HAR3 Hin1 HlyF Hsub Hab Hfa_img HMx
           ltac:(exists b0; rewrite Eflag; exact HM0) HK).
Qed.

End R4.
