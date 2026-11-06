(* crtB_w_entry: the ENTRY piece of the cgif-form walk of check_round_trip, image B: CRT_ENTRY to CRT_RET_CALLOC —
   the prologue (crt_seg1_F), malloc(4 nch ns), crt_seg2_F, malloc(8 nch), crt_seg3_F, calloc(3 nch ns, 1) — with
   the inner journal started by lib/Reusable/YCbq.v:1827 ajournal_sub_init, re-established across each footprint
   run by YCbq.v:636 ajournal_exec (crtB_j_frame: each run writes only the 160-byte frame), and extended by each
   allocator rule (YC5d.v:57 amalloc04_rule, YGCalloc.v:255 acalloc04_rule).  The three calls see s0 = nch ns,
   below sp, so their chains are empty and their traces are dec_crt_ufix's.  The frame survives each call because
   the call's stack window lies below it (crtB_frame_across); the cut's read-only view on RO_RD is read off the inner
   journal's image clause at the end (crtB_rom_kept).  It proves crtB_entry_stmt of lib/B/Prog/crtB_cuts.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YK1b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg crtB_iface crtB_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_glue crtB_walk crtB_segs crtB_cells.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK3 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

Section Entry.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation sink := dec_B_sink_head.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Local Notation GR r k := (YKK.getr r (Z_to_bv 5 k)).
Local Notation AJ := (@ajournal rc sink segs B).

(* A register of a footprint run's final state (crtB_walk.v crtB_ms_reg), read off the run's MS form. *)
Ltac crtE_reg RX r := etransitivity; [exact (RX (Z_to_bv 5 r) eq_refl) |].
Ltac crtE_same RX r := etransitivity; [exact (RX (Z_to_bv 5 r) eq_refl) | reflexivity].
(* A callee-saved register across an allocator call (YG0d.v:22 aregs_preserved). *)
Ltac crtE_pres HP r A := rewrite (HP r ltac:(unfold acallee_saved; lia)); exact A.

(* ---- small facts ---- *)

Lemma crtE_entry_rng : 4096 <= CRT_ENTRY <= 2 ^ 32.
Proof. unfold CRT_ENTRY. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* A return address inside the function: its word reads back as itself. *)
Lemma crtE_ret : forall off, 0 <= off < 4096 -> bv_unsigned (w64 (CRT_AT off)) = CRT_AT off /\ 4096 <= CRT_AT off.
Proof.
  intros off Ho. pose proof crtE_entry_rng as He. unfold CRT_AT.
  split; [apply unsigned_lit |]; lia.
Qed.

Lemma crtE_spZ : forall (r : bvmap 5 word) z, GR r 2 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> spZ r = z.
Proof. intros r z H Hz. unfold spZ. change (bv_unsigned (GR r 2) = z). rewrite H. apply unsigned_lit. exact Hz. Qed.

Lemma crtE_s0Z : forall (r : bvmap 5 word) z, GR r 8 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> s0Z r = z.
Proof. intros r z H Hz. unfold s0Z. change (bv_unsigned (GR r 8) = z). rewrite H. apply unsigned_lit. exact Hz. Qed.

(* An allocator call adds its block's size to the live bytes (YCbq.v:2796 blocks_bytes_bsum, :2788 bsum_app). *)
Lemma crtE_bytes_add : forall ly S ly2 S2 res n,
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n)] -> blocks_bytes S2 = blocks_bytes S + n.
Proof.
  intros ly S ly2 S2 res n E.
  rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), E, bsum_app.
  change (bsum [(res, n)]) with (n + 0). lia.
Qed.

(* The three blocks, appended in call order, are the cut's list (crtB_cuts.v crtB_blocks3) up to order. *)
Lemma crtE_perm3 : forall (L : list (Z * Z)) p q r, Permutation (((L ++ [p]) ++ [q]) ++ [r]) (r :: q :: p :: L).
Proof.
  intros L p q r. rewrite <- !app_assoc. cbn [app].
  eapply perm_trans; [apply Permutation_app_comm|]. cbn [app].
  exact (perm_trans (perm_swap q p _) (perm_trans (perm_skip q (perm_swap r p L)) (perm_swap r q _))).
Qed.

(* The two runtime cells the prologue reads are visible in every world (they lie in a loaded segment). *)
Lemma crtB_cell_vis : forall (W : world segs) a n i,
  dec_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 -> w_H W (wa (a + i)) = false.
Proof.
  intros W a n i Hc Hi Ht. exact (crt_covers_visible (w_H W) a n i (w_Hoff W) Hc Hi Ht).
Qed.

(* ... so the walk's footprint holds them. *)
Lemma crtB_cell_rng : forall (W : world segs) a n,
  dec_seg_covers a n = true -> a + n <= 2 ^ 64 ->
  ExecF.rng (LCK3.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros W a n Hc Ht. pose proof (crt_covers_lo a n Hc) as Ha0.
  apply (crtB_rng_of_vis W a n Ha0 Ht).
  intros x Hx. replace x with (a + (x - a)) by lia. exact (crtB_cell_vis W a n (x - a) Hc ltac:(lia) Ht).
Qed.

(* The frame cells survive an allocator call: the call's stack window lies below the frame. *)
Lemma crtB_frame_across : forall (W1 W2 : world segs) ly1 S1 mem1 mem2 (E : Z -> Prop) sp cs,
  @acall_kept rc segs B ly1 S1 W1 mem1 W2 mem2 (sp - ASTACK) sp E ->
  rw_cells rsegs mem1 sp cs -> Z.of_nat (cells_size cs) = CRT_FRAME ->
  (forall a, sp <= a < sp + CRT_FRAME -> apresent (w_H W1) mem1 a) ->
  YM05.alloc_ceiling <= sp -> sp + CRT_FRAME <= 2 ^ 64 ->
  rw_cells rsegs mem2 sp cs.
Proof.
  intros W1 W2 ly1 S1 mem1 mem2 E sp cs HK HC Hsz HP Hce Hhi.
  pose proof HK as (K1 & _ & _ & _ & K5 & _).
  eapply (crtB_rw_cells_kept W1 W2 mem1 mem2 sp cs HC).
  rewrite Hsz. intros a Ha. pose proof (HP a Ha) as HPa.
  assert (Hout : ~ (sp - ASTACK <= a < sp)) by lia.
  split; [exact HPa|]. split.
  - exact (K5 a ltac:(lia) Hout HPa).
  - exact (K1 a ltac:(lia) Hout).
Qed.

(* The cut's read-only view on RO_RD at any state of the inner journal: the journal's image clause (YCbq.v:362, at
   FP = [] the sink is closed) keeps every image byte outside the owned statics and errno, which crtB_ro_scoped
   gives for RO_RD. *)
Lemma crtB_rom_kept : forall lyc Sc W memc mdc sp ly1 S1 W1 mem1 md1 k1,
  crtB_ro_scoped B RO_RD -> crtB_rom_on RO_RD W memc ->
  AJ DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 k1 ->
  crtB_rom_on RO_RD W1 mem1.
Proof.
  intros lyc Sc W memc mdc sp ly1 S1 W1 mem1 md1 k1 HSC HR HJ1 a Hin Hrom.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _).
  destruct (HSC a Hin) as (Hown & Herr).
  assert (Him : in_img segs a) by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  rewrite (G a Him Hown Herr (fp_spares_closed [] a sink_closed_nil)).
  exact (HR a Hin Hrom).
Qed.

(* The inner journal across a footprint run that writes only the 160-byte frame [sp - 160, sp) (YCbq.v:636
   ajournal_exec; the frame lies in the journal's stack window, so every written byte is an awr_byte). *)
Lemma crtB_j_frame : AR_laws segs B ->
  forall lyc Sc W memc mdc (sp : Z) ly1 S1 W1 mem1 md1 k1 m' md',
  AJ DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 k1 ->
  (forall x : word, ~ (sp - CRT_FRAME <= bv_unsigned x < sp) -> m' x = mem1 x) ->
  YK1b.mem_grows mem1 m' -> same_but_materialized md1 md' ->
  AJ DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly1 S1 W1 m' md' k1.
Proof.
  intros LAWS lyc Sc W memc mdc sp ly1 S1 W1 mem1 md1 k1 m' md' HJ1 HOUT HGROW HSBM.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES1 & _ & _ & _).
  assert (HHIDOUT : forall x : word, w_H W1 x = true -> ~ (sp - CRT_FRAME <= bv_unsigned x < sp)).
  { intros x Hx Hr.
    assert (Hw : sp - DEC_CRT_STK <= bv_unsigned x < sp)
      by (unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
    pose proof (HPRES1 (bv_unsigned x) Hw) as (Hh & _).
    rewrite Z_to_bv_bv_unsigned in Hh. rewrite Hh in Hx. discriminate. }
  assert (HFR2 : forall x : word, ~ (sp - CRT_FRAME <= bv_unsigned x < sp) ->
      mrestrict (w_H W1) m' x = mrestrict (w_H W1) mem1 x)
    by (intros x Hx; unfold mrestrict; destruct (w_H W1 x); [reflexivity | exact (HOUT x Hx)]).
  assert (HGR2 : YK1b.mem_grows (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) m'))
    by (apply crtB_mem_grows_restrict; exact HGROW).
  assert (HHID : forall x : word, w_H W1 x = true -> m' x = mem1 x)
    by (intros x Hx; apply HOUT; exact (HHIDOUT x Hx)).
  assert (HWB : forall a, (sp - CRT_FRAME <= a < sp) ->
      awr_byte DEC_CRT_STK sp [] (ablocks B lyc Sc) (ablocks B ly1 S1) ly1 [] a)
    by (intros a Ha; unfold awr_byte; left; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  eapply ajournal_exec with (Wr := fun a => sp - CRT_FRAME <= a < sp);
    solve [ exact LAWS | exact crtB_segs_low | exact HJ1 | exact HFR2 | exact HGR2 | exact HHID
          | exact HSBM | exact HWB ].
Qed.

(* The trace of a call whose s0 is below sp (so the chain is empty) is dec_utrace pc0 [ra]. *)
Lemma crtB_trace_nil : forall pc0 (regsT : bvmap 5 word) (raw : word),
  YKK.getr regsT 1 = raw ->
  call_trace0 pc0 regsT [] = dec_utrace pc0 [bv_unsigned raw].
Proof.
  intros pc0 regsT raw Hraw. rewrite call_trace_nil. unfold dec_utrace, raZ. rewrite Hraw.
  cbn [flat_map app]. destruct (bv_unsigned raw =? pc0); reflexivity.
Qed.

Lemma crtB_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> s0Z regsT <= spZ regsT -> chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT H1 H2. unfold chain_pre. split; [exact H1|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  unfold bad_next. replace (s0Z regsT <=? spZ regsT) with true by (symmetry; apply Z.leb_le; exact H2).
  reflexivity.
Qed.

(* One malloc call of the walk, at the trampoline, with the inner journal (window [spZ regs - DEC_CRT_STK,
   spZ regs)) and sp = spZ regs - 160: amalloc04_rule (YC5d.v:57) read off at o = -160, ch = []. *)
Lemma crtB_malloc_call :
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  (forall fx' : YKK.FPState, @amalloc04_rule fx' rc sink segs B MT) ->
  forall (fq : YKK.FPState) (W1 : world segs) lyc Sc W memc mdc (regs : bvmap 5 word) ly1 S1 mem1 md1
         (regs1 : bvmap 5 word) j n (raw : word) (K : world segs -> config -> Prop),
  AJ DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 j ->
  YKK.getr regs1 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S1 + n <= LIVE_MAX ->
  spZ regs1 = spZ regs - CRT_FRAME -> spZ regs mod 16 = 0 ->
  YKK.getr regs1 3 = w64 (as_gp B) -> YKK.getr regs1 4 = w64 (as_tp B) ->
  YKK.getr regs1 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  st_nev S1 < EV_MAX -> s0Z regs1 <= spZ regs1 ->
  In (dec_utrace (pc_malloc_ra0 (as_code B)) [bv_unsigned raw]) (as_universe B) ->
  mo_ok MT S1 (mo_malloc MT n) ->
  (forall (W2 : world segs) ly2 S2 (regs2 : bvmap 5 word) mem2 md2 res,
     AJ DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 (j + 1) ->
     aregs_preserved regs1 regs2 -> YKK.getr regs2 10 = w64 res -> frames S2 = frames S1 ->
     4096 <= res -> ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, n)] ->
     @acall_kept rc segs B ly1 S1 W1 mem1 W2 mem2 (spZ regs - CRT_FRAME - ASTACK) (spZ regs - CRT_FRAME)
       (fun a => res <= a < res + req_size n) ->
     mo_le MT S1 S2 (mo_malloc MT n) ->
     SRr segs W2 (mkCfg (@YKK.mkst fq regs2 raw mem2 (YKK.seg_rom segs)) md2) K) ->
  SRr segs W1 (@cfg_at fq segs CRT_MALLOC regs1 mem1 md1) K.
Proof.
  intros HMAL RMAL fq W1 lyc Sc W memc mdc regs ly1 S1 mem1 md1 regs1 j n raw K HJ H10 Hn Hlive Hsp Hsp16
    Hgp Htp Hraw Hrok Hra4 Hnev Hs0 Htr Hmo Hk.
  unfold cfg_at, CRT_MALLOC. rewrite <- HMAL.
  eapply SRr_bind.
  { apply (RMAL fq W1 regs1 mem1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md1 j n (- CRT_FRAME)
             raw [] HJ H10 Hn Hlive).
    + unfold CRT_FRAME in *. lia.
    + unfold CRT_FRAME. reflexivity.
    + unfold CRT_FRAME. lia.
    + unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME. lia.
    + exact Hgp.
    + exact Htp.
    + exact Hraw.
    + exact Hrok.
    + exact Hnev.
    + apply crtB_chain_nil; [unfold raZ; rewrite Hraw; exact Hra4 | exact Hs0].
    + rewrite (crtB_trace_nil _ regs1 raw Hraw). exact Htr.
    + exact Hmo. }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec2 & HJ2 & Hpres & H10' & Hfr & Hres & Hab & Hkept & Hmle).
  subst c2. apply (Hk W2 ly2 S2 regs2 mem2 md2 res HJ2 Hpres H10' Hfr Hres Hab); [|exact Hmle].
  replace (spZ regs - CRT_FRAME - ASTACK) with (spZ regs + - CRT_FRAME - ASTACK) by lia.
  replace (spZ regs - CRT_FRAME) with (spZ regs + - CRT_FRAME) by lia.
  exact Hkept.
Qed.

(* The calloc call, its twin: acalloc04_rule (YGCalloc.v:255) at lib/A/DecodeCalloc.v's DEC_CALLOC_MAX /
   DEC_CALLOC_DEPTH, sz = 1, o = -160, ch = []. *)
Lemma crtB_calloc_call :
  (forall fx' : YKK.FPState, @acalloc04_rule fx' segs B (as_universe B) AJ (@acall_kept rc segs B)
     (mo_ok MT) (mo_le MT) (mo_malloc MT) (decodeb_sigma DB___interceptor_trampoline_calloc) DEC_B_calloc_ra0
     DEC_CALLOC_MAX DEC_CALLOC_DEPTH) ->
  forall (fq : YKK.FPState) (W1 : world segs) lyc Sc W memc mdc (regs : bvmap 5 word) ly1 S1 mem1 md1
         (regs1 : bvmap 5 word) j nm (raw : word) (K : world segs -> config -> Prop),
  AJ DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 j ->
  ly_bot ly1 + DEC_CALLOC_DEPTH < spZ regs1 ->
  YKK.getr regs1 10 = w64 nm -> YKK.getr regs1 11 = w64 1 ->
  0 <= nm < MALLOC_MAX -> nm <= DEC_CALLOC_MAX -> blocks_bytes S1 + nm <= LIVE_MAX ->
  spZ regs1 = spZ regs - CRT_FRAME -> spZ regs mod 16 = 0 ->
  YKK.getr regs1 3 = w64 (as_gp B) -> YKK.getr regs1 4 = w64 (as_tp B) ->
  YKK.getr regs1 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  st_nev S1 < EV_MAX -> s0Z regs1 <= spZ regs1 ->
  In (dec_utrace DEC_B_calloc_ra0 [bv_unsigned raw]) (as_universe B) ->
  mo_ok MT S1 (mo_malloc MT nm) ->
  (forall (W2 : world segs) ly2 S2 (regs2 : bvmap 5 word) mem2 md2 res,
     AJ DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 (j + 1) ->
     aregs_preserved regs1 regs2 -> YKK.getr regs2 10 = w64 res -> frames S2 = frames S1 ->
     4096 <= res -> ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, nm)] ->
     @acall_kept rc segs B ly1 S1 W1 mem1 W2 mem2 (spZ regs - CRT_FRAME - ASTACK) (spZ regs - CRT_FRAME)
       (fun a => res <= a < res + req_size nm) ->
     mo_le MT S1 S2 (mo_malloc MT nm) ->
     SRr segs W2 (mkCfg (@YKK.mkst fq regs2 raw mem2 (YKK.seg_rom segs)) md2) K) ->
  SRr segs W1 (@cfg_at fq segs CRT_CALLOC regs1 mem1 md1) K.
Proof.
  intros RCAL fq W1 lyc Sc W memc mdc regs ly1 S1 mem1 md1 regs1 j nm raw K HJ HDEP H10 H11 Hn Hcmax Hlive Hsp
    Hsp16 Hgp Htp Hraw Hrok Hra4 Hnev Hs0 Htr Hmo Hk.
  unfold cfg_at, CRT_CALLOC.
  eapply SRr_bind.
  { apply (RCAL fq W1 regs1 mem1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md1 j nm 1 (- CRT_FRAME)
             raw [] HJ HDEP H10 H11).
    + lia.
    + lia.
    + rewrite Z.mul_1_r. lia.
    + rewrite Z.mul_1_r. exact Hcmax.
    + rewrite Z.mul_1_r. exact Hlive.
    + unfold CRT_FRAME in *. lia.
    + unfold CRT_FRAME. reflexivity.
    + unfold CRT_FRAME. lia.
    + unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME. lia.
    + exact Hgp.
    + exact Htp.
    + exact Hraw.
    + exact Hrok.
    + exact Hnev.
    + apply crtB_chain_nil; [unfold raZ; rewrite Hraw; exact Hra4 | exact Hs0].
    + change (ctrace0 DEC_B_calloc_ra0 regs1 []) with (call_trace0 DEC_B_calloc_ra0 regs1 []).
      rewrite (crtB_trace_nil _ regs1 raw Hraw). exact Htr.
    + rewrite Z.mul_1_r. exact Hmo. }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec2 & HJ2 & Hpres & H10' & Hfr & Hres & Hab & _ & Hkept
    & Hmle).
  subst c2. rewrite Z.mul_1_r in Hab, Hkept, Hmle.
  apply (Hk W2 ly2 S2 regs2 mem2 md2 res HJ2 Hpres H10' Hfr Hres Hab); [|exact Hmle].
  replace (spZ regs - CRT_FRAME - ASTACK) with (spZ regs + - CRT_FRAME - ASTACK) by lia.
  replace (spZ regs - CRT_FRAME) with (spZ regs + - CRT_FRAME) by lia.
  exact Hkept.
Qed.

(* ---- the piece ---- *)
Theorem crtB_entry : @crtB_entry_stmt fx rc B MT RO_RD.
Proof.
  unfold crtB_entry_stmt. intros RULES CALLOC CTX HUCTX HSC HSUB.
  unfold dec_check_round_trip_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    HJ Hretok Hra4 Hgp Htp H10 H11 H12 H13 Hch HinC Hsp16 Hstk1 Hstk2 HFRM Hev Hnch Hns Hkb HDEP
    HinA HA1 HA2 HinP HP1 HP2 Hbraid HROMV Hnev Hlive Hmo Hcost.
  pose proof RULES as (HMAL & _ & HCELLS & LAWS & HML & HUF & RMAL & _ & RCAL & _ & _).
  destruct HUF as (HUM1 & HUM2 & HUC & _ & _).
  (* the entry data the cuts carry; the read-only view on RO_RD is the statement's at DEC_RO_RD (crtB_ro_sub) *)
  assert (HROM0 : crtB_rom_on RO_RD W memc) by (intros a Hin _; exact (HROMV a (HSUB a Hin))).
  assert (HPRE : crtB_pre B MT RO_RD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns
                   bA nA bP nP T ch).
  { unfold crtB_pre.
    repeat match goal with |- _ /\ _ => split; [first [assumption | exact (HUCTX _ HinC)] |] end.
    assumption. }
  pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & HNEV0 & _ & _ & _ & _ & _ & _ & _ & HSTK0 & _ & _).
  destruct HSTK0 as (Hsp0m & HSTKnn & Hceil0 & Hlo0 & Hhi0 & H47 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as (Hcm & _).
  assert (ESTK : DEC_CRT_STK = 16544) by reflexivity.
  assert (EFR : CRT_FRAME = 160) by reflexivity.
  assert (EAS : ASTACK = 16384) by reflexivity.
  assert (EEV : DEC_CRT_EV = 6) by reflexivity.
  assert (ELV : DEC_CRT_LIVE = 8192) by reflexivity.
  assert (EMX : MALLOC_MAX = 268435456) by reflexivity.
  assert (HNN : 1 <= nch * ns) by nia.
  assert (HNS : nch * ns <= 480) by lia.
  assert (HSPa : YM05.alloc_ceiling + DEC_CRT_STK <= spZ regs) by lia.
  assert (HSPb : spZ regs <= 2 ^ 47) by lia.
  pose proof (mo_malloc_nonneg MT HML (4 * (nch * ns)) ltac:(lia)) as HM1.
  pose proof (mo_malloc_nonneg MT HML (8 * nch) ltac:(lia)) as HM2.
  pose proof (mo_malloc_nonneg MT HML (3 * (nch * ns)) ltac:(lia)) as HM3.
  pose proof (mo_free_nonneg MT HML) as HMF.
  unfold dec_crt_cost in Hcost.
  (* audio and pcm lie in caller blocks, below alloc_ceiling *)
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 HinA) as (_ & HbA4 & HbAt & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 HinP) as (_ & HbP4 & HbPt & _).
  pose proof (req_size_pos nA ltac:(lia)) as HrA.
  pose proof (req_size_pos nP ltac:(lia)) as HrP.
  assert (HAr : 0 <= audio < 2 ^ 64) by lia.
  assert (HPr : 0 <= pcm < 2 ^ 64) by lia.
  (* the inner journal, started at the entry (YCbq.v:1827) *)
  assert (HJI : AJ DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
  { eapply ajournal_sub_init with (STK := STK) (sp0 := sp0) (FP := FP) (ly := ly) (S := S) (W0 := W0)
      (mem := mem0) (md := md0) (own := own) (k := k) (o := spZ regs - sp0).
    all: first [exact HJ | exact LAWS | exact crtB_segs_low | lia | (Z.div_mod_to_equations; lia)]. }
  pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRI & _ & _ & _).
  assert (HFW0 : forall a, spZ regs - CRT_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
    by (intros a Ha; apply HPRI; lia).

  (* ---- CRT_ENTRY: the prologue, `jal malloc` (crt_seg1_F) ---- *)
  assert (ESP0 : bv_unsigned (GR regs 2) = spZ regs) by reflexivity.
  assert (H10' : GR regs 10 = Z_to_bv 64 audio) by exact H10.
  assert (H11' : GR regs 11 = Z_to_bv 64 pcm) by exact H11.
  assert (H12' : GR regs 12 = Z_to_bv 64 nch) by exact H12.
  assert (H13' : GR regs 13 = Z_to_bv 64 ns) by exact H13.
  pose proof (crtB_stk_of (w_H W) memc (spZ regs - CRT_FRAME) (spZ regs) ltac:(lia) ltac:(lia) HFW0) as ST0.
  pose proof (crtB_rng_of_apresent W memc (spZ regs - CRT_FRAME) CRT_FRAME ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; apply HFW0; lia)) as RF0.
  pose proof (dec_cells_asan B HCELLS lyc Sc W memc mdc (w_Hoff W) HAR0) as CELLS0.
  eapply (crtB_run W regs memc mdc CRT_ENTRY).
  { unfold LCK3.ms_of_regs. rewrite H10', H11', H12', H13'. apply crtB_evtF_grows.
    exact (crt_seg1_F (LCK3.RNG_W (world segs) (@w_H segs) W)
      (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8) (GR regs 9)
      (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17) (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21)
      (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25) (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29)
      (GR regs 30) (GR regs 31)
      (@fp_regs fx) (@fp_csr fx) memc audio pcm nch ns (spZ regs - CRT_FRAME)
      ST0 ltac:(rewrite ESP0; lia) CELLS0
      ltac:(hnf; left; rewrite ESP0; unfold GOT_CELL_K, MIDEND; lia)
      Hnch Hns HAr HPr RF0
      (crtB_cell_rng W GOT_CELL_K 8 ltac:(crt_seg) ltac:(crt_top))
      (crtB_cell_rng W CELL_K 8 ltac:(crt_seg) ltac:(crt_top))). }
  intros ms1 md1 (ms0 & (HPs & HGROW1) & HEQ1) HSBM1.
  destruct HPs as (m1 & v0 & v8 & v16 & v32 & v40 & v48 & Ems & HMU1 & _ & _ & HFR1).
  subst ms0. cbn [ms_mem] in HGROW1.
  pose proof (@crtB_ms_shape fx _ _ _ ms1 HEQ1) as E1.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ ms1 r HEQ1) as RA.
  clear HEQ1.
  set (regsA := ms_regs ms1) in *.
  assert (A1 : GR regsA 1 = w64 (CRT_AT 0x68)) by (crtE_reg RA 1; reflexivity).
  assert (A2 : GR regsA 2 = Z_to_bv 64 (spZ regs - CRT_FRAME)) by (crtE_reg RA 2; reflexivity).
  assert (A3 : GR regsA 3 = GR regs 3) by (crtE_reg RA 3; reflexivity).
  assert (A4 : GR regsA 4 = GR regs 4) by (crtE_reg RA 4; reflexivity).
  assert (A8 : GR regsA 8 = Z_to_bv 64 (nch * ns)) by (crtE_reg RA 8; reflexivity).
  assert (A9 : GR regsA 9 = Z_to_bv 64 nch) by (crtE_reg RA 9; reflexivity).
  assert (A10 : GR regsA 10 = Z_to_bv 64 (4 * (nch * ns))) by (crtE_reg RA 10; reflexivity).
  assert (A18 : GR regsA 18 = Z_to_bv 64 ns) by (crtE_reg RA 18; reflexivity).
  assert (A19 : GR regsA 19 = Z_to_bv 64 (3 * (nch * ns))) by (crtE_reg RA 19; reflexivity).
  assert (A20 : GR regsA 20 = Z_to_bv 64 pcm) by (crtE_reg RA 20; reflexivity).
  assert (A24 : GR regsA 24 = Z_to_bv 64 ASAN_K) by (crtE_reg RA 24; reflexivity).
  clear RA.
  assert (HOUT1 : forall x : word, ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs) -> m1 x = memc x).
  { intros x Hx. apply HMU1. cbn [outside]. rewrite ESP0. split; [lia | exact I]. }
  pose proof (crtB_j_frame LAWS lyc Sc W memc mdc (spZ regs) lyc Sc W memc mdc 0 m1 md1 HJI HOUT1 HGROW1 HSBM1)
    as HJA.
  rewrite ESP0 in HFR1.
  pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRA & _ & _ & _).

  (* ---- malloc(4 nch ns) ---- *)
  rewrite E1.
  pose proof (crtE_ret 0x68 ltac:(lia)) as (UR1 & UR1b).
  assert (USA : spZ regsA = spZ regs - CRT_FRAME) by (apply crtE_spZ; [exact A2 | lia]).
  assert (U0A : s0Z regsA = nch * ns) by (apply crtE_s0Z; [exact A8 | lia]).
  apply (crtB_malloc_call HMAL RMAL fx W lyc Sc W memc mdc regs lyc Sc m1 md1 regsA 0 (4 * (nch * ns))
           (w64 (CRT_AT 0x68))).
  { exact HJA. }
  { exact A10. }
  { lia. }
  { lia. }
  { exact USA. }
  { exact Hsp16. }
  { exact (eq_trans A3 Hgp). }
  { exact (eq_trans A4 Htp). }
  { exact A1. }
  { unfold CRT_AT. vm_compute. reflexivity. }
  { rewrite UR1. exact UR1b. }
  { lia. }
  { rewrite U0A, USA. lia. }
  { rewrite UR1. exact HUM1. }
  { apply (mok_station MT Sc Sc T 0 _ HML Hmo (mle_start MT Sc HML)); lia. }
  intros W2 ly2 S2 regs2 mem2 md2 P HJ2 HPRES2 HP10 HFRS2 HP4096 HAB2 HKEPT2 HMO2.
  pose proof (crtB_frame_across W W2 lyc Sc m1 mem2 _ (spZ regs - CRT_FRAME) _ HKEPT2 HFR1 eq_refl
    ltac:(intros a Ha; apply HPRA; lia) ltac:(lia) ltac:(lia)) as HFR2.
  assert (R2_2 : GR regs2 2 = Z_to_bv 64 (spZ regs - CRT_FRAME)) by crtE_pres HPRES2 2 A2.
  assert (R2_3 : GR regs2 3 = GR regs 3) by crtE_pres HPRES2 3 A3.
  assert (R2_4 : GR regs2 4 = GR regs 4) by crtE_pres HPRES2 4 A4.
  assert (R2_8 : GR regs2 8 = Z_to_bv 64 (nch * ns)) by crtE_pres HPRES2 8 A8.
  assert (R2_9 : GR regs2 9 = Z_to_bv 64 nch) by crtE_pres HPRES2 9 A9.
  assert (R2_18 : GR regs2 18 = Z_to_bv 64 ns) by crtE_pres HPRES2 18 A18.
  assert (R2_19 : GR regs2 19 = Z_to_bv 64 (3 * (nch * ns))) by crtE_pres HPRES2 19 A19.
  assert (R2_20 : GR regs2 20 = Z_to_bv 64 pcm) by crtE_pres HPRES2 20 A20.
  assert (R2_24 : GR regs2 24 = Z_to_bv 64 ASAN_K) by crtE_pres HPRES2 24 A24.
  assert (R2_10 : GR regs2 10 = Z_to_bv 64 P) by exact HP10.
  assert (ESP2 : bv_unsigned (GR regs2 2) = spZ regs - CRT_FRAME) by (rewrite R2_2; apply unsigned_lit; lia).
  rewrite <- ESP2 in HFR2.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & HNEV2 & _ & _ & _ & _ & _ & _ & HPR2 & _ & _ & _).

  (* ---- CRT_RET_MALLOC1: P to 48(sp), nch to 40(sp), `jal malloc` (crt_seg2_F) ---- *)
  eapply (crtB_run W2 regs2 mem2 md2 CRT_RET_MALLOC1).
  { unfold LCK3.ms_of_regs. rewrite R2_9. apply crtB_evtF_grows. eapply crt_seg2_F.
    - lia.
    - exact HFR2.
    - rewrite ESP2. apply (crtB_rng_of_apresent W2 mem2); [lia | lia |]. intros a Ha. apply HPR2. lia. }
  intros msB mdB (ms0 & (HPs & HGROW2) & HEQB) HSBMB.
  destruct HPs as (m2 & EmsB & HMU2 & _ & HFRB).
  subst ms0. cbn [ms_mem] in HGROW2.
  pose proof (@crtB_ms_shape fx _ _ _ msB HEQB) as EB.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ msB r HEQB) as RB.
  clear HEQB.
  set (regsB := ms_regs msB) in *.
  assert (B1 : GR regsB 1 = w64 (CRT_AT 0x78)) by (crtE_reg RB 1; reflexivity).
  assert (B2 : GR regsB 2 = Z_to_bv 64 (spZ regs - CRT_FRAME)) by (transitivity (GR regs2 2); [crtE_same RB 2 | exact R2_2]).
  assert (B3 : GR regsB 3 = GR regs 3) by (transitivity (GR regs2 3); [crtE_same RB 3 | exact R2_3]).
  assert (B4 : GR regsB 4 = GR regs 4) by (transitivity (GR regs2 4); [crtE_same RB 4 | exact R2_4]).
  assert (B8 : GR regsB 8 = Z_to_bv 64 (nch * ns)) by (transitivity (GR regs2 8); [crtE_same RB 8 | exact R2_8]).
  assert (B10 : GR regsB 10 = Z_to_bv 64 (8 * nch)) by (crtE_reg RB 10; reflexivity).
  assert (B18 : GR regsB 18 = Z_to_bv 64 ns) by (transitivity (GR regs2 18); [crtE_same RB 18 | exact R2_18]).
  assert (B19 : GR regsB 19 = Z_to_bv 64 (3 * (nch * ns)))
    by (transitivity (GR regs2 19); [crtE_same RB 19 | exact R2_19]).
  assert (B20 : GR regsB 20 = Z_to_bv 64 pcm) by (transitivity (GR regs2 20); [crtE_same RB 20 | exact R2_20]).
  assert (B24 : GR regsB 24 = Z_to_bv 64 ASAN_K) by (transitivity (GR regs2 24); [crtE_same RB 24 | exact R2_24]).
  clear RB.
  assert (HOUT2 : forall x : word, ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs) -> m2 x = mem2 x).
  { intros x Hx. apply HMU2. cbn [outside]. rewrite ESP2. split; [lia | exact I]. }
  pose proof (crtB_j_frame LAWS lyc Sc W memc mdc (spZ regs) ly2 S2 W2 mem2 md2 (0 + 1) m2 mdB HJ2 HOUT2 HGROW2
    HSBMB) as HJB.
  rewrite ESP2 in HFRB.
  pose proof HJB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRB & _ & _ & _).
  assert (BB2 : blocks_bytes S2 = blocks_bytes Sc + 4 * (nch * ns)) by exact (crtE_bytes_add _ _ _ _ _ _ HAB2).

  (* ---- malloc(8 nch) ---- *)
  rewrite EB.
  pose proof (crtE_ret 0x78 ltac:(lia)) as (UR2 & UR2b).
  assert (USB : spZ regsB = spZ regs - CRT_FRAME) by (apply crtE_spZ; [exact B2 | lia]).
  assert (U0B : s0Z regsB = nch * ns) by (apply crtE_s0Z; [exact B8 | lia]).
  apply (crtB_malloc_call HMAL RMAL fx W2 lyc Sc W memc mdc regs ly2 S2 m2 mdB regsB (0 + 1) (8 * nch)
           (w64 (CRT_AT 0x78))).
  { exact HJB. }
  { exact B10. }
  { lia. }
  { lia. }
  { exact USB. }
  { exact Hsp16. }
  { exact (eq_trans B3 Hgp). }
  { exact (eq_trans B4 Htp). }
  { exact B1. }
  { unfold CRT_AT. vm_compute. reflexivity. }
  { rewrite UR2. exact UR2b. }
  { lia. }
  { rewrite U0B, USB. lia. }
  { rewrite UR2. exact HUM2. }
  { apply (mok_station MT Sc S2 T _ _ HML Hmo HMO2); lia. }
  intros W3 ly3 S3 regs3 mem3 md3 Q HJ3 HPRES3 HQ10 HFRS3 HQ4096 HAB3 HKEPT3 HMO3.
  pose proof (crtB_frame_across W2 W3 ly2 S2 m2 mem3 _ (spZ regs - CRT_FRAME) _ HKEPT3 HFRB eq_refl
    ltac:(intros a Ha; apply HPRB; lia) ltac:(lia) ltac:(lia)) as HFR3.
  assert (R3_2 : GR regs3 2 = Z_to_bv 64 (spZ regs - CRT_FRAME)) by crtE_pres HPRES3 2 B2.
  assert (R3_3 : GR regs3 3 = GR regs 3) by crtE_pres HPRES3 3 B3.
  assert (R3_4 : GR regs3 4 = GR regs 4) by crtE_pres HPRES3 4 B4.
  assert (R3_8 : GR regs3 8 = Z_to_bv 64 (nch * ns)) by crtE_pres HPRES3 8 B8.
  assert (R3_18 : GR regs3 18 = Z_to_bv 64 ns) by crtE_pres HPRES3 18 B18.
  assert (R3_19 : GR regs3 19 = Z_to_bv 64 (3 * (nch * ns))) by crtE_pres HPRES3 19 B19.
  assert (R3_20 : GR regs3 20 = Z_to_bv 64 pcm) by crtE_pres HPRES3 20 B20.
  assert (R3_24 : GR regs3 24 = Z_to_bv 64 ASAN_K) by crtE_pres HPRES3 24 B24.
  assert (R3_10 : GR regs3 10 = Z_to_bv 64 Q) by exact HQ10.
  assert (ESP3 : bv_unsigned (GR regs3 2) = spZ regs - CRT_FRAME) by (rewrite R3_2; apply unsigned_lit; lia).
  rewrite <- ESP3 in HFR3.
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & HNEV3 & _ & _ & _ & _ & _ & _ & HPR3 & _ & _ & _).

  (* ---- CRT_RET_MALLOC2: Q to s5, 3 nch ns to 16(sp), `bnez s0` taken, `jal calloc` (crt_seg3_F) ---- *)
  eapply (crtB_run W3 regs3 mem3 md3 CRT_RET_MALLOC2).
  { unfold LCK3.ms_of_regs. apply crtB_evtF_grows. eapply crt_seg3_F.
    - rewrite R3_8, (unsigned_lit (nch * ns)) by lia. lia.
    - exact HFR3.
    - rewrite ESP3. apply (crtB_rng_of_apresent W3 mem3); [lia | lia |]. intros a Ha. apply HPR3. lia. }
  intros msC mdC (ms0 & (HPs & HGROW3) & HEQC) HSBMC.
  destruct HPs as (m3 & EmsC & HMU3 & _ & HFRC).
  subst ms0. cbn [ms_mem] in HGROW3.
  pose proof (@crtB_ms_shape fx _ _ _ msC HEQC) as EC.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ msC r HEQC) as RC.
  clear HEQC.
  set (regsC := ms_regs msC) in *.
  assert (C1 : GR regsC 1 = w64 (CRT_AT 0x94)) by (crtE_reg RC 1; reflexivity).
  assert (C2 : GR regsC 2 = Z_to_bv 64 (spZ regs - CRT_FRAME)) by (transitivity (GR regs3 2); [crtE_same RC 2 | exact R3_2]).
  assert (C3 : GR regsC 3 = GR regs 3) by (transitivity (GR regs3 3); [crtE_same RC 3 | exact R3_3]).
  assert (C4 : GR regsC 4 = GR regs 4) by (transitivity (GR regs3 4); [crtE_same RC 4 | exact R3_4]).
  assert (C8 : GR regsC 8 = Z_to_bv 64 (nch * ns)) by (transitivity (GR regs3 8); [crtE_same RC 8 | exact R3_8]).
  assert (C10 : GR regsC 10 = Z_to_bv 64 (3 * (nch * ns)))
    by (transitivity (GR regs3 19); [crtE_same RC 10 | exact R3_19]).
  assert (C11 : GR regsC 11 = Z_to_bv 64 1) by (crtE_reg RC 11; reflexivity).
  assert (C18 : GR regsC 18 = Z_to_bv 64 ns) by (transitivity (GR regs3 18); [crtE_same RC 18 | exact R3_18]).
  assert (C20 : GR regsC 20 = Z_to_bv 64 pcm) by (transitivity (GR regs3 20); [crtE_same RC 20 | exact R3_20]).
  assert (C21 : GR regsC 21 = Z_to_bv 64 Q) by (transitivity (GR regs3 10); [crtE_same RC 21 | exact R3_10]).
  assert (C24 : GR regsC 24 = Z_to_bv 64 ASAN_K) by (transitivity (GR regs3 24); [crtE_same RC 24 | exact R3_24]).
  clear RC.
  assert (HOUT3 : forall x : word, ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs) -> m3 x = mem3 x).
  { intros x Hx. apply HMU3. cbn [outside]. rewrite ESP3. split; [lia | exact I]. }
  pose proof (crtB_j_frame LAWS lyc Sc W memc mdc (spZ regs) ly3 S3 W3 mem3 md3 (0 + 1 + 1) m3 mdC HJ3 HOUT3
    HGROW3 HSBMC) as HJC.
  rewrite ESP3, R3_19, R2_10 in HFRC.
  pose proof HJC as (_ & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRC & _ & _ & _).
  destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
  (* the stack-depth premise of the calloc rule: every journal step keeps ly_top (YG0f.v:65-68), so ly_bot *)
  assert (HBOT3 : ly_bot ly3 = ly_bot lyc) by (unfold ly_bot; rewrite Etop3; reflexivity).
  assert (EDF : DEC_CRT_FRAME = 160) by reflexivity.
  assert (BB3 : blocks_bytes S3 = blocks_bytes Sc + 4 * (nch * ns) + 8 * nch)
    by (rewrite (crtE_bytes_add _ _ _ _ _ _ HAB3), BB2; reflexivity).

  (* ---- calloc(3 nch ns, 1) ---- *)
  rewrite EC.
  pose proof (crtE_ret 0x94 ltac:(lia)) as (UR3 & UR3b).
  assert (USC : spZ regsC = spZ regs - CRT_FRAME) by (apply crtE_spZ; [exact C2 | lia]).
  assert (U0C : s0Z regsC = nch * ns) by (apply crtE_s0Z; [exact C8 | lia]).
  apply (crtB_calloc_call RCAL fx W3 lyc Sc W memc mdc regs ly3 S3 m3 mdC regsC (0 + 1 + 1) (3 * (nch * ns))
           (w64 (CRT_AT 0x94))).
  { exact HJC. }
  { rewrite HBOT3, USC. lia. }
  { exact C10. }
  { exact C11. }
  { lia. }
  { unfold DEC_CALLOC_MAX. lia. }
  { lia. }
  { exact USC. }
  { exact Hsp16. }
  { exact (eq_trans C3 Hgp). }
  { exact (eq_trans C4 Htp). }
  { exact C1. }
  { unfold CRT_AT. vm_compute. reflexivity. }
  { rewrite UR3. exact UR3b. }
  { lia. }
  { rewrite U0C, USC. lia. }
  { rewrite UR3. exact HUC. }
  { apply (mok_station MT Sc S3 T _ _ HML Hmo (mle_station MT Sc S2 S3 _ _ HML HMO2 HMO3)); lia. }
  intros W4 ly4 S4 regs4 mem4 md4 R HJ4 HPRES4 HR10 HFRS4 HR4096 HAB4 HKEPT4 HMO4.
  pose proof (crtB_frame_across W3 W4 ly3 S3 m3 mem4 _ (spZ regs - CRT_FRAME) _ HKEPT4 HFRC eq_refl
    ltac:(intros a Ha; apply HPRC; lia) ltac:(lia) ltac:(lia)) as HFR4.
  pose proof HJ4 as (_ & _ & _ & _ & _ & HFRJ4 & _).

  (* ---- land at CRT_RET_CALLOC ---- *)
  apply (CALLOC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly4 S4 W4 mem4 md4 regs4 P Q R v0 v8 v32).
  - exact HPRE.
  - split; [exact HJ4|]. split; [exact HFRJ4|]. split.
    + exact (mle_station MT Sc S3 S4 _ _ HML (mle_station MT Sc S2 S3 _ _ HML HMO2 HMO3) HMO4).
    + exact (crtB_rom_kept lyc Sc W memc mdc (spZ regs) ly4 S4 W4 mem4 md4 _ HSC HROM0 HJ4).
  - split; [change (GR regs4 2 = w64 (spZ regs - CRT_FRAME)); crtE_pres HPRES4 2 C2|].
    split; [change (GR regs4 3 = GR regs 3); crtE_pres HPRES4 3 C3|].
    split; [change (GR regs4 4 = GR regs 4); crtE_pres HPRES4 4 C4|].
    split; [change (GR regs4 18 = w64 ns); crtE_pres HPRES4 18 C18|].
    split; [change (GR regs4 21 = w64 Q); crtE_pres HPRES4 21 C21|].
    change (GR regs4 24 = w64 ASAN_K); crtE_pres HPRES4 24 C24.
  - exact HR10.
  - change (GR regs4 20 = w64 pcm); crtE_pres HPRES4 20 C20.
  - exact HFR4.
  - split; [rewrite HAB4, HAB3, HAB2; apply crtE_perm3|]. lia.
  - exact HFRM.
Qed.
End Entry.
