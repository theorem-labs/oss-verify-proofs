(* ctrl_lay_block (0x86104) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in cgif's
   CALLER-JOURNAL form (CONVENTIONS.md section 2 (a working note, not in this delivery); cgif lib/YC20.v:311-365 on origin/ossv/recipes
   c8557374ad2e, `tlzw_kept` / `tlzw_post` / `tlzw_spec`), because the call writes its caller's 32 bytes
   [p + 18, p + 50).  The image-B twin of a Theorem Labs lane's image-A file (a working branch b3f8a5cf908
   lib/A/Prog/C_ctrl_lay_block.v), kept GENERAL in its arguments (the B ctrl_emit_as draft consumes it at
   0x8572c with general p, f, md, g), under a Theorem Labs lane's B decisions
   (decisions.md items 1-17 (a working note, not in this delivery)).

   The statement.  Its proof, pb_ctrl_lay_block, is in lib/B/Prog/C_ctrl_lay_blockPb.v (see the end of this file).

   Provenance (lead's route-(a) condition): the run this contract is glued from is the proved B footprint run
   lib/B/Prog/ctrl_lay_blockF_on.v (`ctrl_lay_block_holds_F_on`, the _on copy of lib/B/Prog/ctrl_lay_blockF.v (not in this delivery), a Theorem Labs lane, relocated from a Theorem Labs lane's twin;
   statement lib/B/Prog/ctrl_lay_block_c.v `ctrl_lay_block_contract_F_on`).  The glue is modelled on cgif
   lib/A/AChf.v (a function with a side-stack frame) with the caller-journal shape of cgif lib/YC20.v:311-365.

   Segments: image B's core twin Reusable.YB1v.tfibsegs (decisions.md items 1, 16; planning core 9afb8c9070a); the
   link to the _F runs is ProgBridge.tfibsegs_rsegs.  The sink head stays a context until Reusable/YE2k.v is clear
   of refusal tokens (one-line marker below).

   Closure: core (lib/Reusable) and the shared model files (lib/Prog: RcModel RcBox RcSynth RcLay) only; no _F file,
   no frame-route file is Required by this statement.  Every identifier of the statement is core or model
   vocabulary. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v APostBase.
(* image B's read-only image vocabulary (IMG_LO / IMG_HI; the composer's globs_marked / img_shadow_vis), as in
   reac_box_model_block's statement *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo.
(* the function's model: the shared, address-free files (lib/Prog, not frame-route files) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry: a constant (decisions.md item 3 (a working note, not in this delivery)), = lib/B/Prog/ctrl_lay_block_c.v:11 CTRL_LAY_BLOCK and
   prog-plan-B.md (a working note, not in this delivery) (v1.9 asan-ubsan image; A twin 0x855f4). *)
Definition CTRL_LAY_BLOCK : Z := 0x86104. (* image-B address *)

(* The machine stack the call needs = the window of the proved B run that the glue re-uses (decisions.md item 4):
   CTRL_LAY_BLOCK_K = 4512 (lib/B/Prog/ctrl_lay_block_c.v:16), which is
   max(4240, 144 + K(__asan_stack_malloc_1) 208, 240 + max(K(__asan_memset) 2208, K(__asan_memcpy) 2224,
   K(reac_box_model_block) 4272)).  reac_box_model_block's 4272 is counted ONCE, inside that max (the earlier draft
   added it a second time).  It covers every cgif call of the glue: the class-1 request at SP2 >= S - 144 needs
   ESTACK below SP2 (S - 4240), reac_box_model_block at SP2 needs its own window 4272 (S - 4416), and the lifted
   __asan_memset / __asan_memcpy windows (2208 / 2224 at SP2).  ctrl_emit_as adds its 128 (CTRL_EMIT_AS_STK =
   Z.max 4640 (128 + CTRL_LAY_BLOCK_STK) = 4640). *)
Definition CTRL_LAY_BLOCK_STK : Z := 4512.

(* No allocator event: the class-1 request, reac_box_model_block's class-0 request and the inline flag release are
   fake-stack events, which keep st_nev (A twin: EV_LAY = EV_BMB = 0). *)
Definition EV_CTRL_LAY_BLOCK : Z := 0.

(* The caller's bytes the call writes: the 32-byte output block (ctrl_lay_block_c.v:19, ctrl_lay_block_W). *)
Definition tctrl_lay_block_out (p a : Z) : Prop := p + 18 <= a < p + 50.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.   (* := lib.Reusable.YE2k.tfib_sink_head once YE2k is clear of refusal tokens *)

Section d.
#[local] Notation SEGS := Reusable.YB1v.tfibsegs.
(* The read-only span of the RO premise (decisions.md item 17, cgif lib/YC20.v:56); the composer instantiates it
   with the B PA instance's pa_relro = [0x9f168, 0xa15e8) and discharges RELRO_IMG. *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.

Section e.
Variable B : asyms.              (* the composer instantiates B := Reusable.YF0m.CtrlB *)
(* The registered globals of the image (the composer's list, as reac_box_model_block's GLOBS). *)
Variable GLOBS : list (Z * Z).

(* A range of a registered read-only image global (reac_box_model_block's row / name form): inside one global of
   GLOBS, 64 bytes off the image ends (the instrumented checks read the shadow word cover), every byte read-only
   (in_roP) and neither allocator-owned nor errno.  The proof restates such a range's shadow at every AR state
   (CtrlRo.globs_marked, CtrlRo.img_shadow_vis: the composer's hypotheses) and its bytes by arodata_okS, so they
   survive __asan_stack_malloc_1 and reac_box_model_block, whose posts keep no allocator-owned shadow byte.
   ctrl's call: f a CTRL_FRAMES row, md a BOX_CATALOGUE row (both PT_GNU_RELRO), the name a .rodata string global. *)
Definition tctrl_lay_block_ro (q n : Z) : Prop :=
  (exists q0 sz, In (q0, sz) GLOBS /\ q0 <= q /\ q + n <= q0 + sz) /\
  CtrlRo.IMG_LO + 64 <= q /\ q + n + 64 <= CtrlRo.IMG_HI /\
  (forall x, q <= x < q + n -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).

(* Caller forms: a range inside one listed global whose bytes are all read-only, neither owned nor errno; and a
   sub-range of such a range. *)
Lemma tctrl_lay_block_ro_of_glob : forall q0 sz q n,
  In (q0, sz) GLOBS -> q0 <= q -> q + n <= q0 + sz ->
  CtrlRo.IMG_LO + 64 <= q -> q + n + 64 <= CtrlRo.IMG_HI ->
  (forall x, q0 <= x < q0 + sz -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  tctrl_lay_block_ro q n.
Proof.
  intros q0 sz q n Hin H1 H2 H3 H4 H5. split; [exists q0, sz; auto|]. split; [exact H3|]. split; [exact H4|].
  intros x Hx. apply H5. lia.
Qed.

Lemma tctrl_lay_block_ro_sub : forall q n q' n',
  tctrl_lay_block_ro q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' -> tctrl_lay_block_ro q' n'.
Proof.
  intros q n q' n' ((q0 & sz & Hin & H1 & H2) & H3 & H4 & H5) Hq Hn Hn'.
  split; [exists q0, sz; split; [exact Hin | lia]|]. split; [lia|]. split; [lia|].
  intros x Hx. apply H5. lia.
Qed.

(* Where a byte the call writes may lie (each byte separately): a static image byte that is neither
   allocator-owned nor errno, a byte of a live heap block of the caller's state, or a byte of a frame of class 2 or
   more of the caller's state.  These are exactly the classes that acall_kept keeps across the call's own callees
   (YCbq.v:824-835; B ProgWorld kept_class), so the glue carries the bytes from memc across __asan_stack_malloc_1 and
   reac_box_model_block; the class-0 and class-1 side-stack regions, which those callees take, are excluded.
   ctrl's call: the output block p + 18 is in LLVMFuzzerTestOneInput's class-6 frame. *)
Definition tctrl_lay_block_home (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
    (exists b m i, In (b, m) (ablocks B lyc Sc) /\ 0 <= i < req_size m /\ a = b + i) \/
    (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ in_zr a (frame_rng lyc (cid, pos))).

(* Every byte a home admits lies below the run's allocator ceiling (YM05's, the one acall_kept's high-memory
   clause reads): image bytes are below 0x5fe000, live blocks end at or below the ceiling (AR_blocks_law), and the
   caller's side-stack frames too (AR_sep_law).  So acall_kept's high-memory clause never constrains the output
   block, and the frame / block clauses, which exempt E, are the ones that apply to it. *)
Lemma tctrl_lay_block_img_low : forall a, in_img SEGS a -> 0 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & Hr).
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) SEGS))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) SEGS sg Hin).
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.

Lemma tctrl_lay_block_home_below : AR_laws SEGS B ->
  forall lyc Sc (W : world SEGS) m md q n,
  AR SEGS B lyc Sc W m md -> tctrl_lay_block_home lyc Sc q n ->
  forall a, q <= a < q + n -> a < alloc_ceiling.
Proof.
  intros LAWS lyc Sc W m md q n HAR Hh a Ha.
  pose proof (proj1 (@alloc_ceiling_value rc)) as [CV _].
  destruct (Hh a Ha) as [(Himg & _ & _) | [(b & m0 & i & Hin & Hi & ->) | (cid & pos & Hin & _ & Hr)]].
  - pose proof (tctrl_lay_block_img_low a Himg) as HL. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m0 HAR Hin) as (_ & _ & Hb & _). lia.
  - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HF). rewrite Forall_forall in HF.
    specialize (HF (cid, pos) Hin). cbn [fst snd] in HF.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
Qed.

(* Discharge forms for a caller (ctrl_emit_as, ACtlW2a, C_reac_ctrl_build_as): a range inside ONE frame of class 2 or
   more of the caller's state; a range of image bytes apart from the bundle's owned statics and errno; a range inside
   one live block. *)
Lemma tctrl_lay_block_home_frame : forall lyc Sc q n cid pos,
  In (cid, pos) (frames Sc) -> 2 <= cid ->
  (forall a, q <= a < q + n -> in_zr a (frame_rng lyc (cid, pos))) ->
  tctrl_lay_block_home lyc Sc q n.
Proof. intros lyc Sc q n cid pos Hin Hc Hr a Ha. right; right. exists cid, pos. auto. Qed.

Lemma tctrl_lay_block_home_img : forall lyc Sc q n,
  (forall a, q <= a < q + n -> in_img SEGS a) ->
  (forall a, q <= a < q + n -> ~ Exists (in_zr a) (as_owned_static B)) ->
  q + n <= as_errno B \/ as_errno B + 4 <= q ->
  tctrl_lay_block_home lyc Sc q n.
Proof.
  intros lyc Sc q n Himg Hown Herr a Ha. left.
  split; [exact (Himg a Ha)|]. split; [exact (Hown a Ha)|]. lia.
Qed.

Lemma tctrl_lay_block_home_block : forall lyc Sc q n b m,
  In (b, m) (ablocks B lyc Sc) -> b <= q -> q + n <= b + req_size m ->
  tctrl_lay_block_home lyc Sc q n.
Proof.
  intros lyc Sc q n b m Hin Hb He a Ha. right; left. exists b, m, (a - b).
  split; [exact Hin|]. split; lia.
Qed.

(* What the call leaves (cgif tlzw_post shape): the same journal, callee-saved registers, the caller's frames and
   blocks, the output block as the proved run's post says (ctrl_lay_block_c.v:250-251), and acall_kept: every
   byte outside the call's own window [sp - CTRL_LAY_BLOCK_STK, sp) and outside [p + 18, p + 50) is kept,
   INCLUDING the bytes and shadow of the caller's frames (acall_kept's frame clause, YCbq.v:831-833). *)
Definition tctrl_lay_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p md g : Z) (fr tb mb nb gb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CTRL_LAY_BLOCK) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18)
      (map (fun x : byte => bv_unsigned x)
         (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)) /\
    acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (tctrl_lay_block_out p).

(* The contract.  The premises are the proved run's (ctrl_lay_block_c.v:160-238) read through the world: a byte
   read is `garr8` over `mrestrict (w_H W)`, an addressable range is `range_addressable` over `aview`, the 8-aligned
   shadow word cover the instrumented checks load (`sh_cover`) is `shadow_hull_vis`; the runtime's cells, the
   shadow map, the side stack and the thread cells come from the journal's AR, not from premises. *)
Definition tctrl_lay_block_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p f md g : Z) (fr tb mb nb gb : list byte),
  (* the caller's journal (YC20.v:349) and the read-only image (decisions.md items 2, 17) *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  (* the arguments: a0 = p, a1 = f, a2 = md, a3 = g.  No achain premise (decisions.md item 5, exception 00:05Z):
     the glue does not consume a frame chain, and cgif's astack_malloc_realizes does not need one. *)
  getr regs 10 = w64 p -> getr regs 11 = w64 f -> getr regs 12 = w64 md -> getr regs 13 = w64 g ->
  0 <= p < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> 0 <= md < 2 ^ 64 -> 0 <= g < 2 ^ 64 ->
  (* the stack: the call's window lies in the caller's journal window *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CTRL_LAY_BLOCK_STK -> spZ regs <= sp0 ->
  (* room for the call's class-1 frame (__asan_stack_malloc_1, jal at 0x86178) and for reac_box_model_block's class-0
     frame (YG0d.v:287, astack_malloc_realizes; count_cid ignores other classes, YG01.v:215) *)
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  (* the output block [p + 18, p + 50): the caller's right to let the call write it and its presence
     (YC20.v:358-359), its home, its shadow; p <> 0 and the wrap check are the B traps at 0x86218 / 0x86220 *)
  p <> 0 -> p + 50 <= 2 ^ 64 ->
  (forall a, p + 18 <= a < p + 50 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  tctrl_lay_block_home lyc Sc (p + 18) 32 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 ->
  (forall a, p + 18 <= a <= p + 50 -> app_addr a) ->
  (* the 24-byte record f, read with checks *)
  f mod 8 = 0 -> length fr = 24%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) f (map (fun x : byte => bv_unsigned x) fr) ->
  tctrl_lay_block_ro f 24 ->
  ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
  (* k = 2: the 32-byte template, read-only image bytes (the proved run's ro_bytes) *)
  (ly_k fr = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) (ly_tm fr) (map (fun x : byte => bv_unsigned x) tb) /\
     tctrl_lay_block_ro (ly_tm fr) 32 /\
     (forall a, ly_tm fr <= a < ly_tm fr + 32 ->
        exists s, In s SEGS /\ seg_writable s = false /\
          Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))) ->
  (* k = 3 .. 9, md <> 0: the 296-byte model record reac_box_model_block reads, and for b = 5 / 6 its name *)
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb) /\
     tctrl_lay_block_ro md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        tctrl_lay_block_ro (rname mb) (Z.of_nat (length nb)))) ->
  (* g <> 0, al <> 0: the al bytes __asan_memcpy copies to p + 18 + ao (its aligned-word check reads to + 7) *)
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\
     garr8 SEGS (mrestrict (w_H W) memc) g (map (fun x : byte => bv_unsigned x) gb) /\
     tctrl_lay_block_ro g (ly_al fr) /\
     app_addr (g + ly_al fr) /\ app_addr (g + 7) /\ app_addr (p + 25 + ly_ao fr)) ->
  (* the apartness the caller checked (ctrl_lay_block_c.v:169-186), over the call's window *)
  ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (p + 18) (p + 50) ->
  ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (ly_tm fr) (ly_tm fr + 32)) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) g (g + ly_al fr)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
  ly_dj (p + 18) (p + 50) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
     ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
  SRr SEGS W (cfg_at SEGS CTRL_LAY_BLOCK regs memc mdc)
    (tctrl_lay_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g fr tb mb nb gb).

End e.
End d.
End b.

(* The proof: pb_ctrl_lay_block : tctrl_lay_block_spec RLO RHI B GLOBS, in lib/B/Prog/C_ctrl_lay_blockPb.v (Qed).
   It chains the region lemmas lay_to_ret (ctrl_lay_block_gR1.v), lay_R23 (ctrl_lay_block_gR23.v), lay_box_arm
   (ctrl_lay_block_gbox.v), lay_R3 (ctrl_lay_block_gR3.v) and lay_R4 (ctrl_lay_block_gR4.v), which lift the cut lemmas
   of ctrl_lay_block_cutsF.v; plan of record analyses/libreac/fuzz_ctrl/glue-B/ctrl_lay_block-B-glue-plan.md.
   The a0 = 0 arm of the class-1 request is DEAD in cgif form: astack_malloc_realizes (cgif lib/YG0d.v:284-299)
   takes the room premise count_cid 1 (frames S) < fs_frames 1 and its post always gives a0 = frame_addr; so the
   real-stack fallback of ctrl_lay_blockF.v (ly_epi_real) is not used by the glue. *)
