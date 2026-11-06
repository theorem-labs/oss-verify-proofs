(* ctrl_emit_as (0x853c4) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in cgif's
   CALLER-JOURNAL form (CONVENTIONS.md section 2 (a working note, not in this delivery); cgif lib/YC20.v:311-365 on origin/ossv/recipes
   c8557374ad2e), because the call writes its caller's output [o, o + len) (an object of a caller frame) besides its own
   128-byte machine-stack frame.  It takes no fake frame itself.  Draft of record:
   ctrl_emit_as-B-draft.md section 2.1 (a working note, not in this delivery), under a Theorem Labs lane's B
   decisions (decisions.md items 1-29 (a working note, not in this delivery)): segment term Reusable.YB1v.tfibsegs (item 16 / a Theorem Labs lane 03:06Z),
   read-only premise arodata_okS over B's RELRO span (item 2), entry pc a constant (item 3), window
   Z.max 4640 (128 + CTRL_LAY_BLOCK_STK) (item 4), general arguments (item 9).  The sink head is a Context
   {SK : sink_head}: no step needs SK = Reusable.YE2k.tfib_sink_head, so a caller at any sink head can use the
   contract (a Theorem Labs lane's request, a Theorem Labs lane 08:2xZ).  The modules that exist both in lib/Reusable and in
   lib/B/Reusable are named qualified (a Theorem Labs lane 04:03Z); only the core's are Imported.

   Differences from the draft text, each forced by the consumed ctrl_lay_block contract of record
   (a working branch 079649851ae, C_ctrl_lay_block.v) or by the proved run's premises
   (ctrl_emit_asF.v, a Theorem Labs lane e7748203ba4):
   - f 24, md 296, the name and the template are ranges of registered read-only image globals:
     `tctrl_emit_as_ro q n`, word for word ctrl_lay_block's tctrl_lay_block_ro over the same list GLOBS (one global
     of GLOBS, 64 bytes off the image ends, every byte in_roP, neither allocator-owned nor errno; a Theorem Labs lane
     08:37Z).  Their shadow at every AR state then comes from the composer's CtrlRo.globs_marked SEGS B GLOBS (a
     Section hypothesis of the glue) and CtrlRo.img_shadow_vis SEGS B (proved: ACtlCutC.ctrl_img_shadow_vis), their
     bytes from arodata_okS; the template keeps
     its per-byte non-writable-segment conjunct (the run's ro_bytes);
   - d 6, s 6 carry `shadow_hull_vis`, `in_app` and `tctrl_emit_as_home` (apart from the side stack for frames, or
     inside one caller frame of class 2 or more);
   - g is 0 (a7 = 0), as in A's spec (lib/A/Prog/C_ctrl_emit_as.v (at head lib/A/Prog/C_ctrl_emit_as.v:157; from a working branch 9fabd8a4264);
     a Theorem Labs lane 08:05Z, replacing a decision of decisions.md (a working note, not in this delivery)): the post is taken at g = 0, gb = [];
   - the output's caller frame has class 2 or more, and the output carries `shadow_hull_vis`; the 1492-byte buffer
     at o lies in one caller frame of class 2 or more also when nothing is emitted (E = false; A's twin premise,
     A C_ctrl_emit_as.v:173-174): the proved run's fp premise lists the range (o, o + R) among its write and data
     ranges, and for R = 0 its apartness from the thread cells and the class-0/1 bytes needs it;
   - the template clause (ly_k row = 2) is ctrl_lay_block's (a registered read-only global, non-writable segment);
   - no JOIN premise: the JOIN blocks are read inside ctrl_lay_block, whose contract owns them.

   Closure of the statement: core (lib/Reusable), the shared address-free model files (lib/Prog) and image B's
   read-only vocabulary lib/B/Prog/CtrlRo.v (IMG_LO / IMG_HI), as ctrl_lay_block's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK11 YK1b YI04 YI16 YM05 APostBase.
(* image B's read-only image vocabulary (IMG_LO / IMG_HI; the composer's globs_marked / img_shadow_vis) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo.
(* the function's model: the shared, address-free files *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay RcFin RcEmit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry: a constant (decisions.md item 3); = lib/B/Prog/ctrl_emit_as_c.v:11 (A twin 0x849d8). *)
Definition CTRL_EMIT_AS : Z := 0x853c4.

(* The stack the call needs (decisions.md item 4): the proved run's window CTRL_EMIT_AS_K = 4640 = 128 + 4512
   (ctrl_emit_as_c.v:14) and 128 + ctrl_lay_block's CTRL_LAY_BLOCK_STK = 4512 (C_ctrl_lay_block.v, 33d01bf4f85). *)
Definition CTRL_EMIT_AS_STK : Z := Z.max 4640 (128 + 4512).

(* No allocator event: no malloc / free; the fake-stack events are ctrl_lay_block's and keep st_nev. *)
Definition EV_CTRL_EMIT_AS : Z := 0.

(* The caller's bytes the call writes: the output [o, o + R). *)
Definition tctrl_emit_as_out (o R a : Z) : Prop := o <= a < o + R.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* Where a range the run reads may lie (A's twin): apart from the side stack for frames [ly_F, ly_F + kFakeStackSize),
   or inside ONE frame of the caller's state of class 2 or more. *)
Definition tctrl_emit_as_home (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  ly_dj (ly_F lyc) (ly_F lyc + kFakeStackSize) q (q + n) \/
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\
     forall a, q <= a < q + n -> in_zr a (frame_rng lyc (cid, pos))).

Section e.
(* The read-only span [RLO, RHI) the caller's arodata_okS speaks of (the B top's instance is [0x9f1a0, 0xa15e8),
   a Theorem Labs lane relaying a Theorem Labs lane); a parameter, as in ctrl_lay_block's spec, so the contract holds at any span. *)
Variables RLO RHI : Z.
Variable B : asyms.
(* The registered globals of the image (the composer's list; the same GLOBS as ctrl_lay_block's and
   reac_box_model_block's). *)
Variable GLOBS : list (Z * Z).

(* A range of a registered read-only image global: word for word ctrl_lay_block's tctrl_lay_block_ro RLO RHI B GLOBS
   (079649851ae). *)
Definition tctrl_emit_as_ro (q n : Z) : Prop :=
  (exists q0 sz, In (q0, sz) GLOBS /\ q0 <= q /\ q + n <= q0 + sz) /\
  CtrlRo.IMG_LO + 64 <= q /\ q + n + 64 <= CtrlRo.IMG_HI /\
  (forall x, q <= x < q + n -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).

Definition tctrl_emit_as_E (row mb : list byte) (n : Z) : bool := em_E (ubat row 21) (ubat row 22) n (em_hid mb).
Definition tctrl_emit_as_len (row : list byte) (n : Z) : Z := em_len (ubat row 21) n.
Definition tctrl_emit_as_R (row mb : list byte) (n : Z) : Z :=
  if tctrl_emit_as_E row mb n then tctrl_emit_as_len row n else 0.
Definition tctrl_emit_as_lay (row tb mb nb gb : list byte) (md g : Z) : list byte :=
  ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb.
Definition tctrl_emit_as_blk (row tb mb nb gb : list byte) (md g : Z) : list byte :=
  fin (ubat row 20) (ubat row 18) (ubat row 19) (tctrl_emit_as_lay row tb mb nb gb md g).
Definition tctrl_emit_as_nm (row mb : list byte) : Prop :=
  (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\ rname mb <> 0.

(* What the call leaves (cgif tlzw_post shape): the same journal, callee-saved registers, the caller's frames and
   blocks, a0 = R, the output (when E) as the proved run's post says (ctrl_emit_as_c.v:239-248), and acall_kept over
   the call's window and the output. *)
Definition tctrl_emit_as_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o md g n : Z) (row tb mb nb gb db sb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr regs 1) mem2
                  (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CTRL_EMIT_AS) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    lib.Reusable.YK11.getr regs2 10 = w64 (tctrl_emit_as_R row mb n) /\
    (tctrl_emit_as_E row mb n = true ->
       garr8 SEGS (mrestrict (w_H W2) mem2) o
         (map (fun x : byte => bv_unsigned x)
            (em_fr db sb (bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536)
               (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0))
               (tctrl_emit_as_blk row tb mb nb gb md g) (tctrl_emit_as_len row n))) /\
       (ubat row 21 <> 2 -> em_wok n = true) /\
       (ubat row 20 = 1 \/ ubat row 20 = 2 ->
          closes (ubat row 20) (ubat row 18) (ubat row 19) (tctrl_emit_as_blk row tb mb nb gb md g) /\
          (closes (ubat row 20) (ubat row 18) (ubat row 19) (tctrl_emit_as_lay row tb mb nb gb md g) ->
           tctrl_emit_as_blk row tb mb nb gb md g = tctrl_emit_as_lay row tb mb nb gb md g))) /\
    acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - CTRL_EMIT_AS_STK) (spZ regs)
      (tctrl_emit_as_out o (tctrl_emit_as_R row mb n)).

(* The contract.  The premises are the proved run's (ctrl_emit_as_c.v:152-228) read through the world: a byte read is
   `garr8` over `mrestrict (w_H W)`, an addressable range is `range_addressable` over `aview`; the runtime's cells,
   the shadow map, the side stack and the thread cells come from the journal's AR, not from premises. *)
Definition tctrl_emit_as_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (o f md d s n ns : Z) (row tb mb nb db sb : list byte),
  let E := tctrl_emit_as_E row mb n in
  let len := tctrl_emit_as_len row n in
  let Lo := spZ regs - CTRL_EMIT_AS_STK in
  let rd := aview SEGS (w_H W) memc in
  let mr := mrestrict (w_H W) memc in
  (* the caller's journal (YC20.v:349) and the read-only image (decisions.md item 2) *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI rd ->
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= raZ regs ->
  lib.Reusable.YK11.getr regs 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
  (* the arguments: a0 = o, a1 = f, a2 = md, a3 = d, a4 = s, a6 = n, a7 = 0 (g), t4 (x29) = ns; a5 carries the
     16-bit header word (read in the post), t3 (x28) is passed on to reac_braid_encode unread *)
  lib.Reusable.YK11.getr regs 10 = w64 o -> lib.Reusable.YK11.getr regs 11 = w64 f ->
  lib.Reusable.YK11.getr regs 12 = w64 md -> lib.Reusable.YK11.getr regs 13 = w64 d ->
  lib.Reusable.YK11.getr regs 14 = w64 s -> lib.Reusable.YK11.getr regs 16 = w64 n ->
  lib.Reusable.YK11.getr regs 17 = w64 0 -> lib.Reusable.YK11.getr regs 29 = w64 ns ->
  -2^31 <= n < 2^31 -> -2^31 <= ns < 2^31 ->
  (* the stack: the call's window lies in the caller's journal window *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CTRL_EMIT_AS_STK -> spZ regs <= sp0 ->
  (* room for ctrl_lay_block's class-1 frame and reac_box_model_block's class-0 frame (YG01.v:215) *)
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  (* the 24-byte row, read with checks; B-only: f <> 0 (trap 0x853fc) and f mod 8 = 0 (trap 0x85408) *)
  f <> 0 -> f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat ->
  garr8 SEGS mr f (map (fun x : byte => bv_unsigned x) row) -> tctrl_emit_as_ro f 24 ->
  ly_k row <= 9 -> ubat row 20 <= 2 -> ubat row 21 <= 2 -> ubat row 22 <= 1 -> ubat row 23 <= 1 ->
  ly_ao row + ly_al row <= 32 ->
  (ubat row 20 = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
  (ubat row 21 = 2 -> ubat row 23 = 0) -> (ubat row 23 = 1 -> ns <= 0) ->
  (* k = 2: the 32-byte template, a registered read-only global in a non-writable segment (C_ctrl_lay_block.v's
     clause) *)
  (ly_k row = 2 ->
     ly_tm row + 32 <= 2 ^ 64 /\ length tb = 32%nat /\
     garr8 SEGS mr (ly_tm row) (map (fun x : byte => bv_unsigned x) tb) /\
     tctrl_emit_as_ro (ly_tm row) 32 /\
     (forall a, ly_tm row <= a < ly_tm row + 32 ->
        (exists s, In s SEGS /\ seg_writable s = false /\
           Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) /\
        ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))) ->
  (* the model record (md <> 0: the BOX_CATALOGUE search 0x85494 is not entered); B-only md mod 8 = 0 (traps
     0x85560, 0x8558c) *)
  md <> 0 -> md mod 8 = 0 -> md + 296 <= 2^64 -> length mb = 296%nat ->
  garr8 SEGS mr md (map (fun x : byte => bv_unsigned x) mb) -> tctrl_emit_as_ro md 296 ->
  (tctrl_emit_as_nm row mb ->
     name_ok nb /\ rname mb + Z.of_nat (length nb) <= 2 ^ 64 /\
     garr8 SEGS mr (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
     tctrl_emit_as_ro (rname mb) (Z.of_nat (length nb))) ->
  (* the two 6-byte headers copied by __asan_memcpy; the aligned-word check reads up to + 7 *)
  length db = 6%nat -> garr8 SEGS mr d (map (fun x : byte => bv_unsigned x) db) ->
  range_addressable rd SHADOW_OFF d 6 -> shadow_hull_vis rd d 6 -> in_app d 6 -> tctrl_emit_as_home lyc Sc d 6 ->
  app_addr (d + 6) -> app_addr (d + 7) ->
  length sb = 6%nat -> garr8 SEGS mr s (map (fun x : byte => bv_unsigned x) sb) ->
  range_addressable rd SHADOW_OFF s 6 -> shadow_hull_vis rd s 6 -> in_app s 6 -> tctrl_emit_as_home lyc Sc s 6 ->
  app_addr (s + 6) -> app_addr (s + 7) ->
  (* the output: B-only o > 0 and o + 1492 <= 2^64 (overflow / null traps 0x85640 .. 0x857a8) *)
  0 < o -> o + 1492 <= 2^64 ->
  (* the output's home, also when E = false (the twin of A's C_ctrl_emit_as.v:173-174, its p := o) *)
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= o /\
                   o + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (E = true ->
     (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\
        forall a, o <= a < o + len -> in_zr a (frame_rng lyc (cid, pos))) /\
     (forall a, o <= a < o + len ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
     range_addressable rd SHADOW_OFF o len /\ shadow_hull_vis rd o len /\ app_addr (o + len)) ->
  (* the apartness the caller checked (ctrl_emit_as_c.v:174-177, :187-193), over the window [Lo, sp) *)
  ly_dj Lo (spZ regs) f (f + 24) -> ly_dj Lo (spZ regs) md (md + 296) ->
  ly_dj Lo (spZ regs) d (d + 6) -> ly_dj Lo (spZ regs) s (s + 6) ->
  (ly_k row = 2 -> ly_dj Lo (spZ regs) (ly_tm row) (ly_tm row + 32)) ->
  (tctrl_emit_as_nm row mb -> ly_dj Lo (spZ regs) (rname mb) (rname mb + Z.of_nat (length nb))) ->
  (E = true ->
     ly_dj Lo (spZ regs) o (o + len) /\ ly_dj o (o + len) f (f + 24) /\ ly_dj o (o + len) md (md + 296) /\
     ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6) /\
     (ly_k row = 2 -> ly_dj o (o + len) (ly_tm row) (ly_tm row + 32)) /\
     (tctrl_emit_as_nm row mb -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
  SRr SEGS W (cfg_at SEGS CTRL_EMIT_AS regs memc mdc)
    (tctrl_emit_as_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o md 0 n row tb mb nb [] db sb).
End e.
End b.

(* =================================================================================================================
   The glue (pb_ctrl_emit_as, at the end of the file).  The proof-internal lemmas below name ctrl's frame-route
   vocabulary QUALIFIED (decisions.md item 15): lib.Lib.* (the run world), lib.B.* (image B's runtime, normalization,
   ProgBridge) and the _F file lib.B.Prog.ctrl_emit_asF, which is Required, never Imported (glue closure rule).
   ================================================================================================================= *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04R YA0nR YK14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame
  lib.Lib.Cells lib.Lib.Step lib.Lib.ExecF lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.B.Img0 lib.B.AsanRT lib.B.MemNorm lib.B.MemNormF
  lib.B.MemNormTr lib.B.ProgBridge lib.B.Prog.ImgBounds lib.B.Prog.RcAsanFP lib.B.Prog.asan_stack_malloc_c
  lib.B.Prog.ctrl_emit_as_c lib.B.Prog.ctrl_emit_asF.

(* lib/Reusable/YM05.v:63 redefines `lia` globally to a pruning tactic (`Ltac Lia.lia ::= rc_inst; ...`), which
   drops the hypotheses a chain through an intermediate variable needs and then fails with "No applicable tactic".
   `rlia` is the untuned one, as ctrl_emit_asF.v:496 writes it. *)
#[local] Ltac rlia := Z.div_mod_to_equations; Zify.zify; xlia zchecker.

Section g1. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
#[local] Notation RS := lib.B.Img0.rsegs.

(* Every segment byte of image B lies in [0x10000, 0x5fe000) (ProgBridge.rsegs_spans). *)
Lemma ce_seg_lo_hi : forall sg a, In sg SEGS ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> 0x10000 <= a < 0x5fe000.
Proof.
  intros sg a Hin Hr.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
            (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) RS))
    by (apply (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s)))); exact Hin).
  rewrite lib.B.ProgBridge.rsegs_spans in H.
  cbn [In] in H. destruct H as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma ce_not_img : forall a, 0x5fe000 <= a \/ a < 0x10000 -> ~ in_img SEGS a.
Proof. intros a Ha (sg & Hin & Hr). pose proof (ce_seg_lo_hi sg a Hin Hr). lia. Qed.

Lemma ce_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Proof. intros a (sg & Hin & Hr). pose proof (ce_seg_lo_hi sg a Hin Hr). unfold kLowMemEnd. lia. Qed.

Lemma ce_rom_none : forall a, 0 <= a < 2 ^ 64 -> (0x5fe000 <= a \/ a < 0x10000) ->
  lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 a) = None.
Proof. intros a Ha Hh. apply seg_rom_none; [exact Ha | apply ce_not_img; exact Hh]. Qed.

(* A byte the world's reader serves: either a visible byte of the memory, or (never hidden) a segment byte. *)
Lemma ce_mbyte_vis : forall (W : world SEGS) (m : word -> option byte) (x : Z) (b : byte),
  mbyte SEGS (mrestrict (w_H W) m) x = Some b ->
  w_H W (Z_to_bv 64 x) = false /\ lib.Lib.Mem.mrd RS m (Z_to_bv 64 x) = Some b.
Proof.
  intros W m x b H. unfold mbyte, mrestrict in H.
  destruct (w_H W (Z_to_bv 64 x)) eqn:Eh.
  - exfalso. pose proof (w_Hoff W _ Eh) as Hoff.
    unfold lib.Reusable.YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite Hoff in H. discriminate H.
  - split; [reflexivity|]. unfold lib.Lib.Mem.mrd. exact H.
Qed.

Lemma ce_le_byte1 : forall b : byte, Z_to_bv 8 (lib.Reusable.YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold lib.Reusable.YO0f.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite !Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* The world's byte array reads as ctrl's bytes_at, and every byte of it is visible. *)
Lemma ce_bytes_of_garr8 : forall (W : world SEGS) (m : word -> option byte) (q : Z) (bs : list byte),
  0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) q (map (fun x : byte => bv_unsigned x) bs) ->
  lib.Lib.Mem.bytes_at RS m q bs /\
  (forall i, (i < length bs)%nat -> w_H W (Z_to_bv 64 (q + Z.of_nat i)) = false).
Proof.
  intros W m q bs Hq Hb HG.
  assert (K : forall i, (i < length bs)%nat ->
            w_H W (Z_to_bv 64 (q + Z.of_nat i)) = false /\
            lib.Lib.Mem.mrd RS m (Z_to_bv 64 (q + Z.of_nat i)) = nth_error bs i).
  { intros i Hi.
    destruct (nth_error bs i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    assert (Hi' : (i < length (map (fun x : byte => bv_unsigned x) bs))%nat) by (rewrite length_map; exact Hi).
    destruct (HG i Hi') as [HV _]. specialize (HV 0%nat ltac:(lia)).
    rewrite (nth_error_nth _ _ _ (map_nth_error (fun x : byte => bv_unsigned x) _ _ Eb)) in HV.
    rewrite ce_le_byte1 in HV. replace (q + Z.of_nat i + Z.of_nat 0) with (q + Z.of_nat i) in HV by lia.
    exact (ce_mbyte_vis W m _ b HV). }
  split; [|intros i Hi; exact (proj1 (K i Hi))].
  split; [exact Hq|]. split; [exact Hb|]. intros i Hi. exact (proj2 (K i Hi)).
Qed.

(* ... and back: visible bytes of the memory are the world's byte array. *)
Lemma ce_garr8_of_bytes : forall (H : word -> bool) (m : word -> option byte) (q : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at RS m q bs ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (q + Z.of_nat i)) = false) ->
  garr8 SEGS (mrestrict H m) q (map (fun x : byte => bv_unsigned x) bs).
Proof.
  intros H m q bs (Hq & Hb & HB) HV j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  rewrite (nth_error_nth _ _ _ (map_nth_error (fun x : byte => bv_unsigned x) _ _ Eb)).
  split; [|pose proof (bv_unsigned_in_range 8 b) as R; change (bv_modulus 8) with 256 in R; lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite ce_le_byte1.
  replace (q + Z.of_nat j + Z.of_nat 0) with (q + Z.of_nat j) by lia.
  pose proof (HB j Hj) as E. rewrite Eb in E. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in E.
  unfold mbyte, mrestrict. rewrite (HV j Hj). exact E.
Qed.

(* The world's view of a visible shadow byte is the memory's byte. *)
Lemma ce_view_shadow : forall (W : world SEGS) (m : word -> option byte) (x v : Z),
  0 <= x < 2 ^ 64 -> 0x5fe000 <= x ->
  aview SEGS (w_H W) m x = Some v ->
  w_H W (Z_to_bv 64 x) = false /\ exists b, m (Z_to_bv 64 x) = Some b /\ bv_unsigned b = v.
Proof.
  intros W m x v Hx Hh H. unfold aview, mbyte, mrestrict in H.
  destruct (w_H W (Z_to_bv 64 x)) eqn:Eh.
  - rewrite (ce_rom_none x Hx (or_introl Hh)) in H. discriminate H.
  - split; [reflexivity|]. destruct (m (Z_to_bv 64 x)) as [b|] eqn:Em.
    + injection H as <-. exists b. split; reflexivity.
    + rewrite (ce_rom_none x Hx (or_introl Hh)) in H. discriminate H.
Qed.

(* An addressable range of the world's view is addressable in ctrl's sense, given its bytes are application memory. *)
Lemma ce_addr_of_view : forall (W : world SEGS) (m : word -> option byte) (q n : Z),
  0 <= q -> 0 <= n -> q + n <= lib.B.AsanRT.APPMEM_END ->
  (forall i, 0 <= i < n -> lib.B.AsanRT.app_mem (q + i)) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF q n ->
  lib.B.AsanRT.addressable m q n.
Proof.
  intros W m q n Hq Hn Hend Happ HR. split; [exact Hq|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (q + i) ltac:(lia)) as (sv & Hs & Hok).
  unfold shadow_of_addr in Hs.
  assert (Hsx : 0 <= SHADOW_OFF + (q + i) / 8 < 2 ^ 64).
  { unfold SHADOW_OFF, lib.B.AsanRT.APPMEM_END in *. Z.div_mod_to_equations. lia. }
  destruct (ce_view_shadow W m _ sv Hsx ltac:(unfold SHADOW_OFF; Z.div_mod_to_equations; lia) Hs)
    as (_ & b & Eb & Ev).
  exists b. split.
  - unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa, lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K.
    replace ((q + i) / 8 + 0x7fff8000) with (SHADOW_OFF + (q + i) / 8) by (unfold SHADOW_OFF; lia).
    rewrite Eb. reflexivity.
  - pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
    assert (Es : bv_unsigned b < 8 -> bv_signed b = bv_unsigned b).
    { intros Hl. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
      change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia. }
    unfold saddr_ok in Hok. unfold lib.B.AsanRT.shadow_ok. rewrite <- Ev in Hok.
    destruct Hok as [H0 | [H1 H2]]; [left | right]; rewrite Es by lia; lia.
Qed.

(* ret_ok of the core is the run's ret_pc identity (the twin of lib/B/KindBGlue.v kb_ret_pc over the core's YK0s). *)
Lemma ce_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

Lemma ce_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma ce_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> lib.Lib.MState.ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, ce_mod2_land; apply ce_land_m2).
  change (bv_modulus 64) with (2 ^ 64) in Hr.
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Lemma ce_outside_dec : forall (WR : list lib.Lib.Frame.ivl) (x : Z),
  lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [lib.Lib.Frame.outside]; [left; exact I|].
  destruct (IH x) as [H | H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z.le_gt_cases lo x) as [H1 | H1]; [destruct (Z.lt_ge_cases x hi) as [H2 | H2]|].
  - right. intros [H3 _]. apply H3. split; assumption.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

(* Outside the run's write ranges the world's reader is unchanged. *)
Lemma ce_view_munch : forall (H : word -> bool) (m m' : word -> option byte) (WR : list lib.Lib.Frame.ivl) (a : Z),
  0 <= a < 2 ^ 64 -> lib.Lib.Frame.munch WR m m' -> lib.Lib.Frame.outside WR a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' WR a Ha Hmu Ho. apply (aview_eq_of SEGS). unfold mrestrict.
  destruct (H (Z_to_bv 64 a)); [reflexivity|]. apply Hmu.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Ho.
Qed.

Lemma ce_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. Qed.

Section j. Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* A byte the caller lets the call write is not image memory (the twin of a Theorem Labs lane's A/Prog/GE_jrnl.v
   ge_awr_not_img, a working branch 8b0fc309e6f). *)
Lemma ce_awr_not_img : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> ~ in_img SEGS a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw Hi.
  pose proof (ce_segs_low a Hi) as Hlow.
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)
    as (_ & [[Hc _] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl _] _]])]]).
  - lia.
  - exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
  - assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin Hr Hi).
  - lia.
Qed.

(* The caller's journal survives a lifted stretch that writes inside WR, when every byte of WR is one the caller
   lets the call write (the twin of GE_jrnl.v ge_jrnl). *)
Lemma ce_jrnl : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (mdc' : Model) (WR : list lib.Lib.Frame.ivl) (m' : word -> option byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  lib.Lib.Frame.munch WR memc m' -> lib.Lib.Frame.wmono RS memc m' ->
  (forall x : word, w_H W x = true -> m' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' WR m' HJ Hmu Hwm Hhid Hsame HW.
  eapply (ajournal_exec SEGS B LAWS ce_segs_low)
    with (Wr := fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a);
    [exact HJ | | | exact Hhid | exact Hsame | ].
  - intros x Hx. cbv beta in Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|].
    apply Hmu. destruct (ce_outside_dec WR (bv_unsigned x)) as [Ho | Ho]; [exact Ho|].
    exfalso. apply Hx. split; [exact (ce_u64 x) | exact Ho].
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|].
    destruct (ce_outside_dec WR (bv_unsigned x)) as [Ho | Ho]; [rewrite (Hmu x Ho); exact Hx|].
    pose proof (ce_awr_not_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (bv_unsigned x) HJ
      (HW _ (ce_u64 x) Ho)) as Hni.
    assert (Hwv : wview RS memc x <> None)
      by (unfold wview; destruct (memc x); [discriminate | exfalso; exact (Hx eq_refl)]).
    pose proof (Hwm x Hwv) as Hwv'. unfold wview in Hwv'. destruct (m' x); [discriminate|].
    pose proof (find_segment_none SEGS (bv_unsigned x) Hni) as Hfs. change SEGS with RS in Hfs.
    rewrite Hfs in Hwv'. exact Hwv'.
  - intros a [Ha Ho]. exact (HW a Ha Ho).
Qed.
End j.

(* The read-only data survives a run that writes no image byte (GE_jrnl.v ge_ro_keep), when the read-only span
   lies in the image. *)
Lemma ce_ro_keep : forall (RLO RHI : Z) (B : asyms) (H : word -> bool) (m m' : word -> option byte)
    (WR : list lib.Lib.Frame.ivl),
  (forall a, RLO <= a < RHI -> in_img SEGS a) ->
  arodata_okS SEGS B RLO RHI (aview SEGS H m) ->
  lib.Lib.Frame.munch WR m m' ->
  (forall a, in_img SEGS a -> lib.Lib.Frame.outside WR a) ->
  arodata_okS SEGS B RLO RHI (aview SEGS H m').
Proof.
  intros RLO RHI B H m m' WR Himg Hro Hmu Hout a Hseg Hno He.
  assert (Hi : in_img SEGS a).
  { destruct Hseg as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | lia] | exact (Himg a Hr)]. }
  pose proof (ce_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (ce_view_munch H m m' WR a ltac:(lia) Hmu (Hout a Hi)).
  exact (Hro a Hseg Hno He).
Qed.
End g1.

(* =================================================================================================================
   The glue's Section hypotheses (the ONE marked place; each is the type its owner states, never a copied text,
   except the consumed callee contract, whose file is not on this base):
   - HTS, AR_laws_B: the core bundle law CtrlTSyms and AR_laws (composer, B := CtrlB);
   - RRO_img: the read-only span lies in the image (composer, at its RLO RHI: [0x9f1a0, 0xa15e8) is inside the
     segment [0x9f000, 0xa2000)); a stretch writes no image byte, so arodata_okS RLO RHI survives it;
   No ProgWorld fact is a hypothesis.  The ProgWorld statements are CITED, proved (a Theorem Labs lane):
   ProgWorldCtlRt.asan_cells_of_AR / ro_agree_of_AR, ProgWorldOwnedRo.AR_states_owned_ro_of_AR,
   ProgWorld_Fs.ctl_fp_of_AR (a working branch d2c835124b3, merged), ProgWorldTlsApart.fp_tls_apart
   (d5f1e30d857, by path), ProgWorldTlsOwned.fp_tls_owned (14f42b38487, by path).  The run's shadow premise is the
   route (C) one: ctrl_emit_asF.aentry_k_on / alay_ret_on (a working branch
   26e8a9dd8b0, by path) take no universal shadow_rw; aentry_k_on takes shadow_rw_on over the shadow words of f 24,
   md 296, d 6, s 6 and (when E) the output, which ce_srw_hull reads off the statement's own shadow_hull_vis
   premises of those five ranges (m_fRV / m_mRV for the two read-only globals), and alay_ret_on takes none;
   - GM: the composer's CtrlRo.globs_marked SEGS B GLOBS (a fact of the composer's list GLOBS; the same one
     ctrl_lay_block's proof takes).  ISV, CtrlRo.img_shadow_vis SEGS B, is CITED, proved from HTS and AR_laws_B:
     ACtlCutC.ctrl_img_shadow_vis (a Theorem Labs lane's cform, on this base);
   - tctrl_lay_block_spec (with its tctrl_lay_block_ro / tctrl_lay_block_home): a Theorem Labs lane's consumed contract
     (a working branch 079649851ae, lib/B/Prog/C_ctrl_lay_block.v
     `tctrl_lay_block_spec RLO RHI B GLOBS` at this glue's RLO RHI), its text with CTRL_LAY_BLOCK /
     CTRL_LAY_BLOCK_STK / EV_CTRL_LAY_BLOCK as the numerals 0x86104 / 4512 / 0.
   ================================================================================================================= *)
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.B.ProgWorld lib.B.ProgWorld_Fs lib.B.ProgWorldCtlRt
  lib.B.ProgWorldOwnedRo lib.B.ProgWorldTlsApart lib.B.ProgWorldTlsOwned.
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.Reusable.YF0m lib.Reusable.YG0s
  lib.Prog.RcSynthLib lib.Prog.RcFinLib lib.Prog.RcEmitLib lib.B.Prog.memset lib.B.Prog.asan_memsetF_on
  lib.B.Prog.asan_memcpyF_on lib.B.Prog.reac_braid_encode_ns0F lib.B.Prog.ctrl_finishF.
(* route (C): the region form of the shadow premise and its region (a Theorem Labs lane's leaf files) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.B.ShadowRwOn lib.B.ShadowRwOnT lib.B.Prog.rng_asan
  lib.B.Prog.sh_word_on.
(* the proved image-shadow visibility (ISV below) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl Require lib.B.ACtlCutC.

(* Image B's writable-and-executable segments end below 2^64 (YA0nR.SRr_fsteps' Hwx), by computation over the
   segment list (the twin of lib/A/Prog/CtrlImg.v ctrl_wx; lib/Reusable/YCeg.v Hwx_tfa is not available on this
   base: YCeg.v does not compile). *)
Lemma ce_wx : wx_segs_nowrap lib.Reusable.YB1v.tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section g2. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
#[local] Notation RS := lib.B.Img0.rsegs.
Variables RLO RHI : Z.
Variable B : asyms.

Hypothesis RRO_img : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis HTS : lib.Reusable.YF0m.CtrlTSyms B.
Hypothesis AR_laws_B : AR_laws SEGS B.
#[local] Notation OWNRO := (lib.B.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B HTS).
#[local] Notation FPAR := (lib.B.ProgWorld_Fs.ctl_fp_of_AR B).
#[local] Notation TLSAP := (lib.B.ProgWorldTlsApart.fp_tls_apart B).
#[local] Notation TLSOWN := (lib.B.ProgWorldTlsOwned.fp_tls_owned B).

Variable GLOBS : list (Z * Z).
(* The composer's start-up certificate for the registered globals (lib/B/Prog/CtrlRo.v:117), the one ctrl_lay_block's
   proof takes: every listed global's shadow is marked at every AR state.  Every shadow byte of the image's read range
   is mapped (CtrlRo.v:45): proved, ACtlCutC.ctrl_img_shadow_vis. *)
Hypothesis GM : CtrlRo.globs_marked SEGS B GLOBS.
#[local] Notation ISV := (lib.B.ACtlCutC.ctrl_img_shadow_vis B HTS AR_laws_B).

(* The consumed callee contract: a Theorem Labs lane's tctrl_lay_block_spec (a working branch 079649851ae,
   lib/B/Prog/C_ctrl_lay_block.v, `tctrl_lay_block_spec RLO RHI B GLOBS`) at this glue's RLO RHI, its text
   with its CTRL_LAY_BLOCK / CTRL_LAY_BLOCK_STK / EV_CTRL_LAY_BLOCK as the numerals 0x86104 / 4512 / 0 and its post
   written out; its tctrl_lay_block_ro and tctrl_lay_block_home are restated here word for word.
   *)
Definition tctrl_lay_block_ro (q n : Z) : Prop :=
  (exists q0 sz, In (q0, sz) GLOBS /\ q0 <= q /\ q + n <= q0 + sz) /\
  CtrlRo.IMG_LO + 64 <= q /\ q + n + 64 <= CtrlRo.IMG_HI /\
  (forall x, q <= x < q + n -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).

Definition tctrl_lay_block_home (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
    (exists b m i, In (b, m) (ablocks B lyc Sc) /\ 0 <= i < req_size m /\ a = b + i) \/
    (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ in_zr a (frame_rng lyc (cid, pos))).

Hypothesis tctrl_lay_block_spec :
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
         (p f md g : Z) (fr tb mb nb gb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= raZ regs ->
  lib.Reusable.YK11.getr regs 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
  lib.Reusable.YK11.getr regs 10 = w64 p -> lib.Reusable.YK11.getr regs 11 = w64 f ->
  lib.Reusable.YK11.getr regs 12 = w64 md -> lib.Reusable.YK11.getr regs 13 = w64 g ->
  0 <= p < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> 0 <= md < 2 ^ 64 -> 0 <= g < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 4512 -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  p <> 0 -> p + 50 <= 2 ^ 64 ->
  (forall a, p + 18 <= a < p + 50 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  tctrl_lay_block_home lyc Sc (p + 18) 32 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 ->
  (forall a, p + 18 <= a <= p + 50 -> app_addr a) ->
  f mod 8 = 0 -> length fr = 24%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) f (map (fun x : byte => bv_unsigned x) fr) ->
  tctrl_lay_block_ro f 24 ->
  ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
  (ly_k fr = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) (ly_tm fr) (map (fun x : byte => bv_unsigned x) tb) /\
     tctrl_lay_block_ro (ly_tm fr) 32 /\
     (forall a, ly_tm fr <= a < ly_tm fr + 32 ->
        exists s, In s SEGS /\ seg_writable s = false /\
          Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb) /\
     tctrl_lay_block_ro md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        tctrl_lay_block_ro (rname mb) (Z.of_nat (length nb)))) ->
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\
     garr8 SEGS (mrestrict (w_H W) memc) g (map (fun x : byte => bv_unsigned x) gb) /\
     tctrl_lay_block_ro g (ly_al fr) /\
     app_addr (g + ly_al fr) /\ app_addr (g + 7) /\ app_addr (p + 25 + ly_ao fr)) ->
  ly_dj (spZ regs - 4512) (spZ regs) (p + 18) (p + 50) ->
  ly_dj (spZ regs - 4512) (spZ regs) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (spZ regs - 4512) (spZ regs) (ly_tm fr) (ly_tm fr + 32)) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (spZ regs - 4512) (spZ regs) g (g + ly_al fr)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (spZ regs - 4512) (spZ regs) md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (spZ regs - 4512) (spZ regs) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
  ly_dj (p + 18) (p + 50) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
     ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
  SRr SEGS W (cfg_at SEGS 0x86104 regs memc mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr regs 1) mem2
                     (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) /\
       aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
       garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18)
         (map (fun x : byte => bv_unsigned x)
            (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)) /\
       acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - 4512) (spZ regs)
         (fun a => p + 18 <= a < p + 50)).


(* ---- geometry: where the side stack for frames lies, and what is apart from it ---- *)

Lemma ce_layout : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md -> layout_ok ly.
Proof. intros ly S W m md (HM & _). exact (am_layout _ _ _ _ HM). Qed.

(* The side stack [ly_F, ly_F + kFakeStackSize) is an owned extent: page-aligned, in application memory, below the
   allocator's ceiling, and (layout_ok's lo_stk_ceil) below the stack. *)
Lemma ce_fs_place : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
  4096 <= ly_F ly /\ ly_F ly mod 4096 = 0 /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
  (forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> lib.B.AsanRT.app_mem a) /\
  ASAN_CEIL <= ly_stk_lo ly.
Proof.
  intros ly S W m md HAR. pose proof (ce_layout ly S W m md HAR) as LOk.
  pose proof (lo_app _ LOk) as HApp. pose proof (lo_F_al _ LOk) as HAl. pose proof (lo_stk_ceil _ LOk) as HC.
  pose proof ASAN_CEIL_range as (CR & _).
  pose proof (proj1 (Forall_forall _ _) HApp (ly_F ly, kFakeStackSize)
                ltac:(unfold owned_extents; cbn [In]; tauto)) as HF.
  cbn [fst snd] in HF. destruct HF as (HF0 & HFr).
  unfold kLowShadowBeg, kHighMemBeg in HFr.
  split; [exact HF0|]. split; [exact HAl|].
  split; [destruct HFr as [H1 | [H1 H2]]; lia |].
  split; [|exact HC].
  intros a Ha. unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG,
    lib.B.AsanRT.APPMEM_END.
  destruct HFr as [H1 | [H1 H2]]; [left | right]; lia.
Qed.

(* Application memory and the shadow map are apart: an application byte is never a shadow byte of an application
   byte, so a range of application memory is apart from the shadow of any application range. *)
Lemma ce_app_not_shadow : forall a x, lib.B.AsanRT.app_mem a -> 0 <= x -> x < lib.B.AsanRT.APPMEM_END ->
  a <> lib.B.AsanRT.shadow_addr x.
Proof.
  intros a x Ha Hx0 Hx1 E. unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG,
    lib.B.AsanRT.APPMEM_END in Ha, Hx1.
  unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in E.
  assert (0 <= x / 8 <= 0x100000000000) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* ---- the footprint of a lifted stretch: every visible byte EXCEPT the class-0 and class-1 side-stack bytes
   (fp_w [0; 1] FS: the two hint words, the two flag arrays, the two frame banks and their shadow).  Neither
   ctrl_emit_asF.aentry_k_on nor ctrl_emit_asF.alay_ret_on takes a side-stack rng premise (their Arguments lists have no
   FpFS / FpFSH / FpTLS), so the footprint may leave those bytes out; the run then cannot have written them
   (YA0nR.fsteps_keeps_hidden at the hidden set below), which is what the caller's journal needs: a side-stack byte
   is allocator-OWNED and has no awr_byte case (decisions.md item 24).  The two fake-stack calls that DO write them
   are inside ctrl_lay_block, at the cut, where its own contract owns them. ---- *)
Definition ce_fpwb (FS : Z) (x : word) : bool :=
  existsb (fun r : lib.Lib.Frame.ivl => (fst r <=? bv_unsigned x) && (bv_unsigned x <? snd r))
    (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS).

Definition ce_H (H : word -> bool) (FS : Z) : word -> bool := fun x => H x || ce_fpwb FS x.

Lemma ce_fpwb_true : forall FS x, ce_fpwb FS x = true ->
  exists r, In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) /\ fst r <= bv_unsigned x < snd r.
Proof.
  intros FS x H. unfold ce_fpwb in H. apply existsb_exists in H as (r & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists r. split; [exact Hin | lia].
Qed.

Lemma ce_fpwb_false : forall FS x,
  (forall r, In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) -> ~ (fst r <= bv_unsigned x < snd r)) ->
  ce_fpwb FS x = false.
Proof.
  intros FS x H. destruct (ce_fpwb FS x) eqn:E; [|reflexivity].
  destruct (ce_fpwb_true FS x E) as (r & Hin & Hr). exfalso. exact (H r Hin Hr).
Qed.

(* The hidden set of a lifted stretch: the world's own hidden bytes together with the class-0 / class-1 side-stack
   bytes.  RNG := ProgBridge.RNG_W (ce_H (w_H W) FS) then (a) avoids the world's hidden memory (so YA0nR.SRr_fevt
   lifts the run) and (b) avoids the side stack's class-0 / class-1 bytes, so YA0nR.fsteps_keeps_hidden gives them
   back unchanged at the end of the stretch. *)
Lemma ce_H_mono : forall H FS x, ce_H H FS x = false -> H x = false.
Proof. intros H FS x E. unfold ce_H in E. apply orb_false_iff in E as [E1 _]. exact E1. Qed.

Lemma ce_fp_avoids_H : forall (W : world SEGS) FS,
  lib.Reusable.YK04R.fp_avoids (w_H W) (lib.B.ProgBridge.RNG_W (ce_H (w_H W) FS)).
Proof.
  intros W FS a n Hr k Hk. exact (ce_H_mono _ _ _ (lib.B.ProgBridge.fp_avoids_RNG_W _ a n Hr k Hk)).
Qed.

(* ---- the window's shadow bytes are 0 at EVERY memory where the window is addressable and both ends are
   8-aligned: the last byte of each granule is addressable only with the metadata byte 0 (AsanRT.shadow_ok at
   a mod 8 = 7 forces it).  So a lifted stretch that leaves the window addressable (ctrl_emit_asF.aQp_on does) leaves
   the window's shadow UNCHANGED in the world's view, which is what the caller's journal needs there: a window
   shadow byte is allocator-owned (YG0n.v:188-191, :236-242) and has no awr_byte case. ---- *)
Lemma ce_signed_zero : forall b : byte, bv_signed b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap in H. change (bv_half_modulus 8) with 128 in H.
  change (bv_modulus 8) with 256 in H. rewrite Z.mod_small in H by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. lia.
Qed.

Lemma ce_shadow_zero_of_addr : forall m q n, lib.B.AsanRT.addressable m q n -> q mod 8 = 0 -> n mod 8 = 0 ->
  forall i, 0 <= i < n / 8 ->
    lib.Lib.Mem.mrd RS m (lib.Lib.Mem.wa (lib.B.AsanRT.shadow_addr q + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m q n (Hq & Hn & Hend & HA) Hq8 Hn8 i Hi.
  assert (Hb : 0 <= 8 * i + 7 < n) by (Z.div_mod_to_equations; lia).
  destruct (HA (8 * i + 7) Hb) as (_ & b & Hb1 & Hb2).
  assert (Esh : lib.B.AsanRT.shadow_addr (q + (8 * i + 7)) = lib.B.AsanRT.shadow_addr q + i).
  { unfold lib.B.AsanRT.shadow_addr.
    replace (q + (8 * i + 7)) with (8 * (q / 8 + i) + 7) by (Z.div_mod_to_equations; lia).
    rewrite Z.mul_comm, Z.div_add_l by lia. cbn. lia. }
  rewrite Esh in Hb1. rewrite Hb1. f_equal. apply ce_signed_zero.
  unfold lib.B.AsanRT.shadow_ok in Hb2.
  assert (Hm8 : (q + (8 * i + 7)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  rewrite Hm8 in Hb2. lia.
Qed.

Lemma ce_win_shadow_view : forall (H : word -> bool) (m m' : word -> option byte) q n,
  lib.B.AsanRT.addressable m q n -> lib.B.AsanRT.addressable m' q n -> q mod 8 = 0 -> n mod 8 = 0 ->
  forall i, 0 <= i < n / 8 ->
    aview SEGS H m' (lib.B.AsanRT.shadow_addr q + i) = aview SEGS H m (lib.B.AsanRT.shadow_addr q + i).
Proof.
  intros H m m' q n HA HA' Hq8 Hn8 i Hi.
  pose proof (ce_shadow_zero_of_addr m q n HA Hq8 Hn8 i Hi) as E.
  pose proof (ce_shadow_zero_of_addr m' q n HA' Hq8 Hn8 i Hi) as E'.
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa, lib.Lib.PropExec.seg_rom in E, E'.
  unfold aview, mbyte, mrestrict, lib.Reusable.YK11.seg_rom. change SEGS with RS.
  destruct (H (Z_to_bv 64 (lib.B.AsanRT.shadow_addr q + i))); [reflexivity|].
  rewrite E, E'. reflexivity.
Qed.

(* ---- the stack window is addressable at every state of the walk: AR marks the whole stack zero-shadow
   (YG0n.v:188-191 zero_shadow_ranges, AR_zshadow_law YG0d.v:435-438), and a zero metadata byte is what ctrl's
   `addressable` asks for.  This is the source of ctrl_emit_asF's AWIN premise at the entry and, after
   ctrl_lay_block returns, at the return memory. ---- *)
Lemma ce_stack_addr : forall ly S (W : world SEGS) m md lo len,
  AR SEGS B ly S W m md -> ly_stk_lo ly <= lo -> 0 <= len -> lo + len <= ly_stk_hi ly ->
  (forall a, lo <= a < lo + len -> lib.B.AsanRT.app_mem a) ->
  lib.B.AsanRT.addressable m lo len.
Proof.
  intros ly S W m md lo len HAR Hlo Hlen Hhi Happ.
  pose proof (ce_layout ly S W m md HAR) as LOk.
  pose proof (lo_top _ LOk) as Htop.
  unfold page_aligned, kHighMemEnd, kHighMemBeg in Htop.
  pose proof (lo_stk_ceil _ LOk) as HC. pose proof ASAN_CEIL_range as (CR & _).
  assert (Hz : zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  { apply (al_zshadow _ _ AR_laws_B ly S W m md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR).
    unfold zero_shadow_ranges. left. reflexivity. }
  split; [lia|]. split; [exact Hlen|].
  assert (Hend : lo + len <= lib.B.AsanRT.APPMEM_END).
  { unfold lib.B.AsanRT.APPMEM_END. destruct (Z.eq_dec len 0) as [->|Hne]; [lia|].
    pose proof (Happ (lo + len - 1) ltac:(lia)) as Ha.
    unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG,
      lib.B.AsanRT.APPMEM_END in Ha. lia. }
  split; [exact Hend|]. intros i Hi.
  split; [exact (Happ (lo + i) ltac:(lia))|].
  assert (Hj : 0 <= (lo + i) / 8 - ly_stk_lo ly / 8 < (ly_stk_hi ly - ly_stk_lo ly) / 8).
  { split; [apply Zle_minus_le_0, Z.div_le_mono; lia |].
    assert (E1 : ly_stk_hi ly - ly_stk_lo ly = 8 * (ly_stk_hi ly / 8 - ly_stk_lo ly / 8))
      by (Z.div_mod_to_equations; lia).
    rewrite E1, Z.mul_comm, Z.div_mul by lia. Z.div_mod_to_equations. lia. }
  pose proof (Hz _ Hj) as Hv.
  assert (Ex : shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + ((lo + i) / 8 - ly_stk_lo ly / 8)
             = SHADOW_OFF + (lo + i) / 8) by (unfold shadow_of_addr; lia).
  rewrite Ex in Hv.
  assert (Hx : 0 <= SHADOW_OFF + (lo + i) / 8 < 2 ^ 64)
    by (unfold SHADOW_OFF, lib.B.AsanRT.APPMEM_END in *; Z.div_mod_to_equations; lia).
  destruct (ce_view_shadow W m _ 0 Hx ltac:(unfold SHADOW_OFF; Z.div_mod_to_equations; lia) Hv)
    as (_ & b & Eb & Ev).
  exists b. split.
  - unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa, lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K.
    replace ((lo + i) / 8 + 0x7fff8000) with (SHADOW_OFF + (lo + i) / 8) by (unfold SHADOW_OFF; lia).
    rewrite Eb. reflexivity.
  - left. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
    change (bv_modulus 8) with 256. rewrite Ev. reflexivity.
Qed.

Lemma ce_shadow_mono : forall x y, x <= y -> lib.B.AsanRT.shadow_addr x <= lib.B.AsanRT.shadow_addr y.
Proof.
  intros x y H. unfold lib.B.AsanRT.shadow_addr.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia.
Qed.

(* Where the class-0 and class-1 bytes of the side stack lie: the hint words, the flag arrays and the two frame
   banks are inside [FS, FS + 2134016), their shadow inside the shadow of that span.  (fs_hint / fs_flag /
   fs_frame / fs_M / fs_B of lib/B/Prog/asan_stack_malloc_c.v at the classes 0 and 1.) *)
Lemma ce_fpw_ranges : forall FS r, In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) ->
  (FS <= fst r /\ snd r <= FS + 2134016) \/
  (lib.B.AsanRT.shadow_addr (FS + 36864) <= fst r /\
   snd r <= lib.B.AsanRT.shadow_addr (FS + 2134016)).
Proof.
  intros FS r Hin.
  unfold lib.B.Prog.RcAsanFP.fp_w, lib.B.Prog.RcAsanFP.fp_w1 in Hin.
  cbn [flat_map app In] in Hin.
  unfold lib.B.Prog.asan_stack_malloc_c.fs_hint, lib.B.Prog.asan_stack_malloc_c.fs_flag,
    lib.B.Prog.asan_stack_malloc_c.fs_frame, lib.B.Prog.asan_stack_malloc_c.fs_M,
    lib.B.Prog.asan_stack_malloc_c.fs_B in Hin.
  cbn [Z.of_nat] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd];
    first [ left; split; lia | right; split; apply ce_shadow_mono; lia ].
Qed.

(* The hidden set ce_H hides no segment byte: the class-0 / class-1 bytes are at or above the side stack's base,
   which is at or above ASAN_GT = 0x5fe000, the top of image B's loaded segments, and their shadow is at or above
   the shadow base 0x7fff8000. *)
Lemma ce_H_off : forall (W : world SEGS) FS, lib.B.Prog.asan_stack_malloc_c.ASAN_GT <= FS ->
  H_off_segments SEGS (ce_H (w_H W) FS).
Proof.
  intros W FS HGT x Hx. unfold ce_H in Hx. apply orb_true_iff in Hx as [H1 | H2].
  - exact (w_Hoff W x H1).
  - destruct (ce_fpwb_true FS x H2) as (r & Hin & Hr).
    apply find_segment_none. apply ce_not_img. left.
    unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT in HGT.
    destruct (ce_fpw_ranges FS r Hin) as [(Hl & Hh) | (Hl & Hh)]; [lia|].
    unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in Hl.
    assert (0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* A range of bytes that the world does not hide and that is apart from the class-0 / class-1 side-stack bytes is a
   footprint range of the stretch's RNG.  Every rng premise of ctrl_emit_asF.aentry_k_on / .alay_ret_on is discharged
   through this lemma. *)
Lemma ce_fpwb_false_of : forall FS a, 0 <= a < 2 ^ 64 ->
  ~ (FS <= a < FS + 2134016) ->
  ~ (lib.B.AsanRT.shadow_addr (FS + 36864) <= a < lib.B.AsanRT.shadow_addr (FS + 2134016)) ->
  ce_fpwb FS (Z_to_bv 64 a) = false.
Proof.
  intros FS a Ha H1 H2. apply ce_fpwb_false. intros r Hin Hr.
  rewrite (lib.Lib.MState.unsigned_lit a ltac:(rlia)) in Hr.
  destruct (ce_fpw_ranges FS r Hin) as [(Hl & Hh) | (Hl & Hh)].
  - apply H1. split; rlia.
  - apply H2. split; rlia.
Qed.

Lemma ce_rng_of : forall (W : world SEGS) FS lo len,
  0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> w_H W (Z_to_bv 64 a) = false) ->
  (forall a, lo <= a < lo + len -> ~ (FS <= a < FS + 2134016) /\
     ~ (lib.B.AsanRT.shadow_addr (FS + 36864) <= a < lib.B.AsanRT.shadow_addr (FS + 2134016))) ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) FS)) lo len.
Proof.
  intros W FS lo len Hlo Hhi Hvis Hap. apply lib.B.ProgBridge.rng_RNG_W; [exact Hlo | exact Hhi |].
  intros a Ha. unfold ce_H. rewrite (Hvis a Ha).
  destruct (Hap a Ha) as (H1 & H2). rewrite (ce_fpwb_false_of FS a ltac:(lia) H1 H2). reflexivity.
Qed.

(* ---- placement facts at any AR state (the side stack above the image, a live class>=2 frame above the class-0/1
   bytes, frame bytes application memory and not owned) and the byte-wise form of ly_dj ---- *)

(* The side stack is above the image: the image's last segment ends at ASAN_GT = 0x5fe000 inside ly_img (ALedger's
   al_img), and layout_ok keeps (ly_F, kFakeStackSize) apart from ly_img (YG0s.owned_extents_bound).  The B twin of
   a Theorem Labs lane's A/ProgWorld_Fs.v pw_F_above (a working branch a48c4068c6e :242-264). *)
Lemma ce_F_above : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
  lib.B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F ly.
Proof.
  intros ly S W m md HAR. pose proof HAR as (M & L & _).
  pose proof (am_layout _ _ _ _ M) as LOk.
  pose proof (lo_img _ LOk) as (I1 & I2 & I3 & I4).
  pose proof (ce_fs_place ly S W m md HAR) as (F0 & _).
  assert (Hm : In (0xa2000, 0x55c000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) RS))
    by (rewrite lib.B.ProgBridge.rsegs_spans; cbn; tauto).
  apply in_map_iff in Hm as (sg & Es & Hsg). injection Es as E1 E2.
  pose proof (al_img _ _ _ _ L sg Hsg) as [_ J2]. rewrite E1, E2 in J2.
  assert (NI : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ in_zr a (ly_img ly)).
  { intros a Ha. refine (proj2 (proj2 (lib.Reusable.YG0s.owned_extents_bound ly a LOk _))).
    apply Exists_exists. exists (ly_F ly, kFakeStackSize).
    split; [unfold owned_extents; cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT. unfold kImgLo in I1.
  destruct (Z_lt_le_dec (ly_F ly) 65536) as [Hlt|Hge].
  - exfalso. apply (NI 65536); [unfold kFakeStackSize; lia | unfold in_zr; lia].
  - destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt2|Hge2].
    + exfalso. apply (NI (ly_F ly)); [unfold kFakeStackSize; lia | unfold in_zr; lia].
    + lia.
Qed.

(* A live frame of class 2 or more starts at or above ly_F + 2134016, the end of the class-0 / class-1 bytes. *)
Lemma ce_frame_lo : forall ly S (W : world SEGS) m md cid pos, AR SEGS B ly S W m md ->
  In (cid, pos) (frames S) -> 2 <= cid -> ly_F ly + 2134016 <= frame_addr ly cid pos.
Proof.
  intros ly S W m md cid pos HAR Hin H2. pose proof HAR as (M & _).
  pose proof (lib.Reusable.YG01.wfs_live _ (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as Hlive.
  pose proof (proj1 (Forall_forall _ _) Hlive (cid, pos) Hin) as Hpos. cbn [fst snd] in Hpos.
  unfold frame_addr, fs_frame_off, kFakeFramesOff. rewrite Z.shiftl_1_l. change kStackSizeLog with 20.
  assert (0 <= pos * fs_frame_bytes cid).
  { apply Z.mul_nonneg_nonneg; [lia|]. unfold fs_frame_bytes. apply Z.shiftl_nonneg. lia. }
  change (2 ^ 20) with 1048576. lia.
Qed.

Lemma ce_app_addr_mem : forall a, app_addr a -> lib.B.AsanRT.app_mem a.
Proof.
  intros a (H0 & H). pose proof ASAN_CEIL_range as (CR & _).
  unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg in H. destruct H as [H | [H1 H2]]; [left | right]; lia.
Qed.

Lemma ce_in_app_mem : forall q n i, in_app q n -> 0 <= i < n -> lib.B.AsanRT.app_mem (q + i).
Proof. intros q n i H Hi. apply ce_app_addr_mem. apply (in_app_addr q n); [exact H | lia]. Qed.

(* A byte of a live frame: application memory, below the ceiling, not owned, not image. *)
Lemma ce_frame_byte : forall ly S (W : world SEGS) m md cid pos a, AR SEGS B ly S W m md ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  lib.B.AsanRT.app_mem a /\ a < ASAN_CEIL /\ ~ aowned B ly S a /\ ~ in_img SEGS a.
Proof.
  intros ly S W m md cid pos a HAR Hin Ha.
  destruct (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin) as (H0 & H1 & H2).
  split; [apply ce_app_addr_mem; exact (in_app_addr _ _ a H2 Ha)|]. split; [unfold ASAN_CEIL; lia|].
  split; [exact (proj2 (proj1 (proj2 (proj2 (al_frames _ _ AR_laws_B _ _ _ _ _ _ _ HAR Hin))) a Ha))|].
  exact (frm_img SEGS B AR_laws_B _ _ _ _ _ _ _ _ HAR Hin Ha).
Qed.

(* ly_dj from bytes: a range apart byte by byte (its first byte included when it is empty) from a non-empty one. *)
Lemma ce_dj_bytes : forall q n c d, 0 <= n -> c < d ->
  (forall x, c <= x < d -> q <= x < q + Z.max n 1 -> False) -> ly_dj q (q + n) c d.
Proof.
  intros q n c d Hn Hcd H. unfold ly_dj.
  destruct (Z_le_gt_dec (q + n) c) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec d q) as [h2|h2]; [right; exact h2|].
  exfalso. apply (H (Z.max q c)); lia.
Qed.

(* Every class-0 / class-1 range is non-empty, and each of its bytes is either in [FS, FS + 2134016) or a shadow
   byte of the side stack, which is not application memory when the side stack lies below the ceiling. *)
Lemma ce_fpw_nonempty : forall FS r, In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) -> fst r < snd r.
Proof.
  intros FS r Hin.
  unfold lib.B.Prog.RcAsanFP.fp_w, lib.B.Prog.RcAsanFP.fp_w1 in Hin. cbn [flat_map app In] in Hin.
  unfold lib.B.Prog.asan_stack_malloc_c.fs_hint, lib.B.Prog.asan_stack_malloc_c.fs_flag,
    lib.B.Prog.asan_stack_malloc_c.fs_frame, lib.B.Prog.asan_stack_malloc_c.fs_M,
    lib.B.Prog.asan_stack_malloc_c.fs_B, lib.B.AsanRT.shadow_addr in Hin.
  cbn [Z.of_nat] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd]; rlia.
Qed.

Lemma ce_fpw_byte : forall FS r x, 0 <= FS -> FS + 2134016 <= ASAN_CEIL ->
  In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) -> fst r <= x < snd r ->
  (FS <= x < FS + 2134016) \/ ~ lib.B.AsanRT.app_mem x.
Proof.
  intros FS r x H0 HC Hin Hx. pose proof ASAN_CEIL_range as (CR & _).
  destruct (ce_fpw_ranges FS r Hin) as [(Hl & Hh) | (Hl & Hh)]; [left; lia | right].
  unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in Hl, Hh.
  unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END.
  assert (0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia).
  assert ((FS + 2134016) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (E8 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity. rewrite E8 in *. lia.
Qed.

(* A data range all of whose bytes are application memory outside [ly_F, ly_F + 2134016) is apart from the class-0
   / class-1 side-stack bytes. *)
Lemma ce_dj_fpw : forall ly S (W : world SEGS) m md q n, AR SEGS B ly S W m md -> 0 <= n ->
  (forall x, q <= x < q + Z.max n 1 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F ly <= x < ly_F ly + 2134016)) ->
  forall r, In r (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] (ly_F ly)) -> ly_dj q (q + n) (fst r) (snd r).
Proof.
  intros ly S W m md q n HAR Hn Hx r Hin.
  pose proof (ce_fs_place ly S W m md HAR) as (F0 & _ & FC & _).
  apply ce_dj_bytes; [exact Hn | exact (ce_fpw_nonempty _ r Hin) |].
  intros x Hr Hq. destruct (Hx x Hq) as (Ha & Hf).
  destruct (ce_fpw_byte (ly_F ly) r x ltac:(lia) ltac:(unfold kFakeStackSize in FC; lia) Hin Hr) as [H | H];
    [exact (Hf H) | exact (H Ha)].
Qed.

(* The thread cells at the values ctl_fp_of_AR uses are non-empty ranges. *)
Lemma ce_tls_nonempty : forall TP DT TS C T DB k r,
  In r (lib.B.Prog.RcAsanFP.fp_tls TP DT TS C T DB k) -> fst r < snd r.
Proof.
  intros TP DT TS C T DB k r Hin. unfold lib.B.Prog.RcAsanFP.fp_tls in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst snd]; lia |]). destruct Hin.
Qed.

(* A write range all of whose bytes are not owned and outside the side stack's header [ly_F, ly_F + 36864) is apart
   from the thread cells (owned: fp_tls_owned) and from that header. *)
Lemma ce_dj_tls : forall ly S (W : world SEGS) m md q n, AR SEGS B ly S W m md -> 0 <= n ->
  (forall x, q <= x < q + Z.max n 1 -> ~ aowned B ly S x /\ ~ (ly_F ly <= x < ly_F ly + 36864)) ->
  forall r, In r (lib.B.Prog.RcAsanFP.fp_tls lib.B.AsanRT.RT_TP (Z_to_bv 64 (lib.B.AsanRT.RT_TP + 32))
                    (Z_to_bv 64 (ly_tsd ly)) (Z_to_bv 64 (ly_C ly)) (Z_to_bv 64 (ly_T ly))
                    (Z_to_bv 64 (ly_D ly)) 0 ++
                  [(ly_F ly, lib.B.Prog.asan_stack_malloc_c.fs_frame (ly_F ly) 0 0)]) ->
  ly_dj q (q + n) (fst r) (snd r).
Proof.
  intros ly S W m md q n HAR Hn Hx r Hin. apply in_app_or in Hin as [Hin | [<- | []]].
  - apply ce_dj_bytes; [exact Hn | exact (ce_tls_nonempty _ _ _ _ _ _ _ r Hin) |].
    intros x Hr Hq. apply (proj1 (Hx x Hq)).
    apply (TLSOWN HTS AR_laws_B ly S W m md x HAR). apply Exists_exists. exists r. split; [exact Hin | exact Hr].
  - cbn [fst snd]. unfold lib.B.Prog.asan_stack_malloc_c.fs_frame. cbn [Z.of_nat].
    apply ce_dj_bytes; [exact Hn | lia |]. intros x Hr Hq. apply (proj2 (Hx x Hq)). lia.
Qed.

(* ---- the run-level state at a stretch base (decisions.md items 24 / 26 / 27: every fact taken at the stretch's
   OWN base memory m from AR, then carried to normalize m, where the _F lemmas are applied unchanged) ---- *)
Lemma ce_win_app : forall ly S (W : world SEGS) m md a, AR SEGS B ly S W m md ->
  ly_stk_lo ly <= a < ly_stk_hi ly -> lib.B.AsanRT.app_mem a.
Proof.
  intros ly S W m md a HAR Ha. pose proof (lo_top _ (ce_layout ly S W m md HAR)) as Htop.
  unfold page_aligned, kHighMemEnd, kHighMemBeg in Htop.
  unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END. lia.
Qed.

Lemma ce_base : forall ly S (W : world SEGS) m md (LO SP0 o f mdp d s RR : Z) cid pos,
  AR SEGS B ly S W m md -> arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) m) ->
  ly_stk_lo ly <= LO -> SP0 = LO + 4640 -> SP0 <= ly_stk_hi ly ->
  In (cid, pos) (frames S) -> 2 <= cid -> frame_addr ly cid pos <= o ->
  o + 1492 <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 <= RR <= 1492 ->
  (forall x, f <= x < f + 24 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F ly <= x < ly_F ly + 2134016)) ->
  (forall x, mdp <= x < mdp + 296 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F ly <= x < ly_F ly + 2134016)) ->
  (forall x, d <= x < d + 6 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F ly <= x < ly_F ly + 2134016)) ->
  (forall x, s <= x < s + 6 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F ly <= x < ly_F ly + 2134016)) ->
  lib.B.MemNorm.ro_agree RS m /\
  lib.Lib.Mem.mem_inv RS (lib.B.MemNorm.normalize RS m) /\
  lib.B.AsanRT.asan_cells (lib.B.MemNorm.normalize RS m) /\
  lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS m) LO 4640 /\
  lib.B.Prog.RcAsanFP.fp [0%nat; 1%nat] (lib.B.MemNorm.normalize RS m) lib.B.AsanRT.RT_TP (ly_F ly) LO SP0
    [(LO, SP0); (o, o + RR)] [(f, f + 24); (mdp, mdp + 296); (d, d + 6); (s, s + 6); (o, o + RR)] /\
  lib.B.Prog.ctrl_emit_as_c.ctrl_emit_as_tls (lib.B.MemNorm.normalize RS m) lib.B.AsanRT.RT_TP (ly_F ly) LO SP0.
Proof.
  intros ly S W m md LO SP0 o f mdp d s RR cid pos HAR HRO Hlo HSP Hhi Hin Hc Ho1 Ho2 HRR Hf Hmd Hd Hs.
  pose proof (ce_fs_place ly S W m md HAR) as (F0 & Fal & FC & Fapp & CS).
  pose proof (ce_frame_lo ly S W m md cid pos HAR Hin Hc) as Hfl.
  pose proof (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)) as HROP.
  pose proof (lib.B.ProgWorldCtlRt.asan_cells_of_AR B HTS ly S W m md HAR) as HAC.
  pose proof (lib.B.ProgWorldCtlRt.ro_agree_of_AR B HTS OWNRO RLO RHI ly S W m md HAR HROP) as HRA.
  assert (RO : lib.B.MemNorm.ro_agree RS m) by exact HRA.
  assert (Wapp : forall a, LO <= a < SP0 -> lib.B.AsanRT.app_mem a)
    by (intros a Ha; apply (ce_win_app ly S W m md a HAR); lia).
  split; [exact RO|]. split; [apply lib.B.MemNorm.mem_inv_normalize|].
  split; [exact (lib.B.MemNormTr.asan_cells_normalize m RO HAC)|].
  split.
  { apply (lib.B.MemNormTr.addressable_normalize m LO 4640 RO).
    apply (ce_stack_addr ly S W m md LO 4640 HAR Hlo ltac:(lia) ltac:(lia)). intros a Ha. apply Wapp. lia. }
  split.
  - apply (lib.B.MemNormTr.fp_normalize _ m _ _ _ _ _ _ RO).
    apply (FPAR HTS AR_laws_B ly S W m md [0%nat; 1%nat] LO SP0 _ _ HAR).
    + repeat constructor.
    + unfold lib.B.Prog.asan_stack_malloc_c.FS_SIZE. unfold kFakeStackSize in FC. lia.
    + exact Wapp.
    + unfold lib.B.Prog.RcAsanFP.fp_dj. constructor; [|constructor; [|constructor]].
      * apply Forall_forall. intros r Hr. cbn [fst snd]. rewrite HSP.
        apply (ce_dj_tls ly S W m md LO 4640 HAR ltac:(lia)); [|exact Hr].
        intros x Hx. split; [apply (al_stack _ _ AR_laws_B ly S W m md x HAR); lia | unfold kFakeStackSize in FC; lia].
      * apply Forall_forall. intros r Hr. cbn [fst snd].
        apply (ce_dj_tls ly S W m md o RR HAR ltac:(lia)); [|exact Hr].
        intros x Hx.
        destruct (ce_frame_byte ly S W m md cid pos x HAR Hin ltac:(lia)) as (_ & _ & Hno & _).
        split; [exact Hno | lia].
    + unfold lib.B.Prog.RcAsanFP.fp_dj.
      repeat (constructor; [apply Forall_forall; intros r Hr; cbn [fst snd]|]); [ | | | | | constructor].
      * apply (ce_dj_fpw ly S W m md f 24 HAR ltac:(lia)); [|exact Hr]. intros x Hx. apply Hf. lia.
      * apply (ce_dj_fpw ly S W m md mdp 296 HAR ltac:(lia)); [|exact Hr]. intros x Hx. apply Hmd. lia.
      * apply (ce_dj_fpw ly S W m md d 6 HAR ltac:(lia)); [|exact Hr]. intros x Hx. apply Hd. lia.
      * apply (ce_dj_fpw ly S W m md s 6 HAR ltac:(lia)); [|exact Hr]. intros x Hx. apply Hs. lia.
      * apply (ce_dj_fpw ly S W m md o RR HAR ltac:(lia)); [|exact Hr]. intros x Hx.
        destruct (ce_frame_byte ly S W m md cid pos x HAR Hin ltac:(lia)) as (Ha & _).
        split; [exact Ha | lia].
  - apply (lib.B.MemNormTr.tls_dj_normalize m _ _ RO).
    exact (TLSAP HTS AR_laws_B ly S W m md [0%nat; 1%nat] LO SP0 HAR ltac:(repeat constructor) Hlo Hhi).
Qed.

(* ---- the footprint of a stretch, RNG_W (ce_H (w_H W') FS): a range is a footprint range when its bytes are
   visible and lie off the class-0 / class-1 side-stack bytes; for a range of application memory and for the
   8-aligned shadow word cover of one, those reduce to placement facts.  FS = ly_F, an owned extent in
   application memory (lo_app), 64-aligned. ---- *)
Lemma ce_F_app : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md -> in_app (ly_F ly) kFakeStackSize.
Proof.
  intros ly S W m md HAR.
  exact (proj1 (Forall_forall _ _) (lo_app _ (ce_layout ly S W m md HAR)) (ly_F ly, kFakeStackSize)
           ltac:(unfold owned_extents; cbn [In]; tauto)).
Qed.

Lemma ce_shadow_not_cls : forall FS s, in_app FS kFakeStackSize ->
  lib.B.AsanRT.ASAN_K <= s < lib.B.AsanRT.HIGHMEM_BEG -> ~ (FS <= s < FS + 2134016).
Proof.
  intros FS s (H0 & H) Hs. unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in H.
  unfold lib.B.AsanRT.ASAN_K, lib.B.AsanRT.HIGHMEM_BEG in Hs. destruct H as [H | [H1 H2]]; lia.
Qed.

Lemma ce_app_not_clsh : forall FS a, in_app FS kFakeStackSize -> lib.B.AsanRT.app_mem a ->
  ~ (lib.B.AsanRT.shadow_addr (FS + 36864) <= a < lib.B.AsanRT.shadow_addr (FS + 2134016)).
Proof.
  intros FS a (H0 & H) Ha Hr. pose proof ASAN_CEIL_range as (CR & _).
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in H.
  unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END in Ha.
  unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in Hr.
  assert (0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia).
  assert ((FS + 2134016) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (E8 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity. rewrite E8 in *. lia.
Qed.

Lemma ce_rng_bytes : forall (W' : world SEGS) FS q n, in_app FS kFakeStackSize ->
  0 <= q -> q + n <= 2 ^ 64 ->
  (forall a, q <= a < q + n ->
     w_H W' (Z_to_bv 64 a) = false /\ lib.B.AsanRT.app_mem a /\ ~ (FS <= a < FS + 2134016)) ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) q n.
Proof.
  intros W' FS q n HF Hq Hn H. apply ce_rng_of; [exact Hq | exact Hn | intros a Ha; exact (proj1 (H a Ha)) |].
  intros a Ha. destruct (H a Ha) as (_ & Hap & Hc). split; [exact Hc | exact (ce_app_not_clsh FS a HF Hap)].
Qed.

(* The 8-aligned shadow word cover of [a, b] inside an application range [q, q + n) lies in the shadow band
   [ASAN_K, HIGHMEM_BEG), and off the side stack's class-0/1 shadow when [q, q + n) is off [FS, FS + 2134016). *)
Lemma ce_cover_band : forall q n a b s, 0 <= q -> q + n <= lib.B.AsanRT.APPMEM_END -> q <= a -> a <= b ->
  b <= q + n - 1 ->
  (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s < (b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 ->
  lib.B.AsanRT.ASAN_K <= s < lib.B.AsanRT.HIGHMEM_BEG.
Proof.
  intros q n a b s Hq Hn Ha Hab Hb Hs.
  unfold lib.B.AsanRT.ASAN_K, lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END in *. rlia.
Qed.

Lemma ce_cover_off : forall FS q n a b s, FS mod 64 = 0 -> 0 <= FS -> 0 <= q ->
  (q + n <= FS \/ FS + 2134016 <= q) -> q <= a -> a <= b -> b <= q + n - 1 ->
  (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s < (b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 ->
  ~ (lib.B.AsanRT.shadow_addr (FS + 36864) <= s < lib.B.AsanRT.shadow_addr (FS + 2134016)).
Proof.
  intros FS q n a b s HF HF0 Hq Hside Ha Hab Hb Hs.
  unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in *. rlia.
Qed.

Lemma ce_rng_cover : forall (W' : world SEGS) FS q n, in_app FS kFakeStackSize -> FS mod 64 = 0 ->
  0 <= q -> q + n <= lib.B.AsanRT.APPMEM_END -> (q + n <= FS \/ FS + 2134016 <= q) ->
  (forall s, (q / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s <
             ((q + n - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 -> w_H W' (Z_to_bv 64 s) = false) ->
  forall a b, q <= a -> a <= b -> b <= q + n - 1 ->
    lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS))
      ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
      ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8).
Proof.
  intros W' FS q n HF HF64 Hq Hn Hside Hvis a b Ha Hab Hb.
  pose proof HF as (HF0 & _).
  assert (M1 : (q / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
    by (apply ctrl_emit_asF.dcF_alig_mono; lia).
  assert (M2 : (b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= ((q + n - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
    by (apply ctrl_emit_asF.dcF_alig_mono; lia).
  apply ce_rng_of.
  - unfold lib.B.AsanRT.ASAN_K. rlia.
  - unfold lib.B.AsanRT.ASAN_K, lib.B.AsanRT.APPMEM_END in *. rlia.
  - intros s Hs. apply Hvis. lia.
  - intros s Hs. assert (Hs' : (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s < (b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8)
      by lia.
    split; [apply (ce_shadow_not_cls FS s HF); exact (ce_cover_band q n a b s Hq Hn Ha Hab Hb Hs') |].
    exact (ce_cover_off FS q n a b s HF64 ltac:(unfold kFakeStackSize in *; lia) Hq Hside Ha Hab Hb Hs').
Qed.

(* ---- the lift of one stretch: the _F run on normalize m (decision 27b), carried back to the real memory by
   ProgWorld.rebase_ro_normalize, lifted by YA0nR.SRr_fsteps under RNG_W (ce_H (w_H W) FS); the continuation gets
   the real end state s, the normalized one s0 the _F post speaks of, their relation, and the bytes ce_H hides
   unchanged. ---- *)
Definition ce_rb (m : word -> option byte) (s s0 : machine_state) : Prop :=
  lib.B.MemNorm.ms_rel RS s s0 /\ lib.B.MemNorm.ro_agree RS (ms_mem s) /\
  (forall a, lib.Lib.Mem.mrd RS (ms_mem s) a = lib.Lib.Mem.mrd RS (ms_mem s0) a) /\
  (forall a bs, lib.Lib.Mem.bytes_at RS (ms_mem s) a bs <-> lib.Lib.Mem.bytes_at RS (ms_mem s0) a bs) /\
  (forall a n, lib.Lib.Mem.wr_at RS (ms_mem s0) a n -> lib.Lib.Mem.wr_at RS (ms_mem s) a n) /\
  (forall WR, lib.Lib.Frame.munch WR (lib.B.MemNorm.normalize RS m) (ms_mem s0) ->
              lib.Lib.Frame.munch WR m (ms_mem s)) /\
  (lib.Lib.Frame.wmono RS (lib.B.MemNorm.normalize RS m) (ms_mem s0) -> lib.Lib.Frame.wmono RS m (ms_mem s)).

Lemma ce_lift : forall (W : world SEGS) R F pc fc (m : word -> option byte) md FS (P : machine_state -> Prop)
    (Q : world SEGS -> config -> Prop),
  lib.B.Prog.asan_stack_malloc_c.ASAN_GT <= FS ->
  lib.B.MemNorm.ro_agree RS m ->
  lib.Lib.ExecF.evtF RS (lib.B.ProgBridge.RNG_W (ce_H (w_H W) FS)) P
    (lib.Lib.MState.MS R F pc fc None (lib.B.MemNorm.normalize RS m) (lib.Lib.PropExec.seg_rom RS)) ->
  (forall s s0 md', P s0 -> ce_rb m s s0 ->
     (forall x : word, ce_H (w_H W) FS x = true -> ms_mem s x = m x) ->
     same_but_materialized md md' -> SRr SEGS W (mkCfg s md') Q) ->
  SRr SEGS W (mkCfg (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom RS)) md) Q.
Proof.
  intros W R F pc fc m md FS P Q HGT RO HP HK.
  destruct (lib.B.ProgBridge.fevt_of_evtF _ _ _ (lib.B.ProgWorld.rebase_ro_normalize _ P R F pc fc None m _ RO HP))
    as (s & Hrun & s0 & HP0 & Hrel & Hro & _ & Hmrd & Hby & Hwr & Hmu & Hwm & _).
  apply (lib.Reusable.YA0nR.SRr_fsteps SEGS ce_wx W _ s md _ Q Hrun (ce_fp_avoids_H W FS)).
  intros md' Hmd.
  apply (HK s s0 md' HP0 (conj Hrel (conj Hro (conj Hmrd (conj Hby (conj Hwr (conj Hmu Hwm))))))); [|exact Hmd].
  intros x Hx.
  exact (lib.Reusable.YA0nR.fsteps_keeps_hidden SEGS ce_wx (ce_H (w_H W) FS) _ _ s (ce_H_off W FS HGT) Hrun
           (lib.B.ProgBridge.fp_avoids_RNG_W _) x Hx).
Qed.

Lemma ce_outside_iff : forall (l : list lib.Lib.Frame.ivl) x,
  lib.Lib.Frame.outside l x <-> (forall r, In r l -> ~ (fst r <= x < snd r)).
Proof.
  induction l as [|[lo hi] l IH]; intros x; cbn [lib.Lib.Frame.outside In].
  - split; [intros _ r []|intros _; exact I].
  - rewrite IH. split.
    + intros [H1 H2] r [<- | Hr]; [exact H1 | exact (H2 r Hr)].
    + intros H. split; [exact (H (lo, hi) (or_introl eq_refl)) | intros r Hr; exact (H r (or_intror Hr))].
Qed.

(* What a stretch with the munch list of ctrl_emit_asF's posts changes: only bytes of the window and the output.
   The class-0/1 side-stack bytes are hidden (unchanged), and the window's shadow reads 0 before and after. *)
Lemma ce_stretch_keep : forall (mb mf : word -> option byte) (FS LO o R : Z),
  0 <= LO -> LO mod 8 = 0 -> LO + 4640 <= lib.B.AsanRT.APPMEM_END ->
  lib.Lib.Frame.munch ([(LO, LO + 4640); (o, o + R)] ++ lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS ++
     [(lib.B.AsanRT.shadow_addr LO, lib.B.AsanRT.shadow_addr (LO + 4640))]) mb mf ->
  (forall x, ce_fpwb FS x = true -> mf x = mb x) ->
  lib.B.AsanRT.addressable mb LO 4640 -> lib.B.AsanRT.addressable mf LO 4640 ->
  forall x : word, ~ (LO <= bv_unsigned x < LO + 4640) -> ~ (o <= bv_unsigned x < o + R) -> mf x = mb x.
Proof.
  intros mb mf FS LO o R H0 H8 HE MU HID AD AD' x Hw Ho.
  destruct (ce_fpwb FS x) eqn:Ef; [exact (HID x Ef)|].
  pose proof (ce_u64 x) as Rx.
  destruct (Z_lt_le_dec (bv_unsigned x) (lib.B.AsanRT.shadow_addr LO)) as [Hs1 | Hs1];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (lib.B.AsanRT.shadow_addr (LO + 4640))) as [Hs2 | Hs2]].
  2: { (* a byte of the window's shadow: 0 before and after *)
    set (i := bv_unsigned x - lib.B.AsanRT.shadow_addr LO).
    assert (Hi : 0 <= i < 4640 / 8).
    { unfold i. unfold lib.B.AsanRT.shadow_addr in *. change (4640 / 8) with 580.
      assert ((LO + 4640) / 8 = LO / 8 + 580) by (Z.div_mod_to_equations; lia). lia. }
    pose proof (ce_shadow_zero_of_addr mb LO 4640 AD H8 eq_refl i Hi) as E.
    pose proof (ce_shadow_zero_of_addr mf LO 4640 AD' H8 eq_refl i Hi) as E'.
    replace (lib.B.AsanRT.shadow_addr LO + i) with (bv_unsigned x) in E, E' by (unfold i; lia).
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa in E, E'. rewrite Z_to_bv_bv_unsigned in E, E'.
    assert (Hr : lib.Lib.PropExec.seg_rom RS x = None).
    { pose proof (ce_rom_none (bv_unsigned x) Rx) as N. rewrite Z_to_bv_bv_unsigned in N. apply N.
      left. unfold lib.B.AsanRT.shadow_addr, lib.B.AsanRT.ASAN_K in Hs1.
      assert (0 <= LO / 8) by (apply Z.div_pos; lia). lia. }
    destruct (mb x) as [b|], (mf x) as [b'|]; rewrite ?Hr in E, E'; congruence. }
  all: apply MU; apply ce_outside_iff; intros r Hr Hin; apply in_app_or in Hr as [Hr | Hr];
    [cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin; [exact (Hw Hin) | exact (Ho Hin)] |].
  all: apply in_app_or in Hr as [Hr | [<- | []]]; [|cbn [fst snd] in Hin; lia].
  all: assert (Ht : ce_fpwb FS x = true) by
         (unfold ce_fpwb; apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  all: congruence.
Qed.

(* The caller's journal across a stretch whose changed bytes are all bytes the caller lets the call write. *)
Lemma ce_jrnl2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k mdc'
    (m' : word -> option byte) (Wr : Z -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (forall a, Wr a \/ ~ Wr a) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> m' x = memc x) ->
  (forall x : word, Wr (bv_unsigned x) -> memc x <> None -> m' x <> None) ->
  (forall x : word, w_H W x = true -> m' x = memc x) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' m' Wr HJ Hdec Hkeep Hgrow Hhid Hsame HW.
  eapply (ajournal_exec SEGS B AR_laws_B ce_segs_low) with (Wr := Wr);
    [exact HJ | | | exact Hhid | exact Hsame | exact HW].
  - intros x Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|]. exact (Hkeep x Hx).
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|].
    destruct (Hdec (bv_unsigned x)) as [Hw | Hw]; [exact (Hgrow x Hw Hx) | rewrite (Hkeep x Hw); exact Hx].
Qed.

(* acall_kept: from the call state to itself, and composition when the second window and set lie in the first. *)
Lemma ce_kept_refl : forall lyc Sc (W : world SEGS) memc slo shi (E : Z -> Prop),
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
  acall_kept SEGS B lyc Sc W memc W memc slo shi E.
Proof.
  intros lyc Sc W memc slo shi E H. unfold acall_kept.
  split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|]. exact H.
Qed.

Lemma ce_kept_trans : forall lyc Sc (W1 W2 W3 : world SEGS) m1 m2 m3 slo shi slo' shi' (E E' : Z -> Prop),
  acall_kept SEGS B lyc Sc W1 m1 W2 m2 slo shi E ->
  acall_kept SEGS B lyc Sc W2 m2 W3 m3 slo' shi' E' ->
  slo <= slo' -> shi' <= shi -> (forall a, E' a -> E a) -> ASAN_CEIL <= slo -> shi <= 2 ^ 64 ->
  acall_kept SEGS B lyc Sc W1 m1 W3 m3 slo shi E.
Proof.
  intros lyc Sc W1 W2 W3 m1 m2 m3 slo shi slo' shi' E E'
    (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6) H1 H2 HE HC H64.
  unfold ASAN_CEIL in HC.
  split; [intros a Ha Hw; rewrite (B1 a Ha ltac:(rlia)); exact (A1 a Ha Hw)|].
  split; [intros b m i Hb Hi He; rewrite (B2 b m i Hb Hi (fun h => He (HE _ h))); exact (A2 b m i Hb Hi He)|].
  split; [intros a Ha Hn He; rewrite (B3 a Ha Hn He); exact (A3 a Ha Hn He)|].
  split; [intros cid pos a Hin Hr He; rewrite (B4 cid pos a Hin Hr (fun h => He (HE _ h)));
          exact (A4 cid pos a Hin Hr He)|].
  split; [intros a Ha Hw Hp; exact (B5 a Ha ltac:(lia) (A5 a Ha Hw Hp))|].
  intros a Ha. destruct (Z_lt_le_dec a slo') as [h | h]; [|destruct (Z_lt_le_dec a shi') as [h' | h']].
  - apply B5; [rlia | rlia | exact (A6 a Ha)].
  - exact (B6 a ltac:(rlia)).
  - apply B5; [rlia | rlia | exact (A6 a Ha)].
Qed.

(* acall_kept from the call state across a stretch that changes only window and output bytes. *)
Lemma ce_kept_step : forall lyc Sc (W Wb : world SEGS) memc mdc (mb mf : word -> option byte) (LO o R : Z) cid pos,
  AR SEGS B lyc Sc W memc mdc -> ly_stk_lo lyc <= LO ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= o ->
  o + R <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  acall_kept SEGS B lyc Sc W memc Wb mb LO (LO + 4640) (tctrl_emit_as_out o R) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (LO <= a < LO + 4640) -> ~ (o <= a < o + R) ->
     mf (Z_to_bv 64 a) = mb (Z_to_bv 64 a)) ->
  (forall a, LO <= a < LO + 4640 -> apresent (w_H Wb) mf a) ->
  acall_kept SEGS B lyc Sc W memc Wb mf LO (LO + 4640) (tctrl_emit_as_out o R).
Proof.
  intros lyc Sc W Wb memc mdc mb mf LO o R cid pos HAR Hlo Hin Ho1 Ho2 (A1 & A2 & A3 & A4 & A5 & A6) HK HP.
  pose proof (ce_fs_place lyc Sc W memc mdc HAR) as (_ & _ & _ & _ & CS).
  destruct (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin) as (Fo0 & Fo1 & _).
  pose proof ASAN_CEIL_range as (CR & _). unfold ASAN_CEIL in *.
  assert (Kv : forall a, 0 <= a < 2 ^ 64 -> ~ (LO <= a < LO + 4640) -> ~ (o <= a < o + R) ->
             aview SEGS (w_H Wb) mf a = aview SEGS (w_H Wb) mb a).
  { intros a Ha H1 H2. apply (aview_eq_of SEGS). unfold mrestrict.
    destruct (w_H Wb (Z_to_bv 64 a)); [reflexivity | exact (HK a Ha H1 H2)]. }
  unfold tctrl_emit_as_out in *.
  split; [intros a Ha Hw; rewrite (Kv a ltac:(rlia) Hw ltac:(rlia)); exact (A1 a Ha Hw)|].
  split.
  { intros b m i Hb Hi He.
    destruct (al_blocks _ _ AR_laws_B lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hceilb & _).
    rewrite (Kv (b + i) ltac:(rlia) ltac:(rlia) He). exact (A2 b m i Hb Hi He). }
  split.
  { intros a Ha Hn He. pose proof (ce_segs_low a Ha) as Hl. unfold kLowMemEnd in Hl.
    assert (Ho : ~ (o <= a < o + R)).
    { intros Hr. apply (proj2 (proj2 (proj2 (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin ltac:(rlia))))).
      exact Ha. }
    rewrite (Kv a ltac:(rlia) ltac:(rlia) Ho). exact (A3 a Ha Hn He). }
  split.
  { intros cid' pos' a Hin' Hr He.
    destruct (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin') as (G0 & G1 & _).
    pose proof (fs_frame_bytes_nonneg cid') as Gn.
    assert (Ha : 0 <= a < ASAN_CEIL).
    { unfold ASAN_CEIL. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr;
        [rlia | unfold shadow_addr, SHADOW_OFF in Hr; rlia]. }
    unfold ASAN_CEIL in Ha.
    rewrite (Kv a ltac:(rlia) ltac:(rlia) He). exact (A4 cid' pos' a Hin' Hr He). }
  split.
  { intros a Ha Hw Hp. destruct (A5 a Ha Hw Hp) as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite (HK a ltac:(rlia) Hw ltac:(rlia)). exact Hb. }
  exact HP.
Qed.

(* awr_byte reads the layout only through ly_F (frame_addr). *)
Lemma ce_awr_ly : forall STK sp0 FP bl0 blc ly ly' own a, ly_F ly' = ly_F ly ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof. intros STK sp0 FP bl0 blc ly ly' own a E H. unfold awr_byte, in_frames, frame_addr in *. rewrite E. exact H. Qed.

Lemma ce_addr_mrd : forall (m1 m2 : word -> option byte) p n,
  (forall a, lib.Lib.Mem.mrd RS m1 a = lib.Lib.Mem.mrd RS m2 a) ->
  lib.B.AsanRT.addressable m2 p n -> lib.B.AsanRT.addressable m1 p n.
Proof.
  intros m1 m2 p n E (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. rewrite E. split; assumption.
Qed.

Lemma ce_raw_of_mrd : forall (m : word -> option byte) a b, 0 <= a < 2 ^ 64 -> (0x5fe000 <= a \/ a < 0x10000) ->
  lib.Lib.Mem.mrd RS m (Z_to_bv 64 a) = Some b -> m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a b Ha Hn H. unfold lib.Lib.Mem.mrd in H. destruct (m (Z_to_bv 64 a)); [exact H|].
  assert (N : lib.Lib.PropExec.seg_rom RS (Z_to_bv 64 a) = None) by (apply (ce_rom_none a Ha Hn)).
  rewrite N in H. discriminate H.
Qed.

(* the lengths of the emitted record *)
Lemma ce_lay_len : forall row tb mb nb gb md g,
  length mb = 296%nat -> (ly_k row = 2 -> length tb = 32%nat) ->
  (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row) -> ly_ao row + ly_al row <= 32 ->
  length (tctrl_emit_as_lay row tb mb nb gb md g) = 32%nat.
Proof.
  intros row tb mb nb gb md g Hmb Htb Hgb Hao.
  assert (R0 : 0 <= ly_ao row) by (unfold ly_ao, lib.Prog.RcPorts.rc_u8; apply bv_unsigned_in_range).
  assert (HB : length (ly_base (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row)))) = 32%nat).
  { unfold ly_base. destruct (ly_k row =? 0) eqn:E0; [reflexivity|].
    destruct (ly_k row =? 1) eqn:E1; [reflexivity|].
    destruct (ly_k row =? 2) eqn:E2; [apply Z.eqb_eq in E2; exact (Htb E2)|].
    unfold ly_Z. destruct (md =? 0); [reflexivity|].
    destruct (lib.Prog.RcSynth.rc mb (ly_bb (ly_k row)) =? 1);
      [exact (lib.Prog.RcSynthLib.rs_synth_len mb _ nb Hmb) | reflexivity]. }
  unfold tctrl_emit_as_lay, ly_lay. destruct ((g =? 0) || (ly_al row =? 0)) eqn:Eg; [exact HB|].
  apply orb_false_iff in Eg as [Eg1 Eg2]. apply Z.eqb_neq in Eg1, Eg2.
  pose proof (Hgb Eg1 Eg2) as Hl.
  unfold ly_put. rewrite !length_app, length_firstn, length_skipn, HB. lia.
Qed.

Lemma ce_fin_len : forall c o n bs, length bs = 32%nat -> 0 <= o -> (c = 2 -> 2 <= n /\ o + n <= 31) ->
  length (fin c o n bs) = 32%nat.
Proof.
  intros c o n bs Hl Ho Hc. unfold fin.
  destruct (c =? 2) eqn:E2.
  - apply Z.eqb_eq in E2. destruct (Hc E2) as [H1 H2].
    apply lib.Prog.RcFinLib.rcf_stamp32_len, lib.Prog.RcFinLib.rcf_rstamp_len; lia.
  - destruct (c =? 1); [apply lib.Prog.RcFinLib.rcf_stamp32_len; exact Hl | exact Hl].
Qed.

Lemma ce_em_fr_len : forall d6 s6 c t0 t1 blk len, length d6 = 6%nat -> length s6 = 6%nat ->
  length blk = 32%nat -> 52 <= len -> Z.of_nat (length (em_fr d6 s6 c t0 t1 blk len)) = len.
Proof.
  intros d6 s6 c t0 t1 blk len H1 H2 H3 H4. unfold em_fr, em_hdr.
  rewrite !length_app, repeat_length. cbn [length]. lia.
Qed.

(* The function's return state keeps the callee-saved registers of the entry. *)
Lemma ce_preserved : forall (regs : bvmap 5 word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  aregs_preserved regs
    (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
       (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) t0 t1 t2
       (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) a0 a1 a2 a3 a4 a5 a6 a7
       (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
       (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
       (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
       (lib.Reusable.YK11.getr regs 27) t3 t4 t5 t6).
Proof.
  intros regs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr' as [-> | Hr']; [reflexivity |]). subst r. reflexivity.
Qed.

(* ---- the end of the function: from the _F post aQp_on of the last stretch (based at the memory mbase of the world
   Wb, where the caller's journal and acall_kept from the call state hold) to tctrl_emit_as_post ---- *)
Lemma ce_finish : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (o f mdp d s g n : Z) (row tb mb nb gb db sb : list byte) cid pos
    lyb Sb (Wb : world SEGS) mbase mdb (st st0 : machine_state) md',
  AR SEGS B lyc Sc W memc mdc ->
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) ->
  ly_stk_lo lyc <= spZ regs - 4640 -> spZ regs <= ly_stk_hi lyc -> spZ regs <= sp0 -> sp0 - STK <= spZ regs - 4640 ->
  spZ regs mod 16 = 0 ->
  In (cid, pos) (frames Sc) -> 2 <= cid -> frame_addr lyc cid pos <= o ->
  o + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  length db = 6%nat -> length sb = 6%nat -> length mb = 296%nat -> (ly_k row = 2 -> length tb = 32%nat) ->
  (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row) -> ly_ao row + ly_al row <= 32 ->
  (ubat row 20 = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
  (tctrl_emit_as_E row mb n = true -> forall a, o <= a < o + tctrl_emit_as_len row n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyb Sb Wb mbase mdb (k + 0) ->
  wle W Wb -> frames Sb = frames Sc -> ablocks B lyb Sb = ablocks B lyc Sc -> ly_F lyb = ly_F lyc ->
  acall_kept SEGS B lyc Sc W memc Wb mbase (spZ regs - 4640) (spZ regs - 4640 + 4640)
    (tctrl_emit_as_out o (tctrl_emit_as_R row mb n)) ->
  lib.B.AsanRT.addressable mbase (spZ regs - 4640) 4640 ->
  lib.B.Prog.ctrl_emit_asF.aQp_on (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
    (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
    (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
    (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
    (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS mbase) o f mdp d s g n
    (ly_F lyc) row tb mb nb gb db sb st0 ->
  ce_rb mbase st st0 ->
  (forall x : word, ce_H (w_H Wb) (ly_F lyc) x = true -> ms_mem st x = mbase x) ->
  same_but_materialized mdb md' ->
  tctrl_emit_as_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o mdp g n row tb mb nb gb db sb
    Wb (mkCfg st md').
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o f mdp d s g n row tb mb nb gb db sb cid pos
    lyb Sb Wb mbase mdb st st0 md' HAR Hret Hlo Hhi Hsp Hst H16 Hin Hc Ho1 Ho2 Hdb Hsb Hmb Htb Hgb Hao Hc2 HEo
    HJb Hwle Hfrs Hbl HF Hkb Hadb HQ Hrb Hhid Hmd.
  destruct Hrb as (Hrel & Hro & Hmrd & Hby & Hwr & Hmu & Hwm).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E0 & MU & WM & MI & ST & AC & SW & AD & FPf & RES).
  subst st0.
  destruct (lib.B.MemNormTr.ms_rel_MS st _ _ _ _ _ _ _ Hrel) as (Est & Erel).
  set (mf := ms_mem st) in *.
  set (RR := tctrl_emit_as_R row mb n).
  set (LO := spZ regs - 4640) in *.
  pose proof (ce_fs_place lyc Sc W memc mdc HAR) as (F0 & Fal & FC & Fapp & CS).
  pose proof (ce_F_above lyc Sc W memc mdc HAR) as FGT.
  pose proof (ce_frame_lo lyc Sc W memc mdc cid pos HAR Hin Hc) as Hfl.
  pose proof (lo_top _ (ce_layout lyc Sc W memc mdc HAR)) as Htop.
  unfold page_aligned, kHighMemEnd, kHighMemBeg in Htop.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT, kFakeStackSize in *.
  assert (HRR : 0 <= RR <= 1492).
  { unfold RR, tctrl_emit_as_R. destruct (tctrl_emit_as_E row mb n) eqn:EE; [|lia].
    pose proof (lib.Prog.RcEmitLib.em_len_rng _ _ _ _ EE) as L. unfold tctrl_emit_as_len. lia. }
  assert (Hsp' : bv_unsigned (lib.Reusable.YK11.getr regs 2) = LO + 4640) by (unfold LO, spZ; lia).
  assert (MUr := Hmu _ MU). assert (WMr := Hwm WM).
  assert (ADf : lib.B.AsanRT.addressable mf LO 4640).
  { apply (ce_addr_mrd mf m'); [exact Hmrd|]. unfold LO, spZ. exact AD. }
  assert (HIDfp : forall x, ce_fpwb (ly_F lyc) x = true -> mf x = mbase x).
  { intros x Hx. apply Hhid. unfold ce_H. rewrite Hx. apply orb_true_r. }
  assert (KEEP : forall x : word, ~ (LO <= bv_unsigned x < LO + 4640) -> ~ (o <= bv_unsigned x < o + RR) ->
                   mf x = mbase x).
  { apply (ce_stretch_keep mbase mf (ly_F lyc) LO o RR); [rlia | unfold LO; rlia | unfold lib.B.AsanRT.APPMEM_END; rlia
          | | exact HIDfp | exact Hadb | exact ADf].
    rewrite <- Hsp'. exact MUr. }
  (* the output bytes: in the frame, application memory above the image *)
  assert (Hout : forall a, o <= a < o + RR -> 0x5fe000 <= a < ASAN_CEIL).
  { intros a Ha. destruct (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin ltac:(rlia)) as (_ & Hc' & _).
    rlia. }
  exists lyb, Sb, (ms_regs st), mf, md'.
  split.
  { rewrite Est. unfold lib.Lib.MState.MS, lib.Reusable.YK11.mkst. cbn [ms_regs].
    rewrite (ce_ret_pc _ Hret). reflexivity. }
  split.
  { replace (k + EV_CTRL_EMIT_AS) with (k + 0) by (unfold EV_CTRL_EMIT_AS; reflexivity).
    apply (ce_jrnl2 STK sp0 FP ly S W0 mem0 md0 own lyb Sb Wb mbase mdb (k + 0) md' mf
             (fun a => (LO <= a < LO + 4640) \/ (o <= a < o + RR)) HJb).
    - intros a. rlia.
    - intros x Hx. apply KEEP; intros h; apply Hx; [left | right]; exact h.
    - intros x Hx Hm. pose proof (ce_u64 x) as Rx.
      assert (Hni : ~ in_img SEGS (bv_unsigned x)).
      { apply ce_not_img. left. destruct Hx as [Hx | Hx]; [rlia | pose proof (Hout _ Hx); rlia]. }
      assert (Hwv : wview RS mbase x <> None) by (unfold wview; destruct (mbase x); [discriminate | exfalso; exact (Hm eq_refl)]).
      pose proof (WMr x Hwv) as Hwv'. unfold wview in Hwv'. destruct (mf x); [discriminate|].
      pose proof (find_segment_none SEGS (bv_unsigned x) Hni) as Hfs. change SEGS with RS in Hfs.
      rewrite Hfs in Hwv'. exact Hwv'.
    - intros x Hx. apply Hhid. unfold ce_H. rewrite Hx. reflexivity.
    - exact Hmd.
    - intros a [Ha | Ha]; [left; rlia|].
      assert (EE : tctrl_emit_as_E row mb n = true).
      { destruct (tctrl_emit_as_E row mb n) eqn:E; [reflexivity|]. exfalso. unfold RR, tctrl_emit_as_R in Ha.
        rewrite E in Ha. lia. }
      unfold RR, tctrl_emit_as_R in Ha. rewrite EE in Ha.
      destruct (HEo EE a Ha) as (Hw & _). rewrite Hbl. exact (ce_awr_ly _ _ _ _ _ _ _ _ _ HF Hw). }
  split.
  { rewrite Est. cbn [ms_regs]. apply ce_preserved. }
  split; [exact Hfrs|].
  split; [rewrite Hbl; apply Permutation_refl|].
  split; [rewrite Est; reflexivity|].
  split.
  { intros EE. destruct (RES EE) as (Hb & Hw & Hcl).
    split; [|split; assumption].
    pose proof (ce_lay_len row tb mb nb gb mdp g Hmb Htb Hgb Hao) as LL.
    assert (LB : length (tctrl_emit_as_blk row tb mb nb gb mdp g) = 32%nat).
    { apply ce_fin_len; [exact LL | unfold ubat; apply bv_unsigned_in_range |].
      intros H2. destruct (Hc2 H2) as [H3 H4]. split; [exact H3|]. exact H4. }
    pose proof (lib.Prog.RcEmitLib.em_len_rng _ _ _ _ EE) as Lr.
    pose proof (ce_em_fr_len db sb (bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536)
                  (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0)) _ (tctrl_emit_as_len row n)
                  Hdb Hsb LB ltac:(unfold tctrl_emit_as_len in *; lia)) as EL.
    apply ce_garr8_of_bytes; [apply Hby; exact Hb|].
    intros i Hi.
    assert (Hoi : o <= o + Z.of_nat i < o + tctrl_emit_as_len row n).
    { rewrite <- EL. rlia. }
    destruct (HEo EE _ Hoi) as (_ & Hh & _).
    destruct (w_H Wb (Z_to_bv 64 (o + Z.of_nat i))) eqn:Eh; [|reflexivity].
    rewrite (Hwle _ Eh) in Hh. discriminate Hh. }
  unfold CTRL_EMIT_AS_STK. change (Z.max 4640 (128 + 4512)) with 4640. fold LO.
  replace (spZ regs) with (LO + 4640) by (unfold LO; lia).
  apply (ce_kept_step lyc Sc W Wb memc mdc mbase mf LO o RR cid pos HAR ltac:(exact Hlo) Hin Ho1 ltac:(rlia) Hkb).
  - intros a Ha Hw Ho. apply KEEP; rewrite (lib.Lib.MState.unsigned_lit a ltac:(rlia)); assumption.
  - intros a Ha. pose proof (lib.B.MemNormTr.stk_of_rel mf m' LO (LO + 4640) Erel) as STr.
    assert (STm : lib.Lib.Frame.stk RS m' LO (LO + 4640)) by (rewrite <- Hsp'; exact ST).
    destruct (STr STm) as (_ & _ & Hs). destruct (Hs a Ha) as (_ & b & Hb).
    destruct Hkb as (_ & _ & _ & _ & _ & A6). destruct (A6 a Ha) as (Hh & _).
    split; [exact Hh|]. exists b.
    apply (ce_raw_of_mrd mf a b); [rlia | left; rlia | exact Hb].
Qed.

(* ---- transport of byte facts between memories and worlds ---- *)
Lemma ce_mbyte_of_view : forall (H H' : word -> bool) (m m' : word -> option byte) x,
  aview SEGS H' m' x = aview SEGS H m x -> mbyte SEGS (mrestrict H' m') x = mbyte SEGS (mrestrict H m) x.
Proof.
  intros H H' m m' x E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H' m') x) as [b'|], (mbyte SEGS (mrestrict H m) x) as [b|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma ce_garr8_view : forall (H H' : word -> bool) (m m' : word -> option byte) q (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H' m' (q + Z.of_nat j) = aview SEGS H m (q + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) q l -> garr8 SEGS (mrestrict H' m') q l.
Proof.
  intros H H' m m' q l E HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  rewrite (ce_mbyte_of_view H H' m m'); [exact (HV 0%nat Hk)|].
  replace (q + Z.of_nat j + Z.of_nat 0) with (q + Z.of_nat j) by lia. exact (E j Hj).
Qed.

(* Off the image, a byte read means a present byte, so a byte array there is writable cells. *)
Lemma ce_rw_cb : forall (m : word -> option byte) q bs,
  lib.Lib.Mem.bytes_at RS m q bs -> (forall i, (i < length bs)%nat -> 0x5fe000 <= q + Z.of_nat i) ->
  lib.Lib.Step.rw_cells RS m q [lib.Lib.Cells.CB (length bs) bs].
Proof.
  intros m q bs HB Hi. apply lib.Prog.RcLayLib.ly_cb_rw; [exact HB|].
  destruct HB as (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|]. intros i Hi'.
  assert (Hn : (Z.to_nat i < length bs)%nat) by lia.
  pose proof (HB _ Hn) as E. rewrite Z2Nat.id in E by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (Hi _ Hn) as Hge. rewrite Z2Nat.id in Hge by lia.
  pose proof (ce_raw_of_mrd m (q + i) b ltac:(lia) ltac:(left; lia) E) as Em.
  unfold wview, lib.Lib.Mem.wa. rewrite Em. discriminate.
Qed.

(* The cells of a present, off-image range: its own bytes. *)
Definition ce_junk (m : word -> option byte) (o n : Z) : list byte :=
  map (fun i => match m (Z_to_bv 64 (o + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
    (seq 0 (Z.to_nat n)).

Lemma ce_junk_rw : forall (m : word -> option byte) o n, 0 <= n -> 0x5fe000 <= o -> o + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, m (Z_to_bv 64 (o + i)) = Some b) ->
  lib.Lib.Step.rw_cells RS m o [lib.Lib.Cells.CB (Z.to_nat n) (ce_junk m o n)].
Proof.
  intros m o n Hn Ho Hon Hp.
  assert (Hl : length (ce_junk m o n) = Z.to_nat n) by (unfold ce_junk; rewrite length_map, length_seq; reflexivity).
  rewrite <- Hl at 1. apply ce_rw_cb; [|intros i Hi; lia].
  split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. rewrite Hl in Hi.
  unfold ce_junk. rewrite nth_error_map, nth_error_seq.
  replace (i <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  replace (0 + i)%nat with i by lia. cbn [option_map]. cbv beta.
  destruct (Hp (Z.of_nat i) ltac:(lia)) as (b & Eb).
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Eb. reflexivity.
Qed.

(* A read-only template: the segment bytes of a non-writable segment, read through ro_agree. *)
Definition ce_wseg (i : nat) : bool :=
  match nth_error RS i with Some sg => seg_writable sg | None => false end.

Lemma ce_rsegs_w : map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)) RS =
  [(0x10000, 0x21000, ce_wseg 0); (0x31000, 0x6e000, ce_wseg 1); (0x9f000, 0x3000, ce_wseg 2);
   (0xa2000, 0x55c000, ce_wseg 3)].
Proof. vm_compute. reflexivity. Qed.

Lemma ce_ro_addr_seg : forall sg a, In sg RS -> seg_writable sg = false -> 0 <= a < 2 ^ 64 ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) ->
  lib.Lib.Mem.ro_addr RS (Z_to_bv 64 a) = true.
Proof.
  intros sg a Hin Hw Ha Hr. unfold lib.Lib.Mem.ro_addr. rewrite (lib.Lib.MState.unsigned_lit a Ha).
  destruct (find_segment RS a 1) as [sg'|] eqn:Ef.
  2: { exfalso. exact (lib.B.MemNorm.find_segment_some RS sg a 1 Hin ltac:(lia) ltac:(lia) Ef). }
  pose proof (lib.B.Reusable.YK1j.find_segment_in _ _ _ _ Ef) as Hin'.
  pose proof (lib.B.Reusable.YK1j.find_segment_range _ _ _ _ Ef) as [R1 R2].
  pose proof (in_map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)) _ _ Hin) as M1.
  pose proof (in_map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)) _ _ Hin') as M2.
  rewrite ce_rsegs_w in M1, M2. rewrite Hw in M1.
  cbn [In] in M1, M2.
  destruct M1 as [E1|[E1|[E1|[E1|[]]]]], M2 as [E2|[E2|[E2|[E2|[]]]]];
    pose proof (f_equal (fun p => fst (fst p)) E1) as A1; pose proof (f_equal (fun p => snd (fst p)) E1) as B1;
    pose proof (f_equal snd E1) as C1;
    pose proof (f_equal (fun p => fst (fst p)) E2) as A2; pose proof (f_equal (fun p => snd (fst p)) E2) as B2;
    pose proof (f_equal snd E2) as C2; cbv beta in A1, B1, C1, A2, B2, C2; cbn [fst snd] in A1, B1, C1, A2, B2, C2;
    first [ rewrite <- C2, C1; reflexivity | exfalso; rlia ].
Qed.

Lemma ce_ro_bytes_of : forall bs a,
  (forall i b, nth_error bs i = Some b -> lib.Lib.Mem.ro_byte RS (a + Z.of_nat i) b) ->
  lib.Lib.Mem.ro_bytes RS a bs.
Proof.
  induction bs as [|b bs IH]; intros a H; cbn [lib.Lib.Mem.ro_bytes]; [exact I|].
  split; [specialize (H 0%nat b eq_refl); rewrite Z.add_0_r in H; exact H|].
  apply IH. intros i b' E. specialize (H (S i) b' E).
  replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact H.
Qed.

(* A visible shadow word cover: shadow_hull_vis of the world's view. *)
Lemma ce_hull_vis : forall (H : word -> bool) (m : word -> option byte) q n, 0 <= q ->
  q + n <= lib.B.AsanRT.APPMEM_END ->
  shadow_hull_vis (aview SEGS H m) q n ->
  forall s, (q / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s <
            ((q + n - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 -> H (Z_to_bv 64 s) = false.
Proof.
  intros H m q n Hq Hn HV s Hs.
  assert (Hs' : shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8).
  { unfold shadow_addr, SHADOW_OFF. unfold lib.B.AsanRT.ASAN_K in Hs.
    replace (0x7fff8000 + q / 8) with (q / 8 + 0x7fff8000) by lia.
    replace (0x7fff8000 + (q + n - 1) / 8) with ((q + n - 1) / 8 + 0x7fff8000) by lia. exact Hs. }
  pose proof (HV s Hs') as Hnn.
  destruct (H (Z_to_bv 64 s)) eqn:Eh; [|reflexivity]. exfalso. apply Hnn.
  unfold aview, mbyte, mrestrict. rewrite Eh.
  assert (Hs0 : 0x5fe000 <= s < 2 ^ 64)
    by (unfold lib.B.AsanRT.ASAN_K, lib.B.AsanRT.APPMEM_END in *; rlia).
  rewrite (ce_rom_none s ltac:(lia) (or_introl (proj1 Hs0))). reflexivity.
Qed.

(* The route (C) shadow premise of one range from its shadow_hull_vis: every byte of the range's 8-aligned shadow word
   cover (sh_word_on) is visible, so it is a present byte of m, so a shadow_rw_on byte (ShadowRwOn.srw_byte_of_mem). *)
Lemma ce_srw_hull : forall (W' : world SEGS) (m : word -> option byte) q n,
  0 <= q -> 0 < n -> q + n <= ASAN_CEIL ->
  shadow_hull_vis (aview SEGS (w_H W') m) q n ->
  lib.B.ShadowRwOn.shadow_rw_on (lib.B.Prog.sh_word_on.sh_word_on q n) m.
Proof.
  intros W' m q n Hq Hn Hc HV a (_ & Ha1 & Ha2) _.
  pose proof ASAN_CEIL_range as (CR & _).
  assert (HE : q + n <= lib.B.AsanRT.APPMEM_END) by (unfold lib.B.AsanRT.APPMEM_END, ASAN_CEIL in *; lia).
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi, lib.B.AsanRT.shadow_addr in Ha1, Ha2.
  assert (Hs' : shadow_addr q / 8 * 8 <= a < shadow_addr (q + n - 1) / 8 * 8 + 8).
  { unfold shadow_addr, SHADOW_OFF. unfold lib.B.AsanRT.ASAN_K in Ha1, Ha2.
    replace (0x7fff8000 + q / 8) with (q / 8 + 0x7fff8000) by lia.
    replace (0x7fff8000 + (q + n - 1) / 8) with ((q + n - 1) / 8 + 0x7fff8000) by lia.
    exact (conj Ha1 Ha2). }
  assert (Ha0 : 0x5fe000 <= a < 2 ^ 64)
    by (unfold lib.B.AsanRT.ASAN_K, lib.B.AsanRT.APPMEM_END in *; rlia).
  destruct (aview SEGS (w_H W') m a) as [v|] eqn:Ev; [|exfalso; exact (HV a Hs' Ev)].
  destruct (ce_view_shadow W' m a v ltac:(lia) (proj1 Ha0) Ev) as (_ & b & Hb & _).
  apply lib.B.ShadowRwOn.srw_byte_of_mem. rewrite Hb. discriminate.
Qed.

(* ---- a data range's footprint facts in a stretch whose world W' sees the range and its shadow cover ---- *)
Lemma ce_range_rng : forall (W' : world SEGS) (m' : word -> option byte) FS q n,
  in_app FS kFakeStackSize -> FS mod 64 = 0 -> 0 <= q -> 0 < n -> q + n <= ASAN_CEIL ->
  (q + n <= FS \/ FS + 2134016 <= q) ->
  (forall a, q <= a < q + n -> w_H W' (Z_to_bv 64 a) = false /\ lib.B.AsanRT.app_mem a) ->
  shadow_hull_vis (aview SEGS (w_H W') m') q n ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) q n /\
  (forall a b, q <= a -> a <= b -> b <= q + n - 1 ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
       ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)) /\
  (forall x, q <= x <= q + n - 1 ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) (x / 8 + lib.B.AsanRT.ASAN_K) 1).
Proof.
  intros W' m' FS q n HF H64 Hq Hn Hc Hside Hb HV. pose proof ASAN_CEIL_range as (CR & _).
  assert (HE : q + n <= lib.B.AsanRT.APPMEM_END) by (unfold lib.B.AsanRT.APPMEM_END, ASAN_CEIL in *; lia).
  assert (Hcov := ce_rng_cover W' FS q n HF H64 Hq HE Hside (ce_hull_vis (w_H W') m' q n Hq HE HV)).
  split; [|split; [exact Hcov|]].
  - apply ce_rng_bytes; [exact HF | exact Hq | unfold ASAN_CEIL in *; lia |]. intros a Ha.
    destruct (Hb a Ha) as (H1 & H2). split; [exact H1|]. split; [exact H2 | lia].
  - intros x Hx.
    exact (ctrl_emit_asF.dcF_shadow1 _ lib.B.AsanRT.ASAN_K q (q + n - 1) x
             (Hcov q (q + n - 1) ltac:(lia) ltac:(lia) ltac:(lia)) Hx).
Qed.

(* Where a kept range (f, md, the name) and a home range (d, s, the template, g) lie. *)
Lemma ce_frame_range : forall lyc Sc (W : world SEGS) memc mdc cid pos q n, AR SEGS B lyc Sc W memc mdc ->
  In (cid, pos) (frames Sc) -> 2 <= cid -> 0 < n ->
  (forall a, q <= a < q + n -> in_zr a (frame_rng lyc (cid, pos))) ->
  0 <= q /\ q + n <= ASAN_CEIL /\ (q + n <= ly_F lyc \/ ly_F lyc + 2134016 <= q) /\
  (forall a, q <= a < q + n -> lib.B.AsanRT.app_mem a).
Proof.
  intros lyc Sc W memc mdc cid pos q n HAR Hin Hc Hn Hfr.
  pose proof (ce_frame_lo lyc Sc W memc mdc cid pos HAR Hin Hc) as Hlo.
  pose proof (ce_fs_place lyc Sc W memc mdc HAR) as (F0 & _).
  pose proof (Hfr q ltac:(lia)) as H1. pose proof (Hfr (q + n - 1) ltac:(lia)) as H2.
  unfold in_zr, frame_rng in H1, H2. cbn [fst snd] in H1, H2.
  destruct (ce_frame_byte lyc Sc W memc mdc cid pos (q + n - 1) HAR Hin H2) as (_ & Hc2 & _).
  split; [lia|]. split; [lia|]. split; [right; lia|].
  intros a Ha. pose proof (Hfr a Ha) as H3. unfold in_zr, frame_rng in H3. cbn [fst snd] in H3.
  exact (proj1 (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin H3)).
Qed.

(* Where a registered read-only global lies: low application memory inside the image's read range, below the side
   stack (which is above the image, ce_F_above) and below the ceiling. *)
Lemma ce_ro_place : forall lyc Sc (W : world SEGS) memc mdc q n, AR SEGS B lyc Sc W memc mdc ->
  tctrl_emit_as_ro RLO RHI B GLOBS q n ->
  0 <= q /\ q + n <= ASAN_CEIL /\ (q + n <= ly_F lyc \/ ly_F lyc + 2134016 <= q) /\
  (forall a, q <= a < q + n -> lib.B.AsanRT.app_mem a).
Proof.
  intros lyc Sc W memc mdc q n HAR (_ & Hlo & Hhi & _).
  pose proof (ce_F_above lyc Sc W memc mdc HAR) as FGT. unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT in FGT.
  pose proof ASAN_CEIL_range as (CR & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in Hlo, Hhi.
  split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split; [left; lia|].
  intros a Ha. unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END. left; lia.
Qed.

(* Both shadow facts of a registered read-only global at ANY AR state (CtrlRo.ro_read_ok_glob, from the composer's
   GM and the proved ISV). *)
Lemma ce_ro_read : forall ly' S' (W' : world SEGS) m' md' q n, AR SEGS B ly' S' W' m' md' ->
  tctrl_emit_as_ro RLO RHI B GLOBS q n -> 0 < n ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF q n /\ shadow_hull_vis (aview SEGS (w_H W') m') q n.
Proof.
  intros ly' S' W' m' md' q n HAR ((q0 & sz & Hin & H1 & H2) & Hlo & Hhi & _) Hn.
  exact (CtrlRo.ro_read_ok_glob SEGS B GLOBS ly' S' W' m' md' q0 sz q n GM Hin ISV HAR H1 H2 Hn Hlo Hhi).
Qed.

Lemma ce_home_place : forall lyc Sc (W : world SEGS) memc mdc q n, AR SEGS B lyc Sc W memc mdc -> 0 < n ->
  in_app q n -> tctrl_emit_as_home lyc Sc q n ->
  0 <= q /\ q + n <= ASAN_CEIL /\ (q + n <= ly_F lyc \/ ly_F lyc + 2134016 <= q) /\
  (forall a, q <= a < q + n -> lib.B.AsanRT.app_mem a).
Proof.
  intros lyc Sc W memc mdc q n HAR Hn Happ [Hdj | (cid & pos & Hin & Hc & Hfr)];
    [| exact (ce_frame_range lyc Sc W memc mdc cid pos q n HAR Hin Hc Hn Hfr)].
  pose proof ASAN_CEIL_range as (CR & _). pose proof Happ as (H0 & H1).
  unfold kLowShadowBeg, kHighMemBeg in H1. unfold ly_dj, kFakeStackSize in Hdj.
  split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split; [lia|].
  intros a Ha. replace a with (q + (a - q)) by lia. apply (ce_in_app_mem q n); [exact Happ | lia].
Qed.

(* The state at the ctrl_lay_block call (0x8572c: after alay_pre), in the run's terms (ctrl_emit_asF.aentry_k_on's
   hypothesis HK names these facts). *)
Definition ce_cut (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o f md d s g n ns FS : Z) (row db sb : list byte) (ms : machine_state) : Prop :=
  exists (u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 w0 : word) (mc : word -> option byte),
    ms = lib.Lib.MState.MS
           (lib.Lib.Frame.mkR (Z_to_bv 64 0x85730) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp u0 u1 u2
              (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
              x14 x15 x16 x17 (lib.Lib.Mem.zxb (nth 1 row (Z_to_bv 8 0))) (lib.Lib.Mem.zxb (nth 0 row (Z_to_bv 8 0)))
              (Z_to_bv 64 n) (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s)
              (Z_to_bv 64 (em_len (ubat row 21) n)) a5 (Z_to_bv 64 lib.B.AsanRT.ASAN_K) u3 u4 u5 u6)
           F (Z_to_bv 64 0x86104) fc None mc (lib.Lib.PropExec.seg_rom RS) /\
    lib.Lib.Step.rw_cells RS mc (bv_unsigned sp + -128)
      (lib.Lib.Cells.CB 24 (lib.Lib.Mem.le8 w0 ++ lib.Lib.Mem.le8 (Z_to_bv 64 g) ++ lib.Lib.Mem.le8 (Z_to_bv 64 ns)) ::
       lib.Lib.Cells.C8 s11 :: lib.Lib.Cells.C8 s10 :: lib.Lib.Cells.C8 s9 :: lib.Lib.Cells.C8 s8 ::
       lib.Lib.Cells.C8 s7 :: lib.Lib.Cells.C8 s6 :: lib.Lib.Cells.C8 s5 :: lib.Lib.Cells.C8 s4 ::
       lib.Lib.Cells.C8 s3 :: lib.Lib.Cells.C8 s2 :: lib.Lib.Cells.C8 s1 :: lib.Lib.Cells.C8 s0 ::
       [lib.Lib.Cells.C8 ra]) /\
    lib.Lib.Frame.stk RS mc (bv_unsigned sp - 4640) (bv_unsigned sp + -128) /\
    lib.Lib.Frame.munch [(bv_unsigned sp - 4640, bv_unsigned sp); (o, o + em_len (ubat row 21) n)] m mc /\
    lib.Lib.Frame.wmono RS m mc /\ lib.Lib.Mem.mem_inv RS mc /\
    lib.B.Prog.ctrl_emit_asF.aJ_on sp tp m o f md d s n FS row mc /\
    lib.Lib.Step.rw_cells RS mc o [lib.Lib.Cells.CB 6 db] /\
    lib.Lib.Step.rw_cells RS mc (o + 6) [lib.Lib.Cells.CB 6 sb] /\
    lib.Lib.Mem.bytes_at RS mc (o + 12)
      [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned a5 mod 65536) mod 256);
       Z_to_bv 8 ((bv_unsigned a5 mod 65536) / 256); nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)] /\
    lib.Lib.Mem.wr_at RS mc (o + 12) (Z.of_nat 6) /\
    lib.Lib.Step.rw_cells RS mc (o + 18)
      [lib.Lib.Cells.CB (Z.to_nat (em_len (ubat row 21) n - 18))
         (repeat (Z_to_bv 8 0) (Z.to_nat (em_len (ubat row 21) n - 18)))].

(* ---- what a stretch whose munch is the window and the output keeps (stretch 1, up to the ctrl_lay_block call):
   every byte outside the two, so every view fact of a range apart from them, and of any shadow byte ---- *)
Lemma ce_raw2 : forall (m m' : word -> option byte) lo hi o L,
  lib.Lib.Frame.munch [(lo, hi); (o, o + L)] m m' ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (o <= bv_unsigned x < o + L) -> m' x = m x.
Proof.
  intros m m' lo hi o L MU x H1 H2. apply MU. apply ce_outside_iff. intros r Hr Hin. cbn [In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin; [exact (H1 Hin) | exact (H2 Hin)].
Qed.

Lemma ce_keep2 : forall (H : word -> bool) (m m' : word -> option byte) lo hi o L,
  lib.Lib.Frame.munch [(lo, hi); (o, o + L)] m m' ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (o <= a < o + L) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' lo hi o L MU a Ha H1 H2. apply (ce_view_munch H m m' _ a Ha MU).
  apply ce_outside_iff. intros r Hr Hin. cbn [In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin; [exact (H1 Hin) | exact (H2 Hin)].
Qed.

Lemma ce_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi o L q (bs : list byte),
  lib.Lib.Frame.munch [(lo, hi); (o, o + L)] m m' -> 0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  ly_dj lo hi q (q + Z.of_nat (length bs)) -> ly_dj o (o + L) q (q + Z.of_nat (length bs)) ->
  garr8 SEGS (mrestrict H m) q (map (fun x : byte => bv_unsigned x) bs) ->
  garr8 SEGS (mrestrict H m') q (map (fun x : byte => bv_unsigned x) bs).
Proof.
  intros H m m' lo hi o L q bs MU Hq Hb D1 D2. apply (ce_garr8_view H H m m'). intros j Hj.
  rewrite length_map in Hj. unfold ly_dj in D1, D2.
  apply (ce_keep2 H m m' lo hi o L MU); rlia.
Qed.

Lemma ce_raddr_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi o L q n,
  lib.Lib.Frame.munch [(lo, hi); (o, o + L)] m m' -> 0 <= q -> q + n <= lib.B.AsanRT.APPMEM_END ->
  (forall a, lo <= a < hi -> lib.B.AsanRT.app_mem a) -> (forall a, o <= a < o + L -> lib.B.AsanRT.app_mem a) ->
  range_addressable (aview SEGS H m) SHADOW_OFF q n -> range_addressable (aview SEGS H m') SHADOW_OFF q n.
Proof.
  intros H m m' lo hi o L q n MU Hq Hn Aw Ao HR x Hx. destruct (HR x Hx) as (sv & E & Ok).
  exists sv. split; [|exact Ok].
  assert (Hs : ~ lib.B.AsanRT.app_mem (shadow_of_addr SHADOW_OFF x) /\ 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64)
    by (unfold shadow_of_addr, SHADOW_OFF, lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG,
          lib.B.AsanRT.APPMEM_END in *; rlia).
  destruct Hs as (Hs & Hr).
  rewrite (ce_keep2 H m m' lo hi o L MU _ Hr (fun h => Hs (Aw _ h)) (fun h => Hs (Ao _ h))). exact E.
Qed.

Lemma ce_hull_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi o L q n,
  lib.Lib.Frame.munch [(lo, hi); (o, o + L)] m m' -> 0 <= q -> 0 < n -> q + n <= lib.B.AsanRT.APPMEM_END ->
  (forall a, lo <= a < hi -> lib.B.AsanRT.app_mem a) -> (forall a, o <= a < o + L -> lib.B.AsanRT.app_mem a) ->
  shadow_hull_vis (aview SEGS H m) q n -> shadow_hull_vis (aview SEGS H m') q n.
Proof.
  intros H m m' lo hi o L q n MU Hq Hn HE Aw Ao HV s Hs.
  assert (Hb : ~ lib.B.AsanRT.app_mem s /\ 0 <= s < 2 ^ 64)
    by (unfold shadow_addr, SHADOW_OFF, lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END, lib.B.AsanRT.HIGHMEM_BEG,
          lib.B.AsanRT.APPMEM_END in *; rlia).
  destruct Hb as (Hs' & Hr).
  rewrite (ce_keep2 H m m' lo hi o L MU s Hr (fun h => Hs' (Aw _ h)) (fun h => Hs' (Ao _ h))). exact (HV s Hs).
Qed.

Lemma ce_hull_sub : forall rd q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  shadow_hull_vis rd q' n'.
Proof. intros rd q n q' n' HV H1 H2 H3 s Hs. apply HV. unfold shadow_addr, SHADOW_OFF in *. rlia. Qed.

Lemma ce_raddr_sub : forall rd q n q' n', range_addressable rd SHADOW_OFF q n -> q <= q' -> q' + n' <= q + n ->
  range_addressable rd SHADOW_OFF q' n'.
Proof. intros rd q n q' n' HR H1 H2 x Hx. apply HR. lia. Qed.

(* A present byte of the normalized side is a present byte of the real side, off the image. *)
Lemma ce_present_of_rw : forall (mA mc : word -> option byte) p cs,
  (forall a, lib.Lib.Mem.mrd RS mA a = lib.Lib.Mem.mrd RS mc a) -> lib.Lib.Step.rw_cells RS mc p cs ->
  forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> 0x5fe000 <= p + i ->
  exists b, mA (Z_to_bv 64 (p + i)) = Some b.
Proof.
  intros mA mc p cs E ((Hwf & (H0 & H1 & HB)) & _) i Hi Hp.
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as L.
  assert (Hn : (Z.to_nat i < length (lib.Lib.Cells.cells_bytes cs))%nat) by (rewrite L; lia).
  pose proof (HB _ Hn) as Eb. rewrite Z2Nat.id in Eb by lia.
  destruct (nth_error (lib.Lib.Cells.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:En;
    [|apply nth_error_None in En; lia].
  exists b. rewrite <- E in Eb. unfold lib.Lib.Mem.wa in Eb.
  exact (ce_raw_of_mrd mA (p + i) b ltac:(rewrite L in Hn; lia) ltac:(left; lia) Eb).
Qed.

(* The real side's bytes_at / rw_cells from equal raw bytes. *)
Lemma ce_bytes_ext : forall (m m' : word -> option byte) a bs,
  (forall i, (i < length bs)%nat -> m' (lib.Lib.Mem.wa (a + Z.of_nat i)) = m (lib.Lib.Mem.wa (a + Z.of_nat i))) ->
  lib.Lib.Mem.bytes_at RS m a bs -> lib.Lib.Mem.bytes_at RS m' a bs.
Proof.
  intros m m' a bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold lib.Lib.Mem.mrd. rewrite (E i Hi). reflexivity.
Qed.

Lemma ce_rw_ext : forall (m m' : word -> option byte) p cs,
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) ->
     m' (lib.Lib.Mem.wa (p + i)) = m (lib.Lib.Mem.wa (p + i))) ->
  lib.Lib.Step.rw_cells RS m p cs -> lib.Lib.Step.rw_cells RS m' p cs.
Proof.
  intros m m' p cs E ((Hwf & HB) & (W0 & W1 & Wr)).
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (ce_bytes_ext m); [|exact HB]. intros i Hi. apply E. rewrite L in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (Wr i Hi).
    unfold wview in *. rewrite (E i Hi). exact Wr.
Qed.

(* ---- after the ctrl_lay_block call: what acall_kept, the later world and AR give back at the return ---- *)
Lemma ce_wle_vis : forall (W W2 : world SEGS) x, wle W W2 -> w_H W x = false -> w_H W2 x = false.
Proof.
  intros W W2 x Hle Hv. destruct (w_H W2 x) eqn:E; [|reflexivity].
  rewrite (Hle x E) in Hv. discriminate Hv.
Qed.

(* Off the image, a visible byte the view keeps is the same raw byte. *)
Lemma ce_view_raw : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> (0x5fe000 <= a \/ a < 0x10000) ->
  H (Z_to_bv 64 a) = false -> H' (Z_to_bv 64 a) = false ->
  aview SEGS H' m' a = aview SEGS H m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a Ha Hn Hv Hv' E. unfold aview, mbyte, mrestrict in E. rewrite Hv, Hv' in E.
  pose proof (ce_rom_none a Ha Hn) as N.
  destruct (m' (Z_to_bv 64 a)) as [b'|], (m (Z_to_bv 64 a)) as [b|]; rewrite ?N in E; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A live frame and its size are 8-aligned (YG0s.frame_off_bounds; the side stack is page-aligned). *)
Lemma ce_frame_al : forall ly S (W : world SEGS) m md cid pos, AR SEGS B ly S W m md ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos mod 8 = 0 /\ fs_frame_bytes cid mod 8 = 0.
Proof.
  intros ly S W m md cid pos HAR Hin. pose proof HAR as (M & _).
  pose proof (lib.Reusable.YG01.wfs_live _ (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as Hlive.
  pose proof (proj1 (Forall_forall _ _) Hlive (cid, pos) Hin) as (Hc & Hp). cbn [fst snd] in Hc, Hp.
  pose proof (lib.Reusable.YG0s.frame_off_bounds cid pos Hc Hp) as (_ & _ & Ho & _ & Hb & _).
  pose proof (lo_F_al _ (ce_layout ly S W m md HAR)) as HF. unfold page_aligned in HF. try unfold kPage in HF.
  unfold frame_addr. split; rlia.
Qed.

(* acall_kept keeps a caller frame's bytes and the shadow of every byte of it. *)
Lemma ce_kept_frame : forall lyc Sc (W W2 : world SEGS) ma m m2 mdc slo shi (E : Z -> Prop) cid pos,
  AR SEGS B lyc Sc W ma mdc -> acall_kept SEGS B lyc Sc W m W2 m2 slo shi E -> In (cid, pos) (frames Sc) ->
  forall x, frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
  (~ E x -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W) m x) /\
  (~ E (shadow_of_addr SHADOW_OFF x) ->
     aview SEGS (w_H W2) m2 (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF x)).
Proof.
  intros lyc Sc W W2 ma m m2 mdc slo shi E cid pos HAR (_ & _ & _ & A4 & _) Hin x Hx.
  pose proof (ce_frame_al lyc Sc W ma mdc cid pos HAR Hin) as (Al & Bl).
  split.
  - intros HE. apply (A4 cid pos x Hin); [left | exact HE]. unfold in_zr, frame_rng. cbn [fst snd]. exact Hx.
  - intros HE. apply (A4 cid pos _ Hin); [right | exact HE].
    unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. rlia.
Qed.

(* The read-only data survives a call with acall_kept (its image-byte clause). *)
Lemma ce_ro_kept : forall lyc Sc (W W2 : world SEGS) m m2 slo shi (E : Z -> Prop),
  acall_kept SEGS B lyc Sc W m W2 m2 slo shi E ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) m) ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W2) m2).
Proof.
  intros lyc Sc W W2 m m2 slo shi E (_ & _ & A3 & _) Hro a Hseg Hno He.
  assert (Hi : in_img SEGS a).
  { destruct Hseg as [(s0 & Hs & _ & Hr) | Hr]; [exists s0; split; [exact Hs | lia] | exact (RRO_img a Hr)]. }
  rewrite (A3 a Hi Hno He). exact (Hro a Hseg Hno He).
Qed.

(* The three 8-byte cells of a 24-byte block. *)
Lemma ce_cb3_c8 : forall (m : word -> option byte) p (a b c : word) rest,
  lib.Lib.Step.rw_cells RS m p
    (lib.Lib.Cells.CB 24 (lib.Lib.Mem.le8 a ++ lib.Lib.Mem.le8 b ++ lib.Lib.Mem.le8 c) :: rest) ->
  lib.Lib.Step.rw_cells RS m p
    (lib.Lib.Cells.C8 a :: lib.Lib.Cells.C8 b :: lib.Lib.Cells.C8 c :: rest).
Proof.
  intros m p a b c rest ((Hwf & HB) & Hw). split; [split|].
  - destruct Hwf as (_ & Hwf). cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf]. tauto.
  - cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in HB |- *. rewrite <- !app_assoc in HB. exact HB.
  - exact Hw.
Qed.

(* Cells of the normalized side are cells of the real side (ProgWorld.rebase_ro_normalize's bytes / wr_at). *)
Lemma ce_rw_of_rb : forall (mA mc : word -> option byte) p cs,
  (forall a bs, lib.Lib.Mem.bytes_at RS mA a bs <-> lib.Lib.Mem.bytes_at RS mc a bs) ->
  (forall a n, lib.Lib.Mem.wr_at RS mc a n -> lib.Lib.Mem.wr_at RS mA a n) ->
  lib.Lib.Step.rw_cells RS mc p cs -> lib.Lib.Step.rw_cells RS mA p cs.
Proof.
  intros mA mc p cs Hby Hwr ((Hwf & HB) & Hw). split; [split; [exact Hwf | exact (proj2 (Hby _ _) HB)]|].
  exact (Hwr _ _ Hw).
Qed.

(* Zero bytes off the image are writable zero cells. *)
Lemma ce_zero_cells : forall (m : word -> option byte) p k, 0 <= k -> 0x5fe000 <= p -> p + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> m (Z_to_bv 64 (p + i)) = Some (Z_to_bv 8 0)) ->
  lib.Lib.Step.rw_cells RS m p [lib.Lib.Cells.CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m p k Hk Hp Hpk H.
  assert (Hl : length (repeat (Z_to_bv 8 0) (Z.to_nat k)) = Z.to_nat k) by apply repeat_length.
  rewrite <- Hl at 1. apply ce_rw_cb; [|intros i Hi; lia].
  split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. rewrite Hl in Hi.
  rewrite nth_error_repeat by exact Hi.
  unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite (H (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

(* A byte of a stk range of the normalized side is present on the real side, off the image. *)
Lemma ce_present_stk : forall (mA mc : word -> option byte) lo hi,
  (forall a, lib.Lib.Mem.mrd RS mA a = lib.Lib.Mem.mrd RS mc a) -> lib.Lib.Frame.stk RS mc lo hi ->
  0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  forall a, lo <= a < hi -> exists b, mA (Z_to_bv 64 a) = Some b.
Proof.
  intros mA mc lo hi E (H0 & H1 & H) Hlo Hhi a Ha. destruct (H a Ha) as (_ & b & Hb).
  exists b. rewrite <- E in Hb. unfold lib.Lib.Mem.wa in Hb.
  exact (ce_raw_of_mrd mA a b ltac:(lia) ltac:(left; lia) Hb).
Qed.

(* ce_range_rng with the shadow cover's visibility given directly (a later world sees all an earlier one saw). *)
Lemma ce_range_rngV : forall (W' : world SEGS) FS q n,
  in_app FS kFakeStackSize -> FS mod 64 = 0 -> 0 <= q -> 0 < n -> q + n <= lib.B.AsanRT.APPMEM_END ->
  (q + n <= FS \/ FS + 2134016 <= q) ->
  (forall a, q <= a < q + n -> w_H W' (Z_to_bv 64 a) = false /\ lib.B.AsanRT.app_mem a) ->
  (forall s, (q / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s <
             ((q + n - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 -> w_H W' (Z_to_bv 64 s) = false) ->
  lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) q n /\
  (forall a b, q <= a -> a <= b -> b <= q + n - 1 ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
       ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)) /\
  (forall x, q <= x <= q + n - 1 ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W') FS)) (x / 8 + lib.B.AsanRT.ASAN_K) 1).
Proof.
  intros W' FS q n HF H64 Hq Hn HE Hside Hb HVc.
  assert (Hcov := ce_rng_cover W' FS q n HF H64 Hq HE Hside HVc).
  split; [|split; [exact Hcov|]].
  - apply ce_rng_bytes; [exact HF | exact Hq | unfold lib.B.AsanRT.APPMEM_END in HE; lia |]. intros a Ha.
    destruct (Hb a Ha) as (H1 & H2). split; [exact H1|]. split; [exact H2 | lia].
  - intros x Hx.
    exact (ctrl_emit_asF.dcF_shadow1 _ lib.B.AsanRT.ASAN_K q (q + n - 1) x
             (Hcov q (q + n - 1) ltac:(lia) ltac:(lia) ltac:(lia)) Hx).
Qed.

(* the cover visibility a shadow_hull_vis gives, as ce_range_rngV takes it *)
Lemma ce_hull_cover : forall (H : word -> bool) (m : word -> option byte) q n, 0 <= q ->
  q + n <= lib.B.AsanRT.APPMEM_END -> shadow_hull_vis (aview SEGS H m) q n ->
  forall s, (q / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s <
            ((q + n - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 -> H (Z_to_bv 64 s) = false.
Proof. intros H m q n Hq Hn HV. exact (ce_hull_vis H m q n Hq Hn HV). Qed.

(* =================================================================================================================
   The proof of tctrl_emit_as_spec, over the spec's binders and premises (Section main; pb_ctrl_emit_as below
   applies the closed ce_main to them).
   ================================================================================================================= *)
Section main.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sj : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (o f md d s g n ns : Z) (row tb mb nb gb db sb : list byte).
Hypothesis HJ : ajournal SEGS B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRO : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc).
Hypothesis Hret : lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1).
Hypothesis Hra : 4096 <= raZ regs.
Hypothesis Hgp : lib.Reusable.YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : lib.Reusable.YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : lib.Reusable.YK11.getr regs 10 = w64 o.
Hypothesis H11 : lib.Reusable.YK11.getr regs 11 = w64 f.
Hypothesis H12 : lib.Reusable.YK11.getr regs 12 = w64 md.
Hypothesis H13 : lib.Reusable.YK11.getr regs 13 = w64 d.
Hypothesis H14 : lib.Reusable.YK11.getr regs 14 = w64 s.
Hypothesis H16 : lib.Reusable.YK11.getr regs 16 = w64 n.
Hypothesis H17 : lib.Reusable.YK11.getr regs 17 = w64 g.
Hypothesis H29 : lib.Reusable.YK11.getr regs 29 = w64 ns.
Hypothesis Hn : -2^31 <= n < 2^31.
Hypothesis Hns : -2^31 <= ns < 2^31.
Hypothesis Hg : 0 <= g < 2^64.
Hypothesis Hsp16 : spZ regs mod 16 = 0.
Hypothesis Hstk1 : sp0 - STK <= spZ regs - CTRL_EMIT_AS_STK.
Hypothesis Hstk2 : spZ regs <= sp0.
Hypothesis Hcnt1 : count_cid 1 (frames Sc) < fs_frames 1.
Hypothesis Hcnt0 : count_cid 0 (frames Sc) < fs_frames 0.
Hypothesis Hf0 : f <> 0.
Hypothesis Hf8 : f mod 8 = 0.
Hypothesis Hf24 : f + 24 <= 2^64.
Hypothesis Hrl : length row = 24%nat.
Hypothesis HfG : garr8 SEGS (mrestrict (w_H W) memc) f (map (fun x : byte => bv_unsigned x) row).
Hypothesis HfR : tctrl_emit_as_ro RLO RHI B GLOBS f 24.
Hypothesis Hk : ly_k row <= 9.
Hypothesis Hc : ubat row 20 <= 2.
Hypothesis HL : ubat row 21 <= 2.
Hypothesis HGG : ubat row 22 <= 1.
Hypothesis HA : ubat row 23 <= 1.
Hypothesis Hao : ly_ao row + ly_al row <= 32.
Hypothesis Hc2 : ubat row 20 = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31.
Hypothesis HLA : ubat row 21 = 2 -> ubat row 23 = 0.
Hypothesis Hns0 : ubat row 23 = 1 -> ns <= 0.
Hypothesis Htm : ly_k row = 2 ->
  ly_tm row + 32 <= 2 ^ 64 /\ length tb = 32%nat /\
  garr8 SEGS (mrestrict (w_H W) memc) (ly_tm row) (map (fun x : byte => bv_unsigned x) tb) /\
  tctrl_emit_as_ro RLO RHI B GLOBS (ly_tm row) 32 /\
  (forall a, ly_tm row <= a < ly_tm row + 32 ->
     (exists s, In s SEGS /\ seg_writable s = false /\
        Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) /\
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
Hypothesis Hmd0 : md <> 0.
Hypothesis Hmd8 : md mod 8 = 0.
Hypothesis Hmd296 : md + 296 <= 2^64.
Hypothesis Hml : length mb = 296%nat.
Hypothesis HmG : garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb).
Hypothesis HmR : tctrl_emit_as_ro RLO RHI B GLOBS md 296.
Hypothesis Hnm : tctrl_emit_as_nm row mb ->
  name_ok nb /\ rname mb + Z.of_nat (length nb) <= 2 ^ 64 /\
  garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
  tctrl_emit_as_ro RLO RHI B GLOBS (rname mb) (Z.of_nat (length nb)).
Hypothesis Hg0 : g = 0.
Hypothesis Hdb : length db = 6%nat.
Hypothesis HdG : garr8 SEGS (mrestrict (w_H W) memc) d (map (fun x : byte => bv_unsigned x) db).
Hypothesis HdA : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF d 6.
Hypothesis HdV : shadow_hull_vis (aview SEGS (w_H W) memc) d 6.
Hypothesis HdP : in_app d 6.
Hypothesis HdH : tctrl_emit_as_home lyc Sc d 6.
Hypothesis Hd6 : app_addr (d + 6).
Hypothesis Hd7 : app_addr (d + 7).
Hypothesis Hsb : length sb = 6%nat.
Hypothesis HsG : garr8 SEGS (mrestrict (w_H W) memc) s (map (fun x : byte => bv_unsigned x) sb).
Hypothesis HsA : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 6.
Hypothesis HsV : shadow_hull_vis (aview SEGS (w_H W) memc) s 6.
Hypothesis HsP : in_app s 6.
Hypothesis HsH : tctrl_emit_as_home lyc Sc s 6.
Hypothesis Hs6 : app_addr (s + 6).
Hypothesis Hs7 : app_addr (s + 7).
Hypothesis Ho : 0 < o.
Hypothesis Ho1492 : o + 1492 <= 2^64.
Hypothesis Hhome : exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= o /\
  o + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid.
Hypothesis HEo : tctrl_emit_as_E row mb n = true ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\
     forall a, o <= a < o + tctrl_emit_as_len row n -> in_zr a (frame_rng lyc (cid, pos))) /\
  (forall a, o <= a < o + tctrl_emit_as_len row n ->
     awr_byte STK sp0 FP (ablocks B ly Sj) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o (tctrl_emit_as_len row n) /\
  shadow_hull_vis (aview SEGS (w_H W) memc) o (tctrl_emit_as_len row n) /\
  app_addr (o + tctrl_emit_as_len row n).
Hypothesis Dsf : ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) f (f + 24).
Hypothesis Dsm : ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) md (md + 296).
Hypothesis Dsd : ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) d (d + 6).
Hypothesis Dss : ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) s (s + 6).
Hypothesis Dst : ly_k row = 2 -> ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) (ly_tm row) (ly_tm row + 32).
Hypothesis Dsn : tctrl_emit_as_nm row mb ->
  ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) (rname mb) (rname mb + Z.of_nat (length nb)).
Hypothesis HEd : tctrl_emit_as_E row mb n = true ->
  ly_dj (spZ regs - CTRL_EMIT_AS_STK) (spZ regs) o (o + tctrl_emit_as_len row n) /\
  ly_dj o (o + tctrl_emit_as_len row n) f (f + 24) /\ ly_dj o (o + tctrl_emit_as_len row n) md (md + 296) /\
  ly_dj o (o + tctrl_emit_as_len row n) d (d + 6) /\ ly_dj o (o + tctrl_emit_as_len row n) s (s + 6) /\
  (ly_k row = 2 -> ly_dj o (o + tctrl_emit_as_len row n) (ly_tm row) (ly_tm row + 32)) /\
  (tctrl_emit_as_nm row mb -> ly_dj o (o + tctrl_emit_as_len row n) (rname mb) (rname mb + Z.of_nat (length nb))).

Lemma m_stkc : CTRL_EMIT_AS_STK = 4640.
Proof. reflexivity. Qed.

Lemma m_AR : AR SEGS B lyc Sc W memc mdc.
Proof. exact (proj1 HJ). Qed.

(* the shadow facts of f and md at the entry memory (registered read-only globals, CtrlRo) *)
Lemma m_fRV : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF f 24 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) f 24.
Proof. exact (ce_ro_read lyc Sc W memc mdc f 24 m_AR HfR ltac:(lia)). Qed.

Lemma m_mRV : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF md 296 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) md 296.
Proof. exact (ce_ro_read lyc Sc W memc mdc md 296 m_AR HmR ltac:(lia)). Qed.

(* the call's window [LO, SP0) in the stack and in the caller's journal window *)
Lemma m_win : ly_stk_lo lyc <= spZ regs - 4640 /\ spZ regs <= ly_stk_hi lyc /\ ASAN_CEIL <= ly_stk_lo lyc /\
  lib.B.AsanRT.HIGHMEM_BEG <= spZ regs - 4640 /\ spZ regs <= lib.B.AsanRT.APPMEM_END /\
  (spZ regs - 4640) mod 8 = 0 /\ sp0 - STK <= spZ regs - 4640 /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hastk as (_ & _ & _ & A1 & A2 & _).
  pose proof (ce_fs_place lyc Sc W memc mdc HAR) as (_ & _ & _ & _ & CS).
  pose proof (lo_top _ (ce_layout lyc Sc W memc mdc HAR)) as Htop.
  unfold page_aligned, kHighMemEnd, kHighMemBeg in Htop.
  pose proof Hstk1 as Hs1. rewrite m_stkc in Hs1.
  unfold lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END.
  split; [rewrite Elo; rlia|].
  split; [rewrite Ehi; rlia|].
  split; [exact CS|].
  split; [rewrite Elo in Htop; rlia|].
  split; [rewrite Ehi in Htop; rlia|].
  split; [unfold spZ in *; rlia|].
  split; [exact Hs1 | exact Hwin].
Qed.

Lemma m_F : in_app (ly_F lyc) kFakeStackSize /\ ly_F lyc mod 64 = 0 /\
  lib.B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F lyc /\ ly_F lyc + kFakeStackSize <= ASAN_CEIL.
Proof.
  pose proof (ce_fs_place lyc Sc W memc mdc m_AR) as (_ & Fal & FC & _).
  split; [exact (ce_F_app lyc Sc W memc mdc m_AR)|]. split; [rlia|].
  split; [exact (ce_F_above lyc Sc W memc mdc m_AR) | exact FC].
Qed.

Lemma m_RR : 0 <= tctrl_emit_as_R row mb n <= 1492.
Proof.
  unfold tctrl_emit_as_R. destruct (tctrl_emit_as_E row mb n) eqn:EE; [|lia].
  pose proof (lib.Prog.RcEmitLib.em_len_rng _ _ _ _ EE) as L. unfold tctrl_emit_as_len. lia.
Qed.

Lemma m_len : tctrl_emit_as_E row mb n = true -> 124 <= tctrl_emit_as_len row n <= 1492.
Proof. intros EE. exact (lib.Prog.RcEmitLib.em_len_rng _ _ _ _ EE). Qed.

(* ---- generic: the window's shadow cover is visible (the stack is zero-shadow, AR_zshadow_law); a view byte array
   and a view-addressable range are, on normalize m, ctrl's bytes_at and addressable ---- *)
Lemma ce_win_vis : forall lyx Sx (W' : world SEGS) m mdx lo len, AR SEGS B lyx Sx W' m mdx ->
  ly_stk_lo lyx <= lo -> lo + len <= ly_stk_hi lyx -> 0 < len ->
  forall s, (lo / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 <= s <
            ((lo + len - 1) / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 -> w_H W' (Z_to_bv 64 s) = false.
Proof.
  intros lyx Sx W' m mdx lo len HAR Hlo Hhi Hln s0 Hs.
  pose proof (lo_top _ (ce_layout lyx Sx W' m mdx HAR)) as Htop.
  unfold page_aligned, kHighMemEnd, kHighMemBeg in Htop.
  assert (Hz : zero_shadow (aview SEGS (w_H W') m) SHADOW_OFF (ly_stk_lo lyx) (ly_stk_hi lyx - ly_stk_lo lyx)).
  { apply (al_zshadow _ _ AR_laws_B lyx Sx W' m mdx (ly_stk_lo lyx, ly_stk_hi lyx - ly_stk_lo lyx) HAR).
    unfold zero_shadow_ranges. left. reflexivity. }
  assert (Hi : 0 <= s0 - shadow_of_addr SHADOW_OFF (ly_stk_lo lyx) < (ly_stk_hi lyx - ly_stk_lo lyx) / 8).
  { unfold shadow_of_addr, SHADOW_OFF. unfold lib.B.AsanRT.ASAN_K in Hs. rlia. }
  pose proof (Hz _ Hi) as Hv.
  replace (shadow_of_addr SHADOW_OFF (ly_stk_lo lyx) + (s0 - shadow_of_addr SHADOW_OFF (ly_stk_lo lyx)))
    with s0 in Hv by lia.
  assert (Hs0 : 0 <= s0 < 2 ^ 64) by (unfold lib.B.AsanRT.ASAN_K in Hs; rlia).
  exact (proj1 (ce_view_shadow W' m s0 0 Hs0 ltac:(unfold lib.B.AsanRT.ASAN_K in Hs; rlia) Hv)).
Qed.

Lemma ce_bytes_n : forall (W' : world SEGS) (m : word -> option byte) q bs,
  lib.B.MemNorm.ro_agree RS m -> 0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W') m) q (map (fun x : byte => bv_unsigned x) bs) ->
  lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS m) q bs.
Proof.
  intros W' m q bs RO Hq Hb HG. destruct (ce_bytes_of_garr8 W' m q bs Hq Hb HG) as (HB & _).
  exact (proj1 (lib.B.MemNorm.bytes_at_rel RS m _ q bs (lib.B.MemNorm.mem_rel_normalize RS m RO)) HB).
Qed.

Lemma ce_vis_of_garr8 : forall (W' : world SEGS) (m : word -> option byte) q bs,
  0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W') m) q (map (fun x : byte => bv_unsigned x) bs) ->
  forall a, q <= a < q + Z.of_nat (length bs) -> w_H W' (Z_to_bv 64 a) = false.
Proof.
  intros W' m q bs Hq Hb HG a Ha. destruct (ce_bytes_of_garr8 W' m q bs Hq Hb HG) as (_ & HV).
  replace a with (q + Z.of_nat (Z.to_nat (a - q))) by lia. apply HV. lia.
Qed.

Lemma ce_addr_n : forall (W' : world SEGS) (m : word -> option byte) q n,
  lib.B.MemNorm.ro_agree RS m -> 0 <= q -> 0 <= n -> q + n <= ASAN_CEIL ->
  (forall a, q <= a < q + n -> lib.B.AsanRT.app_mem a) ->
  range_addressable (aview SEGS (w_H W') m) SHADOW_OFF q n ->
  lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS m) q n.
Proof.
  intros W' m q nq RO Hq Hnq Hcq Happ HA'. pose proof ASAN_CEIL_range as (CR & _).
  apply (lib.B.MemNormTr.addressable_normalize m q nq RO).
  apply (ce_addr_of_view W' m q nq Hq Hnq ltac:(unfold lib.B.AsanRT.APPMEM_END, ASAN_CEIL in *; lia)); [|exact HA'].
  intros i Hi. apply Happ. lia.
Qed.

(* ---- stretch 1: the entry 0x853c4 .. the ctrl_lay_block call, on normalize memc (decision 27b) ---- *)
Definition m_QK1 : machine_state -> Prop := fun ms =>
  lib.B.Prog.ctrl_emit_asF.aQp_on (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
    (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
    (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
    (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
    (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS memc) o f md d s g n
    (ly_F lyc) row tb mb nb gb db sb ms \/
  (tctrl_emit_as_E row mb n = true /\
   ce_cut (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
    (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
    (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
    (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
    (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS memc) o f md d s g n ns
    (ly_F lyc) row db sb ms).

Lemma m_s1_run :
  lib.Lib.ExecF.evtF RS (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) m_QK1
    (lib.Lib.MState.MS
       (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
          (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 5)
          (lib.Reusable.YK11.getr regs 6) (lib.Reusable.YK11.getr regs 7) (lib.Reusable.YK11.getr regs 8)
          (lib.Reusable.YK11.getr regs 9) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
          (Z_to_bv 64 s) (lib.Reusable.YK11.getr regs 15) (Z_to_bv 64 n) (Z_to_bv 64 g)
          (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
          (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
          (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
          (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 28) (Z_to_bv 64 ns)
          (lib.Reusable.YK11.getr regs 30) (lib.Reusable.YK11.getr regs 31))
       lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x853c4) lib.Reusable.YK11.fp_csr None
       (lib.B.MemNorm.normalize RS memc) (lib.Lib.PropExec.seg_rom RS)).
Proof.
  pose proof m_AR as HAR.
  pose proof m_win as (Wlo & Whi & WCS & WHM & WAE & W8 & WJ & Wpres).
  pose proof m_F as (FA & F64 & FGT & FC).
  pose proof m_RR as HRR.
  pose proof ASAN_CEIL_range as (CR & _).
  pose proof Hhome as (cid & pos & Hin & Hcid & Ho1 & Ho2).
  pose proof (ce_frame_lo lyc Sc W memc mdc cid pos HAR Hin Hcid) as Hfl.
  pose proof (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin) as (Fb0 & Fb1 & Fb2).
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT, kFakeStackSize in *. unfold ASAN_CEIL in *.
  pose proof (ce_ro_place lyc Sc W memc mdc f 24 HAR HfR) as (fq0 & fqc & fsd & fap).
  pose proof (ce_ro_place lyc Sc W memc mdc md 296 HAR HmR) as (mq0 & mqc & msd & map').
  pose proof m_fRV as (HfA & HfV). pose proof m_mRV as (HmA & HmV).
  pose proof (ce_home_place lyc Sc W memc mdc d 6 HAR ltac:(rlia) HdP HdH) as (dq0 & dqc & dsd & dap).
  pose proof (ce_home_place lyc Sc W memc mdc s 6 HAR ltac:(rlia) HsP HsH) as (sq0 & sqc & ssd & sap).
  unfold ASAN_CEIL in *.
  assert (PL : forall q n0, (q + n0 <= ly_F lyc \/ ly_F lyc + 2134016 <= q) ->
                 (forall a, q <= a < q + n0 -> lib.B.AsanRT.app_mem a) ->
                 forall x, q <= x < q + n0 -> lib.B.AsanRT.app_mem x /\ ~ (ly_F lyc <= x < ly_F lyc + 2134016)).
  { intros q n0 Hside Hap x Hx. split; [exact (Hap x Hx) | rlia]. }
  destruct (ce_base lyc Sc W memc mdc (spZ regs - 4640) (spZ regs) o f md d s (tctrl_emit_as_R row mb n) cid pos
              HAR HRO Wlo ltac:(rlia) Whi Hin Hcid Ho1 Ho2 HRR (PL f 24 fsd fap) (PL md 296 msd map')
              (PL d 6 dsd dap) (PL s 6 ssd sap)) as (RO & MI & AC & AW & FPb & TLb).
  assert (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = lib.B.AsanRT.RT_TP).
  { rewrite Htp. unfold w64. rewrite (lib.B.ProgWorld.as_tp_RT_TP B HTS).
    apply lib.Lib.MState.unsigned_lit. unfold lib.B.AsanRT.RT_TP. rlia. }
  unfold spZ in *.
  (* bytes and addressable ranges on normalize memc *)
  assert (HR : lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS memc) f row)
    by (apply (ce_bytes_n W memc f row RO); [rlia | rewrite Hrl; rlia | exact HfG]).
  assert (HM : lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS memc) md mb)
    by (apply (ce_bytes_n W memc md mb RO); [rlia | rewrite Hml; rlia | exact HmG]).
  assert (HD : lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS memc) d db)
    by (apply (ce_bytes_n W memc d db RO); [rlia | rewrite Hdb; rlia | exact HdG]).
  assert (HSb : lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS memc) s sb)
    by (apply (ce_bytes_n W memc s sb RO); [rlia | rewrite Hsb; rlia | exact HsG]).
  assert (Af : lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS memc) f 24)
    by (apply (ce_addr_n W memc f 24 RO); [rlia | rlia | unfold ASAN_CEIL; rlia | exact fap | exact HfA]).
  assert (Amd : lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS memc) md 296)
    by (apply (ce_addr_n W memc md 296 RO); [rlia | rlia | unfold ASAN_CEIL; rlia | exact map' | exact HmA]).
  assert (Ad : lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS memc) d 6)
    by (apply (ce_addr_n W memc d 6 RO); [rlia | rlia | unfold ASAN_CEIL; rlia | exact dap | exact HdA]).
  assert (As : lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS memc) s 6)
    by (apply (ce_addr_n W memc s 6 RO); [rlia | rlia | unfold ASAN_CEIL; rlia | exact sap | exact HsA]).
  (* the window *)
  pose proof (ce_u64 (lib.Reusable.YK11.getr regs 2)) as Rsp2.
  assert (HST : lib.Lib.Frame.stk RS (lib.B.MemNorm.normalize RS memc)
                  (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) (bv_unsigned (lib.Reusable.YK11.getr regs 2))).
  { apply (lib.B.MemNormTr.stk_normalize_ro memc _ _ RO); [unfold lib.B.Prog.ImgBounds.IMG_HI; rlia|].
    split; [rlia|]. split; [rlia|]. intros a Ha. destruct (Wpres a ltac:(rlia)) as (Hh & b & Hb).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  assert (Wvis : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                   bv_unsigned (lib.Reusable.YK11.getr regs 2) -> w_H W (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj1 (Wpres a ltac:(rlia)))).
  assert (FpWIN : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc)))
                    (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) 4640).
  { apply ce_rng_bytes; [exact FA | rlia | rlia |]. intros a Ha. split; [apply Wvis; rlia|].
    split; [apply (ce_win_app lyc Sc W memc mdc a HAR); rlia | rlia]. }
  assert (FpWSH : forall a b, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a -> a <= b ->
                    b <= bv_unsigned (lib.Reusable.YK11.getr regs 2) - 1 ->
                    lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc)))
                      ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
                      ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)).
  { intros a b Ha Hab Hb.
    apply (ce_rng_cover W (ly_F lyc) (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) 4640 FA F64
             ltac:(rlia) ltac:(unfold lib.B.AsanRT.APPMEM_END in *; rlia) ltac:(right; rlia)); [|rlia | rlia | rlia].
    intros s0 Hs0.
    exact (ce_win_vis lyc Sc W memc mdc (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) 4640 HAR
             ltac:(rlia) ltac:(rlia) ltac:(rlia) s0 Hs0). }
  assert (FpIMG : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) 0x10000 0x5ee000).
  { apply ce_rng_bytes; [exact FA | rlia | rlia |]. intros a Ha.
    pose proof (lib.B.ProgBridge.img_vis_W W) as (_ & _ & Hv).
    split; [apply Hv; unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI; rlia|].
    split; [unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END; left; rlia | rlia]. }
  (* the data ranges' footprints *)
  pose proof (ce_range_rng W memc (ly_F lyc) f 24 FA F64 fq0 ltac:(rlia) ltac:(unfold ASAN_CEIL; rlia) fsd
                (fun a Ha => conj (ce_vis_of_garr8 W memc f row ltac:(rlia) ltac:(rewrite Hrl; rlia) HfG a
                                     ltac:(rewrite Hrl; rlia)) (fap a Ha)) HfV) as (FpROW & FpSfK & FpSf1).
  pose proof (ce_range_rng W memc (ly_F lyc) md 296 FA F64 mq0 ltac:(rlia) ltac:(unfold ASAN_CEIL; rlia) msd
                (fun a Ha => conj (ce_vis_of_garr8 W memc md mb ltac:(rlia) ltac:(rewrite Hml; rlia) HmG a
                                     ltac:(rewrite Hml; rlia)) (map' a Ha)) HmV) as (FpMD & FpSmdK & FpSmd1).
  pose proof (ce_range_rng W memc (ly_F lyc) d 6 FA F64 dq0 ltac:(rlia) ltac:(unfold ASAN_CEIL; rlia) dsd
                (fun a Ha => conj (ce_vis_of_garr8 W memc d db ltac:(rlia) ltac:(rewrite Hdb; rlia) HdG a
                                     ltac:(rewrite Hdb; rlia)) (dap a Ha)) HdV) as (FpD & FpSdK & FpSd1).
  pose proof (ce_range_rng W memc (ly_F lyc) s 6 FA F64 sq0 ltac:(rlia) ltac:(unfold ASAN_CEIL; rlia) ssd
                (fun a Ha => conj (ce_vis_of_garr8 W memc s sb ltac:(rlia) ltac:(rewrite Hsb; rlia) HsG a
                                     ltac:(rewrite Hsb; rlia)) (sap a Ha)) HsV) as (FpS & FpSsK & FpSs1).
  (* the output (E = true) *)
  assert (Oap : forall a, o <= a < o + 1492 -> lib.B.AsanRT.app_mem a /\ ly_F lyc + 2134016 <= a).
  { intros a Ha. split; [|rlia].
    exact (proj1 (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin ltac:(rlia))). }
  assert (OFP : tctrl_emit_as_E row mb n = true ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) o (tctrl_emit_as_len row n) /\
     (forall a b, o <= a -> a <= b -> b <= o + tctrl_emit_as_len row n - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
          ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)) /\
     (forall x, o <= x <= o + tctrl_emit_as_len row n - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) (x / 8 + lib.B.AsanRT.ASAN_K) 1)).
  { intros EE. pose proof (m_len EE) as Ln. destruct (HEo EE) as (_ & Hp & _ & HoV & _).
    apply (ce_range_rng W memc (ly_F lyc) o (tctrl_emit_as_len row n) FA F64 ltac:(rlia) ltac:(rlia)
             ltac:(unfold ASAN_CEIL; rlia)
             ltac:(right; rlia)); [|exact HoV].
    intros a Ha. split; [exact (proj1 (proj2 (Hp a Ha))) | exact (proj1 (Oap a ltac:(rlia)))]. }
  assert (AO : tctrl_emit_as_E row mb n = true ->
     lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS memc) o (tctrl_emit_as_len row n) /\
     lib.B.AsanRT.app_mem (o + tctrl_emit_as_len row n) /\
     (o + tctrl_emit_as_len row n <= lib.B.AsanRT.RT_LO \/ lib.B.AsanRT.RT_HI <= o)).
  { intros EE. pose proof (m_len EE) as Ln. destruct (HEo EE) as (_ & _ & HoA & _ & HoP).
    split; [apply (ce_addr_n W memc o (tctrl_emit_as_len row n) RO); [rlia | rlia | unfold ASAN_CEIL; rlia | | exact HoA]|].
    - intros a Ha. exact (proj1 (Oap a ltac:(rlia))).
    - split; [exact (ce_app_addr_mem _ HoP) | right; unfold lib.B.AsanRT.RT_HI; rlia]. }
  (* the output cells and the caller's apartness, in ctrl_emit_asF's order *)
  assert (HEo' : tctrl_emit_as_E row mb n = true ->
     lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS memc) o
       [lib.Lib.Cells.CB (Z.to_nat (tctrl_emit_as_len row n)) (ce_junk memc o (tctrl_emit_as_len row n))] /\
     ly_dj (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) (bv_unsigned (lib.Reusable.YK11.getr regs 2))
       o (o + tctrl_emit_as_len row n) /\
     ly_dj o (o + tctrl_emit_as_len row n) f (f + 24) /\
     (ly_k row = 2 -> ly_dj o (o + tctrl_emit_as_len row n) (ly_tm row) (ly_tm row + 32)) /\
     ly_dj o (o + tctrl_emit_as_len row n) md (md + 296) /\
     (tctrl_emit_as_nm row mb ->
        ly_dj o (o + tctrl_emit_as_len row n) (rname mb) (rname mb + Z.of_nat (length nb))) /\
     ly_dj o (o + tctrl_emit_as_len row n) d (d + 6) /\ ly_dj o (o + tctrl_emit_as_len row n) s (s + 6) /\
     (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + tctrl_emit_as_len row n) g (g + ly_al row))).
  { intros EE. pose proof (m_len EE) as Ln. destruct (HEo EE) as (_ & Hp & _).
    destruct (HEd EE) as (D0 & D1 & D2 & D3 & D4 & D5 & D6). rewrite m_stkc in D0.
    split; [|split; [exact D0|]; split; [exact D1|]; split; [exact D5|]; split; [exact D2|];
             split; [exact D6|]; split; [exact D3|]; split; [exact D4 | intros G0; exfalso; exact (G0 Hg0)]].
    apply (lib.B.MemNormTr.rw_cells_normalize memc o _ RO).
    - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi.
      apply lib.B.MemNormTr.ro_addr_above_img. unfold lib.B.Prog.ImgBounds.IMG_HI. rlia.
    - apply ce_junk_rw; [rlia | rlia | rlia |]. intros i Hi.
      destruct (Hp (o + i) ltac:(rlia)) as (_ & _ & b & Hb). exists b. exact Hb. }
  (* the template, read-only *)
  assert (Htm' : ly_k row = 2 -> ly_tm row + 32 <= 2 ^ 64 /\ length tb = 32%nat /\
                   lib.Lib.Mem.ro_bytes RS (ly_tm row) tb).
  { intros K2. destruct (Htm K2) as (T1 & T2 & TG & TR & TS).
    pose proof (ce_ro_place lyc Sc W memc mdc (ly_tm row) 32 HAR TR) as (TP0 & _).
    split; [exact T1|]. split; [exact T2|].
    destruct (ce_bytes_of_garr8 W memc (ly_tm row) tb ltac:(rlia) ltac:(rewrite T2; rlia) TG) as ((_ & _ & TB) & _).
    apply ce_ro_bytes_of. intros i b Eb.
    assert (Hi : (i < length tb)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
    pose proof (TB i Hi) as E. rewrite Eb in E.
    destruct (TS (ly_tm row + Z.of_nat i) ltac:(rewrite T2 in Hi; rlia)) as ((sg & Hsg & Hw & Hr) & _ & _).
    assert (RA : lib.Lib.Mem.ro_addr RS (Z_to_bv 64 (ly_tm row + Z.of_nat i)) = true)
      by (apply (ce_ro_addr_seg sg); [exact Hsg | exact Hw | rewrite T2 in Hi; rlia | exact Hr]).
    split; [|exact RA].
    unfold lib.Lib.Mem.wa in E |- *. rewrite <- (RO _ RA). exact E. }
  (* aentry_k_on's shadow premise (its ctrl_emit_as_stretch_shadow_R, unfolded): the shadow words of f, md, d, s and
     (E) the output, on normalize memc, from the five ranges' shadow_hull_vis at memc *)
  assert (SRW : lib.B.ShadowRwOn.shadow_rw_on
     (fun a => lib.B.Prog.sh_word_on.sh_word_on f 24 a \/ lib.B.Prog.sh_word_on.sh_word_on md 296 a \/
               lib.B.Prog.sh_word_on.sh_word_on d 6 a \/ lib.B.Prog.sh_word_on.sh_word_on s 6 a \/
               (tctrl_emit_as_E row mb n = true /\
                lib.B.Prog.sh_word_on.sh_word_on o (tctrl_emit_as_len row n) a))
     (lib.B.MemNorm.normalize RS memc)).
  { apply (lib.B.ShadowRwOnT.shadow_rw_on_normalize _ memc RO).
    intros a0 Ha0 Hsh0. cbv beta in Ha0.
    destruct Ha0 as [Ha0 | [Ha0 | [Ha0 | [Ha0 | (EEo & Ha0)]]]].
    - exact (ce_srw_hull W memc f 24 fq0 ltac:(lia) ltac:(unfold ASAN_CEIL; rlia) HfV a0 Ha0 Hsh0).
    - exact (ce_srw_hull W memc md 296 mq0 ltac:(lia) ltac:(unfold ASAN_CEIL; rlia) HmV a0 Ha0 Hsh0).
    - exact (ce_srw_hull W memc d 6 dq0 ltac:(lia) ltac:(unfold ASAN_CEIL; rlia) HdV a0 Ha0 Hsh0).
    - exact (ce_srw_hull W memc s 6 sq0 ltac:(lia) ltac:(unfold ASAN_CEIL; rlia) HsV a0 Ha0 Hsh0).
    - pose proof (m_len EEo) as Ln. destruct (HEo EEo) as (_ & _ & _ & HoV & _).
      exact (ce_srw_hull W memc o (tctrl_emit_as_len row n) ltac:(rlia) ltac:(rlia) ltac:(unfold ASAN_CEIL; rlia)
               HoV a0 Ha0 Hsh0). }
  (* the continuation at the ctrl_lay_block argument setup, through ctrl_emit_asF.alay_pre *)
  assert (HK : forall (x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 : word)
                      (mc : word -> option byte), tctrl_emit_as_E row mb n = true ->
    lib.Lib.Step.rw_cells RS mc (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)
      (lib.Lib.Cells.CB 24 (lib.Lib.Mem.le8 w0 ++ lib.Lib.Mem.le8 (Z_to_bv 64 g) ++
                            lib.Lib.Mem.le8 (Z_to_bv 64 ns)) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 27) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 26) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 25) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 24) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 23) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 22) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 21) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 20) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 19) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 18) ::
       lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 9) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 8) ::
       [lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 1)]) ->
    lib.Lib.Frame.stk RS mc (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
      (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128) ->
    lib.Lib.Frame.munch [(bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640, bv_unsigned (lib.Reusable.YK11.getr regs 2));
                         (o, o + em_len (ubat row 21) n)] (lib.B.MemNorm.normalize RS memc) mc ->
    lib.Lib.Frame.wmono RS (lib.B.MemNorm.normalize RS memc) mc -> lib.Lib.Mem.mem_inv RS mc ->
    lib.B.Prog.ctrl_emit_asF.aJ_on (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 4)
      (lib.B.MemNorm.normalize RS memc) o f md d s n (ly_F lyc) row mc ->
    lib.Lib.Step.rw_cells RS mc o [lib.Lib.Cells.CB 6 db] ->
    lib.Lib.Step.rw_cells RS mc (o + 6) [lib.Lib.Cells.CB 6 sb] ->
    lib.Lib.Mem.bytes_at RS mc (o + 12)
      [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) mod 256);
       Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) / 256);
       nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)] ->
    lib.Lib.Mem.wr_at RS mc (o + 12) (Z.of_nat 6) ->
    lib.Lib.Step.rw_cells RS mc (o + 18)
      [lib.Lib.Cells.CB (Z.to_nat (em_len (ubat row 21) n - 18))
         (repeat (Z_to_bv 8 0) (Z.to_nat (em_len (ubat row 21) n - 18)))] ->
    lib.Lib.ExecF.evtF RS (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) m_QK1
      (lib.Lib.MState.MS
         (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128))
            (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) u0 u1 u2 (Z_to_bv 64 o) (Z_to_bv 64 f)
            y10 y11 y12 x13 x14 x15 x16 x17 (lib.Lib.Mem.zxb (nth 1 row (Z_to_bv 8 0)))
            (lib.Lib.Mem.zxb (nth 0 row (Z_to_bv 8 0))) (Z_to_bv 64 n) (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d)
            (Z_to_bv 64 s) (Z_to_bv 64 (em_len (ubat row 21) n)) (lib.Reusable.YK11.getr regs 15)
            (Z_to_bv 64 lib.B.AsanRT.ASAN_K) u3 u4 u5 u6)
         lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8571c) lib.Reusable.YK11.fp_csr None mc
         (lib.Lib.PropExec.seg_rom RS))).
  { intros x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 mc EE FR ST MU WM MIc AJc P1 P2 PH HW P18.
    eapply lib.Lib.ExecF.evtF_mono;
      [exact (lib.B.Prog.ctrl_emit_asF.alay_pre (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
        (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
        (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
        (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
        (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
        (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
        lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS memc) o f md d s g n ns
        row mb db sb (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc))) Hg HST Hrl Hml Hdb Hsb FpWIN
        x1 y10 y11 y12 x13 x14 x15 x16 x17 u0 u1 u2 u3 u4 u5 u6 w0 mc EE FR ST) |].
    intros ms' Hms. right. split; [exact EE|].
    exists u0, u1, u2, x14, x15, x16, x17, u3, u4, u5, u6, w0, mc.
    split; [exact Hms|]. split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM|].
    split; [exact MIc|]. split; [exact AJc|]. split; [exact P1|]. split; [exact P2|]. split; [exact PH|].
    split; [exact HW | exact P18]. }
  rewrite <- Etp in FPb, TLb.
  exact (lib.B.Prog.ctrl_emit_asF.aentry_k_on (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
    (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
    (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
    (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
    (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS memc) o f md d s g n ns
    (ly_F lyc) row tb mb nb gb db sb (ce_junk memc o (tctrl_emit_as_len row n))
    (lib.B.ProgBridge.RNG_W (ce_H (w_H W) (ly_F lyc)))
    Hn Hg HST Dsf Dsm Dsd Dss Hf0 Hf8 Hf24 Hrl HR Hc HL HA Htm' Hmd0 Hmd8 Hmd296 Hml HM Ho Ho1492 HEo'
    Hdb HD Hsb HSb MI AC WHM WAE AW Af Amd Ad As
    (conj (ce_app_addr_mem _ Hd6) (ce_app_addr_mem _ Hd7)) (conj (ce_app_addr_mem _ Hs6) (ce_app_addr_mem _ Hs7))
    AO FPb TLb (lib.B.ProgBridge.rng_bytes_RNG_W _) FpWIN FpWSH FpIMG FpROW
    (fun x Hx => FpSf1 x ltac:(rlia)) FpMD (fun x Hx => FpSmd1 x ltac:(rlia)) FpD
    (fun a b Ha Hab Hb => FpSdK a b Ha Hab ltac:(rlia)) FpS (fun a b Ha Hab Hb => FpSsK a b Ha Hab ltac:(rlia))
    (fun EE => proj1 (OFP EE)) (fun EE => proj2 (proj2 (OFP EE))) (fun EE => proj1 (proj2 (OFP EE)))
    m_QK1 SRW (lib.B.Prog.asan_memsetF_on.asan_memset_holds_F_on lib.B.Prog.memset.memset_holds)
    lib.B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on (fun ms _ H => or_introl H) HK
    (lib.Reusable.YK11.getr regs 5) (lib.Reusable.YK11.getr regs 6) (lib.Reusable.YK11.getr regs 7)
    (lib.Reusable.YK11.getr regs 28) (lib.Reusable.YK11.getr regs 30) (lib.Reusable.YK11.getr regs 31)).
Qed.

(* ---- the cut: the ctrl_lay_block call at 0x86104, through a Theorem Labs lane's tctrl_lay_block_spec, on the REAL memory
   mA at the cut (its premises are the caller's facts at memc, moved across stretch 1, which writes only the
   window and the output) ---- *)
Definition m_R (u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 : word) : bvmap 5 word :=
  lib.Lib.Frame.mkR (Z_to_bv 64 0x85730) (Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128))
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) u0 u1 u2
    (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
    x14 x15 x16 x17 (lib.Lib.Mem.zxb (nth 1 row (Z_to_bv 8 0))) (lib.Lib.Mem.zxb (nth 0 row (Z_to_bv 8 0)))
    (Z_to_bv 64 n) (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s)
    (Z_to_bv 64 (em_len (ubat row 21) n)) (lib.Reusable.YK11.getr regs 15) (Z_to_bv 64 lib.B.AsanRT.ASAN_K)
    u3 u4 u5 u6.

Definition m_lay_post (R' : bvmap 5 word) (mA : word -> option byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr R' 1) mem2
                  (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly Sj W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) /\
    aregs_preserved R' regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (o + 18)
      (map (fun x : byte => bv_unsigned x)
         (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb)) /\
    acall_kept SEGS B lyc Sc W mA W2 mem2 (spZ R' - 4512) (spZ R') (fun a => o + 18 <= a < o + 50).

Lemma m_cut_lay : forall (st : machine_state) md' (u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 : word)
    (mc : word -> option byte),
  tctrl_emit_as_E row mb n = true ->
  st = lib.Lib.MState.MS (m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) lib.Reusable.YK11.fp_regs
         (Z_to_bv 64 0x86104) lib.Reusable.YK11.fp_csr None (ms_mem st) (lib.Lib.PropExec.seg_rom RS) ->
  (forall a, lib.Lib.Mem.mrd RS (ms_mem st) a = lib.Lib.Mem.mrd RS mc a) ->
  lib.Lib.Frame.munch [(bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640, bv_unsigned (lib.Reusable.YK11.getr regs 2));
                       (o, o + em_len (ubat row 21) n)] memc (ms_mem st) ->
  lib.Lib.Frame.wmono RS memc (ms_mem st) ->
  lib.Lib.Step.rw_cells RS mc (o + 18)
    [lib.Lib.Cells.CB (Z.to_nat (em_len (ubat row 21) n - 18))
       (repeat (Z_to_bv 8 0) (Z.to_nat (em_len (ubat row 21) n - 18)))] ->
  same_but_materialized mdc md' ->
  SRr SEGS W (mkCfg st md') (m_lay_post (m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) (ms_mem st)).
Proof.
  intros st md' u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 mc EE Est Hmrd MUA WMA P18 Hmd.
  set (mA := ms_mem st) in Est, Hmrd, MUA, WMA |- *.
  set (R' := m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) in Est |- *.
  pose proof m_AR as HAR.
  pose proof m_win as (Wlo & Whi & WCS & WHM & WAE & W8 & WJ & Wpres).
  pose proof m_F as (FA & F64 & FGT & FC).
  pose proof (m_len EE) as Ln.
  pose proof ASAN_CEIL_range as (CR & _).
  pose proof Hhome as (cid & pos & Hin & Hcid & Ho1 & Ho2).
  pose proof (ce_frame_lo lyc Sc W memc mdc cid pos HAR Hin Hcid) as Hfl.
  pose proof (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin) as (Fb0 & Fb1 & Fb2).
  destruct (HEo EE) as (_ & HoW & HoA & HoV & HoP).
  destruct (HEd EE) as (D0 & D1 & D2 & D3 & D4 & D5 & D6).
  pose proof Dsf as Dsf'. pose proof Dsm as Dsm'. pose proof Dst as Dst'. pose proof Dsn as Dsn'.
  pose proof Hstk1 as Hstk1'. pose proof Hstk2 as Hstk2'. pose proof Hsp16 as Hsp16'.
  unfold CTRL_EMIT_AS_STK, spZ in Dsf', Dsm', Dst', Dsn', D0, Hstk1', Hstk2', Hsp16', Wlo, Whi, WHM, WAE,
    W8, WJ.
  change (Z.max 4640 (128 + 4512)) with 4640 in Dsf', Dsm', Dst', Dsn', D0, Hstk1'.
  change (em_len (ubat row 21) n) with (tctrl_emit_as_len row n) in MUA, P18.
  pose proof (ce_u64 (lib.Reusable.YK11.getr regs 2)) as Rsp.
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT in FGT. unfold kFakeStackSize in FC.
  unfold ASAN_CEIL in CR, Fb1, FC.
  (* what stretch 1 keeps *)
  pose proof (ce_raw2 memc mA _ _ o _ MUA) as KR.
  assert (Aw : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                 bv_unsigned (lib.Reusable.YK11.getr regs 2) -> lib.B.AsanRT.app_mem a)
    by (intros a Ha; apply (ce_win_app lyc Sc W memc mdc a HAR); rlia).
  assert (Ao : forall a, o <= a < o + tctrl_emit_as_len row n -> lib.B.AsanRT.app_mem a)
    by (intros a Ha; exact (proj1 (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin ltac:(rlia)))).
  assert (G2 : lib.Reusable.YK11.getr R' 2 =
               Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)) by reflexivity.
  unfold lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END in WHM, WAE.
  assert (Esp : spZ R' = bv_unsigned (lib.Reusable.YK11.getr regs 2) - 128)
    by (unfold spZ; rewrite G2;
        rewrite (lib.Lib.MState.unsigned_lit (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)) by rlia; rlia).
  assert (AE : forall q n0, q + n0 <= lib.Reusable.YM05.alloc_ceiling -> q + n0 <= lib.B.AsanRT.APPMEM_END)
    by (intros q n0 Hq; unfold lib.B.AsanRT.APPMEM_END in *; rlia).
  assert (L1 : ajournal SEGS B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W mA md' k).
  { apply (ce_jrnl2 STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k md' mA
             (fun a => (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                        bv_unsigned (lib.Reusable.YK11.getr regs 2)) \/ (o <= a < o + tctrl_emit_as_len row n)) HJ).
    - intros a. rlia.
    - intros x Hx. apply KR; intros h; apply Hx; [left | right]; exact h.
    - intros x Hx Hm. pose proof (ce_u64 x) as Rx.
      assert (Hni : ~ in_img SEGS (bv_unsigned x)) by (apply ce_not_img; left; destruct Hx as [Hx | Hx]; rlia).
      assert (Hwv : wview RS memc x <> None)
        by (unfold wview; destruct (memc x); [discriminate | exfalso; exact (Hm eq_refl)]).
      pose proof (WMA x Hwv) as Hwv'. unfold wview in Hwv'. destruct (mA x); [discriminate|].
      pose proof (find_segment_none SEGS (bv_unsigned x) Hni) as Hfs. change SEGS with RS in Hfs.
      rewrite Hfs in Hwv'. exact Hwv'.
    - intros x Hx. apply KR.
      + intros h. pose proof (proj1 (Wpres (bv_unsigned x) ltac:(rlia))) as Hv.
        rewrite Z_to_bv_bv_unsigned in Hv. congruence.
      + intros h. pose proof (proj1 (proj2 (HoW (bv_unsigned x) h))) as Hv.
        rewrite Z_to_bv_bv_unsigned in Hv. congruence.
    - exact Hmd.
    - intros a [Ha | Ha]; [left; rlia | exact (proj1 (HoW a Ha))]. }
  assert (L2 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mA)).
  { apply (ce_ro_keep RLO RHI B (w_H W) memc mA _ RRO_img HRO MUA). intros a (sg & Hsg & Hr).
    pose proof (ce_seg_lo_hi sg a Hsg Hr).
    apply ce_outside_iff. intros r Hr' Hin'. cbn [In] in Hr'.
    destruct Hr' as [<- | [<- | []]]; cbn [fst snd] in Hin'; rlia. }
  assert (L3 : lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr R' 1))
    by (change (lib.Reusable.YK11.getr R' 1) with (Z_to_bv 64 0x85730); vm_compute; reflexivity).
  assert (L4 : 4096 <= raZ R')
    by (unfold raZ; change (lib.Reusable.YK11.getr R' 1) with (Z_to_bv 64 0x85730);
        rewrite (lib.Lib.MState.unsigned_lit 0x85730) by lia; lia).
  (* ranges kept by stretch 1: a byte array apart from the window and the output *)
  assert (GK : forall q (bs : list byte), 0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
     ly_dj (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) (bv_unsigned (lib.Reusable.YK11.getr regs 2))
       q (q + Z.of_nat (length bs)) ->
     ly_dj o (o + tctrl_emit_as_len row n) q (q + Z.of_nat (length bs)) ->
     garr8 SEGS (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) bs) ->
     garr8 SEGS (mrestrict (w_H W) mA) q (map (fun x : byte => bv_unsigned x) bs))
    by (intros q bs; exact (ce_garr8_keep (w_H W) memc mA _ _ o _ q bs MUA)).
  assert (L22 : forall a, o + 18 <= a < o + 50 ->
     awr_byte STK sp0 FP (ablocks B ly Sj) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) mA a).
  { intros a Ha. destruct (HoW a ltac:(rlia)) as (Hw & Hh & _). split; [exact Hw|]. split; [exact Hh|].
    destruct (ce_present_of_rw mA mc (o + 18) _ Hmrd P18 (a - (o + 18))
                ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; rlia) ltac:(rlia)) as (b & Hb).
    exists b. replace (o + 18 + (a - (o + 18))) with a in Hb by lia. exact Hb. }
  assert (L23 : tctrl_lay_block_home lyc Sc (o + 18) 32).
  { intros a Ha. right. right. exists cid, pos. split; [exact Hin|]. split; [exact Hcid|].
    unfold in_zr, frame_rng. cbn [fst snd]. rlia. }
  assert (L24 : range_addressable (aview SEGS (w_H W) mA) SHADOW_OFF (o + 18) 32).
  { apply (ce_raddr_keep (w_H W) memc mA _ _ o _ (o + 18) 32 MUA ltac:(rlia) ltac:(apply AE; rlia) Aw Ao).
    apply (ce_raddr_sub _ o (tctrl_emit_as_len row n)); [exact HoA | rlia | rlia]. }
  assert (L25 : shadow_hull_vis (aview SEGS (w_H W) mA) (o + 18) 32).
  { apply (ce_hull_keep (w_H W) memc mA _ _ o _ (o + 18) 32 MUA ltac:(rlia) ltac:(lia) ltac:(apply AE; rlia) Aw Ao).
    apply (ce_hull_sub _ o (tctrl_emit_as_len row n)); [exact HoV | rlia | lia | rlia]. }
  assert (L26 : forall a, o + 18 <= a <= o + 50 -> app_addr a)
    by (intros a Ha; apply (in_app_addr _ _ a Fb2); rlia).
  pose proof (ce_ro_place lyc Sc W memc mdc f 24 HAR HfR) as (fq0 & fqc & fsd & fap).
  pose proof (ce_ro_place lyc Sc W memc mdc md 296 HAR HmR) as (mq0 & mqc & msd & map').
  unfold ASAN_CEIL in fqc, mqc.
  assert (L30 : garr8 SEGS (mrestrict (w_H W) mA) f (map (fun x : byte => bv_unsigned x) row))
    by (apply GK; [rlia | rewrite Hrl; rlia | rewrite Hrl; exact Dsf' | rewrite Hrl; exact D1 | exact HfG]).
  assert (L36 : ly_k row = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) mA) (ly_tm row) (map (fun x : byte => bv_unsigned x) tb) /\
     tctrl_lay_block_ro (ly_tm row) 32 /\
     (forall a, ly_tm row <= a < ly_tm row + 32 ->
        exists s0, In s0 SEGS /\ seg_writable s0 = false /\
          Z.of_N (seg_base s0) <= a < Z.of_N (seg_base s0) + Z.of_N (seg_size s0))).
  { intros K2. destruct (Htm K2) as (T1 & T2 & TG & TR & TS).
    pose proof (ce_ro_place lyc Sc W memc mdc (ly_tm row) 32 HAR TR) as (tq0 & tqc & _ & _).
    split; [exact T2|].
    split; [apply GK; [rlia | rewrite T2; rlia | rewrite T2; exact (Dst' K2) | rewrite T2; exact (D5 K2) | exact TG]|].
    split; [exact TR|].
    intros a Ha. exact (proj1 (TS a Ha)). }
  assert (L37 : 3 <= ly_k row <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) mA) md (map (fun x : byte => bv_unsigned x) mb) /\
     tctrl_lay_block_ro md 296 /\
     ((ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) mA) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        tctrl_lay_block_ro (rname mb) (Z.of_nat (length nb)))).
  { intros Kr _. split; [exact Hmd8|]. split; [exact Hml|].
    split; [apply GK; [rlia | rewrite Hml; rlia | rewrite Hml; exact Dsm' | rewrite Hml; exact D2 | exact HmG]|].
    split; [exact HmR|].
    intros Hbb Hhas Hrn.
    assert (NM : tctrl_emit_as_nm row mb) by (split; [split; [exact Kr | exact Hbb] | split; assumption]).
    destruct (Hnm NM) as (N1 & N2 & NG & NR).
    pose proof (ce_ro_place lyc Sc W memc mdc (rname mb) _ HAR NR) as (nq0 & _ & _ & _).
    split; [exact N1|].
    split; [apply GK; [rlia | exact N2 | exact (Dsn' NM) | exact (D6 NM) | exact NG]|].
    exact NR. }
  assert (L38 : g <> 0 -> ly_al row <> 0 ->
     Z.of_nat (length gb) = ly_al row /\
     garr8 SEGS (mrestrict (w_H W) mA) g (map (fun x : byte => bv_unsigned x) gb) /\
     tctrl_lay_block_ro g (ly_al row) /\
     app_addr (g + ly_al row) /\ app_addr (g + 7) /\ app_addr (o + 25 + ly_ao row))
    by (intros G0; exfalso; exact (G0 Hg0)).
  assert (L39 : ly_dj (spZ R' - 4512) (spZ R') (o + 18) (o + 50))
    by (rewrite Esp; pose proof D0 as Dx; unfold ly_dj in Dx |- *; rlia).
  assert (L40 : ly_dj (spZ R' - 4512) (spZ R') f (f + 24))
    by (rewrite Esp; pose proof Dsf' as Dx; unfold ly_dj in Dx |- *; rlia).
  assert (L41 : ly_k row = 2 -> ly_dj (spZ R' - 4512) (spZ R') (ly_tm row) (ly_tm row + 32))
    by (intros K2; pose proof (Dst' K2) as Dx; rewrite Esp; unfold ly_dj in Dx |- *; rlia).
  assert (L42 : g <> 0 -> ly_al row <> 0 -> ly_dj (spZ R' - 4512) (spZ R') g (g + ly_al row))
    by (intros G0; exfalso; exact (G0 Hg0)).
  assert (L43 : 3 <= ly_k row <= 9 -> md <> 0 ->
     ly_dj (spZ R' - 4512) (spZ R') md (md + 296) /\
     ((ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (spZ R' - 4512) (spZ R') (rname mb) (rname mb + Z.of_nat (length nb)))).
  { intros Kr _. split; [rewrite Esp; pose proof Dsm' as Dx; unfold ly_dj in Dx |- *; rlia|].
    intros Hbb Hhas Hrn.
    assert (NM : tctrl_emit_as_nm row mb) by (split; [split; [exact Kr | exact Hbb] | split; assumption]).
    pose proof (Dsn' NM) as Dx. rewrite Esp; unfold ly_dj in Dx |- *; rlia. }
  assert (L44 : ly_dj (o + 18) (o + 50) f (f + 24)) by (pose proof D1 as Dx; unfold ly_dj in Dx |- *; rlia).
  assert (L45 : ly_k row = 2 -> ly_dj (o + 18) (o + 50) (ly_tm row) (ly_tm row + 32))
    by (intros K2; pose proof (D5 K2) as Dx; unfold ly_dj in Dx |- *; rlia).
  assert (L46 : 3 <= ly_k row <= 9 -> md <> 0 -> ly_dj (o + 18) (o + 50) md (md + 296))
    by (intros _ _; pose proof D2 as Dx; unfold ly_dj in Dx |- *; rlia).
  assert (L47 : 3 <= ly_k row <= 9 -> md <> 0 -> (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6) -> has mb <> 0 ->
     rname mb <> 0 -> ly_dj (o + 18) (o + 50) (rname mb) (rname mb + Z.of_nat (length nb))).
  { intros Kr _ Hbb Hhas Hrn.
    assert (NM : tctrl_emit_as_nm row mb) by (split; [split; [exact Kr | exact Hbb] | split; assumption]).
    pose proof (D6 NM) as Dx. unfold ly_dj in Dx |- *; rlia. }
  assert (L48 : g <> 0 -> ly_al row <> 0 -> ly_dj (o + 18) (o + 50) g (g + ly_al row))
    by (intros G0; exfalso; exact (G0 Hg0)).
  assert (L15 : spZ R' mod 16 = 0) by (rewrite Esp; rlia).
  assert (L16 : sp0 - STK <= spZ R' - 4512) by (rewrite Esp; rlia).
  assert (L17 : spZ R' <= sp0) by (rewrite Esp; rlia).
  assert (L5 : lib.Reusable.YK11.getr R' 3 = w64 (as_gp B)) by exact Hgp.
  assert (L6 : lib.Reusable.YK11.getr R' 4 = w64 (as_tp B)) by exact Htp.
  assert (L7 : lib.Reusable.YK11.getr R' 10 = w64 o) by reflexivity.
  assert (L8 : lib.Reusable.YK11.getr R' 11 = w64 f) by reflexivity.
  assert (L9 : lib.Reusable.YK11.getr R' 12 = w64 md) by reflexivity.
  assert (L10 : lib.Reusable.YK11.getr R' 13 = w64 g) by reflexivity.
  pose proof (tctrl_lay_block_spec STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W mA md' k R' o f md g row tb mb nb gb
    L1 L2 L3 L4 L5 L6 L7 L8 L9 L10
    ltac:(rlia) ltac:(rlia) ltac:(rlia) Hg L15 L16 L17
    Hcnt1 Hcnt0 ltac:(rlia) ltac:(rlia) L22 L23 L24 L25 L26 Hf8 Hrl L30 HfR Hk Hao L36 L37 L38
    L39 L40 L41 L42 L43 L44 L45 L46 L47 L48) as LB.
  rewrite Est. exact LB.
Qed.

(* ---- stretch 3: from ctrl_lay_block's return (0x85730) to the end, ctrl_emit_asF.alay_ret_on with its Section
   memory m := normalize mem2, the return memory (so its munch / wmono premise is reflexive: no raw munch crosses
   the call), every m-fact re-based at mem2 (decisions.md items 24 / 26); then ce_finish ---- *)
Lemma m_ret : forall (mA mc : word -> option byte) (u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 w0 : word)
    (W2 : world SEGS) (c2 : config),
  tctrl_emit_as_E row mb n = true ->
  (forall a, lib.Lib.Mem.mrd RS mA a = lib.Lib.Mem.mrd RS mc a) ->
  (forall a bs, lib.Lib.Mem.bytes_at RS mA a bs <-> lib.Lib.Mem.bytes_at RS mc a bs) ->
  (forall a n0, lib.Lib.Mem.wr_at RS mc a n0 -> lib.Lib.Mem.wr_at RS mA a n0) ->
  lib.Lib.Frame.munch [(bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640, bv_unsigned (lib.Reusable.YK11.getr regs 2));
                       (o, o + em_len (ubat row 21) n)] memc mA ->
  lib.Lib.Step.rw_cells RS mc (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)
    (lib.Lib.Cells.CB 24 (lib.Lib.Mem.le8 w0 ++ lib.Lib.Mem.le8 (Z_to_bv 64 g) ++ lib.Lib.Mem.le8 (Z_to_bv 64 ns)) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 27) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 26) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 25) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 24) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 23) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 22) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 21) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 20) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 19) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 18) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 9) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 8) ::
     [lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 1)]) ->
  lib.Lib.Frame.stk RS mc (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
    (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128) ->
  lib.Lib.Step.rw_cells RS mc o [lib.Lib.Cells.CB 6 db] ->
  lib.Lib.Step.rw_cells RS mc (o + 6) [lib.Lib.Cells.CB 6 sb] ->
  lib.Lib.Mem.bytes_at RS mc (o + 12)
    [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) mod 256);
     Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) / 256);
     nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)] ->
  lib.Lib.Mem.wr_at RS mc (o + 12) (Z.of_nat 6) ->
  lib.Lib.Step.rw_cells RS mc (o + 18)
    [lib.Lib.Cells.CB (Z.to_nat (em_len (ubat row 21) n - 18))
       (repeat (Z_to_bv 8 0) (Z.to_nat (em_len (ubat row 21) n - 18)))] ->
  wle W W2 -> m_lay_post (m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) mA W2 c2 ->
  SRr SEGS W2 c2
    (tctrl_emit_as_post B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc k regs o md g n row tb mb nb gb db sb).
Proof.
  intros mA mc u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 w0 W2 c2 EE Hmrd Hby Hwr MUA FR ST P1 P2 PH HW P18 Hle
    (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & Hfrs & Hbl & HLB & Hkept).
  subst c2.
  set (R' := m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) in Hpres, Hkept |- *.
  pose proof m_AR as HAR. pose proof (proj1 HJ2) as HAR2.
  pose proof HJ as (_ & (_ & _ & _ & _ & _ & EF1 & _ & _ & _ & El1 & Eh1 & _) & _).
  pose proof HJ2 as (_ & (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & El2 & Eh2 & _) & _).
  assert (EF : ly_F ly2 = ly_F lyc) by congruence.
  assert (El : ly_stk_lo ly2 = ly_stk_lo lyc) by congruence.
  assert (Eh : ly_stk_hi ly2 = ly_stk_hi lyc) by congruence.
  pose proof m_win as (Wlo & Whi & WCS & WHM & WAE & W8 & WJ & Wpres).
  pose proof m_F as (FA & F64 & FGT & FC).
  pose proof (m_len EE) as Ln.
  pose proof ASAN_CEIL_range as (CR & _).
  pose proof Hhome as (cid & pos & Hin & Hcid & Ho1 & Ho2).
  pose proof (ce_frame_lo lyc Sc W memc mdc cid pos HAR Hin Hcid) as Hfl.
  pose proof (frames_bounds SEGS B AR_laws_B _ _ _ _ _ _ _ HAR Hin) as (Fb0 & Fb1 & Fb2).
  destruct (HEo EE) as (_ & HoW & HoA & HoV & HoP).
  destruct (HEd EE) as (D0 & D1 & D2 & D3 & D4 & D5 & D6).
  pose proof Hstk1 as Hstk1'. pose proof Hstk2 as Hstk2'. pose proof Hsp16 as Hsp16'.
  unfold CTRL_EMIT_AS_STK, spZ in D0, Hstk1', Hstk2', Hsp16', Wlo, Whi, WHM, WAE, W8, WJ.
  change (Z.max 4640 (128 + 4512)) with 4640 in D0, Hstk1'.
  change (em_len (ubat row 21) n) with (tctrl_emit_as_len row n) in MUA, P18.
  unfold lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END in WHM, WAE.
  pose proof (ce_u64 (lib.Reusable.YK11.getr regs 2)) as Rsp.
  unfold lib.B.Prog.asan_stack_malloc_c.ASAN_GT in FGT. unfold kFakeStackSize in FC.
  unfold ASAN_CEIL in CR, Fb1, FC, WCS.
  assert (G2 : lib.Reusable.YK11.getr R' 2 =
               Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)) by reflexivity.
  assert (Esp : spZ R' = bv_unsigned (lib.Reusable.YK11.getr regs 2) - 128)
    by (unfold spZ; rewrite G2;
        rewrite (lib.Lib.MState.unsigned_lit (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)) by rlia; rlia).
  rewrite Esp in Hkept.
  assert (HRR : tctrl_emit_as_R row mb n = tctrl_emit_as_len row n) by (unfold tctrl_emit_as_R; rewrite EE; reflexivity).
  (* the real side at the cut: raw bytes, the window present *)
  assert (Aw : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                 bv_unsigned (lib.Reusable.YK11.getr regs 2) -> lib.B.AsanRT.app_mem a)
    by (intros a Ha; apply (ce_win_app lyc Sc W memc mdc a HAR); rlia).
  assert (Ao : forall a, o <= a < o + tctrl_emit_as_len row n -> lib.B.AsanRT.app_mem a)
    by (intros a Ha; exact (proj1 (ce_frame_byte lyc Sc W memc mdc cid pos a HAR Hin ltac:(rlia)))).
  pose proof (ce_rw_of_rb mA mc _ _ Hby Hwr FR) as FRA.
  assert (PWA : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                  bv_unsigned (lib.Reusable.YK11.getr regs 2) -> apresent (w_H W) mA a).
  { intros a Ha. split; [exact (proj1 (Wpres a ltac:(rlia)))|].
    destruct (Z_lt_le_dec a (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)) as [h | h].
    - exact (ce_present_stk mA mc _ _ Hmrd ST ltac:(rlia) ltac:(rlia) a ltac:(rlia)).
    - destruct (ce_present_of_rw mA mc _ _ Hmrd FR (a - (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128))
                  ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; rlia) ltac:(rlia)) as (b & Hb).
      exists b. replace (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128 +
                         (a - (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128))) with a in Hb by lia. exact Hb. }
  (* the output's bytes at the cut: every one present on the real side *)
  assert (POA : forall a, o <= a < o + tctrl_emit_as_len row n -> exists b, mA (Z_to_bv 64 a) = Some b).
  { intros a Ha.
    destruct (Z_lt_le_dec a (o + 6)) as [h1 | h1];
      [| destruct (Z_lt_le_dec a (o + 12)) as [h2 | h2];
         [| destruct (Z_lt_le_dec a (o + 18)) as [h3 | h3]]].
    - destruct (ce_present_of_rw mA mc o _ Hmrd P1 (a - o) ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; rlia)
                  ltac:(rlia)) as (b & Hb). exists b. replace (o + (a - o)) with a in Hb by lia. exact Hb.
    - destruct (ce_present_of_rw mA mc (o + 6) _ Hmrd P2 (a - (o + 6))
                  ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; rlia) ltac:(rlia)) as (b & Hb).
      exists b. replace (o + 6 + (a - (o + 6))) with a in Hb by lia. exact Hb.
    - destruct PH as (_ & _ & PHb).
      assert (Hi : (Z.to_nat (a - (o + 12)) < 6)%nat) by rlia.
      pose proof (PHb _ Hi) as Eb. rewrite Z2Nat.id in Eb by lia.
      destruct (nth_error _ (Z.to_nat (a - (o + 12)))) as [b|] eqn:En; [|apply nth_error_None in En; cbn in En; lia].
      exists b. rewrite <- Hmrd in Eb. unfold lib.Lib.Mem.wa in Eb.
      replace (o + 12 + (a - (o + 12))) with a in Eb by lia.
      exact (ce_raw_of_mrd mA a b ltac:(rlia) ltac:(left; rlia) Eb).
    - destruct (ce_present_of_rw mA mc (o + 18) _ Hmrd P18 (a - (o + 18))
                  ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; rlia) ltac:(rlia)) as (b & Hb).
      exists b. replace (o + 18 + (a - (o + 18))) with a in Hb by lia. exact Hb. }
  (* mem2: the output bytes outside [o + 18, o + 50) and our frame cells are the cut's bytes *)
  assert (KO : forall a, o <= a < o + tctrl_emit_as_len row n -> ~ (o + 18 <= a < o + 50) ->
                 mem2 (Z_to_bv 64 a) = mA (Z_to_bv 64 a)).
  { intros a Ha Hne.
    destruct (ce_kept_frame lyc Sc W W2 memc mA mem2 mdc _ _ _ cid pos HAR Hkept Hin a ltac:(rlia))
      as (KV & _).
    apply (ce_view_raw (w_H W) (w_H W2) mA mem2 a ltac:(rlia) ltac:(left; rlia)).
    - exact (proj1 (proj2 (HoW a Ha))).
    - exact (ce_wle_vis W W2 _ Hle (proj1 (proj2 (HoW a Ha)))).
    - exact (KV Hne). }
  assert (KF : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 128 <= a <
                 bv_unsigned (lib.Reusable.YK11.getr regs 2) -> mem2 (Z_to_bv 64 a) = mA (Z_to_bv 64 a)).
  { intros a Ha. pose proof Hkept as (K1 & _).
    pose proof (proj1 (Wpres a ltac:(rlia))) as Hv.
    apply (ce_view_raw (w_H W) (w_H W2) mA mem2 a ltac:(rlia) ltac:(left; rlia) Hv (ce_wle_vis W W2 _ Hle Hv)).
    apply K1; rlia. }
  assert (PW2 : forall a, bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= a <
                  bv_unsigned (lib.Reusable.YK11.getr regs 2) -> apresent (w_H W2) mem2 a).
  { intros a Ha. pose proof Hkept as (_ & _ & _ & _ & K5 & K6).
    destruct (Z_lt_le_dec a (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 128)) as [h | h].
    - apply K6. rlia.
    - apply K5; [rlia | rlia | exact (PWA a ltac:(rlia))]. }
  (* zeros of the cut's tail, raw on the real side *)
  assert (ZA : forall a, o + 18 <= a < o + tctrl_emit_as_len row n -> mA (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. destruct P18 as ((_ & (_ & _ & HB)) & _).
    assert (Hj : (Z.to_nat (a - (o + 18)) <
                  length (lib.Lib.Cells.cells_bytes
                            [lib.Lib.Cells.CB (Z.to_nat (tctrl_emit_as_len row n - 18))
                               (repeat (Z_to_bv 8 0) (Z.to_nat (tctrl_emit_as_len row n - 18)))]))%nat).
    { cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r, repeat_length. rlia. }
    pose proof (HB _ Hj) as Eb. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes] in Eb.
    rewrite app_nil_r, nth_error_repeat in Eb by rlia. rewrite Z2Nat.id in Eb by lia.
    rewrite <- Hmrd in Eb. unfold lib.Lib.Mem.wa in Eb. replace (o + 18 + (a - (o + 18))) with a in Eb by lia.
    exact (ce_raw_of_mrd mA a _ ltac:(rlia) ltac:(left; rlia) Eb). }
  (* the return state's AR facts (ce_base at the return memory) *)
  assert (RO1 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mA)).
  { apply (ce_ro_keep RLO RHI B (w_H W) memc mA _ RRO_img HRO MUA). intros a (sg & Hsg & Hr).
    pose proof (ce_seg_lo_hi sg a Hsg Hr).
    apply ce_outside_iff. intros r Hr' Hin'. cbn [In] in Hr'.
    destruct Hr' as [<- | [<- | []]]; cbn [fst snd] in Hin'; rlia. }
  pose proof (ce_ro_kept lyc Sc W W2 mA mem2 _ _ _ Hkept RO1) as RO2v.
  pose proof (ce_ro_place lyc Sc W memc mdc f 24 HAR HfR) as (fq0 & fqc & fsd & fap).
  pose proof (ce_ro_place lyc Sc W memc mdc md 296 HAR HmR) as (mq0 & mqc & msd & map').
  pose proof (ce_home_place lyc Sc W memc mdc d 6 HAR ltac:(lia) HdP HdH) as (dq0 & dqc & dsd & dap).
  pose proof (ce_home_place lyc Sc W memc mdc s 6 HAR ltac:(lia) HsP HsH) as (sq0 & sqc & ssd & sap).
  unfold ASAN_CEIL in fqc, mqc, dqc, sqc.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hin).
  assert (FA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos) by (unfold frame_addr; rewrite EF; reflexivity).
  destruct (ce_base ly2 S2 W2 mem2 md2 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
              (bv_unsigned (lib.Reusable.YK11.getr regs 2)) o f md d s (tctrl_emit_as_R row mb n) cid pos
              HAR2 RO2v ltac:(rewrite El; rlia) ltac:(rlia) ltac:(rewrite Eh; rlia) Hin2 Hcid
              ltac:(rewrite FA2; exact Ho1) ltac:(rewrite FA2; exact Ho2) m_RR
              ltac:(intros x Hx; split; [exact (fap x Hx) | rewrite EF; rlia])
              ltac:(intros x Hx; split; [exact (map' x Hx) | rewrite EF; rlia])
              ltac:(intros x Hx; split; [exact (dap x Hx) | rewrite EF; rlia])
              ltac:(intros x Hx; split; [exact (sap x Hx) | rewrite EF; rlia]))
    as (RO2 & MI2 & AC2 & AW2 & FP2 & TL2).
  rewrite HRR in FP2. rewrite EF in FP2, TL2.
  assert (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = lib.B.AsanRT.RT_TP).
  { rewrite Htp. unfold w64. rewrite (lib.B.ProgWorld.as_tp_RT_TP B HTS).
    apply lib.Lib.MState.unsigned_lit. unfold lib.B.AsanRT.RT_TP. lia. }
  rewrite <- Etp in FP2, TL2.
  (* the run's facts on mN := normalize mem2 *)
  assert (STN : forall hi, hi <= bv_unsigned (lib.Reusable.YK11.getr regs 2) ->
     bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 <= hi ->
     lib.Lib.Frame.stk RS (lib.B.MemNorm.normalize RS mem2) (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) hi).
  { intros hi H1 H2. apply (lib.B.MemNormTr.stk_normalize_ro mem2 _ _ RO2); [unfold lib.B.Prog.ImgBounds.IMG_HI; rlia|].
    split; [rlia|]. split; [rlia|]. intros a Ha. destruct (PW2 a ltac:(rlia)) as (_ & b & Hb).
    split; [unfold wview, lib.Lib.Mem.wa; rewrite Hb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. reflexivity. }
  assert (NRM : forall p cs, (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> 0x5fe000 <= p + i < 2 ^ 64) ->
     lib.Lib.Step.rw_cells RS mem2 p cs -> lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) p cs).
  { intros p cs Hp Hrw. apply (lib.B.MemNormTr.rw_cells_normalize mem2 p cs RO2); [|exact Hrw].
    intros i Hi. apply lib.B.MemNormTr.ro_addr_above_img. unfold lib.B.Prog.ImgBounds.IMG_HI.
    exact (Hp i Hi). }
  assert (FR1 : lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2)
                  (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128)
    (lib.Lib.Cells.C8 w0 :: lib.Lib.Cells.C8 (Z_to_bv 64 g) :: lib.Lib.Cells.C8 (Z_to_bv 64 ns) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 27) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 26) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 25) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 24) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 23) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 22) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 21) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 20) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 19) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 18) ::
     lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 9) :: lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 8) ::
     [lib.Lib.Cells.C8 (lib.Reusable.YK11.getr regs 1)])).
  { apply ce_cb3_c8. apply NRM; [intros i Hi; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; rlia|].
    apply (ce_rw_ext mA); [|exact FRA]. intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi.
    unfold lib.Lib.Mem.wa. apply KF. rlia. }
  assert (OK2 : forall p cs, o <= p -> p + Z.of_nat (lib.Lib.Cells.cells_size cs) <= o + 18 ->
     lib.Lib.Step.rw_cells RS mc p cs -> lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) p cs).
  { intros p cs H1 H2 Hrw. apply NRM; [intros i Hi; rlia|].
    apply (ce_rw_ext mA); [|exact (ce_rw_of_rb mA mc p cs Hby Hwr Hrw)].
    intros i Hi. unfold lib.Lib.Mem.wa. apply KO; rlia. }
  assert (P1N := OK2 o [lib.Lib.Cells.CB 6 db] ltac:(lia)
                   ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; lia) P1).
  assert (P2N := OK2 (o + 6) [lib.Lib.Cells.CB 6 sb] ltac:(lia)
                   ltac:(cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; lia) P2).
  assert (P3N : lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) (o + 12)
    [lib.Lib.Cells.CB 6 [Z_to_bv 8 136; Z_to_bv 8 25;
       Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) mod 256);
       Z_to_bv 8 ((bv_unsigned (lib.Reusable.YK11.getr regs 15) mod 65536) / 256);
       nth 0 row (Z_to_bv 8 0); nth 1 row (Z_to_bv 8 0)]]).
  { apply OK2; [lia | cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; lia |].
    split; [split; [split; [reflexivity | exact I] |] | exact HW].
    cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact PH. }
  assert (LL : length (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb) = 32%nat).
  { apply (ce_lay_len row tb mb nb gb md g Hml); [|intros G0; exfalso; exact (G0 Hg0) | exact Hao].
    intros K2. exact (proj1 (proj2 (Htm K2))). }
  destruct (ce_bytes_of_garr8 W2 mem2 (o + 18) _ ltac:(lia) ltac:(rewrite LL; rlia) HLB) as (LB2 & LBV).
  assert (LAYN : lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) (o + 18)
    [lib.Lib.Cells.CB 32 (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb)]).
  { rewrite <- LL at 1. apply NRM; [intros i Hi; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; rlia|].
    apply ce_rw_cb; [exact LB2 | intros i Hi; lia]. }
  assert (Z2 : forall a, o + 50 <= a < o + tctrl_emit_as_len row n -> mem2 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  { intros a Ha. rewrite (KO a ltac:(rlia) ltac:(rlia)). exact (ZA a ltac:(rlia)). }
  assert (P5N : lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) (o + 50)
    [lib.Lib.Cells.CB (Z.to_nat (tctrl_emit_as_len row n - 52))
       (repeat (Z_to_bv 8 0) (Z.to_nat (tctrl_emit_as_len row n - 52)))]).
  { apply NRM; [intros i Hi; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; rlia|].
    apply ce_zero_cells; [rlia | rlia | rlia | intros i Hi; apply Z2; rlia]. }
  assert (P6N : lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) (o + tctrl_emit_as_len row n + -2)
    [lib.Lib.Cells.CB 2 (repeat (Z_to_bv 8 0) 2)]).
  { apply NRM; [intros i Hi; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; rlia|].
    apply (ce_zero_cells mem2 _ 2); [lia | rlia | rlia | intros i Hi; apply Z2; rlia]. }
  (* every output byte present at mem2 *)
  assert (PO2 : forall i, 0 <= i < tctrl_emit_as_len row n -> exists b, mem2 (Z_to_bv 64 (o + i)) = Some b).
  { intros i Hi. destruct (Z_lt_le_dec (o + i) (o + 18)) as [h | h];
      [| destruct (Z_lt_le_dec (o + i) (o + 50)) as [h' | h']].
    - rewrite (KO (o + i) ltac:(rlia) ltac:(rlia)). exact (POA (o + i) ltac:(rlia)).
    - destruct LB2 as (_ & _ & HB).
      assert (Hj : (Z.to_nat (o + i - (o + 18)) <
                    length (ly_lay (ly_k row) tb (ly_Z md mb nb (ly_bb (ly_k row))) g (ly_ao row) (ly_al row) gb))%nat)
        by (rewrite LL; rlia).
      pose proof (HB _ Hj) as Eb. rewrite Z2Nat.id in Eb by lia.
      destruct (nth_error _ _) as [b|] eqn:En; [|apply nth_error_None in En; rlia].
      exists b. unfold lib.Lib.Mem.wa in Eb. replace (o + 18 + (o + i - (o + 18))) with (o + i) in Eb by lia.
      exact (ce_raw_of_mrd mem2 (o + i) b ltac:(rlia) ltac:(left; rlia) Eb).
    - rewrite (KO (o + i) ltac:(rlia) ltac:(rlia)). exact (POA (o + i) ltac:(rlia)). }
  (* the m-facts of alay_ret_on's Section at m := normalize mem2 *)
  assert (HEoN : tctrl_emit_as_E row mb n = true ->
     lib.Lib.Step.rw_cells RS (lib.B.MemNorm.normalize RS mem2) o
       [lib.Lib.Cells.CB (Z.to_nat (tctrl_emit_as_len row n)) (ce_junk mem2 o (tctrl_emit_as_len row n))] /\
     ly_dj (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) (bv_unsigned (lib.Reusable.YK11.getr regs 2))
       o (o + tctrl_emit_as_len row n) /\
     ly_dj o (o + tctrl_emit_as_len row n) f (f + 24) /\
     (ly_k row = 2 -> ly_dj o (o + tctrl_emit_as_len row n) (ly_tm row) (ly_tm row + 32)) /\
     ly_dj o (o + tctrl_emit_as_len row n) md (md + 296) /\
     (tctrl_emit_as_nm row mb ->
        ly_dj o (o + tctrl_emit_as_len row n) (rname mb) (rname mb + Z.of_nat (length nb))) /\
     ly_dj o (o + tctrl_emit_as_len row n) d (d + 6) /\ ly_dj o (o + tctrl_emit_as_len row n) s (s + 6) /\
     (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + tctrl_emit_as_len row n) g (g + ly_al row))).
  { intros _. split; [|split; [exact D0|]; split; [exact D1|]; split; [exact D5|]; split; [exact D2|];
                       split; [exact D6|]; split; [exact D3|]; split; [exact D4 | intros G0; exfalso; exact (G0 Hg0)]].
    apply NRM; [intros i Hi; cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi; rlia|].
    apply ce_junk_rw; [lia | rlia | rlia |]. intros i Hi. exact (PO2 i Hi). }
  assert (ADN : forall q n0, tctrl_emit_as_ro RLO RHI B GLOBS q n0 -> 0 < n0 ->
     lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS mem2) q n0).
  { intros q n0 Hro Hn0. pose proof (ce_ro_place lyc Sc W memc mdc q n0 HAR Hro) as (q0 & qc & _ & qap).
    apply (ce_addr_n W2 mem2 q n0 RO2); [exact q0 | lia | exact qc | exact qap |].
    exact (proj1 (ce_ro_read ly2 S2 W2 mem2 md2 q n0 HAR2 Hro Hn0)). }
  assert (AfN := ADN f 24 HfR ltac:(lia)). assert (AmdN := ADN md 296 HmR ltac:(lia)).
  assert (AnN : tctrl_emit_as_nm row mb ->
     lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS mem2) (rname mb) (Z.of_nat (length nb))).
  { intros NM. destruct (Hnm NM) as (N1 & _ & _ & NR). apply (ADN _ _ NR).
    destruct N1 as ((Nl & _) & _). lia. }
  (* the output's shadow at mem2: kept from the cut (a caller frame's shadow) *)
  assert (RAO : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF o (tctrl_emit_as_len row n)).
  { pose proof (ce_raddr_keep (w_H W) memc mA _ _ o _ o (tctrl_emit_as_len row n) MUA ltac:(rlia)
                  ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) Aw Ao HoA) as RA1.
    intros x Hx. destruct (RA1 x Hx) as (sv & Esv & Ok). exists sv. split; [|exact Ok].
    destruct (ce_kept_frame lyc Sc W W2 memc mA mem2 mdc _ _ _ cid pos HAR Hkept Hin x ltac:(rlia)) as (_ & KS).
    rewrite KS; [exact Esv|]. intros HE. pose proof (Ao (shadow_of_addr SHADOW_OFF x) ltac:(rlia)) as Hap.
    unfold shadow_of_addr, SHADOW_OFF, lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END,
      lib.B.AsanRT.HIGHMEM_BEG, lib.B.AsanRT.APPMEM_END in Hap. rlia. }
  assert (AON : tctrl_emit_as_E row mb n = true ->
     lib.B.AsanRT.addressable (lib.B.MemNorm.normalize RS mem2) o (tctrl_emit_as_len row n) /\
     lib.B.AsanRT.app_mem (o + tctrl_emit_as_len row n) /\
     (o + tctrl_emit_as_len row n <= lib.B.AsanRT.RT_LO \/ lib.B.AsanRT.RT_HI <= o)).
  { intros _. split; [apply (ce_addr_n W2 mem2 o _ RO2); [rlia | rlia | unfold ASAN_CEIL; rlia | exact Ao | exact RAO]|].
    split; [exact (ce_app_addr_mem _ HoP) | right; unfold lib.B.AsanRT.RT_HI; rlia]. }
  (* the read bytes at mem2: registered read-only globals, the same in every arodata state *)
  assert (RG2 : forall q (bs : list byte), tctrl_emit_as_ro RLO RHI B GLOBS q (Z.of_nat (length bs)) ->
     garr8 SEGS (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) bs) ->
     garr8 SEGS (mrestrict (w_H W2) mem2) q (map (fun x : byte => bv_unsigned x) bs)).
  { intros q bs (_ & _ & _ & Hb) HG. apply (ce_garr8_view (w_H W) (w_H W2) memc mem2); [|exact HG].
    intros j Hj. rewrite length_map in Hj. destruct (Hb (q + Z.of_nat j) ltac:(lia)) as (Hseg & Hno & He).
    rewrite (RO2v _ Hseg Hno He). symmetry. exact (HRO _ Hseg Hno He). }
  assert (HRN : lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS mem2) f row).
  { apply (ce_bytes_n W2 mem2 f row RO2); [lia | rewrite Hrl; rlia |].
    apply RG2; [rewrite Hrl; exact HfR | exact HfG]. }
  assert (HnmN : tctrl_emit_as_nm row mb -> name_ok nb /\ lib.Lib.Mem.bytes_at RS (lib.B.MemNorm.normalize RS mem2) (rname mb) nb).
  { intros NM. destruct (Hnm NM) as (N1 & N2 & NG & NR). split; [exact N1|].
    pose proof (ce_ro_place lyc Sc W memc mdc _ _ HAR NR) as (nq0 & _).
    apply (ce_bytes_n W2 mem2 _ nb RO2); [exact nq0 | exact N2 | exact (RG2 _ _ NR NG)]. }
  (* the footprint of stretch 3: RNG_W (ce_H (w_H W2) (ly_F lyc)) *)
  assert (VW2 : forall x, w_H W x = false -> w_H W2 x = false) by (intros x; exact (ce_wle_vis W W2 x Hle)).
  assert (FpWIN2 : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc)))
                     (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) 4640).
  { apply ce_rng_bytes; [exact FA | rlia | rlia |]. intros a Ha.
    split; [apply VW2; exact (proj1 (Wpres a ltac:(rlia)))|].
    split; [apply Aw; rlia | rlia]. }
  assert (FpIMG2 : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) 0x10000 0x5ee000).
  { apply ce_rng_bytes; [exact FA | lia | lia |]. intros a Ha.
    pose proof (lib.B.ProgBridge.img_vis_W W2) as (_ & _ & Hv).
    split; [apply Hv; unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI; lia|].
    split; [unfold lib.B.AsanRT.app_mem, lib.B.AsanRT.LOWMEM_END; left; lia | rlia]. }
  pose proof m_fRV as (HfA & HfV).
  pose proof (ce_range_rngV W2 (ly_F lyc) f 24 FA F64 fq0 ltac:(lia) ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) fsd
                (fun a Ha => conj (VW2 _ (ce_vis_of_garr8 W memc f row ltac:(lia) ltac:(rewrite Hrl; rlia) HfG a
                                            ltac:(rewrite Hrl; rlia))) (fap a Ha))
                (fun s0 Hs0 => VW2 _ (ce_hull_cover (w_H W) memc f 24 ltac:(lia)
                                        ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) HfV s0 Hs0)))
    as (FpROW2 & FpSfK2 & FpSf12).
  assert (OFP2 : tctrl_emit_as_E row mb n = true ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) o (tctrl_emit_as_len row n) /\
     (forall a b, o <= a -> a <= b -> b <= o + tctrl_emit_as_len row n - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
          ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)) /\
     (forall x, o <= x <= o + tctrl_emit_as_len row n - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) (x / 8 + lib.B.AsanRT.ASAN_K) 1)).
  { intros _. apply (ce_range_rngV W2 (ly_F lyc) o (tctrl_emit_as_len row n) FA F64 ltac:(rlia) ltac:(rlia)
                       ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) ltac:(right; rlia)).
    - intros a Ha. split; [apply VW2; exact (proj1 (proj2 (HoW a Ha))) | exact (Ao a Ha)].
    - intros s0 Hs0. apply VW2. exact (ce_hull_cover (w_H W) memc o (tctrl_emit_as_len row n) ltac:(rlia)
                                         ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) HoV s0 Hs0). }
  assert (NFP2 : tctrl_emit_as_nm row mb ->
     lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) (rname mb) (Z.of_nat (length nb)) /\
     (forall a b, rname mb <= a -> a <= b -> b <= rname mb + Z.of_nat (length nb) - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) ((a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)
          ((b / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8 + 8 - (a / 8 + lib.B.AsanRT.ASAN_K) / 8 * 8)) /\
     (forall x, rname mb <= x <= rname mb + Z.of_nat (length nb) - 1 ->
        lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc))) (x / 8 + lib.B.AsanRT.ASAN_K) 1)).
  { intros NM. destruct (Hnm NM) as (N1 & N2 & NG & NR).
    assert (N0 : 0 < Z.of_nat (length nb)) by (destruct N1 as ((Nl & _) & _); lia).
    pose proof (ce_ro_place lyc Sc W memc mdc _ _ HAR NR) as (nq0 & nqc & nsd & nap). unfold ASAN_CEIL in nqc.
    pose proof (ce_ro_read lyc Sc W memc mdc _ _ HAR NR N0) as (_ & NV).
    apply (ce_range_rngV W2 (ly_F lyc) (rname mb) (Z.of_nat (length nb)) FA F64 nq0 N0
             ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) nsd).
    - intros a Ha. split; [apply VW2; exact (ce_vis_of_garr8 W memc _ nb nq0 N2 NG a Ha) | exact (nap a Ha)].
    - intros s0 Hs0. apply VW2. exact (ce_hull_cover (w_H W) memc (rname mb) (Z.of_nat (length nb)) nq0
                                         ltac:(unfold lib.B.AsanRT.APPMEM_END; rlia) NV s0 Hs0). }
  assert (FPnN : tctrl_emit_as_nm row mb ->
     lib.B.Prog.RcAsanFP.fp_dj [(rname mb, rname mb + Z.of_nat (length nb))]
       (lib.B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] (ly_F lyc))).
  { intros NM. destruct (Hnm NM) as (N1 & _ & _ & NR).
    pose proof (ce_ro_place lyc Sc W memc mdc _ _ HAR NR) as (_ & _ & nsd & nap).
    unfold lib.B.Prog.RcAsanFP.fp_dj. constructor; [|constructor].
    apply Forall_forall. intros r Hr. cbn [fst snd].
    apply (ce_dj_fpw lyc Sc W memc mdc (rname mb) (Z.of_nat (length nb)) HAR ltac:(lia)); [|exact Hr].
    intros x Hx. destruct N1 as ((Nl & _) & _).
    split; [apply nap; rlia | rlia]. }
  (* aJ_on at m1 := normalize mem2 = alay_ret_on's Section memory m, so its transport conjunct is the identity *)
  assert (AJN : lib.B.Prog.ctrl_emit_asF.aJ_on (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 4)
                  (lib.B.MemNorm.normalize RS mem2) o f md d s n (ly_F lyc) row (lib.B.MemNorm.normalize RS mem2)).
  { split; [exact AC2|]. split; [exact (fun P H => H)|]. split; [exact AW2|]. split; [exact (proj1 (AON EE))|].
    split; [exact FP2 | exact TL2]. }
  (* alay_ret_on on normalize mem2 *)
  pose proof (lib.B.Prog.ctrl_emit_asF.alay_ret_on (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
    (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
    (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
    (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
    (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 15)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (lib.B.MemNorm.normalize RS mem2) o f md d s g n ns
    (ly_F lyc) row tb mb nb gb db sb (ce_junk mem2 o (tctrl_emit_as_len row n))
    (lib.B.ProgBridge.RNG_W (ce_H (w_H W2) (ly_F lyc)))
    lib.B.Prog.reac_braid_encode_ns0F.reac_braid_encode_ns0_F_holds
    Hn Hns Hg (STN (bv_unsigned (lib.Reusable.YK11.getr regs 2)) ltac:(lia) ltac:(lia)) Dsf Dsn Hf8 Hf24 Hrl Hc HA Hc2 Hml HnmN Ho Ho1492 HEoN Hdb Hsb Hns0
    WHM AfN AmdN (conj (ce_app_addr_mem _ Hd6) (ce_app_addr_mem _ Hd7)) (conj (ce_app_addr_mem _ Hs6) (ce_app_addr_mem _ Hs7))
    AnN AON FPnN FpWIN2 FpIMG2 FpROW2 (fun x Hx => FpSf12 x ltac:(rlia)) (fun a b Ha Hab Hb => FpSfK2 a b Ha Hab ltac:(rlia))
    (fun EE' => proj1 (OFP2 EE')) (fun EE' => proj2 (proj2 (OFP2 EE'))) (fun EE' => proj1 (proj2 (OFP2 EE')))
    (fun NM => proj1 (NFP2 NM)) (fun NM => proj1 (proj2 (NFP2 NM))) lib.B.Prog.ctrl_finishF.ctrl_finish_F_closed_on
    (lib.Reusable.YK11.getr regs2 1) (lib.Reusable.YK11.getr regs2 5) (lib.Reusable.YK11.getr regs2 6)
    (lib.Reusable.YK11.getr regs2 7) (lib.Reusable.YK11.getr regs2 10) (lib.Reusable.YK11.getr regs2 11)
    (lib.Reusable.YK11.getr regs2 12) (lib.Reusable.YK11.getr regs2 13) (lib.Reusable.YK11.getr regs2 14)
    (lib.Reusable.YK11.getr regs2 15) (lib.Reusable.YK11.getr regs2 16) (lib.Reusable.YK11.getr regs2 17)
    (lib.Reusable.YK11.getr regs2 28) (lib.Reusable.YK11.getr regs2 29) (lib.Reusable.YK11.getr regs2 30)
    (lib.Reusable.YK11.getr regs2 31) w0 (lib.B.MemNorm.normalize RS mem2)
    EE FR1 (STN (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128) ltac:(lia) ltac:(lia)) (fun x _ => eq_refl) (fun x H => H) MI2 AJN HRN AfN P1N P2N P3N LAYN
    P5N P6N) as HRUN.
  (* the return state's register map, as alay_ret_on's start state names it (callee-saved: aregs_preserved) *)
  assert (HXR : lib.Lib.Regs6ss.xregs_eqv
    (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs2 1)
       (Z_to_bv 64 (bv_unsigned (lib.Reusable.YK11.getr regs 2) + -128))
       (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs2 5)
       (lib.Reusable.YK11.getr regs2 6) (lib.Reusable.YK11.getr regs2 7) (Z_to_bv 64 o) (Z_to_bv 64 f)
       (lib.Reusable.YK11.getr regs2 10) (lib.Reusable.YK11.getr regs2 11) (lib.Reusable.YK11.getr regs2 12)
       (lib.Reusable.YK11.getr regs2 13) (lib.Reusable.YK11.getr regs2 14) (lib.Reusable.YK11.getr regs2 15)
       (lib.Reusable.YK11.getr regs2 16) (lib.Reusable.YK11.getr regs2 17)
       (lib.Lib.Mem.zxb (nth 1 row (Z_to_bv 8 0))) (lib.Lib.Mem.zxb (nth 0 row (Z_to_bv 8 0)))
       (Z_to_bv 64 n) (Z_to_bv 64 6) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s)
       (Z_to_bv 64 (em_len (ubat row 21) n)) (lib.Reusable.YK11.getr regs 15) (Z_to_bv 64 lib.B.AsanRT.ASAN_K)
       (lib.Reusable.YK11.getr regs2 28) (lib.Reusable.YK11.getr regs2 29) (lib.Reusable.YK11.getr regs2 30)
       (lib.Reusable.YK11.getr regs2 31)) regs2).
  { apply lib.Lib.Regs6ss.xregs_eqv_sym. apply lib.Lib.Regs6ss.mkR_eqv_of;
      match goal with
      | |- reg_get regs2 ?K = _ =>
          first [ reflexivity
                | (let z := eval cbv in (bv_unsigned K) in
                   transitivity (lib.Reusable.YK11.getr regs2 (Z_to_bv 5 z)); [reflexivity|];
                   rewrite (Hpres z ltac:(unfold acallee_saved; lia)); reflexivity) ]
      end. }
  change (SRr SEGS W2 (mkCfg (lib.Lib.MState.MS regs2 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x85730)
            lib.Reusable.YK11.fp_csr None mem2 (lib.Lib.PropExec.seg_rom RS)) md2)
          (tctrl_emit_as_post B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc k regs o md g n row tb mb nb gb db sb)).
  refine (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W2 _ regs2 _ _ _ _ _ _ md2 _ _ HXR).
  apply (ce_lift W2 _ _ _ _ mem2 md2 (ly_F lyc) _ _ ltac:(exact FGT) RO2 HRUN).
  intros st st0 md'' HQ Hrb Hhid Hmd''. apply SRr_ret.
  (* acall_kept from the call state to the return memory: refl, the cut stretch, the ctrl_lay_block call *)
  assert (K0 : acall_kept SEGS B lyc Sc W memc W memc (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
                 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 + 4640)
                 (tctrl_emit_as_out o (tctrl_emit_as_R row mb n)))
    by (apply ce_kept_refl; intros a Ha; apply Wpres; rlia).
  assert (K1 : acall_kept SEGS B lyc Sc W memc W mA (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
                 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 + 4640)
                 (tctrl_emit_as_out o (tctrl_emit_as_R row mb n))).
  { apply (ce_kept_step lyc Sc W W memc mdc memc mA (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) o
             (tctrl_emit_as_R row mb n) cid pos HAR ltac:(rlia) Hin Ho1 ltac:(rewrite HRR; rlia) K0).
    - intros a Ha Hw Ho'. rewrite HRR in Ho'.
      apply (ce_raw2 memc mA _ _ o _ MUA); rewrite (lib.Lib.MState.unsigned_lit a Ha); rlia.
    - intros a Ha. apply PWA. rlia. }
  assert (K2 : acall_kept SEGS B lyc Sc W memc W2 mem2 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640)
                 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640 + 4640)
                 (tctrl_emit_as_out o (tctrl_emit_as_R row mb n))).
  { apply (ce_kept_trans lyc Sc W W W2 memc mA mem2 _ _ _ _ _ (fun a => o + 18 <= a < o + 50) K1 Hkept);
      [rlia | rlia | | unfold ASAN_CEIL; rlia | rlia].
    intros a Ha. unfold tctrl_emit_as_out. rewrite HRR. rlia. }
  assert (ADB : lib.B.AsanRT.addressable mem2 (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4640) 4640).
  { apply (ce_stack_addr ly2 S2 W2 mem2 md2 _ 4640 HAR2); [rewrite El; rlia | lia | rewrite Eh; rlia |].
    intros a Ha. apply Aw. rlia. }
  exact (ce_finish STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs o f md d s g n row tb mb nb gb db sb
    cid pos ly2 S2 W2 mem2 md2 st st0 md'' HAR Hret Wlo Whi Hstk2 Hstk1' Hsp16 Hin Hcid Ho1 Ho2 Hdb Hsb Hml
    (fun K2' => proj1 (proj2 (Htm K2'))) (fun G0 => False_ind _ (G0 Hg0)) Hao Hc2
    (fun EE' => proj1 (proj2 (HEo EE'))) HJ2 Hle Hfrs Hbl EF K2 ADB HQ Hrb Hhid Hmd'').
Qed.

(* ---- the whole function: the entry as a footprint start state, stretch 1, then the E = false return or the cut,
   the ctrl_lay_block call and stretch 3 ---- *)
Lemma m_main : SRr SEGS W (cfg_at SEGS CTRL_EMIT_AS regs memc mdc)
  (tctrl_emit_as_post B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc k regs o md g n row tb mb nb gb db sb).
Proof using All.
  pose proof m_AR as HAR.
  pose proof m_win as (Wlo & Whi & WCS & WHM & WAE & W8 & WJ & Wpres).
  pose proof m_F as (FA & F64 & FGT & FC).
  pose proof (lib.B.ProgWorldCtlRt.ro_agree_of_AR B HTS OWNRO RLO RHI lyc Sc W memc mdc HAR
                (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _))) as RO.
  change (SRr SEGS W (mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x853c4)
            lib.Reusable.YK11.fp_csr None memc (lib.Lib.PropExec.seg_rom RS)) mdc)
          (tctrl_emit_as_post B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc k regs o md g n row tb mb nb gb db sb)).
  assert (HX0 : lib.Lib.Regs6ss.xregs_eqv
    (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2)
       (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 5)
       (lib.Reusable.YK11.getr regs 6) (lib.Reusable.YK11.getr regs 7) (lib.Reusable.YK11.getr regs 8)
       (lib.Reusable.YK11.getr regs 9) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 d)
       (Z_to_bv 64 s) (lib.Reusable.YK11.getr regs 15) (Z_to_bv 64 n) (Z_to_bv 64 g)
       (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
       (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
       (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
       (lib.Reusable.YK11.getr regs 27) (lib.Reusable.YK11.getr regs 28) (Z_to_bv 64 ns)
       (lib.Reusable.YK11.getr regs 30) (lib.Reusable.YK11.getr regs 31)) regs).
  { apply lib.Lib.Regs6ss.xregs_eqv_sym. apply lib.Lib.Regs6ss.mkR_eqv_of;
      first [ reflexivity | exact H10 | exact H11 | exact H12 | exact H13 | exact H14 | exact H16 | exact H17
            | exact H29 ]. }
  refine (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W _ regs _ _ _ _ _ _ mdc _ _ HX0).
  apply (ce_lift W _ _ _ _ memc mdc (ly_F lyc) _ _ ltac:(exact FGT) RO m_s1_run).
  intros st st0 md' HQ Hrb Hhid Hmd.
  destruct HQ as [HQ | (EE & CUT)].
  - (* the run returned at once (E = false, or the whole path ended): the post at the call memory *)
    apply SRr_ret.
    assert (HJ0 : ajournal SEGS B STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc (k + 0))
      by (rewrite Z.add_0_r; exact HJ).
    pose proof Hhome as (cid & pos & Hin & Hcid & Ho1 & Ho2).
    assert (K0 : acall_kept SEGS B lyc Sc W memc W memc (spZ regs - 4640) (spZ regs - 4640 + 4640)
                   (tctrl_emit_as_out o (tctrl_emit_as_R row mb n)))
      by (apply ce_kept_refl; intros a Ha; apply Wpres; unfold spZ in *; rlia).
    assert (ADB : lib.B.AsanRT.addressable memc (spZ regs - 4640) 4640).
    { apply (ce_stack_addr lyc Sc W memc mdc _ 4640 HAR); [exact Wlo | lia | unfold spZ in *; rlia |].
      intros a Ha. apply (ce_win_app lyc Sc W memc mdc a HAR). unfold spZ in *. rlia. }
    exact (ce_finish STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs o f md d s g n row tb mb nb gb db sb
      cid pos lyc Sc W memc mdc st st0 md' HAR Hret Wlo Whi Hstk2 Hstk1 Hsp16 Hin Hcid Ho1 Ho2 Hdb Hsb Hml
      (fun K2' => proj1 (proj2 (Htm K2'))) (fun G0 => False_ind _ (G0 Hg0)) Hao Hc2
      (fun EE' => proj1 (proj2 (HEo EE'))) HJ0 (wle_refl SEGS W) eq_refl eq_refl eq_refl K0 ADB HQ Hrb Hhid Hmd).
  - (* the cut at the ctrl_lay_block call *)
    destruct CUT as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & w0 & mc & E0 & FR & ST & MU & WM &
                     MIc & AJc & P1 & P2 & PH & HW & P18).
    subst st0. destruct Hrb as (Hrel & Hro & Hmrd & Hby & Hwr & Hmu & Hwmo).
    destruct (lib.B.MemNormTr.ms_rel_MS st _ _ _ _ _ _ _ Hrel) as (Est & _).
    apply (SRr_bind SEGS W (mkCfg st md') (m_lay_post (m_R u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6) (ms_mem st))).
    + exact (m_cut_lay st md' u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 mc EE Est Hmrd (Hmu _ MU) (Hwmo WM) P18 Hmd).
    + intros W2 c2 Hle LP.
      exact (m_ret (ms_mem st) mc u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 w0 W2 c2 EE Hmrd Hby Hwr (Hmu _ MU) FR ST
               P1 P2 PH HW P18 Hle LP).
Qed.
End main.

(* ================================================================================================================
   The theorem.
   ================================================================================================================ *)
Theorem pb_ctrl_emit_as : tctrl_emit_as_spec RLO RHI B GLOBS.
Proof.
  unfold tctrl_emit_as_spec. cbv zeta.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o f md d s n ns row tb mb nb db sb
    HJ HRO Hret Hra Hgp Htp H10 H11 H12 H13 H14 H16 H17 H29 Hn Hns Hsp16 Hstk1 Hstk2 Hcnt1 Hcnt0
    Hf0 Hf8 Hf24 Hrl HfG HfR Hk Hc HL HGG HA Hao Hc2 HLA Hns0 Htm Hmd0 Hmd8 Hmd296 Hml HmG HmR Hnm
    Hdb HdG HdA HdV HdP HdH Hd6 Hd7 Hsb HsG HsA HsV HsP HsH Hs6 Hs7 Ho Ho1492 Hhome HEo
    Dsf Dsm Dsd Dss Dst Dsn HEd.
  exact (m_main STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o f md d s 0 n ns row tb mb nb [] db sb
    HJ HRO Hret Hra Hgp Htp H10 H11 H12 H13 H14 H16 H17 H29 Hn Hns ltac:(lia) Hsp16 Hstk1 Hstk2 Hcnt1 Hcnt0
    Hf0 Hf8 Hf24 Hrl HfG HfR Hk Hc HL HGG HA Hao Hc2 HLA Hns0 Htm Hmd0 Hmd8 Hmd296 Hml HmG HmR Hnm eq_refl
    Hdb HdG HdA HdV HdP HdH Hd6 Hd7 Hsb HsG HsA HsV HsP HsH Hs6 Hs7 Ho Ho1492 Hhome HEo
    Dsf Dsm Dsd Dss Dst Dsn HEd).
Qed.
End g2.
