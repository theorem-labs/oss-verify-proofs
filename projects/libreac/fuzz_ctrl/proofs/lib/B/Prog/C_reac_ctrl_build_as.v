(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane). *)
(* fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): reac_ctrl_build_as (0x8528c), the cgif caller-journal contract
   `treac_ctrl_build_as_spec` and its proof `pb_reac_ctrl_build_as`.
   reac_ctrl_build_as writes its own 80-byte frame, calls reac_box_model_upstream_width (a leaf; inside the lifted
   stretch on its proved _F), and TAIL-JUMPS to ctrl_emit_as (0x85388 -> 0x853c4) with a0 = o passed through, so it
   hands its caller's write right on [o, o + len) on: cgif's caller-journal form (cgif lib/YC20.v:311-365 of
   c8557374ad2e). Draft of record: reac_ctrl_build_as-B-draft.md (a working note, not in this delivery),
   section 2.1, under a Theorem Labs lane's decisions (decisions.md (a working note, not in this delivery)). Deltas from the draft text, each forced:
   - the premises on d, s, md, the name and the output carry what ctrl_emit_as's spec of record takes for the same
     ranges (a working branch 270764f2f38 C_ctrl_emit_as.v: shadow_hull_vis, in_app +
     tctrl_emit_as_home for d and s; tctrl_emit_as_ro, the registered read-only global over GLOBS, for md and the
     name (a Theorem Labs lane 08:37Z); the output frame of class 2 or more; decision 129's frame-home premise on o, passed
     on under o <> 0, decision 136 (decisions.md (a working note, not in this delivery))), since the call hands them on at the tail jump;
   - no meter premises (ctrl_emit_as's spec takes none; build_as makes no allocator call);
   - the journal's sink head is a Context (a Theorem Labs lane's request); the composer takes SK := Reusable.YE2k.tfib_sink_head;
   - the read-only span is Section variables RLO RHI with decision 17's RELRO_IMG (decisions.md (a working note, not in this delivery); order RLO RHI B GLOBS);
     the B top takes RLO := 0x9f1a0, RHI := 0xa15e8.
   The switch table (0x21980, .rodata) and the CTRL_FRAMES rows 3..9 (0xa0648..0xa06f0, RELRO) are not premises
   (decision 10): their zero shadow, their non-ownership and the rows' read-only-global form are CHECKED by
   computation over image B's bundle tables (CtrlTSyms: ts_zsh / ts_owned / ts_errno), C_reac_ctrl_build_asLib.bl_ts_zs_sw
   / bl_ts_rows_ro / bl_fr_ro, given the composer's In (0xa0600, 264) GLOBS and RLO <= 0xa0600 /\ 0xa0708 <= RHI.
   The glue (no re-walk): the stretch [entry, tail jump | ret 0] of ctrl's own footprint run is lifted through the
   kit bridge (YA0nR.SRr_fevt), cut at the tail jump, where ctrl_emit_as's cgif spec applies (its run holds the
   fake-stack calls of ctrl_lay_block / reac_box_model_block).
   Glue closure rule (two Theorem Labs lanes 23:38Z): the _F files and their closure are Required QUALIFIED, never
   Imported; no frame-route identifier in the spec, the theorem or a Section hypothesis. The modules that exist both
   in lib/Reusable and lib/{A,B}/Reusable are named qualified (a Theorem Labs lane 04:03Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK0s YI00 YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YE2k YF0m APostBase.
(* ctrl's address-free model files (qualified; glue closure rule) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcPorts RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c reac_ctrl_build_as RcPortsLib.
(* the glue's proof-internal library (named statements of the Section hypotheses; Qed lemmas) and the kit bridge *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_build_asLib CtrlRo.
(* a Theorem Labs lane's ProgWorld statements, image B's real file (ajournal_of_fsteps, arodata_okP_of_S), and a Theorem Labs lane's VIS-free
   ctl_rt_C_of_AR (lib/B/ProgWorldCtlRtC.v ca0e3717187 (the blob this tree had at release c5e779efe8c) = a working branch db8a86df2da): the
   runtime cells and the read-only bytes from AR with no AR_states_vis0_shadow *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgBridge ProgWorld ProgWorldCtlRtC.
(* a Theorem Labs lane's discharge of the image shadow cover (ACtlCutC.v (at head lib/B/ACtlCutC.v:273; from a working branch d2c835124b3)) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlCutC.
(* the lifted stretch and its in-stretch leaf callee, image B's own _F runs in their route (C) _on form (a Theorem Labs lane:
   a working branch 26e8a9dd8b0 reac_ctrl_build_asF.v, a working branch f44cd47cb9a
   reac_box_model_upstream_widthF.v; Required qualified, glue brief :89 (1) (a working note, not in this delivery)) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_asF reac_box_model_upstream_widthF.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation getr := lib.Reusable.YK11.getr.
#[local] Notation mkst := lib.Reusable.YK11.mkst.
#[local] Notation seg_rom := lib.Reusable.YK11.seg_rom.
#[local] Notation garr8 := lib.Reusable.YI00.garr8.
(* names whose families exist as a core copy and an image-B copy in this file's closure (ctrlgate DUP), pinned to the
   constant `About` names in this file's context (measured 07:0xZ): the core's YG0d / YG01 / YG00 *)
#[local] Notation spZ := lib.Reusable.YG0d.spZ.
#[local] Notation frames := lib.Reusable.YG01.frames.
#[local] Notation astate := lib.Reusable.YG00.astate.

(* The entry: REAC_CTRL_BUILD_AS = 0x8528c (lib/B/Prog/reac_ctrl_build_as_c.v:14; decision 3; A twin 0x848ac). *)
Definition A_reac_ctrl_build_asP : Z := 0x8528c.

(* ---------------------------------------------------------------------------------------------------------
   STAND-IN for ctrl_emit_as's cgif spec, a Theorem Labs lane: lib/B/Prog/C_ctrl_emit_as.v,
   from a working branch 00f1b4fabb9, its lines (at head lib/B/Prog/C_ctrl_emit_as.v:59-222) word for word outside comments (GLOBS and the
   read-only-global premise tctrl_emit_as_ro, g fixed to 0, the sink head a Context, RLO RHI B GLOBS).  That file Imports lib.Prog's
   model files and the core's YI00; the local abbreviations below resolve the same names to the same constants
   without importing anything.  When C_ctrl_emit_as.v lands, this module is deleted and that file Required. *)
Module EmitB.
#[local] Notation em_E := RcEmit.em_E.
#[local] Notation em_hid := RcEmit.em_hid.
#[local] Notation em_len := RcEmit.em_len.
#[local] Notation em_fr := RcEmit.em_fr.
#[local] Notation em_wok := RcEmit.em_wok.
#[local] Notation ubat := RcFin.ubat.
#[local] Notation fin := RcFin.fin.
#[local] Notation closes := RcFin.closes.
#[local] Notation ly_lay := RcLay.ly_lay.
#[local] Notation ly_k := RcLay.ly_k.
#[local] Notation ly_Z := RcLay.ly_Z.
#[local] Notation ly_bb := RcLay.ly_bb.
#[local] Notation ly_ao := RcLay.ly_ao.
#[local] Notation ly_al := RcLay.ly_al.
#[local] Notation ly_tm := RcLay.ly_tm.
#[local] Notation ly_dj := RcLay.ly_dj.
#[local] Notation has := RcSynth.has.
#[local] Notation rname := RcSynth.rname.
#[local] Notation name_ok := RcBox.name_ok.
(* --- verbatim outside comments from here (C_ctrl_emit_as.v (at head lib/B/Prog/C_ctrl_emit_as.v:59-222; from a working branch 00f1b4fabb9)) --- *)
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
(* --- end verbatim --- *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
End EmitB.
Import EmitB.
(* ---------------------------------------------------------------- end of the ctrl_emit_as stand-in ---- *)

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
(* the journal's sink head is generic (a Theorem Labs lane's request, 08:2xZ); the composer states the theorem at
   SK := lib.Reusable.YE2k.tfib_sink_head *)
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
(* the read-only span the caller's journal keeps (arodata_okS), as Section variables (decision 17, decisions.md (a working note, not in this delivery); TREPLY / PARSE /
   ctrl_lay_block / ctrl_emit_as alike; a Theorem Labs lane: order RLO RHI B GLOBS).  The B top instantiates
   RLO := 0x9f1a0, RHI := 0xa15e8 (a Theorem Labs lane's one form for image B). *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
(* The stack: own frame 80 and reac_box_model_upstream_width's 16 below it; after the tail jump ctrl_emit_as runs at
   the ENTRY sp, so the call needs exactly ctrl_emit_as's stack (= the _F window REAC_CTRL_BUILD_AS_K = 4640). *)
Definition REAC_CTRL_BUILD_AS_STK : Z := CTRL_EMIT_AS_STK.
(* no allocator event of its own *)
Definition EV_REAC_CTRL_BUILD_AS : Z := 0.

Section e2.
Variable B : asyms.
(* the registered globals of the image: the same GLOBS as ctrl_emit_as's, ctrl_lay_block's and reac_box_model_block's *)
Variable GLOBS : list (Z * Z).

Definition treac_ctrl_build_as_n (md : Z) (mb : list byte) : Z := RcPorts.bm_uw md (firstn 8 (skipn 16 mb)).
Definition treac_ctrl_build_as_len (md : Z) (mb : list byte) : Z := 52 + 36 * treac_ctrl_build_as_n md mb.
Definition treac_ctrl_build_as_ok (o md b : Z) (mb : list byte) : bool :=
  Prog.reac_ctrl_build_as_c.ba_go o md b && Prog.reac_ctrl_build_as_c.ba_E (treac_ctrl_build_as_n md mb) mb b.
Definition treac_ctrl_build_as_R (o md b : Z) (mb : list byte) : Z :=
  if treac_ctrl_build_as_ok o md b mb then treac_ctrl_build_as_len md mb else 0.
Definition treac_ctrl_build_as_nm (b : Z) (mb : list byte) : Prop :=
  (b = 5 \/ b = 6) /\ RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0.
Definition treac_ctrl_build_as_out (o R a : Z) : Prop := o <= a < o + R.

Definition treac_ctrl_build_as_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o md b : Z) (mb nb db sb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_REAC_CTRL_BUILD_AS) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 = w64 (treac_ctrl_build_as_R o md b mb) /\
    (treac_ctrl_build_as_ok o md b mb = true ->
       garr8 SEGS (mrestrict (w_H W2) mem2) o
         (map (fun x : byte => bv_unsigned x)
            (RcEmit.em_fr db sb (bv_unsigned (getr regs 15) mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234)
               (Prog.reac_ctrl_build_as_c.ba_X md mb nb b) (treac_ctrl_build_as_len md mb))) /\
       RcEmit.em_wok (treac_ctrl_build_as_n md mb) = true /\
       (b <= 1 -> RcModel.blocksum (Prog.reac_ctrl_build_as_c.ba_X md mb nb b) = 0) /\
       (RcModel.blocksum (RcLay.ly_Z md mb nb b) = 0 ->
          Prog.reac_ctrl_build_as_c.ba_X md mb nb b = RcLay.ly_Z md mb nb b)) /\
    acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - REAC_CTRL_BUILD_AS_STK) (spZ regs)
      (treac_ctrl_build_as_out o (treac_ctrl_build_as_R o md b mb)).

Definition treac_ctrl_build_as_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (o md b d s ns : Z) (mb nb db sb : list byte),
  let ok := treac_ctrl_build_as_ok o md b mb in
  let len := treac_ctrl_build_as_len md mb in
  let nm := treac_ctrl_build_as_nm b mb in
  let Lo := spZ regs - REAC_CTRL_BUILD_AS_STK in
  let rd := aview SEGS (w_H W) memc in
  let mr := mrestrict (w_H W) memc in
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI rd ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  (* a0 = o, a1 = md, a2 = b (the block kind), a3 = d, a4 = s, a7 = ns; a5 = the 16-bit header word (read in
     the post); a6 is passed on unread (as t3) *)
  getr regs 10 = w64 o -> getr regs 11 = w64 md -> getr regs 12 = w64 b -> getr regs 13 = w64 d ->
  getr regs 14 = w64 s -> getr regs 17 = w64 ns ->
  0 <= o < 2^64 -> 0 <= md < 2^64 -> 0 <= b < 2^64 -> -2^31 <= ns <= 0 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_BUILD_AS_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  (* the two 6-byte headers ctrl_emit_as copies *)
  length db = 6%nat -> garr8 SEGS mr d (map (fun x : byte => bv_unsigned x) db) ->
  range_addressable rd SHADOW_OFF d 6 -> shadow_hull_vis rd d 6 -> in_app d 6 -> tctrl_emit_as_home lyc Sc d 6 ->
  app_addr (d + 6) -> app_addr (d + 7) -> RcLay.ly_dj Lo (spZ regs) d (d + 6) ->
  length sb = 6%nat -> garr8 SEGS mr s (map (fun x : byte => bv_unsigned x) sb) ->
  range_addressable rd SHADOW_OFF s 6 -> shadow_hull_vis rd s 6 -> in_app s 6 -> tctrl_emit_as_home lyc Sc s 6 ->
  app_addr (s + 6) -> app_addr (s + 7) -> RcLay.ly_dj Lo (spZ regs) s (s + 6) ->
  (* the model record (read here for the width and by ctrl_emit_as): a registered read-only image global (a
     BOX_CATALOGUE row at ctrl's call), ctrl_emit_as's tctrl_emit_as_ro *)
  (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\
     garr8 SEGS mr md (map (fun x : byte => bv_unsigned x) mb) /\ tctrl_emit_as_ro RLO RHI B GLOBS md 296 /\
     RcLay.ly_dj Lo (spZ regs) md (md + 296)) ->
  (* the name of an identity block (b = 5, 6): a registered read-only image global (a .rodata string at ctrl's call) *)
  (md <> 0 -> nm ->
     RcBox.name_ok nb /\ RcSynth.rname mb + Z.of_nat (length nb) <= 2 ^ 64 /\
     garr8 SEGS mr (RcSynth.rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
     tctrl_emit_as_ro RLO RHI B GLOBS (RcSynth.rname mb) (Z.of_nat (length nb)) /\
     RcLay.ly_dj Lo (spZ regs) (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb))) ->
  (o <> 0 -> o + 1492 <= 2^64) ->
  (* o's 1492 bytes lie in a live caller frame of class 2 or more (ctrl_emit_as's frame-home premise, decision 129,
     A's form for p := o; build_as takes no side-stack frame of its own, so Sc at the tail jump is Sc here) *)
  (o <> 0 -> exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= o /\
                             o + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (* the caller's output, written when the call goes on: one caller frame of class 2 or more *)
  (ok = true ->
     (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\
        forall a, o <= a < o + len -> in_zr a (frame_rng lyc (cid, pos))) /\
     (forall a, o <= a < o + len ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
     range_addressable rd SHADOW_OFF o len /\ shadow_hull_vis rd o len /\ app_addr (o + len) /\
     RcLay.ly_dj Lo (spZ regs) o (o + len) /\ RcLay.ly_dj o (o + len) md (md + 296) /\
     RcLay.ly_dj o (o + len) d (d + 6) /\ RcLay.ly_dj o (o + len) s (s + 6) /\
     (nm -> RcLay.ly_dj o (o + len) (RcSynth.rname mb) (RcSynth.rname mb + Z.of_nat (length nb)))) ->
  SRr SEGS W (cfg_at SEGS A_reac_ctrl_build_asP regs memc mdc)
    (treac_ctrl_build_as_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o md b mb nb db sb).
End e2.

(* =========================================================================================================
   The proof: the stretch [entry, tail jump | ret 0] lifted (C_reac_ctrl_build_asLib.bl_stretch_on), the journal
   carried across it (ajournal_of_fsteps), ctrl_emit_as's cgif spec at the tail jump, and its post read back in
   reac_ctrl_build_as's terms.
   ========================================================================================================= *)
#[local] Notation BROW b := (Prog.reac_ctrl_build_as_c.ba_fr (Prog.reac_ctrl_build_as_c.ba_row b)).
#[local] Notation BA_GO := Prog.reac_ctrl_build_as_c.ba_go.

(* a registered read-only image global (ctrl_emit_as's tctrl_emit_as_ro) is addressable with a mapped shadow cover at
   every AR state (CtrlRo.ro_read_ok_glob over the composer's globs_marked / img_shadow_vis), inside the image *)
Lemma bl_ro_read : forall B GLOBS lyc Sc (W : world SEGS) m md q n,
  lib.B.Prog.CtrlRo.globs_marked SEGS B GLOBS -> lib.B.Prog.CtrlRo.img_shadow_vis SEGS B ->
  AR SEGS B lyc Sc W m md -> 0 < n -> tctrl_emit_as_ro RLO RHI B GLOBS q n ->
  0x10040 <= q /\ q + n + 64 <= 0x5fe000 /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF q n /\ shadow_hull_vis (aview SEGS (w_H W) m) q n.
Proof.
  intros B GLOBS lyc Sc W m md q n GM HV HAR Hn ((q0 & sz & Hin & H1 & H2) & H3 & H4 & _).
  destruct (lib.B.Prog.CtrlRo.ro_read_ok_glob SEGS B GLOBS lyc Sc W m md q0 sz q n GM Hin HV HAR H1 H2 Hn H3 H4)
    as [RA HH].
  unfold lib.B.Prog.CtrlRo.IMG_LO, lib.B.Prog.CtrlRo.IMG_HI in H3, H4.
  split; [lia|]. split; [lia|]. split; [exact RA | exact HH].
Qed.

Lemma bl_in_app_bound : forall a n, in_app a n -> 0 <= a /\ a + n <= 2 ^ 47.
Proof.
  intros a n [H0 H]. pose proof ASAN_CEIL_range as [CR _].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Section m.
Variable B : asyms.
(* the registered globals of the image (the composer's list, the same GLOBS as ctrl_emit_as's) *)
Variable GLOBS : list (Z * Z).
(* the core's laws of the bundle (frames_bounds, the zero-shadow and client-image laws); composer *)
Hypothesis LAWS : AR_laws SEGS B.
(* image B's bundle tables (Reusable/YF0m.v of 6e42f7692c3, a Theorem Labs lane's re-emitted set); composer, from B's asyms instance.
   ctl_rt_C_of_AR takes it; it also discharges decision 10's image facts by computation *)
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.
(* the one cut: ctrl_emit_as's cgif spec (a Theorem Labs lane, lib/B/Prog/C_ctrl_emit_as.v), at this file's sink head *)
Hypothesis EMIT : tctrl_emit_as_spec (SK := SK) RLO RHI B GLOBS.
(* the registered globals are marked usable (lib/B/Prog/CtrlRo.v:117, the start-up certificate); composer *)
Hypothesis GM : lib.B.Prog.CtrlRo.globs_marked SEGS B GLOBS.
(* CTRL_FRAMES (0xa0600, 264), the table whose rows 3..9 build_as hands to ctrl_emit_as, is a listed global; composer *)
Hypothesis GLOBS_FR : In (0xa0600, 264) GLOBS.
(* CTRL_FRAMES [0xa0600, 0xa0708) lies in the read-only span (a Theorem Labs lane; lia at the top with 0x9f1a0 / 0xa15e8) *)
Hypothesis FR_RELRO : RLO <= 0xa0600 /\ 0xa0708 <= RHI.

Theorem pb_reac_ctrl_build_as : treac_ctrl_build_as_spec B GLOBS.
Proof.
  unfold treac_ctrl_build_as_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o md b d s ns mb nb db sb.
  cbv zeta.
  intros HJ HRO Hra Hra4 Hgp Htp Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Ro Rmd Rb Rns HS16 HSTK HSP Hc1 Hc0
    Hdb HD RAd HVd IAd HOd APd6 APd7 DJd Hsb HSs RAs HVs IAs HOs APs6 APs7 DJs HM HN Ho1492 HoH HOK.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HASTK & _).
  pose proof HASTK as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof (lib.B.ProgWorld.ajournal_of_fsteps (SK := SK) B) as AJF.
  pose proof (lib.B.ACtlCutC.ctrl_img_shadow_vis B TS LAWS) as HIMGSH.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  assert (EK : REAC_CTRL_BUILD_AS_STK = 4640) by reflexivity.
  rewrite EK in HSTK, DJd, DJs, HM, HN, HOK.
  unfold spZ in HS16, HSTK, HSP, DJd, DJs, HM, HN, HOK.
  assert (RSP : lib.Reusable.YM05.alloc_ceiling + 4640 <= bv_unsigned (getr regs 2) <= 2 ^ 47) by lia.
  assert (W80 : sp0 - STK <= bv_unsigned (getr regs 2) - 80) by lia.
  assert (ACL : lib.Reusable.YM05.alloc_ceiling <= bv_unsigned (getr regs 2) - 4640) by lia.
  pose proof (C_reac_ctrl_build_asLib.bl_ts_zs_sw B TS) as HZS_SW.
  pose proof (C_reac_ctrl_build_asLib.bl_fr_ro B GLOBS RLO RHI TS GLOBS_FR (proj1 FR_RELRO) (proj2 FR_RELRO))
    as FR_RO.
  pose proof FR_RELRO as [FRL FRH].
  pose proof (C_reac_ctrl_build_asLib.bl_ts_rows_ro B TS) as ROWS_RO.
  destruct (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI lyc Sc W memc mdc HAR
              (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO
                 (Z.le_refl _) (Z.le_refl _)))
    as (HAC & _ & _ & Pro0).
  assert (Pro : lib.B.MemNorm.ro_agree lib.B.Img0.rsegs memc) by exact Pro0.
  pose proof (bl_in_app_bound d 6 IAd) as Bd. pose proof (bl_in_app_bound s 6 IAs) as Bs.
  assert (Rd : 0 <= d < 2 ^ 64) by lia.
  assert (Rs : 0 <= s < 2 ^ 64) by lia.
  apply (C_reac_ctrl_build_asLib.bl_stretch_on
           (lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_holds_on
              lib.B.Prog.reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds_on)
           W regs memc mdc o md b d s ns mb db sb _
           Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Ro Rmd Rb Rd Rs).
  - apply (C_reac_ctrl_build_asLib.bl_stk_of_present W); [lia | lia | intros a Ha; apply HPRES; lia].
  - lia.
  - exact Hdb.
  - exact Hsb.
  - intros H0. destruct (HM H0) as (M8 & M296 & ML & MG & MRO & MDJ).
    split; [exact M8|]. split; [exact M296|]. split; [exact ML|]. split; [|exact MDJ].
    exact (proj1 (C_reac_ctrl_build_asLib.bl_bytes_of_garr8 W memc md mb ltac:(lia) ltac:(rewrite ML; lia) MG)).
  - exact Pro.
  - exact HAC.
  - lia.
  - apply (C_reac_ctrl_build_asLib.bl_addr_img W memc); [lia | lia | lia |].
    exact (C_reac_ctrl_build_asLib.bl_zs_ra B LAWS lyc Sc W memc mdc _ _ HAR HZS_SW).
  - intros H0. destruct (HM H0) as (M8 & M296 & ML & MG & MRO & MDJ).
    destruct (bl_ro_read B GLOBS lyc Sc W memc mdc md 296 GM HIMGSH HAR ltac:(lia) MRO) as (MB1 & MB2 & MRA & MHV).
    exact (C_reac_ctrl_build_asLib.bl_addr_img W memc md 296 ltac:(lia) ltac:(lia) ltac:(lia) MRA).
  - exact (C_reac_ctrl_build_asLib.bl_imgsh_vis B W lyc Sc memc mdc HIMGSH HAR).
  - apply (C_reac_ctrl_build_asLib.bl_vis_present W memc); [lia | lia | intros a Ha; apply HPRES; lia].
  - intros H0. destruct (HM H0) as (M8 & M296 & ML & MG & MRO & MDJ).
    destruct (bl_ro_read B GLOBS lyc Sc W memc mdc md 296 GM HIMGSH HAR ltac:(lia) MRO) as (MB1 & MB2 & MRA & MHV).
    split.
    + pose proof (C_reac_ctrl_build_asLib.bl_vis_of_garr8 W memc md mb ltac:(lia) ltac:(rewrite ML; lia) MG) as V.
      rewrite ML in V. exact V.
    + replace (md + 295) with (md + 296 - 1) by lia.
      exact (C_reac_ctrl_build_asLib.bl_hull_vis W memc md 296 ltac:(lia) ltac:(lia) ltac:(lia) MHV).
  - intros ms' mdc' HP Hrun Hsame.
    unfold C_reac_ctrl_build_asLib.bl_post in HP. cbv zeta in HP.
    destruct HP as [[HG (t0' & t1' & t2' & t3' & t5' & t6' & mu & -> & MU & WM & ROmu & STmu)] |
                    [HG (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                         -> & MU & WM & ROm & STm)]].
    + (* the arguments pass the checks: the tail jump to ctrl_emit_as *)
      pose proof (AJF LAWS C_reac_ctrl_build_asLib.bl_wx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
                    (C_reac_ctrl_build_asLib.bl_ms0 regs 0x8528c memc) _ mdc mdc' k _ _ HJ Hrun
                    (ProgBridge.fp_avoids_RNG_W (w_H W)) MU Hsame
                    (C_reac_ctrl_build_asLib.bl_awr_window STK sp0 FP _ _ lyc own
                       (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2)) HSTK HSP))
        as HJ1.
      pose proof HJ1 as (HAR1 & _).
      destruct (C_reac_ctrl_build_asLib.bl_go o md b HG) as (Hon & Hmd & Hb6).
      assert (Hb6' : 0 <= b <= 6) by lia.
      destruct (C_reac_ctrl_build_asLib.bl_row_facts b Hb6')
        as (Hlen & Hk & Hr39 & Hbb & H20 & H21 & H22 & H23 & H18 & H19 & Hao & Hal & Hn0 & Hn1).
      destruct (HM Hmd) as (M8 & M296 & ML & MG & MRO & MDJ).
      destruct (bl_ro_read B GLOBS lyc Sc W memc mdc md 296 GM HIMGSH HAR ltac:(lia) MRO) as (MB1 & MB2 & _ & _).
      pose proof (RcPortsLib.bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
      pose proof (C_reac_ctrl_build_asLib.bl_arodata_munch B (w_H W) memc mu RLO RHI _ _ MU
                    ltac:(lia) RELRO_IMG HRO) as HROmu.
      (* ctrl_emit_as's row-level results are reac_ctrl_build_as's *)
      assert (EE : tctrl_emit_as_E (BROW b) mb (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) = true ->
                   treac_ctrl_build_as_ok o md b mb = true).
      { intros HEt. unfold treac_ctrl_build_as_ok, treac_ctrl_build_as_n. rewrite HG. cbn [andb].
        unfold tctrl_emit_as_E in HEt. rewrite reac_ctrl_build_as.ba_E_eq in HEt by exact Hb6'. exact HEt. }
      assert (EL : tctrl_emit_as_len (BROW b) (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) =
                   treac_ctrl_build_as_len md mb).
      { unfold tctrl_emit_as_len, treac_ctrl_build_as_len, treac_ctrl_build_as_n.
        apply reac_ctrl_build_as.ba_len_eq. exact Hb6'. }
      assert (ER : tctrl_emit_as_R (BROW b) mb (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) =
                   treac_ctrl_build_as_R o md b mb).
      { unfold tctrl_emit_as_R, tctrl_emit_as_E, tctrl_emit_as_len, treac_ctrl_build_as_R,
          treac_ctrl_build_as_ok, treac_ctrl_build_as_len, treac_ctrl_build_as_n.
        exact (C_reac_ctrl_build_asLib.bl_R o md b _ mb Hb6' HG). }
      assert (ENM : tctrl_emit_as_nm (BROW b) mb -> treac_ctrl_build_as_nm b mb).
      { intros ((_ & Hbb56) & Hhas & Hrn). rewrite Hk, Hbb in Hbb56. exact (conj Hbb56 (conj Hhas Hrn)). }
      pose proof (FR_RO b Hb6') as FRO. cbv zeta in FRO.
      assert (Ho0 : 0 < o) by lia.
      match goal with |- SRr _ _ (mkCfg ?ms1 _) _ => set (ms1' := ms1) end.
      assert (EC : mkCfg ms1' mdc' = cfg_at SEGS CTRL_EMIT_AS (ms_regs ms1') mu mdc') by reflexivity.
      rewrite EC.
      eapply SRr_mono.
      { pose proof (EMIT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mu mdc' k (ms_regs ms1') o
                      (0xa0600 + 24 * Prog.reac_ctrl_build_as_c.ba_row b) md d s
                      (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) ns (BROW b) [] mb nb db sb) as HE1.
        cbv zeta in HE1.
        apply HE1; clear HE1.
        - exact HJ1.
        - exact HROmu.
        - exact Hra.
        - exact Hra4.
        - exact Hgp.
        - exact Htp.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - lia.
        - lia.
        - exact HS16.
        - exact HSTK.
        - exact HSP.
        - exact Hc1.
        - exact Hc0.
        - lia.
        - replace (0xa0600 + 24 * Prog.reac_ctrl_build_as_c.ba_row b)
            with ((82112 + 3 * Prog.reac_ctrl_build_as_c.ba_row b) * 8) by lia.
          apply Z_mod_mult.
        - lia.
        - exact Hlen.
        - apply (C_reac_ctrl_build_asLib.bl_garr8_ro B (w_H W) mu RLO RHI); [exact HROmu|].
          intros j Hj. rewrite Hlen in Hj.
          destruct (ROWS_RO (0xa0600 + 24 * Prog.reac_ctrl_build_as_c.ba_row b + Z.of_nat j) ltac:(lia))
            as [RO1 RO2].
          split; [lia|]. split; [exact RO1|]. split; [exact RO2|].
          exact (C_reac_ctrl_build_asLib.bl_row_rom b Hb6' j Hj).
        - exact FRO.
        - rewrite Hk. lia.
        - rewrite H20. destruct (b <=? 1); lia.
        - lia.
        - lia.
        - lia.
        - rewrite Hao, Hal. lia.
        - intros Hc. rewrite H20 in Hc. destruct (b <=? 1); discriminate Hc.
        - intros Hc. lia.
        - intros _. lia.
        - intros Hc. rewrite Hk in Hc. lia.
        - exact Hmd.
        - exact M8.
        - exact M296.
        - exact ML.
        - apply (C_reac_ctrl_build_asLib.bl_garr8_munch _ _ memc mu (w_H W) md _ MU);
            [lia | rewrite length_map, ML; lia | rewrite length_map, ML; unfold RcLay.ly_dj in MDJ; lia | exact MG].
        - exact MRO.
        - intros Hnm. destruct (HN Hmd (ENM Hnm)) as (Nok & Nb & NG & NRO & NDJ).
          assert (NL : 0 < Z.of_nat (length nb)) by (destruct Nok as [[N1 _] _]; lia).
          destruct (bl_ro_read B GLOBS lyc Sc W memc mdc (RcSynth.rname mb) (Z.of_nat (length nb)) GM HIMGSH HAR NL NRO)
            as (NB1 & NB2 & _ & _).
          split; [exact Nok|]. split; [exact Nb|].
          split; [apply (C_reac_ctrl_build_asLib.bl_garr8_munch _ _ memc mu (w_H W) _ _ MU);
                  [lia | rewrite length_map; lia | rewrite length_map; unfold RcLay.ly_dj in NDJ; lia | exact NG]|].
          exact NRO.
        - exact Hdb.
        - apply (C_reac_ctrl_build_asLib.bl_garr8_munch _ _ memc mu (w_H W) d _ MU);
            [lia | rewrite length_map, Hdb; lia | rewrite length_map, Hdb; unfold RcLay.ly_dj in DJd; lia | exact HD].
        - exact (C_reac_ctrl_build_asLib.bl_ra_munch _ _ memc mu (w_H W) d 6 MU ltac:(lia) ltac:(lia)
                   ltac:(lia) RAd).
        - exact (C_reac_ctrl_build_asLib.bl_hull_munch _ _ memc mu (w_H W) d 6 MU ltac:(lia) ltac:(lia)
                   ltac:(lia) HVd).
        - exact IAd.
        - exact HOd.
        - exact APd6.
        - exact APd7.
        - exact Hsb.
        - apply (C_reac_ctrl_build_asLib.bl_garr8_munch _ _ memc mu (w_H W) s _ MU);
            [lia | rewrite length_map, Hsb; lia | rewrite length_map, Hsb; unfold RcLay.ly_dj in DJs; lia | exact HSs].
        - exact (C_reac_ctrl_build_asLib.bl_ra_munch _ _ memc mu (w_H W) s 6 MU ltac:(lia) ltac:(lia)
                   ltac:(lia) RAs).
        - exact (C_reac_ctrl_build_asLib.bl_hull_munch _ _ memc mu (w_H W) s 6 MU ltac:(lia) ltac:(lia)
                   ltac:(lia) HVs).
        - exact IAs.
        - exact HOs.
        - exact APs6.
        - exact APs7.
        - exact Ho0.
        - exact (Ho1492 Hon).
        - exact (HoH Hon).
        - intros HEt. rewrite EL.
          destruct (HOK (EE HEt)) as ((cid & pos & Hin & H2c & Hfr) & Haw & ORA & OHV & OAPP & _).
          pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
          assert (OB : forall a, o <= a < o + treac_ctrl_build_as_len md mb -> 0 <= a < lib.Reusable.YM05.alloc_ceiling).
          { intros a Ha. pose proof (Hfr a Ha) as Hz. unfold frame_rng, in_zr in Hz. cbn [fst snd] in Hz. lia. }
          assert (OL : 0 < treac_ctrl_build_as_len md mb)
            by (unfold treac_ctrl_build_as_len, treac_ctrl_build_as_n; lia).
          assert (OAB : 0 <= o /\ o + treac_ctrl_build_as_len md mb <= 2 ^ 47)
            by (unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in OAPP; lia).
          split; [exists cid, pos; split; [exact Hin | split; [exact H2c | exact Hfr]]|].
          split.
          { intros a Ha. destruct (Haw a Ha) as [Hw Hp]. split; [exact Hw|].
            pose proof (OB a Ha).
            exact (C_reac_ctrl_build_asLib.bl_apresent_munch _ _ memc mu (w_H W) a MU ltac:(lia) ltac:(lia) Hp). }
          split; [apply (C_reac_ctrl_build_asLib.bl_ra_munch _ _ memc mu (w_H W) _ _ MU);
                  [lia | lia | lia | exact ORA]|].
          split; [apply (C_reac_ctrl_build_asLib.bl_hull_munch _ _ memc mu (w_H W) _ _ MU);
                  [lia | lia | lia | exact OHV] | exact OAPP].
        - unfold RcLay.ly_dj, spZ, CTRL_EMIT_AS_STK. change (getr (ms_regs ms1') 2) with (getr regs 2).
          right. lia.
        - exact MDJ.
        - exact DJd.
        - exact DJs.
        - intros Hc. rewrite Hk in Hc. lia.
        - intros Hnm. destruct (HN Hmd (ENM Hnm)) as (_ & _ & _ & _ & NDJ). exact NDJ.
        - intros HEt. rewrite EL.
          destruct (HOK (EE HEt)) as ((cid & pos & Hin & _ & Hfr) & _ & _ & _ & _ & ODJ & ODJm & ODJd & ODJs & ODJn).
          split; [exact ODJ|].
          split; [apply (C_reac_ctrl_build_asLib.bl_dj_frame_img B lyc Sc W memc mdc cid pos _ _ _ 24 LAWS HAR Hin);
                  [unfold treac_ctrl_build_as_len, treac_ctrl_build_as_n; lia | lia | exact Hfr |
                   intros a Ha; exact (C_reac_ctrl_build_asLib.bl_in_img a ltac:(lia))]|].
          split; [exact ODJm|]. split; [exact ODJd|]. split; [exact ODJs|].
          split; [intros Hc; rewrite Hk in Hc; lia|].
          intros Hnm; exact (ODJn (ENM Hnm)). }
      (* ctrl_emit_as's post is reac_ctrl_build_as's *)
      intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & Hfrs2 & Hperm & Ha0' & HE & Hack).
      exists ly2, S2, regs2, mem2, md2.
      split; [exact Ec2|].
      split; [exact HJ2|].
      split; [exact (aregs_preserved_trans _ _ _
                       (C_reac_ctrl_build_asLib.bl_aregs regs t0' t1' t2' (Z_to_bv 64 o)
                          (Z_to_bv 64 (0xa0600 + 24 * Prog.reac_ctrl_build_as_c.ba_row b)) (Z_to_bv 64 md)
                          (Z_to_bv 64 d) (Z_to_bv 64 s) (getr regs 15)
                          (Z_to_bv 64 (RcPorts.bm_uw md (firstn 8 (skipn 16 mb)))) (Z_to_bv 64 0)
                          t3' (Z_to_bv 64 ns) t5' t6') Hpres)|].
      split; [exact Hfrs2|].
      split; [exact Hperm|].
      split; [rewrite <- ER; exact Ha0'|].
      split.
      { intros Hok.
        assert (HEt : tctrl_emit_as_E (BROW b) mb (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) = true).
        { unfold treac_ctrl_build_as_ok, treac_ctrl_build_as_n in Hok. rewrite HG in Hok. cbn [andb] in Hok.
          unfold tctrl_emit_as_E. rewrite reac_ctrl_build_as.ba_E_eq by exact Hb6'. exact Hok. }
        destruct (HE HEt) as (HG8 & HW & HCL).
        split; [|split; [exact (HW ltac:(lia)) | exact (C_reac_ctrl_build_asLib.bl_closes b md mb nb Hb6' HCL)]].
        rewrite EL in HG8.
        pose proof (C_reac_ctrl_build_asLib.bl_blk b md mb nb Hb6') as Hblk. cbv zeta in Hblk.
        unfold tctrl_emit_as_blk, tctrl_emit_as_lay in HG8. rewrite Hblk, Hn0, Hn1 in HG8. exact HG8. }
      rewrite ER in Hack.
      exact (C_reac_ctrl_build_asLib.bl_ack_comp B lyc Sc W W2 memc mdc mu mem2
               (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
               (bv_unsigned (getr regs 2) - 4640) (bv_unsigned (getr regs 2))
               (treac_ctrl_build_as_out o (treac_ctrl_build_as_R o md b mb)) LAWS HAR MU
               (Z.le_refl _) (Z.le_refl _) ACL Hack).
    + (* a refusal: the return of 0 *)
      pose proof (AJF LAWS C_reac_ctrl_build_asLib.bl_wx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
                    (C_reac_ctrl_build_asLib.bl_ms0 regs 0x8528c memc) _ mdc mdc' k _ _ HJ Hrun
                    (ProgBridge.fp_avoids_RNG_W (w_H W)) MU Hsame
                    (C_reac_ctrl_build_asLib.bl_awr_window STK sp0 FP _ _ lyc own
                       (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) W80 HSP))
        as HJ0.
      pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES0 & _).
      rewrite (C_reac_ctrl_build_asLib.bl_ret_pc _ Hra).
      match goal with |- SRr _ _ (mkCfg ?ms0 _) _ => set (ms0' := ms0) end.
      apply SRr_ret.
      exists lyc, Sc, (ms_regs ms0'), m', mdc'.
      split; [reflexivity|].
      split; [unfold EV_REAC_CTRL_BUILD_AS; rewrite Z.add_0_r; exact HJ0|].
      split; [exact (C_reac_ctrl_build_asLib.bl_aregs regs t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       t3' t4' t5' t6')|].
      split; [reflexivity|].
      split; [apply Permutation_refl|].
      split; [unfold treac_ctrl_build_as_R, treac_ctrl_build_as_ok; rewrite HG; reflexivity|].
      split; [intros Hok; exfalso; unfold treac_ctrl_build_as_ok in Hok; rewrite HG in Hok; discriminate Hok|].
      apply (C_reac_ctrl_build_asLib.bl_ack_munch B lyc Sc W memc mdc m' _ _ _ _ _ LAWS HAR MU);
        [rewrite EK; unfold spZ; lia | unfold spZ; lia | rewrite EK; unfold spZ; lia |].
      intros a Ha. apply HPRES0. rewrite EK in Ha. unfold spZ in Ha. lia.
Qed.
End m.
End b.
