(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module names, addresses and numbers changed; 1179 of its 1302 lines of code are new or changed and 3112 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F11.v, with its module names changed; 61 of its 242 lines of code are new or changed and 1121 lines of the source are left out. *)
(* lib/A/Prog/Seg/F11Fon.v -- route (C) twin of a Theorem Labs lane's Seg/F11F.v f11_014_evt_F, WITHOUT its `shadow_rw m`
   premise.  An ADDITIVE beside-file of the stage owner (a Theorem Labs lane, the Seg *F.v twin rule of
   a Theorem Labs lane 12:52Z as L3-brief.md (a working note, not in this delivery) states it); Seg/F11F.v stays byte-identical apart from comments.
   proves no function (kind: segment lemma).  rule 24: no function proved.

   WHY A TWIN.  The stage glue lib/A/ACtlG/F11_014.v lifts this footprint run (an ExecF.evtF over RNG) through
   Reusable.YA0nR.SRr_fevt_hid; the route (C) walk's cut carries A.ACtlRtC.ctl_rt_C (shadow_rw_on over the cut's regions), which
   cannot feed a universal `shadow_rw m`.  a Theorem Labs lane's f11_014_evt_on of Seg/F11.v (a version not in this delivery; from a working branch 947e598319e)
   is the same stretch with the premise dropped, but it is a plain Lib.Exec.evt under a
   Section hypothesis (HING_on), not a footprint run, so the lift cannot take it; this file is its footprint form.

   BASE.  The text of f11_014_evt_F at a Theorem Labs lane's fold a working branch 4bae33fdf54, Seg/F11F.v
   blob 2a9b50649ca (= the route (C) walk's blob, a working branch 1502cba0417 / 1899bed1aee, the same file), lines 302-526, with exactly these
   changes: the premise `shadow_rw m` and its intro name HSW removed, and the ingest call cut through the callee's
   narrowed footprint contract reac_identity_ingest_contract_F_on (premise dropped; a Theorem Labs lane 28e24b8fe6c, LANDED.md
   (a working note, not in this delivery) 10:09Z) and its proof reac_identity_ingestF.reac_identity_ingest_F_holds_on (a Theorem Labs lane 36bfd511da3, LANDED.md (a working note, not in this delivery)
   11:12Z, a Theorem Labs lane SIGNED) instead of reac_identity_ingest_F_holds.  REGION: none.  The run reads no shadow byte through
   shadow_rw (its two instrumented loads, the shadow bytes of phi + 36 / phi + 37, come from `addressable m phi 50` by
   sl_shadow1), stores no shadow byte, and the old proof passed HSW only to the ingest call.  The footprint (rng)
   premises are unchanged.
   NAMES.  F11F.v resolves its `Frame.outside` / `Frame.munch` / `Frame.wmono` (:321, :341-342, and the two run
   restatements :396-397, :471-472) to the twin copy lib.A.Tk.UL.Frame (glob of record).  This file writes those
   seven uses with that copy's FULL path, so each resolves to exactly F11F's constant and ctrlgate's DUP rule (two
   Frame copies in the closure) sees no partial name.  Every other constant resolves as in F11F (glob diff). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcParseLib RcFrag RcIdentModel
  RcAsanLib RcLib RcReply RcReplyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_identity_ingest_c.
(* The ingest callee's own proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_identity_ingestF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F11.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
Import ListNotations.
(* The base file, for its footprint helpers f11F_sh_rng / f11F_sh_rng'. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F11F.
(* Restore YK11's register reads (the names F11's statements are written over), as F11F.v does. *)
Import YK11.
Local Open Scope Z_scope.

Module INGon := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingestF.

(* ---- 0x820ac -> 0x820f8 under a footprint, through the ingest callee's narrowed footprint contract. ---- *)
Section RunFon.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

Lemma f11_014_evt_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi fr A lo len : Z) (G idb pb : list byte),
    length G = 50%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 -> len = ir_s G - 13 -> 14 <= ir_s G <= 23 ->
    bytes_at rsegs m phi G -> addressable m phi 50 ->
    0 <= A < 2 ^ 64 -> q64 m (A + 256) (fr + 256) -> q64 m (A + 144) (fr + 2688) ->
    bytes_at rsegs m (fr + 256) (reply_addr G) ->
    0 < fr -> fr + FRAME_BYTES <= 2 ^ 64 -> (fr + 2688) mod 2 = 0 ->
    rw_cells rsegs m (fr + 2688) [CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m (phi + 38) pb ->
    (phi + 38 + len <= fr + 2688 \/ fr + 2688 + 38 <= phi + 38) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (fr + 2688 + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= fr + 2688) ->
    (phi + 38 + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= phi + 38) ->
    asan_cells m ->
    addressable m (fr + 2688) 38 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) x) ->
    rng RNG phi 50 ->
    rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
    rng RNG (A + 256) 8 ->
    rng RNG (A + 144) 8 ->
    rng RNG (fr + 256) 2 ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (fr + 2688) 38 ->
    rng RNG ((fr + 2688) / 8 + ASAN_K) ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1) ->
    rng RNG (phi + 38) len ->
    rng RNG ((phi + 38) / 8 + ASAN_K) ((phi + 38 + len - 1) / 8 - (phi + 38) / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               a4i a5i a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i Fr fc m
    phi fr A lo len G idb pb HG Hphi0 Hphi50 Hlen Hs HB HA HAr Hq256 Hq144 Hra Hfr0 Hfrub Hid2 Hidrw Hpbl Hpb
    Hdj Hstk Hlo Hidw Hpw HAC HidA HOUT
    RBUF RSHA R256 R144 RRA RFR RGOT RCK RID RIS RP RPS.
  pose proof (cp_v_range' G 36) as R36. pose proof (cp_v_range' G 37) as R37.
  assert (Hlen0 : 1 <= len <= 10) by lia.
  (* the two checked bytes and their shadow bytes, out of the record buffer's two regions *)
  assert (Rb36 : rng RNG (phi + 36) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rb37 : rng RNG (phi + 37) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rs36 : rng RNG ((phi + 36) / 8 + ASAN_K) 1)
    by (apply (f11F_sh_rng' RNG phi (phi + 36) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs37 : rng RNG ((phi + 37) / 8 + ASAN_K) 1)
    by (apply (f11F_sh_rng' RNG phi (phi + 37) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs36' : rng RNG (Z.shiftr (phi + 36) 3 + ASAN_K) 1)
    by (apply (f11F_sh_rng RNG phi (phi + 36) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs37' : rng RNG (Z.shiftr (phi + 37) 3 + ASAN_K) 1)
    by (apply (f11F_sh_rng RNG phi (phi + 37) (phi + 49)); [lia | lia | exact RSHA]).
  (* the two instrumented checks: the bytes phi+36 and phi+37 lie in the addressable range [phi, phi+50) *)
  assert (Ha36 : addressable m (phi + 36) 1)
    by (apply (addressable_sub m phi 50 36 1 HA); lia).
  assert (Ha37 : addressable m (phi + 37) 1)
    by (apply (addressable_sub m phi 50 37 1 HA); lia).
  destruct (sl_shadow1 m (phi + 36) Ha36) as (sb1 & RD1 & OK1 & IS1).
  destruct (sl_shadow1 m (phi + 37) Ha37) as (sb2 & RD2 & OK2 & IS2).
  pose proof (rd_byte rsegs m phi G 36 HB ltac:(lia)) as RD36.
  pose proof (rd_byte rsegs m phi G 37 HB ltac:(lia)) as RD37.
  change (Z.of_nat 36) with 36 in RD36. change (Z.of_nat 37) with 37 in RD37.
  pose proof (f11_rd8 m (A + 256) _ Hq256 ltac:(apply length_le8)) as RD256.
  pose proof (f11_rd8 m (A + 144) _ Hq144 ltac:(apply length_le8)) as RD144.
  (* The reply cell in `le2` form, so the `lhu` at 0x820e8 does not make load_post's fold_lit_load vm_compute
     a symbolic byte list (the hang of the cons form [cp_b G 37; cp_b G 36]). *)
  assert (Hra2 : bytes_at rsegs m (fr + 256) (le2 (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)))).
  { unfold reply_addr in Hra. rewrite <- (rc_le2_pair (cp_b G 37) (cp_b G 36)) in Hra.
    change (bv_unsigned (cp_b G 36)) with (cp_v G 36) in Hra.
    change (bv_unsigned (cp_b G 37)) with (cp_v G 37) in Hra. exact Hra. }
  pose proof (f11_rd2 m (fr + 256) _ Hra2 ltac:(apply length_le2)) as RDa.
  (* the ingest call at 0x820f4, from the join at 0x820e0 *)
  assert (J48 : forall y6 : word,
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 37))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (zxb (nth 36 G (Z_to_bv 8 0))) (sxb sb2) y6 a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820e0) fc None m (seg_rom rsegs))).
  { intro y6.
    step. (* lbu a0,0(a0) : the byte phi+37 *)
    step. (* slli a4,a4,8 *)
    step. (* or a0,a4,a0 *)
    rewrite (rc_pack2 (nth 37 G (Z_to_bv 8 0)) (nth 36 G (Z_to_bv 8 0))).
    step. (* bne a0,a1,82bf4 : not taken *)
    change (bv_unsigned (nth 36 G (Z_to_bv 8 0))) with (cp_v G 36).
    change (bv_unsigned (nth 37 G (Z_to_bv 8 0))) with (cp_v G 37).
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    step. (* ld a0,144(s1) : the identity record fr+2688 *)
    step. (* jal reac_identity_ingest *)
    pose proof INGon.reac_identity_ingest_F_holds_on as HI.
    unfold reac_identity_ingest_contract_F_on, REAC_IDENTITY_INGEST in HI.
    eapply evtF_cut.
    { eapply (HI RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lo (fr + 2688)
                 (cp_v G 36 * 256 + cp_v G 37) (phi + 38) len idb pb).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - intros _. split; [exact Hid2 | exact Hidrw].
      - exact Hpbl.
      - intros _ _. exact Hpb.
      - intros _ _ _. lia.
      - exact Hstk.
      - unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _ _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - exact HAC.
      - intros _. exact HidA.
      - intros _ _. apply (addressable_sub m phi 50 38 len HA); lia.
      - exact HOUT.
      - exact RFR.
      - exact RGOT.
      - exact RCK.
      - intros _. split; [exact RID | exact RIS].
      - intros _ _. split; [exact RP | exact RPS]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI & ST & _ & HRW).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 532728)) with (Z_to_bv 64 532728)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (Href : ingest_refused (fr + 2688) (phi + 38) len = false).
    { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq (fr + 2688) 0) ltac:(lia)).
      rewrite (proj2 (Z.eqb_neq (phi + 38) 0) ltac:(lia)). rewrite andb_false_r. reflexivity. }
    unfold ingest_ret. rewrite Href.
    apply evtF_done.
    exists (Z_to_bv 64 532728), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    exact (HRW Href). }
  (* the join at 0x820c8: the check of phi+36 passed (its slow path 0x829b4 writes a5) *)
  assert (J30 : forall y5 : word,
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 36))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (sxb sb1) y5 a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820c8) fc None m (seg_rom rsegs))).
  { intro y5.
    step. (* addi a0,s6,19 : phi+37 *)
    step. (* srli a4,a0,3 *)
    rewrite (unsigned_lit (phi + 37)) by lia.
    step. (* add a4,a4,s10 *)
    step. (* lb a5,0(a4) : the shadow byte of phi+37 *)
    step. (* lbu a4,18(s6) : the byte phi+36 *)
    step. (* bnez a5,829c0 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb2)) by (pose proof (rc_byte_signed sb2); lia).
    destruct (Z.eqb_spec (bv_signed sb2) 0) as [Z2|Z2].
    - cbn [negb]. cbv iota. apply (J48 a6i).
    - cbn [negb]. cbv iota.
      step. (* andi a6,a0,7 *)
      rewrite (unsigned_lit (phi + 37)) by lia. rewrite rc_land7.
      step. (* bge a6,a5,82ccc *)
      unfold sxb. rewrite (rc_lts_signed ((phi + 37) mod 8) (bv_signed sb2))
        by (pose proof (rc_byte_signed sb2); pose proof (Z.mod_pos_bound (phi + 37) 8 ltac:(lia)); lia).
      replace ((phi + 37) mod 8 <? bv_signed sb2) with true
        by (symmetry; apply Z.ltb_lt; destruct OK2 as [H|H]; lia).
      cbn [negb]. cbv iota.
      step. (* j 820e0 *)
      apply (J48 (Z_to_bv 64 ((phi + 37) mod 8))). }
  (* 0x820ac-0x820c4: phi+36, its shadow byte, the u16 at pa = fr+256 and the branch *)
  step. (* addi a0,s6,18 : phi+36 *)
  step. (* srli a1,a0,3 *)
  rewrite (unsigned_lit (phi + 36)) by lia.
  step. (* add a1,a1,s10 *)
  step. (* lb a4,0(a1) : the shadow byte of phi+36 *)
  step. (* ld a1,256(s1) : pa = fr+256 *)
  step. (* lhu a1,0(a1) : the reply address (le2 form; load_post's zext_extract_le2 leaves zx16) *)
  rewrite (f11_zx16 (cp_v G 36 * 256 + cp_v G 37)) by (change (2 ^ 16) with 65536; lia).
  step. (* bnez a4,829b4 *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb1)) by (pose proof (rc_byte_signed sb1); lia).
  destruct (Z.eqb_spec (bv_signed sb1) 0) as [Z1|Z1].
  - cbn [negb]. cbv iota. apply (J30 a5i).
  - cbn [negb]. cbv iota.
    step. (* andi a5,a0,7 *)
    rewrite (unsigned_lit (phi + 36)) by lia. rewrite rc_land7.
    step. (* bge a5,a4,82cc8 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 36) mod 8) (bv_signed sb1))
      by (pose proof (rc_byte_signed sb1); pose proof (Z.mod_pos_bound (phi + 36) 8 ltac:(lia)); lia).
    replace ((phi + 36) mod 8 <? bv_signed sb1) with true
      by (symmetry; apply Z.ltb_lt; destruct OK1 as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 820c8 *)
    apply (J30 (Z_to_bv 64 ((phi + 36) mod 8))).
Qed.

End RunFon.
