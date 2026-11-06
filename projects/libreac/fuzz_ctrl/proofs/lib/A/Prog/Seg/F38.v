(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v, with its module names and numbers changed; 315 of its 421 lines of code are new or changed and 2983 lines of the source are left out. *)
(* Segment F38 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x82940-0x82960, the frame-loop LATCH
   (plan-asan section 2 row F38; no call, no store; ubsan twin C06).
   rule 24: no function proved.
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only
   in an ITERATION-ONLY build on the v1.9 bytes (FACTS 0bfe9aa0d452) with lib/A/Tk/AW/SmLeaf.v's walks admitted.
   It waits for lib/A/Tk/AW Sm* on v1.9 and for Seg/Tac_slot.v / Tac_fsfree.v re-fit to the regenerated Contract.v
   and FrameAPI.v.

   One entry (0x82940, after the free of F37) and two exits (0x81d40, the frame-loop head with the next turn
   index; 0x82b04, the epilogue):
     0x82940  li a0,254          -- a0 takes the turn bound 254.
     0x82944  bltu a0,s5,82b04   -- s5 is the turn counter j (LK: j <= 255).  The branch is taken exactly when
                                    j = 255 (254 <u j), and leaves the loop to the epilogue cut.
     0x82948  ld s6,216(s1)      -- the input cursor of the next turn is built from the spill [A + 216], which
                                    turn j's own block wrote at 0x81d1c (`sd s4,216(s1)`, s4 = p + body_j).
     0x8294c  add s6,s6,s2       -- s2 = len_j (FLSF), so s6 = p + body_j + len_j = p + c_(j+1).
     0x82950  ld a0,224(s1)      -- the spill [A + 224] holds left_j - h_j, written at 0x81d00
                                    (`sd s9,224(s1)`); it is FC's own conjunct of the turn's cuts.
     0x82954  sub s9,a0,s2       -- s9 = left_j - h_j - len_j = left_(j+1) = n - c_(j+1).
     0x82958  addiw s5,s5,1      -- the turn counter becomes j + 1 (j <= 254, so no 32-bit wrap).
     0x8295c  bnez s9,81d40      -- back edge to the loop head when the input is not exhausted.
     0x82960  j 82b04            -- otherwise the epilogue.
   The block 0x82964-0x82974 belongs to F36, not here.

   The segment writes no memory and changes only a0 (10), s5 (21), s6 (22) and s9 (25), so FRA moves with
   sl_fra_move and ENT with ent_mat, and every memory fact of the entry cut is handed on unchanged.

  Cuts: all official (SlotInv.v of a working branch e7f88fd06e7, push 14E; v1.9 names, pcs and bundles of
  a working branch 0a1d413d7c3); this file defines no cut.
  - Entry Inv_A82940_at: LK, FLSF (s2 = len_j for `add s6,s6,s2` / `sub s9,a0,s2`; its FLSI gives the spills
    [A + 216] / [A + 224] the latch loads, f1_IN, [A + 248] and FLC) and LT = IFS g fr (S j).
  - Back edge 0x8295c: Inv_A81d40_at at turn j + 1.  LK, CUR and 1 <= left come from the latch's sums; IFS of
    turn j + 1 is LT; FLSH (PRO and the loop part), f1_IN, [A + 248] and FLC are FLSI's, since the latch writes
    no memory (f38_run).
   - Epilogue 0x82944 (j = 255) / 0x82960 (input exhausted): Inv_A82b04.  X1 at 0x82b04 reads [A + 144]
     (`ld a1,144(s1)`) and the 17 identity bytes from fr + 2691: `spill regs m 144 (fr + 2688)` and
     `addressable m (fr + 2691) 17` are FLSH's (push 12A); the 21 identity bytes with a 0 in bytes 3 .. 19 are
     LT's IDj g fr (S j) (id_ok: byte 19 is 0) (f38_epi).
   The loop composition F00 is not proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch
  RcMatchLib RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module SFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.

(* ===================== model facts of turn j (as in Seg/F32.v) ===================== *)

Lemma f38_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f38_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f38_bz_range (nthb inp (Z.to_nat c))). pose proof (f38_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f38_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f38_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f38_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ 0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j.
Proof.
  intros inp j. pose proof (f38_fc_range inp j) as R. pose proof (f38_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body. unfold f_body, f_len, f_h, f_left in *. lia.
Qed.

(* The next turn's cursor: c_(j+1) = body_j + len_j (fc's own step). *)
Lemma f38_c_S : forall inp j, t_c inp (S j) = t_body inp j + t_len inp j.
Proof. reflexivity. Qed.

(* ===================== the identity record of turn j + 1 (the epilogue's third conjunct) ===================== *)

(* Every turn keeps the identity record at ID_SIZE = 38 bytes (ING keeps the length). *)
Lemma f38_tID_len : forall inp j, length (t_ID inp j) = RcIdentModel.ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - reflexivity.
  - cbn [fst_at]. unfold turn, rp_id, fg_id. cbv zeta.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fs_id];
      repeat apply RcIdentModel.ING_length; exact IH.
Qed.

(* A list with a byte c at index k has a first c. *)
Lemma f38_find_some : forall c (l : list byte) k d, (k < length l)%nat -> bv_unsigned (nth k l d) = c ->
  SFA.find_byte c l <> None.
Proof.
  intros c l. induction l as [|b l IH]; intros k d Hk Hb; [cbn in Hk; lia|].
  cbn [SFA.find_byte]. destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE]; [discriminate|].
  destruct k as [|k]; [exfalso; exact (NE Hb)|].
  pose proof (IH k d ltac:(cbn in Hk; lia) Hb) as IH'.
  destruct (SFA.find_byte c l) as [i|] eqn:F; [discriminate | congruence].
Qed.

(* X1's memchr window, bytes 3 .. 19 of the first 21: byte 19 is a 0. *)
Lemma f38_id_win : forall (l : list byte), (21 <= length l)%nat -> bv_unsigned (nth 19 l (Z_to_bv 8 0)) = 0 ->
  SFA.find_byte 0 (firstn 17 (skipn 3 (firstn 21 l))) <> None.
Proof.
  intros l H H19.
  do 21 (destruct l as [|? l]; [cbn in H; lia|]).
  apply (f38_find_some 0 _ 16 (Z_to_bv 8 0)); [cbn; lia | exact H19].
Qed.

(* ===================== bit-vector helpers ===================== *)

Lemma f38_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma f38_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A 32-bit add of two small values keeps its value (the `addiw` of the turn counter). *)
Lemma f38_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A branch arm the facts in context exclude. *)
Ltac f38_bad HC :=
  exfalso;
  first [ congruence
        | (zify_cond HC; rewrite ?MState.unsigned_lit in HC by lia; lia)
        | (rewrite ?f38_ltu_lit, ?f38_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ apply Bool.negb_true_iff in HC | apply Bool.negb_false_iff in HC | idtac ];
           first [ apply Z.ltb_lt in HC | apply Z.ltb_ge in HC
                 | apply Z.eqb_eq in HC | apply Z.eqb_neq in HC ];
           lia)
        | (vm_compute in HC; discriminate HC) ].

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A (F37's f37_rg_near). *)
Lemma f38_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  unfold rg in Ha, Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap, bv_modulus in Hb.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb.
  rewrite (Z.mod_small a) in Hb by lia. rewrite (Z.mod_small b) in Hb by lia. lia.
Qed.

(* ===================== the machine runs ===================== *)

(* j = 255: `li a0,254` then the unsigned compare 254 < j takes the branch to the epilogue. *)
Lemma f38_evt_x :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (jv : Z),
    x21 = Z_to_bv 64 jv -> 255 <= jv < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 254) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m jv -> Hj.
  step. step. if_cases HC; [apply evt_done; reflexivity | f38_bad HC].
Qed.

(* j <= 254 and the input is not exhausted (aa <> cc): the two spill loads, the two sums and the back edge. *)
Lemma f38_evt_b :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa <> cc ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x81d40) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A aa bb cc jv -> -> -> Hj HA0 HA1 R216 R224 Hbb Hcc Haa Hne.
  step. step. if_cases HC1; [f38_bad HC1|].
  rewrite ?(MState.unsigned_lit A) by lia. step.
  step.
  rewrite ?(MState.unsigned_lit A) by lia. step.
  step. step.
  rewrite ?MState.unsigned_lit by lia. rewrite ?f38_swrap by lia.
  step. if_cases HC2; [apply evt_done; reflexivity | f38_bad HC2].
Qed.

(* j <= 254 and the input is exhausted (aa = cc): the same loads, then the fall-through jump to the epilogue. *)
Lemma f38_evt_e :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa = cc ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A aa bb cc jv -> -> -> Hj HA0 HA1 R216 R224 Hbb Hcc Haa Heq.
  step. step. if_cases HC1; [f38_bad HC1|].
  rewrite ?(MState.unsigned_lit A) by lia. step.
  step.
  rewrite ?(MState.unsigned_lit A) by lia. step.
  step. step.
  rewrite ?MState.unsigned_lit by lia. rewrite ?f38_swrap by lia.
  step. if_cases HC2; [f38_bad HC2|].
  step. apply evt_done. reflexivity.
Qed.

Section F38.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The Lib-evt -> SR bridge (F37's f37_run_lib). *)
Lemma f38_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ===================== the epilogue exit ===================== *)

(* Inv_A82b04 from any register map that keeps the FRA registers, at the entry memory.  [A + 144] and the 17
   bytes at fr + 2691 are FLSH's; the identity bytes are LT's; the rest is FRA / ENT / LK. *)
Lemma f38_epi : forall j g regs mem md fr,
  Hcut B APIf ra (Inv_A82b04 B APIf ra) ->
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md ->
  g_n g < 2 ^ 26 -> LK g fr j regs mem -> FLSH g j fr regs mem -> LT g fr j regs mem ->
  forall regs' md', getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 ->
    getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
    getr regs' 19 = getr regs 19 -> getr regs' 26 = getr regs 26 -> AsanLift.mat_le md md' ->
    SR rsegs (mkCfg (mkst regs' (Z_to_bv 64 0x82b04) mem (seg_rom rsegs)) md') (Post B APIf ra g).
Proof.
  intros j g regs mem md fr Hexit HFRA HENT Hgn HLK HFLSH HLT regs' md' E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof HFLSH as (_ & _ & _ & H144 & H2691).
  pose proof FF as (SEGS & _).
  pose proof HLK as (_ & _ & HOUR).
  pose proof HLT as ((HID & HIDok) & _ & _).
  rewrite <- SEGS. apply Hexit. exists regs', mem, md', fr.
  split; [reflexivity|].
  split; [exact (sl_fra_move B APIf ra g fr [] regs regs' mem md md' HFRA E2 E3 E4 E8 E9 E19 E26 Hmat)|].
  split; [exact (ent_mat APIf g [] mem md md' HENT Hmat)|].
  split; [exact Hgn|]. split; [exact HOUR|].
  (* (1): [A + 144], the base register 9 is kept *)
  split.
  { destruct H144 as (A0 & HA0 & Hq). exists A0.
    split; [unfold rg in HA0 |- *; rewrite E9; exact HA0 | exact Hq]. }
  split; [|exact H2691].
  (* the identity record of turn j + 1 (LT's IDj): its first 21 bytes, byte 19 = 0 (id_ok) *)
  pose proof (f38_tID_len (g_in g) (S j)) as HL.
  destruct HIDok as (_ & _ & _ & H19 & _).
  exists (firstn 21 (t_ID (g_in g) (S j))).
  split; [|split].
  - unfold IDBe in HID. rewrite <- (List.firstn_skipn 21 (t_ID (g_in g) (S j))) in HID.
    apply LM.bytes_at_app in HID. exact (proj1 HID).
  - rewrite List.length_firstn, HL. reflexivity.
  - apply f38_id_win; [rewrite HL; unfold RcIdentModel.ID_SIZE; lia | exact H19].
Qed.

(* ===================== the segment ===================== *)

(* The whole segment from the official entry cut's facts, both exits: the back edge into the official
   Inv_A81d40_at (S j) is proved here in full; the epilogue exit is KX (f38_epi gives it). *)
Lemma f38_run : forall j g phi regs mem md fr,
  Hat B APIf ra (Inv_A81d40_at B APIf ra) (S j) ->
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md ->
  g_n g < 2 ^ 26 -> LK g fr j regs mem -> FLSF g j phi fr regs mem -> LT g fr j regs mem ->
  (forall regs' md', getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 ->
     getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 19 = getr regs 19 -> getr regs' 26 = getr regs 26 -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' (Z_to_bv 64 0x82b04) mem (seg_rom rsegs)) md') (Post B APIf ra g)) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x82940) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j g phi regs mem md fr Hback HFRA HENT Hgn HLK HFLSF HLT KX.
  pose proof FF as (SEGS & _).
  pose proof HFLSF as (HFLSI & H18 & H22 & H23 & H25 & Hrec & Hs152 & Hs280).
  pose proof HFLSI as (HFLSH & H216 & H224 & H248 & HIN & HFLC).
  pose proof HLK as (Hj255 & H21 & HOUR).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Hfrapp).
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv.
  assert (HA : 416 <= A /\ A + 416 <= 2 ^ 64) by lia.
  destruct HA as (HAlo & HAhi).
  (* the model's turn arithmetic *)
  pose proof (f38_t_facts (g_in g) j) as (Rc & EL & (Hh0 & Hh1) & (Hl0 & Hl1) & Eb).
  pose proof (f38_t_facts (g_in g) (S j)) as (Rc' & EL' & _).
  pose proof (f38_c_S (g_in g) j) as EcS.
  (* the harness block bounds (p + n is inside app memory) *)
  pose proof HIN as (Hin & Haddr & Hbytes).
  pose proof Haddr as (Hp0 & Hn0 & Hpn & _).
  assert (Hnn : nlen (g_in g) = g_n g) by reflexivity.
  (* the two spill loads, at the spill base A *)
  set (bb := g_p g + t_body (g_in g) j) in *.
  set (aa := t_left (g_in g) j - t_h (g_in g) j) in *.
  set (cc := flen g j) in *.
  assert (Ebb : bb = g_p g + t_body (g_in g) j) by reflexivity.
  assert (Eaa : aa = t_left (g_in g) j - t_h (g_in g) j) by reflexivity.
  assert (Ecc : cc = t_len (g_in g) j) by reflexivity.
  assert (Hbb : 0 <= bb < 2 ^ 64) by lia.
  assert (Haa : 0 <= aa < 2 ^ 64) by lia.
  assert (Hcc : 0 <= cc <= aa) by lia.
  assert (K216 : ro_cells rsegs mem (A + 216) [C8 (Z_to_bv 64 bb)]).
  { destruct H216 as (A0 & HA0 & Hq).
    assert (EA0 : A0 = A).
    { pose proof Hq as Hqb. unfold q64 in Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
      apply (f38_rg_near regs 9 A A0 Hr9 HA0); lia. }
    subst A0. apply ro_c8. exact Hq. }
  assert (K224 : ro_cells rsegs mem (A + 224) [C8 (Z_to_bv 64 aa)]).
  { destruct H224 as (A0 & HA0 & Hq).
    assert (EA0 : A0 = A).
    { pose proof Hq as Hqb. unfold q64 in Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
      apply (f38_rg_near regs 9 A A0 Hr9 HA0); lia. }
    subst A0. apply ro_c8. exact Hq. }
  destruct (Nat.le_gt_cases 255 j) as [Hx|Hx].
  - (* j = 255: the turn bound takes the branch to the epilogue *)
    assert (Ej : j = 255%nat) by lia.
    apply (f38_run_lib regs (Z_to_bv 64 0x82940) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82b04 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply (f38_evt_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  fp_regs fp_csr mem (Z.of_nat j));
          [ unfold rg in H21; exact H21 | lia ]. }
      { intros ms' E. eexists _, (Z_to_bv 64 0x82b04), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        do 6 (split; [reflexivity|]). reflexivity. }
    + intros R0 pc' mem1 regs1 md1 (Hpc & Hm1 & E2 & E3 & E4 & E8 & E9 & E19 & E26) Hreg Hmat.
      subst pc' mem1.
      apply KX; try (rewrite Hreg; assumption). exact Hmat.
  - (* j <= 254: the latch runs *)
    assert (Hjv : 0 <= Z.of_nat j <= 254) by lia.
    destruct (Z.eq_dec aa cc) as [Heq|Hne].
    + (* the input is exhausted: the loop ends *)
      apply (f38_run_lib regs (Z_to_bv 64 0x82940) mem md
        (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82b04 /\ mem' = mem /\
           getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
           getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
           getr R0 26 = getr regs 26)
        (Post B APIf ra g)).
      * exact Hhalt.
      * eapply LE.evt_mono.
        { unfold Regs6ss.mkR_of.
          eapply (f38_evt_e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    fp_regs fp_csr mem A aa bb cc (Z.of_nat j));
            [ unfold rg in Hr9; exact Hr9 | unfold rg in H18; exact H18 | unfold rg in H21; exact H21
            | lia | lia | lia | exact K216 | exact K224 | lia | lia | lia | exact Heq ]. }
        { intros ms' E. eexists _, (Z_to_bv 64 0x82b04), mem. split; [exact E|].
          split; [reflexivity|]. split; [reflexivity|].
          do 6 (split; [reflexivity|]). reflexivity. }
      * intros R0 pc' mem1 regs1 md1 (Hpc & Hm1 & E2 & E3 & E4 & E8 & E9 & E19 & E26) Hreg Hmat.
        subst pc' mem1.
        apply KX; try (rewrite Hreg; assumption). exact Hmat.
    + (* the back edge: the loop head with turn j + 1 *)
      apply (f38_run_lib regs (Z_to_bv 64 0x82940) mem md
        (fun R0 pc' mem' => pc' = Z_to_bv 64 0x81d40 /\ mem' = mem /\
           getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
           getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
           getr R0 26 = getr regs 26 /\
           getr R0 21 = Z_to_bv 64 (Z.of_nat j + 1) /\
           getr R0 22 = Z_to_bv 64 (bb + cc) /\ getr R0 25 = Z_to_bv 64 (aa - cc))
        (Post B APIf ra g)).
      * exact Hhalt.
      * eapply LE.evt_mono.
        { unfold Regs6ss.mkR_of.
          eapply (f38_evt_b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    fp_regs fp_csr mem A aa bb cc (Z.of_nat j));
            [ unfold rg in Hr9; exact Hr9 | unfold rg in H18; exact H18 | unfold rg in H21; exact H21
            | lia | lia | lia | exact K216 | exact K224 | lia | lia | lia | exact Hne ]. }
        { intros ms' E. eexists _, (Z_to_bv 64 0x81d40), mem. split; [exact E|].
          split; [reflexivity|]. split; [reflexivity|].
          do 9 (split; [reflexivity|]). reflexivity. }
      * intros R0 pc' mem1 regs1 md1
          (Hpc & Hm1 & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E21 & E22 & E25) Hreg Hmat.
        subst pc' mem1.
        assert (F2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact E2).
        assert (F3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact E3).
        assert (F4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact E4).
        assert (F8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact E8).
        assert (F9 : getr regs1 9 = getr regs 9) by (rewrite Hreg; exact E9).
        assert (F19 : getr regs1 19 = getr regs 19) by (rewrite Hreg; exact E19).
        assert (F26 : getr regs1 26 = getr regs 26) by (rewrite Hreg; exact E26).
        assert (F21 : getr regs1 21 = Z_to_bv 64 (Z.of_nat j + 1)) by (rewrite Hreg; exact E21).
        assert (F22 : getr regs1 22 = Z_to_bv 64 (bb + cc)) by (rewrite Hreg; exact E22).
        assert (F25 : getr regs1 25 = Z_to_bv 64 (aa - cc)) by (rewrite Hreg; exact E25).
        (* every spill of the entry cut is a spill of the new register map (only 10/21/22/25 changed) *)
        assert (KS : forall off v, spill regs mem off v -> spill regs1 mem off v).
        { intros off v (A0 & HA0 & Hq). exists A0. split; [unfold rg in *; rewrite F9; exact HA0 | exact Hq]. }
        rewrite <- SEGS. apply Hback. exists regs1, mem, md1, fr.
        split; [reflexivity|].
        split; [exact (sl_fra_move B APIf ra g fr [] regs regs1 mem md md1 HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)|].
        split; [exact (ent_mat APIf g [] mem md md1 HENT Hmat)|].
        split; [exact Hgn|].
        (* LI of turn j + 1 *)
        split.
        { split.
          { split; [lia|]. split; [|exact HOUR].
            unfold rg. rewrite F21. f_equal. lia. }
          split.
          { split; [lia|]. split.
            - unfold rg. rewrite F22. f_equal. lia.
            - unfold rg. rewrite F25. f_equal. lia. }
          split; [lia|].
          (* the frame records of turn j + 1: LT.  v1.9 FSb: [A + 104] / [A + 112] and the body bytes at
             fr + 2880 with their addressability, memory only *)
          destruct HLT as (HID & HFG & HFS).
          split; [exact HID|]. split; [exact HFG|].
          destruct HFS as (Q104 & Q112 & Qbody & Qad & HFI).
          split; [exact (KS 104 _ Q104)|]. split; [exact (KS 112 _ Q112)|].
          split; [exact Qbody|]. split; [exact Qad | exact HFI]. }
        (* FLSH (its body does not read the turn index): PRO, then the loop part.  v1.9 PRO: [A + 208] is the
           former [A + 200], and [A + 32] = fr + 2880 is the 16th conjunct, appended *)
        split.
        { destruct HFLSH as ((Q40 & Q120 & Q136 & Q160 & Q168 & Q176 & Q208 & Q248 & Qadr & Qbytes & Qin &
                              Q184 & Q256 & Q264 & Q272 & Q32) & Q128 & Qstk & Q144 & Q2691).
          split.
          { split; [exact (KS 40 _ Q40)|]. split; [exact (KS 120 _ Q120)|].
            split; [exact (KS 136 _ Q136)|]. split; [exact (KS 160 _ Q160)|].
            split; [exact (KS 168 _ Q168)|]. split; [exact (KS 176 _ Q176)|].
            split; [exact (KS 208 _ Q208)|]. split; [exact (KS 248 _ Q248)|].
            split; [exact Qadr|]. split; [exact Qbytes|]. split; [exact Qin|].
            split; [exact (KS 184 _ Q184)|]. split; [exact (KS 256 _ Q256)|].
            split; [exact (KS 264 _ Q264)|]. split; [exact (KS 272 _ Q272) | exact (KS 32 _ Q32)]. }
          split; [exact (KS 128 _ Q128)|]. split; [exact Qstk|].
          split; [exact (KS 144 _ Q144) | exact Q2691]. }
        (* the harness block and the [A + 248] spill (FLSI) *)
        split; [exact HIN|].
        split; [exact (KS 248 _ H248)|].
        (* FLC of turn j + 1: FLSI's, the latch writes no memory.  v1.9: slots renumbered, and [A + 56] = fr + 2889
           / [A + 48] = fr + 2890 appended as the 13th and 14th conjuncts *)
        destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Ca72 & Ca38 & C72 & C64 & C56 & C48).
        split; [exact (KS 256 _ C256)|]. split; [exact (KS 184 _ C184)|].
        split; [exact (KS 192 _ C192)|]. split; [exact (KS 80 _ C80)|].
        split; [exact (KS 88 _ C88)|]. split; [exact (KS 96 _ C96)|].
        split; [exact (KS 272 _ C272)|]. split; [exact (KS 264 _ C264)|].
        split; [exact Ca72|]. split; [exact Ca38|].
        split; [exact (KS 72 _ C72)|]. split; [exact (KS 64 _ C64)|].
        split; [exact (KS 56 _ C56) | exact (KS 48 _ C48)].
Qed.

(* Entry Inv_A82940_at j; exits Inv_A81d40_at (S j) (back edge) and Inv_A82b04 (epilogue). *)
Lemma seg_F38 : forall j : nat,
  Hat B APIf ra (Inv_A81d40_at B APIf ra) (S j) ->
  Hcut B APIf ra (Inv_A82b04 B APIf ra) ->
  Hat B APIf ra (Inv_A82940_at B APIf ra) j.
Proof.
  intros j Hback Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HLK & HFLSF & HLT).
  subst c.
  pose proof FF as (SEGS & _). rewrite SEGS.
  pose proof HFLSF as ((HFLSH & _) & _).
  apply (f38_run j g phi regs mem md fr Hback HFRA HENT Hgn HLK HFLSF HLT).
  exact (f38_epi j g regs mem md fr Hexit HFRA HENT Hgn HLK HFLSH HLT).
Qed.

End F38.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
