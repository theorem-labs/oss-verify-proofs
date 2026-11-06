(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 615 of its 727 lines of code are new or changed and 899 lines of the source are left out. *)
(* Segment F35 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): 0x82c24-0x82c34, the block compare of the
   row_of_block loop at row i (slot-plan-asan-ubsan section 2 row F35, call BCMP@0x82c34, twin W03). Image A's twin
   is 0x82888-0x82898 (no image-A lemma yet).

     0x82c24  beqz a0,82c5c     -- NOT taken: a0 = 1, the result of declaration_of (F34's exit cut).
     0x82c28  li a2,32          -- the compare length: the 32 declaration bytes.
     0x82c2c  ld a0,312(s1)     -- a0 = [A + 312] = Phi + 18, the block pointer (SlotInv's bundle PTL).
     0x82c30  mv a1,s6          -- a1 = s6 = fr + 64, the row slot that holds row i's declaration (SlotInv's RLc).
     0x82c34  jal wrapper_bcmp  -- return point 0x82c38 with a0 = memcmp_model (t_blk j) (decl_i i) 32, which is 0
                                   exactly when the block equals row i's declaration.

   Image A compares s6 (the block) with s9 (the slot); image B loads the block pointer from the spill [A + 312] and
   keeps the slot in s6. The range has no branch to 0x82fa0 or 0x82fa4 and no instrumented check of its own. The
   wrapper checks that the 32 bytes at Phi + 18 and the 32 bytes at fr + 64 are marked usable in the shadow map: the
   first range is inside the heap block [Phi, Phi + len) with len >= 50 (row kind 9, t_rowsel), the second is the row
   slot that F34 marked usable, so the error path is not reached (the lib/B contract bcmp_wrap_contract, a Section
   Hypothesis). The wrapper writes only its stack scratch [sp - 4560, sp); FRA moves across that write by
   f35_stk_run (the scratch is below sp, so apart from the spill area and the saved registers, and apart from the
   frame by SlotInv.fra_frame), then to the materialized model by Tac_slot.sl_fra_move.

   Entry SlotInv's Inv_B82c24_at (row i). Exits: SlotInv's Inv_B82c38_at (F36's entry at row i: the compare
   result, the checked row address s8, and the row-loop state RLc); SlotInv's Inv_B82bf4_at at row S i and
   Inv_B82ca0_at (F37's entry) are the form's other exits, which this range does not reach (a0 = 1, so the beqz to
   0x82c5c is not taken; v1.9.0's `li s6,1` at 0x82c6c is on that path only). The official cuts carry the block as
   (Phi, AC.a_size len); the row path has len >= 50 (kind 9, t_rowsel), so AC.a_size len = len and the proof works
   with hb1 Phi len. FTURN (the cursor spills [A + 224] / [A + 232] and the Phi bytes), the spill [A + 272] and the
   turn's frame records and local `first` IFS g fr (S j) pass through: the wrapper writes only [sp - 4560, sp),
   below A and the block and apart from the frame. (v1.9.0: the [A + 248] position of both cuts is `True`.) *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot F34.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* The short name YK11 could resolve to lib/Reusable/YK11.v, which the catalogue chain loads; this file's
   registers, mkst and FPState are image B's. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.

Local Definition BCMP_WRAP_K := 4560.
Local Definition BCMP := 0x98930.
Local Definition REAL_BCMP := 0xa2610.
Local Definition REAL_MEMCMP := 0xa2608.
Local Definition GOT_CF := 0xa08e0.
Local Definition CF := 0x13b1e8.
Local Definition MEMCMP := 0x98a00.
Local Notation memcmp_model := SF.memcmp_model.

(* ========================= model helpers ========================= *)

Lemma f35_bz : forall b : byte, 0 <= RIM.bz b.
Proof. intros b. unfold RIM.bz. pose proof (bv_unsigned_in_range 8 b) as H. lia. Qed.

Lemma f35_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f35_bz (RIM.nthb inp (Z.to_nat c))).
  pose proof (f35_bz (RIM.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

(* Every frame cursor c_j lies in [0, n]. *)
Lemma f35_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - pose proof (f35_fL_nonneg inp (fc inp j)) as HL.
    unfold f_next, f_body, f_len, f_h, f_left. lia.
Qed.

(* Phi_j has exactly len_j bytes (the frame's bytes all lie inside the input). *)
Lemma f35_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f35_fc_range inp j) as Hc. pose proof (f35_fL_nonneg inp (fc inp j)) as HL.
  unfold t_phi, t_len, f_phi. rewrite length_firstn, length_skipn.
  unfold f_len, f_body, f_h, f_left in *. unfold nlen in *. lia.
Qed.

(* With at least 50 frame bytes, the block of the frame is the 32 bytes at offset 18 of Phi. *)
Lemma f35_blk : forall inp j, (50 <= length (t_phi inp j))%nat ->
  t_blk inp j = firstn 32 (skipn 18 (t_phi inp j)).
Proof.
  intros inp j H. unfold t_blk, RF.bsl, t_g, fr50.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
  set (p := t_phi inp j) in *.
  rewrite firstn_app. replace (50 - length p)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite skipn_firstn_comm. rewrite firstn_firstn. reflexivity.
Qed.

Lemma f35_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f35_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (f35_byte_range a) as Ra. pose proof (f35_byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma f35_lit0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; intros E; [|subst; reflexivity].
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. change (0 mod 2 ^ 64) with 0 in E.
  Z.div_mod_to_equations. lia.
Qed.

(* ========================= memory helpers ========================= *)

Lemma f35_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma f35_addr_sub : forall m p n k n', addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  addressable m (p + k) n'.
Proof.
  intros m p n k n' (H0 & H1 & H2 & H) Hk Hn' Hkn.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros x Hx. replace (p + k + x) with (p + (k + x)) by lia. apply H. lia.
Qed.

Section F35.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The bcmp wrapper (wrapper_bcmp 0x42aac): it checks that the n bytes at a0 and at a1 are marked usable, then
   calls musl bcmp; a0 = memcmp_model on return; it writes only [sp - 4560, sp). *)
Hypothesis HBC : BW.bcmp_wrap_contract.

(* a_laws_blocks, through SlotInv's lw_blocks: a live block lies at or above 4096, ends below stklo, its end is in
   app memory, and its bytes are app memory (lwb_byte's per-byte list taken apart once here). *)
Lemma f35_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ H4096 Hle Hend Hall].
  split; [exact H4096|]. split; [exact Hle|]. split; [exact Hend|].
  intros a Ha. destruct (Hall a Ha) as (Happ & _ & _ & _ & _). exact Happ.
Qed.

(* ===================== the machine run ===================== *)

(* 0x82c24 with a0 = 1: the beqz falls through, then the bcmp wrapper compares the 32 bytes at L = [A + 312] with
   the 32 bytes at R = s6. *)
Lemma f35_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82c38) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c24) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs vcmp lo -> -> -> HL0 HR0 H312 HBL HBR Hmm HMI HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL312 : ov_read_bytes rsegs m (wa (A + 312)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 312) _ 0 8 H312 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  (* 0x82c24 beqz a0,82c5c (a0 = 1): not taken *)
  step. try if_false.
  (* 0x82c28 li a2,32; 0x82c2c ld a0,312(s1); 0x82c30 mv a1,s6; 0x82c34 jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E32.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 32) with 32%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL32.
    - right; exact HaR32.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* f35_evt on the cut's own memory: ro_agree in place of mem_inv (FRA carries ro_agree only), as F31's
   f31c_evt_ro. The run is taken on the normalized memory (mem_inv_normalize), where the read-side premises hold
   by the mem_rel transfer lemmas of Seg/Tac_ro.v, and MemNorm.evt_normalize carries it back to the cut's memory;
   the post's write facts come back across mem_rel / ro_same. The runtime cells of the post (asan_cells,
   shadow_rw) are not needed by the caller and are dropped. *)
Lemma f35_evt_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 R) s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82c38) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c24) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs vcmp lo E1 E0 E6 HL0 HR0 H312 HBL HBR Hmm HRO HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : LOWMEM_END <= lo) by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
  assert (Hsp64 : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in Hspa; lia).
  pose proof (f35_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A L R ls rs vcmp lo E1 E0 E6 HL0 HR0
    (Tac_ro.ba_rel m _ _ _ REL H312) (Tac_ro.ba_rel m _ _ _ REL HBL) (Tac_ro.ba_rel m _ _ _ REL HBR) Hmm
    (mem_inv_normalize rsegs m)
    (Tac_ro.addressable_rel m _ _ _ REL HADL) (Tac_ro.addressable_rel m _ _ _ REL HADR)
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR (Tac_ro.stk_rel m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hspa
    (Tac_ro.asan_cells_rel m _ REL HAC) (Tac_ro.shadow_rw_rel m _ REL HSW)
    (Tac_ro.ba_rel m _ _ _ REL HRB) (Tac_ro.ba_rel m _ _ _ REL HRM) (Tac_ro.ba_rel m _ _ _ REL HGC)
    (Tac_ro.ba_rel m _ _ _ REL HC254) (Tac_ro.ba_rel m _ _ _ REL HC255)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  exact (Tac_ro.stk_rel_back memX m0' lo _ Hmr Hlo0 Hsp64 ST').
Qed.

(* Lib-evt -> SR bridge: the one place of this file that uses the lazy-model lemma AsanLift.evt_SR_canon_lazy. The one
   lazy run of this file is 0x82c24 -> 0x82c38 through wrapper_bcmp (f35_evt). It reads the word [s1 + 312,
   s1 + 320), the operand bytes [Phi + 18, Phi + 50) and [fr + 64, fr + 96) and their shadow bytes at
   (a >> 3) + 0x7fff8000, the runtime cells of the wrapper (REAL_BCMP 0xa2610, REAL_MEMCMP 0xa2608, GOT_CF 0xa08e0,
   CF + 254 / CF + 255 at 0x13b2e6 / 0x13b2e7, the shadow-map cells of asan_cells), and writes only the wrapper's
   stack scratch [sp - 4560, sp) (BCMP_WRAP_K). The bcmp wrapper contract lives in Lib.Exec, so the run is a
   Lib.Exec.evt and feeds evt_SR_canon_lazy directly. *)
Lemma f35_run_lib : forall regs pc mem md
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

(* The runtime cells the wrapper_bcmp contract reads, from the FRA runtime invariant (RT's named projections; the
   generated asan_cf_cells is taken apart once here, by statement). *)
Lemma f35_bcmp_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL0.
  pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCF0. unfold asan_cf_cells in HCF0. decompose [and] HCF0.
  match goal with H : bytes_at _ mem RT_GOT_CF _ |- _ => rename H into HGOTCF end.
  match goal with H : bytes_at _ mem (RT_CF + 240) _ |- _ => rename H into HCF240 end.
  split; [exact (AsanRTInv.RT_cells _ _ _ HRT)|]. split; [exact (AsanRTInv.RT_shadow_rw _ _ _ HRT)|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (f35_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (f35_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* FRA moves across a run that writes only W, where W is apart from the frame, from the low image / shadow
   (below HIGHMEM_BEG) and from everything at or above sp (the spill area [A, A + 448), the saved registers
   [S - 104, S)): the bcmp wrapper's scratch window [sp - 4560, sp). The S-anchored window [S - SLOT_STACK, S) on
   the new memory is the caller's (the callee's stk post below sp, joined with the untouched part above sp). The frame
   location disjunction is kept by the stklo equality (real arm) and the tp word (side arm, read by a_in_fs and by
   the FakeStack-metadata bound, both below HIGHMEM_BEG) and, on the side arm, by FSREC (Tac_slot's fsrec_munch_lo,
   from the premise that W writes nothing below stklo outside the frame body); the window bytes outside the frame
   keep their shadow bytes (sl_addr_keep: W is app memory). The same move as F31's f31_stk_run. *)
Lemma f35_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall x, AC.aspZ regs <= x -> Frame.outside W x) ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWIN Happ HWframe HWlo HWhi HWfs
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold HIGHMEM_BEG in *; lia).
      apply HWlo. unfold HIGHMEM_BEG in *; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. rewrite Haspz. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + eapply fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx.
    pose proof (HshIS x ltac:(lia)) as Hin. apply HWlo.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  split; [exact HWIN|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWhi. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. rewrite Haspz. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block is app memory below stklo and apart from the frame (fra_in_apart), so outside W *)
  apply (fra_in_keep g mem mem' W Hinb Hinblk MU HAW).
  intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxfr & _). apply HWfs; [exact Hxlo | lia].
Qed.

(* ===================== the segment lemma ===================== *)

(* Entry SlotInv.Inv_B82c24_at at row i; exits SlotInv.Inv_B82c38_at at row i (the one this range reaches),
   Inv_B82bf4_at at row S i and Inv_B82ca0_at (forms-asan-ubsan S_F35). *)
Lemma seg_F35 : forall j i : nat,
  Hat2 B APIf ra (Inv_B82bf4_at B APIf ra) j (S i) ->
  Hat2 B APIf ra (Inv_B82c38_at B APIf ra) j i ->
  Hat B APIf ra (Inv_B82ca0_at B APIf ra) j ->
  Hat2 B APIf ra (Inv_B82c24_at B APIf ra) j i.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j i _ Hbd4 _ g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & H18f & H20f & HFT & HLK &
    Hi10' & Hs272 & _ & HRL & H10 & Hdecl & Haddr & HIFS).
  subst c. rewrite SEGS.
  pose proof HRL as (Hi10 & H23 & H24 & H25 & H21 & H22 & Hprev & HPT).
  pose proof HPT as (Hsel & H18 & H20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hcnt & Hfstk).
  pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
  (* the row path has len >= 50 (kind 9), so the cut's block (Phi, a_size len) is (Phi, len) *)
  assert (Hlen50 : 50 <= flen g j) by (unfold flen; exact (f34_rowsel_len (g_in g) j Hsel)).
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Esz in HFRA, HENT.
  destruct (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel5 & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hdisj & _ & _ & _).
  (* ---- bounds ---- *)
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAb : 0 <= A /\ A + 448 <= 2 ^ 64) by lia.
  assert (Hfrb : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Hfapp; lia).
    unfold app_mem in Ha. unfold LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  assert (Hfr64 : fr + FRAME_BYTES <= 2 ^ 64) by (unfold APPMEM_END in Hfrb; lia).
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGT; lia).
  (* ---- the spills this range reads or passes on ---- *)
  assert (Q312 : q64 mem (A + 312) (phi + 18)) by (apply (f34_spill regs mem 312 _ A Hs312 Hr9); lia).
  assert (Q152 : q64 mem (A + 152) (fr + 64)) by (apply (f34_spill regs mem 152 _ A Hs152 Hr9); lia).
  assert (Q160 : q64 mem (A + 160) (fr + 32)) by (apply (f34_spill regs mem 160 _ A Hs160 Hr9); lia).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  (* ---- the heap block [Phi, Phi + len) with len >= 50 (row kind 9): the 32 block bytes at Phi + 18 ---- *)
  destruct (f35_blocks (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH
              ltac:(apply in_or_app; left; unfold hb1; left; reflexivity)) as (Hp4096 & Hle & Hend & Hby).
  assert (Hphib : phi + flen g j <= g_S g - AF.SLOT_STACK) by lia.
  assert (HphiL : length (t_phi (g_in g) j) = Z.to_nat (flen g j)) by (unfold flen; apply f35_phi_len).
  assert (HphiL50 : (50 <= length (t_phi (g_in g) j))%nat) by lia.
  assert (Hblk : t_blk (g_in g) j = firstn 32 (skipn 18 (t_phi (g_in g) j))) by (apply f35_blk; exact HphiL50).
  assert (HBL : bytes_at rsegs mem (phi + 18) (t_blk (g_in g) j)).
  { rewrite Hblk. change (phi + 18) with (phi + Z.of_nat 18). apply f35_ba_sub; [exact Hphi | lia]. }
  assert (HblkL : length (t_blk (g_in g) j) = 32%nat) by (rewrite Hblk, length_firstn, length_skipn; lia).
  assert (HdeclL : length (decl_i (Z.of_nat i)) = 32%nat) by (apply f34_decl_len; lia).
  assert (HADL : addressable mem (phi + 18) 32).
  { apply (f35_addr_sub mem phi (AC.a_size (flen g j)) 18 32 (proj2 HHB)); unfold AC.a_size; lia. }
  assert (Happ50 : app_mem (phi + 18 + 32)).
  { destruct (Z.eq_dec (flen g j) 50) as [E|NE].
    - destruct Hend as [H0|H0]; [lia|]. rewrite E in H0.
      replace (phi + 18 + 32) with (phi + 50) by lia. exact H0.
    - exact (Hby (phi + 18 + 32) ltac:(lia)). }
  assert (Happ7 : app_mem (phi + 18 + 7)) by exact (Hby (phi + 18 + 7) ltac:(lia)).
  (* ---- the compare result ---- *)
  destruct (SF.memcmp_model_total (t_blk (g_in g) j) (decl_i (Z.of_nat i)) 32 ltac:(lia) ltac:(lia))
    as (v & Hv).
  destruct (f35_mm_spec 32 _ _ v HblkL HdeclL Hv) as [Hiff Hvr].
  destruct (f35_bcmp_cells sp mem md HRT) as (HAC0 & HSW0 & HRBc & HRMc & HGC & HC254 & HC255).
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (HSlo & HShi).
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  (* ---- the run 0x82c24 -> 0x82c38 ---- *)
  apply (f35_run_lib regs (Z_to_bv 64 0x82c24) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82c38 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 v /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f35_evt_ro with (A := A) (L := phi + 18) (R := fr + 64) (ls := t_blk (g_in g) j)
        (rs := decl_i (Z.of_nat i)) (vcmp := v) (lo := g_S g - AF.SLOT_STACK).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in H10; exact H10.
      - unfold rg in H22; exact H22.
      - lia.
      - lia.
      - exact Q312.
      - exact HBL.
      - exact Hdecl.
      - exact Hv.
      - exact Hro.
      - exact HADL.
      - exact Haddr.
      - exact Happ50.
      - apply Hfapp; lia.
      - exact Happ7.
      - apply Hfapp; lia.
      - assert (HdjL : phi + 18 + 32 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= phi + 18)
          by (left; rewrite Haspz; unfold BCMP_WRAP_K; lia).
        exact HdjL.
      - assert (HdjR : fr + 64 + 32 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 64).
        { destruct (Hdisj BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K, FN_STACK; lia)) as [HD|HD];
            [left | right]; unfold BCMP_WRAP_K in *; lia. }
        exact HdjR.
      - assert (HstkW : stk rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs)) by (rewrite Haspz; exact HSlo).
        exact HstkW.
      - assert (HloK : g_S g - AF.SLOT_STACK + BCMP_WRAP_K <= AC.aspZ regs)
          by (rewrite Haspz; unfold BCMP_WRAP_K; lia).
        exact HloK.
      - lia.
      - exact HaspB.
      - exact HAC0.
      - exact HSW0.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & RO' & ST').
      eexists _, (Z_to_bv 64 0x82c38), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in Hr9; rewrite Hr9; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in H22; rewrite H22; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. exact ST'. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E10 &
       MU & WM & HroM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v) by (rewrite Hreg; exact E10).
    assert (HWlo : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K in *. lia. }
    assert (HWhi : forall x, AC.aspZ regs <= x -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      destruct (Hdisj BCMP_WRAP_K ltac:(unfold BCMP_WRAP_K, FN_STACK; lia)) as [HD|HD]; lia. }
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END in *. lia. }
    (* `first` [fr + 2880, fr + 2920) (FLI's RAD, third range) stays addressable: W is app memory *)
    assert (Hfst' : addressable mem' (fr + 2880) 40).
    { pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (_ & _ & _ & _ & _ & Ffst).
      eapply sl_addr_keep; [exact Ffst | exact MU | exact Hallapp]. }
    assert (HWfs : forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
                     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros x Hx _. destruct (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hlo & _).
      subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      unfold BCMP_WRAP_K, FN_STACK in *. lia. }
    assert (Hrtdj : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, AC.GT, BCMP_WRAP_K in *.
      rewrite Haspz in *. unfold HIGHMEM_BEG in *. cbn [disjoint_from].
      repeat split; first [left; lia | exact I]. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. subst W.
      cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. rewrite Haspz in *. unfold BCMP_WRAP_K in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (lw_store (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as [HAH' Hown' HSTKeq HSTKHIeq].
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { assert (Hhi' : stk rsegs mem' sp (g_S g)).
      { eapply (Frame.stk_transport rsegs W mem mem' sp (g_S g)); [exact HShi | exact MU | exact WM |].
        intros x Hx. left. apply HWhi. rewrite Haspz. lia. }
      assert (Hlo' : stk rsegs mem' (g_S g - AF.SLOT_STACK) sp) by (rewrite <- Haspz; exact ST').
      exact (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) Hlo' Hhi' ltac:(lia)). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md)
      by exact (f35_stk_run g fr (hb1 phi (flen g j)) regs regs' mem mem' md W HFRA MU WM HroM Hallapp Hrtdj
                  HAH' HSTKeq HWIN' Hfapp HWfr HWlo HWhi HWfs Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26).
    (* ENT: the wrapper wrote only its scratch [sp - 4560, sp), inside the slot window below S *)
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { eapply ent_store with (W := W) (fr := fr) (regs := regs);
        [ exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKHIeq
        | intros a Hia Ho; exact (proj2 (Hown' a) Ho) ].
      intros x Hx. destruct (Z_le_gt_dec (AC.aspZ regs - BCMP_WRAP_K) x) as [D1|D1];
        [destruct (Z_lt_ge_dec x (AC.aspZ regs)) as [D2|D2]|].
      - right; left. rewrite Haspz in *. unfold AF.SLOT_STACK, BCMP_WRAP_K in *. lia.
      - left. subst W. cbn [Frame.outside]. split; [lia | exact I].
      - left. subst W. cbn [Frame.outside]. split; [lia | exact I]. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
          try reflexivity; exact Hmat).
    assert (Kfr : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
                    bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2. apply (fl_bytes W mem mem' a bs Hb MU). intros x Hx. apply HWfr. lia. }
    assert (Khi : forall a bs, bytes_at rsegs mem a bs -> AC.aspZ regs <= a -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1. apply (fl_bytes W mem mem' a bs Hb MU). intros x Hx. apply HWhi. lia. }
    assert (Hphi' : bytes_at rsegs mem' phi (t_phi (g_in g) j)).
    { apply (fl_bytes W mem mem' phi _ Hphi MU). intros x Hx.
      subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. rewrite Haspz in *.
      unfold BCMP_WRAP_K in *. lia. }
    assert (Hiff' : getr regs' 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i)).
    { rewrite Fr10, (f35_lit0 v Hvr). exact Hiff. }
    (* the spills at A (above sp, so outside the wrapper's scratch) *)
    assert (Hspl : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off w Ho Hs.
      assert (Hq : q64 mem (A + off) w) by (apply (f34_spill regs mem off w A Hs Hr9); lia).
      exists A. split; [unfold rg in *; rewrite Fr9; exact Hr9|].
      unfold q64 in *. apply Khi; [exact Hq | lia]. }
    (* ---- the exit cut ---- *)
    assert (HIexit : Inv_B82c38_at B APIf ra g j i
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82c38) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS, Esz. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|].
      split.
      { split; [exact (proj1 HHB)|]. eapply sl_addr_keep; [exact (proj2 HHB) | exact MU | exact Hallapp]. }
      split; [unfold rg in H18 |- *; rewrite Fr18; exact H18|].
      split; [unfold flen; unfold rg in H20 |- *; rewrite Fr20; exact H20|].
      split.
      { destruct HFT as (HF224 & HF232 & _ & _).
        split; [apply Hspl; [lia | exact HF224]|]. split; [apply Hspl; [lia | exact HF232]|].
        split; [exact Hphi' | exact Hplen]. }
      split.
      { pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Fad & Fstk & Frad & Ffrg & Fknt & _).
        eapply Tac_ro.lk_keep; [exact HLK | | | | | | | exact Hfst' | |].
        - unfold rg in *. rewrite Fr27. exact (proj1 HFLI).
        - eapply sl_addr_keep; [exact Fad | exact MU | exact Hallapp].
        - eapply (Frame.stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES)); [exact Fstk | exact MU | exact WM |].
          intros x Hx. left. apply HWfr. lia.
        - eapply sl_addr_keep; [exact Frad | exact MU | exact Hallapp].
        - eapply sl_addr_keep; [exact Ffrg | exact MU | exact Hallapp].
        - (* the kind-name table (image data below GT): the wrapper writes only its scratch below sp *)
          apply (Tac_ro.knt_munch W mem mem' Fknt MU (munch_meta W mem mem' MU Hallapp)).
          intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. rewrite Haspz in *.
          unfold KNC.KIND_NAME, BCMP_WRAP_K, HIGHMEM_BEG in *. lia.
        - unfold OURb in *. apply Kfr; [exact HOUR | lia | rewrite OUR_length; lia].
        - exact Hspl. }
      split; [exact Hi10|].
      split; [apply Hspl; [lia | exact Hs272]|].
      split; [exact I|].
      split.
      { split; [exact Hi10|].
        split; [unfold rg in *; rewrite Fr23; exact H23|].
        split; [unfold rg in *; rewrite Fr24; exact H24|].
        split; [unfold rg in *; rewrite Fr25; exact H25|].
        split; [unfold rg in *; rewrite Fr21; exact H21|].
        split; [unfold rg in *; rewrite Fr22; exact H22|].
        split; [exact Hprev|].
        split; [exact Hsel|].
        split; [unfold rg in *; rewrite Fr18; exact H18|].
        split; [unfold rg in *; rewrite Fr20; exact H20|].
        split; [exists A; split; [unfold rg in *; rewrite Fr9; exact Hr9 | unfold q64 in *; apply Khi; [exact Q152 | lia]]|].
        split; [exists A; split; [unfold rg in *; rewrite Fr9; exact Hr9 | unfold q64 in *; apply Khi; [exact Q312 | lia]]|].
        split; [exact Hphi'|]. split; [exact Hplen|].
        split; [exists A; split; [unfold rg in *; rewrite Fr9; exact Hr9 | unfold q64 in *; apply Khi; [exact Q160 | lia]]|].
        split; [unfold q64 in *; apply Kfr; [exact Hcnt | lia | rewrite length_le8; lia]|].
        eapply (Frame.stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES)); [exact Hfstk | exact MU | exact WM |].
        intros x Hx. left. apply HWfr. lia. }
      split; [exact Hiff'|].
      split; [apply Kfr; [exact Hdecl | lia | rewrite HdeclL; lia]|].
      split; [eapply sl_addr_keep; [exact Haddr | exact MU | exact Hallapp]|].
      apply (f34_IFS_keep g fr (S j) regs regs' mem mem' W HIFS MU);
        [intros x Hx; apply HWfr; lia | exact Hfst']. }
    pose proof (Hbd4 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F35.
