(* reloc-zl14c *)
(* (uncompress 1.4 UBSan): the plain 1.4 MrP9/S9U2Seg moved to the UBSan image. The 1.4 UBSan
   harness keeps the plain build's frames and register choices (fuzzer 16, uncompress 32, uncompress2_z 160 with the
   z_stream at its sp + 0, inflateInit_ 32), adds UBSan's alignment traps (uncompress: &destLen; uncompress2_z:
   &sourceLen, &destLen; inflateInit_: strm) and a NULL check on &destLen in uncompress, and inflateInit_ builds its
   frame first and keeps strm in s2 and the state size 7176 in s1 over the zalloc call. inflateEnd keeps zfree in a3
   (its 1.3.1 code at new addresses). Addresses from dis/14u-*.dis. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU9 Require Import PImg RMallocRep RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesU9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import U9HBase U9HConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U9LibStmt.

(* a literal's little-endian bytes *)
Lemma le8_lit : forall z, 0 <= z < 2^64 -> le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof. intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.

(* an rdn fact as the ov_read_bytes fact a load step wants *)
Lemma ovr_of_rdn_Z {RCa1 : RunCtx}  : forall (M : word -> option byte) a a' z,
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) -> 0 <= z < 2^64 -> a = a' ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a') 8 = Some (le8 (Z_to_bv 64 z)).
Proof. intros M a a' z H Hz <-. rewrite ov_rdn, le8_lit by lia. exact H. Qed.

Lemma ovr_of_rdn_w {RCa1 : RunCtx}  : forall (M : word -> option byte) a a' (v : word),
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> a = a' ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a') 8 = Some (le8 v).
Proof. intros M a a' v H <-. rewrite ov_rdn. exact H. Qed.

(* read a carved frame's cell k as the rdn fact the records want *)
Ltac cell_fact H k :=
  lazymatch goal with |- OP.rdn _ ?m (Z_to_bv 64 ?E) ?n = Some _ =>
    lazymatch type of H with rw_cells ?segs m ?A ?cs =>
      let c := eval_cell_at cs k in
      lazymatch c with Some ?c0 =>
        let X := fresh "X" in
        pose proof (rw_cells_read_at segs m A cs k c0 n (wa (A + Z.of_nat k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as X;
        rewrite ov_rdn in X; cbv beta iota delta [cbytes] in X;
        replace E with (A + Z.of_nat k) by (cbn; lia);
        first [ exact X | rewrite le8_lit in X by lia; first [ exact X | replace_val X ] ]
      end end end
with replace_val X :=
  lazymatch type of X with _ = Some (Z_to_le_bytes _ ?z) =>
    lazymatch goal with |- _ = Some (Z_to_le_bytes _ ?z') => replace z' with z by lia; exact X end end.

Ltac br_false := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply negb_false_iff, Z.eqb_eq; lia] | rewrite C; cbv iota; clear C ] end.
Ltac br_true := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = true);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_eq; lia | apply negb_true_iff, Z.eqb_neq; lia] | rewrite C; cbv iota; clear C ] end.

(* a worker 1.4 UBSan: an 8-aligned stack address passes UBSan's alignment trap (and x,7 = 0) *)
Lemma land7_al : forall x e, x mod 16 = 0 -> (e - x) mod 8 = 0 -> Z.land e 7 = 0.
Proof.
  intros x e Hx Hk. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  assert (X8 : x mod 8 = 0).
  { pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
    rewrite D. replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult. }
  replace e with (x + (e - x)) by lia. rewrite Z.add_mod by lia. rewrite X8, Hk. reflexivity.
Qed.

Section SEG.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.

(* a worker 1.4 UBSan: the `bnez` after an `and _,x,7` on a stack address x falls through *)
Ltac br_al := lazymatch goal with |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ?E)) 7)) _) then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : Z.land (bv_unsigned (Z_to_bv 64 E)) 7 = 0);
    [ rewrite unsigned_lit by lia; apply (land7_al sp0); [exact SP16 | Z.to_euclidean_division_equations; lia]
    | rewrite C; clear C; change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false; cbv iota ] end.

(* a worker 1.4: UU = u, the caller's sp at the inflate call (IK's convention at 1.4: strm = UU). 1.4's frames: fuzzer 16 (sp0-224), uncompress 32 (sp0-256),
   uncompress2_z 160 (sp0-416 = UU: the z_stream is at its sp+0), inflateInit_ 32 (sp0-448 = UU-32). *)
Abbreviation UU := (sp0 - 416).

Definition T_RET : Z := 0x14c94.

(* the return point in LLVMFuzzerTestOneInput after `jal uncompress` (1.4 UBSan: 0x14d5c + 4) *)
Definition U9_UNC_RA : Z := 0x14dc0.
(* a worker 1.4: the saved cells of the three caller frames. uncompress (1.4) saves s0 (the harness's payl) and keeps
   copies of *destLen (got, UU+176) and sourceLen (UU+168); uncompress2_z saves ra and s0..s4 (no s5 at 1.4: v5 is
   kept as an unused parameter so the consumers' arity is unchanged). *)
Record u2_frames (M : word -> option byte) (q payl : Z) (v2 v3 v4 v5 : word) : Prop := U2_FRAMES {
  uf_hra : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 200)) 8 = Some (Z_to_le_bytes 8 T_RET);
  uf_wra : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 184)) 8 = Some (Z_to_le_bytes 8 U9_UNC_RA);
  uf_us0 : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 payl));
  uf_ura : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 152)) 8 = Some (Z_to_le_bytes 8 OL.U9_HARN_RA);
  uf_s0  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (sp0 + -224)));
  uf_s1  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 q));
  uf_s2  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 128)) 8 = Some (word_to_le_bytes 8 v2);
  uf_s3  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 120)) 8 = Some (word_to_le_bytes 8 v3);
  uf_s4  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 112)) 8 = Some (word_to_le_bytes 8 v4)
}.

(* a worker 1.4: inflateInit_'s saved cells (its frame is UU-32 .. UU) and the z_stream fields uncompress2_z set. *)
Record u2_za_cells (M : word -> option byte) (q : Z) : Prop := U2_ZA_CELLS {
  uz_s2 : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 32)) 8 = Some (Z_to_le_bytes 8 OL.U9_BUF);
  uz_s1 : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 24)) 8 = Some (Z_to_le_bytes 8 (UU + 160));
  uz_s0 : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 16)) 8 = Some (Z_to_le_bytes 8 (UU + 168));
  uz_ra : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.U9_RA_II);
  uz_in : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 q));
  uz_av : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 8)) 4 = Some (Z_to_le_bytes 4 0);
  uz_za : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 64)) 8 = Some (Z_to_le_bytes 8 OL.U9_ZCALLOC);
  uz_zf : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 72)) 8 = Some (Z_to_le_bytes 8 OL.U9_ZCFREE);
  uz_op : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU + 80)) 8 = Some (Z_to_le_bytes 8 0)
}.

(* a worker 1.4 UBSan: LLVMFuzzerTestOneInput -> uncompress -> uncompress2_z -> inflateInit_ -> zcalloc -> malloc's
   entry, with ra = 0x15150 (inflateInit_ after the zalloc call), s2 = strm, s1 = 7176. *)
Lemma u2_seg1_evt : forall (Q : machine_state -> Prop) (q payl lo : Z) (M : word -> option byte)
    (x3 x4 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= sp0 - 208 - 65536 -> 0 <= payl < 2^26 -> 0 <= q < 2^64 -> 1 <= q ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  (* a worker 1.4: no GOT premise: inflateInit_ forms zcalloc / zcfree with auipc + addi *)
  (forall (M1 : word -> option byte),
     munch [(sp0 - 448, sp0 - 208)] M M1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M1 ->
     u2_frames M1 q payl x18 x19 x20 x21 -> u2_za_cells M1 q ->
     Q (MS (mkR (Z_to_bv 64 0x151b0) (Z_to_bv 64 (sp0 - 448)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sp0 - 248)) (Z_to_bv 64 7176)
                (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176) (Z_to_bv 64 0x17d68) (Z_to_bv 64 112) x15 x16 x17
                (Z_to_bv 64 (sp0 - 416)) (Z_to_bv 64 payl) (Z_to_bv 64 0x40000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           bvmap_empty (Z_to_bv 64 0x1a6e8) fc0 None M1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR (Z_to_bv 64 T_RET) (Z_to_bv 64 (sp0 - 208)) x3 x4 x5 x6 x7 (Z_to_bv 64 payl) (Z_to_bv 64 q) (Z_to_bv 64 q) (Z_to_bv 64 payl) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x14d98) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q q payl lo M x3 x4 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO PAYL QR Q1 ST MI HK.
  pose proof (munch_refl [(sp0 - 448, sp0 - 208)] M) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM.
  unfold T_RET.
  (* LLVMFuzzerTestOneInput: frame 16, buffer_length = 0x40000 at sp, then jal uncompress *)
  step. carve_frame 16%nat ST.
  replace (sp0 - 208 + -16) with (sp0 + -224) in * by lia.
  do 9 step.
  (* uncompress (1.4 UBSan): frame 32; the &destLen NULL and alignment checks; got = *destLen at sp+8, the
     sourceLen copy at sp+0; jal uncompress2_z *)
  step. carve_frame 32%nat ST.
  replace (sp0 + -224 + -32) with (sp0 + -256) in * by lia.
  do 3 step. br_false.                (* sd ra; sd s0; beqz a1 (&destLen) *)
  do 3 step. br_al.                   (* mv s0,a1; and a1,a1,7; bnez a1 *)
  do 6 step.                          (* ld a1,0(s0); sd a1,8(sp); sd a3,0(sp); addi a1,sp,8; mv a3,sp; jal *)
  (* uncompress2_z: frame 160; the argument checks with UBSan's alignment traps *)
  step. carve_frame 160%nat ST.
  replace (sp0 + -256 + -160) with (sp0 + -416) in * by lia.
  do 9 step. br_false.                (* 6 sd; mv s2,a0; li a0,-2; beqz a3 (&sourceLen) *)
  do 4 step. br_al.                   (* mv s1,a3; mv s0,a1; and a1,a3,7; bnez a1 *)
  step. br_false.                     (* beqz s0 (&destLen) *)
  do 5 step.                          (* ld s3,0(s1); snez; seqz; and; bnez a1 *)
  (* a worker 1.4: the (sourceLen > 0 && source == NULL) test is false: source = q >= 1 *)
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ rewrite v_sltiu_b2z; rewrite (unsigned_lit q) by lia;
      replace (bv_wrap 64 1) with 1 by reflexivity;
      replace (q <? 1) with false by (symmetry; apply Z.ltb_ge; lia);
      cbn [Z.b2z]; rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l;
      unfold bv_eqb; rewrite (unsigned_lit 0) by lia; reflexivity
    | rewrite C; cbv iota; clear C ] end.
  do 2 step. br_al.                   (* and a1,s0,7; bnez a1 *)
  do 2 step. if_true.                 (* ld s4,0(s0); bnez s2 (dest) *)
  do 10 step.                         (* the z_stream fields; jal inflateInit_ *)
  (* inflateInit_ (UBSan): the frame first; version and size checks; strm's alignment; zalloc / zfree default to
     zcalloc / zcfree *)
  step. carve_frame 32%nat ST.
  replace (sp0 + -416 + -32) with (sp0 + -448) in * by lia.
  do 4 step.                          (* sd ra, s0, s1, s2 *)
  do 2 step. if_false.                (* li a3,-6; beqz a1 *)
  do 2 step. if_false.                (* li a4,112; bne a2,a4 *)
  do 3 step. if_false.                (* lbu a1,0(a1); li a2,49; bne a1,a2 *)
  step. br_false.                     (* beqz a0 *)
  do 2 step. br_al.                   (* and a1,a0,7; bnez a1 *)
  do 3 step. if_true.                 (* ld a3,64(a0); sd zero,48(a0); beqz a3 *)
  do 6 step. if_false.                (* auipc; addi; sd a3,64; sd zero,80; ld a1,72; bnez a1 *)
  do 4 step.                          (* auipc; addi; sd a1,72; j *)
  do 7 step.                          (* mv s2,a0; ld a0,80(a0); lui; addiw s1; li a1,1; mv a2,s1; jalr a3 *)
  do 4 step.                          (* zcalloc: mul; slli; srli; j malloc *)
  apply evt_done.
  lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => apply (HK mx) end.
  - exact MU.
  - exact WM.
  - exact MI.
  - constructor; unfold T_RET, OL.U9_HARN_RA, U9_UNC_RA.
    + cell_fact FR 8%nat.
    + cell_fact FR0 24%nat.
    + cell_fact FR0 16%nat.
    + cell_fact FR1 152%nat.
    + cell_fact FR1 144%nat.
    + cell_fact FR1 136%nat.
    + cell_fact FR1 128%nat.
    + cell_fact FR1 120%nat.
    + cell_fact FR1 112%nat.
  - constructor; unfold OL.U9_BUF, OL.U9_RA_II, OL.U9_ZCALLOC, OL.U9_ZCFREE.
    + cell_fact FR2 0%nat.
    + cell_fact FR2 8%nat.
    + cell_fact FR2 16%nat.
    + cell_fact FR2 24%nat.
    + cell_fact FR1 0%nat.
    + cell_fact FR1 8%nat.
    + cell_fact FR1 64%nat.
    + cell_fact FR1 72%nat.
    + cell_fact FR1 80%nat.
Qed.

(* a worker 1.4: from uncompress's return point (0x14f40, after jal uncompress2_z) to T_RET. 1.4's uncompress writes
   *destLen = got (the fuzzer's buffer_length cell, sp0-224) on the way out and restores s0 (the harness's payl).
   Its two frames are given as rw_cells (a load after the store needs cells the step transports). *)
Lemma u2_seg_ret_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (sl g bl : word) (payl : Z)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 256) [C8 sl; C8 g; C8 (Z_to_bv 64 payl); C8 (Z_to_bv 64 U9_UNC_RA)] ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 224) [C8 bl; C8 (Z_to_bv 64 T_RET)] ->
  (forall M1 : word -> option byte,
     munch [(sp0 - 224, sp0 - 216)] M M1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M1 ->
     Q (MS (mkR (Z_to_bv 64 T_RET) (Z_to_bv 64 (sp0 - 208)) x3 x4 x5 x6 x7 (Z_to_bv 64 payl) x9 (Z_to_bv 64 0) g x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           bvmap_empty (Z_to_bv 64 T_RET) fc0 None M1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 (Z_to_bv 64 (sp0 - 256)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sp0 - 224)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x14fa0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q M sl g bl payl x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         FR0 FR HK.
  pose proof (munch_refl [(sp0 - 224, sp0 - 216)] M) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM.
  unfold T_RET, U9_UNC_RA in *.
  (* uncompress's tail: ld a1,8(sp); sd a1,0(s0); ld ra,24(sp); ld s0,16(sp); addi sp,sp,32; ret *)
  do 6 step.
  (* LLVMFuzzerTestOneInput's tail: li a0,0; ld ra,8(sp); addi sp,sp,16; ret *)
  replace (sp0 - 256 + 32) with (sp0 - 224) in * by lia. do 4 step. apply evt_done.
  replace (sp0 - 224 + 16) with (sp0 - 208) by lia.
  apply HK; assumption.
Qed.

(* a worker 1.4: zalloc returned NULL. inflateInit_ (from 0x15150) returns Z_MEM_ERROR, and uncompress2_z returns it
   at once to uncompress (0x14f40, U9_HARN_RA), restoring s0 (= sp0-224, uncompress's), s1 (= q) and s2..s4. *)
Lemma u2_seg_null_evt : forall (Q : machine_state -> Prop) (q payl : Z) (M : word -> option byte) (v2 v3 v4 v5 : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= q < 2^64 ->
  u2_frames M q payl v2 v3 v4 v5 -> u2_za_cells M q ->
  (forall y10 y13 : word,
     Q (MS (mkR (Z_to_bv 64 OL.U9_HARN_RA) (Z_to_bv 64 (sp0 - 256)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sp0 + -224)) (Z_to_bv 64 q) y10 x11 x12 y13 x14 x15 x16 x17
                v2 v3 v4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           bvmap_empty (Z_to_bv 64 OL.U9_HARN_RA) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 (Z_to_bv 64 (sp0 - 448)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x151b0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q q payl M v2 v3 v4 v5 x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         QR [F_hra F_wra F_us0 F_ura F_s0 F_s1 F_s2 F_s3 F_s4] [Z_s2 Z_s1 Z_s0 Z_ra _ _ _ _ _] HK.
  unfold OL.U9_HARN_RA, OL.U9_BUF, OL.U9_RA_II in *.
  (* inflateInit_'s frame (sp0-448): s2, s1, s0, ra *)
  pose proof (ovr_of_rdn_Z M _ (sp0 - 448 + 24) _ Z_ra ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (sp0 - 448 + 16) _ Z_s0 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (sp0 - 448 + 8) _ Z_s1 ltac:(lia) ltac:(lia)) as HR3.
  pose proof (ovr_of_rdn_Z M _ (sp0 - 448 + 0) _ Z_s2 ltac:(lia) ltac:(lia)) as HR4.
  (* uncompress2_z's frame (sp0-416): ra, s0..s4 *)
  pose proof (ovr_of_rdn_Z M _ (sp0 - 416 + 152) _ F_ura ltac:(lia) ltac:(lia)) as HR5.
  pose proof (ovr_of_rdn_w M _ (sp0 - 416 + 144) _ F_s0 ltac:(lia)) as HR6.
  pose proof (ovr_of_rdn_w M _ (sp0 - 416 + 136) _ F_s1 ltac:(lia)) as HR7.
  pose proof (ovr_of_rdn_w M _ (sp0 - 416 + 128) _ F_s2 ltac:(lia)) as HR8.
  pose proof (ovr_of_rdn_w M _ (sp0 - 416 + 120) _ F_s3 ltac:(lia)) as HR9.
  pose proof (ovr_of_rdn_w M _ (sp0 - 416 + 112) _ F_s4 ltac:(lia)) as HR10.
  (* inflateInit_: beqz a0 (taken); li a3,-4; j; the epilogue (mv a0,a3, 4 ld, addi, ret) *)
  step. if_true. do 2 step. do 7 step.
  replace (sp0 - 448 + 32) with (sp0 - 416) in * by lia.
  (* uncompress2_z at 0x14dfc: bnez a0 (taken); the epilogue (6 ld, addi, ret) *)
  step. if_true. do 8 step.
  apply evt_done.
  replace (sp0 - 416 + 160) with (sp0 - 256) by lia.
  apply HK.
Qed.

(* updatewindow's zalloc call for the window (0x17af8): zcalloc -> malloc's entry, ra = 0x17afc *)
Lemma u2_seg_zw_evt : forall (Q : machine_state -> Prop) (M : word -> option byte)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17b68) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 32768) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17d68) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        bvmap_empty (Z_to_bv 64 0x1a6e8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17d68) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x17b64) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q M x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 5 step. apply evt_done. exact HK.
Qed.

(* inflateEnd's zfree calls (0x17cc4 for the window, 0x17cdc for the state; zfree in a3): zcfree -> free's entry *)
Lemma u2_seg_ze1_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17d34) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 (Z_to_bv 64 0x17d78) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        bvmap_empty (Z_to_bv 64 0x1a5a8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 (Z_to_bv 64 0x17d78) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x17d30) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q M blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

Lemma u2_seg_ze2_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17d4c) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 (Z_to_bv 64 0x17d78) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        bvmap_empty (Z_to_bv 64 0x1a5a8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 (Z_to_bv 64 0x17d78) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x17d48) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q M blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

(* a worker 1.4: inflateEnd between its two zfree calls (0x17cc8 .. 0x17cdc): mv a2,s0; ld a1,56(a2); ld a3,72(a2);
   ld a0,80(a2); mv s0,a2, with strm = UU (the z_stream at uncompress2_z's sp + 0) *)
Lemma u2_seg_ze1b_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (p : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  OL.end_cells_U9 M UU p -> 0 <= p < 2^64 ->
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 (Z_to_bv 64 0) (Z_to_bv 64 p) (Z_to_bv 64 (UU)) (Z_to_bv 64 0x17d78) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        bvmap_empty (Z_to_bv 64 0x17d48) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x17d34) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q M p x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         (_ & E_st & E_zf & E_op) PR HK.
  unfold OL.U9_ZCFREE in *.
  pose proof (ovr_of_rdn_Z M _ (UU + 56) _ E_st ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (UU + 72) _ E_zf ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (UU + 80) _ E_op ltac:(lia) ltac:(lia)) as HR3.
  do 5 step. apply evt_done. exact HK.
Qed.

End SEG.
