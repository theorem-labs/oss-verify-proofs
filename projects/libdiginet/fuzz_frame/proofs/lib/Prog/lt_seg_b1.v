(* Walk of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.plain from the return of malloc (0x12cb4) to
   the return of the second memset (0x12d04), on Exec.evt (fuzz_frame.c:272-275): the test of the malloc
   result (0x12cb4: beqz a0 to abort; the caller gives a block address of 4096 or more), the copy of the
   input into the block buf (fuzz_dup: memcpy when size is not 0), memset of the struct diginet_frame f at
   sp + 0x50 (64 bytes), diginet_frame_parse (buf, size, f), and memset of the struct spec_frame w at sp
   (80 bytes) that begins the inlined spec_read_frame. memcpy, memset and diginet_frame_parse are taken
   through their contracts (Section hypotheses).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import memcpy_c memset_c diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.

(* Decide a branch whose condition becomes linear arithmetic once register literals are unfolded. *)
Ltac b1_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.
Ltac b1_curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* memset's block after a fill with the register zero: the byte is b8 0. *)
Ltac b1_zero :=
  try change (Z_to_bv 8 (0 mod 256)) with (b8 0) in *;
  try change (Z.to_nat 64) with 64%nat in *;
  try change (Z.to_nat 80) with 80%nat in *.

(* From 0x12cd0, with the input bytes at buf: memset (sp + 0x50, 0, 64), diginet_frame_parse (buf,
   size, sp + 0x50), memset (sp, 0, 80), to 0x12d04. *)
Ltac b1_ms1 MSET jf :=
  (* memset (sp + 0x50, 0, 64) *)
  do 4 step;
  b1_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply MSET with (junk := jf) | unfold memset_post; rewrite ?unsigned_lit by lia; post_call rsegs mm ]);
  [ rewrite ?unsigned_lit by lia; eassumption | eassumption | ];
  b1_zero.
Ltac b1_parse PARSE sp buf pl lo :=
  (* diginet_frame_parse (buf, size, sp + 0x50) *)
  do 4 step;
  b1_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply PARSE with (buf := buf) (f := bv_unsigned sp + 80) (lo := lo) (b := pl) (fj := repeat (b8 0) 64)
    | post_call rsegs mm ]);
  [ lia | lia | eassumption | eassumption | cbn [length]; lia | eassumption | lia | cbn [length]; lia | lia
  | eassumption | ].
Ltac b1_ms2 MSET pl jw :=
  (* split on the parse answer, so the cells at f have a size the transport over memset can compute *)
  destruct (fr_code pl =? 0);
  cbv beta iota in *; try unfold parse_cells in *;
  (* mv s1, a0; memset (sp, 0, 80) *)
  do 5 step;
  (b1_curmem ltac:(fun mm => eapply evt_cut;
     [ eapply MSET with (junk := jw) | unfold memset_post; rewrite ?unsigned_lit by lia; post_call rsegs mm ]);
   [ rewrite ?unsigned_lit by lia; eassumption | eassumption | ]);
  b1_zero.
Ltac b1_tail MSET PARSE sp buf pl lo jw jf :=
  b1_ms1 MSET jf; b1_parse PARSE sp buf pl lo; b1_ms2 MSET pl jw; finish.

Section B1.
Hypothesis MC : memcpy_contract.
Hypothesis MSET : memset_contract.
Hypothesis PARSE : diginet_frame_parse_contract.

Lemma lt_b1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf p : Z) (pl jb jw jf : list byte)
         (x1 x2 x3 x4 : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 p -> s2 = Z_to_bv 64 (Z.of_nat (length pl)) ->
    Z.of_nat (length pl) < 2 ^ 26 -> 4096 <= buf -> buf + Z.of_nat (length pl) <= lo ->
    rw_cells rsegs m buf [CB (length pl) jb] ->
    ((0 < length pl)%nat -> bytes_at rsegs m p pl) ->
    ((0 < length pl)%nat -> p + Z.of_nat (length pl) <= buf \/ buf + Z.of_nat (length pl) <= p) ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 jw] ->
    rw_cells rsegs m (bv_unsigned sp + 80) [CB 64 jf] ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 (fr_code pl)) a0' a1' a2' a3' a4' a5'
                       a6' a7' (Z_to_bv 64 (Z.of_nat (length pl))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x12d04) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp + 144); (buf, buf + Z.of_nat (length pl))] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' buf pl /\
         rw_cells rsegs m' (bv_unsigned sp) [CB 80 (repeat (b8 0) 80)] /\
         rw_cells rsegs m' (bv_unsigned sp + 80)
           (if fr_code pl =? 0 then parse_cells buf pl (repeat (b8 0) 64) else [CB 64 (repeat (b8 0) 64)]) /\
         rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cb4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo buf p pl jb jw jf x1 x2 x3 x4 ST LO HSP MI EA0 ES1 ES2 PL B4 BL JB PB DP W FJ SV.
  subst a0 s1 s2.
  pose proof (u64_range sp) as Rsp.
  pose proof (proj1 ST) as LO0.
  pose proof (rw_cells_bound _ _ _ _ JB) as JBb. cbn [cells_size csize] in JBb.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp + 144); (buf, buf + Z.of_nat (length pl))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* beqz a0 (the block address is not 0); mv s0, a0; beqz s2 *)
  step. b1_br false.
  do 2 step.
  destruct (Nat.eq_dec (length pl) 0) as [L0|L0]; [b1_br true | b1_br false].
  - (* size 0: no copy *)
    apply length_zero_iff_nil in L0. subst pl. cbn [length] in *.
    assert (BP : bytes_at rsegs m buf []) by (apply bytes_at_nil; lia).
    clear JB PB DP.
    b1_tail MSET PARSE sp buf (@nil byte) lo jw jf.
  - (* memcpy (buf, p, size) *)
    pose proof (bytes_at_bound _ _ _ _ (PB ltac:(lia))) as PBb.
    do 4 step.
    eapply evt_cut; [ eapply MC with (src := pl) (junk := jb) | ].
    + rewrite unsigned_lit by lia. apply PB. lia.
    + rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    + rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact JB.
    + rewrite !unsigned_lit by lia. apply DP. lia.
    + exact MI.
    + unfold memcpy_post. rewrite !unsigned_lit by lia. rewrite Nat2Z.id. post_call rsegs m.
      (* the copied bytes at buf *)
      lazymatch goal with H : rw_cells rsegs _ buf [CB _ pl] |- _ =>
        pose proof (proj2 (proj1 H)) as BP; clear H end.
      cbn [cells_bytes cbytes] in BP. rewrite app_nil_r in BP.
      clear PB DP POST.
      b1_tail MSET PARSE sp buf pl lo jw jf.
Qed.

End B1.
