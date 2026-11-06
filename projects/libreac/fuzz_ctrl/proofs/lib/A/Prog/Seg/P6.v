(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names and addresses changed; 1043 of its 1221 lines of code are new or changed and 1024 lines of the source are left out. *)
(* Segment P6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): the run from the cut 0x81bd8 to
   the cut 0x81bf8 (v1.8 0x81b58 .. 0x81b78, IDENTICAL: every pc +0x80).  rule 24: no function proved (a slot
   segment).
     81bd8 li   a0,0
     81bdc li   a1,0
     81be0 ld   s7,232(s1)
     81be4 mv   a2,s7
     81be8 ld   s8,224(s1)
     81bec mv   a3,s8
     81bf0 mv   a4,s4
     81bf4 jal  83f8c <reac_ctrl_identity_reply>     (reply(fr = 0, len = 0, pa = [s1+232], pp = [s1+224], pn = s4))
   With fr = 0 the callee's argument test is false (reply_args 0 pa pp pn = false, p6_args0), so it returns -1 with
   OUT unchanged (claim C1.2) and its premises on the fr / len bytes and on the OUT cells are vacuous.  The run
   writes its stack window [S - 9072, S), the class-1 side-stack bytes (fp_w [1%nat] FS) and the shadow of its
   window (p6_W).  p6_evt is the Lib-level run of the eight instructions with the call taken by its contract
   reac_ctrl_identity_reply_contract (a hypothesis of the segment lemma, as R4/R8 do; linking happens later).

   FRA and ENT move across those writes by p6_fra_keep: the runtime invariant RT by AsanRTInv.RT_meta_write (the
   write set is apart from the runtime's cells, p6_rt_disjoint, and every shadow byte reads back after the run), the
   heap invariant AH and the stack bounds by Contract.a_laws_fs_store (the writes are the stack window, the side
   stack and its shadow), whose side-stack premise a_fs_ok of the new memory is rebuilt by p6_fs_ok from the
   callee's fp (class 1) and from a_fs_ok of the old memory; ENT by ent_munch.  The frame, its header and its 392
   shadow bytes are kept because the rebuilt package puts them apart from the class-1 bytes (its fp_dj) and FRA
   puts them apart from the window (fra_frame).

   Cut convention: both cuts are SlotInv's: the entry Inv_A81bd8 and the exit Inv_A81bf8 (SlotInv's XC, no
   mem_inv; aslot push 11: both carry CUR g (c0 (g_in g)), IDBe g fr ID0 and FGBe g fr z72, kept here because the
   call keeps s6 / s9 and writes nothing of the frame; aslot push 12: also the spill [A + 144] = fr + 2688, above
   sp so outside the call's writes, and the 17 bytes at fr + 2691 addressable, whose shadow bytes S(fr) + 336 .. 338
   are frame shadow bytes the call does not write).  No cut carries the callee's side-stack package (fp [1] and
   reac_ctrl_identity_reply_tls at the window, and fp_dj of the frame against fp_w [1] FS): it is rebuilt from the
   entry FRA by Tac_fsfree.inv_a81bd8_pkg.  The callee's mem_inv premise is met by p6_evt_ro, which runs the call
   on the normalized memory (MemNorm.evt_normalize from FRA's ro_agree).  Aslot push 13: PRO moves by P1's
   pro_run: its spills are above sp, our[]'s shadow byte S(fr) + 328 is a frame-shadow byte, and the input block
   (for 0 < n a live block) and its shadow bytes are outside the write set (p6_blk_out). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP RcAsanFPLib reac_ctrl_parse_c reac_ctrl_identity_reply_c.
Import ListNotations.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The write-set predicates (munch, wmono, outside, mkR) of the callee contract and of Tac_slot are Lib.Frame's. *)
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.

(* The write set of the call: the callee's stack window, the class-1 side-stack bytes and the shadow of the window
   (the munch of reac_ctrl_identity_reply_contract with reply_args false). *)
Definition p6_W (S FS : Z) : list ivl :=
  (S - REAC_CTRL_IDENTITY_REPLY_K, S) :: fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)].

(* ---- With fr = 0 the callee's argument test is false, so its write set, data ranges and result are constant. ---- *)

Lemma p6_args0 : forall pa pp pn, reply_args 0 pa pp pn = false.
Proof. intros pa pp pn. unfold reply_args. reflexivity. Qed.

Lemma p6_ret0 : forall len pa pp pn g, reply_ret 0 len pa pp pn g = -1.
Proof. intros len pa pp pn g. unfold reply_ret. rewrite p6_args0. reflexivity. Qed.

Lemma p6_fp0 : forall len pa pp pn S g,
  reac_ctrl_identity_reply_fp 0 len pa pp pn S g = [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].
Proof.
  intros len pa pp pn S g. unfold reac_ctrl_identity_reply_fp, reply_ok. rewrite p6_args0. reflexivity.
Qed.

Lemma p6_Wc0 : forall pa pp pn S,
  reac_ctrl_identity_reply_W 0 pa pp pn S = [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].
Proof. intros pa pp pn S. unfold reac_ctrl_identity_reply_W. rewrite p6_args0. reflexivity. Qed.

Lemma p6_D0 : forall len pa pp pn, reac_ctrl_identity_reply_D 0 len pa pp pn = [].
Proof. intros len pa pp pn. unfold reac_ctrl_identity_reply_D. rewrite p6_args0. reflexivity. Qed.

(* ---- Outside the write set. ---- *)

Lemma p6_out_lo : forall (W : list ivl) x, (forall p, In p W -> x < fst p) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|].
  split.
  - pose proof (H (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma p6_dj_lo : forall (W : list ivl) (c n : Z), (forall p, In p W -> c + n <= fst p) -> disjoint_from W c n.
Proof.
  induction W as [|[lo hi] W IH]; intros c n H; cbn [disjoint_from]; [exact I|].
  split.
  - left. pose proof (H (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

(* Every range of the write set begins at or above the end of the image's writable data (0x5fe000 = ASAN_GT): the
   side stack is placed there, its shadow lies above ASAN_K, and the window lies in high memory. *)
Lemma p6_W_los : forall S FS p, ASAN_GT <= FS -> HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K ->
  In p (p6_W S FS) -> 6283264 <= fst p.
Proof.
  intros S FS p HFS HS Hin.
  assert (D1 : 0 <= (fs_frame FS 1 0) / 8).
  { apply Z.div_pos; [|lia]. unfold fs_frame, fs_B, ASAN_GT in *. cbn [Z.of_nat Pos.of_succ_nat] in *. lia. }
  assert (D2 : 0 <= (S - REAC_CTRL_IDENTITY_REPLY_K) / 8).
  { apply Z.div_pos; [|lia]. unfold HIGHMEM_BEG in HS. lia. }
  unfold p6_W, fp_w, flat_map, fp_w1 in Hin. cbn [app In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst p; cbn [fst];
    unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B, shadow_addr, ASAN_K, ASAN_GT, HIGHMEM_BEG,
      REAC_CTRL_IDENTITY_REPLY_K in *;
    cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
Qed.

(* A byte apart from the class-1 side-stack bytes: it lies outside the side stack, or inside its metadata header
   but off the class-1 hint word and flag bytes; and it is not the shadow byte of a side-stack byte. *)
Lemma p6_out_fpw : forall FS x, 0 < FS ->
  ((x < FS \/ FS + FS_SIZE <= x) \/
   (FS <= x < FS + 36864 /\ ~ (fs_hint FS 1 <= x < fs_hint FS 1 + 8) /\
    ~ (fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1))) ->
  (forall b, FS <= b < FS + FS_SIZE -> x <> shadow_addr b) ->
  outside (fp_w [1%nat] FS) x.
Proof.
  intros FS x HFS Hout Hsh.
  unfold fp_w, flat_map, fp_w1. cbn [app outside].
  assert (HB : ~ (fs_hint FS 1 <= x < fs_hint FS 1 + 8) /\
               ~ (fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1) /\
               ~ (fs_frame FS 1 0 <= x < fs_frame FS 1 (fs_M 1))).
  { unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B, FS_SIZE in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    destruct Hout as [Hout|(H1 & H2 & H3)];
      [repeat split; lia
      | repeat split; [exact H2 | exact H3 | lia]]. }
  destruct HB as (HB1 & HB2 & HB3).
  split; [exact HB1|]. split; [exact HB2|]. split; [exact HB3|].
  split; [|exact I].
  intros [H1 H2]. apply (Hsh (8 * (x - ASAN_K))).
  - unfold shadow_addr, ASAN_K, FS_SIZE, fs_frame, fs_M, fs_B in *.
    cbn [Z.of_nat Pos.of_succ_nat] in *. Z.div_mod_to_equations. lia.
  - unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia.
Qed.

(* The write set in the three pieces the segment reasons about. *)
Lemma p6_out : forall S FS x,
  ~ (S - REAC_CTRL_IDENTITY_REPLY_K <= x < S) ->
  outside (fp_w [1%nat] FS) x ->
  ~ (shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K) <= x < shadow_addr S) ->
  outside (p6_W S FS) x.
Proof.
  intros S FS x H1 H2 H3. unfold p6_W. cbn [outside]. split; [exact H1|].
  apply fl_out_app; [exact H2|]. cbn [outside]. split; [exact H3 | exact I].
Qed.

(* The input block (aslot push 13's PRO): a byte x of a live heap block is app memory below stklo <= S - K (S - K
   8-aligned) and outside the side stack, so neither x nor its shadow byte is in the reply call's write set. *)
Lemma p6_blk_out : forall S FS x lo,
  0 < FS -> FS mod 4096 = 0 -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  app_mem x -> x < lo -> lo <= S - REAC_CTRL_IDENTITY_REPLY_K ->
  HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END -> S mod 16 = 0 ->
  ~ (FS <= x < FS + FS_SIZE) ->
  LF.outside (p6_W S FS) x /\ LF.outside (p6_W S FS) (shadow_addr x).
Proof.
  intros S FS x lo HFS0 HFSa HFSapp Hx Hlo HloS HSh HSa HSm Hnfs.
  assert (HK : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  pose proof (HFSapp FS ltac:(unfold FS_SIZE; lia)) as HF0.
  pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as HF1.
  pose proof (shadow_of_app x Hx) as Hsx.
  split; apply p6_out.
  - lia.
  - apply p6_out_fpw; [exact HFS0 | left; lia |].
    intros b Hb Heq. apply (app_not_shadow x Hx). rewrite Heq. apply shadow_of_app. exact (HFSapp b Hb).
  - clear - Hx HSh HSa HK. unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
    rewrite HK in *. Z.div_mod_to_equations. lia.
  - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsx, HSh. lia.
  - apply p6_out_fpw; [exact HFS0 | left |].
    + clear - Hsx HF0 HF1.
      unfold in_shadow, app_mem, FS_SIZE, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
      lia.
    + intros b Hb Heq. apply Hnfs. clear - Hb Heq HFSa. unfold shadow_addr, FS_SIZE in *.
      Z.div_mod_to_equations. lia.
  - clear - Hx Hlo HloS HSm HK. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx.
    unfold shadow_addr. rewrite HK in *. Z.div_mod_to_equations. lia.
Qed.

(* ---- The Lib-level run of the segment. ---- *)

Lemma p6_evt : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S -> mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x81bf8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp -> -> HS Hpa Hpp H232 H224 Hmod HKS HST HMI HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS.
  assert (HL232 : ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 pa))).
  { pose proof (bytes_at_ov_read rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) 0 8 H232
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL224 : ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 pp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) 0 8 H224
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. (* 81bd8 li a0,0 *)
  step. (* 81bdc li a1,0 *)
  step. (* 81be0 ld s7,232(s1) *)
  step. (* 81be4 mv a2,s7 *)
  step. (* 81be8 ld s8,224(s1) *)
  step. (* 81bec mv a3,s8 *)
  step. (* 81bf0 mv a4,s4 *)
  step. (* 81bf4 jal reac_ctrl_identity_reply *)
  pose proof RPL as HR. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HR.
  eapply evt_cut.
  { eapply HR with (fr := 0) (len := 0) (S := S) (FS := FS) (g := repeat (Z_to_bv 8 0) 50)
      (ja := []) (jp := []) (jn := []).
    all: try (symmetry; apply Z_to_bv_bv_unsigned).
    all: try reflexivity.
    all: try (let HH := fresh "HH" in intros HH; rewrite p6_args0 in HH; discriminate HH).
    all: try exact (u64_range _).
    all: try assumption.
    all: try (rewrite p6_Wc0, p6_D0; assumption).
    all: try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & _ & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  rewrite p6_fp0 in MU. rewrite p6_Wc0, p6_D0 in FP'. rewrite p6_ret0.
  replace (ret_pc (Z_to_bv 64 0x81bf8)) with (Z_to_bv 64 0x81bf8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact SW'|].
  split; [exact ST'|]. split; [exact AD' | exact FP'].
Qed.

(* ---- The segment lemma. ---- *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue
  BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 P1.
Import ListNotations.
(* FRA's FPState and getr are those of the image-A YK11; import it by its full name (as R8.v does). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* mkR_of made concrete, so that the run lemma's register file is p6_evt's mkR (Seg/P1.v p1_mkR_of). *)
Lemma p6_mkR_of : forall regs, Regs6ss.mkR_of regs = LF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
  (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A stack window shrunk from below (Seg/P7.v p7_stk_sub). *)
Lemma p6_stk_sub : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> stk rsegs m a hi.
Proof. intros m lo hi a (H1 & H2 & H) Ha. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

(* Two values of the same register, both in range, are equal (Seg/P7.v p7_rg_inj). *)
Lemma p6_rg_inj : forall regs r A A', rg regs r A -> rg regs r A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A = A'.
Proof.
  intros regs r A A' H H' HA HA'. unfold rg in *. rewrite H in H'.
  apply (f_equal (bv_unsigned (n:=64))) in H'. rewrite !MState.unsigned_lit in H' by lia. exact H'.
Qed.

(* The frame and its 392 shadow bytes, the two ranges the cut keeps apart from the class-1 side-stack bytes. *)
Definition p6_FRW (fr : Z) : list ivl := [(fr, fr + FRAME_BYTES); (Sfr fr, Sfr fr + FRAME_SHADOW)].

(* The write set is apart from the runtime's cells (all below 0x5fe000). *)
Lemma p6_rt_disjoint : forall S FS, ASAN_GT <= FS -> HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K ->
  AsanRTInv.rt_disjoint (p6_W S FS).
Proof.
  intros S FS HFS HS.
  assert (LOS : forall p, In p (p6_W S FS) -> 6283264 <= fst p) by (intros p Hp; exact (p6_W_los S FS p HFS HS Hp)).
  unfold AsanRTInv.rt_disjoint.
  repeat match goal with |- _ /\ _ => split end;
  apply p6_dj_lo; intros p Hp; pose proof (LOS p Hp);
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN in *; lia.
Qed.

(* The side stack's state after the run: the class-1 hint word and flag bytes come from the callee's fp, every
   other class's metadata is kept (the run writes only the class-1 metadata, the class-1 frames, the window and
   their shadow), and the region's presence and writability come from the callee's fs_place. *)
Lemma p6_fs_ok : forall S FS mem mem',
  0 < FS -> (FS + FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  (forall b, FS <= b < FS + FS_SIZE -> ASAN_K <= shadow_addr b < HIGHMEM_BEG) ->
  FS + FS_SIZE <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
  AC.a_fs_ok mem FS ->
  LF.munch (p6_W S FS) mem mem' -> LF.wmono rsegs mem mem' ->
  fs_place mem' FS ->
  bytes_at rsegs mem' (FS + 88) (le8 (Z_to_bv 64 20)) ->
  bytes_at rsegs mem' (FS + 96) [Z_to_bv 8 0] ->
  fp_cls mem' FS 1%nat ->
  AC.a_fs_ok mem' FS.
Proof.
  intros S FS mem mem' HFS0 HDI HSHB HFSS HSAP HOK MU WM HPL H88 H96 HCL.
  destruct HOK as (OK1 & OK2 & OK3 & OK4 & OK5).
  destruct HPL as (PL1 & PL2 & PL3 & PL4 & PL5).
  destruct HCL as (HC1 & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1).
  (* a metadata byte off the class-1 hint and flags is outside the write set *)
  assert (OUTM : forall x, FS <= x < FS + 36864 ->
            ~ (fs_hint FS 1 <= x < fs_hint FS 1 + 8) ->
            ~ (fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1) ->
            LF.outside (p6_W S FS) x).
  { intros x Hx H1 H2. apply p6_out.
    - unfold FS_SIZE in HFSS. lia.
    - apply p6_out_fpw; [exact HFS0 | right; split; [exact Hx | split; [exact H1 | exact H2]] |].
      intros b Hb. pose proof (HSHB b Hb) as Hsb.
      unfold FS_SIZE, LOWMEM_END, ASAN_K, HIGHMEM_BEG in *. lia.
    - intros [HA HB].
      assert (HD0 : 0 <= (S - REAC_CTRL_IDENTITY_REPLY_K) / 8)
        by (apply Z.div_pos; [unfold FS_SIZE in HFSS; lia | lia]).
      assert (HSS2 : shadow_addr S <= HIGHMEM_BEG).
      { unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *|- *.
        Z.div_mod_to_equations. lia. }
      unfold shadow_addr, ASAN_K in HA, HB, HSS2.
      unfold FS_SIZE, LOWMEM_END, HIGHMEM_BEG in HDI. unfold HIGHMEM_BEG in HSS2.
      destruct HDI as [HDlo|HDhi]; lia. }
  (* byte and word transport across the write set *)
  assert (MB : forall a, LF.outside (p6_W S FS) a -> 0 <= a < 2 ^ 64 ->
                 mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ho Ha. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact Ho. }
  assert (HFSb : FS + FS_SIZE <= 2 ^ 64).
  { pose proof (PL4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hap.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, FS_SIZE in *. lia. }
  split.
  { intros a Ha. destruct PL5 as (_ & _ & PL5).
    assert (Ha' : FS <= a < FS + FS_SIZE) by (unfold AC.FS_SIZE, FS_SIZE in *; lia).
    destruct (PL5 a Ha') as (Hv & b & Hb). split; [exact Hv|]. exists b. exact Hb. }
  split.
  { pose proof (bytes_at_le8_word rsegs mem' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW. }
  split.
  { destruct H96 as (_ & _ & H96). pose proof (H96 0%nat ltac:(cbn; lia)) as E.
    cbn [Z.of_nat nth_error] in E. rewrite Z.add_0_r in E. exact E. }
  split.
  { intros c Hc. destruct (Nat.eq_dec c 1) as [ -> | Hne ].
    - pose proof (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 HH1) as HW.
      exists (bv_unsigned h1). unfold AC.a_fs_hint, fs_hint in *. exact HW.
    - destruct (OK4 c Hc) as (h & Hh). exists h.
      intros k Hk. rewrite MB.
      + exact (Hh k Hk).
      + apply OUTM; unfold AC.a_fs_hint, fs_hint, fs_flag, fs_M in *;
          cbn [Z.of_nat Pos.of_succ_nat] in *;
          [ destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia .. ].
      + unfold AC.a_fs_hint in *. cbn [Z.of_nat] in *.
        destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]]; cbn [Z.of_nat Pos.of_succ_nat] in *;
          unfold FS_SIZE in *; lia. }
  { intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [ -> | Hne ].
    - destruct HF1 as (_ & _ & HF1).
      assert (Hjl : (Z.to_nat j < length flags1)%nat)
        by (unfold AC.a_fs_M, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *; lia).
      pose proof (HF1 (Z.to_nat j) Hjl) as E.
      rewrite Z2Nat.id in E by (unfold AC.a_fs_M in *; lia).
      destruct (nth_error flags1 (Z.to_nat j)) as [b|] eqn:En;
        [|exfalso; apply nth_error_None in En; lia].
      pose proof (proj1 (Forall_forall _ _) HFb1 b (@nth_error_In _ flags1 (Z.to_nat j) b En)) as Hb01.
      assert (Ea : AC.a_fs_flag FS 1 j = fs_flag FS 1 0 + j)
        by (unfold AC.a_fs_flag, fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      rewrite Ea. destruct Hb01 as [ -> | -> ]; [left | right]; exact E.
    - destruct (OK5 c j Hc Hj) as [E|E]; [left|right]; rewrite MB; try exact E;
        [ apply OUTM | | apply OUTM | ];
        unfold AC.a_fs_flag, AC.a_fs_M, fs_hint, fs_flag, fs_M, FS_SIZE in *;
        cbn [Z.of_nat Pos.of_succ_nat] in *;
        destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia. }
Qed.

(* ---- The call on the normalized memory (push 5d: no cut carries mem_inv). The transports below are Seg/A1.v's
   (a Theorem Labs lane, commit 22448a01112): the image's segments all end at or below ASAN_GT = 0x5fe000, so no byte at or
   above it is read-only and MemNorm.normalize leaves it alone; every fact the call reads or gives is about such
   bytes (the window, the side stack, the shadow) or is a bytes_at fact, which crosses mem_rel as it is. ---- *)

Definition p6_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma p6_rsegs_below_gt : p6_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p6_find_below : forall segs top x n s,
  p6_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold p6_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma p6_ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (p6_find_below sg 0x5fe000 x n s p6_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma p6_wview_rel_hi : forall m m0 a, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (p6_ro_addr_hi a Ha)). split; auto.
Qed.

Lemma p6_stk_rel : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (p6_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p6_stk_rel_back : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (p6_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p6_shadow_rw_rel : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a ltac:(unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG; lia))
    as (Hw & b & Hb). split.
  - apply (proj2 (p6_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p6_shadow_rw_back : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  destruct (H a Ha) as (Hw & b & Hb).
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. split.
  - apply (proj1 (p6_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma p6_addressable_rel : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma p6_addressable_back : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (MemNorm.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma p6_ba_rel : forall m m0 a bs, MemNorm.mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (MemNorm.bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma p6_ba_back : forall m m0 a bs, MemNorm.mem_rel rsegs m m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs.
Proof. intros m m0 a bs R H. exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma p6_cells_rel : forall m m0, MemNorm.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (p6_ba_rel m m0 a bs R ltac:(assumption)) end.
Qed.

(* asan_tls_cells is a conjunction of bytes_at facts and pure facts; both directions. *)
Lemma p6_tls_cells_iff : forall m m0 TP DT TS C T DB k, MemNorm.mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R. unfold asan_tls_cells.
  pose proof (fun a bs => MemNorm.bytes_at_rel rsegs m m0 a bs R) as E.
  split; intros H;
    repeat match goal with
           | H' : _ /\ _ |- _ => destruct H'
           | H' : exists _, _ |- _ => destruct H'
           end;
    repeat match goal with
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end;
    first [ apply E; eassumption | apply (proj2 (E _ _)); eassumption | eassumption ].
Qed.

Lemma p6_fs_place_rel : forall m m0 FS, MemNorm.mem_rel rsegs m m0 -> fs_place m FS -> fs_place m0 FS.
Proof.
  intros m m0 FS HR (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|].
  pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hap.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, FS_SIZE, ASAN_GT in *.
  exact (p6_stk_rel m m0 FS (FS + 11571200) HR ltac:(lia) ltac:(destruct Hap; lia) P5).
Qed.

Lemma p6_fs_place_back : forall m m0 FS, MemNorm.mem_rel rsegs m m0 -> fs_place m0 FS -> fs_place m FS.
Proof.
  intros m m0 FS HR (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|].
  pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hap.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, FS_SIZE, ASAN_GT in *.
  exact (p6_stk_rel_back m m0 FS (FS + 11571200) HR ltac:(lia) ltac:(destruct Hap; lia) P5).
Qed.

Lemma p6_fp_cls_iff : forall m m0 FS c, MemNorm.mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R. unfold fp_cls.
  pose proof (fun a bs => MemNorm.bytes_at_rel rsegs m m0 a bs R) as E.
  split; intros (Hc & h & fl & H1 & H2 & H3 & H4); split; try exact Hc; exists h, fl.
  - split; [exact (proj1 (E _ _) H1)|]. split; [exact (proj1 (E _ _) H2)|]. split; [exact H3 | exact H4].
  - split; [exact (proj2 (E _ _) H1)|]. split; [exact (proj2 (E _ _) H2)|]. split; [exact H3 | exact H4].
Qed.

Lemma p6_fp_rel : forall cs m m0 TP FS lo hi W D, MemNorm.mem_rel rsegs m m0 ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D R (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exists DT, TS, C, T, DB, k.
  split; [exact (proj1 (p6_tls_cells_iff m m0 TP DT TS C T DB k R) H1)|].
  split; [exact (p6_ba_rel m m0 _ _ R H2)|].
  split; [exact (p6_fs_place_rel m m0 FS R H3)|].
  split; [exact (p6_ba_rel m m0 _ _ R H4)|].
  split; [exact (p6_ba_rel m m0 _ _ R H5)|].
  split; [|exact H7].
  eapply Forall_impl; [|exact H6]. intros c Hc. exact (proj1 (p6_fp_cls_iff m m0 FS c R) Hc).
Qed.

Lemma p6_fp_back : forall cs m m0 TP FS lo hi W D, MemNorm.mem_rel rsegs m m0 ->
  fp cs m0 TP FS lo hi W D -> fp cs m TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D R (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exists DT, TS, C, T, DB, k.
  split; [exact (proj2 (p6_tls_cells_iff m m0 TP DT TS C T DB k R) H1)|].
  split; [exact (p6_ba_back m m0 _ _ R H2)|].
  split; [exact (p6_fs_place_back m m0 FS R H3)|].
  split; [exact (p6_ba_back m m0 _ _ R H4)|].
  split; [exact (p6_ba_back m m0 _ _ R H5)|].
  split; [|exact H7].
  eapply Forall_impl; [|exact H6]. intros c Hc. exact (proj2 (p6_fp_cls_iff m m0 FS c R) Hc).
Qed.

Lemma p6_reply_tls_rel : forall m m0 TP FS lo hi, MemNorm.mem_rel rsegs m m0 ->
  reac_ctrl_identity_reply_tls m TP FS lo hi -> reac_ctrl_identity_reply_tls m0 TP FS lo hi.
Proof.
  intros m m0 TP FS lo hi R H DT TS C T DB k Hc.
  exact (H DT TS C T DB k (proj2 (p6_tls_cells_iff m m0 TP DT TS C T DB k R) Hc)).
Qed.

(* p6_evt from ro_agree instead of mem_inv: the run on the normalized memory, carried back by
   MemNorm.evt_normalize (as P1's p1_evt_ro and Seg/A1.v's a1_req_evt). The mem_rel fact is posed after any
   step tactic (there is none here: p6_evt holds the steps). *)
Lemma p6_evt_ro : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S -> MemNorm.ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x81bf8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp E1 E2 HS Hpa Hpp H232 H224 Hmod HKS HST HRO HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS.
  assert (HKv : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  eapply LE.evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
    apply (p6_evt RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             Fr fc (MemNorm.normalize rsegs m) A S FS pa pp E1 E2 HS Hpa Hpp).
    + exact (p6_ba_rel m _ _ _ REL H232).
    + exact (p6_ba_rel m _ _ _ REL H224).
    + exact Hmod.
    + exact HKS.
    + exact (p6_stk_rel m (MemNorm.normalize rsegs m) (S - REAC_CTRL_IDENTITY_REPLY_K) S REL
               ltac:(lia) ltac:(lia) HST).
    + exact (MemNorm.mem_inv_normalize rsegs m).
    + exact (p6_cells_rel m _ REL HAC).
    + exact (p6_shadow_rw_rel m _ REL HSW).
    + exact Hlo.
    + exact Hhi.
    + exact (p6_addressable_rel m _ _ _ REL HADW).
    + exact (p6_addressable_rel m _ _ _ REL HADB).
    + exact (p6_ba_rel m _ _ _ REL HRB).
    + exact (p6_ba_rel m _ _ _ REL HRM).
    + exact (p6_ba_rel m _ _ _ REL HGC).
    + exact (p6_ba_rel m _ _ _ REL HC254).
    + exact (p6_ba_rel m _ _ _ REL HC255).
    + exact (p6_fp_rel _ m _ _ _ _ _ _ _ REL HFP).
    + exact (p6_reply_tls_rel m _ _ _ _ _ REL HTLS).
  - pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
    intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P10 & P22 & P25 & MU0 & WM0 & _ & SW0
               & ST0 & AD0
               & FP0) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P10|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p6_shadow_rw_back ms m0' Hmem SW0)|].
    split; [exact (p6_stk_rel_back ms m0' (S - REAC_CTRL_IDENTITY_REPLY_K) S Hmem ltac:(lia) ltac:(lia) ST0)|].
    split; [exact (p6_addressable_back ms m0' _ _ Hmem AD0)|].
    exact (p6_fp_back _ ms m0' _ _ _ _ _ _ Hmem FP0).
Qed.

(* Two word_mem values at the same address agree mod 2^64 (Seg/P2.v p2_wm_congr). *)
Lemma p6_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !YN2e.le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* The registered globals of frame_AG lie in [0x21140, 0x9f8e8) (a Theorem Labs lane's F37.v f37_ag_range): v1.9.0's
   round_trip.box .. CTRL_FRAMES + 264 (lib/A/FrameAPI.v, equal to the v1.9 ELF's asan_globals). *)
Lemma p6_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (lo, len) Hin). cbn [fst snd] in Hall.
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* Shadow addresses are monotone, strictly so across a granule. *)
Lemma p6_sh_le : forall a b, a <= b -> shadow_addr a <= shadow_addr b.
Proof. intros a b H. unfold shadow_addr. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma p6_sh_lt : forall a b, a + 8 <= b -> shadow_addr a < shadow_addr b.
Proof.
  intros a b H. unfold shadow_addr.
  pose proof (Z.div_le_mono (a + 8) b 8 ltac:(lia) H) as X.
  replace (a + 8) with (a + 1 * 8) in X by lia. rewrite Z.div_add in X by lia. lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ---- Both cuts are SlotInv's: the entry Inv_A81bd8 (the call's spills, window and side-stack premises) and the
   exit Inv_A81bf8 (with SlotInv's XC, which has no mem_inv). The frame's placement against the window and the side
   stack's bounds come from FRA (fra_frame, fra_app, a_laws_fs_place), not from the cut. ---- *)

(* addressable survives a run whose writes miss the shadow bytes of the range (fl_addressable with the weaker
   premise: only the shadow bytes of [p, p + n) need to be kept). *)
Lemma p6_addr_keep : forall W m m' p n,
  addressable m p n -> LF.munch W m m' ->
  (forall i, 0 <= i < n -> LF.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite LM.wa_unsigned by lia. exact (HW i Hi).
Qed.

(* A side-stack byte past the class-1 flags and off the class-1 frames is outside the class-1 bytes and their
   shadow: an app byte of the side stack is never in the shadow range of the class-1 frames. *)
Lemma p6_out_fs_hi : forall FS x, 0 < FS -> (FS + FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  FS + 28672 <= x < FS + FS_SIZE -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  LF.outside (fp_w [1%nat] FS) x.
Proof.
  intros FS x HFS HDI Hx Hnf. unfold fp_w, flat_map, fp_w1. cbn [app LF.outside].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B, FS_SIZE in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
  unfold shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia.
Qed.

(* FRA and ENT move across the call's writes (the stack window, the class-1 side-stack bytes and the shadow of the
   window); the frame, its shadow and everything at or above sp are outside those writes. *)
Lemma p6_fra_keep : forall g fr regs regs' mem mem' md FS lo hi WW DD,
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md ->
  fp_dj (p6_FRW fr) (fp_w [1%nat] FS) ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  LF.munch (p6_W (AC.aspZ regs) FS) mem mem' -> LF.wmono rsegs mem mem' ->
  ro_agree rsegs mem' -> shadow_rw mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
  fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS lo hi WW DD ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr [] regs' mem' md /\ ENT APIf g [] mem' md /\
  (forall x, fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
     LF.outside (p6_W (AC.aspZ regs) FS) x) /\
  (forall x, AC.aspZ regs <= x -> LF.outside (p6_W (AC.aspZ regs) FS) x).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs regs' mem mem' md FS lo hi WW DD HFRA HENT HFRWdj HFSw HFSr MU WM HRO' SW' ST' AD' HFP'
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof (Hapart REAC_CTRL_IDENTITY_REPLY_K
                ltac:(unfold REAC_CTRL_IDENTITY_REPLY_K, FN_STACK, AF.SLOT_STACK; lia)) as Hfrdj.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  rewrite Haspz in MU, ST', AD', Hfrdj |- *.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HKv : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HFSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HAFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HspB : sp <= APPMEM_END) by lia.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hstkhigh.
  destruct (p1_laws_fs_place APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as (HGTFS & HFShi & HFSmod & HFSapp).
  (* the side stack lies below stklo, which lies below the callee window *)
  assert (HFSsp : FS + FS_SIZE <= sp - REAC_CTRL_IDENTITY_REPLY_K) by lia.
  assert (HKR : HIGHMEM_BEG <= sp - REAC_CTRL_IDENTITY_REPLY_K) by lia.
  assert (HspR : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
  assert (HFS0 : 0 < FS) by (unfold AC.GT in HGTFS; lia).
  assert (HSHB : forall b, FS <= b < FS + FS_SIZE -> ASAN_K <= shadow_addr b < HIGHMEM_BEG).
  { intros b Hb. pose proof (shadow_of_app b (HFSapp b ltac:(lia))) as Hs.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, ASAN_K in *. lia. }
  assert (HDI : FS + FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as A1.
    pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* the window's shadow is shadow memory *)
  assert (WSH : forall y, shadow_addr (sp - REAC_CTRL_IDENTITY_REPLY_K) <= y < shadow_addr sp -> in_shadow y).
  { intros y Hy. right.
    unfold shadow_addr, ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END, REAC_CTRL_IDENTITY_REPLY_K in *.
    Z.div_mod_to_equations. lia. }
  (* low image bytes *)
  assert (OUTlo : forall x, 0 <= x < 6283264 -> LF.outside (p6_W sp FS) x).
  { intros x Hx. apply p6_out_lo. intros p Hp.
    pose proof (p6_W_los sp FS p ltac:(unfold AC.GT, ASAN_GT in *; lia) HKR Hp). lia. }
  (* bytes in high memory above the side stack and off the callee window *)
  assert (OUTh : forall x, HIGHMEM_BEG <= x -> FS + FS_SIZE <= x ->
            ~ (sp - REAC_CTRL_IDENTITY_REPLY_K <= x < sp) -> LF.outside (p6_W sp FS) x).
  { intros x H1 H2 H3. apply p6_out; [exact H3| |].
    - apply p6_out_fpw; [exact HFS0 | left; right; exact H2 |].
      intros b Hb Heq. pose proof (HSHB b Hb) as Hs. lia.
    - intros [HA HB].
      assert (shadow_addr sp <= HIGHMEM_BEG)
        by (unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *; Z.div_mod_to_equations; lia).
      lia. }
  assert (OUTsp : forall x, sp <= x -> LF.outside (p6_W sp FS) x)
    by (intros x Hx; apply OUTh; lia).
  (* the frame's 392 shadow bytes are shadow memory below HIGHMEM_BEG *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Ex : shadow_addr (fr + 8 * (x - Sfr fr)) = x).
    { unfold shadow_addr, Sfr, shadow_addr.
      replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with ((x - (fr / 8 + ASAN_K)) * 8 + fr) by lia.
      rewrite Z.div_add_l by lia. lia. }
    rewrite <- Ex. apply shadow_of_app. apply Hfrapp. lia. }
  (* the frame and its shadow *)
  assert (OUTfrw : forall x, fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
            LF.outside (p6_W sp FS) x).
  { intros x Hx. apply p6_out.
    - destruct Hx as [Hx|Hx].
      + destruct Hfrdj as [Hd|Hd]; lia.
      + pose proof (HshIS x Hx) as Hs.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs, HKR. lia.
    - destruct Hx as [Hx|Hx].
      + exact (fl_dj_out_r (p6_FRW fr) _ fr (fr + FRAME_BYTES) x HFRWdj (or_introl eq_refl) Hx).
      + exact (fl_dj_out_r (p6_FRW fr) _ (Sfr fr) (Sfr fr + FRAME_SHADOW) x HFRWdj (or_intror (or_introl eq_refl))
                 Hx).
    - intros Hc. destruct Hx as [Hx|Hx].
      + exact (AsanRTFacts.app_not_shadow x (Hfrapp x Hx) (WSH x Hc)).
      + assert (HD1 : (fr + FRAME_BYTES) / 8 = fr / 8 + FRAME_SHADOW)
          by (rewrite HFBv, HFSv; replace (fr + 3136) with (fr + 392 * 8) by lia; rewrite Z.div_add by lia;
              reflexivity).
        unfold Sfr, shadow_addr in Hx, Hc.
        destruct Hfrdj as [Hd|Hd].
        * pose proof (Z.div_le_mono (fr + FRAME_BYTES) (sp - REAC_CTRL_IDENTITY_REPLY_K) 8 ltac:(lia) Hd) as HM1.
          rewrite HD1 in HM1. lia.
        * pose proof (Z.div_le_mono sp fr 8 ltac:(lia) Hd) as HM2. lia. }
  (* the heap invariant, ownership and the stack bounds across the writes *)
  pose proof (p1_fs_ok_of_state APIf ([] ++ g_H g) mem md FS HAH HFSw HFSr) as HFSok.
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (HFSok' : AC.a_fs_ok mem' FS).
  { destruct HFP' as (DT & TS & C & T & DB & k & HTc & HTP' & HPl' & H88' & H96' & HCL' & _ & _ & _ & _).
    apply (p6_fs_ok sp FS mem mem' HFS0 HDI HSHB HFSsp HspB HFSok MU WM HPl' H88' H96' (Forall_inv HCL')). }
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
            ~ (FS <= a < FS + AC.FS_SIZE) ->
            ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
            mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hnok Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
    apply p6_out.
    - intros Hw. apply Hnok. right. left. lia.
    - apply p6_out_fpw; [exact HFS0 | |].
      + left. destruct (Z.lt_ge_cases a FS) as [H|H]; [left; exact H|]. right. lia.
      + intros b Hb Heq. apply Hnsh. exists b. split; [lia | exact Heq].
    - intros Hc. apply Hnok. right. right. right. exists (8 * (a - ASAN_K)).
      split.
      + unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia.
      + right. left.
        unfold shadow_addr, ASAN_K, APPMEM_END in *.
        Z.div_mod_to_equations. lia. }
  destruct (p1_laws_fs_store APIf ([] ++ g_H g) mem mem' md FS HAH HFSw HFSr Hmc Hwrit HFSok')
    as (HAH' & Hown' & HSTKeq & HSTKhi').
  (* the runtime invariant *)
  assert (HRT' : AsanRTInv.RT sp mem' md).
  { apply (AsanRTInv.RT_meta_write sp sp mem mem' md md (p6_W sp FS) HRT MU WM
      (p6_rt_disjoint sp FS ltac:(unfold AC.GT, ASAN_GT in *; lia) HKR)).
    intros a Hin. destruct (SW' a Hin) as (_ & b & Hb). exists b. exact Hb. }
  (* the image bytes below 0x5fe000 are kept *)
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (OUTlo x ltac:(lia)). }
  (* a byte of the side stack past the class-1 flags and off the class-1 frames is outside the writes *)
  assert (OUTfs : forall x, FS + 28672 <= x < FS + FS_SIZE -> ~ (FS + 1085440 <= x < FS + 2134016) ->
            LF.outside (p6_W sp FS) x).
  { intros x Hx Hnf. apply p6_out.
    - lia.
    - exact (p6_out_fs_hi FS x HFS0 HDI Hx Hnf).
    - intros Hc. exact (AsanRTFacts.app_not_shadow x (HFSapp x ltac:(lia)) (WSH x Hc)). }
  (* FSREC across the call: its tp word is low image, its flag byte and the slot's last word are side-stack bytes
     of class 6, past the class-1 flags and above the class-1 frames *)
  assert (HRECK : FSREC fr mem -> FSREC fr mem').
  { intros (FS6 & j & Htp6 & HFS6r & Hj & Hfr6 & Hflag & Htail).
    assert (EFS : FS6 = FS).
    { pose proof (p6_wm_congr mem _ FS6 FS Htp6 HFSw) as X. rewrite !Z.mod_small in X by lia. exact X. }
    subst FS6.
    assert (HB6 : fs_B 6 = 4096) by reflexivity. assert (HM6 : fs_M 6 = 256) by reflexivity.
    assert (Hfl : fs_flag FS 6 j = FS + 36352 + j) by (unfold fs_flag; cbn; lia).
    assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr6; unfold fs_frame, fs_B; cbn; lia).
    rewrite HM6 in Hj.
    exists FS, j.
    split.
    { intros k Hk. rewrite KBlo; [exact (Htp6 k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
                                  | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
    split; [exact HFS6r|].
    split; [rewrite HM6; exact Hj|].
    split; [exact Hfr6|].
    split.
    { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. apply OUTfs; lia. }
    { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. apply OUTfs; lia. } }
  (* ENT: the call writes no entry block (they are below stklo and off the side stack), no image byte, nothing at
     or above S and no shadow byte of those *)
  assert (HENT' : ENT APIf g [] mem' md).
  { eapply ent_munch with (W := p6_W sp FS);
      [exact HENT | exact HAH
      | first [exact MU | exact (proj1 (fr_munch_ul _ mem mem') MU)
                        | exact (proj2 (fr_munch_ul _ mem mem') MU)]
      | | exact HSTKeq | exact HSTKhi' | exact (fun a _ Ho => proj2 (Hown' a) Ho)].
    (* ent_munch states outside in Tac_slot's flavour; fr_outside_lib brings it to this file's LF.outside *)
    intros x Hk. first [apply (proj2 (fr_outside_lib _ x)) | idtac].
    destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
    - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (p1_laws_blocks APIf ([] ++ g_H g) mem md q k HAH Hin) as (Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      apply p6_out.
      + lia.
      + apply p6_out_fpw; [exact HFS0 | left |].
        * destruct (Z.lt_ge_cases (q + i) FS) as [H|H]; [left; exact H|]. right.
          destruct (Z.lt_ge_cases (q + i) (FS + FS_SIZE)) as [H'|H']; [|exact H'].
          exfalso. apply Hnfs. exists FS. split; [exact HFSr|]. split; [exact HFSw|]. lia.
        * intros b0 Hb0 Heq. apply (AsanRTFacts.app_not_shadow (q + i) Happq). rewrite Heq.
          apply shadow_of_app. apply HFSapp. lia.
      + intros Hc. exact (AsanRTFacts.app_not_shadow (q + i) Happq (WSH (q + i) Hc)).
    - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg, HGTFS.
      assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
      apply p6_out.
      + lia.
      + apply p6_out_fpw; [exact HFS0 | left; left; lia |].
        intros b0 Hb0 Heq. apply (AsanRTFacts.app_not_shadow x Happx). rewrite Heq.
        apply shadow_of_app. apply HFSapp. lia.
      + intros Hc. exact (AsanRTFacts.app_not_shadow x Happx (WSH x Hc)).
    - apply OUTsp. lia.
    - assert (Hb0 : 0 <= b)
        by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
      assert (Happb : app_mem b).
      { destruct Hor as [Hi|Hr];
          [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
          |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
      pose proof (shadow_of_app b Happb) as Hsb.
      pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
      apply p6_out.
      + unfold HIGHMEM_BEG in HKR. lia.
      + apply p6_out_fpw; [exact HFS0 | left |].
        * unfold LOWMEM_END, HIGHMEM_BEG in HDI. destruct HDI as [HD|HD]; [right | left]; lia.
        * intros b0 Hb0' Heq. destruct Hor as [Hi|Hr].
          -- pose proof (img_below_GT b Hi) as X. unfold AC.GT in X, HGTFS.
             revert Heq. unfold shadow_addr. clear - X HGTFS HFSmod Hb0' Hb0. Z.div_mod_to_equations. lia.
          -- pose proof (p6_sh_lt b0 b ltac:(lia)) as X. lia.
      + intros [Hc1 Hc2]. destruct Hor as [Hi|Hr].
        * pose proof (img_below_GT b Hi) as X. unfold AC.GT in X.
          pose proof (p6_sh_lt b (sp - REAC_CTRL_IDENTITY_REPLY_K) ltac:(unfold HIGHMEM_BEG in HKR; lia)). lia.
        * pose proof (p6_sh_le sp b ltac:(lia)). lia.
    - (* frame batch 2 item 9 (Tac_slot ent_kept's fifth case): the shadow byte of an entry block's byte. The block
         byte is app memory below stklo <= sp - K and off the side stack, so its shadow byte is outside the call's
         writes (p6_blk_out, as for PRO's input block). *)
      destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
      destruct (p1_laws_blocks APIf ([] ++ g_H g) mem md q k HAH Hin) as (Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      refine (proj2 (p6_blk_out sp FS (q + i) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
                       HFS0 HFSmod HFSapp Happq ltac:(lia) ltac:(lia) HKR
                       ltac:(first [lia | unfold APPMEM_END in *; lia]) Hspm _)).
      intros Hc. apply Hnfs. exists FS. split; [exact HFSr|]. split; [exact HFSw | exact Hc]. }
  split.
  { exists A, sp, s5.
    split; [exact HRT'|].
    split; [exact HAH'|].
    split; [exact HRO'|].
    split.
    { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
      - destruct Hcse as (Hthrm & Hlockm). split.
        + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
          * lia.
          * rewrite Hthr in Hx. cbn in Hx. lia.
        + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
          * lia.
          * rewrite Hlock in Hx. cbn in Hx. lia.
      - intros k Hk. rewrite KBlo.
        + exact (Hohd k Hk).
        + rewrite Hhead. lia.
        + rewrite Hhead. lia. }
    split; [exact Hhalt|].
    split.
    { intros a Hin. rewrite KBlo.
      - exact (Hgimg a Hin).
      - destruct Hin as (lo0 & len0 & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
      - destruct Hin as (lo0 & len0 & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
    split; [rewrite E2; exact Hr2|].
    split; [exact Hspm|].
    split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
    split; [rewrite HSTKeq; exact Hstklo|].
    split; [rewrite E4; exact Hr4|].
    split; [unfold rg in *; rewrite E8; exact Hr8|].
    split; [unfold rg in *; rewrite E9; exact Hr9|].
    split; [rewrite E3; exact Hr3|].
    split; [unfold rg in *; rewrite E19; exact Hr19|].
    split; [unfold rg in *; rewrite E26; exact Hr26|].
    split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|].
    split; [exact Hspa|]. split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
      rewrite length_le8. intros x Hx. apply OUTsp. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
      rewrite length_le8. intros x Hx. apply OUTsp. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
      rewrite length_le8. intros x Hx. apply OUTsp. lia. }
    split.
    { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
      - left. split; [exact H0|]. split; [exact Hspfr|]. intros a Ha. rewrite HSTKeq. exact (Hreal a Ha).
      - right. split; [exact Hfr0|]. split.
        + intros FSb Hw HFSbr. apply (Hfsb FSb); [|exact HFSbr].
          intros k Hk. rewrite <- KBlo; [exact (Hw k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
                                         | unfold AC.as_tp, AC.ASYMS; cbn; lia].
        + split; [|exact (HRECK Hrec)].
          intros a Ha. destruct (Hfs a Ha) as (FSb & HFSbr & Hw & Hlo0 & Hhi0).
          exists FSb. split; [exact HFSbr|]. split; [|split; [exact Hlo0 | exact Hhi0]].
          intros k Hk. rewrite KBlo; [exact (Hw k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
                                      | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
      rewrite length_le8. intros x Hx. apply OUTfrw. left. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
      rewrite length_le8. intros x Hx. apply OUTfrw. left. lia. }
    split.
    { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
      eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. apply OUTfrw. right. lia. }
    split.
    { apply (fl_stk (p6_W sp FS) mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx. destruct (Z.lt_ge_cases x (sp - REAC_CTRL_IDENTITY_REPLY_K)) as [Hlt|Hge].
      - left. apply OUTh; lia.
      - destruct (Z.lt_ge_cases x sp) as [Hlt2|Hge2].
        + right. destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
        + left. apply OUTsp. lia. }
    split.
    { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      apply OUTsp. lia. }
    split.
    { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
    split.
    { (* frame_AG: its globals end far below the side stack and the window, so their shadow bytes are kept *)
      intros a Hin. apply (p6_addr_keep (p6_W sp FS) mem mem' a 1 (HAG a Hin) MU).
      intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
      pose proof (p6_ag_range a Hin) as Har. unfold AC.GT in HGTFS.
      assert (Hsa : shadow_addr a < shadow_addr FS) by (apply p6_sh_lt; lia).
      assert (Hsa0 : ASAN_K <= shadow_addr a) by (unfold shadow_addr; pose proof (Z.div_pos a 8); lia).
      apply p6_out.
      - unfold shadow_addr, ASAN_K, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia.
      - apply p6_out_fpw; [exact HFS0 | left |].
        + unfold shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG in *. destruct HDI as [HD|HD];
            [right | left]; Z.div_mod_to_equations; lia.
        + intros b0 Hb0 Heq. pose proof (p6_sh_lt a b0 ltac:(lia)). lia.
      - intros [Hc1 Hc2]. pose proof (p6_sh_lt a (sp - REAC_CTRL_IDENTITY_REPLY_K)
                                        ltac:(unfold HIGHMEM_BEG in HKR; lia)). lia. }
    split.
    { (* the slot window outside the frame stays addressable: the callee's own window by its post, the rest
         because the call writes neither its shadow nor (granule-aligned window) its neighbours' *)
      intros a H1 H2.
      destruct (Z.lt_ge_cases a (sp - REAC_CTRL_IDENTITY_REPLY_K)) as [Hlt|Hge];
        [|destruct (Z.lt_ge_cases a sp) as [Hlt2|Hge2]].
      - apply (p6_addr_keep (p6_W sp FS) mem mem' a 1 (HWA a H1 H2) MU).
        intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
        assert (Hap : app_mem a) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
        pose proof (shadow_of_app a Hap) as Hsa.
        pose proof Hsa as Hsa'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsa'.
        apply p6_out.
        + unfold HIGHMEM_BEG in HKR. lia.
        + apply p6_out_fpw; [exact HFS0 | left |].
          * unfold LOWMEM_END, HIGHMEM_BEG in HDI. destruct HDI as [HD|HD]; [right | left]; lia.
          * (* a is at or above the side stack's end, a 4096-aligned bound, so its granule is past every
               side-stack byte's *)
            intros b0 Hb0 Heq. assert (HFSa : FS + FS_SIZE <= a) by lia.
            revert Heq. unfold shadow_addr. clear - HFSa Hb0 HFSmod HFSZ. Z.div_mod_to_equations. lia.
        + intros [Hc1 Hc2].
          assert (Hm16 : (sp - REAC_CTRL_IDENTITY_REPLY_K) mod 8 = 0).
          { rewrite HKv. pose proof Hspm as X. Z.div_mod_to_equations. lia. }
          (* a is below the granule-aligned window start, so its shadow byte is below the window's shadow *)
          revert Hc1. unfold shadow_addr. clear - Hlt Hm16.
          Z.div_mod_to_equations. lia.
      - replace a with ((sp - REAC_CTRL_IDENTITY_REPLY_K) + (a - (sp - REAC_CTRL_IDENTITY_REPLY_K))) by lia.
        apply (addressable_sub mem' (sp - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K
                 (a - (sp - REAC_CTRL_IDENTITY_REPLY_K)) 1 AD'); lia.
      - apply (p6_addr_keep (p6_W sp FS) mem mem' a 1 (HWA a H1 H2) MU).
        intros i Hi. assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
        assert (Hap : app_mem a) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
        pose proof (shadow_of_app a Hap) as Hsa.
        pose proof Hsa as Hsa'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsa'.
        apply p6_out.
        + unfold HIGHMEM_BEG in HKR. lia.
        + apply p6_out_fpw; [exact HFS0 | left |].
          * unfold LOWMEM_END, HIGHMEM_BEG in HDI. destruct HDI as [HD|HD]; [right | left]; lia.
          * intros b0 Hb0 Heq. pose proof (p6_sh_lt b0 a ltac:(lia)). lia.
        + intros [Hc1 Hc2]. pose proof (p6_sh_le sp a Hge2). lia. }
    split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
    split; [exact Hhb | exact Hlive]. }
  split; [exact HENT'|].
  split; [exact OUTfrw | exact OUTsp].
Qed.

Hypothesis RPL : reac_ctrl_identity_reply_contract.

Lemma seg_P6 : Hcut B APIf ra (Inv_A81bf8 B APIf ra) -> Hcut B APIf ra (Inv_A81bd8 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & HCUR & HPRO & HSP144 & HAD17 & HSP208 &
    HADF & HADI & HIDB & HFGB &
    (HA280 & HADC) &
    (A & pa & pp & f & HA9 & HAr & Hpa & Hpp & H232 & H224 & H208 & HADW & HADB & HAF)).
  (* the reply call's side-stack package is on no cut: FRA gives it (Tac_fsfree.inv_a81bd8_pkg) *)
  destruct (inv_a81bd8_pkg B APIf ra g fr [] regs mem md HFRA) as (FS & HFRWdj & HFP & HTLS).
  subst c. rewrite SEGS.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HKv : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HspR : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
  assert (HA0r : 0 <= A0 < 2 ^ 64) by (unfold APPMEM_END in HAPP; lia).
  assert (EA : A = A0) by (exact (p6_rg_inj regs 9 A A0 HA9 Hr9 HAr HA0r)).
  subst A.
  (* the spill [A1 + 144] of the cut is at FRA's spill base: A1 = A0 (A1 mod 2^64 = A0, both spills in range) *)
  destruct HSP144 as (A1 & HrA1 & HQ144).
  assert (HA1 : A1 = A0).
  { unfold rg in HrA1, Hr9.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HrA1)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A0 (2 ^ 64)) in E0 by lia.
    pose proof HQ144 as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    pose proof Hspill as HSb. unfold q64 in HSb. apply bytes_at_bound in HSb. rewrite length_le8 in HSb.
    clear - E0 HQb HSb. revert E0 HQb HSb. Z.div_mod_to_equations. lia. }
  subst A1.
  (* push 14D: the spill [A2 + 192] = fragb fr likewise *)
  destruct HSP208 as (A2 & HrA2 & HQ208).
  assert (HA2 : A2 = A0).
  { unfold rg in HrA2, Hr9.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HrA2)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A0 (2 ^ 64)) in E0 by lia.
    pose proof HQ208 as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    pose proof Hspill as HSb. unfold q64 in HSb. apply bytes_at_bound in HSb. rewrite length_le8 in HSb.
    clear - E0 HQb HSb. revert E0 HQb HSb. Z.div_mod_to_equations. lia. }
  subst A2.
  (* the side-stack base of fp *)
  pose proof HFP as (DT & TS & C & T & DB & k & HTc & HTPb & HPl & H88 & H96 & HCL &
    HFSlo & HFSapp0 & HWd & HDd).
  assert (HFS0 : 0 < FS) by (destruct HPl as (P1 & _); lia).
  assert (HFSr : 0 <= FS < 2 ^ 64).
  { destruct HPl as (P1 & P2 & P3 & P4 & P5).
    pose proof (P4 FS ltac:(unfold FS_SIZE; lia)) as Hap.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. lia. }
  assert (HFSw : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { pose proof (bytes_at_le8_word rsegs mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 FS) HTPb) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW. }
  (* the runtime cells the callee reads *)
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL0.
  pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCF0.
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (Hsub : forall (m0 : word -> option byte) (a : Z) bs (k0 j0 : nat),
            bytes_at rsegs m0 a bs -> (k0 + j0 <= length bs)%nat ->
            bytes_at rsegs m0 (a + Z.of_nat k0) (firstn j0 (skipn k0 bs))).
  { intros m0 a bs k0 j0 (Ha & HL & H) Hkj.
    assert (Lf : length (firstn j0 (skipn k0 bs)) = j0) by (rewrite length_firstn, length_skipn; lia).
    split; [lia|]. split; [rewrite Lf; lia|].
    intros i Hi. rewrite Lf in Hi.
    replace (a + Z.of_nat k0 + Z.of_nat i) with (a + Z.of_nat (k0 + i)) by lia.
    rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i j0) as [_|Cc]; [|lia].
    rewrite nth_error_skipn. reflexivity. }
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (Hsub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14%nat 1%nat HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (Hsub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15%nat 1%nat HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (Etp : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS).
  { rewrite Hr4. apply MState.unsigned_lit. unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  (* the window [sp - K, sp) is above stklo and inside the entry-anchored slot window *)
  assert (HKRlo : HIGHMEM_BEG <= sp - REAC_CTRL_IDENTITY_REPLY_K) by lia.
  assert (HspB : sp <= APPMEM_END) by lia.
  assert (HSTw : stk rsegs mem (sp - REAC_CTRL_IDENTITY_REPLY_K) sp).
  { destruct Hwin as (Hw0 & Hw1 & Hw). split; [lia|]. split; [lia|]. intros x Hx. apply Hw. lia. }
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81bd8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81bf8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (-1) /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       LF.munch (p6_W sp FS) mem mem' /\ LF.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       shadow_rw mem' /\ stk rsegs mem' (sp - REAC_CTRL_IDENTITY_REPLY_K) sp /\
       addressable mem' (sp - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
       fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - REAC_CTRL_IDENTITY_REPLY_K) sp
          [(sp - REAC_CTRL_IDENTITY_REPLY_K, sp)] [])
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite p6_mkR_of.
    eapply LE.evt_mono.
    + apply (p6_evt_ro RPL) with (A := A0) (S := sp) (FS := FS) (pa := pa) (pp := pp).
      * unfold rg in Hr9. exact Hr9.
      * exact Hr2.
      * exact HspR.
      * exact Hpa.
      * exact Hpp.
      * exact H232.
      * exact H224.
      * exact Hspm.
      * unfold REAC_CTRL_IDENTITY_REPLY_K, HIGHMEM_BEG in *. lia.
      * exact HSTw.
      * exact Hro.
      * exact HACm.
      * exact HSWm.
      * exact HKRlo.
      * exact HspB.
      * rewrite <- Haspz. exact HADW.
      * exact HADB.
      * exact HRBc.
      * exact HRMc.
      * exact HGOTCF.
      * exact HC254.
      * exact HC255.
      * rewrite Etp, <- Haspz. exact HFP.
      * rewrite Etp, <- Haspz. exact HTLS.
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P10 & P22 & P25 & MUq & WMq & ROq & SWq
                  & STq & ADq & FPq).
      exists R, (Z_to_bv 64 0x81bf8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P10|].
      split; [exact P22|]. split; [exact P25|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq|]. split; [exact SWq|].
      split; [exact STq|]. split; [exact ADq|]. rewrite Etp in FPq. exact FPq.
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K10 & K22 & K25 & MU & WM & RO' & SW' & ST' & AD' & FP')
      Hreg Hmat.
    subst pc'.
    rewrite <- Haspz in MU, ST', AD', FP'.
    destruct (p6_fra_keep g fr regs regs' mem mem' md FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K)
      (AC.aspZ regs) [(AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K, AC.aspZ regs)] []
      HFRA HENT HFRWdj HFSw HFSr MU WM RO' SW' ST' AD' FP'
      ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
      ltac:(rewrite Hreg; exact K8) ltac:(rewrite Hreg; exact K9) ltac:(rewrite Hreg; exact K19)
      ltac:(rewrite Hreg; exact K26)) as (HFRAm & HENTm & OUTfrw & OUTsp).
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENTm | exact Hmat]).
    assert (E9' : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    (* push 13: PRO (pro_run: the spills are above sp, our[]'s shadow byte S(fr) + 328 is a frame-shadow byte, the
       input block and its shadow bytes are off the write set, p6_blk_out) *)
    assert (HPRO' : PRO g fr regs' mem').
    { apply (pro_run g fr regs regs' mem mem' (p6_W (AC.aspZ regs) FS) A0 HPRO Hr9 ltac:(lia)
               ltac:(unfold APPMEM_END in HAPP; lia) ltac:(clear - Hfrm; Z.div_mod_to_equations; lia) E9' MU).
      - intros x Hx. apply OUTsp. lia.
      - apply OUTfrw. right. lia.
      - intros Hn Hin i Hi.
        destruct (p1_laws_blocks APIf ([] ++ g_H g) mem md (g_p g) (g_n g) HAH Hin) as (Hpn & Hbody).
        destruct (Hbody (g_p g + i) ltac:(lia)) as (Hap & Hnfs).
        destruct HPl as (Pl1 & Pl2 & Pl3 & Pl4 & Pl5).
        apply (p6_blk_out (AC.aspZ regs) FS (g_p g + i) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
                 HFS0 Pl2 Pl4 Hap); [lia | lia | lia | lia | rewrite Haspz; exact Hspm |].
        intros Hc. apply Hnfs. exists FS. split; [exact HFSr|]. split; [exact HFSw | exact Hc]. }
    assert (HIexit : Inv_A81bf8 B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x81bf8) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hgn|].
      split.
      { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
        rewrite OUR_length. intros x Hx. apply OUTfrw. left. lia. }
      split.
      { (* CUR: the call keeps s6 (x22) and s9 (x25) *)
        destruct HCUR as (Hc0 & H22 & H25). split; [exact Hc0|]. unfold rg in *.
        split; [rewrite Hreg, K22; exact H22 | rewrite Hreg, K25; exact H25]. }
      split; [exact HPRO'|].
      split.
      { (* the spill [A + 144] = fr + 2688: s1 is kept and the slot is above sp, outside the call's writes *)
        exists A0. split; [unfold rg in *; rewrite E9'; exact Hr9|].
        unfold q64 in *. eapply fl_bytes; [exact HQ144 | exact MU |].
        rewrite length_le8. intros x Hx. apply OUTsp. lia. }
      split.
      { (* the 17 bytes at fr + 2691 stay addressable: their shadow bytes S(fr) + 336 .. 338 are frame shadow
           bytes, outside the call's writes *)
        apply (p6_addr_keep (p6_W (AC.aspZ regs) FS) mem mem' (fr + 2691) 17 HAD17 MU).
        intros i Hi. apply OUTfrw. right.
        assert (Hs : Sfr fr + 336 <= shadow_addr (fr + 2691 + i) <= Sfr fr + 338)
          by (clear - Hfrm Hi; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
        lia. }
      split.
      { (* push 14D: the spill [A + 192] = fragb fr, above sp, outside the call's writes *)
        exists A0. split; [unfold rg in *; rewrite E9'; exact Hr9|].
        unfold q64 in *. eapply fl_bytes; [exact HQ208 | exact MU |].
        rewrite length_le8. intros x Hx. apply OUTsp. lia. }
      split.
      { (* push 14D: (fragb fr, 72) and (fr + 2688, 38) stay addressable: their shadow bytes S(fr) + 346 .. 354 /
           S(fr) + 336 .. 340 are frame shadow bytes, outside the call's writes *)
        apply (p6_addr_keep (p6_W (AC.aspZ regs) FS) mem mem' (fragb fr) 72 HADF MU).
        intros i Hi. apply OUTfrw. right.
        assert (Hs : Sfr fr + 346 <= shadow_addr (fragb fr + i) <= Sfr fr + 354)
          by (clear - Hfrm Hi; unfold fragb, Sfr, shadow_addr; Z.div_mod_to_equations; lia).
        lia. }
      split.
      { apply (p6_addr_keep (p6_W (AC.aspZ regs) FS) mem mem' (fr + 2688) 38 HADI MU).
        intros i Hi. apply OUTfrw. right.
        assert (Hs : Sfr fr + 336 <= shadow_addr (fr + 2688 + i) <= Sfr fr + 340)
          by (clear - Hfrm Hi; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
        lia. }
      split.
      { (* IDBe: the identity record [fr + 2688, fr + 2726) is a frame byte range, outside the call's writes *)
        unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
        assert (HID0 : length RcIdentModel.ID0 = 38%nat) by reflexivity.
        rewrite HID0. intros x Hx. apply OUTfrw. left. lia. }
      split.
      { (* FGBe: the fragment scratch [fr + 2768, fr + 2840), the same way *)
        unfold FGBe in *. eapply fl_bytes; [exact HFGB | exact MU |].
        rewrite z72_length. intros x Hx. apply OUTfrw. left. lia. }
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split.
      { exists f, A0. split; [unfold rg in *; rewrite E9'; exact Hr9|].
        unfold q64 in *. eapply fl_bytes; [exact H208 | exact MU |].
        rewrite length_le8. intros x Hx. apply OUTsp. lia. }
      split; [split|].
      { intros A1 HA1 HA1r.
        assert (E1 : A1 = A0).
        { apply (p6_rg_inj regs' 9 A1 A0 HA1); [unfold rg in *; rewrite E9'; exact Hr9 | exact HA1r | exact HA0r]. }
        subst A1. unfold q64 in *.
        eapply fl_bytes; [exact (HA280 A0 Hr9 HA0r) | exact MU |].
        rewrite length_le8. intros x Hx. apply OUTsp. lia. }
      { apply (p6_addr_keep (p6_W (AC.aspZ regs) FS) mem mem' (fr + 3040) 1 HADC MU).
        intros i Hi.
        assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
        assert (Esh : shadow_addr (fr + 3040) = Sfr fr + 380).
        { unfold shadow_addr, Sfr, shadow_addr.
          replace (fr + 3040) with (fr + 380 * 8) by lia. rewrite Z.div_add by lia. lia. }
        rewrite Esh. apply OUTfrw. right. lia. }
      { (* round 4: first.sroa.7's 35 bytes at fr + 2880 stay addressable: their shadow bytes S(fr) + 360 .. 364
           are frame shadow bytes, outside the call's writes *)
        apply (p6_addr_keep (p6_W (AC.aspZ regs) FS) mem mem' (fr + 2880) 35 HAF MU).
        intros i Hi. apply OUTfrw. right.
        assert (Hs : Sfr fr + 360 <= shadow_addr (fr + 2880 + i) <= Sfr fr + 364)
          by (clear - Hfrm Hi; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
        lia. } }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
