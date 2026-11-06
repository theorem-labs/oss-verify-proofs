(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module paths, module names, addresses and numbers changed; 535 of its 675 lines of code are new or changed and 790 lines of the source are left out. *)
(* Segment P6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81d68, 0x81d7c], 6
   instructions, cut Inv_B81d68 (v1.9 pc 0x81d68) -> cut Inv_B81d80 (v1.9 pc 0x81d80) (plan-asan-ubsan.md section 2,
   row P6; section 4, REPLY = reac_ctrl_identity_reply, 0x848fc).  rule 24: no function proved (a slot segment).
     0x81d68 li a0,0; 0x81d6c li a1,0        the record pointer and the length are 0;
     0x81d70 ld a2,88(s1); 0x81d74 ld a3,80(s1); 0x81d78 ld a4,72(s1)   the three reply cells;
     0x81d7c jal reac_ctrl_identity_reply.
   With a0 = 0 the callee refuses (reply_args 0 _ _ _ = false): it returns -1, writes only its own stack window
   [sp - 9072, sp), the class-1 bytes of the side stack for frames and the shadow bytes of that window, and keeps
   the callee-saved registers.  The range has no instrumented shadow check and no UBSan trap.
   The callee's side-stack package is NOT carried by a cut (adopt FSFREE): the call site builds it from FRA with
   Seg/Tac_fsfree.v fra_fp, and Tac_fsfree.fp_post_fs_ok gives the side stack's state after the call, which the
   side-stack store law (SlotInv.lw_fs_store) turns into the heap invariant.  FRA then moves by Tac_bp.bp_fra (the
   write set holds shadow bytes, so RT moves by RT_meta_write) and ENT by Tac_bp6.bp6_ent_W (the write set holds
   the shadow of the window and side-stack bytes).
   The entry cut is SlotInv.v's official Inv_B81d68, which carries the conjuncts the exit Inv_B81d80 asks for:
     spill regs m 64 (fr + 3056)   the 32-byte scratch pointer (stored 0x8153c sd a1,64(s1); read by P8 at
                                   0x81db0); no instruction of this segment writes it;
     XC fr regs m                  s8 = fr + 3040, the code byte's pointer, and that byte addressable;
     PL0 g fr regs m               the turn-0 frame-loop facts (CUR at c0 in s7 / s9, the identity record ID0 at
                                   fr + 2688, the fragment record z72 at fr + 2768, RAD, the record-pointer spills
                                   [A + 176] / [A + 208] and the turn-0 first-fragment state FSj g fr 0 at
                                   fr + 2880) that P7 .. P12 pass to the frame loop; the callee writes none of
                                   their bytes or shadow bytes;
     addressable m KNC.KIND_NAME 112   the kind-name table, whose shadow the callee does not write;
   and both cuts carry PRO; the run keeps [A, A + 448) and our[]'s shadow byte (Tac_bp.bp_PRO_keep).  v1.9.0
   against the patched image: the pcs move +0x88, the reply cells are [A + 88] / [A + 80] / [A + 72] (patched
   [A + 96] / [A + 88] / [A + 80]), the fragment pointer [A + 208] (patched [A + 240]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP asan_stack_malloc_c
  reac_ctrl_identity_reply_c reac_ctrl_parse_c memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
Import ListNotations.
Open Scope Z_scope.

(* ---- the refused call: reply_args is false, so the result is -1 and the footprint is the window alone ---- *)
Lemma p6_args0 : forall pa pp pn, reply_args 0 pa pp pn = false.
Proof. intros pa pp pn. unfold reply_args. reflexivity. Qed.

Lemma p6_ret0 : forall len pa pp pn g, reply_ret 0 len pa pp pn g = -1.
Proof. intros len pa pp pn g. unfold reply_ret. rewrite p6_args0. reflexivity. Qed.

Lemma p6_ok0 : forall len pa pp pn g, reply_ok 0 len pa pp pn g = false.
Proof. intros len pa pp pn g. unfold reply_ok. rewrite p6_args0. reflexivity. Qed.

Lemma p6_fp0 : forall len pa pp pn S g,
  reac_ctrl_identity_reply_fp 0 len pa pp pn S g = [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].
Proof.
  intros len pa pp pn S g. unfold reac_ctrl_identity_reply_fp. rewrite p6_ok0. reflexivity.
Qed.

Lemma p6_Wc0 : forall pa pp pn S,
  reac_ctrl_identity_reply_W 0 pa pp pn S = [(S - REAC_CTRL_IDENTITY_REPLY_K, S)].
Proof. intros pa pp pn S. unfold reac_ctrl_identity_reply_W. rewrite p6_args0. reflexivity. Qed.

Lemma p6_D0 : forall len pa pp pn, reac_ctrl_identity_reply_D 0 len pa pp pn = [].
Proof. intros len pa pp pn. unfold reac_ctrl_identity_reply_D. rewrite p6_args0. reflexivity. Qed.

(* ---- the class-1 layout of the side stack (F9's l2_fsc) ---- *)
Lemma p6_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

(* The write set of the call, in six explicit ranges. *)
Definition p6_W (S FS : Z) : list ivl :=
  [(S - 9072, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (S - 9072), shadow_addr S)].

Lemma p6_W_eq : forall len pa pp pn S FS g,
  reac_ctrl_identity_reply_fp 0 len pa pp pn S g ++ fp_w [1%nat] FS ++
    [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)] = p6_W S FS.
Proof.
  intros len pa pp pn S FS g. destruct (p6_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  rewrite p6_fp0. unfold p6_W, fp_w, fp_w1, REAC_CTRL_IDENTITY_REPLY_K. cbn [flat_map app].
  rewrite F5, F4, F1, F2, F3.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma p6_out : forall S FS x,
  ~ (S - 9072 <= x < S) -> ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
  ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 9072) <= x < shadow_addr S) ->
  outside (p6_W S FS) x.
Proof. intros S FS x N1 N2 N3 N4 N5 N6. unfold p6_W. cbn [outside]. repeat split; lia. Qed.

(* ---- the run: li a0,0; li a1,0; the three loads; jal reac_ctrl_identity_reply by its contract ---- *)
Lemma p6_evt : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Ab TP FS pa pp pn : Z),
    sp = Z_to_bv 64 S -> s1 = Z_to_bv 64 Ab -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 104 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= S -> HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
      [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\ asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d68) fc None m (seg_rom rsegs)).
Proof.
  intros HIR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Ab TP FS pa pp pn -> -> -> HTP Hpa Hpp Hpn HA0 HA64 HS64 HSal HKS Hlo Hhi
    RO88 RO80 RO72 HST HMI HAC HSW HADw HADbc HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof HIR as HC. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HC.
  assert (Etp : bv_unsigned (Z_to_bv 64 TP) = TP) by (apply MState.unsigned_lit; exact HTP).
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply HC with (fr := 0) (len := 0) (pa := pa) (pp := pp) (pn := pn) (S := S) (FS := FS)
      (g := repeat (Z_to_bv 8 0) 50) (ja := []) (jp := []) (jn := []).
    all: rewrite ?Etp.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; rewrite p6_args0 in HH; discriminate HH).
    all: try lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI & ST & HR & HAC' & HSW' & HAD' & HFP' & HTLS').
  subst ms'. rewrite Etp in HFP', HTLS'.
  rewrite p6_ret0 in *. rewrite (p6_W_eq 0 pa pp pn S FS (repeat (Z_to_bv 8 0) 50)) in MU.
  rewrite p6_Wc0, p6_D0 in HFP'.
  replace (ret_pc (Z_to_bv 64 0x81d80)) with (Z_to_bv 64 0x81d80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HAC'|]. split; [exact HSW'|]. split; [exact HAD' | exact HFP'].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_fsfree Tac_bp Tac_bp6.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Open Scope Z_scope.

(* An application byte outside the side stack and the callee window is outside the write set: the two shadow
   ranges hold shadow bytes only. *)
Lemma p6_out_app : forall S FS x,
  app_mem x -> ~ (S - 9072 <= x < S) -> ~ (FS <= x < FS + FS_SIZE) ->
  0 <= FS -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
  outside (p6_W S FS) x.
Proof.
  intros S FS x Hx N1 N2 HFS0 HFSapp Hlo Hhi.
  apply p6_out; [exact N1 | unfold FS_SIZE in N2; lia | unfold FS_SIZE in N2; lia
    | unfold FS_SIZE in N2; lia | |].
  - intros Hin. apply (app_not_shadow x Hx).
    apply (fsf_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia)); [|exact Hin].
    intros y Hy. apply HFSapp. unfold FS_SIZE. Z.div_mod_to_equations. lia.
  - intros Hin. apply (app_not_shadow x Hx).
    apply (fsf_sh_in_win (S - 9072) S x ltac:(unfold HIGHMEM_BEG in Hlo; lia)); [|exact Hin].
    intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* A shadow byte of an application address outside the class-1 frames and the callee window is outside the write
   set: the three application ranges hold no shadow byte, and the two shadow ranges are the shadows of ranges the
   address misses (all bounds are multiples of 8). *)
Lemma p6_out_sh : forall S FS a,
  app_mem a -> 0 <= a -> ~ (FS + 1085440 <= a < FS + 2134016) -> ~ (S - 9072 <= a < S) ->
  0 <= FS -> FS mod 4096 = 0 -> S mod 16 = 0 ->
  (forall b, FS <= b < FS + FS_SIZE -> app_mem b) -> HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
  outside (p6_W S FS) (shadow_addr a).
Proof.
  intros S FS a Ha Ha0 N1 N2 HFS0 HFSal HSal HFSapp Hlo Hhi.
  pose proof (shadow_of_app a Ha) as Hsh.
  apply p6_out.
  - intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh].
    unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
  - intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh]. apply HFSapp. unfold FS_SIZE. lia.
  - intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh]. apply HFSapp. unfold FS_SIZE. lia.
  - intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh]. apply HFSapp. unfold FS_SIZE. lia.
  - unfold shadow_addr. revert N1. clear - HFSal Ha0 HFS0. intros N1. Z.div_mod_to_equations. lia.
  - unfold shadow_addr. revert N2. clear - HSal Ha0 Hlo. unfold HIGHMEM_BEG in Hlo. intros N2.
    Z.div_mod_to_equations. lia.
Qed.

(* The one place this file takes the generated runtime cell list asan_cf_cells apart (a Theorem Labs lane 15:32Z): the GOT
   slot of the flags record and its bytes 240 .. 260. *)
Lemma p6_cf : forall m, asan_cf_cells m ->
  bytes_at rsegs m RT_GOT_CF (le8 (Z_to_bv 64 RT_CF)) /\
  bytes_at rsegs m (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]).
Proof. intros m (H1 & _ & _ & _ & _ & _ & H7 & _). exact (conj H1 H7). Qed.

Section P6.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ctrl_identity_reply (REPLY@0x81d7c), taken on its lib/B contract, never on its code. *)
Hypothesis REPLY : reac_ctrl_identity_reply_contract.

Lemma seg_P6 : Hcut B APIf ra (Inv_B81d80 B APIf ra) -> Hcut B APIf ra (Inv_B81d68 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & (H24 & HADc) & HPRO & H64 & HPL & HADk &
                    Ac & pa & pp & pn & f & Hr9c & HAc & Hpa & Hpp & Hpn & Hq88 & Hq80 & Hq72 & Hq208 &
                    HADw & HADbc).
  subst c.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof (bp_frame_stk B APIf ra g fr [] regs mem md HFRA) as Hfstk.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HRK : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw, HADw.
  pose proof (Hplace 9072 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAeq : Ac = A) by (apply (bp_rg_inj regs 9 Ac A Hr9c Hr9 HAc HA64)). subst Ac.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  (* the side stack: the package of the call, from FRA (adopt FSFREE) *)
  pose proof (fra_fsfree B APIf ra g fr [] regs mem md HFRA) as HFF.
  destruct (fra_fp B APIf ra g fr [] regs mem md [1%nat] REAC_CTRL_IDENTITY_REPLY_K
              [(AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K, AC.aspZ regs)] [] HFRA
              ltac:(intros c Hc; cbn [In] in Hc; destruct Hc as [<-|[]]; lia)
              ltac:(rewrite HRK; lia)
              ltac:(intros w Hw; cbn [In] in Hw; destruct Hw as [<-|[]]; cbn [fst snd];
                    rewrite Haspz, HRK; left; lia)
              ltac:(intros d Hd; cbn [In] in Hd; destruct Hd))
    as (FS & HFP & HTLSdj & HFPDJ & HFSfr).
  rewrite Haspz in HFP, HTLSdj.
  destruct (p6_fsc FS) as (Fhint & Fflag & FM1 & Ffr0 & Ffr1).
  rewrite Ffr1 in HFSfr.
  pose proof HFF as HFF0.
  destruct HFF0 as (FS0 & Hwtp & HFS0r & Hfsok & HFSGT & HFSal & HFSapp & HFSend & HFSfr0 & _).
  (* the package's FS is in range (its own fs_place) and is FSFREE's *)
  assert (HFSr : 0 <= FS < 2 ^ 64).
  { destruct HFP as (DT & TS & C & T & DB & k & _ & _ & (HP1 & _ & _ & HPapp & _) & _).
    pose proof (HPapp FS ltac:(unfold FS_SIZE; lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (EFS : FS = FS0).
  { destruct HFP as (DT & TS & C & T & DB & k & _ & HTPb & _).
    pose proof (KindBGlue.bytes_at_le8_word rsegs mem _ _ HTPb) as Hw.
    rewrite MState.unsigned_lit in Hw by lia.
    apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS)); [exact Hw | exact Hwtp | exact HFSr | exact HFS0r
      | unfold AC.as_tp, AC.ASYMS; cbn; lia | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
  subst FS0.
  unfold AC.GT in HFSGT.
  assert (HFSlow : FS + 11571200 <= 2147450880 \/ 17592186044416 + 2147450880 <= FS).
  { pose proof (HFSapp FS ltac:(unfold AC.FS_SIZE; lia)) as H1.
    pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.FS_SIZE in *. lia. }
  assert (HFSappz : forall a, FS <= a < FS + FS_SIZE -> app_mem a)
    by (intros a Ha; apply HFSapp; unfold AC.FS_SIZE, FS_SIZE in *; lia).
  assert (HFSstk : FS + 11571200 <= g_S g - 1048576) by (unfold AC.FS_SIZE in HFSend; lia).
  (* the thread-pointer register and the runtime's cells *)
  assert (HTPr : 0 <= AC.as_tp AC.ASYMS < 2 ^ 64) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL0.
  destruct (p6_cf mem (AsanRTInv.RT_cf_cells _ _ _ HRT)) as (HGOTCF & HCF240).
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (AsanRTInv.real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (AsanRTInv.real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (bp_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (bp_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HGC : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HGOTCF.
  (* the window of the call *)
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - 9072) (g_S g) Hwin ltac:(lia)) as (_ & Hw1).
  destruct (stk_split rsegs mem (sp - 9072) sp (g_S g) Hw1 ltac:(lia)) as (HSTKw & _).
  (* the three reply cells as read-only cells *)
  assert (RO88 : ro_cells rsegs mem (A + 88) [C8 (Z_to_bv 64 pa)]) by (apply bp_ro8; exact Hq88).
  assert (RO80 : ro_cells rsegs mem (A + 80) [C8 (Z_to_bv 64 pp)]) by (apply bp_ro8; exact Hq80).
  assert (RO72 : ro_cells rsegs mem (A + 72) [C8 (Z_to_bv 64 pn)]) by (apply bp_ro8; exact Hq72).
  (* the normalized memory the run is stepped on (the callee contract needs mem_inv) *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TB0' : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs -> bytes_at rsegs mem a bs)
    by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 HSW0) as HSW0n.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 HAC0) as HAC0n.
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - 9072) sp HR0 ltac:(lia) HSTKw) as HSTKwn.
  assert (HFSmem : stk rsegs mem FS (FS + FS_SIZE)).
  { destruct HFP as (DT & TS & C & T & DB & k & _ & _ & HP & _). destruct HP as (_ & _ & _ & _ & HS). exact HS. }
  pose proof (bp_stk_rel mem (normalize rsegs mem) FS (FS + FS_SIZE) HR0 ltac:(unfold FS_SIZE; lia) HFSmem)
    as HFSstkn.
  pose proof (bp_addr_rel mem (normalize rsegs mem) _ _ HR0 HADw) as HADwn.
  pose proof (bp_addr_rel mem (normalize rsegs mem) _ _ HR0 HADbc) as HADbcn.
  assert (RO88n : ro_cells rsegs (normalize rsegs mem) (A + 88) [C8 (Z_to_bv 64 pa)])
    by (apply bp_ro8; apply TB0; exact Hq88).
  assert (RO80n : ro_cells rsegs (normalize rsegs mem) (A + 80) [C8 (Z_to_bv 64 pp)])
    by (apply bp_ro8; apply TB0; exact Hq80).
  assert (RO72n : ro_cells rsegs (normalize rsegs mem) (A + 72) [C8 (Z_to_bv 64 pn)])
    by (apply bp_ro8; apply TB0; exact Hq72).
  assert (HFPn : fp [1%nat] (normalize rsegs mem) (AC.as_tp AC.ASYMS) FS (sp - 9072) sp
                   [(sp - 9072, sp)] []).
  { apply (bp_fp_tr [1%nat] mem (normalize rsegs mem) _ FS _ _ _ _ TB0 (fun _ => HFSstkn)).
    rewrite <- HRK. exact HFP. }
  pose proof (TB0 _ _ HRBc) as HRBn.
  pose proof (TB0 _ _ HRMc) as HRMn.
  pose proof (TB0 _ _ HGC) as HGCn.
  pose proof (TB0 _ _ HC254) as HC254n.
  pose proof (TB0 _ _ HC255) as HC255n.
  assert (HTLSn : reac_ctrl_identity_reply_tls (normalize rsegs mem) (AC.as_tp AC.ASYMS) FS (sp - 9072) sp).
  { intros DT TS C T DB k HT. rewrite <- HRK.
    apply HTLSdj. exact (bp_atls_tr (normalize rsegs mem) mem _ DT TS C T DB k TB0' HT). }
  unfold rg in Hr19, Hr9, Hr2, H24, Hr4.
  rewrite SEGS.
  apply (bp_run regs (Z_to_bv 64 0x81d68) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81d80 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (-1) /\
       LF.munch (p6_W sp FS) (normalize rsegs mem) m0' /\ LF.wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - 9072) sp /\ shadow_rw m0' /\
       addressable m0' (sp - 9072) 9072 /\
       fp [1%nat] m0' (AC.as_tp AC.ASYMS) FS (sp - 9072) sp [(sp - 9072, sp)] [])
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p6_evt REPLY) with (S := sp) (Ab := A) (TP := AC.as_tp AC.ASYMS) (FS := FS)
        (pa := pa) (pp := pp) (pn := pn).
      all: rewrite ?HRK.
      all: try assumption.
      all: try (unfold HIGHMEM_BEG, APPMEM_END; lia).
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P24' & P25' & P26' & P10' &
                  MUq & WMq & MIq & STq & ACq & SWq & ADq & FPq).
      exists R, (Z_to_bv 64 0x81d80), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P23'|].
      split; [exact P24'|]. split; [exact P25'|]. split; [exact P26'|]. split; [exact P10'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq|]. split; [exact ADq | exact FPq].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K24 & K25 & K26 & K10 & MU0 & WM0 & ST0' & SW0' &
       AD0' & FP0') Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (-1)) by (rewrite Hreg; exact K10).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (bp_stk_back mem' m0' (sp - 9072) sp HRel ltac:(lia) ST0') as ST'.
    pose proof (bp_srw_back mem' m0' HRel SW0') as SW'.
    pose proof (bp_addr_back mem' m0' _ _ HRel AD0') as AD'.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    assert (TB1 : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    assert (FP' : fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - 9072) sp [(sp - 9072, sp)] []).
    { apply (bp_fp_tr [1%nat] m0' mem' _ FS _ _ _ _ TB1); [|exact FP0'].
      intros Hs. exact (bp_stk_back mem' m0' FS (FS + FS_SIZE) HRel ltac:(unfold FS_SIZE; lia) Hs). }
    (* outside the write set: the shapes the rest of the proof uses *)
    assert (OUTapp : forall x, app_mem x -> ~ (sp - 9072 <= x < sp) -> ~ (FS <= x < FS + FS_SIZE) ->
              LF.outside (p6_W sp FS) x).
    { intros x Hx N1 N2. apply (p6_out_app sp FS x Hx N1 N2 ltac:(lia) HFSappz);
        unfold HIGHMEM_BEG, APPMEM_END; lia. }
    assert (OUTsh : forall a, app_mem a -> 0 <= a -> ~ (FS + 1085440 <= a < FS + 2134016) ->
              ~ (sp - 9072 <= a < sp) -> LF.outside (p6_W sp FS) (shadow_addr a)).
    { intros a Ha Ha0 N1 N2. apply (p6_out_sh sp FS a Ha Ha0 N1 N2 ltac:(lia) HFSal
        ltac:(exact Hspm) HFSappz); unfold HIGHMEM_BEG, APPMEM_END; lia. }
    assert (OUTlo : forall x, 0 <= x < 6283264 -> LF.outside (p6_W sp FS) x).
    { intros x Hx. apply p6_out; try lia.
      - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
      - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (OUThi : forall x, sp <= x -> LF.outside (p6_W sp FS) x).
    { intros x Hx. apply p6_out; try lia.
      - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
      - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (OUTfr : forall x, fr <= x < fr + 3136 -> LF.outside (p6_W sp FS) x).
    { intros x Hx. apply p6_out; [lia | lia | lia | lia | |].
      - intros Hin. apply (app_not_shadow x (Happ' x ltac:(lia))).
        apply (fsf_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia)); [|exact Hin].
        intros y Hy. apply HFSappz. unfold FS_SIZE. Z.div_mod_to_equations. lia.
      - intros Hin. apply (app_not_shadow x (Happ' x ltac:(lia))).
        apply (fsf_sh_in_win (sp - 9072) sp x ltac:(lia)); [|exact Hin].
        intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
    assert (OUTfrsh : forall x, Sfr fr <= x < Sfr fr + 392 -> LF.outside (p6_W sp FS) x).
    { intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite bp_sh8; lia).
      apply OUTsh; [apply Happ'; lia | lia | unfold FS_SIZE in *; lia | lia]. }
    (* the side stack after the run is readable (the callee's own fp post) *)
    assert (HFSstk' : stk rsegs mem' FS (FS + FS_SIZE)).
    { destruct FP' as (DT & TS & C & T & DB & k & _ & _ & HP & _).
      destruct HP as (_ & _ & _ & _ & HS). exact HS. }
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside (p6_W sp FS) x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. unfold p6_W in Hx. cbn [LF.outside] in Hx.
      assert (HC : (sp - 9072 <= x < sp) \/ (FS + 8 <= x < FS + 2134016) \/
                   (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) \/
                   (shadow_addr (sp - 9072) <= x < shadow_addr sp)) by lia.
      destruct HC as [Hc|[Hc|[Hc|Hc]]].
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct HFSstk' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(unfold FS_SIZE; lia))).
      - apply SW'. apply (fsf_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia)); [|exact Hc].
        intros y Hy. apply HFSappz. unfold FS_SIZE. Z.div_mod_to_equations. lia.
      - apply SW'. apply (fsf_sh_in_win (sp - 9072) sp x ltac:(lia)); [|exact Hc].
        intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
    (* the heap invariant and stklo: the side-stack store law, with a_fs_ok from the callee's fp post *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (fp_post_fs_ok mem mem' [1%nat] (AC.as_tp AC.ASYMS) FS (sp - 9072) sp
               [(sp - 9072, sp)] [] (p6_W sp FS)
               ltac:(intros cc Hcc; cbn [In] in Hcc; destruct Hcc as [<-|[]]; lia)
               Hfsok ltac:(lia) ltac:(unfold AC.FS_SIZE; lia) FP' MU WM).
      intros q Hq Hcl.
      destruct (Hcl 1%nat ltac:(cbn [In]; left; reflexivity)) as (Hnh & Hnf).
      destruct (p6_fsc FS) as (F1 & F2 & F3 & _ & _).
      rewrite F1 in Hnh. rewrite F2, F3 in Hnf.
      apply p6_out; [lia | lia | lia | lia | |].
      - intros Hin. apply (app_not_shadow q (HFSappz q ltac:(unfold FS_SIZE; lia))).
        apply (fsf_sh_in (FS + 1085440) (FS + 2134016) q ltac:(lia)); [|exact Hin].
        intros y Hy. apply HFSappz. unfold FS_SIZE. Z.div_mod_to_equations. lia.
      - intros Hin. apply (app_not_shadow q (HFSappz q ltac:(unfold FS_SIZE; lia))).
        apply (fsf_sh_in_win (sp - 9072) sp q ltac:(lia)); [|exact Hin].
        intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      apply p6_out.
      - intros Hin. apply Hnok. right; left. unfold APPMEM_END. lia.
      - intros Hin. apply Hnfs. unfold AC.FS_SIZE. lia.
      - intros Hin. apply Hnfs. unfold AC.FS_SIZE. lia.
      - intros Hin. apply Hnfs. unfold AC.FS_SIZE. lia.
      - intros Hin. apply Hnsh. exists (8 * (q - 2147450880)).
        split; [unfold AC.FS_SIZE; unfold shadow_addr, ASAN_K in Hin; Z.div_mod_to_equations; lia|].
        unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
      - intros Hin. apply Hnok. right; right; right. exists (8 * (q - 2147450880)).
        split; [unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
        right; left. unfold shadow_addr, ASAN_K in Hin. unfold APPMEM_END.
        Z.div_mod_to_equations. lia. }
    pose proof (lw_fs_store (APIf rc) ([] ++ g_H g) mem mem' md FS HAH Hwtp HFS0r Hagree Hwrit HFSOK') as HLS.
    pose proof (lws_ah _ _ _ _ _ HLS) as HAH'. pose proof (lws_own _ _ _ _ _ HLS) as HOWN'.
    pose proof (lws_lo _ _ _ _ _ HLS) as HSTK'. pose proof (lws_hi _ _ _ _ _ HLS) as HHI'.
    (* FRA at the memory after the run *)
    assert (HDJ : rt_disjoint (p6_W sp FS)).
    { unfold AsanRTInv.rt_disjoint, p6_W, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
        RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      assert (HS1 : 2147450880 + 785408 <= shadow_addr (FS + 1085440))
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (HS2 : 2147450880 + 785408 <= shadow_addr (sp - 9072))
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = 392%nat).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + 392 - Sfr fr) with 392 by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (bp_ag_lo a Ha) as Halo.
      apply (bp_addr_keep (p6_W sp FS) mem mem' a 1 (HAG a Ha) MU). intros i Hi.
      replace (a + i) with a by lia.
      apply OUTsh; [unfold app_mem, LOWMEM_END; left; lia | lia | lia | lia]. }
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      destruct (Z_le_gt_dec (sp - 9072) a) as [H1|H1]; [destruct (Z_lt_ge_dec a sp) as [H2|H2]|].
      - replace a with (sp - 9072 + (a - (sp - 9072))) by lia.
        exact (addressable_sub mem' (sp - 9072) 9072 (a - (sp - 9072)) 1 AD'
                 ltac:(lia) ltac:(lia) ltac:(lia)).
      - apply (bp_addr_keep (p6_W sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi.
        replace (a + i) with a by lia.
        apply OUTsh; [unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia | lia | lia | lia].
      - apply (bp_addr_keep (p6_W sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi.
        replace (a + i) with a by lia.
        apply OUTsh; [unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia | lia | lia | lia]. }
    (* the side arm's FakeStack frame record *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros (FS1 & j & Htp1 & HFS1r & Hj & Hfreq & Hflag & Htail).
      assert (EFS1 : FS1 = FS)
        by (apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS)); [exact Htp1 | exact Hwtp | exact HFS1r | exact HFS0r
            | unfold AC.as_tp, AC.ASYMS; cbn; lia | unfold AC.as_tp, AC.ASYMS; cbn; lia]).
      subst FS1.
      assert (HM6 : fs_M 6 = 256) by reflexivity.
      assert (HB6 : fs_B 6 = 4096) by reflexivity.
      assert (Hflagv : fs_flag FS 6 j = FS + 36352 + j)
        by (unfold fs_flag; change (2 ^ 15) with 32768; change (2 ^ (15 - Z.of_nat 6)) with 512; lia).
      assert (Hfrv : fr = FS + 36864 + 6291456 + j * 4096)
        by (rewrite Hfreq; unfold fs_frame, fs_B; change (2 ^ 20) with 1048576; cbn [Z.of_nat]; lia).
      rewrite HM6 in Hj.
      exists FS, j.
      split.
      { apply (KindBGlue.kb_word_munch rsegs mem mem' (p6_W sp FS) _ FS Htp1 MU).
        intros k Hk. split; [unfold AC.as_tp, AC.ASYMS; cbn; lia|].
        apply OUTlo. unfold AC.as_tp, AC.ASYMS in *. cbn in *. lia. }
      split; [exact HFS0r|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfreq|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        rewrite Hflagv in Hx. apply p6_out; [lia | lia | lia | lia | |].
        - intros Hin. apply (app_not_shadow x (HFSappz x ltac:(unfold FS_SIZE; lia))).
          apply (fsf_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia)); [|exact Hin].
          intros y Hy. apply HFSappz. unfold FS_SIZE. Z.div_mod_to_equations. lia.
        - intros Hin. apply (app_not_shadow x (HFSappz x ltac:(unfold FS_SIZE; lia))).
          apply (fsf_sh_in_win (sp - 9072) sp x ltac:(lia)); [|exact Hin].
          intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
        rewrite HB6 in Hx.
        apply p6_out; [lia | lia | lia | lia | |].
        - intros Hin. apply (app_not_shadow x (HFSappz x ltac:(unfold FS_SIZE; lia))).
          apply (fsf_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia)); [|exact Hin].
          intros y Hy. apply HFSappz. unfold FS_SIZE. Z.div_mod_to_equations. lia.
        - intros Hin. apply (app_not_shadow x (HFSappz x ltac:(unfold FS_SIZE; lia))).
          apply (fsf_sh_in_win (sp - 9072) sp x ltac:(lia)); [|exact Hin].
          intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. } }
    (* the input block is apart from the run's writes *)
    assert (HWinp : forall x, g_p g <= x < g_p g + g_n g ->
              LF.outside (p6_W sp FS) x /\ LF.outside (p6_W sp FS) (shadow_addr x)).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      pose proof (lw_blocks (APIf rc) ([] ++ g_H g) mem md (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror Hin)))
        as HLB.
      pose proof (lwb_end _ _ _ _ _ _ HLB) as Hend.
      pose proof (proj1 (lwb_byte _ _ _ _ _ _ HLB x Hx)) as Happx.
      pose proof (lwb_byte_not_fs (APIf rc) _ _ _ _ _ HLB x Hx) as Hnfs.
      assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx; lia).
      assert (HnFS : ~ (FS <= x < FS + FS_SIZE)).
      { intros Hin'. apply Hnfs. exists FS. split; [exact HFSr|]. split; [exact Hwtp|].
        unfold AC.FS_SIZE, FS_SIZE in *. lia. }
      split.
      - apply OUTapp; [exact Happx | lia | exact HnFS].
      - apply OUTsh; [exact Happx | exact Hx0 | unfold FS_SIZE in HnFS; lia | lia]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (bp_fra B APIf ra empty FF g fr [] regs regs'' mem mem' md (p6_W sp FS)
               HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
        try assumption.
      all: first
        [ exact OUTlo
        | exact OUTfrsh
        | (intros x Hx; rewrite Hr9 in Hx; rewrite MState.unsigned_lit in Hx by lia; apply OUThi; lia)
        | (intros x Hx; apply OUTfr; lia)
        | (intros x Hx; apply OUThi; lia)
        | (intros x Hx; destruct (bp_out_dec (p6_W sp FS) x) as [Ho|Hno];
           [left; exact Ho | right; exact (RDW x Hno)]) ]. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md')
      by (apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity; exact Hmat).
    (* ENT across the run *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              LF.outside (p6_W sp FS) x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
              (fr <= x < fr + 3136) \/ (Sfr fr <= x < Sfr fr + 392) \/
              (exists y, g_S g - AF.SLOT_STACK <= y < AC.aspZ regs /\ x = shadow_addr y) \/
              AC.a_in_fs AC.ASYMS mem x \/
              (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)).
    { intros x Hx.
      destruct (bp_out_dec (p6_W sp FS) x) as [Ho|Hno]; [left; exact Ho|].
      unfold p6_W in Hno. cbn [LF.outside] in Hno.
      assert (HC : (sp - 9072 <= x < sp) \/ (FS + 8 <= x < FS + 2134016) \/
                   (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) \/
                   (shadow_addr (sp - 9072) <= x < shadow_addr sp)) by lia.
      destruct HC as [Hc|[Hc|[Hc|Hc]]].
      - right; left. lia.
      - right; right; right; right; right; left. exists FS. split; [exact HFSr|].
        split; [exact Hwtp|]. unfold AC.FS_SIZE. lia.
      - right; right; right; right; right; right. exists (8 * (x - 2147450880)).
        split.
        + exists FS. split; [exact HFSr|]. split; [exact Hwtp|]. unfold AC.FS_SIZE.
          unfold shadow_addr, ASAN_K in Hc. Z.div_mod_to_equations. lia.
        + unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
      - right; right; right; right; left. exists (8 * (x - 2147450880)).
        split.
        + rewrite Haspz. unfold shadow_addr, ASAN_K in Hc. Z.div_mod_to_equations. lia.
        + unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    (* ent_kept's fifth case (the entry blocks' shadow): an entry block's byte is app memory below
       stklo <= sp - FN_STACK and off the side stack (a_laws_blocks), so its shadow byte is outside the run's
       write set *)
    assert (HK5 : forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
              LF.outside (p6_W sp FS) (shadow_addr (q + i))).
    { intros q k i Hin Hni Hi.
      pose proof (lw_blocks (APIf rc) ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as HLB.
      pose proof (lwb_end _ _ _ _ _ _ HLB) as Hend.
      pose proof (proj1 (lwb_byte _ _ _ _ _ _ HLB (q + i) ltac:(lia))) as Happq.
      pose proof (lwb_byte_not_fs (APIf rc) _ _ _ _ _ HLB (q + i) ltac:(lia)) as Hnfs.
      assert (Hq0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
      assert (HnFS : ~ (FS <= q + i < FS + FS_SIZE)).
      { intros Hin'. apply Hnfs. exists FS. split; [exact HFSr|]. split; [exact Hwtp|].
        unfold AC.FS_SIZE, FS_SIZE in *. lia. }
      apply OUTsh; [exact Happq | exact Hq0 | unfold FS_SIZE in HnFS; lia | lia]. }
    assert (HENT' : ENT APIf g [] mem' md)
      by exact (bp6_ent_W B APIf ra g fr [] regs mem mem' md (p6_W sp FS) HENT HFRA MU WM HK5
                  HWcases HSTK' HHI' HOWNk).
    assert (HENT'' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply OUTfr. lia. }
    split; [unfold a0v, rg; exact E10|].
    assert (KS : forall off v, 0 <= off <= 440 -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. apply OUThi. lia. }
    assert (KSP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A0 & HA0 & Hq).
      assert (HA0e : A0 = A)
        by (apply (bp_spill_A regs mem off v A A0 HA0 Hq Hr9); unfold APPMEM_END in *; lia).
      subst A0. exact (KS off v Hoff Hq). }
    split.
    { (* PRO: the spills are kept and our[]'s six bytes are frame bytes, whose shadow byte the run misses *)
      apply (bp_PRO_keep fr regs regs'' mem mem' KSP); [|exact HPRO].
      intros HOA. apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
      apply OUTsh; [apply Happ'; lia | lia | lia | lia]. }
    split; [exists f; exact (KS 208 f ltac:(lia) Hq208)|].
    split; [exists pa; exact (KS 88 pa ltac:(lia) Hq88)|].
    split; [exists pp; exact (KS 80 pp ltac:(lia) Hq80)|].
    split; [exists pn; exact (KS 72 pn ltac:(lia) Hq72)|].
    destruct H64 as (A1 & HA1 & Hq64).
    assert (HA1e : A1 = A)
      by (apply (bp_spill_A regs mem 64 (fr + 3056) A A1 HA1 Hq64 Hr9); unfold APPMEM_END in HAPP; lia).
    subst A1.
    split; [exact (KS 64 (fr + 3056) ltac:(lia) Hq64)|].
    split; [unfold rg; rewrite E24; exact H24|].
    split.
    { apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 3040) 1 HADc MU). intros i Hi.
      replace (fr + 3040 + i) with (fr + 3040) by lia.
      apply OUTsh; [apply Happ'; lia | lia | lia | lia]. }
    split.
    { apply (bp_addr_keep (p6_W sp FS) mem mem' KNC.KIND_NAME 112 HADk MU). intros i Hi.
      apply OUTsh; [unfold app_mem, LOWMEM_END, KNC.KIND_NAME; left; lia
        | unfold KNC.KIND_NAME; lia | unfold KNC.KIND_NAME; lia | unfold KNC.KIND_NAME; lia]. }
    destruct HPL as ((Hc0 & Hc23 & Hc25) & HID & HFG & (HRA1 & HRA2 & HRA3) & H176p & H208p & HFS).
    split.
    { split; [exact Hc0|]. unfold rg in *. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
    split.
    { unfold IDBe in *. eapply fl_bytes; [exact HID | exact MU |].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
      intros x Hx. apply OUTfr. lia. }
    split.
    { unfold FGBe in *. eapply fl_bytes; [exact HFG | exact MU |].
      unfold z72. rewrite repeat_length. intros x Hx. apply OUTfr. lia. }
    split.
    { (* RAD: the records' and `first`'s bytes are frame bytes, apart from the class-1 frames and the callee
         window *)
      unfold RAD, fragb. split; [|split].
      - apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 2688) 38 HRA1 MU). intros i Hi.
        apply OUTsh; [apply Happ'; lia | lia | lia | lia].
      - unfold fragb in HRA2. apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 2768) 72 HRA2 MU). intros i Hi.
        apply OUTsh; [apply Happ'; lia | lia | lia | lia].
      - apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 2880) 40 HRA3 MU). intros i Hi.
        apply OUTsh; [apply Happ'; lia | lia | lia | lia]. }
    (* the record-pointer spills [A + 176] = fr + 2688 and [A + 208] = fragb fr *)
    split; [exact (KSP 176 (fr + 2688) ltac:(lia) H176p)|].
    split; [exact (KSP 208 (fragb fr) ltac:(lia) H208p)|].
    (* the turn-0 first-fragment state: `first`'s bytes are frame bytes, its shadow bytes apart from the run *)
    unfold FSj, FSb, u32, b8 in HFS |- *. change (fst_at (g_in g) 0) with fs0 in HFS |- *.
    unfold fs0 in HFS |- *. cbn [fs_have fs_n fs_body] in HFS |- *.
    destruct HFS as (Hhv & Hn & Hbody & H40 & HFI).
    split; [eapply fl_bytes; [exact Hhv | exact MU |]; rewrite length_le4; intros x Hx; apply OUTfr; lia|].
    split; [eapply fl_bytes; [exact Hn | exact MU |]; cbn [length]; intros x Hx; apply OUTfr; lia|].
    split; [eapply fl_bytes; [exact Hbody | exact MU |]; cbn [length]; intros x Hx; apply OUTfr; lia|].
    split; [|exact HFI].
    apply (bp_addr_keep (p6_W sp FS) mem mem' (fr + 2880) 40 H40 MU). intros i Hi.
    apply OUTsh; [apply Happ'; lia | lia | lia | lia].
Qed.

End P6.
