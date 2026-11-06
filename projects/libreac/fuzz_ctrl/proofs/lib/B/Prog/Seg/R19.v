(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its numbers changed; 373 of its 414 lines of code are new or changed and 970 lines of the source are left out. *)
(* Segment R19 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81a50, 0x81a64], 5
   instructions, cut Inv_B81a50 -> cut Inv_B81a68 (plan-asan-ubsan.md section 2, row R19; section 4, BCMP =
   wrapper_bcmp 0x42aac). rule 24: no function proved (a slot segment).

   The code tests the declaration_of result (0x81a50 `bnez a0,81a58`, taken because the cut carries a0 = vd <> 0,
   so the sink jump 0x81a54 `j 82fa4` is not reached), sets a2 = 32 (0x81a58), a0 = s2 = Phi_r + 18 (0x81a5c),
   reloads a1 = [A + 96] = decl_slot fr (0x81a60) and calls the bcmp wrapper (0x81a64), which returns to
   0x81a68. The range has no instrumented shadow check of its own and no arithmetic-check branch to 0x82fa0.

   The wrapper is taken on its lib/B contract (lib/B/Prog/bcmp_wrap_c.v), a Section Hypothesis, never on its
   code: it checks that the 32 bytes at a0 and the 32 bytes at a1 are marked usable in the shadow map, compares
   them with musl bcmp, and writes only its own stack window [sp - 4560, sp). Its result is 0 here, which the
   exit cut carries as a0 = 0: the 32 bytes at Phi_r + 18 are X(0)[18 .. 50), which is the declaration of the
   catalogue row m (RtmB.rb_X0_F), and the 32 bytes at decl_slot fr are that same declaration (the entry cut).

   The contract asks for mem_inv, which the cuts do not carry (they carry ro_agree), so the run is stepped on the
   normalized memory (MemNorm.evt_normalize) and carried back (r19_evt). FRA moves across the wrapper's window by
   Tac_slot.sl_callee_keep, ENT by Tac_slot.ent_store with the heap invariant from RHelp.rh_ah, and the model step
   by Tac_slot.sl_fra_move / ent_mat, RBE by RHelp.rh_RBE_keep. Entry and exit are the official cuts
   Inv_B81a50_at / Inv_B81a68_at of lib/B/Prog/SlotInv.v. Both cuts carry s11 = 32, which the bcmp wrapper keeps.
   v1.9.0 against the patched image: the pcs move +0x64, Phi_r + 18 is in s2 (patched s9), decl_slot fr is
   reloaded from [A + 96] (patched [A + 104]), the 32 is in s11 (patched s2), CUR's n - c in s9 (patched s8). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* ---- small helpers ---- *)

Lemma r19_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

(* memcmp of a list with itself over n <= length bytes is 0. *)
Lemma r19_memcmp_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|a l IH]; intros [|n] Hn; cbn [memcmp_model length] in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* The runtime cells the bcmp wrapper reads, from the runtime invariant RT that FRA carries. *)
Lemma r19_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (rh_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (rh_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* ---- the run of [0x81a50, 0x81a68) with the wrapper contract as stated (mem_inv) ---- *)
Lemma r19_evt_n : bcmp_wrap_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A phi D vd v lo : Z) (ls rs : list byte),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 (phi + 18) -> a0v = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= D -> D + 32 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 D)) ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m D rs -> memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m (phi + 18) 32 -> addressable m D 32 ->
    end_in_app (phi + 18) 32 -> end_in_app D 32 -> app_mem (phi + 18 + 7) -> app_mem (D + 7) ->
    (phi + 18 + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= phi + 18) ->
    (D + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= D) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp -> HIGHMEM_BEG <= lo ->
    bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                       s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81a68) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a50) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi D vd v lo ls rs -> -> -> Hvd Hvdb HA0 HAb Hp0 Hpb HD0 HDb
    R96 HL HR HM MI AL AR EL ER PL PR RL RR ST HK Hlo Hsp HAC HSW RB RM GC C254 C255.
  pose proof (rh_rdn m (A + 96) (le8 (Z_to_bv 64 D)) 8 R96 ltac:(apply length_le8)) as RD96.
  (* 81a50 bnez a0 : taken (vd <> 0) *)
  step. if_true_by (r19_neqb0 vd ltac:(lia)).
  (* 81a58 li a2,32 ; 81a5c mv a0,s2 ; 81a60 ld a1,96(s1) ; 81a64 jal wrapper_bcmp *)
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: cbv zeta.
    all: rewrite ?(MState.unsigned_lit (phi + 18)) by lia; rewrite ?(MState.unsigned_lit D) by lia.
    all: try (change (bv_unsigned (Z_to_bv 64 32)) with 32).
    all: try (change (Z.to_nat 32) with 32%nat).
    all: first [ exact HL | exact HR | exact HM | exact MI | exact AL | exact AR | exact EL | exact ER
               | exact RL | exact RR | exact ST | exact HK | exact Hlo | exact Hsp
               | exact HAC | exact HSW | exact RB | exact RM | exact GC | exact C254 | exact C255
               | (right; exact PL) | (right; exact PR) | lia ]. }
  intros ms' PO. unfold bcmp_wrap_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done.
  exists (Z_to_bv 64 0x81a68), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* ---- the same run from ro_agree: the body goes on the normalized memory ---- *)
Lemma r19_evt : bcmp_wrap_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A phi D vd v lo : Z) (ls rs : list byte),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 (phi + 18) -> a0v = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= phi -> phi + 50 <= 2 ^ 64 -> AC.GT <= D -> D + 32 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 D)) ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m D rs -> memcmp_model ls rs 32 = Some v ->
    MN.ro_agree rsegs m -> addressable m (phi + 18) 32 -> addressable m D 32 ->
    end_in_app (phi + 18) 32 -> end_in_app D 32 -> app_mem (phi + 18 + 7) -> app_mem (D + 7) ->
    (phi + 18 + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= phi + 18) ->
    (D + 32 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= D) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp -> HIGHMEM_BEG <= lo ->
    bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                       s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81a68) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a50) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi D vd v lo ls rs Es1 Es2 Ea0 Hvd Hvdb HA0 HAb Hp0 Hpb HD0 HDb
    R96 HL HR HM HRO AL AR EL ER PL PR RL RR ST HK Hlo Hsp HAC HSW RB RM GC C254 C255.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  { eapply MN.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    eapply r19_evt_n with (A := A) (phi := phi) (D := D) (vd := vd) (v := v) (lo := lo) (ls := ls) (rs := rs).
    - exact BC.
    - exact Es1.
    - exact Es2.
    - exact Ea0.
    - exact Hvd.
    - exact Hvdb.
    - exact HA0.
    - exact HAb.
    - exact Hp0.
    - exact Hpb.
    - unfold AC.GT in HD0; lia.
    - exact HDb.
    - apply MN.bytes_at_normalize; [exact HRO | exact R96].
    - apply MN.bytes_at_normalize; [exact HRO | exact HL].
    - apply MN.bytes_at_normalize; [exact HRO | exact HR].
    - exact HM.
    - apply MN.mem_inv_normalize.
    - exact (rh_addr_rel m _ _ _ REL AL).
    - exact (rh_addr_rel m _ _ _ REL AR).
    - exact EL.
    - exact ER.
    - exact PL.
    - exact PR.
    - exact RL.
    - exact RR.
    - apply rh_stk_norm;
        [ exact HRO | exact ST
        | apply rh_not_ro_hi;
            [ unfold AC.GT; unfold HIGHMEM_BEG in Hlo; lia | unfold APPMEM_END in Hsp; lia ] ].
    - exact HK.
    - exact Hlo.
    - exact Hsp.
    - exact (rh_acells_rel m _ REL HAC).
    - exact (rh_shrw_rel m _ REL HSW).
    - apply MN.bytes_at_normalize; [exact HRO | exact RB].
    - apply MN.bytes_at_normalize; [exact HRO | exact RM].
    - apply MN.bytes_at_normalize; [exact HRO | exact GC].
    - apply MN.bytes_at_normalize; [exact HRO | exact C254].
    - apply MN.bytes_at_normalize; [exact HRO | exact C255]. }
  intros msx (msx0 & Pn & MR & RS).
  destruct Pn as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
                 & E & MU & WM & MI' & ST' & AC' & SW').
  subst msx0.
  destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
  destruct MR as (Hr1 & Hf1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmem).
  cbn in Hr1, Hf1, Hpc1, Hsvc1, Hres1, Hfc1, Hrom1, Hmem, RS.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', mem1.
  split; [unfold MS; subst; reflexivity|].
  split; [exact (MN.munch_rel rsegs _ m _ mem1 m0' REL Hmem RS MU)|].
  split; [exact (MN.wmono_rel rsegs m _ mem1 m0' REL Hmem RS WM)|].
  exact (rh_stk_back mem1 m0' _ _ Hmem ST').
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The bcmp wrapper (wrapper_bcmp 0x42aac), taken on its lib/B contract. *)
Hypothesis HBC : bcmp_wrap_contract.

Lemma seg_R19 : forall b : nat,
  Hat B APIf ra (Inv_B81a68_at B APIf ra) b -> Hat B APIf ra (Inv_B81a50_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & vd & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & HRF & H10 & Hvd & H18 & Hsp96 & HDB & HRBE & H21 & Hb0 & HHB & Hvdb & HLD & HAD & H27)).
  subst c. subst b. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  (* FRA's names *)
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hfrpl & HfrA & _ & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphinz & Hphi4k & Hphistk & _ & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  pose proof (r19_cells sp mem md HRT) as (HAC0 & HSW0 & HRB & HRM & HGC & HC254 & HC255).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKb : BCMP_WRAP_K = 4560) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  rewrite Haspz in Hwlo, Hwstk, Hfrpl.
  assert (Hspb : 0 <= sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  assert (Hesp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  (* the turn's model facts: n_0 is at least 124 bytes, its first 50 bytes are the frame *)
  pose proof HRF as (HRB0 & Hnz & H20 & HF).
  destruct (rb_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HF, HLF.
  (* the block's 32 bytes at Phi_r + 18 are the declaration of the catalogue row *)
  assert (HLS : bytes_at rsegs mem (phi + 18) (RcDecl.decl (rt_mb (g_in g)))).
  { rewrite <- (rb_X0_F (g_in g)).
    pose proof (rh_ba_sub mem phi (rt_F (g_in g) 0) 18 32 HF ltac:(rewrite HLF; lia)) as Hs.
    replace (phi + Z.of_nat 18) with (phi + 18) in Hs by lia. exact Hs. }
  (* the premises of the wrapper *)
  assert (Hsz : AC.a_size (rnb g 0) = rnb g 0) by (unfold AC.a_size; lia).
  destruct HHB as (Hnz0 & HAphi0). pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  assert (HA18 : addressable mem (phi + 18) 32) by (apply (addressable_sub mem phi (rnb g 0) 18 32 HAphi); lia).
  pose proof (addressable_app mem _ _ HAphi) as Happhi.
  pose proof HAphi as (Hphi0 & _ & HphiE & _).
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by (unfold APPMEM_END in HphiE; lia).
  assert (HDlo : AC.GT <= decl_slot fr) by (unfold decl_slot, AC.GT in *; lia).
  pose proof HAD as (Hd0 & _ & HdE & _).
  assert (HD32 : decl_slot fr + 32 <= 2 ^ 64) by (unfold APPMEM_END in HdE; lia).
  assert (ELp : end_in_app (phi + 18) 32) by (right; apply Happhi; lia).
  assert (ERd : end_in_app (decl_slot fr) 32)
    by (right; apply Happfr; unfold decl_slot; lia).
  assert (PLp : app_mem (phi + 18 + 7)) by (apply Happhi; lia).
  assert (PRd : app_mem (decl_slot fr + 7)) by (apply Happfr; unfold decl_slot; lia).
  assert (RLp : phi + 18 + 32 <= sp - BCMP_WRAP_K \/ sp <= phi + 18) by (left; lia).
  assert (RRd : decl_slot fr + 32 <= sp - BCMP_WRAP_K \/ sp <= decl_slot fr).
  { destruct (Hfrpl BCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left; unfold decl_slot; lia | right; unfold decl_slot; lia]. }
  assert (HSTw : stk rsegs mem (g_S g - AF.SLOT_STACK) sp).
  { exact (proj1 (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia))). }
  (* the spill the segment reloads *)
  pose proof (rh_spill_at regs mem A 96 (decl_slot fr) Hsp96 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q96.
  (* the run *)
  eapply (sl_run_lib regs (Z_to_bv 64 0x81a50) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81a68 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\ getr R 18 = getr regs 18 /\ getr R 10 = Z_to_bv 64 0 /\
       munch [(sp - BCMP_WRAP_K, sp)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in H10, H18, Hr9.
    eapply evt_mono.
    + apply (r19_evt HBC) with (A := A) (phi := phi) (D := decl_slot fr) (vd := vd) (v := 0)
        (lo := g_S g - AF.SLOT_STACK) (ls := RcDecl.decl (rt_mb (g_in g)))
        (rs := RcDecl.decl (rt_mb (g_in g)));
      try (match goal with
           | |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs)
           end);
      rewrite ?Haspz;
      [ exact Hr9 | exact H18 | exact H10 | exact Hvd | exact Hvdb | lia | exact HA4 | exact Hphi0
      | exact Hphi50 | exact HDlo | exact HD32 | exact Q96 | exact HLS | exact HDB
      | apply r19_memcmp_refl; rewrite HLD; lia | exact Hro | exact HA18 | exact HAD
      | exact ELp | exact ERd | exact PLp | exact PRd | exact RLp | exact RRd | exact HSTw
      | lia | lia | lia | exact HAC0 | exact HSW0 | exact HRB | exact HRM | exact HGC
      | exact HC254 | exact HC255 ].
    + intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & ST').
      do 3 eexists. split; [exact E|].
      split; [reflexivity|].
      do 16 (split; [reflexivity|]).
      match type of MU with
      | context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST'
      end.
      rewrite Haspz in MU, ST'.
      split; [exact MU|]. split; [exact WM | exact ST'].
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K18 & K10 &
       MU & WM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact K10).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    (* the wrapper's write set and what lies outside it *)
    assert (HoutW : forall x, (x < sp - BCMP_WRAP_K \/ sp <= x) -> outside [(sp - BCMP_WRAP_K, sp)] x)
      by (intros x Hx; apply rh_out1; exact Hx).
    assert (Hallapp : all_app [(sp - BCMP_WRAP_K, sp)]).
    { cbn [all_app app_ivl]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HWin : forall x, ~ outside [(sp - BCMP_WRAP_K, sp)] x ->
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx. left. cbn [outside] in Hx. unfold APPMEM_END in *. lia. }
    assert (HPres : forall x, 0 <= x < 2 ^ 64 -> (exists bb, mbyte rsegs mem x = Some bb) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx Hb.
      destruct (rh_out_dec [(sp - BCMP_WRAP_K, sp)] x) as [Ho|Ho].
      - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
        rewrite (MU (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
      - cbn [outside] in Ho.
        assert (Hr : sp - BCMP_WRAP_K <= x < sp) by lia.
        rewrite rh_mbyte_mrd.
        destruct ST' as (_ & _ & HST). destruct (HST x ltac:(lia)) as (_ & bb & Hbb). exists bb. exact Hbb. }
    destruct (rh_ah B APIf ra g fr (hb1 phi (rnb g 0)) regs mem mem' md
                [(sp - BCMP_WRAP_K, sp)] HFRA MU WM HWin HPres) as (HAH' & HOWN' & HSTKeq & HSTKHeq).
    (* FRA across the callee window, then to regs' / md' *)
    assert (HSTKfull : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (LFr.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) ST'); [|lia].
      eapply (LFr.stk_transport rsegs _ mem mem');
        [ exact (proj2 (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)))
        | exact MU | exact WM |].
      intros x Hx. left. apply HoutW. right. lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md').
    { apply (sl_callee_keep B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs' mem mem' md md' BCMP_WRAP_K
               HFRA);
        [ rewrite Haspz; exact MU | exact WM | exact HSTKfull | lia | rewrite Haspz; lia
        | destruct (Hfrpl BCMP_WRAP_K ltac:(lia)) as [Hc|Hc];
            [right; rewrite Haspz; lia | left; rewrite Haspz; lia]
        | unfold APPMEM_END in *; lia
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    (* ENT across the window *)
    assert (HENT' : ENT APIf g (hb1 phi (rnb g 0)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (rnb g 0)) regs mem mem' md [(sp - BCMP_WRAP_K, sp)]
               HENT HFRA MU);
        [ | exact HSTKeq | exact HSTKHeq | intros a _ Ho; exact (proj2 (HOWN' a) Ho) ].
      intros x Hx. destruct (rh_out_dec [(sp - BCMP_WRAP_K, sp)] x) as [Ho|Ho]; [left; exact Ho|].
      right; left. cbn [outside] in Ho. unfold APPMEM_END in *. lia. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g 0)) mem' md')
      by exact (ent_mat APIf g (hb1 phi (rnb g 0)) mem' md md' HENT' Hmat).
    (* the facts the exit cut asks for, across the window write *)
    assert (HoutFr : forall x, fr <= x < fr + 3136 -> outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. apply HoutW. destruct (Hfrpl BCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left; lia | right; lia]. }
    assert (HoutPhi : forall x, phi <= x < phi + rnb g 0 -> outside [(sp - BCMP_WRAP_K, sp)] x)
      by (intros x Hx; apply HoutW; left; unfold APPMEM_END in *; lia).
    assert (HoutA : forall x, A <= x < A + 448 -> outside [(sp - BCMP_WRAP_K, sp)] x)
      by (intros x Hx; apply HoutW; right; lia).
    assert (HHB' : HB mem' phi (rnb g 0)).
    { split; [exact Hnz0|].
      exact (sl_addr_keep mem mem' [(sp - BCMP_WRAP_K, sp)] phi (AC.a_size (rnb g 0)) HAphi0 MU Hallapp). }
    assert (HRBE' : RBE g fr regs' mem').
    { apply (rh_RBE_keep g fr regs regs' [(sp - BCMP_WRAP_K, sp)] mem mem' A HRBE MU Hallapp Hr9 ltac:(lia) HA4 Fr9
               HoutA).
      intros x Hx. apply HoutW. left. unfold AC.GT, HIGHMEM_BEG in *. lia. }
    assert (HRF' : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs' mem').
    { apply (rh_RFb_keep g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs regs'
               [(sp - BCMP_WRAP_K, sp)] mem mem' MU (rb_RID_len (g_in g) 0) (rb_RFG_len (g_in g) 0 ltac:(lia))
               ltac:(lia) HLF);
        [ intros x Hx; apply HoutFr; lia | exact HoutPhi | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr25
        | exact HRF ]. }
    pose proof HRB0 as (Hb6 & HCUR & HOUR & H22 & _ & _).
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. apply (rh_keep [(sp - BCMP_WRAP_K, sp)] mem mem' (fr + 2624) (OUR (g_in g)) MU);
        [|exact HOUR]. rewrite OUR_length. intros x Hx. apply HoutFr. lia. }
    assert (HCUR' : CUR g 7 regs').
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite Fr23; exact Hc23 | rewrite Fr25; exact Hc25]. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB'|].
    split; [unfold rg in *; rewrite Fr22; exact H22|].
    split; [exact HOUR'|]. split; [exact HCUR'|]. split; [exact HRBE'|].
    split; [unfold rg in *; rewrite Fr21; exact H21|].
    split; [reflexivity|].
    split; [exact HRF'|].
    split; [unfold a0v, rg; exact Fr10|].
    unfold rg; rewrite Fr27; exact H27.
Qed.

End S.
