(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): the stretch after the class-0 request, RE-BASED at the
   real memory mb at the return of __asan_stack_malloc_0, for the cgif-form glue lib/B/Prog/C_reac_box_model_block.v
   (its table row B: 0x86648 .. fwords .. dispatch .. the case).

   The proved _F run (lib/B/Prog/reac_box_model_blockF.v, reac_box_model_block_holdsF.v, a Theorem Labs lane) holds at
   any memory that satisfies its premises, mem_inv included.  The real memory holds the read-only image bytes, so it
   has no mem_inv; MemNorm.normalize drops them.  mb_post_rebaseF runs the stretch on mn := MemNorm.normalize rsegs mb
   (an INSTANTIATION of mb_retF and hbF_body at m := m1 := mn: the class-0 frame of the request is the side-arm frame
   fs_frame FS 0 j, the call's post is built at m2 := mn).  The consumer carries the run from mn back to mb with
   a Theorem Labs lane's shared lift rrB_lift (lib/B/Prog/GlueLift.v, moved there from C_reac_ctrl_identity_replyPf.v), which applies image B's
   MemNormF.evtF_normalize_ro (PROVED); this file takes no hypothesis for it.

   The memory facts move to the normalized memory by image B's MemNormTr (a working branch
   473ae68ba1c, merged here): stk_normalize_ro (the GUARDED form, a Theorem Labs lane 03:41Z name), addressable_normalize,
   asan_cells_normalize, shadow_rw_normalize, rw_cells_normalize (with its not-read-only premise) and
   ro_addr_above_img_range; bytes_at by lib/B/MemNorm.v's bytes_at_normalize; mem_inv of mn is MemNorm.mem_inv_normalize.
   fp and reac_box_model_block_tls move by MemNormTr's fp_normalize and tls_dj_normalize (a working branch
   0fa3ec38d61; reac_box_model_block_tls is tls_dj m TP (fp_w [0%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]) by
   reflexivity).  This file has NO Section hypothesis.

   Three places where mb_post_rebaseF's premises differ from hbF_ctx read at mb (for the auditor):
   - mem_inv rsegs mb is NOT a premise: the real memory holds the read-only image bytes, so it never has mem_inv;
     the stretch's mem_inv is MemNorm.mem_inv_normalize at mn (decisions.md item 27a).
   - ONE premise is ADDED, `o <> 0 -> forall i, 0 <= i < 32 -> ro_addr rsegs (wa (o + i)) = false`: MemNormTr's
     rw_cells_normalize needs [o, o + 32) not read-only and no hbF_ctx premise gives it; the cgif spec's
     `forall a, o <= a < o + 32 -> ~ in_img SEGS a` gives it at the call.
   - asan_stack_malloc_0_contract_F (HSM) STAYS a premise, because hbF_body's context hbF_ctx lists it; the
     re-based stretch is therefore F6-conditional until hbF_ctx drops it (the post-call stretch never applies it).

   rule 24: no function proved (the re-base of the proved run reac_box_model_block_holds_F). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_blockF reac_box_model_block_holdsF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr.
Import ListNotations.
Open Scope Z_scope.

Section Rebase.
  (* The stretch's base memory: the memory at the return of __asan_stack_malloc_0. *)
  Variable mb : word -> option byte.

  (* The post-call stretch at the real memory mb.  ra, sp, s0 .. s11 are the function's ENTRY values (the saved
     registers, Q0); the state is the one the class-0 post pins (mb_retF, asan_stack_malloc_post): ra = 0x86648, sp = A,
     s0 = the entry sp, s1 = A, a0 = the frame, s3 = o, s4 = p, s6 = b, s9 = the shadow offset. *)
  Lemma mb_post_rebaseF :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (p b o FS A : Z) (row nb ob : list byte) (RNG : footprint) (j fr : Z)
           (u0 u1 u2 u3 u4 u5 u6 x1 x2 x3 x4 x5 x6 x7 : word),
      (* (a) *)
      MemNorm.ro_agree rsegs mb ->
      (* (b) the premises of hbF_ctx (reac_box_model_block_holdsF.v:27-67) at mb with off := ASAN_K, but for
         mem_inv (mn has it by MemNorm.mem_inv_normalize; the real memory has none) and the callee forms ((e)) *)
      A = (bv_unsigned sp - 160) / 32 * 32 ->
      bv_unsigned sp mod 16 = 0 ->
      stk rsegs mb (bv_unsigned sp - 4272) (bv_unsigned sp) ->
      asan_cells mb ->
      shadow_rw mb ->
      HIGHMEM_BEG <= bv_unsigned sp - 4272 ->
      bv_unsigned sp <= APPMEM_END ->
      addressable mb (bv_unsigned sp - 4272) 4272 ->
      fp [0%nat] mb (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
        (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
      reac_box_model_block_tls mb (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
      0 <= p < 2^64 ->
      0 <= b < 2^64 ->
      0 <= o < 2^64 ->
      (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs mb p row /\
         (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
      (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
         name_ok nb /\ bytes_at rsegs mb (rname row) nb /\
         (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
         (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
      (o <> 0 -> rw_cells rsegs mb o [CB 32 ob] /\
         (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
      (* the not-read-only premise of rw_cells_normalize for o's cells (the glue's `~ in_img SEGS a` of [o, o + 32)) *)
      (o <> 0 -> forall i, 0 <= i < 32 -> ro_addr rsegs (wa (o + i)) = false) ->
      (p <> 0 -> addressable mb p 296) ->
      (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
         addressable mb (rname row) (Z.of_nat (length nb))) ->
      (o <> 0 -> addressable mb o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
      (b = 1 -> addressable mb JOIN_0014 32) ->
      (b = 2 -> addressable mb JOIN_0013 32) ->
      (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
         fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
      (* (c) the class-0 frame fr = fs_frame FS 0 j, as the side arm of the request's post gives it *)
      0 <= j < fs_M 0 ->
      fr = fs_frame FS 0 j ->
      fr mod 64 = 0 ->
      bytes_at rsegs mb (fs_flag FS 0 j) [Z_to_bv 8 1] ->
      bytes_at rsegs mb (fr + 24) (le8 (Z_to_bv 64 A)) ->
      bytes_at rsegs mb (fr + 64 - 8) (le8 (Z_to_bv 64 (fs_flag FS 0 j))) ->
      bytes_at rsegs mb (shadow_addr fr) (repeat (Z_to_bv 8 0) 8) ->
      addressable mb fr 64 ->
      stk rsegs mb fr (fr + 64) ->
      (forall a, fr <= a < fr + 64 -> app_mem a) ->
      FS <= fr ->
      fr + 64 <= FS + FS_SIZE ->
      ASAN_GT <= fr ->
      fr + 64 <= A - 208 ->
      (forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> 0%nat \/ j' <> j) ->
         fs_frame FS c' j' + fs_B c' <= fr \/ fr + 64 <= fs_frame FS c' j') ->
      (exists hh : word, bytes_at rsegs mb (fs_hint FS 0) (le8 hh)) ->
      (* (d) the window *)
      stk rsegs mb (bv_unsigned sp - 4272) (bv_unsigned sp - 160) ->
      stk rsegs mb (bv_unsigned sp - 160) (bv_unsigned sp + -88) ->
      stk rsegs mb (bv_unsigned sp - 4272) A ->
      rw_cells rsegs mb (bv_unsigned sp + -88)
        [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (* (e) the callee footprint forms and the run's footprint at mn *)
      asan_stack_malloc_0_contract_F ->
      asan_memset_contract_F ->
      asan_memcpy_contract_F ->
      build_dt1_single_contract_F ->
      dt1_head_contract_F ->
      name_field_contract_F ->
      mbF_rng RNG (MemNorm.normalize rsegs mb) sp tp p b o FS row nb ->
      ExecF.evtF rsegs RNG
        (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb) p b o FS row nb)
        (MS (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 fr)
                 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa ASAN_K) s10 s11
                 u3 u4 u5 u6)
            F (Z_to_bv 64 0x86648) fc None (MemNorm.normalize rsegs mb) (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p b o FS A row nb ob RNG j fr
      u0 u1 u2 u3 u4 u5 u6 x1 x2 x3 x4 x5 x6 x7
      RO HA HS16 ST0 AC0 SR0 HHM HAE AW0 FP0 TLS0 Rp Rb Ro HP HN HO HOro AP ANB AO AJ1 AJ2 NDJ
      Hj Efr Hm64 HFL H24 H56 HSH HADD STF APF FSlo FShi GT FRA DIS HH
      STa STb STA FR
      HSM HMS HMC HBD HDH HNF HRNG.
    (* 1. the stretch runs on mn (the consumer lifts it to mb: rrB_lift, MemNormF.evtF_normalize_ro) *)
    set (mn := MemNorm.normalize rsegs mb) in *.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    assert (HAb : bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160) by (rewrite HA; Z.div_mod_to_equations; lia).
    (* 2. stk_normalize_ro's guard, each as its own fact: the window from HIGHMEM_BEG <= sp - 4272 ... *)
    assert (GW : ImgBounds.IMG_HI <= bv_unsigned sp - 4272) by (unfold ImgBounds.IMG_HI; lia).
    assert (GW160 : ImgBounds.IMG_HI <= bv_unsigned sp - 160) by (unfold ImgBounds.IMG_HI; lia).
    (* ... and the class-0 frame from ASAN_GT <= fr *)
    assert (GF : ImgBounds.IMG_HI <= fr) by (pose proof GT as GT'; unfold ASAN_GT in GT'; unfold ImgBounds.IMG_HI; lia).
    (* the premises at mn *)
    pose proof (MemNorm.mem_inv_normalize rsegs mb) as MIn.
    pose proof (MemNormTr.stk_normalize_ro _ _ _ RO GW ST0) as ST0n.
    pose proof (MemNormTr.asan_cells_normalize _ RO AC0) as AC0n.
    pose proof (MemNormTr.shadow_rw_normalize _ RO SR0) as SR0n.
    pose proof (MemNormTr.addressable_normalize _ _ _ RO AW0) as AW0n.
    pose proof (MemNormTr.fp_normalize _ _ _ _ _ _ _ _ RO FP0) as FP0n.
    pose proof (MemNormTr.tls_dj_normalize _ _ _ RO TLS0) as TLS0n.
    (* 4. the body from 0x866d4 at mn (KBF) *)
    assert (KB : KBF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn p b o FS ASAN_K A RNG
                   (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn p b o FS row nb)).
    { pose proof (hbF_body hbF_tail_ok hbF_case0_ok hbF_c3 hbF_c4 hbF_c5 hbF_c6
                    ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn p b o FS ASAN_K A row nb ob RNG) as HB.
      unfold hbF_ctx in HB.
      refine (HB HSM eq_refl HA HS16 ST0n MIn AC0n SR0n HHM HAE AW0n FP0n TLS0n Rp Rb Ro _ _ _ _ _ _ _ _ NDJ
                HMS HMC HBD HDH HNF HRNG).
      - intros Hp. destruct (HP Hp) as (P1 & P2 & P3 & P4 & P5).
        exact (conj P1 (conj P2 (conj (MemNorm.bytes_at_normalize rsegs mb p row RO P3) (conj P4 P5)))).
      - intros Hp Hb Hh Hr. destruct (HN Hp Hb Hh Hr) as (N1 & N2 & N3 & N4).
        exact (conj N1 (conj (MemNorm.bytes_at_normalize rsegs mb _ nb RO N2) (conj N3 N4))).
      - intros Ho. destruct (HO Ho) as (O1 & O2 & O3).
        refine (conj _ (conj O2 O3)). apply (MemNormTr.rw_cells_normalize _ _ _ RO); [|exact O1].
        intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply (HOro Ho). lia.
      - intros Hp. exact (MemNormTr.addressable_normalize _ _ _ RO (AP Hp)).
      - intros Hp Hb Hh Hr. exact (MemNormTr.addressable_normalize _ _ _ RO (ANB Hp Hb Hh Hr)).
      - intros Ho. destruct (AO Ho) as (A1 & A2 & A3). exact (conj (MemNormTr.addressable_normalize _ _ _ RO A1) (conj A2 A3)).
      - intros Hb. exact (MemNormTr.addressable_normalize _ _ _ RO (AJ1 Hb)).
      - intros Hb. exact (MemNormTr.addressable_normalize _ _ _ RO (AJ2 Hb)). }
    (* 3. the return from the class-0 request at m := m1 := m2 := mn, the side arm with i := 0, h := j *)
    eapply (mb_retF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn p b o FS ASAN_K A row nb RNG
              eq_refl HA HS16 ST0n SR0n HHM HAE AW0n FP0n HRNG _ mn (Z_to_bv 64 j)
              (repeat (Z_to_bv 8 0) (Z.to_nat (fs_M 0))) _ KB).
    - (* mb_pre_facts mn *)
      unfold mb_pre_facts.
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply rd_mono_refl|].
      split; [exact MIn|].
      split; [|split; [exact (MemNormTr.stk_normalize_ro _ _ _ RO GW STa) | exact (MemNormTr.stk_normalize_ro _ _ _ RO GW160 STb)]].
      apply (MemNormTr.rw_cells_normalize _ _ _ RO); [|exact FR].
      intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      apply (MemNormTr.ro_addr_above_img_range (bv_unsigned sp + -88) 88);
        [unfold ImgBounds.IMG_HI in GW |- *; lia | lia | lia].
    - (* the post of the class-0 request *)
      pose proof FP0n as (DT & TS & C & T & DB & k & _ & _ & HPL & _).
      unfold asan_stack_malloc_post.
      exists u0, u1, u2, (Z_to_bv 64 fr), x1, x2, x3, x4, x5, x6, x7, u3, u4, u5, u6, mn.
      split; [rewrite (ret_pc_even 0x86648) by first [lia | reflexivity]; reflexivity|].
      split; [apply wmono_refl|].
      split; [exact MIn|].
      split; [rewrite (unsigned_lit A) by lia; exact (MemNormTr.stk_normalize_ro _ _ _ RO GW STA)|].
      split; [exact HPL|].
      split; [destruct HH as (hh & HHb); exists hh; exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HHb)|].
      right. exists 0.
      assert (EM : fs_M 0 = 16384) by reflexivity.
      assert (Ej : (bv_unsigned (Z_to_bv 64 j) + 0) mod fs_M 0 = j).
      { rewrite EM in Hj |- *. rewrite unsigned_lit by lia. rewrite Z.add_0_r. apply Z.mod_small. lia. }
      rewrite Ej.
      split; [lia|].
      split; [intros i' Hi'; lia|].
      split; [apply nth_error_repeat; lia|].
      unfold asan_stack_malloc_frame. cbv zeta.
      rewrite <- Efr.
      rewrite (unsigned_lit A), (unsigned_lit 64) by lia.
      replace (fs_B 0) with 64 by reflexivity.
      replace (fs_shadow_n 0 64) with 8 by reflexivity.
      unfold ASAN_STACK_MALLOC_K.
      split; [reflexivity|].
      split; [exact Hm64|].
      split; [intros Hc; lia|].
      split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HFL)|].
      split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO H24)|].
      split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO H56)|].
      split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HSH)|].
      split; [exact (MemNormTr.addressable_normalize _ _ _ RO HADD)|].
      split; [exact (MemNormTr.stk_normalize_ro _ _ _ RO GF STF)|].
      split; [exact APF|].
      split; [exact FSlo|].
      split; [exact FShi|].
      split; [exact GT|].
      split; [exact FRA|].
      split; [exact DIS|].
      apply munch_refl.
  Qed.
End Rebase.

Print Assumptions mb_post_rebaseF.
