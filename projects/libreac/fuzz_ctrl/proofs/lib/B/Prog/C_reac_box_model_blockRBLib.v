(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): stretch B, from the class-0 return 0x86648 to ret,
   RE-BASED at the real memory mb and exporting its OWN write list (decision 125 (a working note, not in this delivery), a Theorem Labs lane 05:51Z, on a Theorem Labs lane's
   ruling).  A Theorem Labs lane.

   It runs the GENERATED re-based copy C_reac_box_model_blockRB* (gen_rb_modelblock.py, see the header of each copy)
   instead of the accepted _F files: there the munch list Wf has the class-0 hint word replaced by the empty interval
   (FS, FS), and the post Q0 fr j n adds `munch (Wf fr j n ++ the output block) m (ms_mem ms)` at the RUN FRAME - the
   stretch's own writes: the window, flag j, the frame fs_frame FS 0 j and its shadow, the output block (generator
   item 10).  The hint is allocator-owned
   and not an awr_byte, and stretch B never stores to it.

   mb_post_rebaseRB: the stretch on mn := MemNorm.normalize rsegs mb (the consumer lifts it to mb with a Theorem Labs lane's
   rrB_lift), entered by the copy's mb_sideF at the class-0 return with BI built from munch_refl at mn, then the copy's
   hbF_body.  The return address ra0 is general (cgif's malloc contract keeps only the acallee_saved registers;
   generator item 9).  Its premises are those of the accepted Lib's mb_post_rebaseF that this entry needs: the frame facts the
   original malloc post supplied for mb_retF are not needed (mb_sideF takes BI directly).  No Section hypothesis.

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
  C_reac_box_model_blockRB C_reac_box_model_blockRBF C_reac_box_model_blockRB_holdsF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ShadowRwOn ShadowRwOnT.
(* route (C): the run's region and the callee _on contracts the narrowed copy's hbF_ctx takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on
  asan_stack_malloc_cF_on asan_memset_cF_on asan_memcpy_cF_on name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

Section RebaseRB.
  (* The stretch's base memory: the memory at the return of __asan_stack_malloc_0. *)
  Variable mb : word -> option byte.

  Lemma mb_post_rebaseRB :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (p b o FS A : Z) (row nb ob : list byte) (RNG : footprint) (j fr : Z)
           (ra0 u0 u1 u2 u3 u4 u5 u6 x1 x2 x3 x4 x5 x6 x7 : word),
      (* (a) *)
      MemNorm.ro_agree rsegs mb ->
      (* (b) the premises of hbF_ctx at mb with off := ASAN_K, but for mem_inv (mn has it by mem_inv_normalize) *)
      A = (bv_unsigned sp - 160) / 32 * 32 ->
      bv_unsigned sp mod 16 = 0 ->
      stk rsegs mb (bv_unsigned sp - 4272) (bv_unsigned sp) ->
      asan_cells mb ->
      B.ShadowRwOn.shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) mb ->
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
      (* (c) the class-0 frame fr = fs_frame FS 0 j and the two words the stretch reads: the back-pointer at fr + 56
         and the hint word (both as the request's post leaves them) *)
      0 <= j < fs_M 0 ->
      fr = fs_frame FS 0 j ->
      bytes_at rsegs mb (fr + 64 - 8) (le8 (Z_to_bv 64 (fs_flag FS 0 j))) ->
      (exists hh : word, bytes_at rsegs mb (fs_hint FS 0) (le8 hh)) ->
      (* (d) the saved registers *)
      rw_cells rsegs mb (bv_unsigned sp + -88)
        [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (* (e) the callee footprint forms and the run's footprint at mn *)
      asan_stack_malloc_0_contract_F_on ->
      asan_memset_contract_F_on ->
      asan_memcpy_contract_F_on ->
      build_dt1_single_contract_F_on ->
      dt1_head_contract_F_on ->
      name_field_contract_F_on ->
      mbF_rng RNG (MemNorm.normalize rsegs mb) sp tp p b o FS row nb ->
      ExecF.evtF rsegs RNG
        (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb) p b o FS row nb fr j 1)
        (MS (mkR ra0 (Z_to_bv 64 A) gp tp u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 fr)
                 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa ASAN_K) s10 s11
                 u3 u4 u5 u6)
            F (Z_to_bv 64 0x86648) fc None (MemNorm.normalize rsegs mb) (seg_rom rsegs)).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p b o FS A row nb ob RNG j fr
      ra0 u0 u1 u2 u3 u4 u5 u6 x1 x2 x3 x4 x5 x6 x7
      RO HA HS16 ST0 AC0 SR0 HHM HAE AW0 FP0 TLS0 Rp Rb Ro HP HN HO HOro AP ANB AO AJ1 AJ2 NDJ
      Hj Efr H56 HH FR
      HSM HMS HMC HBD HDH HNF HRNG.
    (* 1. the stretch runs on mn (the consumer lifts it to mb: rrB_lift, MemNormF.evtF_normalize_ro) *)
    set (mn := MemNorm.normalize rsegs mb) in *.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    (* 2. stk_normalize_ro's guard, as its own fact: the window from HIGHMEM_BEG <= sp - 4272 *)
    assert (GW : ImgBounds.IMG_HI <= bv_unsigned sp - 4272) by (unfold ImgBounds.IMG_HI; lia).
    (* the premises at mn *)
    pose proof (MemNorm.mem_inv_normalize rsegs mb) as MIn.
    pose proof (MemNormTr.stk_normalize_ro _ _ _ RO GW ST0) as ST0n.
    pose proof (MemNormTr.asan_cells_normalize _ RO AC0) as AC0n.
    pose proof (B.ShadowRwOnT.shadow_rw_on_normalize _ _ RO SR0) as SR0n.
    pose proof (MemNormTr.addressable_normalize _ _ _ RO AW0) as AW0n.
    pose proof (MemNormTr.fp_normalize _ _ _ _ _ _ _ _ RO FP0) as FP0n.
    pose proof (MemNormTr.tls_dj_normalize _ _ _ RO TLS0) as TLS0n.
    (* 3. the body from 0x866d4 at mn (KBF), from the copy's hbF_body *)
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
    (* 4. the entry at the class-0 return: the copy's mb_sideF, its BI from munch_refl at mn *)
    subst fr.
    apply (mb_sideF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn p b o FS ASAN_K A row nb RNG
             eq_refl HA HS16 ST0n SR0n HHM HAE AW0n FP0n HRNG _ j ra0 x1 x2 x3 x4 x5 x6 x7 u0 u1 u2 u3 u4 u5 u6 KB Hj).
    unfold BI.
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply rd_mono_refl|].
    split; [exact MIn|].
    split.
    { apply (MemNormTr.rw_cells_normalize _ _ _ RO); [|exact FR].
      intros i Hi. unfold SAVES in Hi. cbn [cells_size csize Nat.add] in Hi.
      apply (MemNormTr.ro_addr_above_img_range (bv_unsigned sp + -88) 88);
        [unfold ImgBounds.IMG_HI in GW |- *; lia | lia | lia]. }
    split.
    { destruct HH as (hh & HHb). exists hh.
      replace FS with (fs_hint FS 0) by (unfold fs_hint; cbn [Z.of_nat]; lia).
      exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HHb). }
    replace (fs_frame FS 0 j + 56) with (fs_frame FS 0 j + 64 - 8) by lia.
    exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO H56).
  Qed.
End RebaseRB.

Print Assumptions mb_post_rebaseRB.
