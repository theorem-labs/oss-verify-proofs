(* rewind (musl src/stdio/rewind.c), PLAIN build: the walk of rewind_contract (lib/Prog/rewind_c.v) on the
   plain image, 0x19bc4..0x19c50 (144 bytes; link/pf/dis/plain/rewind.s), from fseeko0_contract for the one
   call it makes (+0x6c, jal __fseeko_unlocked). Every instruction is fetched from the image the proof loads
   and decoded there (lib/Lib/Step.v `step`).
   The FILE's lock is -1 (MemFile.v memfile_static, +140), so `bltz` at +0x18 skips __lockfile and the
   __unlockfile tail; rewind calls __fseeko_unlocked(f, 0, SEEK_SET) (+0x6c), then clears F_ERR
   (+0x70 lwu, +0x74 andi -0x21, +0x78 sw) and returns. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c mk_leaf leaf_call mf_walk
  pf_tac fseeko_c rewind_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YI14 YK11 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* Step.v's addr_eq_tac proves `x = wa e` only; the store through the register that holds the FILE's address
   itself (`sw a0, 0(s0)`, +0x78) also needs `wa e = x` *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* rewind_contract's write set and post, as functions of the register maps *)
Definition rw_wr (f : Z) : bvmap 5 word -> (word -> option byte) -> list ivl :=
  fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)].
Definition rw_post (f k om pos len : Z) (pb : list byte) :
    bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs m regs' m' =>
    let n1 := mf_n1 k pos in
    memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
    bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
    mf_dyn m' f MemFile.F_NORD om 0 0 0 (if n1 <? k then pos + n1 else 0) (Z.max len (pos + n1)).

Theorem rewind_proof : fseeko0_contract -> rewind_contract.
Proof.
  intros HF. unfold rewind_contract.
  intros f k fl om wend wpos wbase pos len pb.
  apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in *. unfold getr_same in E.
    unfold arg, errno_ok, errno_at, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. cbv beta. unfold getr_same in E. unfold errno_at. rewrite E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. exact H.
  - unfold leaf_walk, REWIND.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros Hpre MI ST LO SP.
    match goal with |- evt _ ?Q _ => set (QF := Q) end.
    assert (QC : forall c a, QF c -> ms_eqv c a -> QF a).
    { intros c a Hc Ha. unfold QF in *.
      eapply (leaf_walk_close REWIND_K (rw_wr f) (rw_post f k om pos len pb)); [ | exact Hc | exact Ha ].
      intros r1 r2 m0 q1 q2 m' E E' H. exact H. }
    cbv beta in Hpre.
    destruct Hpre as (A0 & HK & HD & HPB & HLEN & AFB & AFS & HE & HTOP & HG).
    change (bv_unsigned a0 = f) in A0. subst f.
    destruct HE as (EW & EF & ERB & ERS & ERG & ERY).
    unfold apart_frame in AFB, AFS, EF.
    repeat match goal with H : context [spZ ?R] |- _ => change (spZ R) with (bv_unsigned sp) in H end.
    repeat match goal with H : context [errno_at ?R] |- _ =>
             change (errno_at R) with (bv_unsigned tp + ERRNO_TP_OFF) in H end.
    unfold REWIND_K, ERRNO_TP_OFF, MemFile.MF_BLOCK, rapart in *.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MUF.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
                            (A_G_SAID, A_G_SAID + SAID_SIZE); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m)
      as MU.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    pose proof (memfile_k_place _ _ _ HK) as HPL.
    pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _).
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep.
    (* the prologue's three stores miss the FILE, g_said, errno and the GOT slot *)
    assert (OF : forall z, bv_unsigned a0 <= z < bv_unsigned a0 + MemFile.MF_BLOCK ->
                           outside [(bv_unsigned sp - 32, bv_unsigned sp)] z)
      by (intros z Hz; cbn [outside]; unfold MemFile.MF_BLOCK in *; lia).
    pose proof (memfile_k_munch _ _ _ _ _ HK MUF WM OF) as HK1.
    pose proof (mf_dyn_munch _ _ _ _ _ _ _ _ _ _ _ HD MUF F0 F1 OF) as HD1.
    pose proof (win_facts _ _ _ _ _ _ _ _ _ _ HK HD) as (_ & _ & HKR).
    pose proof (pend_munch _ _ _ _ _ HPB MUF ltac:(lia) OF) as HPB1.
    pose proof (guard_keep _ _ _ HG MUF ltac:(intros z Hz; cbn [outside]; unfold GOT_GUARD, IMG_TOP in *; lia)) as HG1.
    pose proof (flags_val _ _ _ _ _ _ _ _ _ _ HK HD) as HFL.
    clear HK HD HPB HG MUF OF.
    pose proof (cells_lock _ _ _ HK1) as CL. unfold YI14.U32M1 in CL.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by (symmetry; vm_compute; reflexivity) end; cbv iota.
    zstep. zstep. zstep. zstep.
    pose proof EW as (EW0 & _).
    unfold mf_place_ok, A_G_SAID, SAID_SIZE, IMG_TOP, GOT_GUARD, A_G_SAY, IMG_LO, MemFile.MF_BLOCK in *.
    eapply leaf_call;
      [ exact (HF (bv_unsigned a0) k fl om wend wpos wbase pos len pb)
      | intros r1 r2 m0' q1 q2 m' E E' H; cbv beta zeta in *; unfold getr_same in E'; rewrite <- !E'; exact H
      | exact QC | | exact MI | | | | ].
    * (* __fseeko_unlocked's Pre at the call: f, 0, SEEK_SET, the FILE, errno, the frame at sp - 32 *)
      cbv beta. unfold arg, errno_ok, errno_at, apart_frame, spZ, rapart, FSEEKO_K, ERRNO_TP_OFF.
      getr_simp. rewrite ?unsigned_lit by lia.
      unfold A_G_SAID, SAID_SIZE, IMG_TOP, GOT_GUARD, A_G_SAY, MemFile.MF_BLOCK.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HK1|]. split; [exact HD1|]. split; [exact HPB1|]. split; [exact HLEN|].
      split; [lia|]. split; [lia|].
      split; [split; [exact EW | repeat split; lia]|]. split; [lia | exact HG1].
    * rewrite unsigned_lit by lia. exact ST.
    * rewrite unsigned_lit by lia. unfold FSEEKO_K. lia.
    * rewrite unsigned_lit by lia. lia.
    * intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 PO2.
      cbv beta zeta in PO2. destruct PO2 as (HK2 & HPB2 & HSB2 & PLT & PEQ).
      replace (ret_pc (Z_to_bv 64 105524)) with (Z_to_bv 64 105524)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      rewrite unsigned_lit in ST2 by lia.
      assert (MU2' : munch [(bv_unsigned sp + -160, bv_unsigned sp + -32); (bv_unsigned a0, bv_unsigned a0 + 272);
                            (476464, 476464 + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m0 m2).
      { eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
        cbv beta. unfold errno_at, mf_hdr, mf_said, MemFile.MF_ZEROED, ERRNO_TP_OFF, A_G_SAID, SAID_SIZE, FSEEKO_K.
        getr_simp. rewrite unsigned_lit by lia. cbn [outside] in *. lia. }
      clear MU2.
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32)
                      [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MU2' WM2).
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      assert (MUm2 : munch [(bv_unsigned sp - 160, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
                            (476464, 476464 + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m2).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2'].
        unfold sub_fp. intros x Hx. cbn [outside] in *. lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMm2.
      clear FR MU WM MU2' WM2.
      (* the flags __fseeko_unlocked leaves: F_NORD, with F_ERR when the flush passed g_said's end *)
      assert (HD2 : exists fl2, (fl2 = 4 \/ fl2 = 36) /\
                mf_dyn m2 (bv_unsigned a0) fl2 om 0 0 0 (if mf_n1 k pos <? k then pos + mf_n1 k pos else 0)
                       (Z.max len (pos + mf_n1 k pos))).
      { destruct (Z.lt_ge_cases (mf_n1 k pos) k) as [Hlt | Hge].
        - destruct (PLT Hlt) as (_ & D). exists (Z.lor fl MemFile.F_ERR). split.
          + right. destruct HFL as [-> | ->]; reflexivity.
          + rewrite (proj2 (Z.ltb_lt _ _) Hlt). exact D.
        - assert (Hn1 : mf_n1 k pos = k) by (unfold mf_n1 in *; lia).
          destruct (PEQ Hn1) as (_ & D). exists fl. split; [exact HFL|].
          rewrite Hn1, Z.ltb_irrefl. exact D. }
      destruct HD2 as (fl2 & HFL2 & HD2). clear PLT PEQ.
      pose proof (cells_flags _ _ _ _ _ _ _ _ _ _ HK2 HD2) as CF.
      pose proof HD2 as (Rfl2 & Rom2 & _ & _ & _ & RP2 & RL2 & _ & Dom2 & Dwend2 & Dwpos2 & Dwbase2 & Dpos2 & Dlen2).
      pose proof HK2 as (HA2 & _ & TWB2 & TWS2 & _).
      assert (SB2 : hold (bytes_at rsegs m2 (A_G_SAID + pos) (firstn (Z.to_nat (mf_n1 k pos)) pb))) by exact HSB2.
      clear HSB2.
      pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 4)] m2) as MU5.
      pose proof (wmono_refl rsegs m2) as WM5.
      zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => rename mf into m7 end.
      assert (FV : Z.land (bv_unsigned (zx32 (Z_to_bv 64 fl2))) 18446744073709551583 = 4)
        by (destruct HFL2 as [-> | ->]; vm_compute; reflexivity).
      rewrite FV in CF.
      pose proof (val_of_cell4 _ _ _ CF ltac:(lia)) as VFL.
      unfold mf_fld, MemFile.MF_COOKIE in *.
      assert (K5 : forall a n v, bv_unsigned a0 + 4 <= a -> a + Z.of_nat n <= bv_unsigned a0 + 1304 ->
                     YI04.val_mem rsegs m2 a n v -> YI04.val_mem rsegs m7 a n v).
      { intros a n v H1 H2 H. apply (val_munch _ _ _ _ _ _ H MU5); [lia | lia |].
        intros z Hz. cbn [outside]. lia. }
      apply evt_done. unfold QF.
      eexists _, _. split; [reflexivity|].
      split; [regs_pres|].
      split; [exact MUm2|]. split; [exact WMm2|]. split; [exact MI2|]. split; [exact ST2|].
      split.
      { split.
        - apply (memfile_at_reflag _ m2 m7 _ HA2 MU5).
          + intros z Hz. cbn [outside]. lia.
          + unfold MemFile.memfile_flags. left. rewrite Z.add_0_r. exact VFL.
        - split; [left; split; [reflexivity|];
                  split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwend2]|];
                  split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwpos2]|];
                  apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwbase2]|].
          split; [exact TWB2|].
          split; [exact TWS2|].
          unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK. lia. }
      split.
      { unfold mf_pend_bytes in *. apply (bytes_munch _ m2 m7 _ pb HPB2 MU5).
        intros z Hz. unfold MemFile.MF_BUF in Hz. cbn [outside]. lia. }
      split.
      { unfold hold in SB2. apply (bytes_munch _ m2 m7 _ _ SB2 MU5).
        intros z Hz. rewrite length_firstn in Hz. pose proof HD1 as (_ & _ & _ & _ & _ & Rp & Rl & _).
        unfold A_G_SAID, SAID_SIZE, MemFile.MF_BUFSIZ in *. cbn [outside]. lia. }
      unfold mf_dyn, mf_fld, MemFile.MF_COOKIE, MemFile.F_NORD.
      split; [lia|]. split; [exact Rom2|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact RP2|]. split; [exact RL2|].
      split; [rewrite Z.add_0_r; exact VFL|].
      split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dom2]|].
      split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwend2]|].
      split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwpos2]|].
      split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dwbase2]|].
      split; [apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dpos2]|].
      apply K5; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Dlen2].
Qed.
