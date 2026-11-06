(* __fseeko_unlocked (musl src/stdio/fseek.c), PLAIN build: the walk of fseeko0_contract
   (lib/Prog/fseeko_c.v) on the plain image, 0x19c54..0x19d28 (216 bytes;
   link/pf/dis/plain/__fseeko_unlocked.s), from mwrite_contract and mseek_set_contract for the two
   indirect calls it makes. Every instruction is fetched from the image the proof loads and decoded there
   (lib/Lib/Step.v `step`).
   With off = 0 and whence = SEEK_SET the two whence tests (+0x18, +0x34) pass. When wpos <> wbase (+0x54:
   k > 0 bytes pending) it loads f->write (+0x58; memfile_at fixes it to mwrite, 0x19544) and calls it with
   (f, 0, 0) (+0x70, `leaf_call`); if wpos is then 0 (the flush passed g_said's end) it returns -1 (+0x80).
   Otherwise (`TAIL`, +0x84) it loads f->seek (mseek, 0x19658), zeroes wend / wpos / wbase, calls it with
   (f, 0, 0) (+0x98), finds 0, clears F_EOF (already clear: the flags are F_NORD or F_NORD | F_ERR),
   zeroes rpos / rend and returns 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c mk_leaf leaf_call mf_walk
  pf_tac mwrite_c mseek_c fseeko_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YK11 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* fseeko0_contract's write set and post, as functions of the register maps *)
Definition fs_wr (f : Z) : bvmap 5 word -> (word -> option byte) -> list ivl :=
  fun regs m => [mf_hdr f; mf_said; (errno_at regs, errno_at regs + 4)].
Definition fs_post (f k fl om pos len : Z) (pb : list byte) :
    bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs m regs' m' =>
    let n1 := mf_n1 k pos in
    memfile_k m' f 0 /\ mf_pend_bytes m' f pb /\
    bytes_at rsegs m' (A_G_SAID + pos) (firstn (Z.to_nat n1) pb) /\
    (n1 < k ->
       getr regs' 10 = wz (-1) /\
       mf_dyn m' f (Z.lor fl MemFile.F_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
    (n1 = k ->
       getr regs' 10 = wz 0 /\
       mf_dyn m' f fl om 0 0 0 0 (Z.max len (pos + k))).

(* Step.v's addr_eq_tac proves `x = wa e` only; a store through a register that holds the FILE's address
   itself (`sw a1, 0(s0)`, +0xac) also needs `wa e = x` *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Theorem fseeko0_proof : mwrite_contract -> mseek_set_contract -> fseeko0_contract.
Proof.
  intros HMW HMS. unfold fseeko0_contract.
  intros f k fl om wend wpos wbase pos len pb.
  apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in *. unfold getr_same in E.
    unfold arg, errno_ok, errno_at, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. cbv beta. unfold getr_same in E. unfold errno_at. rewrite E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta zeta in *. unfold getr_same in E'. rewrite <- E'. exact H.
  - unfold leaf_walk, FSEEKO.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros Hpre MI ST LO SP.
    match goal with |- evt _ ?Q _ => set (QF := Q) end.
    assert (QC : forall c a, QF c -> ms_eqv c a -> QF a).
    { intros c a Hc Ha. unfold QF in *.
      eapply (leaf_walk_close FSEEKO_K (fs_wr f) (fs_post f k fl om pos len pb)); [ | exact Hc | exact Ha ].
      intros r1 r2 m0 q1 q2 m' E E' H. unfold fs_post in *. cbv beta zeta in *.
      unfold getr_same in E'. rewrite <- E'. exact H. }
    cbv beta in Hpre.
    destruct Hpre as (A0 & A1 & A2 & HK & HD & HPB & HLEN & AFB & AFS & HE & HTOP & HG).
    change (bv_unsigned a0 = f) in A0. change (bv_unsigned a1 = 0) in A1. change (bv_unsigned a2 = 0) in A2.
    subst f.
    assert (E1 : a1 = Z_to_bv 64 0) by (apply bv_eq; rewrite A1; reflexivity).
    assert (E2 : a2 = Z_to_bv 64 0) by (apply bv_eq; rewrite A2; reflexivity).
    subst a1 a2. clear A1 A2.
    destruct HE as (EW & EF & ERB & ERS & ERG & ERY).
    unfold apart_frame in AFB, AFS, EF.
    repeat match goal with H : context [spZ ?R] |- _ => change (spZ R) with (bv_unsigned sp) in H end.
    repeat match goal with H : context [errno_at ?R] |- _ =>
             change (errno_at R) with (bv_unsigned tp + ERRNO_TP_OFF) in H end.
    unfold FSEEKO_K, ERRNO_TP_OFF, MemFile.MF_BLOCK, rapart in *.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MUF.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
                            (A_G_SAID, A_G_SAID + SAID_SIZE); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m)
      as MU.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    pose proof (memfile_k_place _ _ _ HK) as HPL.
    pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ HK)) as (F0 & F1 & _).
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep. zstep.
    (* the prologue's four stores miss the FILE, g_said, errno and the GOT slot *)
    assert (OF : forall z, bv_unsigned a0 <= z < bv_unsigned a0 + MemFile.MF_BLOCK ->
                           outside [(bv_unsigned sp - 32, bv_unsigned sp)] z)
      by (intros z Hz; cbn [outside]; unfold MemFile.MF_BLOCK in *; lia).
    pose proof (memfile_k_munch _ _ _ _ _ HK MUF WM OF) as HK1.
    pose proof (mf_dyn_munch _ _ _ _ _ _ _ _ _ _ _ HD MUF F0 F1 OF) as HD1.
    pose proof (win_facts _ _ _ _ _ _ _ _ _ _ HK HD) as (HWW & HWB & HKR).
    pose proof (pend_munch _ _ _ _ _ HPB MUF ltac:(lia) OF) as HPB1.
    pose proof (guard_keep _ _ _ HG MUF ltac:(intros z Hz; cbn [outside]; unfold GOT_GUARD, IMG_TOP in *; lia)) as HG1.
    clear HK HD HPB HG MUF OF.
    pose proof HD1 as (Rfl & Rom & Rwend & Rwpos & Rwbase & Rpos & Rlen & _).
    pose proof (cells_win _ _ _ _ _ _ _ _ _ _ HK1 HD1) as C32.
    pose proof (cells_ptrs _ _ _ HK1) as C72.
    zstep. zstep. try if_true. zstep. zstep. zstep. try if_true.
    zstep. zstep. zstep.
    (* +0x84 .. +0xd4: zero the window, seek to 0 through f->seek (mseek), clear F_EOF, zero rpos / rend,
       return 0; reached with nothing pending (k = 0) or after a flush that stored all k bytes *)
    assert (TAIL : forall (M : word -> option byte)
                          (ra1 t01 t11 t21 s1x a01 a31 a41 a51 a61 a71 s2x t31 t41 t51 t61 : word)
                          (kM wendM wposM wbaseM posM : Z),
      memfile_k M (bv_unsigned a0) kM ->
      mf_dyn M (bv_unsigned a0) fl om wendM wposM wbaseM posM (Z.max len (pos + k)) ->
      mf_pend_bytes M (bv_unsigned a0) pb ->
      bytes_at rsegs M (A_G_SAID + pos) (firstn (Z.to_nat (mf_n1 k pos)) pb) ->
      guard_words M ->
      rw_cells rsegs M (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs M lo (bv_unsigned sp + -32) ->
      mem_inv rsegs M ->
      munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
             (A_G_SAID, A_G_SAID + SAID_SIZE); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m M ->
      wmono rsegs m M ->
      mf_n1 k pos = k ->
      evt rsegs QF (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t01 t11 t21 a0 s1x a01
                            (Z_to_bv 64 0) (Z_to_bv 64 0) a31 a41 a51 a61 a71 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                            t31 t41 t51 t61)
                       F (Z_to_bv 64 105688) fc None M (seg_rom rsegs))).
    { intros M ra1 t01 t11 t21 s1x a01 a31 a41 a51 a61 a71 s2x t31 t41 t51 t61 kM wendM wposM wbaseM posM
             T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
      assert (T4h : hold (bytes_at rsegs M (A_G_SAID + pos) (firstn (Z.to_nat (mf_n1 k pos)) pb))) by exact T4.
      clear T4.
      pose proof (cells_flags _ _ _ _ _ _ _ _ _ _ T1 T2) as CF.
      pose proof (cells_rd _ _ _ T1) as CR.
      pose proof (cells_win _ _ _ _ _ _ _ _ _ _ T1 T2) as CW.
      pose proof (cells_seek _ _ _ T1) as CS.
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4);
                              (bv_unsigned a0 + 8, bv_unsigned a0 + 24); (bv_unsigned a0 + 32, bv_unsigned a0 + 48);
                              (bv_unsigned a0 + 56, bv_unsigned a0 + 64); (bv_unsigned a0 + 232, bv_unsigned a0 + 240)] M)
        as MUD.
      pose proof (wmono_refl rsegs M) as WMD.
      pose proof (munch_refl [(bv_unsigned a0 + 32, bv_unsigned a0 + 48); (bv_unsigned a0 + 56, bv_unsigned a0 + 64)] M)
        as MU3.
      pose proof (memfile_at_fields _ _ (memfile_k_at _ _ _ T1)) as (_ & _ & _ & _ & _ & _ & _ & _ & S152 & S248 & _).
      pose proof T2 as (_ & _ & _ & _ & _ & RposM & RlenM & _ & DomM & _ & _ & _ & DposM & DlenM).
      pose proof T1 as (_ & _ & TWB & TWS & _).
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* f->seek is mseek: its Pre in m0 (the three stores missed the words it reads) *)
      assert (K3 : forall a n v, bv_unsigned a0 + 64 <= a -> a + Z.of_nat n <= bv_unsigned a0 + 1304 ->
                     YI04.val_mem rsegs M a n v -> YI04.val_mem rsegs m0 a n v).
      { intros a n v H1 H2 H. apply (val_munch _ _ _ _ _ _ H MU3); [lia | unfold MemFile.MF_BLOCK in F1; lia |].
        intros z Hz. cbn [outside]. lia. }
      pose proof (guard_keep _ _ _ T5 MU3 ltac:(intros z Hz; unfold GOT_GUARD in Hz; cbn [outside];
                    unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in HPL; lia)) as G0.
      pose proof (wr_at_sub _ _ _ (bv_unsigned a0 + MemFile.MF_COOKIE) 8 TWB
                    ltac:(unfold MemFile.MF_COOKIE; lia) ltac:(lia)
                    ltac:(unfold MemFile.MF_COOKIE, MemFile.MF_BLOCK; lia)) as WC.
      clear MU3.
      eapply leaf_call;
        [ exact (HMS (bv_unsigned a0) 0 posM (Z.max len (pos + k)))
        | intros r1 r2 m0' q1 q2 m' E E' H; cbv beta zeta in *; unfold res in *; unfold getr_same in E';
          rewrite <- !E'; exact H
        | exact QC | | exact T8 | | | | ].
      * cbv beta. unfold arg, apart_frame, spZ, MSEEK_K, mf_fld. getr_simp. rewrite ?unsigned_lit by lia.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [unfold SAID_SIZE; lia|]. split; [lia|]. split; [exact F1|].
        split; [apply K3; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact S152]|].
        split; [apply K3; [unfold MemFile.MF_COOKIE; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                                                          unfold MemFile.MF_COOKIE; lia | exact DposM]|].
        split; [apply K3; [unfold MemFile.MF_COOKIE; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                                                          unfold MemFile.MF_COOKIE; lia | exact DlenM]|].
        split; [apply K3; [unfold MemFile.MF_COOKIE; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                                                          unfold MemFile.MF_COOKIE; lia | exact S248]|].
        split; [exact WC|]. split; [unfold MemFile.MF_BLOCK; lia|]. split; [unfold IMG_TOP in *; lia|].
        split; [exact HPL | exact G0].
      * rewrite unsigned_lit by lia. exact T7.
      * rewrite unsigned_lit by lia. unfold MSEEK_K. lia.
      * rewrite unsigned_lit by lia. lia.
      * intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 ST4 PO4.
        cbv beta in PO4. destruct PO4 as (RES & POS4).
        change (bv_unsigned a0' = 0) in RES.
        assert (EA : a0' = Z_to_bv 64 0) by (apply bv_eq; rewrite RES; reflexivity). subst a0'. clear RES.
        replace (ret_pc (Z_to_bv 64 105712)) with (Z_to_bv 64 105712)
          by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite unsigned_lit in ST4 by lia.
        assert (MU4' : munch [(bv_unsigned sp + -80, bv_unsigned sp + -32);
                              (bv_unsigned a0 + 232, bv_unsigned a0 + 240)] m0 m4).
        { eapply munch_weaken; [|exact MU4]. unfold sub_fp. intros x Hx.
          unfold spZ, MSEEK_K, MemFile.MF_COOKIE. getr_simp. rewrite unsigned_lit by lia. cbn [outside] in *. lia. }
        clear MU4.
        (* carry the cells, the frame and the write sets over the call *)
        unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK, A_G_SAID, SAID_SIZE in *.
        pose (W4 := [(bv_unsigned sp + -80, bv_unsigned sp + -32); (bv_unsigned a0 + 232, bv_unsigned a0 + 240)]).
        apply (rw_cells_transport rsegs W4 m0 m4 _ _) in CF;
          [ | exact MU4' | exact WM4 | unfold W4; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        apply (rw_cells_transport rsegs W4 m0 m4 _ _) in CR;
          [ | exact MU4' | exact WM4 | unfold W4; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        apply (rw_cells_transport rsegs W4 m0 m4 _ _) in CW;
          [ | exact MU4' | exact WM4 | unfold W4; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        apply (rw_cells_transport rsegs W4 m0 m4 _ _) in T6;
          [ | exact MU4' | exact WM4 | unfold W4; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        clear W4.
        assert (MU4w : munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
                              (476464, 476464 + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m4).
        { eapply munch_trans; [exact T9|]. eapply munch_weaken; [|exact MU4'].
          unfold sub_fp. intros x Hx. cbn [outside] in *. lia. }
        assert (MUD4 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4);
                              (bv_unsigned a0 + 8, bv_unsigned a0 + 24); (bv_unsigned a0 + 32, bv_unsigned a0 + 48);
                              (bv_unsigned a0 + 56, bv_unsigned a0 + 64); (bv_unsigned a0 + 232, bv_unsigned a0 + 240)]
                             M m4).
        { eapply munch_trans; [exact MUD|]. eapply munch_weaken; [|exact MU4'].
          unfold sub_fp. intros x Hx. cbn [outside] in *. lia. }
        pose proof (wmono_trans rsegs _ _ _ T10 WM4) as WM4w.
        pose proof (wmono_trans rsegs _ _ _ WMD WM4) as WMD4.
        clear T9 MUD T10 WMD MU4' WM4 CS.
        pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 4); (bv_unsigned a0 + 8, bv_unsigned a0 + 24)] m4)
          as MU5.
        zstep. try if_false.
        zstep.
        zstep. zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep.
        release_frame T6 ST4 (bv_unsigned sp).
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => rename mf into m7 end.
        (* the flags word as stored: F_EOF was already clear *)
        assert (FLV : Z.land (bv_unsigned (zx32 (Z_to_bv 64 fl))) 18446744073709551599 = fl).
        { destruct (flags_val _ _ _ _ _ _ _ _ _ _ T1 T2) as [-> | ->]; vm_compute; reflexivity. }
        rewrite FLV in CF.
        pose proof T2 as (RflM & RomM & _).
        pose proof T1 as (_ & _ & TWBM & TWSM & _).
        pose proof (val_of_cell4 _ _ _ CF RflM) as VFL.
        pose proof (val_of_cells_z2 _ _ CR) as (V8 & V16).
        pose proof (val_of_cells_z4 _ _ CW) as (V32 & V40 & V48 & V56).
        replace (bv_unsigned a0 + 8 + 8) with (bv_unsigned a0 + 16) in V16 by lia.
        replace (bv_unsigned a0 + 32 + 8) with (bv_unsigned a0 + 40) in V40 by lia.
        replace (bv_unsigned a0 + 32 + 24) with (bv_unsigned a0 + 56) in V56 by lia.
        unfold mf_fld, MemFile.MF_COOKIE, MemFile.MF_BUFSIZ, MemFile.MF_BUF in *.
        assert (VOM : YI04.val_mem rsegs m7 (bv_unsigned a0 + 136) 4 om).
        { eapply val_munch; [exact DomM | exact MUD4 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
          intros z Hz. cbn [outside]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. lia. }
        assert (VPOS : YI04.val_mem rsegs m7 (bv_unsigned a0 + 232) 8 0).
        { eapply val_munch; [exact POS4 | exact MU5 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
          intros z Hz. cbn [outside]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. lia. }
        assert (VLEN : YI04.val_mem rsegs m7 (bv_unsigned a0 + (232 + 8)) 8 (Z.max len (pos + k))).
        { eapply val_munch; [exact DlenM | exact MUD4 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
          intros z Hz. cbn [outside]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. lia. }
        assert (HA7 : MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m7 (bv_unsigned a0)).
        { apply (memfile_at_rebuild M m7 (bv_unsigned a0) (memfile_k_at _ _ _ T1)).
          - intros z Hz Hd. apply (munch_mbyte _ M m7 z MUD4); [unfold MemFile.MF_ZEROED in Hz; lia|].
            cbn [outside]. unfold in_dyn, MemFile.MF_ZEROED in *. lia.
          - unfold MemFile.memfile_flags. rewrite Z.add_0_r.
            destruct (flags_val _ _ _ _ _ _ _ _ _ _ T1 T2) as [E | E]; rewrite E in VFL; [left | right]; exact VFL.
          - pose proof (memfile_k_at _ _ _ T1) as (_ & _ & _ & _ & _ & HOM & _).
            unfold MemFile.memfile_omode in *. destruct HOM as [HOM | HOM]; [left | right];
              (eapply val_munch; [exact HOM | exact MUD4 | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |]);
              intros z Hz; cbn [outside]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz; lia.
          - unfold MemFile.memfile_window. split; [exact V8|]. split; [exact V16|]. left.
            split; [exact V32|]. split; [exact V40 | exact V56].
          - unfold MemFile.memfile_cookie. exists 0, (Z.max len (pos + k)).
            split; [lia|]. split; [cbn; lia|]. split; [exact VPOS | exact VLEN]. }
        apply evt_done. unfold QF.
        eexists _, _. split; [reflexivity|].
        split; [regs_pres|].
        split; [exact MU4w|]. split; [exact WM4w|]. split; [exact MI4|]. split; [exact ST4|].
        split.
        { split; [exact HA7|].
          split; [left; split; [reflexivity|]; split; [exact V32|]; split; [exact V40 | exact V56]|].
          split; [exact (wr_at_transport rsegs _ _ _ _ TWBM WMD4)|].
          split; [exact (wr_at_transport rsegs _ _ _ _ TWSM WMD4)|].
          unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK. lia. }
        split.
        { unfold mf_pend_bytes in *. apply (bytes_munch _ M m7 _ pb T3 MUD4).
          intros z Hz. unfold MemFile.MF_BUF in Hz. cbn [outside]. lia. }
        split.
        { unfold hold in T4h. apply (bytes_munch _ M m7 _ _ T4h MUD4).
          intros z Hz. rewrite length_firstn in Hz. unfold mf_n1, SAID_SIZE in T11. cbn [outside]. lia. }
        split; [intros Hlt; lia|].
        intros _. split; [reflexivity|].
        unfold mf_dyn, mf_fld, MemFile.MF_COOKIE.
        split; [exact RflM|]. split; [exact RomM|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [lia|]. split; [unfold SAID_SIZE in *; lia|].
        split; [rewrite Z.add_0_r; exact VFL|]. split; [exact VOM|].
        split; [exact V32|]. split; [exact V40|]. split; [exact V56|]. split; [exact VPOS | exact VLEN]. }
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    + (* nothing pending: straight to the seek *)
      assert (EQB : bv_eqb (Z_to_bv 64 wpos) (Z_to_bv 64 wbase) = true)
        by (replace wpos with wbase by (symmetry; apply HWW; exact Hk0); apply bv_eqb_refl).
      rewrite EQB; cbv iota.
      eapply TAIL; [exact HK1 | | exact HPB1 | | exact HG1 | exact FR | exact ST | exact MI | exact MU | exact WM | ].
      * replace (Z.max len (pos + k)) with len by lia. exact HD1.
      * replace (mf_n1 k pos) with 0 by (unfold mf_n1, SAID_SIZE in *; lia). cbn [Z.to_nat firstn].
        apply bytes_at_nil. unfold A_G_SAID, SAID_SIZE in *. lia.
      * unfold mf_n1, SAID_SIZE in *. lia.
    + (* k bytes pending: flush them through f->write (mwrite), then the same tail *)
      assert (NEQ : bv_eqb (Z_to_bv 64 wpos) (Z_to_bv 64 wbase) = false).
      { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. intros E. apply Hk0, HWW, E. }
      rewrite NEQ; cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof EW as (EW0 & _).
      unfold mf_place_ok, A_G_SAID, SAID_SIZE, IMG_TOP, GOT_GUARD, A_G_SAY, IMG_LO, MemFile.MF_BLOCK in *.
      eapply leaf_call;
        [ exact (HMW (bv_unsigned a0) k fl om wend wpos wbase pos len pb [])
        | intros r1 r2 m0 q1 q2 m' E E' H; cbv beta zeta in *; unfold res in *; unfold getr_same in E';
          rewrite <- !E'; exact H
        | exact QC | | exact MI | | | | ].
      * (* mwrite's Pre at the call: f, data (0, 0), the FILE, errno, the frame at sp - 32 *)
        cbv beta. unfold arg, errno_ok, errno_at, apart_frame, spZ, rapart, MWRITE_K, ERRNO_TP_OFF.
        getr_simp. rewrite ?unsigned_lit by lia. cbn [length Z.of_nat].
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact HK1|]. split; [exact HD1|]. split; [exact HPB1|]. split; [exact HLEN|].
        split; [apply bytes_at_nil; lia|].
        unfold A_G_SAID, SAID_SIZE, IMG_TOP, GOT_GUARD, A_G_SAY, MemFile.MF_ZEROED, MemFile.MF_BLOCK.
        do 7 (split; [lia|]).
        split; [exact EW|]. lia.
      * rewrite unsigned_lit by lia. exact ST.
      * rewrite unsigned_lit by lia. unfold MWRITE_K. lia.
      * rewrite unsigned_lit by lia. lia.
      * intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 PO2.
        cbv beta zeta in PO2. destruct PO2 as (HK2 & HPB2 & PLT & PEQ).
        replace (ret_pc (Z_to_bv 64 105672)) with (Z_to_bv 64 105672)
          by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite unsigned_lit in ST2 by lia.
        assert (MU2' : munch [(bv_unsigned sp + -128, bv_unsigned sp + -32); (bv_unsigned a0, bv_unsigned a0 + 272);
                              (476464, 476464 + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m1 m2).
        { eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
          cbv beta. unfold errno_at, mf_hdr, mf_said, MemFile.MF_ZEROED, ERRNO_TP_OFF, A_G_SAID, SAID_SIZE, MWRITE_K.
          getr_simp. rewrite unsigned_lit by lia. cbn [outside] in *. lia. }
        clear MU2.
        assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
        { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2' WM2).
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
        pose proof (guard_keep _ _ _ HG1 MU2' ltac:(intros z Hz; unfold GOT_GUARD in Hz; cbn [outside]; lia)) as HG2.
        assert (MUm2 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 272);
                              (476464, 476464 + 4096); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2'].
          unfold sub_fp. intros x Hx. cbn [outside] in *. lia. }
        pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMm2.
        clear C32 C72 FR MU WM.
        destruct (Z.lt_ge_cases (mf_n1 k pos) k) as [Hlt | Hge].
        -- (* the flush passed g_said's end (+0x80): wpos = 0, return -1 *)
           destruct (PLT Hlt) as (_ & HD2 & HSB2).
           pose proof (cells_win _ _ _ _ _ _ _ _ _ _ HK2 HD2) as CW2.
           zstep. zstep. zstep. zstep.
           rewrite bv_eqb_refl; cbv iota.
           zstep. zstep. zstep. zstep. zstep.
           release_frame FR2 ST2 (bv_unsigned sp).
           zstep. zstep.
           apply evt_done. unfold QF.
           eexists _, _. split; [reflexivity|].
           split; [regs_pres|].
           split; [exact MUm2|]. split; [exact WMm2|]. split; [exact MI2|]. split; [exact ST2|].
           split; [exact HK2|]. split; [exact HPB2|]. split; [exact HSB2|].
           split.
           ++ intros _. split; [reflexivity | exact HD2].
           ++ intros E. lia.
        -- (* all k bytes stored: wpos = wbase <> 0, on to the seek *)
           assert (Hn1 : mf_n1 k pos = k) by (unfold mf_n1 in *; lia).
           destruct (PEQ Hn1) as (_ & fl' & wend' & wpos' & wbase' & HD2 & _ & HZ & HSB2).
           assert (Hn2 : mw_n2 k pos (Z.of_nat (length (@nil byte))) = 0)
             by (unfold mw_n2, mw_pos1, mf_n1 in *; cbn [length Z.of_nat]; lia).
           destruct (HZ Hn2) as (-> & -> & -> & ->).
           pose proof (cells_win _ _ _ _ _ _ _ _ _ _ HK2 HD2) as CW2.
           zstep. zstep. zstep. zstep.
           assert (NZ : bv_eqb (Z_to_bv 64 wbase) (Z_to_bv 64 0) = false).
           { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq.
             destruct HWB as [E | E]; [contradiction | unfold MemFile.MF_BUF in E; lia]. }
           rewrite NZ; cbv iota.
           rewrite Hn2 in HD2, HSB2. unfold mw_pos1 in HD2. rewrite Hn1, Z.add_0_r in HD2.
           cbn [Z.to_nat firstn] in HSB2. rewrite app_nil_r in HSB2.
           eapply TAIL; [exact HK2 | exact HD2 | exact HPB2 | | exact HG2 | exact FR2 | exact ST2 | exact MI2
                        | exact MUm2 | exact WMm2 | exact Hn1].
           rewrite Hn1, <- HLEN, Nat2Z.id, firstn_all. unfold A_G_SAID in HSB2. exact HSB2.
Qed.
