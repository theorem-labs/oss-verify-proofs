From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fflush_c mclose_c __unlist_locked_file_c
  __ofl_lock_c __ofl_unlock_c.
Import ListNotations.
Open Scope Z_scope.

Definition FREE_FN : Z := Eval compute in Symbols.Plain.s_free.

Lemma c4_byte0 : forall m A v rest, rw_cells rsegs m A (C4 v :: rest) ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some (firstn 1 (le4 v)).
Proof.
  intros m A v rest [[_ HB] _]. cbn [cells_bytes cbytes] in HB.
  assert (L : (0 + 1 <= length (le4 v ++ cells_bytes rest))%nat) by (rewrite length_app, length_le4; lia).
  pose proof (bytes_at_ov_read rsegs m A _ 0 1 HB L) as E.
  cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r in E. unfold wa in E. rewrite E. reflexivity.
Qed.

Definition fclose_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h b : Z) (Fc : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists sp' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Plain.s_fclose + 0xa4)%Z)) sp' gp tp t0 t1 t2 (wz h) (wz 0) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz A_OFL_HEAD)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 FREE_FN) fc None m1 (seg_rom rsegs)
    /\ bv_unsigned sp' = bv_unsigned sp - 48
    /\ rw_cells rsegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (h, h + 1304); (A_OFL_HEAD, A_OFL_HEAD + 8)] m m1
    /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (bv_unsigned sp - 48)
    /\ ofl_empty m1 /\ stdio_ok m1 /\ guard_ok m1 /\ bytes_at rsegs m1 b Fc
    /\ (exists junk', rw_cells rsegs m1 h [CB 1304 junk']).

Lemma fclose_pro : fflush_contract -> mclose_contract -> __unlist_locked_file_contract -> __ofl_lock_contract ->
  __ofl_unlock_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h b p : Z) (Fc : list byte),
    a0 = wz h ->
    mstl m h b Fc p (wz 0) (wz 0) -> ofl_one m h -> stdio_ok m -> guard_ok m -> mem_inv rsegs m ->
    Z.of_nat (length Fc) < 2 ^ 63 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    (h + 1304 <= A_LIBC \/ A_OFL_HEAD + 8 <= h) ->
    (h + 1304 <= A_GUARD \/ A_GUARD + 8 <= h) ->
    (h + 1304 <= A_GOT_GUARD \/ A_GOT_GUARD + 8 <= h) ->
    (b + Z.of_nat (length Fc) <= A_OFL_HEAD \/ A_OFL_HEAD + 8 <= b) ->
    evt rsegs (fclose_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h b Fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Plain.s_fclose)) fc None m (seg_rom rsegs)).
Proof.
  intros HFF HMC HUL HOL HOU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h b p Fc EA0 HST HOFL HSO HGU MI HN ST LO HLO50 HHL HBL DLB DGU DGOT DBO.
  subst a0.
  destruct HST as (fl & md & q & rb & HMF & HFL & HMD & Hp & H24).
  destruct HMF as (buf & (pad0 & pad1 & pad2 & ung & HC & Lung & Lbuf & Hh0 & Hh16) & Hq & HRB & HFc & Hb0 & Hbh).
  destruct HSO as (HT & HN3 & HLK). destruct HGU as (HGOT & g & HGD).
  unfold ofl_one in HOFL. unfold mfile_cells in HC.
  unfold wz, A_LIBC, A_OFL_LOCK, A_OFL_HEAD, A_GUARD, A_GOT_GUARD, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (UH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (h, h + 1304); ((symaddr Symbols.Plain.s_ofl_head), (symaddr Symbols.Plain.s_ofl_head) + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by lia.
  carve_frame 48%nat ST.
  do 8 step.
  assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HMF : mfile mm h b Fc fl md q rb (wz 0) (wz 0))
      by (unfold mfile; cbv zeta; exists buf;
          refine (conj _ (conj Hq (conj HRB (conj HFc (conj Hb0 Hbh)))));
          unfold mfile_raw, mfile_cells, wz; exists pad0, pad1, pad2, ung;
          exact (conj HC (conj Lung (conj Lbuf (conj Hh0 Hh16)))));
    eapply evt_cut;
    [ eapply HFF with (lo := lo);
      [ rewrite UH; exact HMF | exact HN
      | unfold guard_ok, A_GOT_GUARD, A_GUARD, wz; split; [exact HGOT | exists g; exact HGD]
      | exact MI | rewrite U48; exact ST | rewrite U48; unfold FFLUSH_K; lia
      | rewrite UH; lia | lia | unfold A_OFL_HEAD; lia ]
    | ]
  end.
  clear HMF.
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & EA & MUc
    & WMc & MIc & STc & HMF2).
  subst ms' a0'.
  unfold FFLUSH_K in MUc. rewrite U48, UH in MUc. rewrite U48 in STc. rewrite UH in HMF2.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m' MUc WMc end.
  clear MUc WMc MI. rename MIc into MI. rename STc into ST.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  destruct HMF2 as (buf2 & (pad0' & pad1' & pad2' & ung' & HC2 & Lung2 & Lbuf2 & _ & _) & Hq2 & _ & HFc2 & _ & _).
  cbn [rpos_of rend_of] in HC2.
  unfold mfile_cells, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in HC2.
  do 3 step. if_true.
  do 4 step.
  eapply evt_cut; [apply HMC | intros ms' ->].
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  destruct HFL as [-> | ->]; unfold wz in *; pose proof (c4_byte0 _ _ _ _ HC2) as RB;
    [ change (firstn 1 (le4 (Z_to_bv 64 8))) with [Z_to_bv 8 8] in RB
    | change (firstn 1 (le4 (Z_to_bv 64 24))) with [Z_to_bv 8 24] in RB ].
  all: do 4 step; if_false; do 2 step.
  all: eapply evt_cut; [apply HUL | intros ms' ->].
  all: lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  all: step; if_false; step.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HOL with (lo := lo);
      [ unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
      | eassumption | rewrite U48; eassumption
      | rewrite U48; unfold OFL_LOCK_K; lia
      | unfold A_OFL_HEAD; lia ]
    | unfold __ofl_lock_post, OFL_LOCK_K; post_call rsegs mm ] end.
  all: match goal with H : stk _ _ _ (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U48 in H; rename H into ST end.
  all: unfold wz, A_OFL_HEAD in *.
  all: do 4 step; if_true; step; if_true; do 2 step; if_false; do 3 step.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply HOU; unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
                    | intros ms' [a0'' [a1'' ->]] ] end.
  all: lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  all: do 2 step.
  all: apply evt_done; unfold fclose_pro_post, FREE_FN.
  all: exists (Z_to_bv 64 (bv_unsigned sp + -48)); do 16 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
    [ rewrite U48; lia
    | replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact FR
    | unfold A_OFL_HEAD; exact MU
    | exact WM
    | eassumption
    | replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact ST
    | unfold ofl_empty, A_OFL_HEAD, wz; exact HOFL
    | unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
    | unfold guard_ok, A_GOT_GUARD, A_GUARD, wz; split; [exact HGOT | exists g; exact HGD]
    | exact HFc2
    | destruct (rw_cells_forget rsegs _ _ _ HC2) as [jk HJ]; exists jk; exact HJ ].
Qed.

Lemma fclose_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 : word) (junk : list byte)
         (ra0 s0o s1o s2o s3o : word),
    bv_unsigned sp = bv_unsigned sp0 - 48 -> s1 = wz 0 -> s2 = wz 0 ->
    rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 junk; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o (wz 0) a1 a2 a3 a4 a5 a6 a7
                                s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Plain.s_fclose + 0xac)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp0 junk
    ra0 s0o s1o s2o s3o Hsp E1 E2 HFR.
  subst s1 s2. unfold wz in *.
  rewrite <- Hsp in HFR.
  do 8 step.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 48) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 48 + 48) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  apply evt_done. rewrite ESP. reflexivity.
Qed.
