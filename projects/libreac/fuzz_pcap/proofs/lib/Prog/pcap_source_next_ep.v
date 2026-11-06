From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct pcap_source_struct_next
  pcap_source_next_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma rw_cells_skip16 : forall m A x cs, rw_cells rsegs m A (CB 16 x :: cs) -> rw_cells rsegs m (A + 16) cs.
Proof.
  intros m A x cs H. pose proof (rw_cells_app_split m A [CB 16 x] cs H) as [H1 H2].
  pose proof (proj1 (proj1 H1)) as W. cbn in W. destruct W as [W _].
  cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma psn_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o : word),
    bv_unsigned sp = bv_unsigned sp0 - 96 ->
    rw_cells rsegs m (bv_unsigned sp + 16)
      [C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o s3 a1 a2 a3 a4 a5 a6 a7
                                s2o s3o s4o s5o s6o s7o s8o s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Plain.s_pcap_source_next + 0x178)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o Hsp HFR.
  pose proof (zr_word sp0) as Rsp. unfold inr64 in Rsp.
  do 13 step.
  apply evt_done.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 96) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 96 + 96) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite ESP. reflexivity.
Qed.

Lemma psn_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h swz : Z) (lol lvt lvid : word)
         (pad : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    bv_unsigned sp <= bv_unsigned a0 ->
    rw_cells rsegs m (bv_unsigned a0) (ps_cells (wz h) (wz swz) lol lvt lvid pad) -> 0 <= h < 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists sp' m1 ph,
         bv_unsigned sp' = bv_unsigned sp - 96 /\
         rw_cells rsegs m1 (bv_unsigned sp - 96)
           [CB 16 ph; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp - 96) /\
         ((h = 0 /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-1)) a1 a2 (wz 0) a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom rsegs)) \/
          (h <> 0 /\
           ms' = MS (mkR ra sp' gp tp t0 t1 t2 a3 a0 (wz 0x10000) a1 a2 (wz h) a4 a5 a6 a7
                         a1 s3 a2 s5 s6 (wz 16) (wz 0xff00) s9 s10 s11 t3 t4 t5 t6)
                    F (wz (symaddr (Symbols.Plain.s_pcap_source_next + 0x50)%Z)) fc None m1 (seg_rom rsegs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h swz lol lvt lvid pad ST LO HLO HA0 HPS HH.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  unfold ps_cells, wz in HPS.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 96%nat ST.
  do 14 step.
  destruct (Z.eq_dec h 0) as [H0|H0].
  - subst h. if_true. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    eapply evt_cut.
    { eapply (psn_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 sp).
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. eapply rw_cells_skip16. eassumption. }
    intros ms' ->. apply evt_done.
    do 3 eexists. split; [apply unsigned_lit; lia|].
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    left. split; [reflexivity|]. unfold wz. reflexivity.
  - assert (EH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
    if_false. do 6 step.
    apply evt_done.
    do 3 eexists. split; [apply unsigned_lit; lia|].
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. split; [exact H0|]. unfold wz. reflexivity.
Qed.
