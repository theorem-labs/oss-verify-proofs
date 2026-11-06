From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct pcap_source_struct_next
  pcap_source_next_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac show_st := lazymatch goal with |- evt _ _ ?st => idtac "GOAL:" st end.
Ltac show_rw := try (match goal with H : rw_cells _ _ ?a ?cs |- _ => idtac "HX:" a cs; fail end).
Ltac fit_addr H :=
  lazymatch goal with |- rw_cells _ _ ?a _ =>
    lazymatch type of H with rw_cells _ _ ?b _ => replace a with b by lia; exact H end end.

Lemma psn_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word),
    bv_unsigned sp = bv_unsigned sp0 - 128 ->
    rw_cells rsegs m (bv_unsigned sp + 24)
      [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o s6 a1 a2 a3 a4 a5 a6 a7
                                s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o t3 t4 t5 t6)
                           F (ret_pc ra0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x148)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o Hsp HFR.
  pose proof (zr_word sp0) as Rsp0. unfold inr64 in Rsp0.
  do 16 step.
  apply evt_done.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 128) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 128 + 128) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite ESP. reflexivity.
Qed.

Lemma psn_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h swz : Z) (lol lvt lvid : word)
         (pad : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> (symaddr ImgPages.Ubsan.top) <= lo ->
    bv_unsigned sp <= bv_unsigned a0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned a0) (ps_cells (wz h) (wz swz) lol lvt lvid pad) -> 0 <= h < 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists m1,
         munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp - 128) /\
         ((h = 0 /\ stk rsegs m1 lo (bv_unsigned sp) /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-1)) a1 a2 (wz 0) a3 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom rsegs)) \/
          (h <> 0 /\ exists sp' ph,
           bv_unsigned sp' = bv_unsigned sp - 128 /\
           rw_cells rsegs m1 (bv_unsigned sp - 128) [C8 a3] /\
           rw_cells rsegs m1 (bv_unsigned sp - 128 + 8) [CB 16 ph] /\
           rw_cells rsegs m1 (bv_unsigned sp - 128 + 24)
             [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
           exists x0, ms' = MS (mkR ra sp' gp tp t0 t1 t2 (wz (bv_unsigned sp' + 8)) a1 x0 a1 a2 (wz h) a3 a5 a6 a7
                         a0 s3 s4 s5 s6 a2 (wz (bv_unsigned sp' + 16)) (wz (-4)) (wz 16)
                         (wz (bv_unsigned sp' + 12)) t3 t4 t5 t6)
                    F (wz (symaddr (Symbols.Ubsan.s_pcap_source_next + 0x74)%Z)) fc None m1 (seg_rom rsegs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h swz lol lvt lvid pad ST LO HLO HA0 HNZ HAL HPS HH.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  unfold ps_cells, wz in HPS.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (L7 : Z.land (bv_unsigned a0) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact HAL. }
  carve_frame 128%nat ST.
  do 15 step.
  if_false.
  do 3 step.
  assert (EL7 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned a0) 7)) = 0) by (rewrite L7; apply unsigned_lit; lia).
  if_false.
  do 3 step.
  destruct (Z.eq_dec h 0) as [H0|H0].
  - subst h. if_true. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    eapply evt_cut.
    { eapply (psn_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 sp).
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia.
        match goal with H : rw_cells _ _ (bv_unsigned sp + -128) (CB 24 ?J :: ?cs) |- _ =>
          pose proof (rw_cells_app_split _ _ [CB 24 J] cs H) as [_ HSV0] end.
        cbn [cells_size csize Nat.add] in HSV0.
        replace (bv_unsigned sp - 128 + 24) with (bv_unsigned sp + -128 + Z.of_nat 24) by lia. exact HSV0. }
    intros ms' ->. apply evt_done.
    exists m1. split; [eassumption|]. split; [eassumption|].
    split; [replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) by lia; eassumption|].
    left. split; [reflexivity|]. split.
    { match goal with H : rw_cells _ _ (bv_unsigned sp + -128) ?cs, S : stk _ _ lo (bv_unsigned sp + -128) |- _ =>
        pose proof (stk_release rsegs _ lo _ cs S H ltac:(lia)) as SR end.
      cbn [cells_size csize Nat.add] in SR.
      replace (bv_unsigned sp + -128 + Z.of_nat 128) with (bv_unsigned sp) in SR by lia. exact SR. }
    unfold wz. reflexivity.
  - assert (EH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
    if_false. do 8 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -128) (C8 ?v1 :: CB 16 ?Y :: ?cs) |- _ =>
      pose proof (rw_cells_app_split _ _ [C8 v1] (CB 16 Y :: cs) H) as [FA FB'];
      pose proof (rw_cells_app_split _ _ [CB 16 Y] cs FB') as [FB FC] end.
    cbn [cells_size csize Nat.add] in FB', FB, FC.
    apply evt_done.
    exists m1. split; [eassumption|]. split; [eassumption|].
    split; [replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) by lia; eassumption|].
    right. split; [exact H0|]. do 2 eexists. split; [apply unsigned_lit; lia|].
    split; [fit_addr FA|]. split; [fit_addr FB|]. split; [fit_addr FC|].
    unfold wz.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + 8)) with (Z_to_bv 64 (bv_unsigned sp + -120))
      by (rewrite unsigned_lit by lia; f_equal; lia).
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + 16)) with (Z_to_bv 64 (bv_unsigned sp + -112))
      by (rewrite unsigned_lit by lia; f_equal; lia).
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + 12)) with (Z_to_bv 64 (bv_unsigned sp + -116))
      by (rewrite unsigned_lit by lia; f_equal; lia).
    eexists. reflexivity.
Qed.
