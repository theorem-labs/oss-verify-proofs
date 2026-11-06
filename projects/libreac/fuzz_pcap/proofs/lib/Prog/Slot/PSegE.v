From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_next_lib memcpy_c
  pcap_source_struct.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* The payload pl = d :: F: the first byte d, the file F; for the empty payload d = 0 and F = []. *)
Definition pl_d (pl : list byte) : Z := match pl with [] => 0 | d :: _ => bv_unsigned d end.
Definition pl_src (p : Z) (pl : list byte) : Z := match pl with [] => p | _ :: _ => p + 1 end.
Definition pl_n (pl : list byte) : Z := Z.of_nat (length (tl pl)).

(* The 104 bytes the prologue saves at S - 104: s11 .. s0, ra. *)
Definition saved_regs (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list byte :=
  le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
  le8 s1 ++ le8 s0 ++ le8 ra.

(* The frame after the prologue's stores: the stack is whole again and the saved registers sit at A + 56. *)
Lemma e_frame : forall m lo A (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  stk rsegs m lo A -> lo <= A ->
  rw_cells rsegs m A [CB 56 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                      C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (A + 160) /\ bytes_at rsegs m (A + 56) (saved_regs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros m lo A j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ST LO H. split.
  - exact (stk_release rsegs m lo A _ ST H LO).
  - destruct H as [[Hwf Hb] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lj _].
    cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
    rewrite Lj in Hb. unfold saved_regs. rewrite !app_nil_r in Hb. exact Hb.
Qed.

Ltac e_fin sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 :=
  let STf := fresh "STf" in let SB := fresh "SB" in
  match goal with
  | ST : stk _ _ ?lo (bv_unsigned sp + -160), FRc : rw_cells _ _ (bv_unsigned sp + -160) _ |- _ =>
      destruct (e_frame _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ST ltac:(lia) FRc) as [STf SB]
  end;
  replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) in STf by lia;
  replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp - 104) in SB by lia;
  apply evt_done; do 2 eexists; split; [reflexivity|];
  refine (conj _ (conj _ (conj _ (conj STf (conj SB (conj _ (conj _ _))))))); try eassumption.

(* Segment E, from the entry 0x12c04 (payload length below 2^26) to the call of malloc (0x14158, ra 0x12c7c). *)
Lemma pcap_E_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pl g0 : list byte) (p S lo : Z),
    bv_unsigned sp = S -> a0 = wz p -> a1 = wz (Z.of_nat (length pl)) -> Z.of_nat (length pl) < 2 ^ 26 ->
    bytes_at rsegs m p pl -> (p + Z.of_nat (length pl) <= S - 160 \/ S <= p) ->
    (p + Z.of_nat (length pl) <= (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= p) ->
    stk rsegs m lo S -> lo + 160 <= S -> (symaddr Symbols.Plain.s_environ) <= lo ->
    rw_cells rsegs m (symaddr Symbols.Plain.s_g_file_len) [CB 16 g0] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z)) (wz (S - 160)) gp tp t0 t1 t2 (wz (pl_d pl)) (wz (pl_src p pl)) (wz (pl_n pl))
                       a1 a2' a3 a4 a5 a6 a7 (wz (pl_n pl)) s3 s4 s5 (wz (symaddr Symbols.Plain.s_g_file_len)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 (symaddr Symbols.Plain.s_malloc)) fc None m' (seg_rom rsegs) /\
         munch [(S - 160, S); ((symaddr Symbols.Plain.s_g_file_len), (symaddr Symbols.Plain.s_environ))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo S /\
         bytes_at rsegs m' (S - 104) (saved_regs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         rw_cells rsegs m' (symaddr Symbols.Plain.s_g_file_len) [C8 (wz (pl_n pl)); C8 (wz (pl_src p pl))] /\
         bytes_at rsegs m' p pl /\ bytes_at rsegs m' (pl_src p pl) (tl pl))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr Symbols.Plain.s_LLVMFuzzerTestOneInput)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m pl g0 p S lo HSP E0 E1 HZ HPL DJS DJG ST LO LG HG MI.
  subst S a0 a1.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HPL) as HPB.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); ((symaddr Symbols.Plain.s_g_file_len), (symaddr Symbols.Plain.s_environ))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  remember (Z.of_nat (length pl)) as z eqn:EZ.
  assert (UZ : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit; lia).
  unfold wz.
  carve_frame 160%nat ST.
  do 15 step.
  rewrite UZ, Z.shiftr_div_pow2, Z.div_small by lia.
  step. if_false.
  step.
  destruct pl as [|d F]; cbn [length Z.of_nat] in EZ; subst z; step.
  - if_true. do 8 step.
    e_fin sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  - if_false.
    let mm := cur_mem in pose proof (bytes_at_byte mm p (d :: F) 0 HPL ltac:(cbn [length]; lia)) as HB0.
    cbn [nth Z.to_nat] in HB0.
    do 10 step.
    replace (Z.of_nat (S (length F)) + -1) with (Z.of_nat (length F)) in * by lia.
    pose proof HPL as HPF. change (d :: F) with ([d] ++ F) in HPF. apply bytes_at_app in HPF.
    destruct HPF as [_ HPF]. cbn [length Z.of_nat] in HPF.
    e_fin sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Qed.

(* The value of the 8 rodata bytes at 0x103f8. *)
Definition A5 : Z := 0xa5a5a5a5a5a5a5a5.
Definition a5b : byte := Z_to_bv 8 0xa5.

(* The reader's cells at sp_h + 32 after the three stores of the rodata value: f, sw, olen, vtag, vid, pad. *)
Definition ps_a5 : list cell :=
  ps_cells (wz A5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5) [a5b; a5b].

(* Its 24 bytes are three copies of the rodata value. *)
Lemma ps_a5_bytes : cells_bytes ps_a5 = le8 (wz A5) ++ le8 (wz A5) ++ le8 (wz A5).
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

Lemma rw_cells_same : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[_ Hb] Hw] Hwf EB ES. split; [split|].
  - exact Hwf.
  - rewrite EB. exact Hb.
  - rewrite ES. exact Hw.
Qed.

(* From 0x12c9c (after the copy) to the call of pcap_source_open (0x131c8, ra 0x12cc4). *)
Lemma pcap_A2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 v8 : word) (sp_h b lo : Z),
    bv_unsigned sp = sp_h -> s4 = wz b -> s6 = wz (symaddr Symbols.Plain.s_g_file_len) ->
    stk rsegs m lo (sp_h + 160) -> lo <= sp_h -> (symaddr Symbols.Plain.s_environ) <= lo ->
    rw_cells rsegs m (symaddr Symbols.Plain.s_g_file_len) [C8 v0; C8 v8] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) (wz (symaddr (Symbols.Plain.Sec.s_rodata + 0xe9)%Z)) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 32, sp_h + 56); ((symaddr Symbols.Plain.s_g_file), (symaddr Symbols.Plain.s_environ))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 160) /\ rw_cells rsegs m' (sp_h + 32) ps_a5 /\
         rw_cells rsegs m' (symaddr Symbols.Plain.s_g_file_len) [C8 v0; C8 (wz b)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x98)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m v0 v8 sp_h b lo HSP E4 E6 ST LO LG HG MI.
  subst sp_h s4 s6.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp + 32, bv_unsigned sp + 56); ((symaddr Symbols.Plain.s_g_file), (symaddr Symbols.Plain.s_environ))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  destruct (stk_split rsegs m lo (bv_unsigned sp + 56) (bv_unsigned sp + 160) ST ltac:(lia)) as [ST1 ST2].
  clear ST.
  carve_frame 24%nat ST1.
  unfold wz.
  do 10 step.
  pose proof (stk_release rsegs _ lo _ _ ST1 FR0 ltac:(lia)) as STa. cbn [cells_size csize Nat.add] in STa.
  replace (bv_unsigned sp + 32 + Z.of_nat 24) with (bv_unsigned sp + 56) in STa by lia.
  pose proof (stk_merge rsegs _ lo _ _ STa ST2 ltac:(lia)) as STf.
  apply (rw_cells_same _ _ _ ps_a5) in FR0;
    [ | cbn; repeat split
      | vm_compute; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity | reflexivity ].
  apply evt_done. eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MI (conj STf (conj FR0 HG))))).
Qed.

Lemma out_sub : forall W W' : list ivl, (forall x, outside W' x -> outside W x) -> sub_fp W W'.
Proof. intros W W' H. exact H. Qed.

(* Segment A, from 0x12c7c (malloc answered b) to the call of pcap_source_open (0x131c8, ra 0x12cc4): the copy
   of the file into b (memcpy, when the file is not empty), g_file = b, and the reader's cells filled from
   rodata. *)
Lemma pcap_A_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (F jb : list byte) (v8 : word)
         (sp_h b src n lo : Z),
    memcpy_contract ->
    bv_unsigned sp = sp_h -> a0 = wz b -> s1 = wz src -> s2 = wz n -> s6 = wz (symaddr Symbols.Plain.s_g_file_len) ->
    n = Z.of_nat (length F) -> n < 2 ^ 26 -> bytes_at rsegs m src F ->
    (n <> 0 -> b <> 0 /\ rw_cells rsegs m b [CB (length F) jb] /\ (b + n <= src \/ src + n <= b) /\
               (b + n <= lo \/ sp_h + 160 <= b) /\ (b + n <= (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= b)) ->
    stk rsegs m lo (sp_h + 160) -> lo <= sp_h -> (symaddr Symbols.Plain.s_environ) <= lo ->
    rw_cells rsegs m (symaddr Symbols.Plain.s_g_file_len) [C8 (wz n); C8 v8] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) sp gp tp t0' t1' t2' s0 s1 (wz (sp_h + 32)) (wz (symaddr (Symbols.Plain.Sec.s_rodata + 0xe9)%Z)) a2' a3' a4' a5' a6' a7'
                       s2 s3 (wz b) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open)) fc None m'
                  (seg_rom rsegs) /\
         munch [(sp_h + 32, sp_h + 56); (b, b + n); ((symaddr Symbols.Plain.s_g_file), (symaddr Symbols.Plain.s_environ))] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (sp_h + 160) /\ rw_cells rsegs m' (sp_h + 32) ps_a5 /\
         rw_cells rsegs m' (symaddr Symbols.Plain.s_g_file_len) [C8 (wz n); C8 (wz b)] /\
         (n <> 0 -> rw_cells rsegs m' b [CB (length F) F]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m F jb v8 sp_h b src n lo MEMC HSP E0 E1 E2 E6 EN HN26 HF HB ST LO LG HG MI.
  subst sp_h a0 s1 s2 s6.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as HFB. rewrite <- EN in HFB.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold wz.
  step. step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - if_true. step. if_true.
    eapply evt_mono.
    { eapply (pcap_A2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz n) v8 (bv_unsigned sp) b lo);
        try reflexivity; eassumption. }
    intros ms' (m' & -> & MU & WM & MI' & ST' & PS & G).
    do 14 eexists. split; [reflexivity|].
    refine (conj _ (conj WM (conj MI' (conj ST' (conj PS (conj G _)))))); [| intros H; exfalso; exact (H N0)].
    eapply munch_weaken; [| exact MU]. apply out_sub. out_tac.
  - destruct (HB N0) as (BNZ & HBC & DJS & DJK & DJG).
    pose proof (rw_cells_bound rsegs _ _ _ HBC) as HBB. cbn [cells_size csize] in HBB.
    rewrite ?Nat.add_0_r, <- EN in HBB.
    assert (UB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
    assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    if_false. step. if_false. step. if_false. do 4 step.
    eapply evt_cut.
    { eapply MEMC.
      - rewrite US. exact HF.
      - rewrite UN. lia.
      - rewrite UB, UN, EN, Nat2Z.id. exact HBC.
      - rewrite UB, US, UN. lia.
      - exact MI. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                -> & MU1 & WM1 & MI1 & HC & HS).
    rewrite UB, UN in MU1, HC. rewrite EN, Nat2Z.id in HC.
    rewrite (ret_pc_even (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x98)%Z)) by (lia || reflexivity).
    pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST MU1 WM1 ltac:(cbn [disjoint_from]; lia)) as ST1.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ HG MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia))
      as HG1.
    eapply evt_mono.
    { eapply (pcap_A2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz n) v8 (bv_unsigned sp) b lo);
        try reflexivity; eassumption. }
    intros ms' (m' & -> & MU & WM & MI' & ST' & PS & G).
    do 14 eexists. split; [reflexivity|].
    refine (conj _ (conj (wmono_trans rsegs _ _ _ WM1 WM) (conj MI' (conj ST' (conj PS (conj G _)))))).
    + apply (munch_trans _ m m1 m').
      * eapply munch_weaken; [| exact MU1]. apply out_sub. out_tac.
      * eapply munch_weaken; [| exact MU]. apply out_sub. out_tac.
    + intros _. exact (rw_cells_transport rsegs _ _ _ _ _ HC MU WM
                         ltac:(cbn [disjoint_from cells_size csize]; rewrite ?Nat.add_0_r; lia)).
Qed.
