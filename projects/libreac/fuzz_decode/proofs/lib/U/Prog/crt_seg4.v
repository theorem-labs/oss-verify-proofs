From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_braid_c check_braid crt_convert crt_enc
  crt_segs reac_braid_encode_exact_c bcmp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma not_out2 : forall a1 b1 a2 b2 x, ~ outside [(a1, b1); (a2, b2)] x -> (a1 <= x < b1) \/ (a2 <= x < b2).
Proof. intros a1 b1 a2 b2 x H. cbn [outside] in H. lia. Qed.

Lemma wview_of_wr : forall m A n (x : word), wr_at rsegs m A n -> A <= bv_unsigned x < A + n -> wview rsegs m x <> None.
Proof.
  intros m A n x (H0 & H1 & H) Hx.
  rewrite <- (wa_of_var x (A + (bv_unsigned x - A))) by lia. apply H. lia.
Qed.

Definition crt_apart (P Q O pcm audio nch ns sp : Z) : Prop :=
  (P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P) /\
  (P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P) /\
  (Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q) /\
  (P + 4 * nch * ns <= O \/ O + 3 * nch * ns <= P) /\
  (Q + 8 * nch <= O \/ O + 3 * nch * ns <= Q) /\
  (P + 4 * nch * ns <= audio \/ audio + 3 * nch * ns <= P) /\
  (Q + 8 * nch <= audio \/ audio + 3 * nch * ns <= Q) /\
  (O + 3 * nch * ns <= audio \/ audio + 3 * nch * ns <= O) /\
  (P + 4 * nch * ns <= sp - 112 \/ sp + 112 <= P) /\
  (Q + 8 * nch <= sp - 112 \/ sp + 112 <= Q) /\
  (O + 3 * nch * ns <= sp - 112 \/ sp + 112 <= O) /\
  (audio + 3 * nch * ns <= sp - 112 \/ sp + 112 <= audio).

Definition crt_s4_post (sp gp tp : word) (P Q O pcm nch ns : Z) (m : word -> option byte) :
    machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR (Z_to_bv 64 0x136a4) sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (3 * (nch * ns))) (Z_to_bv 64 Q) (Z_to_bv 64 ns) (Z_to_bv 64 nch) (Z_to_bv 64 pcm)
               (Z_to_bv 64 O) s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 CRT_FREE) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (P, P + 4 * nch * ns); (Q, Q + 8 * nch); (O, O + 3 * nch * ns)]
      m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma crt_seg4 : reac_braid_encode_exact_contract -> bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (audio pcm nch ns P Q O : Z)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word),
    2 <= nch <= 127 -> nch mod 2 = 0 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
    0 < P -> P + 4 * nch * ns < 2^63 -> P mod 16 = 0 ->
    0 < Q -> Q + 8 * nch < 2^63 -> Q mod 16 = 0 ->
    0 < O -> O + 3 * nch * ns < 2^63 ->
    0 < pcm -> pcm + 3 * nch * ns < 2^63 ->
    0 <= audio -> audio + 3 * nch * ns < 2^63 ->
    braid_map m audio pcm nch ns -> mem_inv rsegs m ->
    wr_at rsegs m P (4 * nch * ns) -> wr_at rsegs m Q (8 * nch) -> wr_at rsegs m O (3 * nch * ns) ->
    stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 audio); C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5;
      C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    crt_apart P Q O pcm audio nch ns (bv_unsigned sp) ->
    frm0 fc ->
    evt rsegs (crt_s4_post sp gp tp P Q O pcm nch ns m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (3 * (nch * ns))) (Z_to_bv 64 Q) (Z_to_bv 64 ns) (Z_to_bv 64 nch) (Z_to_bv 64 pcm) s7
               s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13564) fc None m (seg_rom rsegs)).
Proof.
  intros ENC BCMP ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m audio pcm nch ns P Q O
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra
    HN HE HS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HO0 HO1 HC0 HC1 HA0 HA1 BR MI WP WQ WO ST FR AP Hfc.
  assert (NN : 0 < nch * ns <= 1524) by (clear - HN HS; nia).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold REAC_BRAID_ENCODE_FRAME in ENC.
  step. take false. step. take false. step. step. take false.
  eapply evt_cut.
  { eapply (crt_convert_loop) with (pb := crt_rd m pcm) (P := P) (Q := Q) (pcm := pcm) (nch := nch) (ns := ns).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - clear - HP2. Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - clear - HQ2. Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - exact (crt_pcm_ok m audio pcm nch ns ltac:(lia) ltac:(lia) BR).
    - exact WP.
    - exact WQ.
    - exact (proj1 AP).
    - exact (proj1 (proj2 AP)).
    - exact (proj1 (proj2 (proj2 AP))).
    - exact Hfc. }
  intros ms1 (ra1 & s1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & s9' & s10' & s11' &
    t3' & t4' & t5' & t6' & v4' & v5' & fc1 & m1 & -> & Hfc1 & MU1 & WM1 & HQd & HPd).
  unfold CRT_LOOP_END.
  do 6 step.
  assert (MI1 : mem_inv rsegs m1).
  { apply (rbe_mem_inv_munch rsegs _ m m1 MU1); [|exact MI].
    intros x Hx. destruct (not_out2 _ _ _ _ _ Hx) as [H|H].
    - exact (wview_of_wr m P _ x WP H).
    - exact (wview_of_wr m Q _ x WQ H). }
  assert (ST1 : stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1). cbn [disjoint_from].
    destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _). clear - D1 D2. lia. }
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp) [C8 (Z_to_bv 64 audio); C8 v11; C8 v10; C8 v9; C8 v8; C8 v7;
    C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _). clear - D1 D2. lia. }
  pose proof (wr_at_transport rsegs m m1 O _ WO WM1) as WO1.
  assert (CB : forall ch, 0 <= ch < nch -> 0 <= ch * ns /\ ch * ns + ns <= nch * ns).
  { intros ch Hch. split; [apply Z.mul_nonneg_nonneg; lia|].
    replace (ch * ns + ns) with ((ch + 1) * ns) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  eapply evt_cut.
  { eapply ENC with (a := O) (N := nch) (P := Q) (ns := ns) (Q := fun ch => P + 4 * (ch * ns))
      (V := fun s ch => cv (crt_rd m pcm) (ch * ns + s)) (K := crt_K (crt_rd m pcm) ns) (m := m1).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact HE.
    - lia.
    - exact Hfc1.
    - exact MI1.
    - exact ST1.
    - lia.
    - lia.
    - exact WO1.
    - lia.
    - clear - HQ2. Z.div_mod_to_equations. lia.
    - lia.
    - intros ch Hch. exact (HQd ch Hch).
    - intros ch Hch. destruct (CB ch Hch) as [C1 C2]. split; [lia|]. split; [|lia].
      rewrite Z.mul_comm, Z.mod_add by lia. clear - HP2. Z.div_mod_to_equations. lia.
    - intros s ch Hs Hch.
      pose proof (s24_range (crt_rd m pcm (3 * (ch * ns + s))) (crt_rd m pcm (3 * (ch * ns + s) + 1))
        (crt_rd m pcm (3 * (ch * ns + s) + 2))) as R24.
      split.
      + replace (P + 4 * (ch * ns) + 4 * s) with (P + 4 * (ch * ns + s)) by ring.
        rewrite <- le4_lit.
        * exact (HPd ch s Hch Hs).
        * unfold cv. pose proof (f32_range (s24 (crt_rd m pcm (3 * (ch * ns + s))) (crt_rd m pcm (3 * (ch * ns + s) + 1))
            (crt_rd m pcm (3 * (ch * ns + s) + 2))) (-23) ltac:(lia) ltac:(lia)). lia.
      + unfold rb_sample, crt_K. split; [lia|]. left. reflexivity.
    - destruct AP as (_ & _ & _ & _ & D & _). clear - D. lia.
    - intros ch Hch. destruct (CB ch Hch) as [C1 C2].
      destruct AP as (_ & _ & _ & D & _). clear - D C1 C2. lia.
    - unfold REAC_BRAID_ENCODE_FRAME.
      destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D & _). clear - D. lia.
    - unfold REAC_BRAID_ENCODE_FRAME.
      destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D & _). clear - D. lia.
    - intros ch Hch. destruct (CB ch Hch) as [C1 C2]. unfold REAC_BRAID_ENCODE_FRAME.
      destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & D & _). clear - D C1 C2. lia. }
  intros ms2 (t0e & t1e & t2e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & F2 & m2 & -> & HF2 & MU2 & WM2 & MI2 &
    ST2 & ENC2).
  unfold REAC_BRAID_ENCODE_FRAME in *.
  rewrite ret_pc_even by first [lia | reflexivity].
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp) [C8 (Z_to_bv 64 audio); C8 v11; C8 v10; C8 v9; C8 v8; C8 v7;
    C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D & _). clear - D. lia. }
  do 4 step.
  assert (OB : bytes_at rsegs m2 O (crt_list m audio (3 * (nch * ns)))).
  { apply crt_list_bytes; [lia | lia | lia |]. intros i Hi.
    unfold mrd. rewrite ENC2.
    - rewrite (crt_out m m1 O audio pcm nch ns ltac:(lia) HE ltac:(lia) ltac:(lia) ltac:(lia) BR i ltac:(lia)).
      reflexivity.
    - rewrite wa_unsigned by lia. cbn [outside]. split; [|exact I].
      destruct AP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D & _). clear - D Hi. lia. }
  assert (AB : bytes_at rsegs m2 audio (crt_list m audio (3 * (nch * ns)))).
  { apply crt_list_bytes; [lia | lia | lia |]. intros i Hi.
    destruct AP as (_ & _ & _ & _ & _ & D1 & D2 & D3 & _ & _ & _ & D4).
    assert (E : m2 (wa (audio + i)) = m (wa (audio + i))).
    { rewrite MU2 by (rewrite wa_unsigned by lia; cbn [outside]; clear - D3 D4 Hi; repeat split; lia).
      rewrite MU1 by (rewrite wa_unsigned by lia; cbn [outside]; clear - D1 D2 Hi; repeat split; lia).
      reflexivity. }
    unfold mrd. rewrite E. fold (mrd rsegs m (wa (audio + i))).
    exact (crt_audio_ok m audio pcm nch ns ltac:(lia) HE ltac:(lia) BR i ltac:(lia)). }
  eapply evt_cut.
  { eapply BCMP with (ls := crt_list m audio (3 * (nch * ns))) (rs := crt_list m audio (3 * (nch * ns))) (v := 0)
      (m := m2).
    - rewrite unsigned_lit by lia. exact OB.
    - rewrite unsigned_lit by lia. exact AB.
    - apply memcmp_self. rewrite unsigned_lit by lia. rewrite crt_list_len. lia.
    - exact MI2. }
  intros ms3 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & _ & _).
  rewrite ret_pc_even by first [lia | reflexivity].
  step. take false.
  do 2 step.
  apply evt_done. unfold crt_s4_post.
  do 22 eexists. split.
  { f_equal; crt_regs; crt_w. }
  split; [exact Hfc1|].
  split.
  { apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2) |].
    - refine (munch_weaken _ _ m m1 _ MU1). intros x Hx. cbn [outside] in *. tauto.
    - refine (munch_weaken _ _ m1 m2 _ MU2). intros x Hx. cbn [outside] in *. tauto.
    - refine (munch_weaken _ _ m2 m3 _ MU3). intros x Hx. exact I. }
  split; [exact (wmono_trans rsegs m m2 m3 (wmono_trans rsegs m m1 m2 WM1 WM2) WM3) | exact MI3].
Qed.
