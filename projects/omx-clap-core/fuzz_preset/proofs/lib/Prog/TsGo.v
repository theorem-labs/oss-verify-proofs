From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec TsRuns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ts_Q (n i c f p t : Z) (rav gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms =>
    (i = n /\ at_call rav (Z_to_bv 64 (f + 112)) gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
                (Z_to_bv 64 t) (Z_to_bv 64 0x10394) (Z_to_bv 64 1) F fc m [] (fun m' => m' = m) ms) \/
    (i < n /\ (c = 34 \/ c = 92) /\
     at_call (Z_to_bv 64 0x1535c) (Z_to_bv 64 f) gp tp (Z_to_bv 64 t) (Z_to_bv 64 p)
       (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
       (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
       (Z_to_bv 64 t) (Z_to_bv 64 0x102e9) (Z_to_bv 64 1) F fc m [(f, f + 8)] (fun _ => True) ms) \/
    (i < n /\ 32 <= c /\ c <> 34 /\ c <> 92 /\
     at_call (Z_to_bv 64 0x1536c) (Z_to_bv 64 f) gp tp (Z_to_bv 64 t) (Z_to_bv 64 p)
       (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
       (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
       (Z_to_bv 64 t) (Z_to_bv 64 p) (Z_to_bv 64 1) F fc m [(f, f + 8)] (fun _ => True) ms) \/
    (i < n /\ c < 32 /\
     at_call (Z_to_bv 64 0x1536c) (Z_to_bv 64 f) gp tp (Z_to_bv 64 t) (Z_to_bv 64 p)
       (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
       (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
       (Z_to_bv 64 t) (Z_to_bv 64 (f + 2)) (Z_to_bv 64 (Z.of_nat (length (esc c)))) F fc m [(f, f + 8)]
       (fun m' => bytes_at rsegs m' (f + 2) (map (Z_to_bv 8) (esc c))) ms).

Lemma rw_cons_cb : forall m f j rest,
  rw_cells rsegs m f [CB 8 j] -> rw_cells rsegs m (f + 8) rest -> rw_cells rsegs m f (CB 8 j :: rest).
Proof.
  intros m f j rest [[[Hj _] Hb1] [Hf0 [Hf1 Hw1]]] [[Hwf Hb2] [Hg0 [Hg1 Hw2]]].
  cbn [cell_wf] in Hj. cbn [cells_bytes cbytes cells_size csize] in Hb1, Hf1, Hw1.
  rewrite app_nil_r in Hb1.
  split; [split; [split; [exact Hj | exact Hwf] |] |].
  - cbn [cells_bytes cbytes]. apply bytes_at_app. split; [exact Hb1|].
    rewrite Hj. replace (f + Z.of_nat 8) with (f + 8) by lia. exact Hb2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i 8) as [Hi8|Hi8]; [apply Hw1; lia|].
    replace (f + i) with (f + 8 + (i - 8)) by lia. apply Hw2. lia.
Qed.

Lemma rw_tail_cb : forall m f j rest, rw_cells rsegs m f (CB 8 j :: rest) -> rw_cells rsegs m (f + 8) rest.
Proof.
  intros m f j rest [[[Hj Hwf] Hb] [Hf0 [Hf1 Hw]]]. cbn [cell_wf] in Hj.
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hf1, Hw.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hj in Hb.
  replace (f + Z.of_nat 8) with (f + 8) in Hb by lia.
  split; [split; [exact Hwf | exact Hb] |].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (f + 8 + i) with (f + (i + 8)) by lia. apply Hw. lia.
Qed.

Lemma unsigned8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma zxb8 : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite unsigned8 by exact Hc. reflexivity. Qed.

Lemma ts_case : forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n i c f p t : Z) (j : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x103ec + 16 <= f -> f + 112 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= c < 256 -> i < n ->
  rw_cells rsegs m f [CB 8 j] -> mem_inv rsegs m -> bytes_at rsegs m 0x103ec hexl ->
  evt rsegs (ts_Q n i c f p t rav gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc m)
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 p) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
             (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x152e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n i c f p t j
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v Hf Hf1 Hp Hc Hi RC MI HX.
  rewrite <- (zxb8 c) by lia.
  apply (ts_body _ ra gp tp t0 t1 t2 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m f p (Z_to_bv 8 c) j);
    rewrite ?unsigned8 by lia; [lia | lia | lia | lia | exact RC | exact MI | exact HX | | |].
  - intros Hs r1 x1 x2 x3 m' MU WM -> -> ->. apply evt_done. right. left.
    split; [exact Hi|]. split; [exact Hs|]. unfold at_call.
    exists t0, t1, t2, x3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact I].
  - intros H1 H2 H3 r1 x2 x3 m' MU WM -> ->. apply evt_done. right. right. left.
    split; [exact Hi|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. unfold at_call.
    exists t0, t1, t2, x3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact I].
  - intros Hl r1 x1 x2 x3 m' MU WM HB -> -> ->. apply evt_done. right. right. right.
    split; [exact Hi|]. split; [exact Hl|]. unfold at_call.
    exists t0, t1, t2, x3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact HB].
Qed.

Lemma ts_go0 : forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n c f s t : Z) (j : list byte) (rav s0v s1v : word),
  0x103ec + 16 <= f -> f + 112 < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> 0 <= s < 2 ^ 64 -> 0 <= c < 256 ->
  0 <= n -> (c = 0 <-> n = 0) ->
  ov_read_bytes rsegs m (wa s) 1 = Some [Z_to_bv 8 c] ->
  rw_cells rsegs m f [CB 8 j] ->
  rw_cells rsegs m (f + 8) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                            C8 s1v; C8 s0v; C8 rav] ->
  mem_inv rsegs m -> bytes_at rsegs m 0x103ec hexl ->
  evt rsegs (ts_Q n 0 c f s t rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 s) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x152b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n c f s t j
    rav s0v s1v Hf Hf1 Ht Hs Hc Hn Hcn RD RC SV MI HX.
  apply (ts_first _ ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (Z_to_bv 8 c) Hs RD);
    rewrite ?unsigned8 by lia.
  - intros Hc0 x0 _. assert (Hn0 : n = 0) by (apply Hcn; exact Hc0).
    eapply evt_mono; [apply (ts_epi ra gp tp t0 t1 t2 (Z_to_bv 64 s) x0 a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               rav s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 f t Ht ltac:(lia) Hf1) |].
    + exists j. exact (rw_cons_cb m f j _ RC SV).
    + intros ms H. left. split; [lia | exact H].
  - intros Hc0 x0 x1 x2 y2 y10 -> -> ->.
    assert (Hn0 : 0 < n) by (destruct (Z.eq_dec n 0) as [E|E]; [apply Hcn in E; lia | lia]).
    rewrite zxb8 by lia. apply (ts_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m n 0 c f s t j); lia || assumption.
Qed.

Lemma ts_go1 : forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n i c f p t : Z) (j : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x103ec + 16 <= f -> f + 112 < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> 0 <= p -> p + 1 < 2 ^ 64 -> 0 <= c < 256 ->
  i <= n -> (c = 0 <-> i = n) ->
  ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [Z_to_bv 8 c] ->
  rw_cells rsegs m f [CB 8 j] ->
  rw_cells rsegs m (f + 8) [C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v;
                            C8 s1v; C8 s0v; C8 rav] ->
  mem_inv rsegs m -> bytes_at rsegs m 0x103ec hexl ->
  evt rsegs (ts_Q n i c f (p + 1) t rav gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc m)
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
             (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
             t3 t4 t5 t6) F (Z_to_bv 64 0x1536c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n i c f p t j
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v Hf Hf1 Ht Hp Hp1 Hc Hn Hcn RD RC SV MI HX.
  apply (ts_next _ ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
           (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec) (Z_to_bv 64 13)
           t3 t4 t5 t6 F fc m p (Z_to_bv 8 c) Hp Hp1 RD);
    rewrite ?unsigned8 by lia.
  - intros Hc0 x0 y1 _ ->. assert (Hn0 : i = n) by (apply Hcn; exact Hc0).
    eapply evt_mono; [apply (ts_epi ra gp tp t0 t1 t2 (Z_to_bv 64 (p + 1)) x0 a1 a2 a3 a4 a5 a6 a7
                               (Z_to_bv 64 0x102e9) (Z_to_bv 64 92) (Z_to_bv 64 9) (Z_to_bv 64 48) (Z_to_bv 64 34)
                               (Z_to_bv 64 32) (Z_to_bv 64 117) (Z_to_bv 64 10) (Z_to_bv 64 0x103ec)
                               (Z_to_bv 64 13) t3 t4 t5 t6 F fc m
                               rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v f t Ht ltac:(lia) Hf1) |].
    + exists j. exact (rw_cons_cb m f j _ RC SV).
    + intros ms H. left. split; [lia | exact H].
  - intros Hc0 x0 y1 -> ->.
    assert (Hn0 : i < n) by (destruct (Z.eq_dec i n) as [E|E]; [apply Hcn in E; lia | lia]).
    rewrite zxb8 by lia. apply (ts_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m n i c f (p + 1) t j); lia || assumption.
Qed.
