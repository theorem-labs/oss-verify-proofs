(* text_of (plain): the run from malloc's return (0x15bf8, a0 = the fresh block h) to the `ret`,
   over a memory without read-only entries (mem_inv): the copy of the n taken bytes (memcpy, a
   Section hypothesis, skipped when n = 0), the NUL at h + n, *own = h, and the epilogue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memcpy_c text_of_lem.
Import ListNotations.
Open Scope Z_scope.

Lemma tt_rw_bytes : forall segs m a k bs, rw_cells segs m a [CB k bs] -> bytes_at segs m a bs.
Proof. intros segs m a k bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma tt_rw_byte : forall segs m a b, rw_cells segs m a [C1 b] -> bytes_at segs m a [b].
Proof. intros segs m a b [[_ H] _]. cbn [cells_bytes cbytes] in H. exact H. Qed.

Lemma tt_bytes_cat : forall segs m a bs c, bytes_at segs m a bs ->
  bytes_at segs m (a + Z.of_nat (length bs)) [c] -> bytes_at segs m a (bs ++ [c]).
Proof.
  intros segs m a bs c (H0 & H1 & H) (G0 & G1 & G). cbn [length] in G1.
  split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi.
  destruct (Nat.lt_ge_cases i (length bs)) as [L|L].
  - rewrite nth_error_app1 by exact L. apply H. exact L.
  - assert (E : i = length bs) by lia. subst i.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn.
    specialize (G 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in G. exact G.
Qed.

Section Tail.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HMCP : memcpy_contract.

Definition tail_post (ra sp r0 r1 r2 r3 : word) (h A0 A1 n : Z) (tk : list byte) (v1 v2 : word)
    (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists sp' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR ra sp' gp tp x5 x6 x7 r0 r1 (Z_to_bv 64 h) x11 x12 x13 x14 x15 x16 x17 r2 r3
                  s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ bv_unsigned sp' = bv_unsigned sp + 48
    /\ munch [(h, h + n + 1); (A1, A1 + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' h (tk ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' A1 [C8 (Z_to_bv 64 h)]
    /\ rw_cells rsegs m' A0 [C8 v1; C8 v2].

Lemma tail_walk : forall (m : word -> option byte)
    (sp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 r0 r1 r2 r3 R v v1 v2 : word)
    (h hn P n A0 A1 : Z) (tk junk j1 : list byte) (jb : byte),
  0 < h -> hn = h + n -> Z.of_nat (length tk) = n -> 0 <= P < 2 ^ 64 ->
  bv_unsigned sp + 48 < 2 ^ 63 ->
  bytes_at rsegs m P tk ->
  rw_cells rsegs m h [CB (Z.to_nat n) j1] -> rw_cells rsegs m hn [C1 jb] ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 r3; C8 r2; C8 r1; C8 r0; C8 R] ->
  rw_cells rsegs m A1 [C8 v] -> rw_cells rsegs m A0 [C8 v1; C8 v2] ->
  (P + n <= h \/ h + n + 1 <= P) ->
  (h + n + 1 <= A1 \/ A1 + 8 <= h) -> (h + n + 1 <= A0 \/ A0 + 16 <= h) ->
  (h + n + 1 <= bv_unsigned sp \/ bv_unsigned sp + 48 <= h) ->
  (A1 + 8 <= bv_unsigned sp \/ bv_unsigned sp + 48 <= A1) ->
  (A0 + 16 <= bv_unsigned sp \/ bv_unsigned sp + 48 <= A0) ->
  (A1 + 8 <= A0 \/ A0 + 16 <= A1) ->
  mem_inv rsegs m ->
  evt rsegs (tail_post R sp r0 r1 r2 r3 h A0 A1 n tk v1 v2 m)
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 A1) (Z_to_bv 64 P) (Z_to_bv 64 h) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 n) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15bf8) fc None m (seg_rom rsegs)).
Proof.
  intros m sp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 r0 r1 r2 r3 R v v1 v2
    h hn P n A0 A1 tk junk j1 jb H0 Ehn LTK P0 S63 SRC DST DLB FR OWN CUR
    DSP DDO DDC DDF DOF DCF DOC MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof (rw_cells_bound _ _ _ _ DLB) as BD. cbn [cells_size csize] in BD.
  pose proof (rw_cells_bound _ _ _ _ OWN) as BO. cbn [cells_size csize] in BO.
  pose proof (rw_cells_bound _ _ _ _ CUR) as BC. cbn [cells_size csize] in BC.
  assert (N0 : 0 <= n) by lia.
  assert (UH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UA1 : bv_unsigned (Z_to_bv 64 A1) = A1) by (apply unsigned_lit; lia).
  assert (UHN : bv_unsigned (Z_to_bv 64 (h + n)) = h + n) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(h, h + n + 1); (A1, A1 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. if_false.
  zstep.
  zstep.
  destruct (Z.eq_dec n 0) as [Z0|Z0].
  - if_true.
    assert (TK0 : tk = []) by (destruct tk; [reflexivity | cbn in LTK; lia]).
    subst tk.
    zstep.
    rewrite <- Ehn.
    zstep.
    try (first [rewrite tl_le1_zero | rewrite tl_zlb1_zero | idtac]; mem_after_store).
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    apply evt_done. do 16 eexists.
    split; [reflexivity|].
    split; [first [reflexivity | (rewrite unsigned_lit by lia; lia)]|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split.
    { cbn [app]. lazymatch goal with H : rw_cells rsegs ?mm hn [C1 _] |- bytes_at rsegs ?mm _ _ =>
        apply tt_rw_byte in H; replace h with hn by lia; exact H end. }
    split; eassumption.
  - if_false.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HMCP with (src := tk) (junk := j1);
        [ rewrite UP; exact SRC
        | rewrite UN; lia
        | rewrite UH, UN; exact DST
        | rewrite UP, UH, UN; lia
        | eassumption ]
      | unfold memcpy_post; post_call rsegs mm ] end.
    zstep.
    rewrite <- Ehn.
    zstep.
    try (first [rewrite tl_le1_zero | rewrite tl_zlb1_zero | idtac]; mem_after_store).
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    apply evt_done. do 16 eexists.
    split; [reflexivity|].
    split; [first [reflexivity | (rewrite unsigned_lit by lia; lia)]|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split.
    { lazymatch goal with
      | H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 h)) [CB _ tk], H2 : rw_cells rsegs ?mm hn [C1 _]
        |- bytes_at rsegs ?mm _ _ =>
          rewrite UH in H; apply tt_rw_bytes in H; apply tt_rw_byte in H2;
          apply tt_bytes_cat; [exact H | replace (h + Z.of_nat (length tk)) with hn by lia; exact H2]
      end. }
    split; eassumption.
Qed.

End Tail.
