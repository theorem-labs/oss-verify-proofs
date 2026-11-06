From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sa.
Import ListNotations.
Open Scope Z_scope.

Lemma a09_eqb0 : forall x, 0 <= x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof. intros x Hx. unfold bv_eqb. rewrite (unsigned_lit x) by lia. reflexivity. Qed.

Lemma a09_ne0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. rewrite a09_eqb0 by lia. apply Z.eqb_neq. lia. Qed.

Lemma a09_nrec : forall x, 0 <= x < 256 ->
  Z_to_bv 64 (x - bv_unsigned (Z_to_bv 64 (Z.lor
      (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 283796062672454641) 64))) 6)))
      (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 283796062672454641) 64)))))) = Z_to_bv 64 (x mod 65).
Proof.
  intros x Hx.
  assert (H : forallb (fun k => let z := Z.of_nat k in
      bv_eqb (Z_to_bv 64 (z - bv_unsigned (Z_to_bv 64 (Z.lor
        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 283796062672454641) 64))) 6)))
        (bv_unsigned (Z_to_bv 64 (Z.shiftr (z * 283796062672454641) 64)))))))
        (Z_to_bv 64 (z mod 65))) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). cbv beta zeta in H. rewrite Z2Nat.id in H by lia.
  unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma a09_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. apply unsigned_lit. lia.
Qed.

Lemma a09_z :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 368 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 16) [Cells.CB 24 j1] -> rw_cells rsegs m (spv + 112) [Cells.CB 12 j2] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1352c) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 40); (spv + 112, spv + 124)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 16) (le8 (Z_to_bv 64 (spv + 133))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x12f78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv j1 j2 -> -> -> Hs Hsp C1 C2 MI.
  pose proof (munch_refl [(spv + 16, spv + 40); (spv + 112, spv + 124)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.
  step. step. step. step.
  step. if_true.
  pose proof (sa_cells_bytes _ _ _ C1) as X. cbn [Cells.cells_bytes Cells.cbytes] in X.
  apply bytes_at_app in X as [X _].
  apply evt_done. eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact X].
Qed.

Lemma a09_e :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv n p : Z) (b : byte)
         (j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 n -> s4 = Z_to_bv 64 p -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 368 <= 2 ^ 64 -> 1 <= n < 2 ^ 26 -> 0 <= p -> p + n <= spv ->
    bv_unsigned b mod 65 = 0 ->
    rw_cells rsegs m (spv + 16) [Cells.CB 24 j1] -> rw_cells rsegs m (spv + 112) [Cells.CB 12 j2] ->
    bytes_at rsegs m p [b] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (p + 1))
                       s5 s6 s7 s8 s9 (Z_to_bv 64 (n + -1)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13530) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 40); (spv + 112, spv + 124)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 16) (le8 (Z_to_bv 64 (spv + 133))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x12f78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv n p b j1 j2 -> -> -> -> Hs Hsp Hn Hp Hps H65 C1 C2 HB MI.
  pose proof (munch_refl [(spv + 16, spv + 40); (spv + 112, spv + 124)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8.
  step. if_false.
  step. step. step. step.
  step. if_false_by (a09_ne0 n ltac:(lia)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HR : ov_read_bytes rsegs mm (wa p) 1 = Some [b])
      by (replace (wa p) with (wa (p + 0)) by (f_equal; lia);
          rewrite (bytes_at_read rsegs mm p [b] 0 1 HB) by (cbn; lia); reflexivity)
  end.
  step. step. step. step. step. step. step. step. step. step.
  rewrite !a09_zxb in *. rewrite (a09_nrec (bv_unsigned b)) in * by lia. rewrite H65 in *.
  step. if_true.
  pose proof (sa_cells_bytes _ _ _ C1) as X. cbn [Cells.cells_bytes Cells.cbytes] in X.
  apply bytes_at_app in X as [X _].
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact X].
Qed.

Lemma a09_l :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv n p : Z) (b : byte)
         (j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 n -> s4 = Z_to_bv 64 p -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 368 <= 2 ^ 64 -> 1 <= n < 2 ^ 26 -> 0 <= p -> p + n <= spv ->
    bv_unsigned b mod 65 <> 0 ->
    rw_cells rsegs m (spv + 16) [Cells.CB 24 j1] -> rw_cells rsegs m (spv + 112) [Cells.CB 12 j2] ->
    bytes_at rsegs m p [b] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) (Z_to_bv 64 (p + 1))
                       s5 s6 s7 s8 s9 (Z_to_bv 64 (n + -1)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12fc4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 40); (spv + 112, spv + 124)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 16) (le8 (Z_to_bv 64 (spv + 133))) /\
         bytes_at rsegs m' (spv + 24) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs m' (spv + 32) (le8 (Z_to_bv 64 (bv_unsigned b mod 65))) /\
         bytes_at rsegs m' (spv + 112) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs m' (spv + 120) (le4 (Z_to_bv 64 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x12f78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv n p b j1 j2 -> -> -> -> Hs Hsp Hn Hp Hps H65 C1 C2 HB MI.
  pose proof (munch_refl [(spv + 16, spv + 40); (spv + 112, spv + 124)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 65 ltac:(lia)) as R65.
  step. if_false.
  step. step. step. step.
  step. if_false_by (a09_ne0 n ltac:(lia)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HR : ov_read_bytes rsegs mm (wa p) 1 = Some [b])
      by (replace (wa p) with (wa (p + 0)) by (f_equal; lia);
          rewrite (bytes_at_read rsegs mm p [b] 0 1 HB) by (cbn; lia); reflexivity)
  end.
  step. step. step. step. step. step. step. step. step. step.
  rewrite !a09_zxb in *. rewrite (a09_nrec (bv_unsigned b)) in * by lia.
  step. if_false_by (a09_ne0 (bv_unsigned b mod 65) ltac:(lia)).
  step. step.
  pose proof (sa_cells_bytes _ _ _ C1) as X. cbn [Cells.cells_bytes Cells.cbytes] in X.
  apply bytes_at_app in X as [X1 X]. rewrite length_le8 in X.
  apply bytes_at_app in X as [X2 X]. rewrite length_le8 in X.
  apply bytes_at_app in X as [X3 _].
  pose proof (sa_cells_bytes _ _ _ C2) as Y. cbn [Cells.cells_bytes Cells.cbytes] in Y.
  apply bytes_at_app in Y as [Y1 Y]. rewrite length_le8 in Y.
  apply bytes_at_app in Y as [Y2 _].
  replace (spv + 16 + Z.of_nat 8) with (spv + 24) in X2 by lia.
  replace (spv + 16 + Z.of_nat 8 + Z.of_nat 8) with (spv + 32) in X3 by lia.
  replace (spv + 112 + Z.of_nat 8) with (spv + 120) in Y2 by lia.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact Y1 | exact Y2].
Qed.

Section A09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_A09 : Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) 0 ->
  Hcut B APIf ra (Inv_K1352c B APIf ra empty) -> Hcut B APIf ra (Inv_K13530 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f78 B APIf ra empty).
Proof.
  intros H1 H2 H3 g c (L & A & regs & mem & md & -> & HFR & HP & (Hn & Hp) & HID & H10).
  destruct (sa_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sa_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (Hn26 & Hpl & Hbd & _ & HSKc & _).
  pose proof (sa_segs B APIf ra empty FF) as SEGS.
  pose proof alloc_ceiling_value as Hac.
  unfold SLOT_K, SLOT_STACK, SA_TOP, fsp, SLOT_FRAME in *.
  destruct (sa_rw_of_stk _ _ _ (g_S g - 368 + 16) 24 ST ltac:(lia) ltac:(lia)) as (j1 & C1).
  destruct (sa_rw_of_stk _ _ _ (g_S g - 368 + 112) 12 ST ltac:(lia) ltac:(lia)) as (j2 & C2).
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HID) as HIDn.
  assert (KID : forall m0 m', Frame.munch [(g_S g - 368 + 16, g_S g - 368 + 40);
      (g_S g - 368 + 112, g_S g - 368 + 124)] (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 -> IDb g 0 m').
  { intros m0 m' MU HR. unfold IDb. apply (proj2 (bytes_at_rel rsegs m' m0 _ _ HR)).
    eapply bytes_at_transport; [exact HIDn | exact MU |].
    unfold spk, fsp, SLOT_FRAME. rewrite rec_id_length. cbn [disjoint_from]. unfold RcIdentModel.ID_SIZE.
    split; [lia | split; [lia | exact I]]. }
  assert (FP : forall y, 0 <= y < 2 ^ 64 -> ~ Frame.outside [(g_S g - 368 + 16, g_S g - 368 + 40);
      (g_S g - 368 + 112, g_S g - 368 + 124)] y -> g_S g - SLOT_K <= y < g_S g - 104).
  { intros y Hy O. unfold SLOT_K, SLOT_STACK.
    destruct (Z_le_dec (g_S g - 368 + 16) y); destruct (Z_lt_dec y (g_S g - 368 + 40));
    destruct (Z_le_dec (g_S g - 368 + 112) y); destruct (Z_lt_dec y (g_S g - 368 + 124)); try lia;
    exfalso; apply O; cbn [Frame.outside]; repeat split; try lia; exact I. }
  assert (G16m : forall m0 m', bytes_at rsegs m0 (g_S g - 368 + 16) (le8 (Z_to_bv 64 (g_S g - 368 + 133))) ->
      mem_rel rsegs m' m0 -> G16 g m').
  { intros m0 m' X HR. unfold G16, q64, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs m' m0 _ _ HR) X). }
  destruct (Z.eq_dec (g_n g) 0) as [N0 | N0].
  - assert (Hs1 : YK11.getr regs 9 = Z_to_bv 64 0) by (rewrite Hn, N0; reflexivity).
    eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sa_mkR_of. apply a09_z with (spv := g_S g - 368) (j1 := j1) (j2 := j2);
        [exact Hsp | exact Hs1 | exact H10 | lia | lia | exact C1 | exact C2 | exact (mem_inv_normalize rsegs mem)].
    + intros ms (? & ? & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM | exact FP].
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & m'' & HE & MU & _ & X). injection HE; intros; subst.
      apply H2. exists L, A, regs', m', md. split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact N0|].
      split; [rewrite (sa_getr_eqv _ _ _ Hx); exact Hs1|].
      split; [rewrite (sa_getr_eqv _ _ _ Hx); exact Hp|].
      split; [exact (G16m _ _ X Hrel) | exact (KID _ _ MU Hrel)].
  - destruct Hpl as [[N0' _] | [Npos Hin]]; [lia|].
    assert (Hlen : exists b rest, g_in g = b :: rest).
    { destruct (g_in g) as [|b rest] eqn:E; [|eauto]. unfold g_n, nlen in Npos. rewrite E in Npos. cbn in Npos. lia. }
    destruct Hlen as (b & rest & Ein).
    assert (HNR : NR g = bv_unsigned b mod 65) by (unfold NR, nrec, inb; rewrite Ein; reflexivity).
    assert (Hin2 : In (g_p g, g_n g) (blocks L A)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    apply blocks_In in Hin2 as (q & Hq & Hqin).
    destruct (mr_blocks B (aa_MR (APIf rc)) (aa_laws (APIf rc)) L A mem md q (g_n g) 0 HM Hqin ltac:(lia))
      as (_ & Hq1 & Hq2 & _).
    rewrite Hq in Hq1, Hq2.
    assert (HB : bytes_at rsegs mem (g_p g) [b]).
    { split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. destruct i; [|lia].
      pose proof (Hblk _ _ 0 Hin ltac:(lia)) as E1.
      pose proof (Hbd 0 ltac:(unfold g_n, nlen in Npos; lia)) as E2. rewrite Ein in E2.
      rewrite E2 in E1. rewrite SEGS in E1. unfold mbyte in E1. unfold Mem.mrd, Mem.wa. exact E1. }
    pose proof (bytes_at_normalize rsegs mem _ _ HMI HB) as HBn.
    pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8.
    assert (Hrc0 : rec_c (g_in g) 0 = 1) by (cbn [rec_c]; change (nlen (g_in g)) with (g_n g); lia).
    destruct (Z.eq_dec (bv_unsigned b mod 65) 0) as [Z65 | Z65].
    + eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
      * rewrite sa_mkR_of. apply a09_e with (spv := g_S g - 368) (n := g_n g)
          (p := g_p g) (b := b) (j1 := j1) (j2 := j2);
          [exact Hsp | exact Hn | exact Hp | exact H10 | lia | lia | lia | lia | lia | exact Z65 | exact C1
          | exact C2 | exact HBn | exact (mem_inv_normalize rsegs mem)].
      * intros ms (? & ? & ? & ? & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
        split; [|split; [reflexivity | split; reflexivity]].
        eexists. split; [exact MU|]. split; [exact WM | exact FP].
      * intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
        destruct HQ as (? & ? & ? & m'' & HE & MU & _ & X). injection HE; intros; subst.
        assert (HcT : cT (g_in g) = 1).
        { unfold cT, nrecn. change (nrec (g_in g)) with (NR g). rewrite HNR, Z65. exact Hrc0. }
        apply H3. exists L, A, regs', m', md. split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split; [rewrite HNR; exact Z65|].
        split.
        { rewrite HcT. unfold CUR. split; [lia|].
          rewrite !(sa_getr_eqv _ _ _ Hx). split; [reflexivity|]. f_equal; lia. }
        split; [exact (G16m _ _ X Hrel) | exact (KID _ _ MU Hrel)].
    + eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
      * rewrite sa_mkR_of. apply a09_l with (spv := g_S g - 368) (n := g_n g)
          (p := g_p g) (b := b) (j1 := j1) (j2 := j2);
          [exact Hsp | exact Hn | exact Hp | exact H10 | lia | lia | lia | lia | lia | exact Z65 | exact C1
          | exact C2 | exact HBn | exact (mem_inv_normalize rsegs mem)].
      * intros ms (? & ? & ? & ? & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
        split; [|split; [reflexivity | split; reflexivity]].
        eexists. split; [exact MU|]. split; [exact WM | exact FP].
      * intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
        destruct HQ as (? & ? & ? & m'' & HE & MU & _ & X16 & X24 & X32 & Y112 & Y120). injection HE; intros; subst.
        apply H1. exists L, A, regs', m', md. split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        split.
        { split; [rewrite HNR; cbn [Z.of_nat]; pose proof (Z.mod_pos_bound (bv_unsigned b) 65); lia|].
          split; [rewrite (sa_getr_eqv _ _ _ Hx); reflexivity|].
          split; [unfold NRb, q64, spk, fsp, SLOT_FRAME; rewrite HNR;
                  exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) X32)|].
          split; [exact (G16m _ _ X16 Hrel)|].
          unfold HWb, q64, u32, spk, fsp, SLOT_FRAME.
          assert (E8 : le8 (Z_to_bv 64 0) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)) by reflexivity.
          rewrite E8 in Y112. apply bytes_at_app in Y112 as [Y1 Y2]. rewrite length_le4 in Y2.
          split; [exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) X24)|].
          split; [exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) Y1)|].
          apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)).
          replace (rec_hwb (g_in g) 0) with (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)) by reflexivity.
          apply bytes_at_app. split.
          - replace (g_S g - 368 + 116) with (g_S g - 368 + 112 + Z.of_nat 4) by lia. exact Y2.
          - rewrite length_le4. replace (g_S g - 368 + 116 + Z.of_nat 4) with (g_S g - 368 + 120) by lia. exact Y120. }
        split.
        { rewrite Hrc0. unfold CUR. split; [lia|].
          rewrite !(sa_getr_eqv _ _ _ Hx). split; [reflexivity|]. f_equal; lia. }
        exact (KID _ _ MU Hrel).
Qed.

End A09.
