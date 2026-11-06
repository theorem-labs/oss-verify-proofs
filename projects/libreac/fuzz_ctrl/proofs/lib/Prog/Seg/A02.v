(* Segment A02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): the six-byte `our` loop [0x1324c, 0x13284] and 0x13594,
   K1324c (t) -> K1324c (t + 1) (left != 0, t + 1 < 6), K13288 (left != 0, t = 5) or K13598 (left = 0, n = t < 6:
   the inner loop at 0x1325c writes zeros at sp+76+t .. sp+81, then s5 = p + n). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. The plain segment table
   (v190-segment-table-plain.md (a working note, not in this delivery)) has S_A02 CHANGED with kinds new-call, new-insert,
   register; the new-call / new-insert part (the memset of `first`, NEW 0x13598 .. 0x135a4) is not on this segment:
   SlotInv.v keeps K13598 at 0x13598, so the exit 0x13594 `mv s5,a2` -> 0x13598 is v1.8's and the memset is in S_P01.
   What remains is the register renaming s7 -> s11 (0x13258 `mv s11,a1`, 0x1325c `bnez s11`, 0x13278 `addi
   a1,s11,-1`; the left count of CUR) and `our` sp+60 -> sp+76 (a3 = sp+76 from A01), frame 1920 -> 1936; pcs and
   the instruction sequence are v1.8's. Statements: seg_A02 unchanged; a02_zero takes s11 = 0 (was s7), a02_fill /
   a02_turn return the left count in s11 (was s7), with `our` at spv+76. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

(* ---- The model side: OUR from the bytes the loop stores ---- *)
Lemma a02_firstn_S : forall (l : list byte) k, (k < length l)%nat ->
  firstn (S k) l = firstn k l ++ [RcIdentModel.nthb l k].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|].
  change (firstn (S (S k)) (x :: l)) with (x :: firstn (S k) l).
  rewrite (IH k) by lia. reflexivity.
Qed.

Lemma a02_OUR_short : forall l : list byte, (length l <= 6)%nat -> OUR l = l ++ repeat z8 (6 - length l).
Proof.
  intros l Hl. unfold OUR.
  do 6 (destruct l as [|? l]; [reflexivity|]).
  destruct l as [|? l]; [reflexivity | cbn in Hl; lia].
Qed.

Lemma a02_OUR_full : forall l : list byte, (6 <= length l)%nat -> OUR l = firstn 6 l.
Proof.
  intros l Hl. unfold OUR.
  do 6 (destruct l as [|? l]; [cbn in Hl; lia|]).
  reflexivity.
Qed.

(* The prefix grows by the byte read at p + t. *)
Lemma a02_pre : forall m a (inp : list byte) t, 0 <= t < nlen inp ->
  bytes_at rsegs m a (firstn (Z.to_nat t) inp) -> bytes_at rsegs m (a + t) [RcIdentModel.nthb inp (Z.to_nat t)] ->
  bytes_at rsegs m a (firstn (Z.to_nat (t + 1)) inp).
Proof.
  intros m a inp t Ht H1 H2. unfold nlen in Ht.
  replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
  rewrite a02_firstn_S by lia.
  apply bytes_at_app. split; [exact H1|].
  assert (E : Z.of_nat (length (firstn (Z.to_nat t) inp)) = t) by (rewrite length_firstn; lia).
  rewrite E. exact H2.
Qed.

(* n = t < 6: OUR is the n input bytes and 6 - n zeros. *)
Lemma a02_our_short : forall m a (inp : list byte) t, nlen inp = t -> 0 <= t <= 5 ->
  bytes_at rsegs m a (firstn (Z.to_nat t) inp) -> bytes_at rsegs m (a + t) (repeat z8 (Z.to_nat (6 - t))) ->
  bytes_at rsegs m a (OUR inp).
Proof.
  intros m a inp t Hn Ht H1 H2. unfold nlen in Hn.
  rewrite a02_OUR_short by lia.
  rewrite (firstn_all2 (n := Z.to_nat t)) in H1 by lia.
  apply bytes_at_app. split; [exact H1|].
  replace (a + Z.of_nat (length inp)) with (a + t) by lia.
  replace (6 - length inp)%nat with (Z.to_nat (6 - t)) by lia.
  exact H2.
Qed.

(* ---- Branch conditions ---- *)
Lemma a02_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y Hx Hy Hn. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x y) Hn). reflexivity.
Qed.

Lemma a02_eq : forall x y, x = y -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof. intros x y ->. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Ltac a02_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
      first [ if_false_by (a02_eq x y ltac:(lia))
            | if_true_by (a02_ne x y ltac:(lia) ltac:(lia) ltac:(lia)) ]
  end.

Ltac a02_w := first [ reflexivity
                    | (rewrite ?MState.unsigned_lit by lia; f_equal; lia)
                    | (apply bv_eq; rewrite ?MState.unsigned_lit by lia; lia) ].

(* ---- The inner loop (head 0x1325c, s11 = 0): a0 = u, a6 = x; k = 7 - u zero bytes at x, then 0x13594 s5 = a2,
   exit at 0x13598. *)
Lemma a02_zero : forall (k : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x u q lo hi : Z),
  s11 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 u -> a6 = Z_to_bv 64 x -> a4 = Z_to_bv 64 7 -> a2 = Z_to_bv 64 q ->
  u + Z.of_nat k = 7 -> 1 <= u <= 6 -> lo <= x -> x + Z.of_nat k <= hi ->
  stk rsegs m lo hi ->
  evt rsegs
    (fun ms' => exists (a0' a6' s5' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6' a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6)
                F (Z_to_bv 64 0x13598) fc None m' (seg_rom rsegs) /\
       s5' = Z_to_bv 64 q /\ munch [(x, x + Z.of_nat k)] m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' x (repeat z8 k))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1325c) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m x u q lo hi -> -> -> -> -> Hk Hu Hx1 Hx2 ST; [lia|].
  pose proof ST as (Hlo & Hhi & _).
  destruct (sl_rw_of_stk m lo hi x 1 ST Hx1 ltac:(lia)) as (junk & HC).
  pose proof (munch_refl [(x, x + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.
  step. change (le1 (Z_to_bv 64 0)) with [z8]. mem_after_store.
  pose proof (sl_cells_bytes _ _ _ HC) as HB1. cbn [Cells.cells_bytes Cells.cbytes app] in HB1.
  step. step. step.
  destruct k as [|k].
  - (* u = 6: exit *)
    a02_br. step. step.
    apply evt_done. eexists _, _, _, _. split; [reflexivity|].
    split; [a02_w|]. split; [replace (x + Z.of_nat 1) with (x + 1) by lia; exact MU|].
    split; [exact WM | exact HB1].
  - (* u < 6: the next turn *)
    a02_br.
    eapply evt_cut.
    { eapply IH with (x := x + 1) (u := u + 1) (q := q) (lo := lo) (hi := hi).
      all: first [ reflexivity | lia | assumption | a02_w ]. }
    intros ms' (a0' & a6' & s5' & m' & -> & E5 & MU' & WM' & HB').
    apply evt_done. exists a0', a6', s5', m'. split; [reflexivity|].
    split; [exact E5|]. split.
    { eapply munch_trans.
      - eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros y [Hy _]. split; [lia | exact I].
      - eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside]. intros y [Hy _]. split; [lia | exact I]. }
    split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
    change (repeat z8 (S (S k))) with ([z8] ++ repeat z8 (S k)).
    apply bytes_at_app. split.
    + apply (bytes_at_transport rsegs _ _ m' _ _ HB1 MU'). cbn [disjoint_from length]. split; [lia | exact I].
    + replace (x + Z.of_nat (length [z8])) with (x + 1) by (cbn [length]; lia). exact HB'.
Qed.

(* left = 0 (n = t): 0x1324c .. 0x13258, then the inner loop from u = t + 1, x = sp+76+t. *)
Lemma a02_fill :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv t q lo hi : Z),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 q -> a3 = Z_to_bv 64 (spv + 76) -> a4 = Z_to_bv 64 7 ->
    0 <= t <= 5 -> lo <= spv + 76 + t -> spv + 82 <= hi ->
    stk rsegs m lo hi ->
    evt rsegs
      (fun ms' => exists (a0' a2' a6' s5' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6' a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13598) fc None m' (seg_rom rsegs) /\
         s5' = Z_to_bv 64 q /\ s11' = Z_to_bv 64 0 /\
         munch [(spv + 76 + t, spv + 82)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 76 + t) (repeat z8 (Z.to_nat (6 - t))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1324c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv t q lo hi -> -> -> -> -> Ht Hlo Hhi ST.
  step. step. step. step.
  eapply evt_cut.
  { eapply a02_zero with (k := Z.to_nat (6 - t)) (x := spv + 76 + t) (u := t + 1) (q := q) (lo := lo) (hi := hi).
    all: first [ reflexivity | lia | exact ST | a02_w ]. }
  intros ms' (a0' & a6' & s5' & m' & -> & E5 & MU & WM & HB).
  replace (spv + 76 + t + Z.of_nat (Z.to_nat (6 - t))) with (spv + 82) in MU by lia.
  apply evt_done. eexists _, _, _, _, _, m'. split; [reflexivity|].
  split; [exact E5|]. split; [a02_w|].
  split; [exact MU|]. split; [exact WM | exact HB].
Qed.

(* left != 0: a7 = in[t] (lbu 0(a2), a2 = p + t), stored at sp+76+t; a0 = t + 1, a1 = left - 1, s5 = p + t + 1,
   s11 = left; bne a0, 6 -> 0x1324c, else 0x13288. *)
Lemma a02_turn :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv t l q : Z) (b : byte) (junk : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 l -> s5 = Z_to_bv 64 q -> a3 = Z_to_bv 64 (spv + 76) ->
    a4 = Z_to_bv 64 7 -> a5 = Z_to_bv 64 6 ->
    0 <= t <= 5 -> 1 <= l < 2 ^ 64 -> 0 <= q -> q + 1 < 2 ^ 64 -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    rw_cells rsegs m (spv + 76 + t) [Cells.CB 1 junk] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a6' a7' s5' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 (if t =? 5 then 0x13288 else 0x1324c)) fc None m' (seg_rom rsegs) /\
         a0' = Z_to_bv 64 (t + 1) /\ a1' = Z_to_bv 64 (l - 1) /\ a2' = Z_to_bv 64 q /\
         s5' = Z_to_bv 64 (q + 1) /\ s11' = Z_to_bv 64 l /\
         munch [(spv + 76 + t, spv + 77 + t)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (spv + 76 + t) [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1324c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv t l q b junk -> -> -> -> -> -> Ht Hl Hq0 Hq1 Hs0 Hs1 HR HC.
  pose proof (munch_refl [(spv + 76 + t, spv + 77 + t)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  assert (He : exists e, e = spv + 76 + t) by (eexists; reflexivity).
  destruct He as (e & He).
  rewrite <- He in HC |- *.
  step. step. step. a02_br.
  step. step. step. step.
  rewrite le1_zxb. mem_after_store.
  pose proof (sl_cells_bytes _ _ _ HC) as HB1. cbn [Cells.cells_bytes Cells.cbytes app] in HB1.
  step.
  destruct (Z.eq_dec t 5) as [E5|E5].
  - a02_br. replace (t =? 5) with true by (symmetry; apply Z.eqb_eq; exact E5).
    apply evt_done. subst e. eexists _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [a02_w|]. split; [a02_w|]. split; [a02_w|]. split; [a02_w|]. split; [a02_w|].
    split; [exact MU|]. split; [exact WM | exact HB1].
  - a02_br. replace (t =? 5) with false by (symmetry; apply Z.eqb_neq; exact E5).
    apply evt_done. subst e. eexists _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [a02_w|]. split; [a02_w|]. split; [a02_w|]. split; [a02_w|]. split; [a02_w|].
    split; [exact MU|]. split; [exact WM | exact HB1].
Qed.

Section A02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* One turn of the t loop, given the cut at t + 1. *)
Lemma a02_one : Hcut B APIf ra (Inv_K13288 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty) ->
  forall t : Z, (t + 1 <= 5 -> Hat B APIf ra (Inv_K1324c_at B APIf ra empty) (t + 1)) ->
  Hat B APIf ra (Inv_K1324c_at B APIf ra empty) t.
Proof.
  intros H88 H98 t IH g c
    (L & A & regs & mem & md & -> & HFR & HP & (Ht & Htn & H10 & H11 & H21 & H13 & H14 & H15 & HB0)).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HFR) as ST.
  pose proof HFR as ((Hn26 & _) & _).
  pose proof alloc_ceiling_value as Hac.
  unfold rg in H10, H11, H21, H13, H14, H15.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (Z.eq_dec (g_n g) t) as [Ent|Ent].
  - (* left = 0: zeros at sp+76+t .. sp+81, exit K13598 with c0 = n *)
    set (W := [(g_S g - 1936 + 76 + t, g_S g - 1936 + 82)]).
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of.
      apply a02_fill with (spv := g_S g - 1936) (t := t) (q := g_p g + t) (lo := g_S g - 65536) (hi := g_S g).
      * exact H10.
      * rewrite H11. f_equal. lia.
      * exact H21.
      * exact H13.
      * exact H14.
      * lia.
      * lia.
      * lia.
      * exact ST.
    + intros ms (? & ? & ? & ? & ? & m' & -> & _ & _ & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (a0' & a2' & a6' & s5' & s11' & m'' & HE & E5 & E11 & _ & _ & HB).
      injection HE; intros; subst R pc' m0' s5' s11'.
      apply H98. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold PB, CUR, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
      replace (c0 (g_in g)) with t by (unfold c0, g_n in *; lia).
      split; [split; [lia|]; split|].
      * reflexivity.
      * replace (g_n g - t) with 0 by lia. reflexivity.
      * unfold OURb. apply (a02_our_short m' (spk g 76) (g_in g) t); [exact Ent | lia | |].
        -- apply (bytes_at_transport rsegs W mem m' _ _ HB0 MU').
           rewrite length_firstn. unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
        -- exact (b1_out _ _ _ _ Hrel HB).
  - (* left != 0: store in[t] at sp+76+t *)
    destruct (b4_in_all B APIf ra empty FF g [] L A regs mem md HFR HP ltac:(lia)) as (Hp0 & Hpn & _).
    pose proof (b4_in_rd B APIf ra empty FF g [] L A regs mem md t HFR HP ltac:(lia)) as HR.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 76 + t) 1 ST ltac:(lia) ltac:(lia)) as (junk & HC).
    set (W := [(g_S g - 1936 + 76 + t, g_S g - 1936 + 77 + t)]).
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of.
      apply a02_turn with (spv := g_S g - 1936) (t := t) (l := g_n g - t) (q := g_p g + t)
        (b := RcIdentModel.nthb (g_in g) (Z.to_nat t)) (junk := junk).
      * exact H10.
      * exact H11.
      * exact H21.
      * exact H13.
      * exact H14.
      * exact H15.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact HR.
      * exact HC.
    + intros ms (? & ? & ? & ? & ? & ? & ? & m' & -> & _ & _ & _ & _ & _ & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (a0' & a1' & a2' & a6' & a7' & s5' & s11' & m'' & HE & E0 & E1 & E2 & E5 & E11 & _ & _ & HB).
      injection HE; intros; subst R pc' m0' a0' a1' a2' s5' s11'.
      assert (HB' : bytes_at rsegs m' (spk g 76) (firstn (Z.to_nat (t + 1)) (g_in g))).
      { apply (a02_pre m' (spk g 76) (g_in g) t); [unfold g_n in *; lia | |].
        - apply (bytes_at_transport rsegs W mem m' _ _ HB0 MU').
          rewrite length_firstn. unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
        - exact (b1_out _ _ _ _ Hrel HB). }
      destruct (Z.eq_dec t 5) as [E5'|E5'].
      * (* t = 5: K13288 *)
        rewrite (proj2 (Z.eqb_eq t 5) E5'). subst t.
        apply H88. exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [unfold g_n in *; lia|].
        split; [unfold OURb; rewrite a02_OUR_full by (unfold g_n, nlen in *; lia); exact HB'|].
        split; [replace (g_n g - 6) with (g_n g - 5 - 1) by lia; reflexivity|].
        split; [reflexivity|].
        split; [replace (g_p g + 6) with (g_p g + 5 + 1) by lia; reflexivity|].
        reflexivity.
      * (* t < 5: K1324c (t + 1) *)
        rewrite (proj2 (Z.eqb_neq t 5) E5').
        apply (IH ltac:(lia)). exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [lia|]. split; [unfold g_n in *; lia|].
        split; [reflexivity|].
        split; [replace (g_n g - (t + 1)) with (g_n g - t - 1) by lia; reflexivity|].
        split; [replace (g_p g + (t + 1)) with (g_p g + t + 1) by lia; reflexivity|].
        split; [exact H13|]. split; [exact H14|]. split; [exact H15|].
        exact HB'.
Qed.

Lemma seg_A02 : forall t : Z, Hcut B APIf ra (Inv_K13288 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13598 B APIf ra empty) -> Hat B APIf ra (Inv_K1324c_at B APIf ra empty) t.
Proof.
  intros t H88 H98.
  assert (ALL : forall (k : nat) t', Z.of_nat k = 5 - t' -> Hat B APIf ra (Inv_K1324c_at B APIf ra empty) t').
  { induction k as [|k IHk]; intros t' Hk; apply (a02_one H88 H98 t'); intros Ht1.
    - lia.
    - apply IHk. lia. }
  intros g c Hc.
  assert (Ht : 0 <= t <= 5) by (destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _); exact Ht).
  exact (ALL (Z.to_nat (5 - t)) t ltac:(lia) g c Hc).
Qed.

End A02.
