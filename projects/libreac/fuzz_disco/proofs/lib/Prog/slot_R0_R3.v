From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_exit.
Import ListNotations.
Open Scope Z_scope.

Definition ENTRY_PC : Z := 0x1327c.
Definition R1 : Z := 0x132c4.

Lemma slot_R0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z) (jsv : list byte),
  sp = Z_to_bv 64 (X + 2592) -> a1 = Z_to_bv 64 n ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m (X + 2488) [CB 104 jsv] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (m' : word -> option byte),
       ms' = MS (mkR ra (Z_to_bv 64 X) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (Z.shiftr n 26)) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (if n <? 2 ^ 26 then R1 else R29_RET)) fc None m' (seg_rom rsegs) /\
       munch [(X + 2488, X + 2592)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 2488) (saved_cells s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY_PC) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X n jsv Esp Ea1 HX0 HX1 Hn SV MI.
  subst sp a1. unfold ENTRY_PC, R1, R29_RET.
  pose proof (munch_refl [(X + 2488, X + 2592)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  step.
  step. rewrite ?(unsigned_lit n) by lia.
  assert (Hs : 0 <= Z.shiftr n 26 < 2 ^ 64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  step. rewrite eqb_lit by lia.
  unfold saved_cells.
  destruct (Z.ltb_spec n (2 ^ 26)) as [Hlt|Hge].
  - replace (Z.shiftr n 26 =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
    cbv iota. apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - replace (Z.shiftr n 26 =? 0) with false.
    2: { symmetry; apply Z.eqb_neq. rewrite Z.shiftr_div_pow2 by lia. intros E.
         pose proof (Z.div_le_mono (2 ^ 26) n (2 ^ 26) ltac:(lia) Hge) as D. rewrite Z.div_same in D by lia. lia. }
    cbv iota. step. apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Definition R2_RET : Z := 0x13348.
Definition MALLOC_AT : Z := 0x17330.
Definition setup_of (pl : list byte) : Z := rdb pl 6.
Definition pre_take (n : Z) : Z := Z.min n 7.

Ltac gen_read1 M d pl HB k kz :=
  try (let H := fresh "RD" in pose proof (read1 M d pl k HB ltac:(cbn; lia)) as H;
       change (d + Z.of_nat k) with (d + kz) in H; rewrite ?Z.add_0_r in H; cbn [nth] in H).

Ltac gen_reads d :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    lazymatch goal with HB : bytes_at rsegs M d ?pl |- _ =>
      gen_read1 M d pl HB 0%nat 0; gen_read1 M d pl HB 1%nat 1; gen_read1 M d pl HB 2%nat 2;
      gen_read1 M d pl HB 3%nat 3; gen_read1 M d pl HB 4%nat 4; gen_read1 M d pl HB 5%nat 5;
      gen_read1 M d pl HB 6%nat 6
    end
  end.

Ltac gen_reads_if d :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    match goal with
    | H : ov_read_bytes rsegs M _ 1 = _ |- _ => idtac
    | _ => gen_reads d
    end
  end.

Ltac brn := first [ if_true | if_false | (rewrite ?eqb_lit by lia; first [ if_true | if_false ]) ].
Ltac fix_zero_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) =>
      change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) =>
      rewrite (le1_zxb b); mem_after_store
  end.

Ltac run_to p d :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
          | _ => try fix_zero_store; try gen_reads_if d; first [ step | brn ]
          end).

Lemma rwc_to_CB : forall m A cs n bs, rw_cells rsegs m A cs -> cells_size cs = n -> cells_bytes cs = bs ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A cs n bs H Hn Hb. pose proof (rw_cells_merge rsegs m A [] cs []) as M.
  rewrite app_nil_r in M. cbn [app] in M. subst n bs. apply M. exact H.
Qed.

Ltac r1_fin :=
  unfold setup_of, pre_take, rdb; cbn [nth];
  rewrite ?Z.add_0_r;
  apply evt_done; do 9 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eapply rwc_to_CB; [eassumption | reflexivity | reflexivity] | eassumption].

Lemma slot_R1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X d n : Z) (pl jour : list byte),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 <= n < 2 ^ 26 -> Z.of_nat (length pl) = n -> 0 <= d -> d + n < 2 ^ 64 ->
  d + n <= X \/ X + 2592 <= d ->
  bytes_at rsegs m d pl -> rw_cells rsegs m (X + 914) [CB 6 jour] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 R2_RET) sp gp tp t0' t1 t2 (Z_to_bv 64 (setup_of pl)) s1 (Z_to_bv 64 HUNT_SIZE)
                     a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (n - pre_take n)) s4 (Z_to_bv 64 (d + pre_take n))
                     s6 s7 (Z_to_bv 64 (X + 2336)) s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 MALLOC_AT) fc None m' (seg_rom rsegs) /\
       munch [(X + 914, X + 920)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 914) [CB 6 (our_of pl)] /\ bytes_at rsegs m' d pl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R1) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X d n pl jour Esp Ea0 Ea1 HX0 HX1 Hn HL Hd0 Hd1 Hdj HB OUR MI.
  subst sp a0 a1. unfold R1, R2_RET, MALLOC_AT, HUNT_SIZE.
  pose proof (munch_refl [(X + 914, X + 920)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct pl as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 rest]]]]]]].
  - cbn [length Z.of_nat] in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 1) with 1 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 2) with 2 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 3) with 3 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 4) with 4 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 5) with 5 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. change (Z.of_nat 6) with 6 in HL. subst n. run_to 95024 d. r1_fin.
  - cbn [length] in HL. assert (H7 : 7 <= n) by lia.
    run_to 95024 d.
    replace (pre_take n) with 7 by (unfold pre_take; lia). replace (n - 7) with (n + -7) by lia.
    r1_fin.
Qed.
