(* Arms 4 and 5 of the slot's loop, piece `com` (link/sl/briefs/C45-PIECES.md): the dispatch from the loop
   head to op_decide / op_refused, and the tail from either arm's end to the next loop head or the exit.

   Dispatch (0x13a1c - 0x13a64, LLVMFuzzerTestOneInput.s lines 118-136):
     ld a2, 0x40(sp); lbu a3, 0(a2)        the cursor P and the op byte b at P
     a1 = s2 - 1; a0 = a2 + 1               N - 1, P + 1
     mul/srli/slli/slli/subw/add/andi       a3 = b mod 6 (s8 = 0xab), checked for every b < 256
     sd a0, 0x40(sp); sd a1, 0x48(sp)       the cursor cells := (P + 1, N - 1)
     bltu s9, a3                            s9 = 4: op 5 goes to L_OP5 = 0x13bf4
     slli/add/lw/add/jr                     op 4: the jump table's int32 at 0x106c0 (.rodata) + 0x106b0 = L_OP4
   Tail (0x13af4 or 0x13dd8, lines 172-173 / 357-358, then 522-525):
     bltu s5, s11, 0x1413c                  s5 = 46, s11 = i: i = 47 leaves to the exit
     j 0x1406c; ld s2, 0x48(sp); addiw s11, s11, 1; bnez s2, 0x13a1c; j 0x1413c *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45ComLib.
Local Open Scope Z_scope.

(* a function of a byte, checked at all 256 values *)
Lemma c45c_zfun_check : forall (g h : Z -> Z),
  forallb (fun x => Z.eqb (g x) (h x)) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> g x = h x.
Proof.
  intros g h H x Hx. rewrite forallb_forall in H. apply Z.eqb_eq. apply (H x).
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma c45_dispatch : forall (E : lenv) (i : Z) (gp : word) (op : Z) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms op -> (op = 4 \/ op = 5) ->
  evt rsegs (c45_post E (ms_mem ms) (c45_disp E i gp op)) ms.
Proof.
  intros E i gp op ms HE HL HO Hop.
  destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & HI & HN & LM & MI & TM & ST).
  assert (Em : ms_mem ms = m) by (subst ms; reflexivity).
  unfold lh_op in HO. rewrite Em in HO |- *. subst ms.
  destruct HO as (P' & b & HP' & Hb & Hop').
  destruct LM as ((j0 & j1 & j2 & nc & FR) & SV & NK & NW & IT & O1 & O2 & O3 & O4 & G & O & PR & LA & TX
    & IP & MD & MW & MK & KW & KA & (PL & CURk) & ER & GD).
  assert (KMG : c45_kmg E i kbs mbs gbs m)
    by exact (conj NK (conj NW (conj IT (conj O1 (conj O2 (conj O3 (conj O4 (conj MD (conj MW (conj MK
               (conj KW KA))))))))))).
  assert (KEEP : c45_keep E m) by exact (conj G (conj O (conj PR (conj LA (conj TX (conj IP (conj ER (conj GD PL)))))))).
  assert (CUR : c45_cur E P N) by exact CURk.
  clear NK NW IT O1 O2 O3 O4 G O PR LA TX IP MD MW MK KW KA ER GD.
  (* the cell sp+0x40 holds P, so the op byte is at P *)
  assert (HPr : 4096 <= P /\ P + N <= e_S E - SLOT_STACK_Z).
  { destruct CURk as (k & Hk & -> & ->).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hp0 & Hp1 & _) & _). lia. }
  clear PL CURk.
  assert (EP : P' = P).
  { pose proof (c45c_frame_split E m P nc j0 j1 j2 FR) as (_ & FC2 & _ & _).
    pose proof (c45c_u64_same m _ P P' (c45c_cell8_bytes m _ _ _ FC2) HP') as EW.
    pose proof (bytes_at_bound _ _ _ _ Hb) as BB. cbn [length] in BB.
    destruct HE as (_ & HS2 & _). unfold SLOT_STACK_Z in HPr.
    apply (f_equal bv_unsigned) in EW. unfold wz in EW. rewrite !unsigned_lit in EW by lia. lia. }
  subst P'. clear HP'.
  assert (RB : ro_cells rsegs m P [C1 b]) by (split; [cbn; tauto | exact Hb]).
  clear Hb.
  pose proof (munch_refl [(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold lh_cells in FR.
  assert (HSF : SLOT_FRAME = 480) by reflexivity.
  unfold L_LH, A_JT, wz in *.
  do 13 zstep.
  (* a3 = b mod 6 *)
  assert (Rb : 0 <= bv_unsigned b < 256) by apply c45c_byte_range.
  lazymatch goal with |- context [Z_to_bv 64 (Z.land ?e 255)] =>
    assert (Ea : Z.land e 255 = bv_unsigned b mod 6);
    [ revert Rb; generalize (bv_unsigned b); intros x Rx; revert x Rx;
      apply c45c_zfun_check; vm_compute; reflexivity
    | rewrite Ea ]
  end.
  change (bz b) with (bv_unsigned b) in Hop'. rewrite Hop'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => rename mf into mE end.
  assert (TM1 : MemNorm.task_mem rsegs mE).
  { apply (c45c_tr_task _ m mE TM MU). intros x _ Hx. apply c45c_not_outside1 in Hx.
    destruct HE as (_ & HS2 & _). unfold SLOT_FRAME in Hx. lia. }
  assert (DL : disjoint_from [(e_S E - SLOT_FRAME + 64, e_S E - SLOT_FRAME + 80)] 0 (e_S E - SLOT_STACK_Z))
    by (apply c45c_disj1; unfold SLOT_FRAME, SLOT_STACK_Z; lia).
  pose proof (c45c_tr_kmg E i kbs mbs gbs _ m mE HE MU WM DL KEEP KMG) as KMG1.
  pose proof (c45c_tr_keep E _ m mE HE MU WM DL KEEP) as KEEP1.
  assert (FP : seg_fp (e_S E) (c45_hp E) m mE).
  { apply (c45c_seg_fp_stack _ _ _ m mE MU WM). intros x _ Hx. apply c45c_not_outside1 in Hx.
    unfold SLOT_FRAME, SLOT_STACK_Z in *. lia. }
  pose proof (c45c_frame_split E mE (P + 1) (N - 1) j0 j1 j2 FR) as (F1 & F2 & F3 & F4).
  clear KMG KEEP TM MU WM DL.
  destruct Hop as [-> | ->].
  - (* op_decide: through the jump table *)
    zstep. if_false.
    do 5 zstep.
    apply evt_done. split; [|cbn [ms_mem]; exact FP].
    unfold c45_disp. do 15 eexists. exists F, fc, mE, P, N, kbs, mbs, gbs, j0, j1, j2.
    split; [reflexivity|]. split; [exact FC|]. split; [exact HI|]. split; [exact HN|].
    split; [split; [exact F1 | split; [exact F2 | exact SV]]|].
    split; [exact CUR|]. split; [exact F3|]. split; [exact F4|]. split; [exact KMG1|]. split; [exact KEEP1|].
    split; [exact MI|]. split; [exact TM1 | exact ST].
  - (* op_refused *)
    zstep. if_true.
    apply evt_done. split; [|cbn [ms_mem]; exact FP].
    unfold c45_disp. do 15 eexists. exists F, fc, mE, P, N, kbs, mbs, gbs, j0, j1, j2.
    split; [reflexivity|]. split; [exact FC|]. split; [exact HI|]. split; [exact HN|].
    split; [split; [exact F1 | split; [exact F2 | exact SV]]|].
    split; [exact CUR|]. split; [exact F3|]. split; [exact F4|]. split; [exact KMG1|]. split; [exact KEEP1|].
    split; [exact MI|]. split; [exact TM1 | exact ST].
Qed.

Lemma c45_tail : forall (E : lenv) (i : Z) (gp : word) (pc : Z) (ms : machine_state),
  lenv_ok E -> (pc = C45_END_D \/ pc = C45_END_R) -> c45_end E i gp pc ms ->
  evt rsegs (c45_post E (ms_mem ms) (c45_fin E i gp)) ms.
Proof.
  intros E i gp pc ms HE Hpc HC.
  destruct HC as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & HI & FRM & CUR & B40 & B256
    & KMG & KEEP & MACH).
  assert (Em : ms_mem ms = m) by (subst ms; reflexivity).
  rewrite Em. subst ms.
  assert (HN0 : 0 <= N) by (destruct CUR as (k & Hk & _ & ->); lia).
  pose proof FRM as (_ & FN & _).
  unfold c45_sp, FO_P, wz in FN.
  unfold c45_R, c45_sp, wz.
  unfold C45_END_D, C45_END_R in Hpc.
  destruct (Z.eq_dec i 47) as [Hi47 | Hi47].
  - (* after operation 47: the exit *)
    subst i. destruct Hpc as [-> | ->]; zstep; if_true;
      apply evt_done; (split; [|apply c45_seg_fp_refl]); right; eapply c45c_ex_of; eassumption.
  - assert (Hi : i <= 46) by lia.
    assert (C46 : bv_ltu (Z_to_bv 64 46) (Z_to_bv 64 i) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. }
    assert (SW : bv_swrap 32 (i + 1) = i + 1)
      by (apply bv_swrap_small; change (bv_half_modulus 32%N) with 2147483648; lia).
    assert (CN : N <> 0 -> negb (bv_eqb (Z_to_bv 64 N) (Z_to_bv 64 0)) = true).
    { intros HN. assert (HNr : N < 2 ^ 26).
      { destruct CUR as (k & Hk & _ & ->). destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _). lia. }
      unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. exact HN. }
    destruct Hpc as [-> | ->]; zstep; rewrite C46; cbv iota; zstep; zstep; zstep; zstep; rewrite ?SW.
    all: destruct (Z.eq_dec N 0) as [-> | HN].
    1, 3: if_false; zstep; apply evt_done; (split; [|apply c45_seg_fp_refl]); right;
          eapply c45c_ex_of; eassumption.
    all: rewrite (CN HN); cbv iota; apply evt_done; (split; [|apply c45_seg_fp_refl]); left; split; [lia|];
         eapply c45c_lh_of; try eassumption; lia.
Qed.

Print Assumptions c45_dispatch.
Print Assumptions c45_tail.
