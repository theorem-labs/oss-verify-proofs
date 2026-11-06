(* Segment A02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13310, 0x1333c], the 6-turn loop
   that reads our[t] (fuzz_u8: in[t] when left > 0, else 0 by the beqz a1 arm 0x1332c), U13310 (turn t) -> U13310
   (turn t + 1) or U13340 (after turn 5). The UBSan check T01 (cursor + 1 wraps) is not taken by PB. Measure: 5 - t. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

(* A branch whose condition is decided by the context (unsigned compares of in-range values). *)
Ltac a02_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first
        [ replace c with true;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond]
        | replace c with false;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond] ]
  end.

(* The end of a turn: the byte v stored at d, nothing else written. *)
Ltac a02_post v :=
  lazymatch goal with
  | |- munch _ ?m (write_to_mem ?m _ ?BS) /\ _ =>
      let EBS := fresh "EBS" in
      assert (EBS : BS = [v]) by (first [apply le1_zxb | apply u1_bytes_eq; vm_compute; reflexivity]);
      rewrite EBS;
      split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|];
      split; [apply wmono_write, wmono_refl|];
      apply bytes_at_write_same; cbn [length]; lia
  end.

Lemma a02_our_step : forall inp t, (t < 6)%nat ->
  firstn (S t) (OUR inp) = firstn t (OUR inp) ++ [RcIdentModel.nthb inp t].
Proof.
  intros inp t Ht. unfold OUR. cbn [seq map].
  do 6 (destruct t as [|t]; [reflexivity|]). lia.
Qed.

Lemma a02_nth_past : forall inp t, (length inp <= t)%nat -> RcIdentModel.nthb inp t = Z_to_bv 8 0.
Proof. intros inp t H. unfold RcIdentModel.nthb, RcIdentModel.zb. apply nth_overflow. exact H. Qed.

(* left > 0: T01 not taken, a5 = in[t], cursor and left advance; store at d, then the latch. *)
Lemma a02_ld_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q l d k : Z) (b : byte),
    a0 = Z_to_bv 64 q -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 k -> a4 = Z_to_bv 64 1 ->
    1 <= l -> 1 <= q -> q + l < 2 ^ 64 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= k <= 6 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] -> store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 1)) (Z_to_bv 64 (l + -1)) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (k + -1)) (Z_to_bv 64 1) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if k =? 1 then 0x13340 else 0x13310)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13310) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q l d k b -> -> -> -> -> Hl Hq Hql Hd0 Hd Hk HR HS.
  step. a02_br.
  step. step. a02_br.
  step. step. step. step.
  step.
  step. step. step.
  destruct (Z.eq_dec k 1) as [Hk1|Hk2].
  - try change (1 + -1) with 0. a02_br.
    rewrite (proj2 (Z.eqb_eq k 1) Hk1).
    apply evt_done. do 3 eexists. split; [reflexivity|]. a02_post b.
  - a02_br.
    rewrite (proj2 (Z.eqb_neq k 1) Hk2).
    apply evt_done. do 3 eexists. split; [reflexivity|]. a02_post b.
Qed.

(* left = 0: a5 = 0 (0x1332c); store at d, then the latch. *)
Lemma a02_z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d k : Z),
    a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 k ->
    0 <= d -> d + 1 < 2 ^ 64 -> 1 <= k <= 6 -> store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (k + -1)) a4 a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if k =? 1 then 0x13340 else 0x13310)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13310) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d k -> -> -> Hd0 Hd Hk HS.
  step. a02_br.
  step.
  step.
  step. step. step.
  destruct (Z.eq_dec k 1) as [Hk1|Hk2].
  - try change (1 + -1) with 0. a02_br.
    rewrite (proj2 (Z.eqb_eq k 1) Hk1).
    apply evt_done. do 2 eexists. split; [reflexivity|]. a02_post (Z_to_bv 8 0).
  - a02_br.
    rewrite (proj2 (Z.eqb_neq k 1) Hk2).
    apply evt_done. do 2 eexists. split; [reflexivity|]. a02_post (Z_to_bv 8 0).
Qed.

Section A02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* One turn t at a cut state: either the next turn's state at 0x13310 (t < 5) or U13340 (t = 5). *)
Lemma a02_turn : forall t,
  (t < 5 -> Hat B APIf ra (Inv_U13310_at B APIf ra empty) (t + 1)) ->
  (t = 5 -> Hcut B APIf ra (Inv_U13340 B APIf ra empty)) ->
  Hat B APIf ra (Inv_U13310_at B APIf ra empty) t.
Proof.
  intros t Hnext Hlast g c (L & A & regs & mem & md & -> & HFR & HP & (Ht & H10 & H11 & H12 & H13 & H14 & HB)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _).
  pose proof HGV as ((Hn0 & Hn26) & _).
  pose proof alloc_ceiling_value as Hac.
  assert (Hlen : g_n g = Z.of_nat (length (g_in g))) by reflexivity.
  set (d := spk g 114 + t) in *.
  assert (Hd : d = g_S g - 1936 + 114 + t) by (unfold d, spk, fsp, SLOT_FRAME; lia).
  unfold SLOT_K, SLOT_STACK, SL_TOP in HSK.
  destruct (sl_rw_of_stk _ _ _ d 1 ST ltac:(unfold SLOT_K, SLOT_STACK; lia) ltac:(lia)) as (junk & HC).
  pose proof (rw_cells_store_ok rsegs _ d [Cells.CB 1 junk] 0 (Cells.CB 1 junk) 1 HC eq_refl eq_refl) as HS.
  change (Z.of_nat 0) with 0 in HS. rewrite Z.add_0_r in HS.
  assert (Hlen5 : length (firstn (Z.to_nat t) (OUR (g_in g))) = Z.to_nat t)
    by (rewrite length_firstn, OUR_length; lia).
  (* the bytes of turn t + 1 from those of turn t and the byte v stored at d *)
  assert (Hcat : forall m0 m' v, Frame.munch [(d, d + 1)] (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
     bytes_at rsegs m0 d [v] -> v = RcIdentModel.nthb (g_in g) (Z.to_nat t) ->
     bytes_at rsegs m' (spk g 114) (firstn (Z.to_nat (t + 1)) (OUR (g_in g)))).
  { intros m0 m' v MU Hrel Hv Ev.
    replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
    rewrite (a02_our_step (g_in g) (Z.to_nat t)) by lia. subst v.
    apply bytes_at_app. split.
    - apply (u1_keep _ mem m0 m' _ _ HMI MU Hrel); [|exact HB].
      rewrite Hlen5. cbn [disjoint_from]. split; [|exact I]. left. unfold d. lia.
    - rewrite Hlen5. rewrite Z2Nat.id by lia. exact (u1_out _ _ _ _ Hrel Hv). }
  destruct (Z_lt_ge_dec t (g_n g)) as [Hlt|Hge].
  - (* left > 0: in[t] *)
    replace (Z.min t (g_n g)) with t in H10, H11 by lia.
    destruct (u1_pb B empty g (g_n g - 1) HGV ltac:(lia)) as (Hp0 & Hpn & Hac47).
    pose proof (u1_in_rd B APIf ra empty FF g [] L A regs mem md t HFR HP ltac:(lia)) as HR.
    set (bt := RcIdentModel.nthb (g_in g) (Z.to_nat t)) in *.
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply a02_ld_evt with (q := g_p g + t) (l := g_n g - t) (d := d) (k := 6 - t) (b := bt);
        [exact H10 | exact H11 | exact H12 | exact H13 | exact H14 | lia | lia | lia | lia | lia | lia
        | exact HR | exact HS].
    + intros ms (a5' & a6' & m' & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists [(d, d + 1)]. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. apply (sl_fp1 g d (d + 1) z); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O].
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a5' & a6' & m'' & HE & MU & _ & Hv).
      injection HE; intros; subst.
      pose proof (Hcat m'' m' bt MU Hrel Hv eq_refl) as HB'.
      destruct (Z.eq_dec t 5) as [E5|N5].
      * (* t = 5: U13340 *)
        rewrite (proj2 (Z.eqb_eq (6 - t) 1) ltac:(lia)).
        apply (Hlast E5). exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold OURb, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [rewrite firstn_all2 in HB' by (rewrite OUR_length; lia); exact HB'|].
        split.
        { transitivity (Z_to_bv 64 (g_p g + t + 1)); [reflexivity | f_equal; lia]. }
        { transitivity (Z_to_bv 64 (g_n g - t + -1)); [reflexivity | f_equal; lia]. }
      * (* t < 5: turn t + 1 *)
        rewrite (proj2 (Z.eqb_neq (6 - t) 1) ltac:(lia)).
        apply (Hnext ltac:(lia)). exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [lia|].
        split; [transitivity (Z_to_bv 64 (g_p g + t + 1)); [reflexivity | f_equal; lia]|].
        split; [transitivity (Z_to_bv 64 (g_n g - t + -1)); [reflexivity | f_equal; lia]|].
        split; [transitivity (Z_to_bv 64 (d + 1)); [reflexivity | f_equal; unfold d; lia]|].
        split; [transitivity (Z_to_bv 64 (6 - t + -1)); [reflexivity | f_equal; lia]|].
        split; [reflexivity|].
        exact HB'.
  - (* left = 0: the zero byte *)
    replace (Z.min t (g_n g)) with (g_n g) in H10, H11 by lia.
    replace (g_n g - g_n g) with 0 in H11 by lia.
    assert (Ez : RcIdentModel.nthb (g_in g) (Z.to_nat t) = Z_to_bv 8 0) by (apply a02_nth_past; lia).
    eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply a02_z_evt with (d := d) (k := 6 - t); [exact H11 | exact H12 | exact H13 | lia | lia | lia | exact HS].
    + intros ms (a5' & m' & -> & MU & WM & _). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists [(d, d + 1)]. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. apply (sl_fp1 g d (d + 1) z); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hz | exact O].
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a5' & m'' & HE & MU & _ & Hv).
      injection HE; intros; subst.
      pose proof (Hcat m'' m' (Z_to_bv 8 0) MU Hrel Hv (eq_sym Ez)) as HB'.
      destruct (Z.eq_dec t 5) as [E5|N5].
      * (* t = 5: U13340 *)
        rewrite (proj2 (Z.eqb_eq (6 - t) 1) ltac:(lia)).
        apply (Hlast E5). exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold OURb, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [rewrite firstn_all2 in HB' by (rewrite OUR_length; lia); exact HB'|].
        replace (Z.min 6 (g_n g)) with (g_n g) by lia.
        split; [exact H10|]. replace (g_n g - g_n g) with 0 by lia. reflexivity.
      * (* t < 5: turn t + 1 *)
        rewrite (proj2 (Z.eqb_neq (6 - t) 1) ltac:(lia)).
        apply (Hnext ltac:(lia)). exists L, A, regs', m', md.
        split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
        unfold rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
        replace (Z.min (t + 1) (g_n g)) with (g_n g) by lia.
        split; [lia|].
        split; [exact H10|].
        split; [replace (g_n g - g_n g) with 0 by lia; reflexivity|].
        split; [transitivity (Z_to_bv 64 (d + 1)); [reflexivity | f_equal; unfold d; lia]|].
        split; [transitivity (Z_to_bv 64 (6 - t + -1)); [reflexivity | f_equal; lia]|].
        split; [exact H14|].
        exact HB'.
Qed.

Lemma seg_A02 : forall t : Z, Hcut B APIf ra (Inv_U13340 B APIf ra empty) ->
  Hat B APIf ra (Inv_U13310_at B APIf ra empty) t.
Proof.
  intros t HX.
  assert (MAIN : forall k : nat, forall t, Z.to_nat (5 - t) = k -> Hat B APIf ra (Inv_U13310_at B APIf ra empty) t).
  { induction k as [k IH] using lt_wf_ind.
    intros t' Ek. apply a02_turn.
    - intros Hlt. apply (IH (Z.to_nat (5 - (t' + 1)))); [lia | reflexivity].
    - intros _. exact HX. }
  exact (MAIN (Z.to_nat (5 - t)) t eq_refl).
Qed.

End A02.
