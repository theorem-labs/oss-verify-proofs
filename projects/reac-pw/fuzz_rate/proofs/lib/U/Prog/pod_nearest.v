(** pod_nearest of fuzz_rate's UBSan build (0x14b84): proof of [pod_nearest_contract] (U/Prog/pod_nearest_c.v)
    from the contracts of its soft-float callees and the binary128 value facts [near_sf_facts].

    The code is the plain build's with five sanitizer checks, each a branch to `unimp` at 0x14cd4. The walk is the
    plain walk's (Prog/pod_nearest.v, whose value half, callee bridges and register lemmas it reuses), plus one
    step per check: Prog/pod_nearest.v's [pn_traps] shows the float-cast checks (f < 2^63, d > -2^63 - 1) pass and
    bounds t, so t + 1 and t - 1 do not overflow; the alignment check holds because out is 8-aligned. *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import pod_nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require IImgU.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import pod_nearest_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib.Step.exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(** ** The overflow checks on t + 1 and t - 1 (`addi a0,s1,+-1`, `blt a0,s1`) *)
Lemma lts_inc : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + 1)) (Z_to_bv 64 t) = false.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_ge.
  destruct (Z.ltb_spec ((t + 1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

Lemma lts_dec : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + -1)) (Z_to_bv 64 t) = true.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_lt.
  destruct (Z.ltb_spec ((t + -1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m0 : word -> option byte)
  (b Sp out lo : Z).
Hypothesis NS : near_sf_facts.
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract IImgU.N_img.
Hypothesis HLE : @G_letf2.letf2_contract IImgU.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract IImgU.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract IImgU.N_img.
Hypothesis HGE : @G_getf2.getf2_contract IImgU.N_img.
Hypothesis Hb : 0 <= b < 2^32.
Hypothesis HF10 : Sem.reg_get F (Z_to_bv 5 10) = nan_box (Z_to_bv 32 b).
Hypothesis Hout : 0 <= out /\ out + 8 <= 2^64.
Hypothesis Hal : out mod 8 = 0.
Hypothesis Hdj : hold (out + 8 <= Sp - 96 \/ Sp <= out).
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 96 <= Sp.
Hypothesis HSp : Sp <= 2^64.
Hypothesis TM0 : MemNorm.task_mem rsegs m0.
Hypothesis WR0 : forall a : word, Sp - 96 <= bv_unsigned a < Sp \/ out <= bv_unsigned a < out + 8 ->
  wview rsegs m0 a <> None.

(** The contract's post, with the machine model [pn_bin] in place of [nearest]. *)
Definition Post : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (pod_near_rc (pn_bin b)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
    frm0 fc' /\
    pod_near_mem m0 m' Sp out (pn_bin b) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo Sp.

(** The frame between the prologue and the epilogue, as in the plain walk. *)
Definition frm4 (fv : word) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -48) [C8 fv; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -48) /\ wmono rsegs m0 m /\ mem_inv rsegs m.
Definition frm (fv : word) (m : word -> option byte) : Prop := frm4 fv m /\ munch [(Sp - 96, Sp)] m0 m.

Lemma frm_mi : forall fv m, frm fv m -> mem_inv rsegs m.
Proof. intros fv m [(_ & _ & _ & MI) _]. exact MI. Qed.

Lemma tm_of : forall m, munch [(Sp - 96, Sp); (out, out + 8)] m0 m -> MemNorm.task_mem rsegs m.
Proof.
  intros m MU. apply (tm_munch rsegs _ m0 m TM0 MU). intros a Ha. apply WR0.
  cbn [outside] in Ha. lia.
Qed.

Lemma tm_frm : forall fv m, frm fv m -> MemNorm.task_mem rsegs m.
Proof.
  intros fv m [_ MU]. apply tm_of. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

Lemma frm_stk : forall fv m, frm fv m -> stk rsegs m (Sp + -48 - 48) (Sp + -48).
Proof.
  intros fv m [(_ & ST & _ & _) _].
  exact (proj2 (stk_split rsegs m lo (Sp + -48 - 48) (Sp + -48) ST ltac:(lia))).
Qed.

Lemma frm_call : forall fv m m', frm fv m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I].
  - split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I.
Qed.

Lemma frm_sub : forall fv m m', frm fv m -> munch [(Sp + -48 - 48, Sp + -48)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (Sp + -48 - 48) (Sp + -48) -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI' ST'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
  - split.
    + destruct (stk_split rsegs m lo (Sp + -48 - 48) (Sp + -48) ST ltac:(lia)) as [STa _].
      pose proof (stk_transport_disjoint rsegs _ m m' lo (Sp + -48 - 48) STa MU' WM'
                    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STb.
      exact (stk_merge rsegs m' lo (Sp + -48 - 48) (Sp + -48) STb ST' ltac:(lia)).
    + split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']].
    intros x [Hx _]. split; [lia | exact I].
Qed.

Lemma store_out : forall fv m (v : word), frm fv m ->
  frm4 fv (write_to_mem m (wa out) (le8 v)) /\
  munch [(Sp - 96, Sp); (out, out + 8)] m0 (write_to_mem m (wa out) (le8 v)) /\
  bytes_at rsegs (write_to_mem m (wa out) (le8 v)) out (le8 v) /\
  store_ok rsegs m (wa out) 8 = true.
Proof.
  intros fv m v [(FR & ST & WM & MI) MU].
  pose proof Hdj as D. unfold hold in D.
  assert (WR : wr_at rsegs m out 8).
  { split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply WR0. right.
    unfold wa. rewrite unsigned_lit by lia. lia. }
  assert (HSt : store_ok rsegs m (wa out) 8 = true).
  { pose proof (wr_at_store_ok rsegs m out 8 0 8 WR ltac:(lia) ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (HSt' : store_ok rsegs m (wa out) (length (le8 v)) = true) by (rewrite length_le8; exact HSt).
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + apply (rw_cells_frame rsegs m _ _ out (le8 v) FR); rewrite ?length_le8; cbn [cells_size csize]; lia.
    + apply (stk_write rsegs m lo (Sp + -48) out (le8 v) ST); rewrite ?length_le8; lia.
    + exact (wmono_write rsegs m0 m (wa out) (le8 v) WM).
    + exact (mem_inv_store rsegs m (wa out) (le8 v) MI HSt').
  - apply munch_write; rewrite ?length_le8; [| lia | lia | cbn [inside]; right; left; lia].
    eapply munch_weaken; [|exact MU]. intros x [H1 [H2 _]]. split; [exact H1 | exact I].
  - apply bytes_at_write_same; rewrite ?length_le8; lia.
  - exact HSt.
Qed.

(** The shared exit 0x14cb0: a0 = s1, restore ra, s0-s3 and fs0, free the frame, return. *)
Lemma epi : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m rc
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm4 fv m -> pod_near_mem m0 m Sp out (pn_bin b) -> rc = pod_near_rc (pn_bin b) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 x8 (Z_to_bv 64 rc) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 0x14cb0) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m rc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Efv HFc FRM
    [FR [ST [WM MI]]] PM Erc.
  assert (TM : MemNorm.task_mem rsegs m).
  { apply tm_of. destruct (pn_bin b); cbn [pod_near_mem] in PM.
    - exact (proj1 PM).
    - eapply munch_weaken; [|exact PM]. intros x Hx. cbn [outside] in *. tauto. }
  do 9 step.
  match goal with |- evt _ _ (MS _ ?F' _ ?fc' _ ?m' _) =>
    apply evt_done; unfold Post;
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m' end.
  split; [subst rc; unfold mkR; repeat f_equal; lia|].
  split.
  { intros k Hk. destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|E8].
    - rewrite (freg_get_same Fc _ k fv) by (rewrite E8; reflexivity). rewrite Efv.
      apply reg_get_key. rewrite E8. reflexivity.
    - rewrite reg_get_set_ne by (intro E; apply E8; rewrite <- E; reflexivity). exact (HFc k Hk E8). }
  split; [exact FRM|]. split; [exact PM|]. split; [exact WM|]. split; [exact MI|]. split; [exact TM|].
  pose proof (stk_release rsegs m lo (Sp + -48) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -48 + Z.of_nat 48) with Sp in R by lia. exact R.
Qed.

(** 0x14c90: s1 = r; `sext.w a0,s1`, `beq a0,s1`; then check 5 (`andi a0,s0,7`, `bnez` -> trap, not taken: out
    is 8-aligned), store r at out and return 1; else return 0. *)
Lemma tail : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m (r : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm fv m ->
  pn_bin b = (if (-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31) then Some (bv_swrap 64 r) else None) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16
             x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 0x14c90) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Efv HFc FRM FM Hpn.
  step. step.
  rewrite fits32.
  destruct ((-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31)) eqn:FIT.
  - destruct (store_out fv m (Z_to_bv 64 r) FM) as (F4 & MU2 & BY & HSt).
    cbv iota. step. step.
    rewrite (unsigned_lit out) by lia.
    replace (Z.land out 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; symmetry; exact Hal).
    if_false. step. step.
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | |].
    + rewrite Hpn. cbn [pod_near_mem]. split; [exact MU2|]. rewrite bvsw_lit. exact BY.
    + rewrite Hpn. reflexivity.
  - cbv iota. step. step.
    destruct FM as [F4 MU].
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | rewrite Hpn; exact MU | rewrite Hpn; reflexivity].
Qed.

Lemma body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 -> frm0 fc ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 POD_NEAREST) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc ST MI FRM.
  pose proof (munch_refl [(Sp - 96, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 48 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 48) with 48 in ST1, FR.
  replace (Sp - 48) with (Sp + -48) in ST1, FR by lia.
  unfold POD_NEAREST.
  (* prologue: the frame, ra, s0-s3 and fs0 *)
  do 7 step.
  match type of FR with rw_cells _ ?m1 _ (C8 ?v :: _) =>
    assert (FM : frm v m1) by exact (conj (conj FR (conj ST1 (conj WM MI))) MU);
    assert (Efv : v = Sem.reg_get F (Z_to_bv 5 8)) by (apply reg_get_key; reflexivity) end.
  clear FR ST1 WM MU MI.
  (* 0x14ba0 feq.s a1,fa0,fa0; beqz a1 *)
  step. fix_reg F HF10 10%Z. unfold feq_s. rewrite unbox_nan_box, (u32_lit b Hb).
  destruct (fst (fp_eq fmt_single b b)) eqn:FE; unfold bword; step.
  2:{ (* a NaN: s1 = 0, return 0 *)
      if_true. step. step.
      eapply epi; [exact Efv | intros k _ _; reflexivity | eassumption | exact (proj1 FM) | |].
      - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE; reflexivity). rewrite E. exact (proj2 FM).
      - unfold pn_bin; rewrite FE; reflexivity. }
  if_false.
  (* 0x14ba8 fmv.s fs0,fa0; mv s0,a0; jal __extendsftf2 *)
  step. fix_reg F HF10 10%Z. rewrite unbox_nan_box, sgnj_self32.
  step. step.
  eapply evt_cut.
  { eapply (br_ext IImgU.N_img rsegs 0x15438 eq_refl eq_refl HEX b);
      [ rewrite freg_get_other by reflexivity; exact HF10 | exact (frm_mi _ _ FM) | exact (tm_frm _ _ FM) ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU2 & WM2 & MI2 & _).
  pose proof (frm_call _ _ _ FM MU2 WM2 MI2) as FM2. clear FM MU2 WM2 MI2.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x14bb4 mv s2,a0; lui a0,0x4f000; fmv.w.x fa5,a0; flt.s a0,fa5,fs0 *)
  step. step. step. step.
  unfold flt_s. rewrite !unbox_nan_box, (u32_lit b Hb). fold_unbox.
  destruct (fst (fp_lt fmt_single 1325400064 b)) eqn:LT; unfold bword.
  { (* 2^31 < f: s1 = 0, return 0 *)
    step. step. if_true.
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM2) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT; reflexivity). rewrite E. exact (proj2 FM2).
    - unfold pn_bin; rewrite FE, LT; reflexivity. }
  step. step. if_false.
  (* 0x14bcc mv s3,a1; a3 = high word of C1; mv a0,s2; mv a2,zero; jal __lttf2 *)
  do 8 step.
  eapply evt_cut.
  { eapply (br_le IImgU.N_img rsegs 0x152b4 eq_refl eq_refl HLE); [exact (frm_mi _ _ FM2) | exact (tm_frm _ _ FM2)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU3 & WM3 & MI3 & _).
  pose proof (frm_call _ _ _ FM2 MU3 WM3 MI3) as FM3. clear FM2 MU3 WM3 MI3.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 C1_128.
  (* 0x14bec bltz a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (pn_d b) C1_128 <? 0) eqn:LE; cbv iota.
  { (* d < C1: s1 = 0, return 0 *)
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM3) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT, LE; reflexivity). rewrite E. exact (proj2 FM3).
    - unfold pn_bin; rewrite FE, LT, LE; reflexivity. }
  destruct (pn_traps NS b Hb FE LT LE) as (T1 & T2 & T3).
  (* 0x14bf0 check 1: fa5 = 2^63, flt.s a0,fs0,fa5, beqz -> trap *)
  step. step. step.
  unfold flt_s. rewrite !unbox_nan_box, (u32_lit b Hb). fold_unbox. rewrite T1. unfold bword.
  step. if_false.
  (* 0x14c00 check 2: a2:a3 = C2 = -2^63 - 1, a0:a1 = d; jal __gttf2; blez -> trap *)
  do 7 step.
  eapply evt_cut.
  { eapply (br_ge IImgU.N_img rsegs 0x1537c eq_refl eq_refl HGE); [exact (frm_mi _ _ FM3) | exact (tm_frm _ _ FM3)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & _).
  pose proof (frm_call _ _ _ FM3 MU4 WM4 MI4) as FM4. clear FM3 MU4 WM4 MI4.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 C2_128. rewrite T2.
  step. if_false.
  (* 0x14c20 fcvt.l.s s1,fs0,rtz *)
  step. rewrite unbox_nan_box, (u32_lit b Hb), pn_t_def.
  (* 0x14c24 mv a0,s1; jal __floatditf *)
  step. step.
  eapply evt_cut.
  { eapply (br_fd IImgU.N_img rsegs 0x15594 eq_refl eq_refl HFD (pn_t b));
      [ rewrite unsigned_lit_wrap, SF.wrap64_mod; reflexivity | exact (frm_mi _ _ FM4) | exact (tm_frm _ _ FM4) ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU5 & WM5 & MI5 & _).
  pose proof (frm_call _ _ _ FM4 MU5 WM5 MI5) as FM5. clear FM4 MU5 WM5 MI5.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x14c2c a2:a3 = (long double)t, a0:a1 = d; jal __subtf3 *)
  do 5 step.
  eapply evt_cut.
  { eapply (br_sub IImgU.N_img rsegs 0x156b8 eq_refl eq_refl HSB);
      [ lia | exact (frm_stk _ _ FM5) | exact (frm_mi _ _ FM5) | exact (tm_frm _ _ FM5) | eassumption ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fc6 & m6 & -> & MU6 & WM6 & MI6 & _ & FRM6 & ST6).
  pose proof (frm_sub _ _ _ FM5 MU6 WM6 MI6 ST6) as FM6. clear FM5 MU6 WM6 MI6 ST6.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def.
  (* 0x14c40 s2:s3 = frac; a2:a3 = 0.5L; jal __getf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_ge IImgU.N_img rsegs 0x1537c eq_refl eq_refl HGE); [exact (frm_mi _ _ FM6) | exact (tm_frm _ _ FM6)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & _).
  pose proof (frm_call _ _ _ FM6 MU7 WM7 MI7) as FM7. clear FM6 MU7 WM7 MI7.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 HALF_128.
  (* 0x14c58 bgez a0 *)
  step. rewrite lts0 by apply f128_ge_range. rewrite Z.ltb_antisym, Bool.negb_involutive.
  destruct (0 <=? SF.f128_ge (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) HALF_128) eqn:GE;
    cbv iota.
  { (* 0x14c84 check 3: addi a0,s1,1; blt a0,s1 -> trap (t + 1 does not overflow); mv s1,a0 *)
    step. step. rewrite (lts_inc (pn_t b) T3). cbv iota. step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM7 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE. reflexivity. }
  (* 0x14c5c a0:a1 = frac, a2:a3 = -0.5L; jal __lttf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_le IImgU.N_img rsegs 0x152b4 eq_refl eq_refl HLE); [exact (frm_mi _ _ FM7) | exact (tm_frm _ _ FM7)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & -> & MU8 & WM8 & MI8 & _).
  pose proof (frm_call _ _ _ FM7 MU8 WM8 MI8) as FM8. clear FM7 MU8 WM8 MI8.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 MHALF_128.
  (* 0x14c74 bgez a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) MHALF_128 <? 0) eqn:LM;
    cbn [negb]; cbv iota.
  - (* 0x14c78 check 4: addi a0,s1,-1; blt a0,s1 -> 0x14c8c (t - 1 does not overflow); mv s1,a0 *)
    step. step. rewrite (lts_dec (pn_t b) T3). cbv iota. step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM8 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM.
    replace (pn_t b - 1) with (pn_t b + -1) by lia. reflexivity.
  - (* r = t *)
    eapply tail; [exact Efv | hfc | eassumption | exact FM8 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM. reflexivity.
Qed.

End Walk.

(** The contract of the UBSan build's pod_nearest, from its five soft-float callees' contracts and the binary128
    value facts [near_sf_facts]; no sanitizer trap is reached. *)
Theorem pod_nearest_holds :
  near_sf_facts ->
  @C_extendsftf2.extendsftf2_contract IImgU.N_img -> @G_letf2.letf2_contract IImgU.N_img ->
  @C_floatditf.floatditf_contract IImgU.N_img -> @G_subtf3.subtf3_contract IImgU.N_img ->
  @G_getf2.getf2_contract IImgU.N_img ->
  pod_nearest_contract.
Proof.
  intros NS HEX HLE HFD HSB HGE. unfold pod_nearest_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b
    Hb HF WR Hal Hdj ST HK HW FRM MI TM.
  replace (nearest b NEAR_LO NEAR_HI) with (pn_bin b) by (rewrite (pn_bin_nearest NS b Hb); reflexivity).
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (out := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp out. clear Esp Ea0.
  unfold POD_NEAREST_STACK in *.
  pose proof ST as (Hlo & HSp & STw).
  assert (Hout : 0 <= out /\ out + 8 <= 2^64) by (destruct WR as (W1 & W2 & _); split; assumption).
  assert (Hdj' : hold (out + 8 <= Sp - 96 \/ Sp <= out)) by exact Hdj.
  assert (WR0 : forall x : word, Sp - 96 <= bv_unsigned x < Sp \/ out <= bv_unsigned x < out + 8 ->
                  wview rsegs m x <> None).
  { intros x [Hx|Hx].
    - rewrite <- (Z_to_bv_lit_self x). exact (proj1 (STw (bv_unsigned x) ltac:(lia))).
    - destruct WR as (_ & _ & W3). specialize (W3 (bv_unsigned x - out) ltac:(lia)).
      replace (out + (bv_unsigned x - out)) with (bv_unsigned x) in W3 by lia.
      unfold wa in W3. rewrite Z_to_bv_lit_self in W3. exact W3. }
  eapply evt_mono.
  { eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m b Sp out lo); eassumption. }
  intros ms' H. exact H.
Qed.
