(* The SR glue of the slot's entry and exit (piece `ee`): the facts both chains use.
   - eqv_cl at a cut: the closure is idempotent at a CUT (ee_cut_collapse), a state is in its own closure,
     and a state after an allocator call is ms_eqv to its canonical mkR form (ee_canon: the callee-saved
     registers come back by regs_preserved, the rest are read from the returned map);
   - the program point of each cut predicate the chains end a segment at;
   - the carry of the entry's memory views across an allocator call (each view is local to a region inside
     LFr's lkeep: the frame above sp, the image outside the allocator's statics, the slot's blocks, the
     payload block) and the fresh block calloc hands out;
   - the end: le_fin at the caller's ra gives LGlue's fin_P, and the cut at 0x1414c gives LGlue's FIN. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom CallocSite.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrAl LFrLo LFrEn
  LGlue LEDefs LE2 LEX LGEEOp.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Machine-state facts
   ========================================================================== *)

Lemma ee_eqv_intro : forall (Q : machine_state -> Prop) ms, Q ms -> eqv_cl Q ms.
Proof.
  intros Q ms H. exists ms. split; [exact H|].
  repeat split; try reflexivity; try (intros r _; reflexivity).
Qed.

Lemma ee_MS_eq : forall R F pc fc rv m ro R' F' pc' fc' rv' m' ro',
  MS R F pc fc rv m ro = MS R' F' pc' fc' rv' m' ro' -> R = R' /\ F = F' /\ fc = fc' /\ m = m'.
Proof.
  intros R F pc fc rv m ro R' F' pc' fc' rv' m' ro' H.
  split; [exact (f_equal ms_regs H)|]. split; [exact (f_equal ms_fregs H)|].
  split; [exact (f_equal ms_fcsr H) | exact (f_equal ms_mem H)].
Qed.

(* the state an allocator call returns, up to ms_eqv: its canonical mkR form keeps the caller's
   callee-saved registers (regs_preserved) and reads every other one from the returned map *)
Lemma ee_canon : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (regs' F : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte),
  regs_preserved
    (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) regs' ->
  Q (MS (mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
             (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
             (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
        F pc fc None m (seg_rom rsegs)) ->
  eqv_cl Q (MS regs' F pc fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    regs' F pc fc m RP HQ.
  assert (R2 : reg_get regs' 2 = sp) by exact (RP 2 ltac:(cbv [callee_saved]; lia)).
  assert (R3 : reg_get regs' 3 = gp) by exact (RP 3 ltac:(cbv [callee_saved]; lia)).
  assert (R4 : reg_get regs' 4 = tp) by exact (RP 4 ltac:(cbv [callee_saved]; lia)).
  assert (R8 : reg_get regs' 8 = s0) by exact (RP 8 ltac:(cbv [callee_saved]; lia)).
  assert (R9 : reg_get regs' 9 = s1) by exact (RP 9 ltac:(cbv [callee_saved]; lia)).
  assert (R18 : reg_get regs' 18 = s2) by exact (RP 18 ltac:(cbv [callee_saved]; lia)).
  assert (R19 : reg_get regs' 19 = s3) by exact (RP 19 ltac:(cbv [callee_saved]; lia)).
  assert (R20 : reg_get regs' 20 = s4) by exact (RP 20 ltac:(cbv [callee_saved]; lia)).
  assert (R21 : reg_get regs' 21 = s5) by exact (RP 21 ltac:(cbv [callee_saved]; lia)).
  assert (R22 : reg_get regs' 22 = s6) by exact (RP 22 ltac:(cbv [callee_saved]; lia)).
  assert (R23 : reg_get regs' 23 = s7) by exact (RP 23 ltac:(cbv [callee_saved]; lia)).
  assert (R24 : reg_get regs' 24 = s8) by exact (RP 24 ltac:(cbv [callee_saved]; lia)).
  assert (R25 : reg_get regs' 25 = s9) by exact (RP 25 ltac:(cbv [callee_saved]; lia)).
  assert (R26 : reg_get regs' 26 = s10) by exact (RP 26 ltac:(cbv [callee_saved]; lia)).
  assert (R27 : reg_get regs' 27 = s11) by exact (RP 27 ltac:(cbv [callee_saved]; lia)).
  eexists. split; [exact HQ|].
  split.
  - intros r Hr. cbn [ms_regs MS]. rewrite (Regs6ss.mkR_of_eqv regs' r Hr). unfold Regs6ss.mkR_of.
    rewrite R2, R3, R4, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27. reflexivity.
  - repeat split.
Qed.

(* the slot's ret: ra is even, so ret_pc keeps it *)
Lemma ee_ret_pc : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. set (w := Z_to_bv 64 z).
  rewrite <- (Z_to_bv_bv_unsigned w).
  apply ret_pc_even.
  - pose proof (bv_unsigned_in_range 64 w) as Hw. unfold bv_modulus in Hw.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw. lia.
  - unfold w. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    clear - Hz. Z.div_mod_to_equations. lia.
Qed.

Lemma ee_ret_ra : forall g, lg_ra g mod 2 = 0 -> ret_pc (r_ra (lg_R g)) = Z_to_bv 64 (lg_ra g).
Proof. intros g H. exact (ee_ret_pc (lg_ra g) H). Qed.

(* ==========================================================================
   2. The program point of each cut predicate a segment of the chains ends at
   ========================================================================== *)

Lemma ee_cut1_pc : forall G ms, le_cut1 G ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 CALLOC_PC) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros G ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_cut2_pc : forall G md ms, le_cut2 G md ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 CALLOC_PC) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros G md ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_lh_pc : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_ex_pc : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s8
                  & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_free1_pc : forall S gp R md mk ms, le_free1 S gp R md mk ms ->
  exists R' F fc m, ms = MS R' F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros S gp R md mk ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s7
                          & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_free2_pc : forall S gp R md ms, le_free2 S gp R md ms ->
  exists R' F fc m, ms = MS R' F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros S gp R md ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7
                       & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_free2r_pc : forall S gp R ms, le_free2r S gp R ms ->
  exists R' F fc m, ms = MS R' F (Z_to_bv 64 L_FREE2_RA) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros S gp R ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0 & s1 & s2 & s3 & s4 & s5
                    & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ee_fin_pc : forall g ms, lg_ra g mod 2 = 0 -> le_fin (lg_S g) (lg_gp g) (lg_R g) ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 (lg_ra g)) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros g ms Hra (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FC & _).
  rewrite (ee_ret_ra g Hra). eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

(* ==========================================================================
   3. Bookkeeping: the entry ghost, the slot's blocks, the kept set
   ========================================================================== *)

Lemma ee_place : forall g, len_ghost g -> le_place (lg_G g).
Proof.
  intros g (H16 & H1 & H2 & Hn & Hb & Hp).
  unfold le_place, n_len. cbn [lg_G n_S n_p0 n_pl].
  split; [exact H1|]. split; [exact H2|]. split; [exact H16|]. split.
  - intros Hlt. rewrite <- Hn in Hlt. destruct (Hp Hlt) as [E HB]. rewrite E, <- Hn. exact HB.
  - rewrite <- Hn. lia.
Qed.

Lemma ee_hx_T : forall g, hx g (lg_T g) = [].
Proof. intros g. unfold hx. destruct (lg_T g); reflexivity. Qed.

(* FIN's case split from what is left of hb after the frees *)
Lemma ee_case : forall g hb T, (T = [] \/ exists f, T = [(f, MF_BLOCK)]) -> Permutation hb (hx g T) ->
  (lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = []).
Proof.
  intros g hb T HT HP. unfold hx in HP. revert HP. destruct (lg_T g) as [|t ts]; intros HP.
  - left. split; [reflexivity|]. destruct HT as [-> | (f & ->)].
    + exact (Permutation_nil (Permutation_sym HP)).
    + exact (Permutation_length_1_inv (Permutation_sym HP)).
  - right. split; [discriminate|]. exact (Permutation_nil (Permutation_sym HP)).
Qed.

(* the payload, when there is one, is a block of the driver's (lib_pre) *)
Definition ee_far (g : lghost) (a k : Z) : Prop := 0 < lg_n g -> a + k <= lg_p g \/ lg_p g + lg_n g <= a.

Lemma ee_room_nil : lroom_hb [].
Proof. unfold lroom_hb, hb_bytes. cbn. lia. Qed.

Lemma ee_room_md : forall md, lroom_hb [(md, MD_SIZE)].
Proof. intros md. unfold lroom_hb, hb_bytes, MD_SIZE. cbn. lia. Qed.

Lemma ee_fr1_size : forall p j0 j1 j2, Z.of_nat (cells_size (fr_cells1 p j0 j1 j2)) = 376.
Proof. reflexivity. Qed.

(* the long_alias NUL fin_P carries, from la_ok *)
Lemma ee_la_nul : forall m, la_ok m -> bytes_at rsegs m (A_LONG_ALIAS + 300) [Z_to_bv 8 0].
Proof.
  intros m (la & sl & [[Hwf Hb] _] & _).
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. apply ee_skip in Hb. rewrite Hl in Hb.
  change (Z.of_nat (Z.to_nat 300)) with 300 in Hb. exact Hb.
Qed.

Section EEL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma ee_cut_collapse : forall g pc hb T (P : machine_state -> Prop) c,
  CUT B API g pc hb T (eqv_cl P) c -> CUT B API g pc hb T P c.
Proof.
  intros g pc hb T P c (fx' & L & A & regs & mem & md & Ec & Hf & HL & (c0 & (c1 & H1 & E1) & E0)).
  exists fx', L, A, regs, mem, md. split; [exact Ec|]. split; [exact Hf|]. split; [exact HL|].
  exists c1. split; [exact H1 | exact (lfr_ms_eqv_trans _ _ _ E1 E0)].
Qed.

Lemma ee_cut_pure : forall g pc hb T (X : Prop) (P : machine_state -> Prop) c,
  CUT B API g pc hb T (fun ms => X /\ P ms) c -> X.
Proof. intros g pc hb T X P c (fx' & L & A & regs & mem & md & _ & _ & _ & (c0 & (HX & _) & _)). exact HX. Qed.

(* the 104 saved bytes are writable at every cut: they lie in the stack window LFR keeps writable *)
Lemma ee_cut_wr : forall g pc hb T (P : machine_state -> Prop) c, CUT B API g pc hb T P c ->
  CUT B API g pc hb T (fun ms => P ms /\ wr_at rsegs (ms_mem ms) (lg_S g - 104) 104) c.
Proof.
  intros g pc hb T P c (fx' & L & A & regs & mem & md & Ec & Hf & HL & (c0 & HP & Heq)).
  pose proof HL as (HV & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  pose proof (len_ghost_ok B API FF g HV) as (_ & HS1 & HS2 & _).
  exists fx', L, A, regs, mem, md. split; [exact Ec|]. split; [exact Hf|]. split; [exact HL|].
  exists c0. split; [|exact Heq]. split; [exact HP|].
  pose proof Heq as (_ & _ & _ & _ & _ & _ & Em & _).
  change (ms_mem c0 = normalize_cj rsegs mem) in Em. rewrite Em.
  rewrite (lff_segs B API FF) in Hwin. unfold SLOT_STACK in Hwin. unfold SLOT_STACK_Z in HS1.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite (en_wv mem (lg_S g - 104 + i)).
  - exact (Hwin (lg_S g - 104 + i) ltac:(lia)).
  - unfold TASK_SIZE. lia.
  - apply en_hi_ro. unfold LF_TOP. lia.
Qed.

Lemma ee_pay_blk : forall g, LGV B API g -> 0 < lg_n g -> In (lg_p g, lg_n g) (blocks (lg_L g) (lg_A g)).
Proof.
  intros g ((Hpre & _) & _) Hn.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcase & _).
  destruct Hcase as [(H0 & _) | (_ & q & Hq & Ea)]; [lia|].
  unfold blocks. apply in_map_iff. exists (q, lg_n g). split; [cbn [fst snd]; rewrite Ea; reflexivity | exact Hq].
Qed.

Lemma ee_far_fresh : forall g hb r n, LGV B API g -> lfresh B g hb r n -> ee_far g r n.
Proof.
  intros g hb r n HV (_ & _ & _ & _ & _ & Hb) Hn.
  destruct (Hb (lg_p g) (lg_n g) (ee_pay_blk g HV Hn)) as [H|H]; [left | right]; lia.
Qed.

(* ---- the regions of lkeep ---- *)

Lemma ee_img_keep : forall g hb x,
  (0x102a2 <= x < 0x105a1 \/ 0x207c0 <= x < 0x20848 \/ 0x31b80 <= x < 0x74528) -> lkeep B g hb x.
Proof. intros g hb x Hx. right; left. exact (lo_img_keep B API SH SK x FF Hx). Qed.

Lemma ee_pay_keep : forall g hb x, LGV B API g -> len_ghost g ->
  lo_rng (len_p0 g) (Z.of_nat (length (lg_pl g))) x -> lkeep B g hb x.
Proof.
  intros g hb x HV (_ & _ & _ & Hn & _ & Hp) Hx. unfold lo_rng in Hx.
  assert (Hpos : 0 < lg_n g) by lia. destruct (Hp Hpos) as (E & _).
  right; right; right. unfold in_blk0, in_tb. exists (lg_p g), (lg_n g).
  split; [exact (ee_pay_blk g HV Hpos) | rewrite <- E; lia].
Qed.

(* ---- the entry's memory views across an allocator call ---- *)

Lemma ee_base_carry : forall g hb m m', LGV B API g -> len_ghost g ->
  le_base (lg_G g) m -> lcarry (lkeep B g hb) m m' -> lpost_mem g m' -> le_base (lg_G g) m'.
Proof.
  intros g hb m m' HV HGh ((OD & TX & PR & _) & LA & PL & _ & _ & _) C (MI & TM & _ & ER & GD).
  split; [|split; [|split; [|split; [exact ER | split; [exact MI | exact TM]]]]].
  - split; [|split; [|split; [|exact GD]]].
    + apply (ml_use _ _ _ m m' ml_odd_at C); [|exact OD]. intros x Hx. apply ee_img_keep.
      unfold lo_odd_reg, lo_odd_str, lo_rng, A_ODD in Hx. lia.
    + apply (ml_use _ _ _ m m' ml_texts_at C); [|exact TX]. intros x Hx. apply ee_img_keep.
      unfold lo_rng, A_TEXTS in Hx. lia.
    + apply (ml_use _ _ _ m m' ml_policy_ro C); [|exact PR]. intros x Hx. apply ee_img_keep.
      unfold lo_pol_reg, lo_rng, A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in Hx. lia.
  - apply (ml_use _ _ _ m m' ml_la_ok C); [|exact LA]. intros x Hx. apply ee_img_keep.
    unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. lia.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact PL]. intros x Hx.
    exact (ee_pay_keep g hb x HV HGh Hx).
Qed.

Lemma ee_kern_carry : forall g hb m m', le_kern m -> lcarry (lkeep B g hb) m m' -> le_kern m'.
Proof.
  intros g hb m m' ((kbs & NK & NW & IT & K1 & K2 & K3 & K4) & GN & IP) C.
  assert (HI : iftab_at m' kbs link_tab /\ ifptrs_at m').
  { apply (ml_use _ _ _ m m' (ml_iftab kbs) C); [|split; [exact IT | exact IP]].
    intros x Hx. apply ee_img_keep.
    unfold lo_iftab_reg, lo_odd_str, lo_rng, A_G_NL, NK_IF_NAME, NK_IF_INDEX, A_G_NAMES, G_NAMES_SIZE in Hx.
    lia. }
  split; [|split].
  - exists kbs. split.
    + apply (ml_use _ _ _ m m' (ml_nlk_at kbs) C); [|exact NK]. intros x Hx. apply ee_img_keep.
      unfold lo_rng, A_G_NL, NK_SIZE in Hx. lia.
    + split; [exact NW|]. split; [exact (proj1 HI)|]. repeat split; assumption.
  - apply (ml_use _ _ _ m m' ml_gnames_at C); [|exact GN]. intros x Hx. apply ee_img_keep.
    unfold lo_rng, A_G_NAMES, G_NAMES_SIZE in Hx. lia.
  - exact (proj2 HI).
Qed.

Lemma ee_frame_carry : forall g hb m m', le_frame (lg_G g) m -> lcarry (lkeep B g hb) m m' ->
  le_frame (lg_G g) m'.
Proof.
  intros g hb m m' ((j0 & j1 & j2 & FR) & SB & SW) C.
  split; [exists j0, j1, j2|split].
  - apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact FR]. intros x Hx.
    unfold lo_rng in Hx. rewrite ee_fr1_size in Hx. change (n_S (lg_G g)) with (lg_S g) in Hx.
    left. unfold SLOT_FRAME in *. lia.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact SB]. intros x Hx.
    unfold lo_rng in Hx. rewrite lr_bytes_length in Hx. change (n_S (lg_G g)) with (lg_S g) in Hx.
    change (Z.of_nat 104) with 104 in Hx. left. unfold SLOT_FRAME. lia.
  - apply (ml_use _ _ _ m m' (ml_wr_at _ _) C); [|exact SW]. intros x Hx.
    unfold lo_rng in Hx. change (n_S (lg_G g)) with (lg_S g) in Hx. left. unfold SLOT_FRAME. lia.
Qed.

(* a block calloc handed out earlier keeps its zero bytes: it is one of the slot's blocks hb *)
Lemma ee_blk_carry : forall g hb S a n m m', 0 <= n -> In (a, n) hb ->
  blk_zero S a n m -> lcarry (lkeep B g hb) m m' -> blk_zero S a n m'.
Proof.
  intros g hb S a n m m' Hn Hin (H0 & H16 & HO & U) C.
  split; [exact H0|]. split; [exact H16|]. split; [exact HO|].
  apply (ml_use _ _ _ m m' (ml_u8arr _ _) C); [|exact U]. intros x Hx.
  right; right; left. exists a, n. split; [exact Hin|].
  unfold lo_rng in Hx. rewrite zeros_length in Hx by lia. lia.
Qed.

(* the block calloc(1, n) has just handed out *)
Lemma ee_fresh_blk : forall g hb r n m', len_ghost g -> lfresh B g hb r n -> r mod 16 = 0 -> 0 <= n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (r + i) = Some (Z_to_bv 8 0) /\ writable_at rsegs m' (r + i)) ->
  blk_zero (lg_S g) r n m'.
Proof.
  intros g hb r n m' (_ & _ & HS2 & _) (Hr0 & H4096 & Htop & Himg & _ & _) H16 Hn HZ.
  pose proof (lff_segs B API FF) as SEG.
  unfold SLOT_STACK in Htop.
  split; [exact Hr0|]. split; [exact H16|]. split.
  - split; [exact H4096|]. split; [unfold SLOT_STACK_Z; lia|].
    intros i Hi s Hs Hin. apply (Himg i Hi). split; [rewrite SEG; exact lfr_rsegs_nonnil|].
    exists s. rewrite SEG. split; [exact Hs | exact Hin].
  - split.
    + split; [lia|]. rewrite zeros_length by lia. split; [lia|].
      intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
      rewrite (nth_error_repeat (zb 0) Hi).
      exact (proj1 (HZ (Z.of_nat i) ltac:(lia))).
    + rewrite zeros_length by lia. split; [lia|]. split; [lia|].
      intros i Hi. exact (proj2 (HZ i Hi)).
Qed.

(* ---- the exit's memory view across free ---- *)

Lemma ee_tail_carry : forall g hb R m m', le_tail_mem (lg_S g) R m -> lcarry (lkeep B g hb) m m' ->
  lpost_mem g m' -> le_tail_mem (lg_S g) R m'.
Proof.
  intros g hb R m m' ((j & FR) & SB & SW & _ & _ & LA & _ & _ & _) C (MI & TM & ST & ER & GD).
  split; [exists j|split; [|split; [|split; [exact ER | split; [exact GD | split; [|split; [exact MI | split; [exact TM | exact ST]]]]]]]].
  - apply (ml_use _ _ _ m m' (ml_rw_cells _ _) C); [|exact FR]. intros x Hx.
    unfold lo_rng in Hx. rewrite lo_cb376 in Hx. left. unfold SLOT_FRAME in *. lia.
  - apply (ml_use _ _ _ m m' (ml_bytes_at _ _) C); [|exact SB]. intros x Hx.
    unfold lo_rng in Hx. rewrite lr_bytes_length in Hx. change (Z.of_nat 104) with 104 in Hx.
    left. unfold SLOT_FRAME. lia.
  - apply (ml_use _ _ _ m m' (ml_wr_at _ _) C); [|exact SW]. intros x Hx.
    unfold lo_rng in Hx. left. unfold SLOT_FRAME. lia.
  - apply (ml_use _ _ _ m m' ml_la_ok C); [|exact LA]. intros x Hx. apply ee_img_keep.
    unfold lo_rng, A_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. lia.
Qed.

(* ---- the end ---- *)

Lemma ee_fin_P : forall g ms, LGV B API g -> le_fin (lg_S g) (lg_gp g) (lg_R g) ms -> fin_P g ms.
Proof.
  intros g ms HV (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & _
                  & _ & _ & LA & _).
  pose proof HV as ((Hpre & _) & _).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _).
  rewrite (lff_tp B API FF) in Htp.
  unfold fin_P. split; [reflexivity|]. split.
  - intros r Hr. unfold callee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    + change (wz (lg_S g) = getr (lg_regs g) 2). unfold wz, lg_S, spZ. apply Z_to_bv_bv_unsigned.
    + reflexivity.
    + exact (eq_sym Htp).
    + reflexivity.
    + reflexivity.
    + assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/
                   r = 27) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
  - exact (ee_la_nul _ LA).
Qed.

(* the epilogue at 0x1414c to the caller's ra, then LGlue's FIN *)
Lemma ee_fin : forall g hb T c, ((lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = [])) ->
  CUT B API g L_FREE2_RA hb T (le_free2r (lg_S g) (lg_gp g) (lg_R g)) c -> SR (ms_segs B) c (FIN B API g).
Proof.
  intros g hb T c Hcase HC.
  pose proof (cut_lgv B API g _ _ _ _ c HC) as HV.
  pose proof (len_ghost_ok B API FF g HV) as (_ & HS1 & HS2 & _).
  pose proof HV as (_ & _ & _ & _ & _ & Hra & _).
  eapply SR_mono.
  - apply (cut_evt B API FF g L_FREE2_RA hb T [] _ (lg_ra g) (le_fin (lg_S g) (lg_gp g) (lg_R g)) c HC).
    + intros t [].
    + intros ms H. eapply evt_mono; [exact (le_EXc (lg_S g) (lg_R g) (lg_gp g) ms HS1 HS2 H)|].
      intros ms' (Hf & Hfp). apply ee_eqv_intro. split; [exact Hf | exact (Hfp [])].
    + intros ms' H. exact (ee_fin_pc g ms' Hra H).
  - intros c' H. exists hb, T. split; [exact Hcase|].
    exact (cut_mono B API g _ _ _ _ _ c' (fun ms Hm => ee_fin_P g ms HV Hm) H).
Qed.

End EEL.
