(* ARM 1 (op_write) at the SR level: LGlue's ARM 1 from LC1's three evt segments and the two
   allocator steps of the SR frame.

     loop head 0x13a1c          -- c1_seg_A  (cut_evt)       -> text_of's call  (c1_15aa8, pc 0x15aa8)
     text_of                    -- lfr_text_of               -> its return      (c1_13fb8, pc 0x13fb8)
     0x13fb8                    -- c1_seg_B  (cut_evt)       -> free's call     (c1_173d4, pc 0x173d4)
     free                       -- lfr_free / lfr_free_null  -> its return      (c1_14060, pc 0x14060)
     0x14060                    -- c1_seg_C  (cut_evt_or)    -> loop head i + 1 or the exit

   text_of hands back `own` (0 for a `texts` entry, else the fresh block it allocated, of k <= 320
   bytes), so hb grows by `opt_hb own k hb` and free gives it back: at the end hb is the arm's own hb
   again, and T never changes. The slot's blocks that a segment of this arm writes are the model and
   the marks block (LC1Defs.c1_hp). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem
  text_of_c kernel_c model_write_c reac_link_alias_write_c check_socket_c strlen_c index_of_c
  check_refused_c check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1ALib LC1A LC1B LC1C LFr LFrLo LFrRun LFrAl LFrEn LFrTx LGlue LG1Lib.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The program point of each cut predicate (the cut_evt / cut_evt_or form premise)
   ========================================================================== *)

Lemma g1_15aa8_pc : forall E i gp ms, c1_15aa8 E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 C1_TEXT_OF) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
                    & P & N & kbs & mbs & gbs & nb & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma g1_13fb8_pc : forall E i gp own ms, c1_13fb8 E i gp own ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 C1_TEXT_OF_RA) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp own ms (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                        & F & fc & m & P & N & kbs & mbs & gbs & nb & s & t & sl & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma g1_173d4_pc : forall E i gp own ms, c1_173d4 E i gp own ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 C1_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp own ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & t3 & t4
                        & t5 & t6 & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma g1_14060_pc : forall E i gp ms, c1_14060 E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 C1_FREE_RA) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & t3
                    & t4 & t5 & t6 & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma g1_lh_ms_pc : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma g1_ex_ms_pc : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

(* ==========================================================================
   2. The frame cell text_of writes its answer into, and the input it reads
   ========================================================================== *)

(* the own cell (sp + 0x78) is the first word of the frame's 256-byte buffer *)
Lemma g1_own_cell : forall E i P N kbs mbs gbs m,
  lh_mem E i P N kbs mbs gbs m -> exists w, rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B256) [C8 w].
Proof.
  intros E i P N kbs mbs gbs m ((j0 & j1 & j2 & nc & HF) & _).
  unfold lh_cells in HF. apply c1a_frame_split in HF. destruct HF as (_ & _ & F3).
  change [CB 40 j1; CB 256 j2] with ([CB 40 j1] ++ [CB 256 j2]) in F3.
  apply c1a_rwc_split in F3. destruct F3 as [_ F3b].
  change (Z.of_nat (cells_size [CB 40 j1])) with 40 in F3b.
  replace (e_S E - SLOT_FRAME + 80 + 40) with (e_S E - SLOT_FRAME + FO_B256) in F3b
    by (unfold FO_B256; lia).
  pose proof (rw_cells_split_CB rsegs m (e_S E - SLOT_FRAME + FO_B256) [] 256 j2 [] [8%nat; 248%nat]
                F3b eq_refl) as F3s.
  cbn [app mk_CB_cells] in F3s.
  change [CB 8 (firstn 8 j2); CB 248 (firstn 248 (skipn 8 j2))]
    with ([CB 8 (firstn 8 j2)] ++ [CB 248 (firstn 248 (skipn 8 j2))]) in F3s.
  apply c1a_rwc_split in F3s. destruct F3s as [F3h _].
  exact (lg1_cb8_c8 m _ _ F3h).
Qed.

(* the bytes left at the cursor *)
Lemma g1_cursor_bytes : forall m p0 pl P N, cursor_ok m p0 pl P N ->
  exists inp, bytes_at rsegs m P inp /\ Z.of_nat (length inp) = N.
Proof.
  intros m p0 pl P N (HB & k & Hk & HP & HN).
  exists (skipn (Z.to_nat k) pl). split.
  - rewrite <- (firstn_skipn (Z.to_nat k) pl) in HB.
    apply (proj1 (bytes_at_app rsegs m p0 _ _)) in HB. destruct HB as [_ HB2].
    assert (EL : Z.of_nat (length (firstn (Z.to_nat k) pl)) = k).
    { rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. apply Z.min_l. lia. }
    rewrite EL in HB2. rewrite <- HP in HB2. exact HB2.
  - rewrite length_skipn, Nat2Z.inj_sub by lia. rewrite Z2Nat.id by lia. lia.
Qed.

(* the cursor's bounds inside the payload block *)
Lemma g1_cursor_rng : forall E i P N kbs mbs gbs m,
  lenv_ok E -> lh_mem E i P N kbs mbs gbs m ->
  4096 <= P /\ 0 <= N /\ P + N <= e_S E - SLOT_STACK_Z /\ e_S E <= 2 ^ 47 /\
  P = e_p0 E + (P - e_p0 E) /\ 0 <= P - e_p0 E <= Z.of_nat (length (e_pl E)) /\
  N = Z.of_nat (length (e_pl E)) - (P - e_p0 E).
Proof.
  intros E i P N kbs mbs gbs m HE HL.
  pose proof HE as (HS1 & HS2 & _ & _ & _ & _ & _ & _ & Hpl & (Hp1 & Hp2 & _) & _).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  (_ & k & Hk & HP & HN) & _).
  subst P N. repeat split; lia.
Qed.

Section G1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

(* the callee contracts the arm's segments take (LC1A takes none; LC1B's Section, same names) *)
Hypothesis KERNEL_OK : kernel_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.
Hypothesis ALIAS_WRITE_OK : reac_link_alias_write_contract.
Hypothesis CHECK_SOCKET_OK : check_socket_contract.
Hypothesis STRLEN_OK : strlen_contract.
Hypothesis INDEX_OF_OK : index_of_contract_P.
Hypothesis CHECK_REFUSED_OK : check_refused_contract.
Hypothesis CHECK_WRITE_OK : check_write_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

Hypothesis FF : LFF B API.

(* text_of's SR step is LFrTx.lfr_text_of; it takes the callee's contract as this Section's hypothesis *)
Hypothesis TOF : forall fx' : YK11.FPState, @text_of_contract fx' rc B API.

(* text_of's return cut, with what the free step needs of the block it handed back *)
Definition c1_tof_ret (E : lenv) (i : Z) (gp : word) (own k : Z) (ms : machine_state) : Prop :=
  eqv_cl (c1_13fb8 E i gp own) ms /\ (own = 0 \/ 1 <= k <= 320).

(* ==========================================================================
   3. The cursor at the call of text_of lies inside the payload block
   ========================================================================== *)

Lemma g1_cursor_in : forall g md mk i P N kbs mbs gbs m,
  LGV B API g -> lenv_ok (lg_E g md mk) -> lh_mem (lg_E g md mk) i P N kbs mbs gbs m ->
  0 < lg_n g /\ lg_p g <= P /\ P + N <= lg_p g + lg_n g.
Proof.
  intros g md mk i P N kbs mbs gbs m HV HE HL.
  pose proof (len_ghost_ok B API FF g HV) as (_ & _ & _ & Hn & _ & Hcase).
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  change (e_pl (lg_E g md mk)) with (lg_pl g) in Hpl.
  assert (Hn0 : 0 < lg_n g) by lia.
  destruct (Hcase Hn0) as (Ep & _).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  (_ & k & Hk & HP & HN) & _).
  change (e_p0 (lg_E g md mk)) with (len_p0 g) in HP.
  change (e_pl (lg_E g md mk)) with (lg_pl g) in HN.
  rewrite Ep in HP. split; [exact Hn0|]. lia.
Qed.

(* ==========================================================================
   4. The adapter at text_of's return address 0x13fb8
   ========================================================================== *)

Lemma g1_tof_adapt : forall g md mk hb i R F fc m regs' m' (c0 c1 : word) own k s t sl,
  lenv_ok (lg_E g md mk) -> LGV B API g ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c1_15aa8 (lg_E g md mk) i (lg_gp g) (MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs)) ->
  rw_cells rsegs m (lg_S g - SLOT_FRAME + FO_P) [C8 c0; C8 c1] ->
  regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 s -> s <> 0 ->
  lcarry (fun x => lkeep B g hb x /\
            ~ (lg_S g - SLOT_FRAME + FO_P <= x < lg_S g - SLOT_FRAME + FO_P + 16) /\
            ~ (lg_S g - SLOT_FRAME + FO_B256 <= x < lg_S g - SLOT_FRAME + FO_B256 + 8)) m m' ->
  lpost_mem g m' ->
  cstr_at m' s t -> Z.of_nat (length t) < 320 ->
  bytes_at rsegs m' (s + Z.of_nat (length t) + 1) sl ->
  Z.of_nat (length sl) = (- (s + Z.of_nat (length t) + 1)) mod 8 ->
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) (lg_S g - SLOT_STACK_Z) SLOT_STACK_Z ->
  apart_gnl s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) ->
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_LONG_ALIAS 304 ->
  apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) A_ERRNO 4 ->
  (forall a n, In (a, n) hb -> 0 < n -> apart s (Z.of_nat (length t) + 1 + Z.of_nat (length sl)) a n) ->
  rw_cells rsegs m' (lg_S g - SLOT_FRAME + FO_B256) [C8 (Z_to_bv 64 own)] ->
  (exists adv, 0 <= adv <= bv_unsigned c1 /\
     rw_cells rsegs m' (lg_S g - SLOT_FRAME + FO_P)
       [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))]) ->
  (own = 0 -> k = 0 /\ A_RO_LO <= s /\ s + Z.of_nat (length t) + 1 <= A_RO_END) ->
  (own <> 0 -> own = s /\ 1 <= k <= 320 /\ Z.of_nat (length t) + 1 <= k /\ lfresh B g hb own k) ->
  c1_tof_ret (lg_E g md mk) i (lg_gp g) own k
    (MS regs' F (Z_to_bv 64 C1_TEXT_OF_RA) fc None m' (seg_rom rsegs)).
Proof.
  intros g md mk hb i R F fc m regs' m' c0 c1 own k s t sl HE HV HMD HMK HP HCUR0 RP Hs10 Hs0 CAR HPOST
    HCS HTL HSL HSLL HA1 HA2 HA3 HA4 HAHB HOWN HADV HOWN0 HOWNN.
  set (E := lg_E g md mk) in *.
  (* unpack the call state *)
  destruct HP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
                  & P & N & kbs & mbs & gbs & nb & EQ & FRM & Hi & Hnb & HN & HLM & HCUR & MI & TM & STK).
  pose proof (f_equal ms_regs EQ) as ER.
  pose proof (f_equal ms_fregs EQ) as EFR.
  pose proof (f_equal ms_fcsr EQ) as EFC.
  pose proof (f_equal ms_mem EQ) as EMM.
  cbn [ms_regs ms_fregs ms_fcsr ms_mem MState.MS] in ER, EFR, EFC, EMM.
  subst F0 fc0 m0 R.
  (* the two cursor cells of the cut are the ones the step read *)
  destruct (lg1_c8c8_det m _ _ _ _ _ HCUR HCUR0) as [Ec0 Ec1]. subst c0 c1.
  destruct (g1_cursor_rng E i P N kbs mbs gbs m HE HLM) as (RP1 & RN1 & RPN & RS & RPe & RKr & RNe).
  assert (UP : bv_unsigned (wz P) = P) by (apply unsigned_lit; unfold SLOT_STACK_Z in *; lia).
  assert (UN : bv_unsigned (wz N) = N) by (apply unsigned_lit; unfold SLOT_STACK_Z in *; lia).
  rewrite UP, UN in HADV. destruct HADV as (adv & Hadv & HCUR').
  (* the loop memory at the return address *)
  assert (CAR' : lcarry (lg1_keep_reg E) m m').
  { eapply lcarry_mono; [|exact CAR].
    intros x [Hr Hw]. split; [exact (lg1_keep B API FF g md mk hb x HV HE HMD HMK Hr)|].
    split; intros Hc; apply Hw; [left | right]; exact Hc. }
  pose proof HPOST as (MI' & TM' & STK' & HER' & HGU').
  assert (HLM' : lh_mem E i (P + adv) (N - adv) kbs mbs gbs m').
  { apply (lg1_lh_mem_carry E i P N (P + adv) (N - adv) own kbs mbs gbs m m' HE HLM CAR' HER' HGU');
      [exact HCUR' | exact HOWN |].
    exists (P - e_p0 E + adv). split; [lia|]. split; lia. }
  (* the answer and the slack after it *)
  assert (HBA : bytes_at rsegs m' s (t ++ zb 0 :: sl)).
  { destruct HCS as [HB0 _].
    replace (t ++ zb 0 :: sl) with ((t ++ [zb 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs m' s _ _)). split; [exact HB0|].
    rewrite length_app. cbn [length].
    replace (s + Z.of_nat (length t + 1)) with (s + Z.of_nat (length t) + 1) by lia.
    exact HSL. }
  assert (HAL : al_ok E m' s t sl).
  { split; [exact Hs0|]. split; [exact HBA|]. split; [exact (proj2 HCS)|].
    split; [exact HTL|]. split; [exact HSLL|].
    split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3|].
    split; [exact (HAHB md MD_SIZE HMD ltac:(unfold MD_SIZE; lia)) | exact HA4]. }
  (* the return state *)
  split.
  2:{ destruct (Z.eq_dec own 0) as [Hz|Hne]; [left; exact Hz|].
      right. destruct (HOWNN Hne) as (_ & Hk & _). exact Hk. }
  apply lg1_eqv_canon.
  rewrite (mkR_of_preserved (wz C1_TEXT_OF_RA) (wz (e_S E - SLOT_FRAME)) (lg_gp g) (wz A_TP) t0 t1 t2
             (wz (e_md E)) (wz GNL40) (wz (e_S E - SLOT_FRAME + FO_P)) (wz (e_S E - SLOT_FRAME + FO_B256))
             a2 a3 a4 a5 a6 a7 (wz (sel_ptr nb)) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
             (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6 regs' RP).
  assert (R10 : reg_get regs' 10 = wz s).
  { transitivity (reg_get regs' (Z_to_bv 5 10)); [reflexivity|].
    rewrite (reg_get_getr regs' 10 ltac:(lia)). exact Hs10. }
  rewrite R10.
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7),
         (reg_get regs' 11), (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14),
         (reg_get regs' 15), (reg_get regs' 16), (reg_get regs' 17),
         s3, s4, (reg_get regs' 28), (reg_get regs' 29), (reg_get regs' 30), (reg_get regs' 31),
         F, fc, m', (P + adv), (N - adv), kbs, mbs, gbs, nb, s, t, sl.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact Hnb|]. split; [lia|].
  split; [exact HLM'|].
  split; [exact HCUR'|].
  split; [exact (lg1_c8_bytes m' _ _ HOWN)|].
  split.
  { destruct (Z.eq_dec own 0) as [Hz|Hne]; [left; exact Hz|]. right. exact (proj1 (HOWNN Hne)). }
  split; [exact HAL|].
  split; [exact MI'|]. split; [exact TM' | exact STK'].
Qed.

(* ==========================================================================
   5. The adapter at free's return address 0x14060
   ========================================================================== *)

Lemma g1_free_adapt : forall g md mk hb i own R F fc m regs' m',
  lenv_ok (lg_E g md mk) -> LGV B API g -> In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c1_173d4 (lg_E g md mk) i (lg_gp g) own (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  eqv_cl (c1_14060 (lg_E g md mk) i (lg_gp g))
    (MS regs' F (Z_to_bv 64 C1_FREE_RA) fc None m' (seg_rom rsegs)).
Proof.
  intros g md mk hb i own R F fc m regs' m' HE HV HMD HMK HP RP CAR HPOST.
  set (E := lg_E g md mk) in *.
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & t3 & t4 & t5
                  & t6 & F0 & fc0 & m0 & P & N & kbs & mbs & gbs & EQ & FRM & Hi & HN & HLM & HCUR & MI
                  & TM & STK).
  pose proof (f_equal ms_regs EQ) as ER.
  pose proof (f_equal ms_fregs EQ) as EFR.
  pose proof (f_equal ms_fcsr EQ) as EFC.
  pose proof (f_equal ms_mem EQ) as EMM.
  cbn [ms_regs ms_fregs ms_fcsr ms_mem MState.MS] in ER, EFR, EFC, EMM.
  subst F0 fc0 m0 R.
  pose proof HPOST as (MI' & TM' & STK' & HER' & HGU').
  assert (CAR' : lcarry (lh_reg E) m m').
  { eapply lcarry_mono; [|exact CAR].
    intros x Hr. exact (lg1_keep B API FF g md mk hb x HV HE HMD HMK Hr). }
  assert (HLM' : lh_mem E (i + 1) P N kbs mbs gbs m')
    by exact (lh_mem_carry E (i + 1) P N kbs mbs gbs m m' HLM CAR' HER' HGU').
  assert (HCUR' : rw_cells rsegs m' (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)]).
  { apply (ml_use _ _ _ m m' (ml_rw_cells _ _) CAR'); [|exact HCUR].
    intros x Hx. apply lh_reg_frame.
    change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16 in Hx.
    unfold lo_rng, FO_P, SLOT_FRAME in *. lia. }
  apply lg1_eqv_canon.
  rewrite (mkR_of_preserved (wz C1_FREE_RA) (wz (e_S E - SLOT_FRAME)) (lg_gp g) (wz A_TP) t0 t1 t2
             (wz (e_md E)) (wz GNL40) (wz own) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (e_mk E))
             (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6 regs' RP).
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7),
         (reg_get regs' 10), (reg_get regs' 11), (reg_get regs' 12), (reg_get regs' 13),
         (reg_get regs' 14), (reg_get regs' 15), (reg_get regs' 16), (reg_get regs' 17),
         s2, s3, s4, s5, s6, (reg_get regs' 28), (reg_get regs' 29), (reg_get regs' 30),
         (reg_get regs' 31), F, fc, m', P, N, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact HN|].
  split; [exact HLM'|]. split; [exact HCUR'|].
  split; [exact MI'|]. split; [exact TM' | exact STK'].
Qed.

(* ==========================================================================
   6. The five steps of the arm
   ========================================================================== *)

Lemma g1_segA : forall g md mk hb T i c,
  lenv_ok (lg_E g md mk) ->
  (forall t, In t (c1_hp (lg_E g md mk)) -> In t hb /\ ~ In t T) ->
  CUT B API g L_LH hb T
    (fun ms => lh_ms (lg_E g md mk) i (lg_gp g) ms /\ lh_op (lg_E g md mk) ms 1) c ->
  SR (ms_segs B) c (CUT B API g C1_TEXT_OF hb T (c1_15aa8 (lg_E g md mk) i (lg_gp g))).
Proof.
  intros g md mk hb T i c HE Hhp HC.
  apply (cut_evt B API FF g L_LH hb T (c1_hp (lg_E g md mk)) _ C1_TEXT_OF _ c HC Hhp).
  - intros ms (HL & HO). exact (c1_seg_A (lg_E g md mk) i (lg_gp g) ms HE HL HO).
  - intros ms' H. exact (g1_15aa8_pc _ _ _ _ H).
Qed.

Lemma g1_segB : forall g md mk hb T i own c,
  lenv_ok (lg_E g md mk) ->
  (forall t, In t (c1_hp (lg_E g md mk)) -> In t hb /\ ~ In t T) ->
  CUT B API g C1_TEXT_OF_RA hb T (c1_13fb8 (lg_E g md mk) i (lg_gp g) own) c ->
  SR (ms_segs B) c (CUT B API g C1_FREE hb T (c1_173d4 (lg_E g md mk) i (lg_gp g) own)).
Proof.
  intros g md mk hb T i own c HE Hhp HC.
  apply (cut_evt B API FF g C1_TEXT_OF_RA hb T (c1_hp (lg_E g md mk)) _ C1_FREE _ c HC Hhp).
  - intros ms H.
    exact (c1_seg_B KERNEL_OK MODEL_WRITE_OK ALIAS_WRITE_OK CHECK_SOCKET_OK STRLEN_OK INDEX_OF_OK
             CHECK_REFUSED_OK CHECK_WRITE_OK CHECK_REQUESTS_OK (lg_E g md mk) i (lg_gp g) own ms HE H).
  - intros ms' H. exact (g1_173d4_pc _ _ _ _ _ H).
Qed.

Lemma g1_segC : forall g md mk hb T i c,
  lenv_ok (lg_E g md mk) ->
  (forall t, In t (c1_hp (lg_E g md mk)) -> In t hb /\ ~ In t T) ->
  CUT B API g C1_FREE_RA hb T (c1_14060 (lg_E g md mk) i (lg_gp g)) c ->
  SR (ms_segs B) c (fun c' =>
    CUT B API g L_LH hb T (fun ms => i < 47 /\ lh_ms (lg_E g md mk) (i + 1) (lg_gp g) ms) c' \/
    CUT B API g L_EXIT hb T (ex_ms (lg_E g md mk) (lg_gp g)) c').
Proof.
  intros g md mk hb T i c HE Hhp HC.
  apply (cut_evt_or B API FF g C1_FREE_RA hb T (c1_hp (lg_E g md mk)) _ L_LH _ L_EXIT _ c HC Hhp).
  - intros ms H. exact (c1_seg_C (lg_E g md mk) i (lg_gp g) ms HE H).
  - intros ms' (_ & H). exact (g1_lh_ms_pc _ _ _ _ H).
  - intros ms' H. exact (g1_ex_ms_pc _ _ _ H).
Qed.

(* free(NULL) leaves the state as it was *)
Lemma g1_free_null_adapt : forall g md mk i own R F fc m,
  c1_173d4 (lg_E g md mk) i (lg_gp g) own (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  eqv_cl (c1_14060 (lg_E g md mk) i (lg_gp g)) (MS R F (Z_to_bv 64 C1_FREE_RA) fc None m (seg_rom rsegs)).
Proof.
  intros g md mk i own R F fc m HP.
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & t3 & t4 & t5
                  & t6 & F0 & fc0 & m0 & P & N & kbs & mbs & gbs & EQ & FRM & Hi & HN & HLM & HCUR & MI
                  & TM & STK).
  pose proof (f_equal ms_regs EQ) as ER.
  pose proof (f_equal ms_fregs EQ) as EFR.
  pose proof (f_equal ms_fcsr EQ) as EFC.
  pose proof (f_equal ms_mem EQ) as EMM.
  cbn [ms_regs ms_fregs ms_fcsr ms_mem MState.MS] in ER, EFR, EFC, EMM.
  subst F0 fc0 m0 R.
  apply eqv_cl_intro.
  exists (wz C1_FREE_RA), t0, t1, t2, (wz own), a1, a2, a3, a4, a5, a6, a7,
         s2, s3, s4, s5, s6, t3, t4, t5, t6, F, fc, m, P, N, kbs, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact HN|].
  split; [exact HLM|]. split; [exact HCUR|].
  split; [exact MI|]. split; [exact TM | exact STK].
Qed.

(* the free call: the block text_of handed back, or NULL *)
Lemma g1_free : forall g md mk hb T i own k c,
  lenv_ok (lg_E g md mk) -> LGV B API g -> hb_inv g (lg_E g md mk) hb T ->
  (T = [] \/ exists f, T = [(f, MF_BLOCK)]) ->
  (own = 0 \/ 1 <= k <= 320) ->
  CUT B API g C1_FREE (opt_hb own k hb) T (c1_173d4 (lg_E g md mk) i (lg_gp g) own) c ->
  SR (ms_segs B) c (CUT B API g C1_FREE_RA hb T (c1_14060 (lg_E g md mk) i (lg_gp g))).
Proof.
  intros g md mk hb T i own k c HE HV HI HT HK HC.
  pose proof (lg1_hb_md g (lg_E g md mk) hb T HI) as HMD.
  pose proof (lg1_hb_mk g (lg_E g md mk) hb T HI) as HMK.
  assert (HREG : forall ms, c1_173d4 (lg_E g md mk) i (lg_gp g) own ms ->
            getr (ms_regs ms) 1 = Z_to_bv 64 C1_FREE_RA /\
            getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\
            getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 own).
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & t3 & t4 & t5 & t6
               & F & fc & m & P & N & kbs & mbs & gbs & EQ & _).
    subst ms. cbn [ms_regs MState.MS]. repeat split; reflexivity. }
  eapply SR_mono; [|intros c' Hc'; exact (lg1_cut_eqv B API g C1_FREE_RA hb T _ c' Hc')].
  revert HC. destruct (Z.eq_dec own 0) as [Hz | Hne].
  - (* own = 0: free(NULL) changes nothing *)
    subst own. intros HC.
    replace (opt_hb 0 k hb) with hb in HC by reflexivity.
    apply (lfr_free_null B API FF g hb T C1_FREE_RA _ _ c
             ltac:(unfold C1_FREE_RA; lia) ltac:(unfold C1_FREE_RA; reflexivity) HC).
    + intros ms H. destruct (HREG ms H) as (H1 & _ & _ & H10). split; [exact H1 | exact H10].
    + intros R F fc m H. exact (g1_free_null_adapt g md mk i 0 R F fc m H).
  - (* own <> 0: the block text_of allocated, which is not the kept FILE (k <= 320 < MF_BLOCK) *)
    intros HC.
    assert (Hk : 1 <= k <= 320) by (destruct HK as [Hz0 | Hk0]; [exfalso; exact (Hne Hz0) | exact Hk0]).
    assert (EOPT : opt_hb own k hb = [] ++ (own, k) :: hb)
      by (unfold opt_hb; rewrite (proj2 (Z.eqb_neq own 0) Hne); reflexivity).
    rewrite EOPT in HC.
    assert (HnT : ~ In (own, k) T).
    { destruct HT as [HT0 | (f & HT0)]; rewrite HT0; [intros []|].
      intros [Hf | []]. injection Hf as _ Hs. unfold MF_BLOCK in Hs. lia. }
    apply (lfr_free B API FF g [] own k hb T C1_FREE_RA _ _ c HnT
             ltac:(unfold C1_FREE_RA; lia) ltac:(unfold C1_FREE_RA; reflexivity) HC).
    + intros ms H. destruct (HREG ms H) as (H1 & H2 & H4 & H10).
      split; [exact H1|]. split; [exact H2|]. split; [exact H4 | exact H10].
    + cbn [app]. intros R F fc m regs' m' H HRP HCAR HPM.
      exact (g1_free_adapt g md mk hb i own R F fc m regs' m' HE HV HMD HMK H HRP HCAR HPM).
Qed.

(* ==========================================================================
   7. ARM 1
   ========================================================================== *)

Theorem glue_arm1 : ARM B API 1.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  pose proof (cut_lgv B API g L_LH hb T _ c HC) as HV.
  pose proof (hp_md_mk g (lg_E g md mk) hb T HI HT) as Hhp.
  pose proof (lg1_hb_md g (lg_E g md mk) hb T HI) as HMD.
  pose proof (lg1_hb_mk g (lg_E g md mk) hb T HI) as HMK.
  pose proof (lg1_room g (lg_E g md mk) hb T HI HT) as HROOM.
  (* A: the loop head -> text_of's call *)
  eapply SR_bind; [exact (g1_segA g md mk hb T i c OK Hhp HC)|].
  intros cA HCA.
  (* text_of *)
  eapply SR_bind.
  { apply (lfr_text_of B API FF TOF g hb T C1_TEXT_OF_RA (lg_S g - SLOT_FRAME + FO_P)
             (lg_S g - SLOT_FRAME + FO_B256) (c1_15aa8 (lg_E g md mk) i (lg_gp g))
             (c1_tof_ret (lg_E g md mk) i (lg_gp g)) cA HROOM
             ltac:(unfold C1_TEXT_OF_RA; lia) ltac:(unfold C1_TEXT_OF_RA; reflexivity)
             ltac:(unfold FO_P; lia) ltac:(unfold FO_P, SLOT_FRAME; lia)
             ltac:(unfold FO_B256; lia) ltac:(unfold FO_B256, SLOT_FRAME; lia)
             ltac:(right; unfold FO_P, FO_B256; lia) HCA).
    - (* text_of's Pre over the call cut *)
      intros ms Hms.
      pose proof Hms as Hms'.
      destruct Hms' as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc
                        & m & P & N & kbs & mbs & gbs & nb & EQ & FRM & Hi' & Hnb & HN & HLM & HCUR & MI
                        & TM & STK).
      subst ms. cbn [ms_regs ms_mem MState.MS].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      exists (wz P), (wz N).
      destruct (g1_cursor_rng (lg_E g md mk) i P N kbs mbs gbs m OK HLM)
        as (RP1 & RN1 & RPN & RS & RPe & RKr & RNe).
      assert (UP : bv_unsigned (wz P) = P) by (apply unsigned_lit; unfold SLOT_STACK_Z in *; lia).
      assert (UN : bv_unsigned (wz N) = N) by (apply unsigned_lit; unfold SLOT_STACK_Z in *; lia).
      split; [exact HCUR|].
      split; [exact (g1_own_cell (lg_E g md mk) i P N kbs mbs gbs m HLM)|].
      split.
      { rewrite UP, UN.
        destruct HLM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                         HCU & _).
        exact (g1_cursor_bytes m (e_p0 (lg_E g md mk)) (e_pl (lg_E g md mk)) P N HCU). }
      { rewrite UP, UN. exact (g1_cursor_in g md mk i P N kbs mbs gbs m HV OK HLM). }
    - (* the return address 0x13fb8 *)
      intros R F fc m regs' m' c0 c1 own k s t sl HPms HCU HRP Hs10 Hs0 HCAR HPM HCS HTL HSL HSLL HA1 HA2
        HA3 HA4 HAHB HOWN HADV HOWN0 HOWNN.
      exact (g1_tof_adapt g md mk hb i R F fc m regs' m' c0 c1 own k s t sl OK HV HMD HMK HPms HCU HRP
               Hs10 Hs0 HCAR HPM HCS HTL HSL HSLL HA1 HA2 HA3 HA4 HAHB HOWN HADV HOWN0 HOWNN). }
  intros cB (own & k & HCB).
  (* the pure side condition of the return cut, then B *)
  destruct (lg1_cut_and B API g C1_TEXT_OF_RA (opt_hb own k hb) T (own = 0 \/ 1 <= k <= 320)
              (eqv_cl (c1_13fb8 (lg_E g md mk) i (lg_gp g) own)) cB HCB) as [HK HCB'].
  pose proof (lg1_cut_eqv B API g C1_TEXT_OF_RA (opt_hb own k hb) T
                (c1_13fb8 (lg_E g md mk) i (lg_gp g) own) cB HCB') as HCB2.
  eapply SR_bind.
  { apply (g1_segB g md mk (opt_hb own k hb) T i own cB OK); [|exact HCB2].
    intros tt Htt. destruct (Hhp tt Htt) as [H1 H2].
    split; [apply lg1_opt_in; exact H1 | exact H2]. }
  intros cC HCC.
  (* free *)
  eapply SR_bind; [exact (g1_free g md mk hb T i own k cC OK HV HI HT HK HCC)|].
  intros cD HCD.
  (* C: free's return -> the next loop head or the exit *)
  eapply SR_mono; [exact (g1_segC g md mk hb T i cD OK Hhp HCD)|].
  intros c' [H1 | H2]; unfold arm_post; exists hb, T; split; try exact HI.
  - left. split.
    + destruct H1 as (fx' & L & A & regs & mem & md' & _ & _ & _ & (c0 & (Hlt & _) & _)). exact Hlt.
    + exact (cut_mono B API g L_LH hb T _ _ c' (fun ms H => proj2 H) H1).
  - right. exact H2.
Qed.

End G1.

Print Assumptions glue_arm1.
About glue_arm1.
