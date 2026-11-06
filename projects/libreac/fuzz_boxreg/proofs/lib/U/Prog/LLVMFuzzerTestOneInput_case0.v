From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep
  range_free_c lowest_free_base_c printf_facts_c snprintf_c reac_boxreg_set_name_c reac_boxreg_declare_c
  reac_boxreg_declare_inv bcmp_c strncmp_c read_name_c read_name.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require range_free range_taken lowest_free_base memset bcmp
  strncmp reac_boxreg_declare.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_res LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_rn
  LLVMFuzzerTestOneInput_c0a LLVMFuzzerTestOneInput_c0b LLVMFuzzerTestOneInput_c0c.
Import ListNotations.
Open Scope Z_scope.

Lemma c0_nch_range : forall pl, 0 <= c0_nch pl < 256.
Proof.
  intros [|x pl]; cbn [c0_nch]; [lia|]. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R.
  lia.
Qed.

Lemma c0_base_range : forall pl, -128 <= c0_base pl < 128.
Proof.
  intros [|x [|y pl]]; cbn [c0_base]; try lia.
  pose proof (bv_unsigned_in_range 8 y) as R. change (bv_modulus 8) with 256 in R.
  destruct (c0_byte_signed y) as [[E H]|[E H]]; rewrite E; lia.
Qed.

Lemma c0_used_split : forall pl, Z.of_nat (length (firstn 2 pl)) = c0_used pl.
Proof. intros pl. rewrite length_firstn. unfold c0_used. lia. Qed.

Lemma c0_skip_len : forall pl, Z.of_nat (length (skipn 2 pl)) = Z.of_nat (length pl) - c0_used pl /\
  0 <= c0_used pl <= Z.of_nat (length pl).
Proof. intros pl. rewrite length_skipn. unfold c0_used. lia. Qed.

Lemma c0_mid : forall m A pre c post,
  rw_cells rsegs m A (pre ++ c :: post) -> bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros m A pre c post [[Hwf Hb] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1.
  cbn [cells_bytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Section C0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SLACK : block_slack_present B API.
Hypothesis SNPRINTF : snprintf_contract.

Theorem llvm_case0_ok : llvm_case_ok B API 0.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HT HPC.
  match goal with |- SR _ _ ?Q => set (Pk := Q) end.
  destruct HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & Ec & Hfrm & RB &
    E9 & E18 & E19 & E20 & E21 & FRC & Hi & Hinn & Hpip & Hipn & Hop & RWR & INV & Hfab & AL & Hk).
  assert (Epc : Z_to_bv 64 (llvm_case_pc (Z.land op 3)) = Z_to_bv 64 0x12df4).
  { destruct HPC as (ms & md1 & Ec' & Ep). rewrite Ec in Ec'. injection Ec' as Ems Emd. rewrite <- Ems in Ep. exact Ep. }
  subst c. rewrite Epc. clear HPC Epc.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hstk & Hra & Hpre & Hsn & Hsp47 & Hres0 & Hroom & Hro0
    & Hrelro & Hfrm0 & Hn26).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  unfold LLVM_K, LLVM_FRAME in Hstk.
  subst fab.
  destruct AL as (FR & MINE & RES).
  destruct RB as (E2 & E3 & E4 & E8 & E22 & E23 & E24 & E25 & E26 & E27).
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR) as [Hh Hl].
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. pose proof YM05.alloc_ceiling_lt as Hlt.
  assert (Hn0 : 0 < n) by lia.
  assert (Hpn : 4096 <= p /\ p + n <= spZ regs0 - stk).
  { destruct Hpl as [[En _] | [Hn (q & Hq & Hqp)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
    rewrite Hqp in H1, H2. lia. }
  pose proof INV as ((HL & HB1 & HB2' & _) & _). unfold boxreg_B1 in HB1. unfold boxreg_B2 in HB2'.
  pose proof MINE as (Hrin & Hr0 & Hrd).
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 r HM MINE ltac:(lia)) as (_ & _ & Hr1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + 287) HM MINE ltac:(lia)) as (_ & _ & Hr2 & _).
  assert (Hr16 : r mod 16 = 0).
  { pose proof Hrin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
    exact (mr_blocks_aligned B _ (aa_laws API) L A mem md q 288 HM Hqin). }
  assert (Hr8 : r mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HIF : pf_img_free r 288).
  { intros j Hj sg Hsg. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + j) HM MINE ltac:(lia))
      as (_ & Hn' & _). exact (lf_not_img_res B (r + j) SEGS Hn' sg Hsg). }
  set (S := spZ regs0) in *.
  assert (Hspa : (S - 464) mod 16 = 0).
  { replace (S - 464) with (S + (-29) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (S - 464)) by exact E2.
  assert (Esp : bv_unsigned (reg_get regs 2) = S - 464) by (rewrite G2; apply unsigned_lit; lia).
  destruct (sg_list mem (Z.to_nat (inn - 1)) (ip + 1) ltac:(lia) ltac:(lia)) as (pl & Lpl & HPL).
  { intros x Hx. apply (llvm_payload_read B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x CTX FR). lia. }
  assert (Hlen : Z.of_nat (length pl) = inn - 1) by (rewrite Lpl; lia).
  set (cs0 := [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); CB 8 j1; C8 (Z_to_bv 64 i);
               C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm]).
  assert (Hcs0 : Z.of_nat (cells_size cs0) = 344) by reflexivity.
  change (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 (bx_fabric bs)) :: CB 8 j1 :: C8 (Z_to_bv 64 i) ::
          C8 (Z_to_bv 64 (bx_n bs)) :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 (ip + 1)) ::
          C8 (Z_to_bv 64 (inn - 1)) :: llvm_saved_cells regs0)
    with (lf_cells regs0 cs0 (ip + 1) (inn - 1)) in FRC.
  pose proof (proj1 (lf_cells_split mem (S - 464) regs0 cs0 (ip + 1) (inn - 1) Hcs0) FRC) as (CF1 & CF3 & CF4).
  assert (HPLn : bytes_at rsegs (normalize rsegs mem) (ip + 1) pl) by exact (bytes_at_normalize rsegs mem _ _ Hro HPL).
  assert (CF3n : rw_cells rsegs (normalize rsegs mem) (S - 464 + 344)
                   [C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (Z.of_nat (length pl)))]).
  { rewrite Hlen. apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact CF3].
    intros x Hx Hix. pose proof (lf_in_img_top B _ SEGS Hix). change (Z.of_nat (cells_size _)) with 16 in Hx. lia. }
  rewrite SEGS.
  eapply (llvm_run_norm fx' regs (Z_to_bv 64 0x12df4) mem md); [exact Hh | exact Hl | exact Hro | | |].
  { unfold Regs6ss.mkR_of.
    assert (R18 : reg_get regs 18 = Z_to_bv 64 (1 + Z.of_nat (length pl)))
      by (rewrite Hlen; replace (1 + (inn - 1)) with inn by lia; exact E18).
    assert (R19 : reg_get regs 19 = Z_to_bv 64 (ip + 1)) by exact E19.
    assert (R20 : reg_get regs 20 = Z_to_bv 64 ip) by exact E20.
    assert (R21 : reg_get regs 21 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite Hlen; exact E21).
    assert (R22 : reg_get regs 22 = Z_to_bv 64 1) by exact E22.
    rewrite R18, R19, R20, R21, R22.
    eapply llvm_c0_evt1.
    - lia.
    - rewrite Esp. lia.
    - rewrite Esp. lia.
    - exact HPLn.
    - rewrite Esp. exact CF3n.
    - exact (mem_inv_normalize rsegs mem). }
  { intros ms (a1' & m'' & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m0' (a1' & m'' & HE & MU & WM & MI' & CW') regs1 m1 Hx Hrel Hsame.
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  assert (MU' : munch [(S - 464 + 344, S - 464 + 360)] mem m1).
  { pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m1 m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU) as M.
    rewrite Esp in M. exact M. }
  assert (WM' : wmono rsegs mem m1)
    by exact (wmono_rel rsegs mem (normalize rsegs mem) m1 m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
  assert (Hro1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs mem m1 Hro Hsame).
  assert (FR1 : lf_fr B API stk S L0 A0 mem0 md0 L A m1 md).
  { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | lia | lia | exact MU' | exact WM' | exact Hro1 |].
    intros x Hx0 NO. left. destruct (Z_le_dec (S - 464 + 344) x); destruct (Z_lt_dec x (S - 464 + 360)); try lia;
      exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
  assert (CF1' : rw_cells rsegs m1 (S - 464) cs0).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ CF1 MU' WM'). rewrite Hcs0.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CF4' : rw_cells rsegs m1 (S - 464 + 360) (llvm_saved_cells regs0)).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ CF4 MU' WM').
    change (Z.of_nat (cells_size (llvm_saved_cells regs0))) with 104. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CF3' : rw_cells rsegs m1 (S - 464 + 344)
    [C8 (Z_to_bv 64 (ip + 1 + c0_used pl)); C8 (Z_to_bv 64 (Z.of_nat (length (skipn 2 pl))))]).
  { pose proof (lf_rw_cells_rel m1 m'' _ _ Hrel CW') as H. rewrite Esp in H. exact H. }
  assert (RWR1 : rw_cells rsegs m1 r [CB 288 bs]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ RWR MU' WM'). change (Z.of_nat (cells_size _)) with 288.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HPL1 : bytes_at rsegs m1 (ip + 1 + c0_used pl) (skipn 2 pl)).
  { pose proof (bytes_at_transport rsegs _ mem m1 _ _ HPL MU' ltac:(cbn [disjoint_from]; split; [lia | exact I])) as H.
    rewrite <- (firstn_skipn 2 pl) in H. apply (proj1 (bytes_at_app rsegs m1 _ _ _)) in H. destruct H as [_ H].
    rewrite c0_used_split in H. exact H. }
  assert (G1' : YK11.getr regs1 1 = Z_to_bv 64 0x12f5c) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2' : YK11.getr regs1 2 = Z_to_bv 64 (S - 464)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E2).
  assert (G4' : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E4).
  assert (G10' : YK11.getr regs1 10 = Z_to_bv 64 (S - 464 + 344)).
  { rewrite (lf_getr_eqv _ _ _ Hx).
    change (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + 344) = Z_to_bv 64 (S - 464 + 344)). rewrite Esp. reflexivity. }
  assert (Q3 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E3).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 r) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E8).
  assert (Q9 : YK11.getr regs1 9 = Z_to_bv 64 op) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E9).
  assert (Q19 : YK11.getr regs1 19 = Z_to_bv 64 (c0_nch pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (Q20 : YK11.getr regs1 20 = Z_to_bv 64 (c0_base pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (Q22 : YK11.getr regs1 22 = Z_to_bv 64 (c0_base pl * 2 ^ 56)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (Q23 : YK11.getr regs1 23 = Z_to_bv 64 (bx_fabric bs)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E23).
  assert (Q24 : YK11.getr regs1 24 = Z_to_bv 64 (-1 - (S - 464 + 48))) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E24).
  assert (Q25 : YK11.getr regs1 25 = Z_to_bv 64 (-1 - r)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E25).
  assert (Q26 : YK11.getr regs1 26 = Z_to_bv 64 (S - 464 + 48)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E26).
  assert (Q27 : YK11.getr regs1 27 = Z_to_bv 64 336) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E27).
  pose proof (rn_k_range (skipn 2 pl)) as Hkr.
  assert (ROOM : room_slots (sb_malloc b LLVM_REQ) (rn_k (skipn 2 pl) + 1)).
  { exact (llvm_name_room B API stk empty L0 A0 regs0 mem0 md0 ra p n b (rn_k (skipn 2 pl) + 1) CTX
      ltac:(unfold LLVM_REQ; lia)). }
  refine (llvm_rn_glue B API MALLOC ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs1 m1 md L A r bs
    (sb_malloc b LLVM_REQ) 0x12f5c cs0 (ip + 1 + c0_used pl) (skipn 2 pl) Pk Hn0 Hcs0 FR1 MINE RES ROOM G1'
    _ G2' G4' G10' _ RWR1 HPL1 _ _ _).
  { apply ret_ok_even. reflexivity. }
  { apply (proj2 (lf_cells_split m1 (S - 464) regs0 cs0 _ _ Hcs0)). auto. }
  { pose proof (c0_used_split pl). unfold c0_used in *. lia. }
  { rewrite length_skipn. pose proof (c0_used_split pl). unfold c0_used in *. lia. }
  intros L' A' regs' mem' md' s FR2 MINE2 MINEs Hsr RES2 Hrp G10s HBs CF2x CR2.
  set (ip2 := ip + 1 + c0_used pl + Z.min (Z.of_nat (length (skipn 2 pl))) 1 + rn_k (skipn 2 pl)) in *.
  set (ln2 := Z.of_nat (length (skipn 2 pl)) - Z.min (Z.of_nat (length (skipn 2 pl))) 1 - rn_k (skipn 2 pl)) in *.
  assert (Hip2 : ip2 + ln2 = p + n /\ 0 <= ln2 /\ p <= ip2).
  { unfold ip2, ln2. pose proof (c0_skip_len pl). lia. }
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hblk2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR2) as [Hh2 Hl2].
  pose proof MINEs as (Hsin & Hs0' & Hsd).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 2 pl) + 1) s HM2 MINEs ltac:(lia))
    as (_ & _ & Hs1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 2 pl) + 1) (s + rn_k (skipn 2 pl)) HM2 MINEs
    ltac:(lia)) as (_ & _ & Hs2 & _).
  destruct (llvm_name_parts B API SLACK L' A' mem' md' s (rn_k (skipn 2 pl)) (bsub (skipn 2 pl) 1 (rn_k (skipn 2 pl)))
    HM2 Hsin ltac:(lia) ltac:(lia) ltac:(lia) HBs (rn_name_len (skipn 2 pl))) as (slack & HNB & Hstrl & Hmod & Hnl).
  set (nmstr := nm_str (bsub (skipn 2 pl) 1 (rn_k (skipn 2 pl)) ++ [Z_to_bv 8 0])) in *.
  destruct (llvm_guards B API stk empty L0 A0 regs0 mem0 md0 ra p n b L' A' mem' md' CTX HM2) as (HG1 & cn & HG2).
  pose proof (nm_len nmstr slack) as HNL.
  assert (HE8 : 8 * ((s + rn_k (skipn 2 pl) + 1 + 7) / 8) <= YM05.alloc_ceiling)
    by (apply nm_up8; [lia | Z.div_mod_to_equations; lia]).
  assert (Hnr' : s + Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)) <= r \/ r + 288 <= s).
  { destruct Hsr as [Hsr|Hsr]; [left | right; lia].
    pose proof (nm_up8 (s + rn_k (skipn 2 pl) + 1) r ltac:(lia) ltac:(Z.div_mod_to_equations; lia)). lia. }
  assert (F2 : reg_get regs' 2 = Z_to_bv 64 (S - 464)) by (lf_reg Hrp regs' 2 G2').
  assert (F3 : reg_get regs' 3 = reg_get regs0 3) by (lf_reg Hrp regs' 3 Q3).
  assert (F4 : reg_get regs' 4 = reg_get regs0 4) by (lf_reg Hrp regs' 4 G4').
  assert (F8 : reg_get regs' 8 = Z_to_bv 64 r) by (lf_reg Hrp regs' 8 Q8).
  assert (F9 : reg_get regs' 9 = Z_to_bv 64 op) by (lf_reg Hrp regs' 9 Q9).
  assert (F10 : reg_get regs' 10 = Z_to_bv 64 s) by exact G10s.
  assert (F19 : reg_get regs' 19 = Z_to_bv 64 (c0_nch pl)) by (lf_reg Hrp regs' 19 Q19).
  assert (F20 : reg_get regs' 20 = Z_to_bv 64 (c0_base pl)) by (lf_reg Hrp regs' 20 Q20).
  assert (F22 : reg_get regs' 22 = Z_to_bv 64 (c0_base pl * 2 ^ 56)) by (lf_reg Hrp regs' 22 Q22).
  assert (F23 : reg_get regs' 23 = Z_to_bv 64 (bx_fabric bs)) by (lf_reg Hrp regs' 23 Q23).
  assert (F24 : reg_get regs' 24 = Z_to_bv 64 (-1 - (S - 464 + 48))) by (lf_reg Hrp regs' 24 Q24).
  assert (F25 : reg_get regs' 25 = Z_to_bv 64 (-1 - r)) by (lf_reg Hrp regs' 25 Q25).
  assert (F26 : reg_get regs' 26 = Z_to_bv 64 (S - 464 + 48)) by (lf_reg Hrp regs' 26 Q26).
  assert (F27 : reg_get regs' 27 = Z_to_bv 64 336) by (lf_reg Hrp regs' 27 Q27).
  assert (Esp' : bv_unsigned (reg_get regs' 2) = S - 464) by (rewrite F2; apply unsigned_lit; lia).
  pose proof (proj1 (lf_cells_split mem' (S - 464) regs0 cs0 ip2 ln2 Hcs0) CF2x) as (D1 & D3 & D4).
  assert (NOIMG : forall a x, LF_RES_TOP <= a -> 0 <= x -> ~ in_img B (a + x))
    by (intros a x Ha Hxw Hix; pose proof (lf_in_img_top B _ SEGS Hix); lia).
  set (M := MemNorm.normalize_cj rsegs mem').
  assert (CWM : rw_cells rsegs M (bv_unsigned (reg_get regs' 2)) (cs0 ++ [C8 (Z_to_bv 64 ip2); C8 (Z_to_bv 64 ln2)])).
  { rewrite Esp'. apply (nm_rw_cj B); [exact SEGS | exact Hro2 | | intros x Hxw; apply NOIMG; lia |].
    - exact (top_rwc_join mem' (S - 464) cs0 _ (S - 464 + 344) D1 ltac:(rewrite Hcs0; lia) D3).
    - change (Z.of_nat (cells_size _)) with 360. unfold TASK_SIZE. lia. }
  assert (HPM : bytes_at rsegs M (bv_unsigned (reg_get regs' 2) + 48) bs).
  { pose proof (c0_mid M _ [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); CB 8 j1; C8 (Z_to_bv 64 i);
      C8 (Z_to_bv 64 (bx_n bs))] (CB 288 bs) [CB 8 jm; C8 (Z_to_bv 64 ip2); C8 (Z_to_bv 64 ln2)] CWM) as H.
    cbn [cbytes] in H. rewrite ?app_nil_r in H. exact H. }
  unfold cs0 in CWM. cbn [app] in CWM.
  assert (Hsp16 : bv_unsigned (reg_get regs' 2) mod 16 = 0) by (rewrite Esp'; exact Hspa).
  assert (CRM : rw_cells rsegs M r [CB 288 bs]).
  { apply (nm_rw_cj B); [exact SEGS | exact Hro2 | exact CR2 | |].
    - intros x Hxw. change (Z.of_nat (cells_size _)) with 288 in Hxw.
      destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' r 288 (r + x) HM2 MINE2 ltac:(lia)) as (_ & N & _).
      exact N.
    - change (Z.of_nat (cells_size _)) with 288. unfold TASK_SIZE. lia. }
  assert (HrM : bytes_at rsegs M r bs).
  { destruct CRM as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (HwM : wr_at rsegs M r 288) by (destruct CRM as [_ Hw]; exact Hw).
  assert (STM : Frame.stk rsegs M (S - stk) (bv_unsigned (reg_get regs' 2))).
  { rewrite Esp'. apply (nm_stk_cj B); [exact SEGS | exact Hro2 | lia | unfold TASK_SIZE; lia |].
    intros a Ha. rewrite <- SEGS. apply Hstw2. lia. }
  assert (HNBM : bytes_at rsegs M s (pf_bytes (nmstr ++ [0]) ++ slack)).
  { apply nm_bytes_cj; [exact Hro2 | exact HNB | rewrite HNL; unfold TASK_SIZE; lia]. }
  assert (HG1M : bytes_at rsegs M GOT_GUARD (le8 (Z_to_bv 64 GUARD)))
    by (apply nm_bytes_cj; [exact Hro2 | exact HG1 | rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia]).
  assert (HG2M : bytes_at rsegs M GUARD (le8 cn))
    by (apply nm_bytes_cj; [exact Hro2 | exact HG2 | rewrite length_le8; unfold GUARD, TASK_SIZE; lia]).
  assert (MIM : mem_inv rsegs M)
    by exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem')).
  assert (TMM : MemNorm.task_mem rsegs M)
    by exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem')).
  assert (Hnlo' : s + Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)) <= S - stk) by lia.
  eapply (llvm_run_norm_cj _ regs' (Z_to_bv 64 0x12f5c) mem' md'); [exact Hh2 | exact Hl2 | exact Hro2 | | |].
  { unfold Regs6ss.mkR_of. rewrite F8, F9, F10, F19, F20, F22, F23, F25. fold M.
    eapply llvm_c0_k12f5c with (lo := S - stk) (r := r) (nch := c0_nch pl) (base := c0_base pl) (op := op) (nm := s)
      (i := i) (q := ip2) (c := ln2) (j0 := j0) (j1 := j1) (bs := bs) (jm := jm)
      (NB := pf_bytes (nmstr ++ [0]) ++ slack) (slack := slack) (s := nmstr)
      (canary := cn) (nl := Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack))) (m0 := M);
      first [ exact range_free.range_free_holds
            | exact (reac_boxreg_declare.reac_boxreg_declare_holds range_taken.range_taken_holds
                       (lowest_free_base.lowest_free_base_holds range_taken.range_taken_holds) memset.memset_holds
                       SNPRINTF)
            | exact bcmp.bcmp_holds | exact strncmp.strncmp_holds | apply c0_nch_range | apply c0_base_range
            | apply nm_str_ok | apply munch_refl | apply wmono_refl | exact Hfrm | assumption | reflexivity | lia ]. }
  { intros ms HQ.
    destruct HQ as (t0q & t1q & t2q & s1q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q
      & t3q & t4q & t5q & t6q & Fq & fcq & mq & bsq & j0q & j1q & -> & _).
    do 5 eexists. reflexivity. }
  intros R F pc' fc m0' HQ regs2 m2 Hx2 Hrel2 Hsame2.
  destruct HQ as (t0q & t1q & t2q & s1q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q
    & t3q & t4q & t5q & t6q & Fq & fcq & mq & bs' & j0' & j1' & HE & Hfc' & MU2 & WM2 & HBr & HWr & CW2 & INV' & Hfab'
    & KEPT).
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  pose proof (MemNorm.mem_rel_cj_normalize rsegs mem' Hro2) as HRn.
  assert (MU2' : munch [(S - stk, S - 464 + 32); (r, r + 288)] mem' m2).
  { pose proof (MemNorm.munch_rel_cj rsegs _ mem' _ m2 mq HRn Hrel2 Hsame2 MU2) as Mx. rewrite Esp' in Mx. exact Mx. }
  assert (WM2' : wmono rsegs mem' m2) by exact (MemNorm.wmono_rel_cj rsegs mem' _ m2 mq HRn Hrel2 Hsame2 WM2).
  assert (Hro3 : ro_agree rsegs m2) by exact (MemNorm.ro_agree_same_cj rsegs mem' m2 Hro2 Hsame2).
  assert (FR3 : lf_fr B API stk S L0 A0 mem0 md0 L' A' m2 md').
  { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR2 | lia | lia | exact MU2' | exact WM2' | exact Hro3 |].
    intros x Hx0 NO.
    destruct (Z_le_dec (S - stk) x); destruct (Z_lt_dec x S); try (left; lia).
    all: right; exists r, 288; split; [exact MINE2|];
      destruct (Z_le_dec r x); destruct (Z_lt_dec x (r + 288)); try lia;
      exfalso; apply NO; cbn [Frame.outside]; repeat split; lia. }
  set (csf := [CB 8 j0'; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bx_fabric bs)); CB 8 j1'; C8 (Z_to_bv 64 i);
               C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 ip2); C8 (Z_to_bv 64 ln2)]).
  assert (CFm : rw_cells rsegs m2 (S - 464) (csf ++ llvm_saved_cells regs0)).
  { apply (top_rwc_join m2 (S - 464) csf _ (S - 464 + 360)).
    - pose proof (nm_rw_rel_cj m2 mq _ _ Hrel2 CW2) as H. rewrite Esp' in H. exact H.
    - reflexivity.
    - apply (rw_cells_transport rsegs _ mem' m2 _ _ D4 MU2' WM2').
      change (Z.of_nat (cells_size (llvm_saved_cells regs0))) with 104. cbn [disjoint_from]. repeat split; lia. }
  assert (CRm : rw_cells rsegs m2 r [CB 288 bs']).
  { pose proof INV' as ((HL' & _) & _).
    split; [split; [cbn; split; [exact HL' | exact I] |] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (MemNorm.bytes_at_rel_cj rsegs m2 mq r bs' Hrel2 HBr).
    - change (Z.of_nat (cells_size _)) with 288. exact (MemNorm.wr_at_rel_cj rsegs m2 mq r 288 Hrel2 HWr). }
  assert (H2 : YK11.getr regs2 2 = Z_to_bv 64 (S - 464)) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F2).
  assert (H3 : YK11.getr regs2 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F3).
  assert (H4 : YK11.getr regs2 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F4).
  assert (H8 : YK11.getr regs2 8 = Z_to_bv 64 r) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  assert (H23 : YK11.getr regs2 23 = Z_to_bv 64 (bx_fabric bs)) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  assert (H24 : YK11.getr regs2 24 = Z_to_bv 64 (-1 - (S - 464 + 48))) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F24).
  assert (H25 : YK11.getr regs2 25 = Z_to_bv 64 (-1 - r)) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  assert (H26 : YK11.getr regs2 26 = Z_to_bv 64 (S - 464 + 48)) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F26).
  assert (H27 : YK11.getr regs2 27 = Z_to_bv 64 336) by (rewrite (lf_getr_eqv _ _ _ Hx2); exact F27).
  assert (G10'' : YK11.getr regs2 10 = Z_to_bv 64 s) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  assert (G1'' : YK11.getr regs2 1 = Z_to_bv 64 0x13284) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  refine (llvm_free_glue B API FREE ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs2 m2 md' L' A' r bs' s
    (rn_k (skipn 2 pl) + 1) (sb_malloc (sb_malloc b LLVM_REQ) (rn_k (skipn 2 pl) + 1)) 0x13284
    (csf ++ llvm_saved_cells regs0) Pk FR3 MINE2 MINEs ltac:(lia) RES2 G1'' _ H2 H4 G10'' CFm _ CRm _).
  { apply ret_ok_even. reflexivity. }
  { reflexivity. }
  intros L3 A3 regs3 mem3 md3 FR4 MINE3 RES3 Hrp3 CF3x CR3.
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR4) as [Hh3 Hl3].
  assert (U2 : reg_get regs3 2 = Z_to_bv 64 (S - 464)) by (lf_reg Hrp3 regs3 2 H2).
  assert (U3 : reg_get regs3 3 = reg_get regs0 3) by (lf_reg Hrp3 regs3 3 H3).
  assert (U4 : reg_get regs3 4 = reg_get regs0 4) by (lf_reg Hrp3 regs3 4 H4).
  assert (U8 : reg_get regs3 8 = Z_to_bv 64 r) by (lf_reg Hrp3 regs3 8 H8).
  assert (U23 : reg_get regs3 23 = Z_to_bv 64 (bx_fabric bs)) by (lf_reg Hrp3 regs3 23 H23).
  assert (U24 : reg_get regs3 24 = Z_to_bv 64 (-1 - (S - 464 + 48))) by (lf_reg Hrp3 regs3 24 H24).
  assert (U25 : reg_get regs3 25 = Z_to_bv 64 (-1 - r)) by (lf_reg Hrp3 regs3 25 H25).
  assert (U26 : reg_get regs3 26 = Z_to_bv 64 (S - 464 + 48)) by (lf_reg Hrp3 regs3 26 H26).
  assert (U27 : reg_get regs3 27 = Z_to_bv 64 336) by (lf_reg Hrp3 regs3 27 H27).
  apply (llvm_run (mkFP Fq fcq) regs3 (Z_to_bv 64 0x13284) mem3 md3
    (fun ms => exists R, ms = MS R Fq (Z_to_bv 64 0x13440) fcq None mem3 (YK11.seg_rom rsegs) /\
       reg_get R 19 = Z_to_bv 64 ((-1) mod 2 ^ 32) /\ reg_get R 22 = Z_to_bv 64 1 /\
       forall x, x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ 23 <= x <= 27 ->
         reg_get R (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x)));
    [exact Hh3 | exact Hl3 | | |].
  { unfold Regs6ss.mkR_of. step. step. step. step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros x Hxc. destruct Hxc as [->|[->|[->|[->|Hxc]]]]; try reflexivity.
    assert (Hc : x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
    destruct Hc as [->|[->|[->|[->| ->]]]]; reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H19 & H22 & Hcs) regs4 Hx4.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. unfold Pk. exists (Datatypes.S k).
  exists (mkFP Fq fcq), regs4, mem3, md3, L3, A3, r, (bx_fabric bs), ip2, ln2, bs, bs', (-1), j0', j1', jm.
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfc'|].
  split.
  { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx4).
    split; [lf_reg2 Hcs R' 2 U2|]. split; [lf_reg2 Hcs R' 3 U3|]. split; [lf_reg2 Hcs R' 4 U4|].
    split; [lf_reg2 Hcs R' 8 U8|]. split; [exact H22|]. split; [lf_reg2 Hcs R' 23 U23|].
    split; [lf_reg2 Hcs R' 24 U24|]. split; [lf_reg2 Hcs R' 25 U25|]. split; [lf_reg2 Hcs R' 26 U26 | lf_reg2 Hcs R' 27 U27]. }
  split; [rewrite (lf_getr_eqv _ _ _ Hx4); exact H19|].
  split; [exact CF3x|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact INV|]. split; [reflexivity|].
  split; [exact CR3|]. split; [exact INV'|]. split; [exact Hfab'|]. split; [exact KEPT|].
  split; [split; [exact FR4 | split; [exact MINE3 | exact (llvm_name_back A3 b (rn_k (skipn 2 pl) + 1) RES3)]] | lia].
Qed.

End C0.
