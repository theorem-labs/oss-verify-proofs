From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import WriterRet pj_parse_c check_no_overread_c check_reject_clean_starved_c check_round_trip_c LLVMFuzzerTestOneInput_c EntryDefs EntrySR EntBase EntGlue EntSegA EntStg EntSQ_Cnt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_reject_clean_starved stage of LLVMFuzzerTestOneInput on the #102 ubsan pin, on the rc = 0 path after
   check_round_trip returned 0 (fuzz_preset.c:832-833). check_reject_clean_starved (0x13c3c) is called at 0x13860 with
   (data, size, took, &doc), doc = sp = S - 112; its contract (check_reject_clean_starved_c @ rw102-crcs
   6d86620145430ef7) needs both flag bytes 0, which the stage has (ent_flags). It returns to 0x13864, which jumps to
   0x137dc: pj_free(&doc) (EntSegA.ent_segE3), the next stage stg_pjf_st. *)

Lemma ecrs1_rk : forall regs0 r1 r2, regs_preserved r1 r2 -> ent_rk regs0 r1 -> ent_rk regs0 r2.
Proof.
  intros regs0 r1 r2 RR (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
  split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
  split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
  split; [etransitivity; [apply (RR 22); unfold callee_saved; lia | exact G22]|].
  split; [etransitivity; [apply (RR 23); unfold callee_saved; lia | exact G23]|].
  split; [etransitivity; [apply (RR 24); unfold callee_saved; lia | exact G24]|].
  split; [etransitivity; [apply (RR 25); unfold callee_saved; lia | exact G25]|].
  split; [etransitivity; [apply (RR 26); unfold callee_saved; lia | exact G26]|].
  etransitivity; [apply (RR 27); unfold callee_saved; lia | exact G27].
Qed.

Lemma ecrs1_gr_doc : forall x took doc t, doc <> 0 -> crcs_growth x took doc t = crcs_growth x took 1 t.
Proof. intros x took doc t H. unfold crcs_growth. rewrite (proj2 (Z.eqb_neq doc 0) H). reflexivity. Qed.

Lemma ecrs1_after_doc : forall F b c x doc t, doc <> 0 -> crs_after_doc F b c x doc t = crs_doc_fold F b c x t.
Proof. intros F b c x doc t H. unfold crs_after_doc. rewrite (proj2 (Z.eqb_neq doc 0) H). reflexivity. Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Lemma ecrs1_rpost_blocks : forall K L A regs mem md E gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  forall a k, In (a, k) (blocks L A) -> ~ gone a k -> In (a, k) (blocks L' A').
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' (_ & _ & _ & _ & _ & _ & _ & UB & PA & _) a k Hin Hg.
  destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
  assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB; [exact Hq0 | exact Hg]).
  rewrite <- (PA q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1).
Qed.

(* The payload facts check_reject_clean_starved needs, from the entry's precondition and frame. *)
Lemma ecrs1_pay : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd D,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  0 < empty < 2 ^ 62 -> Permutation Lam D -> new_blks L0 A0 D ->
  0 < p /\ p + n < 2 ^ 62 /\ Z.of_nat (length pl) = n /\ EMem.bytes_at segs mem p pl /\
  (0 < n -> exists a k, In (a, k) (blocks L A) /\ ~ lin Lam (a + 16) (k - 16) /\ a <= p /\ p + n <= a + k) /\
  (forall i, 0 <= i < n ->
     ~ owned B L A (p + i) /\ ~ alloc_statics (p + i) /\ ~ (errno_addr B <= p + i < errno_addr B + 4)).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd D
    ENT INV HEMP PL NEW.
  pose proof ENT as ((PRE & HNL & BLK & _) & SYMS & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
  pose proof INV as (RS & _ & _ & _ & _ & _ & _ & PAY0 & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  pose proof alloc_ceiling_val as HCV. pose proof alloc_ceiling_lt as HCL.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (BY : EMem.bytes_at segs mem p pl).
  { assert (Hp0 : 0 <= p /\ p + n <= 2 ^ 64).
    { destruct PAY as [(Hn & ->)|(Hn & q & Hq & <-)]; [lia|].
      destruct (rg_blk B API HSEG AX FG L0 A0 mem0 md0 (ptr_addr L0 q) n 0 MR0
        (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) ltac:(lia)) as (_ & H1 & H2 & _). lia. }
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (PAY0 (Z.of_nat i) ltac:(lia)) as E1. pose proof (BLK (Z.of_nat i) ltac:(lia)) as E2.
    rewrite Nat2Z.id in E2. exact (eq_trans E1 E2). }
  destruct PAY as [(Hn & ->)|(Hn & q & Hq & <-)].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [intros Hc; lia|]. intros i Hi. lia.
  - pose proof (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) as Hb0.
    pose proof (PSc _ _ Hb0 Hn (fun h => h)) as HbL.
    destruct (rg_blk B API HSEG AX FG L A mem md (ptr_addr L0 q) n 0 MRc HbL ltac:(lia)) as (_ & H1 & H2 & _).
    destruct (rg_blk_in B API HSEG AX FG L A _ _ HbL) as (q' & Hq' & Eq).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BY|].
    split.
    { intros _. exists (ptr_addr L0 q), n. split; [exact HbL|]. split; [|lia].
      intros Hl. unfold lin in Hl. apply (NEW (ptr_addr L0 q + 16) (n - 16)).
      - exact (Permutation_in _ PL Hl).
      - replace (ptr_addr L0 q + 16 - 16) with (ptr_addr L0 q) by lia. replace (n - 16 + 16) with n by lia. exact Hb0. }
    intros i Hi.
    destruct (rg_blk B API HSEG AX FG L A mem md (ptr_addr L0 q) n i MRc HbL Hi) as (_ & _ & _ & Ho).
    split; [exact Ho|]. split.
    + intros Hs. apply (ax_blocks_img AX L A mem md q' n i MRc Hq' Hi). rewrite Eq.
      exact (proj1 (statics_img B API HSEG AX FG _ Hs)).
    + intros He. apply (ax_blocks_img AX L A mem md q' n i MRc Hq' Hi). rewrite Eq.
      replace (ptr_addr L0 q + i) with (errno_addr B + (ptr_addr L0 q + i - errno_addr B)) by lia.
      apply (errno_img B API HSEG AX FG ERRB). lia.
Qed.

End G.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Variable KW : Z.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis CRS : forall fx' : YK11.FPState, @check_reject_clean_starved_contract fx' rc B API F KW.
Hypothesis HKW : 0 <= KW <= PJ_PARSE_K.
Hypothesis HWL1 : esq_wl1.
Hypothesis HWL2 : esq_wl2.
Hypothesis NEXT : stg_pjf_st (fx := fx) B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_crs1_holds : stg_crs1_st (fx := fx) B API F.
Proof.
  unfold stg_crs1_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 t D cset b4
    ENT INV R1 RK R8 R9 R10 R11 R12 R13 FLG HEMP HEMP2 ROOMS HN CNOW JR TREE HCS CFIN.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FLG as (FL1 & FL2).
  pose proof ENT as ((PRE & HNL & _) & SYMS & _ & _ & SLK & _ & _ & _ & LED0 & CNT0 & HJ & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  pose proof TREE as (PL & NODE & TDL & NEW).
  pose proof alloc_ceiling_val as HCV. pose proof alloc_ceiling_lt as HCL.
  assert (HK : SLOT_K = 14704) by reflexivity.
  assert (SPr : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply EMS.unsigned_lit; lia).
  pose proof (json_read_depth jr_strtod (zb pl) t JR) as DEP. unfold MAXD in DEP.
  assert (HCK : 0 <= CRCS_K KW /\ 112 + CRCS_K KW <= 14704).
  { assert (E : PJ_PARSE_K = ltac:(let v := eval vm_compute in PJ_PARSE_K in exact v)) by reflexivity.
    assert (EF : (FREE_K <=? PJ_PARSE_K) = true) by reflexivity. apply Z.leb_le in EF.
    pose proof HKW as HKW'. rewrite E in HKW'. unfold CRCS_K, CRCS_F. rewrite E. lia. }
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md
    Lam peak (ent_c4 cnt0 pl t cset) b4 regs (CRCS_K KW) ENT INV SPr G4 RET ltac:(lia) ltac:(lia)) as REN.
  destruct (ecrs1_pay B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
    (ent_c4 cnt0 pl t cset) b4 D ENT INV HEMP PL NEW) as (HP0 & HP1 & HPL & HBY & HBLK & HOWN).
  pose proof (esq_wdoc HWL1 HWL2 pl t JR HN) as (WD1 & WD2).
  assert (HC0 : 0 <= cnt0 <= Z.of_nat j * 2 ^ 60) by (pose proof LED0 as (_ & _ & H & _); lia).
  destruct (esq_cnt HWL1 HWL2 cnt0 pl t cset j HC0 HJ JR HN HCS) as (HC4 & _).
  pose proof CNOW as (C1 & C2 & C3).
  destruct (ROOMS HN) as (_ & RM).
  destruct (RM E1 E2 E3 C1 C2 C3) as (_ & RMJ). rewrite JR in RMJ. destruct RMJ as (_ & _ & RMF).
  destruct (RMF cset b4 CFIN) as (RC1 & RC2 & RC3).
  assert (DL : forall a k, In (a, k) D -> In (a, k) Lam)
    by (intros a k H; exact (Permutation_in _ (Permutation_sym PL) H)).
  assert (DOCF : spZ regs0 - 112 = 0 \/
    (json_read jr_strtod (zb pl) = Some t /\ pj_node (ms_segs B) mem (lin Lam) (spZ regs0 - 112) t D /\
     (forall a k, In (a, k) D -> In (a, k) Lam) /\ (spZ regs0 - 112) mod 8 = 0 /\ spZ regs <= spZ regs0 - 112 /\
     Z.of_nat (length (wdoc t false)) + 1 < 2 ^ 24 /\ Z.of_nat (length (wdoc t true)) + 1 < 2 ^ 28 /\
     (depth t <= 32)%nat)).
  { right. split; [exact JR|]. split; [exact NODE|]. split; [exact DL|].
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact WD1|]. split; [exact WD2 | exact DEP]. }
  eapply SR_bind.
  { exact (CRS fx1 L A regs mem md Lam peak (ent_c4 cnt0 pl t cset) b4 p n (ent_took pl) (spZ regs0 - 112) pl t D
      REN R10 R11 R12 R13 (proj1 HKW) ltac:(unfold ent_n in HN; lia) HP0 HP1 HPL HBY HBLK HOWN eq_refl DOCF LED
      (proj2 HC4) RES RC1 (fun H _ => RC2 H ltac:(lia)) (fun H _ => RC3 H ltac:(lia)) FL1 FL2). }
  intros c' (fx2 & L' & A' & regs2 & mem2 & md2 & Lam' & peak' & -> & FRM2 & RP2 & RD2 & LED2 & PERM2 & PK2 & NODE2 &
    RT0 & RTN).
  rewrite R1.
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RR2 & _).
  pose proof (rstep_of_rpost B API HSEG AX FG (CRCS_K KW) L A regs mem md alloc_statics (fun _ _ => False)
    L' A' regs2 mem2 md2 RP2) as STEP.
  rewrite SPr in STEP.
  assert (BND : exists trs Ds, (ent_took pl <> 0 -> crs_parse_left (ent_c4 cnt0 pl t cset) (zb pl) (ent_took pl) trs Ds) /\
      rf_ok F A' (ent_b5 F b4 (ent_c4 cnt0 pl t cset) pl t trs Ds)).
  { unfold ent_b5. destruct (Z.eqb_spec (ent_took pl) 0) as [Ht|Ht].
    - exists [], []. split; [intros H; contradiction|].
      pose proof (RT0 Ht) as H. rewrite ecrs1_after_doc in H by lia. exact H.
    - destruct (RTN Ht) as (tr & D' & CP & RF). exists tr, D'. split; [intros _; exact CP|].
      rewrite ecrs1_after_doc in RF by lia. exact RF. }
  destruct BND as (trs & Ds & CPL & RES2).
  assert (INV2 : ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx2 L' A' mem2 md2 Lam' peak'
      (ent_c4 cnt0 pl t cset + crcs_growth (zb pl) (ent_took pl) 1 t) (ent_b5 F b4 (ent_c4 cnt0 pl t cset) pl t trs Ds)).
  { apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
      (ent_c4 cnt0 pl t cset) b4 (CRCS_K KW) alloc_statics (fun a => exists n0, (fun _ _ => False) a n0)
      fx2 L' A' mem2 md2 Lam' peak' (ent_c4 cnt0 pl t cset + crcs_growth (zb pl) (ent_took pl) 1 t)
      (ent_b5 F b4 (ent_c4 cnt0 pl t cset) pl t trs Ds) ENT INV STEP); try lia.
    - intros a Ha. left. left. exact Ha.
    - intros a Ha Hs. pose proof (ent_statics_lo _ Hs). lia.
    - intros a k _ _ (n0 & H0). exact H0.
    - intros a k Hin _. exact (ecrs1_rpost_blocks B API HSEG FA _ _ _ _ _ _ _ _ _ _ _ _ _ RP2 a k Hin (fun h => h)).
    - exact (proj1 RD2).
    - exact FRM2.
    - rewrite <- (ecrs1_gr_doc (zb pl) (ent_took pl) (spZ regs0 - 112) t ltac:(lia)). exact LED2.
    - exact RES2. }
  pose proof (ecrs1_rk regs0 regs regs2 RR2 RK) as (G2' & G3' & G4' & G22' & G23' & G24' & G25' & G26' & G27').
  destruct (kb_md B API L' A' mem2 md2 M2) as (Hh2 & Hz2).
  eapply (ent_kA B HSEG fx2 regs2 _ mem2 md2 _ _ Hh2 Hz2).
  { unfold rmk. rewrite G2'.
    exact (ent_segE3 (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
      (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14)
      (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20)
      (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26)
      (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
      (@fp_regs fx2) (@fp_csr fx2) mem2 (spZ regs0 - 112)). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem3 regs3 HQ HGr.
  ent_inj HQ R pc' mem3.
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx2 L' A' regs3 mem2 md2 Lam' peak' E1 E2 E3
    t D cset b4 trs Ds ENT INV2).
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; transitivity (getr regs2 3); [reflexivity | exact G3']|].
    split; [rewrite HGr; transitivity (getr regs2 4); [reflexivity | exact G4']|].
    split; [rewrite HGr; transitivity (getr regs2 22); [reflexivity | exact G22']|].
    split; [rewrite HGr; transitivity (getr regs2 23); [reflexivity | exact G23']|].
    split; [rewrite HGr; transitivity (getr regs2 24); [reflexivity | exact G24']|].
    split; [rewrite HGr; transitivity (getr regs2 25); [reflexivity | exact G25']|].
    split; [rewrite HGr; transitivity (getr regs2 26); [reflexivity | exact G26']|].
    rewrite HGr; transitivity (getr regs2 27); [reflexivity | exact G27'].
  - rewrite HGr. reflexivity.
  - exact HEMP.
  - exact HEMP2.
  - exact ROOMS.
  - exact HN.
  - exact CNOW.
  - exact JR.
  - split; [exact (Permutation_trans PERM2 PL)|]. split; [exact (NODE2 ltac:(lia))|]. split; [exact TDL | exact NEW].
  - exact HCS.
  - exact CFIN.
  - exact CPL.
Qed.

End S.
