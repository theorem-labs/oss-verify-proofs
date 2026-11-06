From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 Contract FrameAPI KindBGlue AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem Frame Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_cut uslot_seg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_preds uslot_transport uslot_record.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import printf_facts_c snprintf_c reac_box_name_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import memcpy_c find_entry_c role_of_c reac_hunt_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import check_sighting_c reac_disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_classify_on_segment_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_gate_should_push_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_step_c reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_role_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_exit uslot_R0_R3 uslot_frame uslot_step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_sE uslot_sE2 uslot_sB1 uslot_sB2a uslot_sB2b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_sB3a uslot_sLatch uslot_sX uslot_steps.
Import ListNotations.
Open Scope Z_scope.

Lemma rsegs_nn : rsegs <> [].
Proof. discriminate. Qed.

Ltac brom := lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_compute; reflexivity end.

Lemma js_rom : forall j, (j < 24)%nat ->
  seg_rom rsegs (Z_to_bv 64 (JSON_SCALAR_L + Z.of_nat j)) = nth_error js_table j.
Proof. intros j Hj. do 24 (destruct j as [|j]; [brom|]). lia. Qed.

Lemma bn_rom : forall j, (j < 24)%nat ->
  seg_rom rsegs (Z_to_bv 64 (BN_TS + Z.of_nat j)) = nth_error bn_table j.
Proof. intros j Hj. do 24 (destruct j as [|j]; [brom|]). lia. Qed.

Lemma gg_keep : forall k, (k < 8)%nat -> U.MemNorm.cj_drop rsegs (Z_to_bv 64 (GOT_GUARD + Z.of_nat k)) = false.
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Lemma gd_keep : forall k, (k < 8)%nat -> U.MemNorm.cj_drop rsegs (Z_to_bv 64 (GUARD + Z.of_nat k)) = false.
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Lemma mrd_keep_rom : forall mem m0 x, U.MemNorm.mem_rel_cj rsegs mem m0 ->
  Mem.mrd rsegs mem x = seg_rom rsegs x -> Mem.mrd rsegs m0 x = seg_rom rsegs x.
Proof.
  intros mem m0 x HR H. destruct (U.MemNorm.cj_drop rsegs x) eqn:E.
  - unfold Mem.mrd. rewrite (U.MemNorm.mem_rel_cj_drop rsegs mem m0 x HR E). reflexivity.
  - unfold Mem.mrd in *. rewrite (U.MemNorm.mem_rel_cj_keep rsegs mem m0 x HR E). exact H.
Qed.

Lemma mbyte_keep : forall mem m0 a, U.MemNorm.mem_rel_cj rsegs mem m0 ->
  U.MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false -> mbyte rsegs m0 a = mbyte rsegs mem a.
Proof. intros mem m0 a HR E. unfold mbyte. rewrite (U.MemNorm.mem_rel_cj_keep rsegs mem m0 _ HR E). reflexivity. Qed.

Lemma pw_hd : forall a n hb l a' n', pairwise YO0f.ranges_disjoint (((a, n) :: hb) ++ l) -> In (a', n') hb ->
  a + n <= a' \/ a' + n' <= a.
Proof.
  intros a n hb l a' n' D Hin. cbn [app pairwise] in D. destruct D as [D _].
  specialize (D (a', n') (in_or_app _ _ _ (or_introl Hin))). unfold YO0f.ranges_disjoint in D. cbn in D. exact D.
Qed.

Section Run.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables (K S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b0 : sbound).
Hypothesis HSEGS : ms_segs B = rsegs.
Hypothesis HAX : AllocExtra B (aa_MR API).
Hypothesis HKS : alloc_ceiling + K <= S.
Hypothesis HK : 0 <= K.
Hypothesis HS : S <= 2 ^ 47.
Hypothesis HTHR : @sk_threaded SK = 0x51cb0 + 1.
Hypothesis HLOCK : @sk_ofl_lock SK = 0x520d8.
Hypothesis HHEAD : @sk_ofl_head SH = 0x520e0.
Hypothesis HFA : forall fx : FPState, @frame_allocator rc fx B API.
Hypothesis HMAL : ms_malloc B = 0x17aec.
Hypothesis HFRE : ms_free B = 0x179ac.
Hypothesis HLK : ms_lock B = 0x51d20.
Hypothesis HLIBC : ms_libc B = 0x51cb0.
Hypothesis HGG : ms_got_guard B = 0x206a0.
Hypothesis HGD : ms_guard B = 0x51c90.
Hypothesis HCTX : ms_ctx B = 0x51d28.
Hypothesis HTP : ms_tp B = 0x31a20.
Hypothesis HERR : ms_errno_off B = -164.
Hypothesis HVML : ms_vmlock B = None.
Hypothesis HDBL : ms_debruijn_len B = 32.
Hypothesis HDB : ms_debruijn B = 0x10600.
Hypothesis HSC : ms_size_classes B = 0x10620.
Hypothesis HSMC : ms_small_cnt B = 0x10680.
Hypothesis HMDC : ms_med_cnt B = 0x1069b.
Hypothesis TIC : reac_disco_table_init_contract.
Hypothesis GIC : reac_disco_gate_init_contract.
Hypothesis LIC : reac_disco_peer_lock_init_contract.
Hypothesis HIC : reac_hunt_init_contract.
Hypothesis PIC : reac_hunt_pin_contract.
Hypothesis SIC : reac_hunt_silence_proven_contract.
Hypothesis AGE : reac_disco_table_age_contract.
Hypothesis CTC : check_table_contract.
Hypothesis SERA : uslot_ser_chain_A.
Hypothesis SERB : uslot_ser_chain_B.
Hypothesis HTC : reac_hunt_step_contract.
Hypothesis VNC : reac_hunt_verdict_name_contract.
Hypothesis RLC : reac_hunt_role_contract.
Hypothesis HAC : reac_hunt_heard_anything_contract.
Hypothesis MC : memcpy_contract.
Hypothesis FEC : find_entry_contract.
Hypothesis HOC : reac_hunt_observe_contract.
Hypothesis CSC : check_sighting_contract.
Hypothesis CC0 : reac_disco_classify_contract.
Hypothesis CC1 : reac_disco_classify_on_segment_contract.
Hypothesis GSC : reac_disco_gate_should_push_contract.
Hypothesis BC : bcmp_contract.
Hypothesis OBC : reac_disco_table_observe_contract.
Hypothesis ROC : role_of_contract.
Hypothesis HRELRO : G_img_c B frame_RELRO mem0.
Hypothesis HB0 : sb_live b0 <= 64 /\ 0 <= sb_bytes b0 <= 2 ^ 28 /\ sb_cap b0 = CAPMAX.
Hypothesis MCF : forall fx : FPState, @malloc_contract_cf fx rc B API.
Hypothesis FCF : forall fx : FPState, @free_contract_cf fx rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).
Hypothesis HB0ag : sb_live b0 <= 64 /\ 0 <= sb_bytes b0 <= 2 ^ 28 /\ 128 <= sb_cap b0 <= CAP_AG.

Local Notation cut := (slot_cut B API K S L0 A0 mem0 md0 b0).
Local Notation RQ regs0 := (fun c' => exists q, cut q []
  (fun R m => q = bv_unsigned (MState.ret_pc (getr regs0 1)) /\ P_RET regs0 R m) c').
Local Notation sE1 := (step_E1 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA).
Local Notation sMAL0 := (step_mal0 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sE2 := (step_E2 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  TIC GIC LIC HIC PIC SIC).
Local Notation sB1 := (step_B1 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA AGE CTC SERA).
Local Notation sMALS := (step_malS B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sMALF := (step_malF B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sB2A := (step_B2a B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA SERB).
Local Notation sFRES := (step_freS B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sB3A := (step_B3a B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  HTC VNC CTC RLC HAC).
Local Notation sB2B := (step_B2b B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC ROC).
Local Notation sFREF := (step_freF B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sB3B := (step_B3b B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation sX1 := (step_X1 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation sFREH := (step_freH B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation sX2 := (step_X2 B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation envc := (cut_env B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HFA).
Local Notation pure := (cut_pure B API K S L0 A0 mem0 md0 b0).
Local Notation cor := (cut_or B API K S L0 A0 mem0 md0 b0).
Local Notation cex := (cut_ex B API K S L0 A0 mem0 md0 b0).
Local Notation sE1cf := (step_E1_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA).
Local Notation sMAL0cf := (step_mal0_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC MCF LIMLAW).
Local Notation sE2cf := (step_E2_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  TIC GIC LIC HIC PIC SIC).
Local Notation sB1cf := (step_B1_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA AGE CTC SERA).
Local Notation sMALScf := (step_malS_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC MCF LIMLAW).
Local Notation sMALFcf := (step_malF_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC MCF LIMLAW).
Local Notation sB2Acf := (step_B2a_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA SERB).
Local Notation sFREScf := (step_freS_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC FCF).
Local Notation sB3Acf := (step_B3a_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  HTC VNC CTC RLC HAC).
Local Notation sB2Bcf := (step_B2b_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA
  MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC ROC).
Local Notation sFREFcf := (step_freF_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC FCF).
Local Notation sB3Bcf := (step_B3b_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation sX1cf := (step_X1_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation sFREHcf := (step_freH_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC FCF).
Local Notation sX2cf := (step_X2_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).

Definition dblk (d : Z) (pl : list byte) : Prop :=
  (pl = [] /\ IMG_LO <= d < IMG_HI) \/ In (d, Z.of_nat (length pl)) (blocks L0 A0).

Lemma cut_mono : forall pc hb (P P' : bvmap 5 word -> (word -> option byte) -> Prop) c,
  (forall R m, P R m -> P' R m) -> cut pc hb P c -> cut pc hb P' c.
Proof.
  intros pc hb P P' c H (fx' & L & A & regs & mem & md & m0 & E & H1 & H2 & H3 & HP).
  exists fx', L, A, regs, mem, md, m0. exact (conj E (conj H1 (conj H2 (conj H3 (H regs m0 HP))))).
Qed.

Lemma cut_prop : forall pc hb P (A : Prop) c, (forall R m, P R m -> A) -> cut pc hb P c -> A.
Proof. intros pc hb P A c H (fx' & L & Aa & regs & mem & md & m0 & _ & _ & _ & _ & HP). exact (H regs m0 HP). Qed.

Lemma cut_pw : forall pc hb P c, cut pc hb P c -> pairwise YO0f.ranges_disjoint (hb ++ blocks L0 A0).
Proof.
  intros pc hb P c (fx' & L & A & regs & mem & md & m0 & _ & _ & (HSO & _ & HPM & _) & _ & _).
  pose proof HSO as (HM & _).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as D.
  assert (SYM : forall x y, YO0f.ranges_disjoint x y -> YO0f.ranges_disjoint y x).
  { intros [u v] [u' v'] H. unfold YO0f.ranges_disjoint in *. cbn in *. lia. }
  exact (pairwise_perm YO0f.ranges_disjoint SYM _ _ HPM D).
Qed.

Lemma cut_blk : forall pc hb P c, cut pc hb P c -> forall a n, In (a, n) hb ->
  4096 <= a /\ a + n <= alloc_ceiling /\ (forall i, 0 <= i < n -> nseg (a + i)).
Proof.
  intros pc hb P c HC a n Hin. eapply cut_prop; [|exact (envc _ _ _ _ HC)].
  intros R m (_ & _ & HB). destruct (HB a n Hin) as (H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)).
Qed.

Lemma cut_dsj : forall pc hb P c d pl, cut pc hb P c -> dblk d pl ->
  forall a n, In (a, n) hb -> d + Z.of_nat (length pl) <= a \/ a + n <= d.
Proof.
  intros pc hb P c d pl HC [(-> & Hd) | Hd] a n Hin.
  - destruct (cut_blk pc hb P c HC a n Hin) as (_ & _ & HN).
    cbn [length Z.of_nat]. rewrite Z.add_0_r.
    destruct (Z_lt_le_dec a d) as [L1|L1]; [|left; lia].
    destruct (Z_lt_le_dec d (a + n)) as [L2|L2]; [|right; lia].
    exfalso. destruct (HN (Z.max a IMG_LO - a) ltac:(lia)) as [N|N]; unfold IMG_LO, IMG_HI in *; lia.
  - pose proof (pairwise_app _ hb (blocks L0 A0) (a, n) (d, Z.of_nat (length pl)) (cut_pw _ _ _ _ HC) Hin Hd) as D.
    unfold YO0f.ranges_disjoint in D. cbn in D. lia.
Qed.

Lemma cut_sd : forall pc hb P c, cut pc hb P c -> cut pc hb (fun R m => P R m /\ exists canary, ser_data canary m) c.
Proof.
  intros pc hb P c (fx' & L & A & regs & mem & md & m0 & Ec & Hf & HFR & HREL & HP).
  exists fx', L, A, regs, mem, md, m0. split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|].
  split; [exact HREL|]. split; [exact HP|].
  pose proof HFR as (HSO & _ & _ & _).
  pose proof HSO as (HM & _ & _ & _ & _ & _ & HIMG & _).
  assert (RO : forall a, 0x205d0 <= a < 0x206a0 -> Mem.mrd rsegs m0 (Z_to_bv 64 a) = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. apply (mrd_keep_rom mem m0 _ HREL).
    assert (Hi : in_img B a) by (apply (in_img_hi B a HSEGS); unfold IMG_LO, IMG_HI; lia).
    assert (Hso : ~ static_owned B a).
    { unfold static_owned, vml_lo, vml_len. rewrite HLK, HLIBC, HGG, HGD, HDB, HSC, HSMC, HMDC, HVML, HDBL.
      cbv beta iota. lia. }
    assert (Hcx : ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)) by (rewrite HCTX; unfold CTX_SIZE; lia).
    assert (Her : ~ (errno_addr B <= a < errno_addr B + 4)) by (unfold errno_addr; rewrite HTP, HERR; lia).
    destruct (HIMG a Hi Hso Hcx Her) as [E _]. rewrite HSEGS in E.
    assert (G : in_globals frame_RELRO a) by (exists 0x205d0, 208; split; [unfold frame_RELRO; cbn [In]; left; reflexivity | lia]).
    pose proof (HRELRO a G) as G'. rewrite HSEGS in G'.
    change (Mem.mrd rsegs mem (Z_to_bv 64 a)) with (mbyte rsegs mem a). rewrite E. exact G'. }
  destruct (ax_statics HAX L A mem md HM) as (GG & (g & Hg & GW) & _).
  rewrite HSEGS, HGG, HGD in GG. rewrite HSEGS, HGD in GW.
  assert (LJS : length js_table = 24%nat) by reflexivity.
  assert (LBN : length bn_table = 24%nat) by reflexivity.
  exists (Z_to_bv 64 g). unfold ser_data. split; [|split; [|split]].
  - split; [unfold JSON_SCALAR_L; lia|]. split; [rewrite LJS; unfold JSON_SCALAR_L; lia|].
    intros j Hj. rewrite LJS in Hj. unfold Mem.wa. rewrite RO by (unfold JSON_SCALAR_L; lia). exact (js_rom j Hj).
  - split; [unfold BN_TS; lia|]. split; [rewrite LBN; unfold BN_TS; lia|].
    intros j Hj. rewrite LBN in Hj. unfold Mem.wa. rewrite RO by (unfold BN_TS; lia). exact (bn_rom j Hj).
  - apply (word_mem_le8 rsegs m0 GOT_GUARD GUARD); [|unfold GUARD; lia|unfold GOT_GUARD; lia|unfold GOT_GUARD; lia].
    intros k Hk. rewrite (mbyte_keep mem m0 _ HREL (gg_keep k Hk)). exact (GG k Hk).
  - apply (word_mem_le8 rsegs m0 GUARD g); [|exact Hg|unfold GUARD; lia|unfold GUARD; lia].
    intros k Hk. rewrite (mbyte_keep mem m0 _ HREL (gd_keep k Hk)). exact (GW k Hk).
Qed.

Lemma slack : forall X buf cap hb m, xin K S X -> buf mod 16 = 0 -> 0 <= cap -> ENV K S ((buf, cap) :: hb) m ->
  exists slk, buf + cap + Z.of_nat (length slk) <= LO X /\ (- cap) mod 8 <= Z.of_nat (length slk) /\
    Mem.bytes_at rsegs m (buf + cap) slk.
Proof.
  intros X buf cap hb m (Hlo & Hhi) H16 Hc (_ & HB).
  destruct (HB buf cap (or_introl eq_refl)) as (Hb0 & Hbc & _ & HSL).
  pose proof alloc_ceiling_val as (_ & Hac). pose proof alloc_ceiling_lt as Hlt.
  pose proof (Z.div_mod (buf + cap + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (buf + cap + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (- cap) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (- cap) 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod buf 16 ltac:(lia)) as D5. pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D6.
  destruct (rwc_present m (buf + cap) (8 * ((buf + cap + 7) / 8) - (buf + cap))) as [bs RB].
  - lia.
  - lia.
  - lia.
  - intros i Hi. apply (HSL Hc). lia.
  - exists bs. pose proof RB as [[[L _] _] _]. cbn [Cells.cell_wf] in L.
    assert (Lb : Z.of_nat (length bs) = 8 * ((buf + cap + 7) / 8) - (buf + cap)) by (rewrite L; apply Z2Nat.id; lia).
    rewrite Lb. split; [lia|]. split; [lia|]. exact (rw_bytes m (buf + cap) _ bs RB).
Qed.

Lemma d_keep : forall d pl hb m m', dblk d pl -> (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m m' a k) ->
  agree m m' d (Z.of_nat (length pl)).
Proof.
  intros d pl hb m m' [(-> & _) | HD] HB.
  - intros i Hi. cbn in Hi. lia.
  - exact (HB d _ (in_or_app _ _ _ (or_intror HD))).
Qed.

Lemma mk_keep : forall X d h pl hb m m', xin K S X -> dblk d pl -> In (h, 480) hb ->
  agree m m' X (S - X) -> (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m m' a k) ->
  mem_keep X d h pl m m'.
Proof.
  intros X d h pl hb m m' (Hlo & Hhi) HD Hh HSX HB. split; [|split].
  - apply (agree_sub m m' X (S - X) X SLOT_FRAME HSX); lia.
  - exact (HB h 480 (in_or_app _ _ _ (or_introl Hh))).
  - exact (d_keep d pl hb m m' HD HB).
Qed.

Lemma to_R2 : forall X d pl regs0 h, xin K S X -> dblk d pl ->
  forall R m, MP B S L0 A0 [] (P_MAL0 X d pl regs0) HUNT_SIZE X h R m -> P_R2 X d h pl regs0 R m.
Proof.
  intros X d pl regs0 h (Hlo & Hhi) HD R m (regs & m0 & bs & HP & RP & G10 & Hh0 & Hh16 & Hhc & HNI & RB & AS & AB).
  destruct HP as (G1 & G10' & G2 & G3 & G4 & G21 & G23 & G24 & CS & CO & BD).
  destruct (rp13 regs R RP) as (E2 & E3 & E4 & _ & _ & _ & _ & _ & E21 & _ & E23 & E24 & _ & _ & _).
  split; [exact G10|].
  split; [rewrite E2; exact G2|]. split; [rewrite E3; exact G3|]. split; [rewrite E4; exact G4|].
  split; [rewrite E21; exact G21|]. split; [rewrite E23; exact G23|]. split; [rewrite E24; exact G24|].
  split; [apply (rw_agree m0 m X (S - X) (X + 2520) _ AS);
          [lia|cbn [Cells.cells_size Cells.csize saved_of saved_cells]; unfold SLOT_FRAME in *; lia|exact CS]|].
  split; [apply (rw_agree m0 m X (S - X) (X + 946) _ AS);
          [lia|cbn [Cells.cells_size Cells.csize]; unfold SLOT_FRAME in *; lia|exact CO]|].
  split; [exact (bytes_at_agree m0 m d pl BD (d_keep d pl [] m0 m HD AB))|].
  split; [exact Hh16|]. exists bs. exact RB.
Qed.

Lemma to_SR : forall X d h pl regs0 i n now cap hb buf, xin K S X -> dblk d pl -> In (h, 480) hb ->
  forall R m, MP B S L0 A0 hb (P_SM X d h pl regs0 i n now cap) cap X buf R m ->
  P_SR X d h pl regs0 i n now buf cap R m.
Proof.
  intros X d h pl regs0 i n now cap hb buf HXI HD Hh R m (regs & m0 & bs & HP & RP & G10 & _ & _ & _ & _ & RB & AS & AB).
  pose proof HXI as (Hlo & Hhi).
  destruct HP as (Hn & Hcap & G1 & G10' & G21 & G27 & C136 & C152 & HBS).
  destruct (rp13 regs R RP) as (_ & _ & _ & _ & _ & _ & _ & _ & E21 & _ & _ & _ & _ & _ & E27).
  pose proof (mk_keep X d h pl hb m0 m HXI HD Hh AS AB) as MK.
  split; [exact Hn|]. split; [exact Hcap|]. split; [exact G10|]. split; [rewrite E21; exact G21|].
  split; [rewrite E27; exact G27|]. split; [exists bs; exact RB|].
  split; [apply (rw_agree m0 m X (S - X) (X + 136) _ AS); [lia|cbn [Cells.cells_size Cells.csize]; unfold SLOT_FRAME in *; lia|exact C136]|].
  split; [apply (rw_agree m0 m X (S - X) (X + 152) _ AS); [lia|cbn [Cells.cells_size Cells.csize]; unfold SLOT_FRAME in *; lia|exact C152]|].
  exact (base_keep X d h pl regs0 i now regs R m0 m RP MK HBS).
Qed.

Lemma to_FR : forall X d h pl regs0 i n now len k ob hb f, xin K S X -> dblk d pl -> In (h, 480) hb ->
  forall R m, MP B S L0 A0 hb (P_FM X d h pl regs0 i n now len k ob) len X f R m ->
  P_FR X d h pl regs0 i n now len k f ob R m.
Proof.
  intros X d h pl regs0 i n now len k ob hb f HXI HD Hh R m (regs & m0 & bs & HP & RP & G10 & _ & _ & _ & _ & RB & AS & AB).
  destruct HP as (Hn & Hlen & Hl16 & Hk & G1 & G10' & G19 & G20 & G21 & G22 & G8 & G25 & G9 & G27 & HBS).
  destruct (rp13 regs R RP) as (_ & _ & _ & E8 & E9 & _ & E19 & E20 & E21 & E22 & _ & _ & E25 & _ & E27).
  pose proof (mk_keep X d h pl hb m0 m HXI HD Hh AS AB) as MK.
  split; [exact Hn|]. split; [exact Hlen|]. split; [exact Hl16|]. split; [exact Hk|].
  split; [exact G10|]. split; [rewrite E19; exact G19|]. split; [rewrite E20; exact G20|].
  split; [rewrite E21; exact G21|]. split; [rewrite E22; exact G22|]. split; [rewrite E8; exact G8|].
  split; [rewrite E25; exact G25|]. split; [rewrite E9; exact G9|]. split; [rewrite E27; exact G27|].
  split; [exists bs; exact RB|].
  exact (base_keep X d h pl regs0 i now regs R m0 m RP MK HBS).
Qed.

Lemma to_R15 : forall X d h pl regs0 i n now buf hb, xin K S X -> dblk d pl -> In (h, 480) hb ->
  forall R m, FP S L0 A0 hb (P_SFREE X d h pl regs0 i n now buf) X R m -> P_R15 X d h pl regs0 i n now R m.
Proof.
  intros X d h pl regs0 i n now buf hb HXI HD Hh R m (regs & m0 & HP & RP & AS & AB).
  pose proof HXI as (Hlo & Hhi).
  destruct HP as (_ & _ & Hn & G27 & C136 & C152 & HBS).
  destruct (rp13 regs R RP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E27).
  pose proof (mk_keep X d h pl hb m0 m HXI HD Hh AS AB) as MK.
  split; [exact Hn|]. split; [rewrite E27; exact G27|].
  split; [apply (rw_agree m0 m X (S - X) (X + 136) _ AS); [lia|cbn [Cells.cells_size Cells.csize]; unfold SLOT_FRAME in *; lia|exact C136]|].
  split; [apply (rw_agree m0 m X (S - X) (X + 152) _ AS); [lia|cbn [Cells.cells_size Cells.csize]; unfold SLOT_FRAME in *; lia|exact C152]|].
  exact (base_keep X d h pl regs0 i now regs R m0 m RP MK HBS).
Qed.

Lemma to_R27RET : forall X d h pl regs0 i f hb, xin K S X -> dblk d pl -> In (h, 480) hb ->
  forall R m, FP S L0 A0 hb (P_FFREE X d h pl regs0 i f) X R m -> P_R27RET X d h pl regs0 i R m.
Proof.
  intros X d h pl regs0 i f hb HXI HD Hh R m (regs & m0 & HP & RP & AS & AB).
  destruct HP as (_ & _ & n & now & Hn & G21 & G23 & HBS).
  destruct (rp13 regs R RP) as (_ & _ & _ & _ & _ & _ & _ & _ & E21 & _ & E23 & _ & _ & _ & _).
  pose proof (mk_keep X d h pl hb m0 m HXI HD Hh AS AB) as MK.
  exists n, now. split; [exact Hn|]. split; [rewrite E21; exact G21|]. split; [rewrite E23; exact G23|].
  exact (base_keep X d h pl regs0 i now regs R m0 m RP MK HBS).
Qed.

Lemma to_R29 : forall X h regs0, xin K S X ->
  forall R m, FP S L0 A0 [] (P_FREEH X h regs0) X R m -> P_R29 X regs0 R m.
Proof.
  intros X h regs0 (Hlo & Hhi) R m (regs & m0 & HP & RP & AS & _).
  destruct HP as (_ & _ & G2 & G3 & G4 & CS).
  destruct (rp13 regs R RP) as (E2 & E3 & E4 & _).
  split; [rewrite E2; exact G2|]. split; [rewrite E3; exact G3|]. split; [rewrite E4; exact G4|].
  apply (rw_agree m0 m X (S - X) (X + 2520) _ AS);
    [lia|cbn [Cells.cells_size Cells.csize saved_of saved_cells]; unfold SLOT_FRAME in *; lia|exact CS].
Qed.

Lemma room1 : forall h n, 0 <= n <= 65536 -> room_slots (sb_hb b0 [(h, 480)]) n.
Proof.
  intros h n Hn. pose proof HB0 as (Hl & Hby & Hc).
  apply room_slots_small; unfold sb_hb; cbn [sb_live sb_bytes sb_cap length hb_bytes snd Z.of_nat];
    unfold CAPMAX in *; lia.
Qed.

Lemma run_exit : forall X h regs0 c, xok X -> xin K S X ->
  getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) -> getr regs0 4 = Z_to_bv 64 0x31a20 ->
  cut EXIT [(h, 480)] (P_EXIT X h regs0) c -> SR rsegs c (RQ regs0).
Proof.
  intros X h regs0 c HX HXI E02 E04 HC.
  eapply SR_bind; [exact (sX1 X h regs0 [(h, 480)] c HX HC)|]. intros c1 (q & HC1).
  destruct (pure _ _ _ _ _ HC1) as (-> & HC2).
  eapply SR_bind; [exact (sFREH X h regs0 [] c1 HX HXI HC2)|]. intros c2 HC3.
  pose proof HX as (HX0 & _ & HX1 & _).
  apply (sX2 X regs0 [] c2); [lia | unfold SLOT_FRAME in *; lia | exact E02 | exact E04 |].
  exact (cut_mono _ _ _ _ _ (to_R29 X h regs0 HXI) HC3).
Qed.

Lemma run_loop : forall X d h pl regs0, xok X -> dok X d pl -> 0 < d -> xin K S X -> dblk d pl ->
  h mod 16 = 0 -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) -> getr regs0 4 = Z_to_bv 64 0x31a20 ->
  forall i c, cut HDR [(h, 480)] (P_HDR X d h pl regs0 i) c -> SR rsegs c (RQ regs0).
Proof.
  intros X d h pl regs0 HX HD Hd0 HXI HDK Hh16 HDH E02 E04.
  assert (Hh : In (h, 480) [(h, 480)]) by (left; reflexivity).
  apply (SR_loop rsegs Z slot_measure (fun i c => cut HDR [(h, 480)] (P_HDR X d h pl regs0 i) c)).
  intros i c HC. cbv beta in HC |- *.
  assert (NX : forall c', (exists q, cut q [(h, 480)] (P_NEXT X d h pl regs0 i q) c') ->
    SR rsegs c' (fun c'' => RQ regs0 c'' \/ exists w', (slot_measure w' < slot_measure i)%nat /\
      cut HDR [(h, 480)] (P_HDR X d h pl regs0 w') c'')).
  { intros c' (q & HN). unfold P_NEXT in HN. destruct (cor _ _ _ _ _ HN) as [HN1 | HN1].
    - destruct (pure _ _ _ _ _ HN1) as (-> & HN2). destruct (pure _ _ _ _ _ HN2) as (Hi1 & HN3).
      apply SR_ret. right. exists (i + 1). split; [unfold slot_measure; lia | exact HN3].
    - destruct (pure _ _ _ _ _ HN1) as (-> & HN2).
      eapply SR_mono; [exact (run_exit X h regs0 c' HX HXI E02 E04 HN2) | intros c'' H; left; exact H]. }
  eapply SR_bind; [exact (sB1 X d h pl regs0 i _ c HX HD Hd0 HXI Hh HC)|]. intros c1 (q & HC1).
  destruct (pure _ _ _ _ _ HC1) as (-> & HC2). destruct (cor _ _ _ _ _ HC2) as [HSM | HFM].
  - destruct (cex _ _ _ _ _ HSM) as (n & HS1). destruct (cex _ _ _ _ _ HS1) as (now & HS2).
    destruct (cex _ _ _ _ _ HS2) as (cap & HS3).
    assert (Hcap : 2 <= cap <= 1280) by (eapply cut_prop; [|exact HS3]; intros R m (_ & Hc & _); exact Hc).
    eapply SR_bind; [exact (sMALS X d h pl regs0 i n now cap _ c1 HX HXI (room1 h cap ltac:(lia)) HS3)|].
    intros c2 (buf & HC3).
    assert (HMB : 4096 <= buf /\ buf mod 16 = 0 /\ (forall j, 0 <= j < cap -> ~ in_img B (buf + j))).
    { eapply cut_prop; [|exact HC3]. intros R m (regs & m0 & bs & _ & _ & _ & H1 & H2 & _ & H4 & _).
      exact (conj H1 (conj H2 H4)). }
    destruct HMB as (Hb0 & Hb16 & HNI).
    assert (Hb8 : buf mod 8 = 0) by (clear - Hb16; Z.div_mod_to_equations; lia).
    assert (HIF : pf_img_free buf cap).
    { intros j Hj s Hs Hin. apply (HNI j Hj). unfold in_img. rewrite HSEGS.
      split; [exact rsegs_nn | exists s; split; [exact Hs | exact Hin]]. }
    pose proof (pw_hd buf cap [(h, 480)] _ h 480 (cut_pw _ _ _ _ HC3) (or_introl eq_refl)) as Hbh.
    pose proof (cut_dsj _ _ _ _ d pl HC3 HDK buf cap (or_introl eq_refl)) as Hdb.
    assert (HC5 : cut uSER_RET [(buf, cap); (h, 480)]
      (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m) c2).
    { eapply cut_mono; [|exact (cut_sd _ _ _ _ (envc _ _ _ _ HC3))].
      intros R m ((HP & HE) & cn & SD).
      split; [exact (to_SR X d h pl regs0 i n now cap [(h, 480)] buf HXI HDK Hh R m HP)|].
      destruct (slack X buf cap [(h, 480)] m HXI Hb16 ltac:(lia) HE) as (slk & S1 & S2 & S3).
      exists slk, cn. exact (conj S1 (conj S2 (conj S3 SD))). }
    eapply SR_bind; [exact (sB2A X d h pl regs0 i n now buf cap [(buf, cap); (h, 480)] c2 HX HD HXI ltac:(lia) Hb8 HIF Hbh Hdb
      (or_introl eq_refl) (or_intror (or_introl eq_refl)) HC5)|].
    intros c3 (q & HC6). destruct (pure _ _ _ _ _ HC6) as (-> & HC7).
    eapply SR_bind; [exact (sFRES X d h pl regs0 i n now buf cap [(h, 480)] c3 HX HXI HC7)|]. intros c4 HC8.
    eapply SR_bind; [exact (sB3A X d h pl regs0 i n now [(h, 480)] c4 HX HD HXI Hh16 HDH Hh
      (cut_mono _ _ _ _ _ (to_R15 X d h pl regs0 i n now buf [(h, 480)] HXI HDK Hh) HC8))|].
    exact NX.
  - destruct (cex _ _ _ _ _ HFM) as (n & HF1). destruct (cex _ _ _ _ _ HF1) as (now & HF2).
    destruct (cex _ _ _ _ _ HF2) as (len & HF3). destruct (cex _ _ _ _ _ HF3) as (k & HF4).
    destruct (cex _ _ _ _ _ HF4) as (ob & HF5).
    assert (Hlen : 0 <= len < 65536) by (eapply cut_prop; [|exact HF5]; intros R m (_ & Hl & Hl2 & _); lia).
    eapply SR_bind; [exact (sMALF X d h pl regs0 i n now len k ob _ c1 HX HXI (room1 h len ltac:(lia)) HF5)|].
    intros c2 (f & HC3).
    pose proof (pw_hd f len [(h, 480)] _ h 480 (cut_pw _ _ _ _ HC3) (or_introl eq_refl)) as Hfh.
    pose proof (cut_dsj _ _ _ _ d pl HC3 HDK f len (or_introl eq_refl)) as Hdf.
    eapply SR_bind; [exact (sB2B X d h pl regs0 i n now len k f ob [(f, len); (h, 480)] c2 HX HD HXI Hh16 Hfh Hdf HDH
      (or_introl eq_refl) (or_intror (or_introl eq_refl))
      (cut_mono _ _ _ _ _ (to_FR X d h pl regs0 i n now len k ob [(h, 480)] f HXI HDK Hh) HC3))|].
    intros c3 (q & HC4). destruct (pure _ _ _ _ _ HC4) as (-> & HC5).
    eapply SR_bind; [exact (sFREF X d h pl regs0 i f len [(h, 480)] c3 HX HXI HC5)|]. intros c4 HC6.
    eapply SR_bind; [exact (sB3B X d h pl regs0 i [(h, 480)] c4 HX HD
      (cut_mono _ _ _ _ _ (to_R27RET X d h pl regs0 i f [(h, 480)] HXI HDK Hh) HC6))|].
    exact NX.
Qed.

Lemma uslot_run : forall X d pl regs0 c, xok X -> dok X d pl -> 0 < d -> xin K S X -> dblk d pl ->
  cut ENTRY_PC [] (P_ENT X d pl regs0) c -> SR rsegs c (RQ regs0).
Proof.
  intros X d pl regs0 c HX HD Hd0 HXI HDK HC.
  assert (E0 : getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) /\ getr regs0 4 = Z_to_bv 64 0x31a20).
  { eapply cut_prop; [|exact HC]. intros R m (_ & G2 & _ & _ & G4 & _). exact (conj G2 G4). }
  destruct E0 as (E02 & E04).
  eapply SR_bind; [exact (sE1 X d pl regs0 [] c HX HD Hd0 HXI HC)|]. intros c1 (q & HC1).
  destruct (cor _ _ _ _ _ HC1) as [HM | HR]; [|apply SR_ret; exists q; exact HR].
  destruct (pure _ _ _ _ _ HM) as (-> & HM1).
  assert (Hroom : room_slots (sb_hb b0 []) HUNT_SIZE).
  { rewrite sb_hb_nil. pose proof HB0 as (Hl & Hby & Hc).
    apply room_slots_small; unfold HUNT_SIZE, CAPMAX in *; lia. }
  eapply SR_bind; [exact (sMAL0 X d pl regs0 [] c1 HX HXI Hroom HM1)|]. intros c2 (h & HC2).
  assert (Hh16 : h mod 16 = 0).
  { eapply cut_prop; [|exact HC2]. intros R m (regs & m0 & bs & _ & _ & _ & _ & H2 & _). exact H2. }
  pose proof (cut_dsj _ _ _ _ d pl HC2 HDK h HUNT_SIZE (or_introl eq_refl)) as HDH.
  eapply SR_bind; [exact (sE2 X d h pl regs0 [(h, 480)] c2 HX HD HXI HDH (or_introl eq_refl)
    (cut_mono _ _ _ _ _ (to_R2 X d pl regs0 h HXI HDK) HC2))|].
  intros c3 (q & HC3). destruct (cor _ _ _ _ _ HC3) as [HH | HE].
  - destruct (pure _ _ _ _ _ HH) as (-> & HH1).
    exact (run_loop X d h pl regs0 HX HD Hd0 HXI HDK Hh16 HDH E02 E04 0 c3 HH1).
  - destruct (pure _ _ _ _ _ HE) as (-> & HE1). exact (run_exit X h regs0 c3 HX HXI E02 E04 HE1).
Qed.

Lemma CAP_AG_lt : 0 <= CAP_AG -> CAP_AG < 1680.
Proof using.
  intros H0. destruct (Z_lt_le_dec CAP_AG 1680) as [L|L]; [exact L|]. exfalso.
  pose proof (LIVE_BOUND_mono 1680 CAP_AG (2 ^ 29) (2 ^ 29) ltac:(lia) ltac:(lia)).
  pose proof CAP_AG_fits. pose proof CAP_AG_max. lia.
Qed.

Lemma room_ag_small : forall b n, 0 <= n <= 2 ^ 22 -> sb_live b + 1 <= sb_cap b -> 0 < sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> room_ag b n.
Proof using.
  intros b n Hn Hl Hc Hb Hbn. clear HB0 HB0ag. pose proof (CAP_AG_lt ltac:(lia)) as HC. split.
  - apply room_slots_small; unfold CAPMAX; lia.
  - split; lia.
Qed.

Lemma room0_cf : room_ag (sb_hb b0 []) HUNT_SIZE.
Proof using HB0ag.
  clear HB0. rewrite sb_hb_nil. pose proof HB0ag as (Hl & Hby & Hc).
  apply room_ag_small; unfold HUNT_SIZE; lia.
Qed.

Lemma room1_cf : forall h n, 0 <= n <= 65536 -> room_ag (sb_hb b0 [(h, 480)]) n.
Proof using HB0ag.
  intros h n Hn. clear HB0. pose proof HB0ag as (Hl & Hby & Hc).
  apply room_ag_small; unfold sb_hb; cbn [sb_live sb_bytes sb_cap length hb_bytes snd Z.of_nat]; lia.
Qed.

Lemma run_exit_cf : forall X h regs0 c, xok X -> xin K S X ->
  getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) -> getr regs0 4 = Z_to_bv 64 0x31a20 ->
  cut EXIT [(h, 480)] (P_EXIT X h regs0) c -> SRcf B c (RQ regs0).
Proof.
  intros X h regs0 c HX HXI E02 E04 HC.
  eapply SRcf_bind; [exact (sX1cf X h regs0 [(h, 480)] c HX HC)|]. intros c1 (q & HC1).
  destruct (pure _ _ _ _ _ HC1) as (-> & HC2).
  eapply SRcf_bind; [exact (sFREHcf X h regs0 [] c1 HX HXI HC2)|]. intros c2 HC3.
  pose proof HX as (HX0 & _ & HX1 & _).
  apply (sX2cf X regs0 [] c2); [lia | unfold SLOT_FRAME in *; lia | exact E02 | exact E04 |].
  exact (cut_mono _ _ _ _ _ (to_R29 X h regs0 HXI) HC3).
Qed.

Lemma run_loop_cf : forall X d h pl regs0, xok X -> dok X d pl -> 0 < d -> xin K S X -> dblk d pl ->
  h mod 16 = 0 -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) -> getr regs0 4 = Z_to_bv 64 0x31a20 ->
  forall i c, cut HDR [(h, 480)] (P_HDR X d h pl regs0 i) c -> SRcf B c (RQ regs0).
Proof.
  intros X d h pl regs0 HX HD Hd0 HXI HDK Hh16 HDH E02 E04.
  assert (Hh : In (h, 480) [(h, 480)]) by (left; reflexivity).
  apply (SRcf_loop B Z slot_measure (fun i c => cut HDR [(h, 480)] (P_HDR X d h pl regs0 i) c)).
  intros i c HC. cbv beta in HC |- *.
  assert (NX : forall c', (exists q, cut q [(h, 480)] (P_NEXT X d h pl regs0 i q) c') ->
    SRcf B c' (fun c'' => RQ regs0 c'' \/ exists w', (slot_measure w' < slot_measure i)%nat /\
      cut HDR [(h, 480)] (P_HDR X d h pl regs0 w') c'')).
  { intros c' (q & HN). unfold P_NEXT in HN. destruct (cor _ _ _ _ _ HN) as [HN1 | HN1].
    - destruct (pure _ _ _ _ _ HN1) as (-> & HN2). destruct (pure _ _ _ _ _ HN2) as (Hi1 & HN3).
      apply SRcf_ret. right. exists (i + 1). split; [unfold slot_measure; lia | exact HN3].
    - destruct (pure _ _ _ _ _ HN1) as (-> & HN2).
      eapply SRcf_mono; [exact (run_exit_cf X h regs0 c' HX HXI E02 E04 HN2) | intros c'' H; left; exact H]. }
  eapply SRcf_bind; [exact (sB1cf X d h pl regs0 i _ c HX HD Hd0 HXI Hh HC)|]. intros c1 (q & HC1).
  destruct (pure _ _ _ _ _ HC1) as (-> & HC2). destruct (cor _ _ _ _ _ HC2) as [HSM | HFM].
  - destruct (cex _ _ _ _ _ HSM) as (n & HS1). destruct (cex _ _ _ _ _ HS1) as (now & HS2).
    destruct (cex _ _ _ _ _ HS2) as (cap & HS3).
    assert (Hcap : 2 <= cap <= 1280) by (eapply cut_prop; [|exact HS3]; intros R m (_ & Hc & _); exact Hc).
    eapply SRcf_bind; [exact (sMALScf X d h pl regs0 i n now cap _ c1 HX HXI (room1_cf h cap ltac:(lia)) HS3)|].
    intros c2 (buf & HC3).
    assert (HMB : 4096 <= buf /\ buf mod 16 = 0 /\ (forall j, 0 <= j < cap -> ~ in_img B (buf + j))).
    { eapply cut_prop; [|exact HC3]. intros R m (regs & m0 & bs & _ & _ & _ & H1 & H2 & _ & H4 & _).
      exact (conj H1 (conj H2 H4)). }
    destruct HMB as (Hb0 & Hb16 & HNI).
    assert (Hb8 : buf mod 8 = 0) by (clear - Hb16; Z.div_mod_to_equations; lia).
    assert (HIF : pf_img_free buf cap).
    { intros j Hj s Hs Hin. apply (HNI j Hj). unfold in_img. rewrite HSEGS.
      split; [exact rsegs_nn | exists s; split; [exact Hs | exact Hin]]. }
    pose proof (pw_hd buf cap [(h, 480)] _ h 480 (cut_pw _ _ _ _ HC3) (or_introl eq_refl)) as Hbh.
    pose proof (cut_dsj _ _ _ _ d pl HC3 HDK buf cap (or_introl eq_refl)) as Hdb.
    assert (HC5 : cut uSER_RET [(buf, cap); (h, 480)]
      (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m) c2).
    { eapply cut_mono; [|exact (cut_sd _ _ _ _ (envc _ _ _ _ HC3))].
      intros R m ((HP & HE) & cn & SD).
      split; [exact (to_SR X d h pl regs0 i n now cap [(h, 480)] buf HXI HDK Hh R m HP)|].
      destruct (slack X buf cap [(h, 480)] m HXI Hb16 ltac:(lia) HE) as (slk & S1 & S2 & S3).
      exists slk, cn. exact (conj S1 (conj S2 (conj S3 SD))). }
    eapply SRcf_bind; [exact (sB2Acf X d h pl regs0 i n now buf cap [(buf, cap); (h, 480)] c2 HX HD HXI ltac:(lia) Hb8 HIF Hbh Hdb
      (or_introl eq_refl) (or_intror (or_introl eq_refl)) HC5)|].
    intros c3 (q & HC6). destruct (pure _ _ _ _ _ HC6) as (-> & HC7).
    eapply SRcf_bind; [exact (sFREScf X d h pl regs0 i n now buf cap [(h, 480)] c3 HX HXI HC7)|]. intros c4 HC8.
    eapply SRcf_bind; [exact (sB3Acf X d h pl regs0 i n now [(h, 480)] c4 HX HD HXI Hh16 HDH Hh
      (cut_mono _ _ _ _ _ (to_R15 X d h pl regs0 i n now buf [(h, 480)] HXI HDK Hh) HC8))|].
    exact NX.
  - destruct (cex _ _ _ _ _ HFM) as (n & HF1). destruct (cex _ _ _ _ _ HF1) as (now & HF2).
    destruct (cex _ _ _ _ _ HF2) as (len & HF3). destruct (cex _ _ _ _ _ HF3) as (k & HF4).
    destruct (cex _ _ _ _ _ HF4) as (ob & HF5).
    assert (Hlen : 0 <= len < 65536) by (eapply cut_prop; [|exact HF5]; intros R m (_ & Hl & Hl2 & _); lia).
    eapply SRcf_bind; [exact (sMALFcf X d h pl regs0 i n now len k ob _ c1 HX HXI (room1_cf h len ltac:(lia)) HF5)|].
    intros c2 (f & HC3).
    pose proof (pw_hd f len [(h, 480)] _ h 480 (cut_pw _ _ _ _ HC3) (or_introl eq_refl)) as Hfh.
    pose proof (cut_dsj _ _ _ _ d pl HC3 HDK f len (or_introl eq_refl)) as Hdf.
    eapply SRcf_bind; [exact (sB2Bcf X d h pl regs0 i n now len k f ob [(f, len); (h, 480)] c2 HX HD HXI Hh16 Hfh Hdf HDH
      (or_introl eq_refl) (or_intror (or_introl eq_refl))
      (cut_mono _ _ _ _ _ (to_FR X d h pl regs0 i n now len k ob [(h, 480)] f HXI HDK Hh) HC3))|].
    intros c3 (q & HC4). destruct (pure _ _ _ _ _ HC4) as (-> & HC5).
    eapply SRcf_bind; [exact (sFREFcf X d h pl regs0 i f len [(h, 480)] c3 HX HXI HC5)|]. intros c4 HC6.
    eapply SRcf_bind; [exact (sB3Bcf X d h pl regs0 i [(h, 480)] c4 HX HD
      (cut_mono _ _ _ _ _ (to_R27RET X d h pl regs0 i f [(h, 480)] HXI HDK Hh) HC6))|].
    exact NX.
Qed.

Lemma uslot_run_cf : forall X d pl regs0 c, xok X -> dok X d pl -> 0 < d -> xin K S X -> dblk d pl ->
  cut ENTRY_PC [] (P_ENT X d pl regs0) c -> SRcf B c (RQ regs0).
Proof.
  intros X d pl regs0 c HX HD Hd0 HXI HDK HC.
  assert (E0 : getr regs0 2 = Z_to_bv 64 (X + SLOT_FRAME) /\ getr regs0 4 = Z_to_bv 64 0x31a20).
  { eapply cut_prop; [|exact HC]. intros R m (_ & G2 & _ & _ & G4 & _). exact (conj G2 G4). }
  destruct E0 as (E02 & E04).
  eapply SRcf_bind; [exact (sE1cf X d pl regs0 [] c HX HD Hd0 HXI HC)|]. intros c1 (q & HC1).
  destruct (cor _ _ _ _ _ HC1) as [HM | HR]; [|apply SRcf_ret; exists q; exact HR].
  destruct (pure _ _ _ _ _ HM) as (-> & HM1).
  assert (Hroom : room_ag (sb_hb b0 []) HUNT_SIZE).
  { exact room0_cf. }

  eapply SRcf_bind; [exact (sMAL0cf X d pl regs0 [] c1 HX HXI Hroom HM1)|]. intros c2 (h & HC2).
  assert (Hh16 : h mod 16 = 0).
  { eapply cut_prop; [|exact HC2]. intros R m (regs & m0 & bs & _ & _ & _ & _ & H2 & _). exact H2. }
  pose proof (cut_dsj _ _ _ _ d pl HC2 HDK h HUNT_SIZE (or_introl eq_refl)) as HDH.
  eapply SRcf_bind; [exact (sE2cf X d h pl regs0 [(h, 480)] c2 HX HD HXI HDH (or_introl eq_refl)
    (cut_mono _ _ _ _ _ (to_R2 X d pl regs0 h HXI HDK) HC2))|].
  intros c3 (q & HC3). destruct (cor _ _ _ _ _ HC3) as [HH | HE].
  - destruct (pure _ _ _ _ _ HH) as (-> & HH1).
    exact (run_loop_cf X d h pl regs0 HX HD Hd0 HXI HDK Hh16 HDH E02 E04 0 c3 HH1).
  - destruct (pure _ _ _ _ _ HE) as (-> & HE1). exact (run_exit_cf X h regs0 c3 HX HXI E02 E04 HE1).
Qed.

End Run.
