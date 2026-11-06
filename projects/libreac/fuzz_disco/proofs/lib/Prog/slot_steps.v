From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 Contract FrameAPI KindBGlue AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem Frame Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_cut slot_seg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_preds slot_transport.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c slot_ser_defs slot_ser_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import memcpy_c find_entry_c reac_hunt_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import check_sighting_c reac_disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_classify_on_segment_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_gate_should_push_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_step_c reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_role_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_exit slot_R0_R3 slot_frame slot_step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sE slot_sE2 slot_sB1 slot_sB2a slot_sB2b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sB3a slot_sLatch slot_sX slot_record.
Import ListNotations.
Open Scope Z_scope.

Lemma hb_sub0 : forall (hb : list (Z * Z)) (a n : Z), In (a, n) [] -> In (a, n) hb.
Proof. intros hb a n []. Qed.

Lemma hb_sub1 : forall (hb : list (Z * Z)) x, In x hb -> forall a n, In (a, n) [x] -> In (a, n) hb.
Proof. intros hb x H a n [<-|[]]. exact H. Qed.

Lemma hb_sub2 : forall (hb : list (Z * Z)) x y, In x hb -> In y hb -> forall a n, In (a, n) [x; y] -> In (a, n) hb.
Proof. intros hb x y Hx Hy a n [<-|[<-|[]]]; assumption. Qed.

Lemma seg_pre : forall pc W P P' Pn, (forall R m, P' R m -> P R m) -> seg_ev pc W P Pn -> seg_ev pc W P' Pn.
Proof. intros pc W P P' Pn HPP HS fx' regs m0 Hf HI HP. exact (HS fx' regs m0 Hf HI (HPP regs m0 HP)). Qed.

Lemma seg_R27 : forall X d h pl regs0 i n now len f, xok X -> dok X d pl ->
  seg_ev R27 [] (P_R27 X d h pl regs0 i n now len f)
    (fun q R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m).
Proof.
  intros X d h pl regs0 i n now len f HX HD fx' regs m0 Hf HI HP.
  eapply Exec.evt_mono; [exact (R27_ev X d h pl regs0 i n now len f HX HD regs (@fp_regs fx') (@fp_csr fx') m0 HP)|].
  intros ms (R' & -> & HPf). exists R', (@fp_regs fx'), FREE_PC, (@fp_csr fx'), m0.
  split; [reflexivity|]. split; [exact Hf|]. split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|].
  split; [reflexivity | exact HPf].
Qed.

Ltac rqv := let E := fresh "E" in let HP := fresh "HP" in
  intros ? ? ? ? E HP; cbv beta in *;
  unfold P_NEXT, P_HDR, P_EXIT, P_SFREE, P_R15, P_FFREE, P_LAT, P_SM, P_FM, P_FREEH, P_MAL0, P_RET,
    regs_preserved, P_BASE in *;
  setoid_rewrite E; exact HP.

Section Steps.
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
Hypothesis HTHR : @sk_threaded SK = 0x514f0 + 1.
Hypothesis HLOCK : @sk_ofl_lock SK = 0x51918.
Hypothesis HHEAD : @sk_ofl_head SH = 0x51920.
Hypothesis HFA : forall fx : FPState, @frame_allocator rc fx B API.
Hypothesis HMAL : ms_malloc B = 0x17330.
Hypothesis HFRE : ms_free B = 0x171f0.
Hypothesis HLK : ms_lock B = 0x51560.
Hypothesis HLIBC : ms_libc B = 0x514f0.
Hypothesis HGG : ms_got_guard B = 0x1fee8.
Hypothesis HGD : ms_guard B = 0x514d0.
Hypothesis HCTX : ms_ctx B = 0x51568.
Hypothesis HTP : ms_tp B = 0x31260.
Hypothesis HERR : ms_errno_off B = -164.
Hypothesis HVML : ms_vmlock B = None.
Hypothesis HDBL : ms_debruijn_len B = 32.
Hypothesis HDB : ms_debruijn B = 0x10600.
Hypothesis HSC : ms_size_classes B = 0x10620.
Hypothesis HSMC : ms_small_cnt B = 0x10680.
Hypothesis HMDC : ms_med_cnt B = 0x1069b.
Hypothesis MCF : forall fx : FPState, @malloc_contract_cf fx rc B API.
Hypothesis FCF : forall fx : FPState, @free_contract_cf fx rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Local Notation cut := (slot_cut B API K S L0 A0 mem0 md0 b0).
Local Notation stepc := (cut_step B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation envc := (cut_env B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HFA).
Local Notation malc := (cut_mal B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation frec := (cut_fre B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC).
Local Notation stepcf := (cut_step_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD).
Local Notation malcf := (cut_mal_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HMAL HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC MCF LIMLAW).
Local Notation frecf := (cut_fre_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK
  HLIBC HGG HGD HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC FCF).

Definition xin (X : Z) : Prop := S - K <= LO X /\ X + SLOT_FRAME <= S.

Lemma W_ok_nil : forall hb, W_ok K S hb [].
Proof. intros hb x _ H. exfalso. exact (H I). Qed.

Lemma W_ok_cons : forall hb lo hi W,
  (forall x, lo <= x < hi -> (S - K <= x < S) \/ exists a n, In (a, n) hb /\ a <= x < a + n) ->
  W_ok K S hb W -> W_ok K S hb ((lo, hi) :: W).
Proof.
  intros hb lo hi W H1 H2 x Hx HO.
  destruct (Z_le_gt_dec lo x) as [L1|L1]; [destruct (Z_lt_ge_dec x hi) as [L2|L2]|].
  - exact (H1 x (conj L1 L2)).
  - apply (H2 x Hx). intros HW. apply HO. cbn [Frame.outside]. split; [lia | exact HW].
  - apply (H2 x Hx). intros HW. apply HO. cbn [Frame.outside]. split; [lia | exact HW].
Qed.

Ltac wok :=
  unfold W_E1, W_E2, W_B1, W_B2b, W_B3a, SER_W;
  repeat (apply W_ok_cons;
    [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
     unfold xin, LO, SLOT_FRAME, SLOT_STACK in *;
     first [left; lia
           | right; match goal with H : In (?a, ?n) _ |- _ => exists a, n; split; [exact H | lia] end]|]);
  apply W_ok_nil.

Ltac retk G1 G10 G2 G4 :=
  rewrite HTP; split; [exact G1|];
  split; [rewrite G1; apply YK0s.ret_ok_even; vm_compute; reflexivity|];
  split; [exact G10|]; split; [exact G2 | exact G4].

Ltac xal HX := let H := fresh "H" in pose proof HX as (_ & H & _ & _); exact H.

Ltac xstk HXI := let H1 := fresh "H" in let H2 := fresh "H" in
  pose proof HXI as (H1 & H2); unfold LO, SLOT_FRAME, SLOT_STACK, ALLOC_STACK in *; lia.

Lemma env_fenv : forall X hb hb' m, xin X -> (forall a n, In (a, n) hb' -> In (a, n) hb) ->
  ENV K S hb m -> fenv X hb' m.
Proof.
  intros X hb hb' m (Hlo & Hhi) Hsub (STK & HB). split.
  - pose proof STK as (Hs0 & _ & _).
    apply (stk_sub m (S - K) S (LO X) (X + SLOT_FRAME) STK Hlo Hhi). lia.
  - intros a n Hin. destruct (HB a n (Hsub a n Hin)) as (H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [lia|]. split; [exact H3 | exact H4].
Qed.

Lemma cut_pure : forall pc hb (A : Prop) P c, cut pc hb (fun R m => A /\ P R m) c -> A /\ cut pc hb P c.
Proof.
  intros pc hb A P c (fx' & L & Aa & regs & mem & md & m0 & E & H1 & H2 & H3 & HA & HP).
  split; [exact HA|]. exists fx', L, Aa, regs, mem, md, m0. exact (conj E (conj H1 (conj H2 (conj H3 HP)))).
Qed.

Lemma cut_or : forall pc hb P Q c, cut pc hb (fun R m => P R m \/ Q R m) c -> cut pc hb P c \/ cut pc hb Q c.
Proof.
  intros pc hb P Q c (fx' & L & Aa & regs & mem & md & m0 & E & H1 & H2 & H3 & [HP|HP]); [left|right];
    exists fx', L, Aa, regs, mem, md, m0; exact (conj E (conj H1 (conj H2 (conj H3 HP)))).
Qed.

Lemma cut_ex : forall (T : Type) pc hb (P : T -> bvmap 5 word -> (word -> option byte) -> Prop) c,
  cut pc hb (fun R m => exists x, P x R m) c -> exists x, cut pc hb (P x) c.
Proof.
  intros T pc hb P c (fx' & L & Aa & regs & mem & md & m0 & E & H1 & H2 & H3 & x & HP).
  exists x, fx', L, Aa, regs, mem, md, m0. exact (conj E (conj H1 (conj H2 (conj H3 HP)))).
Qed.

Lemma step_E1 : forall X d pl regs0 hb c, xok X -> dok X d pl -> xin X ->
  cut ENTRY_PC hb (P_ENT X d pl regs0) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => (q = MALLOC_AT /\ P_MAL0 X d pl regs0 R m) \/
    (q = bv_unsigned (MState.ret_pc (getr regs0 1)) /\ P_RET regs0 R m)) c').
Proof.
  intros X d pl regs0 hb c HX HD HXI HC.
  eapply (stepc ENTRY_PC hb _ (W_E1 X)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_E1 X d pl regs0 HX HD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb [] m HXI (hb_sub0 hb) HE).
Qed.

Lemma step_mal0 : forall X d pl regs0 hb c, xok X -> xin X -> room_slots (sb_hb b0 hb) HUNT_SIZE ->
  cut MALLOC_AT hb (P_MAL0 X d pl regs0) c ->
  SR rsegs c (fun c' => exists res,
    cut R2_RET ((res, HUNT_SIZE) :: hb) (MP B S L0 A0 hb (P_MAL0 X d pl regs0) HUNT_SIZE X res) c').
Proof.
  intros X d pl regs0 hb c HX HXI Hroom HC. pose proof Hroom as (Hn0 & _).
  apply (malc hb _ HUNT_SIZE X R2_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (G1 & G10 & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_E2 : reac_disco_table_init_contract -> reac_disco_gate_init_contract ->
  reac_disco_peer_lock_init_contract -> reac_hunt_init_contract ->
  reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  forall X d h pl regs0 hb c, xok X -> dok X d pl -> xin X -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  In (h, 480) hb -> cut R2_RET hb (P_R2 X d h pl regs0) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => (q = HDR /\ P_HDR X d h pl regs0 0 R m) \/
    (q = EXIT /\ P_EXIT X h regs0 R m)) c').
Proof.
  intros TIC GIC LIC HIC PIC SIC X d h pl regs0 hb c HX HD HXI HDJ Hh HC.
  eapply (stepc R2_RET hb _ (W_E2 X h)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_E2 TIC GIC LIC HIC PIC SIC X d h pl regs0 HX HD HDJ)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_B1 : reac_disco_table_age_contract -> check_table_contract -> ser_chain_A ->
  forall X d h pl regs0 i hb c, xok X -> dok X d pl -> xin X -> In (h, 480) hb ->
  cut HDR hb (P_HDR X d h pl regs0 i) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = MALLOC_PC /\
    ((exists n now cap, P_SM X d h pl regs0 i n now cap R m) \/
     (exists n now len k ob, P_FM X d h pl regs0 i n now len k ob R m))) c').
Proof.
  intros AGE CHECK SERA X d h pl regs0 i hb c HX HD HXI Hh HC.
  eapply (stepc HDR hb _ (W_B1 X)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_B1 AGE CHECK SERA X d h pl regs0 i HX HD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_malS : forall X d h pl regs0 i n now cap hb c, xok X -> xin X -> room_slots (sb_hb b0 hb) cap ->
  cut MALLOC_PC hb (P_SM X d h pl regs0 i n now cap) c ->
  SR rsegs c (fun c' => exists res,
    cut SER_RET ((res, cap) :: hb) (MP B S L0 A0 hb (P_SM X d h pl regs0 i n now cap) cap X res) c').
Proof.
  intros X d h pl regs0 i n now cap hb c HX HXI Hroom HC. pose proof Hroom as (Hn0 & _).
  apply (malc hb _ cap X SER_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (Hn & Hcap & G1 & G10 & G21 & G23 & C152 & C200 & Hi & Hnow & G2 & G3 & G4 & _).
  retk G1 G10 G2 G4.
Qed.

Lemma step_malF : forall X d h pl regs0 i n now len k ob hb c, xok X -> xin X -> room_slots (sb_hb b0 hb) len ->
  cut MALLOC_PC hb (P_FM X d h pl regs0 i n now len k ob) c ->
  SR rsegs c (fun c' => exists res,
    cut R17_RET ((res, len) :: hb) (MP B S L0 A0 hb (P_FM X d h pl regs0 i n now len k ob) len X res) c').
Proof.
  intros X d h pl regs0 i n now len k ob hb c HX HXI Hroom HC. pose proof Hroom as (Hn0 & _).
  apply (malc hb _ len X R17_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (Hn & Hlen & Hl16 & Hk & G1 & G10 & G19 & G21 & G22 & G23 & G20 & G25 & C200 & C216 &
    Hi & Hnow & G2 & G3 & G4 & _).
  retk G1 G10 G2 G4.
Qed.

Lemma step_B2a : ser_chain_B -> forall X d h pl regs0 i n now buf cap hb c,
  xok X -> dok X d pl -> xin X -> 0 < buf -> buf mod 8 = 0 -> pf_img_free buf cap ->
  (buf + cap <= h \/ h + 480 <= buf) -> (d + Z.of_nat (length pl) <= buf \/ buf + cap <= d) ->
  In (buf, cap) hb -> In (h, 480) hb ->
  cut SER_RET hb (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = SER_FREE /\ P_SFREE X d h pl regs0 i n now buf R m) c').
Proof.
  intros SERB X d h pl regs0 i n now buf cap hb c HX HD HXI Hb0 Hb8 HIF HBH HBD Hb Hh HC.
  eapply (stepc SER_RET hb _ (SER_W (LO X) X buf cap)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_B2a SERB X d h pl regs0 i n now buf cap HX HD Hb0 Hb8 HIF HBH HBD)].
  intros R m ((HP & HSX) & HE). split; [exact HP|]. split; [exact HSX|].
  exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_freS : forall X d h pl regs0 i n now buf cap hb c, xok X -> xin X ->
  cut SER_FREE ((buf, cap) :: hb) (P_SFREE X d h pl regs0 i n now buf) c ->
  SR rsegs c (cut SER_FREE_RET hb (FP S L0 A0 hb (P_SFREE X d h pl regs0 i n now buf) X)).
Proof.
  intros X d h pl regs0 i n now buf cap hb c HX HXI HC.
  apply (frec buf cap hb _ X SER_FREE_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & Hn & G23 & C152 & Hi & Hnow & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_B3a : reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> check_table_contract ->
  reac_hunt_role_contract -> reac_hunt_heard_anything_contract ->
  forall X d h pl regs0 i n now hb c, xok X -> dok X d pl -> xin X -> h mod 16 = 0 ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) -> In (h, 480) hb ->
  cut SER_FREE_RET hb (P_R15 X d h pl regs0 i n now) c ->
  SR rsegs c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros HTC VNC CTC RLC HAC X d h pl regs0 i n now hb c HX HD HXI Hh16 HDJ Hh HC.
  eapply (stepc SER_FREE_RET hb _ (W_B3a X h)); [exact (envc _ _ _ _ HC) | wok | exact (next_reqv X d h pl regs0 i) |].
  eapply seg_pre; [|exact (seg_B3a HTC VNC CTC RLC HAC X d h pl regs0 i n now HX HD Hh16 HDJ)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_B2b : memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract -> check_sighting_contract ->
  check_table_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract ->
  forall X d h pl regs0 i n now len k f ob hb c, xok X -> dok X d pl -> xin X -> h mod 16 = 0 ->
  (f + len <= h \/ h + 480 <= f) -> (d + Z.of_nat (length pl) <= f \/ f + len <= d) ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) -> In (f, len) hb -> In (h, 480) hb ->
  cut R17_RET hb (P_FR X d h pl regs0 i n now len k f ob) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m) c').
Proof.
  intros MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC X d h pl regs0 i n now len k f ob hb c HX HD HXI Hh16
    HFH HFD HHD Hf Hh HC.
  eapply (stepc R17_RET hb _ (W_B2b X h f len)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre;
    [|exact (seg_B2b MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC X d h pl regs0 i n now len k f ob HX HD Hh16 HFH HFD HHD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub2 hb _ _ Hf Hh) HE).
Qed.

Lemma step_R27 : forall X d h pl regs0 i n now len f hb c, xok X -> dok X d pl ->
  cut R27 hb (P_R27 X d h pl regs0 i n now len f) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m) c').
Proof.
  intros X d h pl regs0 i n now len f hb c HX HD HC.
  eapply (stepc R27 hb _ []); [exact HC | apply W_ok_nil | rqv | exact (seg_R27 X d h pl regs0 i n now len f HX HD)].
Qed.

Lemma step_freF : forall X d h pl regs0 i f len hb c, xok X -> xin X ->
  cut FREE_PC ((f, len) :: hb) (P_FFREE X d h pl regs0 i f) c ->
  SR rsegs c (cut R27_RET hb (FP S L0 A0 hb (P_FFREE X d h pl regs0 i f) X)).
Proof.
  intros X d h pl regs0 i f len hb c HX HXI HC.
  apply (frec f len hb _ X R27_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & n' & now' & Hn & G19 & G20 & G21 & Hi & Hnow & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_B3b : forall X d h pl regs0 i hb c, xok X -> dok X d pl ->
  cut R27_RET hb (P_LAT X d h pl regs0 i) c ->
  SR rsegs c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros X d h pl regs0 i hb c HX HD HC.
  exact (stepc R27_RET hb _ [] _ c HC (W_ok_nil hb) (next_reqv X d h pl regs0 i) (seg_B3b X d h pl regs0 i HX HD)).
Qed.

Lemma step_latch : forall X d h pl regs0 i hb c, xok X -> dok X d pl ->
  cut LATCH hb (P_LAT X d h pl regs0 i) c ->
  SR rsegs c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros X d h pl regs0 i hb c HX HD HC.
  exact (stepc LATCH hb _ [] _ c HC (W_ok_nil hb) (next_reqv X d h pl regs0 i) (seg_latch X d h pl regs0 i HX HD)).
Qed.

Lemma step_X1 : forall X h regs0 hb c, cut EXIT hb (P_EXIT X h regs0) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = FREE_PC /\ P_FREEH X h regs0 R m) c').
Proof.
  intros X h regs0 hb c HC.
  eapply (stepc EXIT hb _ []); [exact HC | apply W_ok_nil | rqv | exact (seg_X1 X h regs0)].
Qed.

Lemma step_freH : forall X h regs0 hb c, xok X -> xin X ->
  cut FREE_PC ((h, 480) :: hb) (P_FREEH X h regs0) c ->
  SR rsegs c (cut R29_RET hb (FP S L0 A0 hb (P_FREEH X h regs0) X)).
Proof.
  intros X h regs0 hb c HX HXI HC.
  apply (frec h 480 hb _ X R29_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_X2 : forall X regs0 hb c, 0 <= X -> X + 2592 <= 2 ^ 64 ->
  getr regs0 2 = Z_to_bv 64 (X + 2592) -> getr regs0 4 = Z_to_bv 64 0x31260 ->
  cut R29_RET hb (P_R29 X regs0) c ->
  SR rsegs c (fun c' => exists q, cut q hb (fun R m => q = bv_unsigned (MState.ret_pc (getr regs0 1)) /\
    P_RET regs0 R m) c').
Proof.
  intros X regs0 hb c HX0 HX1 E02 E04 HC.
  eapply (stepc R29_RET hb _ []); [exact HC | apply W_ok_nil | rqv | exact (seg_X2 X regs0 HX0 HX1 E02 E04)].
Qed.

Lemma step_E1_cf : forall X d pl regs0 hb c, xok X -> dok X d pl -> xin X ->
  cut ENTRY_PC hb (P_ENT X d pl regs0) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => (q = MALLOC_AT /\ P_MAL0 X d pl regs0 R m) \/
    (q = bv_unsigned (MState.ret_pc (getr regs0 1)) /\ P_RET regs0 R m)) c').
Proof.
  intros X d pl regs0 hb c HX HD HXI HC.
  eapply (stepcf ENTRY_PC hb _ (W_E1 X)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_E1 X d pl regs0 HX HD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb [] m HXI (hb_sub0 hb) HE).
Qed.

Lemma step_mal0_cf : forall X d pl regs0 hb c, xok X -> xin X -> room_ag (sb_hb b0 hb) HUNT_SIZE ->
  cut MALLOC_AT hb (P_MAL0 X d pl regs0) c ->
  SRcf B c (fun c' => exists res,
    cut R2_RET ((res, HUNT_SIZE) :: hb) (MP B S L0 A0 hb (P_MAL0 X d pl regs0) HUNT_SIZE X res) c').
Proof.
  intros X d pl regs0 hb c HX HXI Hroom HC. pose proof (proj1 Hroom) as (Hn0 & _).
  apply (malcf hb _ HUNT_SIZE X R2_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (G1 & G10 & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_E2_cf : reac_disco_table_init_contract -> reac_disco_gate_init_contract ->
  reac_disco_peer_lock_init_contract -> reac_hunt_init_contract ->
  reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  forall X d h pl regs0 hb c, xok X -> dok X d pl -> xin X -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  In (h, 480) hb -> cut R2_RET hb (P_R2 X d h pl regs0) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => (q = HDR /\ P_HDR X d h pl regs0 0 R m) \/
    (q = EXIT /\ P_EXIT X h regs0 R m)) c').
Proof.
  intros TIC GIC LIC HIC PIC SIC X d h pl regs0 hb c HX HD HXI HDJ Hh HC.
  eapply (stepcf R2_RET hb _ (W_E2 X h)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_E2 TIC GIC LIC HIC PIC SIC X d h pl regs0 HX HD HDJ)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_B1_cf : reac_disco_table_age_contract -> check_table_contract -> ser_chain_A ->
  forall X d h pl regs0 i hb c, xok X -> dok X d pl -> xin X -> In (h, 480) hb ->
  cut HDR hb (P_HDR X d h pl regs0 i) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => q = MALLOC_PC /\
    ((exists n now cap, P_SM X d h pl regs0 i n now cap R m) \/
     (exists n now len k ob, P_FM X d h pl regs0 i n now len k ob R m))) c').
Proof.
  intros AGE CHECK SERA X d h pl regs0 i hb c HX HD HXI Hh HC.
  eapply (stepcf HDR hb _ (W_B1 X)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_B1 AGE CHECK SERA X d h pl regs0 i HX HD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_malS_cf : forall X d h pl regs0 i n now cap hb c, xok X -> xin X -> room_ag (sb_hb b0 hb) cap ->
  cut MALLOC_PC hb (P_SM X d h pl regs0 i n now cap) c ->
  SRcf B c (fun c' => exists res,
    cut SER_RET ((res, cap) :: hb) (MP B S L0 A0 hb (P_SM X d h pl regs0 i n now cap) cap X res) c').
Proof.
  intros X d h pl regs0 i n now cap hb c HX HXI Hroom HC. pose proof (proj1 Hroom) as (Hn0 & _).
  apply (malcf hb _ cap X SER_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (Hn & Hcap & G1 & G10 & G21 & G23 & C152 & C200 & Hi & Hnow & G2 & G3 & G4 & _).
  retk G1 G10 G2 G4.
Qed.

Lemma step_malF_cf : forall X d h pl regs0 i n now len k ob hb c, xok X -> xin X -> room_ag (sb_hb b0 hb) len ->
  cut MALLOC_PC hb (P_FM X d h pl regs0 i n now len k ob) c ->
  SRcf B c (fun c' => exists res,
    cut R17_RET ((res, len) :: hb) (MP B S L0 A0 hb (P_FM X d h pl regs0 i n now len k ob) len X res) c').
Proof.
  intros X d h pl regs0 i n now len k ob hb c HX HXI Hroom HC. pose proof (proj1 Hroom) as (Hn0 & _).
  apply (malcf hb _ len X R17_RET c HC); [|xal HX|xstk HXI|exact Hn0|exact Hroom].
  intros regs m0 (Hn & Hlen & Hl16 & Hk & G1 & G10 & G19 & G21 & G22 & G23 & G20 & G25 & C200 & C216 &
    Hi & Hnow & G2 & G3 & G4 & _).
  retk G1 G10 G2 G4.
Qed.

Lemma step_B2a_cf : ser_chain_B -> forall X d h pl regs0 i n now buf cap hb c,
  xok X -> dok X d pl -> xin X -> 0 < buf -> buf mod 8 = 0 -> pf_img_free buf cap ->
  (buf + cap <= h \/ h + 480 <= buf) -> (d + Z.of_nat (length pl) <= buf \/ buf + cap <= d) ->
  In (buf, cap) hb -> In (h, 480) hb ->
  cut SER_RET hb (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => q = SER_FREE /\ P_SFREE X d h pl regs0 i n now buf R m) c').
Proof.
  intros SERB X d h pl regs0 i n now buf cap hb c HX HD HXI Hb0 Hb8 HIF HBH HBD Hb Hh HC.
  eapply (stepcf SER_RET hb _ (SER_W (LO X) X buf cap)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre; [|exact (seg_B2a SERB X d h pl regs0 i n now buf cap HX HD Hb0 Hb8 HIF HBH HBD)].
  intros R m ((HP & HSX) & HE). split; [exact HP|]. split; [exact HSX|].
  exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_freS_cf : forall X d h pl regs0 i n now buf cap hb c, xok X -> xin X ->
  cut SER_FREE ((buf, cap) :: hb) (P_SFREE X d h pl regs0 i n now buf) c ->
  SRcf B c (cut SER_FREE_RET hb (FP S L0 A0 hb (P_SFREE X d h pl regs0 i n now buf) X)).
Proof.
  intros X d h pl regs0 i n now buf cap hb c HX HXI HC.
  apply (frecf buf cap hb _ X SER_FREE_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & Hn & G23 & C152 & Hi & Hnow & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_B3a_cf : reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> check_table_contract ->
  reac_hunt_role_contract -> reac_hunt_heard_anything_contract ->
  forall X d h pl regs0 i n now hb c, xok X -> dok X d pl -> xin X -> h mod 16 = 0 ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) -> In (h, 480) hb ->
  cut SER_FREE_RET hb (P_R15 X d h pl regs0 i n now) c ->
  SRcf B c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros HTC VNC CTC RLC HAC X d h pl regs0 i n now hb c HX HD HXI Hh16 HDJ Hh HC.
  eapply (stepcf SER_FREE_RET hb _ (W_B3a X h)); [exact (envc _ _ _ _ HC) | wok | exact (next_reqv X d h pl regs0 i) |].
  eapply seg_pre; [|exact (seg_B3a HTC VNC CTC RLC HAC X d h pl regs0 i n now HX HD Hh16 HDJ)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub1 hb _ Hh) HE).
Qed.

Lemma step_B2b_cf : memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract -> check_sighting_contract ->
  check_table_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract ->
  forall X d h pl regs0 i n now len k f ob hb c, xok X -> dok X d pl -> xin X -> h mod 16 = 0 ->
  (f + len <= h \/ h + 480 <= f) -> (d + Z.of_nat (length pl) <= f \/ f + len <= d) ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) -> In (f, len) hb -> In (h, 480) hb ->
  cut R17_RET hb (P_FR X d h pl regs0 i n now len k f ob) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m) c').
Proof.
  intros MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC X d h pl regs0 i n now len k f ob hb c HX HD HXI Hh16
    HFH HFD HHD Hf Hh HC.
  eapply (stepcf R17_RET hb _ (W_B2b X h f len)); [exact (envc _ _ _ _ HC) | wok | rqv |].
  eapply seg_pre;
    [|exact (seg_B2b MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC X d h pl regs0 i n now len k f ob HX HD Hh16 HFH HFD HHD)].
  intros R m (HP & HE). split; [exact HP|]. exact (env_fenv X hb _ m HXI (hb_sub2 hb _ _ Hf Hh) HE).
Qed.

Lemma step_freF_cf : forall X d h pl regs0 i f len hb c, xok X -> xin X ->
  cut FREE_PC ((f, len) :: hb) (P_FFREE X d h pl regs0 i f) c ->
  SRcf B c (cut R27_RET hb (FP S L0 A0 hb (P_FFREE X d h pl regs0 i f) X)).
Proof.
  intros X d h pl regs0 i f len hb c HX HXI HC.
  apply (frecf f len hb _ X R27_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & n' & now' & Hn & G19 & G20 & G21 & Hi & Hnow & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_B3b_cf : forall X d h pl regs0 i hb c, xok X -> dok X d pl ->
  cut R27_RET hb (P_LAT X d h pl regs0 i) c ->
  SRcf B c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros X d h pl regs0 i hb c HX HD HC.
  exact (stepcf R27_RET hb _ [] _ c HC (W_ok_nil hb) (next_reqv X d h pl regs0 i) (seg_B3b X d h pl regs0 i HX HD)).
Qed.

Lemma step_latch_cf : forall X d h pl regs0 i hb c, xok X -> dok X d pl ->
  cut LATCH hb (P_LAT X d h pl regs0 i) c ->
  SRcf B c (fun c' => exists q, cut q hb (P_NEXT X d h pl regs0 i q) c').
Proof.
  intros X d h pl regs0 i hb c HX HD HC.
  exact (stepcf LATCH hb _ [] _ c HC (W_ok_nil hb) (next_reqv X d h pl regs0 i) (seg_latch X d h pl regs0 i HX HD)).
Qed.

Lemma step_X1_cf : forall X h regs0 hb c, cut EXIT hb (P_EXIT X h regs0) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => q = FREE_PC /\ P_FREEH X h regs0 R m) c').
Proof.
  intros X h regs0 hb c HC.
  eapply (stepcf EXIT hb _ []); [exact HC | apply W_ok_nil | rqv | exact (seg_X1 X h regs0)].
Qed.

Lemma step_freH_cf : forall X h regs0 hb c, xok X -> xin X ->
  cut FREE_PC ((h, 480) :: hb) (P_FREEH X h regs0) c ->
  SRcf B c (cut R29_RET hb (FP S L0 A0 hb (P_FREEH X h regs0) X)).
Proof.
  intros X h regs0 hb c HX HXI HC.
  apply (frecf h 480 hb _ X R29_RET c HC); [|xal HX|xstk HXI].
  intros regs m0 (G1 & G10 & G2 & G3 & G4 & _). retk G1 G10 G2 G4.
Qed.

Lemma step_X2_cf : forall X regs0 hb c, 0 <= X -> X + 2592 <= 2 ^ 64 ->
  getr regs0 2 = Z_to_bv 64 (X + 2592) -> getr regs0 4 = Z_to_bv 64 0x31260 ->
  cut R29_RET hb (P_R29 X regs0) c ->
  SRcf B c (fun c' => exists q, cut q hb (fun R m => q = bv_unsigned (MState.ret_pc (getr regs0 1)) /\
    P_RET regs0 R m) c').
Proof.
  intros X regs0 hb c HX0 HX1 E02 E04 HC.
  eapply (stepcf R29_RET hb _ []); [exact HC | apply W_ok_nil | rqv | exact (seg_X2 X regs0 HX0 HX1 E02 E04)].
Qed.

End Steps.
