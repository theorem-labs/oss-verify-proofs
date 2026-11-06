From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require MState Mem Frame Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import CrsNode.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c CrsGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import CrsRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c fuzz_free_c pj_write_c PjWriteNeed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require WriterRet put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require CrsSegA CrsSegB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_fail_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_ran_out_c LedgerCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Frame.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.MState.
Module MemNorm := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.
Import ListNotations.
Local Open Scope Z_scope.

Definition crs_cap (t : jv) (p : bool) : Z := grow_cap 0 0 (piece_lens (wdpieces t p)).

Lemma crs_fa : forall c k, 0 <= c < 2 ^ 64 -> 0 <= k -> c + k < 2 ^ 64 ->
  bv_unsigned (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 c) (Z_to_bv 64 k)) = c + k.
Proof.
  intros c k Hc Hk Hs. unfold fuzz_alloc_fail_c.fail_at_of.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; cbn; lia).
  destruct (Z.ltb_spec (c + k) (2 ^ 64)) as [_|H]; [|lia].
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma crs_fa_m1 : forall c, 0 <= c < 2 ^ 64 ->
  bv_unsigned (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 c) (Z_to_bv 64 (-1))) = 2 ^ 64 - 1.
Proof.
  intros c Hc. unfold fuzz_alloc_fail_c.fail_at_of.
  rewrite (Z_to_bv_unsigned 64 c), bv_wrap_small by (unfold bv_modulus; cbn; lia).
  assert (E : bv_unsigned (Z_to_bv 64 (-1)) = 2 ^ 64 - 1) by reflexivity. rewrite E.
  destruct (Z.ltb_spec (c + (2 ^ 64 - 1)) (2 ^ 64)) as [H|_].
  - assert (c = 0) by lia. subst c. reflexivity.
  - reflexivity.
Qed.

Lemma crs_node_top : forall segs m lb p u Du, pj_node segs m lb p u Du -> p + 56 <= 2 ^ 64.
Proof.
  intros segs m lb p u Du H. destruct u; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & Htop & _) & _) & _); exact Htop.
Qed.

Section Run.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable KW : Z.
Variable F : ResForm.
Variable Gp : rf_R F -> Prop.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis ERR : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis GGD : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis GRD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis TP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HG : globals_free B API omx_G.
Hypothesis LIVEC : fuzz_alloc_live_c.fuzz_alloc_live_contract.
Hypothesis COUNTC : fuzz_alloc_count_c.fuzz_alloc_count_contract.
Hypothesis FAILC : fuzz_alloc_fail_c.fuzz_alloc_fail_contract.
Hypothesis CRCC : check_reject_clean_c.check_reject_clean_contract.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F).
Variables (data size took doc : Z) (tb : list byte) (t : jv) (D : list (Z * Z)).
Hypothesis PRE : call_pre_k B (aa_MR API) (CRCS_K KW) L A regs mem md.
Hypothesis SPHI : spZ regs <= 2 ^ 47.
Hypothesis SPLO : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRCS_K KW.
Hypothesis KWP : 0 <= KW.
Hypothesis DLEN : Z.of_nat (length tb) = size.
Hypothesis DBYT : Mem.bytes_at rsegs mem data tb.
Hypothesis DOCHI : doc <> 0 -> spZ regs <= doc /\ doc mod 8 = 0.
Hypothesis DSUB : doc <> 0 -> forall a k, In (a, k) D -> In (a, k) Lam.
Hypothesis DATA0 : 0 < data.
Hypothesis DATAHI : data + size < 2 ^ 62.
Hypothesis SZ : size <= 0x300000.
Hypothesis DBLK : 0 < size -> exists a k, In (a, k) (blocks L A) /\ ~ lin Lam (a + 16) (k - 16) /\ a <= data /\
  data + size <= a + k.
Hypothesis DNO : forall i, 0 <= i < size ->
  ~ owned B L A (data + i) /\ ~ alloc_statics (data + i) /\ ~ (errno_addr B <= data + i < errno_addr B + 4).
Hypothesis TOOK : took = Z.of_nat (ncalls jr_strtod (zb tb)).
Hypothesis DOCT : doc <> 0 -> json_read jr_strtod (zb tb) = Some t /\ pj_node (ms_segs B) mem (lin Lam) doc t D /\
  Z.of_nat (length (wdoc t false)) + 1 < 2 ^ 24 /\ Z.of_nat (length (wdoc t true)) + 1 < 2 ^ 28 /\
  (depth t <= 32)%nat.
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_parse_contract fx rc B API F.
Hypothesis WRITE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_write_need fx rc B API F KW.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @fuzz_free_contract fx rc B API F.
Hypothesis RES0 : rf_ok F A b.
Hypothesis LED0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis CELLS0 : rd_cells B mem.
(* the two out_of_memory() flags, both 0 at the call (contract premises) *)
Hypothesis RAN0 : Mem.bytes_at rsegs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis OWN0 : Mem.bytes_at rsegs mem LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Definition crs_res_hyp : Prop :=
  (0 < took -> room_run F b (snd (jr_run jr_strtod (zb tb) []))) /\
  (took = 0 -> doc <> 0 -> crs_doc_rooms F b cnt (zb tb) t) /\
  (took <> 0 -> doc <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
     crs_doc_rooms F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) t) /\
  (took = 0 -> Gp (crs_after_doc F b cnt (zb tb) doc t)) /\
  (took <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
     Gp (crs_after_doc F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) doc t)).
Hypothesis RESH : crs_res_hyp.

Lemma RUN0 : 0 < took -> room_run F b (snd (jr_run jr_strtod (zb tb) [])).
Proof. exact (proj1 RESH). Qed.

Lemma ROOM0 : took = 0 -> doc <> 0 -> crs_doc_rooms F b cnt (zb tb) t.
Proof. exact (proj1 (proj2 RESH)). Qed.

Lemma ROOM1 : took <> 0 -> doc <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
  crs_doc_rooms F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) t.
Proof. exact (proj1 (proj2 (proj2 RESH))). Qed.

Lemma GP0 : took = 0 -> Gp (crs_after_doc F b cnt (zb tb) doc t).
Proof. exact (proj1 (proj2 (proj2 (proj2 RESH)))). Qed.

Lemma GP1 : took <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
  Gp (crs_after_doc F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) doc t).
Proof. exact (proj2 (proj2 (proj2 (proj2 RESH)))). Qed.

Definition SP : Z := spZ regs.
Definition KK : Z := CRCS_K KW.

Lemma crs_K : 112 + PJ_PARSE_K <= KK /\ 112 + KW <= KK /\ 112 + ALLOC_STACK <= KK /\ 0 <= PJ_PARSE_K /\
  128 <= KK.
Proof.
  assert (H1 : 0 <= PJ_PARSE_K).
  { pose proof (Z.le_max_r (PARSE_VALUE_K 0) (PJ_FREE_K 33)) as H0. revert H0.
    unfold PJ_PARSE_K. generalize (Z.max (PARSE_VALUE_K 0) (PJ_FREE_K 33)) as z. intros z Hz.
    unfold PJ_FREE_K, PJ_PARSE_F, PJ_FREE_F, FREE_K, ALLOC_STACK in *. lia. }
  unfold KK, CRCS_K, CRCS_F, FREE_K.
  pose proof (Z.le_max_l PJ_PARSE_K (Z.max KW (Z.max ALLOC_STACK 16))) as H2.
  pose proof (Z.le_max_r PJ_PARSE_K (Z.max KW (Z.max ALLOC_STACK 16))) as H3.
  pose proof (Z.le_max_l KW (Z.max ALLOC_STACK 16)) as H4.
  pose proof (Z.le_max_r KW (Z.max ALLOC_STACK 16)) as H5.
  pose proof (Z.le_max_l ALLOC_STACK 16) as H6.
  revert H1 H2 H3 H4 H5 H6.
  generalize (Z.max PJ_PARSE_K (Z.max KW (Z.max ALLOC_STACK 16))) as m1.
  generalize (Z.max KW (Z.max ALLOC_STACK 16)) as m2.
  generalize (Z.max ALLOC_STACK 16) as m3.
  generalize PJ_PARSE_K as pk.
  unfold ALLOC_STACK. intros. lia.
Qed.

Lemma crs_sp : alloc_ceiling + KK <= SP /\ SP mod 16 = 0 /\ SP <= 2 ^ 47 /\ 2 ^ 46 <= alloc_ceiling /\
  0x56000 <= SP - KK.
Proof.
  destruct PRE as (_ & _ & _ & _ & H1 & H2 & _). pose proof cg_ceil as Hc.
  unfold SP, KK, strtod_c.STRTOD_GLOBALS_TOP in *. lia.
Qed.

Lemma crs_glob : forall a, alloc_statics a -> in_globals omx_G a.
Proof.
  intros a Ha. unfold alloc_statics in Ha.
  destruct Ha as [H|[H|[H|H]]]; [exists G_LIVE, 8 | exists G_PEAK, 8 | exists G_COUNT, 8 | exists G_FAIL, 8];
    (split; [cbn; tauto | lia]).
Qed.

Lemma crs_statics_range : forall a, alloc_statics a -> G_FAIL <= a < G_COUNT + 8.
Proof. intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *. lia. Qed.

(* crs_statics_range with the cells' values, for the lia steps that compare them with the stack and errno *)
Ltac crs_stat H :=
  let Hr := fresh "Hr" in pose proof (crs_statics_range _ H) as Hr; unfold G_FAIL, G_COUNT in Hr.

Lemma crs_hg : forall a, alloc_statics a -> forall L1 A1 mem1 md1, aa_MR API L1 A1 mem1 md1 ->
  ~ owned B L1 A1 a /\ (forall p n, In (p, n) (blocks L1 A1) -> ~ (p <= a < p + n)) /\
  (exists seg, find_segment (ms_segs B) a 1 = Some seg /\ seg_writable seg = true).
Proof.
  intros a Ha L1 A1 mem1 md1 HM. destruct (HG a (crs_glob a Ha)) as (_ & _ & Hs & _ & H).
  destruct (H L1 A1 mem1 md1 HM) as [H1 H2]. split; [exact H1|]. split; [exact H2 | exact Hs].
Qed.

Definition WOK (W : list (Z * Z)) : Prop :=
  forall x, 0 <= x < 2 ^ 64 -> ~ (SP - KK <= x < SP) -> ~ (G_FAIL <= x < G_FAIL + 8) -> Frame.outside W x.

Lemma crs_ro_high : forall a : word, 2 ^ 33 <= bv_unsigned a -> Mem.ro_addr rsegs a = false.
Proof. intros a H. unfold Mem.ro_addr. rewrite (cg_high_nofs _ H). reflexivity. Qed.

Lemma crs_ro_seg : forall (a : word) seg, find_segment rsegs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true ->
  Mem.ro_addr rsegs a = false.
Proof. intros a seg H1 H2. unfold Mem.ro_addr. rewrite H1, H2. reflexivity. Qed.

Lemma crs_ro_munch : forall m m' W, MemNorm.ro_agree (ms_segs B) m -> Frame.munch W m m' -> WOK W ->
  MemNorm.ro_agree (ms_segs B) m'.
Proof.
  intros m m' W Hro HM HW a Ha. pose proof crs_sp as Hs.
  assert (Hlo : bv_unsigned a < 2 ^ 33).
  { destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 33)) as [H|H]; [exact H|]. exfalso.
    rewrite SEG in Ha. rewrite (crs_ro_high a H) in Ha. discriminate. }
  assert (Ho : Frame.outside W (bv_unsigned a)).
  { pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr. cbn in Hr.
    apply HW; [lia | lia |]. intros Hf.
    assert (Hst : alloc_statics (bv_unsigned a)) by (unfold alloc_statics; lia).
    destruct (HG _ (crs_glob _ Hst)) as (_ & _ & (seg & Hf1 & Hw) & _).
    rewrite SEG in Hf1, Ha. rewrite (crs_ro_seg a seg Hf1 Hw) in Ha. discriminate. }
  assert (E : Mem.mrd (ms_segs B) m' a = Mem.mrd (ms_segs B) m a) by (unfold Mem.mrd; rewrite (HM a Ho); reflexivity).
  rewrite E. exact (Hro a Ha).
Qed.

Lemma crs_rd_munch : forall L1 A1 m m' md1 W, rd_cells B m -> aa_MR API L1 A1 m' md1 -> Frame.munch W m m' -> WOK W ->
  rd_cells B m'.
Proof.
  intros L1 A1 m m' md1 W (Hro & _ & _) HM HMu HW.
  destruct (ax_statics AX L1 A1 m' md1 HM) as (H1 & (g & _ & H2) & _).
  split; [exact (crs_ro_munch m m' W Hro HMu HW)|]. split; [exact H1 | exists g; exact H2].
Qed.

Lemma crs_rd_post : forall L1 A1 m' md1, MemNorm.ro_agree (ms_segs B) m' -> aa_MR API L1 A1 m' md1 -> rd_cells B m'.
Proof.
  intros L1 A1 m' md1 Hro HM. destruct (ax_statics AX L1 A1 m' md1 HM) as (H1 & (g & _ & H2) & _).
  split; [exact Hro|]. split; [exact H1 | exists g; exact H2].
Qed.

Definition CI0 (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model)
    (Lam1 : list (Z * Z)) (peak1 cnt1 fail1 : Z) (b1 : rf_R F) (g : Z) : Prop :=
  rpost B API KK L A regs mem md alloc_statics (fun _ _ => False) L1 A1 regs mem1 md1 /\
  rd_cells B mem1 /\
  ledger B L1 A1 mem1 Lam1 peak1 cnt1 fail1 /\ peak <= peak1 /\
  rf_ok F A1 b1 /\ 0 <= g.

Definition CC (mem1 : word -> option byte) : Prop :=
  CF.CrsSegA.crs_cells mem1 SP (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
    (getr regs 21).

Definition CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g : Prop :=
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g /\ CC mem1.

(* Both flags stay 0 at every point of the walk: they are omx_G cells (globals_free: in the image, owned in no
   allocator state, not errno), off the stack and outside alloc_statics, so CI0's rpost keeps their bytes. *)
Lemma ci_flags : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g,
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  Mem.bytes_at rsegs mem1 LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
  Mem.bytes_at rsegs mem1 fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g (RP & _).
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IM & _ & _).
  pose proof crs_sp as Hs.
  assert (K : forall a, a = LedgerCells.GL_OWN_RAN_OUT \/ a = LedgerCells.GL_RAN_OUT ->
      mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem a).
  { intros a Ha.
    assert (Hg : in_globals omx_G a).
    { destruct Ha as [-> | ->]; [exists LedgerCells.GL_OWN_RAN_OUT, 8 | exists LedgerCells.GL_RAN_OUT, 8];
        (split; [cbn; tauto | lia]). }
    destruct (HG a Hg) as (Hi & Hr & _ & He & Ho).
    apply (IM a Hi).
    - intros L0 A0 m0 md0 HM. exact (proj1 (Ho L0 A0 m0 md0 HM)).
    - unfold scratch_k. intros [Hk|Hk]; [unfold SP in *; lia | exact (He Hk)].
    - intros Hst. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hst.
      destruct Ha as [-> | ->]; unfold LedgerCells.GL_OWN_RAN_OUT, LedgerCells.GL_RAN_OUT in Hst; lia. }
  assert (ER : fuzz_alloc_ran_out_c.G_RAN_OUT = LedgerCells.GL_RAN_OUT) by reflexivity.
  rewrite ER in RAN0 |- *.
  rewrite <- SEG in OWN0, RAN0 |- *.
  split; (apply (cn_bytes (ms_segs B) mem mem1); [assumption|]);
    intros x Hx; rewrite Mem.length_le1 in Hx; apply K; lia.
Qed.

Lemma crs_init : 0 < size -> st_init_done A = true.
Proof.
  intros Hs. destruct (DBLK Hs) as (a & k & Hin & _). destruct (cg_blk_user L A a k Hin) as (p & Hp & _).
  destruct PRE as (_ & HWF & _). exact (init_done_of_block A (p, k) HWF Hp).
Qed.

Lemma ci_pre : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g, 0 < size ->
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  call_pre_k B (aa_MR API) KK L1 A1 regs mem1 md1 /\ st_init_done A1 = true.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g Hs (RP & _).
  destruct RP as (M1 & W1 & B1 & _ & I1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1).
  pose proof (I1 (crs_init Hs)) as HI.
  destruct PRE as (_ & _ & _ & Hra & Hal & Hlo & Hhi & _ & Htp & _ & _).
  split; [|exact HI].
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact Hra|]. split; [exact Hal|].
  split; [exact Hlo|]. split; [exact Hhi|].
  split; [intros a Ha; apply S1; left; exact Ha|]. split; [exact Htp|].
  split; [intros a Ha; apply S1; right; exact Ha|].
  intros E. rewrite HI in E. discriminate.
Qed.

Lemma ci_data : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g, 0 < size ->
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> Mem.bytes_at rsegs mem1 data tb.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g Hs (RP & _).
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & U & _ & _ & _ & _ & _ & K & _).
  destruct (DBLK Hs) as (a & k & Hin & _ & Ha & Hk). destruct (cg_blk_user L A a k Hin) as (p & Hp & Ep).
  rewrite <- SEG in DBYT |- *. apply (cn_bytes (ms_segs B) mem mem1 data tb DBYT).
  intros x Hx. rewrite DLEN in Hx.
  pose proof (K p k (x - a) Hp (U p k Hp (fun H => H)) ltac:(lia)) as E. rewrite Ep in E.
  replace (a + (x - a)) with x in E by lia. apply E.
  destruct (DNO (x - data) ltac:(lia)) as (_ & Hst & _). replace (data + (x - data)) with x in Hst by lia. exact Hst.
Qed.

Lemma ci_doc : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g, doc <> 0 ->
  (forall bk, In bk Lam -> In bk Lam1) ->
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> pj_node (ms_segs B) mem1 (lin Lam1) doc t D.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g Hd HL (RP & _).
  destruct RP as (M1 & _ & _ & _ & _ & _ & _ & U & P9 & _ & _ & Hhi & _ & K & _).
  destruct (DOCT Hd) as (_ & HN & _). destruct (DOCHI Hd) as (Hd1 & _).
  pose proof crs_sp as Hs. pose proof crs_K as HK. pose proof PRE as (HM & _).
  apply (pj_node_frame (ms_segs B) t mem (lin Lam) mem (lin Lam1) doc D) in HN;
    [| intros a k Hin; apply HL; exact (DSUB Hd a k Hin) | intros x _; reflexivity].
  apply (cn_node_mframe (ms_segs B) mem mem1 (lin Lam1) doc t D HN).
  intros x [Hx|(bk & Hbk & Hx)].
  - pose proof (crs_node_top _ _ _ _ _ _ HN) as Htop.
    assert (Hns : ~ scratch_k B KK regs x)
      by (unfold scratch_k; rewrite ERR; unfold strtod_c.STRTOD_ERRNO, SP in *; lia).
    assert (Hne : ~ alloc_statics x) by (intros Hst; crs_stat Hst; unfold SP in *; lia).
    destruct (Hhi x ltac:(unfold SP in *; lia) Hns Hne) as [E1 E2].
    split; [exact E1 | intros Hw; apply E2; exact Hw].
  - destruct bk as [a k]. unfold pj_holds in Hx. cbn [fst snd] in Hx.
    destruct LED0 as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
    destruct (FB (a, k) (DSUB Hd a k Hbk)) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
    destruct (cg_blk_user L A (a - 16) (k + 16) Hblk) as (p & Hp & Ep).
    pose proof (U p (k + 16) Hp (fun H => H)) as Hp1.
    assert (Hst : ~ alloc_statics x).
    { intros Hst. destruct (crs_hg x Hst L A mem md HM) as (_ & Hb & _). apply (Hb (a - 16) (k + 16) Hblk). lia. }
    pose proof (K p (k + 16) (x - (a - 16)) Hp Hp1 ltac:(lia)) as E. rewrite Ep in E.
    replace (a - 16 + (x - (a - 16))) with x in E by lia. specialize (E Hst).
    split; [exact E|]. intros _.
    destruct (mr_blocks B _ (aa_laws API) L1 A1 mem1 md1 p (k + 16) (x - (a - 16)) M1 Hp1 ltac:(lia)) as ((bb & Hbb) & _).
    assert (Ep1 : ptr_addr L1 p = ptr_addr L p) by exact (P9 p (k + 16) Hp Hp1).
    rewrite Ep1, Ep in Hbb. replace (a - 16 + (x - (a - 16))) with x in Hbb by lia.
    unfold writable_at, wview. rewrite Hbb. discriminate.
Qed.

Lemma crs_libc : forall L1 A1 m1 md1, aa_MR API L1 A1 m1 md1 ->
  0 <= ms_libc B + 8 /\ ms_libc B + 16 <= alloc_ceiling /\
  forall i, 0 <= i < 8 -> owned B L1 A1 (ms_libc B + 8 + i).
Proof.
  intros L1 A1 m1 md1 HM.
  assert (Ho : forall i, 0 <= i < 8 -> owned B L1 A1 (ms_libc B + 8 + i))
    by (intros i Hi; right; unfold static_owned; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 m1 md1 _ HM (Ho 0 ltac:(lia))).
  pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 m1 md1 _ HM (Ho 7 ltac:(lia))).
  split; [lia|]. split; [lia | exact Ho].
Qed.

Lemma crs_bytes_munch : forall m m' W a bs, Mem.bytes_at rsegs m a bs -> Frame.munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> Frame.outside W x) -> Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' W a bs H HM HO. apply (cn_bytes rsegs m m' a bs H). intros x Hx.
  destruct H as (H1 & H2 & _). apply (MemNorm.mbyte_munch rsegs W m m' x HM); [lia | apply HO; exact Hx].
Qed.

Lemma crs_cc_munch : forall m m' W, CC m -> Frame.munch W m m' ->
  (forall x, SP - 56 <= x < SP -> Frame.outside W x) -> CC m'.
Proof.
  intros m m' W (C1 & C2 & C3 & C4 & C5 & C6 & C7) HM HO.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eapply crs_bytes_munch; try eassumption;
    intros x Hx; rewrite Mem.length_le8 in Hx; apply HO; lia.
Qed.

Lemma ci_tA0 : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 fail2 b1 g W mem2,
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  Frame.munch W mem1 mem2 -> Frame.wmono rsegs mem1 mem2 -> WOK W ->
  word_mem (ms_segs B) mem2 G_FAIL fail2 -> 0 <= fail2 < 2 ^ 64 ->
  CI0 L1 A1 mem2 md1 Lam1 peak1 cnt1 fail2 b1 g.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 fail2 b1 g W mem2 (RP & RD & LG & PK & RS & G0) HMu HWm HW HF HFr.
  pose proof crs_sp as Hs. pose proof crs_K as HK. unfold SP in Hs.
  pose proof RP as (M1 & WF1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1).
  assert (Hlow : forall x, 0 <= x < alloc_ceiling ->
      (owned B L1 A1 x \/ exists p n, In (p, n) (blocks L1 A1) /\ p <= x < p + n) -> Frame.outside W x).
  { intros x Hx Ho. apply HW; [lia | unfold SP; lia |]. intros Hf.
    assert (Hst : alloc_statics x) by (unfold alloc_statics; lia).
    destruct (crs_hg x Hst L1 A1 mem1 md1 M1) as (Hn & Hb & _).
    destruct Ho as [Ho | (p & n & Hp & Hpn)]; [exact (Hn Ho) | exact (Hb p n Hp Hpn)]. }
  assert (M2 : aa_MR API L1 A1 mem2 md1) by exact (kb_MR_A B API L1 A1 mem1 mem2 md1 W M1 HMu Hlow).
  destruct (crs_libc L1 A1 mem1 md1 M1) as (Hl1 & Hl2 & Hl3).
  assert (RP2 : rpost B API KK L1 A1 regs mem1 md1 alloc_statics (fun _ _ => False) L1 A1 regs mem2 md1).
  { apply (rp_of_A B API SEG KK L1 A1 regs mem1 md1 alloc_statics mem2 W regs M2 WF1 B1).
    - intros r _. reflexivity.
    - exact HMu.
    - rewrite SEG. exact HWm.
    - exact S1.
    - intros x Hx Hns He. apply HW; [exact Hx | |].
      + intros Hr. apply Hns. left. exact Hr.
      + intros Hr. apply He. unfold alloc_statics. right; right; right. exact Hr.
    - intros i Hi. pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 mem1 md1 _ M1 (Hl3 i Hi)).
      apply Hlow; [lia | left; exact (Hl3 i Hi)].
    - exact Hl1.
    - lia.
    - intros p n i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L1 A1 mem1 md1 p n i M1 Hp Hi) as (_ & R1 & R2 & _).
      split; [lia|]. apply HW; [lia | unfold SP; lia |].
      intros Hr. apply He. unfold alloc_statics. right; right; right. exact Hr. }
  split.
  { apply (rp_seq B API KK L A regs mem md alloc_statics L1 A1 regs mem1 md1 KK regs alloc_statics (fun _ _ => False)
      L1 A1 regs mem2 md1 regs RP RP2).
    - intros r _. reflexivity.
    - lia.
    - lia.
    - unfold KK in *. lia.
    - lia.
    - intros a _ _ He. exact He.
    - intros a _ _ He. exact He.
    - intros p n i _ _ _ He. exact He.
    - intros p n _ _ Hf. exact Hf.
    - intros a Ha Hn. contradiction. }
  split; [exact (crs_rd_munch L1 A1 mem1 mem2 md1 W RD M2 HMu HW)|].
  split.
  { apply (cg_ledger_fail B L1 A1 mem1 mem2 Lam1 peak1 cnt1 fail1 fail2 LG); [| | exact HF | exact HFr].
    - intros a Ha. apply (MemNorm.mbyte_munch _ W mem1 mem2 a HMu); [unfold G_LIVE, G_PEAK, G_COUNT in Ha; lia|].
      apply HW; [unfold G_LIVE, G_PEAK, G_COUNT in Ha; lia | unfold SP, G_LIVE, G_PEAK, G_COUNT in *; lia |].
      unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *. lia.
    - intros a k i Hin Hi. destruct LG as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB (a, k) Hin) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
      destruct (cg_blk_facts B API L1 A1 mem1 md1 (a - 16) (k + 16) M1 Hblk) as (R1 & R2 & _).
      apply (MemNorm.mbyte_munch _ W mem1 mem2 _ HMu); [lia|]. apply Hlow; [lia|].
      right. exists (a - 16), (k + 16). split; [exact Hblk | lia]. }
  split; [exact PK|]. split; [exact RS | exact G0].
Qed.

Lemma ci_tA : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 fail2 b1 g W mem2,
  CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  Frame.munch W mem1 mem2 -> Frame.wmono rsegs mem1 mem2 -> WOK W ->
  (forall x, SP - 56 <= x < SP -> Frame.outside W x) ->
  word_mem (ms_segs B) mem2 G_FAIL fail2 -> 0 <= fail2 < 2 ^ 64 ->
  CI L1 A1 mem2 md1 Lam1 peak1 cnt1 fail2 b1 g.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 fail2 b1 g W mem2 (H0 & HC) HMu HWm HW HO HF HFr.
  split; [exact (ci_tA0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 fail2 b1 g W mem2 H0 HMu HWm HW HF HFr)|].
  exact (crs_cc_munch mem1 mem2 W HC HMu HO).
Qed.

Lemma ci_start : forall mem1 fail1 W, Frame.munch W mem mem1 -> Frame.wmono rsegs mem mem1 -> WOK W ->
  word_mem (ms_segs B) mem1 G_FAIL fail1 -> 0 <= fail1 < 2 ^ 64 -> CC mem1 ->
  CI L A mem1 md Lam peak cnt fail1 b 0.
Proof.
  intros mem1 fail1 W HMu HWm HW HF HFr HC. split; [|exact HC].
  pose proof PRE as (HM & _). destruct (crs_libc L A mem md HM) as (Hl1 & Hl2 & _).
  pose proof cg_ceil as Hc.
  apply (ci_tA0 L A mem md Lam peak cnt (2 ^ 64 - 1) fail1 b 0 W mem1); try assumption.
  split; [exact (rp_refl B API SEG KK L A regs mem md alloc_statics PRE ltac:(lia) Hl1)|].
  split; [exact CELLS0|]. split; [exact LED0|]. split; [lia|]. split; [exact RES0 | lia].
Qed.

Definition G0 : Z := crcs_growth (zb tb) took doc t.

Definition crs_post (c' : config) : Prop :=
  exists (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L' A' regs' mem' md' Lam' peak',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    rpost B API (CRCS_K KW) L A regs mem md alloc_statics (fun _ _ => False) L' A' regs' mem' md' /\
    rd_cells B mem' /\
    ledger B L' A' mem' Lam' peak' (cnt + G0) (2 ^ 64 - 1) /\
    Permutation Lam' Lam /\ peak <= peak' /\
    (doc <> 0 -> pj_node (ms_segs B) mem' (lin Lam') doc t D) /\
    exists bf, rf_ok F A' bf /\ Gp bf.

Lemma crs_finish : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regsF mem1 md1 L1 A1 Lam1 peak1 b1,
  CI0 L1 A1 mem1 md1 Lam1 peak1 (cnt + G0) (2 ^ 64 - 1) b1 G0 -> Permutation Lam1 Lam ->
  frm_zero (@fp_csr fx1) -> regs_preserved regs regsF -> Gp b1 ->
  crs_post (mkCfg (@mkst fx1 regsF (getr regs 1) mem1 (seg_rom (ms_segs B))) md1).
Proof.
  intros fx1 regsF mem1 md1 L1 A1 Lam1 peak1 b1 HC HP FZ RPF HGb.
  pose proof HC as (RP & RC & LG & PK & RS & _).
  exists fx1, L1, A1, regsF, mem1, md1, Lam1, peak1.
  split; [reflexivity|]. split; [exact FZ|].
  split; [exact (rp_regs B API KK L A regs mem md alloc_statics (fun _ _ => False) L1 A1 regs mem1 md1 regsF RP RPF)|].
  split; [exact RC|]. split; [exact LG|]. split; [exact HP|]. split; [exact PK|].
  split; [intros Hd; apply (ci_doc L1 A1 mem1 md1 Lam1 peak1 (cnt + G0) (2 ^ 64 - 1) b1 G0 Hd); [|exact HC];
          intros bk Hb; apply (Permutation_in bk (Permutation_sym HP) Hb)|].
  exists b1. exact (conj RS HGb).
Qed.

Lemma crs_img : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite SEG. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma crs_stk_sub : forall m lo hi lo' hi', Frame.stk (ms_segs B) m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  Frame.stk (ms_segs B) m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H1 & H2 & H) Hl Hh Hlh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma ci_callpre : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 K1, 0 < size ->
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> 0 <= K1 -> 112 + K1 <= KK ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  call_pre_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 /\ st_init_done A1 = true /\
  Frame.stk (ms_segs B) mem1 (SP - KK) SP.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 K1 Hs HC HK1 HKK Hsp Htp Hra.
  destruct (ci_pre L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g Hs HC) as [HP HI].
  pose proof crs_sp as Hsp0. pose proof crs_K as HK.
  assert (Hmod : spZ regs1 mod 16 = 0)
    by (rewrite Hsp; destruct Hsp0 as (_ & Hm & _); unfold SP in *; Z.div_mod_to_equations; lia).
  split; [|split; [exact HI|]].
  - exact (kb_pre_A B API KK 112 K1 L1 A1 regs mem1 md1 regs1 mem1 [] HP ltac:(lia) HK1 ltac:(lia) Hsp Hmod Htp Hra
      (Frame.munch_refl [] mem1) (Frame.wmono_refl _ mem1) (fun _ _ _ => I) (fun _ _ _ => I)).
  - exact (kb_stk B API crs_img KK L1 A1 regs mem1 md1 HP ltac:(lia)).
Qed.

Lemma crs_cc_eq : forall m m', CC m ->
  (forall x, SP - 56 <= x < SP -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> CC m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5 & C6 & C7) E. rewrite SEG in E.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eapply cn_bytes; try eassumption;
    intros x Hx; rewrite Mem.length_le8 in Hx; apply E; lia.
Qed.

Lemma crs_parse_calls : forall x ok tr res cnt0 j, (j < ncalls jr_strtod x)%nat ->
  jr_run jr_strtod x ok = (res, tr) -> oks ok cnt0 (cnt0 + Z.of_nat j) (calls tr) ->
  res = None /\ calls tr = S j.
Proof.
  intros x ok tr res cnt0 j Hj Hrun Hk. unfold oks in Hk.
  destruct (ok_upto_dec ok j) as [Hu | (j' & Hj' & Hf & Hu)].
  - destruct (nth j ok true) eqn:Ej.
    + exfalso. destruct (ok_upto_dec ok (ncalls jr_strtod x)) as [Hall | (j2 & Hj2 & Hf2 & Hu2)].
      * pose proof (G7_1_calls jr_strtod x ok Hall) as Hc. rewrite Hrun in Hc. cbn [snd] in Hc.
        specialize (Hk j ltac:(lia)). rewrite Ej, Z.eqb_refl in Hk. discriminate.
      * assert (Hlt : (j < j2)%nat).
        { destruct (Nat.lt_ge_cases j j2) as [H|H]; [exact H|]. exfalso.
          destruct (Nat.eq_dec j2 j) as [E|Hne]; [subst j2; rewrite Ej in Hf2; discriminate|].
          rewrite (Hu j2 ltac:(lia)) in Hf2. discriminate. }
        destruct (G7_2 jr_strtod x ok j2 Hj2 Hf2 Hu2) as [_ Hc]. rewrite Hrun in Hc. cbn [snd] in Hc.
        specialize (Hk j ltac:(lia)). rewrite Ej, Z.eqb_refl in Hk. discriminate.
    + destruct (G7_2 jr_strtod x ok j Hj Ej Hu) as [H1 H2]. rewrite Hrun in H1, H2. cbn [fst snd] in H1, H2.
      split; assumption.
  - exfalso. destruct (G7_2 jr_strtod x ok j' ltac:(lia) Hf Hu) as [_ Hc]. rewrite Hrun in Hc. cbn [snd] in Hc.
    specialize (Hk j' ltac:(lia)). rewrite Hf in Hk. rewrite (proj2 (Z.eqb_neq _ _)) in Hk by lia. discriminate.
Qed.

Definition PK : Z := pick (zb tb) took.

Lemma crs_pick : 0 < took -> 0 <= PK < took.
Proof. intros H. unfold PK, pick. rewrite (proj2 (Z.eqb_neq took 0)) by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma crs_call_parse : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 (P : config -> Prop),
  0 < size -> 0 < took ->
  CI L A mem1 md Lam peak cnt (cnt + PK) b 0 ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 data -> getr regs1 11 = Z_to_bv 64 size ->
  getr regs1 12 = Z_to_bv 64 (SP - 112) -> frm_zero (@fp_csr fx1) ->
  (forall (fx2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs2 mem2 md2 L2 A2 Lam2 peak2 tr D',
     crs_parse_left cnt (zb tb) took tr D' -> Z.of_nat (calls tr) = PK + 1 ->
     CI L2 A2 mem2 md2 Lam2 peak2 (cnt + (PK + 1)) (2 ^ 64 - 1) (rf_frees F (rf_run F b tr) D') (PK + 1) ->
     Permutation Lam2 Lam -> pj_zero (ms_segs B) mem2 (SP - 112) ->
     regs_preserved regs1 regs2 -> getr regs2 10 = Z_to_bv 64 (-1) -> frm_zero (@fp_csr fx2) ->
     SR (ms_segs B) (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_PARSE) mem1 (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx1 regs1 mem1 P Hs Ht (HC & HCC) Hsp Htp Hra G10 G11 G12 FZ K.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK. pose proof (crs_pick Ht) as Hpk.
  destruct (ci_callpre L A mem1 md Lam peak cnt (cnt + PK) b 0 regs1 PJ_PARSE_K Hs HC ltac:(lia) ltac:(lia)
    Hsp Htp Hra) as (HP1 & HI & Hstk).
  pose proof HC as (RP & RD & LG & PKL & RS & _).
  pose proof RP as (M1 & _).
  pose proof (ci_data L A mem1 md Lam peak cnt (cnt + PK) b 0 Hs HC) as Hdat.
  destruct (DBLK Hs) as (ba & bk & Hbin & Hbl & Hba & Hbk).
  destruct (cg_blk_facts B API L A mem1 md ba bk M1 Hbin) as (Hb1 & Hb2 & _).
  pose proof cg_ceil as Hc.
  assert (Hn : (Z.to_nat PK < ncalls jr_strtod (zb tb))%nat) by lia.
  assert (Hl : length (zb tb) = length tb) by (unfold zb; apply length_map).
  assert (Htk : took <= 2 * size + 2).
  { rewrite TOOK. unfold ncalls. pose proof (G7_4 jr_strtod (zb tb) []) as H. rewrite Hl in H. lia. }
  unfold SP in *.
  eapply SR_bind; [apply (PARSE fx1 L A regs1 mem1 md Lam peak cnt (cnt + PK) b data size (spZ regs - 112) tb)|].
  { split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GGD|]. split; [exact GRD|].
    split; [exact HP1|]. split; [lia|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP in *; lia|].
    split; [exact FZ | exact RD]. }
  { exact LG. }
  { exact RS. }
  { exact G10. }
  { exact G11. }
  { exact G12. }
  { lia. }
  { exact DATA0. }
  { exact DATAHI. }
  { exact DLEN. }
  { rewrite SEG. exact Hdat. }
  { pose proof (PjRoundTrip.G12_1 (zb tb)) as H. rewrite Hl in H. lia. }
  { split.
    - right; right; left. exists ba, bk. split; [exact Hbin|]. split; [exact Hbl | split; lia].
    - exact DNO. }
  { lia. }
  { split; [Z.div_mod_to_equations; lia|]. apply (crs_stk_sub mem1 (spZ regs - KK) (spZ regs)); [exact Hstk | lia..]. }
  { split.
    - left. split; lia.
    - split; [intros _ E; rewrite HI in E; discriminate|].
      intros i Hi. split; [|split; [|split]].
      + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem1 md _ M1 Ho). lia.
      + intros Hst. crs_stat Hst. lia.
      + rewrite ERR. unfold strtod_c.STRTOD_ERRNO. lia.
      + intros Hi'. pose proof (cg_img_bound B SEG _ Hi'). lia. }
  { intros a k Hin. pose proof (ledger_block_range B API L A mem1 md Lam peak cnt (cnt + PK) a k M1 LG Hin). lia. }
  { cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  { cbn [Frame.disjoint_from]. rewrite Hsp. split; [lia|]. split; [lia | exact I]. }
  { lia. }
  { exact (RUN0 Ht). }
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & ok & res & tr & -> & FZ2 & _ & RP2 &
    RD2 & LG2 & Hrun & Hoks & Hcnt & Hfa & Hpk2 & _ & _ & _ & Hres).
  pose proof Hoks as Hoks0.
  assert (Hfail : cnt + PK = cnt + Z.of_nat (Z.to_nat PK)) by lia.
  rewrite Hfail in Hoks.
  destruct (crs_parse_calls (zb tb) ok tr res cnt (Z.to_nat PK) Hn Hrun Hoks) as [-> Hcl].
  destruct Hres as (G2 & (D0 & D' & HDD & HDs & HDn & RS2) & HPm & HZ).
  assert (HPL : crs_parse_left cnt (zb tb) took tr D').
  { exists ok, None. split; [exact Hrun|]. split; [exact Hoks0|]. split.
    - exact (Permutation_trans (Permutation_map snd (Permutation_sym HDD)) HDs).
    - rewrite <- (Permutation_length HDD). exact HDn. }
  assert (Hcnt2 : cnt2 = cnt + (PK + 1)) by (rewrite Hcnt, Hcl; lia).
  assert (Hf2 : fail2 = 2 ^ 64 - 1) by (apply (proj1 Hfa); rewrite Hcl; lia).
  rewrite Hcnt2, Hf2 in LG2.
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RR2 & _ & Hhi2 & _ & _ & S2).
  apply (K fx2 regs2 mem2 md2 L2 A2 Lam2 peak2 tr D' HPL ltac:(rewrite Hcl; lia));
    [| exact HPm | exact HZ | exact RR2 | exact G2 | exact FZ2].
  split.
  - split.
    { apply (rp_seq B API KK L A regs mem md alloc_statics L A regs mem1 md PJ_PARSE_K regs1 (pj_parse_writes (spZ regs - 112))
        (fun _ _ => False) L2 A2 regs2 mem2 md2 regs RP RP2).
      - intros r _. reflexivity.
      - lia.
      - lia.
      - unfold KK in *. lia.
      - lia.
      - intros a Ha Hns He [Hw|Hw]; [apply Hns; left; unfold KK in *; lia | exact (He Hw)].
      - intros a Ha Hns He [Hw|Hw]; [pose proof (cg_img_bound B SEG _ Ha); lia | exact (He Hw)].
      - intros p n i Hp _ Hi He [Hw|Hw]; [|exact (He Hw)].
        destruct (mr_blocks B _ (aa_laws API) L A mem1 md p n i M1 Hp Hi) as (_ & R1 & R2 & _). lia.
      - intros p n _ _ Hf. exact Hf.
      - intros a Ha Hn2. destruct (Z_le_gt_dec (spZ regs - 112) a) as [Ha1|Ha1];
          [destruct (Z_lt_ge_dec a (spZ regs - 112 + 56)) as [Ha2|Ha2]|].
        + right. destruct HZ as ((_ & _ & _ & Hw) & _). destruct (Hw a ltac:(lia)) as [Hw1 _].
          unfold writable_at. exact Hw1.
        + left. intros [Hw|Hw]; [lia|]. crs_stat Hw.
          unfold scratch_k in Ha. rewrite ERR in Ha. unfold strtod_c.STRTOD_ERRNO in Ha. lia.
        + left. intros [Hw|Hw]; [lia|]. crs_stat Hw.
          unfold scratch_k in Ha. rewrite ERR in Ha. unfold strtod_c.STRTOD_ERRNO in Ha. lia. }
    split; [exact RD2|]. split; [exact LG2|]. split; [rewrite Hpk2; lia|]. split; [exact RS2 | lia].
  - apply (crs_cc_eq mem1 mem2 HCC). intros x Hx. unfold SP in Hx.
    assert (Hns : ~ scratch_k B PJ_PARSE_K regs1 x)
      by (unfold scratch_k; rewrite ERR, Hsp; unfold strtod_c.STRTOD_ERRNO; lia).
    assert (Hne : ~ pj_parse_writes (spZ regs - 112) x)
      by (intros [Hw|Hw]; [lia | crs_stat Hw; lia]).
    exact (proj1 (Hhi2 x ltac:(lia) Hns Hne)).
Qed.

Lemma ci_write : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 K1 L' A' regs' mem' md' Lam' peak' cnt' fail' b' g',
  0 < size -> CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> 0 <= K1 -> 112 + K1 <= KK ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  regs_preserved regs1 regs' -> aa_MR API L' A' mem' md' -> WF A' -> bounded A' ->
  MemNorm.ro_agree (ms_segs B) mem' ->
  ledger B L' A' mem' Lam' peak' cnt' fail' -> rf_ok F A' b' ->
  layout_le A1 L1 L' -> (length (st_regions A1) <= length (st_regions A'))%nat ->
  (st_init_done A1 = true -> st_init_done A' = true) -> (exists vm', md' = with_vmmaps vm' md1) ->
  (forall q n, In (q, n) (user_blocks A1) -> In (q, n) (user_blocks A') /\ ptr_addr L' q = ptr_addr L1 q) ->
  keeps B L1 A1 mem1 mem' 0 ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a -> ~ owned B L' A' a ->
     ~ (spZ regs1 - K1 <= a < spZ regs1) -> ~ (errno_addr B <= a < errno_addr B + 4) -> ~ alloc_statics a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem' a)) ->
  (forall a, (spZ regs1 - K1 <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4) ->
     writable_at (ms_segs B) mem1 a -> writable_at (ms_segs B) mem' a) ->
  peak1 <= peak' -> 0 <= g' ->
  CI L' A' mem' md' Lam' peak' cnt' fail' b' g'.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 K1 L' A' regs' mem' md' Lam' peak' cnt' fail' b' g'
    Hs (HC & HCC) HK1 HKK Hsp Htp Hra RR M' WF' B' RO LG' RS' Ly Rg In' Md UK KP FR WS Hpk Hg.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK. pose proof cg_ceil as Hc.
  destruct (ci_callpre L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 K1 Hs HC HK1 HKK Hsp Htp Hra)
    as (HP1 & HI1 & _).
  pose proof HP1 as (M1 & _ & _ & _ & _ & _ & _ & HW1 & _ & HE1 & _).
  pose proof HC as (RP & _ & _ & PK1 & _ & _).
  unfold SP in *.
  assert (RP2 : rpost B API K1 L1 A1 regs1 mem1 md1 alloc_statics (fun _ _ => False) L' A' regs' mem' md').
  { split; [exact M'|]. split; [exact WF'|]. split; [exact B'|]. split; [exact Ly|].
    split; [exact In'|].
    split; [intros HN; rewrite (In' HI1) in HN; discriminate|].
    split; [exact Rg|].
    split; [intros p n Hp _; exact (proj1 (UK p n Hp))|].
    split; [intros p n Hp _; exact (proj2 (UK p n Hp))|].
    split; [exact RR|].
    split; [exact Md|].
    split.
    { intros a Ha Hns He. apply FR; [left; exact Ha | | | | | exact He].
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 mem1 md1 _ M1 Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' mem' md' _ M' Ho). lia.
      - intros H. apply Hns. left. exact H.
      - intros H. apply Hns. right. exact H. }
    split.
    { intros a Ha Hno Hns He. apply FR; [right; exact Ha | exact (Hno L1 A1 mem1 md1 M1) | exact (Hno L' A' mem' md' M')
        | | | exact He].
      - intros H. apply Hns. left. exact H.
      - intros H. apply Hns. right. exact H. }
    split.
    { intros p n i Hp _ Hi _. destruct (mr_blocks B _ (aa_laws API) L1 A1 mem1 md1 p n i M1 Hp Hi) as (_ & R1 & _).
      apply (KP (ptr_addr L1 p) n i); [exact (cg_blk_of_user L1 A1 p n Hp) | lia | exact Hi]. }
    intros a Ha. apply WS; [exact Ha|]. destruct Ha as [Ha|Ha]; [apply HW1; exact Ha | apply HE1; exact Ha]. }
  split; [split|].
  - apply (rp_seq B API KK L A regs mem md alloc_statics L1 A1 regs mem1 md1 K1 regs1 alloc_statics
      (fun _ _ => False) L' A' regs' mem' md' regs RP RP2).
    + intros r _. reflexivity.
    + lia.
    + lia.
    + unfold KK in *. lia.
    + exact HK1.
    + intros a _ _ He. exact He.
    + intros a _ _ He. exact He.
    + intros p n i _ _ _ He. exact He.
    + intros p n _ _ Hf. exact Hf.
    + intros a Ha _. left. intros Hst. crs_stat Hst.
      unfold scratch_k in Ha. rewrite ERR in Ha. unfold strtod_c.STRTOD_ERRNO in Ha. lia.
  - split; [exact (crs_rd_post L' A' mem' md' RO M')|]. split; [exact LG'|]. split; [lia|].
    split; [exact RS' | exact Hg].
  - apply (crs_cc_eq mem1 mem' HCC). intros x Hx. unfold SP in Hx.
    apply FR; [left; lia | | | lia | rewrite ERR; unfold strtod_c.STRTOD_ERRNO; lia |
      intros Hst; crs_stat Hst; lia].
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 mem1 md1 _ M1 Ho). lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' mem' md' _ M' Ho). lia.
Qed.

Lemma crs_size_pos : doc <> 0 -> 0 < size.
Proof.
  intros Hd. destruct (DOCT Hd) as (Hj & _).
  assert (Hne : tb <> []) by (intros E; rewrite E in Hj; vm_compute in Hj; discriminate).
  rewrite <- DLEN. destruct tb as [|c r]; [contradiction | cbn [length]; lia].
Qed.

Lemma crs_call_write : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 fail1 b1 g (p : bool)
    (P : config -> Prop),
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> Permutation Lam1 Lam ->
  CF.WriterRet.wr_rooms F b1 (w0 cnt1 fail1) (wdpieces t p) ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 (if p then 1 else 0) -> frm_zero (@fp_csr fx1) ->
  (forall c', @pj_write_ret fx1 rc B API F KW L1 A1 regs1 mem1 md1 doc t D p Lam1 peak1 cnt1 fail1 b1 c' ->
     SR (ms_segs B) c' P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 fail1 b1 g p P Hd HC HP Hg Hsp Htp Hra G10 G11 FZ K.
  pose proof (crs_size_pos Hd) as Hs.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK. pose proof cg_ceil as Hc.
  destruct HC as (HC0 & HCC).
  destruct (ci_callpre L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g regs1 KW Hs HC0 KWP ltac:(lia) Hsp Htp Hra)
    as (HP1 & HI1 & _).
  pose proof HC0 as (RP & (RO & _) & LG & _ & RS & Hg0).
  destruct (DOCT Hd) as (_ & _ & Hw0 & Hw1 & Hdep). destruct (DOCHI Hd) as (Hd1 & Hd8).
  pose proof (ci_doc L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g Hd
    (fun bk Hb => Permutation_in bk (Permutation_sym HP) Hb) HC0) as HN.
  assert (Ep : negb ((if p then 1 else 0) =? 0) = p) by (destruct p; reflexivity).
  assert (Hts : spZ regs1 <= TASK_SIZE)
    by (assert (T47 : TASK_SIZE = 2 ^ 47) by reflexivity; unfold SP in *; lia).
  assert (Hgg : ms_got_guard B = snprintf_c.GOT_GUARD) by (rewrite GGD; reflexivity).
  assert (Hgd : ms_guard B = snprintf_c.GUARD) by (rewrite GRD; reflexivity).
  pose proof (WRITE fx1 L1 A1 regs1 mem1 md1 b1 doc (if p then 1 else 0) t D Lam1 peak1 cnt1 fail1
    SEG Hgg Hgd (conj HP1 Hts) HI1 RO FZ G10 G11) as HWr.
  rewrite Ep in HWr.
  eapply SR_bind; [apply HWr | exact K].
  - destruct p; lia.
  - exact LG.
  - unfold CF.put_c.off_errno. rewrite ERR. unfold strtod_c.STRTOD_ERRNO, SP in *. lia.
  - rewrite <- SEG. exact HN.
  - left. split; [unfold SP in *; lia|]. unfold CF.put_c.off_errno. rewrite ERR. unfold strtod_c.STRTOD_ERRNO, SP in *. lia.
  - intros a k Hin. apply (Permutation_in (a, k) (Permutation_sym HP)). exact (DSUB Hd a k Hin).
  - lia.
  - exact Hdep.
  - unfold CF.put_c.WMAX. destruct p; lia.
  - exact RS.
  - exact Hg.
Qed.

Lemma crs_new_blk : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g x n,
  CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> ~ In (x, n) (blocks L1 A1) ->
  forall p0 n0, In (p0, n0) (user_blocks A) -> (ptr_addr L p0, n0) <> (x, n).
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g x n ((RP & _) & _) Hnin p0 n0 Hp0 E.
  pose proof RP as (_ & _ & _ & _ & _ & _ & _ & U & P9 & _).
  pose proof (U p0 n0 Hp0 (fun H => H)) as Hp1.
  apply Hnin. rewrite <- E. rewrite <- (P9 p0 n0 Hp0 Hp1). exact (cg_blk_of_user L1 A1 p0 n0 Hp1).
Qed.

Lemma crs_call_wfed : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g (p : bool)
    (P : config -> Prop),
  doc <> 0 ->
  CI L1 A1 mem1 md1 Lam1 peak1 cnt1 (2 ^ 64 - 1) b1 g -> Permutation Lam1 Lam ->
  CF.WriterRet.wr_rooms F b1 (w0 cnt1 (2 ^ 64 - 1)) (wdpieces t p) -> cnt1 + wN t p < 2 ^ 64 - 1 ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 (if p then 1 else 0) ->
  frm_zero (@fp_csr fx1) ->
  (forall (fx2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs2 mem2 md2 L2 A2 peak2 q,
     CI L2 A2 mem2 md2 ((q, crs_cap t p) :: Lam1) peak2 (cnt1 + wN t p) (2 ^ 64 - 1)
       (CF.WriterRet.wfold F b1 (w0 cnt1 (2 ^ 64 - 1)) (wdpieces t p)) (g + wN t p) ->
     (forall p0 n0, In (p0, n0) (user_blocks A) -> (ptr_addr L p0, n0) <> (q - 16, crs_cap t p + 16)) ->
     q <> 0 -> regs_preserved regs1 regs2 -> getr regs2 10 = Z_to_bv 64 q -> frm_zero (@fp_csr fx2) ->
     SR (ms_segs B) (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g p P Hd HC HP Hg Hcn Hsp Htp Hra G10 G11 FZ K.
  pose proof (crs_size_pos Hd) as Hs. pose proof crs_K as HK.
  pose proof HC as ((RP & _ & LG & _ & _ & Hg0) & _).
  assert (Hc0 : 0 <= cnt1) by (destruct LG as (_ & _ & H & _); lia).
  unfold wN, wcalls in Hcn.
  assert (Est : putN (w0 cnt1 (2 ^ 64 - 1)) (wdpieces t p) =
      mkW 0 (concat (wdpieces t p)) (crs_cap t p) (cnt1 + wN t p) (2 ^ 64 - 1) (wcalls t p)).
  { unfold wN, wcalls, crs_cap.
    rewrite putN_ok; cbn [w_failed w_text w_cap w_cnt w_fail w_calls w0 length app]; change (Z.of_nat 0) with 0;
      first [reflexivity | lia | (right; lia)]. }
  apply (crs_call_write fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 (2 ^ 64 - 1) b1 g p P Hd HC HP);
    [exact Hg | exact Hsp | exact Htp | exact Hra | exact G10 | exact G11 | exact FZ |].
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & b2 & -> & _ & FZ2 & RR & M' & WF' & B' & RO & _ &
    LG' & RS' & Ly & Rg & In' & Md & UK & KP & _ & FR & WS & Arms).
  rewrite Est in LG', Arms. cbn [w_failed w_cap w_calls w_cnt w_fail] in LG', Arms.
  destruct Arms as [(_ & q & Gq & Hq & Hnin & HLam & Hpk & Hb & _) | (Hf & _)]; [| exfalso; apply Hf; reflexivity].
  subst Lam2 b2.
  apply (K fx2 regs2 mem2 md2 L2 A2 peak2 q); [| | exact Hq | exact RR | exact Gq | exact FZ2].
  - apply (ci_write L1 A1 mem1 md1 Lam1 peak1 cnt1 (2 ^ 64 - 1) b1 g regs1 KW L2 A2 regs2 mem2 md2 _ peak2 _ _ _
      (g + wN t p) Hs HC KWP ltac:(lia) Hsp Htp Hra RR M' WF' B' RO LG' RS' Ly Rg In' Md UK KP FR WS);
      [rewrite Hpk; lia | unfold wN; lia].
  - exact (crs_new_blk L1 A1 mem1 md1 Lam1 peak1 cnt1 (2 ^ 64 - 1) b1 g _ _ HC Hnin).
Qed.

Lemma crs_call_wst : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g (p : bool) k
    (P : config -> Prop),
  doc <> 0 ->
  CI L1 A1 mem1 md1 Lam1 peak1 cnt1 (cnt1 + k) b1 g -> Permutation Lam1 Lam ->
  0 <= k < wN t p -> CF.WriterRet.wr_rooms F b1 (w0 cnt1 (cnt1 + k)) (wdpieces t p) -> cnt1 + k + 1 < 2 ^ 64 ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 (if p then 1 else 0) ->
  frm_zero (@fp_csr fx1) ->
  (forall (fx2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs2 mem2 md2 L2 A2 peak2,
     CI L2 A2 mem2 md2 Lam1 peak2 (cnt1 + (k + 1)) (2 ^ 64 - 1) (wstarve F b1 cnt1 (cnt1 + k) t p) (g + (k + 1)) ->
     regs_preserved regs1 regs2 -> getr regs2 10 = Z_to_bv 64 0 -> frm_zero (@fp_csr fx2) ->
     SR (ms_segs B) (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g p k P Hd HC HP Hk Hg Hcn Hsp Htp Hra G10 G11 FZ K.
  pose proof (crs_size_pos Hd) as Hs. pose proof crs_K as HK.
  pose proof HC as ((RP & _ & LG & _ & _ & Hg0) & _).
  assert (Hc0 : 0 <= cnt1) by (destruct LG as (_ & _ & H & _); lia).
  assert (Hkn : (Z.to_nat k < length (grow_calls 0 0 (piece_lens (wdpieces t p))))%nat)
    by (unfold wN, wcalls in Hk; lia).
  destruct (putN_starved (wdpieces t p) cnt1 (cnt1 + k) (Z.to_nat k) Hc0 ltac:(lia) Hkn ltac:(lia))
    as (Ef & Ec & Efl & Ecl).
  assert (Hlen : length (w_calls (putN (w0 cnt1 (cnt1 + k)) (wdpieces t p))) = S (Z.to_nat k))
    by (rewrite Ecl; apply firstn_length_le; lia).
  apply (crs_call_write fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 (cnt1 + k) b1 g p P Hd HC HP);
    [exact Hg | exact Hsp | exact Htp | exact Hra | exact G10 | exact G11 | exact FZ |].
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & b2 & -> & _ & FZ2 & RR & M' & WF' & B' & RO & _ &
    LG' & RS' & Ly & Rg & In' & Md & UK & KP & _ & FR & WS & Arms).
  rewrite Ec, Efl in LG'.
  replace (cnt1 + Z.of_nat (Z.to_nat k) + 1) with (cnt1 + (k + 1)) in LG' by lia.
  destruct Arms as [(Hf & _) | (_ & Gz & HLam & Hbr)]; [rewrite Ef in Hf; discriminate|].
  subst Lam2.
  assert (Eb : b2 = wstarve F b1 cnt1 (cnt1 + k) t p).
  { unfold wstarve. cbv zeta.
    destruct Hbr as [(Hz & _ & ->) | (Hz & _ & ->)];
      [rewrite (proj2 (Z.eqb_eq _ _) Hz) | rewrite (proj2 (Z.eqb_neq _ _) Hz)]; reflexivity. }
  rewrite Eb in RS'.
  apply (K fx2 regs2 mem2 md2 L2 A2 peak2); [| exact RR | exact Gz | exact FZ2].
  apply (ci_write L1 A1 mem1 md1 Lam1 peak1 cnt1 (cnt1 + k) b1 g regs1 KW L2 A2 regs2 mem2 md2 _ peak2 _ _ _
    (g + (k + 1)) Hs HC KWP ltac:(lia) Hsp Htp Hra RR M' WF' B' RO LG' RS' Ly Rg In' Md UK KP FR WS); [| lia].
  destruct Hbr as [(_ & Hpk & _) | (_ & Hpk & _)]; rewrite Hpk; lia.
Qed.

Lemma crs_call_free : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g q k
    (P : config -> Prop),
  0 < size ->
  CI L1 A1 mem1 md1 ((q, k) :: Lam1) peak1 cnt1 (2 ^ 64 - 1) b1 g ->
  (forall p0 n0, In (p0, n0) (user_blocks A) -> (ptr_addr L p0, n0) <> (q - 16, k + 16)) ->
  spZ regs1 = SP - 112 -> getr regs1 4 = getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 q ->
  (forall regs2 mem2 md2 L2 A2 Lam2,
     CI L2 A2 mem2 md2 Lam2 peak1 cnt1 (2 ^ 64 - 1) (rf_free F b1 (k + 16)) g -> Permutation Lam2 Lam1 ->
     regs_preserved regs1 regs2 ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 FUZZ_FREE) mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 cnt1 b1 g q k P Hs (HC0 & HCC) Hnew Hsp Htp Hra G10 K.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK. pose proof cg_ceil as Hc.
  destruct (ci_callpre L1 A1 mem1 md1 _ peak1 cnt1 _ b1 g regs1 ALLOC_STACK Hs HC0 ltac:(unfold ALLOC_STACK; lia)
    ltac:(lia) Hsp Htp Hra) as (HP1 & HI1 & _).
  pose proof HC0 as (RP & (RO & _) & LG & PK1 & RS & Hg0).
  pose proof HP1 as (M1 & _).
  pose proof LG as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  destruct (FB (q, k) (or_introl eq_refl)) as (Hk & Hblk & _ & Hnimg). cbn [fst snd] in Hk, Hblk, Hnimg.
  destruct (cg_blk_facts B API L1 A1 mem1 md1 (q - 16) (k + 16) M1 Hblk) as (Hb1 & Hb2 & _).
  eapply SR_bind; [apply (FREE fx1 L1 A1 regs1 mem1 md1 q k b1 ((q, k) :: Lam1) peak1 cnt1 (2 ^ 64 - 1) HP1 G10 LG RO
    (or_intror (or_introl eq_refl)) RS)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & RO2 & _ & In' & Lc & CP & Rg & _ & UK & Arms).
  destruct Arms as [(Hq0 & _) | (_ & _ & (l1 & l2 & E & LG2) & RS2)]; [lia|].
  pose proof CP as (M2 & WF2 & B2 & Ly & P2 & RR & Md & H12 & H14 & S15).
  assert (HPm : Permutation (l1 ++ l2) Lam1).
  { assert (H : Permutation ((q, k) :: Lam1) (l1 ++ (q, k) :: l2)) by (rewrite <- E; apply Permutation_refl).
    apply Permutation_sym. exact (Permutation_cons_app_inv l1 l2 H). }
  apply (K regs2 mem2 md2 L2 A2 (l1 ++ l2)); [| exact HPm | exact RR].
  unfold SP in *.
  assert (RP2 : rpost B API ALLOC_STACK L1 A1 regs1 mem1 md1 alloc_statics
      (fun a n => (a, n) = (q - 16, k + 16)) L2 A2 regs2 mem2 md2).
  { split; [exact M2|]. split; [exact WF2|]. split; [exact B2|]. split; [exact Ly|]. split; [exact In'|].
    split; [exact Lc|]. split; [exact Rg|].
    split; [intros p n Hp Hg; exact (UK p n Hp Hg)|].
    split; [exact P2|]. split; [exact RR|]. split; [exact Md|].
    split.
    { intros a Ha Hns He. apply H12; [left; exact Ha | | | exact Hns |].
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 mem1 md1 _ M1 Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L2 A2 mem2 md2 _ M2 Ho). lia.
      - intros [Hw|(_ & Hw)]; [apply He; unfold alloc_statics; left; exact Hw | lia]. }
    split.
    { intros a Ha Hno Hns He. apply H12; [right; exact Ha | exact (Hno L1 A1 mem1 md1 M1) |
        exact (Hno L2 A2 mem2 md2 M2) | exact Hns |].
      intros [Hw|(_ & Hw)]; [apply He; unfold alloc_statics; left; exact Hw|].
      apply (Hnimg (a - (q - 16)) ltac:(lia)). replace (q - 16 + (a - (q - 16))) with a by lia. exact Ha. }
    split; [intros p n i Hp Hp' Hi _; exact (H14 p n i Hp Hp' Hi)|].
    exact S15. }
  split; [split|].
  - apply (rp_seq B API KK L A regs mem md alloc_statics L1 A1 regs mem1 md1 ALLOC_STACK regs1 alloc_statics
      (fun a n => (a, n) = (q - 16, k + 16)) L2 A2 regs2 mem2 md2 regs RP RP2).
    + intros r _. reflexivity.
    + unfold ALLOC_STACK in *. lia.
    + lia.
    + unfold KK in *. lia.
    + unfold ALLOC_STACK. lia.
    + intros a _ _ He. exact He.
    + intros a _ _ He. exact He.
    + intros p n i _ _ _ He. exact He.
    + intros p n Hp _ Hg. exact (Hnew p n Hp Hg).
    + intros a Ha _. left. intros Hst. crs_stat Hst.
      unfold scratch_k in Ha. rewrite ERR in Ha. unfold strtod_c.STRTOD_ERRNO in Ha. lia.
  - split; [exact (crs_rd_post L2 A2 mem2 md2 RO2 M2)|]. split; [exact LG2|]. split; [exact PK1|].
    split; [exact RS2 | exact Hg0].
  - apply (crs_cc_eq mem1 mem2 HCC). intros x Hx. unfold SP in Hx.
    apply H12; [left; lia | | | | ].
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L1 A1 mem1 md1 _ M1 Ho). lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L2 A2 mem2 md2 _ M2 Ho). lia.
    + unfold scratch_k. rewrite ERR, Hsp. unfold strtod_c.STRTOD_ERRNO, ALLOC_STACK. lia.
    + intros [Hw|(_ & Hw)]; [unfold G_LIVE in Hw; lia | lia].
Qed.

Lemma crs_lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof.
  intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [lsum]; lia.
Qed.

Lemma crs_lsum_nonneg : forall L1 A1 m l pk c f, ledger B L1 A1 m l pk c f -> 0 <= lsum l.
Proof.
  intros L1 A1 m l pk c f (_ & _ & _ & _ & _ & FB). clear -FB. induction FB as [|[a k] l Hk _ IH]; cbn [lsum]; [lia|].
  destruct Hk as (Hk & _). cbn [snd] in Hk. lia.
Qed.

Lemma crs_mem_facts : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g,
  CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g -> Permutation Lam1 Lam ->
  Mem.bytes_at rsegs mem1 fuzz_alloc_live_c.G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam))) /\
  Mem.bytes_at rsegs mem1 fuzz_alloc_fail_c.G_COUNT (Mem.le8 (Z_to_bv 64 cnt1)) /\ 0 <= cnt1 < 2 ^ 64 /\
  Mem.wr_at rsegs mem1 fuzz_alloc_fail_c.G_FAIL_AT 8 /\
  m_halted md1 = None /\ m_vm_lazy md1 = [].
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g (RP & _ & LG & _) HP.
  pose proof RP as (M1 & _).
  pose proof (crs_lsum_nonneg _ _ _ _ _ _ _ LG) as Hl0.
  pose proof LG as ((W1 & W2 & W3 & W4) & Hl & Hc & Hf & _).
  rewrite (crs_lsum_perm _ _ HP) in W1, Hl, Hl0.
  unfold fuzz_alloc_live_c.G_LIVE, fuzz_alloc_fail_c.G_COUNT, fuzz_alloc_fail_c.G_FAIL_AT.
  unfold G_LIVE, G_COUNT, G_FAIL in W1, W3, W4.
  rewrite <- SEG.
  split; [apply (word_mem_le8 (ms_segs B)); [exact W1 | lia | lia | lia]|].
  split; [apply (word_mem_le8 (ms_segs B)); [exact W3 | lia | lia | lia]|].
  split; [lia|].
  split; [apply (globals_wr_at B API omx_G mem1 G_FAIL fail1 HG); [|exact W4]|].
  - intros k Hk. apply crs_glob. unfold alloc_statics, G_FAIL. lia.
  - exact (kb_md B API L1 A1 mem1 md1 M1).
Qed.

(* s5 (x21) is saved in the frame (CC) and restored by the epilogue; from 0x13d00 on it holds CRS_S5 (B5) *)
Definition BR (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = Z_to_bv 64 (SP - 112) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
  getr regs1 8 = Z_to_bv 64 (lsum Lam) /\ getr regs1 9 = Z_to_bv 64 doc /\
  (forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

Definition B5 (regs1 : bvmap 5 word) : Prop := getr regs1 21 = Z_to_bv 64 CF.CrsSegA.CRS_S5.

Lemma crs_b5_rr : forall regs1 regs2, B5 regs1 -> regs_preserved regs1 regs2 -> B5 regs2.
Proof. intros regs1 regs2 G RR. unfold B5 in *. rewrite <- G. apply (RR 21). unfold callee_saved. lia. Qed.

Lemma crs_pres : forall regsF, getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 ->
  getr regsF 4 = getr regs 4 -> getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 ->
  (forall r, 18 <= r <= 27 -> getr regsF (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> regs_preserved regs regsF.
Proof.
  intros regsF H2 H3 H4 H8 H9 H18 r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 | apply H18; lia].
Qed.

Lemma crs_sp_bv : Z_to_bv 64 SP = getr regs 2.
Proof. unfold SP, spZ. apply Z_to_bv_bv_unsigned. Qed.

Ltac crs_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM;
  subst R pc m; clear E.

Lemma crs_kA : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite SEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma crs_k_s8 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 b1,
  CI L1 A1 mem1 md1 Lam1 peak1 (cnt + G0) (2 ^ 64 - 1) b1 G0 -> Permutation Lam1 Lam -> Gp b1 ->
  BR regs1 -> B5 regs1 -> getr regs1 10 = Z_to_bv 64 0 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13e64) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 b1 (HC & HCC) HP HGb (G2 & G3 & G4 & G8 & G9 & G22) G21 G10 FZ.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK.
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  destruct (ci_flags _ _ _ _ _ _ _ _ _ _ HC) as (HO & HR).
  pose proof PRE as (_ & _ & _ & Hra & _).
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk. unfold B5 in G21. rewrite G2, G10, G21.
    apply (CF.CrsSegB.crs_s8 (getr regs1 1) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6) (getr regs1 7)
      (getr regs1 8) (getr regs1 9) (getr regs1 11) (getr regs1 12) (getr regs1 13) (getr regs1 14) (getr regs1 15)
      (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20) (getr regs1 22)
      (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28) (getr regs1 29)
      (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1 SP (cnt + G0)
      (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      FAILC LIVEC);
      [unfold SP in *; lia | unfold SP in *; lia | exact HCC | rewrite G8; exact HL | exact HCn | exact HCr | exact HW |
       exact HO | exact HR]. }
  { intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
    MU & WM & HF).
  crs_inj E R pc' mem'.
  apply SR_ret. rewrite (kb_ret_pc _ Hra).
  apply (crs_finish fx1 regs' m' md1 L1 A1 Lam1 peak1 b1); [| exact HP | exact FZ | | exact HGb].
  - apply (ci_tA0 L1 A1 mem1 md1 Lam1 peak1 (cnt + G0) (2 ^ 64 - 1) (2 ^ 64 - 1) b1 G0 _ m' HC MU WM).
    + intros x Hx _ Hf. cbn [Frame.outside]. split; [unfold fuzz_alloc_fail_c.G_FAIL_AT, G_FAIL in *; lia | exact I].
    + rewrite <- (crs_fa_m1 (cnt + G0) HCr). rewrite <- SEG in HF. exact (bytes_at_le8_word (ms_segs B) _ _ _ HF).
    + lia.
  - apply crs_pres; try (rewrite HGr; reflexivity).
    + rewrite HGr, <- crs_sp_bv. reflexivity.
    + rewrite HGr, <- G3. reflexivity.
    + rewrite HGr, <- G4. reflexivity.
    + intros r Hr.
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [->|[->|[->|[->|Hr']]]]; [rewrite HGr; reflexivity .. |].
      rewrite HGr, <- (G22 r ltac:(lia)).
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
Qed.

Definition gP : Z := if took =? 0 then 0 else PK + 1.
Definition kT : Z := pick (zb tb) (wN t true).
Definition kF : Z := pick (zb tb) (wN t false).
Definition g1 : Z := gP + wN t true.
Definition g2 : Z := g1 + kT + 1.
Definition g3 : Z := g2 + wN t false.

Lemma crs_wN : forall p, 1 <= wN t p.
Proof.
  intros p. unfold wN, wcalls. pose proof (grow_calls_nonempty (wdpieces t p) (wdpieces_nonempty t p)) as H.
  destruct (grow_calls 0 0 (piece_lens (wdpieces t p))) as [|c r]; [contradiction | cbn [length]; lia].
Qed.

Lemma crs_pk_lt : forall n, 0 < n -> 0 <= pick (zb tb) n < n.
Proof. intros n H. unfold pick. rewrite (proj2 (Z.eqb_neq n 0)) by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma crs_took_nn : 0 <= took.
Proof. rewrite TOOK. lia. Qed.

Lemma crs_gP : 0 <= gP /\ (took = 0 -> gP = 0) /\ (0 < took -> gP = PK + 1).
Proof.
  pose proof crs_took_nn as Ht. unfold gP. destruct (Z.eqb_spec took 0) as [E|E].
  - split; [lia|]. split; [reflexivity | lia].
  - pose proof (crs_pick ltac:(lia)). split; [lia|]. split; [lia | reflexivity].
Qed.

Lemma crs_G0n : doc = 0 -> G0 = gP.
Proof.
  intros Hd. unfold G0, crcs_growth, gP, PK. rewrite Hd. change (0 =? 0) with true. cbv iota beta.
  destruct (took =? 0); lia.
Qed.

Lemma crs_G0d : doc <> 0 ->
  G0 = gP + wN t true + pick (zb tb) (wN t true) + 1 + wN t false + pick (zb tb) (wN t false) + 1.
Proof.
  intros Hd. unfold G0, crcs_growth, gP, PK. rewrite (proj2 (Z.eqb_neq doc 0) Hd). cbv iota beta.
  destruct (took =? 0); lia.
Qed.

Lemma crs_wN_le : forall p, Z.of_nat (length (wdoc t p)) + 1 <= 2 ^ 62 ->
  wN t p <= Z.of_nat (length (wdoc t p)) + 1.
Proof. intros p H. unfold wN, wcalls, wdoc in *. exact (crs_wcalls_le (wdpieces t p) H). Qed.

Lemma crs_G0b : 0 <= G0 <= 2 ^ 30.
Proof.
  pose proof crs_took_nn as Htn.
  assert (Hl : length (zb tb) = length tb) by (unfold zb; apply length_map).
  assert (Htk : took <= 2 * size + 2).
  { rewrite TOOK. unfold ncalls. pose proof (G7_4 jr_strtod (zb tb) []) as H. rewrite Hl in H. lia. }
  pose proof crs_gP as (H1 & H2 & H3).
  assert (HgP : gP <= took).
  { destruct (Z.eq_dec took 0) as [E|E]; [rewrite (H2 E); lia|].
    rewrite (H3 ltac:(lia)). pose proof (crs_pick ltac:(lia)). lia. }
  destruct (Z.eq_dec doc 0) as [Hd|Hd].
  - rewrite (crs_G0n Hd). lia.
  - rewrite (crs_G0d Hd). destruct (DOCT Hd) as (_ & _ & Hw0 & Hw1 & _).
    pose proof (crs_wN_le true ltac:(lia)) as W1. pose proof (crs_wN_le false ltac:(lia)) as W0.
    pose proof (crs_wN true). pose proof (crs_wN false).
    pose proof (crs_pk_lt (wN t true) ltac:(lia)). pose proof (crs_pk_lt (wN t false) ltac:(lia)). lia.
Qed.

Lemma crs_ar : doc <> 0 ->
  1 <= wN t true /\ 1 <= wN t false /\ 0 <= kT < wN t true /\ 0 <= kF < wN t false /\ 0 <= gP /\
  g1 = gP + wN t true /\ g2 = g1 + kT + 1 /\ g3 = g2 + wN t false /\ G0 = g3 + kF + 1 /\ G0 <= 2 ^ 30 /\
  0 <= cnt < 2 ^ 62.
Proof.
  intros Hd. pose proof (crs_wN true) as H1. pose proof (crs_wN false) as H2.
  pose proof (crs_pk_lt (wN t true) ltac:(lia)) as H3. pose proof (crs_pk_lt (wN t false) ltac:(lia)) as H4.
  pose proof crs_gP as (H5 & _). pose proof crs_G0b as (_ & H6).
  pose proof (crs_G0d Hd) as H7. pose proof LED0 as (_ & _ & H8 & _).
  unfold g3, g2, g1, kT, kF. repeat split; lia.
Qed.

Lemma crs_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Lemma crs_doc_rng : doc <> 0 -> SP <= doc /\ doc + 56 <= 2 ^ 64.
Proof.
  intros Hd. destruct (DOCHI Hd) as (H1 & _). destruct (DOCT Hd) as (_ & HN & _).
  split; [exact H1 | exact (crs_node_top _ _ _ _ _ _ HN)].
Qed.

Definition DS (regs1 : bvmap 5 word) : Prop :=
  getr regs1 18 = Z_to_bv 64 size /\ getr regs1 19 = Z_to_bv 64 data.

Lemma crs_spz : forall regs1, BR regs1 -> spZ regs1 = SP - 112.
Proof.
  intros regs1 (G2 & _). pose proof crs_sp as Hs. pose proof crs_K as HK. unfold spZ. rewrite G2.
  apply crs_uns. unfold SP in *. lia.
Qed.

Lemma crs_br_rr : forall regs1 regs2, BR regs1 -> regs_preserved regs1 regs2 -> BR regs2.
Proof.
  intros regs1 regs2 (G2 & G3 & G4 & G8 & G9 & G21) RR.
  split; [rewrite <- G2; apply (RR 2); unfold callee_saved; lia|].
  split; [rewrite <- G3; apply (RR 3); unfold callee_saved; lia|].
  split; [rewrite <- G4; apply (RR 4); unfold callee_saved; lia|].
  split; [rewrite <- G8; apply (RR 8); unfold callee_saved; lia|].
  split; [rewrite <- G9; apply (RR 9); unfold callee_saved; lia|].
  intros r Hr. rewrite <- (G21 r Hr). apply RR. unfold callee_saved. lia.
Qed.

Lemma crs_ds_rr : forall regs1 regs2, DS regs1 -> regs_preserved regs1 regs2 -> DS regs2.
Proof.
  intros regs1 regs2 (G18 & G19) RR.
  split; [rewrite <- G18; apply (RR 18); unfold callee_saved; lia | rewrite <- G19; apply (RR 19); unfold callee_saved; lia].
Qed.

Lemma crs_s4_rr : forall regs1 regs2 v, getr regs1 20 = Z_to_bv 64 v -> regs_preserved regs1 regs2 ->
  getr regs2 20 = Z_to_bv 64 v.
Proof. intros regs1 regs2 v G RR. rewrite <- G. apply (RR 20). unfold callee_saved. lia. Qed.

Lemma crs_md : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g, CI0 L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  m_halted md1 = None /\ m_vm_lazy md1 = [].
Proof. intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ((M1 & _) & _). exact (kb_md B API L1 A1 mem1 md1 M1). Qed.

Lemma ci_seg : forall L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g mem2 f,
  CI L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g ->
  Frame.munch [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] mem1 mem2 ->
  Frame.wmono rsegs mem1 mem2 ->
  Mem.bytes_at rsegs mem2 fuzz_alloc_fail_c.G_FAIL_AT (Mem.le8 f) ->
  CI L1 A1 mem2 md1 Lam1 peak1 cnt1 (bv_unsigned f) b1 g.
Proof.
  intros L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 b1 g mem2 f HC MU WM HF.
  pose proof crs_sp as Hs. pose proof crs_K as HK.
  apply (ci_tA L1 A1 mem1 md1 Lam1 peak1 cnt1 fail1 (bv_unsigned f) b1 g _ mem2 HC MU WM).
  - intros x Hx _ Hf. cbn [Frame.outside]. split; [unfold fuzz_alloc_fail_c.G_FAIL_AT, G_FAIL in *; lia | exact I].
  - intros x Hx. cbn [Frame.outside]. split; [unfold fuzz_alloc_fail_c.G_FAIL_AT, SP in *; lia | exact I].
  - rewrite <- SEG in HF. unfold fuzz_alloc_fail_c.G_FAIL_AT in HF. exact (bytes_at_le8_word (ms_segs B) _ _ _ HF).
  - pose proof (bv_unsigned_in_range 64 f) as Hr. unfold bv_modulus in Hr. cbn in Hr. lia.
Qed.

Ltac crs_ret := unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Ltac crs_brs HGr G2 G3 G4 G8 G9 G22 :=
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
  [ rewrite HGr; first [exact G2 | reflexivity]
  | rewrite HGr; first [exact G3 | reflexivity]
  | rewrite HGr; first [exact G4 | reflexivity]
  | rewrite HGr; first [exact G8 | reflexivity]
  | rewrite HGr; first [exact G9 | reflexivity]
  | let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
    intros r Hr; rewrite HGr; try rewrite <- (G22 r Hr);
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
    destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity ].

Ltac crs_b5 HGr := unfold B5; rewrite HGr; reflexivity.

Lemma crs_cap_eq : forall c p, 0 <= c -> c + wN t p < 2 ^ 64 - 1 ->
  w_cap (putN (w0 c (2 ^ 64 - 1)) (wdpieces t p)) = crs_cap t p.
Proof.
  intros c p Hc0 Hcn. unfold wN, wcalls in Hcn.
  assert (Est : putN (w0 c (2 ^ 64 - 1)) (wdpieces t p) =
      mkW 0 (concat (wdpieces t p)) (crs_cap t p) (c + wN t p) (2 ^ 64 - 1) (wcalls t p)).
  { unfold wN, wcalls, crs_cap.
    rewrite putN_ok; cbn [w_failed w_text w_cap w_cnt w_fail w_calls w0 length app]; change (Z.of_nat 0) with 0;
      first [reflexivity | lia | (right; lia)]. }
  rewrite Est. reflexivity.
Qed.

Section Doc.
Variable b0 : rf_R F.
Hypothesis RM : crs_doc_rooms F b0 (cnt + gP) (zb tb) t.
Hypothesis HGd : Gp (crs_doc_fold F b0 (cnt + gP) (zb tb) t).

Definition bD1 : rf_R F := CF.WriterRet.wfold F b0 (w0 (cnt + gP) (2 ^ 64 - 1)) (wdpieces t true).
Definition bD2 : rf_R F := rf_free F bD1 (crs_cap t true + 16).
Definition bD3 : rf_R F := wstarve F bD2 (cnt + g1) (cnt + g1 + kT) t true.
Definition bD4 : rf_R F := CF.WriterRet.wfold F bD3 (w0 (cnt + g2) (2 ^ 64 - 1)) (wdpieces t false).
Definition bD5 : rf_R F := rf_free F bD4 (crs_cap t false + 16).
Definition bD6 : rf_R F := wstarve F bD5 (cnt + g3) (cnt + g3 + kF) t false.

Lemma crs_dfacts : doc <> 0 ->
  CF.WriterRet.wr_rooms F b0 (w0 (cnt + gP) (2 ^ 64 - 1)) (wdpieces t true) /\
  CF.WriterRet.wr_rooms F bD2 (w0 (cnt + g1) (cnt + g1 + kT)) (wdpieces t true) /\
  CF.WriterRet.wr_rooms F bD3 (w0 (cnt + g2) (2 ^ 64 - 1)) (wdpieces t false) /\
  CF.WriterRet.wr_rooms F bD5 (w0 (cnt + g3) (cnt + g3 + kF)) (wdpieces t false) /\
  Gp bD6.
Proof.
  intros Hd. pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0 & Hc).
  assert (C1 : wfull F b0 (cnt + gP) t true = bD2).
  { unfold wfull, bD2, bD1, FMAX. rewrite (crs_cap_eq (cnt + gP) true) by lia. reflexivity. }
  assert (C2 : crs_pass_fold F b0 (cnt + gP) (zb tb) t true = bD3).
  { unfold crs_pass_fold. rewrite C1. unfold bD3. fold kT. f_equal; lia. }
  assert (C3 : crs_pass_cnt (cnt + gP) (zb tb) t true = cnt + g2).
  { unfold crs_pass_cnt. fold kT. lia. }
  assert (C4 : wfull F bD3 (cnt + g2) t false = bD5).
  { unfold wfull, bD5, bD4, FMAX. rewrite (crs_cap_eq (cnt + g2) false) by lia. reflexivity. }
  assert (C5 : crs_doc_fold F b0 (cnt + gP) (zb tb) t = bD6).
  { unfold crs_doc_fold. rewrite C2, C3. unfold crs_pass_fold. rewrite C4. unfold bD6. fold kF. f_equal; lia. }
  pose proof RM as ((R1 & R2) & (R3 & R4)). rewrite C2, C3 in R3, R4. rewrite C1 in R2. rewrite C4 in R4.
  fold kT in R2. fold kF in R4. unfold FMAX in R1, R3.
  replace (cnt + gP + wN t true) with (cnt + g1) in R2 by lia.
  replace (cnt + g2 + wN t false) with (cnt + g3) in R4 by lia.
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  rewrite <- C5. exact HGd.
Qed.

Lemma crs_k_wst0 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g3) (cnt + g3 + kF) bD5 g3 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> getr regs1 1 = Z_to_bv 64 0x13e64 ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 0 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd HC HP HBR HB5 Gra G10 G11 FZ.
  pose proof (crs_dfacts Hd) as (R1 & R2 & R3 & R4 & HGb).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  apply (crs_call_wst fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 (cnt + g3) bD5 g3 false kF crs_post Hd HC HP).
  - exact AkF.
  - exact R4.
  - lia.
  - exact (crs_spz regs1 HBR).
  - exact (proj1 (proj2 (proj2 HBR))).
  - rewrite Gra. crs_ret.
  - exact G10.
  - exact G11.
  - exact FZ.
  - intros fx2 regs2 mem2 md2 L2 A2 peak2 HC2 RR G10' FZ2. rewrite Gra.
    apply (crs_k_s8 fx2 regs2 mem2 md2 L2 A2 Lam1 peak2 bD6); [| exact HP | exact HGb | exact (crs_br_rr regs1 regs2 HBR RR) |
      exact (crs_b5_rr regs1 regs2 HB5 RR) | exact G10' | exact FZ2].
    rewrite EG. replace (cnt + (g3 + kF + 1)) with (cnt + g3 + (kF + 1)) by lia.
    replace (g3 + kF + 1) with (g3 + (kF + 1)) by lia. exact HC2.
Qed.

Lemma crs_k_s7 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g3) (2 ^ 64 - 1) bD5 g3 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + g2) -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13e28) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd (HC & HCC) HP HBR HB5 (G18 & G19) G20 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  pose proof (crs_size_pos Hd) as Hs.
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  destruct (ci_flags _ _ _ _ _ _ _ _ _ _ HC) as (HO & HR).
  pose proof (ci_data _ _ _ _ _ _ _ _ _ _ Hs HC) as Hdat.
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk. pose proof HB5 as G21. unfold B5 in G21. rewrite G18, G19, G20, G21, <- DLEN.
    apply (CF.CrsSegB.crs_s7 (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
      (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 22) (getr regs1 23)
      (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28) (getr regs1 29) (getr regs1 30)
      (getr regs1 31) fp_regs fp_csr mem1 data (cnt + g2) (cnt + g3) tb COUNTC FAILC);
      [exact HCn | lia | lia | exact HW | exact Hdat | lia | exact DATA0 | exact HO | exact HR]. }
  { intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' & t4' & t5' & t6' & m' & E &
    MU & WM & HF).
  crs_inj E R pc' mem'.
  replace (cnt + g3 - (cnt + g2)) with (wN t false) in HF by lia.
  change (pick (zb tb) (wN t false)) with kF in HF.
  pose proof (ci_seg _ _ _ _ _ _ _ _ _ _ _ _ (conj HC HCC) MU WM HF) as HC2.
  rewrite (crs_fa (cnt + g3) kF ltac:(lia) ltac:(lia) ltac:(lia)) in HC2.
  apply (crs_k_wst0 fx1 regs' m' md1 L1 A1 Lam1 peak1 Hd HC2 HP).
  - crs_brs HGr G2 G3 G4 G8 G9 G22.
  - crs_b5 HGr.
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G9.
  - rewrite HGr. reflexivity.
  - exact FZ.
Qed.

Lemma crs_k_s6 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 q,
  doc <> 0 ->
  CI L1 A1 mem1 md1 ((q, crs_cap t false) :: Lam1) peak1 (cnt + g3) (2 ^ 64 - 1) bD4 g3 -> Permutation Lam1 Lam ->
  (forall p0 n0, In (p0, n0) (user_blocks A) -> (ptr_addr L p0, n0) <> (q - 16, crs_cap t false + 16)) ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + g2) -> getr regs1 10 = Z_to_bv 64 q ->
  frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13e24) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 q Hd HC HP Hnew HBR HB5 HDS G20 G10 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22).
  pose proof (crs_size_pos Hd) as Hs.
  destruct (crs_md _ _ _ _ _ _ _ _ _ _ (proj1 HC)) as (Hh & Hz).
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk.
    exact (CF.CrsSegA.crs_s6 (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
      (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20)
      (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27)
      (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  crs_inj HQ R pc' mem'.
  assert (HBR' : BR regs') by crs_brs HGr G2 G3 G4 G8 G9 G22.
  assert (Gra : getr regs' 1 = Z_to_bv 64 0x13e28) by (rewrite HGr; reflexivity).
  apply (crs_call_free fx1 regs' mem1 md1 L1 A1 Lam1 peak1 (cnt + g3) bD4 g3 q (crs_cap t false) crs_post Hs HC Hnew).
  - exact (crs_spz regs' HBR').
  - exact (proj1 (proj2 (proj2 HBR'))).
  - rewrite Gra. crs_ret.
  - rewrite HGr. exact G10.
  - intros regs2 mem2 md2 L2 A2 Lam2 HC2 HP2 RR. rewrite Gra.
    assert (RR1 : regs_preserved regs1 regs').
    { intros r Hr. rewrite HGr. unfold callee_saved in Hr.
      destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |].
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
    apply (crs_k_s7 fx1 regs2 mem2 md2 L2 A2 Lam2 peak1 Hd HC2 (Permutation_trans HP2 HP)
      (crs_br_rr regs' regs2 HBR' RR) (crs_b5_rr regs' regs2 (crs_b5_rr regs1 regs' HB5 RR1) RR)
      (crs_ds_rr regs' regs2 (crs_ds_rr regs1 regs' HDS RR1) RR)
      (crs_s4_rr regs' regs2 _ (crs_s4_rr regs1 regs' _ G20 RR1) RR) FZ).
Qed.

Lemma crs_k_wfed0 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g2) (2 ^ 64 - 1) bD3 g2 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + g2) -> getr regs1 1 = Z_to_bv 64 0x13e24 ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 0 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd HC HP HBR HB5 HDS G20 Gra G10 G11 FZ.
  pose proof (crs_dfacts Hd) as (R1 & R2 & R3 & R4 & HGb).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  apply (crs_call_wfed fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 (cnt + g2) bD3 g2 false crs_post Hd HC HP).
  - exact R3.
  - lia.
  - exact (crs_spz regs1 HBR).
  - exact (proj1 (proj2 (proj2 HBR))).
  - rewrite Gra. crs_ret.
  - exact G10.
  - exact G11.
  - exact FZ.
  - intros fx2 regs2 mem2 md2 L2 A2 peak2 q HC2 Hnew Hq RR G10' FZ2. rewrite Gra.
    apply (crs_k_s6 fx2 regs2 mem2 md2 L2 A2 Lam1 peak2 q Hd); [| exact HP | exact Hnew |
      exact (crs_br_rr regs1 regs2 HBR RR) | exact (crs_b5_rr regs1 regs2 HB5 RR) | exact (crs_ds_rr regs1 regs2 HDS RR) |
      exact (crs_s4_rr regs1 regs2 _ G20 RR) | exact G10' | exact FZ2].
    rewrite E3. replace (cnt + (g2 + wN t false)) with (cnt + g2 + wN t false) by lia. exact HC2.
Qed.

Lemma crs_k_s5 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g2) (2 ^ 64 - 1) bD3 g2 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 10 = Z_to_bv 64 0 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13dbc) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd (HC & HCC) HP HBR HB5 (G18 & G19) G10 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22).
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  destruct (ci_flags _ _ _ _ _ _ _ _ _ _ HC) as (HO & HR).
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk. pose proof HB5 as G21. unfold B5 in G21. rewrite G10, G21.
    apply (CF.CrsSegB.crs_s5 (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 11) (getr regs1 12) (getr regs1 13) (getr regs1 14)
      (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20)
      (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28)
      (getr regs1 29) (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1 (cnt + g2) FAILC LIVEC COUNTC);
      [rewrite G8; exact HL | exact HCn | exact HCr | exact HW | exact HO | exact HR]. }
  { intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & HF).
  crs_inj E R pc' mem'.
  pose proof (ci_seg _ _ _ _ _ _ _ _ _ _ _ _ (conj HC HCC) MU WM HF) as HC2.
  rewrite (crs_fa_m1 (cnt + g2) HCr) in HC2.
  apply (crs_k_wfed0 fx1 regs' m' md1 L1 A1 Lam1 peak1 Hd HC2 HP).
  - crs_brs HGr G2 G3 G4 G8 G9 G22.
  - crs_b5 HGr.
  - split; rewrite HGr; [exact G18 | exact G19].
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G9.
  - rewrite HGr. reflexivity.
  - exact FZ.
Qed.

Lemma crs_k_wst1 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g1) (cnt + g1 + kT) bD2 g1 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 1 = Z_to_bv 64 0x13dbc ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 1 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd HC HP HBR HB5 HDS Gra G10 G11 FZ.
  pose proof (crs_dfacts Hd) as (R1 & R2 & R3 & R4 & HGb).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  apply (crs_call_wst fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 (cnt + g1) bD2 g1 true kT crs_post Hd HC HP).
  - exact AkT.
  - exact R2.
  - lia.
  - exact (crs_spz regs1 HBR).
  - exact (proj1 (proj2 (proj2 HBR))).
  - rewrite Gra. crs_ret.
  - exact G10.
  - exact G11.
  - exact FZ.
  - intros fx2 regs2 mem2 md2 L2 A2 peak2 HC2 RR G10' FZ2. rewrite Gra.
    apply (crs_k_s5 fx2 regs2 mem2 md2 L2 A2 Lam1 peak2 Hd); [| exact HP | exact (crs_br_rr regs1 regs2 HBR RR) |
      exact (crs_b5_rr regs1 regs2 HB5 RR) | exact (crs_ds_rr regs1 regs2 HDS RR) | exact G10' | exact FZ2].
    rewrite E2. replace (cnt + (g1 + kT + 1)) with (cnt + g1 + (kT + 1)) by lia.
    replace (g1 + kT + 1) with (g1 + (kT + 1)) by lia. exact HC2.
Qed.

Lemma crs_k_s4 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + g1) (2 ^ 64 - 1) bD2 g1 -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + gP) -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13d2c) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd (HC & HCC) HP HBR HB5 (G18 & G19) G20 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  pose proof (crs_size_pos Hd) as Hs.
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  destruct (ci_flags _ _ _ _ _ _ _ _ _ _ HC) as (HO & HR).
  pose proof (ci_data _ _ _ _ _ _ _ _ _ _ Hs HC) as Hdat.
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk. pose proof HB5 as G21. unfold B5 in G21. rewrite G18, G19, G20, G21, <- DLEN.
    apply (CF.CrsSegB.crs_s4 (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
      (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 22) (getr regs1 23)
      (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28) (getr regs1 29) (getr regs1 30)
      (getr regs1 31) fp_regs fp_csr mem1 data (cnt + gP) (cnt + g1) tb COUNTC FAILC);
      [exact HCn | lia | lia | exact HW | exact Hdat | lia | exact DATA0 | exact HO | exact HR]. }
  { intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & HF).
  crs_inj E R pc' mem'.
  replace (cnt + g1 - (cnt + gP)) with (wN t true) in HF by lia.
  change (pick (zb tb) (wN t true)) with kT in HF.
  pose proof (ci_seg _ _ _ _ _ _ _ _ _ _ _ _ (conj HC HCC) MU WM HF) as HC2.
  rewrite (crs_fa (cnt + g1) kT ltac:(lia) ltac:(lia) ltac:(lia)) in HC2.
  apply (crs_k_wst1 fx1 regs' m' md1 L1 A1 Lam1 peak1 Hd HC2 HP).
  - crs_brs HGr G2 G3 G4 G8 G9 G22.
  - crs_b5 HGr.
  - split; rewrite HGr; first [reflexivity | rewrite <- DLEN; reflexivity].
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G9.
  - rewrite HGr. reflexivity.
  - exact FZ.
Qed.

Lemma crs_k_s3 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 q,
  doc <> 0 ->
  CI L1 A1 mem1 md1 ((q, crs_cap t true) :: Lam1) peak1 (cnt + g1) (2 ^ 64 - 1) bD1 g1 -> Permutation Lam1 Lam ->
  (forall p0 n0, In (p0, n0) (user_blocks A) -> (ptr_addr L p0, n0) <> (q - 16, crs_cap t true + 16)) ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + gP) -> getr regs1 10 = Z_to_bv 64 q ->
  frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13d28) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 q Hd HC HP Hnew HBR HB5 HDS G20 G10 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22).
  pose proof (crs_size_pos Hd) as Hs.
  destruct (crs_md _ _ _ _ _ _ _ _ _ _ (proj1 HC)) as (Hh & Hz).
  eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
  { unfold rmk.
    exact (CF.CrsSegA.crs_s3 (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
      (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20)
      (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27)
      (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem' regs' HQ HGr.
  crs_inj HQ R pc' mem'.
  assert (HBR' : BR regs') by crs_brs HGr G2 G3 G4 G8 G9 G22.
  assert (Gra : getr regs' 1 = Z_to_bv 64 0x13d2c) by (rewrite HGr; reflexivity).
  apply (crs_call_free fx1 regs' mem1 md1 L1 A1 Lam1 peak1 (cnt + g1) bD1 g1 q (crs_cap t true) crs_post Hs HC Hnew).
  - exact (crs_spz regs' HBR').
  - exact (proj1 (proj2 (proj2 HBR'))).
  - rewrite Gra. crs_ret.
  - rewrite HGr. exact G10.
  - intros regs2 mem2 md2 L2 A2 Lam2 HC2 HP2 RR. rewrite Gra.
    assert (RR1 : regs_preserved regs1 regs').
    { intros r Hr. rewrite HGr. unfold callee_saved in Hr.
      destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |].
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
    apply (crs_k_s4 fx1 regs2 mem2 md2 L2 A2 Lam2 peak1 Hd HC2 (Permutation_trans HP2 HP)
      (crs_br_rr regs' regs2 HBR' RR) (crs_b5_rr regs' regs2 (crs_b5_rr regs1 regs' HB5 RR1) RR)
      (crs_ds_rr regs' regs2 (crs_ds_rr regs1 regs' HDS RR1) RR)
      (crs_s4_rr regs' regs2 _ (crs_s4_rr regs1 regs' _ G20 RR1) RR) FZ).
Qed.

Lemma crs_k_wfed1 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1,
  doc <> 0 -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) b0 gP -> Permutation Lam1 Lam ->
  BR regs1 -> B5 regs1 -> DS regs1 -> getr regs1 20 = Z_to_bv 64 (cnt + gP) -> getr regs1 1 = Z_to_bv 64 0x13d28 ->
  getr regs1 10 = Z_to_bv 64 doc -> getr regs1 11 = Z_to_bv 64 1 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 PJ_WRITE_PC) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 Hd HC HP HBR HB5 HDS G20 Gra G10 G11 FZ.
  pose proof (crs_dfacts Hd) as (R1 & R2 & R3 & R4 & HGb).
  pose proof (crs_ar Hd) as (A1T & A1F & AkT & AkF & AgP & E1 & E2 & E3 & EG & HG0).
  apply (crs_call_wfed fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 (cnt + gP) b0 gP true crs_post Hd HC HP).
  - exact R1.
  - lia.
  - exact (crs_spz regs1 HBR).
  - exact (proj1 (proj2 (proj2 HBR))).
  - rewrite Gra. crs_ret.
  - exact G10.
  - exact G11.
  - exact FZ.
  - intros fx2 regs2 mem2 md2 L2 A2 peak2 q HC2 Hnew Hq RR G10' FZ2. rewrite Gra.
    apply (crs_k_s3 fx2 regs2 mem2 md2 L2 A2 Lam1 peak2 q Hd); [| exact HP | exact Hnew |
      exact (crs_br_rr regs1 regs2 HBR RR) | exact (crs_b5_rr regs1 regs2 HB5 RR) | exact (crs_ds_rr regs1 regs2 HDS RR) |
      exact (crs_s4_rr regs1 regs2 _ G20 RR) | exact G10' | exact FZ2].
    rewrite E1. replace (cnt + (gP + wN t true)) with (cnt + gP + wN t true) by lia. exact HC2.
Qed.

End Doc.

Lemma crs_k_b50 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 b1,
  CI L1 A1 mem1 md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) b1 gP -> Permutation Lam1 Lam ->
  (doc <> 0 -> crs_doc_rooms F b1 (cnt + gP) (zb tb) t) -> Gp (crs_after_doc F b1 (cnt + gP) (zb tb) doc t) ->
  BR regs1 -> DS regs1 -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13cfc) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 b1 (HC & HCC) HP HRM HGa HBR HDS FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22). pose proof HDS as (G18 & G19).
  pose proof crs_sp as Hsp0. pose proof crs_K as HK.
  pose proof PRE as (_ & _ & _ & Hra & _).
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  destruct (Z.eq_dec doc 0) as [Hd|Hd].
  - eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
    { unfold rmk. rewrite G2, G9, Hd.
      apply (CF.CrsSegA.crs_s2_ret (getr regs1 1) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
        (getr regs1 7) (getr regs1 8) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
        (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20)
        (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27)
        (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1 SP
        (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21));
        [unfold SP in *; lia | unfold SP in *; lia | exact HCC]. }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem' regs' HQ HGr.
    crs_inj HQ R pc' mem'.
    apply SR_ret. rewrite (kb_ret_pc _ Hra).
    apply (crs_finish fx1 regs' mem1 md1 L1 A1 Lam1 peak1 b1); [| exact HP | exact FZ | |
      unfold crs_after_doc in HGa; rewrite (proj2 (Z.eqb_eq doc 0) Hd) in HGa; exact HGa].
    + rewrite (crs_G0n Hd). exact HC.
    + apply crs_pres; try (rewrite HGr; reflexivity).
      * rewrite HGr, <- crs_sp_bv. reflexivity.
      * rewrite HGr, <- G3. reflexivity.
      * rewrite HGr, <- G4. reflexivity.
      * intros r Hr.
        assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          by lia.
        destruct Hr' as [->|[->|[->|[->|Hr']]]]; [rewrite HGr; reflexivity .. |].
        rewrite HGr, <- (G22 r ltac:(lia)).
        destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
  - pose proof (crs_doc_rng Hd) as (Hd1 & Hd2).
    destruct (ci_flags _ _ _ _ _ _ _ _ _ _ HC) as (HO & HR).
    eapply (crs_kA fx1 regs1 _ mem1 md1 _ crs_post Hh Hz).
    { unfold rmk.
      apply (CF.CrsSegA.crs_s2_write (getr regs1 1) (getr regs1 2) (getr regs1 3) (getr regs1 4) (getr regs1 5)
        (getr regs1 6) (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12)
        (getr regs1 13) (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19)
        (getr regs1 20) (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26)
        (getr regs1 27) (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) fp_regs fp_csr mem1 (cnt + gP)
        COUNTC); [rewrite G9, crs_uns; unfold SP in *; lia | exact HCn | exact HO | exact HR]. }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem' regs' HQ HGr.
    crs_inj HQ R pc' mem'.
    assert (HGd : Gp (crs_doc_fold F b1 (cnt + gP) (zb tb) t))
      by (unfold crs_after_doc in HGa; rewrite (proj2 (Z.eqb_neq doc 0) Hd) in HGa; exact HGa).
    apply (crs_k_wfed1 b1 (HRM Hd) HGd fx1 regs' mem1 md1 L1 A1 Lam1 peak1 Hd (conj HC HCC) HP).
    + crs_brs HGr G2 G3 G4 G8 G9 G22.
    + crs_b5 HGr.
    + split; rewrite HGr; [exact G18 | exact G19].
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. exact G9.
    + rewrite HGr. reflexivity.
    + exact FZ.
Qed.

Lemma crs_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crs_stk_norm : forall m lo hi, Frame.stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> Mem.ro_addr rsegs (Mem.wa a) = false) ->
  Frame.stk rsegs (MemNorm.normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hr. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b0 & Hb). specialize (Hr a Ha).
  unfold wview, Mem.mrd, MemNorm.normalize in *. cbv beta. rewrite Hr. split; [exact Hw | exists b0; exact Hb].
Qed.

Lemma crs_ro_glob : forall a, alloc_statics a -> Mem.ro_addr rsegs (Mem.wa a) = false.
Proof.
  intros a Ha. crs_stat Ha.
  destruct (HG a (crs_glob a Ha)) as (_ & _ & (seg & Hf & Hw) & _).
  rewrite SEG in Hf. apply (crs_ro_seg (Mem.wa a) seg); [rewrite Mem.wa_unsigned by lia; exact Hf | exact Hw].
Qed.

Lemma crs_kAn : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> MemNorm.ro_agree rsegs mem1 ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (MemNorm.normalize rsegs mem1)
    (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' m0 regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom rsegs)) ->
     MemNorm.mem_rel rsegs mem' m0 -> MemNorm.ro_same rsegs mem1 mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz Hro HE HS HK.
  apply (crs_kA fx1 regs1 pc mem1 md1
    (fun s => exists s0, Q s0 /\ MemNorm.ms_rel rsegs s s0 /\ MemNorm.ro_same rsegs mem1 (ms_mem s)) P Hh Hz).
  - eapply (MemNorm.evt_normalize rsegs); [exact crs_wx | exact Hro | exact HE].
  - intros ms' (s0 & HQ & Hrel & Hsame). destruct (HS s0 HQ) as (R & pc0 & m0 & ->).
    destruct ms' as [R' F' pc'' svc' rv' fc' m' ro'].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS] in *. subst.
    exists R, pc0, m'. reflexivity.
  - intros R pc' mem' regs' (s0 & HQ & Hrel & Hsame) HGr.
    destruct (HS s0 HQ) as (R0 & pc0 & m0 & E0). subst s0.
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS] in *.
    subst R0 pc0.
    exact (HK R pc' mem' m0 regs' HQ HR Hsame HGr).
Qed.

Lemma crs_took_size : 0 < took -> 0 < size.
Proof.
  intros Ht. rewrite <- DLEN. destruct (length tb) as [|n] eqn:E; [|lia].
  exfalso. apply length_zero_iff_nil in E. pose proof TOOK as T. rewrite E in T. vm_compute in T. lia.
Qed.

Lemma crs_k_s1 : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs1 mem1 md1 L1 A1 Lam1 peak1 b1,
  0 < took -> CI L1 A1 mem1 md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) b1 gP -> Permutation Lam1 Lam ->
  (doc <> 0 -> crs_doc_rooms F b1 (cnt + gP) (zb tb) t) -> Gp (crs_after_doc F b1 (cnt + gP) (zb tb) doc t) ->
  pj_zero (ms_segs B) mem1 (SP - 112) ->
  BR regs1 -> DS regs1 -> getr regs1 10 = Z_to_bv 64 (-1) -> frm_zero (@fp_csr fx1) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x13ce0) mem1 (seg_rom (ms_segs B))) md1) crs_post.
Proof.
  intros fx1 regs1 mem1 md1 L1 A1 Lam1 peak1 b1 Ht (HC & HCC) HP HRM HGa HZ HBR HDS G10 FZ.
  pose proof HBR as (G2 & G3 & G4 & G8 & G9 & G22). pose proof HDS as (G18 & G19).
  pose proof crs_sp as Hsp0. pose proof crs_K as HK.
  pose proof (crs_took_size Ht) as Hs.
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ HC HP) as (HL & HCn & HCr & HW & Hh & Hz).
  pose proof HC as (_ & (Hro & _) & _). rewrite SEG in Hro.
  pose proof (ci_pre L1 A1 mem1 md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) b1 gP Hs HC) as (HP1 & _).
  pose proof (kb_stk B API crs_img KK L1 A1 regs mem1 md1 HP1 ltac:(lia)) as Hstk.
  pose proof (crs_stk_sub mem1 _ _ (SP - KK) (SP - 112) Hstk ltac:(unfold SP; lia) ltac:(unfold SP; lia) ltac:(lia))
    as Hstk1.
  rewrite SEG in Hstk1.
  assert (Hn1 : Frame.stk rsegs (MemNorm.normalize rsegs mem1) (SP - KK) (SP - 112)).
  { apply crs_stk_norm; [exact Hstk1|]. intros a Ha. apply crs_ro_high. rewrite Mem.wa_unsigned by (unfold SP in *; lia).
    unfold SP in *. lia. }
  destruct HZ as (_ & HZb). rewrite SEG in HZb.
  eapply (crs_kAn fx1 regs1 _ mem1 md1 _ crs_post Hh Hz Hro).
  { unfold rmk. rewrite G2, G10.
    apply (CF.CrsSegA.crs_s1 (getr regs1 1) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6) (getr regs1 7)
      (getr regs1 8) (getr regs1 9) (getr regs1 11) (getr regs1 12) (getr regs1 13) (getr regs1 14) (getr regs1 15)
      (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20) (getr regs1 21) (getr regs1 22)
      (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27) (getr regs1 28) (getr regs1 29)
      (getr regs1 30) (getr regs1 31) fp_regs fp_csr (MemNorm.normalize rsegs mem1) SP (SP - KK) (-1) (cnt + gP)
      FAILC CRCC).
    - lia.
    - unfold SP in *. lia.
    - unfold SP in *. lia.
    - exact Hn1.
    - apply MemNorm.mem_inv_normalize.
    - lia.
    - lia.
    - exact (MemNorm.bytes_at_normalize rsegs mem1 _ _ Hro HZb).
    - rewrite G8. exact (MemNorm.bytes_at_normalize rsegs mem1 _ _ Hro HL).
    - exact (MemNorm.bytes_at_normalize rsegs mem1 _ _ Hro HCn).
    - exact HCr.
    - apply (MemNorm.wr_at_norm rsegs mem1 _ _ _ (MemNorm.mem_rel_normalize rsegs mem1 Hro) HW).
      intros i Hi. apply crs_ro_glob. unfold alloc_statics, G_FAIL, fuzz_alloc_fail_c.G_FAIL_AT. lia. }
  { intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' m0 regs' HQ HR Hsame HGr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
    MU & WM & _ & _ & HF).
  crs_inj E R pc' m0.
  pose proof (MemNorm.mem_rel_normalize rsegs mem1 Hro) as HR0.
  pose proof (MemNorm.munch_rel rsegs _ mem1 _ mem' m' HR0 HR Hsame MU) as MU'.
  pose proof (MemNorm.wmono_rel rsegs mem1 _ mem' m' HR0 HR Hsame WM) as WM'.
  pose proof (proj2 (MemNorm.bytes_at_rel rsegs mem' m' _ _ HR) HF) as HF'.
  assert (HC2 : CI L1 A1 mem' md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) b1 gP).
  { apply (ci_tA L1 A1 mem1 md1 Lam1 peak1 (cnt + gP) (2 ^ 64 - 1) (2 ^ 64 - 1) b1 gP _ mem' (conj HC HCC) MU' WM').
    - intros x Hx Hn Hf. cbn [Frame.outside]. split; [unfold SP in *; lia|].
      split; [unfold G_FAIL, fuzz_alloc_fail_c.G_FAIL_AT in *; lia | exact I].
    - intros x Hx. cbn [Frame.outside]. split; [unfold SP in *; lia|].
      split; [unfold fuzz_alloc_fail_c.G_FAIL_AT, SP in *; lia | exact I].
    - rewrite <- (crs_fa_m1 (cnt + gP) HCr). rewrite <- SEG in HF'. exact (bytes_at_le8_word (ms_segs B) _ _ _ HF').
    - lia. }
  apply (crs_k_b50 fx1 regs' mem' md1 L1 A1 Lam1 peak1 b1 HC2 HP HRM HGa); [| | exact FZ].
  - crs_brs HGr G2 G3 G4 G8 G9 G22.
  - split; rewrite HGr; [exact G18 | exact G19].
Qed.

Lemma ci0_start : CI0 L A mem md Lam peak cnt (2 ^ 64 - 1) b 0.
Proof.
  pose proof PRE as (HM & _). destruct (crs_libc L A mem md HM) as (Hl1 & Hl2 & _). pose proof cg_ceil as Hc.
  split; [exact (rp_refl B API SEG KK L A regs mem md alloc_statics PRE ltac:(lia) Hl1)|].
  split; [exact CELLS0|]. split; [exact LED0|]. split; [lia|]. split; [exact RES0 | lia].
Qed.

Lemma crs_wm_munch : forall m m' W a v, word_mem (ms_segs B) m a v -> Frame.munch W m m' -> 0 <= a ->
  a + 8 <= 2 ^ 64 -> (forall k, 0 <= k < 8 -> Frame.outside W (a + k)) -> word_mem (ms_segs B) m' a v.
Proof.
  intros m m' W a v Hw HM H0 H1 HO k Hk.
  rewrite (MemNorm.mbyte_munch (ms_segs B) W m m' (a + Z.of_nat k) HM); [exact (Hw k Hk) | lia | apply HO; lia].
Qed.

Lemma crs_k_entry : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState), frm_zero (@fp_csr fx1) ->
  getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 took -> getr regs 13 = Z_to_bv 64 doc ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs (Z_to_bv 64 CRCS) mem (seg_rom (ms_segs B))) md) crs_post.
Proof.
  intros fx1 FZ G10 G11 G12 G13.
  pose proof crs_sp as Hsp0. pose proof crs_K as HK. pose proof cg_ceil as Hc.
  pose proof PRE as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  pose proof (kb_stk B API crs_img KK L A regs mem md PRE ltac:(lia)) as Hstk.
  pose proof (crs_stk_sub mem _ _ (SP - 112) SP Hstk ltac:(unfold SP; lia) ltac:(unfold SP; lia) ltac:(lia)) as Hstk1.
  rewrite SEG in Hstk1.
  destruct (crs_mem_facts _ _ _ _ _ _ _ _ _ _ ci0_start (Permutation_refl Lam)) as (HL & HCn & HCr & HW & _ & _).
  pose proof LED0 as ((_ & _ & _ & W4) & _).
  assert (G22 : forall r, 22 <= r <= 27 -> getr regs (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by (intros; reflexivity).
  pose proof crs_took_nn as Htn.
  destruct (Z.eq_dec took 0) as [Ht|Ht].
  - eapply (crs_kA fx1 regs _ mem md _ crs_post Hh Hz).
    { unfold rmk. rewrite <- crs_sp_bv, G12, Ht.
      apply (CF.CrsSegA.crs_s0_skip (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 13) (getr regs 14) (getr regs 15)
        (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
        (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) fp_regs fp_csr mem SP (Z_to_bv 64 (lsum Lam)) LIVEC);
        [unfold SP in *; lia | unfold SP in *; lia | exact Hstk1 | exact HL]. }
    { intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
      eexists _, _, _. exact E. }
    intros R pc' mem' regs' HQ HGr.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
      MU & WM & HCC').
    crs_inj E R pc' mem'.
    assert (HC1 : CI L A m' md Lam peak cnt (2 ^ 64 - 1) b 0).
    { apply (ci_start m' (2 ^ 64 - 1) _ MU WM).
      - intros x Hx Hn _. cbn [Frame.outside]. split; [unfold SP in *; lia | exact I].
      - apply (crs_wm_munch mem m' _ G_FAIL _ W4 MU); [unfold G_FAIL; lia | unfold G_FAIL; lia |].
        intros k Hk. cbn [Frame.outside]. split; [unfold G_FAIL, SP in *; lia | exact I].
      - lia.
      - exact HCC'. }
    apply (crs_k_b50 fx1 regs' m' md L A Lam peak b); [| apply Permutation_refl | | | | | exact FZ].
    + rewrite (proj1 (proj2 crs_gP) Ht), Z.add_0_r. exact HC1.
    + intros Hd. rewrite (proj1 (proj2 crs_gP) Ht), Z.add_0_r. exact (ROOM0 Ht Hd).
    + rewrite (proj1 (proj2 crs_gP) Ht), Z.add_0_r. exact (GP0 Ht).
    + crs_brs HGr G12 G12 G12 G12 G13 G22.
    + split; rewrite HGr; [exact G11 | exact G10].
  - assert (Ht' : 0 < took) by lia. pose proof (crs_took_size Ht') as Hs.
    destruct (DBLK Hs) as (ba & bk & Hbin & _ & Hba & Hbk).
    destruct (cg_blk_facts B API L A mem md ba bk HM Hbin) as (Hb1 & Hb2 & _).
    assert (Hl : length (zb tb) = length tb) by (unfold zb; apply length_map).
    assert (Htk : took <= 2 * size + 2).
    { rewrite TOOK. unfold ncalls. pose proof (G7_4 jr_strtod (zb tb) []) as H. rewrite Hl in H. lia. }
    pose proof (crs_pick Ht') as Hpk.
    eapply (crs_kA fx1 regs _ mem md _ crs_post Hh Hz).
    { unfold rmk. rewrite <- crs_sp_bv, G10, G11, G12, <- DLEN.
      apply (CF.CrsSegA.crs_s0_parse (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
        (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
        (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
        fp_regs fp_csr mem SP data took cnt tb (Z_to_bv 64 (lsum Lam)) LIVEC FAILC);
        [unfold SP in *; lia | unfold SP in *; lia | exact Hstk1 | exact HL | exact HCn | exact HCr | exact HW |
         exact DBYT | unfold SP in *; lia | lia | exact DATA0]. }
    { intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
      eexists _, _, _. exact E. }
    intros R pc' mem' regs' HQ HGr.
    destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & HCC' & HF).
    crs_inj E R pc' mem'.
    change (pick (zb tb) took) with PK in HF.
    assert (HC1 : CI L A m' md Lam peak cnt (cnt + PK) b 0).
    { apply (ci_start m' (cnt + PK) _ MU WM).
      - intros x Hx Hn Hf. cbn [Frame.outside]. split; [unfold SP in *; lia|].
        split; [unfold G_FAIL, fuzz_alloc_fail_c.G_FAIL_AT in *; lia | exact I].
      - rewrite <- (crs_fa cnt PK ltac:(lia) ltac:(lia) ltac:(lia)). rewrite <- SEG in HF.
        exact (bytes_at_le8_word (ms_segs B) _ _ _ HF).
      - lia.
      - exact HCC'. }
    assert (HBR' : BR regs') by crs_brs HGr G12 G12 G12 G12 G13 G22.
    assert (HDS' : DS regs') by (split; rewrite HGr; first [reflexivity | rewrite <- DLEN; reflexivity]).
    assert (Gra : getr regs' 1 = Z_to_bv 64 0x13ce0) by (rewrite HGr; reflexivity).
    apply (crs_call_parse fx1 regs' m' crs_post Hs Ht' HC1).
    + exact (crs_spz regs' HBR').
    + rewrite HGr. reflexivity.
    + rewrite Gra. crs_ret.
    + rewrite HGr. reflexivity.
    + rewrite HGr, <- DLEN. reflexivity.
    + rewrite HGr. reflexivity.
    + exact FZ.
    + intros fx2 regs2 mem2 md2 L2 A2 Lam2 peak2 tr D' HPL Hct HC2 HP2 HZ2 RR G10' FZ2. rewrite Gra.
      assert (EgP : gP = PK + 1) by exact (proj2 (proj2 crs_gP) Ht').
      apply (crs_k_s1 fx2 regs2 mem2 md2 L2 A2 Lam2 peak2 (rf_frees F (rf_run F b tr) D') Ht');
        [| exact HP2 | | | exact HZ2 | exact (crs_br_rr regs' regs2 HBR' RR) | exact (crs_ds_rr regs' regs2 HDS' RR) |
         exact G10' | exact FZ2].
      * rewrite EgP. exact HC2.
      * intros Hd. rewrite EgP, <- Hct. exact (ROOM1 ltac:(lia) Hd tr D' HPL).
      * rewrite EgP, <- Hct. exact (GP1 ltac:(lia) tr D' HPL).
Qed.

Lemma crs_entry_all : forall (fx1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState), frm_zero (@fp_csr fx1) ->
  getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 took -> getr regs 13 = Z_to_bv 64 doc ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs (Z_to_bv 64 CRCS) mem (seg_rom (ms_segs B))) md) crs_post.
Proof using All. exact crs_k_entry. Qed.

End Run.
