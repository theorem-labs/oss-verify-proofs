From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 Contract FrameAPI KindBGlue AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem Frame Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv uslot_norm uslot_cut.
Import ListNotations.
Open Scope Z_scope.

Definition reqv (P : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall R R' m, (forall r, getr R' r = getr R r) -> P R m -> P R' m.

Section Seg.
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
Hypothesis MCF : forall fx : FPState, @malloc_contract_cf fx rc B API.
Hypothesis FCF : forall fx : FPState, @free_contract_cf fx rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Local Notation cut := (slot_cut B API K S L0 A0 mem0 md0 b0).

Definition seg_ev (pc : Z) (W : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop)
    (Pn : Z -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall (fx' : FPState) regs m0, frm_zero (@fp_csr fx') -> MemNorm.mem_inv_cj rsegs m0 -> P regs m0 ->
    Exec.evt rsegs (fun ms => exists R F' q fc' m0', ms = MState.MS R F' (Z_to_bv 64 q) fc' None m0' (seg_rom rsegs) /\
                     frm_zero fc' /\ Frame.munch W m0 m0' /\ Frame.wmono rsegs m0 m0' /\ Pn q R m0')
      (MState.MS (rmk regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None m0 (seg_rom rsegs)).

Lemma cut_step : forall pc hb P W Pn c,
  cut pc hb P c -> W_ok K S hb W -> (forall q, reqv (Pn q)) -> seg_ev pc W P Pn ->
  SR rsegs c (fun c' => exists q, cut q hb (Pn q) c').
Proof.
  intros pc hb P W Pn c HC HW HR HE.
  eapply SR_mono.
  { apply (cut_run B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD pc hb P W
      (fun R pc' F' fc' m0' => exists q, pc' = Z_to_bv 64 q /\ Pn q R m0') c HC HW).
    intros fx' regs m0 Hf HI HP. eapply Exec.evt_mono; [exact (HE fx' regs m0 Hf HI HP)|].
    intros ms (R & F' & q & fc' & m0' & E & H1 & H2 & H3 & H4).
    exists R, F', (Z_to_bv 64 q), fc', m0'. split; [exact E|]. split; [exact H1|]. split; [exact H2|].
    split; [exact H3|]. exists q. split; [reflexivity | exact H4]. }
  intros c' (fx'' & L & A & regs' & mem' & md & m0' & R & pc' & Ec & Hf & HFR & HREL & HRR & q & Eq & HP).
  subst c' pc'. exists q, fx'', L, A, regs', mem', md, m0'.
  split; [reflexivity|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exact (HR q R regs' m0' HRR HP).
Qed.

Definition MP (hb : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop) (n X res : Z)
    (regs' : bvmap 5 word) (m0' : word -> option byte) : Prop :=
  exists regs m0 bs, P regs m0 /\ regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 res /\
    4096 <= res /\ res mod 16 = 0 /\ res + n <= alloc_ceiling /\ (forall i, 0 <= i < n -> ~ in_img B (res + i)) /\
    Step.rw_cells rsegs m0' res [Cells.CB (Z.to_nat n) bs] /\
    agree m0 m0' X (S - X) /\ (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m0 m0' a k).

Definition FP (hb : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop) (X : Z)
    (regs' : bvmap 5 word) (m0' : word -> option byte) : Prop :=
  exists regs m0, P regs m0 /\ regs_preserved regs regs' /\
    agree m0 m0' X (S - X) /\ (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m0 m0' a k).

Lemma MP_reqv : forall hb P n X res, reqv (MP hb P n X res).
Proof.
  intros hb P n X res R R' m E (regs & m0 & bs & H1 & H2 & H3 & H4).
  exists regs, m0, bs. split; [exact H1|]. split; [exact (kb_preserved_getr regs R R' H2 E)|].
  split; [rewrite E; exact H3 | exact H4].
Qed.

Lemma FP_reqv : forall hb P X, reqv (FP hb P X).
Proof.
  intros hb P X R R' m E (regs & m0 & H1 & H2 & H3).
  exists regs, m0. split; [exact H1|]. split; [exact (kb_preserved_getr regs R R' H2 E) | exact H3].
Qed.

Lemma cut_mal : forall hb P n X pcr c,
  cut 0x17aec hb P c ->
  (forall regs m0, P regs m0 -> getr regs 1 = Z_to_bv 64 pcr /\ YK0s.ret_ok (getr regs 1) /\
     getr regs 10 = Z_to_bv 64 n /\ getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S -> 0 <= n -> room_slots (sb_hb b0 hb) n ->
  SR rsegs c (fun c' => exists res, cut pcr ((res, n) :: hb) (MP hb P n X res) c').
Proof.
  intros hb P n X pcr c HC HPR HX16 HXr Hn Hroom.
  eapply SR_mono.
  { apply (cut_malloc B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HMAL HLK HLIBC HGG HGD
      HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC hb P n X c HC); try assumption.
    intros regs m0 HP. destruct (HPR regs m0 HP) as (_ & H1 & H2 & H3 & H4). tauto. }
  intros c' (fx'' & L' & A' & regs & regs' & mem' & md' & m0 & m0' & res & Ec & Hf & HP & HFR & HREL & HRP & H10 &
    Hr1 & Hr2 & Hr3 & Hr4 & (bs & Hbs) & HA1 & HA2).
  exists res, fx'', L', A', regs', mem', md', m0'.
  destruct (HPR regs m0 HP) as (E1 & _). rewrite E1 in Ec.
  split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exists regs, m0, bs. repeat (split; [assumption|]). assumption.
Qed.

Lemma cut_fre : forall a n hb P X pcr c,
  cut 0x179ac ((a, n) :: hb) P c ->
  (forall regs m0, P regs m0 -> getr regs 1 = Z_to_bv 64 pcr /\ YK0s.ret_ok (getr regs 1) /\
     getr regs 10 = Z_to_bv 64 a /\ getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S ->
  SR rsegs c (cut pcr hb (FP hb P X)).
Proof.
  intros a n hb P X pcr c HC HPR HX16 HXr.
  eapply SR_mono.
  { apply (cut_free B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK HLIBC HGG HGD
      HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC a n hb P X c HC); try assumption.
    intros regs m0 HP. destruct (HPR regs m0 HP) as (_ & H1 & H2 & H3 & H4). tauto. }
  intros c' (fx'' & L' & A' & regs & regs' & mem' & md' & m0 & m0' & Ec & Hf & HP & HFR & HREL & HRP & HA1 & HA2).
  exists fx'', L', A', regs', mem', md', m0'.
  destruct (HPR regs m0 HP) as (E1 & _). rewrite E1 in Ec.
  split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exists regs, m0. repeat (split; [assumption|]). assumption.
Qed.

Definition ENV (hb : list (Z * Z)) (m0 : word -> option byte) : Prop :=
  Frame.stk rsegs m0 (S - K) S /\
  (forall a n, In (a, n) hb -> 4096 <= a /\ a + n <= alloc_ceiling /\ (forall i, 0 <= i < n -> nseg (a + i)) /\
     (0 <= n -> forall x, a + n <= x < 8 * ((a + n + 7) / 8) -> nseg x /\ m0 (Mem.wa x) <> None)).

Lemma cut_env : forall pc hb P c, cut pc hb P c -> cut pc hb (fun regs m0 => P regs m0 /\ ENV hb m0) c.
Proof.
  intros pc hb P c (fx' & L & A & regs & mem & md & m0 & Ec & Hf & HFR & HREL & HP).
  exists fx', L, A, regs, mem, md, m0. split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|].
  split; [exact HREL|]. split; [exact HP|].
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & HWF & HB & HID & _ & _ & _ & _ & HSTK & _ & _).
  pose proof alloc_ceiling_val as Hcv. pose proof alloc_ceiling_lt as Hcl. pose proof ceil_hi as Hch.
  split.
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Hn : nseg a) by (apply nseg_high; lia).
    assert (Hu : bv_unsigned (Mem.wa a) = a) by (apply Mem.wa_unsigned; lia).
    pose proof (HSTK a ltac:(left; exact Ha)) as W. unfold writable_at in W. rewrite HSEGS in W.
    change (Z_to_bv 64 a) with (Mem.wa a) in W.
    rewrite (wview_nseg mem (Mem.wa a)) in W by (rewrite Hu; exact Hn).
    rewrite (wview_nseg m0 (Mem.wa a)) by (rewrite Hu; exact Hn).
    rewrite (mrd_nseg m0 (Mem.wa a)) by (rewrite Hu; exact Hn).
    rewrite (norm_nseg mem m0 a HREL) by (first [exact Hn | unfold TASK_SIZE; lia]).
    split; [exact W|]. destruct (mem (Mem.wa a)) as [b|]; [exists b; reflexivity | contradiction]. }
  intros a n Hin.
  destruct (in_blocks L A a n (Permutation_in _ (Permutation_sym HPM) (in_or_app _ _ _ (or_introl Hin))))
    as (p & Hp & Ep).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as Hr. rewrite Ep in Hr.
  destruct (HFA fx') as (_ & _ & _ & _ & _ & SLK & _).
  split; [lia|]. split; [lia|]. split.
  { intros i Hi. apply (nseg_blk B HSEGS); [lia|]. rewrite <- Ep. exact (ax_blocks_img HAX L A mem md p n i HM Hp Hi). }
  intros Hn0 x Hx.
  pose proof (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p n HM Hp) as Hal. rewrite Ep in Hal.
  pose proof (Z.div_mod (a + n + 7) 8 ltac:(lia)) as Hd1. pose proof (Z.mod_pos_bound (a + n + 7) 8 ltac:(lia)) as Hd2.
  pose proof (Z.div_mod a 16 ltac:(lia)) as Hd3.
  assert (Hpos : 0 < n).
  { destruct (Z.eq_dec n 0) as [E|E]; [|lia]. subst n. exfalso. rewrite Z.add_0_r in *. lia. }
  assert (HNI : ~ in_img B (a + (n - 1))).
  { rewrite <- Ep. exact (ax_blocks_img HAX L A mem md p n (n - 1) HM Hp ltac:(lia)). }
  assert (Hxn : nseg x).
  { unfold nseg, IMG_LO, IMG_HI. destruct (Z_lt_le_dec (a + (n - 1)) 0x10000) as [H1|H1]; [left; lia|].
    destruct (Z_lt_le_dec (a + (n - 1)) 0x53000) as [H2|H2]; [|right; lia].
    exfalso. apply HNI. apply (in_img_hi B _ HSEGS). unfold IMG_LO, IMG_HI. lia. }
  split; [exact Hxn|].
  assert (HPx : present mem x).
  { apply (SLK L A mem md (ptr_addr L p) n x HM); [exact (blocks_in L A p n Hp) | rewrite Ep; exact Hx]. }
  destruct HPx as [bx Hbx].
  rewrite (norm_nseg mem m0 x HREL) by (first [exact Hxn | unfold TASK_SIZE; lia]).
  unfold Mem.wa. rewrite Hbx. discriminate.
Qed.

Lemma cut_step_cf : forall pc hb P W Pn c,
  cut pc hb P c -> W_ok K S hb W -> (forall q, reqv (Pn q)) -> seg_ev pc W P Pn ->
  SRcf B c (fun c' => exists q, cut q hb (Pn q) c').
Proof.
  intros pc hb P W Pn c HC HW HR HE.
  eapply SRcf_mono.
  { apply (cut_run_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HTHR HLOCK HHEAD pc hb P W
      (fun R pc' F' fc' m0' => exists q, pc' = Z_to_bv 64 q /\ Pn q R m0') c HC HW).
    intros fx' regs m0 Hf HI HP. eapply Exec.evt_mono; [exact (HE fx' regs m0 Hf HI HP)|].
    intros ms (R & F' & q & fc' & m0' & E & H1 & H2 & H3 & H4).
    exists R, F', (Z_to_bv 64 q), fc', m0'. split; [exact E|]. split; [exact H1|]. split; [exact H2|].
    split; [exact H3|]. exists q. split; [reflexivity | exact H4]. }
  intros c' (fx'' & L & A & regs' & mem' & md & m0' & R & pc' & Ec & Hf & HFR & HREL & HRR & q & Eq & HP).
  subst c' pc'. exists q, fx'', L, A, regs', mem', md, m0'.
  split; [reflexivity|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exact (HR q R regs' m0' HRR HP).
Qed.

Lemma cut_mal_cf : forall hb P n X pcr c,
  cut 0x17aec hb P c ->
  (forall regs m0, P regs m0 -> getr regs 1 = Z_to_bv 64 pcr /\ YK0s.ret_ok (getr regs 1) /\
     getr regs 10 = Z_to_bv 64 n /\ getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S -> 0 <= n -> room_ag (sb_hb b0 hb) n ->
  SRcf B c (fun c' => exists res, cut pcr ((res, n) :: hb) (MP hb P n X res) c').
Proof.
  intros hb P n X pcr c HC HPR HX16 HXr Hn Hroom.
  eapply SRcf_mono.
  { apply (cut_malloc_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HMAL HLK HLIBC HGG HGD
      HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC MCF LIMLAW hb P n X c HC); try assumption.
    intros regs m0 HP. destruct (HPR regs m0 HP) as (_ & H1 & H2 & H3 & H4). tauto. }
  intros c' (fx'' & L' & A' & regs & regs' & mem' & md' & m0 & m0' & res & Ec & Hf & HP & HFR & HREL & HRP & H10 &
    Hr1 & Hr2 & Hr3 & Hr4 & (bs & Hbs) & HA1 & HA2).
  exists res, fx'', L', A', regs', mem', md', m0'.
  destruct (HPR regs m0 HP) as (E1 & _). rewrite E1 in Ec.
  split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exists regs, m0, bs. repeat (split; [assumption|]). assumption.
Qed.

Lemma cut_fre_cf : forall a n hb P X pcr c,
  cut 0x179ac ((a, n) :: hb) P c ->
  (forall regs m0, P regs m0 -> getr regs 1 = Z_to_bv 64 pcr /\ YK0s.ret_ok (getr regs 1) /\
     getr regs 10 = Z_to_bv 64 a /\ getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S ->
  SRcf B c (cut pcr hb (FP hb P X)).
Proof.
  intros a n hb P X pcr c HC HPR HX16 HXr.
  eapply SRcf_mono.
  { apply (cut_free_cf B API K S L0 A0 mem0 md0 b0 HSEGS HAX HKS HS HTHR HLOCK HHEAD HFA HFRE HLK HLIBC HGG HGD
      HCTX HTP HERR HVML HDBL HDB HSC HSMC HMDC FCF a n hb P X c HC); try assumption.
    intros regs m0 HP. destruct (HPR regs m0 HP) as (_ & H1 & H2 & H3 & H4). tauto. }
  intros c' (fx'' & L' & A' & regs & regs' & mem' & md' & m0 & m0' & Ec & Hf & HP & HFR & HREL & HRP & HA1 & HA2).
  exists fx'', L', A', regs', mem', md', m0'.
  destruct (HPR regs m0 HP) as (E1 & _). rewrite E1 in Ec.
  split; [exact Ec|]. split; [exact Hf|]. split; [exact HFR|]. split; [exact HREL|].
  exists regs, m0. repeat (split; [assumption|]). assumption.
Qed.

End Seg.
