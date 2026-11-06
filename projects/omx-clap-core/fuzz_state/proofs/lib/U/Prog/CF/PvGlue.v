From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.

Lemma vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Lemma pv_run : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall ms, Q ms -> exists R F pc' fc mem', ms = MState.MS R F pc' fc None mem' (seg_rom segs)) ->
  (forall R F pc' fc mem' regs', Q (MState.MS R F pc' fc None mem' (seg_rom segs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR segs (mkCfg (@mkst (mkFP F fc) regs' pc' mem' (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HS HK.
  eapply (evt_SR_canon segs (mkst regs pc mem (seg_rom segs)) Q md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQc & Heq).
  destruct (HS can HQc) as (R & F & pc' & fc & mem' & ->).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R fr' pcv' fc' m' regs' HQc). apply kb_getr_eqv. exact HR.
Qed.

Definition pv_mid (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (st_init_done A' = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> (forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 a) ->
     ~ (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) -> mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem' a).

Lemma mid_rpost : forall K L A regs mem md E L' A' regs' mem' md',
  pv_mid K (spZ regs) L A mem md E L' A' mem' md' -> regs_preserved regs regs' ->
  rpost B API K L A regs mem md E (fun _ _ => False) L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HR.
  unfold rpost, scratch_k.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [intros p n Hp _; exact (H8 p n Hp)|].
  split; [exact H9|]. split; [exact HR|]. split; [exact H10|].
  split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. exact H14.
Qed.

Lemma mid_E : forall K S L A mem md (E E' : Z -> Prop) L' A' mem' md',
  pv_mid K S L A mem md E L' A' mem' md' -> (forall a, E a -> E' a) -> pv_mid K S L A mem md E' L' A' mem' md'.
Proof.
  intros K S L A mem md E E' L' A' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [intros a Ha Hs He; apply H11; auto|].
  split; [intros a Ha Hn Hs He; apply H12; auto|].
  split; [intros p n i Hp Hp' Hi He; apply (H13 p n i); auto|]. exact H14.
Qed.

Lemma layout_le_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (E1 & E2 & E3 & E4) (F1 & F2 & F3 & F4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (F4 r ltac:(lia)). exact (E4 r Hr).
Qed.

Lemma mid_seq : forall K S L A mem md E1 L1 A1 mem1 md1 E2 L2 A2 mem2 md2,
  pv_mid K S L A mem md E1 L1 A1 mem1 md1 -> pv_mid K S L1 A1 mem1 md1 E2 L2 A2 mem2 md2 ->
  pv_mid K S L A mem md (fun a => E1 a \/ E2 a) L2 A2 mem2 md2.
Proof.
  intros K S L A mem md E1 L1 A1 mem1 md1 E2 L2 A2 mem2 md2
    (M1 & W1 & B1 & Y1 & I1 & X1 & R1 & K1 & P1 & D1 & F1 & G1 & U1 & S1)
    (M2 & W2 & B2 & Y2 & I2 & X2 & R2 & K2 & P2 & D2 & F2 & G2 & U2 & S2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split; [exact (layout_le_trans A A1 L L1 L2 Y1 Y2 R1)|].
  split; [intros H; exact (I2 (I1 H))|].
  split.
  { intros H i Hi.
    assert (E : st_init_done A1 = false) by (apply not_true_is_false; intros E0; rewrite (I2 E0) in H; discriminate).
    rewrite (X2 H i Hi). exact (X1 E i Hi). }
  split; [lia|].
  split; [intros p n Hp; exact (K2 p n (K1 p n Hp))|].
  split; [intros p n Hp Hp2; rewrite (P2 p n (K1 p n Hp) Hp2); exact (P1 p n Hp (K1 p n Hp))|].
  split; [destruct D1 as (v1 & ->); destruct D2 as (v2 & ->); exists v2; apply vm_twice|].
  split.
  { intros a Ha Hs He. destruct (F1 a Ha Hs (fun h => He (or_introl h))) as [A1e A1w].
    destruct (F2 a Ha Hs (fun h => He (or_intror h))) as [A2e A2w]. split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (G1 a Ha Hn Hs (fun h => He (or_introl h))) as [A1e A1w].
    destruct (G2 a Ha Hn Hs (fun h => He (or_intror h))) as [A2e A2w]. split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 Hi He. pose proof (K1 p n Hp) as Hp1.
    rewrite <- (P1 p n Hp Hp1). rewrite (U2 p n i Hp1 Hp2 Hi).
    - rewrite (P1 p n Hp Hp1). exact (U1 p n i Hp Hp1 Hi (fun h => He (or_introl h))).
    - rewrite (P1 p n Hp Hp1). exact (fun h => He (or_intror h)). }
  exact S2.
Qed.

Lemma mid_A : img_low B -> forall K S L A mem md mem' W (E : Z -> Prop),
  MR L A mem md -> WF A -> bounded A ->
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  Frame.munch W mem mem' -> Frame.wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (S - K <= x < S \/ errno_addr B <= x < errno_addr B + 4) \/ E x) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> ~ owned B L A x) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ Frame.outside W (ptr_addr L p + i) ->
     E (ptr_addr L p + i) /\ present mem' (ptr_addr L p + i)) ->
  pv_mid K S L A mem md E L A mem' md.
Proof.
  intros [HI _] K S L A mem md mem' W E HM HWF HB HS Hm Hw HW1 HW2 HW3.
  pose proof alloc_ceiling_lt as Hc. pose proof alloc_ceiling_val as Hc'.
  assert (HO : forall x, owned B L A x -> Frame.outside W x).
  { intros x Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hx.
    destruct (kb_outside_dec W x) as [H|H]; [exact H|]. exfalso. exact (HW2 x ltac:(lia) H Ho). }
  assert (HMR : MR L A mem' md).
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      apply (mbyte_munch segs W); [exact Hm | lia | exact (HO a Ho)].
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      apply (present_munch W mem); [exact Hm | lia | exact (HO a Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (kb_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
      + apply (present_munch W mem); [exact Hm | lia | exact Ho | exact Hp].
      + exact (proj2 (HW3 p n i Hin Hi Ho)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|].
  split.
  { intros _ i Hi. assert (Ho : owned B L A (ms_libc B + 8 + i)) by (right; unfold static_owned; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    apply (mbyte_munch segs W); [exact Hm | lia | exact (HO _ Ho)]. }
  split; [lia|]. split; [tauto|]. split; [reflexivity|].
  split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split.
  { intros a Ha Hs He. assert (Ha' : 0 <= a < 2 ^ 64) by lia.
    assert (Ho : Frame.outside W a).
    { destruct (kb_outside_dec W a) as [H|H]; [exact H|]. exfalso.
      destruct (HW1 a Ha' H) as [H'|H']; [exact (Hs H') | exact (He H')]. }
    split; [exact (mbyte_munch segs W mem mem' a Hm Ha' Ho) | exact (writable_munch segs W mem mem' a Hm Ha' Ho)]. }
  split.
  { intros a Hi _ Hs He. pose proof (HI a Hi) as Ha.
    assert (Ho : Frame.outside W a).
    { destruct (kb_outside_dec W a) as [H|H]; [exact H|]. exfalso.
      destruct (HW1 a ltac:(lia) H) as [H'|H']; [exact (Hs H') | exact (He H')]. }
    split; [exact (mbyte_munch segs W mem mem' a Hm ltac:(lia) Ho) |
            exact (writable_munch segs W mem mem' a Hm ltac:(lia) Ho)]. }
  split.
  { intros p n i Hin _ Hi He. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (_ & H1 & H2 & _).
    destruct (kb_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
    - exact (mbyte_munch segs W mem mem' (ptr_addr L p + i) Hm ltac:(lia) Ho).
    - exfalso. exact (He (proj1 (HW3 p n i Hin Hi Ho))). }
  intros a Ha. unfold writable_at. apply Hw. exact (HS a Ha).
Qed.

Lemma mid_of_rpost : forall K S Kc L A regs1 mem md (Ec E : Z -> Prop) L' A' regs2 mem' md',
  rpost B API Kc L A regs1 mem md Ec (fun _ _ => False) L' A' regs2 mem' md' ->
  S - K <= spZ regs1 - Kc -> spZ regs1 <= S ->
  (forall a, Ec a -> E a) ->
  (forall a, S - K <= a < S -> ~ (spZ regs1 - Kc <= a < spZ regs1) -> ~ Ec a) ->
  alloc_ceiling <= S - K -> S <= 2 ^ 64 ->
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  pv_mid K S L A mem md E L' A' mem' md'.
Proof.
  intros K S Kc L A regs1 mem md Ec E L' A' regs2 mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) W1 W2 HE HN Hc Hs HS.
  unfold scratch_k in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [intros p n Hp; exact (H8 p n Hp (fun h => h))|].
  split; [exact H9|]. split; [exact H11|].
  split.
  { intros a Ha Hn He. apply H12; [exact Ha | | intros h; exact (He (HE a h))].
    intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx]. }
  split.
  { intros a Hi Hno Hn He. apply H13; [exact Hi | exact Hno | | intros h; exact (He (HE a h))].
    intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx]. }
  split.
  { intros p n i Hp Hp' Hi He. apply (H14 p n i); [exact Hp | exact Hp' | exact Hi | intros h; exact (He (HE _ h))]. }
  intros a Ha.
  assert (D : (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4) \/
              ~ (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4)) by lia.
  destruct D as [D|D]; [exact (H15 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  apply (proj2 (H12 a ltac:(lia) D (HN a Ha ltac:(lia)))). exact (HS a (or_introl Ha)).
Qed.

Lemma mid_of_call : forall K S Kc L A regs1 mem md (Ec E : Z -> Prop) L' A' regs2 mem' md',
  call_post_k B MR Kc L A regs1 mem md Ec L' A' regs2 mem' md' ->
  MR L A mem md ->
  (st_init_done A = true -> st_init_done A' = true) ->
  (st_init_done A' = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) ->
  S - K <= spZ regs1 - Kc -> spZ regs1 <= S ->
  (forall a, Ec a -> E a) ->
  (forall a, S - K <= a < S -> ~ (spZ regs1 - Kc <= a < spZ regs1) -> ~ Ec a) ->
  alloc_ceiling <= S - K -> S <= 2 ^ 64 ->
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  pv_mid K S L A mem md E L' A' mem' md'.
Proof.
  intros K S Kc L A regs1 mem md Ec E L' A' regs2 mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HM HI HX HR HK W1 W2 HE HN Hc Hs HS.
  unfold scratch_k in *.
  assert (NO : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho.
    - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho). lia. }
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact HI|].
  split; [exact HX|]. split; [exact HR|]. split; [exact HK|].
  split; [exact H5|]. split; [exact H7|].
  split.
  { intros a Ha Hn He. destruct (NO a ltac:(lia)) as [N1 N2].
    apply H8; [left; exact Ha | exact N1 | exact N2 | | intros h; exact (He (HE a h))].
    intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx]. }
  split.
  { intros a Hi Hno Hn He.
    apply H8; [right; exact Hi | exact (Hno L A mem md HM) | exact (Hno L' A' mem' md' H1) | | intros h; exact (He (HE a h))].
    intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx]. }
  split; [intros p n i Hp Hp' Hi _; exact (H9 p n i Hp Hp' Hi)|].
  intros a Ha.
  assert (D : (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4) \/
              ~ (spZ regs1 - Kc <= a < spZ regs1 \/ errno_addr B <= a < errno_addr B + 4)) by lia.
  destruct D as [D|D]; [exact (H10 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  destruct (NO a ltac:(lia)) as [N1 N2].
  assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
  apply (proj2 (H8 a (or_introl Hh) N1 N2 D (HN a Ha ltac:(lia)))). exact (HS a (or_introl Ha)).
Qed.

Lemma word_mem_uniq : forall mem a v v', word_mem segs mem a v -> word_mem segs mem a v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
  intros mem a v v' H H' Hv Hv'.
  assert (E : forall k, (k < 8)%nat -> le_byte v 8 k = le_byte v' 8 k).
  { intros k Hk. specialize (H k Hk). specialize (H' k Hk).
    assert (H2 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in H2. rewrite !kb_byte_unsigned in H2. exact H2. }
  rewrite (kb_le8_digits v Hv), (kb_le8_digits v' Hv').
  rewrite !E by lia. reflexivity.
Qed.

Lemma auxv_join : forall sec lo1 lo2 mem, auxv_pre B sec lo1 mem -> auxv_pre B sec lo2 mem ->
  auxv_pre B sec (Z.max lo1 lo2) mem.
Proof.
  intros sec lo1 lo2 mem (av & ar & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10)
    (av' & ar' & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (Ea : av = av') by (apply (word_mem_uniq mem (ms_libc B + 8)); [exact A1 | exact B1 | lia | lia]).
  subst av'.
  assert (Er : ar = ar') by (apply (word_mem_uniq mem (av + 16 * 8 + 8)); [exact A3 | exact B3 | lia | lia]).
  subst ar'.
  exists av, ar. repeat (split; [assumption|]). lia.
Qed.

Lemma ledger_A : forall L A mem md mem' W Lam peak cnt fail,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     ~ alloc_statics x /\ (forall a k, In (a, k) Lam -> ~ (a - 16 <= x < a - 8))) ->
  ledger B L A mem' Lam peak cnt fail.
Proof.
  intros L A mem md mem' W Lam peak cnt fail HM (AW & R1 & R2 & R3 & ND & FB) Hm HW.
  assert (Out : forall x, 0 <= x < 2 ^ 64 -> (alloc_statics x \/ exists a k, In (a, k) Lam /\ a - 16 <= x < a - 8) ->
                  Frame.outside W x).
  { intros x Hx Hs. destruct (kb_outside_dec W x) as [H|H]; [exact H|]. exfalso.
    destruct (HW x Hx H) as [N1 N2]. destruct Hs as [Hs|(a & k & Hin & Hr)]; [exact (N1 Hs) | exact (N2 a k Hin Hr)]. }
  destruct AW as (W1 & W2 & W3 & W4).
  unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Out.
  split.
  { split; [|split; [|split]];
      (eapply (kb_word_munch segs mem mem' W); [eassumption | exact Hm |]);
      intros k Hk; (split; [unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|]); apply Out;
      unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact ND|].
  rewrite Forall_forall in FB |- *. intros [a k] Hin. specialize (FB _ Hin). cbn [fst snd] in *.
  destruct FB as (Hk & Hb & Hw & Hi). split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hi].
  destruct (lblock_user B L A mem a k (conj Hk (conj Hb (conj Hw Hi)))) as (q & Hq & Eq).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q (k + 16) HM Hq) as Rg. rewrite Eq in Rg.
  pose proof alloc_ceiling_lt.
  apply (kb_word_munch segs mem mem' W); [exact Hw | exact Hm |].
  intros j Hj. split; [lia|]. apply Out; [lia|]. right. exists a, k. split; [exact Hin | lia].
Qed.

Lemma mrd_eq : forall (m m' : word -> option byte) x, m' x = m x -> lib.Lib.Mem.mrd segs m' x = lib.Lib.Mem.mrd segs m x.
Proof. intros m m' x E. unfold lib.Lib.Mem.mrd. rewrite E. reflexivity. Qed.

Lemma rd_cells_A : forall mem mem' W, rd_cells B mem -> Frame.munch W mem mem' ->
  0 <= ms_got_guard B -> ms_got_guard B + 8 <= 2 ^ 64 -> 0 <= ms_guard B -> ms_guard B + 8 <= 2 ^ 64 ->
  (forall x : word, lib.Lib.Mem.ro_addr segs x = true -> Frame.outside W (bv_unsigned x)) ->
  (forall k, 0 <= k < 8 -> Frame.outside W (ms_got_guard B + k) /\ Frame.outside W (ms_guard B + k)) ->
  rd_cells B mem'.
Proof.
  intros mem mem' W (RO & G1 & g & G2) Hm Ha Hb Hc Hd Hro Hg.
  split.
  { intros x Hx. rewrite (mrd_eq mem mem' x (Hm x (Hro x Hx))). exact (RO x Hx). }
  split.
  { apply (kb_word_munch segs mem mem' W); [exact G1 | exact Hm |]. intros k Hk. split; [lia | exact (proj1 (Hg k Hk))]. }
  exists g. apply (kb_word_munch segs mem mem' W); [exact G2 | exact Hm |]. intros k Hk. split; [lia | exact (proj2 (Hg k Hk))].
Qed.

Lemma pre_callee : forall K f Kc L A regs mem md regs1 mem1 lo,
  call_pre_k B MR K L A regs mem md -> 0 <= f -> 0 <= Kc -> f + Kc <= K ->
  spZ regs1 = spZ regs - f -> spZ regs1 mod 16 = 0 ->
  getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  MR L A mem1 md -> Frame.wmono segs mem mem1 ->
  (st_init_done A = false -> auxv_pre B (ly_sec L) lo mem1) -> spZ regs1 <= lo ->
  call_pre_k B MR Kc L A regs1 mem1 md.
Proof.
  intros K f Kc L A regs mem md regs1 mem1 lo (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HW & Htp & Herr & Haux)
    Hf HK1 HfK Hsp Hal1 Htp1 Hra1 HM1 Hw Hax Hle.
  split; [exact HM1|]. split; [exact HWF|]. split; [exact HB|]. split; [exact Hra1|]. split; [exact Hal1|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (HW a ltac:(lia))|].
  split; [rewrite Htp1; exact Htp|].
  split; [intros a Ha; unfold writable_at; apply Hw; exact (Herr a Ha)|].
  intros Hd. exact (auxv_pre_mono B (ly_sec L) lo (spZ regs1) mem1 Hle (Hax Hd)).
Qed.

End G.
