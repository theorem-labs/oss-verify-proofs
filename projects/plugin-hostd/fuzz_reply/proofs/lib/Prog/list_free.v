From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  Tac Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB RelayFrame HarnessRep ListRep
  ListFrame list_free_c memmove_c ListFreeRun ListFreeAux RelayRunT RelayRunF ListTr TrModel.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lf_not_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x O. cbn [outside] in O.
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); first [lia | exfalso; apply O; split; [lia | exact I]].
Qed.

Definition lf_or (P Q : Prop) : Prop := P \/ Q.

Definition lf_drops_t (rs : list (tad * list Z)) (k : nat) : list tev := recs_drop_tr (List.rev (skipn k rs)).

Lemma lf_drops_t_step : forall rs k d, (k < length rs)%nat ->
  lf_drops_t rs k = lf_drops_t rs (S k) ++ rec_drop_tr (nth k rs d).
Proof.
  intros rs k d H. unfold lf_drops_t, recs_drop_tr. rewrite (lf_skipn_cons rs k d H). cbn [List.rev].
  rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma nret_lf_drops_t : forall rs k, nretF (lf_drops_t rs k) = 0%nat.
Proof. intros rs k. apply nret_recs_drop. Qed.

Lemma lf_rec_drop_t : forall (nm : Z -> tad) (r : Z * list byte),
  rec_drop_tr (shr nm r) = [RFree (Z.of_nat (length (snd r)) + 1) (nm (fst r))].
Proof. intros nm r. unfold rec_drop_tr, rec_len, shr, bzs. cbn [fst snd]. rewrite length_map. reflexivity. Qed.

Lemma runF_app0 : forall F qs b (t1 t2 : trF), nretF t1 = 0%nat ->
  runF F qs b (t1 ++ t2) = runF F qs (runF F qs b t1) t2.
Proof. intros F qs b t1 t2 H. unfold runF, run_tr. rewrite run_from_app, H. reflexivity. Qed.

Section LFP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable Fr : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis NDB : blocks_nodup Bm API.
Hypothesis ERRNO_LOW : errno_addr Bm + 4 <= YM05.alloc_ceiling.
Hypothesis HFREE : ms_free Bm = 0x15664.
Local Notation MR := (aa_MR API).

Lemma lmid_EF : forall K sp (E E' Fa Fb : Z -> Prop) L A mem md L' A' mem' md',
  lmid Bm API K sp E Fa L A mem md L' A' mem' md' -> (forall a, E a -> E' a) -> (forall q, Fa q -> Fb q) ->
  lmid Bm API K sp E' Fb L A mem md L' A' mem' md'.
Proof.
  intros K sp E E' Fa Fb L A mem md L' A' mem' md' (M & W & B & LY & LN & SV & Z0 & OW & MD & FR & BK & SC) HE HF.
  split; [exact M|]. split; [exact W|]. split; [exact B|]. split; [exact LY|]. split; [exact LN|].
  split; [intros p n Hp Hn NF; apply SV; [exact Hp | exact Hn | intro X; exact (NF (HF _ X))]|].
  split; [exact Z0|]. split; [exact OW|]. split; [exact MD|].
  split; [intros a Ha N1 N2 N3 N4 N5; apply FR;
          [exact Ha | exact N1 | exact N2 | exact N3 | exact N4 | intro X; exact (N5 (HE _ X))]|].
  split; [intros p n i Hp Hp' NF Hi NE; apply (BK p n i);
          [exact Hp | exact Hp' | intro X; exact (NF (HF _ X)) | exact Hi | intro X; exact (NE (HE _ X))]|].
  exact SC.
Qed.

Section Run.
Hypothesis SEG : ms_segs Bm = rsegs.
Hypothesis FRC : free_contract_rt Bm API Fr.
Hypothesis FNC : free_null_contract Bm.
Hypothesis MMC : memmove_contract.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (bnd : rt_R Fr) (V CAP : Z) (recs : list (Z * list byte)) (junk : list byte) (lines : bool).

Local Notation LA := (bv_unsigned (getr regs (Z_to_bv 5 10))).
Local Notation S0 := (spZ regs).
Local Notation N := (Z.of_nat (length recs)).
Local Notation lst := (HL V CAP recs junk).
Local Notation ARRB := (concat (map text_rec recs) ++ junk).
Local Notation SRS := (map (shr (known_at L A)) recs).

Hypothesis PRE : call_pre_k Bm MR LIST_FREE_K L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis RO : ro_agree (ms_segs Bm) mem.
Hypothesis PLR : forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr (ms_segs Bm) (Z_to_bv 64 a) = false.
Hypothesis HDR : rw_cells (ms_segs Bm) mem LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)].
Hypothesis NCAP : N <= CAP < 2 ^ 30.
Hypothesis ARR : lf_or (CAP = 0 /\ V = 0) (0 < CAP /\ In (V, 16 * CAP) (blocks L A) /\
  rw_cells (ms_segs Bm) mem V [CB (Z.to_nat (16 * CAP)) ARRB]).
Hypothesis NDR : List.NoDup (map fst recs).
Hypothesis NVR : ~ In V (map fst recs).
Hypothesis RECS : forall r, In r recs -> In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A).
Hypothesis RES : rt_ok Fr A bnd.

Definition lfE (a : Z) : Prop := LA <= a < LA + 16.
Definition lfF (q : Z) : Prop := In q (list_blocks lst).

Definition lfval (k : Z) (x18 : word) (r : Z) : word :=
  match r with
  | 2 => Z_to_bv 64 (S0 - 32)
  | 8 => getr regs (Z_to_bv 5 10)
  | 9 => Z_to_bv 64 k
  | 18 => x18
  | _ => getr regs (Z_to_bv 5 r)
  end.

Definition lfRF (R : bvmap 5 word) (f : Z -> word) : Prop :=
  forall r, callee_saved r -> getr R (Z_to_bv 5 r) = f r.

Definition lfRFr (R : bvmap 5 word) (f : Z -> word) : Prop :=
  forall r, callee_saved r -> Sem.reg_get R (Z_to_bv 5 r) = f r.

Definition lfJ_t (k : nat) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model) : Prop :=
  lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m1 md1 /\
  st_init_done A1 = true /\ ro_agree (ms_segs Bm) m1 /\
  rt_ok Fr A1 (runF Fr [] bnd (lf_drops_t SRS k)) /\
  rw_cells (ms_segs Bm) m1 LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (Z.of_nat k)); C4 (Z_to_bv 64 CAP)] /\
  rw_cells (ms_segs Bm) m1 (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                      C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] /\
  (0 < CAP -> In (V, 16 * CAP) (blocks L1 A1) /\ rw_cells (ms_segs Bm) m1 V [CB (Z.to_nat (16 * CAP)) ARRB]) /\
  (0 < CAP -> sptr_of L1 A1 V = sptr_of L A V) /\
  (forall r, In r (firstn k recs) -> In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L1 A1)) /\
  (forall r, In r (firstn k recs) -> sptr_of L1 A1 (fst r) = sptr_of L A (fst r)) /\
  (list_blocks lst = [] -> blocks L1 A1 = blocks L A) /\
  (forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks lst) -> In (q, n) (blocks L1 A1)) /\
  (forall q n, In (q, n) (blocks L1 A1) -> In (q, n) (blocks L A) /\ ~ In q (map fst (skipn k recs))).

Definition LPOST_t (c' : config) : Prop :=
  exists L' A' regs' mem' md',
    c' = mkCfg (YK11.mkst regs' (getr regs (Z_to_bv 5 1)) mem' (seg_rom (ms_segs Bm))) md' /\
    relay_post Bm API LIST_FREE_K (fun a => LA <= a < LA + 16) (fun q => In q (list_blocks lst))
      L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (list_free_tr (sh_of (known_at L A) lst)) /\
       rt_ok Fr A' (runF Fr qs bnd (list_free_tr (sh_of (known_at L A) lst)))) /\
    ro_agree (ms_segs Bm) mem' /\
    list_at Bm L' A' mem' LA empty_list lines /\
    (list_blocks lst = [] -> blocks L' A' = blocks L A) /\
    (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks lst) -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (list_blocks lst)).

Ltac lf_rf1 H H2 :=
  simp_regs; cbn [lfval];
  first [ reflexivity | exact H2 | (f_equal; lia) | (apply H; unfold callee_saved; lia) ].

Ltac lf_rfr H H2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let C := fresh "C" in
  unfold lfRFr; intros r Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia);
  repeat (destruct C as [C|C]; [subst r; lf_rf1 H H2 |]); subst r; lf_rf1 H H2.

Lemma gfacts : MR L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs (Z_to_bv 5 1)) /\ S0 mod 16 = 0 /\
  YM05.alloc_ceiling + 8224 <= S0 /\ S0 < 2 ^ 63 /\
  (forall a, S0 - 8224 <= a < S0 -> writable_at (ms_segs Bm) mem a) /\
  getr regs (Z_to_bv 5 4) = Z_to_bv 64 (ms_tp Bm) /\
  (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> writable_at (ms_segs Bm) mem a) /\
  2 ^ 46 <= YM05.alloc_ceiling /\ YM05.alloc_ceiling < 2 ^ 47 /\ 0 <= LA /\ LA + 16 <= 2 ^ 21.
Proof.
  pose proof PRE as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (in_img_low Bm SEG LA (proj1 (proj1 (PLR LA ltac:(lia))))) as L0.
  pose proof (in_img_low Bm SEG (LA + 15) (proj1 (proj1 (PLR (LA + 15) ltac:(lia))))) as L1.
  unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK in HCE, HWS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HRA|]. split; [exact HAL|].
  split; [lia|]. split; [exact H63|]. split; [intros a Ha; apply HWS; lia|]. split; [exact HTP|].
  split; [exact HER|]. split; [lia|]. split; [exact ACL|]. lia.
Qed.

Lemma lf_RF_of : forall R R' f, lfRFr R f -> Regs6ss.xregs_eqv R R' -> lfRF R' f.
Proof. intros R R' f H X r Hr. exact (lf_get R R' (Z_to_bv 5 r) (f r) X (lf_nz r Hr) (H r Hr)). Qed.

Lemma hdr_disj : forall L1 A1 m1 md1 q n, MR L1 A1 m1 md1 -> In (q, n) (blocks L1 A1) -> 0 < n ->
  LA + 16 <= q \/ q + n <= LA.
Proof.
  intros L1 A1 m1 md1 q n HM H Hn.
  destruct (Z_le_gt_dec (LA + 16) q) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (q + n) LA) as [Y|Y]; [right; exact Y|]. exfalso.
  destruct (lf_blocks_in L1 A1 q n H) as (p & Hp & Ep).
  destruct (Z_le_gt_dec LA q) as [Z1|Z1].
  - apply (ax_blocks_img AX L1 A1 m1 md1 p n 0 HM Hp ltac:(lia)). rewrite Ep, Z.add_0_r.
    exact (proj1 (proj1 (PLR q ltac:(lia)))).
  - apply (ax_blocks_img AX L1 A1 m1 md1 p n (LA - q) HM Hp ltac:(lia)). rewrite Ep.
    replace (q + (LA - q)) with LA by lia. exact (proj1 (proj1 (PLR LA ltac:(lia)))).
Qed.

Lemma hdr_norm : forall m1 cs, ro_agree rsegs m1 -> rw_cells rsegs m1 LA cs -> Z.of_nat (cells_size cs) <= 16 ->
  rw_cells rsegs (normalize rsegs m1) LA cs.
Proof.
  intros m1 cs RO1 H Hs. apply rw_cells_normalize; [exact RO1 | exact H |].
  intros i Hi. rewrite <- SEG. exact (proj2 (PLR (LA + i) ltac:(lia))).
Qed.

Lemma arr_norm : forall L1 A1 m1 md1, MR L1 A1 m1 md1 -> In (V, 16 * CAP) (blocks L1 A1) -> ro_agree rsegs m1 ->
  rw_cells rsegs m1 V [CB (Z.to_nat (16 * CAP)) ARRB] ->
  rw_cells rsegs (normalize rsegs m1) V [CB (Z.to_nat (16 * CAP)) ARRB].
Proof.
  intros L1 A1 m1 md1 HM VB RO1 VA. apply rw_cells_normalize; [exact RO1 | exact VA |].
  intros i Hi. cbn [cells_size csize] in Hi.
  destruct (lf_blocks_in L1 A1 V (16 * CAP) VB) as (pv & Hpv & Epv).
  pose proof (mr_blocks_range _ _ (aa_laws API) L1 A1 m1 md1 pv _ HM Hpv) as BR. rewrite Epv in BR.
  pose proof (@YM05.alloc_ceiling_lt rc).
  apply (ro_addr_out Bm SEG); [lia|].
  intro X. apply (ax_blocks_img AX L1 A1 m1 md1 pv (16 * CAP) i HM Hpv ltac:(lia)). rewrite Epv. exact X.
Qed.

Lemma lmid_start : lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L A mem md.
Proof.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  apply (lmid_EF LIST_FREE_K S0 lfE lfE (fun _ => False) lfF L A mem md L A mem md);
    [| intros a X; exact X | intros q []].
  apply (lmid_A Bm API SEG AX LIST_FREE_K S0 lfE L A mem md mem [] HM HW HB).
  - unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
  - lia.
  - intros a [X|X]; [apply HWS; unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK in X; lia | apply HER; exact X].
  - apply munch_refl.
  - apply wmono_refl.
  - intros x _ O. exfalso. apply O. exact I.
  - intros x _ _. exact I.
Qed.

Lemma free_step_t : forall (k : Z) (x18 : word) L1 A1 R1 m1 md1 q n b (Q : config -> Prop),
  lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m1 md1 -> st_init_done A1 = true ->
  ro_agree (ms_segs Bm) m1 -> rt_ok Fr A1 b -> lfRF R1 (lfval k x18) -> YK0s.ret_ok (getr R1 (Z_to_bv 5 1)) ->
  In (q, n) (blocks L1 A1) -> 0 < n -> lfF q -> getr R1 (Z_to_bv 5 10) = Z_to_bv 64 q ->
  (forall L2 A2 R2 m2 md2 b1 b2,
     lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L2 A2 m2 md2 -> st_init_done A2 = true ->
     ro_agree (ms_segs Bm) m2 -> rt_ok Fr A2 (rt_free Fr b n (sptr_of L1 A1 q)) -> lfRF R2 (lfval k x18) ->
     blocks L1 A1 = b1 ++ (q, n) :: b2 -> blocks L2 A2 = b1 ++ b2 ->
     (forall q' n', In (q', n') (blocks L2 A2) -> sptr_of L2 A2 q' = sptr_of L1 A1 q') ->
     (forall a cs, rw_cells (ms_segs Bm) m1 a cs ->
        (LA <= a /\ a + Z.of_nat (cells_size cs) <= LA + 16) \/
        (S0 - 32 <= a /\ a + Z.of_nat (cells_size cs) <= S0) \/
        (exists q' n', In (q', n') (blocks L1 A1) /\ q' <> q /\ q' <= a /\ a + Z.of_nat (cells_size cs) <= q' + n') ->
        rw_cells (ms_segs Bm) m2 a cs) ->
     SR (ms_segs Bm) (mkCfg (YK11.mkst R2 (getr R1 (Z_to_bv 5 1)) m2 (seg_rom (ms_segs Bm))) md2) Q) ->
  SR (ms_segs Bm) (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x15664) m1 (seg_rom (ms_segs Bm))) md1) Q.
Proof.
  intros k x18 L1 A1 R1 m1 md1 q n b Q LM1 IN1 RO1 RS1 RF1 RA1 QB NP FQ A01 K.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  pose proof LM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (aa_laws API) as LAWS.
  destruct (lf_blocks_in L1 A1 q n QB) as (p & Hp & Ep).
  assert (G2 : getr R1 (Z_to_bv 5 2) = Z_to_bv 64 (S0 - 32)) by exact (RF1 2 ltac:(unfold callee_saved; lia)).
  assert (G4 : getr R1 (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4)) by exact (RF1 4 ltac:(unfold callee_saved; lia)).
  assert (SP1 : spZ R1 = S0 - 32).
  { change (spZ R1) with (bv_unsigned (getr R1 (Z_to_bv 5 2))). rewrite G2. apply unsigned_lit. lia. }
  assert (MRb : forall a, q <= a < q + n -> a < YM05.alloc_ceiling /\ ~ in_img Bm a).
  { intros a Ha. pose proof (mr_blocks_range _ _ LAWS L1 A1 m1 md1 p n M1 Hp) as BR. rewrite Ep in BR.
    split; [lia|]. intro X. apply (ax_blocks_img AX L1 A1 m1 md1 p n (a - q) M1 Hp ltac:(lia)). rewrite Ep.
    replace (q + (a - q)) with a by lia. exact X. }
  assert (CP : call_pre Bm MR L1 A1 R1 m1 md1).
  { apply call_pre_k_alloc.
    apply (lmid_pre Bm API LIST_FREE_K S0 lfE lfF L A regs mem md L1 A1 m1 md1 ALLOC_STACK 32 R1 PRE eq_refl LM1 IN1 SP1).
    - rewrite SP1. clear - HAL. Z.div_mod_to_equations. lia.
    - exact G4.
    - exact RA1.
    - lia.
    - unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia. }
  pose proof FRC as FC. unfold free_contract_rt in FC. rewrite HFREE in FC.
  eapply SR_bind.
  { apply (FC L1 A1 R1 m1 md1 p n b CP RO1 Hp); [rewrite Ep; exact A01 | exact RS1]. }
  intros c (L2 & A2 & R2 & m2 & md2 & -> & CPo & (b1 & b2 & EB1 & EB2) & BK & RO2 & GK & SURV & INI & LN & RS2).
  rewrite Ep in CPo, EB1, BK.
  apply call_post_k_alloc in CPo.
  pose proof CPo as (M2 & W2 & B2 & LY2 & PA2 & RP2 & VM2 & FR2 & BK2 & SW2).
  pose proof (YO10.user_block_ptrs_NoDup A1 W1) as ND1.
  assert (LMc : lmid Bm API LIST_FREE_K S0 (fun _ => False) (fun x => x = q) L1 A1 m1 md1 L2 A2 m2 md2).
  { apply (lmid_call Bm API AX CTX LIST_FREE_K S0 ALLOC_STACK L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 (fun x => x = q)
             M1 CPo).
    - intros a Ha X. destruct (MRb a X) as [X1 X2]. destruct Ha as [Ha|Ha]; [lia | exact (X2 Ha)].
    - rewrite SP1. unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
    - rewrite SP1. lia.
    - unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
    - lia.
    - intros a Ha. apply SC1. exact Ha.
    - intros p' n' Hp' _ NF. apply SURV; [exact Hp'|]. intros E'. subst p'. apply NF. exact Ep.
    - intros p' Hp'. apply SURV; [exact Hp'|]. intros E'. subst p'. pose proof (lf_ndf _ _ _ _ ND1 Hp Hp'). lia.
    - exact LN. }
  assert (LM2 : lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L2 A2 m2 md2).
  { apply (lmid_EF LIST_FREE_K S0 (fun a => lfE a \/ False) lfE (fun x => lfF x \/ x = q) lfF L A mem md L2 A2 m2 md2
      (lmid_trans Bm API LIST_FREE_K S0 lfE lfF (fun _ => False) (fun x => x = q) L A mem md L1 A1 m1 md1
         L2 A2 m2 md2 HW LM1 LMc)).
    - intros a [X|[]]. exact X.
    - intros x [X|X]; [exact X | subst x; exact FQ]. }
  assert (RF2 : lfRF R2 (lfval k x18)) by (intros r Hr; exact (eq_trans (RP2 r Hr) (RF1 r Hr))).
  pose proof (NDB L1 A1 m1 md1 M1) as NB1.
  pose proof (NDB L2 A2 m2 md2 M2) as NB2.
  assert (ESP : sptr_of L1 A1 q = p) by (rewrite <- Ep; exact (sptr_of_eq L1 A1 p n NB1 Hp)).
  assert (SK : forall q' n', In (q', n') (blocks L2 A2) -> sptr_of L2 A2 q' = sptr_of L1 A1 q').
  { intros q' n' H2.
    assert (H1 : In (q', n') (blocks L1 A1)) by (rewrite EB1; apply (lf_in_mid2 b1 b2 (q, n)); rewrite <- EB2; exact H2).
    assert (ND1b : List.NoDup (map fst (b1 ++ (q, n) :: b2))).
    { rewrite <- EB1. first [exact NB1 | apply NoDup_ListNoDup; exact NB1]. }
    assert (Hne : q' <> q) by (apply (lf_nd_mid b1 b2 q n q' n' ND1b); rewrite <- EB2; exact H2).
    destruct (sptr_of_spec L1 A1 q' n' NB1 H1) as (Hp1 & Ea1).
    set (p1 := sptr_of L1 A1 q') in *.
    assert (Hp2 : In (p1, n') (user_blocks A2)).
    { apply SURV; [exact Hp1|]. intros E'. apply Hne. rewrite <- Ea1, E'. exact Ep. }
    rewrite <- Ea1, <- (lf_addr A1 L1 L2 p1 n' W1 LY2 Hp1). exact (sptr_of_eq L2 A2 p1 n' NB2 Hp2). }
  apply (K L2 A2 R2 m2 md2 b1 b2 LM2 (INI IN1) RO2 ltac:(rewrite ESP; exact RS2) RF2 EB1 EB2 SK).
  intros a cs RW [Hh | [Hf | (q' & n' & Hq' & Hne & Hlo & Hhi)]].
  - apply (rw_cp_frame Bm API ALLOC_STACK L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 a cs CPo); [|exact RW].
    intros i Hi. destruct (PLR (a + i) ltac:(lia)) as [IP _].
    pose proof IP as (II & _ & _ & IE).
    split; [right; exact II|].
    split; [exact (lf_img_not_owned Bm API AX L1 A1 m1 md1 _ M1 IP)|].
    split; [exact (lf_img_not_owned Bm API AX L2 A2 m2 md2 _ M2 IP)|].
    split.
    + unfold scratch_k. rewrite SP1. intros [X|X]; [unfold ALLOC_STACK in X; lia | exact (IE X)].
    + intros X. exact (proj2 (MRb _ X) II).
  - apply (rw_cp_frame Bm API ALLOC_STACK L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 a cs CPo); [|exact RW].
    intros i Hi.
    split; [left; lia|].
    split; [intros X; pose proof (owned_low Bm MR LAWS L1 A1 m1 md1 _ M1 X); lia|].
    split; [intros X; pose proof (owned_low Bm MR LAWS L2 A2 m2 md2 _ M2 X); lia|].
    split; [unfold scratch_k; rewrite SP1; intros [X|X]; [unfold ALLOC_STACK in X; lia | lia]|].
    intros X. pose proof (proj1 (MRb _ X)). lia.
  - destruct (lf_blocks_in L1 A1 q' n' Hq') as (p' & Hp'1 & Ep').
    assert (Hp'2 : In (p', n') (user_blocks A2)).
    { apply SURV; [exact Hp'1|]. intros E'. subst p'. apply Hne. rewrite <- Ep'. exact Ep. }
    apply (rw_cp_block Bm API ALLOC_STACK L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 p' n' a cs CPo Hp'1 Hp'2);
      [rewrite Ep'; lia | rewrite Ep'; lia | exact RW].
Qed.

Lemma seg_step : forall L1 A1 R pc m1 md1 W (Pm : (word -> option byte) -> Prop)
    (Rp : bvmap 5 word -> word -> Prop) (Q : config -> Prop),
  lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m1 md1 -> ro_agree (ms_segs Bm) m1 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (S0 - LIST_FREE_K <= x < S0) \/ lfE x) ->
  evt rsegs (fun ms => exists R' pc' m', ms = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Rp R' pc' /\
       munch W (normalize rsegs m1) m' /\ wmono rsegs (normalize rsegs m1) m' /\ Pm m')
     (MS (Regs6ss.mkR_of R) fp_regs pc fp_csr None (normalize rsegs m1) (seg_rom rsegs)) ->
  (forall R0 R' pc' m2 m', Rp R0 pc' -> Regs6ss.xregs_eqv R0 R' -> munch W m1 m2 -> wmono rsegs m1 m2 ->
     ro_agree (ms_segs Bm) m2 -> mem_rel rsegs m2 m' -> Pm m' ->
     lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m2 md1 ->
     SR (ms_segs Bm) (mkCfg (YK11.mkst R' pc' m2 (seg_rom (ms_segs Bm))) md1) Q) ->
  SR (ms_segs Bm) (mkCfg (YK11.mkst R pc m1 (seg_rom (ms_segs Bm))) md1) Q.
Proof.
  intros L1 A1 R pc m1 md1 W Pm Rp Q LM1 RO1 HWE EV K.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  pose proof LM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (aa_laws API) as LAWS.
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh & Hl & _).
  pose proof RO1 as RO1'. rewrite SEG in RO1'.
  rewrite SEG.
  apply (lift_run R pc m1 md1 W Pm Rp Q Hh Hl RO1' EV).
  intros R0 R' pc' m2 m' HRp X MU WM RO2 MREL HPm.
  assert (RO2' : ro_agree (ms_segs Bm) m2) by (rewrite SEG; exact RO2).
  assert (LMa : lmid Bm API LIST_FREE_K S0 lfE (fun _ => False) L1 A1 m1 md1 L1 A1 m2 md1).
  { apply (lmid_A Bm API SEG AX LIST_FREE_K S0 lfE L1 A1 m1 md1 m2 W M1 W1 B1).
    - unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
    - lia.
    - exact SC1.
    - exact MU.
    - rewrite SEG. exact WM.
    - exact HWE.
    - intros x Hx Ho. destruct (lf_outside_dec W x) as [O|O]; [exact O|]. exfalso.
      destruct (HWE x ltac:(lia) O) as [Y|Y].
      + unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK in Y. lia.
      + exact (lf_img_not_owned Bm API AX L1 A1 m1 md1 x M1 (proj1 (PLR x Y)) Ho). }
  assert (LM2 : lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m2 md1).
  { apply (lmid_EF LIST_FREE_K S0 (fun a => lfE a \/ lfE a) lfE (fun x => lfF x \/ False) lfF L A mem md L1 A1 m2 md1
      (lmid_trans Bm API LIST_FREE_K S0 lfE lfF lfE (fun _ => False) L A mem md L1 A1 m1 md1 L1 A1 m2 md1
         HW LM1 LMa)).
    - intros a [Y|Y]; exact Y.
    - intros x [Y|[]]. exact Y. }
  rewrite <- SEG. exact (K R0 R' pc' m2 m' HRp X MU WM RO2' MREL HPm LM2).
Qed.

Lemma tail_t : forall L2 A2 R2 m2 md2 x18 pc, pc = Z_to_bv 64 0x14bd8 ->
  lmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L2 A2 m2 md2 -> st_init_done A2 = true ->
  ro_agree (ms_segs Bm) m2 -> rt_ok Fr A2 (runF Fr [] bnd (list_free_tr (sh_of (known_at L A) lst))) ->
  lfRF R2 (lfval 0 x18) ->
  rw_cells (ms_segs Bm) m2 LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)] ->
  rw_cells (ms_segs Bm) m2 (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                      C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] ->
  (list_blocks lst = [] -> blocks L2 A2 = blocks L A) ->
  (forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks lst) -> In (q, n) (blocks L2 A2)) ->
  (forall q n, In (q, n) (blocks L2 A2) -> In (q, n) (blocks L A) /\ ~ In q (list_blocks lst)) ->
  SR (ms_segs Bm) (mkCfg (YK11.mkst R2 pc m2 (seg_rom (ms_segs Bm))) md2) LPOST_t.
Proof.
  intros L2 A2 R2 m2 md2 x18 pc -> LM2 IN2 RO2 RS2 RF2 HD2 FR2 BE2 BA2 BB2.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  assert (G2 : getr R2 (Z_to_bv 5 2) = Z_to_bv 64 (S0 - 32)) by exact (RF2 2 ltac:(unfold callee_saved; lia)).
  assert (G8 : getr R2 (Z_to_bv 5 8) = Z_to_bv 64 LA).
  { rewrite (RF2 8 ltac:(unfold callee_saved; lia)). cbn [lfval]. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (SPu : bv_unsigned (getr R2 (Z_to_bv 5 2)) = S0 - 32) by (rewrite G2; apply unsigned_lit; lia).
  assert (SPE : Z_to_bv 64 (bv_unsigned (getr R2 (Z_to_bv 5 2)) + 32) = getr regs (Z_to_bv 5 2)).
  { rewrite SPu. replace (S0 - 32 + 32) with S0 by lia. apply Z_to_bv_bv_unsigned. }
  assert (RO2r : ro_agree rsegs m2) by (rewrite <- SEG; exact RO2).
  assert (HDn : rw_cells rsegs (normalize rsegs m2) LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)]).
  { apply hdr_norm; [exact RO2r | rewrite <- SEG; exact HD2 | cbn [cells_size csize]; lia]. }
  assert (FRn : rw_cells rsegs (normalize rsegs m2) (bv_unsigned (getr R2 (Z_to_bv 5 2)))
                  [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                   C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))]).
  { rewrite SPu. apply rw_cells_normalize; [exact RO2r | rewrite <- SEG; exact FR2 |].
    intros i Hi. cbn [cells_size csize] in Hi. apply ro_addr_hi. lia. }
  apply (seg_step L2 A2 R2 (Z_to_bv 64 0x14bd8) m2 md2 [(LA, LA + 16)]
    (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (fun R pc => pc = getr regs (Z_to_bv 5 1) /\ lfRFr R (fun r => getr regs (Z_to_bv 5 r))) LPOST_t LM2 RO2).
  - intros x Hx O. right. unfold lfE. exact (lf_not_out1 _ _ _ O).
  - rewrite lf_mkR_of, G8.
    eapply evt_mono.
    { eapply lf_segC; [exact FRn | exact HDn | rewrite SPu; lia]. }
    intros ms' (m' & -> & MU & WM & HZ & FZ).
    do 3 eexists. split; [reflexivity|].
    split.
    { split; [apply ret_pc_of_ok; exact HRA|]. lf_rfr RF2 SPE. }
    split; [exact MU|]. split; [exact WM|]. exact HZ.
  - intros R0 R' pc' m3 m' (Epc & HR0) X MU WM RO3 MREL HZ LM3. subst pc'.
    apply SR_ret. exists L2, A2, R', m3, md2.
    split; [reflexivity|].
    split.
    { apply (rp_of_lmid Bm API LIST_FREE_K lfE lfF L A regs mem md L2 A2 R' m3 md2 HW LM3).
      intros r Hr. exact (lf_get R0 R' (Z_to_bv 5 r) _ X (lf_nz r Hr) (HR0 r Hr)). }
    split; [exact IN2|]. split; [exists []; split; [exact (eq_sym (nret_list_free _)) | exact RS2]|].
    split; [exact RO3|].
    split.
    { split; [rewrite SEG; exact (rw_cells_of_rel rsegs m3 m' _ _ MREL HZ)|].
      split; [unfold hl_n, empty_list; cbn [hl_recs hl_cap length]; lia|]. split; [left; split; reflexivity|].
      split; [constructor|]. split; [intros []|]. constructor. }
    split; [exact BE2|]. split; [exact BA2|]. exact BB2.
Qed.

Lemma fin_t : forall L1 A1 R1 m1 md1 x18,
  lfJ_t 0 L1 A1 m1 md1 -> lfRF R1 (lfval 0 x18) -> getr R1 (Z_to_bv 5 1) = Z_to_bv 64 0x14bd8 ->
  getr R1 (Z_to_bv 5 10) = Z_to_bv 64 V ->
  SR (ms_segs Bm) (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x15664) m1 (seg_rom (ms_segs Bm))) md1) LPOST_t.
Proof.
  intros L1 A1 R1 m1 md1 x18 (LM1 & IN1 & RO1 & RS1 & HD1 & FR1 & AR1 & VX1 & TX1 & SX1 & BE1 & BA1 & BB1) RF1 RA1 A01.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  pose proof LM1 as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (TR : list_free_tr (sh_of (known_at L A) lst) =
               lf_drops_t SRS 0 ++ (if CAP =? 0 then [] else [RFree (16 * CAP) (Known (sptr_of L A V))]))
    by reflexivity.
  destruct ARR as [(C0 & V0) | (CP & VB & VA)].
  - destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
    pose proof FNC as FN. unfold free_null_contract in FN. rewrite HFREE in FN.
    eapply SR_bind.
    { apply (FN R1 m1 md1); [exact (eq_ind_r YK0s.ret_ok lf_ok8 RA1) | exact (eq_trans A01 (f_equal (Z_to_bv 64) V0))
                            | exact Hh | exact Hl]. }
    intros c ->.
    apply (tail_t L1 A1 R1 m1 md1 x18 _ RA1 LM1 IN1 RO1).
    + rewrite TR, C0. cbn [Z.eqb]. rewrite app_nil_r. exact RS1.
    + exact RF1.
    + exact HD1.
    + exact FR1.
    + exact BE1.
    + exact BA1.
    + intros q n H. destruct (BB1 q n H) as [H1 H2]. split; [exact H1|]. unfold list_blocks. cbn [hl_cap hl_v hl_recs].
      rewrite C0. cbn [Z.eqb app]. exact H2.
  - assert (VB1 : In (V, 16 * CAP) (blocks L1 A1)) by exact (proj1 (AR1 CP)).
    assert (CNZ : (CAP =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (VF : lfF V).
    { unfold lfF, list_blocks. cbn [hl_cap hl_v hl_recs]. rewrite CNZ. left. reflexivity. }
    assert (ND1 : List.NoDup (map fst (blocks L1 A1))).
    { first [exact (NDB L1 A1 m1 md1 M1) | apply NoDup_ListNoDup; exact (NDB L1 A1 m1 md1 M1)]. }
    apply (free_step_t 0 x18 L1 A1 R1 m1 md1 V (16 * CAP) (runF Fr [] bnd (lf_drops_t SRS 0)) LPOST_t
             LM1 IN1 RO1 RS1 RF1 ltac:(rewrite RA1; exact lf_ok8) VB1 ltac:(lia) VF A01).
    intros L2 A2 R2 m2 md2 b1 b2 LM2 IN2 RO2 RS2 RF2 EB1 EB2 SK2 TRN.
    rewrite EB1 in ND1.
    apply (tail_t L2 A2 R2 m2 md2 x18 _ RA1 LM2 IN2 RO2).
    + rewrite TR, CNZ, runF_app0 by apply nret_lf_drops_t. rewrite <- (VX1 CP). exact RS2.
    + exact RF2.
    + apply TRN; [exact HD1 | left; cbn [cells_size csize]; lia].
    + apply TRN; [exact FR1 | right; left; cbn [cells_size csize]; lia].
    + intros E. exfalso. unfold list_blocks in E. cbn [hl_cap hl_v hl_recs] in E. rewrite CNZ in E. discriminate.
    + intros q n H Hn. rewrite EB2. pose proof (BA1 q n H Hn) as H1. rewrite EB1 in H1.
      apply (lf_in_mid b1 b2 (V, 16 * CAP)); [exact H1|]. intros E. apply Hn. injection E as E1 _. rewrite E1.
      exact VF.
    + intros q n H. rewrite EB2 in H. pose proof (lf_nd_mid b1 b2 V (16 * CAP) q n ND1 H) as Hne.
      pose proof (lf_in_mid2 b1 b2 (V, 16 * CAP) _ H) as H1. rewrite <- EB1 in H1.
      destruct (BB1 q n H1) as [H2 H3]. split; [exact H2|].
      unfold list_blocks. cbn [hl_cap hl_v hl_recs]. rewrite CNZ. intros X. apply in_app_or in X.
      destruct X as [[X|[]]|X]; [exact (Hne (eq_sym X)) | exact (H3 X)].
Qed.

Lemma loop_t : forall k, (1 <= k <= length recs)%nat -> forall L1 A1 R1 m1 md1,
  lfJ_t k L1 A1 m1 md1 -> lfRF R1 (lfval (Z.of_nat k) (Z_to_bv 64 (16 * (Z.of_nat k - 1)))) ->
  getr R1 (Z_to_bv 5 1) = Z_to_bv 64 0x14ba4 ->
  getr R1 (Z_to_bv 5 10) = Z_to_bv 64 (fst (nth (k - 1) recs (0, []))) ->
  SR (ms_segs Bm) (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x15664) m1 (seg_rom (ms_segs Bm))) md1) LPOST_t.
Proof.
  induction k as [|k IH]; intros Hk L1 A1 R1 m1 md1 HJ RF1 RA1 A01; [lia|].
  pose proof HJ as (LM1 & IN1 & RO1 & RS1 & HD1 & FR1 & AR1 & VX1 & TX1 & SX1 & BE1 & BA1 & BB1).
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  pose proof LM1 as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (aa_laws API) as LAWS.
  assert (Hkl : (k < length recs)%nat) by lia.
  replace (S k - 1)%nat with k in A01 by lia.
  assert (CP : 0 < CAP) by lia.
  destruct (AR1 CP) as (VB1 & VA1).
  assert (RB1 : In (fst (nth k recs (0, [])), Z.of_nat (length (snd (nth k recs (0, [])))) + 1) (blocks L1 A1))
    by (apply TX1; apply lf_nth_firstn; exact Hkl).
  assert (RIN : In (nth k recs (0, [])) recs) by (apply nth_In; exact Hkl).
  assert (FQ : lfF (fst (nth k recs (0, [])))).
  { unfold lfF, list_blocks. apply in_or_app. right. apply in_map. exact RIN. }
  assert (RV : fst (nth k recs (0, [])) <> V) by (intros E; apply NVR; rewrite <- E; apply in_map; exact RIN).
  assert (ND1 : List.NoDup (map fst (blocks L1 A1))).
  { first [exact (NDB L1 A1 m1 md1 M1) | apply NoDup_ListNoDup; exact (NDB L1 A1 m1 md1 M1)]. }
  apply (free_step_t (Z.of_nat (S k)) (Z_to_bv 64 (16 * (Z.of_nat (S k) - 1))) L1 A1 R1 m1 md1
           (fst (nth k recs (0, []))) (Z.of_nat (length (snd (nth k recs (0, [])))) + 1)
           (runF Fr [] bnd (lf_drops_t SRS (S k))) LPOST_t
           LM1 IN1 RO1 RS1 RF1 ltac:(rewrite RA1; exact lf_ok4) RB1 ltac:(lia) FQ A01).
  intros L2 A2 R2 m2 md2 b1 b2 LM2 IN2 RO2 RS2 RF2 EB1 EB2 SK2 TRN.
  rewrite RA1.
  rewrite EB1 in ND1.
  pose proof LM2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (HD2 : rw_cells (ms_segs Bm) m2 LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (Z.of_nat (S k)));
                                              C4 (Z_to_bv 64 CAP)])
    by (apply TRN; [exact HD1 | left; cbn [cells_size csize]; lia]).
  assert (FR2 : rw_cells (ms_segs Bm) m2 (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                                   C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))])
    by (apply TRN; [exact FR1 | right; left; cbn [cells_size csize]; lia]).
  assert (VB2 : In (V, 16 * CAP) (blocks L2 A2)).
  { rewrite EB2. apply (lf_in_mid b1 b2 (fst (nth k recs (0, [])), Z.of_nat (length (snd (nth k recs (0, [])))) + 1));
      [rewrite <- EB1; exact VB1 | intros E; injection E as E1 _; exact (RV (eq_sym E1))]. }
  assert (VR : 4096 <= V /\ V + 16 * CAP <= YM05.alloc_ceiling).
  { destruct (lf_blocks_in L2 A2 V (16 * CAP) VB2) as (pv & Hpv & Epv).
    pose proof (mr_blocks_range _ _ LAWS L2 A2 m2 md2 pv _ M2 Hpv) as BR. rewrite Epv in BR. exact BR. }
  assert (VA2 : rw_cells (ms_segs Bm) m2 V [CB (Z.to_nat (16 * CAP)) ARRB]).
  { apply TRN; [exact VA1|]. right. right. exists V, (16 * CAP). split; [exact VB1|].
    split; [exact (not_eq_sym RV)|]. cbn [cells_size csize]. lia. }
  assert (TX2 : forall r', In r' (firstn k recs) -> In (fst r', Z.of_nat (length (snd r')) + 1) (blocks L2 A2)).
  { intros r' H. rewrite EB2.
    apply (lf_in_mid b1 b2 (fst (nth k recs (0, [])), Z.of_nat (length (snd (nth k recs (0, [])))) + 1)).
    - rewrite <- EB1. apply TX1. apply lf_firstn_S. exact H.
    - intros E. injection E as E1 _. exact (lf_fst_ne recs k r' Hkl NDR H E1). }
  assert (VX2 : 0 < CAP -> sptr_of L2 A2 V = sptr_of L A V).
  { intros _. rewrite (SK2 V (16 * CAP) VB2). exact (VX1 CP). }
  assert (SX2 : forall r', In r' (firstn k recs) -> sptr_of L2 A2 (fst r') = sptr_of L A (fst r')).
  { intros r' H. rewrite (SK2 _ _ (TX2 r' H)). exact (SX1 r' (lf_firstn_S recs k r' H)). }
  assert (BA2 : forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks lst) -> In (q, n) (blocks L2 A2)).
  { intros q n H Hn. rewrite EB2.
    apply (lf_in_mid b1 b2 (fst (nth k recs (0, [])), Z.of_nat (length (snd (nth k recs (0, [])))) + 1)).
    - rewrite <- EB1. exact (BA1 q n H Hn).
    - intros E. apply Hn. injection E as E1 _. rewrite E1. exact FQ. }
  assert (BB2 : forall q n, In (q, n) (blocks L2 A2) -> In (q, n) (blocks L A) /\ ~ In q (map fst (skipn k recs))).
  { intros q n H. rewrite EB2 in H. pose proof (lf_nd_mid b1 b2 _ _ q n ND1 H) as Hne.
    pose proof (lf_in_mid2 b1 b2 (fst (nth k recs (0, [])), Z.of_nat (length (snd (nth k recs (0, [])))) + 1) _ H)
      as H1.
    rewrite <- EB1 in H1. destruct (BB1 q n H1) as [H2 H3]. split; [exact H2|].
    rewrite (lf_skipn_cons recs k (0, []) Hkl). cbn [map]. intros [X|X]; [exact (Hne (eq_sym X)) | exact (H3 X)]. }
  assert (BE2 : list_blocks lst = [] -> blocks L2 A2 = blocks L A).
  { intros E. exfalso. apply app_eq_nil in E as [_ E2]. apply map_eq_nil in E2. change (recs = []) in E2.
    rewrite E2 in Hkl. cbn in Hkl. lia. }
  assert (RS2' : rt_ok Fr A2 (runF Fr [] bnd (lf_drops_t SRS k))).
  { rewrite (lf_drops_t_step SRS k (shr (known_at L A) (0, [])) ltac:(rewrite length_map; exact Hkl)),
      runF_app0 by apply nret_lf_drops_t.
    rewrite map_nth, lf_rec_drop_t.
    rewrite (SX1 _ (lf_nth_firstn recs k (0, []) Hkl)) in RS2. exact RS2. }
  assert (G8 : getr R2 (Z_to_bv 5 8) = getr regs (Z_to_bv 5 10)) by exact (RF2 8 ltac:(unfold callee_saved; lia)).
  assert (G9 : getr R2 (Z_to_bv 5 9) = Z_to_bv 64 (Z.of_nat (S k))) by exact (RF2 9 ltac:(unfold callee_saved; lia)).
  assert (G18 : getr R2 (Z_to_bv 5 18) = Z_to_bv 64 (16 * (Z.of_nat (S k) - 1)))
    by exact (RF2 18 ltac:(unfold callee_saved; lia)).
  assert (RO2r : ro_agree rsegs m2) by (rewrite <- SEG; exact RO2).
  assert (HD2n : rw_cells rsegs (normalize rsegs m2) LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (Z.of_nat (S k)));
                                                       C4 (Z_to_bv 64 CAP)]).
  { apply hdr_norm; [exact RO2r | rewrite <- SEG; exact HD2 | cbn [cells_size csize]; lia]. }
  assert (VAn : rw_cells rsegs (normalize rsegs m2) V [CB (Z.to_nat (16 * CAP)) ARRB]).
  { apply (arr_norm L2 A2 m2 md2 M2 VB2 RO2r). rewrite <- SEG. exact VA2. }
  pose proof (lf_u8 _ _ _ _ _ VAn) as UA.
  pose proof (lf_cb_len _ _ _ _ _ VAn) as UL.
  pose proof (hdr_disj L2 A2 m2 md2 V (16 * CAP) M2 VB2 ltac:(lia)) as DJ.
  assert (FR2r : rw_cells rsegs m2 (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                              C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))])
    by (rewrite <- SEG; exact FR2).
  assert (VA2r : rw_cells rsegs m2 V [CB (Z.to_nat (16 * CAP)) ARRB]) by (rewrite <- SEG; exact VA2).
  destruct k as [|k'].
  - apply (seg_step L2 A2 R2 (Z_to_bv 64 0x14ba4) m2 md2 [(LA, LA + 16)]
      (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (Z.of_nat 1 - 1)); C4 (Z_to_bv 64 CAP)])
      (fun R pc => pc = Z_to_bv 64 0x15664 /\ Sem.reg_get R (Z_to_bv 5 1) = Z_to_bv 64 0x14bd8 /\
                   Sem.reg_get R (Z_to_bv 5 10) = Z_to_bv 64 V /\
                   lfRFr R (lfval 0 (Z_to_bv 64 (16 * (Z.of_nat 1 - 1)))))
      LPOST_t LM2 RO2).
    + intros x Hx O. right. unfold lfE. exact (lf_not_out1 _ _ _ O).
    + rewrite lf_mkR_of, G8, G9, G18.
      eapply evt_mono.
      { eapply (lf_segB1 MMC) with (k := Z.of_nat 1) (V := V) (CAP := CAP) (us := ARRB);
          [exact HD2n | exact UA | lia | reflexivity | lia | lia | lia | lia | lia | apply mem_inv_normalize]. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MU & WM & HZ & UZ).
      do 3 eexists. split; [reflexivity|].
      split.
      { split; [reflexivity|]. split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
        lf_rfr RF2 I. }
      split; [exact MU|]. split; [exact WM|]. exact HZ.
    + intros R0 R3 pc' m3 m' (Epc & E1 & E10 & HR0) X MU WM RO3 MREL HZ LM3. subst pc'.
      apply (fin_t L2 A2 R3 m3 md2 (Z_to_bv 64 (16 * (Z.of_nat 1 - 1)))).
      * split; [exact LM3|]. split; [exact IN2|]. split; [exact RO3|]. split; [exact RS2'|].
        split.
        { pose proof (rw_cells_of_rel rsegs m3 m' _ _ MREL HZ) as H3.
          replace (Z.of_nat 1 - 1) with (Z.of_nat 0) in H3 by lia. rewrite SEG. exact H3. }
        split.
        { rewrite SEG. apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2r MU WM). cbn [disjoint_from cells_size csize].
          split; [lia | exact I]. }
        split.
        { intros _. split; [exact VB2|]. rewrite SEG. apply (rw_cells_transport rsegs _ m2 m3 _ _ VA2r MU WM).
          cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
        split; [exact VX2|]. split; [exact TX2|]. split; [exact SX2|].
        split; [exact BE2|]. split; [exact BA2|]. exact BB2.
      * exact (lf_RF_of R0 R3 _ HR0 X).
      * exact (lf_get R0 R3 (Z_to_bv 5 1) _ X eq_refl E1).
      * exact (lf_get R0 R3 (Z_to_bv 5 10) _ X eq_refl E10).
  - assert (Hk1 : (k' < length recs)%nat) by lia.
    pose proof (lf_slot rsegs (normalize rsegs m2) V _ recs junk k' Hk1 VAn) as SL.
    replace (V + 16 * Z.of_nat k') with (V + 16 * (Z.of_nat (S (S k')) - 1 - 1)) in SL by lia.
    apply (seg_step L2 A2 R2 (Z_to_bv 64 0x14ba4) m2 md2 [(LA, LA + 16)]
      (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (Z.of_nat (S (S k')) - 1));
                                       C4 (Z_to_bv 64 CAP)])
      (fun R pc => pc = Z_to_bv 64 0x15664 /\ Sem.reg_get R (Z_to_bv 5 1) = Z_to_bv 64 0x14ba4 /\
                   Sem.reg_get R (Z_to_bv 5 10) = Z_to_bv 64 (fst (nth k' recs (0, []))) /\
                   lfRFr R (lfval (Z.of_nat (S k')) (Z_to_bv 64 (16 * (Z.of_nat (S k') - 1)))))
      LPOST_t LM2 RO2).
    + intros x Hx O. right. unfold lfE. exact (lf_not_out1 _ _ _ O).
    + rewrite lf_mkR_of, G8, G9, G18.
      eapply evt_mono.
      { eapply (lf_segB2 MMC) with (k := Z.of_nat (S (S k'))) (V := V) (CAP := CAP) (q := fst (nth k' recs (0, [])))
          (us := ARRB);
          [exact HD2n | exact UA | lia | exact SL | lia | lia | lia | lia | lia | apply mem_inv_normalize]. }
      intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MU & WM & HZ & UZ).
      do 3 eexists. split; [reflexivity|].
      split.
      { split; [reflexivity|]. split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
        lf_rfr RF2 I. }
      split; [exact MU|]. split; [exact WM|]. exact HZ.
    + intros R0 R3 pc' m3 m' (Epc & E1 & E10 & HR0) X MU WM RO3 MREL HZ LM3. subst pc'.
      apply (IH ltac:(lia) L2 A2 R3 m3 md2).
      * split; [exact LM3|]. split; [exact IN2|]. split; [exact RO3|]. split; [exact RS2'|].
        split.
        { pose proof (rw_cells_of_rel rsegs m3 m' _ _ MREL HZ) as H3.
          replace (Z.of_nat (S (S k')) - 1) with (Z.of_nat (S k')) in H3 by lia. rewrite SEG. exact H3. }
        split.
        { rewrite SEG. apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2r MU WM). cbn [disjoint_from cells_size csize].
          split; [lia | exact I]. }
        split.
        { intros _. split; [exact VB2|]. rewrite SEG. apply (rw_cells_transport rsegs _ m2 m3 _ _ VA2r MU WM).
          cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
        split; [exact VX2|]. split; [exact TX2|]. split; [exact SX2|].
        split; [exact BE2|]. split; [exact BA2|]. exact BB2.
      * exact (lf_RF_of R0 R3 _ HR0 X).
      * exact (lf_get R0 R3 (Z_to_bv 5 1) _ X eq_refl E1).
      * replace (S k' - 1)%nat with k' by lia. exact (lf_get R0 R3 (Z_to_bv 5 10) _ X eq_refl E10).
Qed.

Lemma run_main_t : SR (ms_segs Bm) (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_FREE) mem (seg_rom (ms_segs Bm))) md) LPOST_t.
Proof.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1).
  pose proof lmid_start as LM0.
  pose proof (aa_laws API) as LAWS.
  assert (SPr : bv_unsigned (getr regs (Z_to_bv 5 2)) = S0) by reflexivity.
  assert (ST : stk rsegs mem (S0 - 8224) S0).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as STn.
  assert (ROr : ro_agree rsegs mem) by (rewrite <- SEG; exact RO).
  assert (HDn : rw_cells rsegs (normalize rsegs mem) LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)]).
  { apply hdr_norm; [exact ROr | rewrite <- SEG; exact HDR | cbn [cells_size csize]; lia]. }
  assert (FRW : forall m1, munch [(S0 - 32, S0)] mem m1 -> wmono rsegs mem m1 -> 0 < CAP ->
            In (V, 16 * CAP) (blocks L A) /\ rw_cells (ms_segs Bm) m1 V [CB (Z.to_nat (16 * CAP)) ARRB]).
  { intros m1 MU WM CP. destruct ARR as [(C0 & _)|(_ & VB & VA)]; [lia|]. split; [exact VB|].
    destruct (lf_blocks_in L A V (16 * CAP) VB) as (pv & Hpv & Epv).
    pose proof (mr_blocks_range _ _ LAWS L A mem md pv _ HM Hpv) as BR. rewrite Epv in BR.
    rewrite SEG. rewrite SEG in VA. apply (rw_cells_transport rsegs _ mem m1 _ _ VA MU WM).
    cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  destruct (Nat.eq_dec (length recs) 0) as [N0|NP].
  - assert (E0 : recs = []) by (apply length_zero_iff_nil; exact N0).
    assert (HDn0 : rw_cells rsegs (normalize rsegs mem) LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)])
      by (rewrite N0 in HDn; exact HDn).
    apply (seg_step L A regs (Z_to_bv 64 LIST_FREE) mem md [(S0 - 32, S0)]
      (fun m' => rw_cells rsegs m' (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                              C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] /\
                 rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)])
      (fun R pc => pc = Z_to_bv 64 0x15664 /\ Sem.reg_get R (Z_to_bv 5 1) = Z_to_bv 64 0x14bd8 /\
                   Sem.reg_get R (Z_to_bv 5 10) = Z_to_bv 64 V /\ lfRFr R (lfval 0 (getr regs (Z_to_bv 5 18))))
      LPOST_t LM0 RO).
    + intros x Hx O. left. pose proof (lf_not_out1 _ _ _ O). unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
    + rewrite lf_mkR_of. unfold LIST_FREE.
      eapply evt_mono.
      { eapply lf_segA0; [exact STn | rewrite SPr; lia | exact HDn0 | rewrite SPr; lia]. }
      intros ms' (m' & -> & MU & WM & FZ & HZ).
      do 3 eexists. split; [reflexivity|].
      split.
      { split; [reflexivity|]. split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|]. lf_rfr I I. }
      split; [exact MU|]. split; [exact WM|]. split; [exact FZ | exact HZ].
    + intros R0 R1 pc' m1 m' (Epc & E1 & E10 & HR0) X MU WM RO1 MREL (FZ & HZ) LM1. subst pc'.
      apply (fin_t L A R1 m1 md (getr regs (Z_to_bv 5 18))).
      * split; [exact LM1|]. split; [exact INIT|]. split; [exact RO1|].
        split; [rewrite E0; exact RES|].
        split; [rewrite SEG; exact (rw_cells_of_rel rsegs m1 m' _ _ MREL HZ)|].
        split; [rewrite SEG; exact (rw_cells_of_rel rsegs m1 m' _ _ MREL FZ)|].
        split; [exact (FRW m1 MU WM)|].
        split; [intros _; reflexivity|].
        split; [intros r' H; destruct H|].
        split; [intros r' _; reflexivity|].
        split; [intros _; reflexivity|]. split; [intros q n H _; exact H|].
        intros q n H. split; [exact H|]. rewrite E0. intros [].
      * exact (lf_RF_of R0 R1 _ HR0 X).
      * exact (lf_get R0 R1 (Z_to_bv 5 1) _ X eq_refl E1).
      * exact (lf_get R0 R1 (Z_to_bv 5 10) _ X eq_refl E10).
  - assert (CP : 0 < CAP) by lia.
    pose proof (FRW mem (munch_refl _ _) (wmono_refl _ _) CP) as (VB & VA).
    assert (VAn : rw_cells rsegs (normalize rsegs mem) V [CB (Z.to_nat (16 * CAP)) ARRB]).
    { apply (arr_norm L A mem md HM VB ROr). rewrite <- SEG. exact VA. }
    assert (Hk1 : (length recs - 1 < length recs)%nat) by lia.
    pose proof (lf_slot rsegs (normalize rsegs mem) V _ recs junk (length recs - 1) Hk1 VAn) as SL.
    replace (V + 16 * Z.of_nat (length recs - 1)) with (V + 16 * (N - 1)) in SL by lia.
    assert (VR : 4096 <= V /\ V + 16 * CAP <= YM05.alloc_ceiling).
    { destruct (lf_blocks_in L A V (16 * CAP) VB) as (pv & Hpv & Epv).
      pose proof (mr_blocks_range _ _ LAWS L A mem md pv _ HM Hpv) as BR. rewrite Epv in BR. exact BR. }
    apply (seg_step L A regs (Z_to_bv 64 LIST_FREE) mem md [(S0 - 32, S0)]
      (fun m' => rw_cells rsegs m' (S0 - 32) [C8 (getr regs (Z_to_bv 5 18)); C8 (getr regs (Z_to_bv 5 9));
                                              C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] /\
                 rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)])
      (fun R pc => pc = Z_to_bv 64 0x15664 /\ Sem.reg_get R (Z_to_bv 5 1) = Z_to_bv 64 0x14ba4 /\
                   Sem.reg_get R (Z_to_bv 5 10) = Z_to_bv 64 (fst (nth (length recs - 1) recs (0, []))) /\
                   lfRFr R (lfval N (Z_to_bv 64 (16 * (N - 1)))))
      LPOST_t LM0 RO).
    + intros x Hx O. left. pose proof (lf_not_out1 _ _ _ O). unfold LIST_FREE_K, LIST_FREE_FRAME, ALLOC_STACK. lia.
    + rewrite lf_mkR_of. unfold LIST_FREE.
      eapply evt_mono.
      { eapply lf_segA1; [exact STn | rewrite SPr; lia | exact HDn | exact SL | rewrite SPr; lia | rewrite SPr; lia
                         | lia | lia | lia]. }
      intros ms' (m' & -> & MU & WM & FZ & HZ).
      do 3 eexists. split; [reflexivity|].
      split.
      { split; [reflexivity|]. split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|]. lf_rfr I I. }
      split; [exact MU|]. split; [exact WM|]. split; [exact FZ | exact HZ].
    + intros R0 R1 pc' m1 m' (Epc & E1 & E10 & HR0) X MU WM RO1 MREL (FZ & HZ) LM1. subst pc'.
      apply (loop_t (length recs) ltac:(lia) L A R1 m1 md).
      * split; [exact LM1|]. split; [exact INIT|]. split; [exact RO1|].
        split.
        { assert (LD : lf_drops_t SRS (length recs) = []).
          { unfold lf_drops_t. rewrite skipn_all2 by (rewrite length_map; lia). reflexivity. }
          rewrite LD. exact RES. }
        split; [rewrite SEG; exact (rw_cells_of_rel rsegs m1 m' _ _ MREL HZ)|].
        split; [rewrite SEG; exact (rw_cells_of_rel rsegs m1 m' _ _ MREL FZ)|].
        split; [exact (FRW m1 MU WM)|].
        split; [intros _; reflexivity|].
        split; [intros r' H; rewrite firstn_all in H; exact (RECS r' H)|].
        split; [intros r' _; reflexivity|].
        split; [intros _; reflexivity|]. split; [intros q n H _; exact H|].
        intros q n H. split; [exact H|]. rewrite skipn_all. intros [].
      * exact (lf_RF_of R0 R1 _ HR0 X).
      * exact (lf_get R0 R1 (Z_to_bv 5 1) _ X eq_refl E1).
      * exact (lf_get R0 R1 (Z_to_bv 5 10) _ X eq_refl E10).
Qed.

End Run.

Theorem list_free_holds : free_contract_rt Bm API Fr -> free_null_contract Bm -> memmove_contract ->
  list_free_contract Bm API Fr.
Proof.
  intros FRC FNC MMC. unfold list_free_contract.
  intros L A regs mem md bnd l lines. cbv zeta. intros SEG PRE INIT RO PLR LST RES.
  destruct l as [V CAP recs junk].
  destruct LST as (HDR & NCAP & ARR0 & NDR0 & NVR & RECS0).
  refine (run_main_t SEG FRC FNC MMC L A regs mem md bnd V CAP recs junk lines PRE INIT RO PLR HDR NCAP _ _ NVR _ RES).
  - destruct ARR0 as [X|(X1 & X2 & _ & _ & X5)]; [left; exact X | right; exact (conj X1 (conj X2 X5))].
  - first [exact NDR0 | apply NoDup_ListNoDup; exact NDR0].
  - intros r Hr. exact (proj1 (proj1 (Forall_forall _ _) RECS0 r Hr)).
Qed.

End LFP.
