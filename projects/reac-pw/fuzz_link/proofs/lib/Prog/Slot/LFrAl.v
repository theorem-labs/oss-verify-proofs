(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: its direct allocator calls at the SR
   level, from a CUT at the callee's entry to a CUT at the return address with the callee's Post facts.
   - lfr_calloc: calloc(1, n) at 0x1729c (lib/CallocSite.v CALLOC_PC): the model block (8856, 0x13994, ra 0x13998)
     and the marks block (516, 0x139a4, ra 0x139a8); the new block joins the slot's heap blocks hb.
   - lfr_free: free(a) at 0x173d4 (LLVMFuzzerTestOneInput_c.v LLVM_FREE) of one of the slot's blocks that is not
     kept (op_decide's text_of copies 0x13ae8 / 0x13af0, op_read's text_buf buffers 0x13f64 / 0x13f6c, op_write's
     text_of copy 0x1405c, the exit 0x14140 / 0x14148); the block leaves hb.
   - lfr_free_null: free(NULL) at the same sites: nothing changes.
   The contracts are the frame's (LFr.v lff_alloc: lib/FrameAPI.v frame_allocator at the cut's FP state); the
   frame step is lib/Prog/Slot/LFrCall.v lfr_call. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall.
Import ListNotations.
Local Open Scope Z_scope.

Section AL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* the start state an allocator call asks (call_pre_k), from LFR and the cut's ra / sp / tp *)
Lemma la_pre : forall g hb T L A regs mem md ra K,
  LFR B API g hb T L A mem md -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> 0 <= K <= SLOT_STACK - SLOT_FRAME ->
  YK11.getr regs 1 = Z_to_bv 64 ra -> YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) ->
  YK11.getr regs 4 = Z_to_bv 64 A_TP ->
  spZ regs = lg_S g - SLOT_FRAME /\ call_pre_k B (aa_MR API) K L A regs mem md.
Proof.
  intros g hb T L A regs mem md ra K HF Hra Hra2 HK R1 R2 R4.
  pose proof HF as (HGV & HM & HW & HBD & HID & _ & _ & _ & _ & Hwin & Her & _).
  destruct (lc_gv B API g HGV) as (HS & HS16 & HS47 & _).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  assert (HSP : spZ regs = lg_S g - SLOT_FRAME).
  { unfold spZ. rewrite R2. apply MState.unsigned_lit. unfold SLOT_STACK, SLOT_FRAME in *. lia. }
  split; [exact HSP|].
  split; [exact HM|]. split; [exact HW|]. split; [exact HBD|].
  split; [rewrite R1; apply YK0s.ret_ok_even; rewrite MState.unsigned_lit by lia; exact Hra2|].
  rewrite HSP. unfold SLOT_STACK, SLOT_FRAME in *.
  split; [clear - HS16; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Hwin; lia|].
  split; [rewrite R4, (lff_tp B API FF); reflexivity|].
  split; [exact Her|]. intros H0. rewrite HID in H0. discriminate H0.
Qed.

Lemma lfr_calloc : forall g hb T n ra (P : machine_state -> Prop) (P' : Z -> machine_state -> Prop) c,
  0 <= n <= 2 ^ 20 -> lroom_hb hb -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g CALLOC_PC hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\
     getr (ms_regs ms) 10 = Z_to_bv 64 1 /\ getr (ms_regs ms) 11 = Z_to_bv 64 n) ->
  (forall R F fc m regs' m' r,
     P (MS R F (Z_to_bv 64 CALLOC_PC) fc None m (seg_rom rsegs)) ->
     regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 r ->
     lcarry (lkeep B g hb) m m' -> lpost_mem g m' -> lfresh B g hb r n -> r mod 16 = 0 ->
     (forall i, 0 <= i < n -> mbyte rsegs m' (r + i) = Some (Z_to_bv 8 0) /\ writable_at rsegs m' (r + i)) ->
     P' r (MS regs' F (Z_to_bv 64 ra) fc None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (fun c' => exists r, CUT B API g ra ((r, n) :: hb) T (P' r) c').
Proof.
  intros g hb T n ra P P' c Hn Hroom Hra Hra2 HCUT HPR HK.
  pose proof (lc_segs B API FF) as SEG.
  apply (cut_open B API g CALLOC_PC hb T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs CALLOC_PC mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G2 & G4 & G10 & G11). cbn [ms_regs MState.MS] in G1, G2, G4, G10, G11.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R2 : YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME)) by (rewrite (lc_getr R regs 2 HR); exact G2).
  assert (R4 : YK11.getr regs 4 = Z_to_bv 64 A_TP) by (rewrite (lc_getr R regs 4 HR); exact G4).
  assert (R10 : YK11.getr regs 10 = Z_to_bv 64 1) by (rewrite (lc_getr R regs 10 HR); exact G10).
  assert (R11 : YK11.getr regs 11 = Z_to_bv 64 n) by (rewrite (lc_getr R regs 11 HR); exact G11).
  assert (HKc : 0 <= CALLOC_STACK <= SLOT_STACK - SLOT_FRAME)
    by (unfold CALLOC_STACK, ALLOC_STACK, SLOT_STACK, SLOT_FRAME; lia).
  destruct (la_pre g hb T L A regs mem md ra CALLOC_STACK HF Hra Hra2 HKc R1 R2 R4) as (HSP & PRE).
  pose proof HF as (HGV & HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & HP & HKT & HGI).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  destruct (lc_fa B API FF fx') as (_ & _ & _ & _ & HCAL & _ & _ & _ & _ & HBW & _).
  assert (HCP : ms_calloc B = Some CALLOC_PC) by (destruct FF as (_ & _ & _ & _ & H & _); exact H).
  pose proof (calloc_one_site B API CALLOC_PC (HCAL CALLOC_PC HCP) HCP n ltac:(lia) L A regs mem md
    (sb_hb (lg_b g) hb) PRE HRO R10 R11 HRS (lroom B API g hb n HGV Hroom Hn)) as HSR.
  eapply SR_mono; [exact HSR|].
  intros c' [(L' & A' & regs' & mem' & md' & res & Ec & HC & H10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & HBK
    & HRO' & _ & _ & HID' & _ & HRS') (ms' & md'' & Ec' & HZ)].
  exists res.
  rewrite Ec in Ec'. injection Ec' as Ems _. subst ms'.
  cbn [ms_mem ms_regs YK11.mkst] in HZ. rewrite H10 in HZ.
  pose proof Hfr as (Hf1 & Hf2 & Hf3).
  rewrite (MState.unsigned_lit res) in HZ by lia.
  pose proof HC as (HM' & _ & _ & _ & _ & RP & _).
  assert (HBKf : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ False ->
    mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a k i Hin Hi _. exact (HBK a k i Hin (fun H => H) Hi). }
  assert (HRS2 : res_ok_slots A' (sb_hb (lg_b g) ((res, n) :: hb))) by (rewrite sb_hb_cons; exact HRS').
  assert (HP2 : Permutation (blocks L' A') (((res, n) :: hb) ++ blocks (lg_L g) (lg_A g))).
  { rewrite Eb'. cbn [app].
    apply Permutation_trans with ((res, n) :: b1 ++ b2); [apply Permutation_sym, Permutation_middle|].
    apply perm_skip. rewrite <- Eb. exact HP. }
  assert (HKT2 : lkept g ((res, n) :: hb) T).
  { destruct HKT as [H|[H0 [H|(f & -> & Hf)]]]; [left; exact H | right; split; [exact H0 | left; exact H] |].
    right. split; [exact H0|]. right. exists f. split; [reflexivity | right; exact Hf]. }
  assert (HGI2 : mf_gi B link_mf T mem').
  { apply (lfr_gi_keep B T mem mem' HGI).
    - intros a Ha.
      exact (proj1 (lc_frame B API FF g hb T L A mem md regs CALLOC_STACK (fun _ => False) L' A' mem' md'
        HF HSP HKc (lcall_post_k B API CALLOC_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' HC) a
        (or_intror (lfr_heads_img B API FF a Ha)) (fun H => H))).
    - intros f x HT Hx.
      assert (Hin : In (f, MF_BLOCK) (blocks L A))
        by (apply (lc_T_blk B API g hb T L A mem md _ HF); rewrite HT; left; reflexivity).
      pose proof (HBK f MF_BLOCK (x - f) Hin (fun H => H) ltac:(unfold MF_ZEROED, MF_BLOCK in *; lia)) as Hb.
      replace (f + (x - f)) with x in Hb by lia. exact Hb. }
  destruct (lfr_call B API FF g hb T L A mem md regs CALLOC_STACK (fun _ => False) L' A' regs' mem' md'
    ((res, n) :: hb) T HF HSP HKc HC (fun a He _ => False_ind _ He) (fun a He _ => False_ind _ He)
    (fun a _ => or_intror (fun He => He)) (fun a He _ => False_ind _ He) HBKf (fun a k i _ _ _ He => He)
    HID' HRO' HRS2 HP2 HKT2 HGI2) as (HLF & HLC & HPM).
  rewrite Ec, R1.
  apply (cut_close B API fx' g ra ((res, n) :: hb) T (P' res) L' A' regs' mem' md' Hfz HLF).
  apply lc_eqv_self. unfold lcanon.
  apply (HK R (@fp_regs fx') (@fp_csr fx') (normalize_cj rsegs mem) regs' (normalize_cj rsegs mem') res HPc).
  - exact (lc_rp R regs regs' HR RP).
  - exact H10.
  - intros x Hx. exact (HLC x (conj Hx (fun H => H))).
  - exact HPM.
  - exact (lfr_fresh B API g hb L A L' A' mem' md' b1 b2 res n HGV HP HM' Eb' Eb Hr0 Hfr).
  - exact Hr16.
  - intros i Hi.
    assert (HCJ : cj_drop rsegs (Z_to_bv 64 (res + i)) = false).
    { apply lc_cj_keep; [unfold TASK_SIZE; lia|].
      apply (lfr_ro_addr_out B (res + i) SEG (Hf3 i Hi)). lia. }
    split.
    + rewrite (proj1 (lc_norm_keep mem' (res + i) HCJ)). rewrite <- SEG. exact (HZ i Hi).
    + apply (proj2 (proj2 (lc_norm_keep mem' (res + i) HCJ))). rewrite <- SEG.
      apply (HBW L' A' mem' md' res n i HM'); [rewrite Eb'; apply in_or_app; right; left; reflexivity | exact Hi].
Qed.

Lemma lfr_free : forall g hb1 a n hb2 T ra (P P' : machine_state -> Prop) c,
  ~ In (a, n) T -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g LLVM_FREE (hb1 ++ (a, n) :: hb2) T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\
     getr (ms_regs ms) 10 = Z_to_bv 64 a) ->
  (forall R F fc m regs' m',
     P (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) -> regs_preserved R regs' ->
     lcarry (lkeep B g (hb1 ++ hb2)) m m' -> lpost_mem g m' ->
     P' (MS regs' F (Z_to_bv 64 ra) fc None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (CUT B API g ra (hb1 ++ hb2) T P').
Proof.
  intros g hb1 a n hb2 T ra P P' c HnT Hra Hra2 HCUT HPR HK.
  pose proof (lc_segs B API FF) as SEG.
  apply (cut_open B API g LLVM_FREE (hb1 ++ (a, n) :: hb2) T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs LLVM_FREE mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G2 & G4 & G10). cbn [ms_regs MState.MS] in G1, G2, G4, G10.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R2 : YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME)) by (rewrite (lc_getr R regs 2 HR); exact G2).
  assert (R4 : YK11.getr regs 4 = Z_to_bv 64 A_TP) by (rewrite (lc_getr R regs 4 HR); exact G4).
  assert (R10 : YK11.getr regs 10 = Z_to_bv 64 a) by (rewrite (lc_getr R regs 10 HR); exact G10).
  assert (HKf : 0 <= ALLOC_STACK <= SLOT_STACK - SLOT_FRAME) by (unfold ALLOC_STACK, SLOT_STACK, SLOT_FRAME; lia).
  destruct (la_pre g _ T L A regs mem md ra ALLOC_STACK HF Hra Hra2 HKf R1 R2 R4) as (HSP & PRE).
  pose proof HF as (HGV & HM & _ & _ & HID & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & HP & HKT & HGI).
  destruct (lc_gv B API g HGV) as (HS & _ & HS47 & _).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  destruct (lc_fa B API FF fx') as (_ & HFREE & _ & _ & _ & _ & _ & _ & HND & _).
  assert (Hab : In (a, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (proj1 (blocks_In L A a n) Hab) as (p & Epa & Hp).
  assert (HFP : ms_free B = LLVM_FREE) by (destruct FF as (_ & _ & H & _); exact H).
  pose proof (HFREE L A regs mem md p n (sb_hb (lg_b g) (hb1 ++ (a, n) :: hb2))
    (proj2 (call_pre_k_alloc B (aa_MR API) L A regs mem md) PRE) HRO Hp ltac:(rewrite Epa; exact R10) HRS) as HSR.
  rewrite HFP in HSR.
  eapply SR_mono; [exact HSR|].
  intros c' (L' & A' & regs' & mem' & md' & Ec & HC & (b1 & b2 & Eb & Eb') & HBK & HRO' & _ & _ & HIDi & _ & HRS').
  rewrite Epa in HC, Eb, HBK.
  apply (proj1 (call_post_k_alloc B (aa_MR API) L A regs mem md _ L' A' regs' mem' md')) in HC.
  pose proof HC as (HM' & _ & _ & _ & _ & RP & _).
  (* the freed block: below the ceiling, outside the image, apart from the slot's other blocks and the entry
     blocks *)
  assert (HBA : forall x, a <= x < a + n -> 4096 <= a /\ a + n <= YM05.alloc_ceiling /\ ~ in_img B x).
  { intros x Hx. destruct (lc_blk B API FF L A mem md a n (x - a) HM Hab ltac:(lia)) as (_ & H2 & H3 & _ & H5).
    replace (a + (x - a)) with x in H5 by lia. split; [exact H2|]. split; [exact H3 | exact H5]. }
  assert (HD : forall t k, In (t, k) (hb1 ++ hb2 ++ blocks (lg_L g) (lg_A g)) -> a + n <= t \/ t + k <= a).
  { intros t k Hin. pose proof (lc_pw B API L A mem md _ HM HP) as Hpw.
    rewrite <- app_assoc in Hpw. cbn [app] in Hpw.
    destruct (lc_pw_mid ranges_disjoint hb1 (a, n) (hb2 ++ blocks (lg_L g) (lg_A g)) Hpw (t, k) Hin) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (HBK2 : forall a' k i, In (a', k) (blocks L A) -> 0 <= i < k -> ~ (a <= a' + i < a + n) ->
     mbyte (ms_segs B) mem' (a' + i) = mbyte (ms_segs B) mem (a' + i)).
  { intros a' k i Hin Hi HnE. destruct (Z.eq_dec a' a) as [->|Hne].
    - pose proof (lc_nodup_fst _ a k n (HND L A mem md HM) Hin Hab) as ->. exfalso. apply HnE. lia.
    - exact (HBK a' k i Hin Hne Hi). }
  assert (HE02 : forall a' k i, In (a', k) (blocks (lg_L g) (lg_A g)) -> ~ In (a', k) (lg_T g) -> 0 <= i < k ->
    ~ (a <= a' + i < a + n)).
  { intros a' k i Hin _ Hi He.
    destruct (HD a' k ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)); lia. }
  assert (HEhi : forall x, a <= x < a + n -> YM05.alloc_ceiling <= x -> lg_S g - SLOT_STACK <= x < lg_S g).
  { intros x He Hx. exfalso. destruct (HBA x He) as (_ & H3 & _). lia. }
  assert (HEimg : forall x, a <= x < a + n -> lf_img B x -> in_globals llvm_G x).
  { intros x He Hi. exfalso. destruct (HBA x He) as (_ & _ & H5). exact (H5 (proj1 Hi)). }
  assert (HEd : forall x, lg_S g - SLOT_STACK <= x < lg_S g -> (a <= x < a + n) \/ ~ (a <= x < a + n))
    by (intros x _; lia).
  assert (HEw : forall x, a <= x < a + n -> lg_S g - SLOT_STACK <= x < lg_S g -> writable_at (ms_segs B) mem' x).
  { intros x He Hx. exfalso. destruct (HBA x He) as (_ & H3 & _). unfold SLOT_STACK in *. lia. }
  assert (HRS2 : res_ok_slots A' (sb_hb (lg_b g) (hb1 ++ hb2)))
    by (rewrite (sb_hb_remove (lg_b g) hb1 a n hb2); exact HRS').
  assert (HP2 : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (lg_L g) (lg_A g))).
  { rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (a, n)). rewrite <- Eb.
    pose proof HP as HP0. rewrite <- app_assoc in HP0. cbn [app] in HP0. exact HP0. }
  assert (HKT2 : lkept g (hb1 ++ hb2) T).
  { destruct HKT as [H|[H0 [H|(f & -> & Hf)]]]; [left; exact H | right; split; [exact H0 | left; exact H] |].
    right. split; [exact H0|]. right. exists f. split; [reflexivity|].
    apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf|[Hf|Hf]]; [left; exact Hf | | right; exact Hf].
    exfalso. apply HnT. rewrite Hf. left. reflexivity. }
  assert (HGI2 : mf_gi B link_mf T mem').
  { apply (lfr_gi_keep B T mem mem' HGI).
    - intros x Hx. pose proof (lfr_heads_img B API FF x Hx) as Hi.
      assert (HnE : ~ (a <= x < a + n))
        by (intros He; destruct (HBA x He) as (_ & _ & H5); exact (H5 (proj1 Hi))).
      exact (proj1 (lc_frame B API FF g _ T L A mem md regs ALLOC_STACK (fun y => a <= y < a + n) L' A' mem' md'
        HF HSP HKf (lcall_post_k B API ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' HC) x (or_intror Hi) HnE)).
    - intros f x HT Hx.
      assert (Hin : In (f, MF_BLOCK) (blocks L A))
        by (apply (lc_T_blk B API g _ T L A mem md _ HF); rewrite HT; left; reflexivity).
      assert (Hfa : f <> a).
      { intros ->. pose proof (lc_nodup_fst _ a MF_BLOCK n (HND L A mem md HM) Hin Hab) as <-.
        apply HnT. rewrite HT. left. reflexivity. }
      pose proof (HBK f MF_BLOCK (x - f) Hin Hfa ltac:(unfold MF_ZEROED, MF_BLOCK in *; lia)) as Hb.
      replace (f + (x - f)) with x in Hb by lia. exact Hb. }
  destruct (lfr_call B API FF g _ T L A mem md regs ALLOC_STACK (fun y => a <= y < a + n) L' A' regs' mem' md'
    (hb1 ++ hb2) T HF HSP HKf HC HEhi HEimg HEd HEw HBK2 HE02 (HIDi HID) HRO' HRS2 HP2 HKT2 HGI2)
    as (HLF & HLC & HPM).
  rewrite Ec, R1.
  apply (cut_close B API fx' g ra (hb1 ++ hb2) T P' L' A' regs' mem' md' Hfz HLF).
  apply lc_eqv_self. unfold lcanon.
  apply (HK R (@fp_regs fx') (@fp_csr fx') (normalize_cj rsegs mem) regs' (normalize_cj rsegs mem') HPc).
  - exact (lc_rp R regs regs' HR RP).
  - intros x Hx. apply HLC. split.
    + apply (lc_lkeep_mono B g (hb1 ++ (a, n) :: hb2) (hb1 ++ hb2) x); [|exact Hx].
      intros y Hy. apply in_app_iff in Hy. apply in_app_iff.
      destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy].
    + intros He. cbv beta in He. destruct (HBA x He) as (H2 & H3 & H5).
      destruct Hx as [Hx | [Hx | [(t & k & Hin & Hx) | (t & k & Hin & Hx)]]].
      * unfold SLOT_FRAME, SLOT_STACK in *. lia.
      * exact (H5 (proj1 Hx)).
      * assert (Hin' : In (t, k) (hb1 ++ hb2 ++ blocks (lg_L g) (lg_A g))).
        { apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin|].
          right. apply in_or_app. left. exact Hin. }
        destruct (HD t k Hin'); lia.
      * destruct (HD t k ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)); lia.
  - exact HPM.
Qed.

Lemma lfr_free_null : forall g hb T ra (P P' : machine_state -> Prop) c,
  0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g LLVM_FREE hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\ getr (ms_regs ms) 10 = Z_to_bv 64 0) ->
  (forall R F fc m, P (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
     P' (MS R F (Z_to_bv 64 ra) fc None m (seg_rom rsegs))) ->
  SR (ms_segs B) c (CUT B API g ra hb T P').
Proof.
  intros g hb T ra P P' c Hra Hra2 HCUT HPR HK.
  apply (cut_open B API g LLVM_FREE hb T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs LLVM_FREE mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G10). cbn [ms_regs MState.MS] in G1, G10.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R10 : YK11.getr regs 10 = Z_to_bv 64 0) by (rewrite (lc_getr R regs 10 HR); exact G10).
  pose proof HF as (_ & HM & _).
  destruct (mr_model B (aa_MR API) (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  destruct (lc_fa B API FF fx') as (_ & _ & HFN & _).
  assert (HFP : ms_free B = LLVM_FREE) by (destruct FF as (_ & _ & H & _); exact H).
  assert (HRA : YK0s.ret_ok (YK11.getr regs 1))
    by (rewrite R1; apply YK0s.ret_ok_even; rewrite MState.unsigned_lit by lia; exact Hra2).
  pose proof (HFN regs mem md HRA R10 Hh Hl) as HSR. rewrite HFP in HSR.
  eapply SR_mono; [exact HSR|]. intros c' ->. rewrite R1.
  apply (cut_close B API fx' g ra hb T P' L A regs mem md Hfz HF).
  apply (lc_eqv_rep P' fx' R regs ra mem HR). exact (HK R _ _ _ HPc).
Qed.

End AL.
