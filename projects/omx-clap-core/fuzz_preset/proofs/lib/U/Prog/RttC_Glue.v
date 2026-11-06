From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YH03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp round_trip_text_c RttDefs fuzz_free_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttGlue RttModel RttBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Helpers of the last stages of round_trip_text (ubsan #102, 0x15334; RttBase.v): stg_oom (0x153e4), stg_ff
   (0x1544c) and stg_end (0x15488).  Frame 0x70: sp = S - 112, the saved ra s0 .. s5 at S - 8 .. S - 56.
   rc_free_want and rc_ffree_text step over the two calls that the ran-out arm and the read-back arm share:
   free (want) (ms_free B = YH03.src0_A_free) and fuzz_free (text); rc_fin turns the walk invariant with an empty
   own-block list into the frame part of rtt_post. *)

Module LMem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.MState.

Lemma rc_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Lemma rc_nd_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hx|].
  cbn [app] in H. apply NoDup_cons_iff in H. destruct H as [Hn Hd].
  destruct Hx as [<-|Hx]; [apply Hn; apply in_or_app; right; exact Hy | exact (IH l2 x Hd Hx Hy)].
Qed.

Lemma rc_fst_in : forall (l : list (Z * Z)) a k, In (a, k) l -> In a (map fst l).
Proof. intros l a k H. apply in_map_iff. exists (a, k). split; [reflexivity | exact H]. Qed.

Lemma rc_disj : forall (X Y : list (Z * Z)) a k a' k', List.NoDup (map fst X ++ map fst Y) ->
  In (a, k) X -> In (a', k') Y -> a <> a'.
Proof.
  intros X Y a k a' k' H H1 H2 E. subst a'.
  exact (rc_nd_disj _ _ a H (rc_fst_in X a k H1) (rc_fst_in Y a k' H2)).
Qed.

Lemma rc_nd_perm : forall (Lam X Y : list (Z * Z)), Permutation Lam (X ++ Y) -> NoDup (map fst Lam) ->
  List.NoDup (map fst X ++ map fst Y).
Proof.
  intros Lam X Y P H. rewrite <- map_app. apply (Permutation_NoDup (Permutation_map fst P)).
  apply NoDup_ListNoDup. exact H.
Qed.

Lemma rc_node_rw : forall segs m lb p t D, pj_node segs m lb p t D -> pj_rw segs m p.
Proof.
  intros segs m lb p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & (Hrw & _) & _); exact Hrw.
Qed.

Lemma rc_node_top : forall segs m lb p t D, pj_node segs m lb p t D -> 0 <= p /\ p + 56 <= 2 ^ 64.
Proof.
  intros segs m lb p t D H. destruct (rc_node_rw segs m lb p t D H) as (_ & H1 & H2 & _). lia.
Qed.

(* the stack budget: 112 (round_trip_text's frame) + the callees' budgets fit in RTT_K = 112 + PN_K *)
Lemma rc_rttk : 112 + ALLOC_STACK <= RTT_K /\ ALLOC_STACK = 8192 /\
  forall d, (d <= 32)%nat -> 0 <= PJ_FREE_K d /\ 112 + PJ_FREE_K d <= RTT_K.
Proof.
  assert (E : 112 + (48 * 34 + 8192) <= RTT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  split; [unfold ALLOC_STACK; lia|]. split; [reflexivity|].
  intros d Hd. unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK. lia.
Qed.

(* the ledger statics lie in the image, below errno and below the allocation ceiling *)
Lemma rc_stat_rng {rc : YM05.RunCeil} : forall a, alloc_statics a -> a < strtod_c.STRTOD_ERRNO /\ a < alloc_ceiling.
Proof.
  intros a Ha. pose proof alloc_ceiling_val as HCV.
  unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold strtod_c.STRTOD_ERRNO. lia.
Qed.

Lemma rc_slot : forall segs m x y bs, x = y -> LMem.bytes_at segs m x bs -> LMem.bytes_at segs m y bs.
Proof. intros segs m x y bs -> H. exact H. Qed.

Lemma rc_pres : forall regs0 r1 r2 copy s2v s3v s4v s5v, regs_preserved r1 r2 ->
  rtt_regs regs0 r1 copy s2v s3v s4v s5v -> rtt_regs regs0 r2 copy s2v s3v s4v s5v.
Proof.
  intros regs0 r1 r2 copy s2v s3v s4v s5v RR (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
  split; [etransitivity; [apply (RR 8); unfold callee_saved; lia | exact G8]|].
  split; [etransitivity; [apply (RR 9); unfold callee_saved; lia | exact G9]|].
  split; [etransitivity; [apply (RR 18); unfold callee_saved; lia | exact G18]|].
  split; [etransitivity; [apply (RR 19); unfold callee_saved; lia | exact G19]|].
  split; [etransitivity; [apply (RR 20); unfold callee_saved; lia | exact G20]|].
  split; [etransitivity; [apply (RR 21); unfold callee_saved; lia | exact G21]|].
  split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
  split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
  intros r Hr. etransitivity; [apply (RR r); unfold callee_saved; lia | exact (G22 r Hr)].
Qed.

(* a straight-line run that keeps sp, s0, s1, gp, tp, s6 .. s11 and sets s2 .. s5 *)
Lemma rc_regs_run : forall regs0 regs regs1 copy s2v s3v s4v s5v s2v' s3v' s4v' s5v',
  rtt_regs regs0 regs copy s2v s3v s4v s5v ->
  getr regs1 2 = getr regs 2 -> getr regs1 8 = getr regs 8 -> getr regs1 9 = getr regs 9 ->
  getr regs1 18 = s2v' -> getr regs1 19 = s3v' -> getr regs1 20 = s4v' -> getr regs1 21 = s5v' ->
  getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  (forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rtt_regs regs0 regs1 copy s2v' s3v' s4v' s5v'.
Proof.
  intros regs0 regs regs1 copy s2v s3v s4v s5v s2v' s3v' s4v' s5v' (G2 & G8 & G9 & _ & _ & _ & _ & G3 & G4 & G22)
    E2 E8 E9 E18 E19 E20 E21 E3 E4 E22.
  split; [rewrite E2; exact G2|]. split; [rewrite E8; exact G8|]. split; [rewrite E9; exact G9|].
  split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
  split; [rewrite E3; exact G3|]. split; [rewrite E4; exact G4|].
  intros r Hr. rewrite (E22 r Hr). exact (G22 r Hr).
Qed.

Ltac rc_hi HGr :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; rewrite HGr;
  assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.

(* the epilogue's registers: ra s0 .. s5 reloaded from the save area, sp = S, gp tp s6 .. s11 kept *)
Lemma rc_ret_pres : forall regs0 rX regs3 copy s2v s3v s4v s5v (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rtt_regs regs0 rX copy s2v s3v s4v s5v ->
  (forall r, getr regs3 r = getr (LFrame.mkR (getr regs0 1) (Z_to_bv 64 (spZ regs0)) (getr rX 3) (getr rX 4) t0 t1 t2
     (getr regs0 8) (getr regs0 9) a0 a1 a2 a3 a4 a5 a6 a7 (getr regs0 18) (getr regs0 19) (getr regs0 20)
     (getr regs0 21) (getr rX 22) (getr rX 23) (getr rX 24) (getr rX 25) (getr rX 26) (getr rX 27) t3 t4 t5 t6) r) ->
  regs_preserved regs0 regs3.
Proof.
  intros regs0 rX regs3 copy s2v s3v s4v s5v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (_ & _ & _ & _ & _ & _ & _ & G3 & G4 & G22) HG r Hr.
  rewrite HG. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - transitivity (Z_to_bv 64 (spZ regs0)); [reflexivity|]. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - transitivity (getr rX 3); [reflexivity | exact G3].
  - transitivity (getr rX 4); [reflexivity | exact G4].
  - reflexivity.
  - reflexivity.
  - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ 22 <= r <= 27) by lia.
    destruct Hr' as [->|[->|[->|[->|Hr']]]]; [reflexivity | reflexivity | reflexivity | reflexivity |].
    rewrite <- (G22 r Hr').
    assert (Hr'' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr'' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
Qed.

Lemma rc_stk_after : forall segs m m' lo bs, LFrame.stk segs m lo (lo + Z.of_nat (length bs)) ->
  LFrame.wmono segs m m' -> LMem.bytes_at segs m' lo bs -> LFrame.stk segs m' lo (lo + Z.of_nat (length bs)).
Proof.
  intros segs m m' lo bs (H1 & H2 & H) W (_ & _ & Hb). split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Wv _]. split; [exact (W _ Wv)|].
  pose proof (Hb (Z.to_nat (a - lo)) ltac:(lia)) as E.
  replace (lo + Z.of_nat (Z.to_nat (a - lo))) with a in E by lia.
  destruct (nth_error bs (Z.to_nat (a - lo))) as [b|] eqn:En.
  - exists b. exact E.
  - apply nth_error_None in En. lia.
Qed.

Ltac rc_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS LMS.MS] in ER, EP, EM;
  subst R pc m; clear E.

Ltac rc_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma rc_kA : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  Exec.evt rsegs Q (LMS.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = LMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (LMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (LMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HSEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma rc_kAn : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> MemNorm.ro_agree rsegs mem1 ->
  Exec.evt rsegs Q (LMS.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (MemNorm.normalize rsegs mem1)
    (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = LMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' m0 regs', Q (LMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom rsegs)) ->
     MemNorm.mem_rel rsegs mem' m0 -> MemNorm.ro_same rsegs mem1 mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz Hro HE HS HK.
  apply (rc_kA fx1 regs1 pc mem1 md1
    (fun s => exists s0, Q s0 /\ MemNorm.ms_rel rsegs s s0 /\ MemNorm.ro_same rsegs mem1 (ms_mem s)) P Hh Hz).
  - eapply (MemNorm.evt_normalize rsegs); [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (s0 & HQ & Hrel & Hsame). destruct (HS s0 HQ) as (R & pc0 & m0 & ->).
    destruct ms' as [R' F' pc'' svc' rv' fc' m' ro'].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS LMS.MS] in *. subst.
    exists R, pc0, m'. reflexivity.
  - intros R pc' mem' regs' (s0 & HQ & Hrel & Hsame) HGr.
    destruct (HS s0 HQ) as (R0 & pc0 & m0 & E0). subst s0.
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS LMS.MS] in *.
    subst R0 pc0.
    exact (HK R pc' mem' m0 regs' HQ HR Hsame HGr).
Qed.

Lemma rc_ro_high : forall a, alloc_ceiling <= a < 2 ^ 64 -> LMem.ro_addr (ms_segs B) (LMem.wa a) = false.
Proof.
  intros a Ha. pose proof alloc_ceiling_val as HCV. unfold LMem.ro_addr. rewrite LMem.wa_unsigned by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Ef; [|reflexivity].
  destruct (rtt_img_low B API HSEG FA) as [_ HI]. pose proof (HI _ _ Ef). lia.
Qed.

Lemma rc_stk_norm : forall m lo hi, LFrame.stk (ms_segs B) m lo hi -> alloc_ceiling <= lo ->
  LFrame.stk (ms_segs B) (MemNorm.normalize (ms_segs B) m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hlo. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b0 & Hb). pose proof (rc_ro_high a ltac:(lia)) as Hr.
  unfold wview, LMem.mrd, MemNorm.normalize in *. cbv beta. rewrite Hr. split; [exact Hw | exists b0; exact Hb].
Qed.

Lemma rc_rpost_blocks : forall K L A regs mem md E gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  forall a k, In (a, k) (blocks L A) -> ~ gone a k -> In (a, k) (blocks L' A').
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' (_ & _ & _ & _ & _ & _ & _ & UB & PA & _) a k Hin Hg.
  destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
  assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB; [exact Hq0 | exact Hg]).
  rewrite <- (PA q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1).
Qed.

Lemma rc_lblk : forall L A mem md Lam peak cnt fail a k, aa_MR API L A mem md ->
  ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (blocks L A) /\ 4112 <= a /\ a + k <= alloc_ceiling /\
  (forall i, - 16 <= i < k -> ~ in_img B (a + i)).
Proof.
  intros L A mem md Lam peak cnt fail a k HM HL Hin.
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  destruct (FB (a, k) Hin) as (Hk & Hb & _ & _). cbn [fst snd] in Hk, Hb.
  split; [exact Hk|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
  intros i Hi. exact (ledger_block_not_img B L A mem Lam peak cnt fail a k i HL Hin Hi).
Qed.

Lemma rc_apart : forall L A mem md Lam peak cnt fail a k a' k' x, aa_MR API L A mem md ->
  ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> In (a', k') Lam -> a <> a' ->
  a - 16 <= x < a + k -> ~ (a' - 16 <= x < a' + k').
Proof.
  intros L A mem md Lam peak cnt fail a k a' k' x HM HL H1 H2 Hn Hx.
  destruct (rc_lblk L A mem md Lam peak cnt fail a k HM HL H1) as (_ & B1 & _).
  destruct (rc_lblk L A mem md Lam peak cnt fail a' k' HM HL H2) as (_ & B2 & _).
  intros Hy. exact (blocks_apart B API HSEG AX FG L A mem md (a - 16) (k + 16) (a' - 16) (k' + 16) x HM B1 B2
    ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma rc_not_statics : forall L A mem md Lam peak cnt fail a k i, aa_MR API L A mem md ->
  ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> - 16 <= i < k -> ~ alloc_statics (a + i).
Proof.
  intros L A mem md Lam peak cnt fail a k i HM HL Hin Hi Hs.
  destruct (rc_lblk L A mem md Lam peak cnt fail a k HM HL Hin) as (_ & _ & _ & _ & NI).
  destruct (statics_img B API HSEG AX FG (a + i) Hs) as [Hi' _]. exact (NI i Hi Hi').
Qed.

Lemma rc_node_keep : forall K S E g L A mem md L' A' mem' md' Lam Lam2 peak cnt fail p t D,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail ->
  pj_node (ms_segs B) mem (lin Lam) p t D -> (forall bk, In bk D -> In bk Lam) ->
  (forall bk, In bk D -> In bk Lam2) ->
  rstep B API K S E g L A mem md L' A' mem' md' ->
  alloc_ceiling <= p ->
  (forall i, 0 <= i < 56 -> ~ rwin B K S (p + i) /\ ~ E (p + i)) ->
  (forall a k, In (a, k) D -> ~ g (a - 16) /\ forall i, 0 <= i < k -> ~ E (a + i)) ->
  pj_node (ms_segs B) mem' (lin Lam2) p t D.
Proof.
  intros K S E g L A mem md L' A' mem' md' Lam Lam2 peak cnt fail p t D HM HL HN HD HD2 ST Hp HR HB.
  pose proof (rc_node_top _ _ _ _ _ _ HN) as (_ & Hp2).
  pose proof (pj_node_rstep B API HSEG AX FG K S E g L A mem md L' A' mem' md' Lam Lam peak cnt fail p t D
    HM HL HN HD ST Hp Hp2 HR HB (fun bk h => h)) as HN'.
  apply (pj_node_frame (ms_segs B) t mem' (lin Lam) mem' (lin Lam2) p D HN'); [|intros x _; reflexivity].
  intros a k Hin. exact (HD2 (a, k) Hin).
Qed.

End C.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

(* the end of the walk: with no own block left, the invariant gives the frame step of the post (the write set
   widened from rtt_writes 0 to rtt_writes copy) and the 56 bytes of *copy untouched *)
Lemma rc_fin : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D,
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  forall (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd,
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md [] Lam peak cnt bnd ->
  rstep B API RTT_K (spZ regs0) (rtt_writes copy) (fun _ => False) L0 A0 mem0 md0 L A mem md /\
  (copy <> 0 -> forall i, 0 <= i < 56 -> mbyte (ms_segs B) mem (copy + i) = mbyte (ms_segs B) mem0 (copy + i)).
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT fx1 L A mem md Lam peak cnt bnd INV.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & COPY & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  split.
  - apply (rstep_E B API HSEG AX FG RTT_K (spZ regs0) (rtt_writes 0) (rtt_writes copy) (fun _ => False) (fun _ => False)
      L0 A0 mem0 md0 L A mem md RS); [| intros a Ha; exact Ha].
    intros a [[Hz _]|Ha]; [exfalso; apply Hz; reflexivity | right; exact Ha].
  - intros Hc i Hi.
    destruct COPY as [C0|(_ & (_ & _ & Hhi & _) & Hs & _)]; [contradiction|].
    pose proof RS as (_ & _ & _ & _ & _ & _ & AC & _).
    assert (Ha : alloc_ceiling <= copy + i < 2 ^ 64) by lia.
    assert (Hr : ~ rwin B RTT_K (spZ regs0) (copy + i)).
    { unfold rwin. intros [Hr|Hr]; [lia | rewrite ERRB in Hr; unfold strtod_c.STRTOD_ERRNO in Hr; lia]. }
    assert (He : ~ rtt_writes 0 (copy + i)).
    { unfold rtt_writes. intros [[Hz _]|Hst]; [apply Hz; reflexivity | destruct (rc_stat_rng _ Hst); lia]. }
    exact (proj1 (AC (copy + i) Ha Hr He)).
Qed.

Section FW.
Hypothesis HFREE : ms_free B = YH03.src0_A_free.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.

(* free (want) entered with sp = S - 112: the want block of the rendering (not a ledger block) goes; the walk
   invariant holds after it with the bound rf_free bnd cap *)
Lemma rc_free_want : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D,
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  forall (fx1 : YK11.FPState) L A regs mem md X Lam peak cnt bnd want cap (P : config -> Prop),
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = Z_to_bv 64 want ->
  0 <= want < 2 ^ 64 -> 0 < cap -> In (want, cap) (blocks L A) ->
  (forall i, 0 <= i < cap -> ~ in_img B (want + i)) ->
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> want) ->
  (forall a n, In (a, n) Lam -> a - 16 <> want) ->
  (forall L' A' regs' mem' md',
     @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem' md' X Lam peak cnt
       (rf_free F bnd cap) ->
     regs_preserved regs regs' ->
     rstep B API ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap) (fun a => a = want)
       L A mem md L' A' mem' md' ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs (Z_to_bv 64 YH03.src0_A_free) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT fx1 L A regs mem md X Lam peak cnt bnd want cap P
    INV G2 G4 GRA G10 HW0 HCAP WBLK WIMG WNB WNL K.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & DNODE & DSUB & DOC0 & DOCS & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODE & RES & _).
  pose proof RS as (MRc & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  pose proof (rc_node_top _ _ _ _ _ _ DNODE) as (_ & DOCT).
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  destruct (rg_blk B API HSEG AX FG L A mem md want cap 0 MRc WBLK ltac:(lia)) as (_ & WR1 & WR2 & _).
  assert (LAMOK : forall a k, In (a, k) Lam -> a - 16 <> want /\
      forall i, -16 <= i < k -> ~ (want <= a + i < want + cap)).
  { intros a k Hin. split; [exact (WNL a k Hin)|]. intros i Hi Hw.
    destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED Hin) as (_ & Hblk & _).
    apply (blocks_apart B API HSEG AX FG L A mem md want cap (a - 16) (k + 16) (a + i) MRc WBLK Hblk
      (fun e => WNL a k Hin (eq_sym e)) Hw). lia. }
  assert (HS1 : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply rc_uns; lia).
  destruct (rg_blk_in B API HSEG AX FG L A want cap WBLK) as (qq & Hqq & Eqq).
  pose proof (FREEF fx1) as FREE.
  replace (Z_to_bv 64 YH03.src0_A_free) with (Z_to_bv 64 (ms_free B)) by (rewrite HFREE; reflexivity).
  eapply SR_bind; [apply (FREE L A regs mem md qq cap bnd) |].
  - apply call_pre_k_alloc.
    apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs ALLOC_STACK 112
      PRE0 RS INIT); [exact HS1 | rewrite HS1; Z.div_mod_to_equations; lia | exact G4 | exact GRA | lia | lia | lia].
  - exact (proj1 RD).
  - exact Hqq.
  - rewrite G10, Eqq. reflexivity.
  - exact RES.
  - intros c' (L' & A' & regs2 & mem2 & md2 & -> & CPOST & (b1 & b2 & EB1 & EB2) & BKEPT & RA2 & _ & _ & INITk & _ &
      RS2).
    rewrite Eqq in CPOST, EB1, BKEPT.
    pose proof CPOST as (MR2 & _ & _ & _ & _ & RR & _).
    assert (ST3 : rstep B API ALLOC_STACK (spZ regs) (fun a => want <= a < want + cap) (fun a => a = want)
      L A mem md L' A' mem2 md2).
    { apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L A regs mem md _ _ L' A' regs2 mem2 md2 MRc).
      - apply call_post_k_alloc. exact CPOST.
      - exact INITk.
      - intros a k Hin Hk Hne. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; congruence | right; exact H].
      - intros a k i Hin Hne Hi _. exact (BKEPT a k i Hin Hne Hi). }
    rewrite HS1 in ST3.
    assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem2 md2 X Lam peak cnt
      (rf_free F bnd cap)).
    { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md
        X Lam peak cnt bnd ALLOC_STACK (fun a => want <= a < want + cap) (fun a => a = want) fx1 L' A' mem2 md2 X Lam
        peak cnt (rf_free F bnd cap) ENT INV ST3).
      - lia.
      - lia.
      - intros a Ha. right. right. split; [lia|]. split.
        + replace a with (want + (a - want)) by lia. apply WIMG. lia.
        + intros b k Hb Hne Hbk.
          exact (blocks_apart B API HSEG AX FG L A mem md want cap b k a MRc WBLK Hb (fun e => Hne (eq_sym e)) Ha Hbk).
      - intros a Ha Hw. lia.
      - intros a k Hb Hk Ea. exact (WNB a k Hb Hk Ea).
      - intros a k Hin Hk. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
      - exact RA2.
      - exact FRM.
      - intros r _. reflexivity.
      - apply (ledger_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
          (fun a => a = want) L A mem md L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) MRc LED ST3).
        + intros a Ha. destruct (rc_stat_rng a Ha) as (Hs1 & Hs2).
          split; [unfold rwin; rewrite ERRB; lia|].
          intros Hw. apply (WIMG (a - want)); [lia|]. replace (want + (a - want)) with a by lia.
          exact (proj1 (statics_img B API HSEG AX FG a Ha)).
        + intros a k Hin. destruct (LAMOK a k Hin) as (H1 & H2). split; [exact H1 | exact H2].
      - lia.
      - exact PERM.
      - apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
          (fun a => a = want) L A mem md L' A' mem2 md2 Lam Lam peak cnt (2 ^ 64 - 1) doc t D MRc LED NODE DL DL ST3);
          [lia | |].
        + intros i Hi. split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia | lia].
        + intros a k Hin. destruct (LAMOK a k (DL _ Hin)) as (H1 & H2). split; [exact H1|].
          intros i Hi. apply H2. lia.
      - exact RS2. }
    exact (K L' A' regs2 mem2 md2 INV2 RR ST3).
Qed.

End FW.

Section FT.
Hypothesis FF : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API F.

(* fuzz_free (text) entered with sp = S - 112: the ledger block (q, w) of pj_write's text goes; the walk invariant
   holds after it with the own-block list X and the bound rf_free bnd (w + 16) *)
Lemma rc_ffree_text : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D,
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  forall (fx1 : YK11.FPState) L A regs mem md X Lam peak cnt bnd q w (P : config -> Prop),
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md (X ++ [(q, w)]) Lam peak cnt bnd ->
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = Z_to_bv 64 q ->
  0 < q -> In (q, w) Lam -> (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> q - 16) ->
  (forall L' A' regs' mem' md' Lam',
     @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem' md' X Lam' peak cnt
       (rf_free F bnd (w + 16)) ->
     regs_preserved regs regs' ->
     (forall a k, In (a, k) Lam -> a <> q -> In (a, k) Lam') ->
     rstep B API ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16) L A mem md L' A' mem' md' ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs (Z_to_bv 64 FUZZ_FREE) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT fx1 L A regs mem md X Lam peak cnt bnd q w P
    INV G2 G4 GRA G10 Hq0 HqL HqB K.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & DNODE & DSUB & DOC0 & DOCS & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODED & RES & _).
  pose proof RS as (MRc & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) q w MRc LED HqL)
    as (Hw0 & Hqblk & Hq1 & Hq2 & Hqimg).
  pose proof (rc_node_top _ _ _ _ _ _ DNODE) as (_ & DOCT).
  pose proof LED as (_ & _ & _ & _ & ND & _).
  pose proof (rc_nd_perm Lam (X ++ [(q, w)]) Lam0 PERM ND) as NDX.
  assert (QL0 : forall a k, In (a, k) Lam0 -> a <> q).
  { intros a k Ha E. symmetry in E. revert E.
    apply (rc_disj (X ++ [(q, w)]) Lam0 q w a k NDX); [apply in_or_app; right; left; reflexivity | exact Ha]. }
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  assert (SPr : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply rc_uns; lia).
  assert (CPK : call_pre_k B (aa_MR API) ALLOC_STACK L A regs mem md).
  { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs
      ALLOC_STACK 112 PRE0 RS INIT); [exact SPr | rewrite SPr; Z.div_mod_to_equations; lia | exact G4 | exact GRA |
      lia | lia | lia]. }
  eapply SR_bind; [exact (FF fx1 L A regs mem md q w bnd Lam peak cnt (2 ^ 64 - 1) CPK G10 LED (proj1 RD)
    (or_intror HqL) RES)|].
  intros c' (L' & A' & regs2 & mem2 & md2 & -> & RO2 & _ & IN' & _ & CP2 & _ & KP & _ & Arms).
  destruct Arms as [(Hqz & _) | (_ & (b1 & b2 & EB1 & EB2) & (l1 & l2 & EL & LG2) & RS2)]; [lia|].
  pose proof CP2 as (M2 & _ & _ & _ & _ & RR2 & _).
  assert (INL : forall a k, In (a, k) Lam -> a <> q -> In (a, k) (l1 ++ l2)).
  { intros a k Hin Hn. rewrite EL in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hn; congruence | right; exact H]. }
  assert (PERM2 : Permutation (l1 ++ l2) (X ++ Lam0)).
  { assert (H : Permutation ((q, w) :: l1 ++ l2) ((q, w) :: X ++ Lam0)).
    { apply (Permutation_trans (Permutation_middle l1 l2 (q, w))). rewrite <- EL.
      apply (Permutation_trans PERM). rewrite <- app_assoc. apply Permutation_sym. apply Permutation_middle. }
    exact (Permutation_cons_inv H). }
  assert (STEP : rstep B API ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
      L A mem md L' A' mem2 md2).
  { rewrite <- SPr. apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L A regs mem md _ _ L' A' regs2 mem2 md2
      MRc CP2 IN').
    - intros a k Hin Hk Hg. cbv beta in Hg. rewrite EB1 in Hin. rewrite EB2. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hg; lia | right; exact H].
    - intros a k i Hin Hg Hi _. exact (KP a k i Hin Hg Hi). }
  assert (FWq : forall a k i, In (a, k) Lam -> a <> q -> 0 <= i < k -> ~ free_writes q w (a + i)).
  { intros a k i Hin Hn Hi [Hf|(_ & Hf)].
    - apply (rc_not_statics B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k i MRc LED Hin ltac:(lia)).
      unfold alloc_statics. left. exact Hf.
    - apply (rc_apart B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k q w (a + i) MRc LED Hin HqL Hn); lia. }
  assert (FWhi : forall x, alloc_ceiling <= x -> ~ free_writes q w x).
  { intros x Hx [Hf|(_ & Hf)]; [unfold G_LIVE in Hf; lia | lia]. }
  assert (RWhi : forall x, spZ regs0 - 112 <= x < 2 ^ 64 -> ~ rwin B ALLOC_STACK (spZ regs0 - 112) x).
  { intros x Hx [Hr|Hr]; [lia | rewrite ERRB in Hr; unfold strtod_c.STRTOD_ERRNO in Hr; lia]. }
  assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem2 md2 X (l1 ++ l2) peak cnt
      (rf_free F bnd (w + 16))).
  { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md
      (X ++ [(q, w)]) Lam peak cnt bnd ALLOC_STACK (free_writes q w) (fun a => a = q - 16) fx1 L' A' mem2 md2 X
      (l1 ++ l2) peak cnt (rf_free F bnd (w + 16)) ENT INV STEP); try lia.
    - intros a [Ha|(_ & Ha)].
      + left. unfold alloc_statics. left. exact Ha.
      + right. right. split; [lia|]. split.
        * intros Hi. apply (Hqimg (a - q) ltac:(lia)). replace (q + (a - q)) with a by lia. exact Hi.
        * intros b k Hb Hg. cbv beta in Hg.
          exact (blocks_apart B API HSEG AX FG L A mem md (q - 16) (w + 16) b k a MRc Hqblk Hb
            (fun E => Hg (eq_sym E)) ltac:(lia)).
    - intros a Ha Hf. exfalso. apply (FWhi a); [lia | exact Hf].
    - intros a k Hin Hk. exact (HqB a k Hin Hk).
    - intros a k Hin Hk. rewrite EB1 in Hin. rewrite EB2. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
    - exact RO2.
    - exact FRM.
    - intros r Hr. reflexivity.
    - exact LG2.
    - exact PERM2.
    - apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
        L A mem md L' A' mem2 md2 Lam (l1 ++ l2) peak cnt (2 ^ 64 - 1) doc t D MRc LED NODED DL); [| exact STEP | lia | |].
      + intros [a k] Hb. apply INL; [exact (DL _ Hb) | exact (QL0 a k (DSUB _ Hb))].
      + intros i Hi. split; [apply RWhi; lia | apply FWhi; lia].
      + intros a k Hb. pose proof (QL0 a k (DSUB _ Hb)) as Hn. split; [cbv beta; lia|].
        intros i Hi. exact (FWq a k i (DL _ Hb) Hn Hi).
    - exact RS2. }
  exact (K L' A' regs2 mem2 md2 (l1 ++ l2) INV2 RR2 INL STEP).
Qed.

End FT.

End W.
