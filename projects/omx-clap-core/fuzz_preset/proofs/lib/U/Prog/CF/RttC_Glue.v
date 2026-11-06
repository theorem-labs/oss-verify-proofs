From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import PjWriteHyp round_trip_text_c fuzz_free_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import RttGlue RttModel RttBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

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

(* #102: RTT_F 112 (addi sp, sp, -0x70 at ROUND_TRIP_TEXT 0x15334) and RTT_K = RTT_F + CF parse_noting_c.PN_K
   (CF round_trip_text_c at cold/h-rw-pre-4-rw102-rtt 683b0b9349d6): 112 + (48 + max PJ_PARSE_K 16) = 112 + 14208.
   The mirror of lib/Prog/RttC_Glue.v (plain, cold/h-drain-a1-p102-T1 57cb05617903). *)
Lemma rc_rttk : RTT_K = 14320 /\ ALLOC_STACK = 8192 /\
  forall d, (d <= 32)%nat -> 0 <= PJ_FREE_K d /\ RTT_F + PJ_FREE_K d <= RTT_K.
Proof.
  assert (E : RTT_K = 14320) by (vm_compute; reflexivity).
  split; [exact E|]. split; [reflexivity|]. intros d Hd. rewrite E.
  unfold RTT_F, PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK. lia.
Qed.

(* #102: the alloc.c words lie in [GL_FAIL, GL_COUNT + 8) (LedgerCells, generated from the #102 ubsan twin). *)
Lemma rc_stat_rng : forall a, alloc_statics a -> GL_FAIL <= a < GL_COUNT + 8.
Proof. intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold GL_FAIL, GL_COUNT. lia. Qed.

(* #102 rtt_regs (CF RttBase, the mirror of plain RttBase 1a5309005128): sp = S-112, s0 = copy, s1 = regs0 a0,
   s2..s5 = s2v..s5v, gp / tp kept, s6..s11 kept. *)
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

(* #102 shared exit (0x153f8..0x1541c): ld ra, s0..s5 from [S-56, S), addi sp, 0x70: ra s0 s1 s2 s3 s4 s5 come back
   from regs0, gp / tp / s6..s11 from rX. *)
Lemma rc_ret_pres : forall regs0 rX regs3 copy s2v s3v s4v s5v
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rtt_regs regs0 rX copy s2v s3v s4v s5v ->
  (forall r, getr regs3 r = getr (LFrame.mkR (getr regs0 1) (Z_to_bv 64 (spZ regs0)) (getr rX 3) (getr rX 4) t0 t1 t2
     (getr regs0 8) (getr regs0 9) a0 a1 a2 a3 a4 a5 a6 a7 (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21)
     (getr rX 22) (getr rX 23) (getr rX 24) (getr rX 25) (getr rX 26) (getr rX 27) t3 t4 t5 t6) r) ->
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
