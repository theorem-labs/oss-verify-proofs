(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Keeps F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit MonadF Strnlen_iface F_printf_iface I_memcpy AF_atexit ADriver_iface AD_kit AD_emit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
Local Ltac transport_after_call segs m m' MU WM ::=   (* [comment removed for export] *)
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ first [ fp_cover8   (* [comment removed for export] *)
                        | unfold sub_fp; cbn [outside]; intros; Zify.zify; xlia zchecker
                        | unfold sub_fp; cbn [outside]; sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | unfold sub_fp; cbn [outside]; intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.
(* [comment removed for export] *)

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tleaf {R} (t : itree node R) (r : R) : Prop :=
  match t with
  | ITree.Ret r' => r' = r
  | ITree.Vis n k => exists rsp, tleaf (k rsp) r
  end.
Definition mleaf {A} (c : @Monad.M APS A) (s : APS) (a : A) (s' : APS) : Prop := tleaf (c s) (Ok (a, s')).

Lemma tleaf_bind {A B} (t : itree node A) (f : A -> itree node B) r :
  tleaf (ITree.bind _ t f) r -> exists x, tleaf t x /\ tleaf (f x) r.
Proof.
  induction t as [a|n k IH]; cbn; intros H.
  - exists a. split; [reflexivity| exact H].
  - destruct H as [rsp H]. destruct (IH rsp H) as (x & Hx & Hf). exists x. split; [exists rsp; exact Hx| exact Hf].
Qed.
Lemma mleaf_bind {A B} (c : @Monad.M APS A) (f : A -> @Monad.M APS B) s b s' :
  mleaf (Monad.mbind c f) s b s' -> exists a s1, mleaf c s a s1 /\ mleaf (f a) s1 b s'.
Proof.
  unfold mleaf, Monad.mbind, ebind. intros H. destruct (tleaf_bind _ _ _ H) as (x & Hx & Hf).
  destruct x as [|[a s1]]; [cbn in Hf; discriminate Hf|]. exists a, s1. split; assumption.
Qed.
Lemma mleaf_ret {A} (a : A) s b s' : mleaf (Monad.mret a) s b s' -> b = a /\ s' = s.
Proof. unfold mleaf, Monad.mret. cbn. intros H. inversion H. auto. Qed.

Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma implF_leaves : forall {R} RNG (t : itree node R) (Q : R -> footprint -> machine_state -> Prop) ms,
  implS asegs RNG t Q ms -> implS asegs RNG t (fun r RNG' ms' => Q r RNG' ms' /\ tleaf t r) ms.
Proof.
  intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q ms H; cbn in *.
  - eapply evtF_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF.
    eapply implF_mono; [apply IH; apply Hk; exact HF|]. intros r RNG'' ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.
#[using="Type"] Lemma implMA_leaves : forall {A} RNG (c : @Monad.M APS A) s (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG c s Q ms -> implMA RNG c s (fun a s' RNG' ms' => Q a s' RNG' ms' /\ mleaf c s a s') ms.
Proof.
  intros A RNG c s Q ms H. unfold implMA, mleaf in *. eapply implF_mono; [apply implF_leaves; exact H|].
  intros [|[a s']] RNG' ms' [HQ HL]; cbn in *; [exact HQ|]. split; assumption.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fuzz_oneA_leaf0 : forall payload s r s', mleaf (fuzz_oneA AAllocAsan payload) s r s' -> r = 0.
Proof.
  intros payload s r s' H. unfold fuzz_oneA, Harness.fuzz_one in H.
  repeat (apply mleaf_bind in H; destruct H as (? & ? & _ & H)).
  apply mleaf_ret in H. exact (proj1 H).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma libc_need_locks : forall (m : amem) (cdt thr sec : byte) (tm1 : word),
  rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] -> rw_cells asegs m APNEED_LOCKS [C1 (Z_to_bv 8 0)].
Proof.
  intros m cdt thr sec tm1 H.
  apply (proj1 (rw_cells_app asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec] [C1 (Z_to_bv 8 0); C4 tm1])) in H. destruct H as [_ H].
  apply (proj1 (rw_cells_app asegs m _ [C1 (Z_to_bv 8 0)] [C4 tm1])) in H. destruct H as [H _].
  unfold APNEED_LOCKS. exact H.
Qed.
End CANSEC0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section RUN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  (* [comment removed for export] *)
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  (* [comment removed for export] *)
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Let EMIT : emit_printf_stmtA := emit_printf_proofA HSTRN.

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG00 : footprint) (rstk : region) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
            (LB : list ablock) (p : AsanCtrl.aptr) (A cap Lc : Z) (content : list Z) (lo : Z) (canary : word).
  Hypothesis INLB : In (HB p A cap) LB.
  Hypothesis HLBH : forall b, In b LB -> exists p' A' n', b = HB p' A' n'.
  Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
  Hypothesis LC : zlength content <= cap.
  Hypothesis CAP : cap <= 2^26.
  Hypothesis L0 : 0 <= Lc.
  Hypothesis L6 : 6 + Lc <= zlength content.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPG : bv_unsigned sp + 128 = al_sp0 L.   (* [comment removed for export] *)
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis CEIL : ATOP <= lo.
  Hypothesis SPHI : bv_unsigned sp < 2^47.
  Hypothesis LO : lo <= bv_unsigned sp - ATARGET_RUN_STACK.
  Hypothesis RSlo : r_lo rstk <= lo.
  Hypothesis RShi : bv_unsigned sp <= r_hi rstk.
  Hypothesis RSceil : ATOP <= r_rlo rstk.
  Hypothesis HUL : HU L.
  Hypothesis UM1 : In [AMALLOC_PC; 0x7fac4] (al_U L).
  Hypothesis UF1 : In [AFREE_PC; 0x7fb58] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Hypothesis HLB : forall b, In b LB -> 0x5f6000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.

  Notation usp := (bv_unsigned sp).
  Notation tpv := (Z_to_bv 64 ATP).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).

  (* [comment removed for export] *)
  Definition plen : Z := zlength content - 6 - Lc.
  Definition PAY : Z := A + 6 + Lc.
  Definition payload : list Z := skipn (Z.to_nat (6 + Lc)) content.
  Definition cfg : Z := if 0 <? Lc then znth content 2 else 0.
  Definition calls : Z := 1 + Z.land cfg 3.

  (* [comment removed for export] *)
  Definition LBT (own : option (AsanCtrl.aptr * Z)) : list ablock :=
    match own with None => LB | Some (q, D) => HB q D plen :: LB end.
  Definition dptr (own : option (AsanCtrl.aptr * Z)) : Z := match own with None => AEMPTY | Some (_, D) => D end.
  Definition oreg (own : option (AsanCtrl.aptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
  Definition omodel (own : option (AsanCtrl.aptr * Z)) : option AsanCtrl.aptr := match own with None => None | Some (q, _) => Some q end.

  (* [comment removed for export] *)
  Definition FRAME (m : amem) : Prop :=
    exists j0 : list byte, rw_cells asegs m (usp + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition RNGS (RNG : footprint) : Prop :=
    rng RNG lo (usp + 128 - lo) /\ rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG
    /\ rrng RNG rstk /\ rrng RNG RFMT /\ rrng RNG RBstdout /\ fp_le RNG00 RNG.

  #[using="rng_fs_mono"] Lemma RNGS_mono : forall R R', fp_le R R' -> RNGS R -> RNGS R'.
  Proof.
    intros R R' LE (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold RNGS, rrng in *.
    repeat match goal with |- _ /\ _ => split end; try (eapply rng_fp_le; [exact LE|]; assumption).
    - eapply rng_fs_mono; eauto.
    - eapply fp_le_trans; eauto.
  Qed.

  (* [comment removed for export] *)
  Definition BASE (st : APS) (m : amem) : Prop :=
    FRAME m /\ harness_invA m
    /\ rodata_sh0 m /\ rclean m rstk /\ rclean m RBstdout
    /\ mem_inv asegs m /\ stk asegs m lo (usp + -80)
    /\ stdout_file m (aps_so st) /\ aps_ok L st /\ rw_cells asegs m ssp_guard [C8 canary]
    /\ adrv_pres AI LB usp m0 m.
  (* [comment removed for export] *)
  Definition ATX (v : Z) (m : amem) : Prop :=
    atx_cellsA 2 APATX_CALLFN APEXIT_GUARD m /\ rw_cells asegs m 0x5d34d4 [C1 (Z_to_bv 8 v)] /\ rw_cells asegs m 0x132d20 [C1 (Z_to_bv 8 0)].
  #[using="Type"] Lemma ATX_state : forall m, ATX 0 m -> atx_stateA true m.
  Proof. intros m H. exact H. Qed.
  #[using="rc sp"] Lemma ATX_magree : forall (P : Z -> Prop) m m' v,
    magree asegs P m m' -> (forall a, atx_state_addrA a -> P a) -> ATX v m -> ATX v m'.
  Proof.
    intros P m m' v AG HP (AX & CB & CF). split; [| split].
    - eapply atx_cellsA_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
    - Local Ltac2 Set LiaHints.tbl := fun () => "0020>12449347403.7567733905099.75000004008S2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; left; cbn in Ha; lia].
    - eapply rw_cells_magree; [exact AG| exact CF| intros a Ha; apply HP; right; right; cbn in Ha; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Definition INV0 (own : option (AsanCtrl.aptr * Z)) (st : APS) (m : amem) : Prop :=
    BASE st m /\ bytes_at asegs m (dptr own) (zbytes payload) /\ ATX 0 m.
  Definition INV (own : option (AsanCtrl.aptr * Z)) (RNG : footprint) (st : APS) (m : amem) : Prop :=
    AHEAP AI L RNG (aps_m st) (LBT own) m /\ RNGS RNG /\ INV0 own st m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 k t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) x19 (wz AINIT_FLAG) (wz k) (wz 0) (wz (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition RUNST (own : option (AsanCtrl.aptr * Z)) (pc : Z) (k : Z) (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 k t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own RNG st m.

  (* [comment removed for export] *)
  #[using="rc sp cap FC LC CAP L0 L6"] Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + Lc.
  Proof.
    unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
    assert (CF : 0 <= (if 0 <? Lc then znth content 2 else 0) < 256).
    { Local Ltac2 Set LiaHints.tbl := fun () => "00<0>11411152466.6614793723106.6615585054971.6520303486233.6622230016890.6635229186603.6748555178824.6648561457008.6553843967398.6657019999243.6557022093363.646913398412.66 00000300:00C00G00R00Z00^00b00e00h00i00mS1HS2L02L6S2L02L61HS2L6S2LC3CAP2L0S1H2LT1XS2CFS2CFS1HS1HSS2CF".
destruct (0 <? Lc); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
      assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
      pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
    pose proof (land3_range (if 0 <? Lc then znth content 2 else 0) ltac:(lia)).
    repeat split; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="rc LO"] Lemma LO' : lo <= usp - 80 - AHARNESS_STACK.
  Proof. unfold ATARGET_RUN_STACK in LO. Local Ltac2 Set LiaHints.tbl := fun () => "0010>20931172449.64000004S2LO".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 BOT CEIL SPHI LO"] Lemma geo : 0x10007fff8000 <= lo /\ 0x7fff7f800000 <= lo /\ lo <= usp - 80 - 16384 /\ 0 <= usp < 2^47 /\ usp mod 16 = 0.
  Proof.
    pose proof LO' as L'. unfold AHARNESS_STACK in L'. pose proof CEIL as C. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp). Local Ltac2 Set LiaHints.tbl := fun () => "0050>13593960149.6733593755118.6742148885575.6747072207111.67693771091.67  00000900?00I00M00QS4SP162H0S4SPHIS3BOT1H2H0S2L'S2H0".
repeat split; try lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc SP16 BOT CEIL SPHI LO"] Lemma trun_init : forall RNG (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (cdt thr sec : byte) (tm1 : word),
    stk asegs m lo usp -> mem_inv asegs m -> atrun_cells0 m ->
    rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m AGOT_FUZZ_INIT [C8 (wz AFUZZ_INIT)] ->
    rng RNG lo (usp + 128 - lo) -> rng_aimg RNG ->
    (forall (m' : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FRAME m' -> stk asegs m' lo (usp + -80) ->
        munch [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)] m m' ->
        wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' AINIT_FLAG [C1 (Z_to_bv 8 1)] -> ATX 0 m' ->
        evtF asegs RNG Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 (wz 0) x11 x12 x13 x14 x15 x16 x17
                                   a1 a0 (wz AINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                             F (Z_to_bv 64 0x7faa8) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ATARGET_RUN) fc None m (seg_rom asegs)).
  Proof.
    intros until tm1. intros ST MI TR LIBC GFI RSTK RIMG K. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    destruct TR as (PI & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF).
    pose proof (libc_need_locks _ _ _ _ _ LIBC) as NL.
    unfold AINIT_FLAG, AGOT_FUZZ_INIT, AFUZZ_INIT, AAEF_ARGC, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG, APNEED_LOCKS in *. cbn [negb] in X3, X8, X9.
    pose proof (munch_refl [(usp - 128, usp); (0x5d34d0, 0x5d34d0 + 1); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ATARGET_RUN. sort_lits.
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "03`0?10980438552.12811224394751.13011472836995.1241152502513.128 11530975896.1281162083372.124 11658450183.1321216493765.3   12216817688.12812468251268.13013051406724.13013234623000.12813242682756.1301343986644.132 15215617816.12815688435136.12616787763480.12816801487256.12716817863562.1111696738378.3   17749711256.12717776320429.12317829128836.130183032088.129  18324025034.3  18359819160.12819042827563.12719125215256.12719187767192.12719291618456.1271937059352.128 19411207320.12719757891864.1262005795736.128 20102708004.13020404548996.1302107897624.128 21476634491.3  21646008187.3  21724205888.12522226183811.12522237172376.12822480013002.3  22949726232.12823706670360.12623738063896.12724436996044.3  24727303576.12725860552984.12925871243800.12825878270252.12426058469174.11426313435160.12826360729112.12926405009432.12626604760216.12726992675972.13027147338155.12627308953112.1292745835288.128 27498241560.1262761856388.130 27723960707.12427791500568.12827924845976.12828072922155.12728369395992.1262885283352.128 28868026202.3  29527680280.12929754860426.3  3051486595.124 30564739992.127310064792.127  31067574040.12831161366443.12631558065432.12631774658966.12932227944728.12832507878296.12832865795786.3  32891356440.12833020489418.3  33049376152.12833313664792.12833375747096.1283369895192.129 34508518533.3  35526766232.12735909988007.12436115622444.12436213580312.12936338705304.12736344913816.12736371805104.3  3668568768.127 37081859844.13037224984778.3  37394358474.3  37815536536.12738397901439.1323844324376.128 3872907672.128 38863070852.1303897141656.128 39085949080.12739086929944.12939337055114.3  39412320024.1283968803480.127 39769365440.12439987590410.3  40360544024.12840374333670.11741150387864.12841301930264.12741779725592.12841904973208.12742084894980.13042146777215.11142200251523.12542283686176.1114228409541.3   43059643189.11543121191467.12543872801176.12743958150168.1264398566296.127 43987951407.1254415404056.126 44534409240.12844977136295.12645691690520.12745766293656.12745788883264.1264646140824.127 46769156760.12746807179466.3  46887021955.12547041642264.12947234531096.12847367953560.12747403297147.3  47663274663.12548031579032.12848313144512.1264862590488.126 4889764504.127 50285327492.13050311723544.12950344059160.12650592949656.12650628941955.12550664164139.12850667478351.13250867127448.12751234361003.12751430120600.12751678667181.12352477327384.12852512108618.3  52577538839.12652577538839.12752577538839.12852577538839.12952577538839.13052579502455.13252666802250.3  52742303000.12752785972376.12753184435608.12753378168088.12653767577772.12454076858136.12954185434895.13254315885120.12554505215896.12755841003544.12855958408871.12556174447011.11156185989799.12557328287384.12857447876248.12758819719576.12858938499460.1305896867971.123 59308628304.1  59308628433.1  59314873579.12059457942168.12859494614808.12859511939864.12859522377383.12460111391000.12860137899154.12760334854080.12660566055576.12960688318616.12960850650776.12861005229130.3  61042262168.12761085634840.12861603222095.13261917199021.12361994440323.12662316770328.12862534273994.3  62670790311.12562853186584.12663235321901.12263646685401.12963826654415.13263964933016.12764097026584.12864636699416.12864707516824.12865062890008.1286517862296.127 65212743211.12765409584920.12865441969354.3  65613440202.3  65941593752.12866118714776.12766131249304.12866639935768.12867260705573.11167446113816.12967965490855.1236941457560.127 7243127832.128 8044187544.126 8297047192.127 8603416747.126 8697660952.127 894743207.124  8968821784.128 9533375050.3   9668950080.125 9732359576.127 00000700>00?00@00G00K00L00M00T00U00V00]00^00_00f00j01101801901:01A01E01F01M01N01U01[01b01i02002702>02E02L02M02N02U02V02W02[02\02c02d02k03203903>03E03L03S03W03h03o04604=04D04E04K04R04Y04`04a04b04i05005605=05D05E05L05M05N05U05\05c05i06006106806?06@06G06H06O06V06]06d06e06l06m07107807?07F07K07O07P07Q07R07Y07g07n08508608=08D08K08L08S08Z08^08_08f08g08n09509<09C09D09H09I09J09K09O09U09\09c09j09n0:50:<0:=0:D0:K0:O0:V0:]0:^0:_0:f0:m0;40;50;60;=0;A0;H0;O0;P0;W0;^0;e0;f0;l0<:0<A0<G0<N0<R0<Y0<Z0<[0<\0<]0<^0<_0<j0<k0=20=90=@0=G0=K0=R0=`0=d0=k0>20>30>40>50><0>C0>J0>K0>L0>P0>T0>X0>_0>f0>m0>n0?50?60?:0?A0?H0?O0?P0?W0?^0?l0@00@10@80@90@:0@A0@E0@F0@T0@[0@b0@i0A00A70A>0AD0AK0AL0AM0AT0A[0Ab0Ai0Am0B40B50B<0BC0BJ0BQ0BW0B^0B_0Bf0Bg0Bk0C2S2G22G3S2G22G3SSS2G22G3S2G3FFS2G22G3SSS2G22G3SFS2G22G3S2HBS2G22G3S2G22G3SFS2G22G3S2G3SS2G22G3SS2G22G3S4SPHIS2G22G3S2G22G3S2G22G3S2G22G3S2G22G3S2G22G3S2G22G3SSS2G22G3FFS2HBSS2G22G3SS2G22G3S2G22G3S2G22G3S3HspS2G22G3S2G22G3S2G22G3S2G3S4SPHI2G22G32G41HS2G22G3S2G22G3S2G22G3S2G22G3SS4SPHIS2G22G3S2G22G3S2G22G3SSS2G22G3S2G22G3S4SPHIS2G22G3S2G22G3FS2G22G3FSS2G22G3S2G22G3S2G22G3S4SPHIS2G22G3SS2G22G3S2G22G3SS2G22G3SS2G22G3S2G22G3S2G22G3S2G22G3FS2G22G3SS2G3S2G22G3S2G22G3S2G22G3S3HspS2HBSFSS2G22G3S2G22G32G43HspS2G22G3S2G22G3SS2G22G3S2G22G3S2G22G3FS2G22G3S2G22G3S2HBFS2G22G3SS2G22G3S2G22G3S2G22G3S2G22G3SS2G1SFFS2G3S4SPHIS2G22G3S2G22G3S2G22G3S2G3S2G22G3S2G22G3SS2G22G3S2G22G3S2HBS2G22G3S2G22G3SSS2G22G3S2G22G3S2G22G3FSS2G22G3S2HBS2G22G3S2G22G3SS2G22G3S2G22G3S2G22G3SS4SPHIS2G22G32G43HspS2G22G3S4SPHIS2G22G3S2G3S2G22G3SSSSSSS2G22G33HspSS2G22G3S2G22G3S2G22G3S2G22G3S2G3S2G22G3S2G22G32G43HspS2HBS2G22G3S2G22G3SSSS2G22G3S2G22G3S2G22G3SSS2K1S2K2S2K0S2G22G3S2G22G3S2G22G3SS2G22G3FS2HBS2G22G3S2G22G3S2G22G3FS2G22G3S2G22G3S2G22G32G43HspS2G3SS2G22G3SSS2G22G3S2G3SS2G22G32G43HspS2G22G3S2G22G3S2G22G3S2G22G3S2G22G3S2G22G3S4SPHIS2G22G3SSS2G22G3S2G22G3S2G22G3S2G22G3S2G3S2G22G3SS2G22G3S2G22G3S2G22G3S2G22G3S4SPHIS2G22G3SS2G22G3SS2HBS2G22G3".
carve_frame 80%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AX : atx_cellsA 1 0 0 mx) by (exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 X9))))))))) end.
    clear X1 X2 X3 X4 X5 X6 X7 X8 X9.
    call_sp (patexit_specA RNG);
      try (first [ exact AX | exact NL | hyp_by_addr | reflexivity | unfold KHIGH; lia | exact RIMG | (eapply rng_sub'; [exact RSTK | lia]) | lia ]).
    clear AX.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    do 3 zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - eexists. hyp_by_addr.
    - hyp_by_addr.
    - lazymatch goal with H : munch _ m _ |- _ => exact H end.
    - lazymatch goal with H : wmono asegs m _ |- _ => exact H end.
    - hyp_by_addr.
    - hyp_by_addr.
    - unfold ATX, APATX_CALLFN, APEXIT_GUARD. split; [| split; hyp_by_addr]. lazymatch goal with H : atx_cellsA _ _ _ _ |- _ => exact H end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Section AfterCallee.
    Variables (LX : list ablock) (SP' : Z) (m m' : amem).
    Hypothesis HP : aheap_pres CI LX SP' m m'.
    Hypothesis HS : astk_shadow_pres SP' m m'.
    Hypothesis SPlo : lo <= SP'.
    Hypothesis SPhi : SP' <= usp + -80.
    Hypothesis SP8 : SP' mod 8 = 0.
    Hypothesis HL : forall b, In b LB -> In b LX.

    Let AG : magree asegs (dcli CI LX SP') m m' := magree_of_dpost CI LX SP' m m' HP HS.

    #[using="DRV_CI sp"] Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LX SP' a.
    Proof. intros lo' hi' a Hin Ha. left. right; left. exists (lo', hi'). Local Ltac2 Set LiaHints.tbl := fun () => "0010=2594151127.80000004S2Ha".
split; [apply DRV_CI; exact Hin| cbn; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="DRV_CI sp"] Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LX SP' a.
    Proof.
      intros lo' hi' a Hin Ha H8' H8. left. right; right; right. exists (8 * (a - ASHOFF)). split.
      - right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020>33246254979.818282340483.81 00000;00<S2Ha3H8'2H8S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - rewrite shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="CLI_CI sp"] Lemma ci_cli_sh : forall lo' hi' a, In (lo', hi') cli_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LX SP' a.
    Proof.
      intros lo' hi' a Hin Ha H8. left. right; right; right. exists (8 * (a - ASHOFF)). split.
      - right; left. exists (lo', hi'). split; [apply CLI_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020>33246254979.808282340483.80 000007008S2Ha2H8S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - rewrite shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="lo SP16 BOT CEIL SPHI LO SPlo SPhi"] Lemma stack_dcli : forall a, usp + -80 <= a < usp -> dcli CI LX SP' a.
    Proof. intros a Ha. pose proof geo. left. left. Local Ltac2 Set LiaHints.tbl := fun () => "0010>14192466545.7800000GS3BOT4SPlo4SPhi2Ha1H2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    (* [comment removed for export] *)
    #[using="sp lo BOT SPlo SPhi SP8"] Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LX SP' a.
    Proof.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad SP')) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). Local Ltac2 Set LiaHints.tbl := fun () => "0030>10470681520.838119758914.81 8282276668.81 00000J00a00bS3BOT4SPlo4SPhi2Ha2LT1H2H0S3BOT4SPlo3SP82H22Ha2GES".
lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split.
        + left. rewrite !shad_div in *. unfold ASHOFF, KEND in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        + rewrite shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    #[using="DRV_CI CLI_CI SP16 BOT CEIL SPHI LO RSceil LX SP' HP HS SPlo SPhi SP8 HL AG"] Lemma BASE_after_dpost : forall st st' RNG' LX',
      BASE st m ->
      AHEAP AI L RNG' (aps_m st') LX' m' -> aps_rest st' = aps_rest st ->
      mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
      BASE st' m'.
    Proof.
      intros st st' RNG' LX' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP) AH' ESO MI' ST'.
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSceil as RSC. atop_facts.
      split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. Local Ltac2 Set LiaHints.tbl := fun () => "0090?33593762214.10437248714508.10245579130899.10246887762672.10248319357316.10449053759698.10454149153897.1035721498072.102 5849298032.102 00000600<00D00H00N00^00b00f00jS4SPHIS4HL64S6RSceilS2HaS4SPhiS4SPlo3SP82G22G4S2HaS2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split.
      { pose proof CLI_CI as _unusedCI. eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply (ci_drv_sh 0x20d40 0x20dc0); [unfold drv_img_ranges; cbn; tauto| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x20d00); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo rstk) (r_rhi rstk)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x5f4500 0x5f4940); [do 7 right; left; reflexivity| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split; [exact MI'|]. split; [exact ST'|].
      split. { rewrite (aps_so_of_rest _ _ ESO). eapply stdout_file_magree; [exact AG| | exact SO]. intros a [Ha|Ha].
               - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [do 3 right; left; reflexivity| exact Ha].
               - apply (ci_drv 0x5f4500 0x5f4940); [do 7 right; left; reflexivity| cbn in Ha |- *; lia]. }
      split. { eapply aps_ok_rest; [exact ESO| exact RK]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x5f3e50 0x5f3e58); [do 9 right; left; reflexivity|].
               unfold ssp_guard in Ha. cbn in Ha. lia. }
      eapply adrv_pres_trans; [exact DP|]. intros a Ha [Hc|Hs] Hx.
      - apply AG; [exact Ha|]. eapply dcli_weaken; [left; exact Hc| lia| lia| lia| exact HL].
      - apply AG; [exact Ha|]. eapply dcli_weaken; [right; exact Hs| lia| lia| lia| exact HL].
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc AI DRV_CI sp lo BOT SP' HP HS SPlo SPhi AG"] Lemma bytes_after_dpost : forall D bs,
      bytes_at asegs m D bs ->
      ((exists q n, In (HB q D n) LX /\ Z.of_nat (length bs) <= n) \/ (exists lo' hi', In (lo', hi') drv_img_ranges /\ lo' <= D /\ D + Z.of_nat (length bs) <= hi')
       \/ (exists q B n, In (HB q B n) LX /\ B <= D /\ D + Z.of_nat (length bs) <= B + n)) ->
      bytes_at asegs m' D bs.
    Proof.
      intros D bs HBY HW. eapply bytes_at_magree; [exact AG| exact HBY|]. intros a Ha.
      destruct HW as [(q & n & Hin & Hn)|[(lo' & hi' & Hin & H1 & H2)|(q & B & n & Hin & H1 & H2)]].
      - left. right; right; left. exists (HB q D n). Local Ltac2 Set LiaHints.tbl := fun () => "0030>19401133888.842594151127.85 58809290908.8600000G00a01;S3BOT4SPlo4SPhi2Hn2Ha1HS3BOT4SPlo4SPhi2H12H22Ha1HS3BOT4SPlo4SPhi2H12H22Ha1H".
split; [exact Hin| cbn; lia].
      - apply (ci_drv lo' hi'); [exact Hin| lia].
      - left. right; right; left. exists (HB q B n). split; [exact Hin| cbn; lia].
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc AI DRV_CI ra sp m0 LX SP' HP HS AG"] Lemma ATX_after_dpost : forall v, ATX v m -> ATX v m'.
    Proof.
      intros v H. eapply ATX_magree; [exact AG| | exact H]. intros a Ha. unfold atx_state_addrA, atx_addrA in Ha.
      Local Ltac2 Set LiaHints.tbl := fun () => "0040>12455627635.7916091014307.7917800710307.7932427788963.7900000400800<00@S2HaS2HaS2HaS2Ha".
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
        first [ apply (ci_drv 0x5f3e60 0x5f3e90); [unfold drv_img_ranges; cbn; tauto| lia]
              | apply (ci_drv 0x5f3f80 0x5f3f90); [unfold drv_img_ranges; cbn; tauto| lia]
              | apply (ci_drv 0x5d34d0 0x5d3500); [unfold drv_img_ranges; cbn; tauto| lia]
              | apply (ci_drv 0x132d20 0x132d21); [unfold drv_img_ranges; cbn; tauto| lia] ].
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  End AfterCallee.

  (* [comment removed for export] *)
  #[using="rc sp"] Lemma ATX_after_munch : forall v W m m', ATX v m -> munch W m m' -> wmono asegs m m' ->
    (forall a, atx_state_addrA a -> outside W a) -> ATX v m'.
  Proof.
    intros v W m m' H MU WM HW. eapply ATX_magree; [exact (magree_of_munch asegs _ _ _ MU WM)| | exact H].
    intros a Ha. cbn. apply HW. exact Ha.
  Qed.

  (* [comment removed for export] *)
  #[using="DRV_CI A cap FC LC CAP L0 L6 SP16 BOT CEIL SPHI LO"] Lemma after_flag : forall st own RNG m m',
    BASE st m -> AHEAP AI L RNG (aps_m st) (LBT own) m -> bytes_at asegs m (dptr own) (zbytes payload) ->
    match own with None => plen = 0 | Some (_, D) => 0x5f6000 <= D end ->
    munch [(0x5d34d4, 0x5d34d4 + 1)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
    BASE st m' /\ AHEAP AI L RNG (aps_m st) (LBT own) m' /\ bytes_at asegs m' (dptr own) (zbytes payload).
  Proof.
    intros st own RNG m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP) AH PB HD MU WM MI' ST'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    Local Ltac2 Set LiaHints.tbl := fun () => "0070?12444839486.98 22700267513.99 24272767415.96 36540551579.10036540551579.10136540551579.10236540551579.99 00000100500600=00M00T00XSS2HaSS2G42HaS2G22G32G42Ha2HDS2G42HxS2Ha".
assert (AW : appW [(0x5d34d4, 0x5d34d4 + 1)]%Z) by (unfold appW; repeat constructor; cbn; unfold KLOW, KHIGH; lia).
    assert (OUT : forall a, a <> 0x5d34d4 -> (fun a0 : Z => outside [(0x5d34d4, 0x5d34d4 + 1)] a0) a) by (intros a Ha; cbn; lia).
    split; [| split].
    - split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply harness_invA_frame; [exact HI| exact MU| exact WM| exact AW]. }
      split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply OUT. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq in Ha. cbn in Ha. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
      eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT.
      unfold atrun_ivs, AINIT_FLAG in Hx. cbn in Hx. lia.
    - eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
      constructor; [| constructor]. cbn [fst snd]. left. right; left. exists (0x5d34d0, 0x5d3500)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
    - eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="A cap FC LC CAP L0 L6 SP16 BOT CEIL SPHI LO HLB CI_WF"] Lemma BASE_after_emit : forall st st' m m',
    BASE st m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' lo (usp + -80) -> stdout_file m' (aps_so st') -> aps_resv st' = aps_resv st -> aps_atop st' = aps_atop st ->
    BASE st' m'
    /\ forall own, match own with None => plen = 0 | Some (_, D) => 0x5f6000 <= D /\ D + plen <= lo end ->
          bytes_at asegs m (dptr own) (zbytes payload) -> bytes_at asegs m' (dptr own) (zbytes payload).
  Proof.
    intros st st' m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP) MU WM MI' ST' SO' ERV EAT.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    assert (AW : appW [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z).
    { unfold appW. Local Ltac2 Set LiaHints.tbl := fun () => "00A0?16487080957.10218161841858.10128343764437.10628575982988.98 29307869433.10029307869433.10129307869433.10329307869433.99 40461571878.10140463509915.10840463674013.10542146777215.95 43723306049.10543723404353.10246475737191.95 51566774581.95 51790572391.95 00000600900I00Y00]01201G01K01S01a01m02102=02G02H02I02JS2Hx1RS1XS3BOT2G41R2B12B3S3BOT2G32G42Ha1HS2HaS3BOT2G44PLEN2HD2Ha1HS3BOT2G44PLEN2HD2Ha1HS2HaS2G41X1HS2G41R1H2B12B3S2G41R2H02H1S2G1S2G41R2Hx2B1S2Hs2Hx2H0SFS".
repeat constructor; cbn; unfold KLOW, KHIGH; lia. }
    assert (OUT : forall a, (usp + -80 <= a \/ (0x5f6000 <= a < lo) \/ (a < 0x10007fff8000 /\ ~ (0x9d500 <= a < 0x9d500 + 232) /\ ~ (0x5f4520 <= a < 0x5f4520 + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    split.
    2:{ intros own HD PB. eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
        destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia]. }
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
    split. { eapply harness_invA_frame; [exact HI| exact MU| exact WM| exact AW]. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact SO'|]. split; [destruct RK as [RK1 RK2]; split; [rewrite ERV; exact RK1| rewrite EAT; exact RK2]|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
    eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT.
    unfold atrun_ivs, AINIT_FLAG in Hx. cbn in Hx. atop_facts.
    destruct Hc as [Hc|Hs].
    - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
      + left; lia.
      + right; right. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv (DRV_CI' iv Hiv)) as B1 || pose proof (AI_aci_img AI iv Hiv) as B1.
        pose proof (CI_WF iv Hiv) as B0. unfold AIMG_HI in B1. lia.
      + right; left. destruct (HLB b Hb) as (B1 & B2 & B3). lia.
      + right; right. rewrite shad_div. unfold ASHOFF.
        assert (R : 0 <= a' < 2^47).
        { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
          - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). unfold AIMG_HI in *. lia.
          - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. lia. }
        OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right; right. rewrite !shad_div in Hs. unfold ASHOFF in Hs. pose proof geo. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="SP16 BOT CEIL SPHI LO HLB CI_WF"] Lemma BASE_after_munch : forall st W m m',
    BASE st m -> munch W m m' -> wmono asegs m m' -> appW W ->
    (forall a, a < 0x5f6000 \/ 0x7fff7000 <= a < 0x10007fff8000 -> outside W a) ->
    (forall a, usp + -80 <= a -> outside W a) ->
    (forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a) ->
    mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
    BASE st m'.
  Proof.
    intros st W m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP) MU WM AW Wlow Wstk Wblk MI' ST'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. Local Ltac2 Set LiaHints.tbl := fun () => "0090?16083637659.97 18161841858.96 18161841858.97 2797599645.100 2799683493.95  33891828545.97 40461571878.10440461571878.97 40463674013.10200000<00@00C00K00O00R00`00h017S2G42G52Hs1HS2HaS1XS2G41R1HS2HaS1RS2G41R2B12B31HS2G41X1HS2G42R12R21H2H0".
eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply Wstk; cbn in Ha; lia]. }
    split. { eapply harness_invA_frame; [exact HI| exact MU| exact WM| exact AW]. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply Wlow. lia. }
    split; [exact RK|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply Wlow. unfold ssp_guard in Ha. cbn in Ha. lia. }
    eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|].
    destruct Hc as [Hc|Hs].
    - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
      + apply Wstk. lia.
      + apply Wlow. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
      + apply (Wblk b a Hb R).
      + apply Wlow. rewrite shad_div. unfold ASHOFF.
        assert (R : 0 <= a' < 2^47).
        { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
          - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). destruct R as [R1 R2]. unfold AIMG_HI in *. lia.
          - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. atop_facts. lia. }
        right. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - apply Wlow. rewrite !shad_div in Hs. unfold ASHOFF in Hs. right. atop_facts. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="DRV_CI ra m0 SP16 BOT CEIL SPHI LO"] Lemma AHEAP_after_emit : forall RNG st LX m m',
    AHEAP AI L RNG st LX m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    AHEAP AI L RNG st LX m'.
  Proof.
    intros RNG st LX m m' AH MU WM. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
    eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
    - left. left. Local Ltac2 Set LiaHints.tbl := fun () => "0030>10318515423.8124508147902.8165958488200.8100000100200<SSS3BOT4SPHI".
lia.
    - left. right; left. exists (RSTDOUT, RSTDOUT + 232)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
    - left. right; left. exists (0x5f4500, 0x5f4940)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI ASHENV FUZZ HSTRN EMIT A cap HLBH FC LC CAP L0 L6 SP16 SPG BOT CEIL SPHI LO RSlo RShi RSceil HUL HLB CI_WF"] Lemma call_body : forall own k RNG st ms {B} (K : Z -> @Monad.M APS B) (Q : B -> APS -> footprint -> machine_state -> Prop),
    1 <= k <= 4 -> match own with None => plen = 0 | Some _ => 0 < plen end -> RUNST own 0x7fb18 k RNG st ms ->
    (forall rc' RNG' st' ms', RUNST own (if k =? 1 then 0x7fb50 else 0x7fb18) (k - 1) RNG' st' ms' -> rc' = 0 -> implMA RNG' (K rc') st' Q ms') ->
    implMA RNG (rc' <- fuzz_oneA AAllocAsan payload ;; io_emit (ioA AAllocAsan) rc' ;;; K rc') st Q ms.
  Proof.
    intros own k RNG st ms B K Q HK OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (P & RG & (BA & PB & AT))).
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    assert (BOWN : match own with None => True | Some (_, D) => ablock_range D plen /\ 0x5f6000 <= D /\ D + plen <= ATOP end).
    { destruct own as [[q D]|]; [| exact I].
      pose proof (AI_block AI _ _ _ _ _ q D plen P ltac:(left; reflexivity)) as (_ & BR & _).
      pose proof (AI_block_bounds AI _ _ _ _ _ (HB q D plen) P ltac:(left; reflexivity)) as (B1 & B2 & B3). cbn in B1, B2, B3.
      unfold AIMG_HI in B1. Local Ltac2 Set LiaHints.tbl := fun () => "00]0?18459507889.20422700267513.13422700267513.16622844568611.13724391499288.17024391499288.17125316611518.17026060559118.13626060559118.16526060559118.16926060559118.19628575982988.20330058574546.16931412027146.19636099132465.14136099132465.17237491283015.13537994802884.14337994802884.17438688579784.13638688579784.16939364995812.17039364995812.17141167421463.172414080359.199  42146777215.16946196272669.17051028557280.13651319906316.13753867354397.1365407256304.3   54757974937.14254757974937.17356174447011.16958855345930.16559118938897.19959308630497.1  61326644934.13661482382924.16962350818239.14362350818239.17462481520872.19863259952752.3  64653469355.1986566628141.203 00000400800<00?00C00G00S00b01101@01O01\01b01c01d01e02102202302902?02@02A02G02N02R02V02^02d02k03103203303403503<03@03M03N03O03P03T03Z03^03lS2HKS2HaS2HaS1HS2G3S2G3S4PLEN2G42HDS4SPHI2G22G32G4S4SPHI2G22G32G4S4SPHI2G22G32G4S4SPHI2G22G32G4S3BOT2G42Ha1HS4SPHISSSS4PLEN2G42HDSSS4RShiS4RShiSSS4PLENS2HK2KKS2G1S2G3S3SPG2G4S4OWNZS2B12B3S4SP16SSSSS2HK2KKS2KBS3PLM4PLEN2G4SSSS2HKS4SP16S2HKS3BOT2G42B12B2".
split; [exact BR| lia]. }
    assert (HD : match own with None => plen = 0 | Some (_, D) => 0x5f6000 <= D end) by (destruct own as [[q D]|]; [destruct BOWN as (_ & X & _); exact X| exact OWNZ]).
    (* [comment removed for export] *)
    clear FR HI ROD RCS RCB SO RK GU DP. destruct AT as (AXC & CB & CF).   (* [comment removed for export] *)
    assert (PBX : True -> bytes_at asegs m (dptr own) (zbytes payload)) by (intros _; exact PB). clear PB.
    unfold AINIT_FLAG. apply implMA_from_evtF.
    (* [comment removed for export] *)
    pose proof (munch_refl [(0x5d34d4, 0x5d34d4 + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MU1 : munch _ m mx, WM1 : wmono asegs m mx, MI1 : mem_inv asegs mx, ST1 : stk asegs mx _ _ |- _ =>
      destruct (after_flag st own RNG m mx BA P (PBX I) HD MU1 WM1 MI1 ST1) as (BA1 & P1 & PB1);
      assert (AXC1 : atx_cellsA 2 APATX_CALLFN APEXIT_GUARD mx)
        by (eapply atx_cellsA_agree; [exact (magree_of_munch asegs _ _ _ MU1 WM1)| intros a Ha; cbn; unfold atx_addrA in Ha; lia| exact AXC]);
      clear MU1 WM1 BA P PBX AXC; try clear MI ST; rename BA1 into BA; rename P1 into P; rename PB1 into PB; rename AXC1 into AXC
      end end.
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP).
    eapply implMA_bind.
    { (* [comment removed for export] *)
      eapply implMA_leaves.
      eapply (FUZZ L RNG) with (lo := lo) (LB := LBT own) (D := dptr own) (payload := payload) (rstk := rstk);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P.
      - intros b Hb. destruct own as [[q D]|]; cbn [LBT] in Hb; [destruct Hb as [<-|Hb]; [exists q, D, plen; reflexivity|]|]; exact (HLBH b Hb).
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + left. exists q. rewrite PLEN. split; [left; reflexivity| lia].
        + right. split; [| reflexivity]. apply length_zero_iff_nil. unfold zlength in PLEN. lia.
      - exact PB.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr]; [destruct BOWN as ((_ & _ & _ & X) & _); exact X| reflexivity].
      - lia.
      - exact HI.
      - exact ST.
      - exact BOT.
      - pose proof LO'. lia.
      - unfold ATRUN_DEPTH; lia.
      - clear -SP16 G4. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - exact RCS.
      - exact RSlo.
      - lia.
      - exact RSceil.
      - rewrite PLEN. reflexivity.
      - exact MI.
      - exact FRM.
      - reflexivity.
      - reflexivity.
      - rewrite PLEN. reflexivity.
      - reflexivity.
      - exact HUL.
      - exact RGtop.
      - exact RGimg.
      - exact RGimsh.
      - exact RGfs.
      - exact RRS.
      - exact RK. }
    cbv beta. intros r st1 RNG1 ms1 [PO LEAF].
    apply fuzz_oneA_leaf0 in LEAF. subst r.
    destruct PO as (LE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & mF
                    & -> & RR & MI1 & FRM1 & ST1 & HPR & HSP & P1 & HI1 & SOE).
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    unfold ATRUN_RET. fix_ret.
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    pose proof RG1 as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & _).
    assert (BA1 : BASE st1 mF).
    { eapply (BASE_after_dpost (LBT own) (usp + -80) _ mF HPR HSP); [lia| lia| clear -SP16 G4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| | exact BA| exact P1| exact SOE| exact MI1| exact ST1].
      intros b Hb; destruct own as [[q D]|]; [right|]; exact Hb. }
    assert (PB1 : bytes_at asegs mF (dptr own) (zbytes payload)).
    { eapply (bytes_after_dpost (LBT own) (usp + -80) _ mF HPR HSP ltac:(lia) ltac:(lia)); [exact PB|].
      rewrite zbytes_length. unfold zlength in PLEN. destruct own as [[q D]|]; cbn [dptr LBT].
      + left. exists q, plen. split; [left; reflexivity| lia].
      + right; left. exists 0x5d34d0, 0x5d3500. split; [cbn; tauto|]. unfold AEMPTY. lia. }
    assert (AT1 : ATX 1 mF).
    { eapply (ATX_after_dpost (LBT own) (usp + -80) _ mF HPR HSP). split; [exact AXC| split; [exact CB| exact CF]]. }
    clear HPR HSP BA FR PB HI ROD RCS RCB MI ST SO RK GU DP AXC CB CF P.
    pose proof BA1 as (_ & _ & _ & _ & _ & MI & ST & _). destruct AT1 as (AXC & CB & CF).
    rename BA1 into BA. rename P1 into P.
    assert (PBX : True -> bytes_at asegs mF (dptr own) (zbytes payload)) by (intros _; exact PB1). clear PB1.
    (* [comment removed for export] *)
    apply implMA_from_evtF.
    pose proof (munch_refl [(0x5d34d4, 0x5d34d4 + 1)] mF) as MU. pose proof (wmono_refl asegs mF) as WM.
    zstep. zstep. zstep. zstep. apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MU2 : munch _ mF mx, WM2 : wmono asegs mF mx, MI2 : mem_inv asegs mx, ST2 : stk asegs mx _ _ |- _ =>
      destruct (after_flag st1 own RNG1 mF mx BA P (PBX I) HD MU2 WM2 MI2 ST2) as (BA2 & P2 & PB2);
      assert (AXC2 : atx_cellsA 2 APATX_CALLFN APEXIT_GUARD mx)
        by (eapply atx_cellsA_agree; [exact (magree_of_munch asegs _ _ _ MU2 WM2)| intros a Ha; cbn; unfold atx_addrA in Ha; lia| exact AXC]);
      clear MU2 WM2 BA P PBX AXC; try clear MI ST; rename BA2 into BA; rename P2 into P; rename PB2 into PB; rename AXC2 into AXC
      end end.
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP).
    eapply implMA_bind.
    { eapply implMA_keeps with (f := aps_mra); [| apply s_emit_aps_mra].
      unfold io_emit, ioA, io_S. cbn [a_so a_set_so AAllocAsan].
      destruct (drv_got_of_aheap AI _ _ _ _ _ P) as (_ & _ & _ & GSSP).
      eapply (EMIT RNG1 rstk) with (lo := lo) (canary := canary) (v := 0);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact SO.
      - lia.
      - apply unsigned_wz_mod32.
      - exact ST.
      - pose proof LO'. unfold AEMIT_DEPTH, AHARNESS_STACK in *. lia.
      - unfold KHIGH. lia.
      - lia.
      - split; [exact GSSP | exact GU].
      - exact MI.
      - exact FRM1.
      - exact (ASHENV _ _ _ _ _ P).
      - exact RCS.
      - exact RSlo.
      - lia.
      - exact ROD.
      - exact RCB.
      - eapply rng_sub'; [eapply rng_fp_le; [exact LE1 | exact RGstk] | lia].
      - eapply rng_fp_le; [exact LE1 | exact RGimg].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRS].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRF].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRB]. }
    cbv beta. intros [] st2 RNG2 ms2 [PO EH].
    destruct PO as (ER & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & mE & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO2 & SSP2).
    subst RNG2.
    rewrite ?(unsigned_lit (usp + -80)) in MUc, ST2 by lia.
    fix_ret.
    unfold aps_mra in EH. pose proof (f_equal snd EH) as EAT. apply (f_equal fst) in EH. pose proof (f_equal snd EH) as ERV. apply (f_equal fst) in EH. cbn [fst snd] in EH, ERV, EAT.
    assert (P2 : AHEAP AI L RNG1 (aps_m st2) (LBT own) mE).
    { rewrite EH. eapply AHEAP_after_emit; [exact P| exact MUc| exact WMc]. }
    assert (IV2 : INV0 own st2 mE).
    { destruct (BASE_after_emit st1 st2 _ mE BA MUc WMc MI2 ST2 SO2 ERV EAT) as [BA2 PBK]. split; [exact BA2|]. split.
      - apply PBK; [| exact PB]. destruct own as [[q D]|]; [| exact OWNZ]. destruct BOWN as (_ & B1 & B2). lia.
      - eapply (ATX_after_munch 0); [split; [exact AXC| split; [exact CB| exact CF]]| exact MUc| exact WMc|].
        intros a Ha. unfold atx_state_addrA, atx_addrA in Ha. cbn. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq. lia. }
    clear MUc WMc.
    (* [comment removed for export] *)
    eapply implMA_evtF; [| intros ms' H; exact (HKONT _ _ _ _ H eq_refl)].
    zstep. zstep. if_cases KB; zify_cond KB; [| exfalso; revert KB; clear; intros KB; rewrite ?unsigned_lit in KB by lia; cbn in KB; lia]. clear KB.
    zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
    - replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evtF_done. unfold RUNST. do 17 eexists. exists F2, fc2, mE.
      split; [reflexivity|]. split; [exact FRM2|]. split; [exact P2| split; [exact RG1| exact IV2]].
    - replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      apply evtF_done. unfold RUNST. do 17 eexists. exists F2, fc2, mE.
      split; [reflexivity|]. split; [exact FRM2|]. split; [exact P2| split; [exact RG1| exact IV2]].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI ASHENV FUZZ HSTRN EMIT A cap HLBH FC LC CAP L0 L6 SP16 SPG BOT CEIL SPHI LO RSlo RShi RSceil HUL HLB CI_WF"] Lemma calls_loop : forall (n : nat) own rcd RNG st ms,
    (1 <= n <= 4)%nat -> match own with None => plen = 0 | Some _ => 0 < plen end ->
    RUNST own 0x7fb18 (Z.of_nat n) RNG st ms ->
    implMA RNG (run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload rcd) st
           (fun rc' st' RNG' ms' => RUNST own 0x7fb50 0 RNG' st' ms' /\ rc' = 0) ms.
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "0060>19862919622.7220575254577.7850415204536.7851931812947.7463887492502.7765828522090.7800000400800<00@00D00HS2HNS2HNS2HNS2HNS2HNS2HN".
induction n as [|n IH]; intros own rcd RNG st ms HN OWNZ R; [lia|].
    cbn [run_calls].
    eapply (call_body own (Z.of_nat (S n)) RNG st ms (fun rc' => run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload rc'));
      [lia| exact OWNZ| exact R|].
    intros rc' RNG' st' ms' R' ->. destruct n as [|n'].
    - cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implMA_ret. apply evtF_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. split; [exact R'| reflexivity].
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      apply (IH own 0 RNG'); [lia| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Notation POST s RNG := (atarget_run_postA AI L RNG ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo canary m0).

  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI DFREE DFREEN A cap FC LC CAP L0 L6 SP16 BOT CEIL SPHI LO RSceil UF1 UF0"] Lemma run_tail : forall own RNG st ms,
    RUNST own 0x7fb50 0 RNG st ms ->
    implMA RNG ((match omodel own with Some q => afree_M q | None => mret tt end) ;;; mret (if 0 =? 0 then 0 else 1)) st
           (POST st RNG00) ms.
  Proof.
    intros own RNG st ms R.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (P & RG & (BA & PB & AT))).
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    unfold FRAME in FR. destruct FR as [j0 FR].
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind with (Q1 := fun _ st' RNG' ms' => fp_le RNG RNG' /\ exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : amem),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (wz plen) (wz (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (wz (oreg own)) x19 (wz AINIT_FLAG) (wz 0) (wz 0) (wz (-2)) s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x7fb58) fc None m' (seg_rom asegs)
        /\ AHEAP AI L RNG' (aps_m st') LB m' /\ FRAME m'
        /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -80)
        /\ stdout_file m' (aps_so st') /\ aps_ok L st' /\ rw_cells asegs m' ssp_guard [C8 canary] /\ adrv_pres AI LB usp m0 m' /\ ATX 0 m').
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      - (* [comment removed for export] *)
        eapply implMA_mono.
        { Local Ltac2 Set LiaHints.tbl := fun () => "0150?1052421149.125 1052421149.127 11472836995.1641162083375.162 13925130112.12413925130112.12617284870823.12517284870823.12717776320417.16420078028844.12520078028844.12722226183811.16424381366329.15524391499288.14524391499288.15225878270254.16326060559118.12426060559118.12626060559118.14526060559118.15127723960707.16528405174194.12428405174194.1262898439234.125 2898439234.127 30060662506.12530060662506.1273051486595.165 31481120922.12431481120922.1263166865343.125 3166865343.127 36115622447.16237745056650.12437745056650.12637745056650.14537745056650.15138242491404.12438242491404.12639364995812.14539364995812.15242200251523.16342281592088.12542281592088.12743886324944.12443886324944.12643987951393.16445653438483.12445653438483.12646509722084.12546509722084.12746887021955.16650628941955.16350692326760.12751678667182.16352076332702.16553510313876.16353767577760.16553777673155.12553777673155.1275407256304.3   5896867971.163 59504824357.15461917199009.16461994440323.16563235321903.16263259903092.12563259903092.12766768433875.15600000400800900=00>00?00@00A00E00F00G00H00L00P00T00X00g01601E01T01U01V01W01X01Y01_01e01f01o02802902:02>02?02@02A02B02C02D02E02F02G02H02I02J02K02O02]02k02l02m02n02o03003403503603:03;03<03B03C03D03H03I03M03Z03g03hS2G3S2G3SS2G3SSFFS2G3FFSS2G3S2G3S2G3S2G3S4SPHI2G22G32G4S4SPHI2G22G32G4S4SPHI2G22G32G4S4SPHI2G22G32G4SSSFFS4SPHIS4SPHISS3PL03PLMS3PL03PLMFFS2G3SSSSSSSSSFFSSS2G3S3PLM2G22G32G4S3PLM2G22G32G4FFSSFS2G3FSS2G3FFS4SP16SSS2G3SS2G3S2G22G32G42G5S2G22G32G42G5S".
eapply (dfree_M AI DFREE L RNG) with (lo := lo) (p := q) (A := D) (n := plen); try reflexivity;
            rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | left; reflexivity | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia
                  | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ]. all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros [] st' RNG' ms' [SOE PO].
        destruct PO as (LE & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia.
        fix_ret. cbn [aps_m aset_m fst] in HEAP3.
        pose proof (AI_hb_ids AI _ _ _ _ _ P) as ND.
        rewrite (lb_remove_headA q D plen LB ND) in HPR3, HEAP3.
        destruct (BASE_after_dpost LB (usp + -80) m m3 HPR3 HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)
                    ltac:(intros b Hb; exact Hb) st st' _ _ BA HEAP3 SOE MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & DP3).
        pose proof (ATX_after_dpost LB (usp + -80) m m3 HPR3 HSP3 0 AT) as AT3.
        split; [exact LE|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3| exact AT3].
      - (* [comment removed for export] *)
        apply implMA_ret.
        eapply evtF_mono.
        { eapply (DFREEN L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
          all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia. fix_ret.
        destruct (BASE_after_dpost LB (usp + -80) m m3 HPR3 HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)
                    ltac:(intros b Hb; exact Hb) st st _ _ BA HEAP3 eq_refl MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & DP3).
        pose proof (ATX_after_dpost LB (usp + -80) m m3 HPR3 HSP3 0 AT) as AT3.
        split; [apply fp_le_refl|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3| exact AT3]. }
    cbv beta. intros [] st' RNG' ms' (LE & x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & P' & [j0' FR'] & MI' & ST' & SO' & RK' & GU' & DP' & AT').
    apply implMA_ret. cbn [Z.eqb].
    pose proof (RNGS_mono _ _ LE RG) as (RGstk' & _).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep.
    apply evtF_done. unfold atarget_run_postA. split; [eapply fp_le_trans; [exact LE00| exact LE]|].
    destruct (drv_got_of_aheap AI _ _ _ _ _ P') as (_ & _ & _ & GSSP').
    do 14 eexists. exists F, fc, m'.
    split; [reflexivity|].
    split; [lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact DP'|]. split; [exact P'|]. split; [exact SO'|]. split; [split; [exact GSSP'| exact GU']|]. split; [exact (ATX_state _ AT')| exact RK'].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
    implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof. intros X Y RNG a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition PRE1 (RNG : footprint) (s : APS) (m : amem) : Prop :=
    AHEAP AI L RNG (aps_m s) LB m /\ RNGS RNG /\ BASE s m /\ bytes_at asegs m A (zbytes content) /\ ATX 0 m.

  (* [comment removed for export] *)
  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 AINIT_FLAG) (Z_to_bv 64 calls) x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI DFREE DFREEN ASHENV FUZZ HSTRN EMIT cap HLBH FC LC CAP L0 L6 SP16 SPG BOT CEIL SPHI LO RSlo RShi RSceil HUL UF1 UF0 HLB CI_WF"] Lemma trun_empty : forall RNG s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen = 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x7fb08 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & RG & BA & CT & AT).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold runA, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMA_retb. cbv beta iota.
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { Local Ltac2 Set LiaHints.tbl := fun () => "0040?13159645056.10337491283015.10351319906316.10352041488522.10400000700@00G00HS5CALLSS2PZ4PLENS5CALLSS".
eapply (calls_loop (Z.to_nat calls) None 0 RNG); [lia| exact PZ|].
      unfold RUNST. do 17 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AEMPTY, AINIT_FLAG; reflexivity|].
      split; [exact FRM|]. split; [exact P|]. split; [exact RG|]. split; [exact BA|].
      assert (PE : payload = []). { apply length_zero_iff_nil. unfold zlength in PLEN. lia. }
      split; [| exact AT]. cbn [dptr]. rewrite PE. cbn [zbytes map]. apply bytes_at_nil. unfold AEMPTY. lia. }
    cbv beta. intros rcd st' RNG' ms' [R ->]. apply (run_tail None RNG' st' ms' R).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma implMA_bind_assoc : forall {X Y W} RNG (ma : @Monad.M APS X) (g : X -> @Monad.M APS Y) (f : Y -> @Monad.M APS W) s Q ms,
    implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
  Proof.
    intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN EMIT p cap INLB HLBH FC LC CAP L0 L6 SP16 SPG BOT CEIL SPHI LO RSlo RShi RSceil HUL UM1 UF1 UM0 UF0 HLB CI_WF"] Lemma trun_copy : forall RNG s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen <> 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x7fabc x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & RG & BA & CT & AT). pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    pose proof LC as LC'. pose proof L6 as L6'. unfold zlength in LC', L6'.
    (* [comment removed for export] *)
    pose proof (AI_block AI _ _ _ _ _ p A cap P INLB) as (_ & BR & RGA & RGAS & SHA & WRA & _ & (RLO & RHI & AR1 & AR2 & AR3 & AR4 & ARR & ARW)).
    pose proof BR as (BQ1 & BQ2 & BQ3 & BQ4). pose proof (ablk_lin _ _ BQ1) as (BK1 & BK2 & BK3 & BK4). unfold AIMG_HI in BK1.
    unfold runA, Adapter.target_run. rewrite !PLEN.
    replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMA_bind_assoc.
    unfold FRAME in FR. destruct FR as [j0 FR].
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { Local Ltac2 Set LiaHints.tbl := fun () => "01]0?1052421149.154 10702667736.2621086139525.275 12089496813.26212417306270.27513159645056.2751356114379.248 14896448070.26217282764447.15317284870823.1541856331289.262 18676726967.24718676726967.26218817724203.26219392565223.26219826135528.15320078028844.15420080120852.15321703889302.26221703889302.27921706042413.2112190477615.279 23541492202.21023739346196.26224391499288.20424938099585.24725069483565.27525199480016.23126058469174.26226060559118.15326060559118.17927437868152.23927499548284.26228122014079.2792896334970.153 2898439234.154 30060662506.15430655001221.27531481120922.15331481120922.26231481120922.2793164781447.153 3166865343.154 32453922879.26232635148377.24736744590918.26237128782981.27537984878850.20938242491404.15338892314885.27539364995812.20440629668746.27542146777215.26242281592088.15442283686176.1534279910078.262 43185561405.15343191853829.1544347719212.262 43886324944.15344568168577.26245126598772.24745278383857.23145653438483.15346509722084.15446511830492.15347433088064.15347957594509.2475024380283.262 50977087596.26251319906316.23151319906316.23951319906316.24851319906316.25551319906316.25751319906316.27551584415733.2395254653706.153 5254653706.179 53480278889.15453539688044.26254070069915.2625407256304.3   55057437376.8  55094045701.27556174447011.26256680472399.26257355610261.26257622410744.13 57622410744.14 57622410744.27857989657891.27658475011077.27559314873579.21260961191897.24861106136840.27561648889340.23162779541538.24863179633374.24763259903092.154647906794.211  66391162455.2396695008502.262 68345062898.15368477460283.15368483752707.1548081431589.262 8174601171.279 8556059955.262 00000800M00h01=01>02F02[03b03c03d04505:06?06W07Y07i07j07k08W09C09]09n0:Q0:f0;20;G0<V0=K0=l0>?0>R0>c0?80?I0?J0?K0?U0@00@=0AD0A]0A^0A_0B40BI0C`0D;0DZ0D_0E:0EC0ET0Eh0Ei0Ej0Fb0Fc0Fd0G^0Gc0Hi0JC0K80KJ0KK0KL0KQ0LV0MC0M[0Mh0N90NN0Nc0O80OV0Og0Ol0P10P20PC0PW0P]0Pc0Q>0QO0Qd0S?0SR0Sb0U:0UQ0Ul0V<0VQ0VR0WK0Xe0Y:0Y[0Yd0Z50ZJ0ZO0ZP0ZQ0Ze0\<0]AS2G33BK2S3BK23BL23Ha23Ha53Hb5S2G22G33BK23BL13BL23Ha53Hb5S3PL03BK23BL23Ha53Hb5FS2L05CALLS4EPAY2G45PLEN'3AR43BQ23BK13BK23BL13BL23Aa43Ab43Ha23Ha53Hb23Hb5S3BK23BL13BL23Ha53Hb5S2LC3BOT2G22G32G45PLEN'3AR43BK23BK33BL13BL23EPP3Aa43Ab43Ha23Ha53Hb23Hb5FFS3BK23BL23Ha53Hb5S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab43Ha23Ha53Hb23Hb5S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab43Ha23Ha53Hb23Hb5S2G43BK23BL23Ha33Ha53Hb5S2L04EPAY2G45PLEN'3AR43BQ23BK13BK23BL13BL23Aa43Ab43Ha23Ha53Hb23Hb5S2PZ3PL03PLM3BK2FFS2G45PLEN'3BK23BL13BL23BL33Ab43Ha53Hb23Hb51HS2G45PLEN'3BK23BL13BL23BL33Ab43Ha53Hb23Hb51HS2G45PLEN'3BK23BL13BL23BL3S3BK23BL23Ha53Hb5S2L02G43LC'3L6'3AR43BQ23BK13BK23BL2S3BK23BL23Ha13Ha53Hb5S2G33BK23BL2S3CTB3BK23BL23Ha53Hb5S2LC2L03BOT4EPAY2G22G32G45PLEN'3AR43BK13BK23BL23BL33EPP3Aa43Ab43Ha23Ha53Hb23Hb5S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab4S4SPHI2G22G32G43BK23BL23Ha53Hb51HS4SPHI2G22G32G43BK2S4SPHI2G22G32G43BK2S3BK23BL23Ab33Ha5S3BK23BL23Ha53Hb13Hb5S3BK23BL23Ha53Hb5FFS4SPHI3BK2S2G22G33BK23BL13BL23Ha53Hb5S3PL03PLM3BK2S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BK33BL23EPP3Aa43Ha23Ha53Hb51H3PL03PLMS3PL03PLM3BK23BL23Ha53Hb5FFS3PLM3BK23BL23Ha53Hb5S3BK23BK43BL23Ha53Hb5S2LC2L03BOT4EPAY2G45PLEN'3LC'3L6'3AR43BQ23BK13BK23BL23BL33EPP3Aa43Ab43Ha23Ha53Hb23Hb51HS2G22G33BK23BL13BL23Ha53Hb5S2G43LC'3AR43BQ23BK13BK23BL22HaS3BK2S2G22G33BK23BL13BL23Ha53Hb5S3BK23BL2S3BK23BL23Ha53Hb5S2G13BK23BL23Ha53Hb5FFS2L04EPAY2G45PLEN'3BK13BK23BL23BL33Ha23Ha53Hb53Hb63Pb61HFFS2L04EPAY2G45PLEN'3AR43BQ23BK13BK23BL23Aa43Ha23Ha43Ha53Hb5S3BK2S2L04EPAY2G45PLEN'3AR43BQ23BK13BK23BL13BL23Aa43Ab43Ha23Ha53Hb23Hb43Hb5S2L04EPAY2G45PLEN'3AR23AR43BQ23BQ43BK13BK23BL13BL23Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab4S3PLM2G22G32G43BK2FFS3BK2S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab43Ha23Ha53Hb23Hb5S2LC2G43AR43BK23BK33BL23EPP3Ha53Ha63Hb53Pa61HS2G43BK23BL23Ha53Hb33Hb5S3PL03BK23BL2S3PL03BK23BL23Ha5S3PL03BK23BL23Ha53Hb5S3PL03BK23BL23Ha53Hb5S3PL03BK23BL23Ha53Hb5S2PZ3PL03BK23BL23Ha53Hb55CALLSS3BK23BL23Ab43Ha5S3BK2S3BK2FS3BK23BL23Ha53Hb5S2L03BK23BL23Ha53Hb5S4SP16S4BN1'S2G22G33BK23BL13BL23Ha53Hb5S3BK23BL23Ha53Hb5S3PL03BK23BL23Ha53Hb5S2LC2L02PZ3PL04EPAY2G43AR23AR43BK23BL13BL24DISJ3EPP3Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S4CEIL2G32Ha4BN1'1HS4CEIL2G31R1D2B3S2LC2L03BOT4EPAY2G22G32G43LC'3L6'3AR43BQ23BK13BK23BL23BL33EPP3Aa43Ab43Ha23Ha53Hb23Hb52HaS2G22G33BK23BL23Ha53Hb5S2G22G33BK23BL13BL23Ha53Hb5S3BK23BL13BL22K1S3BK23BL23BL43Ha53Hb5FS2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa33Aa43Ab4S2L04EPAY2G45PLEN'3AR23AR43BQ23BK13BK23BN43BL13BL23Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S3BQ23BK23BL23Ha53Hb5S2G22G32G42G53LC'3AR23AR43BK13BK2S3BK23BL2S3BK23BL13BL23Ha5S3BK23BL23Ha53Hb23Hb5S3BK2FFS2G33BK23BL23Ha53Hb5S2L03BOT4SPHI4EPAY2G22G32G45PLEN'3AR43BQ23BK13BK23BL13BL23Aa43Ab43Ha23Ha53Hb23Hb52Y12Y4S2LC2L04EPAY2G45PLEN'3AR43BK13BK23BL13BL23EPP3Aa43Ab43Ha23Ha53Hb23Hb5".
eapply (dmalloc_M AI DMALLOC L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact MI | exact ST | exact BOT | unfold AMALLOC_STACK; pose proof LO'; lia | unfold AREQMAX; lia
              | exact UM1 | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
    cbv beta. intros r s1' RNG1 ms1 [SOE PO].
    destruct PO as (LE1 & u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & HPR & HSP & RR).
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in RR.
    assert (AT1 : ATX 0 m1) by (eapply (ATX_after_dpost LB (usp + -80) m m1 HPR HSP); exact AT).
    destruct r as [nb|]; [| destruct RR].
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & RGN & RGNS & _).
    pose proof BR' as (BN1 & BN2 & BN3 & BN4). pose proof (ablk_lin _ _ BN1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    pose proof RG1 as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & RGfs1 & RRS1 & RRF1 & RRB1 & LE01).
    (* [comment removed for export] *)
    pose proof (magree_of_dpost _ _ _ _ _ HPR HSP) as AG1.
    assert (BA1 : BASE s1' m1).
    { eapply (BASE_after_dpost LB (usp + -80) m m1 HPR HSP); [lia| lia| clear -SP16 G4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| intros b Hb; exact Hb| exact BA| exact HEAP1| exact SOE| exact MI1| exact ST1]. }
    pose proof BA1 as (FR1 & _). unfold FRAME in FR1. destruct FR1 as [j1 FR1].
    assert (CT1 : bytes_at asegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG1| exact CT|]. intros a Ha. left. right; right; left. exists (HB p A cap). split; [exact INLB|]. cbn. rewrite zbytes_length in Ha. lia. }
    pose proof (AI_hb_ids AI _ _ _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) (HB p A cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [ab_addr ab_size] in D. apply D. intros E. injection E. intros _ _ Eid.
      unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite Eid.
      apply in_flat_map. exists (HB p A cap). split; [exact INLB| left; reflexivity]. }
    (* [comment removed for export] *)
    assert (PB : bytes_at asegs m1 PAY (zbytes payload)).
    { rewrite <- (firstn_skipn (Z.to_nat (6 + Lc)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
      rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + Lc)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
    apply implMA_retb. cbv beta iota.
    apply implMA_from_evtF.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; atop_facts; lia|]. clear K1.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    assert (EPP : PAY + plen = A + zlength content) by (unfold PAY, plen; lia).
    pose proof (AI_block AI _ _ _ _ _ p A cap HEAP1 ltac:(right; exact INLB)) as (_ & _ & RGA1 & _ & SHA1 & _ & _ & (RLOa & RHIa & Aa1 & Aa2 & Aa3 & Aa4 & ARRa & ARWa)).
    pose proof (AI_block AI _ _ _ _ _ nb A' plen HEAP1 ltac:(left; reflexivity)) as (_ & _ & _ & _ & SHN1 & _ & _ & (RLOb & RHIb & Ab1 & Ab2 & Ab3 & Ab4 & ARRb & ARWb)).
    pose proof (block_hull RNG1 m1 PAY plen RLOa RHIa ltac:(lia) Aa1 Aa2 ltac:(lia) ltac:(lia) ltac:(lia) ARRa ARWa) as (HRa & HWa & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6).
    pose proof (block_hull RNG1 m1 A' plen RLOb RHIb ltac:(lia) Ab1 Ab2 ltac:(lia) ltac:(lia) ltac:(lia) ARRb ARWb) as (HRb & HWb & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
    assert (UPa : unpoisoned m1 PAY (PAY + plen)).
    { eapply unpoisoned_sub; [apply (ablock_unpoisoned m1 A cap SHA1); first [lia | clear -BQ4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | lia | lia]. }
    assert (UPb : unpoisoned m1 A' (A' + plen)).
    { apply (ablock_unpoisoned m1 A' plen SHN1); first [lia | clear -BN4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. }
    pose proof (AI_rtcells AI _ _ _ _ _ HEAP1) as (_ & Rgot & Rric & Rmem & Rshb & _ & Rini & Rlay & _).
    pose proof (hull_props PAY plen ltac:(lia)) as (_ & _ & _ & _ & Pa5 & Pa6). pose proof (hull_props A' plen ltac:(lia)) as (_ & _ & _ & _ & Pb5 & Pb6).
    name_sp sp (-80)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evtF_cut; [eapply (memcpy_i_spec RNG1) with (RLO1 := hull_lo PAY) (RHI1 := hull_hi PAY plen) (RLO2 := hull_lo A') (RHI2 := hull_hi A' plen) | ] end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- _ => rewrite ?Hsp, ?unsigned_lit by lia
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- mem_inv _ _ => exact MI1
         | |- stk _ _ _ _ => exact ST1
         | |- bytes_at _ _ _ _ => exact PB
         | |- rw_cells _ _ _ [CB _ _] => exact NBLK
         | |- rw_cells _ _ _ _ => assumption
         | |- length _ = _ => rewrite zbytes_length; lia
         | |- app_blk _ _ => first [ eapply ablk_app_blk; [exact BN1| lia] | eapply ablk_app_blk; [eapply ablk_sub; [exact BQ1| unfold PAY; lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND in *; lia ]
         | |- unpoisoned _ _ _ => assumption
         | |- wr_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => assumption
         | |- rng _ lo _ => eapply rng_sub'; [exact RGstk1| lia]
         | |- rng _ PAY _ => eapply rng_sub'; [exact RGA1| lia]
         | |- rng _ _ _ => assumption
         | |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
         | |- _ => unfold KHIGH in *; lia
         end.
    cbv beta. intros ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & ST2 & NB2 & _).
    rewrite ?Hsp in MUc. rewrite ?Hsp in ST2. unname_sp.
    rewrite !(unsigned_lit A') in MUc, NB2 by lia. rewrite !(unsigned_lit plen) in MUc, NB2 by lia.
    replace (bv_unsigned sp + -80 - 2240) with (bv_unsigned sp + -2320) in MUc by lia.
    clear PB CT1 NBLK.   (* [comment removed for export] *)
    transport_after_call asegs m1 m2 MUc WMc.
    fix_ret.
    assert (P2 : AHEAP AI L RNG1 (aps_m s1') (HB nb A' plen :: LB) m2).
    { eapply (AI_frame AI); [exact HEAP1| exact MUc| exact WMc|].
      pose proof (AI_layout AI _ _ _ _ _ HEAP1) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - right; left. exists (HB nb A' plen). split; [left; reflexivity| cbn; lia]. }
    assert (IV2 : INV0 (Some (nb, A')) s1' m2).
    { split.
      - eapply (BASE_after_munch s1' _ m1 m2 BA1 MUc WMc); [| | | | exact MI2| exact ST2].
        + unfold appW. constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'; unfold KLOW, KHIGH, KEND; first [clear - BN1' BN2 BN3; lia| lia]| constructor].   (* [comment removed for export] *)
        + intros a Ha. cbn. pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'. first [clear - Ha BN1' BN3 CEIL G3; atop_facts; lia| lia].   (* [comment removed for export] *)
        + intros a Ha. cbn. lia.
        + intros b a Hb R. cbn.
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as D.
          cbn [ab_addr ab_size] in D. destruct (HLB b Hb) as (B1 & B2 & B3). atop_facts.
          assert (NE : HB nb A' plen <> b).
          { intros E. unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
            subst b. apply in_flat_map. exists (HB nb A' plen). split; [exact Hb| left; reflexivity]. }
          specialize (D NE). first [clear - D R B3 CEIL G3; lia| lia].   (* [comment removed for export] *)
      - split; [cbn [dptr]; apply (rw_cells_bytes_at asegs) in NB2; cbn [cells_bytes cbytes app] in NB2; rewrite app_nil_r in NB2; exact NB2|].
        eapply (ATX_after_munch 0); [exact AT1| exact MUc| exact WMc|].
        intros a Ha. unfold atx_state_addrA, atx_addrA in Ha. cbn. pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'. first [clear - Ha BN1' BN3 CEIL G3; atop_facts; lia| lia]. }
    clear MUc WMc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0 RNG1); [lia| cbn; lia|].
      unfold RUNST. do 17 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AINIT_FLAG; reflexivity|].
      split; [exact FRM|]. split; [exact P2| split; [exact RG1| exact IV2]]. }
    cbv beta. intros rcd st' RNG' ms'' [R ->]. apply (run_tail (Some (nb, A')) RNG' st' ms'' R).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="rng_fs_mono DRV_CI CLI_CI DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN EMIT p cap INLB HLBH FC LC CAP L0 L6 SP16 SPG BOT CEIL SPHI LO RSlo RShi RSceil HUL UM1 UF1 UM0 UF0 HLB CI_WF"] Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : APS)
      (cdt thr sec : byte) (tm1 : word),
    AHEAP AI L RNG00 (aps_m s) LB m0 -> bytes_at asegs m0 A (zbytes content) -> atrun_cells0 m0 -> harness_invA m0 ->
    rw_cells asegs m0 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    stk asegs m0 lo usp -> mem_inv asegs m0 -> frm0 fc ->
    stdout_file m0 (aps_so s) -> ssp_cells m0 canary -> aps_ok L s ->
    rclean m0 rstk -> rodata_sh0 m0 -> rclean m0 RBstdout ->
    tp = tpv -> a0 = wz (A + 2) -> a1 = wz Lc -> a2 = wz PAY -> a3 = wz plen ->
    rng RNG00 lo (usp + 128 - lo) -> rng RNG00 lo (al_top L - lo) -> rng_aimg RNG00 -> rng_aimg_sh RNG00 -> rng_fs L RNG00 ->
    rrng RNG00 rstk -> rrng RNG00 RFMT -> rrng RNG00 RBstdout ->
    implMA RNG00 (runA AAllocAsan cfg payload) s (POST s RNG00)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATARGET_RUN) fc None m0 (seg_rom asegs)).
  Proof.
    intros until tm1. intros P0 CT TR0 HI0 LIBC ST0 MI0 FRM SO0 [GS0 GU0] RK RCS0 ROD0 RCB0 -> -> -> -> -> RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    pose proof LC as LC'. pose proof L6 as L6'. unfold zlength in LC', L6'.
    destruct (HLB _ INLB) as (BA1 & BA2 & BA3). cbn [ab_addr ab_size] in BA1, BA2, BA3.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0) as (_ & _ & GFI0 & _).
    apply implMA_from_evtF.
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact LIBC| exact GFI0| exact RGstk| exact RGimg|].
    intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 MU WM MI1 IF1 AT1.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    (* [comment removed for export] *)
    assert (OUT : forall a, (a < usp - 128 /\ ~ (AINIT_FLAG <= a < AINIT_FLAG + 1) /\ ~ (0x5f3e68 <= a < 0x5f3e6c) /\ ~ (0x5f3e88 <= a < 0x5f3e90) /\ ~ (0x5f3f88 <= a < 0x5f3f90)) \/ usp <= a ->
                            outside [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)] a).
    { intros a Ha. unfold AINIT_FLAG in *. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00U0?11042984095.14911790953086.14919258179774.15424482262554.1422518373760.142 25367824318.15426884133434.14929443231903.14929445647707.15129802130565.15431474779266.13931474779266.14233372620191.14135565800962.14035565800962.14337055971834.14037055971834.14337790137268.15640461571878.15640461571878.16340463674013.16041422282358.14144784519775.149473453246.154  52618128998.15757246334142.15459314873579.13960545783528.14262774748154.1377307630540.153 7307630540.154 7307630540.161 7313919932.155 7313927156.159 7451759070.142 8800126135.150 9362582369.138 00000100800900>00A00B00C00D00S00l01501>01E01M01[01c01k02702?02M02X02Y02Z02[02^02_02n03503F03`03m04@04N04_04b04o053SS2G22G3SS3C2RS1HSSSS2L02G43LC'3L6'S3BOT4SPHI2G22G32G42Y12Y4S3PL03PLMS3PL03PLMS2L02KLS3PL02KPS2L03PL02KL2KPS3PL02KPS3PL02KPS2G22G32Hx1RS2G41X1HS2G41R2B12B31HS2G41R1H2H0SSSS1XSS2L02G43L6'3EC2S2G42ECS2LC3CAP2L02L62G4S3BOT2G32G43LC'3BA13BA32HaS2G22G32G42HaS3BOT2G32G41R2B12B3S3BOT2G32Hs2HxS2G22G32G41R2Hx1HS1HS2G22G32G42HaS2KL".
lia. }
    assert (AW : appW [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x5f3e68, 0x5f3e6c); (0x5f3e88, 0x5f3e90); (0x5f3f88, 0x5f3f90)]).
    { unfold appW, AINIT_FLAG. repeat (constructor; [cbn; unfold KLOW, KHIGH; lia|]). constructor. }
    assert (P1 : AHEAP AI L RNG00 (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact P0| exact MU| exact WM|].
      pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (0x5d34d0, 0x5d3500). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; unfold AINIT_FLAG; lia].
      - left. right; left. exists (0x5f3e60, 0x5f3e90). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia].
      - left. right; left. exists (0x5f3e60, 0x5f3e90). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia].
      - left. right; left. exists (0x5f3f80, 0x5f3f90). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia]. }
    assert (CT1 : bytes_at asegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. unfold AINIT_FLAG in *. lia. }
    assert (BA : BASE s m1).
    { split; [exact FR|]. split.
      { eapply harness_invA_frame; [exact HI0| exact MU| exact WM| exact AW]. }
      split; [eapply rodata_sh0_frame; [exact ROD0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB0| exact MU| exact WM| exact AW]|].
      split; [exact MI1|]. split; [exact ST1|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO0]. intros a Ha. apply OUT. left. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq in Ha. unfold AINIT_FLAG. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU0|]. intros a Ha. apply OUT. left. unfold ssp_guard, AINIT_FLAG in *. cbn in Ha. lia. }
      intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT. unfold atrun_ivs in Hx. cbn [rin_ivs] in Hx. unfold AINIT_FLAG in *.
      destruct Hc as [Hc|Hs].
      - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
        + right. pose proof geo. lia.
        + left. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
        + left. pose proof (HLB _ Hb) as (B1 & B2 & B3). atop_facts. lia.
        + left. rewrite shad_div. unfold ASHOFF.
          assert (R : 0 <= a' < 2^47).
          { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
            - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). unfold AIMG_HI in *. lia.
            - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. atop_facts. lia. }
          rewrite shad_div in Ha, Hx. unfold ASHOFF in Ha, Hx. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      - left. rewrite !shad_div in Hs. unfold ASHOFF in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (PRE : PRE1 RNG00 s m1).
    { split; [exact P1|]. split; [| split; [exact BA| split; [exact CT1| exact AT1]]].
      unfold RNGS, rrng in *. repeat match goal with |- _ /\ _ => split end; first [assumption | apply fp_le_refl]. }
    pose proof (AI_block AI _ _ _ _ _ p A cap P1 INLB) as (_ & _ & RGA & _).
    clear AG OUT MU WM CT SO0 P0 ST0 MI0 TR0 HI0 RCS0 ROD0 RCB0 GS0 GU0 GFI0 LIBC.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? Lc) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zstep. zstep. if_cases KP; zify_cond KP.
      + apply evtF_done. rewrite <- EC.
        eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evtF_done. rewrite <- EC.
        eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
    - (* [comment removed for export] *)
      destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
      pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
      pose proof (u8ro_read asegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1
                    ltac:(unfold zbytes; rewrite nth_error_map; change (Z.to_nat 2) with 2%nat; rewrite EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      zstep. zstep.
      assert (EC : calls = Z.land c2 3 + 1).
      { unfold calls, cfg. replace (0 <? Lc) with true by (symmetry; apply Z.ltb_lt; lia). unfold znth.
        destruct (Z.ltb_spec 2 0); [lia|]. change (Z.to_nat 2) with 2%nat. rewrite (nth_error_nth _ _ _ EC2). lia. }
      replace (bv_unsigned (Z_to_bv 8 c2)) with c2
        by (rewrite Z_to_bv_unsigned; unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus; cbn; lia).
      replace (Z.land c2 3 + 1) with calls by lia.
      zstep. if_cases KP; zify_cond KP.
      + apply evtF_done. eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evtF_done. eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem atarget_run_proofA (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop) :
  (forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
  (forall iv, In iv drv_img_ranges -> In iv (aci AI)) -> (forall iv, In iv cli_img_ranges -> In iv (aci AI)) ->
  (forall iv, In iv (aci AI) -> 0 <= fst iv) ->
  dmalloc_stmt AI -> dfree_stmt AI -> dfree_null_stmt AI -> ashenv_law AI ->
  fuzz_oneA_stmt AI rng_fs -> strnlen_a_stmt ->
  atarget_run_stmtA AI rng_fs.
Proof.
  intros MONO DRV_CI CLI_CI CI_WF DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN.
  intros L RNG rstk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap Lc content lo canary.
  intros P0 INLB HLBH CT FC LC CAP L0 L6 TR0 HI0 (cdt & thr & sec & tm1 & LIBC) ST0 BOT LO SPG SP16 SPHI MI0 FRM SO0 SSP RK RCS RSlo RShi RSceil ROD RCB -> -> -> -> -> HUL UM1 UF1 UM0 UF0
         RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
  pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "0010?17986879152.105000005S3BOT".
eapply (trun_main AI rng_fs MONO DRV_CI CLI_CI DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN L RNG rstk ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            m LB p A cap Lc content lo canary INLB HLBH FC LC CAP L0 L6 SP16 SPG BOT ltac:(lia) SPHI LO RSlo RShi RSceil HUL UM1 UF1 UM0 UF0
            (fun b Hb => AI_block_bounds AI _ _ _ _ _ b P0 Hb) CI_WF);
    first [ exact P0 | exact CT | exact TR0 | exact HI0 | exact LIBC | exact ST0 | exact MI0 | exact FRM | exact SO0 | exact SSP | exact RK
          | exact RCS | exact ROD | exact RCB | exact RGstk | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
          | exact RRS | exact RRF | exact RRB | reflexivity ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
