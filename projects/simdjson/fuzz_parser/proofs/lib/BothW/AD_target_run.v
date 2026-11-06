(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Keeps F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface F_syscalls StdioFiles Stdio_kit MonadF Strnlen_iface F_printf_iface I_memcpy ADriver_iface AD_kit AD_emit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AAtexit_iface AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Keyed Unification.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
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
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
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
Definition trun_hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (trun_hidden T) in H end.
Local Ltac unhide H := unfold trun_hidden in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition aps_mrac (s : APS) := (aps_mra s, aps_cl s).
Lemma s_emit_aps_mrac : forall v, keeps aps_mrac (s_emit aps_so aset_so v).
Proof. intros v. apply a_s_emit_k. intros; reflexivity. Qed.

(* [comment removed for export] *)
Definition cstat_addr (a : Z) : Prop :=
  (0x64dd80 <= a < 0x64dd88) \/ (0x64dda0 <= a < 0x64dda2) \/ (0x64de20 <= a < 0x64de4c) \/ (0x64de80 <= a < 0x64de82).
(* [comment removed for export] *)
Lemma client_static_agree : forall (P : Z -> Prop) s LB m m', magree bsegs P m m' -> (forall a, cstat_addr a -> P a) ->
  (forall p V a, aps_cl s = Some p -> In (HB p V 8) LB -> V <= a < V + 8 -> P a) -> client_static s LB m -> client_static s LB m'.
Proof.
  intros P s LB m m' AG HP _ [CL CS]. split; [exact CL|].
  unfold client_static0, client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard0, guard1 in *.
  destruct CS as [CS|CS]; [left| right]; decompose [and] CS; repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; cbn in Ha; apply HP; unfold cstat_addr; lia]).
Qed.
(* [comment removed for export] *)
Lemma client_static_cl : forall s s' LB m, aps_cl s' = aps_cl s -> client_static s LB m -> client_static s' LB m.
Proof. intros s s' LB m E [CL CS]. split; [rewrite E; exact CL| exact CS]. Qed.
Lemma client_static_lb : forall s LB LB' m, (forall p V, aps_cl s = Some p -> In (HB p V 8) LB -> In (HB p V 8) LB') -> client_static s LB m -> client_static s LB' m.
Proof. intros s LB LB' m _ H. exact H. Qed.
(* [comment removed for export] *)
Lemma magree_of_hpost : forall CI LB SP m m',
  harness_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> magree bsegs (fun a => dcli CI LB SP a /\ outside client_wr a) m m'.
Proof.
  intros CI LB SP m m' HP HS a Ha [[Hc | Hs] Ho].
  - apply HP; [exact Ha| split; assumption].
  - pose proof (HS a Hs) as E. split; [exact E|]. unfold wview, mrd. rewrite E. auto.
Qed.
Ltac ocw := unfold client_wr; cbn [outside fst snd]; lia.

(* [comment removed for export] *)
Lemma wr_at_join_dk : forall m A n k, wr_at bsegs m A n -> wr_at bsegs m (A + n) k -> 0 <= n -> 0 <= k -> wr_at bsegs m A (n + k).
Proof.
  intros m A n k (H0 & H1 & H) (K0 & K1 & K) Hn Hk. split; [exact H0|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_dec i n) as [L|L]; [apply H; lia|]. replace (A + i) with (A + n + (i - n)) by lia. apply K. lia.
Qed.
Lemma wr_at_sub_dk : forall m A n n', wr_at bsegs m A n -> 0 <= n' <= n -> wr_at bsegs m A n'.
Proof. intros m A n n' (H0 & H1 & H) Hn. split; [exact H0|]. split; [lia|]. intros i Hi. apply H. lia. Qed.
Lemma wr_at_adrv_dk : forall AI LB SP m m' n, adrv_pres AI LB SP m m' -> wr_at bsegs m SP n -> SP + n <= 2^47 ->
  (forall a, SP <= a < SP + n -> ~ rin_ivs atrun_ivs a) -> wr_at bsegs m' SP n.
Proof.
  intros AI LB SP m m' n HP (H0 & H1 & H) HT HV. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (HP (SP + i) ltac:(lia) ltac:(left; left; lia) (HV (SP + i) ltac:(lia))) as [_ Wv]. apply Wv. apply H. exact Hi.
Qed.

Section RUN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  (* [comment removed for export] *)
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv CI.
  (* [comment removed for export] *)
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis AHFRESH : forall L RNG st LB m, AHEAP AI L RNG st LB m -> AFRESH st.   (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_oneU_stmt AI rng_fs.   (* [comment removed for export] *)
  Hypothesis HSTRN : strnlen_a_stmt.
  Let EMIT : emit_printf_stmtA := emit_printf_proofA HSTRN.

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG00 : footprint) (rstk : region) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
            (LB : list ablock) (p : AsanCtrl.aptr) (A cap Lc : Z) (content : list Z) (lo : Z) (canary : word)
            (cl0 : option AsanCtrl.aptr).   (* [comment removed for export] *)
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
  Hypothesis UM1 : In [AMALLOC_PC; 0x95494] (al_U L).
  Hypothesis UF1 : In [AFREE_PC; 0x95528] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Hypothesis HLB : forall b, In b LB -> 0x671000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis CL0LB : forall p0, cl0 = Some p0 -> exists V0, In (HB p0 V0 8) LB.   (* [comment removed for export] *)
  Hypothesis WRT0 : wr_at bsegs m0 (bv_unsigned sp) (al_top L - bv_unsigned sp).   (* [comment removed for export] *)

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
    exists j0 : list byte, rw_cells bsegs m (usp + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition RNGS (RNG : footprint) : Prop :=
    rng RNG lo (usp + 128 - lo) /\ rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG
    /\ rrng RNG rstk /\ rrng RNG RFMT /\ rrng RNG RBstdout /\ fp_le RNG00 RNG.

  Lemma RNGS_mono : forall R R', fp_le R R' -> RNGS R -> RNGS R'.
  Proof using rng_fs_mono.
    intros R R' LE (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold RNGS, rrng in *.
    repeat match goal with |- _ /\ _ => split end; try (eapply rng_fp_le; [exact LE|]; assumption).
    - eapply rng_fs_mono; eauto.
    - eapply fp_le_trans; eauto.
  Qed.

  (* [comment removed for export] *)
  Definition BASEc (c : Z) (st : APS) (m : amem) : Prop :=
    FRAME m /\ harness_invA m
    /\ rodata_sh0 m /\ rclean m rstk /\ rclean m RBstdout
    /\ mem_inv bsegs m /\ stk bsegs m lo (usp + -80)
    /\ stdout_file m (aps_so st) /\ aps_ok L st /\ rw_cells bsegs m ssp_guard [C8 canary]
    /\ adrv_pres AI LB usp m0 m
    /\ aincb c m /\ ATEXIT TBL_REG m.
  Notation BASE := (BASEc 0).
  Definition INV0 (own : option (AsanCtrl.aptr * Z)) (st : APS) (m : amem) : Prop :=
    BASE st m /\ bytes_at bsegs m (dptr own) (zbytes payload).
  (* [comment removed for export] *)
  Definition CBOK (cb : list ablock) (st : APS) : Prop :=
    (cb = [] /\ aps_cl st = cl0) \/ (exists pc V, cl0 = None /\ cb = [HB pc V 8] /\ aps_cl st = Some pc).
  Definition INV (own : option (AsanCtrl.aptr * Z)) (RNG : footprint) (st : APS) (m : amem) : Prop :=
    (exists cb, CBOK cb st /\ AHEAP AI L RNG (aps_m st) (cb ++ LBT own) m /\ client_static st (cb ++ LBT own) m) /\ RNGS RNG /\ INV0 own st m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b sm2 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) rcw (wz AINIT_FLAG) (wz k) (wz b) sm2 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition SM2 : word := Z_to_bv 64 (0 + -2).
  Lemma SM2_unsigned : bv_unsigned SM2 = 18446744073709551614.
  Proof using . reflexivity. Qed.

  (* [comment removed for export] *)
  Definition RUNST0 (own : option (AsanCtrl.aptr * Z)) (pc : Z) (k b : Z) (rcw : word) (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b SM2 t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own RNG st m /\ dk (aps_m st) <= 16 + 8 * (calls - k).   (* [comment removed for export] *)
  Definition RUNST (own : option (AsanCtrl.aptr * Z)) (pc : Z) (k b : Z) (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    (exists rcw, RUNST0 own pc k b rcw RNG st ms) /\ 0 <= b <= 1.

  (* [comment removed for export] *)
  Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + Lc.
  Proof using CAP FC L0 L6 LC rc sp.
    unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
    assert (CF : 0 <= (if 0 <? Lc then znth content 2 else 0) < 256).
    { destruct (0 <? Lc); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
      assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
      pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
    pose proof (land3_range (if 0 <? Lc then znth content 2 else 0) ltac:(lia)).
    repeat split; lia.
  Qed.

  Lemma LO' : lo <= usp - 80 - AHARNESS_STACK.
  Proof using LO rc. unfold ATARGET_RUN_STACK in LO. lia. Qed.

  (* [comment removed for export] *)
  Lemma geo : 0x10007fff8000 <= lo /\ 0x7fff7f800000 <= lo /\ lo <= usp - 80 - 16384 /\ 0 <= usp < 2^47 /\ usp mod 16 = 0.
  Proof using BOT CEIL LO SP16 SPHI.
    pose proof LO' as L'. unfold AHARNESS_STACK in L'. pose proof CEIL as C. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp). repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_init : forall RNG (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (cdt thr sec : byte) (tm1 : word),
    stk bsegs m lo usp -> mem_inv bsegs m -> atrun_cells0 m ->
    rw_cells bsegs m 0x66ec80 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    ATEXIT TBL_MAIN m -> aincb 0 m ->
    rw_cells bsegs m AGOT_FUZZ_INIT [C8 (wz AFUZZ_INIT)] ->
    rng RNG lo (usp + 128 - lo) -> rng_aimg RNG ->
    (forall (m' : amem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FRAME m' -> stk bsegs m' lo (usp + -80) ->
        munch [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' AINIT_FLAG [C1 (Z_to_bv 8 1)] -> ATEXIT TBL_REG m' -> aincb 0 m' ->
        evtF bsegs RNG Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 x10 x11 x12 x13 x14 x15 x16 x17
                                   a1 a0 (wz AINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                             F (Z_to_bv 64 0x95478) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ATARGET_RUN) fc None m (seg_rom bsegs)).
  Proof using BOT CEIL LO SP16 SPHI.
    intros until tm1. intros ST MI TR LIBC ATX INCB GFI RSTK RIMG K. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    destruct TR as (PI & _). unfold aincb in INCB.
    unfold AINIT_FLAG, AGOT_FUZZ_INIT, AFUZZ_INIT, AAEF_ARGC in *.
    pose proof (munch_refl [(usp - 128, usp); (0x64dcd0, 0x64dcd0 + 1); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)] m) as MU.
    pose proof (munch_refl [(usp - 128, usp); (0x64dcd0, 0x64dcd0 + 1)] m) as MU0. pose proof (wmono_refl bsegs m) as WM.
    unfold ATARGET_RUN. sort_lits.
    zstep. carve_frame 80%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch type of MU0 with munch _ _ ?mc =>
      pose proof (ATEXIT_munch _ _ m mc ATX MU0 WM ltac:(cbn [disjoint_from]; lia)) as ATX1 end.
    clear MU0 ATX.
    call_sp (atexit1_spec RNG).
    all: try unname_sp.
    all: try first [ exact ATX1 | exact LIBC | eassumption | reflexivity | (unfold KHIGH; lia) | (eapply rng_sub'; [exact RSTK| lia]) ].
    zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
    zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - lazymatch goal with H : rw_cells bsegs _ (usp + -80) _ |- _ => eexists; exact H end.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - unfold aincb. assumption.
  Qed.

  (* [comment removed for export] *)
  Section AfterCallee.
    Variables (LX : list ablock) (SP' : Z) (m m' : amem).
    Hypothesis HP : harness_pres CI LX SP' m m'.   (* [comment removed for export] *)
    Hypothesis HS : astk_shadow_pres SP' m m'.
    Hypothesis SPlo : lo <= SP'.
    Hypothesis SPhi : SP' <= usp + -80.
    Hypothesis SP8 : SP' mod 8 = 0.
    Hypothesis HL : forall b, In b LB -> In b LX.

    Let AG : magree bsegs (fun a => dcli CI LX SP' a /\ outside client_wr a) m m' := magree_of_hpost CI LX SP' m m' HP HS.

    Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LX SP' a.
    Proof using DRV_CI sp. intros lo' hi' a Hin Ha. left. right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin| cbn; lia]. Qed.
    Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LX SP' a.
    Proof using DRV_CI sp.
      intros lo' hi' a Hin Ha H8' H8. left. right; right; right. exists (8 * (a - ASHOFF)). split.
      - right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
      - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    Qed.
    Lemma ci_uri_sh : forall lo' hi' a, In (lo', hi') uri_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LX SP' a.
    Proof using URI_CI sp.
      intros lo' hi' a Hin Ha H8. left. right; right; right. exists (8 * (a - ASHOFF)). split.
      - right; left. exists (lo', hi'). split; [apply URI_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
      - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    Qed.
    Lemma stack_dcli : forall a, usp + -80 <= a < usp -> dcli CI LX SP' a.
    Proof using BOT CEIL LO SP16 SPHI SPhi SPlo. intros a Ha. pose proof geo. left. left. lia. Qed.
    (* [comment removed for export] *)
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LX SP' a.
    Proof using BOT SP8 SPhi SPlo.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad SP')) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split.
        + left. rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
        + rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    Qed.

    Lemma BASE_after_dpost : forall c st st' RNG' LX',
      BASEc c st m -> harness_invA m' ->
      AHEAP AI L RNG' (aps_m st') LX' m' -> aps_rest st' = aps_rest st ->
      mem_inv bsegs m' -> stk bsegs m' lo (usp + -80) ->
      BASEc c st' m'.
    Proof using AG BOT CEIL DRV_CI HL LO RSceil SP16 SP8 SPHI SPhi SPlo URI_CI.
      intros c st st' RNG' LX' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT) HI' AH' ESO MI' ST'.
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSceil as RSC. atop_facts.
      split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; cbn in Ha; split; [apply stack_dcli; lia| ocw]]. }
      split; [exact HI'|].
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. split; [apply (ci_drv_sh 0x10000 0x22f40); [left; reflexivity| exact Ha| reflexivity| reflexivity]|].
               rewrite !shad_div in Ha. unfold ASHOFF in Ha. ocw. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               split; [apply (stack_sh_dcli (r_rlo rstk) (r_rhi rstk)); [atop_facts; lia| lia| exact Ha]|].
               pose proof (shad_mono ATOP (r_rlo rstk) RSC) as SM. rewrite (shad_div ATOP) in SM. unfold ASHOFF in SM. Z.div_mod_to_equations. ocw. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               split; [apply (ci_drv_sh 0x66f0e0 0x66f500); [do 7 right; left; reflexivity| | reflexivity| reflexivity]; rewrite !shad_div in *; unfold ASHOFF in *; lia|].
               rewrite !shad_div in Ha. unfold ASHOFF in Ha. ocw. }
      split; [exact MI'|]. split; [exact ST'|].
      split. { rewrite (aps_so_of_rest _ _ ESO). eapply stdout_file_magree; [exact AG| | exact SO]. intros a [Ha|Ha].
               - split; [apply (ci_drv RSTDOUT (RSTDOUT + 232)); [do 3 right; left; reflexivity| exact Ha]| ocw].
               - split; [apply (ci_drv 0x66f0e0 0x66f500); [do 7 right; left; reflexivity| cbn in Ha |- *; lia]| cbn in Ha; ocw]. }
      split. { eapply aps_ok_rest; [exact ESO| exact RK]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. unfold ssp_guard in Ha. cbn in Ha.
               split; [apply (ci_drv 0x66ea30 0x66ea38); [do 9 right; left; reflexivity| lia]| ocw]. }
      split.
      { eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx.
        assert (OX : outside client_wr a) by (unfold atrun_ivs in Hx; cbn [rin_ivs] in Hx; unfold AINIT_FLAG, ANEWH in Hx; ocw).
        destruct Hc as [Hc|Hs].
        - apply AG; [exact Ha|]. split; [| exact OX]. eapply dcli_weaken; [left; exact Hc| lia| lia| lia| exact HL].
        - apply AG; [exact Ha|]. split; [| exact OX]. eapply dcli_weaken; [right; exact Hs| lia| lia| lia| exact HL]. }
      split.
      { eapply aincb_magree; [exact AG| | exact TX]. intros a Ha. pose proof (aincb_addr_range a Ha).
        split; [apply (ci_drv 0x64dcd0 0x64deb8); [right; left; reflexivity| lia]| ocw]. }
      eapply ATEXIT_magree; [exact AT| exact AG|]. intros a Ha.
      split; [apply (ci_drv 0x66ea40 0x66ec60); [do 10 right; left; reflexivity| lia]| ocw].
    Qed.

    (* [comment removed for export] *)
    Lemma bytes_after_dpost : forall D bs,
      bytes_at bsegs m D bs ->
      ((exists q n, In (HB q D n) LX /\ Z.of_nat (length bs) <= n) \/ (exists lo' hi', In (lo', hi') drv_img_ranges /\ lo' <= D /\ D + Z.of_nat (length bs) <= hi')
       \/ (exists q B n, In (HB q B n) LX /\ B <= D /\ D + Z.of_nat (length bs) <= B + n)) ->
      (forall a, D <= a < D + Z.of_nat (length bs) -> outside client_wr a) ->
      bytes_at bsegs m' D bs.
    Proof using AG BOT DRV_CI SPhi SPlo.
      intros D bs HBY HW HO. eapply bytes_at_magree; [exact AG| exact HBY|]. intros a Ha. split; [| apply HO; exact Ha].
      destruct HW as [(q & n & Hin & Hn)|[(lo' & hi' & Hin & H1 & H2)|(q & B & n & Hin & H1 & H2)]].
      - left. right; right; left. exists (HB q D n). split; [exact Hin| cbn; lia].
      - apply (ci_drv lo' hi'); [exact Hin| lia].
      - left. right; right; left. exists (HB q B n). split; [exact Hin| cbn; lia].
    Qed.
  End AfterCallee.

  (* [comment removed for export] *)
  Lemma BASE_after_emit : forall st st' m m',
    BASE st m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono bsegs m m' ->
    mem_inv bsegs m' -> stk bsegs m' lo (usp + -80) -> stdout_file m' (aps_so st') -> aps_resv st' = aps_resv st -> aps_atop st' = aps_atop st ->
    BASE st' m'
    /\ forall own, match own with None => plen = 0 | Some (_, D) => 0x671000 <= D /\ D + plen <= lo end ->
          bytes_at bsegs m (dptr own) (zbytes payload) -> bytes_at bsegs m' (dptr own) (zbytes payload).
  Proof using A BOT CAP CEIL CI_WF FC HLB L0 L6 LC LO SP16 SPHI.
    intros st st' m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT) MU WM MI' ST' SO' ERV EAT.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    assert (AW : appW [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z).
    { unfold appW. repeat constructor; cbn; unfold KLOW, KHIGH; lia. }
    assert (OUT : forall a, (usp + -80 <= a \/ (0x671000 <= a < lo) \/ (a < 0x10007fff8000 /\ ~ (0x1175f8 <= a < 0x1175f8 + 232) /\ ~ (0x66f100 <= a < 0x66f100 + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    split.
    2:{ intros own HD PB. eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
        destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia]. }
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
    split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply OUT. lia. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact SO'|]. split; [destruct RK as [RK1 RK2]; split; [rewrite ERV; exact RK1| rewrite EAT; exact RK2]|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
    split.
    2:{ split.
        - eapply aincb_magree; [exact AG| | exact TX]. intros a Ha. pose proof (aincb_addr_range a Ha). apply OUT. right; right. lia.
        - eapply ATEXIT_magree; [exact AT| exact AG|]. intros a Ha. apply OUT. right; right. lia. }
    eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT.
    unfold atrun_ivs, AINIT_FLAG, ANEWH in Hx. cbn in Hx. atop_facts.
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
        Z.div_mod_to_equations. lia.
    - right; right. rewrite !shad_div in Hs. unfold ASHOFF in Hs. pose proof geo. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma BASE_after_munch : forall st W m m',
    BASE st m -> munch W m m' -> wmono bsegs m m' -> appW W ->
    (forall a, a < 0x671000 \/ 0x7fff7000 <= a < 0x10007fff8000 -> outside W a) ->
    (forall a, usp + -80 <= a -> outside W a) ->
    (forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a) ->
    mem_inv bsegs m' -> stk bsegs m' lo (usp + -80) ->
    BASE st m'.
  Proof using BOT CEIL CI_WF HLB LO SP16 SPHI.
    intros st W m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT) MU WM AW Wlow Wstk Wblk MI' ST'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply Wstk; cbn in Ha; lia]. }
    split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply Wlow. lia. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply Wlow. lia. }
    split; [exact RK|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply Wlow. unfold ssp_guard in Ha. cbn in Ha. lia. }
    split.
    2:{ split.
        - eapply aincb_magree; [exact AG| | exact TX]. intros a Ha. pose proof (aincb_addr_range a Ha). apply Wlow. left. lia.
        - eapply ATEXIT_magree; [exact AT| exact AG|]. intros a Ha. apply Wlow. left. lia. }
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
        right. Z.div_mod_to_equations. lia.
    - apply Wlow. rewrite !shad_div in Hs. unfold ASHOFF in Hs. right. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AHEAP_after_emit : forall RNG st LX m m',
    AHEAP AI L RNG st LX m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono bsegs m m' ->
    AHEAP AI L RNG st LX m'.
  Proof using BOT CEIL DRV_CI LO SP16 SPHI m0 ra.
    intros RNG st LX m m' AH MU WM. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
    eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
    - left. left. lia.
    - left. right; left. exists (RSTDOUT, RSTDOUT + 232)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
    - left. right; left. exists (0x66f0e0, 0x66f500)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
  Qed.

  Lemma BASE_cbstore : forall c c' st m m',
    BASEc c st m -> munch [(0x64dcd4, 0x64dcd5)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' lo (usp + -80) ->
    rw_cells bsegs m' 0x64dcd4 [C1 (Z_to_bv 8 c')] ->
    BASEc c' st m'
    /\ (forall own, match own with None => plen = 0 | Some (_, D) => 0x671000 <= D end ->
          bytes_at bsegs m (dptr own) (zbytes payload) -> bytes_at bsegs m' (dptr own) (zbytes payload))
    /\ (forall RNG stt LX, AHEAP AI L RNG stt LX m -> AHEAP AI L RNG stt LX m')
    /\ (forall stt LX, (forall p V, aps_cl stt = Some p -> In (HB p V 8) LX -> 0x671000 <= V) -> client_static stt LX m -> client_static stt LX m').
  Proof using A BOT CAP CEIL DRV_CI FC L0 L6 LC LO SP16 SPHI.
    intros c c' st m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT) MU WM MI' ST' CB'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, a <> 0x64dcd4 -> (fun a0 : Z => outside [(0x64dcd4, 0x64dcd5)] a0) a) by (intros a Ha; cbn; lia).
    assert (AW : appW [(0x64dcd4, 0x64dcd5)]%Z) by (unfold appW; repeat constructor; cbn; unfold KLOW, KHIGH; lia).
    split; [| split; [| split]].
    - split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply OUT. lia. }
      split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply OUT. cbn in Ha. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
      split. { eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT.
               unfold atrun_ivs, AINIT_FLAG, ANEWH in Hx. cbn in Hx. lia. }
      split; [exact CB'|].
      eapply ATEXIT_magree; [exact AT| exact AG|]. intros a Ha. apply OUT. lia.
    - intros own HD PB. eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia].
    - intros RNG stt LX AH. eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
      constructor; [| constructor]. cbn [fst snd]. left. right; left. exists (0x64dcd0, 0x64deb8)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
    - intros stt LX HV CS. eapply client_static_agree; [exact AG| | | exact CS].
      + intros a Ha. apply OUT. unfold cstat_addr in Ha. lia.
      + intros pv Vv a EC HIN Ha. apply OUT. pose proof (HV pv Vv EC HIN). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma call_body : forall own k b (rcw : word) RNG st ms {B} (K : Z -> @Monad.M APS B) (Q : B -> APS -> footprint -> machine_state -> Prop),
    1 <= k <= 4 -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => 0 < plen end -> RUNST0 own 0x954e8 k b rcw RNG st ms ->
    (forall rc' RNG' st' ms', RUNST own (if k =? 1 then 0x95520 else 0x954e8) (k - 1) (bad_after rc' b) RNG' st' ms' -> implMA RNG' (K rc') st' Q ms') ->
    implMA RNG (rc' <- fuzz_oneA AAllocAsan payload ;; io_emit (ioA AAllocAsan) rc' ;;; K rc') st Q ms.
  Proof using A ASHENV BOT CAP CEIL CI_WF DRV_CI EMIT FC FUZZ HLB HLBH HUL L0 L6 LC LO RSceil RShi RSlo SP16 SPG SPHI URI_CI rng_fs_mono AHFRESH WRT0.
    intros own k b rcw RNG st ms B K Q HK Hb01 OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (P & RG & [BA PB]) & DKK).
    destruct P as (cb & CBK & P & CST).
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    assert (BOWN : match own with None => True | Some (_, D) => ablock_range D plen /\ 0x671000 <= D /\ D + plen <= ATOP end).
    { destruct own as [[q D]|]; [| exact I].
      pose proof (AI_block AI _ _ _ _ _ q D plen P ltac:(apply in_or_app; right; left; reflexivity)) as (_ & BR & _).
      pose proof (AI_block_bounds AI _ _ _ _ _ (HB q D plen) P ltac:(apply in_or_app; right; left; reflexivity)) as (B1 & B2 & B3). cbn in B1, B2, B3.
      unfold AIMG_HI in B1. split; [exact BR| lia]. }
    assert (HV : forall pv V, aps_cl st = Some pv -> In (HB pv V 8) (cb ++ LBT own) -> 0x671000 <= V).
    { intros pv V _ HIN. pose proof (AI_block_bounds AI _ _ _ _ _ (HB pv V 8) P HIN) as (B1 & _). cbn in B1. unfold AIMG_HI in B1. lia. }
    pose proof TX as INCB. unfold aincb in INCB. clear FR ROD RCS RCB SO GU DP AT.
    pose proof (munch_refl [(0x64dcd4, 0x64dcd5)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    hide PB. apply implMA_from_evtF. unfold AINIT_FLAG. zstep. zstep. unhide PB.
    lazymatch type of MU with munch _ _ ?mx =>
      destruct (BASE_cbstore 0 1 st m mx BA MU WM MI ST INCB) as (BA1 & PBK & AHK & CSK) end.
    pose proof (PBK own ltac:(destruct own as [[q D]|]; [destruct BOWN as (_ & B1 & _); exact B1| exact OWNZ]) PB) as PB1.
    pose proof (AHK _ _ _ P) as P1. pose proof (CSK st _ HV CST) as CST1.
    clear PBK AHK CSK MU WM BA PB P CST HI TX INCB.
    pose proof BA1 as (FR & HI & ROD & RCS & RCB & _ & _ & SO & _ & GU & DP & TX & AT).
    fold AINIT_FLAG.
    zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { (* [comment removed for export] *)
      eapply (FUZZ L RNG) with (lo := lo) (LB := cb ++ LBT own) (D := dptr own) (payload := payload) (rstk := rstk);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P1.
      - intros bb Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + destruct CBK as [[-> _]|(pc & V & _ & -> & _)]; [destruct Hb| destruct Hb as [<-|[]]; exists pc, V, 8; reflexivity].
        + destruct own as [[q D]|]; cbn [LBT] in Hb; [destruct Hb as [<-|Hb]; [exists q, D, plen; reflexivity|]|]; exact (HLBH bb Hb).
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + left. exists q. rewrite PLEN. split; [apply in_or_app; right; left; reflexivity| lia].
        + right. split; [| reflexivity]. apply length_zero_iff_nil. unfold zlength in PLEN. lia.
      - exact PB1.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr]; [destruct BOWN as ((_ & _ & _ & X) & _); exact X| reflexivity].
      - lia.
      - exact HI.
      - exact CST1.
      - exact ST.
      - exact BOT.
      - pose proof LO'. lia.
      - lia.
      - clear -SP16 G4. Z.div_mod_to_equations. lia.
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
      - exact RK.
      - exact (AHFRESH _ _ _ _ _ P1).     (* [comment removed for export] *)
      - unfold DKF. clear - DKK HK CALLS. lia.     (* [comment removed for export] *)
      - (* [comment removed for export] *)
        destruct FR as [j0 FRc]. pose proof (AI_layout AI _ _ _ _ _ P1) as (Y1 & Y2 & Y3 & Y4).
        pose proof (rw_cells_wr_at bsegs _ _ _ 80 FRc ltac:(cbn; lia)) as WF.
        pose proof (harness_top L (usp + -80) ltac:(lia) ltac:(lia)) as TOPG.     (* [comment removed for export] *)
        destruct (Z_le_dec (al_top L) usp) as [TL|TL].
        + apply (wr_at_sub_dk _ _ 80); [exact WF| lia].
        + replace (al_top L - (usp + -80)) with (80 + (al_top L - usp)) by lia.
          apply wr_at_join_dk; [exact WF| | lia| lia].
          replace (usp + -80 + 80) with usp by lia.
          apply (wr_at_adrv_dk AI LB usp m0 _ _ DP WRT0); [lia|].
          intros a Ha. unfold atrun_ivs. cbn [rin_ivs]. unfold AINIT_FLAG, ANEWH. clear - Ha G1 G3. lia. }
    cbv beta. intros r st1 RNG1 ms1 PO.
    destruct PO as (LE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & mh & LB1
                    & -> & RR & MI1 & FRM1 & ST1 & HPR & HSP & P2 & HI2 & CST2 & SOE & ARM0).
    destruct ARM0 as (ARMa & ARMb & AFR1 & DKP). pose proof (conj ARMa ARMb) as ARM. clear ARMa ARMb.   (* [comment removed for export] *)
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    unfold ATRUN_RET. fix_ret. subst r.
    (* [comment removed for export] *)
    assert (CB1 : exists cb1, CBOK cb1 st1 /\ LB1 = cb1 ++ LBT own).
    { destruct ARM as (-> & E1). exists cb. split; [| reflexivity].
      destruct CBK as [[E0 CL]|(pc & V & C0 & E0 & CL)]; [left; split; [exact E0| rewrite E1; exact CL]| right; exists pc, V; split; [exact C0| split; [exact E0| rewrite E1; exact CL]]]. }
    destruct CB1 as (cb1 & CBK1 & ->).
    assert (BA2 : BASEc 1 st1 mh).
    { eapply (BASE_after_dpost (cb ++ LBT own) (usp + -80) _ mh HPR HSP); [lia| lia| clear -SP16 G4; Z.div_mod_to_equations; lia| | exact BA1| exact HI2| exact P2| exact SOE| exact MI1| exact ST1].
      intros bb Hb; apply in_or_app; right; destruct own as [[q D]|]; [right|]; exact Hb. }
    assert (PB2 : bytes_at bsegs mh (dptr own) (zbytes payload)).
    { eapply (bytes_after_dpost (cb ++ LBT own) (usp + -80) _ mh HPR HSP ltac:(lia) ltac:(lia)); [exact PB1| |].
      + rewrite zbytes_length. unfold zlength in PLEN. destruct own as [[q D]|]; cbn [dptr LBT].
        * left. exists q, plen. split; [apply in_or_app; right; left; reflexivity| lia].
        * right; left. exists 0x64dcd0, 0x64deb8. split; [cbn; tauto|]. unfold AEMPTY. lia.
      + intros a Ha. rewrite zbytes_length in Ha. unfold zlength in PLEN. destruct own as [[q D]|]; cbn [dptr] in Ha; [destruct BOWN as (_ & B1 & B2); ocw| lia]. }
    assert (HV2 : forall pv V, aps_cl st1 = Some pv -> In (HB pv V 8) (cb1 ++ LBT own) -> 0x671000 <= V).
    { intros pv V _ HIN. pose proof (AI_block_bounds AI _ _ _ _ _ (HB pv V 8) P2 HIN) as (B1 & _). cbn in B1. unfold AIMG_HI in B1. lia. }
    clear HPR HSP BA1 FR PB1 HI ROD RCS RCB MI ST SO GU DP TX AT P1 CST1 HV RK.
    pose proof BA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TX2 & _). pose proof TX2 as INCB. unfold aincb in INCB. clear TX2.
    assert (RGimg1 : rng_aimg RNG1) by (eapply rng_fp_le; [exact LE1 | exact RGimg]).
    pose proof (munch_refl [(0x64dcd4, 0x64dcd5)] mh) as MU. pose proof (wmono_refl bsegs mh) as WM.
    hide PB2. apply implMA_from_evtF. unfold AINIT_FLAG. zstep. zstep. unhide PB2. clear RGimg1.
    lazymatch type of MU with munch _ ?ma ?mb =>
      destruct (BASE_cbstore 1 0 st1 ma mb BA2 MU WM MI1 ST1 INCB) as (BA & PBK & AHK & CSK) end.
    pose proof (PBK own ltac:(destruct own as [[q D]|]; [destruct BOWN as (_ & B1 & _); exact B1| exact OWNZ]) PB2) as PB.
    pose proof (AHK _ _ _ P2) as P1. pose proof (CSK st1 _ HV2 CST2) as CST1.
    clear PBK AHK CSK MU WM BA2 PB2 P2 CST2 INCB.
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT).
    fold AINIT_FLAG.
    clear HI2. lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    (* [comment removed for export] *)
    zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply implMA_keeps with (f := aps_mrac); [| apply s_emit_aps_mrac].
      unfold io_emit, ioA, io_S. cbn [a_so a_set_so AAllocAsan].
      destruct (drv_got_of_aheap AI _ _ _ _ _ P1) as (_ & _ & _ & GSSP).
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
      - exact (ASHENV _ _ _ _ _ P1).
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
    destruct PO as (ER & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO2 & SSP2).
    subst RNG2.
    rewrite ?(unsigned_lit (usp + -80)) in MUc, ST2 by lia.
    fix_ret.
    unfold aps_mrac in EH. pose proof (f_equal snd EH) as ECL2. apply (f_equal fst) in EH. cbn [fst snd] in EH, ECL2.
    unfold aps_mra in EH. pose proof (f_equal snd EH) as EAT. apply (f_equal fst) in EH. pose proof (f_equal snd EH) as ERV. apply (f_equal fst) in EH. cbn [fst snd] in EH, ERV, EAT.
    assert (P2 : AHEAP AI L RNG1 (aps_m st2) (cb1 ++ LBT own) m2).
    { rewrite EH. eapply AHEAP_after_emit; [exact P1| exact MUc| exact WMc]. }
    assert (CST2 : client_static st2 (cb1 ++ LBT own) m2).
    { eapply client_static_cl; [exact ECL2|]. eapply client_static_agree; [exact (magree_of_munch bsegs _ _ _ MUc WMc)| | | exact CST1].
      - intros a Ha. unfold cstat_addr in Ha. cbn [outside fst snd]. lia.
      - intros pv Vv a EC HIN Ha. pose proof (AI_block_bounds AI _ _ _ _ _ (HB pv Vv 8) P1 HIN) as (B1 & B2 & B3). cbn in B1, B2, B3.
        unfold AIMG_HI in B1. cbn [outside fst snd]. lia. }
    assert (CBK2 : CBOK cb1 st2).
    { destruct CBK1 as [[E1 E2]|(pc & V & E0 & E1 & E2)]; [left; split; [exact E1| rewrite ECL2; exact E2]| right; exists pc, V; split; [exact E0| split; [exact E1| rewrite ECL2; exact E2]]]. }
    assert (IV2 : INV0 own st2 m2).
    { destruct (BASE_after_emit st1 st2 mc m2 BA MUc WMc MI2 ST2 SO2 ERV EAT) as [BA2 PBK]. split; [exact BA2|].
      apply PBK; [| exact PB]. destruct own as [[q D]|]; [| exact OWNZ]. destruct BOWN as (_ & B1 & B2). lia. }
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    clear MUc WMc.
    (* [comment removed for export] *)
    eapply implMA_evtF; [| intros ms' H; exact (HKONT _ _ _ _ H)].
    zstep. change (bv_swrap 32 (0 + -1)) with (-1)%Z.
    zstep. if_cases KB; zify_cond KB; rewrite ?SM2_unsigned in KB; [| exfalso; clear -KB; lia]. clear KB.
    zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
    - replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evtF_done. change (bad_after 0 b) with b. split; [| lia]. exists (Z_to_bv 64 (-1)). unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
      split; [reflexivity|]. split; [exact FRM2|].
      split; [split; [exists cb1; split; [exact CBK2| split; [exact P2| exact CST2]]| split; [exact RG1| exact IV2]]| rewrite EH; clear - DKK DKP; lia].
    - replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      apply evtF_done. change (bad_after 0 b) with b. split; [| lia]. exists (Z_to_bv 64 (-1)). unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
      split; [reflexivity|]. split; [exact FRM2|].
      split; [split; [exists cb1; split; [exact CBK2| split; [exact P2| exact CST2]]| split; [exact RG1| exact IV2]]| rewrite EH; clear - DKK DKP; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma calls_loop : forall (n : nat) own b (rcw : word) RNG st ms,
    (1 <= n <= 4)%nat -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => 0 < plen end ->
    RUNST0 own 0x954e8 (Z.of_nat n) b rcw RNG st ms ->
    implMA RNG (run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload b) st
           (fun b' st' RNG' ms' => RUNST own 0x95520 0 b' RNG' st' ms') ms.
  Proof using A ASHENV BOT CAP CEIL CI_WF DRV_CI EMIT FC FUZZ HLB HLBH HUL L0 L6 LC LO RSceil RShi RSlo SP16 SPG SPHI URI_CI rng_fs_mono AHFRESH WRT0.
    induction n as [|n IH]; intros own b rcw RNG st ms HN Hb01 OWNZ R; [lia|].
    cbn [run_calls].
    eapply (call_body own (Z.of_nat (S n)) b rcw RNG st ms (fun rc' => run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload (bad_after rc' b)));
      [lia| exact Hb01| exact OWNZ| exact R|].
    intros rc' RNG' st' ms' R'. destruct n as [|n'].
    - cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implMA_ret. apply evtF_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. exact R'.
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      destruct R' as [[rcw' R'] Hb01'].
      apply (IH own (bad_after rc' b) rcw' RNG'); [lia| exact Hb01'| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed.

  Notation POST s RNG := (atarget_run_postA AI L RNG ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo canary m0).

  (* [comment removed for export] *)
  Lemma run_tail : forall (s : APS) own b RNG st ms,
    aps_cl s = cl0 ->
    RUNST own 0x95520 0 b RNG st ms ->
    implMA RNG ((match omodel own with Some q => afree_M q | None => mret tt end) ;;; mret (if b =? 0 then 0 else 78)) st
           (POST s RNG00) ms.
  Proof using A BOT CAP CEIL CL0LB DFREE DFREEN DRV_CI FC L0 L6 LC LO RSceil SP16 SPHI UF0 UF1 URI_CI rng_fs_mono.
    intros s own b RNG st ms CLS [[rcw R] Hb01].
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (P & RG & [BA PB]) & DKK).
    destruct P as (cb & CBK & P & CST).
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & TX & AT).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    unfold FRAME in FR. destruct FR as [j0 FR].
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind with (Q1 := fun _ st' RNG' ms' => fp_le RNG RNG' /\ exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : amem),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (wz plen) (wz (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (wz (oreg own)) rcw (wz AINIT_FLAG) (wz 0) (wz b) SM2 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x95528) fc None m' (seg_rom bsegs)
        /\ AHEAP AI L RNG' (aps_m st') (cb ++ LB) m' /\ FRAME m' /\ harness_invA m' /\ client_static st' (cb ++ LB) m' /\ CBOK cb st'
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -80)
        /\ stdout_file m' (aps_so st') /\ aps_ok L st' /\ rw_cells bsegs m' ssp_guard [C8 canary] /\ adrv_pres AI LB usp m0 m'
        /\ aincb 0 m' /\ ATEXIT TBL_REG m').
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      - (* [comment removed for export] *)
        eapply implMA_mono.
        { eapply (dfree_M AI DFREE L RNG) with (lo := lo) (p := q) (A := D) (n := plen); try reflexivity;
            rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | (apply in_or_app; right; left; reflexivity) | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia
                  | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ]. all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros [] st' RNG' ms' [SOE PO].
        destruct PO as (LE & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia.
        fix_ret. cbn [aps_m aset_m fst] in HEAP3.
        pose proof (AI_hb_ids AI _ _ _ _ _ P) as ND.
        assert (ERM : lb_remove q (cb ++ HB q D plen :: LB) = cb ++ LB).
        { destruct CBK as [[-> _]|(pc & V & _ & -> & _)]; [exact (lb_remove_headA q D plen LB ND)| exact (lb_remove_secondA q D plen (HB pc V 8) LB ND)]. }
        rewrite ERM in HPR3, HEAP3.
        assert (HI3 : harness_invA m3).
        { destruct HI as [IG SH]. split; [eapply (client_img_pres AI URI_CI); [exact IG| exact HPR3| exact HEAP3| exact MI3]| eapply (client_sh_pres AI URI_CI); [exact HPR3| exact SH]]. }
        assert (CST3 : client_static st' (cb ++ LB) m3).
        { eapply client_static_cl; [exact (aps_cl_ofU _ _ SOE)|]. eapply (client_static_pres AI URI_CI); [exact HPR3|].
          eapply client_static_lb; [| exact CST]. intros pv Vv EC HIN. apply in_app_or in HIN. apply in_or_app. destruct HIN as [HIN|HIN]; [left; exact HIN|].
          destruct HIN as [E|HIN]; [| right; exact HIN]. exfalso.
          assert (EQ : pv = q) by (inversion E; reflexivity). subst pv.
          destruct CBK as [[-> CL]|(pc & V & C0 & -> & CL)].
          - rewrite EC in CL. destruct (CL0LB q (eq_sym CL)) as (V0 & HIN0).
            unfold hb_ids in ND. cbn [app flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
            apply in_flat_map. exists (HB q V0 8). split; [exact HIN0| left; reflexivity].
          - rewrite CL in EC. assert (Epq : pc = q) by (inversion EC; reflexivity). subst pc.
            unfold hb_ids in ND. cbn [app flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. left; reflexivity. }
        assert (CBK3 : CBOK cb st').
        { pose proof (aps_cl_ofU _ _ SOE) as EC. destruct CBK as [[E1 E2]|(pc & V & E0 & E1 & E2)]; [left; split; [exact E1| rewrite EC; exact E2]| right; exists pc, V; split; [exact E0| split; [exact E1| rewrite EC; exact E2]]]. }
        destruct (BASE_after_dpost (cb ++ LB) (usp + -80) m m3 (harness_pres_of_aheap_pres _ _ _ _ _ HPR3) HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; Z.div_mod_to_equations; lia)
                    ltac:(intros bb Hb; apply in_or_app; right; exact Hb) 0 st st' _ _ BA HI3 HEAP3 (aps_rest_ofU _ _ SOE) MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & DP3 & TX3 & AT3).
        split; [exact LE|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact HI3|]. split; [exact CST3|]. split; [exact CBK3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3|]. split; [exact TX3| exact AT3].
      - (* [comment removed for export] *)
        apply implMA_ret.
        eapply evtF_mono.
        { eapply (DFREEN L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
          all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia. fix_ret.
        assert (HI3 : harness_invA m3).
        { destruct HI as [IG SH]. split; [eapply (client_img_pres AI URI_CI); [exact IG| exact HPR3| exact HEAP3| exact MI3]| eapply (client_sh_pres AI URI_CI); [exact HPR3| exact SH]]. }
        assert (CST3 : client_static st (cb ++ LB) m3) by (eapply (client_static_pres AI URI_CI); [exact HPR3| exact CST]).
        destruct (BASE_after_dpost (cb ++ LB) (usp + -80) m m3 (harness_pres_of_aheap_pres _ _ _ _ _ HPR3) HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; Z.div_mod_to_equations; lia)
                    ltac:(intros bb Hb; apply in_or_app; right; exact Hb) 0 st st _ _ BA HI3 HEAP3 eq_refl MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & DP3 & TX3 & AT3).
        split; [apply fp_le_refl|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact HI3|]. split; [exact CST3|]. split; [exact CBK|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3|]. split; [exact TX3| exact AT3]. }
    cbv beta. intros [] st' RNG' ms' (LE & x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & P' & [j0' FR'] & HI' & CST' & CBK' & MI' & ST' & SO' & RK' & GU' & DP' & TX' & AT').
    apply implMA_ret.
    pose proof (RNGS_mono _ _ LE RG) as (RGstk' & _).
    (* [comment removed for export] *)
    hide TX'. zstep. zstep. zstep.
    do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep. unhide TX'.
    first [ lazymatch goal with |- context [Z_to_bv 64 (Z.land ?e 78)] =>
              replace (Z.land e 78) with (if b =? 0 then 0 else 78)
                by (assert (Hb : b = 0 \/ b = 1) by lia; destruct Hb as [Hb|Hb]; rewrite Hb; vm_compute; reflexivity) end
          | idtac "run_tail: status register left as is" ].
    apply evtF_done. unfold atarget_run_postA. split; [eapply fp_le_trans; [exact LE00| exact LE]|].
    destruct (drv_got_of_aheap AI _ _ _ _ _ P') as (_ & _ & _ & GSSP').
    do 14 eexists. exists F, fc, m', (cb ++ LB).
    split; [reflexivity|].
    split; [destruct (b =? 0); lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact DP'|]. split; [exact P'|]. split; [exact HI'|]. split; [exact CST'|].
    split. { destruct CBK' as [[-> E2]|(pc & V & E0 & -> & E2)]; [split; [reflexivity| rewrite E2, CLS; reflexivity]| exfalso; destruct CST' as [CLN _]; rewrite E2 in CLN; discriminate]. }
    split; [exact SO'|]. split; [split; [exact GSSP'| exact GU']|]. split; [exact RK'|].
    unfold ATXS. split; [exact AT'| split; [exact TX'| right; reflexivity]].
  Qed.

  Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
    implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof using . intros X Y RNG a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Definition PRE1 (RNG : footprint) (s : APS) (m : amem) : Prop :=
    AHEAP AI L RNG (aps_m s) LB m /\ RNGS RNG /\ BASE s m /\ bytes_at bsegs m A (zbytes content) /\ client_static s LB m /\ aps_cl s = cl0
    /\ dk (aps_m s) <= 16.

  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 AINIT_FLAG) (Z_to_bv 64 calls) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma trun_empty : forall RNG s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen = 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x954d8 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof using ASHENV BOT CAP CEIL CI_WF CL0LB DFREE DFREEN DRV_CI EMIT FC FUZZ HLB HLBH HUL L0 L6 LC LO RSceil RShi RSlo SP16 SPG SPHI UF0 UF1 URI_CI rng_fs_mono AHFRESH WRT0.
    intros until m. intros PZ FRM (P & RG & BA & CT & CST & CL0 & DK0).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold runA, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMA_retb. cbv beta iota.
    apply implMA_from_evtF. unfold AINIT_FLAG. zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (calls_loop (Z.to_nat calls) None 0 x19 RNG); [lia| lia| exact PZ|].
      unfold RUNST0. do 16 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AEMPTY, AINIT_FLAG, SM2; reflexivity|].
      split; [exact FRM|]. split; [| clear - DK0; lia].
      split; [exists []; split; [left; split; [reflexivity| exact CL0]| split; [exact P| exact CST]]|]. split; [exact RG|]. split; [exact BA|].
      assert (PE : payload = []). { apply length_zero_iff_nil. unfold zlength in PLEN. lia. }
      cbn [dptr]. rewrite PE. cbn [zbytes map]. apply bytes_at_nil. unfold AEMPTY. lia. }
    cbv beta. intros b st' RNG' ms' R. apply (run_tail s None b RNG' st' ms' CL0 R).
  Qed.

  Lemma implMA_bind_assoc : forall {X Y W} RNG (ma : @Monad.M APS X) (g : X -> @Monad.M APS Y) (f : Y -> @Monad.M APS W) s Q ms,
    implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
  Proof using .
    intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_copy : forall RNG s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen <> 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x9548c x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof using ASHENV BOT CAP CEIL CI_WF CL0LB DFREE DFREEN DMALLOC DRV_CI EMIT FC FUZZ HLB HLBH HUL INLB L0 L6 LC LO RSceil RShi RSlo SP16 SPG SPHI UF0 UF1 UM0 UM1 URI_CI rng_fs_mono AHFRESH WRT0.
    intros until m. intros PZ FRM (P & RG & BA & CT & CST & CL0 & DK0). pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & DP & _ & _).
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
    { eapply implMA_leaves; [| exact (amalloc_M_dk _ s)].   (* [comment removed for export] *)
      eapply (dmalloc_M AI DMALLOC L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact MI | exact ST | exact BOT | unfold AMALLOC_STACK; pose proof LO'; lia | unfold AREQMAX; lia
              | exact UM1 | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
    cbv beta. intros r s1' RNG1 ms1 [[SOE PO] DKM].
    destruct DKM as (DKF1 & _ & _). destruct (DKF1 (AHFRESH _ _ _ _ _ P)) as [_ DKM1]. clear DKF1.
    destruct PO as (LE1 & u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & HPR & HSP & RR).
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in RR.
    destruct r as [nb|]; [| destruct RR].
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & RGN & RGNS & _).
    pose proof BR' as (BN1 & BN2 & BN3 & BN4). pose proof (ablk_lin _ _ BN1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    pose proof RG1 as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & RGfs1 & RRS1 & RRF1 & RRB1 & LE01).
    (* [comment removed for export] *)
    pose proof (magree_of_dpost _ _ _ _ _ HPR HSP) as AG1.
    assert (HI1 : harness_invA m1).
    { destruct HI as [IG SH]. split; [eapply (client_img_pres AI URI_CI); [exact IG| exact HPR| exact HEAP1| exact MI1]| eapply (client_sh_pres AI URI_CI); [exact HPR| exact SH]]. }
    assert (CST1 : client_static s1' (HB nb A' plen :: LB) m1).
    { eapply client_static_cl; [exact (aps_cl_ofU _ _ SOE)|]. eapply client_static_lb; [| eapply (client_static_pres AI URI_CI); [exact HPR| exact CST]].
      intros pv Vv _ HIN. right. exact HIN. }
    assert (CL1 : aps_cl s1' = cl0) by (rewrite (aps_cl_ofU _ _ SOE); exact CL0).
    assert (BA1 : BASE s1' m1).
    { eapply (BASE_after_dpost LB (usp + -80) m m1 (harness_pres_of_aheap_pres _ _ _ _ _ HPR) HSP); [lia| lia| clear -SP16 G4; Z.div_mod_to_equations; lia| intros bb Hb; exact Hb| exact BA| exact HI1| exact HEAP1| exact (aps_rest_ofU _ _ SOE)| exact MI1| exact ST1]. }
    pose proof BA1 as (FR1 & _). unfold FRAME in FR1. destruct FR1 as [j1 FR1].
    assert (CT1 : bytes_at bsegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG1| exact CT|]. intros a Ha. left. right; right; left. exists (HB p A cap). split; [exact INLB|]. cbn. rewrite zbytes_length in Ha. lia. }
    pose proof (AI_hb_ids AI _ _ _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) (HB p A cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [ab_addr ab_size] in D. apply D. intros E. injection E. intros _ _ Eid.
      unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite Eid.
      apply in_flat_map. exists (HB p A cap). split; [exact INLB| left; reflexivity]. }
    (* [comment removed for export] *)
    assert (PB : bytes_at bsegs m1 PAY (zbytes payload)).
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
    { eapply unpoisoned_sub; [apply (ablock_unpoisoned m1 A cap SHA1); first [solve [clear -BQ4; Z.div_mod_to_equations; lia] | lia | clear -BQ4; Z.div_mod_to_equations; lia] | lia | lia]. }
    assert (UPb : unpoisoned m1 A' (A' + plen)).
    { apply (ablock_unpoisoned m1 A' plen SHN1); first [solve [clear -BN4; Z.div_mod_to_equations; lia] | lia | clear -BN4; Z.div_mod_to_equations; lia]. }
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
         | |- length _ = _ => rewrite zbytes_length; first [solve [clear - PLEN'; lia] | lia]   (* [comment removed for export] *)
         | |- app_blk _ _ => first [ eapply ablk_app_blk; [exact BN1| lia] | eapply ablk_app_blk; [eapply ablk_sub; [exact BQ1| unfold PAY; lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND in *; lia ]
         | |- unpoisoned _ _ _ => assumption
         | |- wr_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => assumption
         | |- rng _ lo _ => eapply rng_sub'; [exact RGstk1| lia]
         | |- rng _ PAY _ => eapply rng_sub'; [exact RGA1| lia]
         | |- rng _ _ _ => assumption
         | |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
         | |- _ + _ <= _ \/ _ + _ <= _ => first [solve [clear - DISJ EPAY EPP LC L0; lia] | unfold KHIGH in *; lia]   (* [comment removed for export] *)
         | |- _ => unfold KHIGH in *; lia
         end.
    cbv beta. intros ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & ST2 & NB2 & _).
    rewrite ?Hsp in MUc. rewrite ?Hsp in ST2. unname_sp.
    rewrite !(unsigned_lit A') in MUc, NB2 by lia. rewrite !(unsigned_lit plen) in MUc, NB2 by lia.
    replace (bv_unsigned sp + -80 - 2240) with (bv_unsigned sp + -2320) in MUc by lia.
    clear PB CT1 NBLK.   (* [comment removed for export] *)
    transport_after_call bsegs m1 m2 MUc WMc.
    fix_ret.
    assert (P2 : AHEAP AI L RNG1 (aps_m s1') (HB nb A' plen :: LB) m2).
    { eapply (AI_frame AI); [exact HEAP1| exact MUc| exact WMc|].
      pose proof (AI_layout AI _ _ _ _ _ HEAP1) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - right; left. exists (HB nb A' plen). split; [left; reflexivity| cbn; lia]. }
    assert (WLOW : forall a, a < 0x671000 \/ 0x7fff7000 <= a < 0x10007fff8000 -> outside [(bv_unsigned sp + -2320, bv_unsigned sp + -80); (A', A' + plen)] a).
    { intros a Ha. cbn. pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'. first [clear - Ha BN1' BN3 CEIL G3; atop_facts; lia| lia]. }
    assert (WBLK : forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> outside [(bv_unsigned sp + -2320, bv_unsigned sp + -80); (A', A' + plen)] a).
    { intros b a Hb R. cbn.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as D.
      cbn [ab_addr ab_size] in D. destruct (HLB b Hb) as (B1 & B2 & B3). atop_facts.
      assert (NE : HB nb A' plen <> b).
      { intros E. unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
        subst b. apply in_flat_map. exists (HB nb A' plen). split; [exact Hb| left; reflexivity]. }
      specialize (D NE). first [clear - D R B3 CEIL G3; lia| lia]. }
    assert (CST2 : client_static s1' (HB nb A' plen :: LB) m2).
    { eapply client_static_agree; [exact (magree_of_munch bsegs _ _ _ MUc WMc)| | | exact CST1].
      - intros a Ha. apply WLOW. unfold cstat_addr in Ha. lia.
      - intros pv Vv a EC HIN Ha. rewrite CL1 in EC. destruct (CL0LB pv EC) as (V0 & HIN0).
        destruct HIN as [E|HIN].
        + exfalso. assert (EQ : pv = nb) by (inversion E; reflexivity). subst pv.
          unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
          apply in_flat_map. exists (HB nb V0 8). split; [exact HIN0| left; reflexivity].
        + apply (WBLK (HB pv Vv 8) a HIN). cbn [ab_addr ab_size]. exact Ha. }
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
      - cbn [dptr]. apply (rw_cells_bytes_at bsegs) in NB2. cbn [cells_bytes cbytes app] in NB2. rewrite app_nil_r in NB2. exact NB2. }
    clear MUc WMc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0 x19 RNG1); [lia| lia| cbn; lia|].
      unfold RUNST0. do 16 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AINIT_FLAG, SM2; reflexivity|].
      split; [exact FRM|]. split; [| clear - DKM1 DK0; lia].
      split; [exists []; split; [left; split; [reflexivity| exact CL1]| split; [exact P2| exact CST2]]| split; [exact RG1| exact IV2]]. }
    cbv beta. intros b st' RNG' ms'' R. apply (run_tail s (Some (nb, A')) b RNG' st' ms'' CL0 R).
  Qed.
  (* [comment removed for export] *)
  Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : APS)
      (cdt thr sec : byte) (tm1 : word),
    AHEAP AI L RNG00 (aps_m s) LB m0 -> bytes_at bsegs m0 A (zbytes content) -> atrun_cells0 m0 -> harness_invA m0 ->
    client_static s LB m0 -> aps_cl s = cl0 ->
    ATEXIT TBL_MAIN m0 -> aincb 0 m0 -> rw_cells bsegs m0 0x66ec80 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    stk bsegs m0 lo usp -> mem_inv bsegs m0 -> frm0 fc ->
    stdout_file m0 (aps_so s) -> ssp_cells m0 canary -> aps_ok L s -> dk (aps_m s) <= 16 ->
    rclean m0 rstk -> rodata_sh0 m0 -> rclean m0 RBstdout ->
    tp = tpv -> a0 = wz (A + 2) -> a1 = wz Lc -> a2 = wz PAY -> a3 = wz plen ->
    rng RNG00 lo (usp + 128 - lo) -> rng RNG00 lo (al_top L - lo) -> rng_aimg RNG00 -> rng_aimg_sh RNG00 -> rng_fs L RNG00 ->
    rrng RNG00 rstk -> rrng RNG00 RFMT -> rrng RNG00 RBstdout ->
    implMA RNG00 (runA AAllocAsan cfg payload) s (POST s RNG00)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATARGET_RUN) fc None m0 (seg_rom bsegs)).
  Proof using ASHENV BOT CAP CEIL CI_WF CL0LB DFREE DFREEN DMALLOC DRV_CI EMIT FC FUZZ HLB HLBH HUL INLB L0 L6 LC LO RSceil RShi RSlo SP16 SPG SPHI UF0 UF1 UM0 UM1 URI_CI rng_fs_mono AHFRESH WRT0.
    intros until tm1. intros P0 CT TR0 HI0 CST0 CL0 ATX0 INCB0 LIBC0 ST0 MI0 FRM SO0 [GS0 GU0] RK DK0 RCS0 ROD0 RCB0 -> -> -> -> -> RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    pose proof LC as LC'. pose proof L6 as L6'. unfold zlength in LC', L6'.
    destruct (HLB _ INLB) as (BA1 & BA2 & BA3). cbn [ab_addr ab_size] in BA1, BA2, BA3.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0) as (_ & _ & GFI0 & _).
    apply implMA_from_evtF.
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact LIBC0| exact ATX0| exact INCB0| exact GFI0| exact RGstk| exact RGimg|].
    intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 MU WM MI1 IF1 ATX1 TX1.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    (* [comment removed for export] *)
    assert (OUT : forall a, (a < usp - 128 /\ ~ (AINIT_FLAG <= a < AINIT_FLAG + 1) /\ ~ (0x66ea48 <= a < 0x66ea4c) /\ ~ (0x66ea68 <= a < 0x66ea70)
                             /\ ~ (0x66eb68 <= a < 0x66eb70)) \/ usp <= a ->
                            outside [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)] a).
    { intros a Ha. unfold AINIT_FLAG in *. cbn. lia. }
    assert (AW : appW [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x66ea48, 0x66ea4c); (0x66ea68, 0x66ea70); (0x66eb68, 0x66eb70)]).
    { unfold appW, AINIT_FLAG. constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; unfold KLOW, KHIGH; lia|].
      constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; unfold KLOW, KHIGH; lia|].
      constructor; [cbn; unfold KLOW, KHIGH; lia| constructor]. }
    assert (P1 : AHEAP AI L RNG00 (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact P0| exact MU| exact WM|].
      pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (0x64dcd0, 0x64deb8). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; unfold AINIT_FLAG; lia].
      - left. right; left. exists (0x66ea40, 0x66ec60). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia].
      - left. right; left. exists (0x66ea40, 0x66ec60). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia].
      - left. right; left. exists (0x66ea40, 0x66ec60). split; [apply DRV_CI; cbn; tauto| cbn [fst snd]; lia]. }
    assert (CT1 : bytes_at bsegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. unfold AINIT_FLAG in *. lia. }
    assert (BA : BASE s m1).
    { split; [exact FR|]. split.
      { eapply harness_invA_magree; [exact AG| | exact HI0]. intros a Ha. apply OUT. unfold AINIT_FLAG. lia. }
      split; [eapply rodata_sh0_frame; [exact ROD0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB0| exact MU| exact WM| exact AW]|].
      split; [exact MI1|]. split; [exact ST1|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO0]. intros a Ha. apply OUT. left. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq in Ha. unfold AINIT_FLAG. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU0|]. intros a Ha. apply OUT. left. unfold ssp_guard, AINIT_FLAG in *. cbn in Ha. lia. }
      split; [| split; [exact TX1| exact ATX1]].
      intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT. unfold atrun_ivs in Hx. cbn [rin_ivs] in Hx. unfold AINIT_FLAG, ANEWH in *.
      destruct Hc as [Hc|Hs].
      - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
        + right. lia.
        + left. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
        + left. pose proof (HLB _ Hb) as (B1 & B2 & B3). atop_facts. lia.
        + left. rewrite shad_div. unfold ASHOFF.
          assert (R : 0 <= a' < 2^47).
          { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
            - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). unfold AIMG_HI in *. lia.
            - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. atop_facts. lia. }
          rewrite shad_div in Ha, Hx. unfold ASHOFF in Ha, Hx. Z.div_mod_to_equations. lia.
      - left. rewrite !shad_div in Hs. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
    assert (CST1 : client_static s LB m1).
    { eapply client_static_agree; [exact AG| | | exact CST0].
      - intros a Ha. apply OUT. left. unfold cstat_addr in Ha. unfold AINIT_FLAG. lia.
      - intros pv Vv a EC HIN Ha. apply OUT. left. pose proof (HLB _ HIN) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. unfold AINIT_FLAG. atop_facts. lia. }
    assert (PRE : PRE1 RNG00 s m1).
    { split; [exact P1|]. split; [| split; [exact BA| split; [exact CT1| split; [exact CST1| split; [exact CL0| exact DK0]]]]].
      unfold RNGS, rrng in *. repeat match goal with |- _ /\ _ => split end; first [assumption | apply fp_le_refl]. }
    pose proof (AI_block AI _ _ _ _ _ p A cap P1 INLB) as (_ & _ & RGA & _).
    clear AG OUT MU WM CT SO0 P0 ST0 MI0 TR0 HI0 RCS0 ROD0 RCB0 GS0 GU0 GFI0 ATX0 INCB0 LIBC0.
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
      pose proof (u8ro_read bsegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1
                    ltac:(unfold zbytes; rewrite nth_error_map, EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
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
  Qed.
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem atarget_run_proofA (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop) :
  (forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
  (forall iv, In iv drv_img_ranges -> In iv (aci AI)) -> (forall iv, In iv uri_img_ranges -> In iv (aci AI)) ->
  (forall iv, In iv (aci AI) -> 0 <= fst iv) ->
  dmalloc_stmt AI -> dfree_stmt AI -> dfree_null_stmt AI -> ashenv_law AI ->
  (forall L RNG st LB m, AHEAP AI L RNG st LB m -> AFRESH st) ->     (* [comment removed for export] *)
  fuzz_oneU_stmt AI rng_fs -> strnlen_a_stmt ->
  atarget_run_stmtA AI rng_fs.
Proof using .
  intros MONO DRV_CI URI_CI CI_WF DMALLOC DFREE DFREEN ASHENV AHFRESH FUZZ HSTRN.
  intros L RNG rstk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap Lc content lo canary cdt thr sec tm1.
  intros P0 INLB HLBH CT FC LC CAP L0 L6 TR0 HI0 CST0 ATXS0 LIBC0 ST0 BOT LO SPG SP16 SPHI MI0 FRM SO0 SSP RK DK0 WR0 RCS RSlo RShi RSceil ROD RCB -> -> -> -> -> HUL UM1 UF1 UM0 UF0
         RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
  destruct ATXS0 as (ATX0 & INCB0 & _).
  pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _).
  eapply (trun_main AI rng_fs MONO DRV_CI URI_CI DMALLOC DFREE DFREEN ASHENV AHFRESH FUZZ HSTRN L RNG rstk ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            m LB p A cap Lc content lo canary (aps_cl s) INLB HLBH FC LC CAP L0 L6 SP16 SPG BOT ltac:(lia) SPHI LO RSlo RShi RSceil HUL UM1 UF1 UM0 UF0
            (fun b Hb => AI_block_bounds AI _ _ _ _ _ b P0 Hb) CI_WF
            ltac:(intros p0 E0; exfalso; destruct CST0 as [CLN _]; rewrite E0 in CLN; discriminate CLN) WR0);
    first [ exact P0 | exact DK0 | exact CT | exact TR0 | exact HI0 | exact CST0 | exact ATX0 | exact INCB0 | exact LIBC0 | exact ST0 | exact MI0 | exact FRM | exact SO0 | exact SSP | exact RK
          | exact RCS | exact ROD | exact RCB | exact RGstk | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
          | exact RRS | exact RRF | exact RRB | reflexivity ].
Qed.
End CANSEC1.
