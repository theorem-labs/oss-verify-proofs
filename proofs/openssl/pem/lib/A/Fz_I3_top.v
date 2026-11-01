(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_libiface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_master1 Fz_T_sk Fz_T_mtl Fz_T_its Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_W5_rep Fz_W5_agr Fz_W2_exdc Fz_W5_env Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw Fz_I3_egsi Fz_I3_ibasew Fz_I3_ibase Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_fullw Fz_I3_full Fz_I3_eclw Fz_I3_eclear Fz_I3_gdcw Fz_I3_gdc Fz_I3_fxiw Fz_I3_fxi Fz_lib0 Fz_libA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition e_FI : Z := 0x1f307c.                (* [comment removed for export] *)
Definition FI_RET1 : Z := 0x1f3090. Definition FI_RET2 : Z := 0x1f3094. Definition FI_RET3 : Z := 0x1f30a0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fi_w0_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 FI_RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 0)
                 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ img_untouched m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [CB 8 j8; C8 rae]
    /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma fi_w0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> img_untouched m -> mem_inv asegs m ->
  evt asegs (fi_w0_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae F fc lo m)
    (MS (mkR rae sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_fuzz_init) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae F fc m lo
    STACK LO_HIGH LO_ROOM SP_TOP UNTOUCHED MINV.
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as KEEP.
  pose proof (wmono_refl asegs m) as GROW.
  lazymatch type of KEEP with munch ?W _ _ => assert (WIN_UT : ut_fp W) by ut_fp_lia end.
  th_frame 16%nat [8; 8]%nat STACK.
  unfold e_fuzz_init.
  zstep. zstep. zstep.
  do 3 zstep.
  apply evt_done. unfold fi_w0_post, FI_RET1, e_init_crypto.
  exists (firstn 8 junk). eexists.
  split; [reflexivity|].
  split; [exact KEEP|]. split; [exact GROW|]. split; [exact MINV|].
  split; [exact (ut_munch _ m _ UNTOUCHED KEEP WIN_UT)|].
  split; [exact FR|exact STACK].
Qed.

Lemma fi_w1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  img_untouched m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 FI_RET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_eclear) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 FI_RET1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FI_RET1) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m UNTOUCHED.
  unfold FI_RET1, FI_RET2, e_eclear.
  zstep.
  apply evt_done. reflexivity.
Qed.

Lemma fi_w2 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  img_untouched m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 FI_RET3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 e_fxi) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 FI_RET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FI_RET2) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m UNTOUCHED.
  unfold FI_RET2, FI_RET3, e_fxi.
  do 3 zstep.
  apply evt_done. reflexivity.
Qed.

Definition fi_w3_post (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR rae sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc rae) fc None m (seg_rom asegs)
            /\ stk asegs m lo (bv_unsigned sp).

Lemma fi_w3 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ra rae : word) (j8 : list byte)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -16) [CB 8 j8; C8 rae] -> mem_inv asegs m ->
  evt asegs (fi_w3_post sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FI_RET3) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra rae j8 F fc m lo
    BELOW LO_HIGH LO_ROOM SP_TOP UNTOUCHED SAVED MINV.
  unfold FI_RET3.
  do 4 zstep.
  pose proof (stk_release asegs m lo _ _ BELOW SAVED ltac:(lia)) as REJOINED.
  cbn [cells_size csize Nat.add] in REJOINED.
  apply evt_done. split; [reflexivity|].
  replace (bv_unsigned sp) with (bv_unsigned sp + -16 + Z.of_nat 16) by lia. exact REJOINED.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lh_repE_pos : forall GOBJ m L lh B g bks, lh_repE GOBJ m L lh B g bks -> forall p n, In (p, n) L -> 0 < n.
Proof.
  intros GOBJ m L lh B g bks (REP & PERM & _) p n Hin.
  pose proof (lh_geo_bounds g (proj1 REP)) as (GB & _).
  pose proof (Permutation_in _ PERM Hin) as H. cbn [In] in H. destruct H as [H|[H|H]]; [injection H; lia | injection H; lia |].
  apply in_map_iff in H as (x & E & _). injection E. lia.
Qed.

Lemma rw_u32 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> u32arr asegs m A ws.
Proof.
  intros m A cs ws CELLS BYTES SIZE. unfold rw_cells, cells_at in CELLS. unfold u32arr.
  rewrite <- BYTES. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (cells_size cs)) by (rewrite SIZE; lia). tauto.
Qed.
Lemma rw_u64 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> u64arr asegs m A ws.
Proof.
  intros m A cs ws CELLS BYTES SIZE. unfold rw_cells, cells_at in CELLS. unfold u64arr.
  rewrite <- BYTES. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (cells_size cs)) by (rewrite SIZE; lia). tauto.
Qed.
Lemma rw_u8 : forall (m : mem) A cs bs, rw_cells asegs m A cs -> cells_bytes cs = bs -> cells_size cs = length bs -> u8arr asegs m A bs.
Proof.
  intros m A cs bs CELLS BYTES SIZE. unfold rw_cells, cells_at in CELLS. unfold u8arr.
  rewrite <- SIZE, <- BYTES. tauto.
Qed.

Lemma es_at_rest_of_arrs : forall (m : mem) E, ecl_arrs m E 16 -> es_at_rest m E.
Proof.
  intros m E (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). cbn [Nat.sub repeat] in A0, A1, A2, A3, A4, A5, A6, A7, A8. rewrite app_nil_r in A0, A1, A2, A3, A4, A5, A6, A7, A8.
  exists (repeat (Z_to_bv 64 0) 16), (repeat (Z_to_bv 64 0) 16), (repeat (Z_to_bv 64 0) 16), (repeat ECL_LNW 16).
  split; [exact (rw_u32 m _ _ (repeat (Z_to_bv 64 0) 16) A0 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u32 m _ _ (repeat (Z_to_bv 64 0) 16) A1 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A2 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A3 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A4 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 64) A5 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A6 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u32 m _ _ (repeat ECL_LNW 16) A7 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A8 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact A9|]. lia.
Qed.


(* [comment removed for export] *)
Lemma outside_cover : forall (LW W : list (Z * Z)) (x : Z), outside LW x ->
  (forall lo hi, In (lo, hi) W -> (exists lo' hi', In (lo', hi') LW /\ lo' <= lo /\ hi <= hi') \/ ~ (lo <= x < hi)) -> outside W x.
Proof.
  intros LW W x Ho HW. induction W as [|[wl wh] W IH]; [exact I|]. cbn [outside]. split.
  - destruct (HW wl wh (or_introl eq_refl)) as [(lo' & hi' & Hin & H1 & H2)|H]; [| exact H]. intros Hx.
    clear - Ho Hin Hx H1 H2. induction LW as [|[u v] L IHL]; [destruct Hin|]. cbn [outside] in Ho. destruct Ho as [HO1 HO2].
    destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia | exact (IHL HO2 Hin)].
  - apply IH. intros lo1 hi1 Hin1. exact (HW lo1 hi1 (or_intror Hin1)).
Qed.

(* [comment removed for export] *)
Section PermApart.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma perm_live_apartF : forall Σ (m : mem) x rest y, ART RT Σ m -> Permutation (rt_live RT Σ) (x :: rest) -> In y rest ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m x rest y ART0 P Hy.
  pose proof (Permutation_in x (Permutation_sym P) (or_introl eq_refl)) as INx. destruct (in_split _ _ INx) as (A & B & E).
  assert (Hy' : In y (A ++ B)).
  { apply (Permutation_in y (l := rest)); [| exact Hy]. apply (@Permutation_cons_app_inv _ rest A B x). rewrite <- E. apply Permutation_sym. exact P. }
  destruct x as [p1 n1], y as [p2 n2]. exact (af_live_disj RT AF Σ m p1 n1 p2 n2 A B ART0 E Hy').
Qed.
End PermApart.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Finit.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_FULL : init_crypto_full_stmt RT GOBJ.
Hypothesis C_ECL : eclear_first_stmt RT.
Hypothesis C_FXI : fxi_stmt RT.
Variables FZ_SITES FZ_CALLS : list (Z * Z).

(* [comment removed for export] *)
Definition FI_SITES : list (Z * Z) := [(FI_RET1, e_FI); (FI_RET2, e_FI); (FI_RET3, e_FI)] ++ ICF_SITES ++ ECLR_SITES ++ FXI_SITES.
Definition FI_CALLS : list (Z * Z) :=
  [(FI_RET1, e_init_crypto); (FI_RET2, e_eclear); (FI_RET3, e_fxi); (FI_RET3, e_fxi_ex); (RA_INIT, e_fuzz_init); (RA_INIT, e_FI)] ++ ICF_CALLS ++ ECLR_CALLS ++ FXI_CALLS.
Hypothesis HCG : cg_sub FI_SITES FI_CALLS FZ_SITES FZ_CALLS.

Theorem fuzz_init_A : fuzz_init_cps RT LIB0_A LIB_A FZ_SITES FZ_CALLS.
Proof using AF AFP C_FULL C_ECL C_FXI HCG.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDFS MSTAB RA_IS TP_IS NOFRAMES LIVEPOS LIVEROOM CREDIT FPBAD CGHAS LIB0M SSP ERRNO ARTM0 MINV STACK
    LO_WIN LO_ROOM SP_TOP SP_ALIGN SP_SP0.
  subst tp. intros T c0 AT0 FINISH.
  pose proof (af_sp0_win RT AF Σ m ARTM0) as SP0_WIN.
  destruct (af_client_consts RT AF Σ m ARTM0) as (_ & _ & _ & _ & UNTOUCHED).
  unfold STACK_WIN, FUZZ_STACK, USTACK_TOP, CLI_MAX, FUZZ_LIVE, LIVE_MAX, INIT_COST in *.
  assert (SPF : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  destruct CGHAS as (HAVE_SITES & HAVE_CALLS). destruct HCG as (FI_SITES_IN & FI_CALLS_IN).
  assert (GRAPH_FI : cg_has (rt_cg RT Σ) FI_SITES FI_CALLS).
  { split; intros edge EDGE; [apply HAVE_SITES, FI_SITES_IN, EDGE | apply HAVE_CALLS, FI_CALLS_IN, EDGE]. }

  (* the statics and keys LIB0_A gives at entry *)
  destruct LIB0M as (STATICS & KEYS0).
  unfold lib0_statics in STATICS. rewrite !Forall_cons_iff in STATICS. cbn [fst snd] in STATICS.
  destruct STATICS as (R_SEC & R_ERRFLAG & R_ERRONCE & R_ERRHASH & R_ERRLOCK & R_ALLOW & R_7A0 & R_780 & R_760 & R_740 & R_720 & R_DC
    & R_560 & R_MKINIT & R_MKKEY & R_MKONCE & R_4E0 & R_4C0 & R_4A0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & R_LSRET & R_LSONCE & R_BRET & R_BONCE & R_OD & _ & R_IICL & R_INITLK & R_OPTSLK & R_STOP & R_BINITED
    & R_MEMSET & R_FREE & R_REALLOC & R_MALLOC & R_DTOR & _).
  destruct KEYS0 as (nk & j1 & w & sh & oldcb & u & NK_POS & J1_LO & J1_HI & NEXT0 & KLOCK0 & KEYW0 & J1_CHOICE
                     & KJ1_0 & KJ1A_0 & KJ1B_0 & KJ1C_0 & TJ1_0 & TJ1B_0 & TJ1C_0 & OCB0 & U0).
  destruct ERRNO as (errv & ERRNO0). unfold errno_cell in ERRNO0. rewrite unsigned_lit in ERRNO0 by lia.
  destruct SSP as (guard & _ & GUARD0).
  pose proof (proj1 (rw_cells_app m 5938976 [C4 (Z_to_bv 64 4294967295)] [C4 (Z_to_bv 64 4294967295)]) R_DTOR) as (DTORA0 & DTORB0).
  change (5938976 + Z.of_nat (cells_size [C4 (Z_to_bv 64 4294967295)])) with 5938980 in DTORB0.
  assert (DCB0 : rw_cells asegs m 12187008
            [C8 z64; C8 z64; CB 96 (zeros 96); C8 z64; CB 48 (zeros 48); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
             C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; CB 8 (zeros 8)]).
  { destruct R_DC as ((_ & DC_BYTES) & DC_WR). split; [split|].
    - vm_compute. repeat first [exact I | reflexivity | split].
    - lazymatch goal with |- bytes_at _ _ _ (cells_bytes ?L) =>
        replace (cells_bytes L) with (cells_bytes [CB 328 (zeros 328)]) by (vm_compute; reflexivity) end. exact DC_BYTES.
    - lazymatch goal with |- wr_at _ _ _ (Z.of_nat (cells_size ?L)) =>
        replace (cells_size L) with (cells_size [CB 328 (zeros 328)]) by (vm_compute; reflexivity) end. exact DC_WR. }
  clear R_DC R_DTOR.
  assert (ENV0 : cl_env m (Z_to_bv 8 0) guard).
  { split; [| split; [exact R_ALLOW | split; [left; reflexivity | exact (ssp_guard_rw m guard GUARD0)]]].
    unfold CL_RO, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, e_CRYPTO_malloc, e_CRYPTO_realloc, e_CRYPTO_free, e_wrap_memset.
    repeat (apply Forall_cons; [cbn [fst snd]; first [exact (proj1 R_MALLOC) | exact (proj1 R_REALLOC) | exact (proj1 R_FREE) | exact (proj1 R_MEMSET)] |]).
    apply Forall_nil. }

  (* fuzz_init entry: frame of 16, a0 = 2, a1 = 0, call OPENSSL_init_crypto *)
  pose proof (fi_w0 sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo
                    STACK ltac:(lia) ltac:(lia) ltac:(lia) UNTOUCHED MINV) as WALK0.
  cl_lift WALK0 AT0 c1 AT1.
  destruct (ASTA_unpack RT Σ _ _ c1 AT1) as (ms1 & (j8 & m1 & -> & KEEP1 & GROW1 & MINV1 & UT1 & SAVED1 & BELOW1) & HERE1). clear AT1.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (bv_unsigned sp - 16) ARTM0); [unfold STACK_WIN; lia | | exact GROW1].
    intros a NOT_CLIENT. apply KEEP1. cbn [outside]. split; [| exact I].
    intros IN_WIN. apply NOT_CLIENT. left. unfold USTACK_TOP. lia. }
  assert (LOW1 : forall X cs, rw_cells asegs m X cs -> 0 <= X -> X + Z.of_nat (cells_size cs) <= 12345344 -> rw_cells asegs m1 X cs).
  { intros X cs CELLS X_LO X_HI. apply (rw_cells_agree asegs m m1 X cs CELLS); [| exact GROW1].
    intros a IN_A. apply KEEP1. cbn [outside]. split; [lia | exact I]. }
  pose proof (LOW1 _ _ R_SEC ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SEC1.
  pose proof (LOW1 _ _ R_ERRFLAG ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ERRFLAG1.
  pose proof (LOW1 _ _ R_ERRONCE ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ERRONCE1.
  pose proof (LOW1 _ _ R_ERRHASH ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ERRHASH1.
  pose proof (LOW1 _ _ R_ERRLOCK ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ERRLOCK1.
  pose proof (LOW1 _ _ R_7A0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W7A0_1.
  pose proof (LOW1 _ _ R_780 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W780_1.
  pose proof (LOW1 _ _ R_760 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W760_1.
  pose proof (LOW1 _ _ R_740 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W740_1.
  pose proof (LOW1 _ _ R_720 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W720_1.
  pose proof (LOW1 _ _ DCB0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as DCB1.
  pose proof (LOW1 _ _ R_560 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as B560_1.
  pose proof (LOW1 _ _ R_MKINIT ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as MKINIT1.
  pose proof (LOW1 _ _ R_MKKEY ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as MKKEY1.
  pose proof (LOW1 _ _ R_MKONCE ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as MKONCE1.
  pose proof (LOW1 _ _ R_4E0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W4E0_1.
  pose proof (LOW1 _ _ R_4C0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W4C0_1.
  pose proof (LOW1 _ _ R_4A0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as W4A0_1.
  pose proof (LOW1 _ _ R_LSRET ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as LSRET1.
  pose proof (LOW1 _ _ R_LSONCE ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as LSONCE1.
  pose proof (LOW1 _ _ R_BRET ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as BRET1.
  pose proof (LOW1 _ _ R_BONCE ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as BONCE1.
  pose proof (LOW1 _ _ R_OD ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as OD1.
  pose proof (LOW1 _ _ R_IICL ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as IICL1.
  pose proof (LOW1 _ _ R_INITLK ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as INITLK1.
  pose proof (LOW1 _ _ R_OPTSLK ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as OPTSLK1.
  pose proof (LOW1 _ _ R_STOP ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as STOP1.
  pose proof (LOW1 _ _ R_BINITED ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as BINITED1.
  pose proof (LOW1 _ _ DTORA0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as DTORA1.
  pose proof (LOW1 _ _ DTORB0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as DTORB1.
  pose proof (LOW1 _ _ NEXT0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as NEXT1.
  pose proof (LOW1 _ _ KLOCK0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KLOCK1.
  pose proof (LOW1 _ _ KEYW0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KEYW1.
  pose proof (LOW1 _ _ KJ1_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KJ1_1.
  pose proof (LOW1 _ _ KJ1A_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KJ1A_1.
  pose proof (LOW1 _ _ KJ1B_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KJ1B_1.
  pose proof (LOW1 _ _ KJ1C_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as KJ1C_1.
  pose proof (LOW1 _ _ TJ1_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as TJ1_1.
  pose proof (LOW1 _ _ TJ1B_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as TJ1B_1.
  pose proof (LOW1 _ _ TJ1C_0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as TJ1C_1.
  pose proof (LOW1 _ _ OCB0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as OCB1.
  pose proof (LOW1 _ _ U0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as U1.
  pose proof (LOW1 _ _ ERRNO0 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as ERRNO1.
  assert (ENV1 : cl_env m1 (Z_to_bv 8 0) guard) by (apply (cl_env_seg _ m m1 _ guard ENV0 KEEP1); cl_fp_lia).
  assert (CALLOK1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -16)) lo).
  { unfold call_ok, RT_STACK, USTACK_TOP. rewrite SPF.
    split; [exact BELOW1|]. split; [exact LO_WIN|]. split; [lia|]. split; [lia|].
    replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SP_ALIGN. }
  assert (GRAPH_F : cg_has (rt_cg RT Σ) ICF_SITES ICF_CALLS) by (apply (cg_has_weaken _ _ _ _ _ GRAPH_FI); vm_compute; reflexivity).
  assert (CHOICE_F : (j1 = nk /\ w = z64) \/ (j1 = (nk + 1) mod 128 /\ bv_unsigned w <> 0)).
  { destruct J1_CHOICE as [(J_EQ & W_EQ) | (J_EQ & W_NZ)]; [left; split; assumption |].
    right. split; [rewrite Z.mod_small by lia; exact J_EQ | exact W_NZ]. }

  (* OPENSSL_init_crypto(OPENSSL_INIT_LOAD_CRYPTO_STRINGS, NULL) *)
  apply (cps_realizes asegs _ _ T c1
           (C_FULL Σ PMc (Z_to_bv 64 FI_RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
              (Z_to_bv 64 2) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (Z_to_bv 8 0) guard nk j1
              w errv sh z64 oldcb z64 z64 z64 z64 z64 z64 z64 (Z_to_bv 64 4294967295) z64 (Z_to_bv 8 0) u (Z_to_bv 8 0)
              FDFS MSTAB eq_refl eq_refl ART1 MINV1 CALLOK1 ltac:(rewrite SPF; unfold RT_STACK; lia) GRAPH_F
              ltac:(rewrite NOFRAMES; cbn; unfold FRAMES_MAX; lia) ltac:(unfold LIVE_MAX; lia) ltac:(lia)
              ltac:(apply Forall_forall; intros (p & n) IN_LIVE; exact (LIVEPOS p n IN_LIVE)) ENV1
              STOP1 OD1 BONCE1 LSONCE1 OCB1 OPTSLK1 INITLK1 DTORA1 IICL1 NEXT1 ltac:(lia) KLOCK1 KJ1_1 (proj1 KEYW1) CHOICE_F ltac:(lia) KJ1A_1
              BINITED1 BRET1 LSRET1 ERRNO1 MKONCE1 MKINIT1 MKKEY1 U1 KJ1B_1 TJ1B_1 ERRONCE1 ERRLOCK1 ERRHASH1 ERRFLAG1) HERE1).
  intros cF (ΣF & p1 & p2 & MK & SA & P & pk & lh & B & L' & g' & bks' & lbF & uF & ATF & PERMF & LEN_L & ITEMS & FRF & SP0F & CRF & CGF
             & P1_POS & P1_AL & P1_TOP & P2_POS & P2_AL & P2_TOP & MK_POS & MK_AL & MK_TOP & SA_POS & SA_AL & SA_TOP & P_POS & P_AL & P_TOP
             & PK_POS & PK_AL & PK_TOP).
  destruct (ASTA_unpack RT ΣF _ _ cF ATF)
    as (msF & (mF & BACKF & AFTERF & PRESF & ENVF & STOPF & ODF & BONCEF & LSONCEF & OCBF & OPTSLKF & INITLKF & P1MF & P2MF & DTORF & IICLF
               & KJ1F & KJ1AF & BINITEDF & BRETF & ERRNOF & MKONCEF & MKINITF & MKKEYF & NEXTF & KLOCKF & KJ1BF & UF & TJ1BF & MKF & SAF & PF
               & ERRSTF & PKMF & LHF & LSRETF) & HEREF).
  clear ATF.
  destruct BACKF as (t0_F & t1_F & t2_F & a1_F & a2_F & a3_F & a4_F & a5_F & a6_F & a7_F & t3_F & t4_F & t5_F & t6_F & F_F & fc_F & ->).
  rewrite (ret_pc_even FI_RET1) in HEREF by (unfold FI_RET1; try reflexivity; lia).
  destruct AFTERF as (ARTF & MINVF & BELOWF). rewrite SPF in BELOWF, PRESF.

  (* back at FI_RET1: what OPENSSL_init_crypto leaves alone, carried from m1 to mF *)
  assert (BSS : forall x, (5938440 <= x < 6722776 \/ 12186000 <= x < 12343248) -> ~ (12205720 <= x < 12205728) ->
                  ~ (12205800 <= x < 12205848) -> ~ (12205856 <= x < 12205872) -> ~ (12341912 <= x < 12341920) ->
                  ~ (12337584 <= x < 12337592) -> client_static x).
  { intros x IN_STATIC NOT1 NOT2 NOT3 NOT4 NOT5. split.
    - unfold CLIENT_STATIC. destruct IN_STATIC as [IN_DATA | IN_BSS].
      + exists 5938440, 6722776. split; [cbn [In]; left; reflexivity | exact IN_DATA].
      + exists 12186000, 12343248. split; [cbn [In]; right; right; left; reflexivity | exact IN_BSS].
    - intros (lo' & hi' & ROW & IN_ROW). unfold RT_STATIC in ROW. cbn [In] in ROW.
      repeat (destruct ROW as [ROW|ROW]; [injection ROW as <- <-; lia|]). exact ROW. }
  assert (PEEL : forall (mm : mem) (base : Z) (c : cell) (rest : list cell) (next : Z), rw_cells asegs mm base (c :: rest) ->
                   next = base + Z.of_nat (cells_size [c]) -> rw_cells asegs mm base [c] /\ rw_cells asegs mm next rest).
  { intros mm base c rest next CELLS ->. exact (proj1 (rw_cells_app mm base [c] rest) CELLS). }
  assert (CARRY_F : rw_cells asegs mF 12187744 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs mF 12187552 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF 12187520 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs mF 12187488 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF 12187456 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs mF 12187424 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF 12187008
            [C8 z64; C8 z64; CB 96 (zeros 96); C8 z64; CB 48 (zeros 48); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
             C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; CB 8 (zeros 8)]
      /\ rw_cells asegs mF 12186976 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs mF 12186848 [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF 12186816 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs mF 12186784 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF 5938980 [C4 (Z_to_bv 64 4294967295)]
      /\ rw_cells asegs mF (12340824 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs mF (12341912 + 8 * j1) [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs mF (12341912 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]).
  { repeat match goal with |- _ /\ _ => split end.
    all: eapply (Fz_G_kit2.wg_keep_static_nw _ _ _ _ m1 mF); [eassumption | exact PRESF |].
    all: intros x IN_CELL; cbn [cells_size csize Nat.add] in IN_CELL; clear - IN_CELL BSS J1_LO J1_HI.
    all: split; [apply BSS; lia |].
    all: cbn [ICF_W IB_W LS_W app outside].
    all: unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED,
           G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET.
    all: repeat split; lia. }
  destruct CARRY_F as (SEC_F & W7A0_F & W780_F & W760_F & W740_F & W720_F & DCB_F & B560_F & W4E0_F & W4C0_F & W4A0_F & DTORB_F
                       & KJ1C_F & TJ1_F & TJ1C_F).
  destruct (PEEL _ _ _ _ (MK + 24) MKF eq_refl) as (MKHEAD_F & MKREST_F).
  destruct (PEEL _ _ _ _ (MK + 32) MKREST_F ltac:(cbn [cells_size csize Nat.add]; lia)) as (MKSA_F & MKTAIL_F).
  destruct (PEEL _ _ _ _ (P + 8) PF eq_refl) as (PSLOT_F & PREST_F).
  pose proof (proj2 (rw_cells_app mF 5938976 [C4 (Z_to_bv 64 j1)] [C4 (Z_to_bv 64 4294967295)]) (conj DTORF DTORB_F)) as DKEY_F.
  assert (IN_F : forall blk, In blk ((pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ) -> In blk (rt_live RT ΣF)).
  { intros blk IN_BLK. apply (Permutation_in _ (Permutation_sym PERMF)). apply in_or_app. right. exact IN_BLK. }
  pose proof (Permutation_length PERMF) as LENF. rewrite length_app in LENF. cbn [length] in LENF.
  pose proof (afp_live_hi RT GOBJ AFP ΣF mF SA 32 ARTF (IN_F (SA, 32) ltac:(cbn [In]; tauto)) ltac:(lia)) as SA_HI.
  pose proof (afp_live_hi RT GOBJ AFP ΣF mF P 128 ARTF (IN_F (P, 128) ltac:(cbn [In]; tauto)) ltac:(lia)) as P_HI.
  pose proof (af_live_range RT AF ΣF mF SA 32 ARTF (IN_F (SA, 32) ltac:(cbn [In]; tauto))) as (_ & SA_BELOW & _).
  pose proof (af_live_range RT AF ΣF mF P 128 ARTF (IN_F (P, 128) ltac:(cbn [In]; tauto))) as (_ & P_BELOW & _).
  rewrite SP0F in SA_BELOW, P_BELOW. unfold STACK_WIN in SA_BELOW, P_BELOW.

  (* FI_RET1: ERR_clear_error *)
  destruct (af_client_consts RT AF ΣF mF ARTF) as (_ & _ & _ & _ & UT_F).
  assert (SAVED_F : rw_cells asegs mF (bv_unsigned sp + -16) [CB 8 j8; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 mF _ _ SAVED1). intros a IN_SLOT. cbn [cells_size csize Nat.add] in IN_SLOT. apply PRESF.
    - left. unfold USTACK_TOP. lia.
    - cbn [ICF_W IB_W LS_W app outside].
      unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED,
        G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET.
      repeat split; lia. }
  pose proof (fi_w1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) t0_F t1_F t2_F s0 s1 (Z_to_bv 64 1) a1_F a2_F a3_F a4_F a5_F
                    a6_F a7_F s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_F t4_F t5_F t6_F F_F fc_F mF UT_F) as WALK1.
  cl_lift WALK1 HEREF c2 AT2.
  assert (CALLOK_F : call_ok RT ΣF mF (Z_to_bv 64 (bv_unsigned sp + -16)) lo).
  { unfold call_ok, RT_STACK, USTACK_TOP. rewrite SPF, SP0F.
    split; [exact BELOWF|]. split; [exact LO_WIN|]. split; [lia|]. split; [lia|].
    replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SP_ALIGN. }
  assert (CTX_E : cg_ctx (rt_cg RT ΣF) e_eclear [bv_unsigned (Z_to_bv 64 FI_RET2)]).
  { rewrite CGF, unsigned_lit by (unfold FI_RET2; lia). split; [| exact I].
    apply (proj2 GRAPH_FI). unfold FI_CALLS. cbn [app In]. right. left. reflexivity. }
  assert (CHAIN_F : uw_chain mF (Z_to_bv 64 (bv_unsigned sp + -16)) s0 []).
  { cbn [uw_chain]. replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia. exact FPBAD. }
  assert (GRAPH_E : cg_has (rt_cg RT ΣF) ECLR_SITES ECLR_CALLS)
    by (rewrite CGF; apply (cg_has_weaken _ _ _ _ _ GRAPH_FI); vm_compute; reflexivity).
  assert (OD_EX : exists od : word, rw_cells asegs mF G_IC_OPTSDONE [C8 od] /\ Z.land (bv_unsigned od) 2 = 2)
    by (exists (Z_to_bv 64 OPT_LOAD_STRINGS); split; [exact ODF | vm_compute; reflexivity]).
  apply (cps_realizes asegs _ _ T c2
           (C_ECL ΣF PMc (Z_to_bv 64 FI_RET2) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) t0_F t1_F t2_F s0 s1 (Z_to_bv 64 1)
              a1_F a2_F a3_F a4_F a5_F a6_F a7_F s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_F t4_F t5_F t6_F F_F fc_F mF lo [] lbF guard
              (j1 + 2) j1 MK SA P z64 z64 (zeros 24) (zeros 40) (zeros 120) uF z64 z64 oldcb
              FDFS MSTAB eq_refl ARTF MINVF CALLOK_F ltac:(rewrite SPF; unfold RT_STACK; lia) CTX_E CHAIN_F GRAPH_E
              ltac:(rewrite FRF, NOFRAMES; cbn; unfold FRAMES_MAX; lia) ltac:(rewrite LENF; unfold LIVE_MAX; lia) ltac:(lia) ENVF
              STOPF OD_EX BONCEF BRETF MKONCEF MKKEYF
              ltac:(lia) TJ1BF (IN_F (MK, 72) ltac:(cbn [In]; tauto)) ltac:(Z.div_mod_to_equations; lia) MKHEAD_F MKSA_F MKTAIL_F
              (IN_F (SA, 32) ltac:(cbn [In]; tauto)) ltac:(Z.div_mod_to_equations; lia) SAF
              (IN_F (P, 128) ltac:(cbn [In]; tauto)) ltac:(Z.div_mod_to_equations; lia) PSLOT_F PREST_F
              DKEY_F ltac:(lia) ltac:(lia) TJ1_F UF W4A0_F W4C0_F W4E0_F OCBF) AT2).
  intros c3 (Σ2 & E & N & H & G & SK & LK & D & u2 & top2 & AT3 & LIVE2 & FR2 & SP02 & CR2 & CG2 & FRESH2).
  destruct (ASTA_unpack RT Σ2 _ _ c3 AT3)
    as (ms3 & (m2 & BACK2 & AFTER2 & PRES2 & ENV2 & TOP2 & SAH2 & PC2 & MKC2 & ARRS2 & DSL2 & U2 & W4A0_2 & W4C0_2 & W4E0_2 & OCB2
               & HC2 & NC2 & GC2 & SKC2 & LKC2 & DC2) & HERE3).
  clear AT3.
  destruct BACK2 as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & F2 & fc2 & ->).
  rewrite (ret_pc_even FI_RET2) in HERE3 by (unfold FI_RET2; try reflexivity; lia).
  destruct AFTER2 as (ART2 & MINV2 & WM2 & BELOW2). rewrite SPF in BELOW2, PRES2.
  destruct (af_client_consts RT AF Σ2 m2 ART2) as (_ & _ & _ & _ & UT2).

  (* what ERR_clear_error leaves alone, carried from mF to m2 *)
  assert (GDC59 : GDC_COST = 59) by (vm_compute; reflexivity).
  assert (CARRY_2 : rw_cells asegs m2 KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m2 NEXT_KEY [C4 (Z_to_bv 64 (j1 + 2))]
      /\ rw_cells asegs m2 (KEYS + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK_CLEAN)] /\ rw_cells asegs m2 (12340824 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs m2 (12341912 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m2 12187424 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs m2 12187456 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m2 12187488 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs m2 12187520 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m2 G_IC_STOPPED [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m2 G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)] /\ rw_cells asegs m2 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]
      /\ rw_cells asegs m2 G_IC_BASE_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m2 12186976 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m2 12187008
            [C8 z64; C8 z64; CB 96 (zeros 96); C8 z64; CB 48 (zeros 48); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
             C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; CB 8 (zeros 8)]
      /\ rw_cells asegs m2 12187552 [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m2 12187744 [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m2 ERRNO_A [C4 (sx32 errv)] /\ rw_cells asegs m2 MK_ONCE [C4 (Z_to_bv 64 2)]
      /\ rw_cells asegs m2 MK_KEY [C4 (Z_to_bv 64 (j1 + 2))] /\ rw_cells asegs m2 (12341912 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]).
  { repeat match goal with |- _ /\ _ => split end.
    all: eapply (Fz_G_kit2.wg_keep_static_nw _ _ _ _ mF m2); [eassumption | exact PRES2 |].
    all: intros x IN_CELL; cbn [cells_size csize Nat.add] in IN_CELL; clear - IN_CELL BSS J1_LO J1_HI SA_HI P_HI.
    all: unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in IN_CELL.
    all: split; [apply BSS; lia | cbn [EG_W MTL_W outside]; unfold G_ALLOW_CUST; repeat split; lia]. }
  destruct CARRY_2 as (KLOCK2 & NEXT2 & KJ1B_2 & KJ1C_2 & TJ1C_2 & W720_2 & W740_2 & W760_2 & W780_2 & STOP2 & OD2 & BONCE2 & BRET2
                       & B560_2 & DCB_2 & W7A0_2 & SEC2 & ERRNO2 & MKONCE2 & MKKEY2 & TJ1B_2).
  assert (SAVED2 : rw_cells asegs m2 (bv_unsigned sp + -16) [CB 8 j8; C8 ra]).
  { apply (rw_cells_agree_nw asegs mF m2 _ _ SAVED_F). intros a IN_SLOT. cbn [cells_size csize Nat.add] in IN_SLOT. apply PRES2.
    - left. unfold USTACK_TOP. lia.
    - cbn [EG_W MTL_W outside]. unfold G_ALLOW_CUST. repeat split; lia. }
  destruct (PEEL _ _ _ _ 12187016 DCB_2 eq_refl) as (D580_2 & DCREST).
  destruct (PEEL _ _ _ _ 12187024 DCREST eq_refl) as (D588_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187120 DCREST eq_refl) as (_ & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187128 DCREST eq_refl) as (IP12_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187176 DCREST eq_refl) as (_ & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187184 DCREST eq_refl) as (DC628_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187192 DCREST eq_refl) as (DC630_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187200 DCREST eq_refl) as (DC638_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187208 DCREST eq_refl) as (DC640_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187216 DCREST eq_refl) as (DC648_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187224 DCREST eq_refl) as (DC650_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187232 DCREST eq_refl) as (DC658_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187240 DCREST eq_refl) as (DC660_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187248 DCREST eq_refl) as (DC668_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187256 DCREST eq_refl) as (DC670_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187264 DCREST eq_refl) as (DC678_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187272 DCREST eq_refl) as (DC680_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187280 DCREST eq_refl) as (DC688_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187288 DCREST eq_refl) as (DC690_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187296 DCREST eq_refl) as (DC698_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187304 DCREST eq_refl) as (DC6A0_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187312 DCREST eq_refl) as (DC6A8_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187320 DCREST eq_refl) as (DC6B0_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  destruct (PEEL _ _ _ _ 12187328 DCREST eq_refl) as (DC6B8_2 & DCREST').  clear DCREST. rename DCREST' into DCREST.
  clear DCREST.

  (* FI_RET2: a0 = 0, a1 = -1, the call at 0x1f309c *)
  pose proof (fi_w2 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 s0 s1 (Z_to_bv 64 (E + 896))
                    a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_2 t4_2 t5_2 t6_2 F2 fc2 m2 UT2) as WALK2.
  cl_lift WALK2 HERE3 c4 AT4.
  assert (CALLOK2 : call_ok RT Σ2 m2 (Z_to_bv 64 (bv_unsigned sp + -16)) lo).
  { unfold call_ok, RT_STACK, USTACK_TOP. rewrite SPF, SP02, SP0F.
    split; [exact BELOW2|]. split; [exact LO_WIN|]. split; [lia|]. split; [lia|].
    replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SP_ALIGN. }
  assert (CTX_X : cg_ctx (rt_cg RT Σ2) e_fxi_ex [bv_unsigned (Z_to_bv 64 FI_RET3)]).
  { rewrite CG2, CGF, unsigned_lit by (unfold FI_RET3; lia). split; [| exact I].
    apply (proj2 GRAPH_FI). unfold FI_CALLS. cbn [app In]. right. right. right. left. reflexivity. }
  assert (CHAIN2 : uw_chain m2 (Z_to_bv 64 (bv_unsigned sp + -16)) s0 []).
  { cbn [uw_chain]. replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia. exact FPBAD. }
  assert (GRAPH_X : cg_has (rt_cg RT Σ2) FXI_SITES FXI_CALLS)
    by (rewrite CG2, CGF; apply (cg_has_weaken _ _ _ _ _ GRAPH_FI); vm_compute; reflexivity).
  assert (POS_F : forall p n, In (p, n) (rt_live RT ΣF) -> 0 < n).
  { intros p n IN_LIVE. apply (Permutation_in _ PERMF) in IN_LIVE. apply in_app_or in IN_LIVE as [IN_L | IN_SIX].
    - exact (lh_repE_pos GOBJ mF L' lh B g' bks' LHF p n IN_L).
    - cbn [In] in IN_SIX. repeat (destruct IN_SIX as [IN_SIX | IN_SIX]; [injection IN_SIX as <- <-; lia |]).
      exact (LIVEPOS p n IN_SIX). }
  assert (POS2 : Forall (fun blk : Z * Z => 0 < snd blk) (rt_live RT Σ2)).
  { rewrite LIVE2. apply Forall_app. split.
    - repeat (apply Forall_cons; [cbn [snd]; lia |]). apply Forall_nil.
    - apply Forall_forall. intros (p & n) IN_LIVE. exact (POS_F p n IN_LIVE). }
  assert (COUNT2 : Z.of_nat (length (rt_live RT Σ2)) + 124 <= LIVE_MAX)
    by (rewrite LIVE2, length_app, LENF; cbn [length]; unfold LIVE_MAX; lia).
  assert (J_PICK : (j1 + 3 = j1 + 2 /\ Z_to_bv 64 MK_CLEAN = z64) \/ (j1 + 3 = (j1 + 2 + 1) mod 128 /\ bv_unsigned (Z_to_bv 64 MK_CLEAN) <> 0)).
  { right. split; [rewrite Z.mod_small by lia; lia | rewrite unsigned_lit by lia; lia]. }
  apply (cps_realizes asegs _ _ T c4
           (C_FXI Σ2 PMc (Z_to_bv 64 FI_RET3) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 s0 s1
              (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_2 t4_2 t5_2 t6_2 F2 fc2 m2 lo []
              (Z_to_bv 8 1) guard (j1 + 2) (j1 + 3) sh z64 (Z_to_bv 64 MK_CLEAN) z64 oldcb (Z_to_bv 8 0) z64 z64
              z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 (Z_to_bv 64 OPT_LOAD_STRINGS)
              eq_refl eq_refl eq_refl FDFS MSTAB ART2 MINV2 ENV2 POS2 COUNT2
              ltac:(rewrite FR2, FRF, NOFRAMES; cbn; unfold FRAMES_MAX; lia) ltac:(rewrite CR2, GDC59; lia)
              CALLOK2 ltac:(rewrite SPF; unfold RT_STACK; lia) CTX_X CHAIN2 GRAPH_X
              KLOCK2 NEXT2 ltac:(lia) ltac:(lia) (proj1 KJ1B_2) J_PICK ltac:(lia) KJ1C_2 (proj1 TJ1C_2)
              W720_2 W740_2 W760_2 W780_2 OCB2 STOP2 OD2 BONCE2 BRET2 B560_2 D580_2 D588_2
              DC628_2 DC630_2 DC638_2 DC640_2 DC648_2 DC650_2 DC658_2 DC660_2 DC668_2 DC670_2 DC678_2 DC680_2 DC688_2 DC690_2 DC698_2 DC6A0_2 DC6A8_2 DC6B0_2 DC6B8_2 W7A0_2) AT4).
  intros c5 (Σ3 & lk & xd & AT5 & DCB_LK & DCB_XD & XD_AL & FR3 & SP03 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c5 AT5)
    as (ms5 & (m3 & BACK3 & AFTER3 & PRES3 & ENV3 & KLOCK3 & NEXT3 & KJ_3 & DCKEY3 & DCONCE1_3 & DCRET1_3 & DCONCE2_3 & OCB3
               & DCINIT3 & D580_3 & LKC3 & D588_3 & XDC3 & DCRET2_3) & HERE5).
  clear AT5.
  destruct BACK3 as (t0_3 & t1_3 & t2_3 & a1_3 & a2_3 & a3_3 & a4_3 & a5_3 & a6_3 & a7_3 & t3_3 & t4_3 & t5_3 & t6_3 & F3 & fc3 & ->).
  rewrite (ret_pc_even FI_RET3) in HERE5 by (unfold FI_RET3; try reflexivity; lia).
  destruct AFTER3 as (ART3 & MINV3 & BELOW3). rewrite SPF in BELOW3, PRES3.
  destruct (af_client_consts RT AF Σ3 m3 ART3) as (_ & _ & _ & _ & UT3).

  (* what fxi leaves alone, carried from m2 to m3 *)
  destruct (PEEL _ _ _ _ (MK + 24) MKC2 eq_refl) as (_ & MKREST2).
  destruct (PEEL _ _ _ _ (MK + 32) MKREST2 ltac:(cbn [cells_size csize Nat.add]; lia)) as (MKSA2 & _).
  destruct (PEEL _ _ _ _ (P + 8) PC2 eq_refl) as (PNODE2 & _).
  pose proof (afp_live_hi RT GOBJ AFP ΣF mF MK 72 ARTF (IN_F (MK, 72) ltac:(cbn [In]; tauto)) ltac:(lia)) as MK_HI.
  assert (IN_2 : forall blk, In blk ((pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ) -> In blk (rt_live RT Σ2)).
  { intros blk IN_BLK. rewrite LIVE2. apply in_or_app. right. exact (IN_F blk IN_BLK). }
  pose proof (proj1 (Forall_forall _ _) FRESH2 (E, 904) ltac:(cbn [In]; do 6 right; left; reflexivity)) as (E_HI & E_AL & E_TOP).
  cbn [fst snd] in E_HI, E_AL, E_TOP.
  assert (CARRY_3 : rw_cells asegs m3 12187744 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m3 12187120 [C8 z64]
      /\ rw_cells asegs m3 (12341912 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m3 G_IC_STOPPED [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m3 G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)] /\ rw_cells asegs m3 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]
      /\ rw_cells asegs m3 G_IC_BASE_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m3 MK_ONCE [C4 (Z_to_bv 64 2)]
      /\ rw_cells asegs m3 MK_KEY [C4 (Z_to_bv 64 (j1 + 2))] /\ rw_cells asegs m3 (12341912 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]
      /\ rw_cells asegs m3 ERRNO_A [C4 (sx32 errv)]).
  { repeat match goal with |- _ /\ _ => split end.
    all: eapply (Fz_G_kit2.wg_keep_static_nw _ _ _ _ m2 m3); [eassumption | exact PRES3 |].
    all: intros x IN_CELL; cbn [cells_size csize Nat.add] in IN_CELL; clear - IN_CELL BSS J1_LO J1_HI.
    all: unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in IN_CELL.
    all: split; [apply BSS; lia | cbn [GDC_W outside]; unfold G_ALLOW_CUST; repeat split; lia]. }
  destruct CARRY_3 as (SEC3 & IP12_3 & TJ1C_3 & STOP3 & OD3 & BONCE3 & BRET3 & MKONCE3 & MKKEY3 & TJ1B_3 & ERRNO3).
  assert (MKSA3 : rw_cells asegs m3 (MK + 24) [C8 (Z_to_bv 64 SA)]).
  { apply (Fz_G_kit2.wg_keep_live_nw _ _ _ _ m2 m3 MK 72 _ _ MKSA2 PRES3 (IN_2 (MK, 72) ltac:(cbn [In]; tauto))); [lia | cbn; lia |].
    intros x IN_CELL. cbn [cells_size csize Nat.add] in IN_CELL. cbn [GDC_W outside]. unfold G_ALLOW_CUST. repeat split; lia. }
  assert (SAH3 : rw_cells asegs m3 SA (sa_hdr (Z_to_bv 64 1) z64 top2 (Z_to_bv 64 1) (Z_to_bv 64 P))).
  { apply (Fz_G_kit2.wg_keep_live_nw _ _ _ _ m2 m3 SA 32 _ _ SAH2 PRES3 (IN_2 (SA, 32) ltac:(cbn [In]; tauto))); [lia | unfold sa_hdr; cbn; lia |].
    intros x IN_CELL. unfold sa_hdr in IN_CELL. cbn [cells_size csize Nat.add] in IN_CELL. cbn [GDC_W outside]. unfold G_ALLOW_CUST.
    repeat split; lia. }
  assert (PNODE3 : rw_cells asegs m3 P [C8 (Z_to_bv 64 E)]).
  { apply (Fz_G_kit2.wg_keep_live_nw _ _ _ _ m2 m3 P 128 _ _ PNODE2 PRES3 (IN_2 (P, 128) ltac:(cbn [In]; tauto))); [lia | cbn; lia |].
    intros x IN_CELL. cbn [cells_size csize Nat.add] in IN_CELL. cbn [GDC_W outside]. unfold G_ALLOW_CUST. repeat split; lia. }
  assert (REST3 : errst_at_rest E [] m3).
  { apply (errst_rest_agree m2 m3 E [] (conj eq_refl (es_at_rest_of_arrs m2 E ARRS2))).
    intros a [IN_E | (p & n & [] & _)]. apply PRES3.
    - right. right. left. exists E, 904. split; [rewrite LIVE2; apply in_or_app; left; cbn [In]; do 6 right; left; reflexivity | exact IN_E].
    - cbn [GDC_W outside]. unfold G_ALLOW_CUST. repeat split; lia. }
  assert (SAVED3 : rw_cells asegs m3 (bv_unsigned sp + -16) [CB 8 j8; C8 ra]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ SAVED2). intros a IN_SLOT. cbn [cells_size csize Nat.add] in IN_SLOT. apply PRES3.
    - left. unfold USTACK_TOP. lia.
    - cbn [GDC_W outside]. unfold G_ALLOW_CUST. repeat split; lia. }

  (* FI_RET3: a0 = 1, return *)
  pose proof (fi_w3 sp gp (Z_to_bv 64 TP_A) t0_3 t1_3 t2_3 s0 s1 (Z_to_bv 64 0) a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3_3 t4_3 t5_3 t6_3 (Z_to_bv 64 FI_RET3) ra j8 F3 fc3 m3 lo BELOW3 ltac:(lia) ltac:(lia) ltac:(lia) UT3 SAVED3 MINV3) as WALK3.
  cl_lift WALK3 HERE5 c6 AT6.
  pose proof (stk_release asegs m3 lo _ _ BELOW3 SAVED3 ltac:(lia)) as STACK3.
  cbn [cells_size csize Nat.add] in STACK3. replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in STACK3 by lia.

  (* the blocks this call leaves live, and the facts the post asks of them *)
  destruct DCB_XD as (news & LIVE3 & NEWS_LEN & NEWS_OK & XD_NEW).
  assert (XD_IN3 : In (xd, 40) (rt_live RT Σ3)) by (rewrite LIVE3; apply in_or_app; left; exact XD_NEW).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m3 xd 40 ART3 XD_IN3 ltac:(lia)) as XD_HI.
  destruct (in_split _ _ XD_NEW) as (news_pre & news_post & NEWS_SPLIT).
  assert (XD_APART : forall q nq, In (q, nq) (rt_live RT Σ2) -> xd + 40 <= q \/ q + nq <= xd).
  { intros q nq IN_OLD. apply (af_live_disj RT AF Σ3 m3 xd 40 q nq news_pre (news_post ++ rt_live RT Σ2) ART3).
    - rewrite LIVE3, NEWS_SPLIT, <- app_assoc. reflexivity.
    - apply in_or_app. right. apply in_or_app. right. exact IN_OLD. }
  assert (APART_F : forall q nq, In (q, nq) [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)] ->
                      forall p n, In (p, n) (rt_live RT Σ) -> q + nq <= p \/ p + n <= q).
  { intros q nq NEW p n OLD. destruct (in_split _ _ NEW) as (pre & post & SPLIT6).
    apply (perm_live_apartF RT AF ΣF mF (q, nq) (L' ++ pre ++ post ++ rt_live RT Σ) (p, n) ARTF).
    - eapply Permutation_trans; [exact PERMF |].
      change (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ)
        with (L' ++ [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)] ++ rt_live RT Σ).
      rewrite SPLIT6.
      replace (L' ++ (pre ++ (q, nq) :: post) ++ rt_live RT Σ) with ((L' ++ pre) ++ (q, nq) :: (post ++ rt_live RT Σ))
        by (rewrite <- !app_assoc; reflexivity).
      apply Permutation_sym, Permutation_cons_app. rewrite <- !app_assoc. apply Permutation_refl.
    - apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact OLD. }

  (* cli_pres: nothing of the caller outside LIB_W changed, step by step back to m *)
  assert (CLI3 : cli_pres (rt_live RT Σ) (bv_unsigned sp) m m3).
  { intros a CLIENT OUT_LIB.
    assert (CL_UP : forall live' frames', incl (rt_live RT Σ) live' -> aclient live' frames' (bv_unsigned sp + -16) (bv_unsigned a)).
    { intros live' frames' INCL.
      destruct CLIENT as [AT_STACK | [AT_STATIC | [(p & n & IN_OLD & IN_BLK) | [(f & k & [] & _) | (f & k & [] & _)]]]].
      - left. unfold USTACK_TOP in *. lia.
      - right. left. exact AT_STATIC.
      - right. right. left. exists p, n. split; [apply INCL; exact IN_OLD | exact IN_BLK]. }
    assert (INCL_F : incl (rt_live RT Σ) (rt_live RT ΣF)).
    { intros blk IN_OLD. apply IN_F. cbn [In]. do 6 right. exact IN_OLD. }
    assert (INCL_2 : incl (rt_live RT Σ) (rt_live RT Σ2)).
    { intros blk IN_OLD. rewrite LIVE2. apply in_or_app. right. exact (INCL_F blk IN_OLD). }
    assert (NOT_NEW : forall q nq, In (q, nq) [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)] -> 17594333495296 <= q ->
                        ~ (q <= bv_unsigned a < q + nq)).
    { intros q nq NEW Q_HI IN_Q.
      pose proof (af_live_range RT AF ΣF mF q nq ARTF (IN_F (q, nq) ltac:(cbn [In] in NEW |- *; tauto))) as (_ & Q_BELOW & _).
      rewrite SP0F in Q_BELOW. unfold STACK_WIN in Q_BELOW.
      destruct CLIENT as [AT_STACK | [AT_STATIC | [(p & n & IN_OLD & IN_BLK) | [(f & k & [] & _) | (f & k & [] & _)]]]].
      - lia.
      - apply client_static_range in AT_STATIC. unfold SEGTOP_A in AT_STATIC. lia.
      - destruct (APART_F q nq NEW p n IN_OLD); lia. }
    cbn [LIB_W outside] in OUT_LIB.
    rewrite (PRES3 a (CL_UP _ _ INCL_2)) by (cbn [GDC_W outside]; unfold G_ALLOW_CUST; repeat split; lia).
    rewrite (PRES2 a (CL_UP _ _ INCL_F)).
    2: { cbn [EG_W MTL_W outside]. unfold G_ALLOW_CUST. split; [| split; [| repeat split; lia]].
         - intros IN_SA. apply (NOT_NEW SA 32 ltac:(cbn [In]; tauto) SA_HI). lia.
         - intros IN_P. apply (NOT_NEW P 128 ltac:(cbn [In]; tauto) P_HI). lia. }
    rewrite (PRESF a (CL_UP _ _ (incl_refl _))).
    2: { cbn [ICF_W IB_W LS_W app outside].
         unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED,
           G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET.
         repeat split; lia. }
    apply KEEP1. cbn [outside]. split; [| exact I]. intros IN_FRAME.
    destruct CLIENT as [AT_STACK | [AT_STATIC | [(p & n & IN_OLD & IN_BLK) | [(f & k & [] & _) | (f & k & [] & _)]]]].
    - lia.
    - apply client_static_range in AT_STATIC. unfold SEGTOP_A in AT_STATIC. lia.
    - pose proof (af_live_range RT AF Σ m p n ARTM0 IN_OLD) as (_ & OLD_BELOW & _). unfold STACK_WIN in OLD_BELOW. lia. }

  (* LIB_A at the return: the error-state chain, the default context and its lock *)
  set (CL := news ++ [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ++ L'
             ++ [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)]).
  assert (LIBA3 : LIB_A CL m3).
  { destruct ENV3 as (CLRO3 & ALLOW3 & _ & _).
    split; [exact CLRO3 |]. split; [exact ALLOW3 |]. split; [exact SEC3 |].
    exists E, [(MK, 72); (SA, 32); (P, 128); (xd, 40)].
    split; [| split; [exact REST3 | split; [| split]]].
    - exists (Z_to_bv 64 OPT_LOAD_STRINGS), (j1 + 2), MK, SA, P, 1, z64, top2, (Z_to_bv 64 1), (j1 + 3), xd.
      split; [reflexivity |].
      split; [exact (conj STOP3 (conj OD3 (conj BONCE3 BRET3))) |].
      split.
      { split; [exact MKONCE3 |]. split; [exact MKKEY3 |]. split; [lia |]. split; [exact TJ1B_3 |]. split; [exact MKSA3 |].
        split; [exact SAH3 |]. split; [rewrite unsigned_lit by lia; lia |]. split; [lia | exact PNODE3]. }
      split; [Z.div_mod_to_equations; lia |]. split; [Z.div_mod_to_equations; lia |].
      split; [Z.div_mod_to_equations; lia |]. split; [Z.div_mod_to_equations; lia |].
      split.
      { split; [exact (proj1 DCINIT3) |]. split; [exact (proj1 DCKEY3) |]. split; [lia |].
        split; [exact (proj1 DCONCE1_3) |]. split; [exact (proj1 DCRET1_3) |]. split; [exact (proj1 DCONCE2_3) |].
        split; [exact (proj1 DCRET2_3) |]. split; [exact (proj1 TJ1C_3) |]. split; [exact (proj1 D588_3) |].
        split; [exact XD_AL | exact (proj1 IP12_3)]. }
      split; [exact XDC3 |]. split; [lia |].
      split; [exact (XD_APART MK 72 (IN_2 (MK, 72) ltac:(cbn [In]; tauto))) |].
      split; [exact (XD_APART SA 32 (IN_2 (SA, 32) ltac:(cbn [In]; tauto))) |].
      exact (XD_APART P 128 (IN_2 (P, 128) ltac:(cbn [In]; tauto))).
    - unfold CL. apply in_or_app. right. apply in_or_app. left. cbn [In]. do 6 right. left. reflexivity.
    - intros blk IN_LBL. unfold CL. cbn [In] in IN_LBL.
      destruct IN_LBL as [<- | [<- | [<- | [<- | []]]]].
      + do 3 (apply in_or_app; right). cbn [In]. do 3 right. left. reflexivity.
      + do 3 (apply in_or_app; right). cbn [In]. do 2 right. left. reflexivity.
      + do 3 (apply in_or_app; right). cbn [In]. right. left. reflexivity.
      + apply in_or_app. left. exact XD_NEW.
    - cbn [In]. intros [SAME | [SAME | [SAME | [SAME | []]]]]; injection SAME; lia. }

  apply FINISH. exists Σ3, CL.
  split.
  { unfold ASTA in AT6 |- *. apply (AST_conseq _ _ _ _ _ _ _ AT6); [| tauto].
    intros ms (AT_RET & _). exists m3.
    split; [exists t0_3, t1_3, t2_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, t3_3, t4_3, t5_3, t6_3, F3, fc3; exact AT_RET |].
    split; [exact (conj ART3 (conj MINV3 STACK3)) |].
    split; [exact CLI3 |]. split; [exact LIBA3 |].
    exists (sx32 errv). unfold errno_cell. rewrite unsigned_lit by lia. exact ERRNO3. }
  split.
  { rewrite LIVE3, LIVE2. unfold CL. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. exact PERMF. }
  split; [unfold CL, CLI_MAX; rewrite !length_app; cbn [length]; lia |].
  split.
  { intros p n IN_CL. unfold CL in IN_CL.
    apply in_app_or in IN_CL as [IN_NEWS | IN_CL].
    - pose proof (proj1 (Forall_forall _ _) NEWS_OK (p, n) IN_NEWS) as (_ & _ & _ & POS_N). exact POS_N.
    - apply in_app_or in IN_CL as [IN_ECL | IN_CL].
      + cbn [In] in IN_ECL. repeat (destruct IN_ECL as [IN_ECL | IN_ECL]; [injection IN_ECL as <- <-; lia |]). destruct IN_ECL.
      + apply in_app_or in IN_CL as [IN_L | IN_SIX].
        * exact (lh_repE_pos GOBJ mF L' lh B g' bks' LHF p n IN_L).
        * cbn [In] in IN_SIX. repeat (destruct IN_SIX as [IN_SIX | IN_SIX]; [injection IN_SIX as <- <-; lia |]). destruct IN_SIX. }
  split; [rewrite FR3, FR2, FRF; exact NOFRAMES |].
  split; [rewrite SP03, SP02; exact SP0F |].
  split; [rewrite CR3, CR2, GDC59; unfold INIT_COST; lia |].
  rewrite CG3, CG2. exact CGF.
Qed.
End Finit.
