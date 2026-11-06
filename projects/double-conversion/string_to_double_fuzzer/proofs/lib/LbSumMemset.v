(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface Hoare.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxOrder LxOrderWf.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceB AsRtLib MemsetLib BothMemset_code BothMemset LaState LaMem LaStep LaCheck LbSem LaWf LbSoundVal LbSoundAlu LbSoundMem LbSoundMem2 LbSoundStep LbSoundMatch LbSoundExplore LbGlue.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac clear_ors := repeat match goal with H : context [or] |- _ => clear H end.
Ltac lia_nd := first [ solve [ clear_ors; lia_fast ] | lia_fast ].
#[local] Ltac Lia.lia ::= lia_nd.
Import ListNotations.
Import LXL LAS LAM LAI LAC LBSEM LAWF LBSV LBSM LBSM2.
Open Scope Z_scope.

Module LBSUMS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_eta : forall ms : machine_state,
  ms_svc_pending ms = None -> ms_resv ms = None ->
  ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [regs fregs pc svc resv fcsr mem rom] Hs Hr. cbn in *. subst. reflexivity. Qed.

Lemma w64_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
Proof.
  intros a. apply bv_eq. unfold w64. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_ext : forall segs (m m' : word -> option byte) n a,
  (forall i, 0 <= i < Z.of_nat n -> m' (w64 (a + i)) = m (w64 (a + i))) ->
  rdn segs m' (w64 a) n = rdn segs m (w64 a) n.
Proof.
  intros segs m m' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn]. pose proof (Hag 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
  rewrite w64_succ. rewrite (IH (a + 1)) by (intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hag; lia).
  reflexivity.
Qed.

Lemma havoc_regs_get : forall rs i j,
  list_get (havoc_regs rs i) j Top = if existsb (Nat.eqb (i + j)%nat) keep_regs then list_get rs j Top else Top.
Proof.
  induction rs as [|v r IH]; intros i j; cbn [havoc_regs list_get].
  - destruct (existsb _ _); reflexivity.
  - destruct j as [|j]; [rewrite Nat.add_0_r; reflexivity|].
    rewrite IH. replace (S i + j)%nat with (i + S j)%nat by lia. reflexivity.
Qed.

Lemma list_get_below : forall rs n r, forallb (fun v => aval_below v n) rs = true -> aval_below (list_get rs r Top) n = true.
Proof.
  induction rs as [|v l IH]; intros n r H; [destruct r; reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. destruct r; cbn [list_get]; [exact H1 | apply IH; exact H2].
Qed.

Lemma keep_cs : forall k : nat, existsb (Nat.eqb k) keep_regs = true -> In (Z.of_nat k) cs_regs.
Proof.
  intros k H. apply existsb_exists in H as (k' & Hin & E). apply Nat.eqb_eq in E. subst k'.
  unfold keep_regs in Hin. unfold cs_regs. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn; tauto|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_rom : forall segs ms w ms',
  drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms w ms' H. unfold decode_exec_accesses in H.
  destruct (is_ecall w); [cbn in H; injection H as <-; reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
  match type of H with context [interp_eff_accesses ?a ?b ?c] => destruct (interp_eff_accesses a b c) as [rep| |] end; try discriminate.
  destruct rep as [[c m] acc]. cbn in H. injection H as <-. reflexivity.
Qed.

Lemma step_rom : forall segs ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  unfold fetch_failure in H. destruct (negb _); [discriminate|].
  match type of H with context [if ?t then MachineFault else MachineUnmodeled] => destruct t; discriminate end.
Qed.

Lemma msteps_rom : forall segs ms ms', msteps segs ms ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [reflexivity|].
  rewrite IH. eapply step_rom. exact Hstep.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inrng (lo hi : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) &&& Z.ltb (bv_unsigned x) hi)%bool.
Definition patch (m mf : word -> option byte) (r : Z * Z) : word -> option byte :=
  fun x => if inrng (fst r) (snd r) x then mf x else m x.
Fixpoint patches (m mf : word -> option byte) (rs : list (Z * Z)) : word -> option byte :=
  match rs with [] => m | r :: rs' => patches (patch m mf r) mf rs' end.

Lemma inrng_spec : forall lo hi x, inrng lo hi x = true <-> lo <= bv_unsigned x < hi.
Proof.
  intros lo hi x. unfold inrng. split.
  - intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - intros H. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Definition between (m mf mi : word -> option byte) : Prop := forall x, mi x = m x \/ mi x = mf x.

Lemma patches_end : forall rs m mf mi,
  between m mf mi -> (forall x : word, ~ LibIface.in_ranges (bv_unsigned x) rs -> mf x = mi x) -> forall x, patches mi mf rs x = mf x.
Proof.
  induction rs as [|[lo hi] rs IH]; intros m mf mi HB HOUT x; cbn [patches].
  - symmetry. apply HOUT. intros (r & [] & _).
  - apply (IH m mf).
    + intros y. unfold patch. cbn [fst snd]. destruct (inrng lo hi y); [right; reflexivity | apply HB].
    + intros y Hn. unfold patch. cbn [fst snd]. destruct (inrng lo hi y) eqn:E; [reflexivity|].
      apply HOUT. intros (r & [<-|Hr] & Hin); [|apply Hn; exists r; split; [exact Hr | exact Hin]].
      cbn [fst snd] in Hin. apply (proj2 (inrng_spec lo hi y)) in Hin. rewrite Hin in E. discriminate.
Qed.

Lemma patch_between : forall m mf mi r, between m mf mi -> between m mf (patch mi mf r).
Proof. intros m mf mi r HB x. unfold patch. destruct (inrng _ _ x); [right; reflexivity | apply HB]. Qed.

Lemma patch_wr_agree : forall m mf mi lo hi,
  between m mf mi -> (forall (x : word) b, m x = Some b -> exists b', mf x = Some b') ->
  0 <= lo -> lo <= hi -> hi <= 2 ^ 64 ->
  LBSM2.wr_agree mi (patch mi mf (lo, hi)) lo (hi - lo).
Proof.
  intros m mf mi lo hi HB GR H0 H1 H2. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros x Hx. unfold patch. cbn [fst snd]. destruct (inrng lo hi x) eqn:E; [|reflexivity].
    apply inrng_spec in E. exfalso. apply Hx. lia.
  - intros x b Hb. unfold patch. cbn [fst snd]. destruct (inrng lo hi x); [|exists b; exact Hb].
    destruct (HB x) as [E|E]; rewrite E in Hb; [exact (GR x b Hb) | exists b; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma three_in_length : forall {A} (l : list A) (a b c : A),
  In a l -> In b l -> In c l -> a <> b -> b <> c -> a <> c -> (3 <= length l)%nat.
Proof.
  intros A l a b c Ha Hb Hc Hab Hbc Hac.
  assert (TWO : forall (l' : list A) x y, In x l' -> In y l' -> x <> y -> (2 <= length l')%nat).
  { intros l'. induction l' as [|z r IH]; intros x y Hx Hy Hxy; [destruct Hx|]. cbn.
    destruct Hx as [<-|Hx]; destruct Hy as [E|Hy]; [congruence| | |].
    - destruct r; [destruct Hy|]. cbn; lia.
    - destruct r; [destruct Hx|]. cbn; lia.
    - specialize (IH x y Hx Hy Hxy). lia. }
  revert Ha Hb Hc. induction l as [|z r IH]; intros Ha Hb Hc; [destruct Ha|]. cbn.
  destruct Ha as [<-|Ha]; [pose proof (TWO r b c ltac:(destruct Hb; [congruence|assumption]) ltac:(destruct Hc; [congruence|assumption]) Hbc); lia|].
  destruct Hb as [<-|Hb]; [pose proof (TWO r a c Ha ltac:(destruct Hc; [congruence|assumption]) Hac); lia|].
  destruct Hc as [<-|Hc]; [pose proof (TWO r a b Ha Hb Hab); lia|].
  specialize (IH Ha Hb Hc). lia.
Qed.

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?P => change P with (hide P) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Summaries.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Variable FS : Z.
  Hypothesis UOK : uenv_ok U.
  Hypothesis SEGS : ue_segs U = SEGS_B.
  Hypothesis RO : ue_ro U = RO_B.
  Hypothesis TP : ue_tp U = TP_B.
  Hypothesis MEMSET : ue_memset U = ms_base.
  Hypothesis CBDPC : ue_cbd_pc U = CBD_ENTRY_B.
  Hypothesis CBDFR : ue_cbd_fr U = CBD_FR_B.
  (* [comment removed for export] *)
  Hypothesis RTCOV : forall a b, In (a, b) RT_B -> bm_get (ue_rt U) a = Some b.
  Hypothesis GSHCOV : forall a b, In (a, b) GSH_B -> bm_get (ue_gsh U) a = Some b.
  Let segs := ue_segs U.
  Let fs_consts := LBSM2.fs_consts.
  Let frame_geom := LBSM2.frame_geom FS.

  (* [comment removed for export] *)
  #[using="Type"] Lemma reg_ok : forall rho S ms r, R U G FS M0 rho S ms -> (1 <= r < 32)%nat ->
    val_ok rho (getreg S r) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r))).
  Proof.
    intros rho S ms r HR Hr. unfold getreg. destruct (Nat.eqb_spec r 0); [lia|].
    rewrite <- (LBG.getr_reg_get (ms_regs ms) r Hr). exact (r_regs _ _ _ _ _ _ _ HR r Hr).
  Qed.

  #[using="Type"] Lemma reg_lit : forall rho S ms r z, R U G FS M0 rho S ms -> (1 <= r < 32)%nat -> reg_is_lit S r z = true ->
    getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = w64 z.
  Proof.
    intros rho S ms r z HR Hr H. pose proof (reg_ok rho S ms r HR Hr) as V. unfold reg_is_lit in H.
    destruct (getreg S r) as [|l| |]; try discriminate. apply leqb_sound in H. subst l. cbn in V. rewrite lconst_sound in V.
    rewrite V. apply w64_snorm.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS RTCOV"] Lemma R_rt_ok : forall rho S ms, R U G FS M0 rho S ms -> rt_ok_B (ms_mem ms).
  Proof.
    intros rho S ms HR a b Hin. destruct (r_rt _ _ _ _ _ _ _ HR a b (RTCOV a b Hin)) as [Hb Hrd].
    exists [Z_to_bv 8 b]. unfold segs in Hrd. rewrite SEGS in Hrd. split; [exact Hrd|].
    rewrite LBSM2.bytes_le_cons. change (bytes_le_to_Z []) with 0. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_small by lia. lia.
  Qed.
  #[using="GSHCOV"] Lemma R_gsh_ok : forall rho S ms, R U G FS M0 rho S ms -> gsh_ok_B (ms_mem ms).
  Proof. intros rho S ms HR a b Hin. exact (proj2 (r_gsh _ _ _ _ _ _ _ HR a b (GSHCOV a b Hin))). Qed.
  #[using="SEGS RO"] Lemma R_ro_ok : forall rho S ms, R U G FS M0 rho S ms -> ro_ok SEGS_B RO_B (ms_mem ms).
  Proof.
    intros rho S ms HR a b Ha Hm. rewrite <- SEGS, <- RO in *. apply (proj2 (proj2 (r_abs _ _ _ _ _ _ _ HR)) a b); [|exact Hm].
    apply LBG.in_ranges_rangesZ. exact Ha.
  Qed.
  #[using="fs_consts"] Lemma malloc_ctx_mono : forall wlo whi wlo' whi' m, malloc_ctx_ok_B wlo whi FS m -> wlo <= wlo' -> whi' <= whi -> malloc_ctx_ok_B wlo' whi' FS m.
  Proof.
    intros wlo whi wlo' whi' m (CTX & THR & DT & H1 & H2 & H3 & H4 & H5 & B1 & B2 & B3 & B4 & C1 & C2 & C3) Hlo Hhi.
    exists CTX, THR, DT. repeat (split; [assumption|]). unfold ctx_cell_ok, app_mem in *. clear - H1 H2 H3 H4 H5 B1 B2 B3 B4 C1 C2 C3 Hlo Hhi. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma live_at_dec : forall rho frs k p, live_at FS rho frs k p \/ ~ live_at FS rho frs k p.
  Proof.
    intros rho frs k p. induction frs as [|f r IH].
    - right. intros (h & [] & _).
    - destruct (Z.eq_dec (f_cls f) k) as [E|NE];
        [destruct (Z_le_gt_dec 0 p); [destruct (Z_lt_le_dec p (fs_N (f_cls f)));
          [destruct (Z.eq_dec (64 * rho (f_sym f)) (fs_frame FS (f_cls f) p));
            [destruct (Z.eq_dec (rho (f_flag f)) (fs_flag FS (f_cls f) p))|]|]|]|].
      1: { left. exists f. split; [left; reflexivity|]. split; [exact E|]. split; [lia|]. split; assumption. }
      all: destruct IH as [(h & Hin & Hk & Hat)|NO]; [left; exists h; split; [right; exact Hin | split; assumption]|];
           right; intros (h & [<-|Hin] & Hk & (Q1 & Q2 & Q3)); [subst; try lia; try congruence | apply NO; exists h; repeat split; try assumption; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="UOK"] Lemma R_wr_same : forall rho st ms m' A n,
    R U G FS M0 rho st ms -> LBSM2.wr_agree (ms_mem ms) m' A n -> LBSM2.wclass FS (rho SYM_SP0 - FR_A) (rho SYM_SP0) A n ->
    (forall x, A <= x < A + n -> priv U FS (rho SYM_SP0) x) -> 0x688000 <= A ->   (* [comment removed for export] *)
    (forall c, In c (s_stk st) -> - ue_fr U <= c_off c -> c_off c + c_w c <= 0 -> rho SYM_SP0 + c_off c + c_w c <= A \/ A + n <= rho SYM_SP0 + c_off c) ->
    (forall a, In a (s_arrs st) -> - ue_fr U <= ar_lo a -> ar_hi a <= 0 -> rho SYM_SP0 + ar_hi a <= A \/ A + n <= rho SYM_SP0 + ar_lo a) ->
    (rho SYM_N <= 0 \/ rho SYM_DATA + rho SYM_N <= A \/ A + n <= rho SYM_DATA) ->
    frames_ok U FS rho m' (s_frames st) ->
    R U G FS M0 rho st (ms_with_mem ms m').
  Proof.
    intros rho st ms m' A n HR HW WC PRIV HA CELLS ARRS PAY FRS.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
    eapply (LBSM2.R_wr U G M0 FS UOK rho st st ms m' A n HR HW WC PRIV); try reflexivity.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell. pose proof Hcell as (C1 & C2 & _).
      eapply LBSM2.cell_ok_wr; [exact HW | exact Hcell | lia | lia | apply CELLS; [exact Hc | exact C1 | exact C2]].
    - apply Forall_forall. intros a Ha. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) a Ha) as Harr. pose proof Harr as (C1 & C2 & _).
      eapply LBSM2.arr_okg_wr; [exact HW | exact Harr | lia | lia | apply ARRS; [exact Ha | exact C1 | exact C2]].
    - eapply LBSM2.payload_ok_wr; [exact HW | exact (r_pay _ _ _ _ _ _ _ HR) | lia | lia | exact PAY].
    - eapply LBSM2.abs_ok_wr; [exact UOK | exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | exact HA].
    - intros Hlo. exfalso. pose proof HW as (_ & _ & Wn & _). lia.
    - exact FRS.
  Qed.

  (* [comment removed for export] *)
  #[using="UOK fs_consts"] Lemma R_mem_ext : forall rho st ms m', R U G FS M0 rho st ms -> (forall x, m' x = ms_mem ms x) -> R U G FS M0 rho st (ms_with_mem ms m').
  Proof.
    intros rho st ms m' HR EXT.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR. rewrite EFR in Rsp0. unfold FR_A in Rsp0.
    assert (HW : LBSM2.wr_agree (ms_mem ms) m' (rho SYM_SP0) 0).
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [intros x _; apply EXT | intros x b Hb; exists b; rewrite EXT; exact Hb]. }
    pose proof (proj1 (proj2 (r_pay _ _ _ _ _ _ _ HR))) as P2. rewrite EFR in P2. unfold FR_A in P2.
    eapply R_wr_same; [exact HR | exact HW | left; unfold FR_A; lia | intros x Hx; lia | lia | intros; lia | intros; lia | lia |].
    pose proof (r_apart _ _ _ _ _ _ _ HR) as (AP1 & AP2 & AP3 & AP4 & AP5). pose proof (fo_hi _ _ (r_fs _ _ _ _ _ _ _ HR)) as HI.
    unfold KHI_A, HIEND_A, FR_A, FS_LEN in AP1, AP2, AP4, HI.
    eapply LBSM2.frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | unfold FS_LEN, FS_FLAGS; lia | ].
    right. destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _ & HSH). unfold sh. rewrite ESH, HSH. unfold SHB.
    assert (FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia). lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint pat (w : nat) : Z := match w with O => 0 | S w' => 1 + 256 * pat w' end.
  #[using="Type"] Lemma bytes_le_repeat : forall c w, 0 <= c < 256 -> bytes_le_to_Z (repeat (Z_to_bv 8 c) w) = c * pat w.
  Proof.
    intros c w Hc. induction w as [|w IH]; cbn [repeat pat]; [change (bytes_le_to_Z []) with 0; lia|].
    rewrite LBSM2.bytes_le_cons, IH. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
  Qed.
  #[using="Type"] Lemma pat_bound : forall w, 0 <= pat w /\ 255 * pat w + 1 = 2 ^ (8 * Z.of_nat w).
  Proof.
    induction w as [|w [IH1 IH2]]; [split; [cbn; lia | reflexivity]|]. cbn [pat]. split; [lia|].
    rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat w)) with (8 + 8 * Z.of_nat w) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fill_cells_spec : forall fuel cs off n c x,
    In x (fill_cells cs off n c fuel) ->
    In x cs \/ (exists w : nat, (w = 8 \/ w = 4 \/ w = 2 \/ w = 1)%nat /\ c_w x = Z.of_nat w /\ off <= c_off x /\ c_off x + c_w x <= off + Z.of_nat n
                             /\ c_val x = alit (c * pat w)).
  Proof.
    induction fuel as [|fuel IH]; intros cs off n c x H; cbn [fill_cells] in H; [left; exact H|].
    destruct (Nat.eqb n 0) eqn:En; [left; exact H|].
    set (w := (if Nat.leb 8 n then 8 else if Nat.leb 4 n then 4 else if Nat.leb 2 n then 2 else 1)%nat) in H.
    assert (Hw : (w = 8 \/ w = 4 \/ w = 2 \/ w = 1)%nat /\ (w <= n)%nat).
    { subst w. apply Nat.eqb_neq in En. destruct (Nat.leb_spec 8 n); [split; [auto|lia]|]. destruct (Nat.leb_spec 4 n); [split; [auto|lia]|].
      destruct (Nat.leb_spec 2 n); [split; [auto|lia]|]. split; [auto|lia]. }
    destruct Hw as [Hw Hwn].
    destruct (IH _ _ _ _ _ H) as [Hin | (w' & Hw' & E1 & E2 & E3 & E4)].
    - unfold cells_store in Hin. destruct Hin as [<- | Hin].
      + right. exists w. cbn [c_w c_off c_val]. split; [exact Hw|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
        f_equal. f_equal. subst w. destruct Hw as [E|[E|[E|E]]]; rewrite E; reflexivity.
      + left. exact (proj1 (LBSM2.cells_kill_spec _ _ _ _ Hin)).
    - right. exists w'. split; [exact Hw'|]. split; [exact E1|]. split; [lia|]. split; [lia | exact E4].
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma fill_cells_old : forall fuel cs off n c x,
    In x (fill_cells cs off n c fuel) -> In x cs -> (forall y, In y cs -> c_off y + c_w y <= off \/ off + Z.of_nat n <= c_off y) ->
    c_off x + c_w x <= off \/ off + Z.of_nat n <= c_off x.
  Proof. intros fuel cs off n c x _ Hin H. apply H. exact Hin. Qed.

  #[using="Type"] Lemma firstn_skipn_repeat : forall {A} (b : A) n i k, (i + k <= n)%nat -> firstn k (skipn i (repeat b n)) = repeat b k.
  Proof.
    intros A b n. induction n as [|n IH]; intros i k H.
    - destruct i, k; try reflexivity; cbn in H; lia.
    - destruct i as [|i]; cbn [repeat skipn].
      + destruct k as [|k]; [reflexivity|]. cbn [firstn repeat]. f_equal. specialize (IH 0%nat k ltac:(lia)). cbn [skipn] in IH. exact IH.
      + apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma memset_space_ok : forall rho m b lo hi cs ars off n c cs' ars',
    0 <= c < 256 -> 0 <= n -> 0 <= b + lo -> b + hi <= 2 ^ 62 ->
    Forall (cell_ok U rho m b lo hi) cs -> Forall (arr_okg U rho m b lo hi) ars ->
    memset_space lo hi cs ars off n c = Some (cs', ars') ->
    lo <= off /\ off + n <= hi /\ ars' = ars /\
    Forall (cell_ok U rho (wbytes m (w64 (b + off)) (repeat (Z_to_bv 8 c) (Z.to_nat n))) b lo hi) cs' /\
    Forall (arr_okg U rho (wbytes m (w64 (b + off)) (repeat (Z_to_bv 8 c) (Z.to_nat n))) b lo hi) ars'.
  Proof.
    intros rho m b lo hi cs ars off n c cs' ars' Hc Hn Hb0 Hb62 Hcs Hars H.
    unfold memset_space in H. destruct (in_win lo hi off n) eqn:Win; cbn [negb] in H; [|discriminate].
    apply LBSMT.in_win_sound in Win. destruct Win as [Win1 Win2].
    destruct (arrs_overlap_lit ars off n) eqn:Eov; [discriminate|]. injection H; intros <- <-.
    split; [exact Win1|]. split; [exact Win2|]. split; [reflexivity|].
    pose proof (repeat_length (Z_to_bv 8 c) (Z.to_nat n)) as Hlen.
    split.
    - apply Forall_forall. intros x Hx.
      destruct (fill_cells_spec _ _ _ _ _ _ Hx) as [Hold | (w & Hw & E1 & E2 & E3 & E4)].
      + destruct (LBSM2.cells_kill_spec _ _ _ _ Hold) as [Hin Hov]. apply LBSM2.overlaps_false in Hov.
        apply LBSM2.cell_ok_store; rewrite ?Hlen, ?Z2Nat.id by lia; [lia | lia | exact (proj1 (Forall_forall _ _) Hcs x Hin) | lia | lia | lia].
      + rewrite Z2Nat.id in E3 by lia. unfold cell_ok. split; [lia|]. split; [lia|]. split; [lia|].
        exists (repeat (Z_to_bv 8 c) w). split.
        * replace (b + c_off x) with (b + off + Z.of_nat (Z.to_nat (c_off x - off))) by lia. rewrite E1, Nat2Z.id.
          pose proof (LBSM2.st_hit U m (b + off) (repeat (Z_to_bv 8 c) (Z.to_nat n)) ltac:(lia) ltac:(lia) ltac:(rewrite Hlen; lia)) as HIT. rewrite Hlen in HIT.
          rewrite (LBSM2.rdn_sub U _ (b + off) (Z.to_nat n) _ (Z.to_nat (c_off x - off)) w HIT) by lia.
          rewrite firstn_skipn_repeat by lia. reflexivity.
        * rewrite E4, E1. unfold alit, val_bytes_ok. rewrite repeat_length. split; [reflexivity|].
          rewrite lconst_sound, bytes_le_repeat by lia. destruct (pat_bound w) as [P0 P1].
          assert (M64 : forall z, (snorm z) mod 2 ^ (8 * Z.of_nat w) = z mod 2 ^ (8 * Z.of_nat w)).
          { intros z. rewrite <- (LBSA.mod_mod_pow2_le (snorm z) (8 * Z.of_nat w) 64), <- (LBSA.mod_mod_pow2_le z (8 * Z.of_nat w) 64) by lia. rewrite snorm_mod. reflexivity. }
          rewrite M64. symmetry. apply Z.mod_small. nia.
    - apply Forall_forall. intros a Ha. apply LBSM2.arr_okg_store; rewrite ?Hlen, ?Z2Nat.id by lia; [lia | lia | exact (proj1 (Forall_forall _ _) Hars a Ha) | | lia | lia].
      destruct (LBSM2.arrs_overlap_lit_false _ _ _ _ Eov Ha); lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma list_fill_length : forall n bs t c, length (list_fill bs t n c) = length bs.
  Proof. induction n as [|n IH]; intros; cbn [list_fill]; [reflexivity | rewrite IH, LBSM2.length_list_set; reflexivity]. Qed.
  #[using="Type"] Lemma list_fill_out : forall n bs t c u, (u < t \/ t + n <= u)%nat -> nth_error (list_fill bs t n c) u = nth_error bs u.
  Proof. induction n as [|n IH]; intros bs t c u H; cbn [list_fill]; [reflexivity|]. rewrite IH by lia. apply LBSM2.nth_list_set_ne. lia. Qed.
  #[using="Type"] Lemma list_fill_in : forall n bs t c u, (t <= u < t + n)%nat -> (u < length bs)%nat -> nth_error (list_fill bs t n c) u = Some c.
  Proof.
    induction n as [|n IH]; intros bs t c u H Hl; [lia|]. cbn [list_fill]. destruct (Nat.eq_dec u t) as [->|NE].
    - rewrite list_fill_out by lia. apply LBSM2.nth_list_set_eq. exact Hl.
    - apply IH; [lia | rewrite LBSM2.length_list_set; exact Hl].
  Qed.
  #[using="Type"] Lemma bm_get_fill : forall n bm a c x,
    bm_get (LAC.bm_fill bm a n c) x = if (Z.leb a x &&& Z.ltb x (a + Z.of_nat n))%bool then Some c else bm_get bm x.
  Proof.
    induction n as [|n IH]; intros bm a c x; cbn [LAC.bm_fill].
    - destruct (Z.leb_spec a x); [destruct (Z.ltb_spec x (a + Z.of_nat 0)); [lia|]|]; reflexivity.
    - rewrite IH, LBSM2.bm_get_set.
      destruct (Z.leb_spec (a + 1) x); [destruct (Z.ltb_spec x (a + 1 + Z.of_nat n))|]; cbn;
        destruct (Z.eqb_spec x a); destruct (Z.leb_spec a x); try lia; try (destruct (Z.ltb_spec x (a + Z.of_nat (S n))); try lia); reflexivity.
  Qed.
  #[using="Type"] Lemma nth_repeat_bv : forall (b d : byte) n k, (k < n)%nat -> nth k (repeat b n) d = b.
  Proof. intros b d n. induction n as [|n IH]; intros [|k] H; cbn; try lia; [reflexivity | apply IH; lia]. Qed.

  #[using="UOK fs_consts"] Lemma R_stack_fill : forall rho st ms o n bs stk' ars',
    wf_state st = true -> R U G FS M0 rho st ms ->
    - ue_fr U <= o -> o + n <= 0 -> 0 <= n -> length bs = Z.to_nat n ->
    let m' := wbytes (ms_mem ms) (w64 (rho SYM_SP0 + o)) bs in
    Forall (stack_cell_ok U rho m' (rho SYM_SP0)) stk' ->
    Forall (arr_ok U rho m' (rho SYM_SP0)) ars' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + o)) (Z.to_nat n) = true /\
    R U G FS M0 rho (set_arrs (set_stk st stk') ars') (ms_with_mem ms m').
  Proof.
    intros rho st ms o n bs stk' ars' Hwf HR Ho1 Ho2 Hn Hlen m' Hstk Hars. subst m'.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (r_win _ _ _ _ _ _ _ HR) as Rwin. pose proof (uo_frA U UOK) as EFR.
    set (sp0 := rho SYM_SP0) in *. set (A := sp0 + o) in *.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length bs) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite LBSM2.w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (proj1 Rwin (bv_unsigned x) ltac:(lia)) as [b Hb]. rewrite w64_of_unsigned in Hb.
      unfold wview. rewrite Hb. discriminate. }
    pose proof (LBSM2.wbytes_wr_agree (ms_mem ms) A bs HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (LBSM2.R_geom U G M0 FS _ _ _ HR) as GE. pose proof (LBSM2.geom_facts FS _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    eapply (LBSM2.R_wr U G M0 FS UOK rho st _ ms _ A n HR HW); cbn; try reflexivity.
    - left. rewrite EFR in Ho1. lia.
    - intros x Hx. left. lia.
    - exact Hstk.
    - exact Hars.
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      eapply LBSM2.payload_ok_wr; [exact HW | exact P | lia | lia | destruct P as (_ & P2 & _); lia].
    - eapply LBSM2.abs_ok_wr; [exact UOK | exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | lia].
    - intros Hlo. exfalso. lia.
    - eapply LBSM2.frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | rewrite EFR in Ho1; unfold FR_A in *; lia |].
      right. rewrite F7, HSH. unfold SHB. rewrite EFR in Ho1. unfold FR_A in *. lia.
  Qed.

  #[using="UOK fs_consts frame_geom"] Lemma R_frame_fill : forall rho st ms i f o n bs cs' ars',
    wf_state st = true -> R U G FS M0 rho st ms -> nth_frame (s_frames st) i = Some f ->
    0 <= o -> o + n <= f_size f -> 0 <= n -> length bs = Z.to_nat n ->
    let m' := wbytes (ms_mem ms) (w64 (64 * rho (f_sym f) + o)) bs in
    Forall (cell_ok U rho m' (64 * rho (f_sym f)) 0 (f_size f)) cs' ->
    Forall (arr_okg U rho m' (64 * rho (f_sym f)) 0 (f_size f)) ars' ->
    store_ok segs (ms_mem ms) (w64 (64 * rho (f_sym f) + o)) (Z.to_nat n) = true /\
    R U G FS M0 rho (set_frames st (upd_frame (s_frames st) i (frame_set_space f cs' ars'))) (ms_with_mem ms m').
  Proof.
    intros rho st ms i f o n bs cs' ars' Hwf HR Hn Ho1 Ho2 Hnn Hlen m' Hcs Hars. subst m'.
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (LBSM2.frames_nth U FS rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin).
    pose proof Hf0 as ((Hp0 & Hb0 & Hfl0) & Hk & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p0 Hk Hp0) as (G1 & G2 & G3 & G4 & G5 & G6). rewrite HFR in G1. rewrite HLEN in G2.
    destruct (LBSM2.f_size_cls f Hk) as [E1 E2]. rewrite E1 in Ho2, Hcs, Hars.
    pose proof (LBSM2.R_geom U G M0 FS _ _ _ HR) as GE. pose proof (LBSM2.geom_facts FS _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    set (A := 64 * rho (f_sym f) + o) in *.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length bs) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite LBSM2.w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (fo_def _ _ HFS (bv_unsigned x - FS) ltac:(lia)) as [bb Hbb].
      replace (FS + (bv_unsigned x - FS)) with (bv_unsigned x) in Hbb by lia. rewrite LBSM2.w64_same, w64_of_unsigned in Hbb.
      unfold wview. rewrite Hbb. discriminate. }
    pose proof (LBSM2.wbytes_wr_agree (ms_mem ms) A bs HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (uo_frA U UOK) as EFR. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0.
    eapply (LBSM2.R_wr U G M0 FS UOK rho st _ ms _ A n HR HW); cbn; try reflexivity.
    - right; right; left. lia.
    - intros x Hx. right; right; left. lia.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell.
      pose proof Hcell as (C1 & C2 & _). eapply LBSM2.cell_ok_wr; [exact HW | exact Hcell | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - apply Forall_forall. intros b Hb'. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb') as Harr.
      pose proof Harr as (C1 & C2 & _). eapply LBSM2.arr_okg_wr; [exact HW | exact Harr | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      pose proof (r_apart _ _ _ _ _ _ _ HR) as (_ & _ & _ & _ & AP5). rewrite HLEN in AP5.
      eapply LBSM2.payload_ok_wr; [exact HW | exact P | lia | lia | lia].
    - eapply LBSM2.abs_ok_wr; [exact UOK | exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | lia].
    - intros Hlo. exfalso. lia.
    - eapply (LBSM2.frames_ok_upd U FS rho (ms_mem ms) _ A n (s_frames st) i f); [exact HW | exact HFS | exact RF | exact Hn | repeat split; reflexivity | | | rewrite HFR; lia].
      + intros p (Hat & _ & _ & _ & Hlen' & Hsh). pose proof (LBSM2.frame_set_space_eqs f cs' ars') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        unfold frame_okR, frame_at. cbn [f_sym f_cls f_flag f_sh f_cells f_arrs frame_set_space]. rewrite Q7, Q8, E1. split; [exact Hat|]. split; [exact Hk|].
        split; [exact Hcs|]. split; [exact Hars|]. split; [exact Hlen'|].
        intros t b Ht. destruct (Hsh t b Ht) as [Hb Hm]. split; [exact Hb|].
        pose proof (LBSM2.nth_error_Some_length' _ _ _ Ht) as Tl. rewrite E2 in Hlen'.
        pose proof (LBSM2.sh_frame FS (f_cls f) p Hk (proj1 Hat) (fo_align _ _ HFS)) as (S1 & S2 & S3 & _). rewrite <- (proj1 (proj2 Hat)) in S1, S2, S3.
        rewrite F7, HSH in S3.
        rewrite (LBSM2.wr_out (ms_mem ms) _ A n); [exact Hm | exact HW | lia | lia].
      + intros p q h Hat (Hatq & Hkh & _) Hne. destruct Hat as (Hp & Hb & Hfl). destruct Hatq as (Hq & Hbq & Hflq).
        destruct (LBSM2.slot_apart FS (f_cls h) q (f_cls f) p Hkh Hq Hk Hp Hne) as [D _].
        pose proof (frame_geom (f_cls h) q Hkh Hq) as (H1 & H2 & _). rewrite HFR in H1. rewrite HLEN in H2.
        pose proof (LBSM2.sh_frame FS (f_cls h) q Hkh Hq (fo_align _ _ HFS)) as (T1 & T2 & T3 & _). rewrite F7, HSH in T3.
        pose proof (LBSM2.flag_geom FS (f_cls h) q Hkh Hq) as (L1 & L2 & _). rewrite HFR in L2.
        destruct (LBSM2.f_size_cls h Hkh) as [Eh1 Eh2]. unfold LBSM2.frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq. rewrite <- Hb in D.
        clear - D Ho1 Ho2 Hnn G1 G2 G3 H1 H2 T2 T3 L1 L2 F4 F7 F8 F10 HSL HSH HFL Hb Hb0. lia.   (* [comment removed for export] *)
  Qed.

  #[using="UOK fs_consts frame_geom"] Lemma R_shframe_fill : forall rho st ms i f t n c,
    wf_state st = true -> R U G FS M0 rho st ms -> nth_frame (s_frames st) i = Some f ->
    0 <= t -> t + n <= f_shn f -> 0 <= n -> 0 <= c < 256 ->
    let m' := wbytes (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + t)) (repeat (Z_to_bv 8 c) (Z.to_nat n)) in
    store_ok segs (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + t)) (Z.to_nat n) = true /\
    R U G FS M0 rho (set_frames st (upd_frame (s_frames st) i
         (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat t) (Z.to_nat n) c) (f_flag f))))
      (ms_with_mem ms m').
  Proof.
    intros rho st ms i f t n c Hwf HR Hn Hc1 Hc2 Hnn Hc m'. subst m'.
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (LBSM2.frames_nth U FS rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin).
    pose proof Hf0 as ((Hp0 & Hb0 & Hfl0) & Hk & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p0 Hk Hp0) as (G1 & G2 & G3 & G4 & G5 & G6). rewrite HFR in G1. rewrite HLEN in G2.
    pose proof (LBSM2.sh_frame FS (f_cls f) p0 Hk Hp0 (fo_align _ _ HFS)) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite <- Hb0 in S1, S2, S3, S4, S5.
    destruct (LBSM2.f_size_cls f Hk) as [E1 E2]. rewrite E2 in Hc2.
    pose proof (LBSM2.R_geom U G M0 FS _ _ _ HR) as GE. pose proof (LBSM2.geom_facts FS _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    rewrite F7, HSL in S2. rewrite F7, HSH in S3. rewrite LBSM2.sh64 in S1, S2, S3.
    pose proof (repeat_length (Z_to_bv 8 c) (Z.to_nat n)) as Hlen.
    set (A := SHB + 8 * rho (f_sym f) + t) in *.
    assert (HA0 : 0 <= A) by (unfold SHB in *; lia). assert (HA64 : A < 2 ^ 64) by (unfold SHB in *; lia).
    assert (HAn : A + Z.of_nat (length (repeat (Z_to_bv 8 c) (Z.to_nat n))) <= 2 ^ 64) by (unfold SHB in *; lia).
    split.
    { apply store_ok_of_all; rewrite LBSM2.w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (fo_shdef _ _ HFS (bv_unsigned x - (sh FS + FS_SHLO)) ltac:(rewrite F7, HSL, HSH; unfold SHB in *; lia)) as [bb Hbb].
      replace (sh FS + FS_SHLO + (bv_unsigned x - (sh FS + FS_SHLO))) with (bv_unsigned x) in Hbb by lia. rewrite LBSM2.w64_same, w64_of_unsigned in Hbb.
      unfold wview. rewrite Hbb. discriminate. }
    pose proof (LBSM2.wbytes_wr_agree (ms_mem ms) A (repeat (Z_to_bv 8 c) (Z.to_nat n)) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (uo_frA U UOK) as EFR. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0.
    eapply (LBSM2.R_wr U G M0 FS UOK rho st _ ms _ A n HR HW); cbn; try reflexivity.
    - right; right; right; right; right. rewrite F7, HSL, HSH. unfold SHB in *. lia.
    - intros x Hx. right; right; right. rewrite F7, HSL, HSH. unfold SHB in *. lia.
    - apply Forall_forall. intros c' Hc'. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c' Hc') as Hcell.
      pose proof Hcell as (C1 & C2 & _). eapply LBSM2.cell_ok_wr; [exact HW | exact Hcell | lia | lia | rewrite EFR in *; unfold FR_A, SHB in *; lia].
    - apply Forall_forall. intros b Hb'. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb') as Harr.
      pose proof Harr as (C1 & C2 & _). eapply LBSM2.arr_okg_wr; [exact HW | exact Harr | lia | lia | rewrite EFR in *; unfold FR_A, SHB in *; lia].
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      pose proof (r_apart _ _ _ _ _ _ _ HR) as (_ & _ & AP3 & _). unfold IMGHI_A, app_mem, LOSH_A in AP3. rewrite ?HKHI, ?HHI in AP3.
      eapply LBSM2.payload_ok_wr; [exact HW | exact P | lia | lia | unfold SHB in *; lia].
    - eapply LBSM2.abs_ok_wr; [exact UOK | exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | unfold SHB in *; lia].
    - intros Hlo. exfalso. unfold SHB in *. lia.
    - eapply (LBSM2.frames_ok_upd U FS rho (ms_mem ms) _ A n (s_frames st) i f); [exact HW | exact HFS | exact RF | exact Hn | repeat split; reflexivity | | | rewrite HFL, HFR; unfold SHB in *; destruct (proj2 F4) as [ZLO|ZHI]; [right; lia | left; lia]].   (* [comment removed for export] *)
      + intros p (Hat & _ & Hcs & Hars & Hlen' & Hsh). pose proof (LBSM2.frame_at_inj FS rho f p p0 Hat (conj Hp0 (conj Hb0 Hfl0)) Hk) as ->.
        unfold frame_okR. cbn [f_sym f_cls f_cells f_arrs f_sh f_flag].
        change (f_size (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat t) (Z.to_nat n) c) (f_flag f))) with (f_size f).
        change (f_shn (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat t) (Z.to_nat n) c) (f_flag f))) with (f_shn f).
        rewrite E1, E2 in *. split; [exact Hat|]. split; [exact Hk|]. split; [|split; [|split]].
        * eapply LBSM2.Forall_cell_ok_wr; [exact HW | exact Hcs | lia | lia | unfold SHB in *; lia].
        * eapply LBSM2.Forall_arr_okg_wr; [exact HW | exact Hars | lia | lia | unfold SHB in *; lia].
        * rewrite list_fill_length. exact Hlen'.
        * intros u b Hu. rewrite LBSM2.sh64.
          assert (Ul : (u < length (f_sh f))%nat) by (pose proof (LBSM2.nth_error_Some_length' _ _ _ Hu) as X; rewrite list_fill_length in X; exact X).
          destruct (Nat.lt_ge_cases u (Z.to_nat t)) as [Hlt|Hge]; [|destruct (Nat.lt_ge_cases u (Z.to_nat t + Z.to_nat n)) as [Hin'|Hge2]].
          -- rewrite list_fill_out in Hu by lia. destruct (Hsh u b Hu) as [Hb Hm]. split; [exact Hb|].
             rewrite LBSM2.sh64 in Hm. rewrite (LBSM2.wr_out (ms_mem ms) _ A n); [exact Hm | exact HW | unfold SHB in *; lia | lia].
          -- rewrite list_fill_in in Hu by lia. injection Hu; intros <-. split; [lia|].
             pose proof (LBSM2.st_inside (ms_mem ms) A (repeat (Z_to_bv 8 c) (Z.to_nat n)) HA0 HA64 HAn (u - Z.to_nat t) (Z_to_bv 8 0) ltac:(rewrite Hlen; lia)) as Hst.
             replace (A + Z.of_nat (u - Z.to_nat t)) with (SHB + 8 * rho (f_sym f) + Z.of_nat u) in Hst by lia. rewrite Hst. f_equal.
             apply nth_repeat_bv. lia.
          -- rewrite list_fill_out in Hu by lia. destruct (Hsh u b Hu) as [Hb Hm]. split; [exact Hb|].
             rewrite LBSM2.sh64 in Hm. rewrite (LBSM2.wr_out (ms_mem ms) _ A n); [exact Hm | exact HW | unfold SHB in *; lia | lia].
      + intros p q h Hat (Hatq & Hkh & _) Hne. destruct Hat as (Hp & Hb & Hfl). destruct Hatq as (Hq & Hbq & Hflq).
        pose proof (LBSM2.frame_at_inj FS rho f p p0 (conj Hp (conj Hb Hfl)) (conj Hp0 (conj Hb0 Hfl0)) Hk) as ->.
        destruct (LBSM2.slot_apart FS (f_cls h) q (f_cls f) p0 Hkh Hq Hk Hp0 Hne) as [D _]. rewrite <- Hb0 in D.
        pose proof (frame_geom (f_cls h) q Hkh Hq) as (H1 & H2 & _ & _ & _ & _). rewrite HFR in H1. rewrite HLEN in H2.
        pose proof (LBSM2.sh_frame FS (f_cls h) q Hkh Hq (fo_align _ _ HFS)) as (T1 & T2 & T3 & T4 & T5 & T6).
        pose proof (LBSM2.flag_geom FS (f_cls h) q Hkh Hq) as (L1 & L2 & _). rewrite HFR in L2.
        destruct (LBSM2.f_size_cls h Hkh) as [Eh1 Eh2]. unfold LBSM2.frame_untouched. rewrite Eh1, Eh2, Hflq, Hbq, T1.
        unfold SHB in *. split; [|split].
        -- clear - Hc1 Hc2 Hnn Hb0 G1 S3 F9 F4 H1 H2. lia.   (* [comment removed for export] *)
        -- destruct D as [D|D]; [left; clear - T5 T6 D Hc1; lia | right; clear - D S6 T5 Hc2; lia].
        -- clear - Hc1 Hc2 Hnn Hb0 G1 S3 F9 F4 L1 L2 HFL. lia.
  Qed.

  #[using="UOK fs_consts"] Lemma R_abs_fill : forall rho st ms a n c,
    wf_state st = true -> R U G FS M0 rho st ms -> in_ranges a n (ue_rw U) = true -> ro_clear U a n = true -> 0 < n -> 0 <= c < 256 ->
    let m' := wbytes (ms_mem ms) (w64 a) (repeat (Z_to_bv 8 c) (Z.to_nat n)) in
    store_ok segs (ms_mem ms) (w64 a) (Z.to_nat n) = true /\
    R U G FS M0 rho (set_pay (set_pcache (set_abs st (LAC.bm_fill (s_abs st) a (Z.to_nat n) c)) []) []) (ms_with_mem ms m').
  Proof.
    intros rho st ms a n c Hwf HR Hrw Hroc Hn Hc m'. subst m'.
    assert (Hrg : forall k, 0 <= k < n -> in_rangesZ (a + k) (ue_rw U)) by (intros k Hk; eapply LBSM2.in_ranges_Z; eauto).
    assert (Hra : in_rangesZ a (ue_rw U)) by (pose proof (Hrg 0 ltac:(lia)) as H0; rewrite Z.add_0_r in H0; exact H0).
    pose proof (uo_small U UOK a (or_introl Hra)) as Ha0.
    pose proof (uo_small U UOK (a + (n - 1)) (or_introl (Hrg (n - 1) ltac:(lia)))) as Ha1.
    pose proof (uo_rw_lo U UOK (a + (n - 1)) (Hrg (n - 1) ltac:(lia))) as Hlo.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR.
    set (sp0 := rho SYM_SP0) in *.
    pose proof (repeat_length (Z_to_bv 8 c) (Z.to_nat n)) as Hlen.
    assert (HA0 : 0 <= a) by lia. assert (HA64 : a < 2 ^ 64) by lia.
    assert (HAn : a + Z.of_nat (length (repeat (Z_to_bv 8 c) (Z.to_nat n))) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite LBSM2.w64_unsigned_small by lia; [lia|].
      intros x Hx. pose proof (uo_rw_w U UOK (bv_unsigned x) (ms_mem ms) ltac:(replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia; apply Hrg; lia)) as So.
      rewrite w64_of_unsigned in So. cbn [store_ok] in So. fold segs in So. destruct (wview segs (ms_mem ms) x); [discriminate | discriminate]. }
    pose proof (LBSM2.wbytes_wr_agree (ms_mem ms) a (repeat (Z_to_bv 8 c) (Z.to_nat n)) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (LBSM2.R_geom U G M0 FS _ _ _ HR) as GE. pose proof (LBSM2.geom_facts FS _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    eapply (LBSM2.R_wr U G M0 FS UOK rho st _ ms _ a n HR HW); cbn; try reflexivity.
    - right; left. lia.
    - intros x Hx. right; left. replace x with (a + (x - a)) by lia. apply Hrg. lia.
    - apply Forall_forall. intros c' Hc'. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c' Hc') as Hcell. pose proof Hcell as (C1 & C2 & _).
      eapply LBSM2.cell_ok_wr; [exact HW | exact Hcell | lia | lia | lia].
    - apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb) as Harr. pose proof Harr as (C1 & C2 & _).
      eapply LBSM2.arr_okg_wr; [exact HW | exact Harr | lia | lia | lia].
    - destruct (r_pay _ _ _ _ _ _ _ HR) as (P1 & P2 & P3 & P4). split; [|split; [exact P2 | split; [intros ? ? ? []|intros ? ? []]]].
      intros i Hi. destruct (P1 i Hi) as [b Hb]. eapply LBSM2.rd1_wr_grows; [exact HW | exact Hb].
    - destruct (r_abs _ _ _ _ _ _ _ HR) as (Q1 & Q2 & Q3). split; [|split].
      + intros a' b Hg. rewrite bm_get_fill in Hg.
        destruct (Z.leb_spec a a'); [destruct (Z.ltb_spec a' (a + Z.of_nat (Z.to_nat n)))|]; cbn in Hg.
        * injection Hg; intros <-. split; [replace a' with (a + (a' - a)) by lia; apply Hrg; lia|]. split; [lia|].
          pose proof (LBSM2.st_inside (ms_mem ms) a (repeat (Z_to_bv 8 c) (Z.to_nat n)) HA0 HA64 HAn (Z.to_nat (a' - a)) (Z_to_bv 8 0) ltac:(lia)) as Hin.
          replace (a + Z.of_nat (Z.to_nat (a' - a))) with a' in Hin by lia. rewrite Hin. f_equal. apply nth_repeat_bv. lia.
        * destruct (Q1 a' b Hg) as (Hrw' & Hb & Hm). pose proof (uo_small U UOK a' (or_introl Hrw')).
          split; [exact Hrw'|]. split; [exact Hb|]. rewrite (LBSM2.st_out _ a _ HA0 HA64 HAn) by lia. exact Hm.
        * destruct (Q1 a' b Hg) as (Hrw' & Hb & Hm). pose proof (uo_small U UOK a' (or_introl Hrw')).
          split; [exact Hrw'|]. split; [exact Hb|]. rewrite (LBSM2.st_out _ a _ HA0 HA64 HAn) by lia. exact Hm.
      + intros a' Hrw' Hg. rewrite bm_get_fill in Hg. pose proof (uo_small U UOK a' (or_introl Hrw')).
        destruct (Z.leb_spec a a'); [destruct (Z.ltb_spec a' (a + Z.of_nat (Z.to_nat n)))|]; cbn in Hg; [discriminate| |];
          rewrite (LBSM2.st_out _ a _ HA0 HA64 HAn) by lia; exact (Q2 a' Hrw' Hg).
      + intros a' b Hro Hm. pose proof (uo_small U UOK a' (or_intror Hro)).
        assert (Hnot : ~ (a <= a' < a + Z.of_nat (length (repeat (Z_to_bv 8 c) (Z.to_nat n))))).
        { intros Hct. apply (LBSM2.ro_clear_sound U a n a' Hroc Hro). rewrite repeat_length in Hct. lia. }
        rewrite (LBSM2.st_out _ a _ HA0 HA64 HAn) in Hm by lia. exact (Q3 a' b Hro Hm).
    - intros _ a' b Hg. pose proof (uo_rt_small U UOK a' b Hg) as [_ Hnrw].
      destruct (Z_lt_le_dec a' a); [left; lia|]. destruct (Z_lt_le_dec a' (a + n)); [|right; lia].
      exfalso. apply Hnrw. replace a' with (a + (a' - a)) by lia. apply Hrg. lia.
    - eapply LBSM2.frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | rewrite HFL; lia |].
      left. rewrite F7, HSL. unfold SHB. lia.
  Qed.
  #[using="Type"] Lemma bv5_lit : forall z, 0 <= z < 32 -> forall b : bv 5, bv_unsigned b = z -> Z_to_bv 5 z = b.
  Proof. intros z Hz b Hb. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb. apply bv_wrap_small. pose proof (bv_unsigned_in_range 5 b). lia. Qed.

  #[using="Type"] Lemma list_get_oob : forall (l : list aval) n d, (length l <= n)%nat -> list_get l n d = d.
  Proof. clear. induction l as [|x l IH]; intros [|n] d H; cbn in *; try reflexivity; try lia. apply IH. lia. Qed.
  #[using="Type"] Lemma get_set_top : forall l i r, list_get (list_set l i Top) r Top = (if Nat.eqb r i then Top else list_get l r Top).
  Proof.
    intros l i r. rewrite LBSS.list_get_set. destruct (Nat.eqb_spec r i); cbn [andb]; [|reflexivity].
    destruct (Nat.ltb_spec i (length l)); [reflexivity|]. symmetry. symmetry. rewrite list_get_oob by lia. reflexivity.
  Qed.

  #[using="UOK SEGS MEMSET segs fs_consts frame_geom"] Theorem apply_memset_sound : forall rho S S' ms,
    wf_state S = true -> R U G FS M0 rho S ms -> apply_memset U S = Some S' ->
    exists ms' rho', msteps (ue_segs U) ms ms' /\ R U G FS M0 rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat.
  Proof.
    intros rho S S' ms Hwf HR H.
    destruct (wf_parts S Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    pose proof (r_vs _ _ _ _ _ _ _ HR) as [HC HCB]. destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    (* [comment removed for export] *)
    unfold apply_memset, memset_core in H.
    destruct (Z.eqb_spec (s_pc S) (ue_memset U)) as [HPC|]; [|discriminate]. cbn [negb] in H. rewrite MEMSET in HPC.
    destruct (getreg S 1) as [|lra|? ? ? ?|? ?] eqn:G1; try discriminate.
    destruct (is_const lra) as [ra|] eqn:Hra; [|discriminate].
    destruct (Z.eqb_spec (ra mod 4) 0) as [HRA4|]; [|discriminate]. destruct (Z.leb_spec 0 ra) as [HRA0|]; [|discriminate].
    destruct (Z.ltb_spec ra two64) as [HRA64|]; [|discriminate]. cbn [andb negb] in H.
    destruct (aval_litC (s_ctx S) (getreg S 12)) as [n|] eqn:G12; [|discriminate].
    destruct (Z.leb_spec 0 n) as [HN0|]; [|discriminate]. destruct (Z.leb_spec n 4096) as [HN4096|]; [|discriminate]. cbn [andb negb] in H.
    destruct (getreg S 11) as [|l1|? ? ? ?|? ?] eqn:G11; try discriminate.
    destruct (and_lowlit (s_ctx S) l1 8) as [c|] eqn:Hc; [|discriminate].
    destruct (s_resv S) eqn:ERESV; [discriminate|].
    (* [comment removed for export] *)
    pose proof (reg_ok rho S ms 1 HR ltac:(lia)) as R1. rewrite G1 in R1. cbn [val_ok] in R1. rewrite (is_const_sound rho lra ra Hra) in R1.
    pose proof (reg_ok rho S ms 12 HR ltac:(lia)) as R12. pose proof (aval_litC_sound rho _ _ n _ HC G12 R12) as R12'.
    pose proof (reg_ok rho S ms 11 HR ltac:(lia)) as R11. rewrite G11 in R11. cbn [val_ok] in R11.
    pose proof (reg_ok rho S ms 10 HR ltac:(lia)) as R10.
    destruct (and_lowlit_sound rho (s_ctx S) l1 8 c (LBSS.R_galign U G M0 FS UOK _ _ _ HR) HC ltac:(lia) Hc) as [Hc8 Hcr]. change (2 ^ 8) with 256 in Hc8, Hcr.
    assert (CB : cbyte (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 11))) = Z_to_bv 8 c).
    { unfold cbyte. rewrite R11, w64_unsigned. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
      rewrite (LBSA.mod_mod_pow2_le (evl rho l1) 8 64) by lia. change (2 ^ 8) with 256. rewrite Hc8. symmetry. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    pose proof (r_resv _ _ _ _ _ _ _ HR) as RRESV. rewrite ERESV in RRESV. cbn [resv_ok] in RRESV.
    destruct (ms_resv ms) eqn:EMR; [destruct RRESV|].
    pose proof (ms_eta ms (r_svc _ _ _ _ _ _ _ HR) EMR) as ETA. set (fx := mkFP (ms_fregs ms) (ms_fcsr ms)) in ETA.
    rewrite (r_pc _ _ _ _ _ _ _ HR), HPC in ETA.
    (* [comment removed for export] *)
    pose proof (LBSM2.classify_spec rho (s_frames S) (getreg S 10) _ (s_next S) R10 (LBSS.getreg_below S 10 Hwf) W18 Wfr) as CL10.
    assert (DEST : exists A S1,
      match classify (s_frames S) (getreg S 10) with
      | Some (AShFrm i t) => match nth_frame (s_frames S) i, is_const t with
          | Some f, Some tc => if (Z.leb 0 tc &&& Z.leb (tc + n) (f_shn f))%bool then
               Some (set_frames S (upd_frame (s_frames S) i (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat tc) (Z.to_nat n) c) (f_flag f)))) else None
          | _, _ => None end
      | Some (AFrm i off) => match nth_frame (s_frames S) i with
          | Some f => match memset_space 0 (f_size f) (f_cells f) (f_arrs f) off n c with Some (cs, ars) => Some (set_frames S (upd_frame (s_frames S) i (frame_set_space f cs ars))) | None => None end
          | None => None end
      | Some (AStk off) => match memset_space (- ue_fr U) 0 (s_stk S) (s_arrs S) off n c with Some (cs, ars) => Some (set_arrs (set_stk S cs) ars) | None => None end
      | Some (AAbs a) => if (in_ranges a n (ue_rw U) &&& ro_clear U a n &&& Z.ltb 0 n)%bool then Some (set_pay (set_pcache (set_abs S (LAC.bm_fill (s_abs S) a (Z.to_nat n) c)) []) []) else None
      | _ => None
      end = Some S1 /\
      getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 10)) = w64 A /\ 0 <= A /\ A + n < 2 ^ 64 /\
      store_ok segs (ms_mem ms) (w64 A) (Z.to_nat n) = true /\
      R U G FS M0 rho S1 (ms_with_mem ms (wbytes (ms_mem ms) (w64 A) (repeat (Z_to_bv 8 c) (Z.to_nat n)))) /\
      s_regs S1 = s_regs S /\ s_next S1 = s_next S /\ s_resv S1 = None /\ S' = set_pc (set_regs S1 (LAC.havoc_a1_a6 (s_regs S1))) ra).
    { destruct (classify (s_frames S) (getreg S 10)) as [[off|?|?|a|i off|? ?|i t|?|?|?]|]; try discriminate.
      - (* [comment removed for export] *)
        destruct (memset_space (- ue_fr U) 0 (s_stk S) (s_arrs S) off n c) as [[cs ars]|] eqn:EM; [|discriminate].
        injection H as ES'. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_fr U UOK) as Hfr.
        destruct (memset_space_ok rho (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_stk S) (s_arrs S) off n c cs ars Hcr HN0 ltac:(lia) ltac:(lia)
                    (r_stk _ _ _ _ _ _ _ HR) (r_arrs _ _ _ _ _ _ _ HR) EM) as (W1 & W2 & -> & CELLS & ARRS).
        destruct (R_stack_fill rho S ms off n (repeat (Z_to_bv 8 c) (Z.to_nat n)) cs (s_arrs S) Hwf HR W1 W2 HN0 (repeat_length _ _) CELLS ARRS) as [So HR'].
        exists (rho SYM_SP0 + off), (set_arrs (set_stk S cs) (s_arrs S)). split; [reflexivity|]. split; [exact CL10|]. split; [lia|]. split; [lia|].
        split; [exact So|]. split; [exact HR'|]. cbn. rewrite ERESV. repeat split; try reflexivity. symmetry. exact ES'.
      - (* [comment removed for export] *)
        destruct (in_ranges a n (ue_rw U) &&& ro_clear U a n &&& Z.ltb 0 n)%bool eqn:Hrw0; [|discriminate]. injection H as ES'. destruct CL10 as [CL10 Ha].
        apply andb_prop in Hrw0 as [Hrw Hn0]. apply Z.ltb_lt in Hn0. apply andb_prop in Hrw as [Hrw Hroc].
        + destruct (R_abs_fill rho S ms a n c Hwf HR Hrw Hroc Hn0 Hcr) as [So HR'].
          assert (Hrg : in_rangesZ (a + (n - 1)) (ue_rw U)) by (eapply LBSM2.in_ranges_Z; [exact Hrw | lia]).
          pose proof (uo_small U UOK _ (or_introl Hrg)).
          exists a, (set_pay (set_pcache (set_abs S (LAC.bm_fill (s_abs S) a (Z.to_nat n) c)) []) []). split; [reflexivity|]. split; [exact CL10|].
          split; [lia|]. split; [lia|]. split; [exact So|]. split; [exact HR'|]. cbn. rewrite ERESV. repeat split; try reflexivity. symmetry; exact ES'.
      - (* [comment removed for export] *)
        destruct CL10 as (f & Hnth & CL10). rewrite Hnth in H.
        destruct (memset_space 0 (f_size f) (f_cells f) (f_arrs f) off n c) as [[cs ars]|] eqn:EM; [|discriminate]. injection H as ES'.
        pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
        destruct (LBSM2.frames_nth U FS rho (ms_mem ms) (s_frames S) i f (r_frames _ _ _ _ _ _ _ HR) Hnth) as (p & Hf & Hin).
        pose proof Hf as ((Hp & Hb & Hfl) & Hk & Hcs & Har & _).
        pose proof (frame_geom (f_cls f) p Hk Hp) as (FG1 & FG2 & _). rewrite HLEN in FG2. pose proof (fo_hi _ _ HFS) as HI. pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
        destruct (LBSM2.f_size_cls f Hk) as [E1 _].
        destruct (memset_space_ok rho (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_cells f) (f_arrs f) off n c cs ars Hcr HN0 ltac:(lia) ltac:(lia) Hcs Har EM)
          as (W1 & W2 & -> & CELLS & ARRS).
        destruct (R_frame_fill rho S ms i f off n (repeat (Z_to_bv 8 c) (Z.to_nat n)) cs (f_arrs f) Hwf HR Hnth W1 W2 HN0 (repeat_length _ _) CELLS ARRS) as [So HR'].
        exists (64 * rho (f_sym f) + off), (set_frames S (upd_frame (s_frames S) i (frame_set_space f cs (f_arrs f)))). rewrite Hnth, EM. split; [reflexivity|]. split; [exact CL10|].
        split; [lia|]. split; [lia|]. split; [exact So|]. split; [exact HR'|]. cbn. rewrite ERESV. repeat split; try reflexivity. symmetry; exact ES'.
      - (* [comment removed for export] *)
        destruct CL10 as (f & Hnth & CL10 & _). rewrite Hnth in H.
        destruct (is_const t) as [tc|] eqn:Ktc; [|discriminate].
        destruct (Z.leb 0 tc &&& Z.leb (tc + n) (f_shn f))%bool eqn:Eb; [|discriminate]. injection H as ES'.
        apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.leb_le in Eb2.
        rewrite (is_const_sound rho t tc Ktc) in CL10.
        pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
        destruct (LBSM2.frames_nth U FS rho (ms_mem ms) (s_frames S) i f (r_frames _ _ _ _ _ _ _ HR) Hnth) as (p & Hf & Hin).
        pose proof Hf as ((Hp & Hb & Hfl) & Hk & _).
        pose proof (LBSM2.sh_frame FS (f_cls f) p Hk Hp (fo_align _ _ HFS)) as (S1 & S2 & S3 & _). rewrite <- Hb in S1, S2, S3. rewrite LBSM2.sh64 in S1, S2, S3.
        pose proof (LBSM2.R_geom U G M0 FS _ _ _ HR) as GE. pose proof (LBSM2.geom_facts FS _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
        rewrite F7, HSH in S3. destruct (LBSM2.f_size_cls f Hk) as [_ E2]. rewrite E2 in Eb2.
        destruct (R_shframe_fill rho S ms i f tc n c Hwf HR Hnth Eb1 ltac:(rewrite E2; exact Eb2) HN0 Hcr) as [So HR'].
        exists (SHB + 8 * rho (f_sym f) + tc), (set_frames S (upd_frame (s_frames S) i (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat tc) (Z.to_nat n) c) (f_flag f)))).
        rewrite Hnth. replace (Z.leb 0 tc &&& Z.leb (tc + n) (f_shn f))%bool with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; [exact Eb1 | rewrite E2; exact Eb2]).
        split; [reflexivity|]. split; [exact CL10|]. split; [unfold SHB in *; lia|]. split; [unfold SHB in *; lia|]. split; [exact So|]. split; [exact HR'|].
        cbn. rewrite ERESV. repeat split; try reflexivity. symmetry; exact ES'. }
    clear H. destruct DEST as (A & S1 & _ & HA10 & HA0 & HAn & STOK & HR1 & Eregs & Enext & Eresv1 & ES').
    unfold segs in STOK. rewrite SEGS in STOK.
    assert (RET : ret_ok (w64 ra)).
    { apply ret_ok_even. rewrite LBSM2.w64_unsigned_small by (unfold LAI.two64 in HRA64; rewrite two64_eq in HRA64; lia).
      apply Z.mod_divide in HRA4; [|lia]. destruct HRA4 as [q4 Hq4]. rewrite Hq4. replace (q4 * 4) with (q4 * 2 * 2) by lia. apply Z_mod_mult. }
    assert (LIT5 : forall k : nat, (k < 32)%nat -> forall b : bv 5, bv_unsigned b = Z.of_nat k -> b = Z_to_bv 5 (Z.of_nat k)).
    { intros k Hk b Hb. symmetry. apply bv5_lit; [lia | exact Hb]. }
    pose proof (@memset_summary fx (ms_mem ms) (w64 A) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 11))) (w64 ra) n (ms_rom ms) HN0
                  ltac:(rewrite LBSM2.w64_unsigned_small by lia; lia) STOK RET (ms_regs ms)) as MSUM.
    rewrite (LIT5 10%nat ltac:(lia) (10%bv : bv 5) eq_refl), (LIT5 11%nat ltac:(lia) (11%bv : bv 5) eq_refl), (LIT5 12%nat ltac:(lia) (12%bv : bv 5) eq_refl),
            (LIT5 1%nat ltac:(lia) (1%bv : bv 5) eq_refl) in MSUM.
    specialize (MSUM HA10 eq_refl ltac:(rewrite R12'; reflexivity) ltac:(exact R1)).
    destruct MSUM as (regs' & MS & A10 & AGR).
    unfold LibIfaceA.w64, LBSEM.w64 in ETA. rewrite <- ETA in MS.
    (* [comment removed for export] *)
    set (c0 := {| c_regs := regs'; c_fregs := ms_fregs ms; c_pc := w64 ra; c_fcsr := ms_fcsr ms; c_resv := None |}).
    exists (LBSS.ms_of (ms_with_mem ms (wbytes (ms_mem ms) (w64 A) (repeat (Z_to_bv 8 c) (Z.to_nat n)))) c0 (wbytes (ms_mem ms) (w64 A) (repeat (Z_to_bv 8 c) (Z.to_nat n)))), rho.
    split.
    { match goal with |- msteps _ _ ?X => replace X with (@mkst fx regs' (w64 ra) (wbytes (ms_mem ms) (w64 A) (repeat (Z_to_bv 8 c) (Z.to_nat n))) (ms_rom ms)) by reflexivity end.
      unfold segs. rewrite SEGS. rewrite <- CB. exact MS. }
    split; [| split; [apply agree_refl | rewrite ES'; cbn; rewrite Enext; lia]].
    rewrite ES'. apply (LBSS.R_core_upd U G M0 FS rho S1 _ (set_pc (set_regs S1 (LAC.havoc_a1_a6 (s_regs S1))) ra) c0 HR1); try reflexivity.
    - (* [comment removed for export] *) cbn [s_regs set_pc set_regs]. change (c_regs c0) with regs'. rewrite Eregs. intros r Hr.
      unfold LAC.havoc_a1_a6. rewrite !get_set_top. rewrite (LBG.getr_reg_get regs' r Hr).
      destruct (Nat.eqb_spec r 16); [exact I|]. destruct (Nat.eqb_spec r 15); [exact I|]. destruct (Nat.eqb_spec r 14); [exact I|].
      destruct (Nat.eqb_spec r 13); [exact I|]. destruct (Nat.eqb_spec r 12); [exact I|]. destruct (Nat.eqb_spec r 11); [exact I|].
      + rewrite (AGR (Z_to_bv 5 (Z.of_nat r))).
        * rewrite <- (LBG.getr_reg_get (ms_regs ms) r Hr). exact (r_regs _ _ _ _ _ _ _ HR r Hr).
        * unfold ms_clob. intros Hin. cbn [In] in Hin. remember (Z.of_nat r) as zr eqn:Ezr.
          repeat (destruct Hin as [E|Hin]; [apply (f_equal bv_unsigned) in E; rewrite Z_to_bv_small in E by (change (bv_modulus 5) with 32; lia); lazy in E; lia|]). exact Hin.
    - (* [comment removed for export] *) change (c_resv c0) with (@None word). cbn [s_resv set_pc set_regs]. rewrite Eresv1. exact I.
    - (* [comment removed for export] *) change (c_fcsr c0) with (ms_fcsr ms). exact (r_frm _ _ _ _ _ _ _ HR).
  Qed.
End Summaries.
End LBSUMS.
