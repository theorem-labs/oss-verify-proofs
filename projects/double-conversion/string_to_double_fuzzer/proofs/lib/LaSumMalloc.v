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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib MemsetLib AsanMemset_code AsanMemset LaState LaMem LaStep LaCheck LaSem LaWf LaSoundVal LaSoundAlu LaSoundMem LaSoundMem2 LaSoundStep LaSoundMatch LaSoundExplore LaGlue.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac clear_ors := repeat match goal with H : context [or] |- _ => clear H end.
Ltac lia_nd := first [ solve [ clear_ors; lia_fast ] | lia_fast ].
#[local] Ltac Lia.lia ::= lia_nd.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF LASV LASM LASM2.
Open Scope Z_scope.

Module LASUMM.

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
  LASM2.wr_agree mi (patch mi mf (lo, hi)) lo (hi - lo).
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
  Hypothesis SEGS : ue_segs U = SEGS_A.
  Hypothesis RO : ue_ro U = RO_A.
  Hypothesis TP : ue_tp U = TP_A.
  Hypothesis MEMSET : ue_memset U = ms_base.
  Hypothesis CBDPC : ue_cbd_pc U = CBD_ENTRY_A.
  Hypothesis CBDFR : ue_cbd_fr U = CBD_FR_A.
  (* [comment removed for export] *)
  Hypothesis RTCOV : forall a b, In (a, b) RT_A -> bm_get (ue_rt U) a = Some b.
  Hypothesis GSHCOV : forall a b, In (a, b) GSH_A -> bm_get (ue_gsh U) a = Some b.
  Let segs := ue_segs U.
  Let fs_consts := LASM2.fs_consts.
  Let frame_geom := LASM2.frame_geom FS.

  (* [comment removed for export] *)
  #[using="Type"] Lemma reg_ok : forall rho S ms r, R U G FS M0 rho S ms -> (1 <= r < 32)%nat ->
    val_ok rho (getreg S r) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r))).
  Proof.
    intros rho S ms r HR Hr. unfold getreg. destruct (Nat.eqb_spec r 0); [lia|].
    rewrite <- (LAG.getr_reg_get (ms_regs ms) r Hr). exact (r_regs _ _ _ _ _ _ _ HR r Hr).
  Qed.

  #[using="Type"] Lemma reg_lit : forall rho S ms r z, R U G FS M0 rho S ms -> (1 <= r < 32)%nat -> reg_is_lit S r z = true ->
    getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = w64 z.
  Proof.
    intros rho S ms r z HR Hr H. pose proof (reg_ok rho S ms r HR Hr) as V. unfold reg_is_lit in H.
    destruct (getreg S r) as [|l| |]; try discriminate. apply leqb_sound in H. subst l. cbn in V. rewrite lconst_sound in V.
    rewrite V. apply w64_snorm.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS RTCOV"] Lemma R_rt_ok : forall rho S ms, R U G FS M0 rho S ms -> rt_ok (ms_mem ms).
  Proof.
    intros rho S ms HR a b Hin. destruct (r_rt _ _ _ _ _ _ _ HR a b (RTCOV a b Hin)) as [Hb Hrd].
    exists [Z_to_bv 8 b]. unfold segs in Hrd. rewrite SEGS in Hrd. split; [exact Hrd|].
    rewrite LASM2.bytes_le_cons. change (bytes_le_to_Z []) with 0. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_small by lia. lia.
  Qed.
  #[using="GSHCOV"] Lemma R_gsh_ok : forall rho S ms, R U G FS M0 rho S ms -> gsh_ok (ms_mem ms).
  Proof. intros rho S ms HR a b Hin. exact (proj2 (r_gsh _ _ _ _ _ _ _ HR a b (GSHCOV a b Hin))). Qed.
  #[using="SEGS RO"] Lemma R_ro_ok : forall rho S ms, R U G FS M0 rho S ms -> ro_ok SEGS_A RO_A (ms_mem ms).
  Proof.
    intros rho S ms HR a b Ha Hm. rewrite <- SEGS, <- RO in *. apply (proj2 (proj2 (r_abs _ _ _ _ _ _ _ HR)) a b); [|exact Hm].
    apply LAG.in_ranges_rangesZ. exact Ha.
  Qed.
  #[using="fs_consts"] Lemma malloc_ctx_mono : forall wlo whi wlo' whi' m, malloc_ctx_ok wlo whi FS m -> wlo <= wlo' -> whi' <= whi -> malloc_ctx_ok wlo' whi' FS m.
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
    R U G FS M0 rho st ms -> LASM2.wr_agree (ms_mem ms) m' A n -> LASM2.wclass FS (rho SYM_SP0 - FR_A) (rho SYM_SP0) A n ->
    (forall x, A <= x < A + n -> priv U FS (rho SYM_SP0) x) -> 0x688000 <= A ->   (* [comment removed for export] *)
    (forall c, In c (s_stk st) -> - ue_fr U <= c_off c -> c_off c + c_w c <= 0 -> rho SYM_SP0 + c_off c + c_w c <= A \/ A + n <= rho SYM_SP0 + c_off c) ->
    (forall a, In a (s_arrs st) -> - ue_fr U <= ar_lo a -> ar_hi a <= 0 -> rho SYM_SP0 + ar_hi a <= A \/ A + n <= rho SYM_SP0 + ar_lo a) ->
    (rho SYM_N <= 0 \/ rho SYM_DATA + rho SYM_N <= A \/ A + n <= rho SYM_DATA) ->
    frames_ok U FS rho m' (s_frames st) ->
    R U G FS M0 rho st (ms_with_mem ms m').
  Proof.
    intros rho st ms m' A n HR HW WC PRIV HA CELLS ARRS PAY FRS.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
    eapply (LASM2.R_wr U G M0 FS UOK rho st st ms m' A n HR HW WC PRIV); try reflexivity.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell. pose proof Hcell as (C1 & C2 & _).
      eapply LASM2.cell_ok_wr; [exact HW | exact Hcell | lia | lia | apply CELLS; [exact Hc | exact C1 | exact C2]].
    - apply Forall_forall. intros a Ha. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) a Ha) as Harr. pose proof Harr as (C1 & C2 & _).
      eapply LASM2.arr_okg_wr; [exact HW | exact Harr | lia | lia | apply ARRS; [exact Ha | exact C1 | exact C2]].
    - eapply LASM2.payload_ok_wr; [exact HW | exact (r_pay _ _ _ _ _ _ _ HR) | lia | lia | exact PAY].
    - eapply LASM2.abs_ok_wr; [exact UOK | exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | exact HA].
    - intros Hlo. exfalso. pose proof HW as (_ & _ & Wn & _). lia.
    - exact FRS.
  Qed.

  (* [comment removed for export] *)
  #[using="UOK fs_consts"] Lemma R_mem_ext : forall rho st ms m', R U G FS M0 rho st ms -> (forall x, m' x = ms_mem ms x) -> R U G FS M0 rho st (ms_with_mem ms m').
  Proof.
    intros rho st ms m' HR EXT.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR. rewrite EFR in Rsp0. unfold FR_A in Rsp0.
    assert (HW : LASM2.wr_agree (ms_mem ms) m' (rho SYM_SP0) 0).
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [intros x _; apply EXT | intros x b Hb; exists b; rewrite EXT; exact Hb]. }
    pose proof (proj1 (proj2 (r_pay _ _ _ _ _ _ _ HR))) as P2. rewrite EFR in P2. unfold FR_A in P2.
    eapply R_wr_same; [exact HR | exact HW | left; unfold FR_A; lia | intros x Hx; lia | lia | intros; lia | intros; lia | lia |].
    pose proof (r_apart _ _ _ _ _ _ _ HR) as (AP1 & AP2 & AP3 & AP4 & AP5). pose proof (fo_hi _ _ (r_fs _ _ _ _ _ _ _ HR)) as HI.
    unfold KHI_A, HIEND_A, FR_A, FS_LEN in AP1, AP2, AP4, HI.
    eapply LASM2.frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | unfold FS_LEN, FS_FLAGS; lia | ].
    right. destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _ & HSH). unfold sh. rewrite ESH, HSH. unfold SHB.
    assert (FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="fs_consts frame_geom"] Lemma frames_ok_wr_slot : forall rho m m' A n frs k p,
    LASM2.wr_agree m m' A n -> fs_ok FS m -> frames_ok U FS rho m frs ->
    (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k -> ~ live_at FS rho frs k p ->
    ((fs_frame FS k p <= A /\ A + n <= fs_frame FS k p + fs_fsz k) \/ (sh (fs_frame FS k p) <= A /\ A + n <= sh (fs_frame FS k p) + fs_fsz k / 8)) ->
    frames_ok U FS rho m' frs.
  Proof.
    intros rho m m' A n frs k p HW HFS RF Hk Hp NL RANGE.
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    pose proof (frame_geom k p Hk Hp) as (FG1 & FG2 & FG3 & FG4 & FG5 & FG6). rewrite HFR in FG1. rewrite HLEN in FG2.
    pose proof (LASM2.sh_frame FS k p Hk Hp (fo_align _ _ HFS)) as (S1 & S2 & S3 & S4 & S5 & S6).
    assert (F8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia).
    assert (F8' : 0xcd000 <= FS / 8) by (apply Z.div_le_lower_bound; lia).   (* [comment removed for export] *)
    rewrite S1 in RANGE. unfold sh in S2, S3. rewrite ESH, HSL in S2. rewrite ESH, HSH in S3. unfold SHB in S2, S3, RANGE.
    eapply LASM2.frames_ok_rebuild; [exact RF | apply LASM2.fsim_refl | |].
    - intros ps F2 ND. apply LASM2.Forall2_nth. pose proof (proj1 (LASM2.Forall2_nth _ _ _) F2) as [L F2n]. split; [exact L|].
      intros j h q Hh Hq. pose proof (F2n j h q Hh Hq) as Hh'. eapply LASM2.frame_okR_wr; [exact HW | exact HFS | exact Hh' |].
      destruct Hh' as ((Hq' & Hbq & Hflq) & Kh & _).
      assert (NE : (f_cls h, q) <> (k, p)).
      { intros E. apply NL. exists h. split; [eapply nth_error_In; exact Hh|]. injection E; intros -> <-. split; [reflexivity|]. split; [exact Hq'|]. split; assumption. }
      destruct (LASM2.slot_apart FS (f_cls h) q k p Kh Hq' Hk Hp NE) as [D DF].
      pose proof (frame_geom (f_cls h) q Kh Hq') as (H1 & H2 & _). rewrite HFR in H1. rewrite HLEN in H2.
      pose proof (LASM2.sh_frame FS (f_cls h) q Kh Hq' (fo_align _ _ HFS)) as (T1 & T2 & T3 & T4 & T5 & T6).
      pose proof (LASM2.flag_geom FS (f_cls h) q Kh Hq') as (L1 & L2 & _). rewrite HFL in L1. rewrite HFR in L2.
      destruct (LASM2.f_size_cls h Kh) as [Eh1 Eh2]. unfold LASM2.frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq, T1.
      unfold SHB in *. destruct RANGE as [[R1 R2]|[R1 R2]].
      + split; [|split].
        * destruct D as [D|D]; [left; clear - D R1; lia | right; clear - D R2; lia].
        * clear - H1 H2 T5 T6 F8 F8' LO LOAPP FG1 FG2 R1 R2. lia.   (* [comment removed for export] *)
        * left. clear - L2 FG1 R1. lia.
      + split; [|split].
        * clear - R1 R2 S2 S3 F8 F8' LO LOAPP H1 H2 FG1 FG2. lia.
        * destruct D as [D|D]; [left; clear - T5 T6 S5 D R1; lia | right; clear - R2 S5 S6 T5 D; lia].
        * clear - R1 R2 S2 S3 F8 F8' LO LOAPP L1 L2 FG1 FG2. lia.
    - intros j Hj. pose proof HW as (WA & WAn & Wn & _). apply (LASM2.wr_out m m' A n); [exact HW | rewrite HFL; lia |].
      rewrite HFL. lia.
  Qed.

  #[using="Type"] Lemma combine_snoc : forall {A B} (l : list A) (k : list B) a b, length l = length k -> combine (l ++ [a]) (k ++ [b]) = combine l k ++ [(a, b)].
  Proof. induction l as [|x l IH]; intros [|y k] a b L; cbn in L |- *; try discriminate; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.
  #[using="Type"] Lemma NoDup_snoc : forall {A} (l : list A) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
  Proof.
    induction l as [|a l IH]; intros x ND NI; cbn.
    - constructor; [intros H; apply list_elem_of_In in H; destruct H | constructor].
    - inversion ND as [|a' l' Hni ND']; subst. constructor.
      + intros H. apply list_elem_of_In in H. apply in_app_iff in H. destruct H as [H|[H|[]]]; [apply Hni; apply list_elem_of_In; exact H | apply NI; left; symmetry; exact H].
      + apply IH; [exact ND' | intros H; apply NI; right; exact H].
  Qed.

  #[using="fs_consts frame_geom"] Lemma frames_ok_add : forall rho m m' frs f p,
    LASM2.wr_agree m m' (fs_flag FS (f_cls f) p) 1 -> fs_ok FS m ->
    frames_ok U FS rho m frs -> frame_okR U FS rho m' f p -> ~ live_at FS rho frs (f_cls f) p ->
    m' (w64 (fs_flag FS (f_cls f) p)) = Some (Z_to_bv 8 1) ->
    frames_ok U FS rho m' (frs ++ [f]).
  Proof.
    intros rho m m' frs f p HW HFS ((ps & F2 & ND) & FL & REST) Hf NL FLAG.
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    pose proof Hf as (Hat & Hk & _). pose proof Hat as (Hp & Hb & Hfl).
    pose proof (LASM2.flag_geom FS (f_cls f) p Hk Hp) as (L1 & L2 & L3). rewrite HFL in L1, L3. rewrite HFR in L2.
    pose proof (proj1 (LASM2.Forall2_nth _ _ _) F2) as [L F2n].
    (* [comment removed for export] *)
    assert (OLD : forall j h q, nth_error frs j = Some h -> nth_error ps j = Some q -> (f_cls h, q) <> (f_cls f, p) /\ frame_okR U FS rho m' h q).
    { intros j h q Hh Hq. pose proof (F2n j h q Hh Hq) as Hh'. pose proof Hh' as ((Hq' & Hbq & Hflq) & Kh & _).
      assert (NE : (f_cls h, q) <> (f_cls f, p)).
      { intros E. apply NL. exists h. split; [eapply nth_error_In; exact Hh|]. injection E; intros E1 E0. split; [exact E0|]. rewrite <- E1. split; [exact Hq'|]. split; assumption. }
      split; [exact NE|]. eapply LASM2.frame_okR_wr; [exact HW | exact HFS | exact Hh' |].
      destruct (LASM2.slot_apart FS (f_cls h) q (f_cls f) p Kh Hq' Hk Hp NE) as [D DF].
      pose proof (frame_geom (f_cls h) q Kh Hq') as (H1 & H2 & _). rewrite HFR in H1.
      pose proof (LASM2.sh_frame FS (f_cls h) q Kh Hq' (fo_align _ _ HFS)) as (T1 & T2 & T3 & _).
      pose proof (LASM2.flag_geom FS (f_cls h) q Kh Hq') as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
      destruct (LASM2.f_size_cls h Kh) as [Eh1 Eh2]. unfold LASM2.frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq, T1.
      assert (F8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia).
      unfold sh in T3. rewrite ESH, HSH in T3. unfold SHB in *. lia. }
    split; [|split].
    - exists (ps ++ [p]). split.
      + apply LASM2.Forall2_nth. split; [rewrite !length_app; cbn; lia|].
        intros j x y Hx Hy. destruct (Nat.lt_ge_cases j (length frs)) as [Hj|Hj].
        * rewrite nth_error_app1 in Hx by exact Hj. rewrite nth_error_app1 in Hy by lia. exact (proj2 (OLD j x y Hx Hy)).
        * rewrite nth_error_app2 in Hx by exact Hj. rewrite nth_error_app2 in Hy by lia.
          destruct (j - length frs)%nat eqn:E1; [|destruct n; discriminate]. replace (j - length ps)%nat with 0%nat in Hy by lia.
          cbn in Hx, Hy. injection Hx; intros <-. injection Hy; intros <-. exact Hf.
      + rewrite map_app. cbn [map]. rewrite combine_snoc by (rewrite length_map; exact L). apply NoDup_snoc; [exact ND|].
        intros Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
        assert (Hjl : (j < length ps)%nat).
        { pose proof (proj1 (nth_error_Some _ j) ltac:(rewrite Hj; discriminate)) as X. rewrite length_combine, length_map in X. lia. }
        destruct (nth_error frs j) as [h|] eqn:Hh; [|apply nth_error_None in Hh; lia].
        destruct (nth_error ps j) as [q|] eqn:Hq; [|apply nth_error_None in Hq; lia].
        pose proof (LASM2.nth_error_combine (map f_cls frs) ps j (f_cls h) q ltac:(rewrite nth_error_map, Hh; reflexivity) Hq) as X.
        rewrite X in Hj. injection Hj; intros E1 E2. apply (proj1 (OLD j h q Hh Hq)). rewrite E1, E2. reflexivity.
    - intros k q Hk' Hq'. pose proof (LASM2.flag_geom FS k q Hk' Hq') as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
      assert (LIVE : live_at FS rho (frs ++ [f]) k q <-> live_at FS rho frs k q \/ (k, q) = (f_cls f, p)).
      { split.
        - intros (h & Hin & Hkh & Hath). apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [left; exists h; split; [exact Hin | split; assumption]|].
          right. rewrite <- Hkh. f_equal. eapply LASM2.frame_at_inj; [exact Hath | exact Hat | exact Hk].
        - intros [(h & Hin & Hkh & Hath)|E]; [exists h; split; [apply in_app_iff; left; exact Hin | split; assumption]|].
          injection E; intros -> ->. exists f. split; [apply in_app_iff; right; left; reflexivity|]. split; [reflexivity | exact Hat]. }
      destruct (FL k q Hk' Hq') as [X1 X2]. split.
      + intros HL. apply LIVE in HL. destruct HL as [HL|E].
        * assert (NE : (k, q) <> (f_cls f, p)) by (intros E; apply NL; injection E; intros -> ->; exact HL).
          destruct (LASM2.slot_apart FS k q (f_cls f) p Hk' Hq' Hk Hp NE) as [_ DF].
          eapply LASM2.mem_byte_wr; [exact HW | apply X1; exact HL | lia | lia].
        * injection E; intros -> ->. exact FLAG.
      + intros HNL. assert (NE : (k, q) <> (f_cls f, p)) by (intros E; apply HNL; apply LIVE; right; exact E).
        destruct (LASM2.slot_apart FS k q (f_cls f) p Hk' Hq' Hk Hp NE) as [_ DF].
        eapply LASM2.mem_byte_wr; [exact HW | apply X2; intros HL; apply HNL; apply LIVE; left; exact HL | lia | lia].
    - intros j Hj Hnf. eapply LASM2.mem_byte_wr; [exact HW | apply REST; [exact Hj | exact Hnf] | lia |].
      specialize (Hnf (f_cls f) p Hk Hp). lia.
  Qed.
  (* [comment removed for export] *)
  Hypothesis HMALLOC : forall k, (k = 1 \/ k = 4 \/ k = 5) -> malloc_stmt k.
  Hypothesis MALLOCS : forall pc k, LAC.mallocs_at (ue_malloc U) pc = Some k -> pc = MALLOC_A k.

  #[using="Type"] Lemma zeros_spec : forall n t b, nth_error (LAC.zeros n) t = Some b -> b = 0.
  Proof. intros n t b H. unfold LAC.zeros in H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.
  #[using="Type"] Lemma Some_inj' : forall {X} (x y : X), Some x = Some y -> x = y.
  Proof. intros X x y H. injection H as E. exact E. Qed.

  #[using="UOK SEGS RO TP RTCOV fs_consts frame_geom HMALLOC MALLOCS"] Theorem apply_malloc_sound : forall k rho S S' ms,
    wf_state S = true -> R U G FS M0 rho S ms -> apply_malloc U S k = Some S' ->
    exists ms' rho', msteps (ue_segs U) ms ms' /\ R U G FS M0 rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat.
  Proof.
    intros k rho S S' ms Hwf HR H.
    destruct (wf_parts S Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    pose proof (r_vs _ _ _ _ _ _ _ HR) as HVS. destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    (* [comment removed for export] *)
    unfold apply_malloc, malloc_core in H.
    destruct ((Z.eqb k 1 ||| Z.eqb k 4 ||| Z.eqb k 5) &&& Z.leb 0 (ue_malloc_fr U))%bool eqn:HK; [|discriminate]. cbn [negb] in H.
    apply andb_prop in HK as [HK HMFR0]. apply Z.leb_le in HMFR0.
    destruct (LAC.mallocs_at (ue_malloc U) (s_pc S)) as [k'|] eqn:HMA; [|discriminate]. destruct (Z.eqb_spec k' k) as [->|]; [|discriminate]. cbn [negb] in H.
    pose proof (MALLOCS _ _ HMA) as HPC.
    assert (Hk : k = 1 \/ k = 4 \/ k = 5).
    { repeat (apply orb_prop in HK as [HK|HK]); apply Z.eqb_eq in HK; auto. }
    assert (FSN : 512 <= fs_N k) by (unfold fs_N; destruct Hk as [-> |[-> | ->]]; cbn; lia).
    assert (FSZ : fs_fsz k = 2 ^ (6 + k)) by reflexivity.
    assert (FSZ128 : 128 <= fs_fsz k <= 2048) by (rewrite FSZ; destruct Hk as [-> |[-> | ->]]; cbn; lia).
    assert (SHN : 2 ^ (3 + k) = fs_fsz k / 8) by (rewrite FSZ; destruct Hk as [-> |[-> | ->]]; reflexivity).
    assert (K15 : 1 <= k <= 5) by lia.
    hide Hk.
    destruct (sp_off S) as [ksp|] eqn:Hsp; [|discriminate].
    destruct (getreg S 1) as [|lra|? ? ? ?|? ?] eqn:G1; try discriminate.
    destruct (is_const lra) as [ra|] eqn:Hra; [|discriminate].
    destruct (Z.eqb_spec (ra mod 4) 0) as [HRA4|]; [|discriminate]. destruct (Z.leb_spec 0 ra) as [HRA0|]; [|discriminate].
    destruct (Z.ltb_spec ra two64) as [HRA64|]; [|discriminate]. cbn [andb negb] in H.
    destruct (in_window U (ksp - ue_malloc_fr U) (ue_malloc_fr U)) eqn:HWIN; [|discriminate].
    destruct (Z.eqb_spec (ksp mod 16) 0) as [HK16|]; [|discriminate]. cbn [andb negb] in H.
    destruct (reg_is_lit S 4 (ue_tp U)) eqn:HTP; [|discriminate]. cbn [negb] in H.
    destruct (Nat.leb_spec (length (s_frames S)) 2) as [HLEN2|]; [|discriminate]. cbn [negb] in H.
    destruct (forallb (fun c => Z.leb (c_off c + c_w c) ksp ||| Z.leb ksp (c_off c)) (s_stk S)) eqn:NOSTRc; [|discriminate].
    destruct (forallb (fun a => Z.leb (ar_hi a) ksp ||| Z.leb ksp (ar_lo a)) (s_arrs S)) eqn:NOSTRa; [|discriminate]. cbn [andb negb] in H.
    destruct (s_resv S) eqn:ERESV; [discriminate|].
    set (iG := Itv (Some 0x19a00) (Some 0x1fffffffffe)) in H. set (iQ := Itv (Some 0x669000) (Some 0x7fffffffffff)) in H.   (* [comment removed for export] *)
    apply Some_inj' in H. rename H into ES'.
    (* [comment removed for export] *)
    pose proof (uo_mfr U UOK) as EMFR. rewrite EMFR in HWIN, HMFR0. pose proof (uo_frA U UOK) as EFR.
    apply LASMT.in_window_sound in HWIN. rewrite EFR in HWIN. destruct HWIN as [WIN1 WIN2]. unfold MALLOC_FR, FR_A in WIN1, WIN2.
    set (sp0 := rho SYM_SP0) in *. set (sp := sp0 + ksp).
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as [SP1 SP2]. rewrite EFR in SP1. pose proof (r_align _ _ _ _ _ _ _ HR) as [AL1 AL2]. fold sp0 in SP1, SP2, AL1. unfold FR_A in SP1.
    pose proof (r_apart _ _ _ _ _ _ _ HR) as (AP1 & AP2 & AP3 & AP4 & AP5). fold sp0 in AP1, AP2, AP4. unfold IMGHI_A, app_mem, LOSH_A in AP3. rewrite HKHI in AP1, AP3. rewrite HHI in AP2, AP3. rewrite HLEN in AP4, AP5. unfold FR_A in AP1, AP4.
    hide AP3. hide AP4. hide AP5.
    pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS. pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    (* [comment removed for export] *)
    pose proof (reg_ok rho S ms 1 HR ltac:(lia)) as R1. rewrite G1 in R1. cbn [val_ok] in R1. rewrite (is_const_sound rho lra ra Hra) in R1.
    pose proof (reg_ok rho S ms 2 HR ltac:(lia)) as R2.
    pose proof (LASM2.classify_spec rho (s_frames S) (getreg S 2) _ (s_next S) R2 (LASS.getreg_below S 2 Hwf) W18 Wfr) as CL2.
    unfold sp_off in Hsp. destruct (classify (s_frames S) (getreg S 2)) as [[k'|?|?|?|? ?|? ?|? ?|?|?|?]|]; try discriminate. injection Hsp as ->. fold sp0 in CL2.
    pose proof (reg_lit rho S ms 4 (ue_tp U) HR ltac:(lia) HTP) as R4. rewrite TP in R4.
    (* [comment removed for export] *)
    pose proof (r_resv _ _ _ _ _ _ _ HR) as RRESV. rewrite ERESV in RRESV. cbn [resv_ok] in RRESV.
    destruct (ms_resv ms) eqn:EMR; [destruct RRESV|].
    pose proof (ms_eta ms (r_svc _ _ _ _ _ _ _ HR) EMR) as ETA. set (fx := mkFP (ms_fregs ms) (ms_fcsr ms)) in ETA.
    rewrite (r_pc _ _ _ _ _ _ _ HR), HPC in ETA.
    (* [comment removed for export] *)
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof RF as (_ & FL & _).
    set (fl := fun j : Z => match ms_mem ms (w64 (fs_flag FS k j)) with Some b => bv_unsigned b | None => 0 end).
    assert (FLOK : forall j, 0 <= j < fs_N k -> mem_byte (ms_mem ms) (fs_flag FS k j) (fl j) /\ (fl j = 0 \/ fl j = 1)
                              /\ (fl j = 0 <-> ~ live_at FS rho (s_frames S) k j)).
    { intros j Hj. destruct (FL k j Hk Hj) as [X1 X2].
      destruct (live_at_dec rho (s_frames S) k j) as [L|NL].
      - pose proof (X1 L) as M. unfold mem_byte in M |- *. rewrite LASM2.w64_same in M |- *. subst fl. cbv beta. rewrite M.
        change (bv_unsigned (Z_to_bv 8 1)) with 1. split; [reflexivity|]. split; [right; reflexivity|]. split; [intros; lia | intros X; exfalso; exact (X L)].
      - pose proof (X2 NL) as M. unfold mem_byte in M |- *. rewrite LASM2.w64_same in M |- *. subst fl. cbv beta. rewrite M.
        change (bv_unsigned (Z_to_bv 8 0)) with 0. split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; exact NL | reflexivity]. }
    (* [comment removed for export] *)
    assert (FREE : exists j, 0 <= j < fs_N k /\ fl j = 0).
    { destruct (live_at_dec rho (s_frames S) k 0) as [L0|N0]; [|exists 0; split; [lia | apply (proj2 (proj2 (proj2 (FLOK 0 ltac:(lia))))); exact N0]].
      destruct (live_at_dec rho (s_frames S) k 1) as [L1|N1]; [|exists 1; split; [lia | apply (proj2 (proj2 (proj2 (FLOK 1 ltac:(lia))))); exact N1]].
      destruct (live_at_dec rho (s_frames S) k 2) as [L2|N2]; [|exists 2; split; [lia | apply (proj2 (proj2 (proj2 (FLOK 2 ltac:(lia))))); exact N2]].
      exfalso. destruct L0 as (f0 & I0 & K0 & A0). destruct L1 as (f1 & I1 & K1 & A1). destruct L2 as (f2 & I2 & K2 & A2).
      assert (D : forall fa fb pa pb, f_cls fa = k -> frame_at FS rho fa pa -> frame_at FS rho fb pb -> pa <> pb -> fa <> fb).
      { intros fa fb pa pb Ka Ha Hb Hne ->. apply Hne. eapply LASM2.frame_at_inj; [exact Ha | exact Hb | rewrite Ka; exact Hk]. }
      pose proof (three_in_length (s_frames S) f0 f1 f2 I0 I1 I2 (D _ _ _ _ K0 A0 A1 ltac:(lia)) (D _ _ _ _ K1 A1 A2 ltac:(lia)) (D _ _ _ _ K0 A0 A2 ltac:(lia))). lia. }
    (* [comment removed for export] *)
    assert (MDEF : mem_def (ms_mem ms) (sp - MALLOC_FR) MALLOC_FR).
    { intros i Hi. unfold MALLOC_FR in Hi |- *. destruct (proj1 (r_win _ _ _ _ _ _ _ HR) (sp - 256 + i) ltac:(fold sp0; rewrite EFR; unfold FR_A, sp; lia)) as [b Hb].
      exists b. rewrite LASM2.w64_same. exact Hb. }
    destruct (HMALLOC k Hk fx (ms_regs ms) (ms_mem ms) (ms_rom ms) (w64 ra) sp FS fl
                R1 ltac:(rewrite w64_lit by (unfold LAI.two64 in HRA64; rewrite two64_eq in HRA64; lia); exact HRA4)
                CL2 ltac:(unfold sp; rewrite Z.add_mod, AL1, HK16 by lia; reflexivity) ltac:(unfold MALLOC_FR, KHI_A, sp; lia) ltac:(unfold HIEND_A, sp; lia)
                MDEF R4 (R_rt_ok _ _ _ HR) (R_ro_ok _ _ _ HR)
                ltac:(eapply malloc_ctx_mono; [exact (r_mctx _ _ _ _ _ _ _ HR) | fold sp0; unfold MALLOC_FR, FR_A, sp; lia | fold sp0; unfold sp; lia])
                (fo_tls _ _ HFS) (fo_align _ _ HFS) (fo_lo _ _ HFS) (fo_app _ _ HFS) (fo_hi _ _ HFS) ltac:(unfold hide in AP4; unfold MALLOC_FR, FS_LEN, sp; lia)
                (fo_def _ _ HFS) (fo_shdef _ _ HFS) (fo_log _ _ HFS) (fo_gc _ _ HFS)
                ltac:(intros j Hj; pose proof (FLOK j Hj) as (X & Y & _); exact (conj X Y)) FREE)
      as (regs' & mem' & p & MS & KEEP & Hp & FLp & A0 & FLAG1 & QCELL & SHZ & [FRAME GROW]).
    unfold LibIfaceA.w64, LASEM.w64 in MS, ETA. rewrite <- ETA in MS.
    assert (NLp : ~ live_at FS rho (s_frames S) k p) by (apply (proj1 (proj2 (proj2 (FLOK p Hp)))); exact FLp).
    pose proof (frame_geom k p Hk Hp) as (FG1 & FG2 & FG3 & FG4 & FG5 & FG6). rewrite HFR in FG1. rewrite HLEN in FG2.
    pose proof (LASM2.sh_frame FS k p Hk Hp (fo_align _ _ HFS)) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (LASM2.flag_geom FS k p Hk Hp) as (L1 & L2 & L3). rewrite HFL in L1, L3. rewrite HFR in L2.
    assert (F8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia).
    assert (F8' : 0xcd000 <= FS / 8) by (apply Z.div_le_lower_bound; lia).   (* [comment removed for export] *)
    unfold sh in S2, S3. rewrite ESH, HSL in S2. rewrite ESH, HSH in S3. unfold SHB in S1, S2, S3.
    set (B := fs_frame FS k p) in *. set (Q := fs_flag FS k p) in *.
    (* [comment removed for export] *)
    assert (B64 : B = 64 * (B / 64)).
    { pose proof (fo_align _ _ HFS) as AL. apply Z.mod_divide in FG4; [|lia]. apply Z.mod_divide in AL; [|lia].
      destruct FG4 as [u Hu]. destruct AL as [v Hv]. replace B with (64 * (u + 64 * v)) by lia. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    destruct (fresh_sound rho S iG (B / 64) HVS ltac:(subst iG; unfold in_itv; cbn [ilo ihi]; lia)) as (rho1 & V1 & X1 & VS1 & Fg & N1).
    set (T1 := snd (fresh S iG)) in *. set (g := fst (fresh S iG)) in *.
    assert (Hwf1 : wf_state T1 = true) by (eapply LASS.wf_vext; [exact Hwf | exact X1 | exact VS1]).
    destruct (fresh_sound rho1 T1 iQ Q VS1 ltac:(subst iQ; unfold in_itv; cbn [ilo ihi]; lia)) as (rho2 & V2 & X2 & VS2 & Fq & N2).
    set (T2 := snd (fresh T1 iQ)) in *. set (q := fst (fresh T1 iQ)) in *.
    pose proof (vext_trans _ _ _ _ _ _ X1 X2) as X12.
    assert (HR2 : R U G FS M0 rho2 T2 ms) by (eapply R_vext; [exact Hwf1 | eapply R_vext; [exact Hwf | exact HR | exact X1 | exact VS1] | exact X2 | exact VS2]).
    pose proof (proj1 X12) as AG0.
    assert (HG : forall x, (x < NGLOB)%nat -> rho2 x = rho x) by (intros x Hx; apply AG0; clear - Hx W18; lia).
    assert (Eg : rho2 g = B / 64) by (rewrite Fg; rewrite (proj1 X2) by (rewrite N1; lia); exact V1).
    assert (Eq : rho2 q = Q) by (rewrite Fq; exact V2).
    assert (GSP : rho2 SYM_SP0 = sp0) by (apply HG; unfold SYM_SP0, NGLOB; lia).
    assert (GN : rho2 SYM_N = rho SYM_N) by (apply HG; unfold SYM_N, NGLOB; lia). assert (GD : rho2 SYM_DATA = rho SYM_DATA) by (apply HG; unfold SYM_DATA, NGLOB; lia).
    (* [comment removed for export] *)
    set (T3 := drop_below T2 ksp).
    assert (HR3 : R U G FS M0 rho2 T3 ms) by (apply LASM2.drop_below_sound; exact HR2).
    destruct X12 as (AG & X12b & X12pc & X12regs & Estk & Earrs & X12abs & X12resv & X12d & Epc & Epay & Efr).
    assert (ST3s : s_stk T3 = cells_drop_below (s_stk S) ksp) by (rewrite <- Estk; reflexivity).
    assert (ST3a : s_arrs T3 = filter (fun a => negb (Z.leb (ar_hi a) ksp)) (s_arrs S)) by (rewrite <- Earrs; reflexivity).
    assert (ST3f : s_frames T3 = s_frames S) by (rewrite <- Efr; reflexivity).
    assert (CELLS3 : forall c, In c (s_stk T3) -> ksp <= c_off c).
    { intros c Hc. rewrite ST3s in Hc. unfold cells_drop_below in Hc. apply LASM2.In_filterP in Hc as [Hc Hkeep]. cbv beta in Hkeep.
      pose proof (LASMT.forallb_In _ _ _ _ NOSTRc Hc) as NS. cbv beta in NS.
      destruct (Z.leb_spec (c_off c + c_w c) ksp); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
    assert (ARRS3 : forall a, In a (s_arrs T3) -> ksp <= ar_lo a).
    { intros a Ha. rewrite ST3a in Ha. apply LASM2.In_filterP in Ha as [Ha Hkeep]. cbv beta in Hkeep.
      pose proof (LASMT.forallb_In _ _ _ _ NOSTRa Ha) as NS. cbv beta in NS.
      destruct (Z.leb_spec (ar_hi a) ksp); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
    (* [comment removed for export] *)
    set (m0 := ms_mem ms) in *.
    set (r1 := (sp - MALLOC_FR, sp)) in *. set (r2 := (fs_hint FS k, fs_hint FS k + 8)) in *. set (r3 := (Q, Q + 1)) in *.
    set (r4 := (B + 24, B + 32)) in *. set (r5 := (B + fs_fsz k - 8, B + fs_fsz k)) in *. set (r6 := (sh B, sh B + fs_fsz k / 8)) in *.
    assert (FRAME' : forall x : word, ~ LibIface.in_ranges (bv_unsigned x) [r1; r2; r4; r5; r6; r3] -> mem' x = m0 x).
    { intros x Hx. apply FRAME. intros (r & Hr & Hin). apply Hx. exists r. split; [|exact Hin]. cbn [In] in Hr |- *. tauto. }
    set (m1 := patch m0 mem' r1). set (m2 := patch m1 mem' r2). set (m3 := patch m2 mem' r4). set (m4 := patch m3 mem' r5). set (m5 := patch m4 mem' r6). set (m6 := patch m5 mem' r3).
    assert (BW0 : between m0 mem' m0) by (intros x; left; reflexivity).
    pose proof (patch_between _ _ _ r1 BW0) as BW1. pose proof (patch_between _ _ _ r2 BW1) as BW2. pose proof (patch_between _ _ _ r4 BW2) as BW3.
    pose proof (patch_between _ _ _ r5 BW3) as BW4. pose proof (patch_between _ _ _ r6 BW4) as BW5. pose proof (patch_between _ _ _ r3 BW5) as BW6.
    fold m1 in BW1, BW2. fold m2 in BW2, BW3. fold m3 in BW3, BW4. fold m4 in BW4, BW5. fold m5 in BW5, BW6. fold m6 in BW6.
    assert (END : forall x, m6 x = mem' x).
    { intros x. pose proof (patches_end [r1; r2; r4; r5; r6; r3] m0 mem' m0 BW0 FRAME' x) as X. cbn [patches] in X. exact X. }
    pose proof (patch_wr_agree m0 mem' m0 (sp - MALLOC_FR) sp BW0 GROW ltac:(unfold MALLOC_FR, sp; lia) ltac:(unfold MALLOC_FR; lia) ltac:(unfold sp; lia)) as HW1.
    fold r1 m1 in HW1. replace (sp - (sp - MALLOC_FR)) with MALLOC_FR in HW1 by lia.
    pose proof (patch_wr_agree m0 mem' m1 (fs_hint FS k) (fs_hint FS k + 8) BW1 GROW ltac:(unfold fs_hint; lia) ltac:(lia) ltac:(unfold fs_hint; lia)) as HW2.
    fold r2 m2 in HW2. replace (fs_hint FS k + 8 - fs_hint FS k) with 8 in HW2 by lia. unfold fs_hint in HW2.
    pose proof (patch_wr_agree m0 mem' m2 (B + 24) (B + 32) BW2 GROW ltac:(lia) ltac:(lia) ltac:(lia)) as HW3.
    fold r4 m3 in HW3. replace (B + 32 - (B + 24)) with 8 in HW3 by lia.
    pose proof (patch_wr_agree m0 mem' m3 (B + fs_fsz k - 8) (B + fs_fsz k) BW3 GROW ltac:(lia) ltac:(lia) ltac:(lia)) as HW4.
    fold r5 m4 in HW4. replace (B + fs_fsz k - (B + fs_fsz k - 8)) with 8 in HW4 by lia.
    pose proof (patch_wr_agree m0 mem' m4 (sh B) (sh B + fs_fsz k / 8) BW4 GROW ltac:(unfold sh; rewrite ESH; unfold SHB; lia) ltac:(lia) ltac:(unfold sh; rewrite ESH; unfold SHB; lia)) as HW5.
    fold r6 m5 in HW5. replace (sh B + fs_fsz k / 8 - sh B) with (fs_fsz k / 8) in HW5 by lia. unfold sh in HW5. rewrite ESH in HW5.
    pose proof (patch_wr_agree m0 mem' m5 Q (Q + 1) BW5 GROW ltac:(lia) ltac:(lia) ltac:(lia)) as HW6.
    fold r3 m6 in HW6. replace (Q + 1 - Q) with 1 in HW6 by lia.
    (* [comment removed for export] *)
    pose proof (proj1 (proj2 (r_pay _ _ _ _ _ _ _ HR3))) as P2. rewrite GSP, EFR, GN, GD in P2. unfold FR_A in P2.
    pose proof (r_data _ _ _ _ _ _ _ HR3) as (D1 & D2 & D3). rewrite ?GN, ?GD in D1. rewrite ?GN, ?GD in D2. rewrite ?GN in D3.
    assert (HR4 : R U G FS M0 rho2 T3 (ms_with_mem ms m1)).
    { eapply (R_wr_same _ _ _ _ _ _ HR3 HW1); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a Ha C1 C2; pose proof (ARRS3 a Ha) | |];
      [left; unfold MALLOC_FR, FR_A, sp; lia | intros x Hx; left; rewrite EFR; unfold MALLOC_FR, FR_A, sp in *; lia | unfold sp, MALLOC_FR; lia
            | unfold sp, MALLOC_FR; lia | unfold sp, MALLOC_FR; lia | unfold sp, MALLOC_FR; lia |].
      unfold hide in AP4. eapply LASM2.frames_ok_wr_apart; [exact HW1 | exact HFS | exact (r_frames _ _ _ _ _ _ _ HR3) | rewrite HFL; unfold sp, MALLOC_FR; lia | right; unfold sh; rewrite ESH, HSH; unfold SHB, sp, MALLOC_FR; lia]. }
    assert (FS1 : fs_ok FS m1) by (eapply LASM2.fs_ok_wr; [exact HW1 | exact HFS | eapply LASM2.R_geom; exact HR3 | left; rewrite GSP; unfold MALLOC_FR, FR_A, sp; lia]).
    assert (HR5 : R U G FS M0 rho2 T3 (ms_with_mem ms m2)).
    { eapply (R_wr_same _ _ _ _ _ _ HR4 HW2); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a Ha C1 C2; pose proof (ARRS3 a Ha) | |];
      [right; right; right; right; left; lia | intros x Hx; right; right; left; lia | lia | unfold hide in AP4; lia | unfold hide in AP4; lia | unfold hide in AP5; lia |].
      eapply LASM2.frames_ok_wr_apart; [exact HW2 | exact FS1 | exact (r_frames _ _ _ _ _ _ _ HR4) | rewrite HFL; lia | unfold sh; rewrite ESH, HSL, HSH; unfold SHB; pose proof LOAPP as [ZL|ZH]; [left; lia | right; lia]]. }   (* [comment removed for export] *)
    assert (FS2 : fs_ok FS m2) by (eapply LASM2.fs_ok_wr; [exact HW2 | exact FS1 | eapply LASM2.R_geom; exact HR4 | right; right; right; right; left; cbn [ms_mem ms_with_mem]; lia]).
    assert (NLp2 : ~ live_at FS rho2 (s_frames S) k p).
    { intros L. apply NLp. apply (proj2 (LASM.live_at_agree G FS (s_next S) rho rho2 (s_frames S) k p Wfr AG)). exact L. }
    assert (HR6 : R U G FS M0 rho2 T3 (ms_with_mem ms m3)).
    { eapply (R_wr_same _ _ _ _ _ _ HR5 HW3); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a Ha C1 C2; pose proof (ARRS3 a Ha) | |];
      [right; right; left; lia | intros x Hx; right; right; left; lia | lia | unfold hide in AP4; lia | unfold hide in AP4; lia | unfold hide in AP5; lia |].
      rewrite ST3f. eapply (frames_ok_wr_slot rho2 m2 m3 _ _ (s_frames S) k p HW3 FS2); [| exact Hk | exact Hp | exact NLp2 | left; subst B; lia].
      rewrite <- ST3f. exact (r_frames _ _ _ _ _ _ _ HR5). }
    assert (FS3 : fs_ok FS m3) by (eapply LASM2.fs_ok_wr; [exact HW3 | exact FS2 | eapply LASM2.R_geom; exact HR5 | right; right; left; cbn [ms_mem ms_with_mem]; lia]).
    assert (HR7 : R U G FS M0 rho2 T3 (ms_with_mem ms m4)).
    { eapply (R_wr_same _ _ _ _ _ _ HR6 HW4); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a Ha C1 C2; pose proof (ARRS3 a Ha) | |];
      [right; right; left; lia | intros x Hx; right; right; left; lia | lia | unfold hide in AP4; lia | unfold hide in AP4; lia | unfold hide in AP5; lia |].
      rewrite ST3f. eapply (frames_ok_wr_slot rho2 m3 m4 _ _ (s_frames S) k p HW4 FS3); [| exact Hk | exact Hp | exact NLp2 | left; subst B; lia].
      rewrite <- ST3f. exact (r_frames _ _ _ _ _ _ _ HR6). }
    assert (FS4 : fs_ok FS m4) by (eapply LASM2.fs_ok_wr; [exact HW4 | exact FS3 | eapply LASM2.R_geom; exact HR6 | right; right; left; cbn [ms_mem ms_with_mem]; lia]).
    assert (HR8 : R U G FS M0 rho2 T3 (ms_with_mem ms m5)).
    { eapply (R_wr_same _ _ _ _ _ _ HR7 HW5); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a Ha C1 C2; pose proof (ARRS3 a Ha) | |];
      [right; right; right; right; right; unfold sh; rewrite ESH, HSL, HSH; unfold SHB; lia | intros x Hx; right; right; right; unfold sh; rewrite ESH, HSL, HSH; unfold SHB in *; lia
            | unfold SHB; lia | unfold SHB; lia | unfold SHB; lia | unfold hide in AP3; unfold SHB; lia |].
      rewrite ST3f. eapply (frames_ok_wr_slot rho2 m4 m5 _ _ (s_frames S) k p HW5 FS4); [| exact Hk | exact Hp | exact NLp2 | right; unfold sh; rewrite ESH; subst B; unfold SHB; lia].
      rewrite <- ST3f. exact (r_frames _ _ _ _ _ _ _ HR7). }
    assert (FS5 : fs_ok FS m5) by (eapply LASM2.fs_ok_wr; [exact HW5 | exact FS4 | eapply LASM2.R_geom; exact HR7 | right; right; right; right; right; cbn [ms_mem ms_with_mem]; unfold sh; rewrite ESH, HSL, HSH; unfold SHB; lia]).
    (* [comment removed for export] *)
    set (fr := Frame g k [Cell (2 ^ (6 + k) - 8) 8 (LV (lvar q))] [] (LAC.zeros (Z.to_nat (2 ^ (3 + k)))) q).
    set (T4 := set_frames T3 (s_frames T3 ++ [fr])).
    assert (M6Q : m6 (w64 Q) = Some (Z_to_bv 8 1)).
    { rewrite END. pose proof FLAG1 as M. unfold mem_byte in M. rewrite LASM2.w64_same in M. exact M. }
    assert (HW6' : LASM2.wr_agree mem' m6 sp0 0).
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; apply END | intros x b Hb; exists b; rewrite END; exact Hb]. }
    assert (FROK : frame_okR U FS rho2 m6 fr p).
    { subst fr. unfold frame_okR, frame_at. cbn [f_sym f_cls f_cells f_arrs f_sh f_flag]. unfold f_size, f_shn. cbn [f_cls]. rewrite Eg, Eq, <- B64.
      rewrite <- FSZ, SHN.
      split; [split; [exact Hp | split; reflexivity]|]. split; [exact Hk|]. split; [|split; [constructor | split]].
      - constructor; [|constructor]. unfold cell_ok; cbn [c_off c_w c_val]. split; [lia|]. split; [lia|]. split; [lia|].
        pose proof (cellN_u64 SEGS_A mem' (B + fs_fsz k - 8) Q QCELL ltac:(lia) ltac:(lia) ltac:(lia)) as C. unfold BnMem.BM.cellN in C.
        destruct C as (bs & Hrd & Hv). exists bs. split.
        + change (Z.to_nat 8) with 8%nat. replace (B + (fs_fsz k - 8)) with (B + fs_fsz k - 8) by lia.
          rewrite (LASM2.rdn_wr_out_g (ue_segs U) mem' m6 sp0 0 (B + fs_fsz k - 8) 8 HW6'); [| lia | cbn; lia | cbn; unfold hide in AP4; lia].
          rewrite <- SEGS in Hrd. exact Hrd.
        + cbn [val_bytes_ok]. split; [rewrite (rdn_length _ _ _ _ _ Hrd); reflexivity|]. rewrite lvar_sound, Eq. change (2 ^ (8 * 8)) with (2 ^ 64). exact Hv.
      - cbn [f_sh]. unfold LAC.zeros. rewrite repeat_length. lia.
      - intros t b Ht. pose proof (zeros_spec _ _ _ Ht) as ->. split; [lia|].
        pose proof (proj1 (nth_error_Some _ t) ltac:(rewrite Ht; discriminate)) as Tl. unfold LAC.zeros in Tl. rewrite repeat_length in Tl.
        rewrite END. pose proof (SHZ (Z.of_nat t) ltac:(lia)) as M. unfold mem_byte in M. rewrite LASM2.w64_same in M. exact M. }
    assert (FR6 : frames_ok U FS rho2 m6 (s_frames T3 ++ [fr])).
    { rewrite ST3f. eapply (frames_ok_add rho2 m5 m6 (s_frames S) fr p); [exact HW6 | exact FS5 | | exact FROK | exact NLp2 | exact M6Q].
      rewrite <- ST3f. exact (r_frames _ _ _ _ _ _ _ HR8). }
    assert (HR9 : R U G FS M0 rho2 T4 (ms_with_mem ms m6)).
    { unfold hide in AP4, AP5. eapply (LASM2.R_wr U G M0 FS UOK rho2 T3 T4 (ms_with_mem ms m5) m6 Q 1 HR8 HW6); try reflexivity; rewrite ?GSP.
      - right; right; right; left. rewrite HFL, HFR. lia.
      - intros x Hx. right; right; left. rewrite HLEN. lia.
      - change (s_stk T4) with (s_stk T3). apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR8) c Hc) as Hcell.
        rewrite GSP in Hcell. pose proof Hcell as (C1 & C2 & _).
        eapply LASM2.cell_ok_wr; [exact HW6 | exact Hcell | rewrite EFR in *; unfold FR_A in *; lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
      - change (s_arrs T4) with (s_arrs T3). apply Forall_forall. intros a Ha. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR8) a Ha) as Harr.
        rewrite GSP in Harr. pose proof Harr as (C1 & C2 & _).
        eapply LASM2.arr_okg_wr; [exact HW6 | exact Harr | rewrite EFR in *; unfold FR_A in *; lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
      - change (s_pcache T4) with (s_pcache T3). change (s_pay T4) with (s_pay T3).
        eapply LASM2.payload_ok_wr; [exact HW6 | exact (r_pay _ _ _ _ _ _ _ HR8) | rewrite GD; lia | rewrite GD, GN; lia | rewrite GD, GN; lia].
      - change (s_abs T4) with (s_abs T3). eapply LASM2.abs_ok_wr; [exact UOK | exact HW6 | exact (r_abs _ _ _ _ _ _ _ HR8) | lia].
      - intros Hlo. exfalso. lia.
      - exact FR6. }
    assert (HR10 : R U G FS M0 rho2 T4 (ms_with_mem ms mem')).
    { pose proof (R_mem_ext rho2 T4 (ms_with_mem ms m6) mem' HR9 ltac:(intros x; cbn; symmetry; apply END)) as X. exact X. }
    (* [comment removed for export] *)
    set (rs' := list_set (list_set (havoc_regs (s_regs S) 0) 4 (alit (ue_tp U))) 10 (LV (lscale 64 (lvar g)))).
    assert (ES : S' = set_pc (set_regs T4 rs') ra).
    { subst S' T4 T3 T2 T1 g q rs' fr. unfold setreg. cbn [Nat.eqb]. reflexivity. }
    assert (NX : s_next S' = Datatypes.S (Datatypes.S (s_next S))) by (rewrite ES; subst T4 T3 T2 T1; cbn; reflexivity).
    set (c := {| c_regs := regs'; c_fregs := ms_fregs ms; c_pc := w64 ra; c_fcsr := ms_fcsr ms; c_resv := None |}).
    exists (LASS.ms_of (ms_with_mem ms mem') c mem'), rho2.
    split.
    { replace (LASS.ms_of (ms_with_mem ms mem') c mem') with (@mkst fx regs' (w64 ra) mem' (ms_rom ms)) by reflexivity. unfold segs. rewrite SEGS. exact MS. }
    split; [| split; [exact AG | rewrite NX; lia]].
    rewrite ES. apply (LASS.R_core_upd U G M0 FS rho2 T4 (ms_with_mem ms mem') (set_pc (set_regs T4 rs') ra) c HR10); try reflexivity.
    - (* [comment removed for export] *) cbn [s_regs set_pc set_regs]. change (c_regs c) with regs'. subst rs'. intros r Hr. rewrite !LASS.list_get_set.
      rewrite (LAG.getr_reg_get regs' r Hr).
      destruct (Nat.eqb r 10 &&& Nat.ltb 10 (length (list_set (havoc_regs (s_regs S) 0) 4 (alit (ue_tp U)))))%bool eqn:E10.
      + apply andb_prop in E10 as [E10 _]. apply Nat.eqb_eq in E10. subst r. change (Z.of_nat 10) with 10. rewrite A0.
        cbn [val_ok]. rewrite lscale_sound, lvar_sound, Eg, <- B64. reflexivity.
      + destruct (Nat.eqb r 4 &&& Nat.ltb 4 (length (havoc_regs (s_regs S) 0)))%bool eqn:E4.
        * apply andb_prop in E4 as [E4 _]. apply Nat.eqb_eq in E4. subst r. change (Z.of_nat 4) with 4.
          rewrite (KEEP 4 ltac:(cbn; tauto)). change (Z_to_bv 5 4) with (Z_to_bv 5 (Z.of_nat 4)). rewrite R4, TP. apply alit_ok.
        * rewrite havoc_regs_get. cbn [Nat.add]. destruct (existsb (Nat.eqb r) keep_regs) eqn:Kr; [|exact I].
          rewrite (KEEP (Z.of_nat r) (keep_cs r Kr)), <- (LAG.getr_reg_get (ms_regs ms) r Hr).
          eapply val_ok_agree; [apply list_get_below; exact Wregs | exact AG | exact (r_regs _ _ _ _ _ _ _ HR r Hr)].
    - (* [comment removed for export] *) change (s_resv (set_pc (set_regs T4 rs') ra)) with (s_resv T2). change (c_resv c) with (@None word). rewrite X12resv, ERESV. exact I.
    - (* [comment removed for export] *) change (c_fcsr c) with (ms_fcsr ms). exact (r_frm _ _ _ _ _ _ _ HR).
  Qed.
End Summaries.
End LASUMM.
