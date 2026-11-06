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

Module LASUMC.

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
  Hypothesis HCBD : cbd_stmt_A.

  #[using="Type"] Lemma sh_zrun_spec : forall sh fuel g i, 0 <= i < LAC.sh_zrun sh g fuel -> nth_error sh (g + Z.to_nat (i / 8))%nat = Some 0.
  Proof.
    intros sh fuel. induction fuel as [|fuel IH]; intros g i Hi; cbn [LAC.sh_zrun] in Hi; [lia|].
    destruct (nth_error sh g) as [s|] eqn:E; [|lia]. destruct (Z.eqb_spec s 0) as [->|]; [|lia].
    destruct (Z_lt_le_dec i 8) as [L|L].
    - rewrite Z.div_small by lia. rewrite Nat.add_0_r. exact E.
    - specialize (IH (S g) (i - 8) ltac:(lia)). replace (Z.to_nat (i / 8)) with (S (Z.to_nat ((i - 8) / 8))).
      + rewrite <- Nat.add_succ_comm. exact IH.
      + replace (i / 8) with ((i - 8) / 8 + 1); [lia|]. replace i with (i - 8 + 1 * 8) at 2 by lia. rewrite Z.div_add by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="fs_consts"] Lemma frames_ok_wr_gen : forall rho m m' A n frs,
    LASM2.wr_agree m m' A n -> fs_ok FS m -> frames_ok U FS rho m frs ->
    (forall h q, frame_okR U FS rho m h q -> In h frs -> LASM2.frame_untouched rho A n h) ->
    (A + n <= FS + FS_FLAGS \/ FS + FS_FRAMES <= A) -> frames_ok U FS rho m' frs.
  Proof.
    intros rho m m' A n frs HW HFS RF UNT FL. destruct fs_consts as (HLEN & HFR & HFL & _).
    eapply LASM2.frames_ok_rebuild; [exact RF | apply LASM2.fsim_refl | |].
    - intros ps F2 ND. apply LASM2.Forall2_nth. pose proof (proj1 (LASM2.Forall2_nth _ _ _) F2) as [L F2n]. split; [exact L|].
      intros j h q Hh Hq. eapply LASM2.frame_okR_wr; [exact HW | exact HFS | exact (F2n j h q Hh Hq) | apply (UNT h q (F2n j h q Hh Hq)); eapply nth_error_In; exact Hh].
    - intros j Hj. pose proof HW as (WA & WAn & Wn & _). apply (LASM2.wr_out m m' A n); [exact HW | rewrite HFL; pose proof (fo_lo _ _ HFS); pose proof (fo_hi _ _ HFS); unfold IMGHI_A, KHI_A, HIEND_A, FS_LEN in *; lia |].
      rewrite HFL, HFR in FL. rewrite HFL. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="fs_consts frame_geom"] Lemma frames_ok_c5flags : forall rho m m' frs,
    LASM2.wr_agree m m' (fs_flag FS 5 0) 512 -> fs_ok FS m -> frames_ok U FS rho m frs ->
    (forall h, In h frs -> f_cls h <> 5) -> (forall j, 0 <= j < 512 -> mem_byte m' (fs_flag FS 5 j) 0) ->
    frames_ok U FS rho m' frs.
  Proof.
    intros rho m m' frs HW HFS ((ps & F2 & ND) & FL & REST) NO5 Z5. destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    assert (C5 : forall j, 0 <= j < 512 -> fs_flag FS 5 j = fs_flag FS 5 0 + j) by (intros; unfold fs_flag; lia).
    assert (C5R : fs_flag FS 5 0 = FS + 35840) by (unfold fs_flag; change (fs_flo 5) with 35840; lia).
    assert (OTH : forall k p, (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k -> k <> 5 -> fs_flag FS k p + 1 <= fs_flag FS 5 0 \/ fs_flag FS 5 0 + 512 <= fs_flag FS k p).
    { intros k p Hk Hp NE. unfold fs_flag. destruct Hk as [-> |[-> | E]]; [change (fs_flo 1) with 20480; change (fs_N 1) with 8192 in Hp | change (fs_flo 4) with 34816; change (fs_N 4) with 1024 in Hp | lia]; change (fs_flo 5) with 35840; lia. }
    split; [|split].
    - exists ps. split; [|exact ND]. apply LASM2.Forall2_nth. pose proof (proj1 (LASM2.Forall2_nth _ _ _) F2) as [L F2n]. split; [exact L|].
      intros j h q Hh Hq. pose proof (F2n j h q Hh Hq) as Hh'. eapply LASM2.frame_okR_wr; [exact HW | exact HFS | exact Hh' |].
      destruct Hh' as ((Hq' & Hbq & Hflq) & Kh & _). pose proof (NO5 h ltac:(eapply nth_error_In; exact Hh)) as N5.
      pose proof (frame_geom (f_cls h) q Kh Hq') as (H1 & H2 & _). rewrite HFR in H1.
      pose proof (LASM2.sh_frame FS (f_cls h) q Kh Hq' (fo_align _ _ HFS)) as (T1 & T2 & T3 & _). unfold sh in T3. rewrite ESH, HSH in T3.
      pose proof (OTH _ _ Kh Hq' N5) as O. destruct (LASM2.f_size_cls h Kh) as [Eh1 Eh2].
      assert (F8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia).
      unfold LASM2.frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq, T1. rewrite C5R in *. unfold SHB in *. lia.
    - intros k p Hk Hp. destruct (FL k p Hk Hp) as [X1 X2]. destruct (Z.eq_dec k 5) as [->|NE].
      + change (fs_N 5) with 512 in Hp. split; [intros (h & Hin & K5 & _); exfalso; exact (NO5 h Hin K5) | intros _; apply Z5; exact Hp].
      + pose proof (OTH k p Hk Hp NE) as O. pose proof (LASM2.flag_geom FS k p Hk Hp) as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
        split; intros HL; (eapply LASM2.mem_byte_wr; [exact HW | | lia | lia]); [apply X1; exact HL | apply X2; exact HL].
    - intros j Hj Hnf. destruct (Z_lt_le_dec (FS + FS_FLAGS + j) (fs_flag FS 5 0)) as [L1|L1]; [|destruct (Z_lt_le_dec (FS + FS_FLAGS + j) (fs_flag FS 5 0 + 512)) as [L2|L2]].
      2: { exfalso. apply (Hnf 5 (FS + FS_FLAGS + j - fs_flag FS 5 0)); [auto | change (fs_N 5) with 512; lia | unfold fs_flag; lia]. }
      all: eapply LASM2.mem_byte_wr; [exact HW | apply REST; [exact Hj | exact Hnf] | rewrite HFL; lia | lia].
  Qed.

  #[using="UOK SEGS RO TP CBDPC CBDFR RTCOV GSHCOV fs_consts frame_geom HCBD"] Theorem apply_cbd_sound : forall rho S S' ms,
    wf_state S = true -> R U G FS M0 rho S ms -> apply_cbd U S = Some S' ->
    exists ms' rho', msteps (ue_segs U) ms ms' /\ R U G FS M0 rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat.
  Proof.
    intros rho S S' ms Hwf HR H.
    destruct (wf_parts S Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    pose proof (r_vs _ _ _ _ _ _ _ HR) as HVS. destruct HVS as [HC HCB]. destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    (* [comment removed for export] *)
    unfold apply_cbd, cbd_core in H.
    destruct (Z.eqb_spec (s_pc S) (ue_cbd_pc U)) as [EPC|]; [|discriminate].
    destruct (Z.leb_spec 0 (ue_cbd_fr U)) as [HFR0|]; [|discriminate]. cbn [andb negb] in H.
    destruct (existsb (fun f => Z.eqb (f_cls f) 5) (s_frames S)) eqn:NO5; [discriminate|].
    destruct (sp_off S) as [k|] eqn:Hsp; [|discriminate].
    destruct (getreg S 1) as [|lra|? ? ? ?|? ?] eqn:G1; try discriminate.
    destruct (getreg S 11) as [|l1|? ? ? ?|? ?] eqn:G11; try discriminate.
    destruct (getreg S 12) as [|l2|? ? ? ?|? ?] eqn:G12; try discriminate.
    destruct (getreg S 14) as [|l4|? ? ? ?|? ?] eqn:G14; try discriminate.
    destruct (reg_is_lit S 4 (ue_tp U)) eqn:HTP; [|discriminate]. cbn [negb] in H.
    destruct (is_const lra) as [ra|] eqn:Hra; [|discriminate].
    unfold sext32_view in H.
    destruct (sexact32 (s_ctx S) l1) eqn:X1; [|discriminate].
    destruct (low32s_view (s_ctx S) l4) as [l4s|] eqn:X4; [|discriminate].
    destruct (in_window U (k - ue_cbd_fr U) (ue_cbd_fr U)) eqn:HWIN; [|discriminate].
    destruct (Z.eqb_spec (k mod 16) 0) as [HK16|]; [|discriminate].
    destruct (Z.eqb_spec (ra mod 4) 0) as [HRA4|]; [|discriminate].
    destruct (Z.leb_spec 0 ra) as [HRA0|]; [|discriminate].
    destruct (Z.ltb_spec ra two64) as [HRA64|]; [|discriminate]. cbn [andb negb] in H.
    pose proof (reg_ok rho S ms 10 HR ltac:(lia)) as R10.
    pose proof (LASM2.classify_spec rho (s_frames S) (getreg S 10) _ (s_next S) R10 (LASS.getreg_below S 10 Hwf) W18 Wfr) as CL10.
    destruct (classify (s_frames S) (getreg S 10)) as [[?|?|?|?|i off|? ?|? ?|?|?|?]|]; try discriminate.
    destruct CL10 as (f & Hnth & CL10). rewrite Hnth in H.
    destruct (arr_find (f_arrs f) (s_ctx S) (lconst off) 1) as [a|] eqn:Hfind; [|discriminate].
    destruct (ar_fact a) as [af|] eqn:Haf; [|discriminate].
    destruct (Z.eqb (af_blo af) 48 &&& Z.eqb (af_bhi af) 57 &&& Z.leb 0 off &&& Z.eqb (off mod 8) 0 &&& entails (s_ctx S) (lsub (laddc (af_len af) (ar_lo a)) (laddc l1 off)) None)%bool eqn:OKBUF; [|discriminate].
    apply andb_prop in OKBUF as [OKBUF Hcov]. apply andb_prop in OKBUF as [OKBUF Hoff8]. apply andb_prop in OKBUF as [OKBUF Hoff0]. apply andb_prop in OKBUF as [Hblo Hbhi].
    apply Z.eqb_eq in Hblo. apply Z.eqb_eq in Hbhi. apply Z.leb_le in Hoff0. apply Z.eqb_eq in Hoff8.
    match type of H with context [if negb ?c then inr 16 else _] => destruct c eqn:OKLEN; [|discriminate] end.
    match type of H with context [if negb ?c then inr 17 else _] => destruct c eqn:OKEXP; [|discriminate] end.
    match type of H with context [if negb ?c then inr 18 else _] => destruct c eqn:OKE; [|discriminate] end.
    match type of H with context [if negb ?c then inr 21 else _] => destruct c eqn:OKSH; [|discriminate] end.
    match type of H with context [if negb ?c then inr 19 else _] => destruct c eqn:NOSTR; [|discriminate] end. cbn [negb] in H.
    destruct (s_resv S) eqn:ERESV; [discriminate|].
    set (iR := Itv (Some (-1)) (Some 1)) in H.
    destruct (fresh_val (set_regs (drop_below S k) (havoc_regs (s_regs (drop_below S k)) 0)) iR) as [rv SX] eqn:Hfv.
    injection H as ES'.
    apply andb_prop in NOSTR as [NOSTRc NOSTRa].
    apply andb_prop in OKLEN as [LEN1 LEN2]. apply andb_prop in OKEXP as [OKEXP EXP2]. apply andb_prop in OKEXP as [X2 EXP1]. apply andb_prop in OKE as [E1 E2].
    (* [comment removed for export] *)
    pose proof (uo_frA U UOK) as EFR. rewrite CBDFR in *. rewrite CBDPC in EPC.
    set (sp0 := rho SYM_SP0) in *.
    set (len := evl rho l1). set (expo := evl rho l2). set (e := evl rho l4s). set (a4 := evl rho l4). set (sp := sp0 + k).
    set (B := 64 * rho (f_sym f)) in *. set (buf := B + off) in *.
    assert (HA4 : a4 mod 2 ^ 32 = e mod 2 ^ 32).
    { subst e a4. unfold low32s_view in X4. destruct (sexact32 (s_ctx S) l4); [injection X4; intros <-; reflexivity|].
      destruct (in_range (s_ctx S) l4 two31 two32); [|discriminate]. injection X4; intros <-.
      rewrite laddc_sound, (Zplus_mod (evl rho l4)). replace ((- two32) mod 2 ^ 32) with 0 by reflexivity.
      rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity. }
    pose proof (entails_sound rho _ _ None HC LEN1) as NL1. rewrite laddc_sound in NL1.
    pose proof (entails_sound rho _ _ None HC LEN2) as NL2. rewrite laddc_sound, lneg_sound in NL2.
    pose proof (entails_sound rho _ _ None HC EXP1) as NX1. rewrite laddc_sound, ladd_sound in NX1.
    pose proof (entails_sound rho _ _ None HC EXP2) as NX2. rewrite laddc_sound, lneg_sound, ladd_sound in NX2.
    pose proof (entails_sound rho _ _ None HC E1) as NE1. rewrite laddc_sound in NE1.
    pose proof (entails_sound rho _ _ None HC E2) as NE2. rewrite laddc_sound, lneg_sound in NE2.
    pose proof (entails_sound rho _ _ None HC OKSH) as NSH. rewrite laddc_sound, lneg_sound in NSH.
    pose proof (entails_sound rho _ _ None HC Hcov) as NCOV. rewrite lsub_sound, !laddc_sound in NCOV.
    fold len in NL1, NL2, NX1, NX2, NSH, NCOV. fold expo in NX1, NX2. fold e in NE1, NE2.
    apply LASMT.in_window_sound in HWIN. rewrite EFR in HWIN. destruct HWIN as [WIN1 WIN2]. unfold CBD_FR_A, FR_A in WIN1, WIN2.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as [SP1 SP2]. rewrite EFR in SP1. pose proof (r_align _ _ _ _ _ _ _ HR) as [AL1 AL2]. fold sp0 in SP1, SP2, AL1. unfold FR_A in SP1.
    pose proof (r_apart _ _ _ _ _ _ _ HR) as (AP1 & AP2 & AP3 & AP4 & AP5). fold sp0 in AP1, AP2, AP4. unfold IMGHI_A, app_mem, LOSH_A in AP3. rewrite HKHI in AP1, AP3. rewrite HHI in AP2, AP3. rewrite HLEN in AP4, AP5. unfold FR_A in AP1, AP4.
    hide AP3. hide AP4.
    pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS. pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    assert (F8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia). assert (F8' : 0xcd000 <= FS / 8) by (apply Z.div_le_lower_bound; lia).   (* [comment removed for export] *)
    pose proof (LASM2.geom_facts FS _ _ (LASM2.R_geom U G M0 FS _ _ _ HR)) as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & F10). clear GF1 GF2 GF3 GF4 GF5 GF6 GF7 GF8 GF9.
    assert (FD : (FS + 5279744) / 8 = FS / 8 + 659968).
    { rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (LASM2.geom_facts FS _ _ (LASM2.R_geom U G M0 FS _ _ _ HR))))))))))) at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    (* [comment removed for export] *)
    pose proof (reg_ok rho S ms 1 HR ltac:(lia)) as R1. rewrite G1 in R1. cbn [val_ok] in R1. rewrite (is_const_sound rho lra ra Hra) in R1.
    pose proof (reg_ok rho S ms 2 HR ltac:(lia)) as R2.
    pose proof (LASM2.classify_spec rho (s_frames S) (getreg S 2) _ (s_next S) R2 (LASS.getreg_below S 2 Hwf) W18 Wfr) as CL2.
    unfold sp_off in Hsp. destruct (classify (s_frames S) (getreg S 2)) as [[k'|?|?|?|? ?|? ?|? ?|?|?|?]|]; try discriminate. injection Hsp as ->. fold sp0 in CL2.
    pose proof (reg_ok rho S ms 11 HR ltac:(lia)) as R11. rewrite G11 in R11. cbn [val_ok] in R11. fold len in R11.
    pose proof (reg_ok rho S ms 12 HR ltac:(lia)) as R12. rewrite G12 in R12. cbn [val_ok] in R12. fold expo in R12.
    pose proof (reg_ok rho S ms 14 HR ltac:(lia)) as R14. rewrite G14 in R14. cbn [val_ok] in R14. fold a4 in R14.
    pose proof (reg_lit rho S ms 4 (ue_tp U) HR ltac:(lia) HTP) as R4. rewrite TP in R4.
    (* [comment removed for export] *)
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF.
    destruct (LASM2.frames_nth U FS rho (ms_mem ms) (s_frames S) i f RF Hnth) as (p & Hf & Hin).
    pose proof Hf as ((Hp & Hb & Hfl) & Hk & Hcs & Har & Hshlen & Hsh). fold B in Hb, Hcs, Har, Hsh.
    pose proof (frame_geom (f_cls f) p Hk Hp) as (FG1 & FG2 & FG3 & FG4 & FG5 & FG6). rewrite HFR in FG1. rewrite HLEN in FG2. fold B in FG1, FG2, FG4.
    pose proof (LASM2.sh_frame FS (f_cls f) p Hk Hp (fo_align _ _ HFS)) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite <- Hb in S1, S2, S3, S4, S5. fold B in S1, S2, S3, S4, S5.
    destruct (LASM2.f_size_cls f Hk) as [E1f E2f].
    assert (K5 : f_cls f <> 5).
    { intros E5. assert (X : existsb (fun f0 => Z.eqb (f_cls f0) 5) (s_frames S) = true) by (apply existsb_exists; exists f; split; [exact Hin | rewrite E5; reflexivity]). rewrite X in NO5. discriminate. }
    assert (K14 : f_cls f = 1 \/ f_cls f = 4) by (destruct Hk as [?|[?|?]]; [auto|auto|congruence]).
    hide Hk. hide AP5. hide K14.
    destruct (LASM2.arr_find_spec rho _ _ _ _ _ HC Hfind) as (Hina & Hloa & Hhia). rewrite lconst_sound in Hloa, Hhia.
    pose proof (proj1 (Forall_forall _ _) Har a Hina) as AOK.
    assert (DIG : forall j, 0 <= j < len -> off + j < fs_fsz (f_cls f) /\ exists d, rdn SEGS_A (ms_mem ms) (Z_to_bv 64 (buf + j)) 1 = Some [d] /\ 48 <= bv_unsigned d <= 57).
    { intros j Hj.
      destruct (LASM2.arr_fact_byte_g U rho (ms_mem ms) B 0 (fs_fsz (f_cls f)) a af (off - ar_lo a + j) ltac:(rewrite <- E1f; exact AOK) Haf ltac:(lia)) as (d & Hrd & _ & Hd & _).
      split.
      - destruct AOK as (_ & AHI & AF). rewrite Haf in AF. destruct AF as (_ & _ & AF & _). pose proof (proj1 (AF (off - ar_lo a + j) ltac:(lia))). rewrite E1f in AHI. lia.
      - exists d. replace (buf + j) with (B + ar_lo a + (off - ar_lo a + j)) by (unfold buf; lia). rewrite <- SEGS.
        split; [exact Hrd | rewrite Hblo, Hbhi in Hd; exact Hd]. }
    assert (BUFHI : off + len <= fs_fsz (f_cls f)) by (pose proof (proj1 (DIG (len - 1) ltac:(lia))); lia).
    assert (B8 : B = 8 * (B / 8)) by exact S5.
    assert (SHD : forall j, 0 <= j < len -> mem_byte (ms_mem ms) (sh (buf + j)) 0).
    { intros j Hj. pose proof (sh_zrun_spec (f_sh f) (Z.to_nat (f_shn f)) (Z.to_nat (off / 8)) j ltac:(lia)) as Z0.
      destruct (Hsh _ _ Z0) as [_ M]. unfold mem_byte. rewrite LASM2.w64_same. unfold sh. rewrite ESH.
      replace (SHB + (buf + j) / 8) with (sh B + Z.of_nat (Z.to_nat (off / 8) + Z.to_nat (j / 8))); [exact M|].
      unfold sh. rewrite ESH. pose proof (Z.div_mod off 8 ltac:(lia)) as D1. pose proof (Z.div_mod j 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound j 8 ltac:(lia)) as D3.
      rewrite Nat2Z.inj_add, !Z2Nat.id by (try apply Z.div_pos; lia). unfold buf.
      replace (B + off + j) with ((B / 8 + off / 8 + j / 8) * 8 + j mod 8) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (j mod 8) 8) by lia. lia. }
    (* [comment removed for export] *)
    pose proof (r_resv _ _ _ _ _ _ _ HR) as RRESV. rewrite ERESV in RRESV. cbn [resv_ok] in RRESV.
    destruct (ms_resv ms) eqn:EMR; [destruct RRESV|].
    pose proof (ms_eta ms (r_svc _ _ _ _ _ _ _ HR) EMR) as ETA. set (fx := mkFP (ms_fregs ms) (ms_fcsr ms)) in ETA.
    rewrite (r_pc _ _ _ _ _ _ _ HR), EPC in ETA.
    (* [comment removed for export] *)
    assert (MDEF : mem_def (ms_mem ms) (sp - CBD_FR_A) CBD_FR_A).
    { intros j Hj. unfold CBD_FR_A in Hj |- *. destruct (proj1 (r_win _ _ _ _ _ _ _ HR) (sp - 3072 + j) ltac:(fold sp0; rewrite EFR; unfold FR_A, sp; lia)) as [b Hbb].
      exists b. rewrite LASM2.w64_same. exact Hbb. }
    pose proof RF as (_ & FL & _).
    assert (Z5 : forall j, 0 <= j < 512 -> mem_byte (ms_mem ms) (fs_flag FS 5 j) 0).
    { intros j Hj. apply (proj2 (FL 5 j ltac:(auto) ltac:(change (fs_N 5) with 512; lia))). intros (h & Hinh & K & _).
      assert (X : existsb (fun f0 => Z.eqb (f_cls f0) 5) (s_frames S) = true) by (apply existsb_exists; exists h; split; [exact Hinh | rewrite K; reflexivity]). rewrite X in NO5. discriminate. }
    assert (SHSTK : forall g, (sp - CBD_FR_A) / 8 <= g < sp / 8 -> mem_byte (ms_mem ms) (SH_A + g) 0).
    { intros g Hg. apply (r_shstk _ _ _ _ _ _ _ HR). fold sp0. clear - Hg WIN1 WIN2. unfold CBD_FR_A, FR_A, sp in *.
      assert ((sp0 - 4096) / 8 <= (sp0 + k - 3072) / 8) by (apply Z.div_le_mono; lia). assert ((sp0 + k) / 8 <= sp0 / 8) by (apply Z.div_le_mono; lia). lia. }
    (* [comment removed for export] *)
    assert (C5F : fs_frame FS 5 0 = FS + 5279744) by (unfold fs_frame; change (fs_fro 5) with 5279744; lia). assert (C5L : fs_flag FS 5 0 = FS + 35840) by (unfold fs_flag; change (fs_flo 5) with 35840; lia).
    assert (BODY14 : B + fs_fsz (f_cls f) <= fs_frame FS 5 0).
    { rewrite C5F, Hb. clear - Hp K14 HFR. unfold hide in K14. unfold fs_frame, fs_fro. destruct K14 as [E|E]; rewrite E in *; [change (fs_N 1) with 8192 in Hp; change (fs_fsz 1) with 128 | change (fs_N 4) with 1024 in Hp; change (fs_fsz 4) with 1024]; rewrite HFR; lia. }
    (* [comment removed for export] *)
    assert (BX3 : (B + fs_fsz (f_cls f)) / 8 <= FS / 8 + 659968) by (rewrite <- FD; clear - BODY14 C5F; apply Z.div_le_mono; lia).
    assert (BX1 : (buf + len - 1) / 8 <= (B + fs_fsz (f_cls f)) / 8 - 1).
    { clear - BUFHI NL1 Hoff0 S5 S6 FG3. assert (E8 : B + fs_fsz (f_cls f) = (B / 8 + fs_fsz (f_cls f) / 8) * 8) by lia. rewrite E8, Z.div_mul by lia.
      assert ((buf + len - 1) / 8 < B / 8 + fs_fsz (f_cls f) / 8); [|lia]. apply Z.div_lt_upper_bound; [lia|]. unfold buf. lia. }
    assert (BX0 : B / 8 <= buf / 8) by (clear - Hoff0; apply Z.div_le_mono; unfold buf; lia).
    assert (APART1 : forall rr, In rr (cbd_writes sp FS) -> buf + len <= fst rr \/ snd rr <= buf).
    { intros rr Hrr. unfold cbd_writes, FS5_FLAGS, FS5_FRAMES, FS5_SHADOW, fs_hint in Hrr. cbn [In] in Hrr. rewrite C5F, C5L in Hrr. unfold sh in Hrr. rewrite ESH, FD in Hrr.
      clear - Hrr BUFHI BODY14 C5F AP1 AP4 WIN1 WIN2 FG1 FG2 Hb NL1 Hoff0 LO LOAPP HI F8 F8'. unfold hide in AP4. unfold buf, sp, CBD_FR_A, SHB in *. rewrite C5F in BODY14.
      destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; lia. }
    assert (APART2 : forall rr, In rr (cbd_writes sp FS) -> sh (buf + len - 1) + 1 <= fst rr \/ snd rr <= sh buf).
    { intros rr Hrr. unfold cbd_writes, FS5_FLAGS, FS5_FRAMES, FS5_SHADOW, fs_hint in Hrr. cbn [In] in Hrr. rewrite C5F, C5L in Hrr. unfold sh in Hrr |- *. rewrite ESH, FD in Hrr. rewrite ESH.
      clear - Hrr BX0 BX1 BX3 AP1 AP4 WIN1 WIN2 LO LOAPP HI F8 F8' FG1 FG2 Hb NL1. unfold hide in AP4. unfold sp, CBD_FR_A, SHB in *.
      destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; lia. }
    (* [comment removed for export] *)
    assert (SIDE : (KHI_A <= sp - CBD_FR_A /\ sp <= HIEND_A /\ IMGHI_A <= buf /\ app_mem buf len /\ buf + len <= HIEND_A) /\ ((sp <= buf \/ buf + len <= sp - CBD_FR_A) /\ (sp <= FS \/ FS + FS_LEN <= sp - CBD_FR_A))).   (* [comment removed for export] *)
    { clear - AP1 AP2 AP4 WIN1 WIN2 FG1 FG2 Hb BODY14 C5F BUFHI NL1 Hoff0 LO LOAPP HI. unfold hide in AP4. unfold IMGHI_A, app_mem, LOSH_A, KHI_A, HIEND_A, CBD_FR_A, FS_LEN, sp, buf in *. rewrite C5F in BODY14. repeat split; lia. }
    destruct SIDE as ((SD1 & SD2 & SD3 & SD3' & SD4) & (SD5 & SD6)). hide SD5. hide SD6.
    assert (MCTX : malloc_ctx_ok (sp - CBD_FR_A) sp FS (ms_mem ms)).
    { eapply malloc_ctx_mono; [exact (r_mctx _ _ _ _ _ _ _ HR) | | ]; fold sp0; clear - WIN1 WIN2; unfold CBD_FR_A, FR_A, sp; lia. }
    assert (RA4 : bv_unsigned (w64 ra) mod 4 = 0) by (clear - HRA0 HRA64 HRA4; rewrite w64_lit by (unfold LAI.two64 in HRA64; rewrite two64_eq in HRA64; lia); exact HRA4).
    assert (SP16 : sp mod 16 = 0) by (clear - AL1 HK16; unfold sp; rewrite Z.add_mod, AL1, HK16 by lia; reflexivity).
    pose proof (HCBD fx (ms_regs ms) (ms_mem ms) (ms_rom ms) sp buf len expo e a4 FS (w64 ra) (getr (ms_regs ms) (Z_to_bv 5 13))
                R1 RA4 CL2 SP16 SD1 SD2
                R4 CL10 SD3 SD3' SD4 R11 R12 eq_refl R14 HA4
                ltac:(clear - NL1 NL2; lia) ltac:(clear - NX1 NX2; lia) ltac:(clear - NE1 NE2; lia)
                ltac:(intros j Hj; exact (proj2 (DIG j Hj))) SHD MDEF SD5
                (R_ro_ok _ _ _ HR) (R_rt_ok _ _ _ HR) (R_gsh_ok _ _ _ HR) MCTX
                (fo_tls _ _ HFS) (fo_align _ _ HFS) (fo_lo _ _ HFS) (fo_app _ _ HFS) (fo_hi _ _ HFS) SD6
                APART1 APART2 (fo_def _ _ HFS) (fo_shdef _ _ HFS) (fo_log _ _ HFS) (fo_gc _ _ HFS) Z5 SHSTK)
      as CBD1.
    destruct CBD1 as (regs' & mem' & MS & KEEP & (r & A0 & Hr) & Z5' & [FRAME GROW]).
    unfold LibIfaceA.w64, LASEM.w64 in MS, ETA. rewrite <- ETA in MS.
    (* [comment removed for export] *)
    destruct (fresh_val_sound rho S iR r (conj HC HCB) ltac:(subst iR; unfold in_itv; cbn [ilo ihi]; clear - Hr; lia)) as (rho1 & VX1 & VS1 & VOKr & VBr).
    set (T1 := snd (fresh_val S iR)). change (snd (fresh_val S iR)) with T1 in VX1, VS1, VBr.
    assert (HR1 : R U G FS M0 rho1 T1 ms) by (eapply R_vext; [exact Hwf | exact HR | exact VX1 | exact VS1]).
    pose proof VX1 as VX1'. destruct VX1' as (AG & X1b & X1pc & X1regs & Estk & Earrs & X1abs & X1resv & X1d & Epc & Epay & Efr).
    assert (HG : forall x, (x < NGLOB)%nat -> rho1 x = rho x) by (intros x Hx; apply AG; clear - Hx W18; lia).
    assert (GSP : rho1 SYM_SP0 = sp0) by (apply HG; unfold SYM_SP0, NGLOB; lia).
    assert (GN : rho1 SYM_N = rho SYM_N) by (apply HG; unfold SYM_N, NGLOB; lia). assert (GD : rho1 SYM_DATA = rho SYM_DATA) by (apply HG; unfold SYM_DATA, NGLOB; lia).
    set (T3 := drop_below T1 k).
    assert (HR3 : R U G FS M0 rho1 T3 ms) by (apply LASM2.drop_below_sound; exact HR1).
    assert (ST3s : s_stk T3 = cells_drop_below (s_stk S) k) by (rewrite <- Estk; reflexivity).
    assert (ST3a : s_arrs T3 = filter (fun a => negb (Z.leb (ar_hi a) k)) (s_arrs S)) by (rewrite <- Earrs; reflexivity).
    assert (ST3f : s_frames T3 = s_frames S) by (rewrite <- Efr; reflexivity).
    assert (CELLS3 : forall c, In c (s_stk T3) -> k <= c_off c).
    { intros c Hc. rewrite ST3s in Hc. unfold cells_drop_below in Hc. apply LASM2.In_filterP in Hc as [Hc Hkeep]. cbv beta in Hkeep.
      pose proof (LASMT.forallb_In _ _ _ _ NOSTRc Hc) as NS. cbv beta in NS.
      destruct (Z.leb_spec (c_off c + c_w c) k); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
    assert (ARRS3 : forall a', In a' (s_arrs T3) -> k <= ar_lo a').
    { intros a' Ha. rewrite ST3a in Ha. apply LASM2.In_filterP in Ha as [Ha Hkeep]. cbv beta in Hkeep.
      pose proof (LASMT.forallb_In _ _ _ _ NOSTRa Ha) as NS. cbv beta in NS.
      destruct (Z.leb_spec (ar_hi a') k); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
    (* [comment removed for export] *)
    assert (UNT : forall mm h q A n, frame_okR U FS rho1 mm h q -> In h (s_frames S) ->
              ((A = FS + 5279744 /\ n = 2 ^ 20) \/ (A = SHB + (FS / 8 + 659968) /\ n = 2 ^ 17)) ->
              LASM2.frame_untouched rho1 A n h).
    { intros mm h q A n ((Hq & Hbq & Hflq) & Kh & _) Hinh RNG.
      assert (N5 : f_cls h <> 5).
      { intros E5. assert (X : existsb (fun f0 => Z.eqb (f_cls f0) 5) (s_frames S) = true) by (apply existsb_exists; exists h; split; [exact Hinh | rewrite E5; reflexivity]). rewrite X in NO5. discriminate. }
      pose proof (frame_geom (f_cls h) q Kh Hq) as (H1 & H2 & H3 & _). rewrite HFR in H1. rewrite HLEN in H2.
      pose proof (LASM2.sh_frame FS (f_cls h) q Kh Hq (fo_align _ _ HFS)) as (T1' & T2 & T3' & T4 & T5 & T6). unfold sh in T2, T3'. rewrite ESH, HSL in T2. rewrite ESH, HSH in T3'.
      pose proof (LASM2.flag_geom FS (f_cls h) q Kh Hq) as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
      assert (HB5 : fs_frame FS (f_cls h) q + fs_fsz (f_cls h) <= fs_frame FS 5 0).
      { rewrite C5F. clear - Hq Kh N5 HFR. unfold fs_frame, fs_fro. destruct Kh as [E|[E|E]]; rewrite E in *; [change (fs_N 1) with 8192 in Hq; change (fs_fsz 1) with 128 | change (fs_N 4) with 1024 in Hq; change (fs_fsz 4) with 1024 | congruence]; rewrite HFR; lia. }
      destruct (LASM2.f_size_cls h Kh) as [Eh1 Eh2]. unfold LASM2.frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq, T1'. rewrite C5F in HB5.
      clear - H1 H2 H3 T2 T3' T5 T6 M1 M2 HB5 RNG LO LOAPP HI F8 F8' F10. unfold SHB in *. destruct RNG as [[-> ->]|[-> ->]]; lia. }   (* [comment removed for export] *)
    clear - HR3 HFS ST3f ST3s ST3a CELLS3 ARRS3 UNT NO5 Z5' FRAME GROW GSP GN GD EFR HLEN HFR HFL HKHI HHI ESH HSL HSH LO LOAPP HI F8 F8' FD F10
            AP1 AP2 AP3 AP4 AP5 WIN1 WIN2 SP1 SP2 C5F C5L KEEP A0 MS VOKr VBr Hfv ERESV X1resv X1b AG Wregs R4 HR Hwf ES'
            UOK SEGS RO TP MEMSET CBDPC CBDFR RTCOV GSHCOV HCBD fs_consts frame_geom segs.
    (* [comment removed for export] *)
    set (m0 := ms_mem ms) in *.
    set (r1 := (sp - CBD_FR_A, sp)) in *. set (r2 := (fs_hint FS 5, fs_hint FS 5 + 8)) in *. set (r3 := FS5_FLAGS FS) in *. set (r4 := FS5_FRAMES FS) in *. set (r5 := FS5_SHADOW FS) in *.
    assert (FRAME' : forall x : word, ~ LibIface.in_ranges (bv_unsigned x) [r1; r2; r4; r5; r3] -> mem' x = m0 x).
    { intros x Hx. apply FRAME. intros (rr & Hrr & Hinr). apply Hx. exists rr. split; [|exact Hinr]. unfold cbd_writes in Hrr. cbn [In] in Hrr |- *. tauto. }
    set (m1 := patch m0 mem' r1). set (m2 := patch m1 mem' r2). set (m3 := patch m2 mem' r4). set (m4 := patch m3 mem' r5). set (m5 := patch m4 mem' r3).
    assert (BW0 : between m0 mem' m0) by (intros x; left; reflexivity).
    pose proof (patch_between _ _ _ r1 BW0) as BW1. pose proof (patch_between _ _ _ r2 BW1) as BW2. pose proof (patch_between _ _ _ r4 BW2) as BW3.
    pose proof (patch_between _ _ _ r5 BW3) as BW4. pose proof (patch_between _ _ _ r3 BW4) as BW5.
    fold m1 in BW1, BW2. fold m2 in BW2, BW3. fold m3 in BW3, BW4. fold m4 in BW4, BW5. fold m5 in BW5.
    assert (END : forall x, m5 x = mem' x).
    { intros x. pose proof (patches_end [r1; r2; r4; r5; r3] m0 mem' m0 BW0 FRAME' x) as X. cbn [patches] in X. exact X. }
    pose proof (patch_wr_agree m0 mem' m0 (sp - CBD_FR_A) sp BW0 GROW ltac:(unfold CBD_FR_A, sp; lia) ltac:(unfold CBD_FR_A; lia) ltac:(unfold sp; lia)) as HW1.
    fold r1 m1 in HW1. replace (sp - (sp - CBD_FR_A)) with CBD_FR_A in HW1 by lia.
    pose proof (patch_wr_agree m0 mem' m1 (fs_hint FS 5) (fs_hint FS 5 + 8) BW1 GROW ltac:(unfold fs_hint; lia) ltac:(lia) ltac:(unfold fs_hint; lia)) as HW2.
    fold r2 m2 in HW2. replace (fs_hint FS 5 + 8 - fs_hint FS 5) with 8 in HW2 by lia. unfold fs_hint in HW2.
    pose proof (patch_wr_agree m0 mem' m2 (fs_frame FS 5 0) (fs_frame FS 5 0 + 2 ^ 20) BW2 GROW ltac:(rewrite C5F; lia) ltac:(lia) ltac:(rewrite C5F; lia)) as HW3.
    change (fs_frame FS 5 0, fs_frame FS 5 0 + 2 ^ 20) with (FS5_FRAMES FS) in HW3. fold r4 m3 in HW3. replace (fs_frame FS 5 0 + 2 ^ 20 - fs_frame FS 5 0) with (2 ^ 20) in HW3 by lia. rewrite C5F in HW3.
    pose proof (patch_wr_agree m0 mem' m3 (sh (fs_frame FS 5 0)) (sh (fs_frame FS 5 0) + 2 ^ 17) BW3 GROW ltac:(unfold sh; rewrite ESH, C5F; unfold SHB; lia) ltac:(lia) ltac:(unfold sh; rewrite ESH, C5F; unfold SHB; lia)) as HW4.
    change (sh (fs_frame FS 5 0), sh (fs_frame FS 5 0) + 2 ^ 17) with (FS5_SHADOW FS) in HW4. fold r5 m4 in HW4. replace (sh (fs_frame FS 5 0) + 2 ^ 17 - sh (fs_frame FS 5 0)) with (2 ^ 17) in HW4 by lia.
    unfold sh in HW4. rewrite ESH, C5F in HW4.
    pose proof (patch_wr_agree m0 mem' m4 (fs_flag FS 5 0) (fs_flag FS 5 0 + 512) BW4 GROW ltac:(rewrite C5L; lia) ltac:(lia) ltac:(rewrite C5L; lia)) as HW5.
    change (fs_flag FS 5 0, fs_flag FS 5 0 + 512) with (FS5_FLAGS FS) in HW5. fold r3 m5 in HW5. replace (fs_flag FS 5 0 + 512 - fs_flag FS 5 0) with 512 in HW5 by lia.
    rewrite FD in HW4.
    pose proof (proj1 (proj2 (r_pay _ _ _ _ _ _ _ HR3))) as P2. rewrite GSP, EFR, GN, GD in P2. unfold FR_A in P2. hide P2.
    pose proof (r_data _ _ _ _ _ _ _ HR3) as (D1 & D2 & D3). rewrite ?GN, ?GD in D1. rewrite ?GN, ?GD in D2. rewrite ?GN in D3.
    assert (RFt : forall mm, R U G FS M0 rho1 T3 (ms_with_mem ms mm) -> frames_ok U FS rho1 mm (s_frames S)).
    { intros mm HRm. rewrite <- ST3f. exact (r_frames _ _ _ _ _ _ _ HRm). }
    assert (HR4 : R U G FS M0 rho1 T3 (ms_with_mem ms m1)).
    { eapply (R_wr_same _ _ _ _ _ _ HR3 HW1); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a' Ha C1 C2; pose proof (ARRS3 a' Ha) | |];
      [left; unfold CBD_FR_A, FR_A, sp; lia | intros x Hx; left; rewrite EFR; unfold CBD_FR_A, FR_A, sp in *; lia | unfold sp, CBD_FR_A; lia
      | unfold sp, CBD_FR_A; lia | unfold sp, CBD_FR_A; lia | unfold hide in P2; unfold sp, CBD_FR_A; lia |].
      rewrite ST3f. eapply LASM2.frames_ok_wr_apart; [exact HW1 | exact HFS | rewrite <- ST3f; exact (r_frames _ _ _ _ _ _ _ HR3) | unfold hide in AP4; rewrite HFL; unfold sp, CBD_FR_A; lia | right; unfold sh; rewrite ESH, HSH; unfold SHB, sp, CBD_FR_A; lia]. }
    assert (FS1 : fs_ok FS m1) by (eapply LASM2.fs_ok_wr; [exact HW1 | exact HFS | eapply LASM2.R_geom; exact HR3 | left; rewrite GSP; unfold CBD_FR_A, FR_A, sp; lia]).
    assert (HR5 : R U G FS M0 rho1 T3 (ms_with_mem ms m2)).
    { eapply (R_wr_same _ _ _ _ _ _ HR4 HW2); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a' Ha C1 C2; pose proof (ARRS3 a' Ha) | |];
      [right; right; right; right; left; lia | intros x Hx; right; right; left; lia | lia | unfold hide in AP4; lia | unfold hide in AP4; lia | unfold hide in AP5; lia |].
      rewrite ST3f. eapply LASM2.frames_ok_wr_apart; [exact HW2 | exact FS1 | exact (RFt _ HR4) | rewrite HFL; lia | unfold sh; rewrite ESH, HSL, HSH; unfold SHB; pose proof LOAPP as [ZL|ZH]; [left; lia | right; lia]]. }   (* [comment removed for export] *)
    assert (FS2 : fs_ok FS m2) by (eapply LASM2.fs_ok_wr; [exact HW2 | exact FS1 | eapply LASM2.R_geom; exact HR4 | right; right; right; right; left; cbn [ms_mem ms_with_mem]; lia]).
    assert (HR6 : R U G FS M0 rho1 T3 (ms_with_mem ms m3)).
    { eapply (R_wr_same _ _ _ _ _ _ HR5 HW3); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a' Ha C1 C2; pose proof (ARRS3 a' Ha) | |];
      [right; right; left; lia | intros x Hx; right; right; left; lia | lia | unfold hide in AP4; lia | unfold hide in AP4; lia | unfold hide in AP5; lia |].
      rewrite ST3f. eapply (frames_ok_wr_gen rho1 m2 m3 _ _ (s_frames S) HW3 FS2 (RFt _ HR5)); [|right; lia].
      intros h q Hh Hinh. eapply (UNT m2 h q); [exact Hh | exact Hinh | left; split; reflexivity]. }
    assert (FS3 : fs_ok FS m3) by (eapply LASM2.fs_ok_wr; [exact HW3 | exact FS2 | eapply LASM2.R_geom; exact HR5 | right; right; left; cbn [ms_mem ms_with_mem]; lia]).
    assert (HR7 : R U G FS M0 rho1 T3 (ms_with_mem ms m4)).
    { eapply (R_wr_same _ _ _ _ _ _ HR6 HW4); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a' Ha C1 C2; pose proof (ARRS3 a' Ha) | |];
      [right; right; right; right; right; unfold sh; rewrite ESH, HSL, HSH; unfold SHB; lia | intros x Hx; right; right; right; unfold sh; rewrite ESH, HSL, HSH; unfold SHB in *; lia
      | unfold SHB; lia | unfold hide in AP4; unfold SHB; lia | unfold hide in AP4; unfold SHB; lia | unfold hide in AP3; unfold hide in AP5; unfold SHB; lia |].
      rewrite ST3f. eapply (frames_ok_wr_gen rho1 m3 m4 _ _ (s_frames S) HW4 FS3 (RFt _ HR6)); [|rewrite HFL, HFR; unfold SHB; pose proof LOAPP as [ZL|ZH]; [right; lia | left; lia]].   (* [comment removed for export] *)
      intros h q Hh Hinh. eapply (UNT m3 h q); [exact Hh | exact Hinh | right; split; reflexivity]. }
    assert (FS4 : fs_ok FS m4) by (eapply LASM2.fs_ok_wr; [exact HW4 | exact FS3 | eapply LASM2.R_geom; exact HR6 | right; right; right; right; right; cbn [ms_mem ms_with_mem]; unfold sh; rewrite ESH, HSL, HSH; unfold SHB; lia]).
    assert (M5Z : forall j, 0 <= j < 512 -> mem_byte m5 (fs_flag FS 5 j) 0).
    { intros j Hj. unfold mem_byte. rewrite LASM2.w64_same, END. pose proof (Z5' j Hj) as M. unfold mem_byte in M. rewrite LASM2.w64_same in M. exact M. }
    assert (HR8 : R U G FS M0 rho1 T3 (ms_with_mem ms m5)).
    { eapply (R_wr_same _ _ _ _ _ _ HR7 HW5); rewrite ?GSP, ?GN, ?GD; [ | | | intros c Hc C1 C2; pose proof (CELLS3 c Hc) | intros a' Ha C1 C2; pose proof (ARRS3 a' Ha) | |];
      [right; right; right; left; rewrite C5L, HFL, HFR; lia | intros x Hx; right; right; left; rewrite C5L in Hx; lia | rewrite C5L; lia | unfold hide in AP4; rewrite C5L; lia | unfold hide in AP4; rewrite C5L; lia | unfold hide in AP5; rewrite C5L; lia |].
      rewrite ST3f. eapply (frames_ok_c5flags rho1 m4 m5 (s_frames S) HW5 FS4 (RFt _ HR7)); [|exact M5Z].
      intros h Hinh E5. assert (X : existsb (fun f0 => Z.eqb (f_cls f0) 5) (s_frames S) = true) by (apply existsb_exists; exists h; split; [exact Hinh | rewrite E5; reflexivity]). rewrite X in NO5. discriminate. }
    assert (HR9 : R U G FS M0 rho1 T3 (ms_with_mem ms mem')).
    { pose proof (R_mem_ext rho1 T3 (ms_with_mem ms m5) mem' HR8 ltac:(intros x; cbn; symmetry; apply END)) as X. exact X. }
    (* [comment removed for export] *)
    injection Hfv as Erv ESX.
    set (rs' := list_set (list_set (havoc_regs (s_regs S) 0) 4 (alit (ue_tp U))) 10 rv).
    assert (ES : S' = set_pc (set_regs T3 rs') ra).
    { subst S' SX rv T3 T1 rs'. unfold setreg, fresh_val, fresh. cbn [Nat.eqb fst snd]. reflexivity. }
    assert (NX : s_next S' = Datatypes.S (s_next S)) by (rewrite ES; subst T3 T1; cbn; reflexivity).
    set (c0 := {| c_regs := regs'; c_fregs := ms_fregs ms; c_pc := w64 ra; c_fcsr := ms_fcsr ms; c_resv := None |}).
    exists (LASS.ms_of (ms_with_mem ms mem') c0 mem'), rho1.
    split.
    { replace (LASS.ms_of (ms_with_mem ms mem') c0 mem') with (@mkst fx regs' (w64 ra) mem' (ms_rom ms)) by reflexivity. unfold segs. rewrite SEGS. exact MS. }
    split; [| split; [exact AG | rewrite NX; lia]].
    rewrite ES. apply (LASS.R_core_upd U G M0 FS rho1 T3 (ms_with_mem ms mem') (set_pc (set_regs T3 rs') ra) c0 HR9); try reflexivity.
    - (* [comment removed for export] *) cbn [s_regs set_pc set_regs]. change (c_regs c0) with regs'. subst rs'. intros q Hq. rewrite !LASS.list_get_set.
      rewrite (LAG.getr_reg_get regs' q Hq).
      destruct (Nat.eqb q 10 &&& Nat.ltb 10 (length (list_set (havoc_regs (s_regs S) 0) 4 (alit (ue_tp U)))))%bool eqn:E10.
      + apply andb_prop in E10 as [E10 _]. apply Nat.eqb_eq in E10. subst q. change (Z.of_nat 10) with 10. rewrite A0.
        rewrite <- Erv. change (Z_to_bv 64 r) with (w64 r). pose proof VOKr as V. cbn [fst fresh_val fresh] in V. exact V.
      + destruct (Nat.eqb q 4 &&& Nat.ltb 4 (length (havoc_regs (s_regs S) 0)))%bool eqn:E4.
        * apply andb_prop in E4 as [E4 _]. apply Nat.eqb_eq in E4. subst q. change (Z.of_nat 4) with 4.
          rewrite (KEEP 4 ltac:(cbn; tauto)). change (Z_to_bv 5 4) with (Z_to_bv 5 (Z.of_nat 4)). rewrite R4, TP. apply alit_ok.
        * rewrite havoc_regs_get. cbn [Nat.add]. destruct (existsb (Nat.eqb q) keep_regs) eqn:Kq; [|exact I].
          rewrite (KEEP (Z.of_nat q) (keep_cs q Kq)), <- (LAG.getr_reg_get (ms_regs ms) q Hq).
          eapply val_ok_agree; [apply list_get_below; exact Wregs | exact AG | exact (r_regs _ _ _ _ _ _ _ HR q Hq)].
    - (* [comment removed for export] *) change (s_resv (set_pc (set_regs T3 rs') ra)) with (s_resv T1). change (c_resv c0) with (@None word). rewrite X1resv, ERESV. exact I.
    - (* [comment removed for export] *) change (c_fcsr c0) with (ms_fcsr ms). exact (r_frm _ _ _ _ _ _ _ HR).
  Qed.
End Summaries.
End LASUMC.
