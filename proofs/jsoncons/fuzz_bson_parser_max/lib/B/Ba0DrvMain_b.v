(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvA_b
  Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvC_defs_b Ba0DrvC_b Ba0DrvD_defs_b Ba0DrvLibL_b Ba0DrvD_b Ba0DrvE_defs_b Ba0DrvStdio_b Ba0DrvLibInit_b Ba0DrvE_b Ba0DrvE2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanSoundK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MainPhaseA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws AgentLib Spec BigintSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint expr_nb (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => expr_nb a && expr_nb b
  | EExt _ _ _ a => expr_nb a
  | EBlob _ _ _ _ => false
  end.
Definition kentry_nb (K : kentry) : bool :=
  match K with
  | KWord a _ v => expr_nb (a_base a) && expr_nb v
  | KZero a n => expr_nb (a_base a) && expr_nb n
  | KBlob _ _ _ => false
  | KImg _ _ => true
  | KAlign e _ | KRange e _ _ => expr_nb e
  | KWr a _ => expr_nb (a_base a)
  | KDisj a1 _ a2 _ => expr_nb (a_base a1) && expr_nb (a_base a2)
  end.
Lemma edenot_nb : forall v b b' e, expr_nb e = true -> edenot (Env v b) e = edenot (Env v b') e.
Proof.
  intros v b b' e. induction e as [z|n|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|sx lo n x IHx|sx k i n]; cbn [expr_nb edenot]; intros H;
    try reflexivity; try (apply andb_prop in H as (H1 & H2); rewrite (IHx H1), (IHy H2); reflexivity); try (rewrite (IHx H); reflexivity); discriminate H.
Qed.
Lemma regs_ok_nb : forall v b b' sr R, forallb expr_nb sr = true -> regs_ok (Env v b) sr R -> regs_ok (Env v b') sr R.
Proof.
  intros v b b' sr R Hb HR r. rewrite (HR r). apply edenot_nb. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  destruct (nth_in_or_default (ridx r) sr (ELit 0)) as [Hin|Hd]; [exact (proj1 (forallb_forall _ _) Hb _ Hin) | rewrite Hd; reflexivity].
Qed.
Lemma kentry_ok_nb : forall segs v b b' M K, kentry_nb K = true -> kentry_ok segs (Env v b) M K -> kentry_ok segs (Env v b') M K.
Proof.
  intros segs v b b' M K Hb HK. destruct K as [a w x|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2]; cbn [kentry_nb] in Hb; cbn [kentry_ok] in *;
    unfold flat, estart, elenZ, adenot in *; try discriminate Hb; try exact HK.
  - apply andb_prop in Hb as (H1 & H2). rewrite <- (edenot_nb v b b' _ H1), <- (edenot_nb v b b' _ H2). exact HK.
  - apply andb_prop in Hb as (H1 & H2). rewrite <- (edenot_nb v b b' _ H1), <- (edenot_nb v b b' _ H2). exact HK.
  - rewrite <- (edenot_nb v b b' _ Hb). exact HK.
  - rewrite <- (edenot_nb v b b' _ Hb). exact HK.
  - rewrite <- (edenot_nb v b b' _ Hb). exact HK.
  - apply andb_prop in Hb as (H1 & H2). rewrite <- (edenot_nb v b b' _ H1), <- (edenot_nb v b b' _ H2). exact HK.
Qed.
Lemma know_ok_nb : forall segs v b b' M kn, forallb kentry_nb kn = true -> know_ok segs (Env v b) M kn -> know_ok segs (Env v b') M kn.
Proof.
  intros segs v b b' M kn Hb HK. unfold know_ok in *. rewrite Forall_forall in *. intros K HKin.
  exact (kentry_ok_nb segs v b b' M K (proj1 (forallb_forall _ _) Hb K HKin) (HK K HKin)).
Qed.
Lemma main_nb : forallb expr_nb sr_mainA = true /\ forallb kentry_nb kn_mainA = true.
Proof. vm_compute. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_body_nilA : forall data fs, t_body data fs [].
Proof. intros data fs. unfold t_body. repeat (first [apply t_emit_has_nil | destruct (_ <=? _)%Z | destruct (_ <? _)%nat]). Qed.
Lemma t_body_refusedA : forall data fs, MAX_INPUT <= Z.of_nat (length data) -> t_body data fs = t_die msg_refused fs.
Proof. intros data fs H. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.
Lemma t_body_shortA : forall data fs, Z.of_nat (length data) < MAX_INPUT -> (length data < 6)%nat -> t_body data fs = t_die msg_short fs.
Proof.
  intros data fs H1 H2. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact H2). reflexivity.
Qed.
Lemma CFGA_eq : forall data, ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768)%Z = CFGA data.
Proof. intros. reflexivity. Qed.
Lemma t_body_overrunA : forall data fs, Z.of_nat (length data) < MAX_INPUT -> (6 <= length data)%nat ->
  Z.of_nat (length data) < 6 + CFGA data -> t_body data fs = t_die msg_overrun fs.
Proof.
  intros data fs H1 H2 H3. pose proof (CFGA_range (Z_to_bv 64 0) data) as HC. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFGA_eq.
  replace (length data <? 6 + Z.to_nat (CFGA data))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.
Lemma t_body_okA : forall data fs, Z.of_nat (length data) < MAX_INPUT -> 6 + CFGA data <= Z.of_nat (length data) ->
  t_body data fs = t_emit (W 1 (zero_lines (Z.to_nat (CALLSA data)))) (t_exit (exit_code 0) fs).
Proof.
  intros data fs H1 H3. pose proof (CFGA_range (Z_to_bv 64 0) data) as HC. pose proof (B2A_range (Z_to_bv 64 0) data) as HB. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFGA_eq.
  replace (length data <? 6 + Z.to_nat (CFGA data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  unfold CALLSA. change (bv_unsigned (nth 2 data (Z_to_bv 8 0))) with (B2A data).
  destruct (Z.to_nat (CFGA data)) eqn:E.
  - replace (CFGA data =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (CFGA data =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    pose proof (Z.mod_pos_bound (B2A data) 4 ltac:(lia)). rewrite Z2Nat.inj_add, Nat.add_1_r by lia. reflexivity.
Qed.
Lemma list_byte_eqb_iffA : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  intros p. induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate | discriminate]); [tauto|].
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 H2]. f_equal; [apply bv_eq; exact H1 | exact H2].
  - intros H. injection H as -> ->. auto.
Qed.

#[local] Existing Instance PropExec.fx0.
Section Main.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record drv_ctxA (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (ar : asan_run) (HI : asan_iface) (sp0 : word) (M0 : word -> option byte) : Prop := DRV_CTXA {
  dc_iface : asan_iface_okB L ar C scfg HI;
  dc_fnull : afree_null_spec L ar scfg HI;
  dc_icpt : aicpt_ok L ar IL scfg HI;
  dc_consts : drv_consts_stmt L C IL;
  dc_sp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47;
  dc_al : bv_unsigned sp0 mod 16 = 0;
  dc_layout : drv_layoutA L ar IL sp0;
  dc_m0 : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0)
}.
(* [comment removed for export] *)
Record drv_pathA (sp0 : word) (M0 : word -> option byte) (p1 : word) (path : list byte) : Prop := DRV_PATHA {
  dp_lo : bv_unsigned sp0 <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47;
  dp_str : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]);
  dp_nonul : ~ In (Z_to_bv 8 0) path;
  dp_len : Z.of_nat (length path) <= 131071;
  dp_def : defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16)          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition dg_openerr_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA L C IL ar HI sp0 M0 -> forall path fs0 fdata p1 cr0 A0, drv_pathA sp0 M0 p1 path ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    open_err_kA scfg ar HI sp0 fs0 fdata p1 M0 [] cr0 A0 (t_die (msg_cannot_open path) fs0).
(* [comment removed for export] *)
Definition dg_short_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA L C IL ar HI sp0 M0 -> forall fs0 fdata p0 p1 can A0 CAP crC,
    65536 <= CAP <= 67108864 -> Z.of_nat (length fdata) < CAP -> (length fdata < 6)%nat ->
    close_kgA scfg ar HI sp0 fs0 fdata p0 p1 can M0 [] A0 CAP crC (t_die msg_short fs0).
Definition dg_overrun_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA L C IL ar HI sp0 M0 -> forall fs0 fdata p0 p1 can A0 CAP crC,
    65536 <= CAP <= 67108864 -> Z.of_nat (length fdata) < CAP -> (6 <= length fdata)%nat -> Z.of_nat (length fdata) < 6 + CFGA fdata ->
    close_kgA scfg ar HI sp0 fs0 fdata p0 p1 can M0 [] A0 CAP crC (t_die msg_overrun fs0).
(* [comment removed for export] *)
Definition dg_refuse_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA L C IL ar HI sp0 M0 -> forall path fs0 fdata p0 p1 can A0,
    fs_lookup fs0 path = Some fdata -> 67108864 <= Z.of_nat (length fdata) ->
    refuse_kA scfg ar HI sp0 path fs0 fdata p0 p1 can M0 [] A0 (t_die msg_refused fs0).
(* [comment removed for export] *)
Definition drv_main_on (P : list byte -> Fs.Fs -> Prop) (KP : list byte -> Fs.Fs -> TSet)
           (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs -> P path fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_okB L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okA Lay ar scfg HI (LSt ar) -> drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp p0 M0 ->
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    cr0 = (8192, 2 ^ 34) ->
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) (KP path fs).
(* [comment removed for export] *)
Definition dg_nofile_stmt := drv_main_on (fun path fs => (4096 <= length path)%nat \/ path = [] \/ (path <> dot_path /\ fs_lookup fs path = None))
                                         (fun path fs => t_die (msg_cannot_open path) fs).
(* [comment removed for export] *)
Definition dg_dot_stmt := drv_main_on (fun path _ => path = dot_path) (fun path fs => t_alt2 (t_die (msg_cannot_open path) fs) (t_die (msg_read_error path) fs)).

(* [comment removed for export] *)
Definition drv_budgetA (L : asan_layout) (Lay : lib_layoutA) : Prop :=
  forall n, 0 <= n < 67108864 ->
    credA L (hl_k_per_malloc L + 4 * fst (lla_credit Lay n)) (hl_b_lin L * n + hl_b_overhead L + 4 * snd (lla_credit Lay n)) 0 (adebit L (8192, 2 ^ 34) 65536).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem as0_drv_main : forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  drv_lib_layoutA Lay L -> drv_lib_cellsA Lay -> drv_budgetA L Lay ->
  dg_openerr_stmt L C IL -> dg_short_stmt L C IL -> dg_overrun_stmt L C IL -> dg_refuse_stmt L C IL ->
  dg_nofile_stmt L C IL Lay LSt -> dg_dot_stmt L C IL Lay LSt ->
  drv_main_stmt scfg L C IL Lay LSt.
Proof.
  intros L C IL Lay LSt DLL DLC HBUD DG_OPENERR DG_SHORT DG_OVERRUN DG_REFUSE DG_NOFILE DG_DOT.
  unfold drv_main_stmt.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok LSXa DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  cbn [spec].
  destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
  { exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs (or_introl Hlong) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  destruct (list_byte_eqb path []) eqn:Hemp.
  { apply list_byte_eqb_iffA in Hemp.
    exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs (or_intror (or_introl Hemp)) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  assert (Hne : path <> []) by (intros E; apply list_byte_eqb_iffA in E; rewrite E in Hemp; discriminate).
  destruct (list_byte_eqb path dot_path) eqn:Hdot.
  { apply list_byte_eqb_iffA in Hdot.
    exact (DG_DOT Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs Hdot ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_iffA in E; rewrite E in Hdot; discriminate).
  destruct (fs_lookup fs path) as [fdata|] eqn:Hlk.
  2:{ exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs (or_intror (or_intror (conj Hnd Hlk))) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO
               Ecr PDEF SAH). }
  (* [comment removed for export] *)
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA L C IL ar HI sp M0) by (constructor; try assumption).
  assert (Hppl : openat_plain_name path = true).
  { destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
    unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
    lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
    exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity. }
  assert (Hnonul : ~ In (Z_to_bv 8 0) path).
  { destruct Hva as (_ & _ & _ & Hnn & _). inversion Hnn as [|x l _ Hn2]; subst. inversion Hn2 as [|y l2 Hy _]; subst. exact Hy. }
  assert (Hplen131 : Z.of_nat (length path) <= 131071).
  { destruct Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l _ Hf2]; subst. inversion Hf2 as [|y l2 Hy _]; subst. exact Hy. }
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (PTH : drv_pathA sp M0 p1 path) by (constructor; assumption).
  subst cr0.
  (* [comment removed for export] *)
  set (PLv := Z.max 0 (Z.min (PLA fdata) 67108863)).
  assert (HPLv : 0 <= PLv < 67108864) by lia.
  destruct (dlla_credit_pos Lay L DLL PLv ltac:(lia)) as [CP1 CP2].
  pose proof (HBUD PLv HPLv) as HB. pose proof HB as (HB1 & HB2).
  assert (Hcr65536 : acredit_ok L (8192, 2 ^ 34) 65536).
  { unfold credA, adebit, acredit_ok, CAPk in *. cbn [fst snd] in *. rewrite Z.pow_0_r in HB2. nia. }
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; fdata]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; fdata]) _ _ NB2 HK) as HK'.
  apply (@drv_openA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL path fs fdata p0 p1 can M0 M0def Hlk Hne Hppl Hfs ltac:(lia) Hnonul ltac:(lia) STRF [] (8192, 2 ^ 34) A0 Hcr65536
           (t_die (msg_cannot_open path) fs) (t_body fdata fs) R model tid HR' HK' DI FDS EFS).
  - exact (DG_OPENERR ar HI sp M0 CTX path fs fdata p1 (8192, 2 ^ 34) A0 PTH SAH).
  - apply (@drv_fileA PropExec.fx0 scfg L ar C IL HI HIok ICok ILY sp Hsp Hal DL HRD (conj Hkpm (conj Hlin Hovh)) path fs fdata p0 p1 can M0 M0def Hlk [] A0
             (hl_k_per_malloc L + 4 * fst (lla_credit Lay PLv)) (hl_b_lin L * PLv + hl_b_overhead L + 4 * snd (lla_credit Lay PLv)) ltac:(lia) ltac:(nia)
             (t_body fdata fs) (t_body_nilA fdata fs)); [ | | exact HB].
    + (* [comment removed for export] *)
      intros Hlt CAP crC HCAP HltC HK1 HB1'.
      destruct (Nat.lt_ge_cases (length fdata) 6) as [Hs|Hge6].
      { rewrite (t_body_shortA fdata fs) by (unfold MAX_INPUT; lia). exact (DG_SHORT ar HI sp M0 CTX fs fdata p0 p1 can A0 CAP crC HCAP HltC Hs). }
      destruct (Z.lt_ge_cases (Z.of_nat (length fdata)) (6 + CFGA fdata)) as [Hov|Hok].
      { rewrite (t_body_overrunA fdata fs) by (unfold MAX_INPUT; lia). exact (DG_OVERRUN ar HI sp M0 CTX fs fdata p0 p1 can A0 CAP crC HCAP HltC Hge6 Hov). }
      rewrite (t_body_okA fdata fs) by (unfold MAX_INPUT; lia).
      apply (@hdr_okA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL fs fdata p0 p1 can M0 [] A0 CAP HCAP crC HltC Hok); [| apply t_emit_has_nil].
      assert (HPLeq : PLA fdata = PLv) by (unfold PLv, PLA; pose proof (CFGA_range sp fdata); lia).
      apply (@drv_targetA PropExec.fx0 scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def [] A0 CAP HCAP crC HltC Hok); [ | | apply t_emit_has_nil].
      * intros HPLp. unfold acredit_ok. rewrite HPLeq. lia.
      * apply (@drv_loopA scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def A0 CAP HCAP HltC Lay (LSt ar) ILY HPR DLL DLC LIok [] crC AUXV).
        -- (* [comment removed for export] *)
           pose proof (CALLSA_range sp fdata) as HCL.
           unfold Ba0DrvE_b.lib_roomA, Ba0DrvE_b.credit_scaleA, credit_le, cr1A. rewrite HPLeq. cbn [fst snd].
           split.
           ++ destruct (PLv =? 0)%Z eqn:EP; unfold adebit; cbn [fst snd]; split; nia.
           ++ intros c Hc. destruct (dlla_frames Lay L DLL c Hc) as (LK1 & LK2). change (ff_count c []) with 0%nat. change (Z.of_nat 0) with 0. nia.
        -- exact (tail_XA scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def A0 CAP HCAP Lay (LSt ar) ILY HEX FNok LSXa).
    + (* [comment removed for export] *)
      intros Hge. rewrite (t_body_refusedA fdata fs) by (unfold MAX_INPUT; lia).
      exact (DG_REFUSE ar HI sp M0 CTX path fs fdata p0 p1 can A0 Hlk Hge).
  - apply t_body_nilA.
Qed.
End Main.
