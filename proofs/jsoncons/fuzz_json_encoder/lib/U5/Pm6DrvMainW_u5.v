(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec BigintSpec RefNodes. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Startup_u5 Pm6MainEntry_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Hoare.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Usage_u5 Pm6OpenFail_defs_u5 Pm6OpenFail_u5.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface LibIface LibIfaceFp DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvLib_u5 Pm6DrvA_u5 Pm6DrvC_defs_u5 Pm6DrvC_u5 Pm6DrvD_defs_u5 Pm6DrvLibL_u5 Pm6DrvD_u5
  Pm6DrvE_u5 Pm6DrvG_defs_u5 Pm6DrvG_u5 Pm6DrvH_u5.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Drv Require Import LibStaticsU.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmXubsanStmt.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import LibIfaceFpW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvLibLW_u5 Pm6DrvFW_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SpecG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1.
Variable scfg : SpuriousCfg.
#[local] Existing Instance PropExec.fx0.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_body_nil : forall data fs, t_body data fs [].
Proof.
  intros data fs. unfold t_body.
  repeat (first [apply t_emit_has_nil | destruct (_ <=? _)%Z | destruct (_ <? _)%nat]).
Qed.

Lemma t_body_refused : forall data fs, MAX_INPUT <= Z.of_nat (length data) -> t_body data fs = t_die msg_refused fs.
Proof. intros data fs H. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

Lemma t_body_short : forall data fs, Z.of_nat (length data) < MAX_INPUT -> (length data < 6)%nat -> t_body data fs = t_die msg_short fs.
Proof.
  intros data fs H1 H2. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact H2). reflexivity.
Qed.

Lemma CFG_eq : forall data,
  ((bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) mod 32768)%Z = CFG data.
Proof. intros. reflexivity. Qed.

Lemma t_body_overrun : forall data fs, Z.of_nat (length data) < MAX_INPUT -> (6 <= length data)%nat ->
  Z.of_nat (length data) < 6 + CFG data -> t_body data fs = t_die msg_overrun fs.
Proof.
  intros data fs H1 H2 H3. pose proof (CFG_range data) as HC. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
  replace (length data <? 6 + Z.to_nat (CFG data))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Lemma t_body_ok : forall data fs, Z.of_nat (length data) < MAX_INPUT -> 6 + CFG data <= Z.of_nat (length data) ->
  t_body data fs = t_emit (W 1 (zero_lines (Z.to_nat (CALLS data)))) (t_exit (exit_code 0) fs).
Proof.
  intros data fs H1 H3. pose proof (CFG_range data) as HC. pose proof (B2_range data) as HB. unfold t_body.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
  replace (length data <? 6 + Z.to_nat (CFG data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  unfold CALLS. change (B2 data) with (bv_unsigned (nth 2 data (Z_to_bv 8 0))). fold (B2 data).
  destruct (Z.to_nat (CFG data)) eqn:E.
  - replace (CFG data =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (CFG data =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. reflexivity.
Qed.

Lemma PL_eq : forall data, PL data = (Z.of_nat (length data) - 6 - CFG data)%Z.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_bodyG_nil : forall PhiD data fs, t_bodyG PhiD data fs [].
Proof.
  intros PhiD data fs. unfold t_bodyG.
  repeat (first [apply t_emit_has_nil | destruct (_ <=? _)%Z | destruct (_ <? _)%nat]).
Qed.
Lemma t_bodyG_refused : forall PhiD data fs, MAX_INPUT <= Z.of_nat (length data) -> t_bodyG PhiD data fs = t_die msg_refused fs.
Proof. intros PhiD data fs H. unfold t_bodyG. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.
Lemma t_bodyG_short : forall PhiD data fs, Z.of_nat (length data) < MAX_INPUT -> (length data < 6)%nat -> t_bodyG PhiD data fs = t_die msg_short fs.
Proof.
  intros PhiD data fs H1 H2. unfold t_bodyG.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact H2). reflexivity.
Qed.
Lemma t_bodyG_overrun : forall PhiD data fs, Z.of_nat (length data) < MAX_INPUT -> (6 <= length data)%nat ->
  Z.of_nat (length data) < 6 + CFG data -> t_bodyG PhiD data fs = t_die msg_overrun fs.
Proof.
  intros PhiD data fs H1 H2 H3. pose proof (CFG_range data) as HC. unfold t_bodyG.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
  replace (length data <? 6 + Z.to_nat (CFG data))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.
Lemma t_bodyG_ok : forall PhiD data fs, Z.of_nat (length data) < MAX_INPUT -> 6 + CFG data <= Z.of_nat (length data) ->
  t_bodyG PhiD data fs = succG (PhiD data) (Z.to_nat (CALLS data)) fs.
Proof.
  intros PhiD data fs H1 H3. pose proof (CFG_range data) as HC. pose proof (B2_range data) as HB. unfold t_bodyG.
  replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). cbv zeta. rewrite CFG_eq.
  replace (length data <? 6 + Z.to_nat (CFG data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  unfold CALLS. change (B2 data) with (bv_unsigned (nth 2 data (Z_to_bv 8 0))). fold (B2 data).
  destruct (Z.to_nat (CFG data)) eqn:E.
  - replace (CFG data =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (CFG data =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hdr_okD_iff : forall data, SpecG.hdr_okD data <-> (Z.of_nat (length data) < MAX_INPUT /\ (6 <= length data)%nat /\ 6 + CFG data <= Z.of_nat (length data)).
Proof.
  intros data. unfold SpecG.hdr_okD, SpecG.cfgD. rewrite CFG_eq. pose proof (CFG_range data) as HC. split; intros (A & B & C); (split; [exact A | split; [exact B | lia]]).
Qed.

Lemma list_byte_eqb_iff : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  intros p. induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate | discriminate]); [tauto|].
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 H2]. f_equal; [apply bv_eq; exact H1 | exact H2].
  - intros H. injection H as -> ->. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  (* [comment removed for export] *)
  Variable LF : word -> heap_layout.
  Variable HIF : word -> heap_iface.
  (* [comment removed for export] *)
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  (* [comment removed for export] *)
  Variable cr0 : credit.

  Hypothesis HIokF : forall sp, valid_sp sp -> heap_iface_ok (LF sp) scfg (HIF sp).
  Hypothesis DLF : forall sp, valid_sp sp -> drv_layout (LF sp) sp.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (LF sp).
  (* [comment removed for export] *)
  Variable PHI : list byte -> Prop.
  Hypothesis LIokWF : forall sp, valid_sp sp -> LCU.lib_iface_okU (LayF sp) scfg (HIF sp) (LStF sp) PHI.
  Hypothesis LXokF : forall sp, valid_sp sp -> lib_exit_ok (LStF sp).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HINIT : forall (lim : Z) sp a0s path envp uid hw rdraw tid regs mem brk mbase,
    (lim <= 2 ^ 39)%Z ->
    valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase -> valid_argv [a0s; path] -> valid_envp envp ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z -> main_entry sp [a0s; path] envp uid hw rdraw tid regs mem ->
    hi_heap (HIF sp) [] cr0 mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp).
  (* [comment removed for export] *)
  Hypothesis Hfs : sc_fs scfg = true.
  (* [comment removed for export] *)
  Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    cred (LF sp) (hl_k_per_malloc (LF sp) + 4 * fst (ll_credit (LayF sp) n))
                 (n + hl_b_overhead (LF sp) + 4 * snd (ll_credit (LayF sp) n)) 0 (debit (LF sp) cr0 65536).

  (* [comment removed for export] *)
  Definition src_realizes_stmtG_lim (lim : Z) : Prop :=
    forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
      (forall a0s path, in_argv inp = [a0s; path] -> PmXubsanStmt.phi_okU PHI path (in_fs inp)) ->
      srealizes RSEGS scfg
        (init_config RSEGS Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rdraw lim inp)
        (specG (fun d => PHI (payload d)) (in_argv inp) (in_fs inp)).

  Lemma cred_credit_ok : forall L Kc Bc, 0 <= Kc -> 0 <= Bc -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
    cred L Kc Bc 0 (debit L cr0 65536) -> credit_ok L cr0 65536.
  Proof.
    intros L Kc Bc HK HB Hk Hb [C1 C2]. unfold debit, credit_ok, CAPk in *. cbn [fst snd] in C1, C2. rewrite Z.pow_0_r in C2. lia.
  Qed.

  Theorem src0_realizes_specG_lim : forall lim, (lim <= 2 ^ 39)%Z -> src_realizes_stmtG_lim lim.
  Proof.
    unfold src_realizes_stmtG_lim. intros lim Hlim sp brk mbase rdraw inp Hsp Hbrk Hmb Hfits Hva Hve Hvfs Hcreds HPHIOK.
    apply ref_startup; try assumption.
    intros tid regs mem Htid ME.
    rewrite with_tid_init_model_E.
    set (RE := run_env_of inp).
    destruct inp as [argv envp ifs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0].
    unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp in_stdin in_uid in_hwcap] in *.
    (* [comment removed for export] *)
    set (fs0 := fs_seed_tmp ifs0 tmp0) in *. clearbody fs0.
    assert (Huid : bv_unsigned uid < 2 ^ 32) by (destruct Hcreds as [Hu _]; unfold valid_id in Hu; cbn [in_uid] in Hu; lia).
    clearbody RE. clear Hcreds.
    pose proof (HIokF sp Hsp) as HIok. pose proof (DLF sp Hsp) as DL. pose proof (DLLF sp Hsp) as DLL. pose proof (LXokF sp Hsp) as LXok. pose proof (LIokWF sp Hsp) as LIokW.
    set (L := LF sp) in *. set (HI := HIF sp) in *. set (Lay := LayF sp) in *. set (LSt := LStF sp) in *.
    pose proof (dl_k L sp DL) as Hkpm. pose proof (dl_b L sp DL) as Hovh.
    assert (Hcr65536 : credit_ok L cr0 65536).
    { destruct (dll_credit_pos Lay L DLL 0 ltac:(lia)) as [P1 P2]. pose proof (Hbudget sp 0 Hsp ltac:(lia)) as HB0.
      fold L Lay in HB0. refine (cred_credit_ok L _ _ _ _ Hkpm Hovh HB0); lia. }
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage_w scfg sp [] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - apply (ref_usage_w scfg sp [a0s] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - cbn [specG].
      pose proof (HINIT lim sp a0s path envp uid hw rdraw tid regs mem brk mbase Hlim Hsp Hbrk Hmb Hva Hve Htid ME) as HH0. fold HI in HH0.
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply list_byte_eqb_iff in Hemp.
          apply (ref_open_fail_empty_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits Hemp).
        * assert (Hne : path <> []) by (intros E; apply list_byte_eqb_iff in E; rewrite E in Hemp; discriminate).
          (* [comment removed for export] *)
          assert (HKA : open_err_k scfg sp a0s path envp hw rdraw tid mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp)
                          fs0 stdin0 (t_die (msg_cannot_open path) fs0)).
          { unfold open_err_k. intros e vals R M He HL P0 P38 P2 HR HK HA.
            exact (ref_open_fail_errno scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp ME Hfits
                     e vals R M He HL P0 P38 P2 HR HK HA). }
          replace (0x3a170%bv : word) with (Z_to_bv 64 0x3a170) by (apply bv_eq; reflexivity).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- (* [comment removed for export] *)
             apply list_byte_eqb_iff in Hdot.
             pose proof (drv_dir scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem _ fs0 stdin0 cr0 Hva Hve Hsp Htid ME Hfits Hfs Hdot DL HH0 Hcr65536
                           _ HKA) as HD.
             rewrite Hdot in HD |- *. exact HD.
          -- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_iff in E; rewrite E in Hdot; discriminate).
             (* [comment removed for export] *)
             assert (Hppl : openat_plain_name path = true).
             { destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
               unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
               lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
               exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity. }
             destruct (fs_lookup fs0 path) as [fdata|] eqn:Hlk.
             ++ (* [comment removed for export] *)
                apply (drv_open scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem _ fs0 stdin0 fdata cr0 Hva Hve Hsp Htid ME Hlk Hne Hppl Hfs
                         ltac:(lia) DL HH0 Hcr65536 _ _ HKA); [| apply t_bodyG_nil].
                (* [comment removed for export] *)
                set (PLv := Z.max 0 (Z.min (PL fdata) 67108863)).
                assert (HPLv : 0 <= PLv < 67108864) by lia.
                destruct (dll_credit_pos Lay L DLL PLv ltac:(lia)) as [CP1 CP2].
                apply (drv_file scfg L HI HIok sp a0s path envp uid hw rdraw tid mem
                         fs0 stdin0 fdata cr0 Hva Hve Hsp Htid Hlk ltac:(lia) DL
                         (hl_k_per_malloc L + 4 * fst (ll_credit Lay PLv)) (PLv + hl_b_overhead L + 4 * snd (ll_credit Lay PLv))
                         ltac:(lia) ltac:(lia) (t_bodyG (fun d => PHI (payload d)) fdata fs0) (t_bodyG_nil _ fdata fs0)).
                ** (* [comment removed for export] *)
                   intros Hlt CAP crC HCAP HltC HK1 HB1.
                   destruct (Nat.lt_ge_cases (length fdata) 6) as [Hs|Hge6].
                   { rewrite (t_bodyG_short _ fdata fs0) by (unfold MAX_INPUT; lia).
                     exact (hdr_short scfg L HI HIok sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP crC Hs). }
                   destruct (Z.lt_ge_cases (Z.of_nat (length fdata)) (6 + CFG fdata)) as [Hov|Hok].
                   { rewrite (t_bodyG_overrun _ fdata fs0) by (unfold MAX_INPUT; lia).
                     exact (hdr_overrun scfg L HI HIok sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP HCAP crC HltC Hge6 Hov). }
                   rewrite (t_bodyG_ok _ fdata fs0) by (unfold MAX_INPUT; lia). cbv beta.
                   apply (hdr_ok scfg L HI sp a0s path envp uid hw rdraw tid mem fs0 stdin0 fdata Hva Hve Hsp ltac:(lia) DL CAP HCAP crC HltC Hok);
                     [| apply t_emit_has_nil].
                   assert (HPLeq : PL fdata = PLv) by (unfold PLv; rewrite !PL_eq; pose proof (CFG_range fdata); lia).
                   apply (drv_target scfg L HI HIok sp a0s path envp uid hw rdraw tid mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp) fs0 stdin0 fdata Hva Hve Hsp Htid ltac:(lia) DL CAP HCAP crC HltC Hok);
                     [ intros HPLp; unfold credit_ok; rewrite HPLeq; lia | exact fp_ok_fx0 | | apply t_emit_has_nil].
                   assert (HPHI : PHI (payload fdata)).
                   { apply (HPHIOK a0s path eq_refl ltac:(lia) Hne Hnd fdata Hlk). apply hdr_okD_iff.
                     split; [exact Hlt | split; [lia | exact Hok]]. }
                   apply (drv_loopw scfg L HI HIok sp a0s path envp uid hw rdraw tid regs mem (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp) fs0 stdin0 fdata Hva Hve Hsp Htid ME ltac:(lia) DL CAP HCAP crC HltC
                            Lay LSt DLL (LIOU Lay scfg HI LSt PHI LIokW) LXok PHI LIokW Huid Hfits Hok); [| exact HPHI | exact HPHI].
                   (* [comment removed for export] *)
                   pose proof (CALLS_range fdata) as HCL.
                   unfold credit_le, credit_scale, cr1. rewrite HPLeq. cbn [fst snd].
                   destruct (PLv =? 0)%Z eqn:EP; unfold debit; cbn [fst snd]; split; nia.
                ** (* [comment removed for export] *)
                   intros Hge. unfold refuse_at. rewrite (t_bodyG_refused _ fdata fs0) by (unfold MAX_INPUT; lia).
                   exact (drv_refuse scfg HI sp a0s path envp hw rdraw tid mem fs0 stdin0 fdata Hsp Htid ltac:(lia)).
                ** pose proof (Hbudget sp PLv Hsp HPLv) as HB. fold L Lay in HB. exact HB.
             ++ replace (Z_to_bv 64 0x3a170) with (0x3a170%bv : word) by (apply bv_eq; reflexivity).
                apply (ref_open_fail_absent_w scfg sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits ltac:(lia) Hne Hppl Hlk).
    - apply (ref_usage_w scfg sp (a0s :: path :: x :: l) envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 _ Hva Hve Hsp Htid ME Hfits). cbn; lia.
  Qed.

  (* [comment removed for export] *)
End Main.
End FPX_1.
