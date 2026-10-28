(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX MemSplit MuslStrlen Spec RefNodes LibTail UbLibDiagKn UbLibDiagKnMain UbStartup UbStartupFacts UbMainEntry UbMainEntryN UbStartupDefs UbUsageCS_defs UbUsageCS UbOpenFailCS_defs UbOpenFailCS UbReadErr_defs UbReadErr UbRefused UbHdrErr UbStdioDefs UbExitBase UbMainExit UbLibMainRet HeapCeil RegsEquivM MainEqv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import MainDefs MainArith MainWalk_defs MainMem MainHeap MainSegs MainOpen MainLoop.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; intros [|b q]; cbn; try (split; [discriminate|congruence]).
  - split; reflexivity.
  - rewrite andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
    + intros [Hab ->]. f_equal. apply bv_eq. exact Hab.
    + intros E. injection E as -> ->. split; reflexivity.
Qed.

Lemma ro_none_mem_inv : forall m, ro_none m -> mem_inv usegs m.
Proof.
  intros m Hro a b Hab. destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L|L]; [apply ro_addr_false; lia|].
  destruct (Z_lt_le_dec (bv_unsigned a) 0x2c5000) as [L2|L2]; [|apply ro_addr_false; lia].
  exfalso. pose proof (Hro (bv_unsigned a) ltac:(lia)) as E. rewrite Z_to_bv_bv_unsigned in E. congruence.
Qed.

Section Top.
  Context {HCEIL : HeapCeil}.
  Variable HS : hsr.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.

  Let KRELh : forall s mo, hs_KREL HS s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. destruct HH as (_ & K & _). exact K. Qed.
  Let AOK : alloc_ok_of_live HS.
  Proof. destruct HH as (_ & _ & _ & A & _). exact A. Qed.
  Let RFR : RHEAP_frame HS.
  Proof. destruct HH as (_ & _ & _ & _ & A & _). exact A. Qed.
  Let RBR : RHEAP_block_range HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let AUF : rauxv_frame HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let LBR : lb_remove_laws HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section TwoArgs.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
    Variables (ps0 : PState) (B : Z).
    Hypothesis Hva : valid_argv [a0s; path].
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
    Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
    Hypothesis RH0 : hs_RHEAP HS ps0 [] mem0.
    Hypothesis AUX0 : hs_rauxv_ok HS mem0 B.
    Hypothesis HB : bv_unsigned sp0 <= B.
    Hypothesis HB64 : B < 2 ^ 64.
    Hypothesis HCE : hceil + 8388608 <= bv_unsigned sp0.
    Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.

    Let model0 : Model := MainDefs.model0 tid brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0).
    Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
    Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
    Let pp : word := p1 sp0 a0s path envv.
    Let spm : Z := bv_unsigned sp0 - 128.
    Let lo : Z := bv_unsigned sp0 - 8388608.
    Let tidZ : Z := bv_unsigned tid.

    Hypothesis KR0 : hs_KREL HS ps0 model0.

    Lemma model0_fds : m_fds model0 = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
    Proof. reflexivity. Qed.
    Lemma model0_fs : m_fs model0 = fs0.
    Proof. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma stk_at_open : forall M l h, frame_mod mem0 M (regA_w sp0) ->
      bv_unsigned sp0 - stack_max_size <= l -> h <= bv_unsigned sp0 -> stk usegs M l h.
    Proof.
      intros M l h [_ Hg] Hl Hh. pose proof SPlo as Hlo. pose proof SPhi as Hhi. rewrite stack_max_size_val in Hl.
      apply (stk_grows sp0 mem0 M); [| lia | exact Hg].
      split; [lia|]. split; [lia|]. intros x Hx.
      assert (NE : mem0 (wa x) <> None).
      { apply (main_entry_win_mapped sp0 _ _ rdraw tid regs0 mem0 ME). rewrite wa_eq, u_small by lia. rewrite stack_max_size_val. lia. }
      destruct (mem0 (wa x)) as [b|] eqn:E; [|congruence]. split.
      + unfold wview. rewrite E. discriminate.
      + exists b. unfold mrd. rewrite E. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma statics_at_open : forall M,
      frame_mod mem0 M (regA_w sp0) -> frameA sp0 M -> statics HS sp0 tidZ B M.
    Proof.
      intros M FM FA. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      assert (RS : forall r, In r (regA_w sp0) -> bv_unsigned (fst r) = bv_unsigned sp0 - 224 /\ snd r = 176).
      { intros r Hr. unfold regA_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. split; reflexivity. }
      pose proof FM as [Hout Hg].
      split.
      - eapply mem_inv_frame; [| exact FM |].
        + apply ro_none_mem_inv. exact (main_entry_ro_none sp0 _ _ rdraw tid regs0 mem0 Hvsp ME).
        + apply Forall_forall. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - apply stk_at_open; [exact FM | rewrite stack_max_size_val; lia | lia].
      - apply stk_at_open; [exact FM | rewrite stack_max_size_val; lia | lia].
      - eapply cells_ok_frame; [apply diag_cells_wf | exact (cells_ok_main_entry sp0 _ _ rdraw tid regs0 mem0 Hvsp ME) | exact FM |].
        eapply Forall_impl; [| apply diag_cells_range]. intros [[a w] v] [R1 R2] r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - eapply cells_ok_frame; [apply pf1_cells_wf | exact (pf1_cells_main_entry sp0 _ _ rdraw tid regs0 mem0 Hvsp ME) | exact FM |].
        eapply Forall_impl; [| apply pf1_cells_range]. intros [[a w] v] [R1 R2] r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - eapply rdn_frame; [exact FM | | unorm; lia |].
        + subst tidZ. rewrite Z_to_bv_bv_unsigned. apply (UbStartupFacts.main_entry_tid sp0 _ _ rdraw tid Hlo regs0 mem0 ME).
        + intros r Hr. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - intros i Hi. pose proof (prist_rng_bounds i Hi) as Hb. rewrite (Hout (Z_to_bv 64 i)).
        + (* [comment removed for export] *)
          prist_lit Hi. repeat match type of Hi with _ \/ _ => destruct Hi as [Hi|Hi] end;
            first [ exfalso; exact Hi
                  | apply (main_entry_none_below sp0 _ _ rdraw tid regs0 mem0 Hvsp ME); lia
                  | none_by_range Hvsp ME Hi ].
        + apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2, u_small by lia. lia.
      - exact FA.
      - eapply AUF; [exact AUX0 | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
        unfold RAUXV_CELL. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
    Qed.

    Lemma heap_at_open : forall M, frame_mod mem0 M (regA_w sp0) -> hs_RHEAP HS ps0 [] M.
    Proof.
      intros M FM. pose proof SPlo. pose proof SPhi. hcb. eapply (heap_frame HS HH); [exact RH0 | exact FM |].
      intros r Hr. unfold regA_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. left. cbn [fst]. rewrite u_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma above_at_open : forall M, frame_mod mem0 M (regA_w sp0) ->
      forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M x = mem0 x.
    Proof.
      intros M FM x Hx. pose proof SPlo. pose proof SPhi. apply (proj1 FM). apply outside_of_disjoint. intros r Hr.
      unfold regA_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma first_alloc : forall vals R M mo K,
      length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
      regs_ok (MainOpen.ENV a0s path vals) srA R -> know_ok RSEGS (MainOpen.ENV a0s path vals) M knA ->
      statics HS sp0 tidZ B M -> hs_RHEAP HS ps0 [] M -> hs_KREL HS ps0 mo ->
      (forall regs' mem' model' A p s,
         read_call_regs sp0 regs' pp A 0 65536 65536 -> rblock_range A 65536 -> hs_RHEAP HS s [(p, A, 65536)] mem' -> hs_KREL HS s model' ->
         wr_at usegs mem' A 65536 -> statics HS sp0 tidZ B mem' ->
         rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe23ec)) ->
         m_fs model' = m_fs mo -> m_fds model' = m_fds mo ->
         (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> mem' x = M x) ->
         realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2c16a8) mem' (seg_rom RSEGS)) model') K) ->
      realizes RSEGS (mkCfg (mkst (regupd R 10 (Z_to_bv 64 3)) (Z_to_bv 64 0x2c16ac) M (seg_rom RSEGS)) mo) K.
    Proof.
      intros vals R M mo K HL P0 P2 HR HK ST RH KR HKK. pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb.
      destruct (KRELh ps0 mo KR) as [Hh Hlazy].
      eapply (seg_C sp0 a0s path envv Hvsp vals R M mo K Hh Hlazy HL P0 P2 HR HK).
      intros R' Q1 Q2 Q4 Q8 Q10 Q18 Q20 Q21.
      destruct (errno_rw M R' Q4) as [errv ERR].
      change (Z_to_bv 64 0x2b611c) with (Z_to_bv 64 RMALLOC_SYM).
      eapply (malloc_call HS HH HX R' M mo ps0 [] 65536 lo B errv 0xe2344 K Q1);
        [ lia | reflexivity | exact Q4 | exact Q10 | lia | exact RH | exact KR
        | apply (AOK ps0 [] M 65536 RH); [lia | cbn [lb_bytes fold_right]; pose proof (hx_live HS HX); lia | cbn [length]; pose proof (hx_live HS HX); lia
          | cbn [lb_big fold_right]; pose proof (big1_le1 65536); pose proof (hx_live HS HX); lia ]   (* [comment removed for export] *)
        | exact (st_aux _ _ _ _ _ ST) | rewrite Q2, u_small by lia; lia
        | rewrite Q2, u_small by lia; exact (st_stk _ _ _ _ _ ST)
        | subst lo; lia | rewrite Q2, u_small by lia; unfold RMALLOC_STACK; subst lo; lia
        | exact ERR | exact (st_inv _ _ _ _ _ ST) |].
      intros regs2 mem2 model2 A p s2 errv2 junk KEPT2 R10 HKR2 MP2 INV2 STK2 ERR2 AUX2 HP2 HBR2 HRH2 CB2.
      rewrite Q2, u_small in STK2, HP2 by lia.
      destruct (KRELh s2 model2 HKR2) as [Hh2 Hlazy2]. destruct (hx_mpres HS HX _ _ MP2) as [FS2 FDS2].
      assert (ST2 : statics HS sp0 tidZ B mem2) by (eapply (statics_heap HS HX sp0 tidZ B Hvsp Htid); [exact ST | exact HP2 | exact HRH2 | exact STK2 | exact INV2 | exact AUX2]).
      pose proof HBR2 as (C1 & C2 & C3 & C4 & C5). clear C2.
      assert (HWR2 : wr_at usegs mem2 A 65536) by (eapply (wr_at_of_CB sp0); [exact CB2 | lia]).
      pose proof (KEPT2 2%bv ltac:(clear; cbn; tauto)) as S2. pose proof (KEPT2 4%bv ltac:(clear; cbn; tauto)) as S4.
      pose proof (KEPT2 8%bv ltac:(clear; cbn; tauto)) as S8. pose proof (KEPT2 18%bv ltac:(clear; cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto]))) as S18.
      pose proof (KEPT2 20%bv ltac:(clear; cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto]))) as S20. pose proof (KEPT2 21%bv ltac:(clear; cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto]))) as S21.
      rewrite Q2 in S2. rewrite Q4 in S4. rewrite Q8 in S8. rewrite Q18 in S18. rewrite Q20 in S20. rewrite Q21 in S21.
      assert (ABOVE2 : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> mem2 x = M x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq. apply (proj1 (HP2 _ (u64_range x) ltac:(left; lia))). }
      (* [comment removed for export] *)
      eapply (seg_E sp0 model2 Hvsp Hh2 Hlazy2 regs2 mem2 pp A K);
        [ split; [exact S2 | split; [exact S4 | split; [exact S8 | split; [exact S18 | exact S20]]]]
        | exact R10 | lia | exact S21
        | apply (stk_ok_main HS sp0 tidZ B Hvsp); exact ST2 | apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ ST2) |].
      intros regs3 mem3 NR3 FM3 STK3.
      assert (ST3 : statics HS sp0 tidZ B mem3) by (eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact ST2 | exact FM3 | left; reflexivity]).
      (* [comment removed for export] *)
      eapply (seg_N sp0 model2 Hvsp Hh2 Hlazy2 regs3 mem3 pp A 0 65536 K NR3); [lia | lia
        | exact STK3 | apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ ST3) |].
      intros regs4 mem4 RC4 FM4 RA4 STK4.
      apply (HKK regs4 mem4 model2 A p s2).
      - exact RC4.
      - exact HBR2.
      - eapply (heap_frame HS HH); [| exact FM4 | apply (regL_w_hi sp0 Hvsp HCE)].
        eapply (heap_frame HS HH); [exact HRH2 | exact FM3 | apply (regL_w_hi sp0 Hvsp HCE)].
      - exact HKR2.
      - eapply wr_at_transport; [| exact (frame_mod_wmono _ _ _ FM4)]. eapply wr_at_transport; [exact HWR2 | exact (frame_mod_wmono _ _ _ FM3)].
      - eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact ST3 | exact FM4 | left; reflexivity].
      - exact RA4.
      - exact FS2.
      - exact FDS2.
      - intros x Hx. rewrite <- (ABOVE2 x Hx).
        rewrite (proj1 FM4 x) by (apply outside_of_disjoint; intros r Hr; unfold regL_w, MSTK in Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia).
        apply (proj1 FM3 x). apply outside_of_disjoint. intros r Hr. unfold regL_w, MSTK in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma RInv0 : forall mo regs' mem' model' A p s data,
      m_fs mo = fs0 -> m_fds mo = fd_insert (m_fds model0) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)) ->
      read_call_regs sp0 regs' pp A 0 65536 65536 -> rblock_range A 65536 -> hs_RHEAP HS s [(p, A, 65536)] mem' -> hs_KREL HS s model' ->
      wr_at usegs mem' A 65536 -> statics HS sp0 tidZ B mem' ->
      rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe23ec)) ->
      m_fs model' = m_fs mo -> m_fds model' = m_fds mo ->
      RInv HS sp0 pp tidZ path data B fs0 0 65536 A s p regs' mem' model'.
    Proof.
      intros mo regs' mem' model' A p s data FS FDS RC HBR RH KR WR ST RA FS' FDS'. split; try assumption.
      - lia.
      - lia.
      - exists 0. split; [lia | reflexivity].
      - reflexivity.
      - rewrite FS'. exact FS.
      - rewrite FDS', FDS. apply fd_lookup_insert_eq.
      - rewrite FDS', FDS, fd_lookup_insert_neq, model0_fds; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate].
      - rewrite FDS', FDS, fd_lookup_insert_neq, model0_fds; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    Qed.

    (* [comment removed for export] *)
    Lemma open_fail : forall e vals R M,
      (1 <= e <= 4095)%Z -> scF e ->
      length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
      regs_ok (MainOpen.ENV a0s path vals) srA R -> know_ok RSEGS (MainOpen.ENV a0s path vals) M knA ->
      statics HS sp0 tidZ B M -> hs_RHEAP HS ps0 [] M ->
      (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0x2c16ac) M (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
    Proof.
      intros e vals R M He HSC HL P0 P2 HR HK ST RH ABOVE. pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb.
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      eapply (seg_F sp0 a0s path envv Hvsp e vals R M model0 _ Hh Hlazy He HSC HL P0 P2 HR HK).
      intros R' M' Q2 Q4 Q18 FM.
      assert (RS : forall r, In r (regF_w sp0) -> (bv_unsigned (fst r) = bv_unsigned sp0 - 240 /\ snd r = 16) \/ (bv_unsigned (fst r) = 0x335ff4 /\ snd r = 4)).
      { intros r Hr. unfold regF_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      destruct ST as [INV STK TOP CELLS PF1 TID RELRO FR AUX].
      (* [comment removed for export] *)
      assert (RH' : hs_RHEAP HS ps0 [] M').
      { eapply RFR; [exact RH | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
        unfold rclient_write_ok. cbn [fst snd]. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2.
        + left. lia.
        + right. left. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia. }
      destruct (hx_statics HS HX _ _ _ RH') as (_ & _ & [can Hcan]).
      destruct (path_facts sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME) as (Sr & Slo & Shi & Sfit & t8 & Ht8).
      fold pp in Sr, Slo, Shi, Sfit, Ht8. pose proof (u64_range pp) as Hpr. pose proof (path_len a0s path Hva) as HPl.
      assert (ABOVE' : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = mem0 x).
      { intros x Hx. rewrite <- (ABOVE x Hx). apply (proj1 FM x). apply outside_of_disjoint. intros r Hr.
        destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; (first [clear - Hx Hvsp SPlo; lia | lia]). }
      rewrite <- model0_fs.
      refine (ref_cannot_open sp0 [] model0 Hvsp Hh Hlazy eq_refl pp tidZ can R' M' Q2 Q4 Q18 _ _ _ _ _ _ _ path t8 _ _ _ _ _ _).
      - assert (STK' : stk usegs M' lo spm) by (apply (stk_grows sp0 M M'); [exact STK | (first [clear - Hlo; lia | lia]) | exact (proj2 FM)]).
        eapply stk_stk_ok; [exact STK' | unfold UbOpenFailCS_defs.OF_STK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold UbOpenFailCS_defs.OF_STK; lia | lia].
      - intros i Hi. rewrite (proj1 FM (Z_to_bv 64 i)); [apply mem_inv_ro_none; [exact INV | exact Hi] |].
        apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2, u_small by lia; lia.
      - eapply cells_ok_frame; [apply diag_cells_wf | exact CELLS | exact FM |].
        pose proof diag_cells_no_errno as N1.
        eapply Forall_impl; [| apply (Forall_and diag_cells_range N1)].
        intros [[a w] v] [[R1 R2] R3] r Hr. cbn [fst snd]. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - eapply rdn_frame; [exact FM | exact TID | unorm; lia |]. intros r Hr. unorm.
        destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - subst tidZ. exact Htid.
      - exact Hcan.
      - exact Slo.
      - apply (path_nonul a0s path Hva).
      - exact HPl.
      - lia.
      - specialize (Sfit Hfit). lia.
      - rewrite <- Sr. apply rdn_ext; [lia|]. intros x Hx. apply ABOVE'. lia.
      - rewrite <- Ht8. apply rdn_ext; [unorm; lia|]. intros x Hx. apply ABOVE'. revert Hx. unorm. intros Hx. lia.
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition cs_ok (cs : list (Z * nat * Z)) : Prop :=
      forallb cell_wf_b cs = true /\ Forall (fun c => client_cell c \/ static_cell c) cs
      /\ Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x2c5000 <= a /\ a + Z.of_nat w <= 0x358000 /\ (a + Z.of_nat w <= 0x335ff4 \/ 0x335ff8 <= a) end) cs.

    (* [comment removed for export] *)
    Let slo : Z := bv_unsigned sp0 - 128 - TR_STACK.

    Record tstat (cs : list (Z * nat * Z)) (mem : word -> option byte) : Prop := TS {
      ts_inv   : mem_inv usegs mem;
      ts_stk   : stk usegs mem slo spm;
      ts_top   : stk usegs mem spm (bv_unsigned sp0 - 48);
      ts_cells : cells_ok mem cs;
      ts_tid   : exists t, rdn RSEGS mem (Z_to_bv 64 0x335ff0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 t)) /\ 0 < t < 2 ^ 22;
      ts_frame : mframe sp0 mem;
      ts_aux   : exists B', hs_rauxv_ok HS mem B' /\ bv_unsigned sp0 <= B' }.

    Lemma stk_shrink : forall m l l' h, stk usegs m l h -> l <= l' -> stk usegs m l' h.
    Proof. intros m l l' h (S1 & S2 & S3) Hl. split; [lia|]. split; [lia|]. intros a Ha. apply S3. lia. Qed.

    Lemma statics_tstat : forall cs m, cells_ok m cs -> statics HS sp0 tidZ B m -> tstat cs m.
    Proof.
      intros cs m Hc [INV STK TOP CELLS PF1 TID RELRO FR AUX]. pose proof SPlo. split; try assumption.
      - eapply stk_shrink; [exact STK | subst lo slo; unfold TR_STACK; lia].
      - exists tidZ. split; [exact TID | exact Htid].
      - exists B. split; [exact AUX | exact HB].
    Qed.

    Lemma tstat_frame : forall cs m m' rs,
      cs_ok cs -> tstat cs m -> frame_mod m m' rs -> (rs = regL_w sp0 \/ rs = regLe_w sp0) -> tstat cs m'.
    Proof.
      intros cs m m' rs (WF & SPLIT & RNG) ST FM Hrs. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      assert (RS : forall r, In r rs -> (bv_unsigned (fst r) = bv_unsigned sp0 - 128 - 1024 /\ snd r = 1024) \/ (bv_unsigned (fst r) = 0x335ff4 /\ snd r = 4)).
      { intros r Hr. destruct Hrs as [-> | ->]; unfold regL_w, regLe_w, MSTK in Hr; cbn [In] in Hr.
        - destruct Hr as [<-|[]]. left. cbn [fst snd]. rewrite u_small by lia. lia.
        - destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [left; rewrite u_small by lia; lia | right; rewrite u_small by lia; split; reflexivity]. }
      destruct ST as [INV STK TOP CELLS [t [TID Ht]] FR [B' [AUX HB']]]. pose proof FM as [Hout Hg].
      assert (OUT : forall x : word, (bv_unsigned x < bv_unsigned sp0 - 128 - 1024 \/ bv_unsigned sp0 - 128 <= bv_unsigned x) ->
                    ~ (0x335ff4 <= bv_unsigned x < 0x335ff8) -> m' x = m x).
      { intros x H1 H2. apply Hout. apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia. }
      split.
      - eapply mem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - apply (stk_grows sp0 m m'); [exact STK | subst slo; unfold TR_STACK; lia | exact Hg].
      - apply (stk_grows sp0 m m'); [exact TOP | subst spm; lia | exact Hg].
      - eapply cells_ok_frame; [exact WF | exact CELLS | exact FM |].
        eapply Forall_impl; [| exact RNG]. intros [[a w] v] (R1 & R2 & R3) r Hr. cbn [fst snd].
        destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - exists t. split; [|exact Ht]. eapply rdn_frame; [exact FM | exact TID | unorm; lia |]. intros r Hr. unorm.
        destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - eapply (mframe_agree sp0 Hvsp); [exact FR|]. intros x Hx. apply OUT; lia.
      - exists B'. split; [|exact HB']. eapply AUF; [exact AUX | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
        unfold RAUXV_CELL. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    Qed.

    Lemma tstat_heap : forall cs m m' LB s' LB' B',
      cs_ok cs -> tstat cs m -> rheap_pres LB spm m m' -> hs_RHEAP HS s' LB' m' ->
      stk usegs m' slo spm -> mem_inv usegs m' -> hs_rauxv_ok HS m' B' -> bv_unsigned sp0 <= B' -> tstat cs m'.
    Proof.
      intros cs m m' LB s' LB' B' (WF & SPLIT & RNG) [INV STK TOP CELLS [t [TID Ht]] FR AUX] HP HR STK' INV' AUX' HB'. pose proof SPlo. pose proof SPhi.
      split; try assumption.
      - eapply stk_pres_eq; [exact TOP|]. intros a Ha. refine (proj1 (HP a _ _)); [lia | left; subst spm; lia].
      - eapply (cells_ok_heap HS HX sp0); [exact WF | exact SPLIT | exact CELLS | exact HP | exact HR].
      - exists t. split; [|exact Ht]. rewrite (rdn_ext RSEGS 4 m' m); [exact TID | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
        rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
        assert (RC : rclient_addr LB spm (bv_unsigned x)) by (right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia).
        exact (proj1 (HP _ (u64_range x) RC)).
      - eapply (mframe_agree sp0 Hvsp); [exact FR|]. intros x Hx.
        rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
        assert (RC : rclient_addr LB spm (bv_unsigned x)) by (left; subst spm; lia).
        exact (proj1 (HP _ (u64_range x) RC)).
      - exists B'. split; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_client_heap : forall LB m m' (a : Z) n bs,
      rheap_pres LB spm m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> client_cell (a, n, 0) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros LB m m' a n bs HP HD HC. unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in HC.
      rewrite (rdn_ext RSEGS n m' m); [exact HD | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
      rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
      assert (RC : rclient_addr LB spm (bv_unsigned x)).
      { right. left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. (first [clear - HC Hx; lia | lia]). }
      exact (proj1 (HP _ (u64_range x) RC)).
    Qed.

    (* [comment removed for export] *)
    Lemma exit_store_ok : forall m, stk usegs m slo spm -> stk usegs m spm (bv_unsigned sp0 - 48) ->
      store_ok RSEGS m (Z_to_bv 64 (bv_unsigned sp0 - 48 - 144)) 144 = true.
    Proof.
      intros m STK TOP. pose proof SPlo. pose proof SPhi.
      apply store_ok_of_wview; [unorm; lia|]. intros i Hi. unorm. rewrite <- wa_eq.
      destruct (Z_lt_le_dec (bv_unsigned sp0 - 192 + i) (bv_unsigned sp0 - 128)) as [L|L].
      - destruct STK as (_ & _ & S3). refine (proj1 (S3 _ _)). subst slo spm. unfold TR_STACK. lia.
      - destruct TOP as (_ & _ & S3). refine (proj1 (S3 _ _)). subst spm. lia.
    Qed.

    Lemma mframe_main_frame : forall m, mframe sp0 m -> exists slots, main_frame m (Z_to_bv 64 (bv_unsigned sp0 - 128)) slots.
    Proof.
      intros m [F1 F2]. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      destruct (F2 0%nat ltac:(lia)) as [w0 H0]. destruct (F2 1%nat ltac:(lia)) as [w1 H1].
      destruct (F2 2%nat ltac:(lia)) as [w2 H2]. destruct (F2 3%nat ltac:(lia)) as [w3 H3].
      destruct (F2 4%nat ltac:(lia)) as [w4 H4]. destruct (F2 5%nat ltac:(lia)) as [w5 H5].
      destruct (F2 6%nat ltac:(lia)) as [w6 H6]. destruct (F2 7%nat ltac:(lia)) as [w7 H7].
      exists [w0; w1; w2; w3; w4; w5; w6; w7]. split.
      - reflexivity.
      - intros i Hi. rewrite u_small by lia.
        replace (bv_unsigned sp0 - 128 + 8 + 8 * Z.of_nat i) with (bv_unsigned sp0 - 120 + 8 * Z.of_nat i) by lia.
        destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ | | | | | | | | lia]; cbn [nth]; assumption.
      - rewrite u_small by lia. replace (bv_unsigned sp0 - 128 + 72) with (bv_unsigned sp0 - 56) by lia. exact F1.
      - rewrite u_small by lia. lia.
      - rewrite u_small by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma exit_tail : forall regs mem model s LB p (A n : Z) (status : word) cs (P : (word -> option byte) -> Prop) pending,
      cs_ok cs ->
      getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x336098 -> getr regs 8 = status ->
      getr regs 9 = Z_to_bv 64 A ->
      hs_RHEAP HS s LB mem -> In (p, A, n) LB -> hs_KREL HS s model -> m_fs model = fs0 ->
      fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      tstat cs mem -> P mem ->
      (forall m m', P m -> frame_mod m m' (regL_w sp0) -> P m') ->
      (forall m m' LB, P m -> rheap_pres LB spm m m' -> P m') ->
      (forall mem' model' regs', tstat cs mem' -> P mem' -> (exists s' LB', hs_RHEAP HS s' LB' mem') ->
          m_halted model' = None -> m_vm_lazy model' = [] ->
          fd_lookup (m_fds model') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
          getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) -> getr regs' 4 = Z_to_bv 64 0x336098 -> getr regs' 10 = status ->
          exit_pre regs' mem' model' status pending) ->
      realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xe2504) mem (seg_rom RSEGS)) model)
               (t_emit (W 1 pending) (t_exit (bv_and status (Z_to_bv 64 255)) fs0)).
    Proof.
      intros regs mem model s LB p A n status cs P pending CS R2 R4 R8 R9 RH HIn KR FS FD1 TS HP PF PH EXIT.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb. destruct (KRELh s model KR) as [Hh Hlazy].
      assert (Elo : slo = bv_unsigned sp0 - 128 - 65536) by reflexivity. assert (Espm : spm = bv_unsigned sp0 - 128) by reflexivity.
      eapply (seg_I sp0 model Hvsp Hh Hlazy regs mem pp A status _ R2 R4 R8 R9);
        [ eapply stk_stk_ok; [exact (ts_stk _ _ TS) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia]
        | apply mem_inv_ro_none; exact (ts_inv _ _ TS) |].
      intros regs1 mem1 Q2 Q4 Q8 Q1 Q9 Q10 FM1 STK1.
      assert (TS1 : tstat cs mem1) by (eapply tstat_frame; [exact CS | exact TS | exact FM1 | left; reflexivity]).
      assert (RH1 : hs_RHEAP HS s LB mem1) by (eapply (heap_frame HS HH); [exact RH | exact FM1 | apply (regL_w_hi sp0 Hvsp HCE)]).
      assert (HP1 : P mem1) by (eapply PF; [exact HP | exact FM1]).
      destruct (errno_rw mem1 regs1 Q4) as [errv ERR]. destruct (ts_aux _ _ TS1) as [B' [AUX1 HB']].
      change (Z_to_bv 64 0x2b5fdc) with (Z_to_bv 64 RFREE_SYM).
      eapply (free_call HS HH HX regs1 mem1 model s LB p A n slo B' errv 0xe2510 _ Q1);
        [ lia | reflexivity | exact Q4 | exact Q10 | exact RH1 | exact KR | exact HIn
        | exact AUX1 | rewrite Q2, u_small by lia; lia
        | rewrite Q2, u_small by lia; exact (ts_stk _ _ TS1)
        | rewrite Elo; unfold TR_STACK; lia | rewrite Q2, u_small by lia; unfold RFREE_STACK; lia
        | exact ERR | exact (ts_inv _ _ TS1) |].
      intros regs2 mem2 model2 s2 KEPT2 HKR2 MP2 INV2 STK2 ERR2 AUX2 HP2 HRH2.
      rewrite Q2, u_small in STK2, HP2 by lia.
      destruct (KRELh s2 model2 HKR2) as [Hh2 Hlazy2]. destruct (hx_mpres HS HX _ _ MP2) as [FS2 FDS2].
      assert (TS2 : tstat cs mem2) by (eapply tstat_heap; [exact CS | exact TS1 | exact HP2 | exact HRH2 | exact STK2 | exact INV2 | exact AUX2 | exact HB']).
      assert (HPm2 : P mem2) by (eapply PH; [exact HP1 | exact HP2]).
      pose proof (KEPT2 2%bv ltac:(clear; cbn; tauto)) as S2. pose proof (KEPT2 4%bv ltac:(clear; cbn; tauto)) as S4. pose proof (KEPT2 8%bv ltac:(clear; cbn; tauto)) as S8.
      rewrite Q2 in S2. rewrite Q4 in S4. rewrite Q8 in S8.
      destruct (mframe_main_frame mem2 (ts_frame _ _ TS2)) as [slots MF].
      rewrite <- FS, <- FS2.
      apply (main_return_exit model2 regs2 mem2 (Z_to_bv 64 (bv_unsigned sp0 - 128)) status slots pending S2 S8 MF).
      intros regs' T2 T4 T10. apply (EXIT mem2 model2 regs' TS2 HPm2).
      - eexists. eexists. exact HRH2.
      - exact Hh2.
      - exact Hlazy2.
      - rewrite FDS2. exact FD1.
      - rewrite T2. f_equal. rewrite u_small by lia. lia.
      - rewrite T4. exact S4.
      - exact T10.
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma cells_ok_in : forall m cs, cells_ok m cs -> forall c, In c cs -> cell_ok m c.
    Proof. intros m cs H c Hc. unfold cells_ok in H. exact (proj1 (Forall_forall _ _) H c Hc). Qed.
    Lemma cells_ok_app : forall m c1 c2, cells_ok m c1 -> cells_ok m c2 -> cells_ok m (c1 ++ c2).
    Proof. intros. unfold cells_ok in *. apply Forall_app. split; assumption. Qed.
    Lemma cells_ok_incl : forall m c1 c2, cells_ok m c2 -> incl c1 c2 -> cells_ok m c1.
    Proof. intros m c1 c2 H Hi. unfold cells_ok in *. eapply incl_Forall; eassumption. Qed.

    (* [comment removed for export] *)
    Definition cells_keep_a : list (Z * nat * Z) := Eval vm_compute in
      filter (fun c : Z * nat * Z => match c with (a, _, _) => negb ((0x3231e0 <=? a) && (a <? 0x3232c8))%Z end) diag_cells.
    Definition stderr_dirty : list (Z * nat * Z) :=
      [(0x3231e0, 4%nat, 5); (0x3231e8, 8%nat, 0); (0x3231f0, 8%nat, 0); (0x323208, 8%nat, 0x356770); (0x323218, 8%nat, 0x356770); (0x32326c, 4%nat, 0xffffffff)]%Z.
    Definition cells_a : list (Z * nat * Z) := cells_keep_a ++ stderr_dirty.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition dgc_c : Z * nat * Z := (0x33375c, 1%nat, 0)%Z.
    Definition exit_list : list (Z * nat * Z) := Eval vm_compute in (exit_cells ++ atexit_reg_cells ++ [dgc_c]).   (* [comment removed for export] *)
    Lemma exit_list_eq : exit_list = (exit_cells ++ atexit_reg_cells) ++ [dgc_c].
    Proof. vm_compute. reflexivity. Qed.
    Lemma dgc_cells_ok : forall m : word -> option byte, m (Z_to_bv 64 0x33375c) = None -> cells_ok m [dgc_c].
    Proof.
      intros m Hm. unfold cells_ok, dgc_c. apply Forall_cons; [| apply Forall_nil]. unfold cell_ok.
      rewrite (rdn_ext RSEGS 1 m (fun _ => None)); [vm_compute; reflexivity | unorm; lia |].
      intros x Hx. revert Hx. unorm. intros Hx. rewrite <- (Z_to_bv_bv_unsigned x).
      replace (bv_unsigned x) with 0x33375c%Z by lia. exact Hm.
    Qed.
    Definition stdout_cells (k : nat) : list (Z * nat * Z) :=
      [(0x3233c0, 4%nat, 5); (0x3233c8, 8%nat, 0); (0x3233d0, 8%nat, 0); (0x3233e0, 8%nat, 0x356f80);
       (0x3233e8, 8%nat, 0x356b80 + 2 * Z.of_nat k); (0x3233f8, 8%nat, 0x356b80); (0x323408, 8%nat, 0x2b9a78);
       (0x323418, 8%nat, 0x356b80); (0x323420, 8%nat, 1024); (0x323438, 4%nat, 1); (0x32344c, 4%nat, 0xffffffff)]%Z.
    Definition cells_b (k : nat) : list (Z * nat * Z) := exit_list ++ stdout_cells k.

    (* [comment removed for export] *)
    Definition cell_rng_b (c : Z * nat * Z) : bool :=
      match c with (a, w, _) => (0x2c5000 <=? a) && (a + Z.of_nat w <=? 0x358000) && ((a + Z.of_nat w <=? 0x335ff4) || (0x335ff8 <=? a)) end.
    Lemma cell_rng_b_ok : forall c : Z * nat * Z, cell_rng_b c = true ->
      match c with (a, w, _) => 0x2c5000 <= a /\ a + Z.of_nat w <= 0x358000 /\ (a + Z.of_nat w <= 0x335ff4 \/ 0x335ff8 <= a) end.
    Proof.
      intros [[a w] v] H. unfold cell_rng_b in H.
      repeat (apply andb_true_iff in H; let X := fresh "X" in destruct H as [H X]).
      apply orb_leb_or in X. apply Z.leb_le in H. apply Z.leb_le in X0. repeat split; assumption.
    Qed.
    Lemma cells_a_ok : cs_ok cells_a.
    Proof using Htid.   (* [comment removed for export] *)
      unfold cs_ok. split; [vm_compute; reflexivity|]. split.
      - apply (Forall_by_b _ _ cell_side_b cell_side_b_ok). vm_compute. reflexivity.
      - apply (Forall_by_b _ _ cell_rng_b cell_rng_b_ok). vm_compute. reflexivity.
    Qed.

    Lemma cells_b_ok : forall k, (k <= 3)%nat -> cs_ok (cells_b k).
    Proof using Htid.   (* [comment removed for export] *)
      intros k Hk.
      unfold cs_ok. split; [reflexivity|]. split.
      - apply (Forall_by_b _ _ cell_side_b cell_side_b_ok). vm_compute. reflexivity.
      - apply (Forall_by_b _ _ cell_rng_b cell_rng_b_ok). vm_compute. reflexivity.
    Qed.

    Ltac in_list := cbn [In app cells_a cells_keep_a stderr_dirty cells_b exit_list stdout_cells]; repeat (first [ left; reflexivity | right ]).
    (* [comment removed for export] *)
    Ltac by_cell CI :=
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?w = Some ?rhs =>
        let a' := eval vm_compute in a in
        replace (Z_to_bv 64 a) with (Z_to_bv 64 a') by reflexivity;
        first [ refine (CI (a', w, _) _)
              | lazymatch rhs with [Z_to_bv 8 ?v] =>
                  change (Some rhs) with (Some (word_to_le_bytes 1 (Z_to_bv 64 v))); refine (CI (a', w, _) _) end ];
        first [ in_nth | in_list ]   (* [comment removed for export] *)
      end.

    Lemma errno_cell_any : forall m, errno_cell m.
    Proof.
      intros m. destruct (errno_rw_any m) as [e [[_ Hb] _]]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
      exists (le4 e). split; [| reflexivity].
      pose proof (bytes_at_rdn usegs m (0x336098 - 164) (le4 e) 0 4 Hb ltac:(cbn; lia)) as R.
      rewrite rdn_same in R. cbn [firstn skipn le4 word_to_le_bytes] in R |- *. exact R.
    Qed.

    (* [comment removed for export] *)
    Lemma hdr_fail : forall regs mem model s p (A cap : Z) (pc : Z) (msg : list byte),
      getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 0x336098 -> getr regs 8 = Z_to_bv 64 2 ->
      getr regs 9 = Z_to_bv 64 A ->
      statics HS sp0 tidZ B mem -> hs_RHEAP HS s [(p, A, cap)] mem -> hs_KREL HS s model -> m_fs model = fs0 ->
      fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      (forall (K : TSet) (can : Z), hfH regs mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) tidZ can -> K [] ->
         (forall regs' mem', hfPost regs mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) regs' mem' ->
            realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xe2504) mem' (seg_rom RSEGS)) model) K) ->
         realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom RSEGS)) model) (t_emit (W 2 msg) K)) ->
      realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom RSEGS)) model) (t_die msg fs0).
    Proof.
      intros regs mem model s p A cap pc msg R2 R4 R8 R9 ST RH KR FS FD1 FW.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (proj2 (proj2 Hvsp)) as Hal. hcb.
      destruct (hx_statics HS HX _ _ _ RH) as (_ & _ & [can Hcan]).
      unfold t_die. apply (FW _ can).
      { split; [exact R2 | exact R4 | rewrite u_small by lia; rewrite <- Zminus_mod_idemp_l, Hal; reflexivity
              | rewrite u_small by lia; lia | rewrite u_small by lia; lia
              | eapply stk_stk_ok; [exact (st_stk _ _ _ _ _ ST) | unfold HF_FR; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold HF_FR; lia | lia]
              | apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ ST) | exact (st_cells _ _ _ _ _ ST) | exact (st_tid _ _ _ _ _ ST) | subst tidZ; lia | exact Hcan]. }
      { apply t_exit_has_nil. }
      intros regs' mem' [P_sp P_tp P_a0 P_cs P_frame P_flags P_rpos P_rend P_wpos P_wbase P_lock P_stk].
      rewrite u_small in P_frame by lia.
      eapply rz_conseq; [| apply (exit_leaf_eq 2 fs0 ltac:(lia))].
      destruct ST as [INV STK TOP CELLS PF1 TID RELRO FR AUX]. pose proof P_frame as [Hout Hg].
      assert (RS : forall r, In r [(Z_to_bv 64 (bv_unsigned sp0 - 128 - HF_FR), HF_FR); (Z_to_bv 64 0x3231e0, 232)] ->
                 (bv_unsigned (fst r) = bv_unsigned sp0 - 128 - 256 /\ snd r = 256) \/ (bv_unsigned (fst r) = 0x3231e0 /\ snd r = 232)).
      { intros r Hr. unfold HF_FR in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      eapply (exit_tail regs' mem' model s [(p, A, cap)] p A cap (Z_to_bv 64 2) cells_a (fun _ => True) []);
        [ apply cells_a_ok | exact P_sp | exact P_tp | rewrite (P_cs 8%bv ltac:(clear; cbn; tauto)); exact R8
        | rewrite (P_cs 9%bv ltac:(clear; cbn; tauto)); exact R9 | | left; reflexivity | exact KR | exact FS | exact FD1 | | exact I
        | intros; exact I | intros; exact I | ].
      - (* [comment removed for export] *)
        eapply RFR; [exact RH | apply frame_mod_munch; exact P_frame | exact (frame_mod_wmono _ _ _ P_frame) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
        unfold rclient_write_ok. cbn [fst snd]. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2.
        + left. lia.
        + right. left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
      - (* [comment removed for export] *)
        split.
        + eapply mem_inv_frame; [exact INV | exact P_frame |]. apply Forall_forall. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
        + apply (stk_grows sp0 mem mem'); [| subst slo; unfold TR_STACK; lia | exact Hg]. eapply stk_shrink; [exact STK | subst lo slo; unfold TR_STACK; lia].
        + apply (stk_grows sp0 mem mem'); [exact TOP | subst spm; lia | exact Hg].
        + unfold cells_a. apply cells_ok_app.
          * eapply cells_ok_frame; [reflexivity | eapply cells_ok_incl; [exact CELLS | exact (incl_filter (fun c : Z * nat * Z => match c with (a, _, _) => negb ((0x3231e0 <=? a) && (a <? 0x3232c8))%Z end) diag_cells) (* [comment removed for export] *)] | exact P_frame |].
            unfold cells_keep_a. repeat (apply Forall_cons; [intros r Hr; destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; cbn; (first [clear - Hlo Hvsp; lia | lia]) |]). apply Forall_nil.
          * unfold cells_ok, stderr_dirty. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
        + exists tidZ. split; [| exact Htid]. eapply rdn_frame; [exact P_frame | exact TID | unorm; lia |].
          intros r Hr. unorm. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
        + eapply (mframe_agree sp0 Hvsp); [exact FR|]. intros x Hx. apply Hout. apply outside_of_disjoint.
          intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
        + exists B. split; [| exact HB]. eapply AUF; [exact AUX | apply frame_mod_munch; exact P_frame | exact (frame_mod_wmono _ _ _ P_frame) |].
          apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
          unfold RAUXV_CELL. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
      - (* [comment removed for export] *)
        intros memx modelx regsx TSx _ [sx [LBx RHx]] Hhx Hlazyx FD1x X2 X4 X10.
        destruct TSx as [INVx STKx TOPx CELLSx [t [TIDx Ht]] FRx AUXx].
        pose proof (cells_ok_in _ _ CELLSx) as CI.
        destruct (hx_statics HS HX _ _ _ RHx) as (NL & _ & _).
        exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x336098), t, (Z_to_bv 64 0x356770), (Z_to_bv 64 0).
        split; [| split; [exact Hhx | split; [exact Hlazyx | left; split; [reflexivity | exists (Z_to_bv 64 0), (Z_to_bv 64 0)]]]].
        + split; try assumption; rewrite ?u_small by lia; try (lia_guard; first [clear - Hvsp SPlo SPhi Ht; lia | lia]).
          * apply exit_store_ok; assumption.
          * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI.
          * exists false. cbn [atexit_cells]. by_cell CI.   (* [comment removed for export] *)
          * by_cell CI.   (* [comment removed for export] *)
          * apply osl_byte_ex.
          * by_cell CI.   (* [comment removed for export] *)
          * split; [exact NL|]. repeat split; by_cell CI.
          * repeat split; by_cell CI.   (* [comment removed for export] *)
          * repeat split; by_cell CI.
        + repeat split; by_cell CI.
    Qed.

    Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
    Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.

    Lemma zero_lines_S : forall k, zero_lines (S k) = [Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines k.
    Proof. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma after_tr : forall (A cap : Z) (data : list byte) (p : bptr) model regs mem regs2 mem2 model2 (sb1 : Z),
      TRpost HS (Z_to_bv 64 (bv_unsigned sp0 - 128)) A cap data [(p, A, cap)] model regs mem regs2 mem2 model2 ->
      tr_call_regs sp0 regs A (Z.of_nat (length data)) (hdr_cfg data) sb1 ->
      mframe sp0 mem -> stk usegs mem spm (bv_unsigned sp0 - 48) -> m_fs model = fs0 ->
      realizes RSEGS (mkCfg (mkst regs2 (Z_to_bv 64 0xe247c) mem2 (seg_rom RSEGS)) model2)
               (t_emit (W 1 (zero_lines (Nat.pred (hdr_calls data)))) (t_exit (exit_code 0) fs0)).
    Proof.
      intros A cap data p model regs mem regs2 mem2 model2 sb1 TQ TC FR TOP FS.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (hdr_calls_range data) as HCR.
      set (k := Nat.pred (hdr_calls data)) in *. assert (Hk : (k <= 3)%nat) by (subst k; lia).
      destruct TQ as [Q2 Q4 Q10 QCS QAB QSTK QSTKC (s' & LB' & RH' & KR' & HLB) QMP (B' & AUX' & HB') QRO QINV QCELLS QDGC QRELRO QOUT QCAN QTID QERR Qh Qlazy Qfs Qfd1 Qfd2].
      rewrite u_small in QAB, QSTKC, HB' by lia.
      destruct TC as (T1 & T2 & T4 & T8 & T9 & _).
      destruct (main_ret_0 regs2 mem2 (seg_rom RSEGS) Q10) as (regs3 & RUN & E8 & E10 & KEEP).
      lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) (mkst _ ?pc' _ _) =>
        replace (Z_to_bv 64 0xe247c) with pc by (apply bv_eq; reflexivity) end.
      eapply rz_msteps; [exact Qh | exact Qlazy | exact RUN |]. clear RUN.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc' _ _) _) _ =>
        replace pc' with (Z_to_bv 64 0xe2504) by (apply bv_eq; reflexivity) end.
      rewrite <- (exit_code_and_255 0) by lia.
      assert (NE : forall r : reg, In r [2; 4; 9]%bv -> r <> 1%bv /\ r <> 8%bv /\ r <> 10%bv /\ r <> 11%bv).
      { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; repeat split; intros E; apply (f_equal bv_unsigned) in E; discriminate. }
      assert (K2 : getr regs3 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
      { destruct (NE 2%bv ltac:(clear; cbn; tauto)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4). exact Q2. }
      assert (K4 : getr regs3 4 = Z_to_bv 64 0x336098).
      { destruct (NE 4%bv ltac:(clear; cbn; tauto)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4). exact Q4. }
      assert (K9 : getr regs3 9 = Z_to_bv 64 A).
      { destruct (NE 9%bv ltac:(clear; cbn; tauto)) as (N1 & N2 & N3 & N4). rewrite (KEEP _ N1 N2 N3 N4), (QCS 9%bv ltac:(clear; cbn; tauto)). exact T9. }
      eapply (exit_tail regs3 mem2 model2 s' LB' p A cap (Z_to_bv 64 0) (cells_b k)
                (fun m => rdn RSEGS m (Z_to_bv 64 0x356b80) (2 * k) = Some (zero_lines k)) (zero_lines k));
        [ apply cells_b_ok; exact Hk | exact K2 | exact K4 | exact E8 | exact K9 | exact RH' | apply HLB; left; reflexivity | exact KR'
        | rewrite Qfs; exact FS | exact Qfd1 | | exact (so_bytes _ _ QOUT) | | | ].
      - (* [comment removed for export] *)
        split.
        + exact QINV.
        + exact QSTKC.
        + eapply stk_pres_eq; [exact TOP|]. intros a Ha. rewrite wa_eq. apply QAB. rewrite u_small by lia. subst spm. lia.
        + unfold cells_b. apply cells_ok_app; [rewrite exit_list_eq; apply cells_ok_app; [exact QCELLS | apply dgc_cells_ok; exact QDGC] |].
          destruct QOUT. unfold cells_ok, stdout_cells. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
        + destruct QTID as [t [Ht1 Ht2]]. exists t. split; [exact Ht1 | exact Ht2].
        + eapply (mframe_agree sp0 Hvsp); [exact FR|]. intros x Hx. apply QAB. lia.
        + exists B'. split; [exact AUX' | lia].
      - intros m m' HPm FM. eapply rdn_frame; [exact FM | exact HPm | unorm; lia |].
        intros r Hr. unorm. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
      - intros m m' LB HPm HPR. eapply (rdn_client_heap LB m m'); [exact HPR | exact HPm |].
        unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
      - (* [comment removed for export] *)
        intros memx modelx regsx TSx HPx [sx [LBx RHx]] Hhx Hlazyx FD1x X2 X4 X10.
        destruct TSx as [INVx STKx TOPx CELLSx [t [TIDx Ht]] FRx AUXx].
        pose proof (cells_ok_in _ _ CELLSx) as CI.
        destruct (hx_statics HS HX _ _ _ RHx) as (NL & _ & [can Hcan]).
        exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x336098), t, (Z_to_bv 64 0), (Z_to_bv 64 0).
        split; [| split; [exact Hhx | split; [exact Hlazyx |]]].
        + split; try assumption; rewrite ?u_small by lia; try (first [clear - Hvsp SPlo SPhi Ht; lia | lia]).
          * apply exit_store_ok; assumption.
          * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI. * by_cell CI.
          * exists true. cbn [atexit_cells]. repeat split; by_cell CI.   (* [comment removed for export] *)
          * by_cell CI.   (* [comment removed for export] *)
          * apply osl_byte_ex.
          * by_cell CI.   (* [comment removed for export] *)
          * split; [exact NL|]. repeat split; by_cell CI.
          * repeat split; by_cell CI.   (* [comment removed for export] *)
          * repeat split; by_cell CI.
        + destruct k as [|k'].
          * left. split; [reflexivity|]. exists (Z_to_bv 64 0x356b80), (Z_to_bv 64 0). repeat split; by_cell CI.
          * right. exists 0x356b80, (0x356b80 + 2 * Z.of_nat (S k')), (Z_to_bv 64 0x356b80), (Z_to_bv 64 1024), (Z_to_bv 64 0), (Z_to_bv 64 can).
            split; [| exact FD1x]. split; try by_cell CI.
            -- lia.
            -- rewrite zero_lines_length. lia.
            -- rewrite zero_lines_length. unfold rw_bytes_max. lia.
            -- rewrite zero_lines_length. exact HPx.
            -- split; [by_cell CI | exact (proj1 Hcan)].
    Qed.

    (* [comment removed for export] *)
    Lemma buf_bytes_of_rdn : forall m (A : Z) (data : list byte),
      rdn RSEGS m (Z_to_bv 64 A) (length data) = Some data -> 0 <= A -> A + Z.of_nat (length data) < 2 ^ 64 -> buf_bytes m A data.
    Proof.
      intros m A data HD HA HAn i Hi. pose proof (rdn_nth RSEGS m (length data) (Z_to_bv 64 A) data i HD Hi) as H.
      unfold nat_to_word in H. rewrite Z_to_bv_add64 in H. exact H.
    Qed.

    Lemma t_body_split : forall (data : list byte) fs,
      Z.of_nat (length data) < MAX_INPUT ->
      t_body data fs =
        if (length data <? 6)%nat then t_die msg_short fs
        else if (length data <? 6 + Z.to_nat (hdr_cfg data))%nat then t_die msg_overrun fs
        else t_emit (W 1 (zero_lines (hdr_calls data))) (t_exit (exit_code 0) fs).
    Proof.
      intros data fs Hlen. unfold t_body. cbv zeta.
      replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; lia).
      unfold hdr_calls, hdr_cfg, hdr_b. reflexivity.
    Qed.
    (* [comment removed for export] *)
    Theorem ref_open_fail_toolong :
      (4096 <= length path)%nat ->
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
    Proof.
      intros Hlong. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (seg_A sp0 a0s path envv rdraw tid regs0 mem0 brk mbase lim fs0 stdin0 Hva Hve Hvsp Htid ME).
      intros vals R M HL P0 P2 P5 HR HK FM FA.
      pose proof (statics_at_open M FM FA) as ST. pose proof (heap_at_open M FM) as RH. pose proof (above_at_open M FM) as ABOVE.
      destruct (openat_regs' sp0 a0s path envv vals R P2 HR) as (H17 & H10 & H11 & Hfl).
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      destruct (path_facts sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME) as (Sr & Slo & Shi & _).
      pose proof (u64_range pp) as Hpr. fold pp in Sr, Slo, Shi. pose proof (path_len a0s path Hva) as HPl.
      eapply (rz_openat_toolong RSEGS R (Z_to_bv 64 0x2c16a8) M model0 ECALLW ECALL_2c166c is_ecall_ECALLW Hh Hlazy H17 H10 Hfl (firstn 4096 path)).
      - rewrite H11.
        replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
          by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by (first [clear - Hlong Hvsp; lia | lia]); cbn [firstn]; apply app_nil_r).
        apply (rdn_firstn RSEGS M (length path + 1)); [| (first [clear - Hlong; lia | lia])].
        rewrite <- Sr. apply rdn_agree. intros j Hj. apply ABOVE. rewrite u_small by lia. lia.
      - intros Hin. apply (path_nonul a0s path Hva). rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
      - rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
        apply (open_fail ENAMETOOLONG vals R M ltac:(unfold ENAMETOOLONG; lia) scF_ENAMETOOLONG HL P0 P2 HR HK ST RH ABOVE).
    Qed.

    Theorem ref_open_fail_empty :
      path = [] ->
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
    Proof.
      intros Hnil. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (seg_A sp0 a0s path envv rdraw tid regs0 mem0 brk mbase lim fs0 stdin0 Hva Hve Hvsp Htid ME).
      intros vals R M HL P0 P2 P5 HR HK FM FA.
      pose proof (statics_at_open M FM FA) as ST. pose proof (heap_at_open M FM) as RH. pose proof (above_at_open M FM) as ABOVE.
      destruct (openat_regs' sp0 a0s path envv vals R P2 HR) as (H17 & H10 & H11 & Hfl).
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      destruct (path_at_A sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME M FM ltac:(rewrite Hnil; cbn; (first [clear; lia | lia]))) as (PA1 & PA2 & PA3).
      eapply (rz_openat_empty RSEGS R (Z_to_bv 64 0x2c16a8) M model0 ECALLW ECALL_2c166c is_ecall_ECALLW Hh Hlazy H17 H10 Hfl).
      - rewrite Hnil in PA3. split; [cbn; lia|]. split; [intros [] |]. rewrite H11. exact PA3.
      - rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
        apply (open_fail ENOENT vals R M ltac:(unfold ENOENT; lia) scF_ENOENT HL P0 P2 HR HK ST RH ABOVE).
    Qed.

    Theorem ref_open_fail_absent :
      (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false ->
      fs_lookup fs0 path = None ->
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_cannot_open path) fs0).
    Proof.
      intros Hlen Hne Hsl Hnd Hfs. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (seg_A sp0 a0s path envv rdraw tid regs0 mem0 brk mbase lim fs0 stdin0 Hva Hve Hvsp Htid ME).
      intros vals R M HL P0 P2 P5 HR HK FM FA.
      pose proof (statics_at_open M FM FA) as ST. pose proof (heap_at_open M FM) as RH. pose proof (above_at_open M FM) as ABOVE.
      destruct (openat_regs' sp0 a0s path envv vals R P2 HR) as (H17 & H10 & H11 & Hfl).
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      destruct (path_at_A sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME M FM Hlen) as (PA1 & PA2 & PA3).
      eapply (rz_openat_absent RSEGS R (Z_to_bv 64 0x2c16a8) M model0 ECALLW ECALL_2c166c is_ecall_ECALLW Hh Hlazy H17 H10 Hfl path);
        [split; [exact PA1 | split; [exact PA2 | rewrite H11; exact PA3]] | exact Hne | exact Hsl | exact Hnd | exact Hfs |].
      rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
      apply (open_fail ENOENT vals R M ltac:(unfold ENOENT; lia) scF_ENOENT HL P0 P2 HR HK ST RH ABOVE).
    Qed.

    Variable data : list byte.
    Hypothesis Hdata : fs_lookup fs0 path = Some data.
    Hypothesis TR : target_run_stmt HS.

    (* [comment removed for export] *)
    Lemma x_header : forall cap A s p regs mem model,
      XInv HS sp0 pp tidZ data B fs0 cap A s p regs mem model ->
      realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2c16ac) mem (seg_rom RSEGS)) model) (t_body data fs0).
    Proof.
      intros cap A s p regs mem model [XR XLEN XCAP XBR XRH XKR XWR XDATA XST XRA XFS XFD1 XFD2].
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (proj2 (proj2 Hvsp)) as Hal. hcb.
      destruct (KRELh s model XKR) as [Hh Hlazy]. unfold MAX_INPUT in XLEN.
      pose proof XBR as (B1 & B2 & B3 & B4 & B5). clear B2.
      pose proof (hdr_cfg_range data) as Hcr. pose proof (hdr_calls_range data) as HCR.
      rewrite t_body_split by (unfold MAX_INPUT; lia).
      assert (STK : stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK) by (apply (stk_ok_main HS sp0 tidZ B Hvsp); exact XST).
      assert (RO : ro_none mem) by (apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ XST)).
      assert (BB : buf_bytes mem A data) by (apply buf_bytes_of_rdn; [exact XDATA | lia | lia]).
      destruct (Nat.ltb_spec (length data) 6) as [L6|L6].
      - (* [comment removed for export] *)
        eapply (seg_Hs sp0 model Hvsp Hh Hlazy regs mem pp A (Z.of_nat (length data)) cap _ XR ltac:(lia) STK RO XRA).
        intros regs' mem' (Q2 & Q4 & Q8 & Q18 & Q20) Q9 FM STK'.
        eapply (hdr_fail regs' mem' model s p A cap 0xe24c4 msg_short Q2 Q4 Q8 Q9).
        + eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact XST | exact FM | left; reflexivity].
        + eapply (heap_frame HS HH); [exact XRH | exact FM | apply (regL_w_hi sp0 Hvsp HCE)].
        + exact XKR. + exact XFS. + exact XFD1.
        + intros K can HF K0 HK. exact (hdr_short_fwrite model Hh Hlazy XFD2 regs' mem' _ tidZ can K HF K0 HK).
      - destruct (Nat.ltb_spec (length data) (6 + Z.to_nat (hdr_cfg data))) as [LO|LO].
        + (* [comment removed for export] *)
          eapply (seg_Ho sp0 model Hvsp Hh Hlazy regs mem pp A cap data _ XR L6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold MSTK; lia) BB STK RO XRA).
          intros regs' mem' Q2 Q4 Q8 Q20 Q9 FM STK'.
          eapply (hdr_fail regs' mem' model s p A cap 0xe24e0 msg_overrun Q2 Q4 Q8 Q9).
          * eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact XST | exact FM | left; reflexivity].
          * eapply (heap_frame HS HH); [exact XRH | exact FM | apply (regL_w_hi sp0 Hvsp HCE)].
          * exact XKR. * exact XFS. * exact XFD1.
          * intros K can HF K0 HK. exact (hdr_overrun_fwrite model Hh Hlazy XFD2 regs' mem' _ tidZ can K HF K0 HK).
        + (* [comment removed for export] *)
          eapply (seg_Hk sp0 model Hvsp Hh Hlazy regs mem pp A cap data _ XR ltac:(lia) ltac:(lia) ltac:(lia) BB STK RO XRA).
          intros regs' mem' TC FM STK'.
          assert (ST' : statics HS sp0 tidZ B mem') by (eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact XST | exact FM | left; reflexivity]).
          assert (RH' : hs_RHEAP HS s [(p, A, cap)] mem') by (eapply (heap_frame HS HH); [exact XRH | exact FM | apply (regL_w_hi sp0 Hvsp HCE)]).
          destruct (hx_statics HS HX _ _ _ RH') as (_ & _ & HCAN').
          (* [comment removed for export] *)
          destruct (hdr_calls data) as [|calls'] eqn:EC; [lia|].
          rewrite zero_lines_S. eapply rz_conseq; [| apply t_emit_W_app].
          pose proof TC as (T1 & T2 & T4 & T8 & T9 & T10 & T11 & T12 & T13 & T18 & T19 & T20 & T21).
          eapply (TR (Z_to_bv 64 (bv_unsigned sp0 - 128)) A cap data s [(p, A, cap)] model regs' mem').
          * split; try assumption; rewrite ?u_small by (first [clear - Hvsp SPlo SPhi; lia | lia]); try (lia_guard; first [clear - Hvsp SPlo L6 LO SPhi XCAP; lia | lia]).
            all: first
              [ unfold hdr_payload_len; assumption
              | apply errno_cell_any
              | rewrite <- Zminus_mod_idemp_l, Hal; reflexivity
              | exists tidZ; split; [exact (st_tid _ _ _ _ _ ST') | exact Htid]
              | exists B; split; [exact (st_aux _ _ _ _ _ ST') | split; [lia | exact HB64]]
              | eapply stk_stk_ok; [exact (st_stk _ _ _ _ _ ST') | unfold TR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold TR_STACK; lia | lia]
              | eapply stk_shrink; [exact (st_stk _ _ _ _ _ ST') | unfold TR_STACK; lia]
              | apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ ST')
              | exact (st_inv _ _ _ _ _ ST') | exact (st_cells _ _ _ _ _ ST') | exact (st_pf1 _ _ _ _ _ ST')
              | apply prist_relro; exact (st_relro _ _ _ _ _ ST') | apply prist_lib; exact (st_relro _ _ _ _ _ ST')   (* [comment removed for export] *)
              | cbn; left; reflexivity
              | replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia);
                eapply (rdn_block_frame sp0 Hvsp HCE mem mem' _ A cap 0 data FM XBR); [lia | lia | left; reflexivity | rewrite Z.add_0_r; exact XDATA]
              | unfold TR_STACK; lia
              | unfold MAX_INPUT; lia
              | cbn [lb_bytes fold_right blk_size snd length Z.of_nat Pos.of_succ_nat]; lia ].
          * apply t_emit_has_nil.
          * intros regs2 mem2 model2 TQ. replace calls' with (Nat.pred (hdr_calls data)) by (rewrite EC; reflexivity).
            eapply (after_tr A cap data p model regs' mem' regs2 mem2 model2 _ TQ TC (st_frame _ _ _ _ _ ST') (st_top _ _ _ _ _ ST') XFS).
    Qed.

    (* [comment removed for export] *)
    Theorem ref_file :
      (length path <= 4095)%nat -> path <> [] -> path_has_slash path = false -> path_is_dirref path = false ->
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
    Proof.
      intros Hlen Hne Hsl Hnd. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      apply (seg_A sp0 a0s path envv rdraw tid regs0 mem0 brk mbase lim fs0 stdin0 Hva Hve Hvsp Htid ME).
      intros vals R M HL P0 P2 P5 HR HK FM FA.
      pose proof (statics_at_open M FM FA) as ST. pose proof (heap_at_open M FM) as RH. pose proof (above_at_open M FM) as ABOVE.
      destruct (openat_regs' sp0 a0s path envv vals R P2 HR) as (H17 & H10 & H11 & Hfl).
      destruct (path_at_A sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME M FM Hlen) as (PA1 & PA2 & PA3).
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      unfold t_opened.
      eapply (rz_openat_file RSEGS R (Z_to_bv 64 0x2c16a8) M model0 ECALLW ECALL_2c166c is_ecall_ECALLW Hh Hlazy H17 H10 Hfl
                eq_refl path data); [split; [exact PA1 | split; [exact PA2 | rewrite H11; exact PA3]] | exact Hne | exact Hsl | exact Hnd | exact Hdata | |].
      - intros e He. apply (open_fail e vals R M (openat_errnos_range e He) (scF_openat e He) HL P0 P2 HR HK ST RH ABOVE).
      - rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
        change (alloc_fd (m_fds model0)) with (Z_to_bv 64 3).
        set (mo := with_fds _ model0).
        eapply (first_alloc vals R M mo _ HL P0 P2 HR HK ST RH); [apply (hx_krel_fds HS HX); exact KR0 |].
        intros regs' mem' model' A p s RC HBR RH' KR' WR ST' RA' FS' FDS' ABOVE'.
        eapply (loop_sound HS HH HX sp0 pp tidZ path data B fs0 Hvsp Hdata Htid HB HCE (length data) 0 65536 A s p regs' mem' model').
        + lia.
        + eapply (RInv0 mo); try eassumption; reflexivity.
        + intros cap' A' s' p' regs2 mem2 model2 CI. eapply (close_step HS HH HX); [exact CI|]. intros regs3 model3 XI. eapply x_header. exact XI.
        + intros Hbig. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    Qed.
    (* [comment removed for export] *)
    Theorem ref_dir :
      path = dot_path ->
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
    Proof.
      intros Hdot. pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb.
      assert (Hlen : (length path <= 4095)%nat) by (rewrite Hdot; cbn; lia).
      apply (seg_A sp0 a0s path envv rdraw tid regs0 mem0 brk mbase lim fs0 stdin0 Hva Hve Hvsp Htid ME).
      intros vals R M HL P0 P2 P5 HR HK FM FA.
      pose proof (statics_at_open M FM FA) as ST. pose proof (heap_at_open M FM) as RH. pose proof (above_at_open M FM) as ABOVE.
      destruct (openat_regs' sp0 a0s path envv vals R P2 HR) as (H17 & H10 & H11 & Hfl).
      destruct (path_at_A sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME M FM Hlen) as (PA1 & PA2 & PA3).
      destruct (KRELh ps0 model0 KR0) as [Hh Hlazy].
      unfold t_opened_dir.
      eapply (rz_openat_dot RSEGS R (Z_to_bv 64 0x2c16a8) M model0 ECALLW ECALL_2c166c is_ecall_ECALLW Hh Hlazy H17 H10 Hfl eq_refl path);
        [split; [exact PA1 | split; [exact PA2 | rewrite H11; exact PA3]] | rewrite Hdot; reflexivity | |].
      - intros e He. apply (open_fail e vals R M (openat_errnos_range e He) (scF_openat e He) HL P0 P2 HR HK ST RH ABOVE).
      - rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
        change (alloc_fd (m_fds model0)) with (Z_to_bv 64 3).
        set (mo := with_fds _ model0).
        eapply (first_alloc vals R M mo _ HL P0 P2 HR HK ST RH); [apply (hx_krel_fds HS HX); exact KR0 |].
        intros regs2 mem2 model' A p s (R1 & R2 & R4 & R8 & R9 & R10 & R11 & R12 & R17 & R18 & R19 & R20 & R21 & R22) HBR RH' KR' WR ST2 RA2 FS' FDS' ABOVE2.
        destruct (KRELh s model' KR') as [Hh' Hlazy'].
        (* [comment removed for export] *)
        eapply (rz_read_dir RSEGS regs2 (Z_to_bv 64 0x2c16a8) mem2 model' ECALLW (Z_to_bv 64 3));
          [ apply ECALL_2c166c | apply is_ecall_ECALLW | exact Hh' | exact Hlazy' | exact R17 | exact R10
          | rewrite u_small by lia; lia
          | rewrite FDS'; cbv delta [mo]; rewrite with_fds_fds; apply fd_lookup_insert_eq
          | rewrite R11, R12; unorm; unfold TASK_SIZE; lia
          | ].
        rewrite AgentLib.v_addi_lit by lia. change (0x2c16a8 + 4)%Z with 0x2c16ac%Z.
        replace (errno_ret EISDIR) with (Z_to_bv 64 (2 ^ 64 - 21)) by (apply bv_eq; reflexivity).
        eapply (seg_L5c sp0 model' Hvsp Hh' Hlazy' (regupd regs2 10 (Z_to_bv 64 (2 ^ 64 - 21))) mem2 pp A 0 65536);
          [ unfold read_ret_regs; repeat split;
              first [ rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate); assumption
                    | apply getr_same; intros E; apply (f_equal bv_unsigned) in E; discriminate ]
          | apply (stk_ok_main HS sp0 tidZ B Hvsp); exact ST2 | apply mem_inv_ro_none; exact (st_inv _ _ _ _ _ ST2) | exact RA2 |].
        intros regs3 mem3 (Q2 & Q4 & Q8 & Q18 & Q20) FM3 STK3.
        assert (ST3 : statics HS sp0 tidZ B mem3) by (eapply (statics_frame HS HH sp0 tidZ B Hvsp HB); [exact ST2 | exact FM3 | right; reflexivity]).
        assert (RH3 : hs_RHEAP HS s [(p, A, 65536)] mem3) by (eapply (heap_frame HS HH); [exact RH' | exact FM3 | apply (regLe_w_hi sp0 Hvsp HCE)]).
        destruct (hx_statics HS HX _ _ _ RH3) as (_ & _ & [can Hcan]).
        (* [comment removed for export] *)
        assert (ABOVE3 : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> mem3 x = mem0 x).
        { intros x Hx. rewrite <- (ABOVE x Hx), <- (ABOVE2 x Hx).
          apply (proj1 FM3 x). apply outside_of_disjoint. intros r Hr. unfold regLe_w, MSTK in Hr. cbn [In] in Hr.
          destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; (first [clear - Hx Hlo; lia | lia]). }
        destruct (path_facts sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME) as (Sr & Slo & Shi & _ & t8 & Ht8).
        pose proof (u64_range pp) as Hpr. fold pp in Sr, Slo, Shi, Ht8.
        replace fs0 with (m_fs model') by (rewrite FS'; reflexivity).
        assert (FD2' : fd_lookup (m_fds model') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
        { rewrite FDS'. cbv delta [mo]. rewrite with_fds_fds, fd_lookup_insert_neq, model0_fds; [reflexivity | intros E; apply (f_equal bv_unsigned) in E; discriminate]. }
        assert (STK3' : stk_ok RSEGS mem3 (Z_to_bv 64 (bv_unsigned sp0 - 128)) UbReadErr_defs.RE_STK).
        { eapply stk_stk_ok; [exact (st_stk _ _ _ _ _ ST3) | unfold UbReadErr_defs.RE_STK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold UbReadErr_defs.RE_STK; lia | lia]. }
        assert (LP : length path = 1%nat) by (rewrite Hdot; reflexivity).
        assert (Sr3 : rdn RSEGS mem3 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
        { rewrite <- Sr. apply rdn_ext; [rewrite LP; cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. intros x Hx. apply ABOVE3. lia. }
        assert (Ht83 : rdn RSEGS mem3 (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8).
        { rewrite <- Ht8. apply rdn_ext; [unorm; lia|]. intros x Hx. apply ABOVE3. revert Hx. unorm. intros Hx. lia. }
        exact (ref_read_error sp0 [] model' Hvsp Hh' Hlazy' FD2' pp tidZ can regs3 mem3 Q2 Q4 Q18 STK3'
                 (mem_inv_ro_none _ (st_inv _ _ _ _ _ ST3)) (st_cells _ _ _ _ _ ST3) (st_tid _ _ _ _ _ ST3) Htid Hcan Slo
                 path t8 (path_nonul a0s path Hva) ltac:(rewrite LP; cbn; lia) ltac:(rewrite LP; cbn [Z.of_nat Pos.of_succ_nat]; lia) Sr3 Ht83).
    Qed.
  End TwoArgs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section UsageTop.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables av envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
    Hypothesis Hva : valid_argv av.
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
    Hypothesis ME : main_entry sp0 av envv rdraw tid regs0 mem0.
    Hypothesis Hargc : length av <> 2%nat.
    Hypothesis Hfit : entry_stack_fits sp0 av envv.
    Let model0 : Model := MainDefs.model0 tid brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0).

    Theorem ref_usage :
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe22e8) mem0 (seg_rom RSEGS)) model0) (t_die (msg_usage (hd [] av)) fs0).
    Proof.
      pose proof (proj1 Hvsp : 0x7fff80000000 <= bv_unsigned sp0) as Hlo. pose proof (proj1 (proj2 Hvsp) : bv_unsigned sp0 <= 0x800000000000) as Hhi.
      assert (Hh : m_halted model0 = None) by reflexivity. assert (Hlazy : m_vm_lazy model0 = []) by reflexivity.
      apply (seg_U sp0 av envv rdraw tid regs0 mem0 model0 Hva Hve Hvsp Htid ME Hargc Hh Hlazy).
      intros R M Q2 Q4 Q8 Q11 FM (Fra & [s0v Fs0] & F1 & F2 & F3 & F4 & F5 & F6 & F7) Margv.
      assert (RS : forall r, In r (regU_w sp0) -> bv_unsigned (fst r) = bv_unsigned sp0 - 128 /\ snd r = 80).
      { intros r Hr. unfold regU_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. split; reflexivity. }
      assert (ABOVE : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M x = mem0 x).
      { intros x Hx. apply (proj1 FM). apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia. }
      destruct (arg0_facts sp0 av envv rdraw tid regs0 mem0 Hva Hve Hvsp ME) as (Sr & Slo & Shi & Slen & [t8 Ht8] & Sfit & Snul).
      set (pp := cat_argv_ptr sp0 av envv 0) in *. set (a0s := nth 0 av []) in *.
      pose proof (u64_range pp) as Hpr.
      replace (hd [] av) with a0s by (subst a0s; destruct av; reflexivity).
      change fs0 with (m_fs model0).
      refine (ref_usage_cs sp0 model0 Hvsp Hh Hlazy eq_refl pp (bv_unsigned tid) (bv_unsigned (canary_w rdraw)) s0v R M Q2 Q4 Q8 Q11
                _ _ _ _ Htid _ Margv Slo Fra Fs0 F1 F2 F3 F4 F5 F6 F7 a0s t8 Snul Slen _ _ _ _).
      - intros a n Ha Hn. rewrite u_small in Ha, Hn by lia. eapply frame_mod_store_ok; [exact FM|].
        apply (main_entry_store_ok_win sp0 av envv rdraw tid regs0 mem0 ME); unfold UbUsageCS_defs.US_STK in *; rewrite ?stack_max_size_val; lia.
      - intros i Hi. rewrite (proj1 FM (Z_to_bv 64 i)); [apply (main_entry_ro_none sp0 _ _ rdraw tid regs0 mem0 Hvsp ME); exact Hi |].
        apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2, u_small by lia. lia.
      - eapply cells_ok_frame; [apply diag_cells_wf | exact (cells_ok_main_entry sp0 _ _ rdraw tid regs0 mem0 Hvsp ME) | exact FM |].
        eapply Forall_impl; [| apply diag_cells_range]. intros [[a w] v] [R1 R2] r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - eapply rdn_frame; [exact FM | | unorm; lia |].
        + rewrite Z_to_bv_bv_unsigned. apply (UbStartupFacts.main_entry_tid sp0 _ _ rdraw tid Hlo regs0 mem0 ME).
        + intros r Hr. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - split; [| apply u64_range]. eapply rdn_frame; [exact FM | exact (proj1 (canary_ok_main_entry sp0 _ _ rdraw tid regs0 mem0 Hvsp ME)) | unfold CANARY; unorm; lia |].
        intros r Hr. unfold CANARY. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - lia.
      - specialize (Sfit Hfit). lia.
      - rewrite <- Sr. apply rdn_ext; [lia|]. intros x Hx. apply ABOVE. lia.
      - rewrite <- Ht8. apply rdn_ext; [unorm; lia|]. intros x Hx. apply ABOVE. revert Hx. unorm. intros Hx. lia.
    Qed.
  End UsageTop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem main_realizes : main_realizes_stmt HS.
  Proof.
    (* [comment removed for export] *)
    intros sp0 tid brk mbase rnd lim inp regs mem ps0 B Hsp Hfit Hva Hve Hfs Htid HCE ME RH0 KR0 AUX0 [HB HB64] TR.
    assert (EM : model0 tid brk mbase sp0 lim inp
                 = model0 tid brk mbase sp0 lim (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
      by (unfold model0; rewrite <- init_model_canon; reflexivity).
    rewrite EM in KR0 |- *. clear EM.
    set (AMB := amb_of inp) in *. set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
    set (fs0 := in_fs inp) in *. set (stdin0 := in_stdin inp) in *.
    clearbody AMB argv envp fs0 stdin0. clear inp.
    unfold model0.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage sp0 [] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
    - apply (ref_usage sp0 [a0s] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
    - cbn [spec].
      pose proof Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|x l [Hsl Hdd] _]; subst.
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong sp0 a0s path envp rnd tid regs mem brk mbase lim fs0 stdin0 ps0 B Hva Hve Hsp Htid ME RH0 AUX0 HB HCE Hfit KR0 Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply list_byte_eqb_eq in Hemp.
          apply (ref_open_fail_empty sp0 a0s path envp rnd tid regs mem brk mbase lim fs0 stdin0 ps0 B Hva Hve Hsp Htid ME RH0 AUX0 HB HCE Hfit KR0 Hemp).
        * assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply list_byte_eqb_eq in Hdot.
             apply (ref_dir sp0 a0s path envp rnd tid regs mem brk mbase lim fs0 stdin0 ps0 B Hva Hve Hsp Htid ME RH0 AUX0 HB HCE Hfit KR0 Hdot).
          -- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             assert (Hdr : path_is_dirref path = false).
             { unfold path_is_dirref. rewrite (path_eqb_neq _ _ Hnd), Hdd. reflexivity. }
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ apply (ref_file sp0 a0s path envp rnd tid regs mem brk mbase lim fs0 stdin0 ps0 B Hva Hve Hsp Htid ME RH0 AUX0 HB HB64 HCE Hfit KR0 data Hlk TR ltac:(lia) Hne Hsl Hdr).
             ++ apply (ref_open_fail_absent sp0 a0s path envp rnd tid regs mem brk mbase lim fs0 stdin0 ps0 B Hva Hve Hsp Htid ME RH0 AUX0 HB HCE Hfit KR0 ltac:(lia) Hne Hsl Hdr Hlk).
    - apply (ref_usage sp0 (a0s :: path :: x :: l) envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
  Qed.
End Top.
