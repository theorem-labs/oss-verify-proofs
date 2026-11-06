(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX
  Spec RefNodes LibTail LibDiagKn RefMemcpyLib RefMemcpyBase RefMemcpy RefPrintfBufBase
  RefReadErr_defs RefRefused HeapCeil
  RegsEquivM MainEqv MainDefs MainWalk_defs MainMem MainHeap MainSegs.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac in_bv := lazymatch goal with | |- ?a = ?b \/ _ => tryif constr_eq a b then (left; reflexivity) else (right; in_bv) | |- ?a = ?b => constr_eq a b; reflexivity end.

Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition STAGE : Z := 0x80c69.
Definition STAGE_LEN : Z := 65536.

(* [comment removed for export] *)
Lemma diag_cells_no_errno :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => a + Z.of_nat w <= 0x925ac \/ 0x925b0 <= a end) diag_cells.
Proof. unfold diag_cells. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma pf1_cells_no_errno :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => a + Z.of_nat w <= 0x925ac \/ 0x925b0 <= a end) pf1_cells.
Proof. unfold pf1_cells. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
(* [comment removed for export] *)
Lemma diag_cells_no_stage :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => a + Z.of_nat w <= STAGE \/ STAGE + STAGE_LEN <= a end) diag_cells.
Proof. unfold diag_cells, STAGE, STAGE_LEN. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma pf1_cells_no_stage :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => a + Z.of_nat w <= STAGE \/ STAGE + STAGE_LEN <= a end) pf1_cells.
Proof. unfold pf1_cells, STAGE, STAGE_LEN. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

(* [comment removed for export] *)
Definition prist_range (i : Z) : Prop :=
  0x80870 <= i < 0x80a20 \/ 0x90c70 <= i < 0x90c90 \/ 0x90d30 <= i < 0x91af0 \/ 0xb26a0 <= i < 0xb28c0.
Definition prist_none (mem : word -> option byte) : Prop := forall i, prist_range i -> mem (Z_to_bv 64 i) = None.

Section Loop.
  Context {HCEIL : HeapCeil}.
  Variable HS : hsr.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.
  Variables (sp0 pp : word) (tid : Z) (path : list byte) (data : list byte) (B : Z) (fs0 : Fs).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hdata : fs_lookup fs0 path = Some data.
  Hypothesis Htid : 0 < tid < 2 ^ 22.
  Hypothesis HB : bv_unsigned sp0 <= B.
  Hypothesis HCE : hceil + 8388608 <= bv_unsigned sp0.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let spm : Z := bv_unsigned sp0 - 128.
  Let lo : Z := bv_unsigned sp0 - 8388608.

  (* [comment removed for export] *)
  Let KRELh : forall s mo, hs_KREL HS s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. destruct HH as (_ & K & _). exact K. Qed.
  Let AOK : alloc_ok_of_live HS.
  Proof. destruct HH as (_ & _ & _ & A & _). exact A. Qed.
  Let RFR : RHEAP_frame HS.
  Proof. destruct HH as (_ & _ & _ & _ & A & _). exact A. Qed.
  Let RBR : RHEAP_block_range HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let RBD : RHEAP_blocks_disjoint HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let RND : RHEAP_blocks_nodup HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let AUF : rauxv_frame HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let LBR : lb_remove_laws HS.
  Proof. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.

  (* [comment removed for export] *)
  Definition mframe (M : word -> option byte) : Prop :=
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67178))
    /\ forall i, (i < 8)%nat -> exists w : word,
         rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 120 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 w).

  (* [comment removed for export] *)
  Record statics (mem : word -> option byte) : Prop := ST {
    st_inv   : mem_inv rsegs mem;
    st_stk   : stk rsegs mem lo spm;
    st_top   : stk rsegs mem spm (bv_unsigned sp0 - 48);      (* [comment removed for export] *)
    st_cells : cells_ok mem diag_cells;
    st_pf1   : cells_ok mem pf1_cells;
    st_tid   : rdn RSEGS mem (Z_to_bv 64 0x925a8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    st_relro : relro_none mem;
    st_frame : mframe mem;
    st_aux   : hs_rauxv_ok HS mem B;
    st_prist : prist_none mem }.

  (* [comment removed for export] *)
  Record RInv (len cap A : Z) (s : PState) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) : Prop := RI {
    ri_regs : read_call_regs sp0 regs pp A len cap (Z.min (cap - len) 65536);
    ri_len  : 0 <= len < cap /\ len <= Z.of_nat (length data);
    ri_cap  : 65536 <= cap <= 67108864;
    ri_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k;
    ri_blk  : rblock_range A cap;
    ri_heap : hs_RHEAP HS s [(p, A, cap)] mem;
    ri_krel : hs_KREL HS s model;
    ri_wr   : wr_at rsegs mem A cap;
    ri_data : rdn RSEGS mem (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) data);
    ri_st   : statics mem;
    ri_ra   : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ad50));
    ri_fs   : m_fs model = fs0;
    ri_fd3  : fd_lookup (m_fds model) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 len));
    ri_fd1  : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    ri_fd2  : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record MInv (len n cap A : Z) (s : PState) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) : Prop := MI {
    mi_regs : m_regs sp0 regs pp A len cap n;
    mi_len  : 0 <= len /\ 1 <= n /\ len + n <= cap /\ len + n <= Z.of_nat (length data);
    mi_cap  : 65536 <= cap <= 67108864;
    mi_pow  : exists k, 0 <= k /\ cap = 65536 * 2 ^ k;
    mi_blk  : rblock_range A cap;
    mi_heap : hs_RHEAP HS s [(p, A, cap)] mem;
    mi_krel : hs_KREL HS s model;
    mi_wr   : wr_at rsegs mem A cap;
    mi_data : rdn RSEGS mem (Z_to_bv 64 A) (Z.to_nat (len + n)) = Some (firstn (Z.to_nat (len + n)) data);
    mi_st   : statics mem;
    mi_fs   : m_fs model = fs0;
    mi_fd3  : fd_lookup (m_fds model) (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 (len + n)));
    mi_fd1  : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    mi_fd2  : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record CInv (cap A : Z) (s : PState) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) : Prop := CI {
    ci_r1 : getr regs 1 = Z_to_bv 64 0x78ef8;  ci_r2 : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144);
    ci_r4 : getr regs 4 = Z_to_bv 64 0x92650;  ci_r8 : getr regs 8 = Z_to_bv 64 2;  ci_r9 : getr regs 9 = Z_to_bv 64 A;
    ci_r10 : getr regs 10 = Z_to_bv 64 3;  ci_r17 : getr regs 17 = Z_to_bv 64 57;  ci_r18 : getr regs 18 = pp;
    ci_r19 : getr regs 19 = Z_to_bv 64 (Z.of_nat (length data));  ci_r20 : getr regs 20 = Z_to_bv 64 3;  ci_r21 : getr regs 21 = Z_to_bv 64 cap;
    ci_cap  : Z.of_nat (length data) <= cap /\ 65536 <= cap <= 67108864;
    ci_lt   : Z.of_nat (length data) < MAX_INPUT;
    ci_blk  : rblock_range A cap;
    ci_heap : hs_RHEAP HS s [(p, A, cap)] mem;
    ci_krel : hs_KREL HS s model;
    ci_wr   : wr_at rsegs mem A cap;
    ci_data : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    ci_st   : statics mem;
    ci_ra   : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ad64));
    ci_fs   : m_fs model = fs0;
    ci_fd3  : exists e3, fd_lookup (m_fds model) (Z_to_bv 64 3) = Some e3;
    ci_fd1  : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    ci_fd2  : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record XInv (cap A : Z) (s : PState) (p : bptr) (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) : Prop := XI {
    xi_regs : close_ret_regs sp0 regs pp A (Z.of_nat (length data)) cap;
    xi_len  : Z.of_nat (length data) < MAX_INPUT;
    xi_cap  : Z.of_nat (length data) <= cap /\ 65536 <= cap <= 67108864;
    xi_blk  : rblock_range A cap;
    xi_heap : hs_RHEAP HS s [(p, A, cap)] mem;
    xi_krel : hs_KREL HS s model;
    xi_wr   : wr_at rsegs mem A cap;
    xi_data : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    xi_st   : statics mem;
    xi_ra   : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ad64));
    xi_fs   : m_fs model = fs0;
    xi_fd1  : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    xi_fd2  : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma seg_rom_high : forall x : word, 0xb4000 <= bv_unsigned x -> seg_rom RSEGS x = None.
  Proof.
    intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
    change Plain.M.loaded_segments with rsegs. rewrite find_segment_rsegs.
    destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x2a000); cbn [andb]; try lia;
    destruct (Z.leb_spec 0x2a000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x7a000); cbn [andb]; try lia;
    destruct (Z.leb_spec 0x7a000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x80000); cbn [andb]; try lia;
    destruct (Z.leb_spec 0x80000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0xb4000); cbn [andb]; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma stk_grows : forall m m' l h, stk rsegs m l h -> 0xb4000 <= l -> mem_grows m m' -> stk rsegs m' l h.
  Proof.
    intros m m' l h (S1 & S2 & S3) Hl Hg. split; [exact S1|]. split; [exact S2|].
    intros x Hx. destruct (S3 x Hx) as [Hw [b Hb]].
    assert (E0 : exists b0, m (wa x) = Some b0).
    { unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E; [exists b0; reflexivity|].
      rewrite seg_rom_same in Hb. change rsegs with RSEGS in Hb.
      rewrite seg_rom_high in Hb; [discriminate|]. rewrite wa_eq, u_small by lia. lia. }
    destruct E0 as [b0 E0].
    assert (E1 : exists b1, m' (wa x) = Some b1).
    { destruct (m' (wa x)) as [b1|] eqn:E; [exists b1; reflexivity|]. exfalso. apply (Hg (wa x)); congruence. }
    destruct E1 as [b1 E1]. split.
    - unfold wview. rewrite E1. discriminate.
    - exists b1. unfold mrd. rewrite E1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma stk_pres_eq : forall m m' l h, stk rsegs m l h -> (forall a, l <= a < h -> m' (wa a) = m (wa a)) -> stk rsegs m' l h.
  Proof.
    intros m m' l h (S1 & S2 & S3) Hag. split; [exact S1|]. split; [exact S2|].
    intros x Hx. destruct (S3 x Hx) as [Hw Hb]. unfold wview, mrd in *. rewrite (Hag x Hx). split; assumption.
  Qed.

  Lemma mframe_agree : forall m m',
    mframe m -> (forall x : word, bv_unsigned sp0 - 120 <= bv_unsigned x < bv_unsigned sp0 - 48 -> m' x = m x) -> mframe m'.
  Proof.
    intros m m' [F1 F2] Hag. pose proof SPlo. pose proof SPhi. split.
    - rewrite (rdn_ext RSEGS 8 m' m); [exact F1 | unorm; lia |]. intros x Hx. apply Hag. revert Hx. unorm. intros Hx. lia.
    - intros i Hi. destruct (F2 i Hi) as [w Hw]. exists w.
      rewrite (rdn_ext RSEGS 8 m' m); [exact Hw | unorm; lia |]. intros x Hx. apply Hag. revert Hx. unorm. intros Hx. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma statics_frame : forall m m' rs,
    statics m -> frame_mod m m' rs ->
    (rs = regL_w sp0 \/ rs = regLe_w sp0) -> statics m'.
  Proof.
    intros m m' rs ST FM Hrs. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (RS : forall r, In r rs -> (bv_unsigned (fst r) = bv_unsigned sp0 - 128 - 1024 /\ snd r = 1024) \/ (bv_unsigned (fst r) = 0x925ac /\ snd r = 4)).
    { intros r Hr. destruct Hrs as [-> | ->]; unfold regL_w, regLe_w, MSTK in Hr; cbn [In] in Hr.
      - destruct Hr as [<-|[]]. left. cbn [fst snd]. rewrite u_small by lia. lia.
      - destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [left; rewrite u_small by lia; lia | right; rewrite u_small by lia; split; reflexivity]. }
    destruct ST as [INV STK TOP CELLS PF1 TID RELRO FR AUX PRI]. destruct FM as [Hout Hg].
    assert (FM : frame_mod m m' rs) by (split; assumption).
    assert (OUT : forall x : word, (bv_unsigned x < bv_unsigned sp0 - 128 - 1024 \/ bv_unsigned sp0 - 128 <= bv_unsigned x) ->
                  ~ (0x925ac <= bv_unsigned x < 0x925b0) -> m' x = m x).
    { intros x H1 H2. apply Hout. apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia. }
    split.
    - eapply mem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    - eapply stk_grows; [exact STK | subst lo; lia | exact Hg].
    - eapply stk_grows; [exact TOP | lia | exact Hg].
    - eapply cells_ok_frame; [apply diag_cells_wf | exact CELLS | exact FM |].
      pose proof diag_cells_no_errno as N1.
      eapply Forall_impl; [| apply (Forall_and diag_cells_range N1)].
      intros [[a w] v] [[R1 R2] R3] r Hr. cbn [fst snd].
      destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    - eapply cells_ok_frame; [apply pf1_cells_wf | exact PF1 | exact FM |].
      pose proof pf1_cells_no_errno as N1.
      eapply Forall_impl; [| apply (Forall_and pf1_cells_range N1)].
      intros [[a w] v] [[R1 R2] R3] r Hr. cbn [fst snd].
      destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    - eapply rdn_frame; [exact FM | exact TID | unorm; lia |]. intros r Hr. unorm.
      destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    - intros i Hi. rewrite OUT; [apply RELRO; exact Hi | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - eapply mframe_agree; [exact FR|]. intros x Hx. apply OUT; lia.
    - eapply AUF; [exact AUX | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
      apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
      unfold RAUXV_CELL. destruct (RS r Hr) as [[E1 E2]|[E1 E2]]; rewrite E1, E2; lia.
    - intros i Hi. unfold prist_range in Hi. rewrite OUT; [apply PRI; unfold prist_range; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition client_cell (c : Z * nat * Z) : Prop :=
    match c with (a, w, _) =>
      0x7a000 <= a /\ a + Z.of_nat w <= 0xb4000
      /\ (a + Z.of_nat w <= RLIBC \/ RCTX + 928 <= a) /\ (a + Z.of_nat w <= RERRNO \/ RERRNO + 4 <= a)
      /\ (a + Z.of_nat w <= RSSP_GUARD \/ RSSP_GUARD + 8 <= a) /\ (a + Z.of_nat w <= RGOT_SSP \/ RGOT_SSP + 8 <= a)
      /\ (a + Z.of_nat w <= RVMLOCK \/ RVMLOCK + 4 <= a) end.
  Definition static_cell (c : Z * nat * Z) : Prop :=
    c = (0x7f808, 8%nat, 0xb2690) \/ c = (0xb28e3, 1%nat, 0).

  Lemma diag_cells_split : Forall (fun c => client_cell c \/ static_cell c) diag_cells.
  Proof.
    unfold diag_cells, client_cell, static_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK.
    repeat (apply Forall_cons; [cbn; first [left; lia | right; tauto] |]). apply Forall_nil.
  Qed.
  Lemma pf1_cells_split : Forall (fun c => client_cell c \/ static_cell c) pf1_cells.
  Proof.
    unfold pf1_cells, client_cell, static_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK.
    repeat (apply Forall_cons; [cbn; first [left; lia | right; tauto] |]). apply Forall_nil.
  Qed.

  Lemma cells_ok_heap : forall cs m m' LB s' LB',
    forallb cell_wf_b cs = true -> Forall (fun c => client_cell c \/ static_cell c) cs ->
    cells_ok m cs -> rheap_pres LB spm m m' -> hs_RHEAP HS s' LB' m' -> cells_ok m' cs.
  Proof.
    intros cs m m' LB s' LB' Hwf Hsplit Hc HP HR.
    destruct (hx_statics HS HX s' LB' m' HR) as (S1 & S2 & S3).
    unfold cells_ok in *. induction cs as [|[[a w] v] cs IH]; [constructor|].
    cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
    inversion Hsplit as [|x l Hx Hl]; subst. inversion Hc as [|x' l' Hc1 Hcl]; subst.
    constructor; [|apply IH; assumption].
    destruct Hx as [CL | ST].
    - eapply cell_ok_agree; [exact H1 | | exact Hc1]. intros i Hi.
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      rewrite <- wa_eq. unfold client_cell in CL.
      assert (RC : rclient_addr LB spm i) by (right; left; unfold ralloc_static; lia).
      exact (proj1 (HP i ltac:(lia) RC)).
    - destruct ST as [E|E]; injection E as -> -> ->; unfold cell_ok; assumption.
  Qed.

  Lemma statics_heap : forall m m' LB s' LB',
    statics m -> rheap_pres LB spm m m' -> hs_RHEAP HS s' LB' m' ->
    stk rsegs m' lo spm -> mem_inv rsegs m' -> hs_rauxv_ok HS m' B -> statics m'.
  Proof.
    intros m m' LB s' LB' [INV STK TOP CELLS PF1 TID RELRO FR AUX PRI] HP HR STK' INV' AUX'. pose proof SPlo. pose proof SPhi.
    split; try assumption.
    - eapply stk_pres_eq; [exact TOP|]. intros a Ha. refine (proj1 (HP a _ _)); [lia | left; lia].
    - eapply cells_ok_heap; [apply diag_cells_wf | apply diag_cells_split | exact CELLS | exact HP | exact HR].
    - eapply cells_ok_heap; [apply pf1_cells_wf | apply pf1_cells_split | exact PF1 | exact HP | exact HR].
    - rewrite (rdn_ext RSEGS 4 m' m); [exact TID | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
      rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
      assert (RC : rclient_addr LB spm (bv_unsigned x)) by (right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia).
      exact (proj1 (HP _ (u64_range x) RC)).
    - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq.
      assert (RC : rclient_addr LB spm i) by (right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia).
      assert (Hi64 : 0 <= i < 2 ^ 64) by lia. exact (proj1 (HP i Hi64 RC)).
    - eapply mframe_agree; [exact FR|]. intros x Hx.
      rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
      assert (RC : rclient_addr LB spm (bv_unsigned x)) by (left; subst spm; lia).
      exact (proj1 (HP _ (u64_range x) RC)).
    - intros i Hi. unfold prist_range in Hi. rewrite <- (PRI i ltac:(unfold prist_range; lia)). rewrite <- wa_eq.
      assert (RC : rclient_addr LB spm i) by (right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia).
      exact (proj1 (HP i ltac:(lia) RC)).
  Qed.

  Lemma statics_wblock : forall m A n k bs,
    statics m -> rblock_range A n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
    statics (wbytes m (Z_to_bv 64 (A + k)) bs).
  Proof.
    intros m A n k bs [INV STK TOP CELLS PF1 TID RELRO FR AUX PRI] HBR Hk Hl. pose proof SPlo. pose proof SPhi.
    pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
    split.
    - eapply mem_inv_wbytes_block; eassumption.
    - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact STK | lia | lia].
    - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact TOP | lia | lia].
    - eapply cells_ok_wbytes_out; [apply diag_cells_wf | exact CELLS | unorm; lia |].
      eapply Forall_cells_weaken; [|apply diag_cells_range]. intros a w v [Q1 Q2]. unorm. lia.
    - eapply cells_ok_wbytes_out; [apply pf1_cells_wf | exact PF1 | unorm; lia |].
      eapply Forall_cells_weaken; [|apply pf1_cells_range]. intros a w v [Q1 Q2]. unorm. lia.
    - eapply rdn_wbytes_out; [exact TID | unorm; lia | unorm; lia | unorm; lia].
    - intros i Hi. rewrite wbytes_outside; [apply RELRO; exact Hi | unfold in_rng; unorm; lia | unorm; lia].
    - eapply mframe_agree; [exact FR|]. intros x Hx. apply wbytes_outside; unfold in_rng; unorm; lia.
    - eapply AUF; [exact AUX | | |].
      + rewrite wbytes_eq, <- wa_eq. apply (munch_write [(A + k, A + k + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
      + rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
      + constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia.
    - intros i Hi. unfold prist_range in Hi. rewrite wbytes_outside; [apply PRI; unfold prist_range; lia | unfold in_rng; unorm; lia | unorm; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma statics_wstage : forall m bs,
    statics m -> Z.of_nat (length bs) <= STAGE_LEN -> statics (wbytes m (Z_to_bv 64 STAGE) bs).
  Proof.
    intros m bs [INV STK TOP CELLS PF1 TID RELRO FR AUX PRI] Hl. pose proof SPlo. pose proof SPhi. unfold STAGE, STAGE_LEN in *.
    split.
    - intros a b Hab. pose proof (u64_range a) as Ha.
      destruct (Z_lt_le_dec (bv_unsigned a) 0x80c69) as [Hlt|Hge].
      + rewrite wbytes_below in Hab by (rewrite ?u_small by lia; lia). exact (INV a b Hab).
      + destruct (Z_lt_le_dec (bv_unsigned a) (0x80c69 + Z.of_nat (length bs))) as [Hin|Hout].
        * apply ro_addr_false. lia.
        * rewrite wbytes_above in Hab by (rewrite u_small by lia; lia). exact (INV a b Hab).
    - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact STK | lia | lia].
    - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact TOP | lia | lia].
    - eapply cells_ok_wbytes_out; [apply diag_cells_wf | exact CELLS | unorm; lia |].
      eapply Forall_cells_weaken; [|apply diag_cells_no_stage]. intros a w v Q. unfold STAGE, STAGE_LEN in Q. unorm. lia.
    - eapply cells_ok_wbytes_out; [apply pf1_cells_wf | exact PF1 | unorm; lia |].
      eapply Forall_cells_weaken; [|apply pf1_cells_no_stage]. intros a w v Q. unfold STAGE, STAGE_LEN in Q. unorm. lia.
    - eapply rdn_wbytes_out; [exact TID | unorm; lia | unorm; lia | unorm; lia].
    - intros i Hi. rewrite wbytes_outside; [apply RELRO; exact Hi | unfold in_rng; unorm; lia | unorm; lia].
    - eapply mframe_agree; [exact FR|]. intros x Hx. apply wbytes_outside; unfold in_rng; unorm; lia.
    - eapply AUF; [exact AUX | | |].
      + rewrite wbytes_eq, <- wa_eq. apply (munch_write [(0x80c69, 0x80c69 + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
      + rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
      + constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia.
    - intros i Hi. unfold prist_range in Hi. rewrite wbytes_outside; [apply PRI; unfold prist_range; lia | unfold in_rng; unorm; lia | unorm; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma heap_wblock : forall m s p A n k bs,
    hs_RHEAP HS s [(p, A, n)] m -> rblock_range A n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
    hs_RHEAP HS s [(p, A, n)] (wbytes m (Z_to_bv 64 (A + k)) bs).
  Proof.
    intros m s p A n k bs HR HBR Hk Hl. pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
    eapply RFR; [exact HR | | |].
    - rewrite wbytes_eq, <- wa_eq. apply (munch_write [(A + k, A + k + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
    - rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
    - constructor; [|constructor]. right. right. exists (p, A, n). split; [left; reflexivity|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma heap_wstage : forall m s LB bs,
    hs_RHEAP HS s LB m -> Z.of_nat (length bs) <= STAGE_LEN -> hs_RHEAP HS s LB (wbytes m (Z_to_bv 64 STAGE) bs).
  Proof.
    intros m s LB bs HR Hl. unfold STAGE, STAGE_LEN in *. hcb.
    eapply RFR; [exact HR | | |].
    - rewrite wbytes_eq, <- wa_eq. apply (munch_write [(0x80c69, 0x80c69 + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
    - rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
    - constructor; [|constructor]. right. left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
  Qed.

  Lemma wr_at_wbytes : forall m A n (a : word) bs, wr_at rsegs m A n -> wr_at rsegs (wbytes m a bs) A n.
  Proof. intros. eapply wr_at_transport; [eassumption|]. rewrite wbytes_eq. apply wmono_write. apply wmono_refl. Qed.

  (* [comment removed for export] *)
  Lemma heap_frame : forall m m' s LB rs,
    hs_RHEAP HS s LB m -> frame_mod m m' rs ->
    (forall r, In r rs -> hceil <= bv_unsigned (fst r) \/ (bv_unsigned (fst r) = RERRNO /\ snd r = 4)) ->
    hs_RHEAP HS s LB m'.
  Proof.
    intros m m' s LB rs HR FM Hrs.
    eapply RFR; [exact HR | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
    apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
    unfold rclient_write_ok. cbn [fst snd]. destruct (Hrs r Hr) as [H1 | [H1 H2]]; [left; exact H1 |].
    right. left. rewrite H1, H2. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
  Qed.

  Lemma regL_w_hi : forall r, In r (regL_w sp0) -> hceil <= bv_unsigned (fst r) \/ (bv_unsigned (fst r) = RERRNO /\ snd r = 4).
  Proof.
    intros r Hr. pose proof SPlo. pose proof SPhi. hcb. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
    left. cbn [fst]. rewrite u_small by lia. lia.
  Qed.
  Lemma regLe_w_hi : forall r, In r (regLe_w sp0) -> hceil <= bv_unsigned (fst r) \/ (bv_unsigned (fst r) = RERRNO /\ snd r = 4).
  Proof.
    intros r Hr. pose proof SPlo. pose proof SPhi. hcb. unfold regLe_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]].
    - left. cbn [fst]. rewrite u_small by lia. lia.
    - right. cbn [fst snd]. unfold RERRNO. rewrite u_small by lia. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_block_frame : forall m m' rs (A : Z) n k bs,
    frame_mod m m' rs -> rblock_range A n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
    (rs = regL_w sp0 \/ rs = regLe_w sp0) ->
    rdn RSEGS m (Z_to_bv 64 (A + k)) (length bs) = Some bs -> rdn RSEGS m' (Z_to_bv 64 (A + k)) (length bs) = Some bs.
  Proof.
    intros m m' rs A n k bs FM HBR Hk Hl Hrs HD. pose proof SPlo. pose proof SPhi.
    pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
    eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm.
    destruct Hrs as [-> | ->]; unfold regL_w, regLe_w, MSTK in Hr; cbn [In] in Hr.
    - destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
    - destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_stage_frame : forall m m' bs,
    frame_mod m m' (regL_w sp0) -> Z.of_nat (length bs) <= STAGE_LEN ->
    rdn RSEGS m (Z_to_bv 64 STAGE) (length bs) = Some bs -> rdn RSEGS m' (Z_to_bv 64 STAGE) (length bs) = Some bs.
  Proof.
    intros m m' bs FM Hl HD. pose proof SPlo. pose proof SPhi. unfold STAGE, STAGE_LEN in *.
    eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm.
    unfold regL_w, MSTK in Hr; cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
  Qed.

  Lemma Z_to_bv_add64 : forall a b : Z, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
  Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. bv_wrap_simplify_solve. Qed.

  Lemma ECALL_7611c : fetch_word RSEGS (Z_to_bv 64 0x75f78) = Some ECALLW.
  Proof. vm_compute. reflexivity. Qed.

  Lemma firstn_app_read : forall (n : nat) (l : list byte) bs,
    bs = firstn (length bs) (skipn n l) -> firstn n l ++ bs = firstn (n + length bs) l.
  Proof. intros n l bs E. rewrite (FileSim.firstn_add l n (length bs)), <- E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma file_read_next : forall len cnt,
    0 <= len -> 0 <= cnt < 2 ^ 64 -> len < 2 ^ 64 ->
    file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)
    /\ length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) = Nat.min (Z.to_nat cnt) (length data - Z.to_nat len).
  Proof.
    intros len cnt Hl Hc Hl2. split.
    - rewrite file_read_unguarded. unfold word_to_nat. rewrite !u_small by lia. reflexivity.
    - rewrite file_read_length_eq. unfold word_to_nat. rewrite !u_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma errno_rw : forall m regs, getr regs 4 = Z_to_bv 64 0x92650 ->
    exists e : word, rw_cells rsegs m (errno_addr (getr regs 4)) [C4 e].
  Proof. intros m regs H4. unfold errno_addr. rewrite H4, u_small by lia. apply errno_rw_any. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rdn_rheap_pres : forall LB m m' (a : Z) n bs,
    rheap_pres LB spm m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs ->
    0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> in_block LB i) ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros LB m m' a n bs HP HD Ha Hn HIN.
    rewrite (rdn_ext RSEGS n m' m); [exact HD | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
    rewrite <- (Z_to_bv_bv_unsigned x). rewrite <- wa_eq.
    exact (proj1 (HP _ (u64_range x) (or_intror (or_intror (HIN _ Hx))))).
  Qed.

  Lemma wr_at_rheap_pres : forall LB m m' (A n : Z),
    rheap_pres LB spm m m' -> wr_at rsegs m A n -> (forall i, A <= i < A + n -> in_block LB i) -> wr_at rsegs m' A n.
  Proof.
    intros LB m m' A n HP (W1 & W2 & W3) HIN. split; [exact W1|]. split; [exact W2|].
    intros i Hi. assert (H1 : 0 <= A + i < 2 ^ 64) by lia. assert (H2 : A <= A + i < A + n) by lia.
    apply (proj2 (HP (A + i) H1 (or_intror (or_intror (HIN _ H2))))). apply W3. exact Hi.
  Qed.

  Lemma heap_wblock_in : forall m s LB p A n k bs,
    hs_RHEAP HS s LB m -> In (p, A, n) LB -> rblock_range A n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
    hs_RHEAP HS s LB (wbytes m (Z_to_bv 64 (A + k)) bs).
  Proof.
    intros m s LB p A n k bs HR HIn HBR Hk Hl. pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
    eapply RFR; [exact HR | | |].
    - rewrite wbytes_eq, <- wa_eq. apply (munch_write [(A + k, A + k + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
    - rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
    - constructor; [|constructor]. right. right. exists (p, A, n). split; [exact HIn|]. cbn. lia.
  Qed.

  Lemma wr_at_of_CB : forall m A n junk, rw_cells rsegs m A [CB (Z.to_nat n) junk] -> 0 <= n -> wr_at rsegs m A n.
  Proof.
    intros m A n junk H Hn. destruct (u8arr_of_rw_cells rsegs m A _ junk H) as [Hb Hw].
    destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hlen _]. rewrite Hlen, Z2Nat.id in Hw by lia. exact Hw.
  Qed.

  Lemma in_block_1 : forall p A n LB i, A <= i < A + n -> in_block ((p, A, n) :: LB) i.
  Proof. intros p A n LB i Hi. exists (p, A, n). split; [left; reflexivity | cbn; lia]. Qed.

  (* [comment removed for export] *)
  Lemma stk_ok_main : forall m, statics m -> stk_ok RSEGS m (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK.
  Proof.
    intros m ST. pose proof SPlo. pose proof SPhi.
    eapply stk_stk_ok; [exact (st_stk m ST) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma read_step : forall regs mem model s p (A len cap : Z) K,
    RInv len cap A s p regs mem model ->
    (* [comment removed for export] *)
    (forall regs' mem' model' n, MInv len n cap A s p regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2ace8) mem' (seg_rom RSEGS)) model') K) ->
    (* [comment removed for export] *)
    (len = Z.of_nat (length data) -> forall regs' mem' model', CInv cap A s p regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75f78) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x75f78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s p A len cap K [RC [Hlen Hld] Hcap HPOW HBR HRH HKR HWR HDATA ST Hra Hfs Hfd3 Hfd1 Hfd2] KMORE KEOF.
    pose proof Htid as HtidPin.   (* [comment removed for export] *)
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb.
    assert (Elo : lo = bv_unsigned sp0 - 8388608) by reflexivity. assert (Espm : spm = bv_unsigned sp0 - 128) by reflexivity.
    set (cnt := Z.min (cap - len) 65536) in RC.
    destruct RC as (R1 & R2 & R4 & R8 & R9 & R10 & R11 & R12 & R17 & R18 & R19 & R20 & R21 & R22).
    pose proof HBR as (B1 & B2 & B3 & B4 & B5). clear B2.
    destruct (KRELh s model HKR) as [Hh Hlazy].
    assert (Hc1 : 1 <= cnt <= 65536) by lia. assert (Hc2 : len + cnt <= cap) by lia.
    destruct (file_read_next len cnt ltac:(lia) ltac:(lia) ltac:(lia)) as [FR FL].
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) in *.
    assert (Lbs : Z.of_nat (length bs) <= STAGE_LEN) by (unfold STAGE_LEN; rewrite FL; lia).
    eapply (rz_read_file RSEGS regs (Z_to_bv 64 0x75f78) mem model ECALLW (Z_to_bv 64 3) path (Z_to_bv 64 len) data cnt);
      [ apply ECALL_7611c | apply is_ecall_ECALLW | exact Hh | exact Hlazy | exact R17 | exact R10
      | rewrite u_small by lia; lia | exact Hfd3 | rewrite Hfs; exact Hdata | exact R12 | lia
      | unfold MAX_RW_COUNT; lia | lia
      | rewrite R11; unorm; unfold TASK_SIZE; lia
      | rewrite R11; apply RefPrintfBufBase.data_store_ok; lia
      | ].
    cbv zeta. rewrite R12, R11. fold bs. rewrite AgentLib.v_addi_lit by lia. change (0x75f78 + 4)%Z with 0x75f7c%Z.
    change 0x80c69 with STAGE.
    set (mem' := wbytes mem (Z_to_bv 64 STAGE) bs).
    set (model' := with_fds (fd_insert (m_fds model) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 len + len_word bs))) model).
    assert (Hh' : m_halted model' = None) by (subst model'; rewrite with_fds_halted'; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (subst model'; rewrite with_fds_lazy; exact Hlazy).
    assert (ST' : statics mem') by (subst mem'; apply statics_wstage; [exact ST | exact Lbs]).
    assert (HRH' : hs_RHEAP HS s [(p, A, cap)] mem') by (subst mem'; apply heap_wstage; [exact HRH | exact Lbs]).
    assert (HWR' : wr_at rsegs mem' A cap) by (subst mem'; apply wr_at_wbytes; exact HWR).
    assert (HKR' : hs_KREL HS s model') by (subst model'; apply (hx_krel_fds HS HX); exact HKR).
    assert (Hra' : rdn RSEGS mem' (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ad50))).
    { subst mem'. unfold STAGE, STAGE_LEN in *. eapply rdn_wbytes_out; [exact Hra | unorm; lia | unorm; lia | unorm; lia]. }
    assert (HDATA' : rdn RSEGS mem' (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) data)).
    { subst mem'. unfold STAGE, STAGE_LEN in *. eapply rdn_wbytes_out; [exact HDATA | unorm; lia | unorm; lia | unorm; lia]. }
    assert (HSTG' : rdn RSEGS mem' (Z_to_bv 64 STAGE) (length bs) = Some bs).
    { subst mem'. apply rdn_wbytes_hit. unfold STAGE, STAGE_LEN in *. unorm. lia. }
    assert (Hfs' : m_fs model' = fs0) by (subst model'; rewrite with_fds_fs; exact Hfs).
    assert (Hfd1' : fd_lookup (m_fds model') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))).
    { subst model'. rewrite with_fds_fds, fd_lookup_insert_neq; [exact Hfd1 | intros E; apply (f_equal bv_unsigned) in E; discriminate]. }
    assert (Hfd2' : fd_lookup (m_fds model') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { subst model'. rewrite with_fds_fds, fd_lookup_insert_neq; [exact Hfd2 | intros E; apply (f_equal bv_unsigned) in E; discriminate]. }
    destruct (Nat.eq_dec (length bs) 0) as [Z0 | NZ].
    - (* [comment removed for export] *)
      assert (Elen : len = Z.of_nat (length data)) by (rewrite FL in Z0; lia).
      assert (Ebs : bs = []) by (destruct bs; [reflexivity | cbn in Z0; lia]).
      rewrite Ebs. cbn [len_word length Z.of_nat].
      eapply (seg_L5b sp0 model' Hvsp Hh' Hlazy' (regupd regs 10 (Z_to_bv 64 0)) mem' pp A len cap);
        [ | apply stk_ok_main; exact ST' | apply mem_inv_ro_none; exact (st_inv mem' ST') | exact Hra' | ].
      { unfold read_ret_regs. repeat split;
          first [ rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate); assumption
                | apply getr_same; intros E; apply (f_equal bv_unsigned) in E; discriminate ]. }
      intros regs2 mem2 Q1 Q2 Q4 Q8 Q9 Q10 Q17 Q18 Q19 Q20 Q21 Q22 FM2 STK2 RA2.
      apply (KEOF Elen regs2 mem2 model'). split; try assumption.
      + rewrite <- Elen. exact Q19.
      + lia.
      + unfold MAX_INPUT. lia.
      + eapply heap_frame; [exact HRH' | exact FM2 | apply regL_w_hi].
      + eapply wr_at_transport; [exact HWR' | exact (frame_mod_wmono _ _ _ FM2)].
      + replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
        eapply (rdn_block_frame mem' mem2 _ A cap 0 data FM2 HBR); [lia | lia | left; reflexivity |].
        rewrite Z.add_0_r. rewrite Elen, Nat2Z.id, firstn_all in HDATA'. exact HDATA'.
      + eapply statics_frame; [exact ST' | exact FM2 | left; reflexivity].
      + subst model'. rewrite with_fds_fds, fd_lookup_insert_eq. eexists. reflexivity.
    - (* [comment removed for export] *)
      set (n := Z.of_nat (length bs)).
      assert (Hn : 1 <= n <= cnt /\ len + n <= Z.of_nat (length data)) by (subst n; rewrite FL; lia).
      assert (Elw : len_word bs = Z_to_bv 64 n) by reflexivity.
      rewrite Elw.
      eapply (seg_L5a sp0 model' Hvsp Hh' Hlazy' (regupd regs 10 (Z_to_bv 64 n)) mem' pp A len cap n);
        [ | lia | lia | lia | lia
        | apply stk_ok_main; exact ST' | apply mem_inv_ro_none; exact (st_inv mem' ST') | exact Hra' | ].
      { unfold read_ret_regs. repeat split;
          first [ rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate); assumption
                | apply getr_same; intros E; apply (f_equal bv_unsigned) in E; discriminate ]. }
      intros regs2 mem2 LB2 T1 T9 T10 T11 T12 T19 T21 T23 FM2 STK2.
      assert (ST2 : statics mem2) by (eapply statics_frame; [exact ST' | exact FM2 | left; reflexivity]).
      assert (HRH2 : hs_RHEAP HS s [(p, A, cap)] mem2) by (eapply heap_frame; [exact HRH' | exact FM2 | apply regL_w_hi]).
      assert (HWR2 : wr_at rsegs mem2 A cap) by (eapply wr_at_transport; [exact HWR' | exact (frame_mod_wmono _ _ _ FM2)]).
      assert (HSTG2 : rdn RSEGS mem2 (Z_to_bv 64 STAGE) (length bs) = Some bs) by (eapply rdn_stage_frame; [exact FM2 | exact Lbs | exact HSTG']).
      assert (HD2 : rdn RSEGS mem2 (Z_to_bv 64 (A + 0)) (length (firstn (Z.to_nat len) data)) = Some (firstn (Z.to_nat len) data)).
      { eapply (rdn_block_frame mem' mem2 _ A cap 0 _ FM2 HBR); [lia | rewrite length_firstn; lia | left; reflexivity |].
        rewrite Z.add_0_r, length_firstn. replace (Z.to_nat len `min` length data)%nat with (Z.to_nat len) by lia. exact HDATA'. }
      destruct (KRELh s model' HKR') as [_ _].
      (* [comment removed for export] *)
      assert (MC : mcH mem2 (Z_to_bv 64 (A + len)) (Z_to_bv 64 STAGE) n bs).
      { unfold STAGE, STAGE_LEN in *.
        split; [lia | subst n; lia | exact HSTG2
              | replace (length bs) with (Z.to_nat n) by lia;
                eapply (MainMem.wr_at_store_ok mem2 A cap len (Z.to_nat n)); [exact HWR2 | lia | lia | lia]
              | unorm; lia | unorm; lia | unorm; lia]. }
      assert (RET : ret_ok (Z_to_bv 64 0x2ace8)) by (apply ret_ok_even; reflexivity).
      destruct (ref_memcpy mem2 (Z_to_bv 64 (A + len)) (Z_to_bv 64 STAGE) n bs (seg_rom RSEGS) MC regs2 (Z_to_bv 64 0x2ace8)
                  RET T1 T10 T11 T12) as (regs3 & RUN3 & KEPT3).
      lazymatch type of RUN3 with msteps _ (mkst _ ?pc3 _ _) _ => replace (Z_to_bv 64 0x75224) with pc3 by (apply bv_eq; reflexivity) end.
      eapply rz_msteps; [exact Hh' | exact Hlazy' | exact RUN3 |]. clear RUN3.
      set (mem3 := wbytes mem2 (Z_to_bv 64 (A + len)) bs) in *.
      pose proof (KEPT3 2%bv ltac:(clear; cbn; first [in_bv | tauto])) as U2. pose proof (KEPT3 4%bv ltac:(clear; cbn; first [in_bv | tauto])) as U4.
      pose proof (KEPT3 8%bv ltac:(clear; cbn; first [in_bv | tauto])) as U8. pose proof (KEPT3 18%bv ltac:(clear; cbn; first [in_bv | tauto])) as U18.
      pose proof (KEPT3 20%bv ltac:(clear; cbn; first [in_bv | tauto])) as U20. pose proof (KEPT3 19%bv ltac:(clear; cbn; first [in_bv | tauto])) as U19.
      pose proof (KEPT3 21%bv ltac:(clear; cbn; first [in_bv | tauto])) as U21. pose proof (KEPT3 22%bv ltac:(clear; cbn; first [in_bv | tauto])) as U22.
      pose proof (KEPT3 9%bv ltac:(clear; cbn; first [in_bv | tauto])) as U9. pose proof (KEPT3 23%bv ltac:(clear; cbn; first [in_bv | tauto])) as U23.
      destruct LB2 as ((T2 & T4 & T8 & T18 & T20) & T22).
      rewrite T2 in U2. rewrite T4 in U4. rewrite T8 in U8. rewrite T18 in U18. rewrite T20 in U20.
      rewrite T19 in U19. rewrite T21 in U21. rewrite T22 in U22. rewrite T9 in U9. rewrite T23 in U23.
      apply (KMORE regs3 mem3 model' n). split.
      + split; [split; [repeat split; assumption | exact U22] |]. repeat split; assumption.
      + lia.
      + lia.
      + exact HPOW.
      + exact HBR.
      + subst mem3. eapply heap_wblock; [exact HRH2 | exact HBR | lia | lia].
      + exact HKR'.
      + subst mem3. apply wr_at_wbytes. exact HWR2.
      + subst mem3. replace (Z.to_nat (len + n)) with (Z.to_nat len + length bs)%nat by lia.
        rewrite <- (firstn_app_read (Z.to_nat len) data bs) by (rewrite FL, FR, <- (take_take (drop _ _)), (take_ge (drop (Z.to_nat len) data) (length data - Z.to_nat len)) by (rewrite length_drop; lia); reflexivity).
        rewrite length_firstn in HD2. replace (Z.to_nat len `min` length data)%nat with (Z.to_nat len) in HD2 by lia.
        rewrite Z.add_0_r in HD2.
        apply rdn_app_Z.
        * eapply rdn_wbytes_out; [exact HD2 | unorm; lia | unorm; lia | unorm; lia].
        * rewrite Z2Nat.id by lia. apply rdn_wbytes_hit. unorm. lia.
        * lia.
        * lia.
      + subst mem3. eapply statics_wblock; [exact ST2 | exact HBR | lia | lia].
      + exact Hfs'.
      + subst model'. rewrite with_fds_fds, fd_lookup_insert_eq, Elw, Z_to_bv_add64. reflexivity.
      + exact Hfd1'.
      + exact Hfd2'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma close_step : forall regs mem model s p A cap K,
    CInv cap A s p regs mem model ->
    (forall regs' model', XInv cap A s p regs' mem model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75f7c) mem (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x75f78) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s p A cap K CI HK.
    destruct CI as [R1 R2 R4 R8 R9 R10 R17 R18 R19 R20 R21 Hcap Hlen HBR HRH HKR HWR HDATA ST Hra Hfs [e3 He3] Hfd1 Hfd2].
    destruct (KRELh s model HKR) as [Hh Hlazy].
    eapply (rz_close RSEGS regs (Z_to_bv 64 0x75f78) mem model ECALLW (Z_to_bv 64 3) e3);
      [ apply ECALL_7611c | apply is_ecall_ECALLW | exact Hh | exact Hlazy | exact R17 | exact R10
      | rewrite u_small by lia; lia | exact He3 |].
    rewrite AgentLib.v_addi_lit by lia. change (0x75f78 + 4)%Z with 0x75f7c%Z.
    apply HK. split; try assumption.
    - unfold close_ret_regs. repeat split;
        first [ rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate); assumption
              | apply getr_same; intros E; apply (f_equal bv_unsigned) in E; discriminate ].
    - apply (hx_krel_fds HS HX). exact HKR.
    - rewrite with_fds_fds, fd_lookup_remove_neq; [exact Hfd1 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
    - rewrite with_fds_fds, fd_lookup_remove_neq; [exact Hfd2 | intros E; apply (f_equal bv_unsigned) in E; discriminate].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma m_cont : forall regs mem model s p (A len n cap : Z) K,
    MInv len n cap A s p regs mem model -> len + n <> cap ->
    (forall regs' mem', RInv (len + n) cap A s p regs' mem' model ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75f78) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2ace8) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s p A len n cap K [MR Hlen Hcap HPOW HBR HRH HKR HWR HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hne HK.
    pose proof SPlo. pose proof SPhi. hcb. destruct (KRELh s model HKR) as [Hh Hlazy].
    pose proof HBR as (B1 & B2 & B3 & B4 & B5). clear B2.
    eapply (seg_Ma sp0 model Hvsp Hh Hlazy regs mem pp A len cap n K MR); [lia | lia | lia | lia | exact Hne
      | apply stk_ok_main; exact ST | apply mem_inv_ro_none; exact (st_inv mem ST) |].
    intros regs1 mem1 NR1 Q9 FM1 STK1.
    assert (ST1 : statics mem1) by (eapply statics_frame; [exact ST | exact FM1 | left; reflexivity]).
    eapply (seg_N sp0 model Hvsp Hh Hlazy regs1 mem1 pp A (len + n) cap K NR1); [lia | lia
      | exact STK1 | apply mem_inv_ro_none; exact (st_inv mem1 ST1) |].
    intros regs2 mem2 RC2 FM2 RA2 STK2. apply HK. split; try assumption.
    - lia.
    - eapply heap_frame; [| exact FM2 | apply regL_w_hi]. eapply heap_frame; [exact HRH | exact FM1 | apply regL_w_hi].
    - eapply wr_at_transport; [| exact (frame_mod_wmono _ _ _ FM2)]. eapply wr_at_transport; [exact HWR | exact (frame_mod_wmono _ _ _ FM1)].
    - assert (LL : length (firstn (Z.to_nat (len + n)) data) = Z.to_nat (len + n)) by (rewrite length_firstn; lia).
      rewrite <- LL at 1. rewrite <- LL in HDATA at 1.
      replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) in HDATA |- * by (f_equal; lia).
      eapply (rdn_block_frame mem1 mem2 _ A cap 0 _ FM2 HBR); [lia | rewrite LL; lia | left; reflexivity |].
      eapply (rdn_block_frame mem mem1 _ A cap 0 _ FM1 HBR); [lia | rewrite LL; lia | left; reflexivity | exact HDATA].
    - eapply statics_frame; [exact ST1 | exact FM2 | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma m_refuse : forall regs mem model s p (A len n cap : Z),
    MInv len n cap A s p regs mem model -> len + n = cap -> MAX_INPUT <= cap ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2ace8) mem (seg_rom RSEGS)) model) (t_die msg_refused fs0).
  Proof.
    intros regs mem model s p A len n cap [MR Hlen Hcap HPOW HBR HRH HKR HWR HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hcapeq Hbig.
    pose proof SPlo. pose proof SPhi. hcb. destruct (KRELh s model HKR) as [Hh Hlazy]. unfold MAX_INPUT in Hbig.
    pose proof HBR as (B1 & B2 & B3 & B4 & B5). clear B2.
    eapply (seg_Mb sp0 model Hvsp Hh Hlazy regs mem pp A len cap n _ MR); [lia | lia | lia | exact Hcapeq
      | apply stk_ok_main; exact ST | apply mem_inv_ro_none; exact (st_inv mem ST) |].
    intros regs1 mem1 GR1 FM1 STK1.
    assert (ST1 : statics mem1) by (eapply statics_frame; [exact ST | exact FM1 | left; reflexivity]).
    eapply (seg_Gr sp0 model Hvsp Hh Hlazy regs1 mem1 pp A cap _ GR1); [lia
      | exact STK1 | apply mem_inv_ro_none; exact (st_inv mem1 ST1) |].
    intros regs2 mem2 (Q2 & Q4 & _) Q9 FM2 STK2.
    assert (ST2 : statics mem2) by (eapply statics_frame; [exact ST1 | exact FM2 | left; reflexivity]).
    assert (HRH2 : hs_RHEAP HS s [(p, A, cap)] mem2).
    { eapply heap_frame; [| exact FM2 | apply regL_w_hi]. eapply heap_frame; [exact HRH | exact FM1 | apply regL_w_hi]. }
    destruct (hx_statics HS HX _ _ _ HRH2) as (_ & _ & [can Hcan]).
    rewrite <- Hfs. apply (ref_refused_tail sp0 [] model Hvsp Hh Hlazy Hfd2 tid can regs2 mem2 Q2 Q4).
    - eapply stk_stk_ok; [exact (st_stk mem2 ST2) | unfold RefReadErr_defs.RE_STK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold RefReadErr_defs.RE_STK; lia | lia].
    - apply mem_inv_ro_none. exact (st_inv mem2 ST2).
    - exact (st_cells mem2 ST2).
    - exact (st_tid mem2 ST2).
    - exact Htid.
    - exact Hcan.
  Qed.

  (* [comment removed for export] *)
  Lemma m_grow : forall regs mem model s p (A len n cap : Z) K,
    MInv len n cap A s p regs mem model -> len + n = cap -> cap < MAX_INPUT ->
    (forall regs' mem' model' A' s' p', RInv cap (2 * cap) A' s' p' regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75f78) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2ace8) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s p A len n cap K [MR Hlen Hcap [k [Hk HPOW]] HBR HRH HKR HWR HDATA ST Hfs Hfd3 Hfd1 Hfd2] Hcapeq Hsmall HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb. unfold MAX_INPUT in Hsmall.
    assert (Hk10 : k < 10).
    { destruct (Z_lt_le_dec k 10) as [?|Hge]; [assumption|]. exfalso.
      pose proof (Z.pow_le_mono_r 2 10 k ltac:(lia) Hge). change (2 ^ 10) with 1024 in H. lia. }
    assert (Hcap2 : 2 * cap <= 67108864).
    { pose proof (Z.pow_le_mono_r 2 (k + 1) 10 ltac:(lia) ltac:(lia)). rewrite Z.pow_succ_r in H by lia. change (2 ^ 10) with 1024 in H. lia. }
    assert (Elo : lo = bv_unsigned sp0 - 8388608) by reflexivity. assert (Espm : spm = bv_unsigned sp0 - 128) by reflexivity.
    destruct (KRELh s model HKR) as [Hh Hlazy].
    pose proof HBR as (B1 & B2 & B3 & B4 & B5). clear B2.
    rewrite Hcapeq in HDATA, Hfd3.
    (* [comment removed for export] *)
    eapply (seg_Mb sp0 model Hvsp Hh Hlazy regs mem pp A len cap n _ MR); [lia | lia | lia | exact Hcapeq
      | apply stk_ok_main; exact ST | apply mem_inv_ro_none; exact (st_inv mem ST) |].
    intros regs0 mem0 GR0 FM0 STK0.
    assert (ST0 : statics mem0) by (eapply statics_frame; [exact ST | exact FM0 | left; reflexivity]).
    assert (HRH0 : hs_RHEAP HS s [(p, A, cap)] mem0) by (eapply heap_frame; [exact HRH | exact FM0 | apply regL_w_hi]).
    assert (HD0 : rdn RSEGS mem0 (Z_to_bv 64 (A + 0)) (length (firstn (Z.to_nat cap) data)) = Some (firstn (Z.to_nat cap) data)).
    { eapply (rdn_block_frame mem mem0 _ A cap 0 _ FM0 HBR); [lia | rewrite length_firstn; lia | left; reflexivity |].
      rewrite Z.add_0_r, length_firstn. replace (Z.to_nat cap `min` length data)%nat with (Z.to_nat cap) by lia. exact HDATA. }
    assert (HWR0 : wr_at rsegs mem0 A cap) by (eapply wr_at_transport; [exact HWR | exact (frame_mod_wmono _ _ _ FM0)]).
    (* [comment removed for export] *)
    eapply (seg_Gb sp0 model Hvsp Hh Hlazy regs0 mem0 pp A cap K GR0); [lia
      | exact STK0 | apply mem_inv_ro_none; exact (st_inv mem0 ST0) |].
    intros regs1 mem1 ((Q2 & Q4 & Q8 & Q18 & Q20) & Q22) Q1 Q9 Q10 Q19 Q21 Q23 FM1 STK1.
    assert (ST1 : statics mem1) by (eapply statics_frame; [exact ST0 | exact FM1 | left; reflexivity]).
    assert (HRH1 : hs_RHEAP HS s [(p, A, cap)] mem1) by (eapply heap_frame; [exact HRH0 | exact FM1 | apply regL_w_hi]).
    assert (HD1 : rdn RSEGS mem1 (Z_to_bv 64 (A + 0)) (length (firstn (Z.to_nat cap) data)) = Some (firstn (Z.to_nat cap) data)).
    { eapply (rdn_block_frame mem0 mem1 _ A cap 0 _ FM1 HBR); [lia | rewrite length_firstn; lia | left; reflexivity | exact HD0]. }
    (* [comment removed for export] *)
    destruct (errno_rw mem1 regs1 Q4) as [errv ERR].
    change (Z_to_bv 64 0x68018) with (Z_to_bv 64 RMALLOC_SYM).
    eapply (malloc_call HS HH HX regs1 mem1 model s [(p, A, cap)] (2 * cap) lo B errv 0x2ad10 K Q1);
      [ lia | reflexivity | exact Q4 | exact Q10 | lia | exact HRH1 | exact HKR
      | apply (AOK s [(p, A, cap)] mem1 (2 * cap) HRH1); [lia | cbn [lb_bytes fold_right blk_size snd]; pose proof (hx_live HS HX); lia | cbn [length]; pose proof (hx_live HS HX); lia]
      | exact (st_aux mem1 ST1) | rewrite Q2, u_small by lia; lia
      | rewrite Q2, u_small by lia; rewrite <- Espm; exact (st_stk mem1 ST1)
      | rewrite Elo; lia | rewrite Q2, u_small by lia; unfold RMALLOC_STACK; lia
      | exact ERR | exact (st_inv mem1 ST1) |].
    intros regs2 mem2 model2 A2 p2 s2 errv2 junk KEPT2 R10 HKR2 MP2 INV2 STK2 ERR2 AUX2 HP2 HBR2 HRH2 CB2.
    rewrite Q2, u_small in STK2, HP2 by lia. rewrite <- Espm in STK2, HP2.
    destruct (KRELh s2 model2 HKR2) as [Hh2 Hlazy2]. destruct (hx_mpres HS HX _ _ MP2) as [FS2 FDS2].
    assert (ST2 : statics mem2) by (eapply statics_heap; [exact ST1 | exact HP2 | exact HRH2 | exact STK2 | exact INV2 | exact AUX2]).
    pose proof HBR2 as (C1 & C2 & C3 & C4 & C5). clear C2.
    assert (HD2 : rdn RSEGS mem2 (Z_to_bv 64 (A + 0)) (length (firstn (Z.to_nat cap) data)) = Some (firstn (Z.to_nat cap) data)).
    { eapply rdn_rheap_pres; [exact HP2 | exact HD1 | lia | rewrite length_firstn; lia |]. rewrite length_firstn. intros i Hi. apply in_block_1. lia. }
    assert (HWR2 : wr_at rsegs mem2 A2 (2 * cap)) by (eapply wr_at_of_CB; [exact CB2 | lia]).
    (* [comment removed for export] *)
    assert (Hp : p2 <> p).
    { intros E. pose proof (RND s2 _ mem2 HRH2) as ND. cbn [map blk_id fst] in ND. subst p2. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
    assert (DISJ : A2 + 2 * cap <= A \/ A + cap <= A2).
    { pose proof (RBD s2 _ mem2 (p2, A2, 2 * cap) (p, A, cap) HRH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hp) as D.
      cbn [blk_addr blk_size fst snd] in D. exact D. }
    (* [comment removed for export] *)
    pose proof (KEPT2 2%bv ltac:(clear; cbn; first [in_bv | tauto])) as S2. pose proof (KEPT2 4%bv ltac:(clear; cbn; first [in_bv | tauto])) as S4.
    pose proof (KEPT2 8%bv ltac:(clear; cbn; first [in_bv | tauto])) as S8. pose proof (KEPT2 18%bv ltac:(clear; cbn; first [in_bv | tauto])) as S18.
    pose proof (KEPT2 20%bv ltac:(clear; cbn; first [in_bv | tauto])) as S20. pose proof (KEPT2 19%bv ltac:(clear; cbn; first [in_bv | tauto])) as S19.
    pose proof (KEPT2 21%bv ltac:(clear; cbn; first [in_bv | tauto])) as S21. pose proof (KEPT2 22%bv ltac:(clear; cbn; first [in_bv | tauto])) as S22.
    pose proof (KEPT2 9%bv ltac:(clear; cbn; first [in_bv | tauto])) as S9. pose proof (KEPT2 23%bv ltac:(clear; cbn; first [in_bv | tauto])) as S23.
    rewrite Q2 in S2. rewrite Q4 in S4. rewrite Q8 in S8. rewrite Q18 in S18. rewrite Q20 in S20.
    rewrite Q19 in S19. rewrite Q21 in S21. rewrite Q22 in S22. rewrite Q9 in S9. rewrite Q23 in S23.
    (* [comment removed for export] *)
    eapply (seg_L2 sp0 model2 Hvsp Hh2 Hlazy2 regs2 mem2 pp A cap (2 * cap) A2 K);
      [ split; [split; [exact S2 | split; [exact S4 | split; [exact S8 | split; [exact S18 | exact S20]]]] | exact S22]
      | exact R10 | exact S19 | exact S21 | exact S9 | exact S23 | lia | lia
      | apply stk_ok_main; exact ST2 | apply mem_inv_ro_none; exact (st_inv mem2 ST2) |].
    intros regs3 mem3 ((T2 & T4 & T8 & T18 & T20) & T22) T1 T9 T10 T11 T12 T19 T21 T23 FM3 STK3.
    assert (ST3 : statics mem3) by (eapply statics_frame; [exact ST2 | exact FM3 | left; reflexivity]).
    assert (HRH3 : hs_RHEAP HS s2 [(p2, A2, 2 * cap); (p, A, cap)] mem3) by (eapply heap_frame; [exact HRH2 | exact FM3 | apply regL_w_hi]).
    assert (HD3 : rdn RSEGS mem3 (Z_to_bv 64 (A + 0)) (length (firstn (Z.to_nat cap) data)) = Some (firstn (Z.to_nat cap) data)).
    { eapply (rdn_block_frame mem2 mem3 _ A cap 0 _ FM3 HBR); [lia | rewrite length_firstn; lia | left; reflexivity | exact HD2]. }
    assert (HWR3 : wr_at rsegs mem3 A2 (2 * cap)) by (eapply wr_at_transport; [exact HWR2 | exact (frame_mod_wmono _ _ _ FM3)]).
    (* [comment removed for export] *)
    set (bs := firstn (Z.to_nat cap) data) in *.
    assert (Lbs : length bs = Z.to_nat cap) by (subst bs; rewrite length_firstn; lia).
    assert (MC : mcH mem3 (Z_to_bv 64 A2) (Z_to_bv 64 A) cap bs).
    { split; [lia | exact Lbs | rewrite Z.add_0_r in HD3; exact HD3
            | rewrite Lbs; replace (Z_to_bv 64 A2) with (Z_to_bv 64 (A2 + 0)) by (f_equal; lia);
              eapply (MainMem.wr_at_store_ok mem3 A2 (2 * cap) 0 (Z.to_nat cap)); [exact HWR3 | lia | lia | lia]
            | unorm; lia | unorm; lia | unorm; lia]. }
    assert (RET : ret_ok (Z_to_bv 64 0x2ad2c)) by (apply ret_ok_even; reflexivity).
    destruct (ref_memcpy mem3 (Z_to_bv 64 A2) (Z_to_bv 64 A) cap bs (seg_rom RSEGS) MC regs3 (Z_to_bv 64 0x2ad2c)
                RET T1 T10 T11 T12) as (regs4 & RUN4 & KEPT4).
    lazymatch type of RUN4 with msteps _ (mkst _ ?pc4 _ _) _ => replace (Z_to_bv 64 0x75224) with pc4 by (apply bv_eq; reflexivity) end.
    eapply rz_msteps; [exact Hh2 | exact Hlazy2 | exact RUN4 |]. clear RUN4.
    set (mem4 := wbytes mem3 (Z_to_bv 64 A2) bs) in *.
    assert (Emem4 : mem4 = wbytes mem3 (Z_to_bv 64 (A2 + 0)) bs) by (subst mem4; f_equal; f_equal; lia).
    assert (ST4 : statics mem4) by (rewrite Emem4; eapply statics_wblock; [exact ST3 | exact HBR2 | lia | rewrite Lbs; lia]).
    assert (HRH4 : hs_RHEAP HS s2 [(p2, A2, 2 * cap); (p, A, cap)] mem4).
    { rewrite Emem4. eapply heap_wblock_in; [exact HRH3 | left; reflexivity | exact HBR2 | lia | rewrite Lbs; lia]. }
    assert (HD4 : rdn RSEGS mem4 (Z_to_bv 64 (A2 + 0)) (length bs) = Some bs).
    { rewrite Emem4. apply rdn_wbytes_hit. unorm. rewrite Lbs. lia. }
    assert (HWR4 : wr_at rsegs mem4 A2 (2 * cap)) by (subst mem4; apply wr_at_wbytes; exact HWR3).
    pose proof (KEPT4 2%bv ltac:(clear; cbn; first [in_bv | tauto])) as U2. pose proof (KEPT4 4%bv ltac:(clear; cbn; first [in_bv | tauto])) as U4.
    pose proof (KEPT4 8%bv ltac:(clear; cbn; first [in_bv | tauto])) as U8. pose proof (KEPT4 18%bv ltac:(clear; cbn; first [in_bv | tauto])) as U18.
    pose proof (KEPT4 20%bv ltac:(clear; cbn; first [in_bv | tauto])) as U20. pose proof (KEPT4 19%bv ltac:(clear; cbn; first [in_bv | tauto])) as U19.
    pose proof (KEPT4 21%bv ltac:(clear; cbn; first [in_bv | tauto])) as U21. pose proof (KEPT4 22%bv ltac:(clear; cbn; first [in_bv | tauto])) as U22.
    pose proof (KEPT4 9%bv ltac:(clear; cbn; first [in_bv | tauto])) as U9. pose proof (KEPT4 23%bv ltac:(clear; cbn; first [in_bv | tauto])) as U23.
    rewrite T2 in U2. rewrite T4 in U4. rewrite T8 in U8. rewrite T18 in U18. rewrite T20 in U20.
    rewrite T19 in U19. rewrite T21 in U21. rewrite T22 in U22. rewrite T9 in U9. rewrite T23 in U23.
    (* [comment removed for export] *)
    eapply (seg_L3 sp0 model2 Hvsp Hh2 Hlazy2 regs4 mem4 pp A cap (2 * cap) A2 K);
      [ split; [split; [exact U2 | split; [exact U4 | split; [exact U8 | split; [exact U18 | exact U20]]]] | exact U22]
      | exact U9 | exact U19 | exact U21 | exact U23
      | apply stk_ok_main; exact ST4 | apply mem_inv_ro_none; exact (st_inv mem4 ST4) |].
    intros regs5 mem5 ((V2 & V4 & V8 & V18 & V20) & V22) V1 V9 V10 V19 V21 FM5 STK5.
    assert (ST5 : statics mem5) by (eapply statics_frame; [exact ST4 | exact FM5 | left; reflexivity]).
    assert (HRH5 : hs_RHEAP HS s2 [(p2, A2, 2 * cap); (p, A, cap)] mem5) by (eapply heap_frame; [exact HRH4 | exact FM5 | apply regL_w_hi]).
    assert (HD5 : rdn RSEGS mem5 (Z_to_bv 64 (A2 + 0)) (length bs) = Some bs).
    { eapply (rdn_block_frame mem4 mem5 _ A2 (2 * cap) 0 _ FM5 HBR2); [lia | rewrite Lbs; lia | left; reflexivity | exact HD4]. }
    assert (HWR5 : wr_at rsegs mem5 A2 (2 * cap)) by (eapply wr_at_transport; [exact HWR4 | exact (frame_mod_wmono _ _ _ FM5)]).
    (* [comment removed for export] *)
    destruct (errno_rw mem5 regs5 V4) as [errv5 ERR5].
    change (Z_to_bv 64 0x67ed8) with (Z_to_bv 64 RFREE_SYM).
    eapply (free_call HS HH HX regs5 mem5 model2 s2 [(p2, A2, 2 * cap); (p, A, cap)] p A cap lo B errv5 0x2ad34 K V1);
      [ lia | reflexivity | exact V4 | exact V10 | exact HRH5 | exact HKR2 | right; left; reflexivity
      | exact (st_aux mem5 ST5) | rewrite V2, u_small by lia; lia
      | rewrite V2, u_small by lia; rewrite <- Espm; exact (st_stk mem5 ST5)
      | rewrite Elo; lia | rewrite V2, u_small by lia; unfold RFREE_STACK; lia
      | exact ERR5 | exact (st_inv mem5 ST5) |].
    intros regs6 mem6 model6 s6 KEPT6 HKR6 MP6 INV6 STK6 ERR6 AUX6 HP6 HRH6.
    rewrite V2, u_small in STK6, HP6 by lia. rewrite <- Espm in STK6, HP6.
    assert (ELB : hs_lb_remove HS p [(p2, A2, 2 * cap); (p, A, cap)] = [(p2, A2, 2 * cap)]).
    { destruct LBR as (L1 & L2 & L3). rewrite (L2 p (p2, A2, 2 * cap)) by (cbn; exact Hp). rewrite (L1 p A cap []) by (cbn; tauto). reflexivity. }
    rewrite ELB in HP6, HRH6.
    destruct (KRELh s6 model6 HKR6) as [Hh6 Hlazy6]. destruct (hx_mpres HS HX _ _ MP6) as [FS6 FDS6].
    assert (ST6 : statics mem6) by (eapply statics_heap; [exact ST5 | exact HP6 | exact HRH6 | exact STK6 | exact INV6 | exact AUX6]).
    assert (HD6 : rdn RSEGS mem6 (Z_to_bv 64 (A2 + 0)) (length bs) = Some bs).
    { eapply rdn_rheap_pres; [exact HP6 | exact HD5 | lia | rewrite Lbs; lia |]. rewrite Lbs. intros i Hi. apply in_block_1. lia. }
    assert (HWR6 : wr_at rsegs mem6 A2 (2 * cap)).
    { eapply wr_at_rheap_pres; [exact HP6 | exact HWR5 |]. intros i Hi. apply in_block_1. lia. }
    pose proof (KEPT6 2%bv ltac:(clear; cbn; first [in_bv | tauto])) as W2. pose proof (KEPT6 4%bv ltac:(clear; cbn; first [in_bv | tauto])) as W4.
    pose proof (KEPT6 8%bv ltac:(clear; cbn; first [in_bv | tauto])) as W8. pose proof (KEPT6 18%bv ltac:(clear; cbn; first [in_bv | tauto])) as W18.
    pose proof (KEPT6 20%bv ltac:(clear; cbn; first [in_bv | tauto])) as W20. pose proof (KEPT6 19%bv ltac:(clear; cbn; first [in_bv | tauto])) as W19.
    pose proof (KEPT6 21%bv ltac:(clear; cbn; first [in_bv | tauto])) as W21. pose proof (KEPT6 9%bv ltac:(clear; cbn; first [in_bv | tauto])) as W9.
    pose proof (KEPT6 22%bv ltac:(clear; cbn; first [in_bv | tauto])) as W22.
    rewrite V2 in W2. rewrite V4 in W4. rewrite V8 in W8. rewrite V18 in W18. rewrite V20 in W20.
    rewrite V19 in W19. rewrite V21 in W21. rewrite V9 in W9. rewrite V22 in W22.
    (* [comment removed for export] *)
    eapply (seg_R sp0 model6 Hvsp Hh6 Hlazy6 regs6 mem6 pp A2 cap (2 * cap) K);
      [ split; [split; [split; [exact W2 | split; [exact W4 | split; [exact W8 | split; [exact W18 | exact W20]]]] | exact W22] |]
      | lia | lia
      | apply stk_ok_main; exact ST6 | apply mem_inv_ro_none; exact (st_inv mem6 ST6) |].
    { split; [exact W19 | split; [exact W21 | exact W9]]. }
    intros regs7 mem7 RC7 FM7 RA7 STK7.
    apply (HK regs7 mem7 model6 A2 s6 p2).
    split.
    - exact RC7.
    - lia.
    - lia.
    - exists (k + 1). split; [lia|]. rewrite Z.pow_succ_r by lia. lia.
    - exact HBR2.
    - eapply heap_frame; [exact HRH6 | exact FM7 | apply regL_w_hi].
    - exact HKR6.
    - eapply wr_at_transport; [exact HWR6 | exact (frame_mod_wmono _ _ _ FM7)].
    - fold bs. rewrite <- Lbs. replace (Z_to_bv 64 A2) with (Z_to_bv 64 (A2 + 0)) by (f_equal; lia).
      eapply (rdn_block_frame mem6 mem7 _ A2 (2 * cap) 0 _ FM7 HBR2); [lia | rewrite Lbs; lia | left; reflexivity | exact HD6].
    - eapply statics_frame; [exact ST6 | exact FM7 | left; reflexivity].
    - exact RA7.
    - rewrite FS6, FS2. exact Hfs.
    - rewrite FDS6, FDS2. exact Hfd3.
    - rewrite FDS6, FDS2. exact Hfd1.
    - rewrite FDS6, FDS2. exact Hfd2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_sound : forall (n : nat) len cap A s p regs mem model K,
    Z.of_nat (length data) - len <= Z.of_nat n ->
    RInv len cap A s p regs mem model ->
    (forall cap' A' s' p' regs' mem' model', CInv cap' A' s' p' regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x75f78) mem' (seg_rom RSEGS)) model') K) ->
    (MAX_INPUT <= Z.of_nat (length data) -> K = t_die msg_refused fs0) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x75f78) mem (seg_rom RSEGS)) model) K.
  Proof.
    induction n as [|n IH]; intros len cap A s p regs mem model K Hn RI KEOF KREF.
    - (* [comment removed for export] *)
      pose proof (ri_len _ _ _ _ _ _ _ _ RI) as Hlen.
      eapply read_step; [exact RI | | intros _; exact (KEOF cap A s p)].
      intros regs' mem' model' n0 MI. exfalso. pose proof (mi_len _ _ _ _ _ _ _ _ _ MI). lia.
    - pose proof (ri_len _ _ _ _ _ _ _ _ RI) as Hlen. pose proof (ri_cap _ _ _ _ _ _ _ _ RI) as Hcap.
      eapply read_step; [exact RI | | intros _; exact (KEOF cap A s p)].
      intros regs1 mem1 model1 n0 MI. pose proof (mi_len _ _ _ _ _ _ _ _ _ MI) as Hlen1.
      destruct (Z.eq_dec (len + n0) cap) as [Heq | Hne].
      + destruct (Z_lt_le_dec cap MAX_INPUT) as [Hsmall | Hbig].
        * eapply m_grow; [exact MI | exact Heq | exact Hsmall |]. intros regs2 mem2 model2 A2 s2 p2 RI2.
          eapply (IH cap); [lia | exact RI2 | exact KEOF | exact KREF].
        * rewrite (KREF ltac:(lia)). eapply m_refuse; [exact MI | exact Heq | exact Hbig].
      + eapply m_cont; [exact MI | exact Hne |]. intros regs2 mem2 RI2.
        eapply (IH (len + n0)); [lia | exact RI2 | exact KEOF | exact KREF].
  Qed.
End Loop.
