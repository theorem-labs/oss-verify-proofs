(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX MemSplit
  Spec RefNodes LibTail LibDiagKn RefMemcpyLib RefMemcpyBase RefMemcpy
  RefStdioDefs RefPrintfFirst RefPrintfBufBase RefPrintfBuf
  SReach SReachTree RegsEquivM MainEqv MainDefs MainArith MainWalk_defs MainMem MainHeap MainSegs MainLoop TRWalk_defs TRSegs HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Image Exec TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface CXXRep XRep XFuzz_stmt XFuzz_stmt2 F_atexit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac in_from H := cbn [In] in H; decompose [or] H; clear H; try contradiction; subst; in_solve.

Lemma lb_bytes_perm : forall LB LB', Permutation LB' LB -> lb_bytes LB' = lb_bytes LB.
Proof.
  intros LB LB' P. induction P as [| x l l' P IH | x y l | l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - cbn [lb_bytes fold_right]. fold (lb_bytes l). fold (lb_bytes l'). lia.
  - cbn [lb_bytes fold_right]. fold (lb_bytes l). lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma pristine_of_z : forall m lo hi, pristine_z m lo hi -> pristine m lo hi.
Proof. intros m lo hi P a Ha. rewrite wa_eq. apply P. exact Ha. Qed.

(* [comment removed for export] *)
Lemma evt_realizes : forall (P : machine_state -> Prop) ms mo K,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  evt rsegs P ms -> (forall ms', P ms' -> realizes RSEGS (mkCfg ms' mo) K) ->
  realizes RSEGS (mkCfg ms mo) K.
Proof.
  intros P ms mo K Hh Hl EV HK.
  eapply sreach_realizes; [apply (cj_evt_sreach RSEGS P ms mo Hh Hl EV)|].
  intros [ms' mo'] [HP Hmo]. cbn in HP, Hmo. subst mo'. apply HK. exact HP.
Qed.

Section TR.
  Context {HCEIL : HeapCeil}.
  Variable HS : hsr.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.
  (* [comment removed for export] *)
  Variable FT : mem -> Prop.
  Hypothesis FTL : ft_local FT.
  Hypothesis FZ : fuzz_stmt_with2 HS FT.   (* [comment removed for export] *)

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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fuzz_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma fuzz_call : forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
      (s : PState) (LB : list block) (D N lo B : Z) (ds : list byte) (errv : word) (ra : Z) (K : TSet),
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 RATP ->
    getr regs 10 = Z_to_bv 64 D -> getr regs 11 = Z_to_bv 64 N ->
    bytes_at rsegs mem D ds -> Z.of_nat (length ds) = N -> N < 2 ^ 26 -> D mod 16 = 0 ->
    (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = P_FUZZ_EMPTY) ->
    hs_RHEAP HS s LB mem -> hs_KREL HS s model ->
    lb_bytes LB + FUZZ_LIVE2 <= hs_LIVE_MAX HS -> Z.of_nat (length LB) + FUZZ_CNT <= hs_LIVE_CNT_MAX HS ->
    hs_rauxv_ok HS mem B -> bv_unsigned (getr regs 2) <= B -> B < 2 ^ 64 ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    stk rsegs mem lo (bv_unsigned (getr regs 2)) -> hceil <= lo -> lo <= bv_unsigned (getr regs 2) - FUZZ_STACK ->
    rw_cells rsegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv rsegs mem ->
    XImg mem -> CanaryReads mem -> HStat FT mem ->
    bv_unsigned (getr regs 2) <= 0x7fffffffffff ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) (s' : PState) (LB' : list block) (errv' : word),
        (forall r, In r fuzz_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        hs_KREL HS s' model' -> hs_MPRES HS model model' ->
        mem_inv rsegs mem' -> stk rsegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells rsegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> hs_rauxv_ok HS mem' B ->
        hs_RHEAP HS s' LB' mem' -> Permutation LB' LB ->
        HStat FT mem' ->
        xpres LB (bv_unsigned (getr regs 2)) XH_X mem mem' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 P_FUZZ_ENTRY) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s LB D N lo B ds errv ra K Hra Hra64 Hra2 Htp Ha0 Ha1 HBY HLEN HN HD16 HBLK HEMP HRH HKR HLIVE HCNT
           HAU HB HB64 HSP16 HSTK HLO HLO2 HERR HINV HXI HCAN HHS HSP47 HK.
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 P_FUZZ_ENTRY) (Z_to_bv 32 0) None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0, Ha1.
    eapply sreach_realizes.
    { apply (hx_sr HS HX).
      apply (FZ (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (Z_to_bv 64 D) (Z_to_bv 64 N) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)
                bvmap_empty (Z_to_bv 32 0) mem model s LB D N lo B ds errv);
        try assumption; try reflexivity.
      - rewrite <- Htp. exact HERR.
      - rewrite u_small by lia. exact Hra2. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HRH' & HPERM & HHS' & HX').
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' s' LB' errv'); try exact HKR'; try exact HMP; try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HRH'; try exact HPERM; try exact HHS'; try exact HX'.
    - intros r Hr. unfold fuzz_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma atexit_call : forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
      (fn f0 a0v nx lo : Z) (f3 pad fj aj : list byte) (ra : Z) (K : TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 10 = Z_to_bv 64 fn -> 0 <= fn < 2 ^ 64 ->
    rw_cells rsegs mem A_ATEXIT (AtexitCells 0 0 f0 a0v f3 pad nx fj aj) ->
    bytes_at rsegs mem A_NEED_LOCKS [b8 0] ->
    stk rsegs mem lo (bv_unsigned (getr regs 2)) -> lo + ATEXIT_FRAME <= bv_unsigned (getr regs 2) -> 0xb4000 <= lo ->
    mem_inv rsegs mem ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte),
        (forall r, In r leaf_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        munch [(lo, bv_unsigned (getr regs 2)); (A_ATEXIT, A_ATEXIT + 544)] mem mem' -> wmono rsegs mem mem' ->
        mem_inv rsegs mem' -> stk rsegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells rsegs mem' A_ATEXIT (AtexitCells 1 A_ATEXIT_BUILTIN P_ATEXIT_CALL fn f3 pad nx fj aj) ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 P_ATEXIT) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model fn f0 a0v nx lo f3 pad fj aj ra K Hh Hl Hra Hra64 Hra2 Ha0 Hfn AX NL ST LO LOHI MI HK.
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) bvmap_empty (Z_to_bv 64 P_ATEXIT) (Z_to_bv 32 0) None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Ha0.
    eapply evt_realizes; [exact Hh | exact Hl | |].
    { apply (atexit_spec (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)
                bvmap_empty (Z_to_bv 32 0) mem fn f0 a0v nx lo f3 pad fj aj); assumption. }
    intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST' & AX').
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m'); try exact MU; try exact WM; try exact MI'; try exact ST'; try exact AX'.
    - intros r Hr. unfold leaf_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; reflexivity.
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition atexit_cells0 : list cell := AtexitCells 0 0 0 0 (zeros 3) (zeros 4) 0 (zeros 248) (zeros 248).
  Definition atexit_cells1 : list cell := AtexitCells 1 A_ATEXIT_BUILTIN P_ATEXIT_CALL 0x2b090 (zeros 3) (zeros 4) 0 (zeros 248) (zeros 248).

  Lemma atexit_cells0_zeros : cells_bytes atexit_cells0 = zeros 544 /\ cells_size atexit_cells0 = 544%nat /\ cells_wf atexit_cells0.
  Proof. vm_compute. repeat split; reflexivity. Qed.
  Lemma atexit_zero_rw : rw_bytes_b rsegs A_ATEXIT (zeros 544) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma atexit_cells_initial : forall m, pristine m 0xb26a0 0xb28c0 -> rw_cells rsegs m A_ATEXIT atexit_cells0.
  Proof.
    intros m P. destruct atexit_cells0_zeros as (B & S & W).
    eapply rw_cells_recast; [apply (rw_cells_zero_image m A_ATEXIT 544) | exact W | rewrite B; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | rewrite S; reflexivity].
    - exact P. - exact atexit_zero_rw. - unfold A_ATEXIT; lia. - unfold A_ATEXIT; cbn; lia.
  Qed.
  Definition atexit_bytes1 : list byte := Eval vm_compute in cells_bytes atexit_cells1.
  Lemma atexit_cells1_bytes : cells_bytes atexit_cells1 = atexit_bytes1 /\ length atexit_bytes1 = 544%nat /\ cells_wf atexit_cells1.
  Proof. vm_compute. repeat split; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition atexit_fix_cells : list (Z * nat * Z) :=
    [(0xb26a4, 4%nat, 0); (0xb26b0, 8%nat, 0xb26b8); (0xb26a8, 4%nat, 1); (0xb26b8, 8%nat, 0); (0xb26c0, 8%nat, 0x67824); (0xb27c0, 8%nat, 0x2b090)]%Z.
  Lemma atexit_cells_fix : forall m, rw_cells rsegs m A_ATEXIT atexit_cells1 -> cells_ok m atexit_fix_cells.
  Proof.
    intros m RC. destruct atexit_cells1_bytes as (B & L & W).
    destruct RC as [[_ BA] _]. rewrite B in BA.
    unfold atexit_fix_cells, cells_ok.
    repeat (apply Forall_cons; [unfold cell_ok;
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?v =>
        let k := eval vm_compute in (Z.to_nat (a - A_ATEXIT)) in
        let R := fresh "R" in
        pose proof (bytes_at_rdn rsegs m A_ATEXIT atexit_bytes1 k n BA ltac:(rewrite L; cbn; lia)) as R;
        replace (wa (A_ATEXIT + Z.of_nat k)) with (Z_to_bv 64 a) in R by (rewrite wa_eq; f_equal; reflexivity);
        etransitivity; [exact R | vm_compute; reflexivity] end |]).
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_zero : forall m (a : Z), m (Z_to_bv 64 a) = None -> seg_rom RSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0) ->
    rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 0].
  Proof. intros m a Hm Hr. cbn [rdn]. rewrite Hm, Hr. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tr_cells : list (Z * nat * Z) := exit_cells_base ++ atexit_fix_cells.
  Definition tr_list : list (Z * nat * Z) := Eval vm_compute in tr_cells.
  Lemma tr_cells_eq : tr_cells = tr_list. Proof. vm_compute. reflexivity. Qed.
  Lemma tr_cells_wf : forallb cell_wf_b tr_cells = true. Proof. vm_compute. reflexivity. Qed.
  Lemma tr_cells_range :
    Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
      0x7a178 <= a /\ a + Z.of_nat w <= 0xb2d18 /\ (a + Z.of_nat w <= 0x80b10 \/ 0x80bf8 <= a) /\ (a + Z.of_nat w <= 0x90c70 \/ 0x90c78 <= a)
      /\ (a + Z.of_nat w <= 0x925ac \/ 0x925b0 <= a) /\ (a + Z.of_nat w <= XH_LO \/ XH_HI <= a) end) tr_cells.
  Proof. rewrite tr_cells_eq. unfold tr_list, XH_LO, XH_HI. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
  Lemma tr_cells_split : Forall (fun c => client_cell c \/ static_cell c) tr_cells.
  Proof.
    rewrite tr_cells_eq. unfold tr_list, client_cell, static_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK.
    repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [left; lia | right; tauto] |]). apply Forall_nil.
  Qed.
  Lemma pf1_cells_range' : Forall (fun c : Z * nat * Z => match c with (a, w, _) => (a = 0x7f808 /\ w = 8%nat) \/ (0x80b10 <= a /\ a + Z.of_nat w <= 0x80ba4) end) pf1_cells.
  Proof. unfold pf1_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Call.
    Variables (sp : word) (A cap : Z) (data : list byte) (ps : PState) (LB : list block) (model0 : Model)
              (regs0 : bvmap 5 word) (mem0 : word -> option byte).
    Hypothesis PRE : TRpre HS sp A cap data ps LB model0 regs0 mem0.

    Let cfg : Z := hdr_cfg data.
    Let N : Z := hdr_payload_len data.
    Let CP : Z := A + 2.
    Let PL : Z := A + 2 + hdr_cfg data + 4.
    (* [comment removed for export] *)
    Let ds : list byte := firstn (Z.to_nat N) (skipn (Z.to_nat (6 + cfg)) data).
    Let calls : nat := hdr_calls data.

    Let SPlo : 0x7fff7f811000 <= bv_unsigned sp.
    Proof. pose proof (tr_splo _ _ _ _ _ _ _ _ _ _ PRE) as H. hcb. unfold TR_STACK in H. lia. Qed.
    Let HCLO : hceil + TR_STACK + 4096 <= bv_unsigned sp.
    Proof. exact (tr_splo _ _ _ _ _ _ _ _ _ _ PRE). Qed.
    (* [comment removed for export] *)
    Ltac hcb ::=
      let K := fresh "HCEILB" in pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as K;
      let L := fresh "HCLO" in pose proof (HCLO : hceil + 65536 + 4096 <= bv_unsigned sp) as L.
    Let SPhi : bv_unsigned sp <= 0x7fffffffff80.
    Proof. pose proof (tr_sphi _ _ _ _ _ _ _ _ _ _ PRE). lia. Qed.
    Let SP16 : bv_unsigned sp mod 16 = 0.
    Proof. exact (tr_sp16 _ _ _ _ _ _ _ _ _ _ PRE). Qed.
    Let Hcfg : 0 <= cfg < 32768. Proof. exact (hdr_cfg_range data). Qed.
    Let HN : 0 <= N < 2 ^ 26.
    Proof. pose proof (tr_len6 _ _ _ _ _ _ _ _ _ _ PRE). pose proof (tr_lenhi _ _ _ _ _ _ _ _ _ _ PRE). unfold MAX_INPUT in *. subst N. unfold hdr_payload_len. subst cfg. lia. Qed.
    Let Hds : length ds = Z.to_nat N.
    Proof.
      pose proof (tr_len6 _ _ _ _ _ _ _ _ _ _ PRE). subst ds N cfg. unfold hdr_payload_len in *.
      rewrite length_firstn, length_skipn. lia.
    Qed.
    Let Hcalls : (1 <= calls <= 4)%nat. Proof. exact (hdr_calls_range data). Qed.

    (* [comment removed for export] *)
    Definition tr_region (r : word * Z) : Prop :=
      (bv_unsigned sp - TR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x80b10 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x80bf8 /\ 0 <= snd r)
      \/ (0xb2d28 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0xb2d30 /\ 0 <= snd r)
      \/ (0x90c70 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x90c78 /\ 0 <= snd r).

    Record tinv (m : word -> option byte) : Prop := TI {
      ti_inv   : mem_inv rsegs m;
      ti_stk   : stk rsegs m (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
      ti_cells : cells_ok m tr_cells;
      ti_relro : relro_none m;
      ti_xdata : pristine_z m 0x80870 0x80a20;
      ti_tid   : exists t, rdn RSEGS m (Z_to_bv 64 0x925a8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 t)) /\ 0 < t < 2 ^ 22;
      ti_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> m a = mem0 a;
      ti_aux   : exists B', hs_rauxv_ok HS m B' /\ bv_unsigned sp + 128 <= B' < 2 ^ 64;
      ti_hs    : HStat FT m }.

    (* [comment removed for export] *)
    Definition cagree (LBc : list block) (m m' : word -> option byte) : Prop :=
      forall a, 0 <= a < 2 ^ 64 -> rclient_addr LBc (bv_unsigned sp - 80) a -> (a < XH_LO \/ XH_HI <= a) -> m' (wa a) = m (wa a).
    Lemma cagree_of_rheap_pres : forall LBc m m', rheap_pres LBc (bv_unsigned sp - 80) m m' -> cagree LBc m m'.
    Proof. intros LBc m m' HP a Ha HC _. exact (proj1 (HP a Ha HC)). Qed.
    Lemma cagree_of_xpres : forall LBc m m', xpres LBc (bv_unsigned sp - 80) XH_X m m' -> cagree LBc m m'.
    Proof. intros LBc m m' HP a Ha HC HX'. refine (proj1 (HP a Ha _)). split; [exact HC|]. cbn. unfold XH_LO, XH_HI in *. lia. Qed.

    Lemma XImg_of_tinv : forall m, tinv m -> XImg m.
    Proof. intros m TIm. split; apply pristine_of_z; [exact (ti_relro _ TIm) | exact (ti_xdata _ TIm)]. Qed.

    Lemma tinv_frame : forall m m' rs,
      tinv m -> frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> tinv m'.
    Proof.
      intros m m' rs [INV STK CELLS RELRO XD [t [TID Ht]] ABOVE [B' [AUX HB']] HSm] FM RS. pose proof SPlo. pose proof SPhi.
      pose proof FM as [Hout Hg]. unfold tr_region, TR_STACK in RS.
      assert (OUT : forall a : Z, 0 <= a < 2 ^ 64 -> (a < 0x80b10 \/ (0x80bf8 <= a /\ a < 0x90c70) \/ (0x90c78 <= a /\ a < 0xb2d28) \/ (0xb2d30 <= a /\ a < bv_unsigned sp - 65536) \/ bv_unsigned sp <= a) ->
                m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
      { intros a Ha Hra. apply Hout. apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (RS r Hr) as [X|[X|[X|X]]]; lia. }
      split.
      - eapply mem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. pose proof (u64_range (fst r)). destruct (RS r Hr); lia.
      - apply (stk_grows sp m m'); [exact STK | unfold TR_STACK; lia | exact Hg].
      - eapply cells_ok_frame; [apply tr_cells_wf | exact CELLS | exact FM |].
        eapply Forall_impl; [| apply tr_cells_range]. intros [[a w] v] (R1 & R2 & R3 & R4 & R5 & R6) r Hr. cbn [fst snd].
        destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - intros i Hi. rewrite OUT; [apply RELRO; exact Hi | lia | lia].
      - intros i Hi. rewrite OUT; [apply XD; exact Hi | lia | lia].
      - exists t. split; [|exact Ht]. eapply rdn_frame; [exact FM | exact TID | unorm; lia |]. intros r Hr. unorm.
        destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - intros a Ha. rewrite <- (ABOVE a Ha). apply Hout. apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - exists B'. split; [|exact HB']. eapply AUF; [exact AUX | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
        unfold RAUXV_CELL. destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - eapply HStat_agree; [exact FTL | exact HSm |]. intros a Ha. rewrite !wa_eq. apply OUT; unfold XH_LO, XH_HI in Ha; lia.
    Qed.

    Lemma heap_frame_tr : forall m m' s1 LB1 rs,
      hs_RHEAP HS s1 LB1 m -> frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> hs_RHEAP HS s1 LB1 m'.
    Proof.
      intros m m' s1 LB1 rs RH FM RS. pose proof SPlo. pose proof HCLO as HCL. unfold TR_STACK in HCL. unfold tr_region, TR_STACK in RS.
      eapply RFR; [exact RH | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
      apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
      hcb. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn [fst snd].
      destruct (RS r Hr) as [X|[X|[X|X]]]; [left; lia | right; left; lia | right; left; lia | right; left; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma cells_ok_cagree : forall cs m m' LBc s' LB',
      forallb cell_wf_b cs = true -> Forall (fun c => client_cell c \/ static_cell c) cs ->
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => a + Z.of_nat w <= XH_LO \/ XH_HI <= a end) cs ->
      cells_ok m cs -> cagree LBc m m' -> hs_RHEAP HS s' LB' m' -> cells_ok m' cs.
    Proof.
      intros cs m m' LBc s' LB' Hwf Hsplit Hxh Hc HP HR. pose proof SPlo.
      destruct (hx_statics HS HX s' LB' m' HR) as (S1 & S2 & S3).
      unfold cells_ok in *. induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hsplit as [|x l Hx Hl]; subst. inversion Hc as [|x' l' Hc1 Hcl]; subst. inversion Hxh as [|x'' l'' Hx2 Hl2]; subst.
      constructor; [|apply IH; assumption].
      destruct Hx as [CL | ST].
      - eapply cell_ok_agree; [exact H1 | | exact Hc1]. intros i Hi.
        unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
        rewrite <- wa_eq. unfold client_cell in CL.
        apply HP; [lia | right; left; unfold ralloc_static; lia | lia].
      - destruct ST as [E|E]; injection E as -> -> ->; unfold cell_ok; assumption.
    Qed.

    Lemma tinv_cagree : forall m m' LB1 s2 LB2 B2,
      tinv m -> cagree LB1 m m' -> hs_RHEAP HS s2 LB2 m' ->
      stk rsegs m' (bv_unsigned sp - TR_STACK) (bv_unsigned sp - 80) -> mem_inv rsegs m' ->
      hs_rauxv_ok HS m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 -> HStat FT m' -> tinv m'.
    Proof.
      intros m m' LB1 s2 LB2 B2 [INV STK CELLS RELRO XD [t [TID Ht]] ABOVE AUX HSm] HP RH STK' INV' AUX' HB2 HS'. pose proof SPlo. pose proof SPhi.
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. apply HP; [apply u64_range | left; lia | unfold XH_HI; lia]. }
      assert (AGc : forall a : Z, 0x7a000 <= a -> a < 0x925a8 + 8 -> (a + 1 <= RLIBC \/ False) -> (a < RSSP_GUARD \/ RSSP_GUARD + 8 <= a) -> (a < RGOT_SSP \/ RGOT_SSP + 8 <= a) -> (a < RERRNO \/ RERRNO + 4 <= a) -> (a < XH_LO \/ XH_HI <= a) ->
                m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
      { intros a R1 R2 R3 R4 R5 R6 R7. rewrite <- wa_eq. apply HP; [unfold RLIBC in *; lia | right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *; lia | exact R7]. }
      split; try assumption.
      - destruct STK as (Q1 & Q2 & Q3). destruct STK' as (_ & _ & Q3'). split; [exact Q1|]. split; [exact Q2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply Q3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply Q3. lia.
      - eapply cells_ok_cagree; [apply tr_cells_wf | apply tr_cells_split | | exact CELLS | exact HP | exact RH].
        eapply Forall_impl; [| apply tr_cells_range]. intros [[a w] v]. tauto.
      - intros i Hi. rewrite <- (RELRO i Hi). apply AGc; unfold RLIBC, RSSP_GUARD, RGOT_SSP, RERRNO, XH_LO; lia.
      - intros i Hi. rewrite <- (XD i Hi). apply AGc; unfold RLIBC, RSSP_GUARD, RGOT_SSP, RERRNO, XH_LO; lia.
      - exists t. split; [|exact Ht]. rewrite (rdn_ext RSEGS 4 m' m); [exact TID | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
        rewrite <- (Z_to_bv_bv_unsigned x). apply AGc; unfold RLIBC, RSSP_GUARD, RGOT_SSP, RERRNO, XH_HI; lia.
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma HStat_rheap_pres : forall LBc m m', HStat FT m -> rheap_pres LBc (bv_unsigned sp - 80) m m' -> HStat FT m'.
    Proof.
      intros LBc m m' HSm HP. pose proof SPlo. eapply HStat_agree; [exact FTL | exact HSm |]. intros a Ha. unfold XH_LO, XH_HI in Ha.
      refine (proj1 (HP a _ _)); [lia | right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_block_tr : forall m m' rs (Bk n k : Z) bs,
      frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> rblock_range Bk n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
      rdn RSEGS m (Z_to_bv 64 (Bk + k)) (length bs) = Some bs -> rdn RSEGS m' (Z_to_bv 64 (Bk + k)) (length bs) = Some bs.
    Proof.
      intros m m' rs Bk n k bs FM RS HBR Hk Hl HD. pose proof SPlo. unfold tr_region, TR_STACK in RS.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm. destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
    Qed.

    Lemma rdn_client_cagree : forall LB1 m m' (a : Z) n bs,
      cagree LB1 m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> client_cell (a, n, 0) -> (a + Z.of_nat n <= XH_LO \/ XH_HI <= a) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros LB1 m m' a n bs HP HD HC HXr. unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in HC.
      rewrite (rdn_ext RSEGS n m' m); [exact HD | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
      apply HP; [apply u64_range | right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia | lia].
    Qed.

    Lemma tframe_agree : forall m m' s0 s1 s2 s3 s4 s5 s6 s7,
      tframe sp m s0 s1 s2 s3 s4 s5 s6 s7 -> (forall x : word, bv_unsigned sp - 80 <= bv_unsigned x < bv_unsigned sp -> m' x = m x) ->
      tframe sp m' s0 s1 s2 s3 s4 s5 s6 s7.
    Proof.
      intros m m' s0 s1 s2 s3 s4 s5 s6 s7 TF AG. pose proof SPlo. pose proof SPhi. unfold tframe in *.
      repeat match goal with |- _ /\ _ => split end;
        lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
          rewrite (rdn_ext RSEGS 8 m' m); [tauto | unorm; lia | intros x Hx; apply AG; revert Hx; unorm; intros Hx; lia] end.
    Qed.
    Lemma tframe_cagree : forall LBc m m' s0 s1 s2 s3 s4 s5 s6 s7,
      tframe sp m s0 s1 s2 s3 s4 s5 s6 s7 -> cagree LBc m m' -> tframe sp m' s0 s1 s2 s3 s4 s5 s6 s7.
    Proof.
      intros LBc m m' s0 s1 s2 s3 s4 s5 s6 s7 TF HP. pose proof SPlo. eapply tframe_agree; [exact TF|]. intros x Hx.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. apply HP; [apply u64_range | left; lia | unfold XH_HI; lia].
    Qed.

    (* [comment removed for export] *)
    Definition sto (j : nat) (m : word -> option byte) : Prop :=
      match j with
      | O => cells_ok m pf1_cells
      | S k => stdout_after m k /\ rdn RSEGS m (Z_to_bv 64 0x80ba0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
      end.

    (* [comment removed for export] *)
    Definition quiet_region (r : word * Z) : Prop :=
      (bv_unsigned sp - TR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x90c70 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x90c78 /\ 0 <= snd r).
    Lemma quiet_tr : forall r, quiet_region r -> tr_region r.
    Proof. intros r [X|X]; [left; exact X | right; right; right; exact X]. Qed.

    Lemma sto_frame : forall j m m' rs, (j <= 4)%nat -> sto j m -> frame_mod m m' rs -> (forall r, In r rs -> quiet_region r) -> sto j m'.
    Proof.
      intros j m m' rs Hj ST FM RS. pose proof SPlo. unfold quiet_region, TR_STACK in RS. destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_frame; [apply pf1_cells_wf | exact ST | exact FM |].
        eapply Forall_impl; [| apply pf1_cells_range']. intros [[a w] v] RR r Hr. cbn [fst snd]. destruct (RS r Hr) as [X|X]; lia.
      - destruct ST as [[F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12] LBF].
        assert (T : forall (a : Z) (n : nat) bs, 0x80b10 <= a -> a + Z.of_nat n <= 0xb2d30 -> (a + Z.of_nat n <= 0x80ba4 \/ 0xb2d28 <= a) ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor HD. eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm. destruct (RS r Hr) as [X|X]; lia. }
        split; [split|]; (eapply T; [ | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia.
    Qed.

    Lemma stdout_cells_client : forall (a : Z) (n : nat), 0x80b10 <= a -> a + Z.of_nat n <= 0x80ba4 \/ (0xb2d28 <= a /\ a + Z.of_nat n <= 0xb2d30) -> client_cell (a, n, 0).
    Proof. intros a n Ha Hn. unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia. Qed.

    Lemma sto_cagree : forall j m m' LB1 s2 LB2, (j <= 4)%nat -> sto j m -> cagree LB1 m m' -> hs_RHEAP HS s2 LB2 m' -> sto j m'.
    Proof.
      intros j m m' LB1 s2 LB2 Hj ST HP RH. pose proof SPlo. pose proof SPhi. destruct j as [|k]; cbn [sto] in *.
      - eapply (cells_ok_cagree pf1_cells m m' LB1 s2 LB2); [apply pf1_cells_wf | apply (pf1_cells_split 1); lia | | exact ST | exact HP | exact RH].
        eapply Forall_impl; [| apply pf1_cells_range']. intros [[a w] v]. unfold XH_LO. lia.
      - destruct ST as [[F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12] LBF].
        split; [split|]; (eapply rdn_client_cagree; [exact HP | eassumption | apply stdout_cells_client; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia | unfold XH_LO, XH_HI; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia]).
    Qed.

    (* [comment removed for export] *)
    Lemma incb_cagree : forall LB1 m m' b, cagree LB1 m m' -> rdn RSEGS m (Z_to_bv 64 0x90c74) 1 = Some [b] -> rdn RSEGS m' (Z_to_bv 64 0x90c74) 1 = Some [b].
    Proof.
      intros LB1 m m' b HP HD. eapply (rdn_client_cagree LB1 m m' 0x90c74 1); [exact HP | exact HD | unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia | unfold XH_LO; cbn; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma tinv_wblock : forall m (Bk n : Z) bs,
      tinv m -> rblock_range Bk n -> Z.of_nat (length bs) <= n -> tinv (wbytes m (Z_to_bv 64 Bk) bs).
    Proof.
      intros m Bk n bs [INV STK CELLS RELRO XD [t [TID Ht]] ABOVE [B' [AUX HB']] HSm] HBR Hl. pose proof SPlo. pose proof SPhi.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      assert (EB : Z_to_bv 64 Bk = Z_to_bv 64 (Bk + 0)) by (f_equal; lia).
      split.
      - rewrite EB. eapply mem_inv_wbytes_block; [exact INV | exact HBR | lia | lia].
      - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact STK | unfold TR_STACK; lia | lia].
      - eapply cells_ok_wbytes_out; [apply tr_cells_wf | exact CELLS | unorm; lia |].
        eapply Forall_impl; [| apply tr_cells_range]. intros [[a w] v] (Q1 & Q2 & _). unorm. lia.
      - intros i Hi. rewrite MemSplit.wbytes_outside; [apply RELRO; exact Hi | unorm; lia | unorm; lia].
      - intros i Hi. rewrite MemSplit.wbytes_outside; [apply XD; exact Hi | unorm; lia | unorm; lia].
      - exists t. split; [|exact Ht]. eapply rdn_wbytes_out; [exact TID | unorm; lia | unorm; lia | unorm; lia].
      - intros a Ha. rewrite MemSplit.wbytes_outside; [apply ABOVE; exact Ha | unorm; lia | unorm; lia].
      - exists B'. split; [|exact HB']. eapply AUF; [exact AUX | | |].
        + rewrite wbytes_eq, <- wa_eq. apply (munch_write [(Bk, Bk + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
        + rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
        + constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia.
      - eapply HStat_agree; [exact FTL | exact HSm |]. intros a Ha. unfold XH_LO, XH_HI in Ha. rewrite !wa_eq. apply MemSplit.wbytes_outside; unorm; lia.
    Qed.

    Lemma sto0_wblock : forall m (Bk n : Z) bs,
      cells_ok m pf1_cells -> rblock_range Bk n -> Z.of_nat (length bs) <= n -> cells_ok (wbytes m (Z_to_bv 64 Bk) bs) pf1_cells.
    Proof.
      intros m Bk n bs ST HBR Hl. pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      eapply cells_ok_wbytes_out; [apply pf1_cells_wf | exact ST | unorm; lia |].
      eapply Forall_impl; [| apply pf1_cells_range']. intros [[a w] v] [Q1|Q2]; unorm; lia.
    Qed.
    Lemma incb_wblock : forall m (Bk n : Z) bs b,
      rdn RSEGS m (Z_to_bv 64 0x90c74) 1 = Some [b] -> rblock_range Bk n -> Z.of_nat (length bs) <= n ->
      rdn RSEGS (wbytes m (Z_to_bv 64 Bk) bs) (Z_to_bv 64 0x90c74) 1 = Some [b].
    Proof.
      intros m Bk n bs b HD HBR Hl. pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      eapply rdn_wbytes_out; [exact HD | unorm; lia | unorm; lia | unorm; lia].
    Qed.

    Lemma tinv_stk80 : forall m, tinv m -> stk_ok RSEGS m sp 80.
    Proof. intros m TI. pose proof SPlo. pose proof SPhi. eapply stk_stk_ok; [exact (ti_stk _ TI) | unfold TR_STACK; lia | lia | lia | lia]. Qed.
    Lemma tinv_stklo : forall m, tinv m -> stk rsegs m (bv_unsigned sp - TR_STACK) (bv_unsigned sp - 80).
    Proof. intros m TI. destruct (ti_stk _ TI) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. Qed.
    Lemma tinv_ro : forall m, tinv m -> ro_none m.
    Proof. intros m TI. apply mem_inv_ro_none. exact (ti_inv _ TI). Qed.

    (* [comment removed for export] *)
    Lemma lb_remove_perm : forall L p Ak n, List.NoDup (map blk_id L) -> In (p, Ak, n) L ->
      Permutation L ((p, Ak, n) :: hs_lb_remove HS p L).
    Proof.
      destruct LBR as (L1 & L2 & L3).
      induction L as [|b L IH]; intros p Ak n ND HIn; [destruct HIn|].
      inversion ND as [|x l Hni Hnd]; subst.
      destruct HIn as [-> | HIn].
      - rewrite (L1 p Ak n L Hni). apply Permutation_refl.
      - assert (NE : blk_id b <> p).
        { intros E. apply Hni. rewrite E. replace p with (blk_id (p, Ak, n)) by reflexivity. apply in_map. exact HIn. }
        rewrite (L2 p b L NE). eapply Permutation_trans; [apply perm_skip; apply (IH p Ak n Hnd HIn) | apply perm_swap].
    Qed.

    Lemma zero_lines_snoc : forall k, zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10] = zero_lines (S k).
    Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines app]. rewrite IH. reflexivity. Qed.

    Lemma errno_cell_any : forall m, errno_cell m.
    Proof.
      intros m. destruct (errno_rw_any m) as [e [[_ Hb] _]]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
      exists (le4 e). split; [| reflexivity].
      pose proof (bytes_at_rdn rsegs m (0x92650 - 164) (le4 e) 0 4 Hb ltac:(cbn; lia)) as R.
      rewrite rdn_same in R. cbn [firstn skipn le4 word_to_le_bytes] in R |- *. exact R.
    Qed.


    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Section Loop.
      (* [comment removed for export] *)
      Variables (Dz OWz : Z) (cb : list block).
      Hypothesis COPY : (N = 0 /\ Dz = P_FUZZ_EMPTY /\ OWz = 0 /\ cb = [])
                        \/ (1 <= N /\ OWz = Dz /\ exists pD, cb = [(pD, Dz, N)] /\ rblock_range Dz N).
      Let LB0 : list block := cb ++ LB.
      (* [comment removed for export] *)
      Variable K : TSet.
      Hypothesis HPOST : forall regs' mem' model', TRpost HS sp A cap data LB model0 regs0 mem0 regs' mem' model' ->
         realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2addc) mem' (seg_rom RSEGS)) model') K.

      Let HD16 : Dz mod 16 = 0.
      Proof. destruct COPY as [(_ & -> & _) | (_ & _ & pD & _ & (_ & R2 & _))]; [reflexivity | exact R2]. Qed.
      Let HDr : 0 < Dz /\ Dz + N < 2 ^ 47.
      Proof.
        destruct COPY as [(-> & -> & _) | (_ & _ & pD & _ & (R1 & _ & _ & R4 & _))]; [unfold P_FUZZ_EMPTY; lia|].
        hcb. lia.
      Qed.

      Record lstate (k : nat) (r : Z) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (sC : PState) (LBc : list block) : Prop := LS {
        ls_regs  : loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz);
        ls_r     : getr regs 21 = Z_to_bv 64 r;
        ls_k4    : forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr;
        ls_tinv  : tinv m;
        ls_frame : tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23);
        ls_heap  : hs_RHEAP HS sC LBc m;
        ls_perm  : Permutation LBc LB0;
        ls_krel  : hs_KREL HS sC mo;
        ls_mpres : hs_MPRES HS model0 mo;
        ls_copy  : rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds;
        ls_sto   : sto k m;
        ls_incb  : rdn RSEGS m (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0] }.

      Lemma copy_frame : forall m m' rs, rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds ->
        frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds.
      Proof.
        intros m m' rs HC FM RS. destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & _ & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        - replace (Z_to_bv 64 Dz) with (Z_to_bv 64 (Dz + 0)) in HC |- * by (f_equal; lia).
          eapply (rdn_block_tr m m' rs Dz N 0 ds FM RS HBR); [lia | rewrite Hds; lia | exact HC].
      Qed.
      Lemma copy_cagree : forall m m' LBc, Permutation LBc LB0 -> rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds ->
        cagree LBc m m' -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds.
      Proof.
        intros m m' LBc HP HC HPR. destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        - pose proof HBR as (R1 & _ & _ & R4 & R5). hcb.
          rewrite (rdn_ext RSEGS (length ds) m' m); [exact HC | unorm; rewrite Hds; lia |]. intros x Hx. revert Hx. unorm. rewrite Hds. intros Hx.
          rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. apply HPR; [apply u64_range | | unfold XH_LO, XH_HI; lia].
          right. right. exists (pD, Dz, N). split; [| cbn; lia].
          eapply Permutation_in; [apply Permutation_sym; exact HP|]. subst LB0. rewrite Ecb. left. reflexivity.
      Qed.
      Lemma copy_in : forall LBc, Permutation LBc LB0 -> 1 <= N -> exists pD, In (pD, Dz, N) LBc.
      Proof.
        intros LBc HP HN1. destruct COPY as [(N0 & _) | (_ & _ & pD & Ecb & _)]; [lia|]. exists pD.
        eapply Permutation_in; [apply Permutation_sym; exact HP|]. subst LB0. rewrite Ecb. left. reflexivity.
      Qed.
      Lemma LB0_bytes : lb_bytes LB0 <= 2 ^ 26 + 2 ^ 27 /\ Z.of_nat (length LB0) <= 3.
      Proof.
        pose proof (tr_lb1 _ _ _ _ _ _ _ _ _ _ PRE) as [H1 H2]. pose proof HN as HN'. subst LB0.
        destruct COPY as [(_ & _ & _ & ->) | (_ & _ & pD & -> & _)]; cbn [app lb_bytes fold_right length blk_size snd]; fold (lb_bytes LB); lia.
      Qed.

      Let MPtrans : forall mo1 mo2 mo3, hs_MPRES HS mo1 mo2 -> hs_MPRES HS mo2 mo3 -> hs_MPRES HS mo1 mo3.
      Proof. destruct HH as (_ & _ & [_ T] & _). exact T. Qed.
      Let Hfd1 : forall mo, hs_MPRES HS model0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
      Proof. intros mo MP. destruct (hx_mpres HS HX _ _ MP) as [_ E]. rewrite E. exact (tr_fd1 _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let Hfd2 : forall mo, hs_MPRES HS model0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
      Proof. intros mo MP. destruct (hx_mpres HS HX _ _ MP) as [_ E]. rewrite E. exact (tr_fd2 _ _ _ _ _ _ _ _ _ _ PRE). Qed.

      (* [comment removed for export] *)
      Lemma tr_ret : forall regs m mo sC LBf,
        loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz) ->
        (forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr) ->
        tinv m -> tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) ->
        hs_RHEAP HS sC LBf m -> Permutation LBf LB -> hs_KREL HS sC mo -> hs_MPRES HS model0 mo -> sto calls m ->
        rdn RSEGS m (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b030) m (seg_rom RSEGS)) mo) K.
      Proof.
        intros regs m mo sC LBf LR K4 TI TF RH PERM KR MP STO INCB. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        eapply (seg_T8 sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ _ _ _ _ _ _ _ _ K LR (tinv_stk80 m TI) (tinv_ro m TI) (ti_relro m TI) TF).
        intros regs' Q2 Q4 Q10 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q3 K4'.
        rename TI into TI'. rename RH into RH'. rename STO into STO'. rename m into mem'.
        apply HPOST. destruct TI' as [INV STK CELLS RELRO XD TID ABOVE [B' [AUX HB']] HSm].
        pose proof (tr_lb1 _ _ _ _ _ _ _ _ _ _ PRE) as [LB1 LB2].
        destruct calls as [|k'] eqn:EC; [lia|]. cbn [sto] in STO'. destruct STO' as [SA LBF].
        destruct (hx_statics HS HX _ _ _ RH') as (_ & _ & CAN).
        split; try assumption.
        - intros rr Hrr. cbn [In] in Hrr.
          destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
            first [assumption | rewrite K4' by in_solve; apply K4; in_solve].
        - eapply stk_stk_ok; [exact STK | lia | lia | unfold TR_STACK; lia | lia].
        - exists sC, LBf. split; [exact RH'|]. split; [exact KR|]. split; [intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERM | exact Hb]|].
          rewrite (lb_bytes_perm LB LBf PERM), (Permutation_length PERM). split; assumption.
        - exists B'. split; [exact AUX|]. lia.
        - apply mem_inv_ro_none. exact INV.
        - unfold exit_cells. unfold cells_ok. apply Forall_app. split.
          + eapply incl_Forall; [| exact CELLS]. unfold tr_cells. apply incl_appl. apply incl_refl.
          + unfold atexit_one_cells. pose proof (proj1 (Forall_forall _ _) CELLS) as CI.
            repeat apply Forall_cons; try apply Forall_nil.
            1-5: apply CI; rewrite tr_cells_eq; unfold tr_list; in_solve.
            unfold cell_ok. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. exact INCB.
        - change (hdr_calls data) with calls. rewrite EC. cbn [Nat.pred]. exact SA.
        - apply errno_cell_any.
        - exact (proj1 (hx_mpres HS HX _ _ MP)).
        - apply Hfd1. exact MP.
        - apply Hfd2. exact MP.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_free : forall regs m mo sC LBc,
        lstate calls 1 regs m mo sC LBc -> getr regs 19 = Z_to_bv 64 0 ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b014) m (seg_rom RSEGS)) mo) K.
      Proof.
        intros regs m mo sC LBc [LR R21 K4 TI TF RH PERM KR MP CPY STO INCB] R19. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        destruct COPY as [(N0 & ED & EOW & Ecb) | (N1 & EOW & pD & Ecb & HBR)].
        - (* [comment removed for export] *)
          rewrite EOW in LR.
          eapply (seg_T7null sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ K LR R19 R21 (tinv_stk80 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 LR1 K4'.
          eapply (tr_ret regs1 m mo sC LBc); try assumption.
          + rewrite EOW. exact LR1.
          + intros rr Hrr. rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply Permutation_trans; [exact PERM|]. subst LB0. rewrite Ecb. apply Permutation_refl.
        - (* [comment removed for export] *)
          eapply (seg_T7free sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ K LR R19 R21 (tinv_stk80 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q1 Q10 K4'.
          destruct (ti_aux _ TI) as [B' [AUX1 HB']]. destruct (errno_rw m regs1 Q4) as [errv ERR].
          assert (HIn : In (pD, Dz, N) LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM|]; subst LB0; rewrite Ecb; left; reflexivity).
          change (Z_to_bv 64 0x67ed8) with (Z_to_bv 64 RFREE_SYM).
          eapply (free_call HS HH HX regs1 m mo sC LBc pD Dz N (bv_unsigned sp - TR_STACK) B' errv 0x2b030 K Q1);
            [ lia | reflexivity | exact Q4 | rewrite Q10, EOW; reflexivity | exact RH | exact KR | exact HIn
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (tinv_stklo m TI)
            | pose proof HCLO; unfold TR_STACK in *; lia | rewrite Q2, u_small by lia; unfold RFREE_STACK, TR_STACK; lia
            | exact ERR | exact (ti_inv _ TI) |].
          intros regs2 mem2 mo2 s2 KEPT KR2 MP2 INV2 STK2 ERR2 AUX2 HP2 RH2.
          rewrite Q2, u_small in STK2, HP2 by lia.
          pose proof (cagree_of_rheap_pres _ _ _ HP2) as CA2.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          eapply (tr_ret regs2 mem2 mo2 s2 (hs_lb_remove HS pD LBc)).
          + unfold loop_base. rewrite S2, S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold heap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply tinv_cagree; [exact TI | exact CA2 | exact RH2 | exact STK2 | exact INV2 | exact AUX2 | exact HB' | eapply HStat_rheap_pres; [exact (ti_hs _ TI) | exact HP2]].
          + eapply tframe_cagree; [exact TF | exact CA2].
          + exact RH2.
          + pose proof (lb_remove_perm LBc pD Dz N (RND _ _ _ RH) HIn) as P1.
            apply (Permutation_cons_inv (a:=(pD, Dz, N))). eapply Permutation_trans; [apply Permutation_sym; exact P1|].
            eapply Permutation_trans; [exact PERM|]. subst LB0. rewrite Ecb. apply Permutation_refl.
          + exact KR2.
          + eapply MPtrans; [exact MP | exact MP2].
          + eapply sto_cagree; [lia | exact STO | exact CA2 | exact RH2].
          + eapply incb_cagree; [exact CA2 | exact INCB].
      Qed.

      Let LIVE : 2 ^ 31 <= hs_LIVE_MAX HS /\ 2103 <= hs_LIVE_CNT_MAX HS. Proof. exact (hx_live HS HX). Qed.

      (* [comment removed for export] *)
      Lemma tr_call_harness : forall k r regs m mo sC LBc (Kx : TSet),
        (k <= 4)%nat -> lstate k r regs m mo sC LBc ->
        (forall regs' m' mo' sC' LBc', lstate k r regs' m' mo' sC' LBc' ->
           getr regs' 1 = Z_to_bv 64 0x2b014 -> getr regs' 11 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b0c0) m' (seg_rom RSEGS)) mo') Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2aff0) m (seg_rom RSEGS)) mo) Kx.
      Proof.
        intros k r regs m mo sC LBc Kx Hk [LR R21 K4 TI TF RH PERM KR MP CPY STO INCB] HK. pose proof SPlo. pose proof SPhi.
        pose proof LIVE as [LV1 LV2]. pose proof LB0_bytes as [LBB LBL]. pose proof HN as HN'.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        eapply (seg_T5 sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ (getr regs 19) _ Kx LR eq_refl R21 (tinv_stk80 m TI) (tinv_ro m TI) (ti_relro m TI)).
        intros regs1 mem1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q19 Q21 Q1 Q10 Q11 K4a FM1 STK1 INCB1.
        assert (RS1 : forall rr, In rr (regTc_w sp) -> tr_region rr).
        { intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold tr_region, TR_STACK.
          destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        assert (RQ1 : forall rr, In rr (regTc_w sp) -> quiet_region rr).
        { intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold quiet_region, TR_STACK.
          destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        assert (TI1 : tinv mem1) by (eapply tinv_frame; [exact TI | exact FM1 | exact RS1]).
        assert (RH1 : hs_RHEAP HS sC LBc mem1) by (eapply heap_frame_tr; [exact RH | exact FM1 | exact RS1]).
        assert (TF1 : tframe sp mem1 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply tframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM1). apply outside_of_disjoint.
          intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        assert (CPY1 : rdn RSEGS mem1 (Z_to_bv 64 Dz) (length ds) = Some ds) by (eapply copy_frame; [exact CPY | exact FM1 | exact RS1]).
        assert (STO1 : sto k mem1) by (eapply sto_frame; [exact Hk | exact STO | exact FM1 | exact RQ1]).
        destruct (ti_aux _ TI1) as [B' [AUX1 HB']]. destruct (errno_rw mem1 regs1 Q4) as [errv ERR].
        destruct (hx_statics HS HX _ _ _ RH1) as (NL1 & GOT1 & [can1 CAN1]).
        change (Z_to_bv 64 0x2b3e0) with (Z_to_bv 64 P_FUZZ_ENTRY).
        eapply (fuzz_call regs1 mem1 mo sC LBc Dz N (bv_unsigned sp - TR_STACK) B' ds errv 0x2b004 Kx Q1);
          [ lia | reflexivity | exact Q4 | exact Q10 | exact Q11
          | apply rdn_bytes_at; [exact CPY1 | lia | rewrite Hds; lia] | rewrite Hds; lia | lia | exact HD16
          | intros HN1; exact (copy_in LBc PERM HN1)
          | intros HN0; destruct COPY as [(_ & ED & _) | (HN1 & _)]; [exact ED | lia]
          | exact RH1 | exact KR
          | rewrite (lb_bytes_perm LB0 LBc PERM); unfold FUZZ_LIVE2; lia
          | rewrite (Permutation_length PERM); unfold FUZZ_CNT; lia
          | exact AUX1 | rewrite Q2, u_small by lia; lia | lia
          | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite Q2, u_small by lia; exact (tinv_stklo mem1 TI1)
          | pose proof HCLO; unfold TR_STACK in *; lia
          | rewrite Q2, u_small by lia; unfold FUZZ_STACK, TR_STACK; lia
          | exact ERR | exact (ti_inv _ TI1) | exact (XImg_of_tinv _ TI1)
          | split; [exact GOT1 | exists can1; exact (proj1 CAN1)]
          | exact (ti_hs _ TI1)
          | rewrite Q2, u_small by lia; pose proof SPhi; unfold TR_STACK in *; lia |].
        intros regs2 mem2 mo2 s2 LB2 errv2 KEPT A0 KR2 MP2 INV2 STK2 ERR2 AUX2 RH2 PERM2 HS2 X2.
        rewrite Q2, u_small in STK2, X2 by lia.
        pose proof (cagree_of_xpres _ _ _ X2) as CA2.
        destruct (KRELh s2 mo2 KR2) as [Hh2 Hlazy2].
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
        pose proof (KEPT 21%bv ltac:(in_solve)) as S21. pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
        assert (LR2 : loop_base sp regs2 (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz)).
        { unfold loop_base. rewrite S2, S4, S8, S9, S18, S20, S22, S23. repeat split; assumption. }
        assert (TI2 : tinv mem2) by (eapply tinv_cagree; [exact TI1 | exact CA2 | exact RH2 | exact STK2 | exact INV2 | exact AUX2 | exact HB' | exact HS2]).
        eapply (seg_T6 sp mo2 SP16 SPlo SPhi Hh2 Hlazy2 regs2 mem2 _ _ _ _ Kx LR2 ltac:(rewrite S21; exact Q21) A0 (tinv_stk80 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
        intros regs3 mem3 LR3 T19 T21 T1 T11 K4b FM3 STK3 INCB3.
        assert (RS3 : forall rr, In rr (regTc_w sp) -> tr_region rr) by exact RS1.
        apply (HK regs3 mem3 mo2 s2 LB2); [| exact T1 | exact T11 | exact T19].
        split; try assumption.
        - intros rr Hrr. rewrite (K4b rr Hrr), (KEPT rr) by (unfold fuzz_kept; in_from Hrr). rewrite (K4a rr Hrr). apply K4. exact Hrr.
        - eapply tinv_frame; [exact TI2 | exact FM3 | exact RS3].
        - eapply tframe_agree; [eapply tframe_cagree; [exact TF1 | exact CA2]|]. intros x Hx. apply (proj1 FM3). apply outside_of_disjoint.
          intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia.
        - eapply heap_frame_tr; [exact RH2 | exact FM3 | exact RS3].
        - eapply Permutation_trans; [exact PERM2 | exact PERM].
        - eapply MPtrans; [exact MP | exact MP2].
        - eapply copy_frame; [eapply copy_cagree; [exact PERM | exact CPY1 | exact CA2] | exact FM3 | exact RS3].
        - eapply sto_frame; [exact Hk | eapply sto_cagree; [exact Hk | exact STO1 | exact CA2 | exact RH2] | exact FM3 | exact RQ1].
      Qed.

      Ltac pf_region Hr :=
        cbn [In] in Hr;
        repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
        unfold tr_region, TR_STACK; cbn [fst snd]; rewrite ?u_small by lia; lia.

      (* [comment removed for export] *)
      Lemma tr_printf_buf : forall k r regs m mo sC LBc (Kx : TSet),
        (1 <= k <= 3)%nat -> lstate k r regs m mo sC LBc ->
        getr regs 1 = Z_to_bv 64 0x2b014 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 ->
        (forall regs' m', lstate (S k) r regs' m' mo sC LBc -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b014) m' (seg_rom RSEGS)) mo) Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b0c0) m (seg_rom RSEGS)) mo) Kx.
      Proof.
        intros k r regs m mo sC LBc Kx Hk [LR R21 K4 TI TF RH PERM KR MP CPY STO INCB] R1 R11 R19 HK. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy]. destruct k as [|k']; [lia|]. cbn [sto] in STO. destruct STO as [SA LBF].
        destruct SA as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12].
        destruct (hx_statics HS HX _ _ _ RH) as (_ & GOT & [can [CAN CAN64]]).
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        set (w := 0xb2d28 + 2 * Z.of_nat k').
        assert (PH : pfH m (Z_to_bv 64 (bv_unsigned sp - 80)) w can).
        { split; rewrite ?u_small by lia; try assumption; try (subst w; lia).
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - eapply stk_stk_ok; [exact (ti_stk _ TI) | unfold PF_FR, TR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold PF_FR; lia | lia].
          - apply mem_inv_ro_none. exact (ti_inv _ TI). }
        destruct (printf0_buffered regs m (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp - 80)) w can PH R1 ltac:(exact Q2) R11)
          as (regs' & mem' & RUN & KCS & FM & BY & WP & FL).
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
        rewrite u_small in FM by lia.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1056), 1056); (Z_to_bv 64 0x80b10, 4); (Z_to_bv 64 0x80b38, 8); (Z_to_bv 64 w, 2)] -> tr_region rr).
        { intros rr Hr. subst w. pf_region Hr. }
        assert (T : forall (a : Z) (n : nat) bs, 0x80b14 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                  (a + Z.of_nat n <= 0x80b38 \/ 0x80b40 <= a) -> a + Z.of_nat n <= w ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS mem' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor Hw HD. eapply rdn_frame; [exact FM | exact HD | unorm; lia |].
          intros rr Hr. unorm. subst w. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        apply HK.
        - split.
          + unfold loop_base. rewrite !(KCS _) by (unfold callee_saved; in_solve). exact LR.
          + rewrite (KCS _) by (unfold callee_saved; in_solve). exact R21.
          + intros rr Hrr. rewrite (KCS rr) by (unfold callee_saved; in_from Hrr). apply K4. exact Hrr.
          + eapply tinv_frame; [exact TI | exact FM | exact RS].
          + eapply tframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM). apply outside_of_disjoint.
            intros rr Hr. subst w. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply heap_frame_tr; [exact RH | exact FM | exact RS].
          + exact PERM. + exact KR. + exact MP.
          + eapply copy_frame; [exact CPY | exact FM | exact RS].
          + cbn [sto]. split; [split|].
            * exact FL.
            * eapply T; [ | | | | exact F2]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F3]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F4]; subst w; cbn; lia.
            * replace (0xb2d28 + 2 * Z.of_nat (S k')) with (w + 2) by (subst w; lia). exact WP.
            * eapply T; [ | | | | exact F6]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F7]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F8]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F9]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F10]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F11]; subst w; cbn; lia.
            * rewrite <- zero_lines_snoc. replace (2 * S k')%nat with (2 * k' + 2)%nat by lia.
              apply rdn_app_Z; [ | | lia | lia].
              -- eapply rdn_frame; [exact FM | exact F12 | unorm; lia |].
                 intros rr Hr. unorm. subst w. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
              -- replace (0xb2d28 + Z.of_nat (2 * k')) with w by (subst w; lia). exact BY.
            * eapply T; [ | | | | exact LBF]; subst w; cbn; lia.
          + eapply T; [ | | | | exact INCB]; subst w; cbn; lia.
        - rewrite (KCS _) by (unfold callee_saved; in_solve). exact R19.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_printf_first : forall r regs m mo sC LBc (Kx : TSet),
        lstate 0 r regs m mo sC LBc ->
        getr regs 1 = Z_to_bv 64 0x2b014 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 -> Kx [] ->
        (forall regs' m', lstate 1 r regs' m' mo sC LBc -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2b014) m' (seg_rom RSEGS)) mo) Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b0c0) m (seg_rom RSEGS)) mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) Kx).
      Proof.
        intros r regs m mo sC LBc Kx [LR R21 K4 TI TF RH PERM KR MP CPY STO INCB] R1 R11 R19 K0 HK. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy]. cbn [sto] in STO.
        destruct (hx_statics HS HX _ _ _ RH) as (_ & GOT & [can [CAN CAN64]]).
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        assert (PH : p1H regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can).
        { split; rewrite ?u_small by lia; try assumption; try lia.
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - eapply stk_stk_ok; [exact (ti_stk _ TI) | unfold TR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
          - apply mem_inv_ro_none. exact (ti_inv _ TI). }
        unfold W. cbn [map].
        apply (printf0_first mo Hh Hlazy (Hfd1 mo MP) regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can Kx PH K0).
        intros regs' mem' PP. destruct PP. rewrite u_small in P_frame by lia.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1232), 1232); (Z_to_bv 64 0x80b10, 232); (Z_to_bv 64 0xb2d28, 1)] -> tr_region rr).
        { intros rr Hr. pf_region Hr. }
        apply HK.
        - split.
          + unfold loop_base. rewrite (P_cs 4%bv), (P_cs 8%bv), (P_cs 9%bv), (P_cs 18%bv), (P_cs 20%bv), (P_cs 22%bv), (P_cs 23%bv) by in_solve. rewrite P_sp. split; [reflexivity | exact (proj2 LR)].
          + rewrite (P_cs _) by in_solve. exact R21.
          + intros rr Hrr. rewrite (P_cs rr) by (in_from Hrr). apply K4. exact Hrr.
          + eapply tinv_frame; [exact TI | exact P_frame | exact RS].
          + eapply tframe_agree; [exact TF|]. intros x Hx. apply (proj1 P_frame). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply heap_frame_tr; [exact RH | exact P_frame | exact RS].
          + exact PERM. + exact KR. + exact MP.
          + eapply copy_frame; [exact CPY | exact P_frame | exact RS].
          + cbn [sto]. split; [split|]; try assumption; first [reflexivity | replace (0xb2d28 + 2 * Z.of_nat 0) with 0xb2d28 by lia; exact P_wpos].
          + eapply rdn_frame; [exact P_frame | exact INCB | unorm; lia |].
            intros rr Hr. unorm. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
        - rewrite (P_cs _) by in_solve. exact R19.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_after_printf : forall (rn k : nat) regs m mo sC LBc,
        (1 <= rn)%nat -> (k + rn = calls + 1)%nat -> (1 <= k)%nat ->
        lstate k (Z.of_nat rn) regs m mo sC LBc -> getr regs 19 = Z_to_bv 64 0 ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2b014) m (seg_rom RSEGS)) mo) K.
      Proof.
        induction rn as [|rn IH]; intros k regs m mo sC LBc Hrn Hk Hk1 LS R19; [lia|].
        pose proof Hcalls as HC. pose proof SPlo. pose proof SPhi.
        destruct rn as [|rn'].
        - (* [comment removed for export] *) assert (Ek : k = calls) by lia. subst k. eapply tr_free; [exact LS | exact R19].
        - destruct LS as [LR R21 K4 TI TF RH PERM KR MP CPY STO INCB]. destruct (KRELh sC mo KR) as [Hh Hlazy].
          eapply (seg_T7more sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ (Z.of_nat (S (S rn'))) K LR R19 R21 ltac:(lia)
                    (tinv_stk80 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 LR1 Q19 Q21 K4a.
          replace (Z.of_nat (S (S rn')) - 1) with (Z.of_nat (S rn')) in Q21 by lia.
          assert (LS1 : lstate k (Z.of_nat (S rn')) regs1 m mo sC LBc).
          { split; try assumption. intros rr Hrr. rewrite (K4a rr Hrr). apply K4. exact Hrr. }
          eapply (tr_call_harness k _ regs1 m mo sC LBc K ltac:(lia) LS1).
          intros regs2 m2 mo2 sC2 LBc2 LS2 T1 T11 T19.
          eapply (tr_printf_buf k _ regs2 m2 mo2 sC2 LBc2 K ltac:(lia) LS2 T1 T11 T19).
          intros regs3 m3 LS3 U19.
          eapply (IH (S k)); [lia | lia | lia | exact LS3 | exact U19].
      Qed.

      (* [comment removed for export] *)
      Lemma tr_loop : forall regs m mo sC LBc,
        lstate 0 (Z.of_nat calls) regs m mo sC LBc -> K [] ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2aff0) m (seg_rom RSEGS)) mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
      Proof.
        intros regs m mo sC LBc LS K0.
        eapply (tr_call_harness 0 _ regs m mo sC LBc _ ltac:(lia) LS).
        intros regs2 m2 mo2 sC2 LBc2 LS2 T1 T11 T19.
        eapply (tr_printf_first _ regs2 m2 mo2 sC2 LBc2 K LS2 T1 T11 T19 K0).
        intros regs3 m3 LS3 U19.
        eapply (tr_after_printf calls 1); [lia | lia | lia | exact LS3 | exact U19].
      Qed.
    End Loop.


    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Let MPrefl : forall mo, hs_MPRES HS mo mo.
    Proof. destruct HH as (_ & _ & [R _] & _). exact R. Qed.

    Lemma calls_of_hdr : forall c, nth 2 data (Z_to_bv 8 0) = c -> Z.of_nat calls = calls_of cfg c.
    Proof.
      intros c Hc. subst calls cfg. unfold hdr_calls, calls_of, hdr_b. rewrite Hc. pose proof (hdr_cfg_range data) as HR.
      pose proof (bv_unsigned_in_range 8 c) as H8. unfold bv_modulus in H8. cbn in H8.
      destruct (Z.eqb_spec (hdr_cfg data) 0) as [E|E].
      - rewrite E. reflexivity.
      - destruct (Z.to_nat (hdr_cfg data)) eqn:EN; [lia|].
        replace (Z.land (bv_unsigned c) 3) with (bv_unsigned c mod 4)%Z by (symmetry; apply (Z.land_ones (bv_unsigned c) 2); lia).
        pose proof (Z.mod_pos_bound (bv_unsigned c) 4 ltac:(lia)). lia.
    Qed.

    Lemma bss_byte0 : forall a : Z, 0x90c70 <= a < 0x90c90 -> seg_rom RSEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
    Proof.
      intros a Ha.
      assert (E : exists k : nat, (k < 32)%nat /\ a = 0x90c70 + Z.of_nat k) by (exists (Z.to_nat (a - 0x90c70)); lia).
      destruct E as (k & Hk & ->).
      do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma munch_agree : forall W m m' (a : Z), munch W m m' -> 0 <= a < 2 ^ 64 -> Lib.Frame.outside W a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
    Proof. intros W m m' a MU Ha OUT. rewrite <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. exact OUT. Qed.

    Variable K : TSet.
    Hypothesis K0 : K [].
    Hypothesis HPOST : forall regs' mem' model', TRpost HS sp A cap data LB model0 regs0 mem0 regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2addc) mem' (seg_rom RSEGS)) model') K.

    Theorem target_run_ok :
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x2af38) mem0 (seg_rom RSEGS)) model0) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof HN as HN'. pose proof Hcfg as Hcfg'. pose proof Hcalls as HC.
      pose proof PRE as PRE'.
      destruct PRE' as [R1 R2 R4 R10 R11 R12 R13 L6 LHI _ _ _ STK STKC RH KR BLK [LB1 LB2] AUX CAP DATA RO INV CELLS PF1 REL XD XHP AXP HEXFLAG TID ERRC CAN Hh Hlazy FD1 FD2].
      hcb.
      (* [comment removed for export] *)
      apply in_map_iff in BLK. destruct BLK as ([[pb Ab] capb] & Eb & HbLB). cbn in Eb. injection Eb as E1 E2. subst Ab capb.
      pose proof (RBR _ _ _ _ RH HbLB) as HBRb. cbn [blk_addr blk_size fst snd] in HBRb.
      pose proof HBRb as (B1 & B2 & B3 & B4 & B5). clear B2.
      set (c := nth 2 data (Z_to_bv 8 0)).
      pose proof (calls_of_hdr c eq_refl) as ECALLS.
      assert (LATCH0 : rdn RSEGS mem0 (Z_to_bv 64 0x90c70) 1 = Some [Z_to_bv 8 0]).
      { apply rdn1_zero; [apply HEXFLAG; lia | apply bss_byte0; lia]. }
      assert (STK0 : stk_ok RSEGS mem0 sp 80) by (eapply stk_stk_ok; [exact STKC | unfold TR_STACK; lia | lia | lia | lia]).
      (* [comment removed for export] *)
      eapply (seg_T0b sp model0 SP16 SPlo SPhi Hh Hlazy regs0 mem0 (Z_to_bv 64 CP) (Z_to_bv 64 cfg) (Z_to_bv 64 PL) (Z_to_bv 64 N) _ R1 R2 R4 R10 R11 R12 R13 LATCH0 STK0 RO REL).
      intros regs1 mem1 LR1 Q1 Q10 K4a FM1 STK1 TF1 LATCH1.
      pose proof FM1 as [Hout1 Hg1].
      assert (OUT1 : forall a : Z, 0 <= a < 2 ^ 64 -> (a < 0x90c70 \/ (0x90c71 <= a /\ a < bv_unsigned sp - 80) \/ bv_unsigned sp <= a) -> mem1 (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
      { intros a Ha Hra. apply Hout1. apply outside_of_disjoint. intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite !u_small by lia; lia. }
      assert (Q1r : forall r, In r (regTb_w sp) -> quiet_region r).
      { intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr. unfold quiet_region, TR_STACK.
        destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (RH1 : hs_RHEAP HS ps LB mem1) by (eapply heap_frame_tr; [exact RH | exact FM1 | intros r Hr; apply quiet_tr; apply Q1r; exact Hr]).
      assert (INV1 : mem_inv rsegs mem1).
      { eapply mem_inv_frame; [exact INV | exact FM1 |]. apply Forall_forall. intros r Hr. pose proof (u64_range (fst r)).
        unfold regTb_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (STKC1 : stk rsegs mem1 (bv_unsigned sp - TR_STACK) (bv_unsigned sp)) by (apply (stk_grows sp mem0 mem1); [exact STKC | unfold TR_STACK; lia | exact Hg1]).
      assert (ST0 : sto 0 mem1) by (eapply (sto_frame 0); [lia | exact PF1 | exact FM1 | exact Q1r]).
      assert (DATA1 : rdn RSEGS mem1 (Z_to_bv 64 A) (length data) = Some data).
      { replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) in DATA |- * by (f_equal; lia).
        eapply (rdn_block_tr mem0 mem1 _ A cap 0 data FM1); [intros r Hr; apply quiet_tr; apply Q1r; exact Hr | exact HBRb | lia | lia | exact DATA]. }
      pose proof LR1 as (V2 & V4 & V8 & V9 & V18 & V19 & V20).
      (* [comment removed for export] *)
      assert (AX1 : rw_cells rsegs mem1 A_ATEXIT atexit_cells0).
      { apply atexit_cells_initial. intros a Ha. rewrite wa_eq. rewrite OUT1; [apply AXP; lia | lia | lia]. }
      destruct (hx_statics HS HX _ _ _ RH1) as (NL1 & GOT1 & [can1 CAN1]).
      assert (NLB : bytes_at rsegs mem1 A_NEED_LOCKS [b8 0]) by (apply (rdn_bytes_at [b8 0] mem1 A_NEED_LOCKS); [exact NL1 | unfold A_NEED_LOCKS; lia | unfold A_NEED_LOCKS; cbn; lia]).
      destruct (stk_split rsegs mem1 _ (bv_unsigned sp - 80) _ STKC1 ltac:(unfold TR_STACK; lia)) as [STlo1 SThi1].
      change (Z_to_bv 64 0x67760) with (Z_to_bv 64 P_ATEXIT).
      eapply (atexit_call regs1 mem1 model0 0x2b090 0 0 0 (bv_unsigned sp - TR_STACK) (zeros 3) (zeros 4) (zeros 248) (zeros 248) 0x2afcc _ Hh Hlazy Q1
                ltac:(lia) ltac:(reflexivity) Q10 ltac:(lia));
        [ exact AX1 | exact NLB | rewrite V2, u_small by lia; exact STlo1 | rewrite V2, u_small by lia; unfold ATEXIT_FRAME, TR_STACK; lia
        | unfold TR_STACK; lia | exact INV1 |].
      intros regs2 mem2 KEPT2 A0 MU2 WM2 INV2 ST2 AX2.
      rewrite V2, u_small in MU2, ST2 by lia.
      (* [comment removed for export] *)
      assert (OUT2 : forall a : Z, 0 <= a < 2 ^ 64 -> (a < 0xb26a0 \/ (0xb28c0 <= a /\ a < bv_unsigned sp - TR_STACK) \/ bv_unsigned sp - 80 <= a) -> mem2 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
      { intros a Ha Hra. eapply munch_agree; [exact MU2 | exact Ha |]. unfold A_ATEXIT, TR_STACK in *. cbn. lia. }
      pose proof (atexit_cells_fix mem2 AX2) as AXC2. pose proof (proj1 (Forall_forall _ _) AXC2) as CIx.
      pose proof (proj1 (Forall_forall _ _) CELLS) as CI0.
      assert (TI2 : tinv mem2).
      { split.
        - exact INV2.
        - destruct ST2 as (P1 & P2 & P3). destruct STKC1 as (_ & P5 & P6). split; [exact P1|]. split; [exact P5|].
          intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply P3; lia|].
          assert (E : mem2 (wa a) = mem1 (wa a)) by (rewrite !wa_eq; apply OUT2; unfold TR_STACK; lia).
          unfold wview, mrd. rewrite E. apply P6. lia.
        - rewrite tr_cells_eq. unfold tr_list, cells_ok.
          repeat apply Forall_cons; try apply Forall_nil.
          all: first [ solve [apply CIx; unfold atexit_fix_cells; in_solve]
                     | eapply cell_ok_agree; [reflexivity | intros i Hi; rewrite OUT2; [apply OUT1; [lia | unfold TR_STACK in *; lia] | lia | unfold TR_STACK in *; lia] | solve [apply CI0; unfold diag_cells; in_solve] ] ].
        - intros i Hi. rewrite OUT2, OUT1; [apply REL; exact Hi | lia | lia | lia | unfold TR_STACK; lia].
        - intros i Hi. rewrite OUT2, OUT1; [apply XD; exact Hi | lia | lia | lia | unfold TR_STACK; lia].
        - destruct TID as [t [Ht1 Ht2]]. exists t. split; [|exact Ht2].
          rewrite (rdn_ext RSEGS 4 mem2 mem0); [exact Ht1 | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
          rewrite <- (Z_to_bv_bv_unsigned x). rewrite OUT2, OUT1; [reflexivity | apply u64_range | lia | apply u64_range | unfold TR_STACK; lia].
        - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). rewrite OUT2, OUT1; [reflexivity | apply u64_range | lia | apply u64_range | unfold TR_STACK; lia].
        - destruct AUX as [B' [AUX0 HB']]. exists B'. split; [|exact HB'].
          eapply AUF; [eapply AUF; [exact AUX0 | apply frame_mod_munch; exact FM1 | exact (frame_mod_wmono _ _ _ FM1) |] | exact MU2 | exact WM2 |].
          + apply Forall_forall. intros iv Hiv. unfold ivls, regTb_w in Hiv. cbn [map In fst snd] in Hiv. unfold RAUXV_CELL.
            destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + unfold A_ATEXIT, RAUXV_CELL, TR_STACK. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
        - apply HStat_initial. intros a Ha. unfold XH_LO, XH_HI in Ha. rewrite wa_eq. rewrite OUT2, OUT1; [apply XHP; lia | lia | lia | lia | unfold TR_STACK; lia]. }
      assert (RH2 : hs_RHEAP HS ps LB mem2).
      { eapply RFR; [exact RH1 | exact MU2 | exact WM2 |]. unfold rclient_write_ok, A_ATEXIT, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK, TR_STACK.
        apply Forall_cons; [left; cbn [fst]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_nil. }
      assert (TF2 : tframe sp mem2 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
      { eapply tframe_agree; [exact TF1|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply OUT2; [apply u64_range | lia]. }
      assert (ST02 : sto 0 mem2).
      { cbn [sto] in ST0 |- *. eapply cells_ok_agree; [apply pf1_cells_wf | | exact ST0].
        unfold cells_agree. eapply Forall_impl; [|apply pf1_cells_range']. intros [[a w] v] Hr i Hi. apply OUT2; [lia | unfold TR_STACK; lia]. }
      assert (DATA2 : rdn RSEGS mem2 (Z_to_bv 64 A) (length data) = Some data).
      { rewrite (rdn_ext RSEGS (length data) mem2 mem1); [exact DATA1 | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
        rewrite <- (Z_to_bv_bv_unsigned x). apply OUT2; [apply u64_range | unfold TR_STACK; lia]. }
      assert (INCB2 : rdn RSEGS mem2 (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0]).
      { apply rdn1_zero; [| apply bss_byte0; lia]. rewrite OUT2, OUT1; [apply HEXFLAG; lia | lia | lia | lia | unfold TR_STACK; lia]. }
      pose proof (KEPT2 2%bv ltac:(in_solve)) as W2. pose proof (KEPT2 4%bv ltac:(in_solve)) as W4. pose proof (KEPT2 8%bv ltac:(in_solve)) as W8.
      pose proof (KEPT2 9%bv ltac:(in_solve)) as W9. pose proof (KEPT2 18%bv ltac:(in_solve)) as W18. pose proof (KEPT2 19%bv ltac:(in_solve)) as W19.
      pose proof (KEPT2 20%bv ltac:(in_solve)) as W20.
      assert (LR2 : regs118 sp regs2 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 cfg) (Z_to_bv 64 CP)).
      { unfold regs118. rewrite W2, W4, W8, W9, W18, W19, W20. exact LR1. }
      clear AX1 AX2 NLB STlo1 SThi1.
      (* [comment removed for export] *)
      eapply (seg_TA sp model0 SP16 SPlo SPhi Hh Hlazy regs2 mem2 _ _ _ _ _ LR2 A0 (tinv_stk80 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
      intros regs3 LR3 K4c.
      assert (K4_3 : forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs3 rr = getr regs0 rr).
      { intros rr Hrr. rewrite (K4c rr Hrr), (KEPT2 rr) by (unfold leaf_kept; in_from Hrr). apply K4a. exact Hrr. }
      assert (HC3 : cfg <> 0 -> rdn RSEGS mem2 (Z_to_bv 64 CP) 1 = Some [c]).
      { intros _. subst c CP. pose proof (rdn_nth RSEGS mem2 (length data) (Z_to_bv 64 A) data 2 DATA2 ltac:(lia)) as R.
        unfold nat_to_word in R. rewrite Z_to_bv_add64 in R. exact R. }
      clear RH RH1 DATA DATA1 INV1 STKC1 ST0 TF1 CELLS.
      destruct (Z.eq_dec N 0) as [N0|N1].
      - (* [comment removed for export] *)
        rewrite N0 in LR3.
        eapply (seg_T1zero sp model0 SP16 SPlo SPhi Hh Hlazy regs3 mem2 cfg _ _ c _ LR3 ltac:(lia) HC3 ltac:(subst CP; rewrite u_small by lia; lia)
                  (tinv_stk80 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
        intros regs4 LR4 Q21 Q19 K4d.
        eapply (tr_loop P_FUZZ_EMPTY 0 [] ltac:(left; repeat split; lia) K HPOST regs4 mem2 model0 ps LB); [| exact K0].
        split; try assumption.
        + rewrite N0. exact LR4.
        + rewrite ECALLS. exact Q21.
        + intros rr Hrr. rewrite (K4d rr Hrr). apply K4_3. exact Hrr.
        + apply Permutation_refl.
        + apply MPrefl.
        + assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
      - (* [comment removed for export] *)
        eapply (seg_T1pos sp model0 SP16 SPlo SPhi Hh Hlazy regs3 mem2 N cfg _ _ c _ LR3 ltac:(lia) ltac:(lia) HC3 ltac:(subst CP; rewrite u_small by lia; lia)
                  (tinv_stk80 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
        intros regs4 LR4 Q21 K4d.
        eapply (seg_T2 sp model0 SP16 SPlo SPhi Hh Hlazy regs4 mem2 _ _ _ _ _ _ LR4 Q21 (tinv_stk80 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
        intros regs5 LR5 U21 U1 U10 K4e.
        pose proof LR5 as (X2 & X4 & X8 & X9 & X18 & X19 & X20).
        destruct (ti_aux _ TI2) as [B' [AUX2 HB']]. destruct (errno_rw mem2 regs5 X4) as [errv ERR].
        pose proof (hx_live HS HX) as [LV1 LV2].
        change (Z_to_bv 64 0x68018) with (Z_to_bv 64 RMALLOC_SYM).
        eapply (malloc_call HS HH HX regs5 mem2 model0 ps LB N (bv_unsigned sp - TR_STACK) B' errv 0x2af9c _ U1);
          [ lia | reflexivity | exact X4 | exact U10 | lia | exact RH2 | exact KR
          | apply (AOK ps LB mem2 N RH2); lia
          | exact AUX2 | rewrite X2, u_small by lia; lia
          | rewrite X2, u_small by lia; exact (tinv_stklo mem2 TI2)
          | unfold TR_STACK in *; lia | rewrite X2, u_small by lia; unfold RMALLOC_STACK, TR_STACK; lia
          | exact ERR | exact (ti_inv _ TI2) |].
        intros regs6 mem6 mo6 D pD s6 errv6 junk KEPT6 Y10 KR6 MP6 INV6 STK6 ERR6 AUX6 HP6 HBR6 RH6 CB6.
        rewrite X2, u_small in STK6, HP6 by lia.
        pose proof (cagree_of_rheap_pres _ _ _ HP6) as CA6.
        destruct (KRELh s6 mo6 KR6) as [Hh6 Hlazy6].
        pose proof HBR6 as (C1 & C2 & C3 & C4 & C5).
        assert (TI6 : tinv mem6) by (eapply tinv_cagree; [exact TI2 | exact CA6 | exact RH6 | exact STK6 | exact INV6 | exact AUX6 | exact HB' | eapply HStat_rheap_pres; [exact (ti_hs _ TI2) | exact HP6]]).
        assert (TF6 : tframe sp mem6 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)) by (eapply tframe_cagree; [exact TF2 | exact CA6]).
        assert (ST6 : sto 0 mem6) by (eapply (sto_cagree 0); [lia | exact ST02 | exact CA6 | exact RH6]).
        assert (INCB6 : rdn RSEGS mem6 (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0]) by (eapply incb_cagree; [exact CA6 | exact INCB2]).
        assert (DATA6 : rdn RSEGS mem6 (Z_to_bv 64 A) (length data) = Some data).
        { eapply (rdn_rheap_pres (Z_to_bv 64 (bv_unsigned sp + 48)) LB mem2 mem6 A (length data) data);
            [rewrite u_small by lia; replace (bv_unsigned sp + 48 - 128) with (bv_unsigned sp - 80) by lia; exact HP6 | exact DATA2 | lia | lia |].
          intros i Hi. exists (pb, A, cap). split; [exact HbLB | cbn; lia]. }
        (* [comment removed for export] *)
        pose proof (KEPT6 2%bv ltac:(in_solve)) as S2. pose proof (KEPT6 4%bv ltac:(in_solve)) as S4. pose proof (KEPT6 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT6 9%bv ltac:(in_solve)) as S9. pose proof (KEPT6 18%bv ltac:(in_solve)) as S18. pose proof (KEPT6 19%bv ltac:(in_solve)) as S19.
        pose proof (KEPT6 20%bv ltac:(in_solve)) as S20. pose proof (KEPT6 21%bv ltac:(in_solve)) as S21.
        assert (LR6 : regs118 sp regs6 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 cfg) (Z_to_bv 64 CP)).
        { unfold regs118. rewrite S2, S4, S8, S9, S18, S19, S20. exact LR5. }
        eapply (seg_T3 sp mo6 SP16 SPlo SPhi Hh6 Hlazy6 regs6 mem6 _ _ _ _ _ (Z_to_bv 64 D) _ LR6 ltac:(rewrite S21; exact U21) Y10 ltac:(rewrite u_small by lia; lia)
                  (tinv_stk80 mem6 TI6) (tinv_ro mem6 TI6) (ti_relro mem6 TI6)).
        intros regs7 LR7 Z21 Z1 Z10 Z11 Z12 K4f.
        (* [comment removed for export] *)
        assert (DISJ : D + N <= A \/ A + cap <= D).
        { assert (Hp : pD <> pb).
          { intros E. subst pD. pose proof (RND _ _ _ RH6) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l Hni Hnd]; subst.
            apply Hni. replace pb with (blk_id (pb, A, cap)) by reflexivity. apply in_map. exact HbLB. }
          pose proof (RBD _ _ _ (pD, D, N) (pb, A, cap) RH6 ltac:(left; reflexivity) ltac:(right; exact HbLB) Hp) as DJ.
          cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
        assert (SRC : rdn RSEGS mem6 (Z_to_bv 64 PL) (length ds) = Some ds).
        { subst ds PL. rewrite Hds.
          pose proof (rdn_skipn RSEGS mem6 (length data) (Z_to_bv 64 A) data (Z.to_nat (6 + cfg)) DATA6 ltac:(lia)) as R.
          unfold nat_to_word in R. rewrite Z_to_bv_add64, Z2Nat.id in R by lia.
          replace (A + 2 + hdr_cfg data + 4) with (A + (6 + cfg)) by (subst cfg; lia).
          eapply rdn_firstn; [exact R | subst N cfg; unfold hdr_payload_len; lia]. }
        assert (MC : mcH mem6 (Z_to_bv 64 D) (Z_to_bv 64 PL) N ds).
        { split; [lia | exact Hds | exact SRC
                | rewrite Hds; replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia);
                  eapply (MainMem.wr_at_store_ok mem6 D N 0 (Z.to_nat N)); [eapply (wr_at_of_CB sp); [exact CB6 | lia] | lia | lia | lia]
                | subst PL; unorm; subst N cfg; unfold hdr_payload_len in *; lia | subst PL; unorm; subst N cfg; unfold hdr_payload_len in *; lia | unorm; lia]. }
        assert (RET : ret_ok (Z_to_bv 64 0x2afb0)) by (apply ret_ok_even; reflexivity).
        destruct (ref_memcpy mem6 (Z_to_bv 64 D) (Z_to_bv 64 PL) N ds (seg_rom RSEGS) MC regs7 (Z_to_bv 64 0x2afb0) RET Z1 Z10 Z11 Z12) as (regs8 & RUN & KEEP8).
        lazymatch type of RUN with ?hd _ (mkst _ ?pc4 _ _) _ => replace (Z_to_bv 64 0x75224) with pc4 by (apply bv_eq; reflexivity) end.
        eapply rz_msteps; [exact Hh6 | exact Hlazy6 | exact RUN |]. clear RUN.
        set (mem9 := wbytes mem6 (Z_to_bv 64 D) ds) in *.
        assert (TI9 : tinv mem9) by (subst mem9; eapply tinv_wblock; [exact TI6 | exact HBR6 | rewrite Hds; lia]).
        assert (TF9 : tframe sp mem9 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply tframe_agree; [exact TF6|]. intros x Hx. subst mem9. apply MemSplit.wbytes_outside; unorm; rewrite ?Hds; lia. }
        assert (RH9 : hs_RHEAP HS s6 ((pD, D, N) :: LB) mem9).
        { subst mem9. replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
          eapply (heap_wblock_in HS HH sp); [exact RH6 | left; reflexivity | exact HBR6 | lia | rewrite Hds; lia]. }
        assert (ST9 : sto 0 mem9) by (subst mem9; cbn [sto]; eapply sto0_wblock; [exact ST6 | exact HBR6 | rewrite Hds; lia]).
        assert (INCB9 : rdn RSEGS mem9 (Z_to_bv 64 0x90c74) 1 = Some [Z_to_bv 8 0]) by (subst mem9; eapply incb_wblock; [exact INCB6 | exact HBR6 | rewrite Hds; lia]).
        assert (CPY9 : rdn RSEGS mem9 (Z_to_bv 64 D) (length ds) = Some ds) by (subst mem9; apply rdn_wbytes_hit; unorm; rewrite Hds; lia).
        pose proof (KEEP8 2%bv ltac:(in_solve)) as Y2. pose proof (KEEP8 4%bv ltac:(in_solve)) as Y4. pose proof (KEEP8 8%bv ltac:(in_solve)) as Y8.
        pose proof (KEEP8 9%bv ltac:(in_solve)) as Y9. pose proof (KEEP8 18%bv ltac:(in_solve)) as Y18. pose proof (KEEP8 19%bv ltac:(in_solve)) as Y19.
        pose proof (KEEP8 20%bv ltac:(in_solve)) as Y20. pose proof (KEEP8 21%bv ltac:(in_solve)) as Y21.
        assert (LR8 : regs118 sp regs8 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 D) (Z_to_bv 64 CP)).
        { unfold regs118. rewrite Y2, Y4, Y8, Y9, Y18, Y19, Y20. exact LR7. }
        eapply (seg_T4 sp mo6 SP16 SPlo SPhi Hh6 Hlazy6 regs8 mem9 _ _ _ _ _ _ LR8 ltac:(rewrite Y21; exact Z21)
                  (tinv_stk80 mem9 TI9) (tinv_ro mem9 TI9) (ti_relro mem9 TI9)).
        intros regs9 LR9 V21' V19' K4g.
        eapply (tr_loop D D [(pD, D, N)] ltac:(right; split; [lia | split; [reflexivity | exists pD; split; [reflexivity | exact HBR6]]]) K HPOST regs9 mem9 mo6 s6 ((pD, D, N) :: LB)); [| exact K0].
        split; try assumption.
        + rewrite ECALLS. exact V21'.
        + intros rr Hrr. rewrite (K4g rr Hrr), (KEEP8 rr) by (unfold callee_kept; in_from Hrr).
          rewrite (K4f rr Hrr), (KEPT6 rr) by (unfold heap_kept; in_from Hrr).
          rewrite (K4e rr Hrr), (K4d rr Hrr). apply K4_3. exact Hrr.
        + apply Permutation_refl.
    Qed.
  End Call.

  (* [comment removed for export] *)
  Theorem target_run_sound_with : target_run_stmt HS.
  Proof.
    intros sp A cap data s LB model regs mem K PRE K0 HPOST.
    exact (target_run_ok sp A cap data s LB model regs mem PRE K K0 HPOST).
  Qed.
End TR.

(* [comment removed for export] *)
Theorem target_run_sound {HCEIL : HeapCeil} : forall HS : hsr,
  heap_sr_hyps HS -> heap_extra HS -> fuzz_stmt2 HS -> target_run_stmt HS.
Proof.
  intros HS HH HX (FT & FTL & FZ). exact (target_run_sound_with HS HH HX FT FTL FZ).
Qed.
