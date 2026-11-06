(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX MemSplit
  Spec RefNodes LibTail LibDiagKn RefMemcpyLib RefMemcpyBase RefMemcpy
  RefStdioDefs RefPrintfFirst RefPrintfBufBase RefPrintfBuf
  SReach RegsEquivM MainEqv MainDefs MainArith MainWalk_defs MainMem MainHeap MainSegs MainLoop MainTop TRWalk_defs TRSegs HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Image.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_SR ECH_Img ECH_Xpres ECH_LibState ECH_Iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac in_from H := cbn [In] in H; decompose [or] H; clear H; try contradiction; subst; in_solve.

(* [comment removed for export] *)
Ltac libx_lit H := unfold LIBX, LIBX0 in H; cbn [rin_ivs fst snd] in H.
Ltac libx_goal := unfold LIBX, LIBX0; cbn [rin_ivs fst snd].

Lemma lb_bytes_perm : forall LB LB', Permutation LB' LB -> lb_bytes LB' = lb_bytes LB.
Proof.
  intros LB LB' P. induction P as [| x l l' P IH | x y l | l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - cbn [lb_bytes fold_right]. fold (lb_bytes l). fold (lb_bytes l'). lia.
  - cbn [lb_bytes fold_right]. fold (lb_bytes l). lia.
  - lia.
Qed.
Lemma lb_big_perm : forall LB LB', Permutation LB' LB -> lb_big LB' = lb_big LB.
Proof.
  intros LB LB' P. induction P as [| x l l' P IH | x y l | l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - cbn [lb_big fold_right]. fold (lb_big l). fold (lb_big l'). lia.
  - cbn [lb_big fold_right]. fold (lb_big l). lia.
  - lia.
Qed.
Lemma lb_big_le_length : forall LB, lb_big LB <= Z.of_nat (length LB).
Proof.
  induction LB as [|b LB IH]; [cbv; discriminate|]. rewrite lb_big_cons. cbn [length].
  pose proof (big1_range (blk_size b)). lia.
Qed.

(* [comment removed for export] *)
Lemma libx_bounds : forall a, rin_ivs LIBX a -> 0x2dc188 <= a < 0x310be0.
Proof. intros a Ha. libx_lit Ha. lia. Qed.

Section TR.
  Context {HCEIL : HeapCeil}.
  Variable HS : hsr.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.
  Hypothesis FZ : fuzz_stmt HS.

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
      (s : PState) (LIB LBc : list block) (st : libst) (D N lo B : Z) (ds : list byte) (errv : word) (ra : Z) (K : TSet),
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 RATP ->
    getr regs 10 = Z_to_bv 64 D -> getr regs 11 = Z_to_bv 64 N ->
    bytes_at rsegs mem D ds -> Z.of_nat (length ds) = N -> N < 2 ^ 26 -> D mod 16 = 0 ->
    (1 <= N -> exists pD, In (pD, D, N) LBc) -> (N = 0 -> D = P_FUZZ_EMPTY) ->
    hs_RHEAP HS s (LIB ++ LBc) mem -> hs_KREL HS s model -> LIBST st LIB mem ->
    lb_bytes (LIB ++ LBc) + fuzz_live st <= hs_LIVE_MAX HS ->
    Z.of_nat (length (LIB ++ LBc)) + fuzz_cnt st <= hs_LIVE_CNT_MAX HS ->
    lb_big (LIB ++ LBc) + fuzz_big st <= hs_LIVE_BIG_MAX HS ->
    hs_rauxv_ok HS mem B -> bv_unsigned (getr regs 2) <= B -> B < 2 ^ 64 ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    stk rsegs mem lo (bv_unsigned (getr regs 2)) -> hceil <= lo -> lo <= bv_unsigned (getr regs 2) - FUZZ_STACK ->
    rw_cells rsegs mem (errno_addr (getr regs 4)) [C4 errv] -> mem_inv rsegs mem -> relro_lib mem ->
    (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) (s' : PState) (LIB' LBc' : list block)
            (st' : libst) (errv' : word),
        (forall r, In r fuzz_kept -> getr regs' r = getr regs r) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        hs_KREL HS s' model' -> hs_MPRES HS model model' ->
        mem_inv rsegs mem' -> relro_lib mem' -> stk rsegs mem' lo (bv_unsigned (getr regs 2)) ->
        rw_cells rsegs mem' (errno_addr (getr regs 4)) [C4 errv'] -> hs_rauxv_ok HS mem' B ->
        hs_RHEAP HS s' (LIB' ++ LBc') mem' -> Permutation LBc' LBc ->
        LIBST st' LIB' mem' -> is_fresh st' = false ->
        Z.of_nat (length LIB') <= LIB_CNT_MAX -> lb_bytes LIB' <= LIB_BYTES_MAX -> lb_big LIB' <= LIB_BIG_MAX ->
        (is_fresh st = false -> LIB' = LIB) ->
        xpres LBc (bv_unsigned (getr regs 2)) LIBX mem mem' ->
        realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSEGS)) model') K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 P_FUZZ_ENTRY) mem (seg_rom RSEGS)) model) K.
  Proof.
    intros regs mem model s LIB LBc st D N lo B ds errv ra K Hra Hra64 Hra2 Htp Ha0 Ha1 HBY HLEN HN HD16 HBLK HEMP HRH HKR HLIB
           HLIVE HCNT HBIG HAU HB HB64 HSP16 HSTK HLO HLO2 HERR HINV HREL HK.
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
                bvmap_empty (Z_to_bv 32 0) mem model s LIB LBc st D N lo B ds errv);
        try assumption; try reflexivity.
      - rewrite <- Htp. exact HERR.
      - rewrite u_small by lia. exact Hra2. }
    intros c' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LIB' & LBc' & st' &
               Hms & HKR' & HMP & HINV' & HREL' & HSTK' & HERR' & HAU' & HRH' & HPERM & HLIB' & HFR' & HL1 & HL2 & HL3 & HSAME & HX').
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' s' LIB' LBc' st' errv'); try exact HKR'; try exact HMP; try exact HINV'; try exact HREL'; try exact HSTK'; try exact HAU';
      try exact HRH'; try exact HPERM; try exact HLIB'; try exact HFR'; try exact HL1; try exact HL2; try exact HL3; try exact HSAME; try exact HX'.
    - intros r Hr. unfold fuzz_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_at : forall LB SP X m m' (a : Z),
    xpres LB SP X m m' -> 0 <= a < 2 ^ 64 -> rclient_addr LB SP a -> ~ rin_ivs X a -> m' (wa a) = m (wa a).
  Proof. intros LB SP X m m' a XP Ha HC HnX. exact (proj1 (XP a Ha (conj HC HnX))). Qed.

  (* [comment removed for export] *)
  Definition avoidX_b (X : list (Z * Z)) (c : Z * nat * Z) : bool :=
    match c with (a, w, _) => forallb (fun iv : Z * Z => (a + Z.of_nat w <=? fst iv) || (snd iv <=? a)) X end.
  Lemma avoidX_b_ok : forall X c, avoidX_b X c = true ->
    match c with (a, w, _) => forall i, a <= i < a + Z.of_nat w -> ~ rin_ivs X i end.
  Proof.
    intros X [[a w] v]. induction X as [|[lo hi] X IH]; intros Hb i Hi; cbn; [tauto|].
    cbn [avoidX_b forallb fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2].
    intros [R|R].
    - apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
    - exact (IH H2 i Hi R).
  Qed.

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
    Definition k_stack (r : word * Z) : Prop :=
      bv_unsigned sp - TR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r.
    Definition k_outF (r : word * Z) : Prop := 0x2dc7a0 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x2dc888 /\ 0 <= snd r.
    Definition k_outB (r : word * Z) : Prop := 0x30ff60 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x30ff68 /\ 0 <= snd r.
    Definition k_latch (r : word * Z) : Prop := bv_unsigned (fst r) = 0x2ec900 /\ snd r = 1.
    Definition k_incb (r : word * Z) : Prop := bv_unsigned (fst r) = 0x2ec904 /\ snd r = 1.
    Definition k_atex (r : word * Z) : Prop :=
      (0x30f4d0 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x30f4f0 /\ 0 <= snd r)
      \/ (bv_unsigned (fst r) = 0x30f5e8 /\ snd r = 8).
    Definition tr_region (r : word * Z) : Prop :=
      k_stack r \/ k_outF r \/ k_outB r \/ k_latch r \/ k_incb r \/ k_atex r.
    Ltac unk := unfold tr_region, k_stack, k_outF, k_outB, k_latch, k_incb, k_atex, TR_STACK.
    Ltac unk_in H := unfold tr_region, k_stack, k_outF, k_outB, k_latch, k_incb, k_atex, TR_STACK in H.

    Record tinv (m : word -> option byte) : Prop := TI {
      ti_inv   : mem_inv rsegs m;
      ti_stk   : stk rsegs m (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
      ti_cells : cells_ok m exit_cells;
      ti_relro : relro_none m;
      ti_tid   : exists t, rdn RSEGS m (Z_to_bv 64 0x2ef3d0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 t)) /\ 0 < t < 2 ^ 22;
      ti_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> m a = mem0 a;
      ti_aux   : exists B', hs_rauxv_ok HS m B' /\ bv_unsigned sp + 128 <= B' < 2 ^ 64 }.

    (* [comment removed for export] *)
    Definition exit_rng_b (c : Z * nat * Z) : bool :=
      match c with (a, w, _) =>
        (0x27efc8 <=? a) && (a + Z.of_nat w <=? 0x30fb48) && ((a + Z.of_nat w <=? 0x2dc7a0) || (0x2dc888 <=? a))
        && ((a + Z.of_nat w <=? 0x2ec900) || (0x2ec905 <=? a)) && ((a + Z.of_nat w <=? 0x2ef3d4) || (0x2ef3d8 <=? a))
        && ((a + Z.of_nat w <=? 0x30f4d0) || (0x30f4f0 <=? a)) && ((a + Z.of_nat w <=? 0x30f5e8) || (0x30f5f0 <=? a)) end.
    Definition exit_rng (c : Z * nat * Z) : Prop :=
      match c with (a, w, _) =>
        0x27efc8 <= a /\ a + Z.of_nat w <= 0x30fb48 /\ (a + Z.of_nat w <= 0x2dc7a0 \/ 0x2dc888 <= a)
        /\ (a + Z.of_nat w <= 0x2ec900 \/ 0x2ec905 <= a) /\ (a + Z.of_nat w <= 0x2ef3d4 \/ 0x2ef3d8 <= a)
        /\ (a + Z.of_nat w <= 0x30f4d0 \/ 0x30f4f0 <= a) /\ (a + Z.of_nat w <= 0x30f5e8 \/ 0x30f5f0 <= a) end.
    Lemma exit_rng_b_ok : forall c : Z * nat * Z, exit_rng_b c = true -> exit_rng c.
    Proof.
      intros [[a w] v] H. unfold exit_rng_b in H. unfold exit_rng.
      repeat (apply andb_true_iff in H; let X := fresh "X" in destruct H as [H X]).
      repeat match goal with
             | X : (_ || _)%bool = true |- _ => apply orb_leb_or in X
             | X : (_ <=? _) = true |- _ => apply Z.leb_le in X
             end.
      repeat split; assumption.
    Qed.
    Lemma exit_cells_range : Forall exit_rng exit_cells.
    Proof. apply (Forall_by_b _ _ exit_rng_b exit_rng_b_ok). vm_compute. reflexivity. Qed.
    Lemma exit_cells_wf : forallb cell_wf_b exit_cells = true. Proof. vm_compute. reflexivity. Qed.
    Lemma exit_cells_split : Forall (fun c => client_cell c \/ static_cell c) exit_cells.
    Proof using HCEIL PRE.
      apply (Forall_by_b _ _ cell_side_b cell_side_b_ok). vm_compute. reflexivity. Qed.
    Lemma exit_cells_noX : forallb (avoidX_b LIBX) exit_cells = true.
    Proof. vm_compute. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma tr_region_exit : forall r a w v, tr_region r -> exit_rng (a, w, v) ->
      a + Z.of_nat w <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a.
    Proof. intros r a w v Hr (R1 & R2 & R3 & R4 & R5 & R6 & R7). pose proof SPlo. unk_in Hr. lia. Qed.
    Lemma tr_region_lo : forall r, tr_region r ->
      (0x2dc7a0 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x2ec905)
      \/ (0x30f4d0 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x30f5f0)
      \/ (0x30ff60 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x30ff68)
      \/ (bv_unsigned sp - TR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp).
    Proof. intros r Hr. unk_in Hr. unfold TR_STACK. lia. Qed.
    Lemma tr_region_libx : forall r i, tr_region r -> rin_ivs LIBX i ->
      i < bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= i.
    Proof. intros r i Hr Hi. pose proof SPlo. libx_lit Hi. unk_in Hr. lia. Qed.
    Lemma tr_region_block : forall r Bk n i, tr_region r -> rblock_range Bk n -> Bk <= i < Bk + n ->
      i < bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= i.
    Proof. intros r Bk n i Hr (R1 & R2 & R3 & R4 & R5) Hi. clear R2. hcb. unk_in Hr. lia. Qed.

    Lemma tinv_frame : forall m m' rs,
      tinv m -> frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> tinv m'.
    Proof.
      intros m m' rs [INV STK CELLS RELRO [t [TID Ht]] ABOVE [B' [AUX HB']]] FM RS. pose proof SPlo. pose proof SPhi.
      pose proof FM as [Hout Hg].
      split.
      - eapply mem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. pose proof (u64_range (fst r)).
        pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
      - apply (stk_grows sp m m'); [exact STK | unfold TR_STACK; lia | exact Hg].
      - eapply cells_ok_frame; [apply exit_cells_wf | exact CELLS | exact FM |].
        eapply Forall_impl; [| apply exit_cells_range]. intros [[a w] v] RR r Hr. exact (tr_region_exit r a w v (RS r Hr) RR).
      - intros i Hi Hj. rewrite Hout; [apply RELRO; [exact Hi | exact Hj]|]. apply outside_of_disjoint. intros r Hr. rewrite u_small by lia.
        pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
      - exists t. split; [|exact Ht]. eapply rdn_frame; [exact FM | exact TID | unorm; lia |]. intros r Hr. unorm.
        pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
      - intros a Ha. rewrite <- (ABOVE a Ha). apply Hout. apply outside_of_disjoint. intros r Hr.
        pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
      - exists B'. split; [|exact HB']. eapply AUF; [exact AUX | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
        apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). cbn [fst snd].
        unfold RAUXV_CELL. pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
    Qed.

    Lemma heap_frame_tr : forall m m' s1 LB1 rs,
      hs_RHEAP HS s1 LB1 m -> frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> hs_RHEAP HS s1 LB1 m'.
    Proof.
      intros m m' s1 LB1 rs RH FM RS. pose proof SPlo. pose proof HCLO as HCL. unfold TR_STACK in HCL.
      eapply RFR; [exact RH | apply frame_mod_munch; exact FM | exact (frame_mod_wmono _ _ _ FM) |].
      apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
      hcb. unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn [fst snd].
      destruct (tr_region_lo r (RS r Hr)) as [X|[X|[X|X]]]; [right; left; lia | right; left; lia | right; left; lia | left; unfold TR_STACK in X; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_block_tr : forall m m' rs (Bk n k : Z) bs,
      frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> rblock_range Bk n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
      rdn RSEGS m (Z_to_bv 64 (Bk + k)) (length bs) = Some bs -> rdn RSEGS m' (Z_to_bv 64 (Bk + k)) (length bs) = Some bs.
    Proof.
      intros m m' rs Bk n k bs FM RS HBR Hk Hl HD. pose proof SPlo.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm.
      pose proof (tr_region_lo r (RS r Hr)). unfold TR_STACK in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lib_frame : forall st LIBc LBx sC m m' rs,
      LIBST st LIBc m -> hs_RHEAP HS sC (LIBc ++ LBx) m ->
      frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> LIBST st LIBc m'.
    Proof.
      intros st LIBc LBx sC m m' rs HL RH FM RS. pose proof FM as [Hout Hg].
      eapply LIBST_frame; [exact HL|]. intros a Ha Hla. split.
      - rewrite wa_eq. apply Hout. apply outside_of_disjoint. intros r Hr. rewrite u_small by lia.
        destruct Hla as [HXa | (b & Hb & Hrb)].
        + exact (tr_region_libx r a (RS r Hr) HXa).
        + pose proof (RBR _ _ _ _ RH (in_or_app _ _ _ (or_introl Hb))) as BR.
          exact (tr_region_block r _ _ a (RS r Hr) BR Hrb).
      - intros W. exact (frame_mod_wmono _ _ _ FM _ W).
    Qed.

    (* [comment removed for export] *)
    Lemma lib_none_frame : forall m m' rs, lib_none m -> frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> lib_none m'.
    Proof.
      intros m m' rs HL [Hout _] RS i Hi. rewrite Hout; [apply HL; exact Hi|]. apply outside_of_disjoint. intros r Hr.
      pose proof (libx_bounds i (LIBX0_sub_LIBX i Hi)). rewrite u_small by lia. exact (tr_region_libx r i (RS r Hr) (LIBX0_sub_LIBX i Hi)).
    Qed.
    Lemma libx_client : forall LBx SP i, rin_ivs LIBX i -> rclient_addr LBx SP i.
    Proof.
      intros LBx SP i Hi. libx_lit Hi. right. left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
    Qed.
    Lemma lib_none_heap : forall m m' LBx SP, lib_none m -> rheap_pres LBx SP m m' -> lib_none m'.
    Proof.
      intros m m' LBx SP HL HP i Hi. pose proof (libx_bounds i (LIBX0_sub_LIBX i Hi)).
      rewrite <- (HL i Hi), <- wa_eq. exact (proj1 (HP i ltac:(lia) (libx_client LBx SP i (LIBX0_sub_LIBX i Hi)))).
    Qed.
    Lemma lib_none_wblock : forall m (Bk n : Z) bs, lib_none m -> rblock_range Bk n -> Z.of_nat (length bs) <= n ->
      lib_none (wbytes m (Z_to_bv 64 Bk) bs).
    Proof.
      intros m Bk n bs HL (R1 & R2 & R3 & R4 & R5) Hl i Hi. clear R2. hcb. pose proof (libx_bounds i (LIBX0_sub_LIBX i Hi)).
      rewrite MemSplit.wbytes_outside; [apply HL; exact Hi | unorm; lia | unorm; lia].
    Qed.
    Lemma lib_none_LIBST : forall m, lib_none m -> LIBST lib_fresh [] m.
    Proof. intros m HL. apply LIBST_fresh_intro. intros a Ha. rewrite wa_eq. apply HL. exact Ha. Qed.

    (* [comment removed for export] *)
    Lemma cells_ok_xpres : forall cs m m' LB1 s2 LB2,
      forallb cell_wf_b cs = true -> Forall (fun c => client_cell c \/ static_cell c) cs -> forallb (avoidX_b LIBX) cs = true ->
      cells_ok m cs -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> hs_RHEAP HS s2 LB2 m' -> cells_ok m' cs.
    Proof.
      intros cs m m' LB1 s2 LB2 Hwf Hsplit HnX Hc XP HR.
      destruct (hx_statics HS HX s2 LB2 m' HR) as (S1 & S2 & S3).
      unfold cells_ok in *. induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      cbn [forallb] in HnX. apply andb_true_iff in HnX as [Hn1 HnX].
      inversion Hsplit as [|x l Hx Hl]; subst. inversion Hc as [|x' l' Hc1 Hcl]; subst.
      constructor; [|apply IH; assumption].
      destruct Hx as [CL | ST].
      - eapply cell_ok_agree; [exact H1 | | exact Hc1]. intros i Hi.
        pose proof H1 as Hw. unfold cell_wf_b in Hw. repeat (apply andb_true_iff in Hw; destruct Hw as [Hw ?]).
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
        rewrite <- wa_eq. unfold client_cell in CL.
        apply (xpres_at LB1 _ LIBX m m' i XP); [lia | right; left; unfold ralloc_static; lia | exact (avoidX_b_ok LIBX (a, w, v) Hn1 i Hi)].
      - destruct ST as [E|E]; injection E as -> -> ->; unfold cell_ok; assumption.
    Qed.

    Lemma tinv_xpres : forall m m' LB1 s2 LB2 B2,
      tinv m -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> hs_RHEAP HS s2 LB2 m' ->
      stk rsegs m' (bv_unsigned sp - TR_STACK) (bv_unsigned sp - 80) -> mem_inv rsegs m' ->
      hs_rauxv_ok HS m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 -> tinv m'.
    Proof.
      intros m m' LB1 s2 LB2 B2 [INV STK CELLS RELRO [t [TID Ht]] ABOVE AUX] XP RH STK' INV' AUX' HB2. pose proof SPlo. pose proof SPhi.
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
        apply (xpres_at LB1 _ LIBX m m' _ XP (u64_range x)); [left; lia | intros R; libx_lit R; lia]. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - eapply (cells_ok_xpres exit_cells m m' LB1 s2 LB2); [apply exit_cells_wf | apply exit_cells_split | apply exit_cells_noX | exact CELLS | exact XP | exact RH].
      - intros i Hi Hj. rewrite <- (RELRO i Hi Hj). rewrite <- wa_eq.
        apply (xpres_at LB1 _ LIBX m m' i XP); [lia | right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia | intros R; libx_lit R; lia].
      - exists t. split; [|exact Ht]. rewrite (rdn_ext RSEGS 4 m' m); [exact TID | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
        rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
        apply (xpres_at LB1 _ LIBX m m' _ XP (u64_range x)); [right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia | intros R; libx_lit R; lia].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; assumption.
    Qed.

    Lemma rdn_xclient_pres : forall LB1 m m' (a : Z) n bs,
      xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> client_cell (a, n, 0) ->
      (forall i, a <= i < a + Z.of_nat n -> ~ rin_ivs LIBX i) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros LB1 m m' a n bs XP HD HC HnX. unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in HC.
      rewrite (rdn_ext RSEGS n m' m); [exact HD | unorm; lia |]. intros x Hx. revert Hx. unorm. intros Hx.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
      apply (xpres_at LB1 _ LIBX m m' _ XP (u64_range x)); [| apply HnX; lia].
      right. left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. (first [clear - Hx HC; lia | lia]).
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
    Lemma tframe_xpres : forall m m' LB1 s0 s1 s2 s3 s4 s5 s6 s7,
      tframe sp m s0 s1 s2 s3 s4 s5 s6 s7 -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> tframe sp m' s0 s1 s2 s3 s4 s5 s6 s7.
    Proof.
      intros m m' LB1 s0 s1 s2 s3 s4 s5 s6 s7 TF XP. pose proof SPlo. eapply tframe_agree; [exact TF|]. intros x Hx.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
      apply (xpres_at LB1 _ LIBX m m' _ XP (u64_range x)); [left; lia | intros R; libx_lit R; lia].
    Qed.

    (* [comment removed for export] *)
    Definition sto (j : nat) (m : word -> option byte) : Prop :=
      match j with
      | O => cells_ok m pf1_cells
      | S k => stdout_after m k /\ rdn RSEGS m (Z_to_bv 64 0x2dc830) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
      end.

    (* [comment removed for export] *)
    Definition quiet_region (r : word * Z) : Prop := k_stack r \/ k_latch r \/ k_incb r \/ k_atex r.
    Lemma quiet_tr : forall r, quiet_region r -> tr_region r.
    Proof. intros r [X|[X|[X|X]]]; unfold tr_region; tauto. Qed.

    Lemma pf1_cells_range' : Forall (fun c : Z * nat * Z => match c with (a, w, _) => (a = 0x2db120 /\ w = 8%nat) \/ (0x2dc7a0 <= a /\ a + Z.of_nat w <= 0x2dc834) end) pf1_cells.
    Proof. unfold pf1_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
    Lemma pf1_cells_noX : forallb (avoidX_b LIBX) pf1_cells = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma sto_frame : forall j m m' rs, (j <= 4)%nat -> sto j m -> frame_mod m m' rs -> (forall r, In r rs -> quiet_region r) -> sto j m'.
    Proof.
      intros j m m' rs Hj ST FM RS. pose proof SPlo. unfold quiet_region, k_stack, k_latch, k_incb, k_atex, TR_STACK in RS. destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_frame; [apply pf1_cells_wf | exact ST | exact FM |].
        eapply Forall_impl; [| apply pf1_cells_range']. intros [[a w] v] RR r Hr. cbn [fst snd]. destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - destruct ST as [[F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12] LBF].
        assert (T : forall (a : Z) (n : nat) bs, 0x2dc7a0 <= a -> a + Z.of_nat n <= 0x30ff68 -> (a + Z.of_nat n <= 0x2dc834 \/ 0x30ff60 <= a) ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor HD. eapply rdn_frame; [exact FM | exact HD | unorm; lia |]. intros r Hr. unorm. destruct (RS r Hr) as [X|[X|[X|X]]]; lia. }
        split; [split|]; (eapply T; [ | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia.
    Qed.

    Lemma stdout_cells_client : forall (a : Z) (n : nat), 0x2dc7a0 <= a -> a + Z.of_nat n <= 0x2dc834 \/ (0x30ff60 <= a /\ a + Z.of_nat n <= 0x30ff68) -> client_cell (a, n, 0).
    Proof. intros a n Ha Hn. unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia. Qed.
    Lemma stdout_cells_noX : forall (a : Z) (n : nat), 0x2dc7a0 <= a -> a + Z.of_nat n <= 0x2dc834 \/ (0x30ff60 <= a /\ a + Z.of_nat n <= 0x30ff68) ->
      forall i, a <= i < a + Z.of_nat n -> ~ rin_ivs LIBX i.
    Proof. intros a n Ha Hn i Hi R. libx_lit R. lia. Qed.

    Lemma sto_xpres : forall j m m' LB1 s2 LB2, (j <= 4)%nat -> sto j m -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> hs_RHEAP HS s2 LB2 m' -> sto j m'.
    Proof.
      intros j m m' LB1 s2 LB2 Hj ST XP RH. pose proof SPlo. pose proof SPhi. destruct j as [|k]; cbn [sto] in *.
      - eapply (cells_ok_xpres pf1_cells m m' LB1 s2 LB2); [apply pf1_cells_wf | apply (pf1_cells_split 1); lia | apply pf1_cells_noX | exact ST | exact XP | exact RH].
      - destruct ST as [[F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12] LBF].
        split; [split|]; (eapply rdn_xclient_pres; [exact XP | eassumption | apply stdout_cells_client | apply stdout_cells_noX]);
          cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; (first [clear - Hj; lia | lia]).
    Qed.

    (* [comment removed for export] *)
    Lemma tinv_wblock : forall m (Bk n : Z) bs,
      tinv m -> rblock_range Bk n -> Z.of_nat (length bs) <= n -> tinv (wbytes m (Z_to_bv 64 Bk) bs).
    Proof.
      intros m Bk n bs [INV STK CELLS RELRO [t [TID Ht]] ABOVE [B' [AUX HB']]] HBR Hl. pose proof SPlo. pose proof SPhi.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      assert (EB : Z_to_bv 64 Bk = Z_to_bv 64 (Bk + 0)) by (f_equal; lia).
      split.
      - rewrite EB. eapply mem_inv_wbytes_block; [exact INV | exact HBR | lia | lia].
      - rewrite wbytes_eq, <- wa_eq. apply stk_write; [exact STK | unfold TR_STACK; lia | lia].
      - eapply cells_ok_wbytes_out; [apply exit_cells_wf | exact CELLS | unorm; lia |].
        eapply Forall_impl; [| apply exit_cells_range]. intros [[a w] v] (Q1 & Q2 & _). unorm. lia.
      - intros i Hi Hj. rewrite MemSplit.wbytes_outside; [apply RELRO; [exact Hi | exact Hj] | unorm; lia | unorm; lia].
      - exists t. split; [|exact Ht]. eapply rdn_wbytes_out; [exact TID | unorm; lia | unorm; lia | unorm; lia].
      - intros a Ha. rewrite MemSplit.wbytes_outside; [apply ABOVE; exact Ha | unorm; lia | unorm; lia].
      - exists B'. split; [|exact HB']. eapply AUF; [exact AUX | | |].
        + rewrite wbytes_eq, <- wa_eq. apply (munch_write [(Bk, Bk + Z.of_nat (length bs))]); [apply munch_refl | lia | lia | cbn; left; lia].
        + rewrite wbytes_eq. apply wmono_write. apply wmono_refl.
        + constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia.
    Qed.

    Lemma sto0_wblock : forall m (Bk n : Z) bs,
      cells_ok m pf1_cells -> rblock_range Bk n -> Z.of_nat (length bs) <= n -> cells_ok (wbytes m (Z_to_bv 64 Bk) bs) pf1_cells.
    Proof.
      intros m Bk n bs ST HBR Hl. pose proof HBR as (R1 & R2 & R3 & R4 & R5). clear R2. hcb.
      eapply cells_ok_wbytes_out; [apply pf1_cells_wf | exact ST | unorm; lia |].
      eapply Forall_impl; [| apply pf1_cells_range]. intros [[a w] v] [Q1 Q2]. unorm. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma atexit_reg_cells_wf : forallb cell_wf_b atexit_reg_cells = true. Proof. vm_compute. reflexivity. Qed.
    Lemma atexit_reg_cells_split : Forall (fun c => client_cell c \/ static_cell c) atexit_reg_cells.
    Proof using HCEIL PRE. apply (Forall_by_b _ _ cell_side_b cell_side_b_ok). vm_compute. reflexivity. Qed.
    Lemma atexit_reg_cells_noX : forallb (avoidX_b LIBX) atexit_reg_cells = true. Proof. vm_compute. reflexivity. Qed.
    Lemma atexit_reg_cells_eq : atexit_reg_cells = atexit_done_cells ++ [(0x2ec904, 1%nat, 0)].
    Proof. reflexivity. Qed.
    Definition atx_rng (c : Z * nat * Z) : Prop :=
      match c with (a, w, _) => (0x30f4d0 <= a /\ a + Z.of_nat w <= 0x30f4f0) \/ (a = 0x30f5e8 /\ w = 8%nat) \/ (a = 0x2ec904 /\ w = 1%nat) end.
    Lemma atexit_reg_cells_range : Forall atx_rng atexit_reg_cells.
    Proof. unfold atexit_reg_cells, atx_rng. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
    (* [comment removed for export] *)
    Definition pf_region (r : word * Z) : Prop := k_stack r \/ k_outF r \/ k_outB r.
    Lemma pf_tr : forall r, pf_region r -> tr_region r.
    Proof. intros r [X|[X|X]]; unfold tr_region; tauto. Qed.
    Lemma atx_frame : forall m m' rs, cells_ok m atexit_reg_cells -> frame_mod m m' rs -> (forall r, In r rs -> pf_region r) ->
      cells_ok m' atexit_reg_cells.
    Proof.
      intros m m' rs HC FM RS. pose proof SPlo. unfold pf_region, k_stack, k_outF, k_outB, TR_STACK in RS.
      eapply cells_ok_frame; [apply atexit_reg_cells_wf | exact HC | exact FM |].
      eapply Forall_impl; [| apply atexit_reg_cells_range]. intros [[a w] v] RR r Hr. cbn [fst snd]. unfold atx_rng in RR.
      destruct (RS r Hr) as [X|[X|X]]; lia.
    Qed.
    Lemma atx_xpres : forall m m' LB1 s2 LB2, cells_ok m atexit_reg_cells -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> hs_RHEAP HS s2 LB2 m' ->
      cells_ok m' atexit_reg_cells.
    Proof.
      intros m m' LB1 s2 LB2 HC XP RH.
      eapply (cells_ok_xpres atexit_reg_cells m m' LB1 s2 LB2); [apply atexit_reg_cells_wf | apply atexit_reg_cells_split | apply atexit_reg_cells_noX | exact HC | exact XP | exact RH].
    Qed.
    (* [comment removed for export] *)
    Lemma atx5_of_reg : forall m, cells_ok m atexit_reg_cells -> cells_ok m atexit_done_cells.
    Proof. intros m HC. rewrite atexit_reg_cells_eq in HC. unfold cells_ok in *. apply Forall_app in HC. exact (proj1 HC). Qed.
    Lemma reg_of_atx5 : forall m, cells_ok m atexit_done_cells -> rdn RSEGS m (Z_to_bv 64 0x2ec904) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      cells_ok m atexit_reg_cells.
    Proof. intros m HC HB. rewrite atexit_reg_cells_eq. unfold cells_ok in *. apply Forall_app. split; [exact HC|]. apply Forall_cons; [exact HB | apply Forall_nil]. Qed.
    (* [comment removed for export] *)
    Lemma atx5_frame : forall m m' rs, cells_ok m atexit_done_cells -> frame_mod m m' rs -> (forall r, In r rs -> pf_region r \/ k_incb r) ->
      cells_ok m' atexit_done_cells.
    Proof.
      intros m m' rs HC FM RS. pose proof SPlo. unfold pf_region, k_stack, k_outF, k_outB, k_incb, TR_STACK in RS.
      eapply cells_ok_frame; [vm_compute; reflexivity | exact HC | exact FM |].
      unfold atexit_done_cells. repeat (apply Forall_cons; [intros r Hr; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (RS r Hr) as [[X|[X|X]]|X]; lia |]). apply Forall_nil.
    Qed.
    Lemma atx5_xpres : forall m m' LB1 s2 LB2, cells_ok m atexit_done_cells -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> hs_RHEAP HS s2 LB2 m' ->
      cells_ok m' atexit_done_cells.
    Proof.
      intros m m' LB1 s2 LB2 HC XP RH.
      pose proof atexit_reg_cells_split as SP. rewrite atexit_reg_cells_eq in SP. apply Forall_app in SP. destruct SP as [SP _].
      eapply (cells_ok_xpres atexit_done_cells m m' LB1 s2 LB2); [vm_compute; reflexivity | exact SP | vm_compute; reflexivity | exact HC | exact XP | exact RH].
    Qed.
    (* [comment removed for export] *)
    Definition incb0 (m : word -> option byte) : Prop := rdn RSEGS m (Z_to_bv 64 0x2ec904) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
    Lemma incb0_frame : forall m m' rs, incb0 m -> frame_mod m m' rs -> (forall r, In r rs -> pf_region r \/ k_latch r \/ k_atex r) -> incb0 m'.
    Proof.
      intros m m' rs HB FM RS. pose proof SPlo. unfold pf_region, k_stack, k_outF, k_outB, k_latch, k_atex, TR_STACK in RS. unfold incb0 in *.
      eapply rdn_frame; [exact FM | exact HB | unorm; lia |]. intros r Hr. unorm. destruct (RS r Hr) as [[X|[X|X]]|[X|[X|X]]]; lia.
    Qed.
    Lemma incb0_xpres : forall m m' LB1, incb0 m -> xpres LB1 (bv_unsigned sp - 80) LIBX m m' -> incb0 m'.
    Proof.
      intros m m' LB1 HB XP. unfold incb0 in *. eapply rdn_xclient_pres; [exact XP | exact HB | | intros i Hi R; libx_lit R; lia].
      unfold client_cell, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
    Qed.
    Lemma incb0_wblock : forall m (Bk n : Z) bs, incb0 m -> rblock_range Bk n -> Z.of_nat (length bs) <= n -> incb0 (wbytes m (Z_to_bv 64 Bk) bs).
    Proof.
      intros m Bk n bs HB (R1 & R2 & R3 & R4 & R5) Hl. clear R2. hcb. unfold incb0 in *.
      eapply rdn_wbytes_out; [exact HB | unorm; lia | unorm; lia | unorm; lia].
    Qed.

    Lemma tinv_stk128 : forall m, tinv m -> stk_ok RSEGS m sp 128.
    Proof. intros m TI. pose proof SPlo. pose proof SPhi. eapply stk_stk_ok; [exact (ti_stk _ TI) | unfold TR_STACK; lia | lia | lia | lia]. Qed.
    Lemma tinv_stklo : forall m, tinv m -> stk rsegs m (bv_unsigned sp - TR_STACK) (bv_unsigned sp - 80).
    Proof. intros m TI. destruct (ti_stk _ TI) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. Qed.
    Lemma tinv_ro : forall m, tinv m -> ro_none m.
    Proof. intros m TI. apply mem_inv_ro_none. exact (ti_inv _ TI). Qed.
    Lemma relro_lib_of_none : forall m, relro_none m -> relro_lib m.
    Proof.
      intros m R a Ha Hn. unfold RELRO_LO, RELRO_HI, RGOT_SSP in *. rewrite wa_eq. apply R; lia.
    Qed.

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

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Section Loop.
      (* [comment removed for export] *)
      Variables (Dz OWz : Z) (cb : list block).
      Hypothesis COPY : (N = 0 /\ Dz = P_FUZZ_EMPTY /\ OWz = 0 /\ cb = [])
                        \/ (1 <= N /\ OWz = Dz /\ exists pD, cb = [(pD, Dz, N)] /\ rblock_range Dz N).
      (* [comment removed for export] *)
      Let LB0 : list block := cb ++ LB.
      (* [comment removed for export] *)
      Variable K : TSet.
      Hypothesis HPOST : forall regs' mem' model', TRpost HS sp A cap data LB model0 regs0 mem0 regs' mem' model' ->
         realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdda4c) mem' (seg_rom RSEGS)) model') K.

      Let HD16 : Dz mod 16 = 0.
      Proof. destruct COPY as [(_ & -> & _) | (_ & _ & pD & _ & (_ & R2 & _))]; [reflexivity | exact R2]. Qed.
      Let HDr : 0 < Dz /\ Dz + N < 2 ^ 47.
      Proof.
        destruct COPY as [(-> & -> & _) | (_ & _ & pD & _ & (R1 & _ & _ & R4 & _))]; [unfold P_FUZZ_EMPTY; lia|].
        hcb. lia.
      Qed.

      (* [comment removed for export] *)
      Record lstate (k : nat) (r : Z) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (sC : PState)
                    (LIBc LBc : list block) (st : libst) : Prop := LS {
        ls_regs  : loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz);
        ls_r     : getr regs 21 = Z_to_bv 64 r;
        ls_k4    : forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr;
        ls_tinv  : tinv m;
        ls_frame : tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23);
        ls_heap  : hs_RHEAP HS sC (LIBc ++ LBc) m;
        ls_perm  : Permutation LBc LB0;
        ls_lib   : LIBST st LIBc m;
        ls_libn  : Z.of_nat (length LIBc) + (if is_fresh st then LIB_CNT_MAX else 0) <= LIB_CNT_MAX
                   /\ lb_bytes LIBc + (if is_fresh st then LIB_BYTES_MAX else 0) <= LIB_BYTES_MAX
                   /\ lb_big LIBc + (if is_fresh st then LIB_BIG_MAX else 0) <= LIB_BIG_MAX;
        ls_krel  : hs_KREL HS sC mo;
        ls_mpres : hs_MPRES HS model0 mo;
        ls_copy  : rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds;
        ls_sto   : sto k m;
        ls_atx   : cells_ok m atexit_reg_cells }.

      Lemma copy_frame : forall m m' rs, rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds ->
        frame_mod m m' rs -> (forall r, In r rs -> tr_region r) -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds.
      Proof.
        intros m m' rs HC FM RS. destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & _ & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        - replace (Z_to_bv 64 Dz) with (Z_to_bv 64 (Dz + 0)) in HC |- * by (f_equal; lia).
          eapply (rdn_block_tr m m' rs Dz N 0 ds FM RS HBR); [lia | rewrite Hds; lia | exact HC].
      Qed.
      Lemma copy_xpres : forall m m' LBc, Permutation LBc LB0 -> rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds ->
        xpres LBc (bv_unsigned sp - 80) LIBX m m' -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds.
      Proof.
        intros m m' LBc HP HC XP. destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        - pose proof HBR as (R1 & _ & _ & R4 & R5). hcb.
          rewrite (rdn_ext RSEGS (length ds) m' m); [exact HC | unorm; rewrite ?Hds; lia |]. intros x Hx. revert Hx. unorm. rewrite Hds. intros Hx.
          rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
          apply (xpres_at LBc _ LIBX m m' _ XP (u64_range x)); [| intros R; libx_lit R; lia].
          right. right. exists (pD, Dz, N). split; [| cbn; lia].
          eapply Permutation_in; [apply Permutation_sym; exact HP|]. subst LB0. rewrite Ecb. left. reflexivity.
      Qed.
      Lemma copy_heap : forall m m' LBx SP, rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds ->
        rheap_pres LBx SP m m' -> (forall b, In b cb -> In b LBx) -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds.
      Proof.
        intros m m' LBx SP HC HPR Hcb. destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        - pose proof HBR as (R1 & _ & _ & R4 & _). hcb.
          rewrite (rdn_ext RSEGS (length ds) m' m); [exact HC | unorm; rewrite ?Hds; lia |]. intros x Hx. revert Hx. unorm. rewrite Hds. intros Hx.
          rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
          refine (proj1 (HPR _ (u64_range x) _)). right. right. exists (pD, Dz, N). split; [| cbn; lia].
          apply Hcb. rewrite Ecb. left. reflexivity.
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
        hs_RHEAP HS sC LBf m -> (forall b, In b LB -> In b LBf) -> hs_KREL HS sC mo -> hs_MPRES HS model0 mo -> sto calls m ->
        cells_ok m atexit_reg_cells -> m (Z_to_bv 64 0x2ecb3c) = None ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddcc8) m (seg_rom RSEGS)) mo) K.
      Proof.
        intros regs m mo sC LBf LR K4 TI TF RH HLB KR MP STO ATX DGC. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        eapply (seg_T8 sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ _ _ _ _ _ _ _ _ K LR (tinv_stk128 m TI) (tinv_ro m TI) (ti_relro m TI) TF).
        intros regs' Q2 Q4 Q10 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 KP K4'.
        rename TI into TI'. rename RH into RH'. rename STO into STO'. rename m into mem'.
        apply HPOST. destruct TI' as [INV STK CELLS RELRO TID ABOVE [B' [AUX HB']]].
        destruct calls as [|k'] eqn:EC; [lia|]. cbn [sto] in STO'. destruct STO' as [SA LBF].
        destruct (hx_statics HS HX _ _ _ RH') as (_ & _ & CAN).
        split; try assumption.
        - intros rr Hrr. cbn [In] in Hrr.
          destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
            first [assumption | rewrite K4' by in_solve; apply K4; in_solve].
        - eapply stk_stk_ok; [exact STK | lia | lia | unfold TR_STACK; lia | lia].
        - exists sC, LBf. split; [exact RH'|]. split; [exact KR|]. exact HLB.
        - exists B'. split; [exact AUX|]. lia.
        - apply mem_inv_ro_none. exact INV.
        - unfold cells_ok. apply Forall_app. split; [exact CELLS | exact ATX].
        - change (hdr_calls data) with calls. rewrite EC. cbn [Nat.pred]. exact SA.
        - apply errno_cell_any.
        - exact (proj1 (hx_mpres HS HX _ _ MP)).
        - apply Hfd1. exact MP.
        - apply Hfd2. exact MP.
      Qed.

      Ltac regT_k Hr := unfold regT_w in Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; unfold k_stack, TR_STACK; cbn [fst snd]; rewrite u_small by lia; lia.

      (* [comment removed for export] *)
      Lemma tr_free : forall regs m mo sC LIBc LBc st,
        lstate calls 1 regs m mo sC LIBc LBc st -> getr regs 19 = Z_to_bv 64 0 ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddca8) m (seg_rom RSEGS)) mo) K.
      Proof.
        intros regs m mo sC LIBc LBc st [LR R21 K4 TI TF RH PERM LIB LIBN KR MP CPY STO ATX] R19. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        pose proof (LIBST_cleanup_byte st LIBc m LIB) as DGC. unfold A_global_cleanup in DGC. rewrite wa_eq in DGC.
        destruct COPY as [(N0 & ED & EOW & Ecb) | (N1 & EOW & pD & Ecb & HBR)].
        - (* [comment removed for export] *)
          rewrite EOW in LR.
          eapply (seg_T7null sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ K LR R19 R21 (tinv_stk128 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 LR1 Q19 K4'.
          eapply (tr_ret regs1 m mo sC (LIBc ++ LBc)); try assumption.
          + rewrite EOW. exact LR1.
          + intros rr Hrr. rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + intros b Hb. apply in_or_app. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. subst LB0. rewrite Ecb. exact Hb.
        - (* [comment removed for export] *)
          eapply (seg_T7free sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ K LR R19 R21 (tinv_stk128 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q19 Q1 Q10 K4'.
          destruct (ti_aux _ TI) as [B' [AUX1 HB']]. destruct (errno_rw m regs1 Q4) as [errv ERR].
          assert (HIn : In (pD, Dz, N) (LIBc ++ LBc)).
          { apply in_or_app. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. subst LB0. rewrite Ecb. left. reflexivity. }
          change (Z_to_bv 64 0x26f3a8) with (Z_to_bv 64 RFREE_SYM).
          eapply (free_call HS HH HX regs1 m mo sC (LIBc ++ LBc) pD Dz N (bv_unsigned sp - TR_STACK) B' errv 0xddcc8 K Q1);
            [ lia | reflexivity | exact Q4 | rewrite Q10, EOW; reflexivity | exact RH | exact KR | exact HIn
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (tinv_stklo m TI)
            | pose proof HCLO; unfold TR_STACK in *; lia | rewrite Q2, u_small by lia; unfold RFREE_STACK, TR_STACK; lia
            | exact ERR | exact (ti_inv _ TI) |].
          intros regs2 mem2 mo2 s2 KEPT KR2 MP2 INV2 STK2 ERR2 AUX2 HP2 RH2.
          rewrite Q2, u_small in STK2, HP2 by lia.
          pose proof (xpres_of_heap_pres _ _ LIBX _ _ HP2) as XP2.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          eapply (tr_ret regs2 mem2 mo2 s2 (hs_lb_remove HS pD (LIBc ++ LBc))).
          + unfold loop_base. rewrite S2, S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold heap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply tinv_xpres; [exact TI | exact XP2 | exact RH2 | exact STK2 | exact INV2 | exact AUX2 | exact HB'].
          + eapply tframe_xpres; [exact TF | exact XP2].
          + exact RH2.
          + (* [comment removed for export] *)
            intros b Hb.
            pose proof (lb_remove_perm (LIBc ++ LBc) pD Dz N (RND _ _ _ RH) HIn) as P1.
            assert (P2 : Permutation (LIBc ++ LBc) ((pD, Dz, N) :: (LIBc ++ LB))).
            { eapply Permutation_trans; [apply Permutation_app_head; exact PERM |]. subst LB0. rewrite Ecb. cbn [app].
              apply Permutation_sym. apply Permutation_middle. }
            assert (P3 : Permutation (hs_lb_remove HS pD (LIBc ++ LBc)) (LIBc ++ LB)).
            { apply (Permutation_cons_inv (a:=(pD, Dz, N))). eapply Permutation_trans; [apply Permutation_sym; exact P1 | exact P2]. }
            eapply Permutation_in; [apply Permutation_sym; exact P3|]. apply in_or_app. right. exact Hb.
          + exact KR2.
          + eapply MPtrans; [exact MP | exact MP2].
          + eapply sto_xpres; [lia | exact STO | exact XP2 | exact RH2].
          + eapply atx_xpres; [exact ATX | exact XP2 | exact RH2].
          + (* [comment removed for export] *)
            rewrite <- DGC, <- wa_eq. refine (proj1 (HP2 0x2ecb3c ltac:(lia) _)).
            right. left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
      Qed.

      Let LIVE : 2 ^ 28 <= hs_LIVE_MAX HS /\ 2850 <= hs_LIVE_CNT_MAX HS /\ 16 <= hs_LIVE_BIG_MAX HS. Proof. exact (hx_live HS HX). Qed.

      (* [comment removed for export] *)
      Lemma tr_call_harness : forall k r regs m mo sC LIBc LBc st (Kx : TSet),
        (k <= 4)%nat -> lstate k r regs m mo sC LIBc LBc st ->
        (forall regs' m' mo' sC' LIBc' LBc' st', lstate k r regs' m' mo' sC' LIBc' LBc' st' ->
           getr regs' 1 = Z_to_bv 64 0xddca8 -> getr regs' 11 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddd60) m' (seg_rom RSEGS)) mo') Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddc84) m (seg_rom RSEGS)) mo) Kx.
      Proof.
        intros k r regs m mo sC LIBc LBc st Kx Hk [LR R21 K4 TI TF RH PERM LIB (LN1 & LN2 & LN3) KR MP CPY STO ATX] HK. pose proof SPlo. pose proof SPhi.
        pose proof LIVE as (LV1 & LV2 & LV3). pose proof LB0_bytes as [LBB LBL]. pose proof HN as HN'.
        pose proof (lb_big_le_length LB0) as LBG. pose proof (lb_big_nonneg LIBc) as LG0. pose proof (lb_big_nonneg LBc) as LG1.
        destruct (KRELh sC mo KR) as [Hh Hlazy].
        eapply (seg_T5 sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ (getr regs 19) _ Kx LR eq_refl R21 (tinv_stk128 m TI) (tinv_ro m TI) (ti_relro m TI)).
        intros regs1 mem1 LR1 Q19 Q21 Q1 Q10 Q11 K4a FM1 STK1 CB1.
        pose proof LR1 as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        assert (RS1 : forall rr, In rr (regTc_w sp) -> tr_region rr).
        { intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unk. destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        assert (TI1 : tinv mem1) by (eapply tinv_frame; [exact TI | exact FM1 | exact RS1]).
        assert (RH1 : hs_RHEAP HS sC (LIBc ++ LBc) mem1) by (eapply heap_frame_tr; [exact RH | exact FM1 | exact RS1]).
        assert (LIB1 : LIBST st LIBc mem1) by (eapply lib_frame; [exact LIB | exact RH | exact FM1 | exact RS1]).
        assert (ATX1 : cells_ok mem1 atexit_done_cells).
        { eapply atx5_frame; [apply atx5_of_reg; exact ATX | exact FM1 |].
          intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold pf_region, k_stack, k_incb, TR_STACK.
          destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        destruct (ti_aux _ TI1) as [B' [AUX1 HB']]. destruct (errno_rw mem1 regs1 Q4) as [errv ERR].
        change (Z_to_bv 64 0xdddb0) with (Z_to_bv 64 P_FUZZ_ENTRY).
        eapply (fuzz_call regs1 mem1 mo sC LIBc LBc st Dz N (bv_unsigned sp - TR_STACK) B' ds errv 0xddc98 Kx Q1);
          [ lia | reflexivity | exact Q4 | exact Q10 | exact Q11
          | apply rdn_bytes_at; [eapply copy_frame; [exact CPY | exact FM1 | exact RS1] | lia | rewrite Hds; lia] | rewrite Hds; lia | lia | exact HD16
          | intros HN1; exact (copy_in LBc PERM HN1)
          | intros HN0; destruct COPY as [(_ & ED & _) | (HN1 & _)]; [exact ED | lia]
          | exact RH1 | exact KR | exact LIB1
          | rewrite lb_bytes_app, (lb_bytes_perm LB0 LBc PERM); unfold fuzz_live, FUZZ_LIVE, LIB_BYTES_MAX in *; destruct (is_fresh st); lia
          | rewrite length_app, Nat2Z.inj_add, (Permutation_length PERM); unfold fuzz_cnt, TRANS_CNT, LIB_CNT_MAX in *; destruct (is_fresh st); lia
          | rewrite lb_big_app, (lb_big_perm LB0 LBc PERM); unfold fuzz_big, TRANS_BIG, LIB_BIG_MAX in *; destruct (is_fresh st); lia
          | exact AUX1 | rewrite Q2, u_small by lia; lia | lia
          | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite Q2, u_small by lia; exact (tinv_stklo mem1 TI1)
          | pose proof HCLO; unfold TR_STACK in *; lia
          | rewrite Q2, u_small by lia; unfold FUZZ_STACK, TR_STACK; lia
          | exact ERR | exact (ti_inv _ TI1) | apply relro_lib_of_none; exact (ti_relro _ TI1) |].
        intros regs2 mem2 mo2 s2 LIB2 LBc2 st2 errv2 KEPT A0 KR2 MP2 INV2 REL2 STK2 ERR2 AUX2 RH2 PERM2 LST2 FR2 L1 L2 L3 SAME X2.
        rewrite Q2, u_small in STK2, X2 by lia.
        destruct (KRELh s2 mo2 KR2) as [Hh2 Hlazy2].
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
        pose proof (KEPT 21%bv ltac:(in_solve)) as S21. pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
        assert (LR2 : loop_base sp regs2 (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz)).
        { unfold loop_base. rewrite S2, S4, S8, S9, S18, S20, S22, S23. repeat split; assumption. }
        assert (TI2 : tinv mem2) by (eapply tinv_xpres; [exact TI1 | exact X2 | exact RH2 | exact STK2 | exact INV2 | exact AUX2 | exact HB']).
        eapply (seg_T6 sp mo2 SP16 SPlo SPhi Hh2 Hlazy2 regs2 mem2 _ _ _ _ Kx LR2 ltac:(rewrite S21; exact Q21) A0 (tinv_stk128 mem2 TI2) (tinv_ro mem2 TI2) (ti_relro mem2 TI2)).
        intros regs3 mem3 LR3 T19 T21 T1 T11 K4b FM3 STK3 CB3.
        assert (RS3 : forall rr, In rr (regTc_w sp) -> tr_region rr) by exact RS1.
        apply (HK regs3 mem3 mo2 s2 LIB2 LBc2 st2); [| exact T1 | exact T11 | exact T19].
        split.
        - exact LR3.
        - exact T21.
        - intros rr Hrr. rewrite (K4b rr Hrr), (KEPT rr) by (unfold fuzz_kept; in_from Hrr). rewrite (K4a rr Hrr). apply K4. exact Hrr.
        - eapply tinv_frame; [exact TI2 | exact FM3 | exact RS3].
        - eapply tframe_agree; [eapply tframe_xpres; [eapply tframe_agree; [exact TF | intros x Hx; apply (proj1 FM1); apply outside_of_disjoint; intros rr Hr; unfold regTc_w in Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia] | exact X2] |].
          intros x Hx. apply (proj1 FM3). apply outside_of_disjoint. intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia.
        - eapply heap_frame_tr; [exact RH2 | exact FM3 | exact RS3].
        - eapply Permutation_trans; [exact PERM2 | exact PERM].
        - eapply lib_frame; [exact LST2 | exact RH2 | exact FM3 | exact RS3].
        - rewrite FR2. repeat split; lia.
        - exact KR2.
        - eapply MPtrans; [exact MP | exact MP2].
        - eapply copy_frame; [eapply (copy_xpres mem1 mem2 LBc); [exact PERM | eapply copy_frame; [exact CPY | exact FM1 | exact RS1] | exact X2] | exact FM3 | exact RS3].
        - eapply sto_frame; [lia | eapply sto_xpres; [lia | eapply sto_frame; [lia | exact STO | exact FM1 |] | exact X2 | exact RH2] | exact FM3 |].
          + intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold quiet_region, k_stack, k_incb, TR_STACK.
            destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold quiet_region, k_stack, k_incb, TR_STACK.
            destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia.
        - apply reg_of_atx5; [| exact CB3]. eapply atx5_frame; [eapply atx5_xpres; [exact ATX1 | exact X2 | exact RH2] | exact FM3 |].
          intros rr Hr. unfold regTc_w in Hr. cbn [In] in Hr. unfold pf_region, k_stack, k_incb, TR_STACK.
          destruct Hr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia.
      Qed.

      Ltac pf_region Hr :=
        cbn [In] in Hr;
        repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
        unfold pf_region, k_stack, k_outF, k_outB, TR_STACK; cbn [fst snd]; rewrite ?u_small by lia; lia.

      (* [comment removed for export] *)
      Lemma tr_printf_buf : forall k r regs m mo sC LIBc LBc st (Kx : TSet),
        (1 <= k <= 3)%nat -> lstate k r regs m mo sC LIBc LBc st ->
        getr regs 1 = Z_to_bv 64 0xddca8 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 ->
        (forall regs' m', lstate (S k) r regs' m' mo sC LIBc LBc st -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddca8) m' (seg_rom RSEGS)) mo) Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddd60) m (seg_rom RSEGS)) mo) Kx.
      Proof.
        intros k r regs m mo sC LIBc LBc st Kx Hk [LR R21 K4 TI TF RH PERM LIB LIBN KR MP CPY STO ATX] R1 R11 R19 HK. pose proof SPlo. pose proof SPhi.
        destruct (KRELh sC mo KR) as [Hh Hlazy]. destruct k as [|k']; [lia|]. cbn [sto] in STO. destruct STO as [SA LBF].
        destruct SA as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12].
        destruct (hx_statics HS HX _ _ _ RH) as (_ & GOT & [can [CAN CAN64]]).
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        set (w := 0x30ff60 + 2 * Z.of_nat k') in *.
        assert (PH : pfH m (Z_to_bv 64 (bv_unsigned sp - 80)) w can).
        { split; rewrite ?u_small by lia; try assumption; try (subst w; lia).
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - eapply stk_stk_ok; [exact (ti_stk _ TI) | unfold PF_FR, TR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold PF_FR; lia | lia].
          - apply mem_inv_ro_none. exact (ti_inv _ TI). }
        destruct (printf0_buffered regs m (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp - 80)) w can PH R1 ltac:(exact Q2) R11)
          as (regs' & mem' & RUN & KCS & FM & BY & WP & FL).
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
        rewrite u_small in FM by lia.
        assert (RSp : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1056), 1056); (Z_to_bv 64 0x2dc7a0, 4); (Z_to_bv 64 0x2dc7c8, 8); (Z_to_bv 64 w, 2)] -> pf_region rr).
        { intros rr Hr. subst w. pf_region Hr. }
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1056), 1056); (Z_to_bv 64 0x2dc7a0, 4); (Z_to_bv 64 0x2dc7c8, 8); (Z_to_bv 64 w, 2)] -> tr_region rr).
        { intros rr Hr. apply pf_tr. apply RSp. exact Hr. }
        assert (T : forall (a : Z) (n : nat) bs, 0x2dc7a4 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                  (a + Z.of_nat n <= 0x2dc7c8 \/ 0x2dc7d0 <= a) -> a + Z.of_nat n <= w ->
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
          + exact PERM.
          + eapply lib_frame; [exact LIB | exact RH | exact FM | exact RS].
          + exact LIBN. + exact KR. + exact MP.
          + eapply copy_frame; [exact CPY | exact FM | exact RS].
          + cbn [sto]. split; [split|].
            * exact FL.
            * eapply T; [ | | | | exact F2]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F3]; subst w; cbn; lia.
            * eapply T; [ | | | | exact F4]; subst w; cbn; lia.
            * replace (0x30ff60 + 2 * Z.of_nat (S k')) with (w + 2) by (subst w; lia). exact WP.
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
              -- replace (0x30ff60 + Z.of_nat (2 * k')) with w by (subst w; lia). exact BY.
            * eapply T; [ | | | | exact LBF]; subst w; cbn; lia.
          + eapply atx_frame; [exact ATX | exact FM | exact RSp].
        - rewrite (KCS _) by (unfold callee_saved; in_solve). exact R19.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_printf_first : forall r regs m mo sC LIBc LBc st (Kx : TSet),
        lstate 0 r regs m mo sC LIBc LBc st ->
        getr regs 1 = Z_to_bv 64 0xddca8 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 -> Kx [] ->
        (forall regs' m', lstate 1 r regs' m' mo sC LIBc LBc st -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddca8) m' (seg_rom RSEGS)) mo) Kx) ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddd60) m (seg_rom RSEGS)) mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) Kx).
      Proof.
        intros r regs m mo sC LIBc LBc st Kx [LR R21 K4 TI TF RH PERM LIB LIBN KR MP CPY STO ATX] R1 R11 R19 K0 HK. pose proof SPlo. pose proof SPhi.
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
        assert (RSp : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1232), 1232); (Z_to_bv 64 0x2dc7a0, 232); (Z_to_bv 64 0x30ff60, 1)] -> pf_region rr).
        { intros rr Hr. pf_region Hr. }
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 1232), 1232); (Z_to_bv 64 0x2dc7a0, 232); (Z_to_bv 64 0x30ff60, 1)] -> tr_region rr).
        { intros rr Hr. apply pf_tr. apply RSp. exact Hr. }
        apply HK.
        - split.
          + unfold loop_base. rewrite (P_cs 4%bv), (P_cs 8%bv), (P_cs 9%bv), (P_cs 18%bv), (P_cs 20%bv), (P_cs 22%bv), (P_cs 23%bv) by in_solve. rewrite P_sp. split; [reflexivity | exact (proj2 LR)].
          + rewrite (P_cs _) by in_solve. exact R21.
          + intros rr Hrr. rewrite (P_cs rr) by (in_from Hrr). apply K4. exact Hrr.
          + eapply tinv_frame; [exact TI | exact P_frame | exact RS].
          + eapply tframe_agree; [exact TF|]. intros x Hx. apply (proj1 P_frame). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply heap_frame_tr; [exact RH | exact P_frame | exact RS].
          + exact PERM.
          + eapply lib_frame; [exact LIB | exact RH | exact P_frame | exact RS].
          + exact LIBN. + exact KR. + exact MP.
          + eapply copy_frame; [exact CPY | exact P_frame | exact RS].
          + cbn [sto]. split; [split|]; try assumption; first [reflexivity | replace (0x30ff60 + 2 * Z.of_nat 0) with 0x30ff60 by lia; exact P_wpos].
          + eapply atx_frame; [exact ATX | exact P_frame | exact RSp].
        - rewrite (P_cs _) by in_solve. exact R19.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_after_printf : forall (rn k : nat) regs m mo sC LIBc LBc st,
        (1 <= rn)%nat -> (k + rn = calls + 1)%nat -> (1 <= k)%nat ->
        lstate k (Z.of_nat rn) regs m mo sC LIBc LBc st -> getr regs 19 = Z_to_bv 64 0 ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddca8) m (seg_rom RSEGS)) mo) K.
      Proof.
        induction rn as [|rn IH]; intros k regs m mo sC LIBc LBc st Hrn Hk Hk1 LS R19; [lia|].
        pose proof Hcalls as HC. pose proof SPlo. pose proof SPhi.
        destruct rn as [|rn'].
        - (* [comment removed for export] *) assert (Ek : k = calls) by lia. subst k. eapply tr_free; [exact LS | exact R19].
        - destruct LS as [LR R21 K4 TI TF RH PERM LIB LIBN KR MP CPY STO ATX]. destruct (KRELh sC mo KR) as [Hh Hlazy].
          eapply (seg_T7more sp mo SP16 SPlo SPhi Hh Hlazy regs m _ _ _ (Z.of_nat (S (S rn'))) K LR R19 R21 ltac:(lia)
                    (tinv_stk128 m TI) (tinv_ro m TI) (ti_relro m TI)).
          intros regs1 LR1 Q19 Q21 K4a.
          replace (Z.of_nat (S (S rn')) - 1) with (Z.of_nat (S rn')) in Q21 by lia.
          assert (LS1 : lstate k (Z.of_nat (S rn')) regs1 m mo sC LIBc LBc st).
          { split; try assumption. intros rr Hrr. rewrite (K4a rr Hrr). apply K4. exact Hrr. }
          eapply (tr_call_harness k _ regs1 m mo sC LIBc LBc st K ltac:(lia) LS1).
          intros regs2 m2 mo2 sC2 LIBc2 LBc2 st2 LS2 T1 T11 T19.
          eapply (tr_printf_buf k _ regs2 m2 mo2 sC2 LIBc2 LBc2 st2 K ltac:(lia) LS2 T1 T11 T19).
          intros regs3 m3 LS3 U19.
          eapply (IH (S k)); [lia | lia | lia | exact LS3 | exact U19].
      Qed.

      (* [comment removed for export] *)
      Lemma tr_loop : forall regs m mo sC LIBc LBc st,
        lstate 0 (Z.of_nat calls) regs m mo sC LIBc LBc st -> K [] ->
        realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddc84) m (seg_rom RSEGS)) mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
      Proof.
        intros regs m mo sC LIBc LBc st LS K0.
        eapply (tr_call_harness 0 _ regs m mo sC LIBc LBc st _ ltac:(lia) LS).
        intros regs2 m2 mo2 sC2 LIBc2 LBc2 st2 LS2 T1 T11 T19.
        eapply (tr_printf_first _ regs2 m2 mo2 sC2 LIBc2 LBc2 st2 K LS2 T1 T11 T19 K0).
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

    Lemma tinv0 : tinv mem0.
    Proof.
      pose proof PRE as PRE'.
      destruct PRE' as [R1 R2 R4 R10 R11 R12 R13 L6 LHI _ _ _ STK STKC RH KR BLK [LB1 LB2] AUX CAP DATA RO INV CELLS PF1 REL LIBN TID ERRC CAN Hh Hlazy FD1 FD2].
      split; try assumption.
      - eapply cells_ok_incl; [exact CELLS|]. exact (incl_filter (fun c : Z * nat * Z => match c with (a, _, _) => negb (exit_skip a) end) diag_cells).
      - intros a _. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma pre_cells0 : cells_ok mem0 atexit_pre_cells /\ rdn RSEGS mem0 (Z_to_bv 64 0x2ec900) 1 = Some [Z_to_bv 8 0] /\ incb0 mem0.
    Proof.
      pose proof (cells_ok_in _ _ (tr_cells _ _ _ _ _ _ _ _ _ _ PRE)) as CI.
      split; [| split].
      - unfold atexit_pre_cells, cells_ok. repeat (apply Forall_cons; [refine (CI _ _); in_solve |]). apply Forall_nil.
      - change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). refine (CI (0x2ec900, 1%nat, 0) _). in_solve.
      - unfold incb0. refine (CI (0x2ec904, 1%nat, 0) _). in_solve.
    Qed.

    Variable K : TSet.
    Hypothesis K0 : K [].
    Hypothesis HPOST : forall regs' mem' model', TRpost HS sp A cap data LB model0 regs0 mem0 regs' mem' model' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdda4c) mem' (seg_rom RSEGS)) model') K.

    Theorem target_run_ok :
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xddbc0) mem0 (seg_rom RSEGS)) model0) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof HN as HN'. pose proof Hcfg as Hcfg'. pose proof Hcalls as HC.
      pose proof PRE as PRE'. destruct PRE' as [R1 R2 R4 R10 R11 R12 R13 L6 LHI _ _ _ STK STKC RH KR BLK [LB1 LB2] AUX CAP DATA RO INV CELLS PF1 REL LIBN TID ERRC CAN Hh Hlazy FD1 FD2].
      pose proof tinv0 as TI0. destruct pre_cells0 as (APC & Hib & CB0).
      (* [comment removed for export] *)
      apply in_map_iff in BLK. destruct BLK as ([[pb Ab] capb] & Eb & HbLB). cbn in Eb. injection Eb as E1 E2. subst Ab capb.
      pose proof (RBR _ _ _ _ RH HbLB) as HBRb. cbn [blk_addr blk_size fst snd] in HBRb.
      pose proof HBRb as (B1 & B2 & B3 & B4 & B5). clear B2. hcb.
      set (c := nth 2 data (Z_to_bv 8 0)).
      pose proof (calls_of_hdr c eq_refl) as ECALLS.
      (* [comment removed for export] *)
      eapply (seg_T0 sp model0 SP16 SPlo SPhi Hh Hlazy regs0 mem0 (Z_to_bv 64 CP) (Z_to_bv 64 cfg) (Z_to_bv 64 PL) (Z_to_bv 64 N) (Z_to_bv 8 0) _ R1 R2 R4 R10 R11 R12 R13 Hib APC
                (tinv_stk128 mem0 TI0) (tinv_ro mem0 TI0) (ti_relro mem0 TI0)).
      intros regs1 mem1 LR1 K6a FM1 STK1 TF1 ATX1'.
      pose proof (ATX1' eq_refl) as ATX5. clear ATX1'.
      assert (Q1 : forall r, In r (regTb_w sp) -> quiet_region r).
      { intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr. unfold quiet_region, k_stack, k_latch, k_incb, k_atex, TR_STACK.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (RS1 : forall r, In r (regTb_w sp) -> tr_region r) by (intros r Hr; apply quiet_tr; apply Q1; exact Hr).
      assert (TI1 : tinv mem1) by (eapply tinv_frame; [exact TI0 | exact FM1 | exact RS1]).
      assert (RH1 : hs_RHEAP HS ps LB mem1) by (eapply heap_frame_tr; [exact RH | exact FM1 | exact RS1]).
      assert (ST1 : sto 0 mem1) by (eapply (sto_frame 0); [lia | exact PF1 | exact FM1 | exact Q1]).
      assert (LN1 : lib_none mem1) by (eapply lib_none_frame; [exact LIBN | exact FM1 | exact RS1]).
      assert (CB1 : incb0 mem1).
      { eapply incb0_frame; [exact CB0 | exact FM1 |]. intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr. unfold pf_region, k_stack, k_latch, k_atex, TR_STACK.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (ATX1 : cells_ok mem1 atexit_reg_cells) by (apply reg_of_atx5; [exact ATX5 | exact CB1]).
      assert (DATA1 : rdn RSEGS mem1 (Z_to_bv 64 A) (length data) = Some data).
      { replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) in DATA |- * by (f_equal; lia).
        eapply (rdn_block_tr mem0 mem1 _ A cap 0 data FM1); [exact RS1 | exact HBRb | lia | lia | exact DATA]. }
      assert (HC1 : cfg <> 0 -> rdn RSEGS mem1 (Z_to_bv 64 CP) 1 = Some [c]).
      { intros _. subst c CP. pose proof (rdn_nth RSEGS mem1 (length data) (Z_to_bv 64 A) data 2 DATA1 ltac:(lia)) as R.
        unfold nat_to_word in R. rewrite Z_to_bv_add64 in R. exact R. }
      clear TI0 RH DATA.
      destruct (Z.eq_dec N 0) as [N0|N1].
      - (* [comment removed for export] *)
        rewrite N0 in LR1.
        eapply (seg_T1zero sp model0 SP16 SPlo SPhi Hh Hlazy regs1 mem1 cfg _ _ c _ LR1 ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (tinv_stk128 mem1 TI1) (tinv_ro mem1 TI1) (ti_relro mem1 TI1)).
        intros regs2 LR2 Q21 K4b.
        eapply (tr_loop P_FUZZ_EMPTY 0 [] ltac:(left; repeat split; lia) K HPOST regs2 mem1 model0 ps [] LB lib_fresh); [| exact K0].
        split; try assumption.
        + rewrite N0. exact LR2.
        + rewrite ECALLS. exact Q21.
        + intros rr Hrr. rewrite (K4b rr Hrr). apply K6a. cbn [In] in Hrr |- *. tauto.
        + apply Permutation_refl.
        + apply lib_none_LIBST. exact LN1.
        + cbn [is_fresh lib_fresh length Z.of_nat lb_bytes lb_big fold_right]. unfold LIB_CNT_MAX, LIB_BYTES_MAX, LIB_BIG_MAX. lia.
        + apply MPrefl.
        + assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
      - (* [comment removed for export] *)
        eapply (seg_T1pos sp model0 SP16 SPlo SPhi Hh Hlazy regs1 mem1 N cfg _ _ c _ LR1 ltac:(lia) ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (tinv_stk128 mem1 TI1) (tinv_ro mem1 TI1) (ti_relro mem1 TI1)).
        intros regs2 LR2 Q21 K6b.
        eapply (seg_T2 sp model0 SP16 SPlo SPhi Hh Hlazy regs2 mem1 _ _ _ _ _ _ LR2 Q21 (tinv_stk128 mem1 TI1) (tinv_ro mem1 TI1) (ti_relro mem1 TI1)).
        intros regs3 LR3 U21 U1 U10 K6c.
        pose proof LR3 as (V2 & V4 & V8 & V9 & V18 & V19 & V20).
        destruct (ti_aux _ TI1) as [B' [AUX1 HB']]. destruct (errno_rw mem1 regs3 V4) as [errv ERR].
        pose proof (hx_live HS HX) as (LV1 & LV2 & LV3).
        change (Z_to_bv 64 0x26f4e8) with (Z_to_bv 64 RMALLOC_SYM).
        eapply (malloc_call HS HH HX regs3 mem1 model0 ps LB N (bv_unsigned sp - TR_STACK) B' errv 0xddc28 _ U1);
          [ lia | reflexivity | exact V4 | exact U10 | lia | exact RH1 | exact KR
          | apply (AOK ps LB mem1 N RH1); [lia | lia | lia | pose proof (lb_big_le_length LB); pose proof (big1_range N); lia]
          | exact AUX1 | rewrite V2, u_small by lia; lia
          | rewrite V2, u_small by lia; exact (tinv_stklo mem1 TI1)
          | pose proof HCLO; unfold TR_STACK in *; lia | rewrite V2, u_small by lia; unfold RMALLOC_STACK, TR_STACK; lia
          | exact ERR | exact (ti_inv _ TI1) |].
        intros regs4 mem4 mo4 D pD s4 errv4 junk KEPT W10 KR4 MP4 INV4 STK4 ERR4 AUX4 HP4 HBR4 RH4 CB4.
        rewrite V2, u_small in STK4, HP4 by lia.
        pose proof (xpres_of_heap_pres _ _ LIBX _ _ HP4) as XP4.
        destruct (KRELh s4 mo4 KR4) as [Hh4 Hlazy4].
        pose proof HBR4 as (C1 & C2 & C3 & C4 & C5). hcb.
        assert (TI4 : tinv mem4) by (eapply tinv_xpres; [exact TI1 | exact XP4 | exact RH4 | exact STK4 | exact INV4 | exact AUX4 | exact HB']).
        assert (TF4 : tframe sp mem4 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply tframe_xpres; [exact TF1 | exact XP4]. }
        assert (ST4 : sto 0 mem4) by (eapply (sto_xpres 0); [lia | exact ST1 | exact XP4 | exact RH4]).
        assert (LN4 : lib_none mem4) by (eapply lib_none_heap; [exact LN1 | exact HP4]).
        assert (CB4' : incb0 mem4) by (eapply incb0_xpres; [exact CB1 | exact XP4]).
        assert (ATX4 : cells_ok mem4 atexit_reg_cells) by (eapply atx_xpres; [exact ATX1 | exact XP4 | exact RH4]).
        assert (DATA4 : rdn RSEGS mem4 (Z_to_bv 64 A) (length data) = Some data).
        { eapply (rdn_rheap_pres (Z_to_bv 64 (bv_unsigned sp + 48)) LB mem1 mem4 A (length data) data);
            [rewrite u_small by lia; replace (bv_unsigned sp + 48 - 128) with (bv_unsigned sp - 80) by lia; exact HP4 | exact DATA1 | lia | lia |].
          intros i Hi. exists (pb, A, cap). split; [exact HbLB | cbn; lia]. }
        (* [comment removed for export] *)
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 19%bv ltac:(in_solve)) as S19.
        pose proof (KEPT 20%bv ltac:(in_solve)) as S20. pose proof (KEPT 21%bv ltac:(in_solve)) as S21.
        assert (LR4 : regs138 sp regs4 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 cfg) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite S2, S4, S8, S9, S18, S19, S20. exact LR3. }
        eapply (seg_T3 sp mo4 SP16 SPlo SPhi Hh4 Hlazy4 regs4 mem4 _ _ _ _ _ (Z_to_bv 64 D) _ LR4 ltac:(rewrite S21; exact U21) W10 ltac:(rewrite u_small by lia; lia)
                  (tinv_stk128 mem4 TI4) (tinv_ro mem4 TI4) (ti_relro mem4 TI4)).
        intros regs5 LR5 X21 X1 X10 X11 X12 K6d.
        (* [comment removed for export] *)
        assert (DISJ : D + N <= A \/ A + cap <= D).
        { assert (Hp : pD <> pb).
          { intros E. subst pD. pose proof (RND _ _ _ RH4) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l Hni Hnd]; subst.
            apply Hni. replace pb with (blk_id (pb, A, cap)) by reflexivity. apply in_map. exact HbLB. }
          pose proof (RBD _ _ _ (pD, D, N) (pb, A, cap) RH4 ltac:(left; reflexivity) ltac:(right; exact HbLB) Hp) as DJ.
          cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
        assert (SRC : rdn RSEGS mem4 (Z_to_bv 64 PL) (length ds) = Some ds).
        { subst ds PL. rewrite Hds.
          pose proof (rdn_skipn RSEGS mem4 (length data) (Z_to_bv 64 A) data (Z.to_nat (6 + cfg)) DATA4 ltac:(lia)) as R.
          unfold nat_to_word in R. rewrite Z_to_bv_add64, Z2Nat.id in R by lia.
          replace (A + 2 + hdr_cfg data + 4) with (A + (6 + cfg)) by (subst cfg; lia).
          eapply rdn_firstn; [exact R | subst N cfg; unfold hdr_payload_len; lia]. }
        assert (MC : mcH mem4 (Z_to_bv 64 D) (Z_to_bv 64 PL) N ds).
        { split; [lia | exact Hds | exact SRC
                | rewrite Hds; replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia);
                  eapply (MainMem.wr_at_store_ok mem4 D N 0 (Z.to_nat N)); [eapply (wr_at_of_CB sp); [exact CB4 | lia] | lia | lia | lia]
                | subst PL; unorm; subst N cfg; unfold hdr_payload_len in *; lia | subst PL; unorm; subst N cfg; unfold hdr_payload_len in *; lia | unorm; lia]. }
        assert (RET : ret_ok (Z_to_bv 64 0xddc40)) by (apply ret_ok_even; reflexivity).
        destruct (ref_memcpy mem4 (Z_to_bv 64 D) (Z_to_bv 64 PL) N ds (seg_rom RSEGS) MC regs5 (Z_to_bv 64 0xddc40) RET X1 X10 X11 X12) as (regs6 & RUN & KEEP6).
        lazymatch type of RUN with msteps _ (mkst _ ?pc4 _ _) _ => replace (Z_to_bv 64 0x2798bc) with pc4 by (apply bv_eq; reflexivity) end.
        eapply rz_msteps; [exact Hh4 | exact Hlazy4 | exact RUN |]. clear RUN.
        set (mem5 := wbytes mem4 (Z_to_bv 64 D) ds) in *.
        assert (TI5 : tinv mem5) by (subst mem5; eapply tinv_wblock; [exact TI4 | exact HBR4 | rewrite Hds; lia]).
        assert (TF5 : tframe sp mem5 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply tframe_agree; [exact TF4|]. intros x Hx. subst mem5. apply MemSplit.wbytes_outside; unorm; rewrite ?Hds; lia. }
        assert (RH5 : hs_RHEAP HS s4 ((pD, D, N) :: LB) mem5).
        { subst mem5. replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
          eapply (heap_wblock_in HS HH sp); [exact RH4 | left; reflexivity | exact HBR4 | lia | rewrite Hds; lia]. }
        assert (ST5 : sto 0 mem5) by (subst mem5; cbn [sto]; eapply sto0_wblock; [exact ST4 | exact HBR4 | rewrite Hds; lia]).
        assert (LN5 : lib_none mem5) by (subst mem5; eapply lib_none_wblock; [exact LN4 | exact HBR4 | rewrite Hds; lia]).
        assert (CB5 : incb0 mem5) by (subst mem5; eapply incb0_wblock; [exact CB4' | exact HBR4 | rewrite Hds; lia]).
        assert (ATX5' : cells_ok mem5 atexit_reg_cells).
        { subst mem5. pose proof HBR4 as (R1' & R2' & R3' & R4' & R5'). clear R2'.
          eapply cells_ok_wbytes_out; [apply atexit_reg_cells_wf | exact ATX4 | unorm; rewrite Hds; lia |].
          eapply Forall_impl; [| apply atexit_reg_cells_range]. intros [[a w] v] RR. unfold atx_rng in RR. unorm. rewrite Hds. lia. }
        assert (CPY5 : rdn RSEGS mem5 (Z_to_bv 64 D) (length ds) = Some ds) by (subst mem5; apply rdn_wbytes_hit; unorm; rewrite Hds; lia).
        pose proof (KEEP6 2%bv ltac:(in_solve)) as Y2. pose proof (KEEP6 4%bv ltac:(in_solve)) as Y4. pose proof (KEEP6 8%bv ltac:(in_solve)) as Y8.
        pose proof (KEEP6 9%bv ltac:(in_solve)) as Y9. pose proof (KEEP6 18%bv ltac:(in_solve)) as Y18. pose proof (KEEP6 19%bv ltac:(in_solve)) as Y19.
        pose proof (KEEP6 20%bv ltac:(in_solve)) as Y20. pose proof (KEEP6 21%bv ltac:(in_solve)) as Y21.
        assert (LR6 : regs138 sp regs6 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 D) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite Y2, Y4, Y8, Y9, Y18, Y19, Y20. exact LR5. }
        eapply (seg_T4 sp mo4 SP16 SPlo SPhi Hh4 Hlazy4 regs6 mem5 _ _ (Z_to_bv 64 cfg) _ _ _ _ LR6 ltac:(rewrite Y21; exact X21)
                  (tinv_stk128 mem5 TI5) (tinv_ro mem5 TI5) (ti_relro mem5 TI5)).
        intros regs7 LR7 Z21 K6e.
        eapply (tr_loop D D [(pD, D, N)] ltac:(right; split; [lia | split; [reflexivity | exists pD; split; [reflexivity | exact HBR4]]]) K HPOST regs7 mem5 mo4 s4 [] ((pD, D, N) :: LB) lib_fresh); [| exact K0].
        split; try assumption.
        + rewrite ECALLS. exact Z21.
        + intros rr Hrr. assert (H6 : In rr ([22; 23; 24; 25; 26; 27]%bv : list reg)) by (cbn [In] in Hrr |- *; tauto).
          rewrite (K6e rr Hrr), (KEEP6 rr) by (unfold callee_kept; in_from Hrr).
          rewrite (K6d rr H6), (KEPT rr) by (unfold heap_kept; in_from Hrr).
          rewrite (K6c rr H6), (K6b rr H6). apply K6a. exact H6.
        + apply Permutation_refl.
        + apply lib_none_LIBST. exact LN5.
        + cbn [is_fresh lib_fresh length Z.of_nat lb_bytes lb_big fold_right]. unfold LIB_CNT_MAX, LIB_BYTES_MAX, LIB_BIG_MAX. lia.
    Qed.
  End Call.

  (* [comment removed for export] *)
  Theorem target_run_sound : target_run_stmt HS.
  Proof.
    intros sp A cap data s LB model regs mem K PRE K0 HPOST.
    exact (target_run_ok sp A cap data s LB model regs mem PRE K K0 HPOST).
  Qed.

End TR.
