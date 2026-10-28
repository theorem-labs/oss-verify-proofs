(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_free Fz_M_clear_free Fz_M_clear_realloc Fz_M_secure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_sync Fz_W1_grow Fz_W1_growc Fz_W1_write Fz_W1_writet.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_MEM_WRITE : Z := 0x1832b0.
Definition WRITE_STACK : Z := 64 + GROW_STACK.

(* [comment removed for export] *)
Definition src_loc (LBall : list block) (T : bptr -> Prop) (SP IN inl : Z) : Prop :=
  SP <= IN \/ exists ps AS ns, In (ps, AS, ns) LBall /\ ~ T ps /\ AS <= IN /\ IN + inl <= AS + ns.

Definition write_T (pbi pbm prp pd : bptr) : bptr -> Prop := fun q => q = pbi \/ q = pbm \/ q = prp \/ q = pd.

Definition write_re_res (BI BM RP len' inl sec : Z) (pd : bptr) (nm : Z) (hd tl : list cell) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q D' jk i fl', v = Z_to_bv 64 inl /\ LBall' = (q, D', grow_n len') :: lb_remove pd LBall
     /\ nth_error L i = Some (pd, nm) /\ L' = (q, grow_n len') :: cremove i L /\ rblock_range D' (grow_n len')
     /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')]
     /\ rw_cells usegs m' BM (bufmem_cells len' D' (grow_n len') (Z_to_bv 64 sec))
     /\ rw_cells usegs m' RP (readp_cells len' D' 0 (Z_to_bv 64 (grow_n len')) (Z_to_bv 64 sec))
     /\ length jk = Z.to_nat (grow_n len') /\ rw_cells usegs m' D' [CB (Z.to_nat (grow_n len')) jk]
     /\ rw_cells usegs m' BI hd /\ rw_cells usegs m' (BI + 52) tl.

Definition W1_write_re_stmt (sec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi : Z) (pbb : bptr) (BB : Z) (pbm : bptr) (BM : Z) (prp : bptr) (RP : Z) (pd : bptr) (D len max nm off fl inl IN : Z)
         (rmaxw : word) (junk src : list byte) (hd tl : list cell),
  (2 <= f)%nat ->
  croom L (wA (grow_n (len - off + inl))) (wB (grow_n (len - off + inl))) (wBig (grow_n (len - off + inl))) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - WRITE_STACK ->
  a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 inl -> 0 < inl -> 0 < IN ->
  In (pbi, BI, nbi) LBall -> 72 <= nbi -> In (pbb, BB, 16) LBall -> cown LBall L pbm BM 32 32 -> In (prp, RP, 32) LBall -> cown LBall L pd D max nm ->
  (pbi <> pbb /\ pbi <> pbm /\ pbi <> prp /\ pbi <> pd /\ pbb <> pbm /\ pbb <> prp /\ pbb <> pd /\ pbm <> prp /\ pbm <> pd /\ prp <> pd) ->
  ro_cells usegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl ->
  ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
  rw_cells usegs m BI hd -> Z.of_nat (cells_size hd) = 48 -> rw_cells usegs m (BI + 52) tl -> 52 + Z.of_nat (cells_size tl) <= nbi ->
  rw_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
  rw_cells usegs m BM (bufmem_cells len D max (Z_to_bv 64 sec)) -> rw_cells usegs m RP (readp_cells len D off rmaxw (Z_to_bv 64 sec)) ->
  0 <= off <= len -> len <= max -> 0 < max -> max < len - off + inl -> len - off + inl < 1610612733 ->
  rw_cells usegs m D [CB (Z.to_nat max) junk] ->
  bytes_at usegs m IN src -> length src = Z.to_nat inl -> src_loc LBall (fun q => q = pbi \/ q = pbb \/ q = pbm \/ q = prp \/ q = pd) (bv_unsigned sp) IN inl ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MEM_WRITE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (write_T pbi pbm prp pd) [] 2
                (wA (grow_n (len - off + inl))) (wB (grow_n (len - off + inl))) (wBig (grow_n (len - off + inl)))
                (write_re_res BI BM RP (len - off + inl) inl sec pd nm hd tl LBall L)).

Theorem W1_write_re_spec : forall sec, W1_grow_re_stmt sec -> W1_write_re_stmt sec.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros sec GROW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi pbb BB pbm BM prp RP pd D len max nm off fl inl IN rmaxw junk src hd tl
         Hf ROOM CST SLO -> -> -> HINL HIN INBI HNBI INBB OWNM INRP OWND PNE INITC FLC FLOK PTRC HD HDZ TL TLZ BBC BMC RPC HOFF HLEN HMAX0 HGROW HLIM DBLK SRC LSRC SLOC.
  destruct PNE as (NE_IB & NE_IM & NE_IR & NE_ID & NE_BM & NE_BR & NE_BD & NE_MR & NE_MD & NE_RD).
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & BI16 & _ & BICe & _). assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBB) as (BB0 & BB16 & _ & BBCe & _). assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INRP) as (RP0 & RP16 & _ & RPCe & _). assert (RP8 : RP mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  assert (APDB : D + max <= BB \/ BB + 16 <= D) by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND) INBB); intros E; apply NE_BD; symmetry; exact E).
  assert (APDM : D + max <= BM \/ BM + 32 <= D) by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND) (proj1 OWNM)); intros E; apply NE_MD; symmetry; exact E).
  assert (APDR : D + max <= RP \/ RP + 32 <= D) by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND) INRP); intros E; apply NE_RD; symmetry; exact E).
  assert (APMR : BM + 32 <= RP \/ RP + 32 <= BM) by (exact (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM) INRP NE_MR)).
  assert (BOXH : tbox ((BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= BM \/ BM + 32 <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48)
          /\ (BI + 52 <= BB \/ BB + 16 <= BI + 48) /\ (BB + 16 <= BM \/ BM + 32 <= BB) /\ (BB + 16 <= RP \/ RP + 32 <= BB))).
  { unfold tbox.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI (proj1 OWND) NE_ID) as A1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI (proj1 OWNM) NE_IM) as A2.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as A3.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INBB NE_IB) as A4.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBB (proj1 OWNM) NE_BM) as A5.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBB INRP NE_BR) as A6.
    clear - A1 A2 A3 A4 A5 A6 HNBI. repeat split; lia. }
  pose proof (grow_n_bounds (len - off + inl) ltac:(lia)) as HN.
  pose proof (rw_cells_CB_length usegs m D _ _ DBLK) as LJ.
  pose proof (bytes_at_bound _ _ _ _ SRC) as INB. rewrite LSRC, Z2Nat.id in INB by lia.
  unfold WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_MEM_WRITE, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  cprefix. eapply evt_mono.
  { eapply (W1_write_head_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BI BB BM RP D len max off fl inl IN rmaxw (Z_to_bv 64 sec) junk);
      try first [reflexivity | eassumption | exact (proj1 BBC) | lia]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & rmaxw' & fl' & junk' & j8 & mh & -> & MUh & WMh & MIh & STh & FRh & FLOK' & FLCh & BMCh & RPCh & LJh & DBLKh).
  assert (CSTh : cstate st LBall LB L mh (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m mh sp _ tp lo B (bv_unsigned sp)); [exact CST| exact MUh| exact WMh| exact MIh| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbi, BI, nbi)); [exact INBI| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pd, D, max)); [exact (proj1 OWND)| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbm, BM, 32)); [exact (proj1 OWNM)| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (prp, RP, 32)); [exact INRP| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (_ & _ & _ & _ & I1). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (_ & _ & _ & _ & I2).
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM)) as (_ & _ & _ & _ & I3). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INRP) as (_ & _ & _ & _ & I4).
      clear - I1 I2 I3 I4 HNBI HMAX0 BI0 D0 BM0 RP0 LO SLO GLO. cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STh.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (write_T pbi pbm prp pd) [] (bv_unsigned sp) st LBall L m st LBall L mh).
  { eapply cframe_seg; [apply cframe_refl| exact MUh| exact WMh| exact HP| lia|]. unfold write_T.
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pbi, BI, nbi)); [exact INBI| intros b0 _ NT E; apply NT; left; exact E| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pd, D, max)); [exact (proj1 OWND)| intros b0 _ NT E; apply NT; do 3 right; exact E| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pbm, BM, 32)); [exact (proj1 OWNM)| intros b0 _ NT E; apply NT; right; left; exact E| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (prp, RP, 32)); [exact INRP| intros b0 _ NT E; apply NT; right; right; left; exact E| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (BBCh : rw_cells usegs mh BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]).
  { pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INBB NE_IB) as A4.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBB (proj1 OWNM) NE_BM) as A5.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBB INRP NE_BR) as A6.
    eapply rw_cells_transport; [exact BBC| exact MUh| exact WMh|]. clear - A4 A5 A6 APDB HNBI BBCe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI (proj1 OWND) NE_ID) as AI1.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI (proj1 OWNM) NE_IM) as AI2.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as AI3.
  assert (HDh : rw_cells usegs mh BI hd).
  { eapply rw_cells_transport; [exact HD| exact MUh| exact WMh|]. clear - AI1 AI2 AI3 HDZ HNBI BICe LO SLO. cbn [disjoint_from]. lia. }
  assert (TLh : rw_cells usegs mh (BI + 52) tl).
  { eapply rw_cells_transport; [exact TL| exact MUh| exact WMh|]. clear - AI1 AI2 AI3 TLZ HNBI BICe LO SLO. cbn [disjoint_from]. lia. }
  clear AI1 AI2 AI3.
  assert (SRCh : bytes_at usegs mh IN src).
  { eapply bytes_at_transport; [exact SRC| exact MUh|]. rewrite LSRC, Z2Nat.id by lia.
    destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)].
    - clear - SL BICe DCe BMCe RPCe LO SLO HNBI HMAX0 HINL. cbn [disjoint_from]. lia.
    - pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & _ & _ & SCe & _).
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INBI ltac:(intros E; apply NTS; left; exact E)) as A1.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS (proj1 OWND) ltac:(intros E; apply NTS; do 4 right; exact E)) as A2.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS (proj1 OWNM) ltac:(intros E; apply NTS; right; right; left; exact E)) as A3.
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INRP ltac:(intros E; apply NTS; do 3 right; left; exact E)) as A4.
      clear - A1 A2 A3 A4 S1 S2 SCe LO SLO HNBI HMAX0 HINL. cbn [disjoint_from]. lia. }
  clear APDB APDR.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply GROW with (pbm := pbm) (BM := BM) (pd := pd) (D := D) (len := len - off) (max := max) (nm := nm) (len' := len - off + inl) (junk := junk');
      [exact Hf| exact ROOM| exact CSTh
      | rewrite unsigned_lit by lia; unfold GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia
      | reflexivity| reflexivity| lia| exact OWNM| exact OWND| exact NE_MD| lia| lia| lia| exact BMCh| exact DBLKh]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & D' & jk & i & -> & -> & HI & -> & RNG & BMC1 & LJ1 & DB1)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  assert (NTB : ~ (pbb = pbm \/ pbb = pd)) by (intros [E|E]; [exact (NE_BM E)| exact (NE_BD E)]).
  assert (NTR : ~ (prp = pbm \/ prp = pd)) by (intros [E|E]; [apply NE_MR; symmetry; exact E| exact (NE_RD E)]).
  assert (NTI : ~ (pbi = pbm \/ pbi = pd)) by (intros [E|E]; [exact (NE_IM E)| exact (NE_ID E)]).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbb, BB, 16) CFR1 BBCh INBB NTB
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BBC1.
  unfold readp_cells in RPCh.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (prp, RP, 32) CFR1 RPCh INRP NTR
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as RPC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 FLCh INBI NTI
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as FLC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 HDh INBI NTI
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; lia)) as HD1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 TLh INBI NTI
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; lia)) as TL1.
  assert (SRC1 : bytes_at usegs m1 IN src).
  { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)].
    - eapply (cfr_bytes_stack _ _ _ _ _ _ _ _ CFR1 SRCh). lia.
    - eapply (cfr_bytes_block _ _ _ _ _ _ _ _ (ps, AS, ns) CFR1 SRCh INS); [intros [E|E]; apply NTS; [right; right; left; exact E| do 4 right; exact E]
                                                                            | unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]. }
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D'0 & _ & _ & D'Ce & _).
  (* [comment removed for export] *)
  assert (INQ : In (q, D', grow_n (len - off + inl)) ((q, D', grow_n (len - off + inl)) :: lb_remove pd LBall)) by (left; reflexivity).
  assert (KEEP : forall p A n, In (p, A, n) LBall -> p <> pd -> In (p, A, n) ((q, D', grow_n (len - off + inl)) :: lb_remove pd LBall)).
  { intros p A n H NE. right. apply lb_remove_In. split; [exact H| unfold blk_id; cbn [fst snd]; exact NE]. }
  assert (FRESH : forall p A n, In (p, A, n) LBall -> p <> pd -> p <> q).
  { intros p A n H NE. eapply cstate_head_fresh; [exact CST1| apply lb_remove_In; split; [exact H| unfold blk_id; cbn [fst snd]; exact NE]]. }
  assert (APQB : D' + grow_n (len - off + inl) <= BB \/ BB + 16 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (KEEP _ _ _ INBB NE_BD)); intros E; exact (FRESH _ _ _ INBB NE_BD (eq_sym E))).
  assert (APQM : D' + grow_n (len - off + inl) <= BM \/ BM + 32 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (KEEP _ _ _ (proj1 OWNM) NE_MD)); intros E; exact (FRESH _ _ _ (proj1 OWNM) NE_MD (eq_sym E))).
  assert (APQR : D' + grow_n (len - off + inl) <= RP \/ RP + 32 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (KEEP _ _ _ INRP NE_RD)); intros E; exact (FRESH _ _ _ INRP NE_RD (eq_sym E))).
  assert (APSQ : IN + inl <= D' \/ D' + grow_n (len - off + inl) <= IN).
  { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)]; [clear - SL D'Ce LO SLO HINL; lia|].
    assert (NSD : ps <> pd) by (intros E; apply NTS; do 4 right; exact E).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (KEEP _ _ _ INS NSD) ltac:(intros E; exact (FRESH _ _ _ INS NSD (eq_sym E)))) as A.
    clear - A S1 S2 HINL. lia. }
  clear APDM.
  unfold bufmem_cells in BMC1.
  (* [comment removed for export] *)
  cprefix.
  pose proof W1_write_tail_proof as TAIL. unfold W1_write_tail_stmt, bufmem_cells, readp_cells in TAIL.
  eapply evt_mono.
  { eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo (bv_unsigned sp) BB BM RP D' (len - off) (len - off + inl) (grow_n (len - off + inl)) inl IN
              (Z_to_bv 64 sec) _ _ _ _ jk src j8 ra s0 s1 s2 s3 s4 s5);
      try first [reflexivity | eassumption | exact (proj1 BBC1) | lia]. }
  clear TAIL. cbv beta.
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & jk' & m2 & -> & MU2 & WM2 & MI2 & ST2 & BMC2 & RPC2 & LJ2 & DB2).
  rewrite Z_to_bv_bv_unsigned.
  apply climpl_done.
  exists (Z_to_bv 64 inl), m2, ((q, D', grow_n (len - off + inl)) :: lb_remove pd LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| exact MI2| | lia| lia| | exact ST2| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, D', grow_n (len - off + inl))); [exact INQ| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (prp, RP, 32)); [exact (KEEP _ _ _ INRP NE_RD)| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - pose proof RNG as (_ & _ & _ & _ & I1). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INRP) as (_ & _ & _ & _ & I2).
      clear - I1 I2 HN D'0 RP0 LO SLO GLO. cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X|]| exact MU2| exact WM2| exact HP1| lia|].
    - intros q0 _ NT [E|E]; apply NT; unfold write_T; [right; left; exact E| do 3 right; exact E].
    - apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      + apply (cseg_ok_block _ _ _ _ _ (q, D', grow_n (len - off + inl))); [exact INQ| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
        intros b0 Hb0 NT E. destruct b0 as [[p0 A0] n0]. unfold blk_id in E, NT. cbn [fst snd] in E, NT.
        apply (FRESH p0 A0 n0 Hb0); [intros X; apply NT; unfold write_T; do 3 right; exact X| exact E].
      + apply (cseg_ok_block _ _ _ _ _ (prp, RP, 32)); [exact (KEEP _ _ _ INRP NE_RD)| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
        intros b0 _ NT E. apply NT. unfold write_T. right; right; left. exact E. }
  exists q, D', jk', i, fl'.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HI|]. split; [reflexivity|]. split; [exact RNG|]. split; [exact FLOK'|].
  split.
  { pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (KEEP _ _ _ INBI NE_ID) INQ (FRESH _ _ _ INBI NE_ID)) as A1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as A2.
    eapply rw_cells_transport; [exact FLC1| exact MU2| exact WM2|]. clear - A1 A2 HNBI BICe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  split; [exact BMC2|]. split; [exact RPC2|]. split; [exact LJ2|]. split; [exact DB2|].
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (KEEP _ _ _ INBI NE_ID) INQ (FRESH _ _ _ INBI NE_ID)) as A1.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as A2.
  split; (eapply rw_cells_transport; [| exact MU2| exact WM2|]); [exact HD1| | exact TL1|]; clear - A1 A2 HDZ TLZ HNBI BICe LO SLO; cbn [disjoint_from]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition write_new_res (BI BM RP inl sec : Z) (hd tl : list cell) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q D' jk fl', v = Z_to_bv 64 inl /\ LBall' = (q, D', grow_n inl) :: LBall /\ L' = (q, grow_n inl) :: L
     /\ rblock_range D' (grow_n inl)
     /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')]
     /\ rw_cells usegs m' BM (bufmem_cells inl D' (grow_n inl) (Z_to_bv 64 sec))
     /\ rw_cells usegs m' RP (readp_cells inl D' 0 (Z_to_bv 64 (grow_n inl)) (Z_to_bv 64 sec))
     /\ length jk = Z.to_nat (grow_n inl) /\ rw_cells usegs m' D' [CB (Z.to_nat (grow_n inl)) jk]
     /\ rw_cells usegs m' BI hd /\ rw_cells usegs m' (BI + 52) tl.

Definition W1_write_new_stmt (sec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbi : bptr) (BI nbi : Z) (pbb : bptr) (BB : Z) (pbm : bptr) (BM : Z) (prp : bptr) (RP fl inl IN : Z) (rmaxw rflw : word) (src : list byte) (hd tl : list cell),
  (1 <= f)%nat -> croom L (wA (grow_n inl)) (wB (grow_n inl)) (wBig (grow_n inl)) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - WRITE_STACK ->
  a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 inl -> 0 < inl < 1610612733 -> 0 < IN ->
  In (pbi, BI, nbi) LBall -> 72 <= nbi -> In (pbb, BB, 16) LBall -> cown LBall L pbm BM 32 32 -> In (prp, RP, 32) LBall ->
  (pbi <> pbb /\ pbi <> pbm /\ pbi <> prp /\ pbb <> pbm /\ pbb <> prp /\ pbm <> prp) ->
  ro_cells usegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl ->
  ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
  rw_cells usegs m BI hd -> Z.of_nat (cells_size hd) = 48 -> rw_cells usegs m (BI + 52) tl -> 52 + Z.of_nat (cells_size tl) <= nbi ->
  rw_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
  rw_cells usegs m BM (bufmem_cells 0 0 0 (Z_to_bv 64 sec)) -> rw_cells usegs m RP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 rmaxw; C8 rflw] ->
  bytes_at usegs m IN src -> length src = Z.to_nat inl -> src_loc LBall (fun q => q = pbi \/ q = pbb \/ q = pbm \/ q = prp) (bv_unsigned sp) IN inl ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_MEM_WRITE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = pbi \/ q = pbm \/ q = prp) [] 1
                (wA (grow_n inl)) (wB (grow_n inl)) (wBig (grow_n inl)) (write_new_res BI BM RP inl sec hd tl LBall L)).

Theorem W1_write_new_spec : forall sec, W1_grow_null_stmt sec -> W1_write_new_stmt sec.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros sec GROW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbi BI nbi pbb BB pbm BM prp RP fl inl IN rmaxw rflw src hd tl
         Hf ROOM CST SLO -> -> -> HINL HIN INBI HNBI INBB OWNM INRP PNE INITC FLC FLOK PTRC HD HDZ TL TLZ BBC BMC RPC SRC LSRC SLOC.
  destruct PNE as (NE_IB & NE_IM & NE_IR & NE_BM & NE_BR & NE_MR).
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (BI0 & BI16 & _ & BICe & _). assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBB) as (BB0 & BB16 & _ & BBCe & _). assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INRP) as (RP0 & RP16 & _ & RPCe & _). assert (RP8 : RP mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  assert (APMR : BM + 32 <= RP \/ RP + 32 <= BM) by (exact (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM) INRP NE_MR)).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI (proj1 OWNM) NE_IM) as APIM.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as APIR.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INBB NE_IB) as APIB.
  pose proof (grow_n_bounds inl HINL) as HN.
  pose proof (bytes_at_bound _ _ _ _ SRC) as INB. rewrite LSRC, Z2Nat.id in INB by lia.
  unfold WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_MEM_WRITE, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold bufmem_cells in BMC.
  (* [comment removed for export] *)
  cprefix. eapply evt_mono.
  { eapply (W1_write_head0_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BI BB BM RP fl inl IN (Z_to_bv 64 sec) rmaxw rflw);
      try first [reflexivity | eassumption | exact (proj1 BBC) | exact (proj1 BMC) | exact (proj1 RPC) | lia].
    unfold tbox. clear - APIM APIR APIB HNBI. repeat split; lia. }
  cbv beta. intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fl' & j8 & mh & -> & MUh & WMh & MIh & STh & FRh & FLOK' & FLCh).
  assert (CSTh : cstate st LBall LB L mh (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m mh sp _ tp lo B (bv_unsigned sp)); [exact CST| exact MUh| exact WMh| exact MIh| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbi, BI, nbi)); [exact INBI| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBI) as (_ & _ & _ & _ & I1).
      clear - I1 HNBI BI0 LO SLO GLO. cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STh.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = pbi \/ q = pbm \/ q = prp) [] (bv_unsigned sp) st LBall L m st LBall L mh).
  { eapply cframe_seg; [apply cframe_refl| exact MUh| exact WMh| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pbi, BI, nbi)); [exact INBI| intros b0 _ NT E; apply NT; left; exact E| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  assert (BBCh : rw_cells usegs mh BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]).
  { eapply rw_cells_transport; [exact BBC| exact MUh| exact WMh|]. clear - APIB HNBI BBCe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (HDh : rw_cells usegs mh BI hd).
  { eapply rw_cells_transport; [exact HD| exact MUh| exact WMh|]. clear - HDZ HNBI BICe LO SLO. cbn [disjoint_from]. lia. }
  assert (TLh : rw_cells usegs mh (BI + 52) tl).
  { eapply rw_cells_transport; [exact TL| exact MUh| exact WMh|]. clear - TLZ HNBI BICe LO SLO. cbn [disjoint_from]. lia. }
  assert (BMCh : rw_cells usegs mh BM [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sec)]).
  { eapply rw_cells_transport; [exact BMC| exact MUh| exact WMh|]. clear - APIM HNBI BMCe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (RPCh : rw_cells usegs mh RP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 rmaxw; C8 rflw]).
  { eapply rw_cells_transport; [exact RPC| exact MUh| exact WMh|]. clear - APIR HNBI RPCe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (SRCh : bytes_at usegs mh IN src).
  { eapply bytes_at_transport; [exact SRC| exact MUh|]. rewrite LSRC, Z2Nat.id by lia.
    destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)].
    - clear - SL BICe LO SLO HNBI HINL. cbn [disjoint_from]. lia.
    - pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & _ & _ & SCe & _).
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INBI ltac:(intros E; apply NTS; left; exact E)) as A1.
      clear - A1 S1 S2 SCe LO SLO HNBI HINL. cbn [disjoint_from]. lia. }
  clear APIM APIR APIB.
  eapply climpl_seq.
  { eapply GROW with (pbm := pbm) (BM := BM) (len' := inl);
      [exact Hf| exact ROOM| exact CSTh
      | rewrite unsigned_lit by lia; unfold GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia
      | reflexivity| reflexivity| lia| exact OWNM| unfold bufmem_cells; exact BMCh]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & D' & jk & -> & -> & -> & RNG & BMC1 & LJ1 & DB1)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbb, BB, 16) CFR1 BBCh INBB ltac:(intros E; apply NE_BM; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BBC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (prp, RP, 32) CFR1 RPCh INRP ltac:(intros E; exact (NE_MR E))
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as RPC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 FLCh INBI ltac:(intros E; apply NE_IM; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as FLC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 HDh INBI ltac:(intros E; apply NE_IM; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; lia)) as HD1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbi, BI, nbi) CFR1 TLh INBI ltac:(intros E; apply NE_IM; symmetry; exact E)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; lia)) as TL1.
  assert (SRC1 : bytes_at usegs m1 IN src).
  { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)].
    - eapply (cfr_bytes_stack _ _ _ _ _ _ _ _ CFR1 SRCh). lia.
    - eapply (cfr_bytes_block _ _ _ _ _ _ _ _ (ps, AS, ns) CFR1 SRCh INS); [intros E; apply NTS; right; right; left; symmetry; exact E
                                                                            | unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]. }
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D'0 & _ & _ & D'Ce & _).
  assert (INQ : In (q, D', grow_n inl) ((q, D', grow_n inl) :: LBall)) by (left; reflexivity).
  assert (FRESH : forall p A n, In (p, A, n) LBall -> p <> q) by (intros p A n H; eapply cstate_head_fresh; [exact CST1| exact H]).
  assert (APQB : D' + grow_n inl <= BB \/ BB + 16 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (or_intror INBB)); intros E; exact (FRESH _ _ _ INBB (eq_sym E))).
  assert (APQM : D' + grow_n inl <= BM \/ BM + 32 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (or_intror (proj1 OWNM))); intros E; exact (FRESH _ _ _ (proj1 OWNM) (eq_sym E))).
  assert (APQR : D' + grow_n inl <= RP \/ RP + 32 <= D')
    by (apply (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (or_intror INRP)); intros E; exact (FRESH _ _ _ INRP (eq_sym E))).
  assert (APSQ : IN + inl <= D' \/ D' + grow_n inl <= IN).
  { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)]; [clear - SL D'Ce LO SLO HINL; lia|].
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INQ (or_intror INS) ltac:(intros E; exact (FRESH _ _ _ INS (eq_sym E)))) as A.
    clear - A S1 S2 HINL. lia. }
  unfold bufmem_cells in BMC1.
  cprefix.
  pose proof W1_write_tail_proof as TAIL. unfold W1_write_tail_stmt, bufmem_cells, readp_cells in TAIL.
  eapply evt_mono.
  { eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo (bv_unsigned sp) BB BM RP D' 0 inl (grow_n inl) inl IN
              (Z_to_bv 64 sec) _ _ _ _ jk src j8 ra s0 s1 s2 s3 s4 s5);
      try first [reflexivity | eassumption | exact (proj1 BBC1) | lia]. }
  clear TAIL. cbv beta.
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & jk' & m2 & -> & MU2 & WM2 & MI2 & ST2 & BMC2 & RPC2 & LJ2 & DB2).
  rewrite Z_to_bv_bv_unsigned.
  apply climpl_done.
  exists (Z_to_bv 64 inl), m2, ((q, D', grow_n inl) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| exact MI2| | lia| lia| | exact ST2| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, D', grow_n inl)); [exact INQ| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (prp, RP, 32)); [right; exact INRP| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - pose proof RNG as (_ & _ & _ & _ & I1). pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INRP) as (_ & _ & _ & _ & I2).
      clear - I1 I2 HN D'0 RP0 LO SLO GLO. cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X|]| exact MU2| exact WM2| exact HP1| lia|].
    - intros q0 _ NT E. apply NT. right; left. symmetry. exact E.
    - apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      + apply (cseg_ok_block _ _ _ _ _ (q, D', grow_n inl)); [exact INQ| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
        intros b0 Hb0 NT E. destruct b0 as [[p0 A0] n0]. unfold blk_id in E. cbn [fst snd] in E. exact (FRESH p0 A0 n0 Hb0 E).
      + apply (cseg_ok_block _ _ _ _ _ (prp, RP, 32)); [right; exact INRP| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
        intros b0 _ NT E. apply NT. right; right. exact E. }
  exists q, D', jk', fl'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; [exact FLOK'|].
  split.
  { pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror INBI) INQ (FRESH _ _ _ INBI)) as A1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as A2.
    eapply rw_cells_transport; [exact FLC1| exact MU2| exact WM2|]. clear - A1 A2 HNBI BICe LO SLO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  replace (0 + inl) with inl in * by lia.
  split; [exact BMC2|]. split; [exact RPC2|]. split; [exact LJ2|]. split; [exact DB2|].
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror INBI) INQ (FRESH _ _ _ INBI)) as A1.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INBI INRP NE_IR) as A2.
  split; (eapply rw_cells_transport; [| exact MU2| exact WM2|]); [exact HD1| | exact TL1|]; clear - A1 A2 HDZ TLZ HNBI BICe LO SLO; cbn [disjoint_from]; lia.
Qed.
End WithCeiling0.
