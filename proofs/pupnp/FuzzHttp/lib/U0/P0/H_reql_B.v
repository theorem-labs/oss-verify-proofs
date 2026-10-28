(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_sscanf H_scanner_get_token H_vfmatch_A H_vfmatch_G2 H_match H_obj
     H_membuffer_assign H_str_alloc H_map_str_to_int H_memptr_cmp H_parse_uri_A H_parse_uri H_httpmsg_destroy H_UpnpPrintf H_prep
     H_presp_B H_presp_C H_entity_read_method H_phdr_B H_pent_A H_ListAddTail H_freelist H_pparse_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_reql_A H_reql_V HU_reql_vt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition zmod8 (x : Z) : Prop := (x mod 8 = 0)%Z.
Definition zmod16 (x : Z) : Prop := (x mod 16 = 0)%Z.

Lemma disjoint_from_Forall : forall (W : list ivl) X n,
  Forall (fun iv => snd iv <= X \/ X + n <= fst iv)%Z W -> disjoint_from W X n.
Proof.
  induction W as [|[l h] W IH]; intros X n F; cbn; [exact I|].
  inversion F as [|? ? Hiv F']; subst. cbn in Hiv. split; [lia| apply IH; exact F'].
Qed.

Lemma table_strings_mono : forall ws ne B B', table_strings ws ne B -> (B <= B')%Z -> table_strings ws ne B'.
Proof.
  intros ws ne B B' TS LE i Hi. destruct (TS i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5).
  exists S, str, slack. repeat (split; [assumption|]). lia.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L_ = 0x180f0.
  Hypothesis TPV : al_tp L_ = 0x3b820.
  Hypothesis ERRNOV : al_errno L_ = 0x3b77c.
  Hypothesis CAN : canary_ok AI.
  Hypothesis ERRNC : forall lo hi, al_client_static L_ lo hi -> hi <= al_errno L_ \/ al_errno L_ + 4 <= lo.
  Hypothesis BLK4096 : blk4096_ok AI.
  Hypothesis BLKIMG : blk_img_ok AI.
  Hypothesis SNC : strncasecmp_stmt.

  Hypothesis GOTGIFST : exists lo hi, al_client_static L_ lo hi /\ lo <= GOT_GIF /\ GOT_GIF + 8 <= hi.
  Hypothesis GOTGMAXST : exists lo hi, al_client_static L_ lo hi /\ lo <= GOT_GMAX /\ GOT_GMAX + 8 <= hi.
  Hypothesis TABST : exists lo hi, al_client_static L_ lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi.
  Hypothesis ZST : exists lo hi, al_client_static L_ lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi.
  Hypothesis MTST : exists lo hi, al_client_static L_ lo hi /\ lo <= METHOD_TAB /\ METHOD_TAB + 176 <= hi.
  Hypothesis GIFST : exists lo hi, al_client_static L_ lo hi /\ lo <= GIF /\ GIF + 4 <= hi.
  Hypothesis GMST : exists lo hi, al_client_static L_ lo hi /\ lo <= GMAXA /\ GMAXA + 8 <= hi.
  Hypothesis IWST : exists lo hi, al_client_static L_ lo hi /\ lo <= INITWASCALLED /\ INITWASCALLED + 1 <= hi.

  #[using="Type"] Lemma mown_heap_pres : forall m m' (LB LB' : list BLK) A0 cap0 (ok : option K) bs0 SP,
    mown AI m LB A0 cap0 ok bs0 -> heap_pres AI (okb AI ok A0 cap0) SP m m' -> (0 <= cap0)%Z -> (forall b, In b LB -> In b LB') -> mown AI m' LB' A0 cap0 ok bs0.
  Proof.
    intros m m' LB LB' A0 cap0 [k|] bs0 SP OWN HP HC SUB; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [apply SUB; exact HIN|].
    eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact BLK|]. eapply client_range_block; [left; reflexivity| cbn; lia|].
    cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
  Qed.

  Section ARM.

    Variables (P q lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list BLK) (m0 : mem).
    Variables (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word).
    Hypothesis QLO : (lo + PP_DEPTH <= q + 208)%Z.
    Hypothesis QLO2 : (lo <= q + 208 - PP_ADEPTH - al_stack L_)%Z.
    Hypothesis STK0 : (0 <= al_stack L_)%Z.
    Hypothesis LO0 : (0x5d000 <= lo)%Z.
    Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
    Hypothesis QP : (q + 208 <= P)%Z.
    Hypothesis PB : (P + 504 <= B)%Z.
    Hypothesis BHI : (B < 2^62)%Z.
    Hypothesis P8 : zmod8 P.
    Hypothesis Q16 : zmod16 (q + 208).
    Hypothesis HT : hdr_tab_ok ws lo.
    Hypothesis MT : meth_tab_ok mws lo.
    Hypothesis GMX : (0 < gmax < 2^32)%Z.

    #[using="B PB BHI"] Lemma PHI63 : (P + 504 < 2^63)%Z. Proof. lia. Qed.
    #[using="QLO"] Lemma QLO1 : (lo <= q)%Z. Proof. unfold PP_DEPTH in QLO. lia. Qed.
    #[using="lo MT"] Lemma MWSL : length mws = 22%nat. Proof. exact (proj1 MT). Qed.
    #[using="lo MT"] Lemma MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
    Proof. intros i Hi. destruct (proj1 (proj2 MT) i Hi) as (id & H1 & H2). exists id. split; [exact H1| lia]. Qed.

    Notation S := (P + 480)%Z.
    Notation MB := (P + 400)%Z.
    Notation PST := (pp_st AI P q).
    Notation S7 := (wz (P + 8)). Notation S8 := (wz (P + 276)). Notation S9 := (wz (P + 280)).
    Notation FXC := [C8 S9; C8 S8; C8 S7; C8 (wz (2^64 - 1 - MTAB)); C8 (wz FMTREQ)].

    Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m :=
      (MS (mkR x1 (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom rsegs)).

    Variables (A len cap : Z) (okm : option K) (rm sc SA slen scap : Z) (sok : option K) (sbs : list byte)
              (isreq : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z) (ebw elw : word) (hack entp clen csz esp : Z).

    Definition stof (bs : list byte) (cur meth : Z) (uc : list cell) (maj min err pos ub : Z) (UB : list BLK) : pstate AI :=
      mkPS cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB.

    Definition RQ (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (bs : list byte) (cur meth : Z) (uc : list cell) (maj min err pos ub : Z) (UB : list BLK) : Prop :=
      RHEAP rsegs AI s LB m /\ RENV rsegs AI m B /\ mem_inv rsegs m /\ stk rsegs m lo q
      /\ (exists e, rw_cells rsegs m (al_errno L_) [C4 e])
      /\ rw_cells rsegs m (q + 104) (ppFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) /\ rw_cells rsegs m (q + 16) FXC
      /\ p_parser AI m LB P (stof bs cur meth uc maj min err pos ub UB)
      /\ bsub AI (ps_blocks AI (stof bs cur meth uc maj min err pos ub UB) ++ LBK) LB
      /\ NoDup (map blk_id (ps_blocks AI (stof bs cur meth uc maj min err pos ub UB) ++ LBK))
      /\ pp_stat m gmax gifv ws mws
      /\ hpx AI (pp_W P) LBK (q + 208) m0 m.

    Ltac open_RQ H :=
      destruct H as (HR & HE & MI & ST & [errv ERR] & FSH & F32 & PP & BSUB & ND & STAT & HPX).
    Ltac open_PP H :=
      destruct H as (PSC & PMSG & CUR & PMETH & PURI & PRS_ & PSM & PVER & PHL & XV & PENT & PCTL & PURL & UBO); cbn [stof
        ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min
        ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in *.

    Definition rqFX (m : mem) (c8 : list cell) (c40 : list cell) : Prop :=
      (exists j0, rw_cells rsegs m q [C8 j0]) /\ rw_cells rsegs m (q + 8) c8 /\ cells_size c8 = 8%nat
      /\ rw_cells rsegs m (q + 56) c40 /\ cells_size c40 = 48%nat.

    #[using="Type"] Lemma ppFX_split : forall m, ppFX P q m ->
      rw_cells rsegs m (q + 16) FXC
      /\ exists j0 j8 j40 j48 ja jb j64 j72 j80,
           rw_cells rsegs m q [C8 j0] /\ rw_cells rsegs m (q + 8) [C8 j8]
           /\ rw_cells rsegs m (q + 56) [C8 j40; C8 j48] /\ rw_cells rsegs m (q + 72) [C4 ja; C4 jb] /\ rw_cells rsegs m (q + 80) [C8 j64]
           /\ rw_cells rsegs m (q + 88) [C8 j72; C8 j80].
    Proof.
      intros m ([j1 Q0] & Q32 & [j2 Q40]). split; [exact Q32|].
      pose proof (rw_cells_split_CB rsegs m q [] 16 j1 [] [8; 8]%nat Q0 eq_refl) as A0. cbn [app mk_CB_cells] in A0.
      pose proof (rw_cells_CB_C8 rsegs m q [] _ _ A0) as A1. cbn [app] in A1.
      pose proof (rw_cells_CB_C8 rsegs m q [_] _ _ A1) as A2. cbn [app] in A2.
      lazymatch type of A2 with rw_cells _ _ _ [?c0; ?c1] =>
        destruct (proj1 (rw_cells_app rsegs m q [c0] [c1]) A2) as [B0 B8] end. cbn [cells_size csize Nat.add] in B8.
      pose proof (rw_cells_split_CB rsegs m (q + 56) [] 48 j2 [] [8; 8; 4; 4; 8; 8; 8]%nat Q40 eq_refl) as C0. cbn [app mk_CB_cells] in C0.
      pose proof (rw_cells_CB_C8 rsegs m (q + 56) [] _ _ C0) as C1. cbn [app] in C1.
      pose proof (rw_cells_CB_C8 rsegs m (q + 56) [_] _ _ C1) as C2. cbn [app] in C2.
      pose proof (rw_cells_CB_C4 rsegs m (q + 56) [_; _] _ _ C2) as C3. cbn [app] in C3.
      pose proof (rw_cells_CB_C4 rsegs m (q + 56) [_; _; _] _ _ C3) as C4'. cbn [app] in C4'.
      pose proof (rw_cells_CB_C8 rsegs m (q + 56) [_; _; _; _] _ _ C4') as C5. cbn [app] in C5.
      pose proof (rw_cells_CB_C8 rsegs m (q + 56) [_; _; _; _; _] _ _ C5) as C6. cbn [app] in C6.
      pose proof (rw_cells_CB_C8 rsegs m (q + 56) [_; _; _; _; _; _] _ _ C6) as C7. cbn [app] in C7.
      lazymatch type of C7 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6] =>
        destruct (proj1 (rw_cells_app rsegs m (q + 56) [c0; c1] [c2; c3; c4; c5; c6]) C7) as [D40 D56];
        cbn [cells_size csize Nat.add] in D56;
        destruct (proj1 (rw_cells_app rsegs m (q + 56 + 16) [c2; c3] [c4; c5; c6]) D56) as [D56' D64];
        cbn [cells_size csize Nat.add] in D64;
        destruct (proj1 (rw_cells_app rsegs m (q + 56 + 16 + 8) [c4] [c5; c6]) D64) as [D64' D72];
        cbn [cells_size csize Nat.add] in D72 end.
      lazymatch type of D56' with rw_cells _ _ ?a _ => replace a with (q + 72)%Z in D56' by lia end.
      lazymatch type of D64' with rw_cells _ _ ?a _ => replace a with (q + 80)%Z in D64' by lia end.
      lazymatch type of D72 with rw_cells _ _ ?a _ => replace a with (q + 88)%Z in D72 by lia end.
      lazymatch type of B8 with rw_cells _ _ ?a _ => replace a with (q + 8)%Z in B8 by lia end.
      do 9 eexists. split; [exact B0|]. split; [exact B8|]. split; [exact D40|]. split; [exact D56'|]. split; [exact D64'| exact D72].
    Qed.

    #[using="Type"] Lemma ppFX_merge : forall m c8 c40, rqFX m c8 c40 -> rw_cells rsegs m (q + 16) FXC -> ppFX P q m.
    Proof.
      intros m c8 c40 ([j0 Q0] & Q8 & S8 & Q40 & S40) Q32. split; [| split; [exact Q32|]].
      - pose proof (proj2 (rw_cells_app rsegs m q [C8 j0] c8)) as J. cbn [cells_size csize Nat.add] in J. specialize (J (conj Q0 Q8)).
        destruct (rw_cells_forget rsegs m q _ J) as [jk F]. cbn [cells_size csize app] in F. rewrite cells_size_app in F || idtac. cbn [cells_size csize] in F. rewrite S8 in F. eexists. exact F.
      - destruct (rw_cells_forget rsegs m (q + 56) _ Q40) as [jk F]. rewrite S40 in F. eexists. exact F.
    Qed.

    Definition HI64 : Z := 2^64.

    Definition wcls (LBw : list BLK) (iv : ivl) : Prop :=
      ((lo <= fst iv /\ snd iv <= q) \/ (q <= fst iv /\ snd iv <= q + 16) \/ (q + 56 <= fst iv /\ snd iv <= q + 104))%Z
      \/ ((P + 4 <= fst iv /\ snd iv <= P + 224) \/ (P + 276 <= fst iv /\ snd iv <= P + 284) \/ (P + 432 <= fst iv /\ snd iv <= P + 452) \/ (P + 488 <= fst iv /\ snd iv <= P + 496))%Z
      \/ (fst iv = al_errno L_ /\ snd iv = al_errno L_ + 4)%Z
      \/ (exists b, In b LBw /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z.

    #[using="LOK ERRNOV ERRNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO LO0 CEIL QP PB HT MT"] Lemma rq_seg : forall s LB m m' W (LBw OB : list BLK),
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> hpx AI (pp_W P) LBK (q + 208) m0 m ->
      bsub AI (OB ++ LBK) LB -> NoDup (map blk_id (OB ++ LBK)) -> (forall b, In b LBw -> In b OB) ->
      munch W m m' -> wmono rsegs m m' -> Forall (wcls LBw) W ->
      rw_cells rsegs m (q + 104) (ppFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) -> rw_cells rsegs m (q + 16) FXC ->
      p_rs m P rm sc -> p_ent m P ebw elw ->
      pp_stat m gmax gifv ws mws ->
      RHEAP rsegs AI s LB m' /\ RENV rsegs AI m' B /\ hpx AI (pp_W P) LBK (q + 208) m0 m'
      /\ rw_cells rsegs m' (q + 104) (ppFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) /\ rw_cells rsegs m' (q + 16) FXC
      /\ p_rs m' P rm sc /\ p_ent m' P ebw elw
      /\ pp_stat m' gmax gifv ws mws
      /\ (forall (LBh : list BLK), (forall b, In b LBh -> In b OB) -> (forall b b', In b LBh -> In b' LBw -> b <> b') -> heap_pres AI LBh HI64 m m')
      /\ (forall X0 n, (q <= X0)%Z -> (X0 + Z.of_nat n <= P + 4 \/ (P + 224 <= X0 /\ X0 + Z.of_nat n <= P + 276) \/ (P + 284 <= X0 /\ X0 + Z.of_nat n <= P + 432)
                                     \/ (P + 452 <= X0 /\ X0 + Z.of_nat n <= P + 488) \/ P + 496 <= X0)%Z ->
                      (X0 + Z.of_nat n <= P + 504)%Z -> (X0 + Z.of_nat n <= q \/ (q + 16 <= X0 /\ X0 + Z.of_nat n <= q + 56) \/ q + 104 <= X0)%Z ->
                      disjoint_from W X0 (Z.of_nat n)).
    Proof.
      intros s LB m m' W LBw OB HR HE HP BSUB ND SUBW MU WM FW FSH F32 PRS_ PENT STAT.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO1 as QLO1'.
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3. rewrite ERRNOV in WE1, WE2.
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBO SUBK].
      assert (SUBW' : forall b, In b LBw -> In b LB) by (intros b Hb; apply SUBO; apply SUBW; exact Hb).
      assert (BWR : forall b, In b LBw -> (0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling /\ (blk_addr b + blk_size b <= fst we \/ snd we <= blk_addr b))%Z).
      { intros b Hb. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (R1 & _ & _ & R4 & RF).
        pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia. }
      assert (DJW : forall X0 n, (forall iv, In iv W -> wcls LBw iv -> snd iv <= X0 \/ X0 + Z.of_nat n <= fst iv)%Z -> disjoint_from W X0 (Z.of_nat n)).
      { intros X0 n HX. apply disjoint_from_Forall. apply List.Forall_forall. intros iv Hiv. apply (HX iv Hiv). exact (proj1 (List.Forall_forall _ _) FW iv Hiv). }

      assert (UP : forall X0 n, (q <= X0)%Z -> (X0 + Z.of_nat n <= P + 4 \/ (P + 224 <= X0 /\ X0 + Z.of_nat n <= P + 276) \/ (P + 284 <= X0 /\ X0 + Z.of_nat n <= P + 432)
                                     \/ (P + 452 <= X0 /\ X0 + Z.of_nat n <= P + 488) \/ P + 496 <= X0)%Z ->
                      (X0 + Z.of_nat n <= P + 504)%Z -> (X0 + Z.of_nat n <= q \/ (q + 16 <= X0 /\ X0 + Z.of_nat n <= q + 56) \/ q + 104 <= X0)%Z ->
                      disjoint_from W X0 (Z.of_nat n)).
      { intros X0 n H1 H2 H3 H4. apply DJW. intros [l' h'] _ C. unfold wcls in C. cbn in *. destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; [lia| lia| lia|].
        destruct (BWR b Hb) as (R1 & R4 & _). lia. }

      assert (LOWS : forall X0 n, (X0 + Z.of_nat n <= lo)%Z -> (X0 + Z.of_nat n <= al_errno L_ \/ al_errno L_ + 4 <= X0)%Z ->
                   (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat n <= shi)%Z -> disjoint_from W X0 (Z.of_nat n)).
      { intros X0 n H1 H2 (slo & shi & Hst & H3 & H4). destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1' & W2').
        apply DJW. intros [l' h'] _ C. unfold wcls in C. cbn in *. destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; [lia| lia| lia|].
        destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (_ & _ & _ & _ & RF).
        pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1. lia. }

      assert (LOWSB : forall X0 (xs : list byte), bytes_at rsegs m X0 xs -> (X0 + Z.of_nat (length xs) <= lo)%Z -> (X0 + Z.of_nat (length xs) <= al_errno L_ \/ al_errno L_ + 4 <= X0)%Z ->
                   (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat (length xs) <= shi)%Z -> bytes_at rsegs m' X0 xs).
      { intros X0 xs BX H1 H2 H3. eapply bytes_at_transport; [exact BX| exact MU| apply LOWS; assumption]. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
               destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [left; lia| left; lia| right; right; left; lia| right; right; right].
               exists b. split; [exact (SUBW' b Hb)| cbn; lia]. }
      split. { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
               destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [left; lia| left; lia| right; right; left; lia| right; right; right].
               exists b. split; [exact (SUBW' b Hb)| cbn; lia]. }
      split. { eapply (hpx_trans rsegs AI); [exact HP|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU| exact WM|].
               eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
               destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *.
               - left. lia.
               - right; right. unfold pp_W, inside. cbn. lia.
               - right; left. intros a Ha [Hc|[(slo & shi & Hst & Hr)|(b0 & Hb0 & Hr0)]]; [lia| |].
                 + pose proof (ERRNC slo shi Hst). rewrite ERRNOV in *. lia.
                 + destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBK b0 Hb0)) as (_ & _ & _ & _ & RF).
                   pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia.
               - right; left. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact (SUBW' b Hb)| | lia| lia].
                 intros b0 Hb0. split; [exact (SUBK b0 Hb0)|]. intros ->. exact (nodup_in_neq AI _ _ _ _ ND (SUBW b Hb) Hb0 eq_refl). }
      split. { eapply rw_cells_transport; [exact FSH| exact MU| exact WM|]. unfold ppFS. cbn [cells_size csize Nat.add]. apply UP; lia. }
      split. { eapply rw_cells_transport; [exact F32| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
      split. { destruct PRS_ as [RC RR]. split; [| exact RR]. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
      split. { unfold p_ent in *. eapply rw_cells_transport; [exact PENT| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
      split. { destruct STAT as (TAB & [zb ZB] & MTB & GG & GI & GM & IW & GGM).
               destruct TABST as (l1 & h1 & ST1 & ? & ?). destruct ZST as (l2 & h2 & ST2 & ? & ?). destruct MTST as (l3 & h3 & ST3 & ? & ?).
               destruct GIFST as (l4 & h4 & ST4 & ? & ?). destruct GMST as (l5 & h5 & ST5 & ? & ?). destruct IWST as (l6 & h6 & ST6 & ? & ?).
               destruct GOTGIFST as (l7 & h7 & ST7 & ? & ?). destruct GOTGMAXST as (l8 & h8 & ST8 & ? & ?).
               pose proof (ERRNC _ _ ST1). pose proof (ERRNC _ _ ST2). pose proof (ERRNC _ _ ST3). pose proof (ERRNC _ _ ST4). pose proof (ERRNC _ _ ST5). pose proof (ERRNC _ _ ST6). pose proof (ERRNC _ _ ST7). pose proof (ERRNC _ _ ST8).
               destruct (lo_static_img rsegs AI LOK _ _ ST1) as (w1 & Hw1 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w1 Hw1).
               destruct (lo_static_img rsegs AI LOK _ _ ST2) as (w2 & Hw2 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w2 Hw2).
               destruct (lo_static_img rsegs AI LOK _ _ ST3) as (w3 & Hw3 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w3 Hw3).
               destruct (lo_static_img rsegs AI LOK _ _ ST4) as (w4 & Hw4 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w4 Hw4).
               destruct (lo_static_img rsegs AI LOK _ _ ST5) as (w5 & Hw5 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w5 Hw5).
               destruct (lo_static_img rsegs AI LOK _ _ ST6) as (w6 & Hw6 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w6 Hw6).
               destruct (lo_static_img rsegs AI LOK _ _ ST7) as (w7 & Hw7 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w7 Hw7).
               destruct (lo_static_img rsegs AI LOK _ _ ST8) as (w8 & Hw8 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w8 Hw8).
               pose proof (proj1 HT) as WSL66. pose proof MWSL as WSL22.
               split. { eapply u64arr_transport; [exact TAB| exact MU| exact WM|]. rewrite WSL66. apply (LOWS TAB_HDR 528%nat); [cbn; lia| cbn; lia| exists l1, h1; split; [exact ST1| cbn; lia]]. }
               split. { exists zb. apply (LOWSB ZERO_ADDR [zb] ZB); [cbn; lia| cbn; lia| exists l2, h2; split; [exact ST2| cbn; lia]]. }
               split. { eapply u64arr_transport; [exact MTB| exact MU| exact WM|]. rewrite WSL22. apply (LOWS MTAB 176%nat); [cbn; lia| cbn; lia| exists l3, h3; split; [exact ST3| cbn; lia]]. }
               split. { apply (LOWSB GOT_GIF (le8 (wz GIF)) GG); rewrite ?length_le8; [cbn; lia| cbn; lia| exists l7, h7; split; [exact ST7| cbn; lia]]. }
               split. { apply (LOWSB GIF (le4 gifv) GI); rewrite ?length_le4; [cbn; lia| cbn; lia| exists l4, h4; split; [exact ST4| cbn; lia]]. }
               split. { eapply rw_cells_transport; [exact GM| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply (LOWS GMAXA 8%nat); [cbn; lia| cbn; lia| exists l5, h5; split; [exact ST5| cbn; lia]]. }
               split. { eapply rw_cells_transport; [exact IW| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply (LOWS INITWASCALLED 1%nat); [cbn; lia| cbn; lia| exists l6, h6; split; [exact ST6| cbn; lia]]. }
               apply (LOWSB GOT_GMAX (le8 (wz GMAXA)) GGM); rewrite ?length_le8; [cbn; lia| cbn; lia| exists l8, h8; split; [exact ST8| cbn; lia]]. }
      split.
      { intros LBh S1 S2 a Ha Hc. split; [| intros Hw; apply WM; exact Hw].
        unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. apply E.
        apply outside_of_forall. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
        destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b0 & Hb0 & Hr0)]]; [unfold HI64 in Hc; lia| |].
        - destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1' & W2'). pose proof (lo_img_ceiling rsegs AI LOK w Hw).
          pose proof (ERRNC slo shi Hst).
          destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [lia| lia| lia|].
          destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (_ & _ & _ & _ & RF).
          pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X0. cbn in X0. lia.
        - destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBO b0 (S1 b0 Hb0))) as (_ & _ & _ & R4 & RF).
          destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [lia| lia| |].
          + pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia.
          + pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR (SUBO b0 (S1 b0 Hb0)) (SUBW' b Hb) (S2 b0 b Hb0 Hb)). lia. }
      exact UP.
    Qed.

    Notation POST gp F fc st0 := (reql_post AI P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e gp F fc st0).

    #[using="Type"] Lemma rq_exit : forall s LB m bs cur meth uc maj min err pos ub UB c8 c40 (r : Z) (st0 : pstate AI)
        gp (F : bvmap 5 word) fc x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs cur meth uc maj min err pos ub UB -> rqFX m c8 c40 -> ps_isreq st0 = isreq -> (0 <= r <= 5)%Z ->
      (r = 4 -> pos = 2 /\ meth <= 11 /\ X + 2 * (len - cur) <= VMAX /\ entp = 1)%Z ->
      SREACH AI (POST gp F fc st0) (PRS HEAD x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros until t6. intros INV FX ISR RR R4. pose proof INV as INV'. open_RQ INV.
      apply sreach_ret. unfold reql_post. do 17 eexists. exists m, r, (stof bs cur meth uc maj min err pos ub UB).
      split; [reflexivity|]. split.
      { split; [exact HR|]. split; [exact HE|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact ERR|]. split; [exact FSH|].
        split; [eapply ppFX_merge; [exact FX| exact F32]|]. split; [exact PP|]. split; [exact BSUB|]. split; [exact ND|]. split; [exact STAT| exact HPX]. }
      split; [cbn; symmetry; exact ISR|]. split; [exact RR|].
      intros E. destruct (R4 E) as (-> & M11 & BUD & E1). split; [reflexivity|].
      unfold pp_side. cbn. unfold POS_ENTITY, POS_HEADERS, POS_RESPONSE_LINE. repeat split; intros; try lia.
    Qed.

    #[using="Type"] Lemma rq_entry : forall s LB m (st : pstate AI),
      pp_core AI P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s LB m st ->
      st = stof (ps_bs st) (ps_cur st) (ps_meth st) (ps_uc st) (ps_maj st) (ps_min st) (ps_err st) (ps_pos st) (ps_ub st) (ps_UB st) ->
      RQ s LB m (ps_bs st) (ps_cur st) (ps_meth st) (ps_uc st) (ps_maj st) (ps_min st) (ps_err st) (ps_pos st) (ps_ub st) (ps_UB st)
      /\ exists j0 j8 j40 j48 ja jb j64 j72 j80,
           rw_cells rsegs m q [C8 j0] /\ rw_cells rsegs m (q + 8) [C8 j8]
           /\ rw_cells rsegs m (q + 56) [C8 j40; C8 j48] /\ rw_cells rsegs m (q + 72) [C4 ja; C4 jb] /\ rw_cells rsegs m (q + 80) [C8 j64]
           /\ rw_cells rsegs m (q + 88) [C8 j72; C8 j80].
    Proof.
      intros s LB m st (HR & HE & MI & ST & ERR & FSH & FX & PP & BSUB & ND & STAT & HPX) EST.
      destruct (ppFX_split m FX) as [F32 REST]. split; [| exact REST].
      rewrite EST in PP, BSUB, ND.
      split; [exact HR|]. split; [exact HE|]. split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact FSH|]. split; [exact F32|].
      split; [exact PP|]. split; [exact BSUB|]. split; [exact ND|]. split; [exact STAT| exact HPX].
    Qed.

    #[using="BLK4096 BLKIMG gmax gifv m0 GMX"] Lemma msg_factsR : forall s LB m bs0, RHEAP rsegs AI s LB m -> p_msg AI m LB P A len cap okm bs0 ->
      bytes_at rsegs m A bs0 /\ (Z.of_nat (length bs0) >= len)%Z /\ (0 < A \/ (A = 0 /\ len = 0))%Z /\ (A + Z.of_nat (length bs0) <= alloc_ceiling)%Z
      /\ (0 <= len <= cap)%Z /\ (cap + 1 <= LMAX)%Z /\ (0 <= A)%Z /\ (A + (cap + 1) <= alloc_ceiling)%Z
      /\ (okm = None -> A = 0 /\ len = 0 /\ bs0 = [])
      /\ (forall km, okm = Some km -> In (km, A, cap + 1)%Z LB /\ rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs0] /\ Z.of_nat (length bs0) = cap + 1
                                   /\ 4096 <= A /\ (A + (cap + 1) <= 0x2a000 \/ 0x5d000 <= A) /\ nth_error bs0 (Z.to_nat len) = Some (Z_to_bv 8 0))%Z.
    Proof.
      intros s LB m bs0 HR (MBC & OWN & HL & HC & NULM). unfold LMAX in *.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      destruct okm as [km|]; cbn in OWN.
      - destruct OWN as [HIN BLK]. destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R4.
        pose proof (BLK4096 _ _ _ _ HR HIN) as R5. cbn in R5. pose proof (BLKIMG _ _ _ _ HR HIN) as R6. cbn in R6.
        pose proof (proj2 (proj1 BLK)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
        assert (W0 : length bs0 = Z.to_nat (cap + 1)) by (pose proof BLK as BLK'; destruct BLK' as [[W0 _] _]; cbn in W0; LiaTuning.ctauto).
        split; [exact BY|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold LMAX; lia|]. split; [lia|]. split; [lia|].
        split; [intros; discriminate|]. intros km' E. injection E as <-. split; [exact HIN|]. split; [exact BLK|]. split; [lia|]. split; [lia|]. split; [lia| exact NULM].
      - destruct OWN as (-> & -> & ->). cbn in NULM. subst len. cbn.
        split. { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold LMAX; lia|]. split; [lia|]. split; [lia|].
        split; [intros _; repeat split; reflexivity| intros; discriminate].
    Qed.

    #[using="Type"] Lemma nodup_reurl : forall (C UB UB' LBK0 : list BLK),
      NoDup (map blk_id ((C ++ UB) ++ LBK0)) -> NoDup (map blk_id UB') ->
      (forall b b0, In b UB' -> In b0 (C ++ LBK0) -> blk_id b <> blk_id b0) ->
      NoDup (map blk_id ((C ++ UB') ++ LBK0)).
    Proof.
      intros C UB UB' LBK0 ND NDU FR.
      assert (PM : forall U : list BLK, Permutation (map blk_id ((C ++ U) ++ LBK0)) (map blk_id U ++ map blk_id (C ++ LBK0))).
      { intros U. rewrite <- map_app. apply Permutation_map. rewrite <- app_assoc. apply Permutation_app_swap_app. }
      rewrite (PM UB) in ND. apply list.NoDup_app in ND. destruct ND as (_ & _ & NDC).
      rewrite (PM UB'). apply list.NoDup_app. split; [exact NDU|]. split; [| exact NDC].
      intros x Hx Hy. apply base.list_elem_of_In in Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & Hb).
      apply base.list_elem_of_In in Hy. apply in_map_iff in Hy. destruct Hy as (b0 & E & Hb0). exact (FR b b0 Hb Hb0 (eq_sym E)).
    Qed.

    #[using="Type"] Lemma nodup_url_facts : forall (C UB LBK0 : list BLK),
      NoDup (map blk_id ((C ++ UB) ++ LBK0)) ->
      NoDup (map blk_id UB) /\ (forall b b0, In b UB -> In b0 (C ++ LBK0) -> blk_id b <> blk_id b0).
    Proof.
      intros C UB LBK0 ND.
      assert (PM : Permutation (map blk_id ((C ++ UB) ++ LBK0)) (map blk_id UB ++ map blk_id (C ++ LBK0))).
      { rewrite <- map_app. apply Permutation_map. rewrite <- app_assoc. apply Permutation_app_swap_app. }
      rewrite PM in ND. apply list.NoDup_app in ND. destruct ND as (NDU & DJ & NDC). split; [exact NDU|].
      intros b b0 Hb Hb0 E. apply (DJ (blk_id b)); apply base.list_elem_of_In; [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb0].
    Qed.

    #[using="LOK ERRNOV ERRNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO LO0 CEIL QP PB HT MT"] Lemma RQ_segU : forall s LB m m' W (LBw : list BLK) bs0 cur meth uc maj min err pos ub UB
        bs' cur' meth' uc' maj' min' err' pos' ub' UB',
      RQ s LB m bs0 cur meth uc maj min err pos ub UB ->
      munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> Forall (wcls LBw) W -> (forall b, In b LBw -> In b (okb AI okm A cap)) ->
      (Forall (fun iv => q <= fst iv \/ snd iv <= lo)%Z W \/ stk rsegs m' lo q) ->
      (exists e, rw_cells rsegs m' (al_errno L_) [C4 e]) ->
      p_scan m' P cur' -> (0 <= cur' <= len)%Z -> p_methw m' P meth' -> p_uri m' P uc' -> p_ver m' P isreq maj' min' ->
      p_ctl m' P err' hack pos' entp clen csz esp -> H_prep.p_url m' P ub' -> ubo AI ub' UB' ->
      (forall b, In b UB' -> In b LB) -> NoDup (map blk_id UB') ->
      (forall b b0, In b UB' -> In b0 ((hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap) ++ LBK) -> blk_id b <> blk_id b0) ->
      ((LBw = [] /\ bs' = bs0) \/ p_msg AI m' LB P A len cap okm bs') ->
      RQ s LB m' bs' cur' meth' uc' maj' min' err' pos' ub' UB'
      /\ (forall X0 n, (q <= X0)%Z -> (X0 + Z.of_nat n <= P + 4 \/ (P + 224 <= X0 /\ X0 + Z.of_nat n <= P + 276) \/ (P + 284 <= X0 /\ X0 + Z.of_nat n <= P + 432)
                                     \/ (P + 452 <= X0 /\ X0 + Z.of_nat n <= P + 488) \/ P + 496 <= X0)%Z ->
                      (X0 + Z.of_nat n <= P + 504)%Z -> (X0 + Z.of_nat n <= q \/ (q + 16 <= X0 /\ X0 + Z.of_nat n <= q + 56) \/ q + 104 <= X0)%Z ->
                      disjoint_from W X0 (Z.of_nat n)).
    Proof.
      intros until UB'. intros INV MU WM MI' FW SUBW STH ERR' SC' CUR' METH' URI' VER' CTL' URL' UBO' SUBU NDU FRU MSG'. open_RQ INV. open_PP PP.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      assert (SUBW2 : forall b, In b LBw -> In b (ps_blocks AI (stof bs0 cur meth uc maj min err pos ub UB))).
      { intros b Hb. unfold ps_blocks. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB]. apply in_or_app. right. apply in_or_app. left. exact (SUBW b Hb). }
      destruct (rq_seg s LB m m' W LBw _ HR HE HPX BSUB ND SUBW2 MU WM FW FSH F32 PRS_ PENT STAT) as (HR2 & HE2 & HP2 & FSH2 & F322 & PRS2 & PENT2 & STAT2 & HPgen & UP).
      assert (ST2 : stk rsegs m' lo q).
      { destruct STH as [FWQ|ST']; [| exact ST']. eapply (stk_transport_disjoint rsegs); [exact ST| exact MU| exact WM|].
        apply disjoint_from_Forall. eapply Forall_impl; [| exact FWQ]. cbn. intros [l h] Hl; cbn in *. lia. }

      pose proof ND as ND0. unfold ps_blocks in ND0, BSUB. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB] in ND0, BSUB.
      assert (N1 : NoDup (map blk_id (hl_blocks AI ns hs ++ (okb AI okm A cap ++ okb AI sok SA scap ++ UB ++ LBK)))).
      { rewrite <- ?app_assoc in ND0. rewrite <- ?app_assoc. exact ND0. }
      assert (N2 : NoDup (map blk_id ((hl_blocks AI ns hs ++ okb AI okm A cap) ++ (okb AI sok SA scap ++ UB ++ LBK)))).
      { rewrite <- ?app_assoc in ND0. rewrite <- ?app_assoc. exact ND0. }
      assert (HPh : heap_pres AI (hl_blocks AI ns hs) HI64 m m').
      { apply HPgen; [intros b Hb; unfold ps_blocks; cbn; apply in_or_app; left; exact Hb|].
        intros b b' Hb Hb'. exact (nodup_in_neq AI _ _ _ _ N1 Hb (in_or_app _ _ _ (or_introl (SUBW _ Hb')))). }
      assert (HPs : heap_pres AI (okb AI sok SA scap) HI64 m m').
      { apply HPgen; [intros b Hb; unfold ps_blocks; cbn; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
        intros b b' Hb Hb'. apply not_eq_sym. exact (nodup_in_neq AI _ _ _ _ N2 (in_or_app _ _ _ (or_intror (SUBW _ Hb'))) (in_or_app _ _ _ (or_introl Hb))). }
      assert (MSG2 : p_msg AI m' LB P A len cap okm bs').
      { destruct MSG' as [[-> ->]|MSG']; [| exact MSG'].
        assert (HPm : heap_pres AI (okb AI okm A cap) HI64 m m').
        { apply HPgen; [intros b Hb; unfold ps_blocks; cbn; apply in_or_app; right; apply in_or_app; left; exact Hb| intros b b' _ []]. }
        destruct PMSG as (MBC & OWN & HL & HC & NULM). split; [| split; [| split; [exact HL| split; [exact HC| exact NULM]]]].
        - eapply rw_cells_transport; [exact MBC| exact MU| exact WM|]. unfold mbuf_cells. cbn [cells_size csize Nat.add]. apply UP; lia.
        - eapply mown_heap_pres; [exact OWN| exact HPm| lia| intros b Hb; exact Hb]. }
      split; [| exact UP].
      split; [exact HR2|]. split; [exact HE2|]. split; [exact MI'|]. split; [exact ST2|]. split; [exact ERR'|]. split; [exact FSH2|]. split; [exact F322|].
      split.
      { split; [exact SC'|]. split; [exact MSG2|]. split; [exact CUR'|]. split; [exact METH'|]. split; [exact URI'|]. split; [exact PRS2|].
        split. { destruct PSM as (SMC & SOWN & SL & SC32). split; [| split; [| split; [exact SL| exact SC32]]].
                 - eapply rw_cells_transport; [exact SMC| exact MU| exact WM|]. unfold mbuf_cells. cbn [cells_size csize Nat.add]. apply UP; lia.
                 - eapply mown_heap_pres; [exact SOWN| exact HPs| cbn; lia| intros b Hb; exact Hb]. }
        split; [exact VER'|].
        split. { destruct PHL as (LC & FLC & FF & DL & HS & IT & HB & NB & X0').
                 split. { eapply rw_cells_transport; [exact LC| exact MU| exact WM|]. unfold lhead_cells. cbn [cells_size csize Nat.add]. apply UP; cbn; lia. }
                 split. { eapply rw_cells_transport; [exact FLC| exact MU| exact WM|]. unfold fl_cells. cbn [cells_size csize Nat.add]. apply UP; cbn; lia. }
                 split. { eapply rw_cells_transport; [exact FF| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; cbn; lia. }
                 split. { eapply (dlseg_heap_pres AI); [exact DL| exact HPh|]. intros b it Hn. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hn). }
                 split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPh|]. intros b Hb. unfold hl_blocks. apply in_or_app. right. exact Hb. }
                 auto. }
        split; [exact XV|]. split; [exact PENT2|]. split; [exact CTL'|]. split; [exact URL'| exact UBO']. }
      split. { intros b Hb. unfold ps_blocks in Hb. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB] in Hb.
               apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply BSUB; apply in_or_app; right; exact Hb].
               apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply BSUB; apply in_or_app; left; apply in_or_app; left; exact Hb|].
               apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply BSUB; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hb|].
               apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply BSUB; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
               apply SUBU. exact Hb. }
      split. { unfold ps_blocks in ND |- *. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB] in ND |- *.
               assert (E : forall U : list BLK, (hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap ++ U) = ((hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap) ++ U))
                 by (intros U; rewrite <- ?app_assoc; reflexivity).
               rewrite E in ND |- *. eapply nodup_reurl; [exact ND| exact NDU| exact FRU]. }
      split; [exact STAT2| exact HP2].
    Qed.

    #[using="LOK ERRNOV ERRNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO LO0 CEIL QP PB HT MT"] Lemma RQ_seg : forall s LB m m' W (LBw : list BLK) bs0 cur meth uc maj min err pos ub UB
        bs' cur' meth' uc' maj' min' err' pos',
      RQ s LB m bs0 cur meth uc maj min err pos ub UB ->
      munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> Forall (wcls LBw) W -> (forall b, In b LBw -> In b (okb AI okm A cap)) ->
      (Forall (fun iv => q <= fst iv \/ snd iv <= lo)%Z W \/ stk rsegs m' lo q) ->
      (exists e, rw_cells rsegs m' (al_errno L_) [C4 e]) ->
      p_scan m' P cur' -> (0 <= cur' <= len)%Z -> p_methw m' P meth' -> p_uri m' P uc' -> p_ver m' P isreq maj' min' ->
      p_ctl m' P err' hack pos' entp clen csz esp -> H_prep.p_url m' P ub ->
      ((LBw = [] /\ bs' = bs0) \/ p_msg AI m' LB P A len cap okm bs') ->
      RQ s LB m' bs' cur' meth' uc' maj' min' err' pos' ub UB
      /\ (forall X0 n, (q <= X0)%Z -> (X0 + Z.of_nat n <= P + 4 \/ (P + 224 <= X0 /\ X0 + Z.of_nat n <= P + 276) \/ (P + 284 <= X0 /\ X0 + Z.of_nat n <= P + 432)
                                     \/ (P + 452 <= X0 /\ X0 + Z.of_nat n <= P + 488) \/ P + 496 <= X0)%Z ->
                      (X0 + Z.of_nat n <= P + 504)%Z -> (X0 + Z.of_nat n <= q \/ (q + 16 <= X0 /\ X0 + Z.of_nat n <= q + 56) \/ q + 104 <= X0)%Z ->
                      disjoint_from W X0 (Z.of_nat n)).
    Proof.
      intros until pos'. intros INV MU WM MI' FW SUBW STH ERR' SC' CUR' METH' URI' VER' CTL' URL' MSG'.
      pose proof INV as INV'. open_RQ INV'. open_PP PP.
      unfold ps_blocks in ND. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB] in ND.
      assert (E : forall U : list BLK, (hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap ++ U) = ((hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap) ++ U))
        by (intros U; rewrite <- ?app_assoc; reflexivity).
      rewrite E in ND. destruct (nodup_url_facts _ _ _ ND) as [NDU FRU].
      eapply RQ_segU; try eassumption.
      intros b Hb. apply BSUB. unfold ps_blocks. cbn. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
    Qed.

    Definition FRM (m : mem) (j0 : word) (c8 : list cell) (ubw ulw tyw jt j64 tb tl : word) : Prop :=
      rw_cells rsegs m q [C8 j0] /\ rw_cells rsegs m (q + 8) c8 /\ cells_size c8 = 8%nat
      /\ rw_cells rsegs m (q + 56) [C8 ubw; C8 ulw] /\ rw_cells rsegs m (q + 72) [C4 tyw; C4 jt] /\ rw_cells rsegs m (q + 80) [C8 j64]
      /\ rw_cells rsegs m (q + 88) [C8 tb; C8 tl].

    Ltac open_FRM H := destruct H as (Q0 & Q8 & SZ8 & Q40 & Q56 & Q64 & Q72).

    #[using="Type"] Lemma FRM_rqFX : forall m j0 c8 ubw ulw tyw jt j64 tb tl, FRM m j0 c8 ubw ulw tyw jt j64 tb tl ->
      rqFX m c8 [C8 ubw; C8 ulw; C4 tyw; C4 jt; C8 j64; C8 tb; C8 tl].
    Proof.
      intros until tl. intros FR. open_FRM FR. split; [eexists; exact Q0|]. split; [exact Q8|]. split; [exact SZ8|]. split; [| reflexivity].
      apply (proj2 (rw_cells_app rsegs m (q + 56) [C8 ubw; C8 ulw] [C4 tyw; C4 jt; C8 j64; C8 tb; C8 tl])). split; [exact Q40|].
      lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (q + 72)%Z by (cbn; lia) end.
      apply (proj2 (rw_cells_app rsegs m _ [C4 tyw; C4 jt] [C8 j64; C8 tb; C8 tl])). split; [exact Q56|].
      lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (q + 80)%Z by (cbn; lia) end.
      apply (proj2 (rw_cells_app rsegs m _ [C8 j64] [C8 tb; C8 tl])). split; [exact Q64|].
      lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (q + 88)%Z by (cbn; lia) end. exact Q72.
    Qed.

    Ltac tr H MU WM := eapply (rw_cells_transport rsegs _ _ _ _ _ H MU WM); unfold p_ctl_cells, mbuf_cells, lhead_cells, fl_cells; cbn [disjoint_from cells_size csize Nat.add fst snd]; lia.

    #[using="LOK TPV ERRNOV ERRNC BLK4096 BLKIMG GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma rq_loop : forall (k : nat) gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB
        j0 c8 ubw ulw tyw jt j64 tb tl x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 c8 ubw ulw tyw jt j64 tb tl -> (len - cur < Z.of_nat k)%Z -> ps_isreq st0 = isreq ->
      (forall m' (c0 : Z) tyw' tb' tl' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6',
          RQ s LB m' bs0 c0 meth uc maj min err pos ub UB -> FRM m' j0 c8 ubw ulw tyw' jt j64 tb' tl' -> (cur <= c0)%Z ->
          SREACH AI (POST gp F fc st0) (PRS match_entry (wz 0x15cfc) t0' t1' t2' (wz S) (wz FMT09) (wz (q + 88)) (wz (q + 56)) a4' a5' a6' a7' s7v s9v t3' t4' t5' t6' gp F fc m') s LB) ->
      SREACH AI (POST gp F fc st0) (PRS 0x15cb8 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      induction k as [|k IH]; intros until t6; intros INV FR HK ISR HK0; [pose proof INV as INV'; open_RQ INV'; open_PP PP; exfalso; lia|].
      pose proof INV as INV'. open_RQ INV'. open_PP PP. open_FRM FR.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'.
      pose proof P8 as P8'. unfold zmod8 in P8'. pose proof Q16 as Q16'. unfold zmod16 in Q16'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & OKN & OKS). unfold LMAX in CMX.
      destruct PMSG as (MBC & OWN & _). unfold p_scan in PSC.
      destruct (proj1 (rw_cells_app rsegs m (q + 72) [C4 tyw] [C4 jt]) Q56) as [Q56a Q60]. cbn [cells_size csize Nat.add] in Q60.
      eapply sreach_evt. { rewrite TPV. apply (rq_blank P q). }
      intros ms1 ->. rewrite <- TPV.
      eapply sreach_evt.
      { eapply (sgt_call q lo S (q + 88) (q + 72) MB A cur len cap bs0 tb tl tyw); unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *; try eassumption; try reflexivity; try lia. }
      intros ms2 PO. unfold sgt_qpost in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & cur' & tb' & tl' & tyw' & -> & MU2 & WM2 & MI2 & ST2 & SC2 & T2 & TY2 & CUR2 & ALT).
      replace (ret_pc (wz 0x15cc8)) with (wz 0x15cc8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR].
      assert (FW2 : Forall (wcls []) [(q - 96, q); (S + 8, S + 16); (q + 88, q + 88 + 16); (q + 72, q + 72 + 4)]%Z).
      { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia. }
      destruct (RQ_seg s LB m m2 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur' meth uc maj min err pos INV MU2 WM2 MI2 FW2 ltac:(intros b [])
                  (or_intror ST2) ltac:(eexists; tr ERR MU2 WM2) SC2 CUR2
                  ltac:(split; [tr MC MU2 WM2| exact MR]) ltac:(split; [tr UC MU2 WM2| exact US]) ltac:(split; [eexists; tr VC MU2 WM2| exact VR])
                  ltac:(split; [tr CTL MU2 WM2| exact CTLB]) ltac:(split; [tr ULC MU2 WM2| exact ULR]) ltac:(left; split; reflexivity))
        as [INV2 UP2].
      assert (FR2 : FRM m2 j0 c8 ubw ulw tyw' jt j64 tb' tl').
      { split; [tr Q0 MU2 WM2|]. split; [eapply rw_cells_transport; [exact Q8| exact MU2| exact WM2| rewrite SZ8; cbn; lia]|]. split; [exact SZ8|].
        split; [tr Q40 MU2 WM2|].
        split. { apply (proj2 (rw_cells_app rsegs m2 (q + 72) [C4 tyw'] [C4 jt])). split; [exact TY2|]. cbn [cells_size csize Nat.add].
                 eapply rw_cells_transport; [exact Q60| exact MU2| exact WM2| cbn; lia]. }
        split; [tr Q64 MU2 WM2| exact T2]. }
      pose proof CUR as CUR0.
      clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC MBC OWN CUR MC MR UC US PRS_ PSM VC VR PHL XV PENT CTL CTLB ULC ULR UBO Q0 Q8 SZ8 Q40 Q56 Q64 Q72 BUF MU2 WM2 INV errv pad Q56a Q60.
      pose proof INV2 as INV2'. open_RQ INV2'. open_PP PP. pose proof FR2 as FR2'. open_FRM FR2'. unfold p_scan in PSC.

      assert (RTL : (0 <= r <= 5)%Z /\ (r = 4 -> exists tlz ty, tl' = wz tlz /\ tyw' = wz ty /\ 0 <= ty <= 5 /\ 1 <= tlz /\ cur' = cur + tlz)%Z).
      { destruct ALT as [(tlz & ty & -> & _ & -> & -> & L1 & EC & _ & TYR & _)|([-> | ->] & _ & _)]; unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE.
        - split; [lia|]. intros _. exists tlz, ty. repeat split; try reflexivity; lia.
        - split; [lia| intros; exfalso; lia].
        - split; [lia| intros; exfalso; lia]. }
      destruct RTL as [RR RTL].
      destruct (Z.eq_dec r 4) as [R4|NR].
      - destruct (RTL R4) as (tlz & ty & Etl & Ety & TYR & L1 & EC). subst r. rewrite Etl in Q72, FR2.
        eapply sreach_evt.
        { rewrite TPV. eapply (rq_tok P q QP PHI63 4 ty tlz cur' tb' tyw'); try eassumption; try LiaTuning.alia. all: try (intros _; split; [exact Ety| exact TYR]).
 }
        intros ms3 (m3 & a0' & [(NR & _)|[(_ & T12 & -> & ->)|(_ & TN1 & TN2 & -> & MU3 & WM3 & MI3 & Q563 & Q723 & SC3)]]); [exfalso; lia| |]; rewrite <- TPV.
        +
          eapply (IH gp F fc st0 s LB m2 bs0 cur' meth uc maj min err pos ub UB j0 c8 ubw ulw tyw' jt j64 tb' (wz tlz)); [exact INV2| exact FR2| lia| exact ISR|].
          intros. eapply HK0; [eassumption| eassumption| lia].
        +
          destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR].
          assert (FW3 : Forall (wcls []) [(P + 488, P + 496)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
          destruct (RQ_seg s LB m2 m3 _ [] bs0 cur' meth uc maj min err pos ub UB bs0 (cur' - tlz)%Z meth uc maj min err pos INV2 MU3 WM3 MI3 FW3 ltac:(intros b [])
                      ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU3 WM3) SC3 ltac:(lia)
                      ltac:(split; [tr MC MU3 WM3| exact MR]) ltac:(split; [tr UC MU3 WM3| exact US]) ltac:(split; [eexists; tr VC MU3 WM3| exact VR])
                      ltac:(split; [tr CTL MU3 WM3| exact CTLB]) ltac:(split; [tr ULC MU3 WM3| exact ULR]) ltac:(left; split; reflexivity))
            as [INV3 UP3].
          eapply (HK0 m3 (cur' - tlz)%Z tyw' tb' (wz tlz)); [exact INV3| | lia].
          split; [tr Q0 MU3 WM3|]. split; [eapply rw_cells_transport; [exact Q8| exact MU3| exact WM3| rewrite SZ8; cbn; lia]|]. split; [exact SZ8|].
          split; [tr Q40 MU3 WM3|]. split; [exact Q563|]. split; [tr Q64 MU3 WM3| exact Q723].
      -
        rewrite <- (Z_to_bv_bv_unsigned tl') in Q72.
        eapply sreach_evt.
        { rewrite TPV. eapply (rq_tok P q QP PHI63 r 0 (bv_unsigned tl') cur' tb' tyw'); try eassumption; try LiaTuning.alia; intros E; exfalso; exact (NR E). }
        intros ms3 (m3 & a0' & [(_ & -> & ->)|[(E4 & _)|(E4 & _)]]); [| exfalso; exact (NR E4)| exfalso; exact (NR E4)]. rewrite <- TPV.
        eapply rq_exit; [exact INV2| | exact ISR| lia| intros E; exfalso; exact (NR E)].
        eapply FRM_rqFX. exact FR2.
    Qed.

    #[using="Type"] Lemma heap_pres_u64arrR : forall (LB : list BLK) SP m m' A0 xs,
      heap_pres AI LB SP m m' -> u64arr rsegs m A0 xs -> client_range AI LB SP A0 (8 * Z.of_nat (length xs)) -> u64arr rsegs m' A0 xs.
    Proof.
      intros LB SP m m' A0 xs HP [BA WA] CR. split.
      - eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact BA|]. rewrite u64s_length. replace (Z.of_nat (8 * length xs)) with (8 * Z.of_nat (length xs))%Z by lia. exact CR.
      - eapply (heap_pres_wr_at rsegs AI); [exact HP| exact WA| exact CR].
    Qed.

    #[using="GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QP HT MT"] Lemma RQ_hp : forall s s' LB LB' m m' bs0 cur meth uc maj min err pos ub UB,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB ->
      mem_inv rsegs m' -> stk rsegs m' lo q -> RENV rsegs AI m' B -> (exists e, rw_cells rsegs m' (al_errno L_) [C4 e]) ->
      heap_pres AI LB q m m' -> RHEAP rsegs AI s' LB' m' -> (forall b, In b LB -> In b LB') ->
      RQ s' LB' m' bs0 cur meth uc maj min err pos ub UB
      /\ (forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z -> rw_cells rsegs m' X0 cs).
    Proof.
      intros until UB. intros INV MI' ST' HE' ERR' HP HR' SUB. pose proof INV as INV'. open_RQ INV'. open_PP PP.
      assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z -> rw_cells rsegs m' X0 cs).
      { intros X0 cs H H1. eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact H| apply client_range_above; lia]. }
      assert (TRS : forall X0 cs, rw_cells rsegs m X0 cs -> (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat (cells_size cs) <= shi)%Z -> rw_cells rsegs m' X0 cs).
      { intros X0 cs H (slo & shi & Hst & S1 & S2). eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact H| eapply client_range_static; [exact Hst| lia| lia]]. }
      assert (TRB : forall X0 xs, bytes_at rsegs m X0 xs -> (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat (length xs) <= shi)%Z -> bytes_at rsegs m' X0 xs).
      { intros X0 xs H (slo & shi & Hst & S1 & S2). eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact H| eapply client_range_static; [exact Hst| lia| lia]]. }
      assert (HPsub : forall LBh : list BLK, (forall b, In b LBh -> In b LB) -> heap_pres AI LBh HI64 m m').
      { intros LBh S1 a Ha Hc. apply HP; [exact Ha|]. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [unfold HI64 in Hc; lia| right; left; exact Hc| right; right; exists b; split; [apply S1; exact Hb| exact Hr]]. }
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBO SUBK].
      split; [| exact TR].
      split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
      split; [apply (TR _ _ FSH); lia|]. split; [apply (TR _ _ F32); lia|].
      split.
      { split; [unfold p_scan in *; apply (TR _ _ PSC); lia|].
        split. { destruct PMSG as (MBC & OWN & HL & HC & NULM). split; [apply (TR _ _ MBC); lia|]. split; [| split; [exact HL| split; [exact HC| exact NULM]]].
                 eapply mown_heap_pres; [exact OWN| | cbn; lia| exact SUB]. apply HPsub. intros b Hb. apply SUBO. unfold ps_blocks. cbn. apply in_or_app. right. apply in_or_app. left. exact Hb. }
        split; [exact CUR|]. split; [destruct PMETH as [MC MR]; split; [apply (TR _ _ MC); lia| exact MR]|].
        split; [destruct PURI as [UC US]; split; [apply (TR _ _ UC); lia| exact US]|].
        split; [destruct PRS_ as [RC RR]; split; [apply (TR _ _ RC); lia| exact RR]|].
        split. { destruct PSM as (SMC & SOWN & SL & SC32). split; [apply (TR _ _ SMC); lia|]. split; [| split; [exact SL| exact SC32]].
                 eapply mown_heap_pres; [exact SOWN| | cbn; lia| exact SUB]. apply HPsub. intros b Hb. apply SUBO. unfold ps_blocks. cbn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
        split; [destruct PVER as ([pad VC] & VR); split; [eexists; apply (TR _ _ VC); lia| exact VR]|].
        split. { destruct PHL as (LC & FLC & FF & DL & HS & IT & HB & NB & X0'). split; [apply (TR _ _ LC); lia|]. split; [apply (TR _ _ FLC); lia|]. split; [apply (TR _ _ FF); lia|].
                 split. { eapply (dlseg_heap_pres AI); [exact DL| apply HPsub; intros b Hb; apply SUBO; unfold ps_blocks; cbn; apply in_or_app; left; exact Hb|].
                          intros b it Hn. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hn). }
                 split. { eapply (hdrs_mem_heap_pres AI); [exact HS| apply HPsub; intros b Hb; apply SUBO; unfold ps_blocks; cbn; apply in_or_app; left; exact Hb|].
                          intros b Hb. unfold hl_blocks. apply in_or_app. right. exact Hb. }
                 auto. }
        split; [exact XV|]. split; [unfold p_ent in *; apply (TR _ _ PENT); lia|].
        split; [destruct PCTL as [CTL CTLB]; split; [apply (TR _ _ CTL); lia| exact CTLB]|].
        split; [destruct PURL as [ULC ULR]; split; [apply (TR _ _ ULC); lia| exact ULR]| exact UBO]. }
      split; [intros b Hb; apply SUB; exact (BSUB b Hb)|]. split; [exact ND|].
      split. { destruct STAT as (TAB & [zb ZB] & MTB & GG & GI & GM & IW & GGM).
               destruct TABST as (l1 & h1 & ST1 & ? & ?). destruct ZST as (l2 & h2 & ST2 & ? & ?). destruct MTST as (l3 & h3 & ST3 & ? & ?).
               destruct GIFST as (l4 & h4 & ST4 & ? & ?). destruct GMST as (l5 & h5 & ST5 & ? & ?). destruct IWST as (l6 & h6 & ST6 & ? & ?).
               destruct GOTGIFST as (l7 & h7 & ST7 & ? & ?). destruct GOTGMAXST as (l8 & h8 & ST8 & ? & ?). pose proof (proj1 HT) as WSL66. pose proof MWSL as WSL22.
               split. { eapply heap_pres_u64arrR; [exact HP| exact TAB|]. rewrite WSL66. eapply client_range_static; [exact ST1| lia| cbn; lia]. }
               split. { exists zb. apply (TRB _ _ ZB). exists l2, h2. split; [exact ST2| cbn; lia]. }
               split. { eapply heap_pres_u64arrR; [exact HP| exact MTB|]. rewrite WSL22. eapply client_range_static; [exact ST3| lia| cbn; lia]. }
               split. { apply (TRB _ _ GG). rewrite length_le8. exists l7, h7. split; [exact ST7| cbn; lia]. }
               split. { apply (TRB _ _ GI). rewrite length_le4. exists l4, h4. split; [exact ST4| cbn; lia]. }
               split. { apply (TRS _ _ GM). exists l5, h5. split; [exact ST5| cbn; lia]. }
               split. { apply (TRS _ _ IW). exists l6, h6. split; [exact ST6| cbn; lia]. }
               apply (TRB _ _ GGM). rewrite length_le8. exists l8, h8. split; [exact ST8| cbn; lia]. }
      eapply (hpx_trans rsegs AI); [exact HPX|]. eapply (hpx_weaken rsegs AI); [eapply (hpx_of_heap_pres rsegs AI); exact HP| intros a Ha; exact Ha| lia| exact SUBK].
    Qed.

    Definition url_pcs (Hd PC1 PC2 RAPU : Z) : Prop :=
      (Hd = 0x15d50 /\ PC1 = 0x15d94 /\ PC2 = 0x15f68 /\ RAPU = 0x15f7c) \/ (Hd = 0x15dd8 /\ PC1 = 0x15e1c /\ PC2 = 0x15e3c /\ RAPU = 0x15e50).

    #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 HT MT GMX"] Lemma rq_url : forall (Hd PC1 PC2 RAPU : Z), url_pcs Hd PC1 PC2 RAPU ->
      forall gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB (o l : Z) (km : K)
             j0 c8 tyw jt j64 tb tl x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 c8 (wz (A + o)) (wz l) tyw jt j64 tb tl -> ps_isreq st0 = isreq ->
      okm = Some km -> (0 <= o)%Z -> (1 <= l)%Z -> (o + l < len)%Z -> (meth <= 12)%Z ->
      (forall s' LB' m' (r o' l' U : Z) (kU : K) (junk' : list byte) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
          RQ s' LB' m' bs0 cur meth [CB 216 junk'] maj min err pos U [(kU, U, l' + 1)%Z] -> FRM m' j0 c8 (wz (A + o')) (wz l') tyw jt j64 tb tl ->
          (o <= o' /\ o' + l' = o + l /\ 1 <= l' /\ 0 <= r < 2^64 /\ 4096 <= U)%Z -> (forall b, In b LB -> In b LB') ->
          SREACH AI (POST gp F fc st0) (PRS RAPU (wz RAPU) t0' t1' t2' (wz r) a1' a2' a3' a4' a5' a6' a7' s7v s9v t3' t4' t5' t6' gp F fc m') s' LB') ->
      SREACH AI (POST gp F fc st0) (PRS Hd x1 t0 t1 t2 (wz (A + o)) a1 (wz l) a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros Hd PC1 PC2 RAPU PCS. intros until t6. intros INV FR ISR OKM O0 L1 OL M12 HK.
      pose proof INV as INV'. open_RQ INV'. open_PP PP. pose proof FR as FR'. open_FRM FR'. pose proof BSUB as BSUB0.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'. pose proof QLO2 as QLO2'. unfold PP_ADEPTH in QLO2'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & _ & OKS). unfold LMAX in CMX.
      destruct (OKS km OKM) as (HINM & BLK & LBS2 & A4 & AW & NULM).

      eapply sreach_evt.
      { rewrite TPV. destruct PCS as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
        - eapply (rq_slash1 P q lo QLO1 QP PHI63 A o l (Z.to_nat (cap + 1)) bs0); try eassumption; try LiaTuning.alia.
        - eapply (rq_slash2 P q lo QLO1 QP PHI63 A o l (Z.to_nat (cap + 1)) bs0); try eassumption; try LiaTuning.alia. }
      intros ms1 PO1. cbv beta in PO1.
      assert (PO1' : exists m1 (o' l' ra' : Z) (a1' a3' a4' : word),
        ms1 = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4' a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m1
        /\ (ra' = PC1 \/ ra' = PC2) /\ munch [(q + 56, q + 72)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
        /\ rw_cells rsegs m1 A [CB (Z.to_nat (cap + 1)) bs0] /\ rw_cells rsegs m1 (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z).
      { destruct PCS as [(-> & -> & -> & ->)|(-> & -> & -> & ->)]; rewrite <- TPV in PO1;
          destruct PO1 as (m1 & o' & l' & ra' & a1' & a3' & a4' & E & HRA & REST); exists m1, o', l', ra', a1', a3', a4'; (split; [exact E| split; [exact HRA| LiaTuning.ctauto]]). }
      clear PO1. destruct PO1' as (m1 & o' & l' & ra' & a1' & a3' & a4' & -> & HRA & MU1 & WM1 & MI1 & BLK1 & Q401 & OL').
      assert (RPC : ret_pc (wz ra') = wz ra') by (destruct PCS as [(_ & -> & -> & _)|(_ & -> & -> & _)]; destruct HRA as [-> | ->]; (apply ret_pc_even; [lia| reflexivity])).
      assert (RA64 : (0 <= ra' < 2^32)%Z) by (destruct PCS as [(_ & -> & -> & _)|(_ & -> & -> & _)]; destruct HRA as [-> | ->]; lia).

      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      assert (FW1 : Forall (wcls []) [(q + 56, q + 72)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
      destruct (RQ_seg s LB m m1 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur meth uc maj min err pos INV MU1 WM1 MI1 FW1 ltac:(intros b [])
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU1 WM1) ltac:(tr PSC MU1 WM1) CUR
                  ltac:(split; [tr MC MU1 WM1| exact MR]) ltac:(split; [tr UC MU1 WM1| exact US]) ltac:(split; [eexists; tr VC MU1 WM1| exact VR])
                  ltac:(split; [tr CTL MU1 WM1| exact CTLB]) ltac:(split; [tr ULC MU1 WM1| exact ULR]) ltac:(left; split; reflexivity))
        as [INV1 _].
      assert (FR1 : FRM m1 j0 c8 (wz (A + o')) (wz l') tyw jt j64 tb tl).
      { split; [tr Q0 MU1 WM1|]. split; [eapply rw_cells_transport; [exact Q8| exact MU1| exact WM1| rewrite SZ8; cbn; lia]|]. split; [exact SZ8|].
        split; [exact Q401|]. split; [tr Q56 MU1 WM1|]. split; [tr Q64 MU1 WM1| tr Q72 MU1 WM1]. }

      set (src := firstn (Z.to_nat l') (skipn (Z.to_nat o') bs0)).
      assert (LSRC : Z.of_nat (length src) = l'). { subst src. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
      assert (BSRC : bytes_at rsegs m1 (A + o') src).
      { pose proof (proj2 (proj1 BLK1)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
        rewrite <- (firstn_skipn (Z.to_nat o') bs0) in BY. apply bytes_at_app in BY. destruct BY as [_ BY].
        rewrite firstn_length_le in BY by lia. replace (A + Z.of_nat (Z.to_nat o'))%Z with (A + o')%Z in BY by lia.
        rewrite <- (firstn_skipn (Z.to_nat l') (skipn (Z.to_nat o') bs0)) in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
      clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC PMSG CUR MC MR UC US PRS_ PSM VC VR PHL XV PENT CTL CTLB ULC ULR UBO Q0 Q8 SZ8 Q40 Q56 Q64 Q72 BUF MU1 WM1 INV FR errv pad BLK.
      pose proof INV1 as INV1'. open_RQ INV1'.
      assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      eapply sreach_bind.
      { eapply (str_alloc_spec AI AC LOK MALPC) with (SRC := (A + o')%Z) (n := l') (src := src) (bsrc := (km, A, cap + 1)%Z) (lo := lo) (B := B);
          rewrite ?EQq; try eassumption; try reflexivity; cbn; try lia. }
      clear ERR errv. intros s2 LB2 ms2 PO2. unfold str_alloc_post in PO2.
      destruct PO2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & U & -> & (MI2 & ST2 & HE2 & [e2 ERR2] & HP2) & RES).
      rewrite ?EQq in ST2, HP2. rewrite RPC.
      assert (RES' : exists LBn : list BLK, LB2 = LBn ++ LB /\ RHEAP rsegs AI s2 LB2 m2
               /\ ((U = 0 /\ LBn = []) \/ (exists kU, LBn = [(kU, U, l' + 1)%Z] /\ 4096 <= U /\ rw_cells rsegs m2 U [CB (Z.to_nat (l' + 1)) (src ++ [Z_to_bv 8 0])]))%Z).
      { destruct RES as [(-> & -> & HR2)|(kU & -> & BR & HR2 & UBLK)].
        - exists []. split; [reflexivity|]. split; [exact HR2|]. left. split; reflexivity.
        - exists [(kU, U, l' + 1)%Z]. split; [reflexivity|]. split; [exact HR2|]. right. exists kU. split; [reflexivity|].
          pose proof (BLK4096 _ _ _ _ HR2 (or_introl eq_refl)) as U4. cbn in U4. split; [lia| exact UBLK]. }
      clear RES. destruct RES' as (LBn & -> & HR2 & RES).
      destruct (RQ_hp s s2 LB (LBn ++ LB) m1 m2 bs0 cur meth uc maj min err pos ub UB INV1 MI2 ST2 HE2 (ex_intro _ e2 ERR2) HP2 HR2 ltac:(intros b Hb; apply in_or_app; right; exact Hb))
        as [INV2 TR2].
      assert (FR2 : FRM m2 j0 c8 (wz (A + o')) (wz l') tyw jt j64 tb tl).
      { pose proof FR1 as FR1'. open_FRM FR1'. split; [apply (TR2 _ _ Q0); lia|]. split; [apply (TR2 _ _ Q8); lia|]. split; [exact SZ8|].
        split; [apply (TR2 _ _ Q40); lia|]. split; [apply (TR2 _ _ Q56); lia|]. split; [apply (TR2 _ _ Q64); lia| apply (TR2 _ _ Q72); lia]. }
      assert (UR : (0 <= U < 2^64)%Z).
      { destruct RES as [(-> & _)|(kU & -> & U4 & UBLK)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR2 (or_introl eq_refl)) as (R1 & _ & _ & R4 & _). cbn in R1, R4. lia. }
      clear INV1 TR2 FR1 HR HE MI ST FSH F32 PP BSUB ND STAT HPX MI1 BSRC BLK1 Q401 HP2.
      pose proof INV2 as INV2'. open_RQ INV2'. open_PP PP. pose proof FR2 as FR2'. open_FRM FR2'.
      destruct PCTL as [CTL CTLB]. destruct PURL as [ULC ULR].
      unfold p_ctl_cells in CTL.
      lazymatch type of CTL with rw_cells _ _ _ (?c0 :: ?rest) => destruct (proj1 (rw_cells_app rsegs m2 (P + 440) [c0] rest) CTL) as [EC CTL7]; cbn [cells_size csize Nat.add] in CTL7 end.

      eapply sreach_evt.
      { rewrite TPV. destruct PCS as [(_ & -> & -> & ->)|(_ & -> & -> & ->)].
        - eapply (rq_sa09 P q QP PHI63 ra' U l'); try eassumption; try LiaTuning.alia.
        - eapply (rq_sa P q QP PHI63 ra' U l'); try eassumption; try LiaTuning.alia. }
      intros ms3 PO3. cbv beta in PO3.
      assert (PO3' : exists m3 (errw' : word) a0' a1' a2' x1' pc',
        ms3 = PRS pc' x1' u0 u1 u2 a0' a1' a2' v3 v4 v5 v6 v7 s7v s9v u3 u4 u5 u6 gp F fc m3
        /\ munch [(P + 432, P + 444)]%Z m2 m3 /\ wmono rsegs m2 m3 /\ mem_inv rsegs m3
        /\ rw_cells rsegs m3 (P + 432) [C8 (wz U)] /\ rw_cells rsegs m3 (P + 440) [C4 errw'] /\ rw_cells rsegs m3 (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ ( (U = 0 /\ pc' = HEAD /\ x1' = wz ra' /\ a0' = wz 3 /\ errw' = wz 500)
           \/ (U <> 0 /\ pc' = parse_uri_entry /\ x1' = wz RAPU /\ a0' = wz U /\ a1' = wz l' /\ a2' = S7 /\ errw' = wz err) )%Z).
      { destruct PCS as [(_ & -> & -> & ->)|(_ & -> & -> & ->)]; rewrite <- TPV in PO3;
          destruct PO3 as (m3 & errw' & a0' & a1'' & a2' & x1' & pc' & E & REST); exists m3, errw', a0', a1'', a2', x1', pc'; (split; [exact E| exact REST]). }
      clear PO3. destruct PO3' as (m3 & errw' & a0' & a1'' & a2' & x1' & pc' & -> & MU3 & WM3 & MI3 & UBC3 & EC3 & Q403 & ALT).

      assert (CTL3 : forall e : Z, errw' = wz e -> rw_cells rsegs m3 (P + 440) (p_ctl_cells e hack pos entp clen csz esp)).
      { intros e ->. unfold p_ctl_cells. apply (proj2 (rw_cells_app rsegs m3 (P + 440) [C4 (wz e)] _)). split; [exact EC3|]. cbn [cells_size csize Nat.add]. tr CTL7 MU3 WM3. }
      destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). unfold p_scan in PSC.
      assert (FW3 : Forall (wcls []) [(P + 432, P + 444)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
      pose proof ND as ND0. unfold ps_blocks in ND0. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB] in ND0.
      assert (EA : forall Ux : list BLK, (hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap ++ Ux) = ((hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap) ++ Ux))
        by (intros Ux; rewrite <- ?app_assoc; reflexivity).
      destruct ALT as [(-> & -> & -> & -> & ->)|(UNZ & -> & -> & -> & -> & -> & ->)].
      -
        destruct (RQ_segU s2 (LBn ++ LB) m2 m3 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur meth uc maj min 500 pos 0 []
                    INV2 MU3 WM3 MI3 FW3 ltac:(intros b []) ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU3 WM3)
                    ltac:(tr PSC MU3 WM3) CUR ltac:(split; [tr MC MU3 WM3| exact MR]) ltac:(split; [tr UC MU3 WM3| exact US]) ltac:(split; [eexists; tr VC MU3 WM3| exact VR])
                    ltac:(split; [exact (CTL3 500 eq_refl)| lia]) ltac:(split; [exact UBC3| lia]) ltac:(cbn; reflexivity)
                    ltac:(intros b []) ltac:(cbn; constructor) ltac:(intros b b0 []) ltac:(left; split; reflexivity)) as [INV3 UP3].
        eapply rq_exit; [exact INV3| | exact ISR| lia| intros; exfalso; lia].
        eapply FRM_rqFX. split; [tr Q0 MU3 WM3|]. split; [tr Q8 MU3 WM3|]. split; [exact SZ8|]. split; [exact Q403|]. split; [tr Q56 MU3 WM3|]. split; [tr Q64 MU3 WM3| tr Q72 MU3 WM3].
      -
        destruct RES as [(U0 & _)|(kU & -> & U4 & UBLK)]; [exfalso; exact (UNZ U0)|].
        pose proof (ai_blocks_nodup rsegs AI _ _ _ HR2) as NDL. rewrite map_app in NDL. cbn [map app] in NDL.
        replace (blk_id (kU, U, l' + 1)%Z) with kU in NDL by reflexivity. apply list.NoDup_cons in NDL. destruct NDL as [KNI _].
        assert (KFR : forall b0, In b0 LB -> kU <> blk_id b0).
        { intros b0 Hb0 E. apply KNI. rewrite E. apply base.list_elem_of_In. apply in_map. exact Hb0. }
        assert (BSUBC : forall b0, In b0 ((hl_blocks AI ns hs ++ okb AI okm A cap ++ okb AI sok SA scap) ++ LBK) -> In b0 LB).
        { intros b0 Hb0. apply BSUB0. unfold ps_blocks. cbn [stof ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB]. rewrite EA.
          apply in_app_or in Hb0. apply in_or_app. destruct Hb0 as [H|H]; [left; apply in_or_app; left; exact H| right; exact H]. }
        destruct (RQ_segU s2 ([(kU, U, l' + 1)%Z] ++ LB) m2 m3 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur meth uc maj min err pos U [(kU, U, l' + 1)%Z]
                    INV2 MU3 WM3 MI3 FW3 ltac:(intros b []) ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU3 WM3)
                    ltac:(tr PSC MU3 WM3) CUR ltac:(split; [tr MC MU3 WM3| exact MR]) ltac:(split; [tr UC MU3 WM3| exact US]) ltac:(split; [eexists; tr VC MU3 WM3| exact VR])
                    ltac:(split; [exact (CTL3 err eq_refl)| lia]) ltac:(split; [exact UBC3| lia]) ltac:(cbn; split; [reflexivity| lia])
                    ltac:(intros b [<-|[]]; left; reflexivity) ltac:(cbn; constructor; [intros HH; inversion HH| constructor])
                    ltac:(intros b b0 [<-|[]] Hb0; cbn; apply KFR; exact (BSUBC b0 Hb0))
                    ltac:(left; split; reflexivity)) as [INV3 UP3].
        assert (FR3 : FRM m3 j0 c8 (wz (A + o')) (wz l') tyw jt j64 tb tl).
        { split; [tr Q0 MU3 WM3|]. split; [tr Q8 MU3 WM3|]. split; [exact SZ8|]. split; [exact Q403|]. split; [tr Q56 MU3 WM3|]. split; [tr Q64 MU3 WM3| tr Q72 MU3 WM3]. }
        destruct (ai_block_range rsegs AI _ _ _ _ HR2 (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & RF). cbn in R1, R2, R3, R4, RF.
        pose proof (BLKIMG _ _ _ _ HR2 (or_introl eq_refl)) as UW. cbn in UW.
        pose proof (rw_cells_transport rsegs _ m2 m3 _ _ UBLK MU3 WM3 ltac:(cbn; lia)) as UBLK3.
        clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC PMSG CUR MC MR UC US PRS_ PSM VC VR PHL XV PENT ULC ULR UBO Q0 Q8 SZ8 Q40 Q56 Q64 Q72 MU3 WM3 INV2 FR2 errv pad EC CTL CTL7 CTL3 EC3 UBC3 Q403 UBLK ND0 HR2 CTLB.
        pose proof INV3 as INV3'. open_RQ INV3'. open_PP PP.
        destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3. rewrite ERRNOV in WE1, WE2.
        pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as RW. cbn in RW.

        assert (RU : (U + (l' + 1) <= round_up8 (U + (l' + 1)) <= U + (l' + 1) + 7)%Z /\ (round_up8 (U + (l' + 1)) - (U + (l' + 1)) = (- (U + l' + 1)) mod 8)%Z
                     /\ (U + (l' + 1) <= 0x2a000 -> round_up8 (U + (l' + 1)) <= 0x2a000)%Z).
        { unfold round_up8. Z.div_mod_to_equations. lia. }
        destruct RU as (RU1 & RU2 & RU4).
        pose proof (proj2 (proj1 UBLK3)) as BYU. cbn [cells_bytes cbytes] in BYU. rewrite app_nil_r in BYU.
        assert (LSU : length (src ++ [Z_to_bv 8 0]) = Z.to_nat (l' + 1)) by (rewrite length_app; cbn; lia).
        destruct (bytes_at_extend (Z.to_nat (round_up8 (U + (l' + 1)) - (U + (l' + 1)))) m3 U (src ++ [Z_to_bv 8 0]) BYU) as (sl & BYS & LSL).
        { intros x Hx. rewrite LSU in Hx. eapply (ai_block_slack rsegs AI); [exact HR| left; reflexivity| cbn; lia]. }
        { rewrite LSU. lia. }
        rewrite <- app_assoc in BYS. cbn [app] in BYS.
        destruct (CAN _ _ _ HR) as [SSP1 [canary SSP2]].
        destruct PURI as [UC US]. destruct (rw_cells_forget rsegs _ _ _ UC) as [junk UCB]. rewrite US in UCB.
        pose proof STAT as STAT'. destruct STAT' as (_ & _ & _ & GG & GI & _).
        destruct (stk_split rsegs _ _ (q - 928)%Z _ ST ltac:(lia)) as [STlo SThi].
        assert (EQt : bv_unsigned (wz (al_tp L_)) = al_tp L_) by (rewrite TPV; apply unsigned_lit; lia).
        pose proof P8 as P8'. unfold zmod8 in P8'.
        pose proof parse_uri_spec as PU. unfold parse_uri_stmt, PURI_DEPTH in PU.
        eapply sreach_evt.
        { eapply (PU U (P + 8) l' src sl junk errv canary gifv); rewrite ?EQq, ?EQt, ?LSL; unfold got_ssp, ssp_guard; try eassumption; try reflexivity; try lia.
          rewrite TPV. rewrite ERRNOV in ERR. exact ERR. }
        intros ms4 PO4. unfold parse_uri_post, PURI_DEPTH in PO4. rewrite ?EQq, ?EQt in PO4.
        destruct PO4 as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m4 & r & junk' & errv' & -> & MU4 & WM4 & MI4 & ST4 & UC4 & BYU4 & ERR4 & SSP14 & SSP24 & GG4 & GI4).
        replace (ret_pc (wz RAPU)) with (wz RAPU : word) by (symmetry; destruct PCS as [(_ & _ & _ & ->)|(_ & _ & _ & ->)]; (apply ret_pc_even; [lia| reflexivity])).
        rewrite TPV in MU4, ERR4. replace (243744 - 164)%Z with (al_errno L_) in MU4, ERR4 by (rewrite ERRNOV; reflexivity).
        destruct PMETH as [MC MR]. destruct PVER as ([pad VC] & VR). destruct PCTL as [CTL CTLB]. destruct PURL as [ULC ULR]. unfold p_scan in PSC.
        assert (FW4 : Forall (wcls []) [(q - 928, q); (P + 8, P + 8 + 216); (al_errno L_, al_errno L_ + 4)]%Z).
        { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn -[al_errno]; rewrite ?ERRNOV; lia. }
        assert (ST4' : stk rsegs m4 lo q).
        { eapply (stk_merge rsegs _ lo (q - 928)%Z q); [| exact ST4| lia]. eapply (stk_transport_disjoint rsegs); [exact STlo| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]. }
        destruct (RQ_seg s2 _ m3 m4 _ [] bs0 cur meth uc maj min err pos U [(kU, U, l' + 1)%Z] bs0 cur meth [CB 216 junk'] maj min err pos INV3 MU4 WM4 MI4 FW4 ltac:(intros b [])
                    (or_intror ST4') ltac:(eexists; exact ERR4) ltac:(eapply rw_cells_transport; [exact PSC| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]) CUR
                    ltac:(split; [eapply rw_cells_transport; [exact MC| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]| exact MR]) ltac:(split; [exact UC4| reflexivity])
                    ltac:(split; [eexists; eapply rw_cells_transport; [exact VC| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]| exact VR])
                    ltac:(split; [eapply rw_cells_transport; [exact CTL| exact MU4| exact WM4| rewrite ERRNOV; unfold p_ctl_cells; cbn; lia]| exact CTLB])
                    ltac:(split; [eapply rw_cells_transport; [exact ULC| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]| exact ULR]) ltac:(left; split; reflexivity))
          as [INV4 UP4].
        pose proof FR3 as FR3'. open_FRM FR3'. rewrite <- (Z_to_bv_bv_unsigned (wz r)).
        eapply (HK s2 _ m4 (bv_unsigned (wz r)) o' l' U kU junk'); [exact INV4| | | intros b Hb; apply in_or_app; right; exact Hb].
        + split; [eapply rw_cells_transport; [exact Q0| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]|].
          split; [eapply rw_cells_transport; [exact Q8| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]|]. split; [exact SZ8|].
          split; [eapply rw_cells_transport; [exact Q40| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]|].
          split; [eapply rw_cells_transport; [exact Q56| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]|].
          split; [eapply rw_cells_transport; [exact Q64| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia]|].
          eapply rw_cells_transport; [exact Q72| exact MU4| exact WM4| rewrite ERRNOV; cbn; lia].
        + pose proof (bv_unsigned_in_range 64 (wz r)) as RR. unfold bv_modulus in RR. lia.
    Qed.

    #[using="LOK ERRNOV ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO LO0 CEIL QP PB BHI Q16 HT MT GMX"] Lemma rq_msicall : forall gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB (o1 l1 rpc : Z) (km : K)
        j0 c8 ubw ulw tyw jt j64 s7v s9v t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 c8 ubw ulw tyw jt j64 (wz (A + o1)) (wz l1) -> ps_isreq st0 = isreq ->
      okm = Some km -> (0 <= o1 /\ 1 <= l1 /\ o1 + l1 < len)%Z -> ret_pc (wz rpc) = wz rpc ->
      (forall m' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
          RQ s LB m' bs0 cur meth uc maj min err pos ub UB -> FRM m' j0 c8 ubw ulw tyw jt j64 (wz (A + o1)) (wz l1) -> (r = -1 \/ 0 <= r < 11)%Z ->
          SREACH AI (POST gp F fc st0) (MS (mkR (wz rpc) (wz q) gp (wz (al_tp L_)) t0' t1' t2' (wz P) (wz S) (wz r) a1' a2' a3' a4' a5' a6' a7' (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3' t4' t5' t6')
                                         F (wz rpc) fc None m' (seg_rom rsegs)) s LB) ->
      SREACH AI (POST gp F fc st0) (MS (mkR (wz rpc) (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz P) (wz S) (wz (A + o1)) (wz l1) (wz MTAB) (wz 11) (wz 1) a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
                                     F (wz map_str_to_int_entry) fc None m (seg_rom rsegs)) s LB.
    Proof.
      intros until t6. intros INV FR ISR OKM OL RPC HK.
      pose proof INV as INV'. open_RQ INV'. open_PP PP. pose proof FR as FR'. open_FRM FR'.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & _ & OKS). unfold LMAX in CMX.
      destruct (OKS km OKM) as (HINM & BLK & LBS2 & A4 & AW & NULM).
      set (tok := firstn (Z.to_nat l1) (skipn (Z.to_nat o1) bs0)).
      assert (LT : Z.of_nat (length tok) = l1). { subst tok. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
      assert (BT : bytes_at rsegs m (A + o1) tok).
      { pose proof (proj2 (proj1 BLK)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
        rewrite <- (firstn_skipn (Z.to_nat o1) bs0) in BY. apply bytes_at_app in BY. destruct BY as [_ BY].
        rewrite firstn_length_le in BY by lia. replace (A + Z.of_nat (Z.to_nat o1))%Z with (A + o1)%Z in BY by lia.
        rewrite <- (firstn_skipn (Z.to_nat l1) (skipn (Z.to_nat o1) bs0)) in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
      pose proof STAT as STAT'. destruct STAT' as (_ & _ & MTB & _).
      destruct (stk_split rsegs _ _ (q - 144)%Z _ ST ltac:(lia)) as [STlo SThi].
      assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      pose proof Q16 as Q16'. unfold zmod16 in Q16'.
      pose proof (map_str_to_int_spec SNC) as MS_. unfold map_str_to_int_stmt in MS_.
      eapply sreach_evt.
      { eapply (MS_ (A + o1)%Z l1 MTAB 11 1 tok mws); rewrite ?EQq; try eassumption; try reflexivity; try lia.
        all: try (rewrite MWSL; reflexivity).
        all: try (eapply table_strings_mono; [exact (proj2 (proj2 MT))| lia]).
 }
      clear MS_. intros ms1 PO. unfold map_str_to_int_post in PO. rewrite ?EQq in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & r & -> & MU1 & WM1 & MI1 & ST1 & RR).
      rewrite RPC.
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      assert (FW1 : Forall (wcls []) [(q - 144, q)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
      assert (ST1' : stk rsegs m1 lo q).
      { eapply (stk_merge rsegs _ lo (q - 144)%Z q); [| exact ST1| lia]. eapply (stk_transport_disjoint rsegs); [exact STlo| exact MU1| exact WM1| cbn; lia]. }
      destruct (RQ_seg s LB m m1 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur meth uc maj min err pos INV MU1 WM1 MI1 FW1 ltac:(intros b [])
                  (or_intror ST1') ltac:(eexists; tr ERR MU1 WM1) ltac:(tr PSC MU1 WM1) CUR
                  ltac:(split; [tr MC MU1 WM1| exact MR]) ltac:(split; [tr UC MU1 WM1| exact US]) ltac:(split; [eexists; tr VC MU1 WM1| exact VR])
                  ltac:(split; [tr CTL MU1 WM1| exact CTLB]) ltac:(split; [tr ULC MU1 WM1| exact ULR]) ltac:(left; split; reflexivity))
        as [INV1 _].
      eapply HK; [exact INV1| | exact RR].
      split; [tr Q0 MU1 WM1|]. split; [tr Q8 MU1 WM1|]. split; [exact SZ8|]. split; [tr Q40 MU1 WM1|]. split; [tr Q56 MU1 WM1|]. split; [tr Q64 MU1 WM1| tr Q72 MU1 WM1].
    Qed.

    #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma rq_09 : forall gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB (o1 l1 o2 l2 : Z) (km : K)
        j0 c8 tyw jt j64 t0 t1 t2 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 c8 (wz (A + o2)) (wz l2) tyw jt j64 (wz (A + o1)) (wz l1) -> ps_isreq st0 = isreq ->
      okm = Some km -> (0 <= o1 /\ 1 <= l1 /\ o1 + l1 < o2 /\ 1 <= l2 /\ o2 + l2 < len)%Z ->
      SREACH AI (POST gp F fc st0) (PRS map_str_to_int_entry (wz 0x15d18) t0 t1 t2 (wz (A + o1)) (wz l1) (wz MTAB) (wz 11) (wz 1) a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros until t6. intros INV FR ISR OKM OL.
      eapply (rq_msicall gp F fc st0 s LB m bs0 cur meth uc maj min err pos ub UB o1 l1 0x15d18 km); [exact INV| exact FR| exact ISR| exact OKM| lia| apply ret_pc_even; [lia| reflexivity]|].
      clear INV FR. intros m1 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV FR RR.
      pose proof INV as INV'. open_RQ INV'. open_PP PP. pose proof FR as FR'. open_FRM FR'.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & _ & OKS). unfold LMAX in CMX.
      pose proof STAT as STAT'. destruct STAT' as (_ & _ & MTB & _).
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      unfold p_ctl_cells in CTL.
      lazymatch type of CTL with rw_cells _ _ _ (?c0 :: ?rest) => destruct (proj1 (rw_cells_app rsegs m1 (P + 440) [c0] rest) CTL) as [EC CTL7]; cbn [cells_size csize Nat.add] in CTL7 end.
      eapply sreach_evt.
      { rewrite TPV. eapply (rq_msi09 P q lo QLO1 LO0 QP PHI63 mws MWSL MID r meth err (A + o2)%Z l2); try eassumption; try LiaTuning.alia. }
      intros ms2 (m2 & meth' & err' & a0' & a1'' & a2'' & pc & -> & MU2 & WM2 & MI2 & MTB2 & MC2 & EC2 & Q402 & ALT). rewrite <- TPV.
      assert (CTL2 : rw_cells rsegs m2 (P + 440) (p_ctl_cells err' hack pos entp clen csz esp)).
      { unfold p_ctl_cells. apply (proj2 (rw_cells_app rsegs m2 (P + 440) [C4 (wz err')] _)). split; [exact EC2|]. cbn [cells_size csize Nat.add]. tr CTL7 MU2 WM2. }
      assert (MR2 : (0 <= meth' <= 12)%Z /\ (0 <= err' < 2^31)%Z) by (destruct ALT as [(_ & _ & -> & [-> | ->])|(_ & _ & _ & -> & -> & _)]; unfold p_methw in *; lia).
      assert (FW2 : Forall (wcls []) [(P + 4, P + 8); (P + 440, P + 444)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
      destruct (RQ_seg s LB m1 m2 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur meth' uc maj min err' pos INV MU2 WM2 MI2 FW2 ltac:(intros b [])
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU2 WM2) ltac:(tr PSC MU2 WM2) CUR
                  ltac:(split; [exact MC2| lia]) ltac:(split; [tr UC MU2 WM2| exact US]) ltac:(split; [eexists; tr VC MU2 WM2| exact VR])
                  ltac:(split; [exact CTL2| lia]) ltac:(split; [tr ULC MU2 WM2| exact ULR]) ltac:(left; split; reflexivity))
        as [INV2 _].
      assert (FR2 : FRM m2 j0 c8 (wz (A + o2)) (wz l2) tyw jt j64 (wz (A + o1)) (wz l1)).
      { split; [tr Q0 MU2 WM2|]. split; [tr Q8 MU2 WM2|]. split; [exact SZ8|]. split; [exact Q402|]. split; [tr Q56 MU2 WM2|]. split; [tr Q64 MU2 WM2| tr Q72 MU2 WM2]. }
      destruct ALT as [(-> & -> & -> & E5)|(-> & -> & -> & -> & -> & _)].
      {   eapply rq_exit; [exact INV2| eapply FRM_rqFX; exact FR2| exact ISR| lia| intros; exfalso; lia]. }

      clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC PMSG CUR MC MR UC US PRS_ PSM VC VR PHL XV PENT CTL CTLB EC CTL7 ULC ULR UBO Q0 Q8 SZ8 Q40 Q56 Q64 Q72 MU2 WM2 INV FR errv pad CTL2 EC2 MC2 Q402 MTB2 MTB.
      eapply (rq_url 0x15d50 0x15d94 0x15f68 0x15f7c ltac:(left; repeat split; reflexivity) gp F fc st0 s LB m2 bs0 cur 12 uc maj min err pos ub UB o2 l2 km);
        [exact INV2| exact FR2| exact ISR| exact OKM| lia| lia| lia| lia|].
      clear INV2 FR2. intros s3 LB3 m3 r3 o' l' U kU junk' u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 INV3 FR3 FACTS SUB3.
      pose proof INV3 as INV'. open_RQ INV'. open_PP PP. pose proof FR3 as FR'. open_FRM FR'.
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      eapply sreach_evt.
      { rewrite TPV. eapply (rq_pu09 P q PHI63 r3 err hack pos entp clen csz esp); unfold ctl8; try eassumption; try LiaTuning.alia. }
      intros ms4 (m4 & ra0 & pos' & -> & MU4 & WM4 & MI4 & CTL4 & ALT). rewrite <- TPV.
      assert (FW4 : Forall (wcls []) [(P + 448, P + 452)]%Z) by (repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia).
      assert (PR : (0 <= pos' <= 4)%Z /\ (ra0 = 3 \/ ra0 = 0)%Z) by (destruct ALT as [(_ & -> & -> & _)|(_ & -> & ->)]; lia).
      destruct (RQ_seg s3 LB3 m3 m4 _ [] bs0 cur 12 [CB 216 junk'] maj min err pos U [(kU, U, l' + 1)%Z] bs0 cur 12 [CB 216 junk'] maj min err pos' INV3 MU4 WM4 MI4 FW4 ltac:(intros b [])
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(eexists; tr ERR MU4 WM4) ltac:(tr PSC MU4 WM4) CUR
                  ltac:(split; [tr MC MU4 WM4| exact MR]) ltac:(split; [tr UC MU4 WM4| exact US]) ltac:(split; [eexists; tr VC MU4 WM4| exact VR])
                  ltac:(split; [unfold ctl8 in CTL4; exact CTL4| lia]) ltac:(split; [tr ULC MU4 WM4| exact ULR]) ltac:(left; split; reflexivity))
        as [INV4 _].
      eapply rq_exit; [exact INV4| | exact ISR| lia| intros; exfalso; lia].
      eapply FRM_rqFX. split; [tr Q0 MU4 WM4|]. split; [tr Q8 MU4 WM4|]. split; [exact SZ8|]. split; [tr Q40 MU4 WM4|]. split; [tr Q56 MU4 WM4|]. split; [tr Q64 MU4 WM4| tr Q72 MU4 WM4].
    Qed.

    Ltac splitc FR n H1 H2 :=
      lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
        let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
        let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
        change (rw_cells segs m A (cs1 ++ cs2)) in FR;
        destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
        try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
               let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
      end.

    #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma rq_full : forall gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB
        j0 j8 ubw ulw tyw jt j64 tb tl t0 t1 t2 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 [C8 j8] ubw ulw tyw jt j64 tb tl -> ps_isreq st0 = isreq ->
      (meth <= 11)%Z -> (X + 2 * (len - cur) <= VMAX)%Z -> entp = 1%Z ->
      SREACH AI (POST gp F fc st0) (PRS match_entry (wz 0x15dcc) t0 t1 t2 (wz S) (wz FMTREQ) (wz (q + 88)) (wz (q + 56)) (wz (q + 72)) a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros until t6. intros INV FR ISR M11 BUD ENTP.
      pose proof INV as INV'. open_RQ INV'. open_PP PP. pose proof FR as FR'. open_FRM FR'.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'.
      pose proof Q16 as Q16'. unfold zmod16 in Q16'. pose proof P8 as P8'. unfold zmod8 in P8'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & OKN & OKS). unfold LMAX in CMX.
      pose proof PMSG as PMSG'. destruct PMSG' as (MBC & OWN & _). unfold p_scan in PSC.
      assert (MOK : vf_ok (q + -64) lo S MB A len cap cur bs0) by (unfold vf_ok; lia).

      pose proof (rw_cells_C44_C8 _ _ _ _ Q56) as Q56w.
      assert (Q56x : rw_cells rsegs m (q + 72) [C8 (le_bytes_to_word (le4 tyw ++ le4 jt)); C8 j64]).
      { apply (proj2 (rw_cells_app rsegs m (q + 72) [C8 _] [C8 j64])). split; [exact Q56w|]. cbn [cells_size csize Nat.add].
        replace (q + 72 + Z.of_nat 8)%Z with (q + 80)%Z by lia. exact Q64. }
      eapply sreach_evt.
      { rewrite TPV. eapply (match_req q lo S MB A len cap cur bs0 MOK (q + 88) (q + 56) (q + 72));
          unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc; try eassumption; try LiaTuning.alia. }
      intros ms2 PO. unfold mpost in PO.
      destruct PO as (r & cur' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & -> & MU2 & WM2 & MI2 & ST2 & SC2 & MBC2 & BUF2 & RR & CUR' & ROK & RNOK & XR).
      rewrite <- TPV. unfold X_req in XR. destruct XR as (pa & pb & pc & pd & pe & pf & Q722 & Q402 & Q562 & HOK).
      replace (ret_pc (wz 0x15dcc)) with (wz 0x15dcc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold H_vfmatch_A.SCc in SC2.

      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR].
      assert (FW2 : Forall (wcls []) ((lo, q) :: (S + 8, S + 16) :: [(q + 88, q + 88 + 16); (q + 56, q + 56 + 16); (q + 72, q + 72 + 16)])%Z).
      { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia. }
      destruct (RQ_seg s LB m m2 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur' meth uc maj min err pos INV MU2 WM2 MI2 FW2 ltac:(intros b [])
                  (or_intror ST2) ltac:(eexists; tr ERR MU2 WM2) SC2 CUR'
                  ltac:(split; [tr MC MU2 WM2| exact MR]) ltac:(split; [tr UC MU2 WM2| exact US]) ltac:(split; [eexists; tr VC MU2 WM2| exact VR])
                  ltac:(split; [tr CTL MU2 WM2| exact CTLB]) ltac:(split; [tr ULC MU2 WM2| exact ULR]) ltac:(left; split; reflexivity))
        as [INV2 _].
      pose proof (rw_cells_transport rsegs _ m m2 _ _ Q0 MU2 WM2 ltac:(cbn; lia)) as Q02.
      pose proof (rw_cells_transport rsegs _ m m2 _ _ Q8 MU2 WM2 ltac:(cbn; lia)) as Q82.
      destruct (Z.eq_dec r 4) as [R4|NR].
      2:{
          eapply sreach_evt. { rewrite TPV. eapply (rq_mreq P q mws MWSL r pc pd); [exact MI2| exact Q402| exact RR]. }
          intros ms3 [[_ ->]|[E _]]; [| exfalso; exact (NR E)]. rewrite <- TPV.
          eapply (rq_exit _ _ _ _ _ _ _ _ _ _ _ _ _ [C8 j8] [C8 pc; C8 pd; C8 pe; C8 pf; C8 pa; C8 pb]); [exact INV2| | exact ISR| exact RR| intros E; exfalso; exact (NR E)].
          split; [eexists; exact Q02|]. split; [exact Q82|]. split; [reflexivity|]. split; [| reflexivity].
          apply (proj2 (rw_cells_app rsegs m2 (q + 56) [C8 pc; C8 pd] [C8 pe; C8 pf; C8 pa; C8 pb])). split; [exact Q402|]. cbn [cells_size csize Nat.add].
          replace (q + 56 + Z.of_nat 16)%Z with (q + 72)%Z by lia.
          apply (proj2 (rw_cells_app rsegs m2 (q + 72) [C8 pe; C8 pf] [C8 pa; C8 pb])). split; [exact Q562|]. cbn [cells_size csize Nat.add].
          replace (q + 72 + Z.of_nat 16)%Z with (q + 88)%Z by lia. exact Q722. }

      destruct (HOK R4) as (o1 & l1 & o2 & l2 & o3 & l3 & -> & -> & -> & -> & -> & -> & O1 & L1 & OL1 & L2 & OL2 & L3 & OL3 & CL & bcr & Hbcr & CRLF). subst r.
      assert (EOK : exists km, okm = Some km).
      { destruct okm as [km|]; [exists km; reflexivity| exfalso]. destruct (OKN eq_refl) as (_ & LEN0 & _). lia. }
      destruct EOK as [km EOK].
      eapply sreach_evt. { rewrite TPV. eapply (rq_mreq P q mws MWSL 4 (wz (A + o2)) (wz l2)); [exact MI2| exact Q402| lia]. }
      intros ms3 [[E _]|[_ ->]]; [exfalso; lia|]. rewrite <- TPV.
      destruct (proj1 (rw_cells_app rsegs m2 (q + 72) [C8 (wz (A + o3))] [C8 (wz l3)]) Q562) as [Q56a Q642]. cbn [cells_size csize Nat.add] in Q642.
      replace (q + 72 + Z.of_nat 8)%Z with (q + 80)%Z in Q642 by lia.
      destruct (rw_cells_C8_C44s _ _ _ Q56a) as (va & vb & Q56s & EV).
      assert (FR2 : FRM m2 j0 [C8 j8] (wz (A + o2)) (wz l2) va vb (wz l3) (wz (A + o1)) (wz l1)).
      { split; [exact Q02|]. split; [exact Q82|]. split; [reflexivity|]. split; [exact Q402|]. split; [exact Q56s|]. split; [exact Q642| exact Q722]. }
      clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC MBC OWN MC MR UC US PRS_ PSM VC VR PHL XV PENT CTL CTLB ULC ULR UBO Q0 Q8 Q40 Q56 Q64 Q72 Q56w Q56x BUF MU2 WM2 INV FR errv pad SC2 MBC2 BUF2 Q02 Q82 Q402 Q56a Q56s Q642 Q722 HOK MI2 ST2 OKN OKS PMSG LBS ANZ AHI LC CMX A0 AHI2 MOK SZ8.
      rename CUR into CUR0.
      eapply (rq_url 0x15dd8 0x15e1c 0x15e3c 0x15e50 ltac:(right; repeat split; reflexivity) gp F fc st0 s LB m2 bs0 cur' meth uc maj min err pos ub UB o2 l2 km);
        [exact INV2| exact FR2| exact ISR| exact EOK| lia| lia| lia| lia|].
      clear INV2 FR2. intros s3 LB3 m3 r3 o' l' U kU junk' u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 INV3 FR3 FACTS SUB3.

      pose proof INV3 as INV'. open_RQ INV'. open_PP PP. pose proof FR3 as FR'. open_FRM FR'.
      eapply sreach_evt. { rewrite TPV. eapply (rq_pu P q r3 (wz (A + o1)) (wz l1)); [exact MI| exact Q72| lia]. }
      intros ms4 [(NR1 & ->)|(R1 & ->)]; rewrite <- TPV.
      {   eapply rq_exit; [exact INV3| eapply FRM_rqFX; exact FR3| exact ISR| lia| intros; exfalso; lia]. }
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      rename m3 into m4. pose proof INV3 as INV4.
      pose proof Q0 as Q04. pose proof Q40 as Q404. pose proof Q56 as Q564. pose proof Q64 as Q644. pose proof Q8 as Q84. pose proof Q72 as Q724.
      clear HR HE MI ST ERR FSH F32 BSUB ND STAT HPX PSC CUR MC MR UC US PRS_ PSM VC VR PHL XV PENT CTL CTLB ULC ULR UBO Q0 Q8 Q40 Q56 Q64 Q72 INV3 FR3 errv pad PMSG.

      pose proof INV4 as INV'. open_RQ INV'. open_PP PP.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & _ & OKS). unfold LMAX in CMX.
      destruct (OKS km EOK) as (HINM & BLK & LBS2 & A4 & AW & NULM).
      destruct (ai_block_range rsegs AI _ _ _ _ HR HINM) as (Ra1 & Ra2 & Ra3 & Ra4 & _). cbn in Ra1, Ra2, Ra3, Ra4.
      assert (RU : (A + (cap + 1) <= round_up8 (A + (cap + 1)) <= A + (cap + 1) + 7)%Z /\ (round_up8 (A + (cap + 1)) mod 8 = 0)%Z
                   /\ (round_up8 (A + (cap + 1)) <= alloc_ceiling)%Z /\ (A + (cap + 1) <= 0x2a000 -> round_up8 (A + (cap + 1)) <= 0x2a000)%Z).
      { unfold round_up8. Z.div_mod_to_equations. lia. }
      destruct RU as (RU1 & RU2 & RU3 & RU4).
      assert (SLX : exists sl, bytes_at rsegs m4 (A + (cap + 1)) sl /\ Z.of_nat (length sl) = (round_up8 (A + (cap + 1)) - (A + (cap + 1)))%Z).
      { destruct (bytes_at_extend (Z.to_nat (round_up8 (A + (cap + 1)) - (A + (cap + 1)))) m4 (A + (cap + 1)) []) as (sl & B2 & Lsl2).
        - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
        - intros x Hx. cbn [length Z.of_nat] in Hx. eapply (ai_block_slack rsegs AI); [exact HR| exact HINM| cbn; lia].
        - cbn [length Z.of_nat]. lia.
        - exists sl. cbn [app] in B2. split; [exact B2| lia]. }
      destruct SLX as (sl & SLK & LSL).
      destruct (CAN _ _ _ HR) as [SSP1 [canary SSP2]].
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR]. unfold p_scan in PSC.
      pose proof STAT as STAT'. destruct STAT' as (_ & _ & MTB & _).
      splitc VC 2%nat VER0 VR1. splitc VR1 1%nat PMJ VR2. splitc VR2 1%nat PMN PPD.
      assert (Q56v : rw_cells rsegs m4 (q + 72) [C8 (wz (A + o3)); C8 (wz l3)]).
      { apply (proj2 (rw_cells_app rsegs m4 (q + 72) [C8 (wz (A + o3))] [C8 (wz l3)])). split.
        - rewrite <- EV. apply rw_cells_C44_C8. exact Q564.
        - cbn [cells_size csize Nat.add]. replace (q + 72 + Z.of_nat 8)%Z with (q + 80)%Z by lia. exact Q644. }
      assert (EQt : bv_unsigned (wz (al_tp L_)) = 0x3b820%Z) by (rewrite TPV; apply unsigned_lit; lia).
      rewrite ERRNOV in ERR.
      assert (Q8A : (q mod 8 = 0)%Z) by (clear - Q16'; Z.div_mod_to_equations; lia).
      eapply sreach_evt.
      { eapply (rqv_vtail SNC P q lo ltac:(lia) LO0 QP ltac:(lia) mws MWSL (proj1 (proj2 MT)) (proj2 (proj2 MT)) Q8A
                  A len cap o1 l1 o3 l3 err meth pos hack entp clen csz esp maj min bs0 sl bcr j8 s9v canary errv (wz (al_tp L_)));
          unfold ctl8, rqv_ctl8, p_ctl_cells in *; try eassumption; try LiaTuning.alia. split; [exact SSP1| exact SSP2]. }
      intros ms5 PO. destruct PO as (m5 & ra0 & err' & meth' & pos' & maj' & min' & ev' & j8' & PO). do 18 (let x := fresh "y" in destruct PO as [x PO]).
      destruct PO as (-> & _ & MU5 & WM5 & MI5 & ST5 & Q85 & FX5 & Q565 & Q725 & BLK5 & SLK5 & PMJ5 & PMN5 & MJR5 & MNR5 & CTL5 & MC5 & MTB5 & SSP5 & ERR5 & ALT).

      assert (FW5 : Forall (wcls [(km, A, cap + 1)%Z]) [(lo, q); (A + (o3 + l3), A + (o3 + l3) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8); (P + 276, P + 284); (q + 8, q + 16); (0x3b77c, 0x3b77c + 4)]%Z).
      { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn -[al_errno]; rewrite ?ERRNOV; try lia.
        right; right; right. exists (km, A, cap + 1)%Z. split; [left; reflexivity| cbn; lia]. }
      assert (VER5 : rw_cells rsegs m5 (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj'); C4 (wz min'); C4 pad]).
      { apply (proj2 (rw_cells_app rsegs m5 (P + 264) [C8 (wz 0); C4 (wz isreq)] [C4 (wz maj'); C4 (wz min'); C4 pad])). split; [tr VER0 MU5 WM5|].
        cbn [cells_size csize Nat.add]. replace (P + 264 + Z.of_nat 12)%Z with (P + 276)%Z by lia.
        apply (proj2 (rw_cells_app rsegs m5 (P + 276) [C4 (wz maj')] [C4 (wz min'); C4 pad])). split; [exact PMJ5|].
        cbn [cells_size csize Nat.add]. replace (P + 276 + Z.of_nat 4)%Z with (P + 280)%Z by lia.
        apply (proj2 (rw_cells_app rsegs m5 (P + 280) [C4 (wz min')] [C4 pad])). split; [exact PMN5|].
        cbn [cells_size csize Nat.add]. replace (P + 280 + Z.of_nat 4)%Z with (P + 284)%Z by lia. tr PPD MU5 WM5. }
      assert (RNG : (0 <= err' < 2^31 /\ 0 <= meth' <= 12 /\ 0 <= pos' <= 4)%Z) by (destruct ALT as [(_ & -> & -> & [-> | ->])|(_ & -> & M' & ->)]; lia).
      destruct (RQ_seg s3 LB3 m4 m5 _ [(km, A, cap + 1)%Z] bs0 cur' meth [CB 216 junk'] maj min err pos U [(kU, U, l' + 1)%Z] bs0 cur' meth' [CB 216 junk'] maj' min' err' pos' INV4 MU5 WM5 MI5 FW5
                  ltac:(intros b [<-|[]]; rewrite EOK; left; reflexivity)
                  (or_intror ST5) ltac:(eexists; rewrite ERRNOV; exact ERR5) ltac:(tr PSC MU5 WM5) CUR
                  ltac:(split; [exact MC5| lia]) ltac:(split; [tr UC MU5 WM5| exact US]) ltac:(split; [eexists; exact VER5| lia])
                  ltac:(split; [exact CTL5| lia]) ltac:(split; [tr ULC MU5 WM5| exact ULR])
                  ltac:(right; split; [tr (proj1 PMSG) MU5 WM5| split; [rewrite EOK; cbn; split; [exact HINM| exact BLK5]| exact (proj2 (proj2 PMSG))]]))
        as [INV5 _].
      eapply (rq_exit _ _ _ _ _ _ _ _ _ _ _ _ _ [C8 j8'] [C8 (wz (A + o')); C8 (wz l'); C8 (wz (A + o3)); C8 (wz l3); C8 (wz (A + o1)); C8 (wz l1)] ra0);
        [exact INV5| | exact ISR| destruct ALT as [(-> & _)|(-> & _)]; lia|].
      - split; [eexists; tr Q04 MU5 WM5|]. split; [exact Q85|]. split; [reflexivity|]. split; [| reflexivity].
        apply (proj2 (rw_cells_app rsegs m5 (q + 56) [C8 (wz (A + o')); C8 (wz l')] [C8 (wz (A + o3)); C8 (wz l3); C8 (wz (A + o1)); C8 (wz l1)])). split; [tr Q404 MU5 WM5|].
        cbn [cells_size csize Nat.add]. replace (q + 56 + Z.of_nat 16)%Z with (q + 72)%Z by lia.
        apply (proj2 (rw_cells_app rsegs m5 (q + 72) [C8 (wz (A + o3)); C8 (wz l3)] [C8 (wz (A + o1)); C8 (wz l1)])). split; [exact Q565|].
        cbn [cells_size csize Nat.add]. replace (q + 72 + Z.of_nat 16)%Z with (q + 88)%Z by lia. exact Q725.
      - intros E4. destruct ALT as [(-> & _)|(_ & _ & M' & ->)]; [exfalso; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia| exact ENTP].
    Qed.

    #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma rq_line : forall gp (F : bvmap 5 word) fc (st0 : pstate AI) s LB m bs0 cur meth uc maj min err pos ub UB
        j0 j8 ubw ulw tyw jt j64 tb tl t0 t1 t2 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      RQ s LB m bs0 cur meth uc maj min err pos ub UB -> FRM m j0 [C8 j8] ubw ulw tyw jt j64 tb tl -> ps_isreq st0 = isreq ->
      (meth <= 11)%Z -> (X + 2 * (len - cur) <= VMAX)%Z -> entp = 1%Z ->
      SREACH AI (POST gp F fc st0) (PRS match_entry (wz 0x15cfc) t0 t1 t2 (wz S) (wz FMT09) (wz (q + 88)) (wz (q + 56)) a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros until t6. intros INV FR ISR M11 BUD ENTP.
      pose proof INV as INV'. open_RQ INV'. open_PP PP. pose proof FR as FR'. open_FRM FR'.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. pose proof QLO as QLO'. unfold PP_DEPTH in QLO'.
      pose proof Q16 as Q16'. unfold zmod16 in Q16'. pose proof P8 as P8'. unfold zmod8 in P8'.
      destruct (msg_factsR _ _ _ _ HR PMSG) as (BUF & LBS & ANZ & AHI & LC & CMX & A0 & AHI2 & OKN & OKS). unfold LMAX in CMX.
      pose proof PMSG as PMSG'. destruct PMSG' as (MBC & OWN & _). unfold p_scan in PSC.
      assert (MOK : vf_ok (q + -64) lo S MB A len cap cur bs0) by (unfold vf_ok; lia).
      eapply sreach_evt.
      { rewrite TPV. eapply (match_req09 q lo S MB A len cap cur bs0 MOK (q + 88) (q + 56));
          unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc; try eassumption; try LiaTuning.alia. }
      intros ms2 PO. unfold mpost in PO.
      destruct PO as (r & cur' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & -> & MU2 & WM2 & MI2 & ST2 & SC2 & MBC2 & BUF2 & RR & CUR' & ROK & RNOK & XR).
      rewrite <- TPV. unfold X_req09 in XR. destruct XR as (pa & pb & pc & pd & Q722 & Q402 & HOK).
      replace (ret_pc (wz 0x15cfc)) with (wz 0x15cfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold H_vfmatch_A.SCc in SC2.
      destruct PCTL as [CTL CTLB]. destruct PMETH as [MC MR]. destruct PURI as [UC US]. destruct PVER as ([pad VC] & VR). destruct PURL as [ULC ULR].
      assert (FW2 : Forall (wcls []) ((lo, q) :: (S + 8, S + 16) :: [(q + 88, q + 88 + 16); (q + 56, q + 56 + 16)])%Z).
      { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia. }
      destruct (RQ_seg s LB m m2 _ [] bs0 cur meth uc maj min err pos ub UB bs0 cur' meth uc maj min err pos INV MU2 WM2 MI2 FW2 ltac:(intros b [])
                  (or_intror ST2) ltac:(eexists; tr ERR MU2 WM2) SC2 CUR'
                  ltac:(split; [tr MC MU2 WM2| exact MR]) ltac:(split; [tr UC MU2 WM2| exact US]) ltac:(split; [eexists; tr VC MU2 WM2| exact VR])
                  ltac:(split; [tr CTL MU2 WM2| exact CTLB]) ltac:(split; [tr ULC MU2 WM2| exact ULR]) ltac:(left; split; reflexivity))
        as [INV2 _].
      assert (FR2 : FRM m2 j0 [C8 j8] pc pd tyw jt j64 pa pb).
      { split; [tr Q0 MU2 WM2|]. split; [tr Q8 MU2 WM2|]. split; [reflexivity|]. split; [exact Q402|]. split; [tr Q56 MU2 WM2|]. split; [tr Q64 MU2 WM2| exact Q722]. }
      pose proof INV2 as INV2'. destruct INV2' as (_ & _ & _ & _ & _ & _ & F322 & _).
      eapply sreach_evt. { rewrite TPV. eapply (rq_m09 P q r pa pb); [exact MI2| exact Q722| exact F322| exact RR]. }
      intros ms3 [[R4 ->]|[NR ->]]; rewrite <- TPV.
      -
        destruct (HOK R4) as (o1 & l1 & o2 & l2 & -> & -> & -> & -> & O1 & L1 & OL1 & L2 & OL2 & OC & CL).
        assert (EOK : exists km, okm = Some km).
        { destruct okm as [km|]; [exists km; reflexivity| exfalso]. destruct (OKN eq_refl) as (_ & LEN0 & _). lia. }
        destruct EOK as [km EOK].
        eapply (rq_09 gp F fc st0 s LB m2 bs0 cur' meth uc maj min err pos ub UB o1 l1 o2 l2 km); [exact INV2| exact FR2| exact ISR| exact EOK| lia].
      -
        eapply rq_full; [exact INV2| exact FR2| exact ISR| exact M11| rewrite (RNOK NR); exact BUD| exact ENTP].
    Qed.

    #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma reql_arm_pre : forall s LB m bs cur meth uc maj min err pos ub UB x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc,
      pp_core AI P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s LB m (stof bs cur meth uc maj min err pos ub UB) ->
      pp_side AI gmax (stof bs cur meth uc maj min err pos ub UB) -> pos = POS_REQUEST_LINE ->
      SREACH AI (POST gp F fc (stof bs cur meth uc maj min err pos ub UB))
             (pp_st AI P q PP_REQL x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
    Proof.
      intros until fc. intros CORE SIDE POS.
      destruct (rq_entry s LB m _ CORE eq_refl) as [INV (j0 & j8 & j40 & j48 & ja & jb & j64 & j72 & j80 & Q0 & Q8 & Q40 & Q56 & Q64 & Q72)].
      cbn [stof ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min
           ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in INV.
      destruct SIDE as (BUD & _ & ENTP & _ & M11).
      cbn [stof ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min
           ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in BUD, ENTP, M11.
      unfold POS_REQUEST_LINE, POS_ENTITY, POS_COMPLETE in *.
      specialize (ENTP ltac:(lia)). specialize (M11 ltac:(lia)).
      pose proof INV as INV'. open_RQ INV'. open_PP PP.
      assert (ISR : ps_isreq (stof bs cur meth uc maj min err pos ub UB) = isreq) by reflexivity.
      unfold pp_st. change (wz PP_REQL) with (wz 0x15cb8 : word).
      eapply (rq_loop (Datatypes.S (Z.to_nat (len - cur))) gp F fc _ s LB m bs cur meth uc maj min err pos ub UB j0 [C8 j8] j40 j48 ja jb j64 j72 j80);
        [exact INV| | lia| exact ISR|].
      { split; [exact Q0|]. split; [exact Q8|]. split; [reflexivity|]. split; [exact Q40|]. split; [exact Q56|]. split; [exact Q64| exact Q72]. }
      intros m' c0 tyw' tb' tl' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' INV1 FR1 LEC.
      eapply rq_line; [exact INV1| exact FR1| exact ISR| exact M11| lia| exact ENTP].
    Qed.

  End ARM.

  #[using="AC LOK MALPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG SNC GOTGIFST GOTGMAXST TABST ZST MTST GIFST GMST IWST"] Theorem reql_ok : reql_stmt AI.
  Proof.
    unfold reql_stmt. intros P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX.
    unfold reql_arm. intros s LB m st x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc CORE SIDE POS.
    destruct st as [cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB].
    cbn [ps_pos] in POS.
    eapply reql_arm_pre; try eassumption; try exact P8; try exact Q16.
  Qed.
End W.

Theorem reql_proof {HCEIL : HasCeiling} : forall (AI : alloc_if rsegs) (AC : alloc_contracts AI),
  layout_ok AI -> al_malloc_pc (ai_L rsegs AI) = 0x180f0 -> al_tp (ai_L rsegs AI) = 0x3b820 -> al_errno (ai_L rsegs AI) = 0x3b77c ->
  canary_ok AI -> (forall lo hi, al_client_static (ai_L rsegs AI) lo hi -> hi <= al_errno (ai_L rsegs AI) \/ al_errno (ai_L rsegs AI) + 4 <= lo) ->
  blk4096_ok AI -> blk_img_ok AI -> strncasecmp_stmt ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= METHOD_TAB /\ METHOD_TAB + 176 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= GIF /\ GIF + 4 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= GMAXA /\ GMAXA + 8 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= INITWASCALLED /\ INITWASCALLED + 1 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= GOT_GIF /\ GOT_GIF + 8 <= hi) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= GOT_GMAX /\ GOT_GMAX + 8 <= hi) ->
  reql_stmt AI.
Proof.
  intros. eapply reql_ok; eassumption.
Qed.

