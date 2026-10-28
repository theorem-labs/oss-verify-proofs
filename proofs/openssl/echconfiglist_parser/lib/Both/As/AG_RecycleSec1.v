(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazyLedger AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsDepotInv AW_DepotFrame
     AllocWalkKit SecLazy SecLazy2 AS_SecRecycle1 AS_SecRecycle2 AG_Malloc AG_Malloc2 AG_MallocModel AG_WFHit AG_FreeModel AG_WFFree
     AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_RepQFrame2 AG_RecycleModel AG_WriteSet AG_RecycleDefs AG_RecycleSecModel.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma map_upd_nth : forall {A B} (f : A -> B) l i x, List.map f (upd_nth l i x) = upd_nth (List.map f l) i (f x).
Proof. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity| reflexivity| reflexivity| rewrite IH; reflexivity]. Qed.
Lemma rs_chunks_upd : forall (l : list Z) i x, (i < length l)%nat -> nth_error l (length l - 1)%nat = Some x ->
  rs_chunks l (Z.of_nat i) (zlen l) x = upd_nth l i x.
Proof.
  intros l i x Hi Hl. unfold rs_chunks. destruct (Z.eqb_spec (Z.of_nat i) (zlen l - 1)) as [E|NE].
  - assert (EI : i = (length l - 1)%nat) by (unfold zlen in E; lia). subst i.
    destruct l as [|z l0]; [cbn in Hi; lia|].
    destruct (exists_last (l := z :: l0) ltac:(discriminate)) as [l2 [y EQ]]. rewrite EQ in Hl |- *.
    rewrite length_app in Hl |- *. cbn [length] in Hl |- *. replace (length l2 + 1 - 1)%nat with (length l2) in Hl |- * by lia.
    rewrite nth_error_app2, Nat.sub_diag in Hl by lia. cbn in Hl. injection Hl as ->. rewrite upd_nth_last. reflexivity.
  - rewrite Nat2Z.id. clear Hl NE. revert i Hi. induction l as [|y l IH]; intros [|i] Hi; cbn in Hi |- *; try lia; [reflexivity|].
    rewrite <- (IH i) by lia. reflexivity.
Qed.
Lemma nth_error_upd_nth_same : forall {A} (l : list A) i x, (i < length l)%nat -> nth_error (upd_nth l i x) i = Some x.
Proof. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try lia; [reflexivity| apply IH; lia]. Qed.
Lemma nth_error_upd_nth_other : forall {A} (l : list A) i j x, i <> j -> nth_error (upd_nth l i x) j = nth_error l j.
Proof. induction l as [|y l IH]; intros [|i] [|j] x H; cbn; try reflexivity; [exfalso; exact (H eq_refl)| apply IH; congruence]. Qed.
End HCW.

Section RSPost.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m0 : mem) (XC XB : list Z) (ch : chunk) (idx : nat) (h lsth : schunk) (d : depot) (lo : Z).
  Let st := a_st s.
  Let T := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let pa := a_pa s.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let mch := ch_chunk_beg ch.
  Let U := ch_user_beg ch.
  Let a := sc_map_beg h.
  Let msz := sc_map_size h.
  Let lst := sc_map_beg lsth.
  Let chunks := List.map sc_map_beg (as_sec st).
  Let l1 := secdel_l1 (as_sec st) idx.
  Let st2 := remove_map (set_sec (del_state st ch) nres l1) a.
  Let L2 := rs_L (a_L s) a msz.
  Let s2 := mkAst st2 T CTX (a_fsb s) L2 (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

  Hypothesis RQ : AREPQ s (mch :: XC) XB m0.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis SEC : ch_primary ch = false.
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis HIDX : nth_error (as_sec st) idx = Some h.
  Hypothesis HMAP : sc_map_beg h = sec_map_beg ch.
  Hypothesis HLAST : nth_error (as_sec st) (length (as_sec st) - 1)%nat = Some lsth.
  Hypothesis DPL : depot_placed s d.
  Hypothesis LO : aceil <= lo.

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st (mch :: XC) XB. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok s /\ WFQ (a_st s) (mch :: XC) XB. Proof. exact (conj PL WQ). Qed.
  Let MEM : ARmem s m0. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ WQ). Qed.
  Let SND : List.NoDup (List.map sc_map_beg (as_sec st)). Proof. pose proof WQ as WW. destruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.
  Let HIN : In h (as_sec st). Proof. eapply nth_error_In. exact HIDX. Qed.
  Let LIN : In lsth (as_sec st). Proof. eapply nth_error_In. exact HLAST. Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECP & SEC2 & TCX).

  (* [comment removed for export] *)
  Let ENT : sc_map_beg h = a /\ sc_size h = rq_needed (compute_req (ch_used ch)) /\ msz = round_up (sc_size h) kPageSize + kPageSize
            /\ find_sec_idx (as_sec st) a 0%nat = Some idx /\ rq_primary (compute_req (ch_used ch)) = false /\ in_primary st (ch_alloc_beg ch) = false
            /\ ch_rz ch = 2048 /\ U = ch_alloc_beg ch + 2048 /\ mch = ch_alloc_beg ch + 2032 /\ ch_alloc_beg ch = a + kPageSize
            /\ ch_lo ch = a /\ ch_end ch = a + msz /\ 1 <= ch_used ch.
  Proof.
    pose proof (sec_entry st XC XB ch WQ CHIN SEC) as (i0 & h0 & Hi0 & Hb0 & Hs0 & Hm0 & FX0 & NP & NIP & RZ & UP & MP).
    pose proof (find_sec_idx_nodup _ _ _ _ SND HIDX HMAP) as FX1.
    assert (EI : i0 = idx) by congruence. subst i0. assert (EH : h0 = h) by congruence. subst h0.
    destruct (WFQ_chunk st _ _ ch WQ CHIN) as (K1 & _).
    unfold ch_lo, ch_end. rewrite SEC. fold a in HMAP. unfold sec_map_beg in HMAP.
    refine (conj eq_refl (conj Hs0 (conj Hm0 (conj _ (conj NP (conj NIP (conj RZ (conj UP (conj MP _))))))))).
    - pose proof FX1 as FX2. unfold sec_map_beg in FX2. rewrite <- HMAP in FX2. exact FX2.
    - subst msz. rewrite Hm0, Hs0. unfold kPageSize in *. repeat split; lia.
  Qed.
  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599296 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
            /\ 1 <= nch <= nres /\ nres <= 16384 /\ 12599296 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
            /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 12599296 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
  Proof.
    placed. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4). pose proof ENT as (_ & Hs & Hm & _).
    pose proof WQ as WW. destruct WW as (_ & _ & _ & _ & _ & _ & Wn & Wr & _).
    pose proof (SECP h HIN) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (SECP lsth LIN) as (L1' & L2' & L3' & L4' & _). fold a msz in Q1, Q2, Q3, Q4. fold lst in L1', L2', L3', L4'.
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia]. apply aapp_env in X2; [| clear; lia].
    apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia]. apply aapp_env in F1; [| unfold AFS_SIZE; clear; lia].
    pose proof (aapp_sh_env_div _ _ Q2 ltac:(unfold kPageSize in Q4; clear - Q4; lia)) as ASH. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
    apply aapp_env in L2'; [| unfold kPageSize in L4'; clear - L4'; lia].
    pose proof (nth_error_lt _ _ _ HIDX) as LT.
    assert (MZ : msz mod 4096 = 0).
    { rewrite Hm. unfold round_up, kPageSize. set (q := (sc_size h + 4096 - 1) / 4096). replace (q * 4096 + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve, kChunksBlockCount in *.
    subst T sb pa nch nres. unfold a_sb in *. unfold st in *.
    assert (NN : 1 <= zlen (as_sec (a_st s))) by (unfold zlen; clear - LT; lia).
    repeat split; try (first [clear - LO T2 T3 S2 S3 X2 X3 P2 P3 N1 N2 N3 N4 Q2 Q3 Q4 ASH NN Wn Wr F1 F2 Q1 MZ LT L2' L4' L3' L1'; lia | lia]).
  Qed.
  Let BANDS : hidden ((T + 4096 <= 65536 \/ (12599296 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)
                   /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                   /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                   /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                   /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
  Proof.
    placed. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & N3 & _).
    pose proof (SECP h HIN) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (SECP lsth LIN) as (_ & L2' & _ & L4' & _). fold a msz in Q2, Q4. fold lst in L2', L4'.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
    split; [exact (aapp_lit _ _ N1)|]. split; [exact (aapp_lit _ _ N3)|]. split; [exact (aapp_lit _ _ Q2)|].
    split; [exact (aapp_sh_lit_div _ _ Q2 ltac:(unfold kPageSize in Q4; clear - Q4; lia))|]. split; [exact (aapp_lit _ _ F1)|].
    pose proof (aapp_lit _ _ L2') as L. unfold kPageSize in L4'. clear - L L4'. unfold aapp_lo, aapp_hi in *. lia.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  (* [comment removed for export] *)
  Let PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
            /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 131072)
            /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
  Proof.
    placed. pose proof (SECP h HIN) as (_ & _ & _ & _ & Q5 & Q6 & Q7 & Q8 & Q9). destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & DS & _).
    destruct (DS h HIN) as [E1 E2]. fold a msz in Q5, Q6, Q7, Q8, Q9, E1, E2.
    refine (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj E1 (conj E2 _))))))).
    intros sc Hin NE. apply (SEC2 h sc HIN Hin). fold a. intros E. exact (NE (eq_sym E)).
  Qed.

  (* [comment removed for export] *)
  Lemma rs_ent : sc_map_beg h = a /\ sc_size h = rq_needed (compute_req (ch_used ch)) /\ msz = round_up (sc_size h) kPageSize + kPageSize
            /\ find_sec_idx (as_sec st) a 0%nat = Some idx /\ rq_primary (compute_req (ch_used ch)) = false /\ in_primary st (ch_alloc_beg ch) = false
            /\ ch_rz ch = 2048 /\ U = ch_alloc_beg ch + 2048 /\ mch = ch_alloc_beg ch + 2032 /\ ch_alloc_beg ch = a + kPageSize
            /\ ch_lo ch = a /\ ch_end ch = a + msz /\ 1 <= ch_used ch.
  Proof. exact ENT. Qed.
  Lemma rs_bnd : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599296 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
            /\ 1 <= nch <= nres /\ nres <= 16384 /\ 12599296 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
            /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 12599296 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
  Proof. exact BND. Qed.
  Lemma rs_bands : hidden ((T + 4096 <= 65536 \/ (12599296 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)
                   /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                   /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                   /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                   /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
  Proof. exact BANDS. Qed.
  Lemma rs_pnew : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
            /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 131072)
            /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
  Proof. exact PNEW. Qed.

  (* [comment removed for export] *)
  Variables (m2 : mem) (spv : Z).
  (* [comment removed for export] *)
  Let W : list ivl := rs_W lo (wz spv) a msz pa nch lst T.
  Hypothesis SPV : 0 <= spv < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis MU : munch W m0 m2.
  Hypothesis WMO : wmono_out [(a, a + msz)] m0 m2.
  Hypothesis MI2 : mem_inv asegs m2.
  Hypothesis INST2 : rw_cells asegs m2 (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES2 : rw_cells asegs m2 (AINST + 112) [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)].
  Hypothesis SST2 : stk asegs m2 (AINST + 136) (AINST + 680).
  Hypothesis MTX2 : rw_cells asegs m2 (AINST + 680) [C8 (wz 0)].
  Hypothesis GST2 : stk asegs m2 (AINST + 688) (AINST + 728).
  Hypothesis PA2 : u64arr asegs m2 pa (wlist (rs_chunks chunks (Z.of_nat idx) nch lst)).
  Hypothesis LSTC2 : Z.of_nat idx < nch - 1 -> rw_cells asegs m2 (lst + 24) [C8 (wz (Z.of_nat idx))].
  Hypothesis TST2 : stk asegs m2 (T + 2800) (T + 3168).
  Hypothesis SH2 : u8arr asegs m2 (sh a) (repeat (b8 0) (Z.to_nat (msz / 8))).
  Hypothesis GONE : forall x : word, a <= bv_unsigned x < a + msz -> m2 x = None.

  (* [comment removed for export] *)
  Let AG : agree_on (outside W) m0 m2.
  Proof. intros x Hx Hr. pose proof (MU (wa x)) as E. rewrite wa_unsigned in E by exact Hr. exact (E Hx). Qed.
  Let SPE : bv_unsigned (wz spv) = spv. Proof. unfold wz. apply unsigned_lit. exact SPV. Qed.
  Ltac wsplit := unfold W, rs_W; rewrite ?SPE; cbn [outside app]; repeat split; try exact I.

  (* [comment removed for export] *)
  Lemma Z_lo : forall x, 65536 <= x < AIMG_TOP -> ~ (AINST + 112 <= x < AINST + 728) -> outside W x.
  Proof.
    intros x Hx Hn. pose proof BND as B. bands_as (BT & _ & BP & _ & _ & BA & BS & _ & BL). clear - Hx Hn B BT BP BA BS BL SPE; try acb.
    unfold AIMG_TOP, AINST in *. wsplit; (first [clear - B Hx Hn BT; tlia | tlia]).
  Qed.
  (* [comment removed for export] *)
  Lemma Z_static : forall x, astatic x -> ~ (AINST + 112 <= x < AINST + 728) -> outside W x.
  Proof.
    intros x Hx Hn. apply Z_lo; [| exact Hn]. clear - Hx. unfold astatic in Hx.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP, AIMG_TOP in *.
    lia.
  Qed.
  Lemma Z_flags : forall x, aflags_range x -> outside W x.
  Proof.
    intros x Hx. apply Z_lo; clear - Hx; unfold aflags_range in Hx;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP, AINST, AIMG_TOP in *; lia.
  Qed.
  Lemma Z_T : forall x, T <= x < T + 4096 -> ~ (T + 2800 <= x < T + 3168) -> outside W x.
  Proof.
    intros x Hx Hn. pose proof BND as B. placed. destruct PNEW as (_ & _ & N3 & _). pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _ & _ & L7 & _). fold lst T in L7.
    bands_as (BT & _). clear - Hx Hn B D2 D4 N3 L4 L7 BT SPE; try acb. subst T pa sb. unfold a_sb, disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - B Hx BT D4 N3 L7 L4 ACEILB Hn; tlia | tlia]).
  Qed.
  Lemma Z_CTX : forall x, CTX + 8 <= x < CTX + 160 -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct PNEW as (_ & _ & _ & N4 & _). pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _ & _ & _ & L8 & _). fold lst CTX in L8.
    bands_as (_ & BC & _). clear - Hx B D5 TCX N4 L4 L8 BC SPE; try acb. subst T pa CTX. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - B Hx D5 N4 L8 L4 ACEILB BC TCX; tlia | tlia]).
  Qed.
  Lemma Z_SB : forall x, sb <= x < sb + kSpaceSize + kPageSize -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct PNEW as (N1 & _). pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & L5 & _). fold lst sb in L5.
    clear - Hx B D1 D2 N1 L4 L5 SPE; try acb. subst T pa sb. unfold a_sb, disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - B Hx D1 N1 L5 L4 ACEILB D2; tlia | tlia]).
  Qed.
  Lemma Z_PA : forall x, pa + 8 * nch <= x < pa + 8 * nres -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct PNEW as (_ & N2 & _). pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _ & L6 & _). fold lst pa in L6.
    bands_as (_ & _ & BP & _). clear - Hx B D4 N2 L4 L6 BP SPE; try acb. subst T pa. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - B Hx N2 L6 L4 ACEILB BP D4; tlia | tlia]).
  Qed.
  Lemma Z_SEC : forall h' x, In h' (as_sec st) -> sc_map_beg h' <> a -> sc_map_beg h' <= x < sc_map_beg h' + sc_map_size h' ->
    ~ (lst + 24 <= x < lst + 32) -> outside W x.
  Proof.
    intros h' x Hh NE Hx Hn. pose proof BND as B. placed. pose proof (SECP h' Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    destruct PNEW as (_ & _ & _ & _ & _ & _ & _ & N8). pose proof (N8 h' Hh NE) as D.
    pose proof (aapp_lit _ _ Q2) as Q2l. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
    clear - Hx Hn B Q2 Q2l Q3 Q5 Q6 Q7 D SPE; try acb. subst sb T pa. unfold a_sb, disj, kSpaceSize, kPageSize, kPtrArrayReserve, AHI_LO, AINST in *.
    acb. wsplit; (first [clear - Q3 B Hx Q2 Q6 D Hn ACEILB0 Q2l Q7; tlia | tlia]).
  Qed.
  Lemma Z_SH : forall lo' k x, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= k -> lo' + 8 * k <= aceil ->
    (lo' + 8 * k <= a \/ a + msz <= lo') -> sh lo' <= x < sh lo' + k -> outside W x.
  Proof.
    intros lo' k x H0 H8 Hk Hhi Hd Hx. pose proof BND as B.
    assert (A8 : a mod 8 = 0) by (clear - B; try acb; Z.div_mod_to_equations; lia).
    assert (M8 : 8 * (msz / 8) = msz) by (clear - B; try acb; Z.div_mod_to_equations; lia).
    assert (SS : sh lo' + k <= sh a \/ sh a + msz / 8 <= sh lo') by (clear - H8 A8 Hk Hd B M8; try acb; apply sh_sep; try assumption; lia).
    assert (SR : 0x7fff8000 <= sh lo' /\ sh lo' + k <= 0x10007fef8000) by (clear - H0 Hk Hhi; try acb; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    bands_as (BT & _ & BP & BN & BS & BA & _ & _ & BL). clear - Hx B SS SR BT BP BN BS BA BL SPE; try acb. subst T pa. unfold AINST in *. wsplit; (first [clear - SR B Hx BP BA BL SS BT; tlia | tlia]).
  Qed.
  (* [comment removed for export] *)
  Let LT : (idx < length (as_sec st))%nat. Proof. exact (nth_error_lt _ _ _ HIDX). Qed.
  Let LEN1 : length l1 = (length (as_sec st) - 1)%nat. Proof. unfold l1. apply secdel_l1_length. exact LT. Qed.
  Let ZLEN1 : zlen l1 = nch - 1. Proof. unfold zlen, nch, zlen. rewrite LEN1. clear - LT. lia. Qed.
  Let L1IN : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
  Proof. intros y. unfold l1, a. exact (secdel_l1_in _ _ _ _ SND HIDX). Qed.
  Let SUB1 : forall y, In y l1 -> In y (as_sec st). Proof. intros y Hy. exact (proj1 (proj1 (L1IN y) Hy)). Qed.
  Let CHUNKS1 : rs_chunks chunks (Z.of_nat idx) nch lst = List.map sc_map_beg l1 ++ [lst].
  Proof.
    assert (LC : length chunks = length (as_sec st)) by (unfold chunks; apply length_map).
    assert (HL' : nth_error chunks (length chunks - 1)%nat = Some lst) by (unfold chunks, lst; rewrite length_map, nth_error_map, HLAST; reflexivity).
    unfold nch. replace (zlen (as_sec st)) with (zlen chunks) by (unfold zlen; rewrite LC; reflexivity).
    rewrite (rs_chunks_upd chunks idx lst ltac:(rewrite LC; exact LT) HL').
    unfold l1, secdel_l1. rewrite <- firstn_map, map_upd_nth. fold chunks. rewrite (znth_nth_error _ _ _ _ HLAST). fold lst.
    rewrite <- LC.
    set (u := upd_nth chunks idx lst).
    assert (LU : length u = length chunks) by (unfold u; apply upd_nth_length).
    assert (NZ : (0 < length chunks)%nat) by (rewrite LC; clear - LT; lia).
    assert (HY : nth_error u (length chunks - 1)%nat = Some lst).
    { unfold u. destruct (Nat.eq_dec idx (length chunks - 1)%nat) as [E|NE]; [rewrite E; apply nth_error_upd_nth_same; clear - NZ; lia| rewrite nth_error_upd_nth_other by exact NE; exact HL']. }
    rewrite <- (firstn_skipn (length chunks - 1)%nat u) at 1. f_equal.
    rewrite <- LU in HY |- *. destruct (exists_last (l := u) ltac:(intros E; rewrite E in LU; cbn in LU; (first [clear - NZ LU; lia | lia]))) as [u0 [y EQ]].
    rewrite EQ in HY |- *. rewrite length_app in HY |- *. cbn [length] in HY |- *. replace (length u0 + 1 - 1)%nat with (length u0) in HY |- * by (first [clear; lia | lia]).
    rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. rewrite nth_error_app2, Nat.sub_diag in HY by lia. cbn in HY. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma placed_after : placed_ok s2.
  Proof.
    placed. unfold placed_ok. change (a_sb s2) with sb. change (a_pa s2) with pa. change (a_thr s2) with T. change (a_ctx s2) with CTX.
    change (a_fsb s2) with (a_fsb s). change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s). change (as_sec (a_st s2)) with l1.
    refine (conj S1 (conj S2 (conj S3 (conj P1 (conj P2 (conj P3 (conj T1 (conj T2 (conj T3 (conj X1 (conj X2 (conj X3 (conj D1 (conj D2 (conj D3 (conj D4 (conj D5
            (conj F1 (conj F2 (conj D6 (conj D7 (conj D8 (conj D9 (conj _ (conj _ TCX))))))))))))))))))))))))).
    - intros sc Hin. exact (SECP sc (SUB1 sc Hin)).
    - intros sc sc' Hin Hin' NE. exact (SEC2 sc sc' (SUB1 sc Hin) (SUB1 sc' Hin') NE).
  Qed.
  Lemma depot_placed_after : depot_placed s2 d.
  Proof.
    destruct DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10). unfold depot_placed. change (as_sec (a_st s2)) with l1.
    refine (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj _ G10))))))))).
    intros sc Hin. exact (G9 sc (SUB1 sc Hin)).
  Qed.
  Let WQ2 : WFQ st2 XC XB.
  Proof. pose proof (WFQ_del_sec_at st XC XB ch WQ CHIN SEC idx h HIDX HMAP) as X. rewrite <- HMAP in X. exact X. Qed.
  Ltac trw H Z Hz := eapply (rw_cells_transport_ag (outside W) m0 m2 AG); [exact H|];
                  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat List.map];
                  intros ? Hz; apply Z.
  Ltac trj H Z Hz := eapply (junk_transport_ag (outside W) m0 m2 AG); [exact H|]; intros ? Hz; apply Z.
  Ltac inst_static Hz := clear - Hz; try acb; first [unfold astatic; left; unfold OI_MISMATCH, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia
                            | unfold OI_MISMATCH, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia].

  (* [comment removed for export] *)
  Lemma statics_after : inst_rep s2 m2 /\ flags_rep s2 m2 /\ ia_rep s2 m2 /\ sec_rep s2 m2.
  Proof.
    destruct MEM as (INST & FL & _ & SEC0 & IA & _). pose proof BND as B.
    split.
    { destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & A5 & J5 & A6 & A7 & J6 & A8 & J7 & A9).
      unfold inst_rep. change (a_sb s2) with sb. change (a_ri s2) with (a_ri s). change (a_pa s2) with pa.
      change (as_n_reserved (a_st s2)) with nres. change (as_sec (a_st s2)) with l1. rewrite ZLEN1.
      change (as_qmax (a_st s2)) with (as_qmax st). change (as_qmin (a_st s2)) with (as_qmin st). change (as_qcache (a_st s2)) with (as_qcache st).
      change (as_gq (a_st s2)) with (as_gq st).
      split; [trw A1 Z_static Hz; inst_static Hz|].
      split; [trj J1 Z_static Hz; inst_static Hz|].
      split; [exact NRES2|].
      split; [intros _; unfold OI_SECMUTEX; replace (AINST + 136 + (680 - 136)) with (AINST + 680) by (first [clear; lia | lia]); exact SST2|].
      split; [exact MTX2|].
      split; [intros _; unfold OI_GSTATS, OI_Q; replace (AINST + 688 + (728 - 688)) with (AINST + 728) by lia; exact GST2|].
      split; [trj J4 Z_static Hz; inst_static Hz|].
      split; [trw A5 Z_static Hz; inst_static Hz|].
      split; [trj J5 Z_static Hz; inst_static Hz|].
      split; [trw A6 Z_static Hz; inst_static Hz|].
      split; [trw A7 Z_static Hz; inst_static Hz|].
      split; [trj J6 Z_static Hz; inst_static Hz|].
      split; [trw A8 Z_static Hz; inst_static Hz|].
      split; [trj J7 Z_static Hz; inst_static Hz| trw A9 Z_static Hz; inst_static Hz]. }
    split.
    { apply (flags_rep_frame_ag s2 m0 m2 (outside W) AG); [exact Z_flags| exact FL]. }
    split.
    { apply (ia_rep_frame_ag s2 m0 m2 (outside W) AG); [| exact IA]. intros x Hx. apply Z_static; [unfold astatic; do 11 right; left; exact Hx|].
      clear - Hx; try acb. unfold AIAINST, AINST in *. lia. }
    (* [comment removed for export] *)
    destruct SEC0 as (U0 & J0 & H0). unfold sec_rep. change (a_pa s2) with pa. change (as_sec (a_st s2)) with l1. change (as_n_reserved (a_st s2)) with nres. rewrite ZLEN1.
    pose proof PA2 as PA2'. rewrite CHUNKS1 in PA2'. unfold wlist in PA2'. rewrite map_app in PA2'. cbn [List.map] in PA2'.
    apply u64arr_snoc in PA2' as [PA3 LAST3]. rewrite length_map, length_map, LEN1 in LAST3.
    replace (8 * Z.of_nat (length (as_sec st) - 1)) with (8 * (nch - 1)) in LAST3 by (unfold nch, zlen; clear - LT; lia).
    split; [exact PA3|].
    split.
    { intros _. apply (stk_merge asegs m2 _ (pa + 8 * nch)).
      - pose proof (stk_of_rw_cells asegs m2 _ _ LAST3) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K.
        replace (pa + 8 * (nch - 1) + 8) with (pa + 8 * nch) in K by (first [clear; lia | lia]). exact K.
      - destruct (Z.eq_dec nch nres) as [E|NE]; [rewrite <- E; replace (pa + 8 * (nch - 1) + 8 * (nch - (nch - 1))) with (pa + 8 * nch) by (first [clear - BND SPV LT LEN1; lia | lia]); apply stk_empty; clear - B; try acb; lia|].
        change (a_pa s) with pa in J0. change (zlen (as_sec (a_st s))) with nch in J0. change (as_n_reserved (a_st s)) with nres in J0.
        assert (B1 : 0 <= pa + 8 * nch) by (clear - B; try acb; lia). assert (B2 : pa + 8 * nch + 8 * (nres - nch) <= 2 ^ 64) by (clear - B; try acb; lia).
        assert (B3 : 0 <= 8 * (nres - nch)) by (clear - B; try acb; lia).
        pose proof (junk_stk' _ _ _ J0 B1 B2 B3) as K.
        replace (pa + 8 * nch + 8 * (nres - nch)) with (pa + 8 * nres) in K by (first [clear; lia | lia]).
        replace (pa + 8 * (nch - 1) + 8 * (nres - (nch - 1))) with (pa + 8 * nres) by (first [clear; lia | lia]).
        eapply (stk_transport_ag (outside W) m0 m2 AG); [exact K|]. intros x Hx. apply Z_PA. exact Hx.
      - clear - B; try acb. lia. }
    intros j h' Hj. pose proof (nth_error_lt _ _ _ Hj) as LJ. rewrite LEN1 in LJ.
    (* [comment removed for export] *)
    assert (CASE : (j <> idx /\ nth_error (as_sec st) j = Some h') \/ (j = idx /\ h' = lsth /\ Z.of_nat idx < nch - 1)).
    { unfold l1, secdel_l1 in Hj. rewrite nth_error_firstn in Hj.
      replace (Nat.ltb j (length (as_sec st) - 1)) with true in Hj by (symmetry; apply Nat.ltb_lt; clear - LJ; lia). rewrite (znth_nth_error _ _ _ _ HLAST) in Hj.
      destruct (Nat.eq_dec j idx) as [E|NE].
      - right. subst j. rewrite nth_error_upd_nth_same in Hj by exact LT. split; [reflexivity|]. split; [congruence|]. unfold nch, zlen. clear - LJ; lia.
      - left. rewrite nth_error_upd_nth_other in Hj by (intros E; exact (NE (eq_sym E))). exact (conj NE Hj). }
    assert (Hin' : In h' (as_sec st)) by (destruct CASE as [[_ E]|(_ & -> & _)]; [eapply nth_error_In; exact E| exact LIN]).
    assert (NEa : sc_map_beg h' <> a) by (apply (proj1 (L1IN h')); eapply nth_error_In; exact Hj).
    placed. pose proof (SECP h' Hin') as (_ & _ & _ & Q4 & _). pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _). fold lst in L4.
    destruct CASE as [[NEj Hj0]|(Ej & Eh & LTj)].
    - (* [comment removed for export] *)
      destruct (H0 j h' Hj0) as [C1 J1'].
      assert (NL : sc_map_beg h' <> lst).
      { intros EL. pose proof (proj1 (List.NoDup_nth_error _) SND j (length (as_sec st) - 1)%nat) as X.
        enough (j = (length (as_sec st) - 1)%nat) by (clear - H LJ; lia).
        apply X; [rewrite length_map; clear - LJ; lia|]. rewrite !nth_error_map. rewrite Hj0, HLAST. cbn. unfold lst in EL. congruence. }
      assert (FAR : forall x, sc_map_beg h' <= x < sc_map_beg h' + kPageSize -> outside W x).
      { intros x Hx. apply (Z_SEC h'); [exact Hin'| exact NEa| clear - Hx Q4; try acb; unfold kPageSize in *; lia|].
        pose proof (SEC2 h' lsth Hin' LIN NL) as D. fold lst in D. clear - Hx D L4 Q4; try acb. unfold disj, kPageSize in *. lia. }
      split; [trw C1 FAR Hz; clear - Hz Q4; try acb; unfold kPageSize in *; lia | trj J1' FAR Hz; clear - Hz Q4; try acb; unfold kPageSize in *; lia].
    - (* [comment removed for export] *)
      subst j h'. fold lst. destruct (H0 _ _ HLAST) as [C1 J1']. fold lst in C1, J1'.
      assert (FAR : forall x, lst <= x < lst + kPageSize -> ~ (lst + 24 <= x < lst + 32) -> outside W x).
      { intros x Hx Hn. apply (Z_SEC lsth); [exact LIN| exact NEa| clear - Hx L4; try acb; unfold kPageSize in *; lia| exact Hn]. }
      apply (rw_cells_app asegs _ _ [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth))] [C8 (wz (Z.of_nat (length (as_sec st) - 1)%nat))]) in C1.
      destruct C1 as [C1 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C1.
      split.
      + apply (rw_cells_app asegs _ _ [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth))] [C8 (wz (Z.of_nat idx))]).
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact (LSTC2 LTj)].
        trw C1 FAR Hz; clear - Hz L4; try acb; unfold kPageSize in *; lia.
      + trj J1' FAR Hz; clear - Hz L4; try acb; unfold kPageSize in *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma thread_after : thread_rep s2 m2.
  Proof.
    pose proof BND as B. destruct MEM as (_ & _ & THR & _).
    destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_ctx s2) with CTX. change (a_thr s2) with T. change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s).
    change (a_cache s2) with (a_cache s). change (as_tq (a_st s2)) with (as_tq st).
    fold T CTX in T1, T2, T2b, T2c, T2d, T3, T4, J1, J3, T5. unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
    split; [trw T1 Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T2 Z_CTX Hz; clear - Hz; try acb; lia|]. split; [trw T2b Z_CTX Hz; clear - Hz; try acb; lia|].
    split; [trw T2c Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T2d Z_T Hz; clear - Hz; try acb; lia|].
    split; [trw T3 Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T4 Z_T Hz; clear - Hz; try acb; lia|].
    split; [trj J1 Z_T Hz; clear - Hz; try acb; lia|].
    split; [unfold a_cache, OT_CACHE in *; fold T in J2 |- *; trj J2 Z_T Hz; clear - Hz; try acb; lia|].
    split; [intros _; replace (T + 2800 + (3168 - 2800)) with (T + 3168) by (clear; lia); exact TST2|].
    trw T5 Z_T Hz; clear - Hz; try acb; lia.
  Qed.
  (* [comment removed for export] *)
  Let CHL2 : forall x, In x (chunk_list st2) -> In x (chunk_list st) /\ x <> ch.
  Proof.
    intros x Hx. change (chunk_list st2) with (chunk_list (del_state st ch)) in Hx.
    apply (del_in st ch KEYS CHIN) in Hx. destruct Hx as [Hx NE]. split; [exact Hx|]. intros ->. exact (NE eq_refl).
  Qed.
  (* [comment removed for export] *)
  Lemma Z_rec : forall x y, In x (chunk_list st) -> x <> ch -> ch_alloc_beg x <= y < ch_end x -> outside W y.
  Proof.
    intros x y Hx NEQ Hy. pose proof BND as B. placed. clear S1 S2 S3 P1 P2 P3 T1 T2 T3 X1 X2 X3 D1 D2 D3 D4 D5 F1 F2 D6 D7 D8 D9 TCX.
    pose proof (record_extQ s _ _ OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (record_vs_recordQ s _ _ OKQ ch CHIN x Hx NEQ) as D.
    pose proof ENT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E11 & E12 & _). rewrite E11, E12 in D.
    assert (NS : ch_used x <= round_up (ch_used x) 8) by (unfold round_up; clear - X9; Z.div_mod_to_equations; lia).
    destruct (ch_primary x) eqn:PX.
    - destruct (record_primary_spaceQ s _ _ OKQ x Hx PX) as [P1 P2]. change (a_sb s) with sb in P1, P2.
      apply Z_SB. unfold kSpaceSize, kPageSize in P2 |- *. clear - Hy P1 P2 X3; try acb. lia.
    - destruct (record_secondary_mapQ s _ _ OKQ x Hx PX) as (h' & Hh & M1 & M2 & M3). change (as_sec (a_st s)) with (as_sec st) in Hh.
      assert (NEa : sc_map_beg h' <> a) by (intros Ea; clear - D M1 Ea X3 X6 X7 X8 X9 NS B; try acb; lia).
      apply (Z_SEC h'); [exact Hh| exact NEa| clear - Hy M1 M2 M3 X3; try acb; unfold kPageSize in *; lia|].
      destruct (Z.eq_dec (sc_map_beg h') lst) as [EL|NL]; [clear - Hy M3 EL; try acb; unfold kPageSize in *; lia|].
      pose proof (SEC2 h' lsth Hh LIN NL) as DD. pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _). fold lst in DD, L4.
      clear - Hy DD L4 M1 M2 M3 X3; try acb. unfold disj, kPageSize in *. lia.
  Qed.
  Lemma Z_rec_sh : forall x lo' k y, In x (chunk_list st) -> x <> ch ->
    ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k -> sh lo' <= y < sh lo' + k -> outside W y.
  Proof.
    intros x lo' k y Hx NEQ G1 G2 G3 G4 Gy.
    pose proof (record_extQ s _ _ OKQ x Hx) as (X1 & X2 & _). pose proof (record_vs_recordQ s _ _ OKQ ch CHIN x Hx NEQ) as D.
    pose proof ENT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E11 & E12 & _). rewrite E11, E12 in D. unfold AIMG_TOP in X1.
    apply (Z_SH lo' k); try assumption.
    - clear - G1 X1. lia.
    - clear - G2 X2. lia.
    - clear - G1 G2 D. lia.
  Qed.
  Lemma chunks_after : forall x, In x (chunk_list st2) -> chunk_rep m2 x.
  Proof.
    intros x Hx2. destruct (CHL2 x Hx2) as [Hx NEQ]. destruct MEM as (_ & _ & _ & _ & _ & _ & CHR & _).
    pose proof (record_extQ s _ _ OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8 /\ (round_up (ch_used x) 8) mod 8 = 0)
      by (unfold nsh, round_up; clear - X9; Z.div_mod_to_equations; lia).
    pose proof (chunk_alignQ s _ _ OKQ x Hx) as (A1 & A2 & A3 & A4 & A5).
    assert (AL8 : ch_alloc_beg x mod 8 = 0 /\ ch_user_beg x mod 8 = 0 /\ 8 * (ch_rz x / 8) = ch_rz x)
      by (clear - A1 A2 A3; Z.div_mod_to_equations; lia).
    clear A1 A2 A3. destruct AL8 as (A1 & A3 & RZ8).
    pose proof (Z_rec x) as APP. pose proof (Z_rec_sh x) as SHW.
    apply (chunk_rep_frameQ_ag s (mch :: XC) XB m0 m2 (outside W) AG WQ x Hx); [| exact (CHR x Hx)].
    intros y [Hy|[AX' Hy]].
    - destruct Hy as [Hy|[Hy|[[Q Hy]|[Hy|[Hy|[[Q Hy]|[NP Hy]]]]]]].
      + apply (APP y Hx NEQ). clear - Hy X3 X6 X7 X9 NS. lia.
      + apply (APP y Hx NEQ). clear - Hy X3 X6 X8 X9. lia.
      + apply (APP y Hx NEQ). clear - Hy X3 X6 X7 X8 NS. lia.
      + apply (SHW (ch_alloc_beg x) (ch_rz x / 8) y Hx NEQ); clear - Hy X3 X6 X7 X8 X9 NS A1 RZ8; lia.
      + apply (SHW (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) y Hx NEQ);
          clear - Hy X3 X6 X7 X8 X9 NS A3 A4; try lia; Z.div_mod_to_equations; lia.
      + apply (SHW (ch_user_beg x) (nsh (ch_used x)) y Hx NEQ); clear - Hy X3 X6 X7 X8 X9 NS A3; try lia; unfold nsh; Z.div_mod_to_equations; lia.
      + unfold ch_lo in SHW. rewrite NP in SHW. apply (SHW (ch_alloc_beg x - kPageSize) 512 y Hx NEQ); unfold kPageSize in *; clear - Hy X3 X6 X7 X8 X9 NS A1;
          try lia; Z.div_mod_to_equations; lia.
    - destruct Hy as [Hy|Hy].
      + apply (APP y Hx NEQ). clear - Hy X3 X6 X7 X8 NS. lia.
      + apply (SHW (ch_user_beg x) (nsh (ch_used x)) y Hx NEQ); clear - Hy X3 X6 X7 X8 X9 NS A3; try lia; unfold nsh; Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma alive_kept_rs : alive_kept st st2.
  Proof.
    intros x Hx AX'. change (chunk_list st2) with (chunk_list (del_state st ch)). apply (del_in st ch KEYS CHIN). split; [exact Hx|].
    intros E. pose proof (WFQ_inj st _ _ WQ x ch Hx CHIN E) as EX. rewrite EX, QUAR in AX'. discriminate AX'.
  Qed.
  Lemma alive_after_rs : agree_on (alive st) m0 m2.
  Proof.
    intros y (x & Hx & AX' & R) Hr. apply AG; [| exact Hr].
    assert (NEQ : x <> ch) by (intros ->; rewrite QUAR in AX'; discriminate AX').
    pose proof (record_extQ s _ _ OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8) by (unfold nsh, round_up; clear - X9; Z.div_mod_to_equations; lia).
    pose proof (chunk_alignQ s _ _ OKQ x Hx) as (_ & _ & A3 & _).
    destruct R as [R|R].
    - apply (Z_rec x y Hx NEQ). clear - R X3 X6 X7 X8 NS. lia.
    - apply (Z_rec_sh x (ch_user_beg x) (nsh (ch_used x)) y Hx NEQ); clear - R X3 X6 X7 X8 X9 NS A3; first [lia| unfold nsh; Z.div_mod_to_equations; lia].
  Qed.
  (* [comment removed for export] *)
  Let BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b).
  Proof. intros b Hb. pose proof (WFQ_batch _ _ _ b WQ Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. clear - B1 B2. lia. Qed.
  Let HPB : forall b y, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
      (qb_addr b <= y < qb_addr b + kBatchSize \/ sh (qb_addr b) <= y < sh (qb_addr b) + kBatchSize / 8) -> outside W y.
  Proof.
    intros b y Hb Hr. pose proof (batch_in_spaceQ s _ _ OKQ b Hb) as (P1 & P2 & P3). change (a_sb s) with sb in P1, P2.
    pose proof BND as B. unfold kBatchSize, kSpaceSize in *. destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1.
    destruct Hr as [Hr|Hr].
    - apply Z_SB. unfold kSpaceSize, kPageSize. clear - Hr P1 P2; try acb. lia.
    - apply (Z_SH (qb_addr b) 1024); try assumption; clear - Hr N1 P1 P2 B; try acb; (first [clear - B P1 P2 N1; lia | lia]).
  Qed.
  Lemma batches_after : batches_rep m2 (qc_list (as_tq st)) /\ batches_rep m2 (qc_list (as_gq st)).
  Proof.
    destruct MEM as (_ & _ & _ & _ & _ & _ & _ & BT & BG).
    split.
    - eapply (batches_rep_transport_ag (outside W) m0 m2); [exact AG| | | exact BT].
      + intros b y Hb Hr. apply (HPB b y); [apply in_app_iff; left; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport_ag (outside W) m0 m2); [exact AG| | | exact BG].
      + intros b y Hb Hr. apply (HPB b y); [apply in_app_iff; right; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma regions_after : forall c0, 0 <= c0 < kNumClasses ->
    region_rep s2 m2 c0 /\ pclass_rep s2 m2 c0 /\ region_shadow_rep s2 m2 c0 /\ region_junk_rep s2 m2 c0.
  Proof.
    intros c0 Hc0. destruct MEM as (_ & _ & _ & _ & _ & RC & _). destruct (RC c0 Hc0) as (R1 & R2 & R3 & R4).
    pose proof BND as B. destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1.
    pose proof (farray_in_spaceQ s _ _ OKQ c0 Hc0) as (F1 & F2 & F3 & F4 & F5). change (a_sb s) with sb in F1, F2. change (a_st s) with st in F2, F4, F5.
    pose proof (tail_in_spaceQ s _ _ OKQ c0 Hc0) as (T1' & T2' & T3' & T4' & T5'). change (a_sb s) with sb in T1', T2'. change (a_st s) with st in T1', T2', T3', T4', T5'.
    assert (ZFA : forall y, FA s c0 <= y < FA s c0 + rg_mapped_free_array (get_region st c0) -> outside W y).
    { intros y Hy. apply Z_SB. unfold kSpaceSize, kPageSize in *. clear - Hy F1 F2; try acb. lia. }
    assert (ZTL : forall y, RB s c0 + rg_allocated_user (get_region st c0) <= y < RB s c0 + rg_mapped_user (get_region st c0) -> outside W y).
    { intros y Hy. apply Z_SB. unfold kSpaceSize, kPageSize in *. clear - Hy T1' T2'; try acb. lia. }
    assert (ZRI : forall y, a_ri s <= y < a_ri s + kPageSize -> outside W y).
    { intros y Hy. unfold a_ri in Hy. fold sb in Hy. apply Z_SB. unfold kSpaceSize, kPageSize in *. clear - Hy; try acb. lia. }
    assert (ZFC : forall cp y, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
                  compact_to_addr st c0 cp <= y < compact_to_addr st c0 cp + class_size c0 -> outside W y).
    { intros cp y Hin Hy. pose proof (freech_in_spaceQ s _ _ OKQ c0 cp Hc0 Hin) as (P1 & P2 & P3 & P4 & P5). change (a_sb s) with sb in P1, P2.
      change (a_st s) with st in P1, P2, P3. apply Z_SB. unfold kSpaceSize, kPageSize in *. clear - Hy P1 P2; try acb. lia. }
    assert (ZFCS : forall cp y, In cp (rg_free_array (get_region st c0)) \/ In cp (pc_chunks (get_pc st c0)) ->
                  sh (compact_to_addr st c0 cp) <= y < sh (compact_to_addr st c0 cp) + class_size c0 / 8 -> outside W y).
    { intros cp y Hin Hy. pose proof (freech_in_spaceQ s _ _ OKQ c0 cp Hc0 Hin) as (P1 & P2 & P3 & P4 & P5). change (a_sb s) with sb in P1, P2.
      change (a_st s) with st in P1, P2, P3.
      assert (C8 : 8 * (class_size c0 / 8) = class_size c0) by (clear - P5; try acb; Z.div_mod_to_equations; lia).
      apply (Z_SH (compact_to_addr st c0 cp) (class_size c0 / 8)); try assumption.
      - clear - P1 B; try acb. lia.
      - clear - P4; try acb. lia.
      - unfold kSpaceSize in P2. clear - P2 B C8; try acb. lia.
      - unfold kSpaceSize in P2. clear - P1 P2 N1 C8; try acb. lia. }
    split.
    { enough (X : region_rep s m2 c0) by exact X.
      apply (region_rep_frameQ_ag s (mch :: XC) XB m0 m2 (outside W) AG WQ c0 Hc0); [exact ZRI| exact ZFA| exact ZTL| exact R1]. }
    split.
    { enough (X : pclass_rep s m2 c0) by exact X.
      apply (pclass_rep_frameQ_ag s (mch :: XC) XB m0 m2 (outside W) AG WQ c0 Hc0); [| exact R2].
      intros y Hy. apply Z_T; unfold a_cache, OT_CACHE, PCLASS_SIZE, kNumClasses in *; fold T in Hy; clear - Hy Hc0; try acb; lia. }
    split.
    { enough (X : region_shadow_rep s m2 c0) by exact X.
      apply (region_shadow_rep_frameQ_ag s (mch :: XC) XB m0 m2 (outside W) AG WQ c0 Hc0); [exact ZFCS| | | exact R3].
      - intros y Hy. apply (Z_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8)); try assumption.
        + clear - T1' B; try acb. lia.
        + clear - T4' T5'; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in T2'. clear - T2' T4' T5' B; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in T2'. clear - T1' T2' T4' T5' N1; try acb. Z.div_mod_to_equations. lia.
      - intros y Hy. apply (Z_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8)); try assumption.
        + clear - F1 B; try acb. lia.
        + clear - F4 F5; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in F2. clear - F2 F4 F5 B; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in F2. clear - F1 F2 F4 F5 N1; try acb. Z.div_mod_to_equations. lia. }
    enough (X : region_junk_rep s m2 c0) by exact X.
    apply (region_junk_rep_frame_ag s m0 m2 (outside W) AG c0 Hc0); [exact ZFC| exact R4].
  Qed.
  (* [comment removed for export] *)
  Theorem arepq_after_rs : AREPQ s2 XC XB m2.
  Proof.
    destruct statics_after as (I1 & I2 & I3 & I4). destruct batches_after as [B1' B2'].
    split; [exact placed_after|]. split; [exact WQ2|].
    split; [exact I1|]. split; [exact I2|]. split; [exact thread_after|]. split; [exact I4|]. split; [exact I3|].
    split; [exact regions_after|]. split; [exact chunks_after|]. exact (conj B1' B2').
  Qed.

  (* [comment removed for export] *)
  Lemma flagsx_after_rs : flagsx_rep m0 -> flagsx_rep m2.
  Proof.
    intros (X1 & X2 & [g X3] & X4 & [b X5]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
    split; [trw X1 Z_lo Hz; clear - Hz; unfold AIMG_TOP, AINST in *; lia|].
    split; [trw X2 Z_lo Hz; clear - Hz; unfold AIMG_TOP, AINST in *; lia|].
    split; [exists g; trw X3 Z_lo Hz; clear - Hz; unfold AIMG_TOP, AINST in *; lia|].
    split; [trw X4 Z_lo Hz; clear - Hz; unfold AIMG_TOP, AINST in *; lia|].
    exists b; trw X5 Z_lo Hz; clear - Hz; unfold AIMG_TOP, AINST in *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma awin_after_rs :
    (forall x : word, in_rangesb x (a_S s) = true -> in_rangesb x (a_L s) = true) ->
    (forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false) ->
    awin_vis s m0 -> awin_vis s2 m2.
  Proof.
    intros SL NL AWV x Hx. change (a_S s2) with (a_S s) in Hx. apply (WMO x); [| exact (AWV x Hx)].
    cbn. split; [| exact I]. intros R. pose proof (SL x Hx) as E. rewrite (NL x R) in E. discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma avis_after_rs : avis s s2 m0 m2.
  Proof.
    apply (avis_of_wmono_out s s2 [(a, a + msz)] m0 m2 WMO).
    intros iv y [<-|[]] Hy. cbn [fst snd] in Hy. exists h. split; [exact HIN|]. split; [| left; exact Hy].
    intros Hin. change (as_sec (a_st s2)) with l1 in Hin. exact (proj2 (proj1 (L1IN h) Hin) eq_refl).
  Qed.
  Lemma acompl_after_rs : acompl s s2 d lo spv m0 m2.
  Proof.
    apply (acompl_of_munch s s2 d lo spv W m0 m2 MU). pose proof BND as B.
    placed. pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _). fold lst in L4.
    intros iv y Hiv Hy. unfold W, rs_W in Hiv. rewrite SPE in Hiv. unfold awrit, astatw.
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Hy.
    - left. exact Hy.
    - do 6 right. left. left. unfold AINST. clear - Hy. lia.
    - do 4 right. left. change (a_pa s) with pa. unfold kPtrArrayReserve. clear - Hy B; try acb. lia.
    - do 5 right. left. exists h. split; [left; exact HIN|]. left. exact Hy.
    - do 5 right. left. exists lsth. split; [left; exact LIN|]. left. fold lst. unfold kPageSize in L4. clear - Hy L4; try acb. lia.
    - do 5 right. left. exists h. split; [left; exact HIN|]. right. exact Hy.
    - right. left. change (a_thr s) with T. unfold kPageSize. clear - Hy. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_SHsp : forall X k y, sb <= X -> X + k <= sb + kSpaceSize + kPageSize -> sh X <= y < sh X + k / 8 -> outside W y.
  Proof.
    intros X k y H1 H2 Hy. pose proof BND as B. destruct PNEW as (N1 & _). unfold disj in N1.
    assert (SS : sh X + k / 8 <= sh a \/ sh a + msz / 8 <= sh X)
      by (unfold sh, kSpaceSize, kPageSize in *; clear - H1 H2 N1 Hy; Z.div_mod_to_equations; lia).
    assert (SR : 0x7fff8000 <= sh X /\ sh X + k / 8 <= sh aceil)
      by (unfold sh, ASHADOW_BASE, kSpaceSize, kPageSize in *; clear - H1 H2 B Hy; try acb; Z.div_mod_to_equations; lia).
    bands_as (BT & _ & BP & BN & BS & BA & _ & _ & BL). clear - Hy B SS SR BT BP BN BS BA BL SPE; try acb. subst T pa. unfold AINST in *. wsplit; (first [clear - ACEILB SR B Hy BP BA BL SS BT; tlia | tlia]).
  Qed.
  Lemma pendz_after_rs : agree_on (pendz st XB) m0 m2.
  Proof.
    intros y (x & Hx & R) Hr. apply AG; [| exact Hr].
    pose proof (WFQ_xb st _ _ x WQ Hx) as CV. unfold xb_ok in CV.
    pose proof (carved_in_spaceQ s _ _ OKQ _ _ CV) as (P1 & P2 & P3). change (a_sb s) with sb in P1, P2.
    destruct R as [R|R].
    - apply Z_SB. unfold kSpaceSize, kPageSize in *. clear - R P1 P2; lia.
    - apply (Z_SHsp x (class_size (class_of_addr st x))); unfold kSpaceSize, kPageSize in *; clear - R P1 P2; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma DEPOT_transport_ag : forall (P : Z -> Prop) d0 m m', DEPOT asegs d0 m -> agree_on P m m' ->
    (forall y, 7915480 <= y < 12109808 \/ 7849928 <= y < 7849956 \/ d_nb d0 <= y < d_nb d0 + 16 * 65536 \/ d_sb d0 <= y < d_sb d0 + 8 * 131072 -> P y) ->
    DEPOT asegs d0 m'.
  Proof.
    intros P d0 m m' [WF DM] AGP HP. split; [exact WF|].
    pose proof (wf_ids d0 WF) as I1. pose proof (wf_frames d0 WF) as I2.
    destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
    constructor.
    - intros b Hb. eapply (rw_cells_transport_ag P m m' AGP); [exact (T1 b Hb)|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hb Hy. lia.
    - eapply (rw_cells_transport_ag P m m' AGP); [exact T2|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hy. lia.
    - eapply (rw_cells_transport_ag P m m' AGP); [exact T3|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hy. lia.
    - intros id Hid. eapply (rw_cells_transport_ag P m m' AGP); [exact (T4 id Hid)|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hid Hy I1. lia.
    - intros id Hid. destruct (T5 id Hid) as [sid H5]. exists sid. eapply (rw_cells_transport_ag P m m' AGP); [exact H5|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hid Hy I1. lia.
    - intros id Hid. destruct (T6 id Hid) as (j1 & j2 & j3 & H6). exists j1, j2, j3. eapply (rw_cells_transport_ag P m m' AGP); [exact H6|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hid Hy I1. lia.
    - eapply (rw_cells_transport_ag P m m' AGP); [exact T7|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hy. lia.
    - eapply (rw_cells_transport_ag P m m' AGP); [exact T8|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hy. lia.
    - eapply (rw_cells_transport_ag P m m' AGP); [exact T9|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros y Hy. apply HP. clear - Hy. lia.
    - destruct T10 as (junk & U10 & L10). exists junk. split; [| exact L10]. eapply (u8arr_transport_ag P m m' AGP); [exact U10|].
      intros y Hy. apply HP. clear - Hy I2 L10. lia.
  Qed.
  Lemma Z_depot : forall y,
    7915480 <= y < 12109808 \/ 7849928 <= y < 7849956 \/ d_nb d <= y < d_nb d + 16 * 65536 \/ d_sb d <= y < d_sb d + 8 * 131072 -> outside W y.
  Proof.
    intros y Hy. pose proof BND as B. placed. pose proof (SECP lsth LIN) as (_ & _ & _ & L4 & _). fold lst in L4.
    destruct DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). fold T in G1, G2. fold pa in G7, G8.
    destruct (G9 h HIN) as [E1 E2]. destruct (G9 lsth LIN) as [E3 E4]. fold a msz in E1, E2. fold lst in E3, E4.
    bands_as (BT & _ & BP & BN & BS & BA & _ & _ & BL).
    clear - Hy B L4 G1 G2 G7 G8 E1 E2 E3 E4 BT BN BS SPE; try acb. subst T pa. unfold disj, kPageSize, kPtrArrayReserve, AINST in *.
    (* [comment removed for export] *)
    destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    - clear - Hy B BT SPE. wsplit; tlia.
    - clear - Hy B BT SPE. wsplit; tlia.
    - wsplit; [clear - Hy B| clear - Hy B| clear - Hy G7 B| clear - Hy E1| clear - Hy E3 L4| clear - Hy BN B ACEILB| clear - Hy G1]; lia.
    - wsplit; [clear - Hy B| clear - Hy B| clear - Hy G8 B| clear - Hy E2| clear - Hy E4 L4| clear - Hy BS B ACEILB| clear - Hy G2]; lia.
  Qed.
  Lemma depot_after_rs : DEPOT asegs d m0 -> DEPOT asegs d m2.
  Proof. intros DEP. exact (DEPOT_transport_ag (outside W) d m0 m2 DEP AG Z_depot). Qed.

  (* [comment removed for export] *)
  Lemma rs_l1in : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
  Proof. exact L1IN. Qed.

End RSPost.
