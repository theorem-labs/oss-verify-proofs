(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsDepotInv
     AW_AllocBase AW_MallocBase AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc2 AW_AllocSec2 AG_LargeModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma u8arr_app2 : forall mm A l1 l2, u8arr asegs mm A (l1 ++ l2) <-> u8arr asegs mm A l1 /\ u8arr asegs mm (A + Z.of_nat (length l1)) l2.
Proof.
  intros mm A l1 l2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add. rewrite wr_at_app by lia. tauto.
Qed.
End HCW.

Section ArepAfterLarge.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m0 m2 : mem) (a size lo spv : Z) (d : depot) (L2 : list (word * word)) (AL2 b1 id : Z) (LB : list (Z * Z)).
  Let st := a_st s.
  Let T := a_thr s.
  Let sb := a_sb s.
  Let pa := a_pa s.
  Let r := compute_req size.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let nres' := large_nres st.
  Let st2 := large_state st a size.
  Let ch := large_chunk a size.
  Let U := a + kPageSize + 2048.
  Let Wsh : word * word := (wz (sh a), wz (msz / 8)).
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 (Wsh :: a_S s) (a_Zr s) AL2 (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let W : list ivl := (lo, spv) :: (T + 3168, T + 3169) :: (a, a + msz) :: (sh a, sh a + msz / 8) :: (pa + 8 * nch, pa + 8 * (nres + 16384))
                      :: (AINST + 112, AINST + 728) :: (T + 2800, T + 3168) :: depot_W d.

  Hypothesis HR : ARHEAP s LB m0.
  Hypothesis DPL : depot_placed s d.
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis LO : aceil <= lo.
  (* [comment removed for export] *)
  Hypothesis PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz (a_ctx s) 160
                    /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 131072)
                    /\ (forall sc, In sc (as_sec st) -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
  Hypothesis NSEC : nch = nres -> nres = 0.
  Hypothesis AG : agree_on (outside W) m0 m2.
  Hypothesis WM : wmono asegs m0 m2.
  Hypothesis MI2 : mem_inv asegs m2.
  (* [comment removed for export] *)
  Hypothesis INST2 : rw_cells asegs m2 (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES2 : rw_cells asegs m2 (AINST + 112) [C8 (wz nres'); C8 (wz (nch + 1)); C8 (wz 0)].
  Hypothesis SST2 : stk asegs m2 (AINST + 136) (AINST + 680).
  Hypothesis MTX2 : rw_cells asegs m2 (AINST + 680) [C8 (wz 0)].
  Hypothesis GST2 : stk asegs m2 (AINST + 688) (AINST + 728).
  Hypothesis PA2 : u64arr asegs m2 pa (wlist (map sc_map_beg (as_sec st) ++ [a])).
  Hypothesis PAJ2 : stk asegs m2 (pa + 8 * (nch + 1)) (pa + 8 * nres').
  Hypothesis LHDR2 : rw_cells asegs m2 a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)].
  Hypothesis LHJ2 : stk asegs m2 (a + 32) (a + 4096).
  Hypothesis CH2 : rw_cells asegs m2 (a + 6128) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)].
  Hypothesis B1 : b1_ok b1.
  Hypothesis MAG2 : rw_cells asegs m2 (a + 4096) [C8 (wz kAllocBegMagic); C8 (wz (a + 6128))].
  Hypothesis MAGJ2 : stk asegs m2 (a + 4112) (a + 6128).
  Hypothesis FILL2 : u8arr asegs m2 (a + 6144) (repeat (b8 0xbe) 4096).
  Hypothesis SLK2 : stk asegs m2 (a + 6144 + 4096) (a + msz).
  Hypothesis SHA2 : u8arr asegs m2 (sh a) (repeat (b8 0xfa) 512).
  Hypothesis SHU2 : u8arr asegs m2 (sh (a + 4096)) (sec_shadow size msz).
  Hypothesis TST2 : stk asegs m2 (T + 2800) (T + 3168).
  Hypothesis UNW2 : rw_cells asegs m2 (T + 3168) [C1 (b8 0)].

  Let R0 : AREP s m0. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R0). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. pose proof (proj1 AR) as X. clear - X. aunf. lia. Qed.   (* [comment removed for export] *)
  Let RQ := large_req size SZ.
  Let GEO : size + 8 <= needed - 4088 /\ needed <= size + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof.
    apply (large_geo st a size SZ). destruct AR as (_ & _ & AL). unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. exact AL.
  Qed.
  Let AL' : Z.land a (kPageSize - 1) = 0.
  Proof. destruct AR as (_ & _ & AL). unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. exact AL. Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 12599296 <= a_ctx s /\ a_ctx s + 160 <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 12599296 <= a /\ a + msz <= aceil /\ 73728 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= (sh aceil)
            /\ 0 <= nch <= nres /\ nres <= 16384 /\ nch + 1 <= nres' <= 32768 /\ 12599296 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil.
  Proof.
    placed. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4). destruct AR as (A1 & A2 & A3). pose proof GEO as (G1 & G2 & G3 & G4 & _).
    destruct WFs as (_ & _ & _ & _ & _ & _ & Wn & Wr & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia]. apply aapp_env in X2; [| clear; lia].
    apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia]. apply aapp_env in F1; [| unfold AFS_SIZE; clear; lia].
    pose proof (aapp_sh_env_div _ _ A1 ltac:(clear - G1 G3 SZ; lia)) as ASH. apply aapp_env in A1; [| clear - G1 G3 SZ; lia].
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve, kChunksBlockCount in *.
    subst T sb pa nch nres nres'. unfold a_sb, large_nres in *. unfold st in *.
    assert (NN : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
    repeat split; try (first [clear - LO SZ T2 T3 S2 S3 X2 X3 P2 P3 N1 N2 N3 N4 A1 A2 GEO ASH NN Wn Wr F1 F2; (first [clear - LO T2 S2 S3 X2 P2 N1 N3 A1 SZ GEO ASH NN Wn Wr F1; (lia_guard; lia) | lia]) | (lia_guard; (lia_guard; lia))]); try (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    - destruct (Z.eqb_spec (zlen (as_sec (a_st s))) (as_n_reserved (a_st s))) as [E|NE]; unfold kChunksBlockCount; (first [clear - E SZ NE Wn; lia | (first [clear - E SZ NE Wn; lia | (first [clear - Wn NE; lia | lia])])]).
    - destruct (Z.eqb_spec (zlen (as_sec (a_st s))) (as_n_reserved (a_st s))) as [E|NE]; unfold kChunksBlockCount; [pose proof (NSEC E)|]; (first [clear - H SZ Wr; lia | (first [clear - NSEC Wn Wr; lia | lia])]).
  Qed.
  Let BANDS : hidden ((T + 4096 <= 65536 \/ (12599296 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (a_ctx s + 160 <= 2147446784 \/ 17594333495296 <= a_ctx s)
                   /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)
                   /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                   /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                   /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)).
  Proof.
    placed. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & N3 & _). destruct AR as (A1 & _). pose proof GEO as (G1 & _ & G3 & _).
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
    split; [exact (aapp_lit _ _ N1)|]. split; [exact (aapp_lit _ _ N3)|]. split; [exact (aapp_lit _ _ A1)|].
    split; [exact (aapp_sh_lit_div _ _ A1 ltac:(clear - G1 G3 SZ; lia))| exact (aapp_lit _ _ F1)].
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  (* [comment removed for export] *)
  Let BELOW : forall h, In h (as_sec st) -> sc_map_beg h <= a + kPageSize -> sc_map_beg h < a.
  Proof.
    intros h Hh Hle. placed. destruct PNEW as (_ & _ & _ & _ & _ & _ & _ & PS). pose proof (PS h Hh) as D. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _).
    pose proof BND as B. unfold disj, kPageSize in *. clear - Hle D Q4 B; try acb. lia.
  Qed.
  Let SBX : a + msz <= as_space_beg st \/ as_space_beg st + kSpaceSize <= a.
  Proof. destruct PNEW as (D & _). unfold disj in D. subst sb. unfold a_sb, kPageSize in D. unfold st. clear - D; try acb. lia. Qed.
  Let WF2 : WF st2.
  Proof. refine (WF_large st a size WFs SZ AL' _ SBX BELOW NSEC). pose proof BND as B. clear - B; try acb. lia. Qed.
  Let PL2 : placed_ok s2.
  Proof.
    placed. destruct PNEW as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). destruct AR as (A1 & A2 & A3). pose proof BND as B.
    unfold placed_ok. change (a_sb s2) with sb. change (a_pa s2) with pa. change (a_thr s2) with T. change (a_ctx s2) with (a_ctx s).
    change (a_fsb s2) with (a_fsb s). change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s).
    change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]).
    refine (conj S1 (conj S2 (conj S3 (conj P1 (conj P2 (conj P3 (conj T1 (conj T2 (conj T3 (conj X1 (conj X2 (conj X3 (conj D1 (conj D2 (conj D3 (conj D4 (conj D5
            (conj F1 (conj F2 (conj D6 (conj D7 (conj D8 (conj D9 (conj _ (conj _ TCX))))))))))))))))))))))))).
    - intros sc Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (SEC sc Hin)|].
      cbn [sc_map_beg sc_map_size].
      refine (conj _ (conj _ (conj _ (conj _ (conj N1 (conj N2 (conj N3 (conj N4 N5)))))))); unfold kPageSize, AHI_LO; try (acb); first [exact A1 | clear - A3 B; try acb; lia].
    - intros sc sc' Hin Hin' NE. apply in_app_iff in Hin. apply in_app_iff in Hin'.
      destruct Hin as [Hin|[<-|[]]]; destruct Hin' as [Hin'|[<-|[]]]; cbn [sc_map_beg sc_map_size] in *.
      + exact (SEC2 sc sc' Hin Hin' NE).
      + pose proof (N8 sc Hin) as D. clear - D; try acb. unfold disj in *. lia.
      + pose proof (N8 sc' Hin') as D. clear - D; try acb. unfold disj in *. lia.
      + exfalso. exact (NE eq_refl).
  Qed.
  Let OK2 : ast_ok s2. Proof. split; [exact PL2| exact WF2]. Qed.
  Let DPL2 : depot_placed s2 d.
  Proof.
    destruct DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10). destruct PNEW as (_ & _ & _ & _ & _ & N6 & N7 & _).
    unfold depot_placed. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]).
    refine (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj _ G10))))))))).
    intros sc Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (G9 sc Hin)|]. cbn [sc_map_beg sc_map_size]. exact (conj N6 N7).
  Qed.

  (* [comment removed for export] *)
  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact WFs. Qed.
  Let UPOS : 0 < U. Proof. pose proof BND as B. subst U. unfold kPageSize. clear - B; try acb. lia. Qed.
  Let FRESH : PositiveMap.find (ckey U) (as_chunks st) = None.
  Proof. refine (large_fresh st a size WFs SZ AL' _ SBX BELOW). pose proof BND as B; clear - B; try acb; lia. Qed.
  Let PERM : Permutation (chunk_list st2) (ch :: chunk_list st).
  Proof. exact (chunk_list_upd_perm (large_base st a size) ch KEYS UPOS FRESH). Qed.
  Let INl : forall x, In x (chunk_list st2) <-> x = ch \/ In x (chunk_list st).
  Proof. refine (lg_chunks st a size WFs SZ AL' _ SBX BELOW). pose proof BND as B; clear - B; try acb; lia. Qed.
  Let CHIN : In ch (chunk_list st2). Proof. apply INl. left. reflexivity. Qed.
  Let CHNOT : ~ In ch (chunk_list st).
  Proof. intros Hin. apply (chunk_list_find st ch KEYS) in Hin. cbn [ch_user_beg ch large_chunk] in Hin. fold U in Hin. rewrite FRESH in Hin. discriminate. Qed.
  Let PRIMch : ch_primary ch = false. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Let EXT : ch_lo ch = a /\ ch_end ch = a + msz /\ ch_user_beg ch = U /\ ch_alloc_beg ch = a + kPageSize /\ ch_used ch = size /\ ch_rz ch = 2048 /\ ch_state ch = CAllocated.
  Proof.
    unfold ch_lo, ch_end. rewrite PRIMch. cbn [ch_alloc_beg ch_class ch_user_beg ch_used ch_rz ch_state ch large_chunk].
    fold r. fold needed. subst msz U needed r. unfold kPageSize. repeat split; lia.
  Qed.

  Ltac wsplit := unfold W; cbn [outside depot_W app]; repeat split; try exact I.

  (* [comment removed for export] *)
  Lemma Z_static : forall x, astatic x -> ~ (AINST + 112 <= x < AINST + 728) -> outside W x.
  Proof.
    intros x Hx Hn. pose proof BND as B. bands_as (BT & _). clear - Hx Hn B BT; try acb. unfold astatic in Hx.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP in *.
    wsplit; (first [clear - Hx Hn B BT; lia | lia]).
  Qed.
  Lemma Z_flags : forall x, aflags_range x -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. bands_as (BT & _). clear - Hx B BT; try acb. unfold aflags_range in Hx.
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP, AINST in *.
    wsplit; (first [clear - B Hx BT; lia | lia]).
  Qed.
  Lemma Z_T : forall x, T <= x < T + 2800 -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct DPL as (E1 & E2 & _). destruct PNEW as (_ & _ & N3 & _).
    bands_as (BT & _). clear - Hx B D2 D4 E1 E2 N3 BT; try acb. subst T pa. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - Hx B ACEILB N3 BT D4 E1 E2; lia | lia]).
  Qed.
  Lemma Z_CTX : forall x, a_ctx s + 8 <= x < a_ctx s + 160 -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct DPL as (_ & _ & _ & _ & E1 & E2 & _). destruct PNEW as (_ & _ & _ & N4 & _).
    bands_as (_ & BC & _). clear - Hx B D5 TCX E1 E2 N4 BC; try acb. subst T pa. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - Hx B ACEILB TCX N4 BC D5 E1 E2; lia | lia]).
  Qed.
  Lemma Z_SB : forall x, sb <= x < sb + kSpaceSize + kPageSize -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct DPL as (_ & _ & E1 & E2 & _). destruct PNEW as (N1 & _).
    clear - Hx B D1 D2 E1 E2 N1; try acb. subst T pa sb. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - Hx B ACEILB D2 N1 D1 E1 E2; lia | lia]).
  Qed.
  Lemma Z_PA : forall x, pa <= x < pa + 8 * nch -> outside W x.
  Proof.
    intros x Hx. pose proof BND as B. placed. destruct DPL as (_ & _ & _ & _ & _ & _ & E1 & E2 & _). destruct PNEW as (_ & N2 & _).
    bands_as (_ & _ & BP & _). clear - Hx B D4 E1 E2 N2 BP; try acb. subst T pa. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AINST in *.
    wsplit; (first [clear - Hx B ACEILB D4 N2 BP E1 E2; lia | lia]).
  Qed.
  Lemma Z_SEC : forall h x, In h (as_sec st) -> sc_map_beg h <= x < sc_map_beg h + sc_map_size h -> outside W x.
  Proof.
    intros h x Hh Hx. pose proof BND as B. placed. pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & E & _). destruct (E h Hh) as [E1 E2]. destruct PNEW as (_ & _ & _ & _ & _ & _ & _ & N8). pose proof (N8 h Hh) as D.
    pose proof (aapp_lit _ _ Q2) as Q2l. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].   (* [comment removed for export] *)
    clear - Hx B Q2 Q2l Q3 Q6 Q7 E1 E2 D; try acb. subst sb T pa. unfold a_sb, disj, kSpaceSize, kPageSize, kPtrArrayReserve, AHI_LO, AINST in *.
    acb. wsplit; (first [clear - Hx B Q3 ACEILB0 Q7 D Q2l Q6 Q2 E1 E2; lia | lia]).
  Qed.
  Lemma Z_SH : forall lo' k x, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= k -> lo' + 8 * k <= aceil ->
    (lo' + 8 * k <= a \/ a + msz <= lo') -> sh lo' <= x < sh lo' + k -> outside W x.
  Proof.
    intros lo' k x H0 H8 Hk Hhi Hd Hx. pose proof BND as B. destruct AR as (_ & _ & A3). pose proof GEO as (_ & _ & _ & _ & _ & G6 & _).
    assert (A8 : a mod 8 = 0) by (clear - A3; try acb; Z.div_mod_to_equations; lia).
    assert (M8 : 8 * (msz / 8) = msz) by (clear - G6; try acb; Z.div_mod_to_equations; lia).
    assert (SS : sh lo' + k <= sh a \/ sh a + msz / 8 <= sh lo') by (clear - H8 A8 Hk Hd B M8; try acb; apply sh_sep; try assumption; lia).
    assert (SR : 0x7fff8000 <= sh lo' /\ sh lo' + k <= 0x10007fef8000) by (clear - H0 Hk Hhi; try acb; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    bands_as (BT & _ & BP & BN & BS & BA & _). clear - Hx B SS SR BT BP BN BS BA; try acb. subst T pa. unfold AINST in *. wsplit; (first [clear - Hx B SR BT BA SS BP BN BS; lia | lia]).
  Qed.

  Ltac trw H Z Hz := eapply (rw_cells_transport_pt (outside W) m0 m2 AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map];
                  intros ? Hz; apply Z.
  Ltac trj H Z Hz := eapply (junk_transport_pt (outside W) m0 m2 AG WM); [exact H|]; intros ? Hz; apply Z.
  Ltac inst_static Hz := clear - Hz; try acb; first [unfold astatic; left; unfold OI_MISMATCH, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia
                            | unfold OI_MISMATCH, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER in *; lia].

  (* [comment removed for export] *)
  Lemma statics_after : inst_rep s2 m2 /\ flags_rep s2 m2 /\ ia_rep s2 m2 /\ sec_rep s2 m2.
  Proof.
    destruct R0 as (_ & INST & FL & _ & SEC0 & IA & _). pose proof BND as B.
    split.
    { destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & A5 & J5 & A6 & A7 & J6 & A8 & J7 & A9).
      unfold inst_rep. change (a_sb s2) with sb. change (a_ri s2) with (a_ri s). change (a_pa s2) with pa.
      change (as_n_reserved (a_st s2)) with nres'. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]).
      change (as_qmax (a_st s2)) with (as_qmax st). change (as_qmin (a_st s2)) with (as_qmin st). change (as_qcache (a_st s2)) with (as_qcache st).
      change (as_gq (a_st s2)) with (as_gq st).
      replace (zlen (as_sec st ++ [mkSC a msz needed])) with (nch + 1) by (unfold nch, zlen; rewrite length_app; cbn [length]; lia).
      split; [trw A1 Z_static Hz; inst_static Hz|].
      split; [trj J1 Z_static Hz; inst_static Hz|].
      split; [exact NRES2|].
      split; [intros _; unfold OI_SECMUTEX; replace (AINST + 136 + (680 - 136)) with (AINST + 680) by lia; exact SST2|].
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
    { apply (flags_rep_frame s2 m0 m2 (outside W) AG WM); [exact Z_flags| exact FL]. }
    split.
    { apply (ia_rep_frame s2 m0 m2 (outside W) AG WM); [| exact IA]. intros x Hx. apply Z_static; [unfold astatic; do 11 right; left; exact Hx|].
      clear - Hx; try acb. unfold AIAINST, AINST in *. lia. }
    (* [comment removed for export] *)
    destruct SEC0 as (U0 & J0 & H0). unfold sec_rep. change (a_pa s2) with pa. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]).
    change (as_n_reserved (a_st s2)) with nres'.
    replace (zlen (as_sec st ++ [mkSC a msz needed])) with (nch + 1) by (unfold nch, zlen; rewrite length_app; cbn [length]; lia).
    split; [rewrite map_app; cbn [map sc_map_beg]; exact PA2|].
    split; [intros _; replace (pa + 8 * (nch + 1) + 8 * (nres' - (nch + 1))) with (pa + 8 * nres') by lia; exact PAJ2|].
    intros i h Hi. destruct (lt_dec i (length (as_sec st))) as [LT|GE].
    - rewrite nth_error_app1 in Hi by exact LT. destruct (H0 i h Hi) as [C1 J1']. pose proof (nth_error_In _ _ Hi) as IN.
      placed. pose proof (SEC h IN) as (_ & _ & _ & Q4 & _).
      split; [trw C1 (Z_SEC h) Hz; [exact IN| clear - Hz Q4; try acb; unfold kPageSize in *; lia] | trj J1' (Z_SEC h) Hz; [exact IN| clear - Hz Q4; try acb; unfold kPageSize in *; lia]].
    - rewrite nth_error_app2 in Hi by (first [clear - GE SZ; lia | lia]). destruct (i - length (as_sec st))%nat as [|k] eqn:EK; cbn in Hi; [| destruct k; discriminate].
      injection Hi as <-. cbn [sc_map_beg sc_map_size sc_size].
      replace (Z.of_nat i) with nch by (unfold nch, zlen; (first [clear - GE EK SZ; lia | lia])).
      split; [exact LHDR2| intros _; unfold kPageSize; replace (a + 32 + (4096 - 32)) with (a + 4096) by lia; exact LHJ2].
  Qed.

  Lemma thread_after : thread_rep s2 m2.
  Proof.
    pose proof BND as B. destruct R0 as (_ & _ & _ & THR & _).
    destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_ctx s2) with (a_ctx s). change (a_thr s2) with T. change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s).
    change (a_cache s2) with (a_cache s). change (as_tq (a_st s2)) with (as_tq st).
    fold T in T1, T2c, T2d, T3, T4, J1, J3, T5. unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
    split; [trw T1 Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T2 Z_CTX Hz; clear - Hz; try acb; lia|]. split; [trw T2b Z_CTX Hz; clear - Hz; try acb; lia|].
    split; [trw T2c Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T2d Z_T Hz; clear - Hz; try acb; lia|].
    split; [trw T3 Z_T Hz; clear - Hz; try acb; lia|]. split; [trw T4 Z_T Hz; clear - Hz; try acb; lia|].
    split; [trj J1 Z_T Hz; clear - Hz; try acb; lia|].
    split; [unfold a_cache, OT_CACHE in *; fold T in J2 |- *; trj J2 Z_T Hz; clear - Hz; try acb; lia|].
    split; [intros _; replace (T + 2800 + (3168 - 2800)) with (T + 3168) by (clear; lia); exact TST2|].
    exact UNW2.
  Qed.

  (* [comment removed for export] *)
  Let SH3 : poisoned m2 (a + kPageSize) 256%nat kAsanHeapLeftRedzoneMagic
          /\ SHAD m2 U (shadow_of size)
          /\ poisoned m2 (U + round_up size 8) (Z.to_nat ((a + msz - (U + round_up size 8)) / 8)) kAsanHeapLeftRedzoneMagic
          /\ poisoned m2 a 512%nat kAsanHeapLeftRedzoneMagic.
  Proof.
    pose proof BND as B. destruct AR as (A1 & A2 & A3). pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (S0 : SHAD m2 (a + kPageSize) (sec_shadow size msz)) by (split; [unfold kPageSize; clear - B; try acb; lia| split; [unfold kPageSize; clear - A3; try acb; Z.div_mod_to_equations; lia| exact SHU2]]).
    unfold sec_shadow in S0. apply SHAD_app in S0. destruct S0 as [S1 S23]. rewrite repeat_length in S23.
    replace (a + kPageSize + 8 * Z.of_nat 256) with U in S23 by (subst U; clear; lia).
    rewrite app_assoc in S23. apply SHAD_app in S23. destruct S23 as [S2 S3].
    assert (SOF : repeat (b8 0) (Z.to_nat (size / 8)) ++ (if size mod 8 =? 0 then [] else [b8 (size mod 8)]) = shadow_of size) by reflexivity.
    rewrite SOF in S2, S3. rewrite (shadow_of_length size) in S3 by (clear - SZ; try acb; lia).
    replace (U + 8 * nsh size) with (U + round_up size 8) in S3 by (unfold nsh, round_up; clear - SZ; try acb; Z.div_mod_to_equations; lia).
    replace (msz - 6144 - round_up size 8) with (a + msz - (U + round_up size 8)) in S3 by (subst U; unfold kPageSize; clear; lia).
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [clear - B; try acb; lia|]. split; [clear - A3; try acb; Z.div_mod_to_equations; lia| exact SHA2].
  Qed.

  Lemma new_chunk_rep : chunk_rep m2 ch.
  Proof.
    pose proof BND as B. pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    destruct EXT as (E1 & E2 & E3 & E4 & E5 & E6 & E7). destruct SH3 as (S1 & S2 & S3 & S4).
    unfold chunk_rep. rewrite E2, E3, E4, E5, E6, E7. rewrite PRIMch.
    split.
    { exists b1, id. destruct B1 as [B1a B1b]. split; [| split; [exact B1a| exact B1b]].
      unfold kChunkHeaderSize. replace (U - 16) with (a + 6128) by (subst U; unfold kPageSize; clear; lia). exact CH2. }
    split.
    { right. unfold kChunkHeaderSize. replace (U - 16) with (a + 6128) by (subst U; unfold kPageSize; clear; lia). unfold kPageSize.
      split; [exact MAG2|]. intros _. replace (a + 4096 + 16 + (2048 - 32)) with (a + 6128) by (clear; lia). replace (a + 4096 + 16) with (a + 4112) by (clear; lia). exact MAGJ2. }
    split.
    { split.
      - (* [comment removed for export] *)
        destruct FILL2 as [_ WF1]. rewrite repeat_length in WF1. change (Z.of_nat 4096) with 4096 in WF1.
        destruct (stk_split asegs _ _ (U + size) _ SLK2 ltac:(hci; subst U; unfold kPageSize; clear - SZ G1 G3; try acb; lia)) as [SL _].
        destruct SL as (_ & _ & SL3).
        assert (W2 : wr_at asegs m2 (U + 4096) (size - 4096)).
        { split; [subst U; clear - B; try acb; unfold kPageSize; lia|]. split; [subst U; clear - B SZ G1 G3; try acb; unfold kPageSize; lia|].
          intros i Hi. replace (U + 4096 + i) with (a + 6144 + 4096 + (i)) by (subst U; unfold kPageSize; clear; lia).
          apply (proj1 (SL3 (a + 6144 + 4096 + i) ltac:(hci; subst U; unfold kPageSize in *; clear - Hi; try acb; lia))). }
        replace U with (a + 6144) in W2 |- * by (subst U; unfold kPageSize; clear; lia).
        pose proof (proj2 (wr_at_app asegs m2 (a + 6144) 4096 (size - 4096) ltac:(hci; clear; lia) ltac:(hci; clear - SZ; try acb; lia)) (conj WF1 W2)) as W12.
        replace (4096 + (size - 4096)) with size in W12 by (clear; lia). exact W12.
      - destruct S2 as (_ & _ & [_ WS]). rewrite shadow_of_length in WS by (clear - SZ; try acb; lia). exact WS. }
    split.
    { intros POS. destruct (stk_split asegs _ _ (U + size) _ SLK2 ltac:(hci; subst U; unfold kPageSize; clear - SZ G1 G3; try acb; lia)) as [_ SL].
      replace (U + size + (a + msz - (U + size))) with (a + msz) by (clear; lia). exact SL. }
    split; [unfold kPageSize in S1; replace (Z.to_nat (2048 / 8)) with 256%nat by reflexivity; exact S1|].
    split; [exact S3|]. replace (a + kPageSize - kPageSize) with a by (clear; lia). exact S4.
  Qed.

  (* [comment removed for export] *)
  Lemma new_block : (exists junk, rw_cells asegs m2 U [CB (Z.to_nat size) junk]) /\ addressable m2 U size.
  Proof.
    pose proof BND as B. pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct SH3 as (_ & S2 & _).
    split; [| split; [clear - SZ; try acb; lia| exact S2]].
    destruct (stk_split asegs _ _ (U + size) _ SLK2 ltac:(hci; subst U; unfold kPageSize; clear - SZ G1 G3; try acb; lia)) as [SL _].
    destruct (stk_cells _ _ _ SL ltac:(hci; subst U; unfold kPageSize; clear - SZ; try acb; lia)) as [junk J].
    assert (L : length junk = Z.to_nat (U + size - (a + 6144 + 4096))) by (destruct J as [[[L _] _] _]; exact L).
    apply u8arr_of_rw_cells in J.
    exists (repeat (b8 0xbe) 4096 ++ junk).
    assert (UJ : u8arr asegs m2 U (repeat (b8 190) 4096 ++ junk)).
    { apply (proj2 (u8arr_app2 m2 U _ _)). replace U with (a + 6144) by (subst U; unfold kPageSize; clear; lia). split; [exact FILL2|]. rewrite repeat_length. change (Z.of_nat 4096) with 4096. exact J. }
    apply rw_cells_of_u8arr in UJ. rewrite length_app, repeat_length, L in UJ.
    replace (4096 + Z.to_nat (U + size - (a + 6144 + 4096)))%nat with (Z.to_nat size) in UJ by (subst U; unfold kPageSize; clear - SZ; try acb; lia). exact UJ.
  Qed.

  (* [comment removed for export] *)
  Lemma old_chunk_rep : forall x, In x (chunk_list st) -> chunk_rep m2 x.
  Proof.
    intros x Hx. destruct R0 as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof BND as B.
    assert (Hx' : In x (chunk_list (a_st s2))) by (apply INl; right; exact Hx).
    assert (NEQ : x <> ch) by (intros ->; exact (CHNOT Hx)).
    pose proof (record_ext s2 OK2 x Hx') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    pose proof (record_vs_record s2 OK2 ch CHIN x Hx' NEQ) as D. destruct EXT as (E1 & E2 & _). rewrite E1, E2 in D. clear E1 E2.
    acb. unfold AIMG_TOP in X1.   (* [comment removed for export] *)
    apply (chunk_rep_frame s2 m0 m2 (outside W) AG WM OK2 x Hx'); [| exact (CHR x Hx)].
    (* [comment removed for export] *)
    assert (APP : forall y, ch_lo x <= y < ch_end x -> outside W y).
    { intros y Hy. destruct (ch_primary x) eqn:PX.
      - destruct (record_primary_space s2 OK2 x Hx' PX) as [P1 P2]. change (a_sb s2) with sb in P1, P2.
        apply Z_SB. unfold kSpaceSize, kPageSize in P2 |- *. clear - Hy P1 P2; try acb. lia.
      - destruct (record_secondary_map s2 OK2 x Hx' PX) as (h & Hh & M1 & M2 & _).
        change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hh. apply in_app_iff in Hh. destruct Hh as [Hh|[<-|[]]].
        + apply (Z_SEC h); [exact Hh| clear - Hy M1 M2; try acb; lia].
        + exfalso. cbn [sc_map_beg sc_map_size] in M1, M2. clear - Hy M1 M2 D X3 X6 X7 X8 X9; try acb. lia. }
    assert (SHW : forall lo' k y, ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k -> sh lo' <= y < sh lo' + k -> outside W y).
    { intros lo' k y G1 G2 G3 G4 Gy. apply (Z_SH lo' k); try assumption.
      - clear - G1 X1; try acb. lia.
      - acb. clear - G2 X2; try acb. lia.
      - clear - G1 G2 D; try acb. lia. }
    pose proof (chunk_align s2 OK2 x Hx') as (A1 & A2 & A3 & A4 & A5).
    assert (AL8 : ch_alloc_beg x mod 8 = 0 /\ ch_user_beg x mod 8 = 0 /\ 8 * (ch_rz x / 8) = ch_rz x)
      by (clear - A1 A2 A3; try acb; Z.div_mod_to_equations; lia).
    clear A1 A2 A3. destruct AL8 as (A1 & A3 & RZ8).
    assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8 /\ (round_up (ch_used x) 8) mod 8 = 0)
      by (unfold nsh, round_up; clear - X9; try acb; Z.div_mod_to_equations; lia).
    intros y Hy. destruct Hy as [Hy|[Hy|[[Q Hy]|[Hy|[Hy|[[Q Hy]|[NP Hy]]]]]]].
    - apply APP. clear - Hy X3 X6 X7 X9 NS; try acb. lia.
    - apply APP. clear - Hy X3 X6 X8 X9; try acb. lia.
    - apply APP. clear - Hy X3 X6 X7 X8 NS; try acb. lia.
    - apply (SHW (ch_alloc_beg x) (ch_rz x / 8) y); clear - Hy X3 X6 X7 X8 X9 NS A1 RZ8; try acb; lia.
    - apply (SHW (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) y);
        clear - Hy X3 X6 X7 X8 X9 NS A3 A4; try acb; try lia; Z.div_mod_to_equations; lia.
    - apply (SHW (ch_user_beg x) (nsh (ch_used x)) y); clear - Hy X3 X6 X7 X8 X9 NS A3; try acb; try lia; unfold nsh; Z.div_mod_to_equations; lia.
    - unfold ch_lo in *. rewrite NP in *. apply (SHW (ch_alloc_beg x - kPageSize) 512 y); unfold kPageSize in *; clear - Hy X3 X6 X7 X8 X9 NS A1; try acb;
        try lia; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma batches_after : batches_rep m2 (qc_list (as_tq st)) /\ batches_rep m2 (qc_list (as_gq st)).
  Proof.
    destruct R0 as (_ & _ & _ & _ & _ & _ & _ & _ & BT & BG).
    assert (BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
              0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
    { intros b Hb. pose proof (WF_batch _ b WFs Hb) as (Q1 & Q2 & _). unfold kBatchSize, kBatchCount in *. clear - Q1 Q2; try acb. lia. }
    assert (HPB : forall b y, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
              (qb_addr b <= y < qb_addr b + kBatchSize \/ sh (qb_addr b) <= y < sh (qb_addr b) + kBatchSize / 8) -> outside W y).
    { intros b y Hb Hr. pose proof (batch_in_space s2 OK2 b Hb) as (P1 & P2 & P3). change (a_sb s2) with sb in P1, P2.
      pose proof BND as B. unfold kBatchSize, kSpaceSize in *. destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1.
      destruct Hr as [Hr|Hr].
      - apply Z_SB. unfold kSpaceSize, kPageSize. clear - Hr P1 P2; try acb. lia.
      - apply (Z_SH (qb_addr b) 1024); try assumption; try (clear - Hr N1 P1 P2 B; try acb; lia).
        all: (clear - P2 B; try acb; lia). }
    split.
    - eapply (batches_rep_transport (outside W) m0 m2); [exact AG| exact WM| | | exact BT].
      + intros b y Hb Hr. apply (HPB b y); [apply in_app_iff; left; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport (outside W) m0 m2); [exact AG| exact WM| | | exact BG].
      + intros b y Hb Hr. apply (HPB b y); [apply in_app_iff; right; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Let FREE_out : forall c0 cp0 y, 0 <= c0 < kNumClasses ->
      In cp0 (rg_free_array (get_region st c0)) \/ In cp0 (pc_chunks (get_pc st c0)) ->
      compact_to_addr st c0 cp0 <= y < compact_to_addr st c0 cp0 + class_size c0 -> outside W y.
  Proof.
    intros c0 cp0 y Hc0 Hin Hy.
    pose proof (freech_in_space s2 OK2 c0 cp0 Hc0 Hin) as (P1 & P2 & P3 & P4 & P5).
    change (a_sb s2) with sb in P1, P2. change (compact_to_addr (a_st s2) c0 cp0) with (compact_to_addr st c0 cp0) in P1, P2, P3.
    apply Z_SB. unfold kSpaceSize, kPageSize in *; clear - Hy P1 P2; try acb; lia.
  Qed.
  Let FREE_sh_out : forall c0 cp0 y, 0 <= c0 < kNumClasses ->
      In cp0 (rg_free_array (get_region st c0)) \/ In cp0 (pc_chunks (get_pc st c0)) ->
      sh (compact_to_addr st c0 cp0) <= y < sh (compact_to_addr st c0 cp0) + class_size c0 / 8 -> outside W y.
  Proof.
    intros c0 cp0 y Hc0 Hin Hy. pose proof BND as B. destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1.
    pose proof (freech_in_space s2 OK2 c0 cp0 Hc0 Hin) as (P1 & P2 & P3 & P4 & P5).
    change (a_sb s2) with sb in P1, P2. change (compact_to_addr (a_st s2) c0 cp0) with (compact_to_addr st c0 cp0) in P1, P2, P3.
    assert (C8 : 8 * (class_size c0 / 8) = class_size c0) by (clear - P5; try acb; Z.div_mod_to_equations; lia).
    apply (Z_SH (compact_to_addr st c0 cp0) (class_size c0 / 8)); try assumption.
    - clear - P1 B; try acb. lia.
    - clear - P4; try acb. lia.
    - acb. unfold kSpaceSize in P2. clear - P2 B C8; try acb. lia.
    - unfold kSpaceSize in P2. clear - P1 P2 N1 C8; try acb. lia.
  Qed.

  Lemma regions_after : forall c0, 0 <= c0 < kNumClasses ->
    region_rep s2 m2 c0 /\ pclass_rep s2 m2 c0 /\ region_shadow_rep s2 m2 c0 /\ region_junk_rep s2 m2 c0.
  Proof.
    intros c0 Hc0. destruct R0 as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (RG & PC & RSH & RJ).
    pose proof BND as B. destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1.
    pose proof (farray_in_space s2 OK2 c0 Hc0) as (F1 & F2 & F3 & F4 & F5).
    change (a_sb s2) with sb in F1, F2. change (FA s2 c0) with (FA s c0) in F1, F2, F3.
    change (get_region (a_st s2) c0) with (get_region st c0) in F2, F4, F5.
    pose proof (tail_in_space s2 OK2 c0 Hc0) as (T1' & T2' & T3' & T4' & T5').
    change (a_sb s2) with sb in T1', T2'. change (RB s2 c0) with (RB s c0) in T1', T2', T3'.
    change (get_region (a_st s2) c0) with (get_region st c0) in T1', T2', T3', T4', T5'.
    split.
    { apply (region_rep_frame s2 m0 m2 (outside W) AG WM OK2 c0 Hc0); [ | | | exact RG].
      - intros y Hy. change (a_ri s2) with (a_ri s) in Hy. unfold a_ri in Hy. fold sb in Hy.
        apply Z_SB; unfold kSpaceSize, kPageSize in *; clear - Hy B; try acb; lia.
      - intros y Hy. change (FA s2 c0) with (FA s c0) in Hy. change (get_region (a_st s2) c0) with (get_region st c0) in Hy.
        apply Z_SB; unfold kSpaceSize, kPageSize in *; clear - Hy F1 F2; try acb; lia.
      - intros y Hy. change (RB s2 c0) with (RB s c0) in Hy. change (get_region (a_st s2) c0) with (get_region st c0) in Hy.
        apply Z_SB; unfold kSpaceSize, kPageSize in *; clear - Hy T1' T2'; try acb; lia. }
    split.
    { unfold pclass_rep. change (a_st s2) with st2. change (get_pc st2 c0) with (get_pc st c0).
      change (as_cache_inited st2) with (as_cache_inited st). change (a_cache s2) with (a_cache s).
      apply (pclass_rep_frame s m0 m2 (outside W) AG WM OK c0 Hc0); [| exact PC].
      intros y Hy. apply Z_T. unfold a_cache, OT_CACHE, PCLASS_SIZE, kNumClasses in *. fold T in Hy. clear - Hy Hc0; try acb. lia. }
    split.
    { apply (region_shadow_rep_frame s2 m0 m2 (outside W) AG WM OK2 c0 Hc0).
      - intros cp0 y Hin Hy. exact (FREE_sh_out c0 cp0 y Hc0 Hin Hy).
      - intros y Hy. change (RB s2 c0) with (RB s c0) in Hy. change (get_region (a_st s2) c0) with (get_region st c0) in Hy.
        apply (Z_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8)); try assumption.
        + clear - T1' B; try acb. lia.
        + clear - T4' T5'; try acb. Z.div_mod_to_equations. lia.
        + acb. unfold kSpaceSize in T2'. clear - T2' T4' T5' B; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in T2'. clear - T1' T2' T4' T5' N1; try acb. Z.div_mod_to_equations. lia.
      - intros y Hy. change (FA s2 c0) with (FA s c0) in Hy. change (get_region (a_st s2) c0) with (get_region st c0) in Hy.
        apply (Z_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8)); try assumption.
        + clear - F1 B; try acb. lia.
        + clear - F4 F5; try acb. Z.div_mod_to_equations. lia.
        + acb. unfold kSpaceSize in F2. clear - F2 F4 F5 B; try acb. Z.div_mod_to_equations. lia.
        + unfold kSpaceSize in F2. clear - F1 F2 F4 F5 N1; try acb. Z.div_mod_to_equations. lia.
      - unfold region_shadow_rep in RSH |- *. exact RSH. }
    apply (region_junk_rep_frame s2 m0 m2 (outside W) AG WM c0 Hc0).
    - intros cp0 y Hin Hy. exact (FREE_out c0 cp0 y Hc0 Hin Hy).
    - exact RJ.
  Qed.

  (* [comment removed for export] *)
  Lemma arep_after : AREP s2 m2.
  Proof.
    destruct statics_after as (I1 & I2 & I3 & I4). destruct batches_after as [B1' B2'].
    split; [exact OK2|]. split; [exact I1|]. split; [exact I2|]. split; [exact thread_after|]. split; [exact I4|]. split; [exact I3|].
    split; [exact regions_after|].
    split.
    { intros x Hx. change (a_st s2) with st2 in Hx. apply INl in Hx. destruct Hx as [->|Hx]; [exact new_chunk_rep| exact (old_chunk_rep x Hx)]. }
    exact (conj B1' B2').
  Qed.

  Lemma depot_placed_after : depot_placed s2 d. Proof. exact DPL2. Qed.
  Lemma placed_after : placed_ok s2 /\ WF st2. Proof. exact OK2. Qed.

  Lemma arheap_after : ARHEAP s2 ((U, size) :: LB) m2.
  Proof.
    destruct HR as (_ & ND & LBs). destruct EXT as (_ & _ & E3 & _ & E5 & _ & E7).
    assert (AL : forall b, In b (alb s2) <-> b = (U, size) \/ In b (alb s)).
    { intros b. unfold alb. change (a_st s2) with st2. rewrite !in_map_iff. split.
      - intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply INl in Hx. destruct Hx as [->|Hx].
        + left. rewrite <- E, E3, E5. reflexivity.
        + right. exists x. split; [exact E|]. apply filter_In. split; [exact Hx| exact AX].
      - intros [->|(x & E & Hx)].
        + exists ch. split; [rewrite E3, E5; reflexivity|]. apply filter_In. split; [exact CHIN| unfold is_alloc; rewrite E7; reflexivity].
        + apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [apply INl; right; exact Hx| exact AX]. }
    split; [exact arep_after|]. split.
    - constructor; [| exact ND]. intros Hin. apply LBs in Hin. destruct (alb_In s U size Hin) as (x & Hx & _ & EU & _).
      apply (chunk_list_find st x KEYS) in Hx. rewrite EU in Hx. rewrite FRESH in Hx. discriminate.
    - intros b. rewrite AL. cbn [In]. rewrite LBs. split; intros [H|H]; [left; symmetry; exact H| right; exact H| left; symmetry; exact H| right; exact H].
  Qed.
End ArepAfterLarge.

