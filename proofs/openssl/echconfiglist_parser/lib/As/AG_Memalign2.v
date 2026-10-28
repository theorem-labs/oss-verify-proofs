(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2
     AsDepotInv AsDepotHash AsUnwind CidBits AW_AllocBase AW_MallocBase AW_Malloc AW_AllocBaseAl AW_Memalign AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).


Section MemalignHit.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).

  (* [comment removed for export] *)
  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let rz := rz_size size.
  Let needed := round_up (Z.max size 8) 8 + rz.
  Let c := class_id needed.
  Let csz := class_size c.
  Let csz8 := csz / 8.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let pc := get_pc st c.
  Let cnt := pc_count pc.
  Let chunks := pc_chunks pc.
  Let cp := hd 0 chunks.
  Let AB := compact_to_addr st c cp.
  Let U := AB + rz.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1c4c70 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let n := Z.of_nat (length T).
  Let id := d_putid d (depot_hash T).
  Let d' := d_put d (depot_hash T) n.
  Let W : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: depot_W d.
  (* [comment removed for export] *)
  Let ch := mkChunk AB U (rq_size (compute_req size)) rz c CAllocated.
  Let st' := hit_state st c cnt (tl chunks) ch.
  Let s' := mkAst st' (a_thr s) (a_ctx s) (a_fsb s) (a_L s) (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2544 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis HIT : cnt <> 0.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.

  (* [comment removed for export] *)
  Let RQ : rq_rz (compute_req size) = rz /\ rq_needed (compute_req size) = needed /\ rq_primary (compute_req size) = true
           /\ rq_size (compute_req size) = size /\ 16 <= rz <= 2048 /\ size + rz <= needed /\ needed < size + rz + 8 /\ 8 + rz <= needed.
  Proof.
    pose proof (rz_size_facts size) as (RZ & _). unfold compute_req. replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.ltb Z.eqb].
    replace (round_up (Z.max size 8) 8 + rz_size size <=? kMaxSize) with true by (symmetry; apply Z.leb_le; subst needed rz; lia).
    subst needed rz. unfold round_up. repeat split; try reflexivity; Z.div_mod_to_equations; (first [clear - RZ H H0 SZ; lia | lia]).
  Qed.
  Let HC : 1 <= c < 32.
  Proof. subst c. apply class_id_range. destruct RQ as (_ & _ & _ & _ & A & B & _). unfold kMaxSize in SZ. lia. Qed.
  Let CSZ : 32 <= csz <= 65536 /\ needed <= csz /\ csz mod 32 = 0 /\ 8 * csz8 = csz.
  Proof.
    pose proof (class_size_table_facts c ltac:(hci; lia)) as (T1 & T2 & T3 & _). subst csz8 csz.
    pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; destruct RQ as (_ & _ & _ & _ & A & B & _); lia)). subst c.
    repeat split; try (first [clear - T3 HC T1 H T2; lia | lia]); Z.div_mod_to_equations; lia.
  Qed.


  (* [comment removed for export] *)
  Let CO : cache_ok st c. Proof. apply WF_cache; [exact WFs| unfold kNumClasses; lia]. Qed.
  Let PCS : pc_chunks (get_pc st c) = cp :: tl chunks.
  Proof.
    unfold cp, chunks, pc. destruct (pc_chunks (get_pc st c)) as [|x l] eqn:E; [exfalso | reflexivity].
    apply HIT. unfold cnt, pc. rewrite (co_count _ _ CO), E. reflexivity.
  Qed.
  Let CV : carved st c AB.
  Proof. apply carved_cache; [exact WFs| unfold kNumClasses; lia| rewrite PCS; left; reflexivity]. Qed.
  Let ABE : AB = sb + c * 2^32 + cp * 16.
  Proof. subst AB sb. rewrite compact_to_addr_eq, region_beg_eq. reflexivity. Qed.
  Let PLF : sb mod 65536 = 0 /\ AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil
         /\ a_pa s mod kPageSize = 0 /\ aapp (a_pa s) kPtrArrayReserve /\ a_pa s + kPtrArrayReserve <= aceil
         /\ TH mod kPageSize = 0 /\ akobj TH kPageSize /\ TH + kPageSize <= aceil
         /\ a_ctx s mod 8 = 0 /\ aapp (a_ctx s) 160 /\ a_ctx s + 160 <= aceil
         /\ disj sb (kSpaceSize + kPageSize) (a_pa s) kPtrArrayReserve
         /\ disj sb (kSpaceSize + kPageSize) TH kPageSize /\ disj sb (kSpaceSize + kPageSize) (a_ctx s) 160
         /\ disj (a_pa s) kPtrArrayReserve TH kPageSize /\ disj (a_pa s) kPtrArrayReserve (a_ctx s) 160
         /\ (disj TH kPageSize (a_ctx s) 160 /\ kPageSize <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s).
  Proof.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    subst sb TH. unfold a_sb. repeat split; assumption || (destruct TCX as (A & B & C); first [exact A| lia]).
  Qed.
  Let RNG : sb <= AB /\ AB + csz <= sb + kSpaceSize /\ AB mod 8 = 0 /\ 0 <= cp * 16 /\ cp * 16 + csz <= 2^32.
  Proof.
    pose proof (carved_in_space s OK c AB CV) as (A & B & _). pose proof (carved_range st c AB WFs CV) as (C1 & C2 & _).
    rewrite region_beg_eq in C1, C2. destruct PLF as (S1 & _).
    subst csz sb. unfold a_sb in *. unfold st in *. rewrite ABE in *. unfold kFreeArrayOffset in *.
    clear - A B C1 C2 S1; try acb. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 0x10007fff8000 <= sb
            /\ sb + 137438953472 + 4096 <= aceil /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 32 <= csz /\ 8 * csz8 = csz
            /\ 12386304 <= a_ctx s /\ a_ctx s + 160 <= aceil /\ 12386304 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12386304 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12386304 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 1 <= c < 32 /\ P = TH + 208 + 80 * c /\ CA = TH + 208
            /\ 0x2008fff7000 <= sh AB /\ sh AB + csz8 <= 0x10007fff8000.
  Proof.
    destruct PLF as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _).
    destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
    destruct RNG as (R1 & R2 & _). destruct CSZ as (C1 & C2 & C3 & C4).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    apply aapp_env in X2; [| clear; lia]. apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia].
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *.
    subst P CA. repeat split; try (lia_guard; first [clear - LO T2 S2 S3 R1 R2 C1 C4 X2 P2 N1 N3 HC; lia | (lia_guard; lia)]); unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; (first [clear - H0 H R1 S2 ACEILB R2 S3; lia | lia]).
  Qed.
  (* [comment removed for export] *)
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (12386304 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (a_ctx s + 160 <= 2147446784 \/ 17594333495296 <= a_ctx s)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d)).
  Proof.
    destruct PLF as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _).
    destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & N3 & _).
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
    split; [exact (aapp_lit _ _ N1)| exact (aapp_lit _ _ N3)].
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).

  Ltac wsplit := unfold W; cbn [outside depot_W app]; repeat split; try exact I.

  (* [comment removed for export] *)
  Lemma Z_static : forall a, astatic a -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. bands_as (BT & _). clear - Ha B BT; try acb. unfold astatic in Ha.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP in Ha.
    wsplit; (first [clear - Ha B BT; lia | lia]).
  Qed.
  Lemma Z_SB : forall a, sb <= a < sb + kSpaceSize + kPageSize -> (a + 1 <= AB \/ AB + csz <= a) -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha Hb. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & _).
    destruct DPL as (_ & _ & E1 & E2 & _). clear - Ha Hb B D1 D2 D3 E1 E2; try acb.
    unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. wsplit; (first [clear - Ha B Hb D2 E1 E2; lia | lia]).
  Qed.
  Lemma Z_PA : forall a, a_pa s <= a < a_pa s + kPtrArrayReserve -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & _).
    destruct DPL as (_ & _ & _ & _ & _ & _ & E1 & E2 & _). bands_as (_ & _ & BP & _). clear - Ha B D1 D4 E1 E2 BP; try acb.
    unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. wsplit; (first [clear - Ha B D4 D1 BP E1 E2; lia | lia]).
  Qed.
  Lemma Z_SEC : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + sc_map_size h -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros h a Hh Ha. pose proof BND as B.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & E & _). destruct (E h Hh) as [E1 E2].
    pose proof (aapp_lit _ _ Q2) as Q2l. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].   (* [comment removed for export] *)
    clear - Ha B Q2 Q2l Q3 Q5 Q7 E1 E2; try acb.
    subst sb TH. unfold a_sb, disj, kSpaceSize, kPageSize, AHI_LO in *. acb. wsplit; (first [clear - Q3 B Ha Q7 Q5 Q2l Q2 E1 E2; lia | lia]).
  Qed.
  Lemma Z_CTX : forall a, a_ctx s + 8 <= a < a_ctx s + 160 -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & D5 & TCX & _).
    destruct DPL as (_ & _ & _ & _ & E1 & E2 & _). bands_as (_ & BC & _). clear - Ha B D3 TCX E1 E2 BC; try acb.
    unfold disj, kSpaceSize, kPageSize in *. wsplit; (first [clear - Ha B TCX D3 BC E1 E2; lia | lia]).
  Qed.
  Lemma Z_T : forall a, TH <= a < TH + 208 -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _).
    destruct DPL as (E1 & E2 & _). bands_as (BT & _). clear - Ha B D2 E1 E2 BT; try acb.
    subst TH. unfold disj, kSpaceSize, kPageSize in *. wsplit; (first [clear - Ha B D2 BT E1 E2; lia | lia]).
  Qed.
  Lemma Z_PC : forall c' a, 0 <= c' < 32 -> c' <> c -> CA + 80 * c' <= a < CA + 80 * c' + 80 -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros c' a Hc' NE Ha. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _).
    destruct DPL as (E1 & E2 & _). bands_as (BT & _). clear - Hc' NE Ha B D2 E1 E2 BT; try acb.
    subst TH. unfold disj, kSpaceSize, kPageSize in *. wsplit; try (first [clear - Hc' Ha B NE D2 BT E1 E2; lia | lia]).
  Qed.
  Lemma Z_SH : forall lo' k a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= k -> lo' + 8 * k <= aceil ->
    (lo' + 8 * k <= AB \/ AB + csz <= lo') -> sh lo' <= a < sh lo' + k -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros lo' k a H0 H8 Hk Hhi Hd Ha. pose proof BND as B. destruct RNG as (_ & _ & AB8 & _).
    assert (SS : sh lo' + k <= sh AB \/ sh AB + csz8 <= sh lo') by (clear - H8 AB8 Hk Hd B; try acb; apply sh_sep; try assumption; lia).
    assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + k <= 0x10007fef8000) by (clear - H0 Hk Hhi; try acb; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    bands_as (BT & _ & _ & BN & BS). clear - Ha B SS SB BT BN BS; try acb. wsplit; (first [clear - Ha B SB BT SS BN BS; lia | lia]).
  Qed.
  Lemma Z_flags : forall a, aflags_range a -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. bands_as (BT & _). clear - Ha B BT; try acb. unfold aflags_range in Ha.
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP in Ha.
    wsplit; (first [clear - B Ha BT; lia | lia]).
  Qed.
  Lemma Z_PCc : forall a, P + 4 <= a < P + 80 -> outside W a.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros a Ha. pose proof BND as B. destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & _).
    destruct DPL as (E1 & E2 & _). bands_as (BT & _). clear - Ha B D2 E1 E2 BT; try acb.
    subst TH. unfold disj, kSpaceSize, kPageSize in *. wsplit; try (first [clear - Ha B D2 BT E1 E2; lia | lia]).
  Qed.

  (* [comment removed for export] *)
  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact WFs. Qed.
  Let UPOS : 0 < U. Proof. pose proof BND as B. destruct RQ as (_ & _ & _ & _ & Q5 & _). subst U. clear - B Q5; try acb. lia. Qed.
  Let FRESH : PositiveMap.find (ckey U) (as_chunks st) = None.
  Proof.
    destruct RQ as (Q1 & Q2 & Q3 & Q4 & _). destruct CSZ as (_ & C2 & _). destruct PLF as (_ & S2 & _).
    refine (hit_fresh st size c cp (tl chunks) WFs ltac:(hci; lia) ltac:(hci; unfold kNumClasses; lia) Q3 _ PCS _).
    - rewrite Q2. exact C2.
    - subst sb. unfold a_sb, AHI_LO in S2. unfold st. lia.
  Qed.
  Let WF' : WF st'.
  Proof.
    destruct RQ as (Q1 & Q2 & Q3 & Q4 & _). destruct CSZ as (_ & C2 & _). destruct PLF as (_ & S2 & _).
    refine (WF_hit st size c cp (tl chunks) WFs ltac:(hci; lia) ltac:(hci; unfold kNumClasses; lia) _ Q3 _ PCS _).
    - rewrite Q2. reflexivity.
    - rewrite Q2. exact C2.
    - subst sb. unfold a_sb, AHI_LO in S2. unfold st. lia.
  Qed.
  Let OK' : ast_ok s'. Proof. split; [exact PL| exact WF']. Qed.
  Let PERM : Permutation (chunk_list st') (ch :: chunk_list st).
  Proof. exact (chunk_list_upd_perm (set_pc st c (mkPC (cnt - 1) (tl chunks))) ch KEYS UPOS FRESH). Qed.
  Let INl : forall x, In x (chunk_list st') <-> x = ch \/ In x (chunk_list st).
  Proof.
    intros x. split.
    - intros Hx. apply (Permutation_in x PERM) in Hx. destruct Hx as [E|Hx]; [left; symmetry; exact E| right; exact Hx].
    - intros Hx. apply (Permutation_in x (Permutation_sym PERM)). destruct Hx as [->|Hx]; [left; reflexivity| right; exact Hx].
  Qed.
  Let CHIN : In ch (chunk_list st'). Proof. apply INl. left. reflexivity. Qed.
  Let CHNOT : ~ In ch (chunk_list st).
  Proof. intros Hin. apply (chunk_list_find st ch KEYS) in Hin. cbn [ch_user_beg ch] in Hin. rewrite FRESH in Hin. discriminate. Qed.
  Let LENC : length (as_cache st) = 32%nat.
  Proof. destruct WFs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Let PCc : get_pc st' c = mkPC (cnt - 1) (tl chunks).
  Proof. unfold st', hit_state, get_pc, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx. clear - HC; try acb. lia. Qed.
  Let PCo : forall c', 0 <= c' -> c' <> c -> get_pc st' c' = get_pc st c'.
  Proof. intros c' H1 H2. unfold st', hit_state, get_pc, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx. clear - HC H1 H2; try acb. lia. Qed.
  Let PRIMch : ch_primary ch = true.
  Proof. unfold ch_primary. cbn [ch_class ch]. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
  (* [comment removed for export] *)
  Let EXT : ch_lo ch = AB /\ ch_end ch = AB + csz /\ ch_user_beg ch = U /\ ch_alloc_beg ch = AB /\ ch_used ch = size /\ ch_rz ch = rz.
  Proof.
    destruct RQ as (_ & _ & _ & Q4 & _). unfold ch_lo, ch_end. rewrite PRIMch. cbn [ch_alloc_beg ch_class ch_user_beg ch_used ch_rz ch].
    subst csz. repeat split; try reflexivity. exact Q4.
  Qed.

  (* [comment removed for export] *)
  Lemma land_lnot7 : forall x, Z.land x (Z.lnot 7) = x - x mod 8.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT.
    intros x. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. (first [clear - H; lia | lia]).
  Qed.
  Lemma malloc_hit_model : exists st'' ev, am_malloc_k st size 0 = Some (U, st'', ev) /\ same_but_shadow st'' st'.
  Proof.
    destruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). destruct RNG as (R1 & R2 & R3 & _). pose proof BND as B. destruct CSZ as (_ & C2 & _).
    pose proof (rz_size_facts size) as (_ & RZ16 & RZC). fold rz in RZ16, RZC. pose proof SZ as SZ2. unfold kMaxSize in SZ2.
    assert (U8 : U mod 8 = 0) by (subst U; clear - R3 RZ16; try acb; Z.div_mod_to_equations; lia).
    assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
    { intros a Ha Hb. unfold addr_is_in_mem, kHighMemBeg, kHighMemEnd. apply orb_true_intro. right.
      apply andb_true_intro. split; [apply Z.leb_le| apply Z.leb_le]; clear - Ha Hb B; try acb; lia. }
    refine (am_malloc_hit st size 0 c cp (tl chunks) ltac:(hci; clear - SZ; try acb; lia) _ _ _ _ PCS HIT _ _ _ _ _ Q3 _).
    - unfold size_too_big, kMaxAllowedMalloc. rewrite Q2, Q4. change (rq_n (compute_req size)) with size. change (2^40) with 1099511627776.
      replace (1099511627776 <? size) with false by (symmetry; apply Z.ltb_ge; clear - SZ2 Q6 Q5; try acb; lia).
      replace (1099511627776 <? needed) with false by (symmetry; apply Z.ltb_ge; clear - SZ2; try acb; lia). reflexivity.
    - rewrite Q2. exact (proj2 SZ).
    - rewrite Q2. reflexivity.
    - unfold kNumClasses. clear - HC; try acb. lia.
    - change (compact_to_addr st c cp + rq_rz (compute_req size)) with U. change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). exact U8.
    - change (compact_to_addr st c cp + rq_rz (compute_req size)) with U. apply IM; subst U; clear - B R1 Q6 C2 Q5; try acb; lia.
    - change (compact_to_addr st c cp + rq_rz (compute_req size)) with U. rewrite Q4, land_lnot7. apply IM; subst U; clear - B R1 Q6 C2 Q5 SZ2; try acb; Z.div_mod_to_equations; lia.
    - change (compact_to_addr st c cp + rq_rz (compute_req size)) with U. rewrite Q4, land_lnot7. apply IM; subst U; clear - B R1 Q6 C2 Q5 Q7 SZ2; try acb; Z.div_mod_to_equations; lia.
    - change (rq_rz (compute_req size)) with rz. clear - RZC; try acb. clearbody rz. lia.
    - rewrite Q2, Q4. change (rq_rz (compute_req size)) with rz. clear - Q6; try acb. lia.
  Qed.

  Lemma u8arr_app : forall mm A l1 l2, u8arr asegs mm A (l1 ++ l2) <-> u8arr asegs mm A l1 /\ u8arr asegs mm (A + Z.of_nat (length l1)) l2.
  Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT DCAP.
    intros mm A l1 l2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add. rewrite wr_at_app by lia. (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]).
  Qed.

  (* [comment removed for export] *)
  Section Post.
    Variables (m' : mem) (j0 j1 j2 j3 : word) (b1 : Z).
    Hypothesis MU : munch W m m'.
    Hypothesis WM : wmono asegs m m'.
    Hypothesis MI' : mem_inv asegs m'.
    Hypothesis QC1' : rw_cells asegs m' P [C4 (wz (cnt - 1)); C4 (wz (max_count c))].
    Hypothesis QC3' : u32arr asegs m' (P + 16) (wlist (rev (tl chunks))).
    Hypothesis QC4' : stk asegs m' (P + 16 + 4 * (cnt - 1)) (P + 80).
    Hypothesis QST' : rw_cells asegs m' (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3].
    Hypothesis HDR : rw_cells asegs m' (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)].
    Hypothesis B1 : b1_ok b1.
    Hypothesis LEFT : rz = 16 \/ (rw_cells asegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs m' (AB + 16) (U + -16)).
    Hypothesis FILL : u8arr asegs m' U (repeat (b8 0xbe) (Z.to_nat (Z.min size 4096))).
    Hypothesis SLACK : stk asegs m' (U + Z.min size 4096) (AB + csz).
    Hypothesis SHA : u8arr asegs m' (sh AB) (alloc_shadow rz size csz).
    Hypothesis TST' : stk asegs m' (TH + 2800) (TH + 3168).
    Hypothesis UNW' : rw_cells asegs m' (TH + 3168) [C1 (b8 0)].
    Hypothesis DEP' : DEPOT asegs d' m'.

    Let AG : agree_on (outside W) m m'. Proof. apply munch_agree. exact MU. Qed.

    (* [comment removed for export] *)
    Let SH3 : poisoned m' AB (Z.to_nat (rz / 8)) kAsanHeapLeftRedzoneMagic
            /\ SHAD m' U (shadow_of size)
            /\ poisoned m' (U + round_up size 8) (Z.to_nat ((AB + csz - (U + round_up size 8)) / 8)) kAsanHeapLeftRedzoneMagic.
    Proof.
      destruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). destruct RNG as (R1 & R2 & R3 & _). pose proof BND as B.
      pose proof (rz_size_facts size) as (_ & RZ16 & _). fold rz in RZ16.
      assert (S0 : SHAD m' AB (alloc_shadow rz size csz)) by (split; [clear - B; try acb; lia| split; [exact R3| exact SHA]]).
      unfold alloc_shadow in S0. apply SHAD_app in S0. destruct S0 as [S1 S2]. apply SHAD_app in S2. destruct S2 as [S2 S3].
      rewrite repeat_length, Z2Nat.id in S2, S3 by (clear - Q5; try acb; Z.div_mod_to_equations; lia).
      replace (AB + 8 * (rz / 8)) with U in S2, S3 by (subst U; clear - RZ16; try acb; Z.div_mod_to_equations; lia).
      rewrite (shadow_of_length size) in S3 by (clear - SZ; try acb; lia).
      replace (U + 8 * nsh size) with (U + round_up size 8) in S3 by (unfold nsh, round_up; clear - SZ; try acb; Z.div_mod_to_equations; lia).
      replace (csz - rz - round_up size 8) with (AB + csz - (U + round_up size 8)) in S3 by (subst U; clear; lia).
      split; [exact S1| split; [exact S2| exact S3]].
    Qed.

    Lemma new_chunk_rep : chunk_rep m' ch.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' b1 HDR B1 LEFT FILL SLACK SHA.
      destruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). destruct RNG as (R1 & R2 & R3 & _). pose proof BND as B.
      destruct EXT as (E1 & E2 & E3 & E4 & E5 & E6). destruct SH3 as (S1 & S2 & S3). destruct CSZ as (_ & C2 & _).
      unfold chunk_rep. rewrite E2, E3, E4, E5, E6. cbn [ch_state ch]. rewrite PRIMch.
      assert (MN : 1 <= Z.min size 4096 <= size) by (clear - SZ; try acb; lia).
      split.
      { exists b1, id. destruct B1 as [B1a B1b]. split; [| split; [exact B1a| exact B1b]].
        unfold kChunkHeaderSize. replace (U - 16) with (U + -16) by (clear; lia). exact HDR. }
      split.
      { destruct LEFT as [L|[L1 L2]]; [left; exact L| right]. unfold kChunkHeaderSize. replace (U - 16) with (U + -16) by (clear; lia).
        split; [exact L1|]. intros _. replace (AB + 16 + (rz - 32)) with (U + -16) by (subst U; clear; lia). exact L2. }
      split.
      { split.
        - (* [comment removed for export] *)
          destruct FILL as [_ WF1]. rewrite repeat_length, Z2Nat.id in WF1 by lia.
          destruct (stk_split asegs _ _ (U + size) _ SLACK ltac:(hci; subst U; clear - MN Q6 C2 Q5; try acb; lia)) as [SL _].
          destruct SL as (_ & _ & SL3).
          assert (W2 : wr_at asegs m' (U + Z.min size 4096) (size - Z.min size 4096)).
          { split; [subst U; clear - B MN Q5; try acb; lia|]. split; [subst U; clear - B MN Q5 Q6 C2; try acb; lia|]. intros i Hi. apply (proj1 (SL3 (U + Z.min size 4096 + i) ltac:(hci; clear - Hi MN; try acb; lia))). }
          pose proof (proj2 (wr_at_app asegs m' U (Z.min size 4096) (size - Z.min size 4096) ltac:(hci; lia) ltac:(hci; lia)) (conj WF1 W2)) as W12.
          replace (Z.min size 4096 + (size - Z.min size 4096)) with size in W12 by (clear; lia). exact W12.
        - destruct S2 as (_ & _ & [_ WS]). rewrite shadow_of_length in WS by (clear - SZ; try acb; lia). exact WS. }
      split.
      { intros POS. destruct (stk_split asegs _ _ (U + size) _ SLACK ltac:(hci; subst U; clear - MN Q6 C2 Q5; try acb; lia)) as [_ SL].
        replace (U + size + (AB + csz - (U + size))) with (AB + csz) by (clear; lia). exact SL. }
      split; [exact S1|]. split; [exact S3| exact I].
    Qed.

    (* [comment removed for export] *)
    Lemma new_block : (exists junk, rw_cells asegs m' U [CB (Z.to_nat size) junk]) /\ addressable m' U size.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT DCAP m' FILL SLACK SHA.
      destruct RQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof BND as B. destruct CSZ as (_ & C2 & _).
      destruct SH3 as (_ & S2 & _).
      assert (MN : 1 <= Z.min size 4096 <= size) by (clear - SZ; try acb; lia).
      split; [| split; [clear - SZ; try acb; lia| exact S2]].
      destruct (stk_split asegs _ _ (U + size) _ SLACK ltac:(hci; subst U; clear - MN Q6 C2 Q5; try acb; lia)) as [SL _].
      destruct (stk_cells _ _ _ SL ltac:(hci; clear - MN; try acb; lia)) as [junk J].
      assert (L : length junk = Z.to_nat (U + size - (U + Z.min size 4096))) by (destruct J as [[[L _] _] _]; exact L).
      apply u8arr_of_rw_cells in J.
      exists (repeat (b8 0xbe) (Z.to_nat (Z.min size 4096)) ++ junk).
      assert (FL : Z.of_nat (length (repeat (b8 190) (Z.to_nat (Z.min size 4096)))) = Z.min size 4096) by (rewrite repeat_length; clear - MN; try acb; lia).
      assert (UJ : u8arr asegs m' U (repeat (b8 190) (Z.to_nat (Z.min size 4096)) ++ junk)).
      { apply (proj2 (u8arr_app m' U _ _)). split; [exact FILL|]. rewrite FL. exact J. }
      apply rw_cells_of_u8arr in UJ. rewrite length_app, repeat_length, L in UJ.
      replace (Z.to_nat (Z.min size 4096) + Z.to_nat (U + size - (U + Z.min size 4096)))%nat with (Z.to_nat size) in UJ by (clear - MN; try acb; lia). exact UJ.
    Qed.

    (* [comment removed for export] *)
    Lemma pclass_after_c : pclass_rep s' m' c.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' MU WM QC1' QC3' QC4'.
      pose proof BND as B. pose proof (hit_cells_of_arep s m R c ltac:(hci; unfold kNumClasses; lia) HIT) as HCL.
      cbv zeta in HCL. destruct HCL as (jj0 & jj1 & jj2 & jj3 & _ & QC2 & _ & _ & _ & _ & _ & _ & _ & CC & CR & _ & _ & _ & INI).
      unfold pclass_rep. change (a_st s') with st'. rewrite PCc. cbn [pc_count pc_chunks].
      change (as_cache_inited st') with (as_cache_inited st). change (a_cache s') with (a_cache s). unfold st. rewrite INI. cbn [andb].
      replace (negb (c =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
      assert (EA : a_cache s + PCLASS_SIZE * c = P) by (subst P CA TH; unfold a_cache, OT_CACHE, PCLASS_SIZE; clear; lia). rewrite EA.
      split; [exact QC1'|]. split.
      { eapply (rw_cells_transport_pt (outside W) m m' AG WM). { unfold P, CA, TH, csz in *. unfold a_cache, OT_CACHE in QC2. exact QC2. }
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply Z_PCc. clear - Ha; try acb. lia. }
      split; [exact QC3'|].
      intros _. replace (P + 16 + 4 * (cnt - 1) + (64 - 4 * (cnt - 1))) with (P + 80) by (clear; lia). exact QC4'.
    Qed.

    Lemma thread_after : thread_rep s' m'.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' j0 j1 j2 j3 MU WM QST' TST' UNW'.
      pose proof BND as B. destruct R as (_ & _ & _ & THR & _).
      destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
      destruct PLF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TCX & _).
      unfold thread_rep. change (a_ctx s') with (a_ctx s). change (a_thr s') with TH. change (a_top s') with (a_top s). change (a_bot s') with (a_bot s).
      change (a_cache s') with (a_cache s). change (as_tq (a_st s')) with (as_tq st).
      fold TH in T1, T2c, T2d, T3, T4, J1, J3, T5. unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
      Ltac trc H Z := eapply (rw_cells_transport_pt (outside W) m m' AG WM); [exact H|];
                      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat]; let Ha := fresh in intros ? Ha; apply Z; clear - Ha; try acb; lia.
      split; [trc T1 Z_T|]. split; [trc T2 Z_CTX|]. split; [trc T2b Z_CTX|]. split; [trc T2c Z_T|]. split; [trc T2d Z_T|].
      split; [trc T3 Z_T|]. split; [trc T4 Z_T|].
      split; [eapply (junk_transport_pt (outside W) m m' AG WM); [exact J1|]; let Ha := fresh in intros ? Ha; apply Z_T; clear - Ha; try acb; lia|].
      split.
      { intros _. unfold a_cache, OT_CACHE. fold TH. pose proof (stk_of_rw_cells asegs _ _ _ QST') as SQ.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SQ.
        replace (TH + 208 + 2560 + (2800 - 208 - 2560)) with (TH + 208 + 2560 + 32) by (clear; lia). exact SQ. }
      split; [intros _; replace (TH + 2800 + (3168 - 2800)) with (TH + 3168) by (clear; lia); exact TST'|].
      exact UNW'.
    Qed.
    (* [comment removed for export] *)
    Lemma old_chunk_rep : forall x, In x (chunk_list st) -> chunk_rep m' x.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' MU WM.
      intros x Hx. destruct R as (_ & _ & _ & _ & _ & _ & _ & CHR & _).
      assert (Hx' : In x (chunk_list (a_st s'))) by (apply INl; right; exact Hx).
      assert (NEQ : x <> ch) by (intros ->; exact (CHNOT Hx)).
      pose proof (record_ext s' OK' x Hx') as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
      pose proof (record_vs_record s' OK' ch CHIN x Hx' NEQ) as D. destruct EXT as (E1 & E2 & _). rewrite E1, E2 in D. clear E1 E2.
      acb. unfold AIMG_TOP in X1.   (* [comment removed for export] *)
      apply (chunk_rep_frame s' m m' (outside W) AG WM OK' x Hx'); [| exact (CHR x Hx)].
      (* [comment removed for export] *)
      assert (APP : forall a, ch_lo x <= a < ch_end x -> outside W a).
      { intros a Ha. destruct (ch_primary x) eqn:PX.
        - destruct (record_primary_space s' OK' x Hx' PX) as [P1 P2]. apply Z_SB; [| clear - Ha D; try acb; lia].
          change (a_sb s') with sb in P1, P2. unfold kSpaceSize, kPageSize in P2 |- *. clear - Ha P1 P2; try acb. lia.
        - destruct (record_secondary_map s' OK' x Hx' PX) as (h & Hh & L1 & L2 & _). apply (Z_SEC h); [exact Hh| clear - Ha L1 L2; try acb; lia]. }
      assert (SHW : forall lo' k a, ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k -> sh lo' <= a < sh lo' + k -> outside W a).
      { intros lo' k a G1 G2 G3 G4 Ga. apply (Z_SH lo' k); try assumption.
        - clear - G1 X1; try acb. lia.
        - acb. clear - G2 X2; try acb. lia.
        - clear - G1 G2 D; try acb. lia. }
      pose proof (chunk_align s' OK' x Hx') as (A1 & A2 & A3 & A4 & A5).
      assert (AL8 : ch_alloc_beg x mod 8 = 0 /\ ch_user_beg x mod 8 = 0 /\ 8 * (ch_rz x / 8) = ch_rz x)
        by (clear - A1 A2 A3; try acb; Z.div_mod_to_equations; lia).
      clear A1 A2 A3. destruct AL8 as (A1 & A3 & RZ8).
      assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8 /\ (round_up (ch_used x) 8) mod 8 = 0)
        by (unfold nsh, round_up; clear - X9; try acb; Z.div_mod_to_equations; lia).
      intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
      - apply APP. clear - Ha X3 X6 X7 X9 NS; try acb. lia.
      - apply APP. clear - Ha X3 X6 X8 X9; try acb. lia.
      - apply APP. clear - Ha X3 X6 X7 X8 NS; try acb. lia.
      - apply (SHW (ch_alloc_beg x) (ch_rz x / 8) a); clear - Ha X3 X6 X7 X8 X9 NS A1 RZ8; try acb; lia.
      - apply (SHW (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a);
          clear - Ha X3 X6 X7 X8 X9 NS A3 A4; try acb; try lia; Z.div_mod_to_equations; lia.
      - apply (SHW (ch_user_beg x) (nsh (ch_used x)) a); clear - Ha X3 X6 X7 X8 X9 NS A3; try acb; try lia; unfold nsh; Z.div_mod_to_equations; lia.
      - unfold ch_lo in *. rewrite NP in *. apply (SHW (ch_alloc_beg x - kPageSize) 512 a); unfold kPageSize in *; clear - Ha X3 X6 X7 X8 X9 NS A1; try acb;
          try lia; Z.div_mod_to_equations; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma batches_after : batches_rep m' (qc_list (as_tq st)) /\ batches_rep m' (qc_list (as_gq st)).
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' MU WM.
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & BT & BG).
      assert (BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
                0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
      { intros b Hb. pose proof (WF_batch _ b WFs Hb) as (Q1 & Q2 & _). unfold kBatchSize, kBatchCount in *. clear - Q1 Q2; try acb. lia. }
      assert (HPB : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
                (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> outside W a).
      { intros b a Hb Hr. pose proof (batch_in_space s' OK' b Hb) as (P1 & P2 & P3). change (a_sb s') with sb in P1, P2.
        pose proof (batch_vs_record s' OK' ch CHIN b Hb) as D. destruct EXT as (E1 & E2 & _). rewrite E1, E2 in D.
        pose proof BND as B. unfold kBatchSize, kSpaceSize in *.
        destruct Hr as [Hr|Hr].
        - apply Z_SB; [unfold kSpaceSize, kPageSize; clear - Hr P1 P2; try acb; lia| clear - Hr D; try acb; lia].
        - apply (Z_SH (qb_addr b) 1024); try assumption; try (clear - Hr D P1 P2 B; try acb; lia).
          all: (clear - P2 B; try acb; lia). }
      split.
      - eapply (batches_rep_transport (outside W) m m'); [exact AG| exact WM| | | exact BT].
        + intros b a Hb Hr. apply (HPB b a); [apply in_app_iff; left; exact Hb| exact Hr].
        + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
      - eapply (batches_rep_transport (outside W) m m'); [exact AG| exact WM| | | exact BG].
        + intros b a Hb Hr. apply (HPB b a); [apply in_app_iff; right; exact Hb| exact Hr].
        + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
    Qed.

    (* [comment removed for export] *)
    Lemma statics_after : inst_rep s' m' /\ flags_rep s' m' /\ ia_rep s' m' /\ sec_rep s' m'.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' MU WM.
      destruct R as (_ & INST & FL & _ & SEC0 & IA & _).
      split.
      { apply (inst_rep_frame s' m m' (outside W) AG WM); [| exact INST]. intros a Ha. apply Z_static. unfold astatic. left. exact Ha. }
      split.
      { apply (flags_rep_frame s' m m' (outside W) AG WM); [| exact FL]. exact Z_flags. }
      split.
      { apply (ia_rep_frame s' m m' (outside W) AG WM); [| exact IA]. intros a Ha. apply Z_static. unfold astatic. do 11 right. left. exact Ha. }
      apply (sec_rep_frame s' m m' (outside W) AG WM OK'); [| | exact SEC0].
      - intros a Ha. apply Z_PA. change (a_pa s') with (a_pa s) in Ha. change (a_st s') with st' in Ha. change (as_n_reserved st') with (as_n_reserved st) in Ha.
        destruct WFs as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). unfold kChunksBlockCount, kPtrArrayReserve in *.
        assert (0 <= zlen (as_sec st)) by (unfold zlen; lia). clear - Ha Wn Wr H; try acb. lia.
      - intros h a Hh Ha. apply (Z_SEC h); [exact Hh|].
        pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
        pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _). unfold kPageSize in *. clear - Ha Q4; try acb. lia.
    Qed.

    (* [comment removed for export] *)
    Let PCsub : forall c0 cp0, 0 <= c0 -> In cp0 (pc_chunks (get_pc st' c0)) -> In cp0 (pc_chunks (get_pc st c0)).
    Proof.
      intros c0 cp0 Hc0 Hin. destruct (Z.eq_dec c0 c) as [->|NE].
      - rewrite PCc in Hin. cbn [pc_chunks] in Hin. rewrite PCS. right. exact Hin.
      - rewrite (PCo c0 Hc0 NE) in Hin. exact Hin.
    Qed.
    (* [comment removed for export] *)
    Let FREE_out : forall c0 cp0 a, 0 <= c0 < kNumClasses ->
        In cp0 (rg_free_array (get_region st c0)) \/ In cp0 (pc_chunks (get_pc st' c0)) ->
        compact_to_addr st c0 cp0 <= a < compact_to_addr st c0 cp0 + class_size c0 -> outside W a.
    Proof.
      intros c0 cp0 a Hc0 Hin Ha.
      pose proof (freech_in_space s' OK' c0 cp0 Hc0 Hin) as (P1 & P2 & P3 & P4 & P5).
      pose proof (freech_vs_record s' OK' ch CHIN c0 cp0 Hc0 Hin) as D. destruct EXT as (E1 & E2 & _). rewrite E1, E2 in D.
      change (a_sb s') with sb in P1, P2. change (compact_to_addr (a_st s') c0 cp0) with (compact_to_addr st c0 cp0) in P1, P2, P3, D.
      apply Z_SB; [unfold kSpaceSize, kPageSize in *; clear - Ha P1 P2; try acb; lia| clear - Ha D; try acb; lia].
    Qed.
    Let FREE_sh_out : forall c0 cp0 a, 0 <= c0 < kNumClasses ->
        In cp0 (rg_free_array (get_region st c0)) \/ In cp0 (pc_chunks (get_pc st' c0)) ->
        sh (compact_to_addr st c0 cp0) <= a < sh (compact_to_addr st c0 cp0) + class_size c0 / 8 -> outside W a.
    Proof.
      intros c0 cp0 a Hc0 Hin Ha. pose proof BND as B.
      pose proof (freech_in_space s' OK' c0 cp0 Hc0 Hin) as (P1 & P2 & P3 & P4 & P5).
      pose proof (freech_vs_record s' OK' ch CHIN c0 cp0 Hc0 Hin) as D. destruct EXT as (E1 & E2 & _). rewrite E1, E2 in D.
      change (a_sb s') with sb in P1, P2. change (compact_to_addr (a_st s') c0 cp0) with (compact_to_addr st c0 cp0) in P1, P2, P3, D.
      assert (C8 : 8 * (class_size c0 / 8) = class_size c0) by (clear - P5; try acb; Z.div_mod_to_equations; lia).
      apply (Z_SH (compact_to_addr st c0 cp0) (class_size c0 / 8)); try assumption.
      - clear - P1 B; try acb. lia.
      - clear - P4; try acb. lia.
      - acb. unfold kSpaceSize in P2. clear - P2 B C8; try acb. lia.
      - clear - D C8; try acb. lia.
    Qed.

    Lemma regions_after : forall c0, 0 <= c0 < kNumClasses ->
      region_rep s' m' c0 /\ pclass_rep s' m' c0 /\ region_shadow_rep s' m' c0 /\ region_junk_rep s' m' c0.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' MU WM QC1' QC3' QC4'.
      intros c0 Hc0. destruct R as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c0 Hc0) as (RG & PC & RSH & RJ).
      pose proof BND as B. destruct EXT as (E1 & E2 & _).
      pose proof (farray_in_space s' OK' c0 Hc0) as (F1 & F2 & F3 & F4 & F5).
      pose proof (farray_vs_record s' OK' ch CHIN c0 Hc0) as FD. rewrite E1, E2 in FD.
      change (a_sb s') with sb in F1, F2. change (FA s' c0) with (FA s c0) in F1, F2, F3, FD.
      change (get_region (a_st s') c0) with (get_region st c0) in F2, F4, F5, FD.
      pose proof (tail_in_space s' OK' c0 Hc0) as (T1' & T2' & T3' & T4' & T5').
      pose proof (tail_vs_record s' OK' ch CHIN c0 Hc0) as TD. rewrite E1, E2 in TD.
      change (a_sb s') with sb in T1', T2'. change (RB s' c0) with (RB s c0) in T1', T2', T3', TD.
      change (get_region (a_st s') c0) with (get_region st c0) in T1', T2', T3', T4', T5', TD.
      split.
      { apply (region_rep_frame s' m m' (outside W) AG WM OK' c0 Hc0); [ | | | exact RG].
        - intros a Ha. change (a_ri s') with (a_ri s) in Ha. unfold a_ri in Ha. fold sb in Ha.
          apply Z_SB; unfold kSpaceSize, kPageSize in *; clear - Ha B; try acb; lia.
        - intros a Ha. change (FA s' c0) with (FA s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
          apply Z_SB; [unfold kSpaceSize, kPageSize in *; clear - Ha F1 F2; try acb; lia| clear - Ha FD; try acb; lia].
        - intros a Ha. change (RB s' c0) with (RB s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
          apply Z_SB; [unfold kSpaceSize, kPageSize in *; clear - Ha T1' T2'; try acb; lia| clear - Ha TD; try acb; lia]. }
      split.
      { destruct (Z.eq_dec c0 c) as [->|NE]; [exact pclass_after_c|].
        unfold pclass_rep. change (a_st s') with st'. rewrite (PCo c0 ltac:(hci; clear - Hc0; try acb; lia) NE).
        change (as_cache_inited st') with (as_cache_inited st). change (a_cache s') with (a_cache s).
        apply (pclass_rep_frame s m m' (outside W) AG WM OK c0 Hc0); [| exact PC].
        intros a Ha. apply (Z_PC c0); [unfold kNumClasses in Hc0; clear - Hc0; try acb; lia| exact NE|].
        unfold a_cache, OT_CACHE, PCLASS_SIZE in Ha. subst CA TH. clear - Ha; try acb. lia. }
      split.
      { apply (region_shadow_rep_frame s' m m' (outside W) AG WM OK' c0 Hc0).
        - intros cp0 a Hin Ha. exact (FREE_sh_out c0 cp0 a Hc0 Hin Ha).
        - intros a Ha. change (RB s' c0) with (RB s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
          apply (Z_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8)); try assumption.
          + clear - T1' B; try acb. lia.
          + clear - T4' T5'; try acb. Z.div_mod_to_equations. lia.
          + acb. unfold kSpaceSize in T2'. clear - T2' T4' T5' B; try acb. Z.div_mod_to_equations. lia.
          + clear - TD T4' T5'; try acb. Z.div_mod_to_equations. lia.
        - intros a Ha. change (FA s' c0) with (FA s c0) in Ha. change (get_region (a_st s') c0) with (get_region st c0) in Ha.
          apply (Z_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8)); try assumption.
          + clear - F1 B; try acb. lia.
          + clear - F4 F5; try acb. Z.div_mod_to_equations. lia.
          + acb. unfold kSpaceSize in F2. clear - F2 F4 F5 B; try acb. Z.div_mod_to_equations. lia.
          + clear - FD F4 F5; try acb. Z.div_mod_to_equations. lia.
        - unfold region_shadow_rep in RSH |- *. change (a_st s') with st'. destruct RSH as (H1 & H2 & H3 & H4).
          split; [exact H1|]. split; [| split; [exact H3| exact H4]].
          intros cp0 Hin. apply H2. apply (PCsub c0); [clear - Hc0; try acb; lia| exact Hin]. }
      apply (region_junk_rep_frame s' m m' (outside W) AG WM c0 Hc0).
      - intros cp0 a Hin Ha. exact (FREE_out c0 cp0 a Hc0 Hin Ha).
      - unfold region_junk_rep in RJ |- *. change (a_st s') with st'. destruct RJ as [H1 H2].
        split; [exact H1|]. intros cp0 Hin. apply H2. apply (PCsub c0); [clear - Hc0; try acb; lia| exact Hin].
    Qed.

    (* [comment removed for export] *)
    Lemma arep_after : AREP s' m'.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' j0 j1 j2 j3 b1 MU WM QC1' QC3' QC4' QST' HDR B1 LEFT FILL SLACK SHA TST' UNW'.
      destruct statics_after as (I1 & I2 & I3 & I4). destruct batches_after as [B1' B2'].
      split; [exact OK'|]. split; [exact I1|]. split; [exact I2|]. split; [exact thread_after|]. split; [exact I4|]. split; [exact I3|].
      split; [exact regions_after|].
      split.
      { intros x Hx. change (a_st s') with st' in Hx. apply INl in Hx. destruct Hx as [->|Hx]; [exact new_chunk_rep| exact (old_chunk_rep x Hx)]. }
      split; [exact B1'| exact B2'].
    Qed.

    Lemma arheap_after : ARHEAP s' ((U, size) :: LB) m'.
    Proof using HCEIL ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT m' j0 j1 j2 j3 b1 MU WM QC1' QC3' QC4' QST' HDR B1 LEFT FILL SLACK SHA TST' UNW'.
      destruct HR as (_ & ND & LBs). destruct RQ as (_ & _ & _ & Q4 & _).
      assert (AL : forall b, In b (alb s') <-> b = (U, size) \/ In b (alb s)).
      { intros b. unfold alb. change (a_st s') with st'. rewrite !in_map_iff. split.
        - intros (x & E & Hx). apply filter_In in Hx. destruct Hx as [Hx AX]. apply INl in Hx. destruct Hx as [->|Hx].
          + left. rewrite <- E. cbn [ch_user_beg ch_used ch]. rewrite Q4. reflexivity.
          + right. exists x. split; [exact E|]. apply filter_In. split; [exact Hx| exact AX].
        - intros [->|(x & E & Hx)].
          + exists ch. split; [cbn [ch_user_beg ch_used ch]; rewrite Q4; reflexivity|]. apply filter_In. split; [exact CHIN| reflexivity].
          + apply filter_In in Hx. destruct Hx as [Hx AX]. exists x. split; [exact E|]. apply filter_In. split; [apply INl; right; exact Hx| exact AX]. }
      split; [exact arep_after|]. split.
      - constructor; [| exact ND]. intros Hin. apply LBs in Hin. destruct (alb_In s U size Hin) as (x & Hx & _ & EU & _).
        apply (chunk_list_find st x KEYS) in Hx. rewrite EU in Hx. rewrite FRESH in Hx. discriminate.
      - intros b. rewrite AL. cbn [In]. rewrite LBs. split; intros [H|H]; [left; symmetry; exact H| right; exact H| left; symmetry; exact H| right; exact H].
    Qed.

  End Post.
  (* [comment removed for export] *)
  Variable MP : Z. Variable pjunk : word.
  Hypothesis Ha0 : a0 = wz MP. Hypothesis Ha1 : a1 = wz 64. Hypothesis Ha2 : a2 = wz size.
  Hypothesis SZP : size = 32768.
  Hypothesis MPR : 0 <= MP /\ MP + 8 <= 2^64.
  Hypothesis MPDJ : hidden (forall a, MP <= a < MP + 8 -> outside W a).
  Hypothesis PW : rw_cells asegs m MP [C8 pjunk].
  Let neededA := round_up (Z.max size 8) 64 + 64 + rz.
  (* [comment removed for export] *)
  Definition memalign_hit_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1 m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
      /\ ARHEAP s' ((U, size) :: LB) m1 /\ DEPOT asegs d' m1
      /\ (exists junk, rw_cells asegs m1 U [CB (Z.to_nat size) junk]) /\ addressable m1 U size
      /\ U mod 64 = 0
      /\ munch [(MP, MP + 8)]%Z m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m' /\ rw_cells asegs m' MP [C8 (wz U)] /\ stk asegs m' lo (bv_unsigned sp)
      /\ m' = write_to_mem m1 (wa MP) (le8 (wz U)).

  Theorem memalign_arep_hit :
    evt asegs memalign_hit_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c4bd0) fc None m (seg_rom asegs)).
  Proof.
    pose proof (hit_cells_of_arep s m R c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIT) as HCL. cbv zeta in HCL.
    destruct HCL as (j0 & j1 & j2 & j3 & QC1 & QC2 & QC3 & QC4 & QST & CHUNK & SHK & TST & UNW & CC & CR & CPS & AB1 & AB2 & INI).
    change (a_sb s + c * 2 ^ 32 + hd 0 (pc_chunks (get_pc (a_st s) c)) * 16) with (sb + c * 2^32 + cp * 16) in CHUNK, SHK, AB1, AB2.
    rewrite <- ABE in CHUNK, SHK, AB1, AB2.
    pose proof PLF as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & TCX & TB1 & TB2).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof BND as B.
    (* [comment removed for export] *)
    assert (ERZ : rz = 1024) by (unfold rz; rewrite SZP; reflexivity).
    assert (ENA : neededA = 33856) by (unfold neededA; rewrite ERZ, SZP; reflexivity).
    assert (EC : c = 29) by (unfold c, needed; rewrite ERZ, SZP; reflexivity).
    assert (ECA : class_id neededA = c) by (rewrite ENA, EC; reflexivity).
    assert (ECSZ : csz = 49152) by (unfold csz; rewrite EC; reflexivity).
    assert (ABA : AB mod 64 = 0).
    { pose proof (co_elems _ _ CO cp ltac:(rewrite PCS; left; reflexivity)) as (_ & _ & _ & CM).
      unfold kCompactPtrScale in CM. rewrite Z.shiftl_mul_pow2 in CM by (clear; lia). change (2 ^ 4) with 16 in CM.
      change (class_size c) with csz in CM. rewrite ECSZ in CM.
      rewrite ABE. clear - CM S1 HC; try acb. Z.div_mod_to_equations. nia. }
    eapply evt_mono.
    { eapply (@memalign_spec _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d
                ATSD (a_ctx s) TH (a_top s) (a_bot s) CH sb cnt (max_count c) chunks j0 j1 j2 j3 MP pjunk rz neededA c csz csz8 (Z.min size 4096) CA P cp AB U n id).
      - constructor. repeat split; try reflexivity. { symmetry; exact ECA. } exact ABE.
      - exact MPR.
      - exact MPDJ.
      - exact LO.
      - exact HI.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - split; [exact (proj1 SZ)|]. rewrite ENA. unfold kMaxSize. clear; lia.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T1, T2.   (* [comment removed for export] *)
        clear - B T1 T2 X2; try acb. repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold disj, kSpaceSize, kPageSize in *. clear - D2 D3 TCX; try acb. lia.
      - constructor. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - G1 G2 G3 G4 G5 G6 G10 G12 B; try acb.
        repeat match goal with |- _ /\ _ => split end; first [assumption | (first [clear - G3 G4; lia | lia])].
      - constructor. acb. unfold AHI_LO, kSpaceSize. clear - B S1; try acb. lia.
      - exact CC.
      - exact CR.
      - exact CPS.
      - constructor. split; [exact AB1| exact AB2].
      - constructor. exact ABA.
      - constructor. rewrite ERZ. reflexivity.
      - constructor. unfold kPageSize in TB1. clear - TB1 TB2; try acb. lia.
      - exact DCAP.
      - acb. clear - G11 G13 B; try acb. lia.
      - exact FCH.
      - exact Ha0.
      - exact Ha1.
      - exact Ha2.
      - rewrite TP. apply ienv_of_arep. exact R.
      - exact MI.
      - exact ST.
      - exact QC1.
      - exact QC2.
      - exact QC3.
      - exact QC4.
      - exact QST.
      - exact CHUNK.
      - exact SHK.
      - exact TST.
      - exact UNW.
      - exact DEP.
      - exact PW. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0' & j1' & j2' & j3' & b1 & m1 & m' & -> & MU & WM & MI1 & ST1 &
                    QC1' & QC3' & QC4' & QST' & HDR & B1 & LEFT & FILL & SLACK & SHA & TST' & UNW' & DEP' & UA & MU3 & WM3 & MI' & PW' & ST' & EQM).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m1, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
    split; [eapply arheap_after; eassumption|]. split; [exact DEP'|].
    assert (NB : (exists junk, rw_cells asegs m1 U [CB (Z.to_nat size) junk]) /\ addressable m1 U size) by (eapply new_block; eassumption).
    destruct NB as [NB1 NB2].
    split; [exact NB1|]. split; [exact NB2|]. split; [exact UA|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI'|]. split; [exact PW'|]. split; [exact ST'| exact EQM].
  Qed.

End MemalignHit.

