(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BsDepotInv.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section ClientFrame.
  Context {HCEIL : HeapCeil}.
  Variable s : ast.
  Hypothesis OK : ast_ok s.
  Let st := a_st s.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.

  Definition aclient (LB : list (Z * Z)) (SP a : Z) : Prop :=
       SP <= a
    \/ ((0x17e000 <= a < 0x186f48) \/ (0x189858 <= a < 0x18d980) \/ (0x18d988 <= a < 0x18d9d8) \/ (0x6b3690 <= a < 0x6e7248))
    \/ (exists A n, In (A, n) LB /\ A <= a < A + n)
    \/ (exists A n, In (A, n) LB /\ sh A <= a < sh A + nsh n)
    \/ (a_fsb s <= a < a_fsb s + AFS_SIZE) \/ (sh (a_fsb s) <= a < sh (a_fsb s + AFS_SIZE))
    \/ (sh aceil <= a < AHI_LO).
  Definition amframe (LB : list (Z * Z)) (SP : Z) (m m' : mem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient LB SP a -> m' (wa a) = m (wa a).

  Definition apriv (LB : list (Z * Z)) (SP X Y : Z) : Prop := forall a, X <= a < Y -> ~ aclient LB SP a.

  Lemma amframe_of_munch : forall LB SP W m m',
    munch W m m' -> Forall (fun iv => apriv LB SP (fst iv) (snd iv)) W -> amframe LB SP m m'.
  Proof.
    intros LB SP W m m' MU AP a Ha CL. pose proof (MU (wa a)) as E. rewrite wa_unsigned in E by exact Ha. apply E. clear E MU.
    induction W as [|[x y] W IH]; [exact I|]. cbn. apply Forall_cons_iff in AP. destruct AP as [P1 P2]. cbn in P1.
    split; [| exact (IH P2)]. intros R. exact (P1 a R CL).
  Qed.
  Lemma amframe_trans : forall LB SP m1 m2 m3, amframe LB SP m1 m2 -> amframe LB SP m2 m3 -> amframe LB SP m1 m3.
  Proof. intros LB SP m1 m2 m3 A B a Ha CL. rewrite (B a Ha CL). exact (A a Ha CL). Qed.

  Definition bsep (A n X Y : Z) : Prop := A + round_up n 8 <= X \/ Y <= A.

  Variable LB : list (Z * Z).
  Hypothesis HLB : forall b, In b LB -> In b (alb s).

  Let blk : forall A n, In (A, n) LB -> exists ch, In ch (chunk_list st) /\ ch_state ch = CAllocated /\ ch_user_beg ch = A /\ ch_used ch = n.
  Proof. intros A n H. exact (alb_In s A n (HLB _ H)). Qed.

  Lemma bsep_outside : forall X Y, (Y <= a_sb s \/ a_sb s + kSpaceSize <= X) ->
    (forall sc, In sc (as_sec st) -> Y <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= X) ->
    forall A n, In (A, n) LB -> bsep A n X Y.
  Proof.
    intros X Y HS HC A n Hin. destruct (blk A n Hin) as (ch & Hch & _ & <- & <-).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & XP & XS).
    unfold bsep. destruct (ch_primary ch) eqn:E.
    - destruct (XP eq_refl) as (_ & _ & B1 & B2). clear - G2 G4 B1 B2 HS G1; try acb. lia.
    - destruct (XS eq_refl) as (h & Hh & L0 & E0 & A0). destruct (HC h Hh); clear - G2 G4 L0 E0 A0 H G1 X3; try acb; unfold kPageSize in *; lia.
  Qed.

  Lemma bsep_region_hi : forall c, 0 <= c < kNumClasses ->
    forall A n, In (A, n) LB -> bsep A n (RB s c + rg_allocated_user (get_region st c)) (RB s c + kRegionSize).
  Proof.
    intros c Hc A n Hin. destruct (blk A n Hin) as (ch & Hch & _ & <- & <-).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & XP & XS).
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    assert (ERB : forall c', RB s c' = a_sb s + c' * 4294967296) by (intros c'; unfold RB, a_sb; rewrite region_beg_eq; reflexivity).
    pose proof (ro_alloc_nonneg _ _ (WF_region st c WFs Hc)) as AU0. fold st. set (au := rg_allocated_user (get_region st c)) in *.
    unfold bsep, kRegionSize. rewrite (ERB c). destruct (ch_primary ch) eqn:E.
    - destruct (XP eq_refl) as (C & EE & B1 & B2). destruct C as (Hcl & _ & C1 & _ & C3). fold st in C1, C3, EE. rewrite region_beg_eq in C1, C3.
      change (as_space_beg st) with (a_sb s) in C1, C3.
      pose proof (ro_alloc_le _ _ (WF_region st _ WFs Hcl)) as L1. pose proof (ro_mapped_bound _ _ (WF_region st _ WFs Hcl)) as L2.
      unfold kUserMapSize, kFreeArrayOffset in L2.
      destruct (Z.lt_trichotomy (ch_class ch) c) as [LT|[EQ|GT]].
      + left. clear - G2 G4 EE C3 L1 L2 LT AU0; try acb. nia.
      + left. subst c. clear - G2 G4 EE C3; try acb. lia.
      + right. unfold kNumClasses in Hc. clear - G2 C1 GT G1; try acb. nia.
    - destruct (XS eq_refl) as (h & Hh & L0 & E0 & A0). pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
      pose proof (ro_mapped_bound _ _ (WF_region st c WFs Hc)) as L2. pose proof (ro_alloc_le _ _ (WF_region st c WFs Hc)) as L1.
      fold st au in L1, L2. unfold kUserMapSize, kFreeArrayOffset in L2. unfold disj, kSpaceSize, kPageSize, kNumClasses in *.
      clear - G2 G4 L0 E0 A0 D G1 X3 Hc AU0 L1 L2; try acb. destruct D; [left| right]; nia.
  Qed.

  Lemma bsep_apiece : forall X Y, apiece s X Y -> forall A n, In (A, n) LB -> bsep A n X Y.
  Proof.
    intros X Y P A n Hin. destruct (blk A n Hin) as (ch & Hch & AL & <- & <-).
    destruct (apiece_block_sep s OK ch X Y Hch AL P); unfold bsep; [right| left]; assumption.
  Qed.

  Lemma blk_range : forall A n, In (A, n) LB -> AIMG_TOP <= A /\ A mod 8 = 0 /\ 1 <= n /\ n <= round_up n 8 /\ round_up n 8 = 8 * nsh n /\ A + round_up n 8 <= aceil.
  Proof.
    intros A n Hin. destruct (blk A n Hin) as (ch & Hch & _ & <- & <-).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _).
    pose proof (chunk_align s OK ch Hch) as (_ & _ & AL & _).
    repeat split; lia.
  Qed.
  Lemma blk_band : forall A n, In (A, n) LB -> aapp A (round_up n 8).
  Proof.
    intros A n Hin. destruct (blk A n Hin) as (ch & Hch & _ & <- & <-).
    pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _).
    pose proof (ext_band s OK ch Hch) as EB. eapply aapp_sub; [exact EB| lia| lia].
  Qed.

  Definition arng (X Y : Z) : Prop := (4096 <= X /\ Y <= AIMG_LO) \/ (AIMG_TOP <= X /\ Y <= ALOWSH_LO) \/ (AHI_LO <= X /\ Y <= aceil).
  Lemma arng_of_akobj : forall X k, akobj X k -> arng X (X + k).
  Proof. intros X k [H|[H|H]]; unfold arng, alow1, aapp_lo, aapp_hi in *; [left| right; left| right; right]; exact H. Qed.
  Lemma arng_of_aapp : forall X k, aapp X k -> arng X (X + k).
  Proof. intros X k H. apply arng_of_akobj. right. exact H. Qed.
  Lemma arng_hi : forall X Y, AHI_LO <= X -> Y <= aceil -> arng X Y.
  Proof. intros X Y H1 H2. right; right. split; assumption. Qed.
  Lemma arng_sub : forall X Y X' Y', arng X Y -> X <= X' -> Y' <= Y -> arng X' Y'.
  Proof. intros X Y X' Y' H L1 L2. unfold arng in *. lia. Qed.

  Lemma arng_facts : forall X Y, arng X Y -> X <= Y ->
    4096 <= X /\ Y <= aceil /\ (Y <= 0x10000 \/ 0x6e8000 <= X) /\ (Y <= ASHADOW_BASE \/ AHI_LO <= X).
  Proof. intros X Y H L. acb. unfold arng, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, ASHADOW_BASE in *. lia. Qed.

  Let FSB := a_fsb s.
  Let PLF : aapp FSB AFS_SIZE /\ FSB + AFS_SIZE <= aceil.
  Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _). split; assumption. Qed.
  Let PLFE : 7241728 <= FSB /\ FSB + AFS_SIZE <= aceil.
  Proof. exact (aapp_env _ _ (proj1 PLF) ltac:(unfold AFS_SIZE; lia)). Qed.

  Let PLFS : FSB + AFS_SIZE <= ASHADOW_BASE \/ AHI_LO <= FSB.
  Proof. pose proof (proj1 PLF) as F. clear - F. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, ASHADOW_BASE in *. lia. Qed.

  Lemma apriv_stack : forall lo SP, aceil <= lo -> apriv LB SP lo SP.
  Proof.
    intros lo SP LO a Ha CL. unfold aclient in CL. acb. unfold AFS_SIZE, AHI_LO in *.
    destruct CL as [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|[C|[C|C]]]]]].
    - lia. - lia.
    - pose proof (blk_range A n Hin) as B. acb. unfold AIMG_TOP in B. lia.
    - pose proof (blk_range A n Hin) as B. acb.
      pose proof (sh_hi A (nsh n) ltac:(hci; unfold AIMG_TOP in B; lia) ltac:(hci; acb; lia)). unfold AHI_LO in *. lia.
    - unfold FSB in *. lia.
    - pose proof (sh_mono FSB (FSB + 11571200) ltac:(hci; lia)). pose proof (sh_hi (FSB + 11571200) 0 ltac:(hci; lia) ltac:(hci; acb; unfold FSB in *; lia)).
      unfold FSB, AHI_LO in *. lia.
    - lia.
  Qed.

  Lemma apriv_app : forall SP X Y, arng X Y -> Y <= SP ->
    (forall A n, In (A, n) LB -> bsep A n X Y) -> (Y <= FSB \/ FSB + AFS_SIZE <= X) -> apriv LB SP X Y.
  Proof.
    intros SP X Y HR HSP HB HF a Ha CL.
    pose proof (arng_facts X Y HR ltac:(lia)) as (HX & HY & HIMG & HSH). clear HR.
    unfold aclient in CL. acb. unfold AFS_SIZE, AHI_LO, ASHADOW_BASE in *.
    destruct CL as [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|[C|[C|C]]]]]].
    - lia. - lia.
    - pose proof (blk_range A n Hin) as B. destruct (HB A n Hin); lia.
    - pose proof (blk_range A n Hin) as B. acb.
      pose proof (sh_hi A (nsh n) ltac:(hci; unfold AIMG_TOP in B; lia) ltac:(hci; acb; lia)).
      pose proof (sh_lo A ltac:(hci; unfold AIMG_TOP in B; lia)). unfold AHI_LO, ASHADOW_BASE in *. lia.
    - unfold FSB in *. lia.
    - pose proof (sh_hi (a_fsb s + 11571200) 0 ltac:(hci; unfold FSB in *; lia) ltac:(hci; acb; unfold FSB in *; lia)).
      pose proof (sh_lo (a_fsb s) ltac:(hci; unfold FSB in *; lia)). unfold FSB, AHI_LO, ASHADOW_BASE in *. lia.
    - unfold sh, ASHADOW_BASE in C. lia.
  Qed.

  Lemma apriv_shadow : forall SP X Y, arng X Y -> X <= Y -> X mod 8 = 0 -> aceil <= SP ->
    (forall A n, In (A, n) LB -> bsep A n X Y) -> (Y <= FSB \/ FSB + AFS_SIZE <= X) -> apriv LB SP (sh X) (sh X + (Y - X) / 8).
  Proof.
    intros SP X Y HR HXY X8 HSP HB HF a Ha CL.
    pose proof (arng_facts X Y HR HXY) as (HX & HY & HIMG & HSH). clear HR.
    unfold aclient in CL. acb. unfold AFS_SIZE, AHI_LO in *.
    rewrite (sh_diff8 X Y X8) in Ha.
    pose proof (sh_hi Y 0 ltac:(hci; lia) ltac:(hci; acb; lia)) as YH.
    pose proof (sh_lo X ltac:(hci; lia)) as XL. unfold AHI_LO, ASHADOW_BASE in *.
    destruct CL as [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|[C|[C|C]]]]]].
    - lia. - lia.
    - pose proof (blk_range A n Hin) as B. pose proof (blk_band A n Hin) as BB.
      clear - B BB C Ha YH XL. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in BB. lia.
    - pose proof (blk_range A n Hin) as (B1 & B2 & B3 & B4 & B5 & B6). destruct (HB A n Hin) as [D|D].
      + pose proof (sh_mono _ _ D) as M. rewrite B5, (sh_add8 A (nsh n) B2) in M. lia.
      + pose proof (sh_mono _ _ D) as M. lia.
    - unfold FSB in *. lia.
    - destruct HF as [D|D].
      + pose proof (sh_mono _ _ D). unfold FSB in *. lia.
      + pose proof (sh_mono _ _ D). unfold FSB in *. lia.
    - pose proof (sh_mono Y aceil ltac:(hci; lia)). lia.
  Qed.

  Lemma apriv_static : forall SP X Y, Y <= AIMG_TOP -> aceil <= SP ->
    (Y <= 0x17e000 \/ (0x186f48 <= X /\ Y <= 0x189858) \/ (0x18d980 <= X /\ Y <= 0x18d988) \/ (0x18d9d8 <= X /\ Y <= 0x6b3690) \/ 0x6e7248 <= X) ->
    apriv LB SP X Y.
  Proof.
    intros SP X Y HY HSP HR a Ha CL. unfold aclient in CL. acb. unfold AFS_SIZE, AHI_LO, AIMG_TOP in *.
    destruct CL as [C|[C|[(A & n & Hin & C)|[(A & n & Hin & C)|[C|[C|C]]]]]].
    - lia. - lia.
    - pose proof (blk_range A n Hin) as B. unfold AIMG_TOP in B. lia.
    - pose proof (blk_range A n Hin) as B. pose proof (sh_lo A ltac:(hci; unfold AIMG_TOP in B; lia)). unfold ASHADOW_BASE in *. lia.
    - unfold FSB in *. lia.
    - pose proof (sh_lo (a_fsb s) ltac:(hci; unfold FSB in *; lia)). unfold ASHADOW_BASE, FSB in *. lia.
    - pose proof (sh_lo aceil ltac:(hci; lia)). unfold ASHADOW_BASE in *. lia.
  Qed.

  Lemma bsep_mono : forall A n X Y X' Y', X <= X' -> Y' <= Y -> bsep A n X Y -> bsep A n X' Y'.
  Proof. intros A n X Y X' Y' H1 H2 [B|B]; [left| right]; lia. Qed.
  Lemma apriv_mono : forall SP X Y X' Y', X <= X' -> Y' <= Y -> apriv LB SP X Y -> apriv LB SP X' Y'.
  Proof. intros SP X Y X' Y' H1 H2 P a Ha. apply P. lia. Qed.

  Let PLN : 4096 <= a_thr s /\ a_thr s + 4096 <= aceil /\ 0x10007fff8000 <= a_sb s /\ a_sb s + 137438953472 + 4096 <= aceil
            /\ 7241728 <= a_pa s /\ a_pa s + 8388608 <= aceil /\ 7241728 <= FSB /\ FSB + 11571200 <= aceil
            /\ (a_sb s + 137438953472 + 4096 <= FSB \/ FSB + 11571200 <= a_sb s) /\ (a_pa s + 8388608 <= FSB \/ FSB + 11571200 <= a_pa s)
            /\ (a_thr s + 4096 <= FSB \/ FSB + 11571200 <= a_thr s) /\ a_sb s mod 65536 = 0.
  Proof.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & _).
    pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; lia)) as TE. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; lia)) as PE.
    unfold FSB. unfold disj, a_sb, AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve, AFS_SIZE in *. acb.
    clear - S1 S2 S3 PE P3 TE T3 PLFE F2 D6 D7 D8; try acb. unfold AFS_SIZE, a_sb in *. repeat split; lia.
  Qed.
  Let PLB : akobj (a_thr s) kPageSize /\ aapp (a_pa s) kPtrArrayReserve.
  Proof. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & _). split; assumption. Qed.

  Lemma apriv_thread : forall SP X Y, a_thr s <= X -> Y <= a_thr s + kPageSize -> X <= Y -> aceil <= SP -> apriv LB SP X Y.
  Proof.
    intros SP X Y H1 H2 H3 H4. acb.
    apply apriv_app; [| unfold kPageSize in *; clear - H2 H4 PLN; try acb; lia| |].
    - eapply arng_sub; [apply arng_of_akobj; exact (proj1 PLB)| exact H1| exact H2].
    - intros A n Hin. apply (bsep_mono A n (a_thr s) (a_thr s + kPageSize)); [exact H1| exact H2| exact (bsep_apiece _ _ (ap_thread s) A n Hin)].
    - unfold AFS_SIZE, kPageSize in *. clear - H1 H2 PLN; try acb. lia.
  Qed.

  Lemma apriv_rinfo : forall SP X Y, a_ri s <= X -> Y <= a_ri s + kPageSize -> X <= Y -> aceil <= SP -> apriv LB SP X Y.
  Proof.
    intros SP X Y H1 H2 H3 H4. unfold a_ri, kSpaceSize, kPageSize in *. acb.
    apply apriv_app; [apply arng_hi; [unfold AHI_LO; clear - H1 PLN; try acb; lia| acb; clear - H2 PLN; try acb; lia]| clear - H2 H4 PLN; try acb; lia| |].
    - intros A n Hin. apply (bsep_mono A n (a_ri s) (a_ri s + kPageSize)); [unfold a_ri, kSpaceSize; exact H1| unfold a_ri, kSpaceSize, kPageSize; exact H2| exact (bsep_apiece _ _ (ap_rinfo s) A n Hin)].
    - unfold AFS_SIZE. clear - H1 H2 PLN; try acb. lia.
  Qed.

  Lemma apriv_ptrarr : forall SP X Y, a_pa s <= X -> Y <= a_pa s + kPtrArrayReserve -> X <= Y -> aceil <= SP -> apriv LB SP X Y.
  Proof.
    intros SP X Y H1 H2 H3 H4. acb.
    apply apriv_app; [| unfold kPtrArrayReserve in *; clear - H2 H4 PLN; try acb; lia| |].
    - eapply arng_sub; [apply arng_of_aapp; exact (proj2 PLB)| exact H1| exact H2].
    - intros A n Hin. apply (bsep_mono A n (a_pa s) (a_pa s + kPtrArrayReserve)); [exact H1| exact H2| exact (bsep_apiece _ _ (ap_ptrarr s) A n Hin)].
    - unfold AFS_SIZE, kPtrArrayReserve in *. clear - H1 H2 PLN; try acb. lia.
  Qed.

  Lemma apriv_region_hi : forall SP c X Y, 0 <= c < kNumClasses -> RB s c + rg_allocated_user (get_region st c) <= X -> Y <= RB s c + kRegionSize ->
    X <= Y -> aceil <= SP -> apriv LB SP X Y.
  Proof.
    intros SP c X Y Hc H1 H2 H3 H4. pose proof (region_in_space st c Hc) as [R1 R2]. change (as_space_beg st) with (a_sb s) in R1, R2. change (region_beg st c) with (RB s c) in R1, R2.
    pose proof (ro_alloc_nonneg _ _ (WF_region st c WFs Hc)) as A0. fold st in H1. unfold kRegionSize in *. acb.
    apply apriv_app; [apply arng_hi; [unfold AHI_LO; clear - H1 PLN R1 A0; try acb; lia| acb; clear - H2 PLN R2; try acb; unfold kSpaceSize in *; lia]| clear - H2 H4 PLN R2; try acb; unfold kSpaceSize in *; lia| |].
    - intros A n Hin. apply (bsep_mono A n (RB s c + rg_allocated_user (get_region st c)) (RB s c + kRegionSize)); [exact H1| exact H2| exact (bsep_region_hi c Hc A n Hin)].
    - unfold AFS_SIZE. clear - H1 H2 PLN R1 R2 A0; try acb. unfold kSpaceSize in *. lia.
  Qed.
  Lemma apriv_region_hi_sh : forall SP c X Y, 0 <= c < kNumClasses -> RB s c + rg_allocated_user (get_region st c) <= X -> Y <= RB s c + kRegionSize ->
    X <= Y -> X mod 8 = 0 -> aceil <= SP -> apriv LB SP (sh X) (sh X + (Y - X) / 8).
  Proof.
    intros SP c X Y Hc H1 H2 H3 X8 H4. pose proof (region_in_space st c Hc) as [R1 R2]. change (as_space_beg st) with (a_sb s) in R1, R2. change (region_beg st c) with (RB s c) in R1, R2.
    pose proof (ro_alloc_nonneg _ _ (WF_region st c WFs Hc)) as A0. fold st in H1. unfold kRegionSize in *. acb.
    apply apriv_shadow; [apply arng_hi; [unfold AHI_LO; clear - H1 PLN R1 A0; try acb; lia| acb; clear - H2 PLN R2; try acb; unfold kSpaceSize in *; lia]| exact H3| exact X8| acb; exact H4| |].
    - intros A n Hin. apply (bsep_mono A n (RB s c + rg_allocated_user (get_region st c)) (RB s c + kRegionSize)); [exact H1| exact H2| exact (bsep_region_hi c Hc A n Hin)].
    - unfold AFS_SIZE. clear - H1 H2 PLN R1 R2 A0; try acb. unfold kSpaceSize in *. lia.
  Qed.

  Lemma apriv_freech : forall SP c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    aceil <= SP -> apriv LB SP (compact_to_addr st c cp) (compact_to_addr st c cp + class_size c).
  Proof.
    intros SP c cp Hc Hin H4.
    assert (CV : carved st c (compact_to_addr st c cp)) by (destruct Hin as [Hin|Hin]; [apply carved_free| apply carved_cache]; assumption).
    pose proof (carved_in_space s OK c _ CV) as (C1 & C2 & C3). acb.
    apply apriv_app; [apply arng_hi; [unfold AHI_LO; clear - C1 PLN; try acb; lia| acb; clear - C2 PLN; try acb; unfold kSpaceSize in *; lia]| clear - C2 H4 PLN; try acb; unfold kSpaceSize in *; lia| |].
    - intros A n HinB. exact (bsep_apiece _ _ (ap_freech s c cp Hc Hin) A n HinB).
    - unfold AFS_SIZE. clear - C1 C2 PLN; try acb. unfold kSpaceSize in *. lia.
  Qed.
  Lemma apriv_freech_sh : forall SP c cp, 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    aceil <= SP -> apriv LB SP (sh (compact_to_addr st c cp)) (sh (compact_to_addr st c cp) + class_size c / 8).
  Proof.
    intros SP c cp Hc Hin H4.
    assert (CV : carved st c (compact_to_addr st c cp)) by (destruct Hin as [Hin|Hin]; [apply carved_free| apply carved_cache]; assumption).
    pose proof (carved_in_space s OK c _ CV) as (C1 & C2 & C3). pose proof CV as (_ & _ & CVa & CVm & _). rewrite region_beg_eq in CVa, CVm.
    pose proof (class_size_table_facts c Hc) as (T1 & T2 & T3 & _).
    acb. change (as_space_beg st) with (a_sb s) in CVa, CVm.
    replace (class_size c / 8) with ((compact_to_addr st c cp + class_size c - compact_to_addr st c cp) / 8) by (f_equal; lia).
    apply apriv_shadow; [apply arng_hi; [unfold AHI_LO; clear - C1 PLN; try acb; lia| acb; clear - C2 PLN; try acb; unfold kSpaceSize in *; lia]| clear - C3; try acb; lia| | acb; exact H4| |].
    - destruct PLN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). pose proof CV as (_ & CS0 & _). set (ab := compact_to_addr st c cp) in *.
      assert (M1 : (ab - (a_sb s + c * 2 ^ 32)) mod 8 = 0) by (apply (mod8_of (class_size c)); [clear - T2; try acb; Z.div_mod_to_equations; lia| exact CS0| exact CVm]).
      replace ab with ((ab - (a_sb s + c * 2 ^ 32)) + (a_sb s + c * 2 ^ 32)) by (clear; lia). apply mod8_add; [exact M1|]. clear - S16; try acb. Z.div_mod_to_equations. lia.
    - intros A n HinB. exact (bsep_apiece _ _ (ap_freech s c cp Hc Hin) A n HinB).
    - unfold AFS_SIZE. clear - C1 C2 PLN; try acb. unfold kSpaceSize in *. lia.
  Qed.

  Lemma apriv_depot_statics : forall SP, aceil <= SP -> apriv LB SP 2567960 6762288 /\ apriv LB SP 2502408 2502436.
  Proof. intros SP H. split; (apply apriv_static; [clear; unfold AIMG_TOP; lia| exact H| clear; lia]). Qed.
  Lemma apriv_inst : forall SP X Y, AINST <= X -> Y <= AINST + 4096 -> aceil <= SP -> apriv LB SP X Y.
  Proof. intros SP X Y H1 H2 H. apply apriv_static; [unfold AINST, AIMG_TOP in *; clear - H2; try acb; lia| exact H| unfold AINST in *; clear - H1 H2; try acb; lia]. Qed.

  Lemma apriv_depot_blocks : forall SP nb sbd,
    aapp nb (16 * 65536) -> aapp sbd (8 * 32768) ->
    disj (a_sb s) (kSpaceSize + kPageSize) nb (16 * 65536) -> disj (a_sb s) (kSpaceSize + kPageSize) sbd (8 * 32768) ->
    (forall sc, In sc (as_sec st) -> disj (sc_map_beg sc) (sc_map_size sc) nb (16 * 65536) /\ disj (sc_map_beg sc) (sc_map_size sc) sbd (8 * 32768)) ->
    disj FSB AFS_SIZE nb (16 * 65536) -> disj FSB AFS_SIZE sbd (8 * 32768) ->
    aceil <= SP -> apriv LB SP nb (nb + 16 * 65536) /\ apriv LB SP sbd (sbd + 8 * 32768).
  Proof.
    intros SP nb sbd NB SBB DN DB DS FN FB H.
    pose proof (aapp_env _ _ NB ltac:(lia)) as [N1 N2]. pose proof (aapp_env _ _ SBB ltac:(lia)) as [B1 B2].
    unfold disj, kSpaceSize, kPageSize, AFS_SIZE in *. acb. split.
    - apply apriv_app; [apply arng_of_aapp; exact NB| clear - N2 H; try acb; lia| | unfold AFS_SIZE; clear - FN; try acb; lia].
      intros A n Hin. apply (bsep_outside nb (nb + 16 * 65536)); [clear - DN; try acb; unfold kSpaceSize; lia| | exact Hin].
      intros sc Hsc. destruct (DS sc Hsc) as [D _]. clear - D; try acb. lia.
    - apply apriv_app; [apply arng_of_aapp; exact SBB| clear - B2 H; try acb; lia| | unfold AFS_SIZE; clear - FB; try acb; lia].
      intros A n Hin. apply (bsep_outside sbd (sbd + 8 * 32768)); [clear - DB; try acb; unfold kSpaceSize; lia| | exact Hin].
      intros sc Hsc. destruct (DS sc Hsc) as [_ D]. clear - D; try acb. lia.
  Qed.
End ClientFrame.
