(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BLFrame BArr BellsX BacX BImage BSysStep BSFModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BazyRestrict BazyLedger BazySR BazyNodes BReach.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepX BsDepotInv BW_DepotFrame BecLazy BecLazy2 BG_MallocModel BG_Malloc2 BG_RepQ BG_WriteSet.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition pendz (st : astate) (XB : list Z) (a : Z) : Prop :=
    exists x, In x XB /\ (x <= a < x + class_size (class_of_addr st x) \/ sh x <= a < sh x + class_size (class_of_addr st x) / 8).

  Definition secgone (s s' : ast) (a : Z) : Prop :=
    exists sc, In sc (as_sec (a_st s)) /\ ~ In sc (as_sec (a_st s'))
               /\ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc \/ sh (sc_map_beg sc) <= a < sh (sc_map_beg sc + sc_map_size sc)).
  Definition avis (s s' : ast) (m m' : mem) : Prop :=
    forall x : word, wview asegs m x <> None -> wview asegs m' x <> None \/ secgone s s' (bv_unsigned x).

  Lemma avis_of_wmono : forall s s' m m', wmono asegs m m' -> avis s s' m m'.
  Proof. intros s s' m m' WM x V. left. exact (WM x V). Qed.
  Lemma avis_of_wmono_out : forall s s' X m m',
    wmono_out X m m' -> (forall iv a, In iv X -> fst iv <= a < snd iv -> secgone s s' a) -> avis s s' m m'.
  Proof.
    intros s s' X m m' WM SUB x V.
    assert (D : outside X (bv_unsigned x) \/ secgone s s' (bv_unsigned x)).
    { clear WM V. induction X as [|[lo' hi'] X IH]; [left; exact I|]. cbn.
      destruct (Z.lt_ge_cases (bv_unsigned x) lo') as [L|G]; [| destruct (Z.lt_ge_cases (bv_unsigned x) hi') as [L2|G2]].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S].
      - right. apply (SUB (lo', hi') (bv_unsigned x)); [left; reflexivity| cbn; lia].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S]. }
    destruct D as [O|S]; [left; exact (WM x O V)| right; exact S].
  Qed.

  Definition alive (st : astate) (a : Z) : Prop :=
    exists ch, In ch (chunk_list st) /\ ch_state ch = CAllocated
               /\ (ch_user_beg ch <= a < ch_user_beg ch + ch_used ch \/ sh (ch_user_beg ch) <= a < sh (ch_user_beg ch) + nsh (ch_used ch)).

  Definition alive_kept (st st' : astate) : Prop :=
    forall ch, In ch (chunk_list st) -> ch_state ch = CAllocated -> In ch (chunk_list st').
  Lemma alive_kept_refl : forall st, alive_kept st st.
  Proof. intros st ch H _. exact H. Qed.
  Lemma alive_kept_trans : forall a b c, alive_kept a b -> alive_kept b c -> alive_kept a c.
  Proof. intros a b c A B ch H E. exact (B ch (A ch H E) E). Qed.
  Lemma alive_mono : forall st st' a, alive_kept st st' -> alive st a -> alive st' a.
  Proof. intros st st' a K (ch & H & E & R). exists ch. split; [exact (K ch H E)|]. exact (conj E R). Qed.
  Lemma agree_alive_trans : forall st0 st1 m0 m1 m2, alive_kept st0 st1 ->
    agree_on (alive st0) m0 m1 -> agree_on (alive st1) m1 m2 -> agree_on (alive st0) m0 m2.
  Proof. intros st0 st1 m0 m1 m2 K A B a Ha Hr. rewrite (B a (alive_mono _ _ a K Ha) Hr). exact (A a Ha Hr). Qed.

  Section Compose.
    Variables (s0 s1 s2 : ast) (d : depot) (lo SP : Z) (m0 m1 m2 : mem) (mo0 mo1 mo2 : Model).
    Hypothesis E1 : a_thr s1 = a_thr s0 /\ a_sb s1 = a_sb s0 /\ a_pa s1 = a_pa s0.
    Hypothesis SUB1 : forall sc, In sc (as_sec (a_st s1)) -> In sc (as_sec (a_st s0)).
    Hypothesis SUB2 : forall sc, In sc (as_sec (a_st s2)) -> In sc (as_sec (a_st s1)).

    Lemma awrit_01_02 : forall a, awrit s0 s1 d lo SP a -> awrit s0 s2 d lo SP a.
    Proof. intros a W. apply (awrit_mono s0 s1 s2 d lo SP a); [| exact W]. intros sc Hsc. right. exact (SUB1 sc Hsc). Qed.
    Lemma awrit_12_02 : forall a, awrit s1 s2 d lo SP a -> awrit s0 s2 d lo SP a.
    Proof.
      intros a W. destruct E1 as (Et & Es & Ep). unfold awrit in W |- *. rewrite Et, Es, Ep in W.
      destruct W as [H|[H|[H|[H|[H|[H|H]]]]]]; [tauto|tauto|tauto|tauto|tauto| |tauto].
      right; right; right; right; right; left. destruct H as (sc & I & R). exists sc. split; [| exact R].
      destruct I as [I|I]; [left; exact (SUB1 sc I)| right; exact I].
    Qed.
    Lemma acompl_trans : acompl s0 s1 d lo SP m0 m1 -> acompl s1 s2 d lo SP m1 m2 -> acompl s0 s2 d lo SP m0 m2.
    Proof.
      intros A B a Ha NW. rewrite (B a Ha) by (intros W; exact (NW (awrit_12_02 a W))). apply (A a Ha). intros W. exact (NW (awrit_01_02 a W)).
    Qed.
    Lemma secgone_01_02 : forall a, secgone s0 s1 a -> secgone s0 s2 a.
    Proof. intros a (sc & I & NI & R). exists sc. split; [exact I|]. split; [intros I2; exact (NI (SUB2 sc I2))| exact R]. Qed.
    Lemma secgone_12_02 : forall a, secgone s1 s2 a -> secgone s0 s2 a.
    Proof. intros a (sc & I & NI & R). exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R]. Qed.
    Lemma avis_trans : avis s0 s1 m0 m1 -> avis s1 s2 m1 m2 -> avis s0 s2 m0 m2.
    Proof.
      intros A B x V. destruct (A x V) as [V1|G]; [| right; exact (secgone_01_02 _ G)].
      destruct (B x V1) as [V2|G]; [left; exact V2| right; exact (secgone_12_02 _ G)].
    Qed.

    Lemma avmx_trans : avmx s0 s1 mo0 mo1 -> avmx s1 s2 mo1 mo2 -> avmx s0 s2 mo0 mo2.
    Proof.
      intros A B x Hx. destruct (A x Hx) as [A1 A2]. split.
      - destruct A1 as [H1|(sc & I & NI & R)].
        + destruct (proj1 (B x H1)) as [H2|(sc & I & NI & R)]; [left; exact H2| right]. exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R].
        + right. exists sc. split; [exact I|]. split; [| exact R]. intros I2. exact (NI (SUB2 sc I2)).
      - intros sc I2 NI. exact (False_ind _ (NI (SUB1 sc (SUB2 sc I2)))).
    Qed.
  End Compose.

  Definition rstep_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : ast) (d : depot) (lo : Z) (m : mem) (mo : Model) (XC' XB' PZ : list Z) (MODEL : astate -> Prop)
      (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ a_AL s' = a_AL s /\ a_sb s' = a_sb s /\ a_pa s' = a_pa s
    /\ (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s)))
    /\ as_cache_inited (a_st s') = true
    /\ (forall c0, 0 <= c0 -> rg_allocated_user (get_region (a_st s') c0) = rg_allocated_user (get_region (a_st s) c0))
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ AREPQ s' XC' XB' m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo'
    /\ nonvm_same mo mo' /\ avmx s s' mo mo' /\ depot_cov d mo'
    /\ DEPOT asegs d m' /\ depot_placed s' d /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avis s s' m m' /\ agree_on (pendz (a_st s) PZ) m m'
    /\ alive_kept (a_st s) (a_st s') /\ agree_on (alive (a_st s)) m m'
    /\ MODEL (a_st s').
End HCW.
