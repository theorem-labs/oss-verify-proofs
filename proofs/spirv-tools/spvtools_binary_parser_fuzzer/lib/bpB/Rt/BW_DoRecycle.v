(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts2 BsAtomics BsDepotInv BllocWalkKit BW_IAInit BW_MergeBatches BW_Recycle.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

  Definition dr_frame (m : mem) (spv : Z) (j0 : list byte) (ca cs s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : Prop :=
    rw_cells asegs m spv [CB 8 j0; C8 ca; C8 cs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Section DoRecycle.

    Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

    Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (ca cs : word).
    Variables (lo : Z) (l : list qbatch).
    Let spv := bv_unsigned sp.
    Let T0 := spv + 112.
    Hypothesis LO : aceil <= lo. Hypothesis HI : lo + 800 <= spv. Hypothesis SPT : T0 + 96 <= 2^47.
    Hypothesis OKL : Forall bok l.
    Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.

    Let FRAME (m : mem) (j0 : list byte) : Prop := dr_frame m spv j0 ca cs s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (wz 0x9447c).

    Definition dr_head_mem (m : mem) (T : list qbatch) (j0 : list byte) : Prop :=
         rw_cells asegs m T0 [C8 (wz (zlen T)); C8 (wz (hd 0 (map qb_addr T))); C8 (wz (last (map qb_addr T) 0)); C8 (wz (bsum T))]
      /\ bseg m T 0
      /\ FRAME m j0.

    Definition dr_head_ms (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word) (T : list qbatch) (pc : Z) (m : mem) : machine_state :=
      MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (zlen T)) a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) x4 (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

    Definition dr_exit_post (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state -> Prop :=
      fun ms' => ms' = MS (mkR (wz 0x9447c) (Z_to_bv 64 T0) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9447c) fc None m (seg_rom asegs)
                 /\ stk asegs m lo T0.

    Ltac dr_lits :=
      unfold AINST, OI_Q, wz in *;
      replace (1628632 + 64) with 1628696 in * by reflexivity; replace (1628632 + 688) with 1629320 in * by reflexivity;
      replace (1628632 + 32) with 1628664 in * by reflexivity; replace (1628632 + 728) with 1629360 in * by reflexivity.

    Let FWT : forall L, Forall (ifar l L) [(T0, T0 + 32)]%Z.
    Proof. intros L. constructor; [unfold ifar; right; left; unfold T0 in *; unfold spv in *; clear - LO HI; lia| constructor]. Qed.
    Let FPT : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(T0, T0 + 32)]%Z.
    Proof. constructor; [cbn [fst snd]; right; unfold T0 in *; unfold spv in *; clear - LO HI; pose proof aceil_range; unfold AHI_LO; lia| constructor]. Qed.
    Let FWF : forall L, Forall (ifar l L) [(spv, T0)]%Z.
    Proof. intros L. constructor; [unfold ifar; right; left; unfold T0 in *; unfold spv in *; clear - LO HI; lia| constructor]. Qed.

    Definition dr_entry_post (m : mem) (T : list qbatch) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state -> Prop :=
      fun ms' => exists (a1' : word) (j0 : list byte) m',
        ms' = (match T with
               | [] => MS (mkR (wz 0x9447c) (Z_to_bv 64 T0) gp tp t0 t1 t2 s0 s1 (wz 0) a1' ca cs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9447c) fc None m' (seg_rom asegs)
               | _ => dr_head_ms (wz 0x9447c) t0 t1 t2 a1' ca cs a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 T 0x946ec m'
               end)
        /\ munch [(spv, T0)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' T0 [C8 (wz (zlen T)); C8 (wz (hd 0 (map qb_addr T))); C8 (wz (last (map qb_addr T) 0)); C8 (wz (bsum T))]
        /\ bseg m' T 0
        /\ match T with [] => stk asegs m' lo T0 | _ => stk asegs m' lo spv /\ FRAME m' j0 end.

    Lemma dr_entry : forall (T : list qbatch) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
      mem_inv asegs m -> stk asegs m lo T0 -> Forall bok T -> (forall x, In x T -> In (qb_addr x) (map qb_addr l)) -> bsum T < 2^62 ->
      rw_cells asegs m T0 [C8 (wz (zlen T)); C8 (wz (hd 0 (map qb_addr T))); C8 (wz (last (map qb_addr T) 0)); C8 (wz (bsum T))] ->
      bseg m T 0 ->
      evt asegs (dr_entry_post m T t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6)
        (MS (mkR (wz 0x9447c) (Z_to_bv 64 T0) gp tp t0 t1 t2 s0 s1 (wz (AINST + OI_Q)) (Z_to_bv 64 T0) ca cs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x94674) fc None m (seg_rom asegs)).
    Proof.
      intros until m. intros MI ST OKT SUBT BS HT BST.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      assert (Z0 : 0 <= zlen T) by (unfold zlen; clear; lia). pose proof (bsum_nonneg T OKT) as BT0. pose proof (bsum_len T OKT) as LT. unfold kBatchSize in LT.
      pose proof (munch_refl [(spv, T0)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
      unfold FRAME, dr_frame, dr_head_ms. unfold T0 in *; unfold spv in *. dr_lits. unfold kBatchSize, kSpaceSize, AHI_LO, AIMG_TOP in *. acb.

      step. carve_frame 112%nat ST.
      lazymatch goal with FRu : rw_cells _ _ ?adr [CB 112 ?j] |- _ =>
        replace adr with (bv_unsigned sp) in FRu by (clear; lia);
        let J := fresh "J" in remember j as J in FRu;
        apply (rw_cells_split_CB asegs _ _ [] 112 J [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FRu; [| reflexivity]; cbn [mk_CB_cells app] in FRu;
        repeat match type of FRu with context [CB ?k (take ?i ?l0)] => let X := fresh "jk" in remember (take i l0) as X in FRu end;
        repeat match type of FRu with context [CB ?k (drop ?i ?l0)] => let X := fresh "jk" in remember (drop i l0) as X in FRu end;
        repeat match goal with H' : _ = take _ _ |- _ => clear H' | H' : _ = drop _ _ |- _ => clear H' | H' : _ = J |- _ => clear H' end;
        rename FRu into FR
      end.
      try rewrite Z.add_0_r in ST.
      do 11 st1. step. step. step.

      pose proof (munch_agree _ _ _ MU) as AGL.
      step. if_cases K; zify_cond K.
      -
        destruct T as [|b T']. 2: { exfalso. revert K. rewrite zlen_cons'. rewrite ?unsigned_lit by (rewrite bsum_cons in *; pose proof (bsum_nonneg T' ltac:(apply Forall_cons_iff in OKT; exact (proj2 OKT))); clear - Z0 LT BS H; unfold zlen in *; cbn [length] in *; lia). unfold zlen. clear. lia. }
        clear K. cbn [zlen length Z.of_nat map hd last bsum fold_right] in HT |- *.

        do 11 step. step. release_frame FR ST (bv_unsigned sp + 112). step.
        pose proof (munch_agree _ _ _ MU) as AGL2.
        apply evt_done. unfold dr_entry_post. exists (Z_to_bv 64 T0), []. eexists. split; [cbn [zlen length Z.of_nat]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HT|]. split; [exact I| exact ST].
      - destruct T as [|b T']. { exfalso. apply K. reflexivity. } clear K.

        step. step. step. step. step. step. step. litx. step.
        apply evt_done. unfold dr_entry_post, dr_head_ms. do 2 eexists. eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HT|].
        split; [eapply (bseg_far l OKL PW _ m); [apply FWF| exact OKT| exact SUBT| exact AGL| exact WM| exact BST]|].
        split; [assumption| exact FR].
    Qed.

    Definition dr_deq_post (m : mem) (b : qbatch) (T' : list qbatch) (j0 : list byte) (rax t0 t1 t2 a2 a3 a4 a5 a6 a7 x7 x8 x9 t3 t4 t5 t6 : word) : machine_state -> Prop :=
      fun ms' => exists m',
        ms' = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (qb_size b)) (wz (bsum T')) a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize)
                      (wz (qb_count b)) (if qb_count b =? 0 then x7 else wz (qb_addr b + 152)) (if qb_count b =? 0 then x8 else wz (qb_count b + 16)) (if qb_count b =? 0 then x9 else wz 16) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 (if qb_count b =? 0 then 0x94744 else 0x9472c)) fc None m' (seg_rom asegs)
        /\ munch [(T0, T0 + 32)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' T0 [C8 (wz (zlen T')); C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (last (map qb_addr T') 0)); C8 (wz (bsum T'))]
        /\ bseg m' T' 0
        /\ FRAME m' j0
        /\ rw_cells asegs m' (qb_addr b) [C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
        /\ u64arr asegs m' (qb_addr b + 24) (wlist (qb_chunks b))
        /\ stk asegs m' (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize)
        /\ poisoned m' (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.

    Lemma dr_deq : forall (b : qbatch) (T' : list qbatch) (j0 : list byte) (rax x4 x6 x7 x8 x9 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
      mem_inv asegs m -> Forall bok (b :: T') -> (forall x, In x (b :: T') -> In (qb_addr x) (map qb_addr l)) -> List.NoDup (map qb_addr (b :: T')) ->
      bsum (b :: T') < 2^62 ->
      dr_head_mem m (b :: T') j0 ->
      evt asegs (dr_deq_post m b T' j0 rax t0 t1 t2 a2 a3 a4 a5 a6 a7 x7 x8 x9 t3 t4 t5 t6)
        (dr_head_ms rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 (b :: T') 0x946ec m).
    Proof.
      intros until m. intros MI OKT SUB ND BS (HT & BST & FR).
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      apply Forall_cons_iff in OKT. destruct OKT as [OKB OKT']. pose proof OKB as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      cbn [bseg] in BST. destruct BST as [BB BST'].
      pose proof (batch_open m b _ OKB BB) as (BC & BA & BJ & BP). clear BB.
      assert (INB : In (qb_addr b) (map qb_addr l)) by (apply (SUB b); left; reflexivity).
      assert (SUBT : forall x, In x T' -> In (qb_addr x) (map qb_addr l)) by (intros x Hx; apply SUB; right; exact Hx).
      assert (Z0 : 0 <= zlen T') by (unfold zlen; clear; lia).
      pose proof (bsum_nonneg T' OKT') as BT0. pose proof (bsum_len T' OKT') as LT'. unfold kBatchSize in LT'.
      assert (LENB : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in B5; clear - B5; lia).
      rewrite bsum_cons in BS. rewrite zlen_cons', bsum_cons in *. cbn [map hd] in HT, ND |- *.
      pose proof (proj1 (proj1 (NoDup_cons_iff _ _) ND)) as NIB.
      assert (NTB : forall x, In x T' -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; rewrite <- E; apply in_map; exact Hx).
      pose proof (munch_refl [(T0, T0 + 32)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
      unfold FRAME, dr_frame in FR. unfold dr_head_ms. unfold T0 in *; unfold spv in *. dr_lits. unfold kBatchSize, kBatchCount, kSpaceSize, AHI_LO, AIMG_TOP in *. acb.

      step. step. step.
      step. if_cases Kn; zify_cond Kn;
        [ destruct T' as [|c T'']; cbn [map hd last] in Kn, HT |- *; [exfalso; apply Kn; reflexivity| clear Kn]
        | destruct T' as [|c T'']; cbn [map hd last] in Kn, HT |- *;
          [   st1; clear Kn
          | exfalso; apply Forall_cons_iff in OKT'; destruct OKT' as [(C1 & C2 & _) _]; unfold AHI_LO, kBatchSize in C1, C2;
            revert Kn; rewrite ?unsigned_lit, ?land64_id by (clear - C1 C2 ACEILB; lia); clear - C1; intros Kn; lia ] ].

      all: step; step; step; step; step; step; step.
      all: lazymatch type of BST' with bseg _ ?r 0 =>
             lazymatch type of HT with rw_cells _ _ _ (C8 (Z_to_bv 64 ?z) :: _) =>
               replace z with (zlen r) in HT by (rewrite ?zlen_cons'; unfold zlen; cbn [length]; clear; lia) end;
             rewrite !unsigned_lit in HT by (clear - BS BT0 B6 LT'; rewrite ?bsum_cons in *; unfold zlen in *; cbn [length] in *; lia);
             replace (qb_size b + bsum r - qb_size b) with (bsum r) in HT by (clear; lia);
             rewrite !unsigned_lit by (clear - BS BT0 B6 LT'; rewrite ?bsum_cons in *; unfold zlen in *; cbn [length] in *; lia);
             replace (qb_size b + bsum r - qb_size b) with (bsum r) by (clear; lia)
           end.

      all: pose proof (munch_agree _ _ _ MU) as AGL.
      all: step; if_cases Kc; zify_cond Kc; rewrite ?unsigned_lit, ?land64_id in Kc by (clear - B4; lia); [| step; step; step].
      all: apply evt_done; unfold dr_deq_post, FRAME, dr_frame; unfold kBatchSize, AINST, wz;
           first [ rewrite (proj2 (Z.eqb_eq _ _) Kc) | rewrite (proj2 (Z.eqb_neq _ _) Kc) ]; cbv iota;
           replace (1628632 + 64) with 1628696 by reflexivity; replace (1628632 + 688) with 1629320 by reflexivity;
           eexists; split; [reflexivity|];
           split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HT|];
           split; [eapply (bseg_far l OKL PW _ m); [apply FWT| exact OKT'| exact SUBT| exact AGL| exact WM| exact BST']|];
           split; [exact FR|]; split; [exact BC|]; split; [exact BA|]; split; [exact BJ|];
           eapply (pois_far2 _ m _ b); [exact FPT| exact OKB| exact AGL| exact WM| exact BP].
    Qed.

    Lemma dr_call_chunk : forall (B i cnt mi : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6 : word) (m : mem),
      mem_inv asegs m -> AHI_LO <= B -> B + kBatchSize <= aceil -> 0 <= i < cnt -> cnt <= kBatchCount -> 0 <= mi < 2^64 ->
      rw_cells asegs m (B + 24 + 8 * i) [C8 (wz mi)] ->
      evt asegs (fun ms' => ms' = MS (mkR (wz 0x94738) sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (Z_to_bv 64 (spv + 8)) (wz mi) a2 a3 a4 a5 a6 a7
                                         (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6 (wz (B + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6
                 (wz (B + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9472c) fc None m (seg_rom asegs)).
    Proof.
      intros until m. intros MI B1 B2 IR CR MR CELL.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      unfold T0 in *; unfold spv in *. dr_lits. unfold kBatchSize, kBatchCount, kSpaceSize, AHI_LO in *. acb.

      replace (B + 24 + 8 * i) with (B + 152 + 8 * i + -128) in CELL by (clear; lia).
      step. step. step.
      apply evt_done. reflexivity.
    Qed.

    Lemma dr_next_chunk : forall (B i cnt : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6 : word) (m : mem),
      0 <= i < cnt -> cnt <= kBatchCount -> 0 <= B -> B + kBatchSize <= 2^64 ->
      evt asegs (fun ms' => ms' = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7
                                         (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6 (wz (B + 152 + 8 * (i + 1))) (wz (cnt + 16)) (wz (16 + (i + 1))) s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 (if i + 1 =? cnt then 0x94744 else 0x9472c)) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6
                 (wz (B + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x94738) fc None m (seg_rom asegs)).
    Proof.
      intros until m. intros IR CR B0 B1.
      dr_lits. unfold kBatchSize, kBatchCount, kSpaceSize in *.

      step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - IR CR B0 B1; lia).
      - replace (i + 1 =? cnt) with false by (symmetry; apply Z.eqb_neq; clear - K; lia).
        apply evt_done. replace (B + 152 + 8 * i + 8) with (B + 152 + 8 * (i + 1)) by (clear; lia). replace (16 + i + 1) with (16 + (i + 1)) by (clear; lia). reflexivity.
      - replace (i + 1 =? cnt) with true by (symmetry; apply Z.eqb_eq; clear - K; lia).
        apply evt_done. replace (B + 152 + 8 * i + 8) with (B + 152 + 8 * (i + 1)) by (clear; lia). replace (16 + i + 1) with (16 + (i + 1)) by (clear; lia). reflexivity.
    Qed.

    Lemma dr_class_id : forall c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
      Z.shiftr ((c * 2^32 + off) * 2^27) 59 = c /\ 0 <= (c * 2^32 + off) * 2^27 < 2^64.
    Proof.
      intros c off Hc Hoff. rewrite Z.shiftr_div_pow2 by lia.
      replace ((c * 2^32 + off) * 2^27) with (off * 2^27 + c * 2^59) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by nia. split; [lia| nia].
    Qed.

    Lemma dr_call_batch : forall (B sb c off : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word) (j0 : list byte) (m : mem),
      mem_inv asegs m -> AHI_LO <= sb -> sb + kSpaceSize + kPageSize <= aceil -> 0 <= c < 32 -> 0 <= off < 2^32 -> B = sb + c * 2^32 + off ->
      rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] -> FRAME m j0 ->
      evt asegs (fun ms' => ms' = MS (mkR (wz 0x94770) sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) ca (wz AINST) (wz c) (wz B) a4 a5 a6 a7
                                         (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x94bb0) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz B) (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x94744) fc None m (seg_rom asegs)).
    Proof.
      intros until m. intros MI S1 S2 HC HO EB SB32 FR.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (bv_unsigned_in_range _ ca) as CAR; change (bv_modulus 64) with (2^64)%Z in CAR.
      unfold FRAME, dr_frame in FR. unfold T0 in *; unfold spv in *. unfold OI_SPACEBEG in SB32. dr_lits. unfold kBatchSize, kSpaceSize, kPageSize, AHI_LO in *. acb.

      step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - S1 S2 HC HO EB ACEILB; lia). clear - HC HO EB. intros K. nia. } clear K.
      step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - S1 S2 HC HO EB ACEILB; nia). clear - HC HO EB. intros K. nia. } clear K.

      step. step. step. step. step. step. step.
      pose proof (dr_class_id c off HC HO) as [CID CB].
      rewrite (unsigned_lit B), (unsigned_lit sb) by (clear - S1 S2 HC HO EB ACEILB; nia).
      rewrite EB. replace (sb + c * 2 ^ 32 + off - sb) with (c * 2 ^ 32 + off) by (clear; lia).
      rewrite (unsigned_lit (c * 2 ^ 32 + off)) by (clear - HC HO; nia). rewrite Z.shiftl_mul_pow2 by (clear; lia).
      rewrite (unsigned_lit ((c * 2 ^ 32 + off) * 2 ^ 27)) by exact CB. rewrite CID.
      apply evt_done. reflexivity.
    Qed.

    Lemma dr_loop_test : forall (T : list qbatch) (j0 : list byte) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word) (m : mem),
      mem_inv asegs m -> Forall bok T -> bsum T < 2^62 -> dr_head_mem m T j0 -> stk asegs m lo spv ->
      evt asegs (fun ms' => match T with
                           | [] => dr_exit_post m t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ms'
                           | _ => ms' = dr_head_ms rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 T 0x946ec m
                           end)
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) x4 (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x94770) fc None m (seg_rom asegs)).
    Proof.
      intros until m. intros MI OKT BS (HT & BST & FR) ST.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      assert (Z0 : 0 <= zlen T) by (unfold zlen; clear; lia). pose proof (bsum_nonneg T OKT) as BT0. pose proof (bsum_len T OKT) as LT. unfold kBatchSize in LT.
      unfold FRAME, dr_frame in FR. unfold dr_head_ms, dr_exit_post. unfold T0 in *; unfold spv in *. dr_lits. unfold kBatchSize, kSpaceSize, AHI_LO in *. acb.

      step. step. if_cases K; zify_cond K.
      - destruct T as [|b T']. { exfalso. apply K. reflexivity. } clear K. apply evt_done. reflexivity.
      - destruct T as [|b T']. 2: { exfalso. revert K. rewrite zlen_cons'. rewrite ?unsigned_lit by (rewrite bsum_cons in *; pose proof (bsum_nonneg T' ltac:(apply Forall_cons_iff in OKT; exact (proj2 OKT))); clear - Z0 LT BS H; unfold zlen in *; cbn [length] in *; lia). unfold zlen. clear. lia. }
        clear K.

        do 11 step. step. release_frame FR ST (bv_unsigned sp + 112). step.
        apply evt_done. split; [reflexivity| assumption].
    Qed.
  End DoRecycle.
End HCW.
