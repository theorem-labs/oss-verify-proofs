(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_MallocBase AW_LargeAlloc1 AW_LargeAlloc2 AW_LargeAlloc3 AW_GetBlockBegin AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma cb8_word' : forall m A bs cs, rw_cells asegs m A (CB 8 bs :: cs) -> exists w, rw_cells asegs m A (C8 w :: cs).
Proof.
  intros m A bs cs R. assert (L : length bs = 8%nat) by (destruct R as [[[L _] _] _]; exact L).
  destruct (le8_surj bs L) as [w Hw]. exists w. destruct R as [[[_ W] B] R']. refine (conj (conj (conj I W) _) R').
  cbn [cells_bytes cbytes] in *. rewrite Hw. exact B.
Qed.
(* [comment removed for export] *)
Lemma cb8_word2 : forall m A w bs cs, rw_cells asegs m A (C8 w :: CB 8 bs :: cs) -> exists w2, rw_cells asegs m A (C8 w :: C8 w2 :: cs).
Proof.
  intros m A w bs cs R.
  apply (rw_cells_app asegs m A [C8 w] (CB 8 bs :: cs)) in R. destruct R as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
  destruct (cb8_word' _ _ _ _ R2) as [w2 R3]. exists w2.
  apply (rw_cells_app asegs m A [C8 w] (C8 w2 :: cs)). split; [exact R1| exact R3].
Qed.

Lemma firstn_skipn_mid : forall {X} (pre post : list X) (x : X),
  firstn (length pre) (pre ++ x :: post) = pre /\ skipn (S (length pre)) (pre ++ x :: post) = post.
Proof.
  intros X pre post x. split.
  - rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r.
  - rewrite skipn_app. replace (S (length pre) - length pre)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma u64arr_app : forall m A ws1 ws2,
  u64arr asegs m A (ws1 ++ ws2) <-> u64arr asegs m A ws1 /\ u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2. rewrite !u64arr_u8arr, u64s_app, u8arr_app, u64s_length.
  replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) by lia. tauto.
Qed.

(* [comment removed for export] *)
Definition dealloc1_post (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v s1v s2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (W : list ivl)
    (lo a msz nres nch pa TH : Z) (chunks' : list Z) (X : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x1998d4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a) (wz a) (wz msz) (wz 0) a3 a4 a5 a6 a7
                  (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1c06e0) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra]
    /\ rw_cells asegs m' 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' 6976264 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]
    /\ stk asegs m' 6976288 6976832 /\ rw_cells asegs m' 6976832 [C8 (wz 0)] /\ stk asegs m' 6976840 6976880
    /\ u64arr asegs m' pa (wlist chunks')
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz)]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ X m'.
End HCW.

Section Dealloc1.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo a msz sz idx pa nres nch TH lst : Z) (chunks : list Z).   (* [comment removed for export] *)
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Let W : list ivl := [(lo, bv_unsigned sp); (6976264, 6976880); (pa, pa + 8 * nch); (a + 16, a + 32); (lst + 24, lst + 32); (TH + 2800, TH + 3168)]%Z.
  Hypothesis LNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ 0x2000 <= msz.
  Hypothesis PAR : aapp pa (8 * nch) /\ pa + 8 * nch <= aceil.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch < 2^40.
  Hypothesis IDX : nth_error chunks (Z.to_nat idx) = Some a.
  Hypothesis RNG : hidden (akobj TH 4096 /\ TH + 4096 <= aceil).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (pa + 8 * nch <= a \/ a + msz <= pa) /\ (pa + 8 * nch <= TH \/ TH + 4096 <= pa)).

  Let LRE : 12599296 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + 8 * nch <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Ltac prep :=
    pose proof AR as R; destruct R as (AHI & CE & AL & MSZ); pose proof PAR as R; destruct R as [PLO PHI]; pose proof NCH as R; destruct R as (LEN & IDR & NHI);
    pose proof RNG as R; destruct R as [RNG']; pose proof LR as R; destruct R as [LLO LHI];
    unfold AHI_LO in *; acb;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dealloc1_head : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem),
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs m1 6976264 [C8 (wz nres); C8 (wz nch); C8 (wz 0)] ->
    stk asegs m1 6976288 6976832 -> rw_cells asegs m1 6976832 [C8 (wz 0)] -> stk asegs m1 6976840 6976880 ->
    u64arr asegs m1 pa (wlist chunks) ->
    rw_cells asegs m1 a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)] ->
    stk asegs m1 (TH + 2800) (TH + 3168) ->
    evt asegs (fun ms' => exists (x6 x28 x29 x30 x31 : word) (nf ca : word) m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp (Z_to_bv 64 (bv_unsigned ca - msz)) x6 t2 (wz a) s1 (wz 6976216) (wz 6976840) (wz (pa + 8 * idx)) (wz idx) (wz 6976856) (wz lst) (Z_to_bv 64 (- msz)) (wz msz)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x199898) fc None m' (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp); (6976264, 6976880)]%Z m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -32)
        /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m' 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
        /\ rw_cells asegs m' 6976264 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]
        /\ stk asegs m' 6976288 6976296 /\ rw_cells asegs m' 6976296 [C8 nf; C8 (Z_to_bv 64 (bv_unsigned ca - msz))] /\ stk asegs m' 6976312 6976832
        /\ rw_cells asegs m' 6976832 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)] /\ stk asegs m' 6976840 6976880
        /\ u64arr asegs m' pa (wlist chunks)
        /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)]
        /\ stk asegs m' (TH + 2800) (TH + 3168))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + 64)) (wz (AINST + 688)) (wz (a + 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1997e0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until m1. intros MI ST INST64 NRES SST MTX GST PA HDR TST.
    prep. unfold AINST. change (6976152 + 64) with 6976216. change (6976152 + 688) with 6976840. unfold wz in *.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (6976264, 6976880)]%Z m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    region_table.
    (* [comment removed for export] *)
    step. carve_frame 32%nat ST. step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. rewrite (unsigned_lit (a + 4096)) by lia.
    replace (Z.land 4095 (a + 4096)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; clear - AL AHI; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step.
    apply rw_cells_C8_zero_split' in MTX.
    assert (MA : 6976832 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6976832 < 2^64) by lia.
    astep. step. step. step. step.
    repeat match goal with |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
                         | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    astep.
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (a + 4096)) by lia. replace (a + 4096 - 4096) with a by lia.
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    assert (NTH1 : nth_error (wlist chunks) (Z.to_nat idx) = Some (Z_to_bv 64 a)) by (unfold wlist; rewrite nth_error_map, IDX; reflexivity).
    assert (NTH2 : nth_error (wlist chunks) (Z.to_nat (nch - 1)) = Some (Z_to_bv 64 lst)) by (unfold wlist; rewrite nth_error_map, LNTH; reflexivity).
    step. step. step. rewrite (unsigned_lit idx), Z.shiftl_mul_pow2 by lia. change (2^3) with 8. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_read asegs mm _ _ idx (Z_to_bv 64 a) (wa (pa + 8 * idx)) PA NTH1 ltac:(hci; lia) eq_refl) as HR1;
      pose proof (u64arr_read asegs mm _ _ (nch - 1) (Z_to_bv 64 lst) (wa (pa + 8 * (nch - 1))) PA NTH2 ltac:(hci; lia) eq_refl) as HR2 end.
    step. clear HR1. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8. step. step.
    destruct (stk_split asegs _ 6976288 6976296 6976832 SST ltac:(hci; lia)) as [SS1 SS2]. clear SST.
    destruct (stk_split asegs _ 6976296 6976312 6976832 SS2 ltac:(hci; lia)) as [SS3 SS4]. clear SS2.
    destruct (stk_cells _ _ _ SS3 ltac:(hci; lia)) as [cj CJ]. change (Z.to_nat (6976312 - 6976296)) with 16%nat in CJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 cj [] [8;8]%nat) in CJ; [| reflexivity]. cbn [mk_CB_cells app] in CJ.
    repeat match type of CJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in CJ end.
    repeat match type of CJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in CJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    destruct (cb8_word' _ _ _ _ CJ) as [nf CJ1]. clear CJ. destruct (cb8_word2 _ _ _ _ _ CJ1) as [ca CJ]. clear CJ1.
    step. step. step. replace (pa + nch * 8 + -8) with (pa + 8 * (nch - 1)) by lia. step. clear HR2.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit msz) by lia.
    st1.
    apply (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nch + -1))] [C8 (Z_to_bv 64 0)]) in NRES. destruct NRES as [NRES SRT].
    change (6976264 + Z.of_nat (cells_size [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nch + -1))])) with 6976280 in SRT. apply rw_cells_C8_zero_split in SRT. apply rw_cells_C4_0_bytes in SRT.
    st1.
    apply rw_cells_bytes_C4_0 in SRT. apply rw_cells_C4C4_C8_zero in SRT.
    st1. st1. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (NRES' : rw_cells asegs mm 6976264 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nch - 1)); C8 (Z_to_bv 64 0)])
        by (apply (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nch - 1))] [C8 (Z_to_bv 64 0)]); replace (nch - 1) with (nch + -1) by lia; split; [exact NRES| exact SRT]) end.
    clear NRES SRT.
    rewrite (unsigned_lit msz) by lia. replace (0 - msz) with (- msz) by lia. replace (pa + idx * 8) with (pa + 8 * idx) by lia.
    apply evt_done. do 5 eexists. exists (Z_to_bv 64 (bv_unsigned nf + 1)), ca. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dealloc1_tail : forall (x5 x6 x7 x13 x15 x28 x29 x30 x31 : word) (mX : mem) (chunks' : list Z) (m0 : mem) (nf ca : word) (X : mem -> Prop),
    (forall m', munch [(6976832, 6976880)]%Z mX m' -> wmono asegs mX m' -> X m') ->
    mem_inv asegs mX -> munch W m0 mX -> wmono asegs m0 mX ->
    stk asegs mX lo (bv_unsigned sp + -32) ->
    rw_cells asegs mX (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs mX 6976264 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)] ->
    stk asegs mX 6976288 6976296 -> rw_cells asegs mX 6976296 [C8 nf; C8 ca] -> stk asegs mX 6976312 6976832 ->
    rw_cells asegs mX 6976832 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)] -> stk asegs mX 6976840 6976880 ->
    u64arr asegs mX pa (wlist chunks') -> Z.of_nat (length (wlist chunks')) = nch ->
    rw_cells asegs mX a [C8 (wz a); C8 (wz msz)] ->
    stk asegs mX (TH + 2800) (TH + 3168) ->
    evt asegs (dealloc1_post ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 F fc m0 W lo a msz nres nch pa TH chunks' X)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz a) s1 (wz 6976216) (wz 6976840) x13 (wz idx) (wz 6976856) x15 (Z_to_bv 64 (- msz)) (wz msz)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1998a0) fc None mX (seg_rom asegs)).
  Proof.
    intros until X. intros XK MI MU WM ST FR INST64 NRES SS1 SSC SS2 MTX GST PA LENW HDR TST.
    prep. unfold W in MU. unfold wz in *.
    pose proof (munch_refl [(6976832, 6976880)]%Z mX) as MUX. pose proof (wmono_refl asegs mX) as WMX.
    region_table.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ 6976840 6976856 6976880 GST ltac:(hci; lia)) as [GS1 GS2]. clear GST.
    destruct (stk_split asegs _ 6976856 6976872 6976880 GS2 ltac:(hci; lia)) as [GS3 GS4]. clear GS2.
    destruct (stk_cells _ _ _ GS3 ltac:(hci; lia)) as [gj GJ]. change (Z.to_nat (6976872 - 6976856)) with 16%nat in GJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 gj [] [8;8]%nat) in GJ; [| reflexivity]. cbn [mk_CB_cells app] in GJ.
    repeat match type of GJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in GJ end.
    repeat match type of GJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in GJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    assert (GA1 : 6976856 mod 8 = 0) by reflexivity. assert (GR1 : 0 <= 6976856 < 2^64) by lia.
    assert (GA2 : 6976864 mod 8 = 0) by reflexivity. assert (GR2 : 0 <= 6976864 < 2^64) by lia.
    astep.
    step. step. step. rewrite (unsigned_lit msz) by lia.
    astep.
    (* [comment removed for export] *)
    step. apply rw_cells_C4_1_bytes in MTX. st1. apply rw_cells_bytes_C4_0 in MTX. apply rw_cells_C4C4_C8_zero in MTX.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GST' : stk asegs mm 6976840 6976880) by (apply (stk_merge asegs _ _ 6976856); [exact GS1| |lia]; apply (stk_merge asegs _ _ 6976872); [exact GS3| exact GS4|lia]);
      assert (SST' : stk asegs mm 6976288 6976832) by (apply (stk_merge asegs _ _ 6976296); [assumption| |lia]; apply (stk_merge asegs _ _ 6976312); [|assumption|lia];
         lazymatch goal with H : rw_cells asegs mm 6976296 _ |- _ => pose proof (stk_of_rw_cells asegs _ _ _ H) as KK; cbn [cells_size csize length Nat.add] in KK; exact KK end) end.
    apply evt_done. unfold dealloc1_post. do 13 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption. exact (XK _ MUX WMX).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem dealloc1_last : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem),
    idx = nch - 1 ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs m1 6976264 [C8 (wz nres); C8 (wz nch); C8 (wz 0)] ->
    stk asegs m1 6976288 6976832 -> rw_cells asegs m1 6976832 [C8 (wz 0)] -> stk asegs m1 6976840 6976880 ->
    u64arr asegs m1 pa (wlist chunks) ->
    rw_cells asegs m1 a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)] ->
    stk asegs m1 (TH + 2800) (TH + 3168) ->
    evt asegs (dealloc1_post ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 F fc m1 W lo a msz nres nch pa TH chunks
                 (fun m' => rw_cells asegs m' (lst + 24) [C8 (wz idx)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + 64)) (wz (AINST + 688)) (wz (a + 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1997e0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until m1. intros IL MI ST INST64 NRES SST MTX GST PA HDR TST.
    assert (LA : lst = a) by (rewrite <- IL in LNTH; rewrite IDX in LNTH; congruence).
    eapply evt_cut. { eapply dealloc1_head; eassumption. }
    cbv beta. intros ms' (x6 & x28 & x29 & x30 & x31 & nf & ca & m2 & -> & MU & WM & MI2 & ST2 & FR2 & INST2 & NRES2 & SS1 & CJ & SS2 & MTX2 & GST2 & PA2 & HDR2 & TST2).
    clear MI ST INST64 NRES SST MTX GST PA HDR TST.
    prep. unfold wz in *. rewrite LA.
    apply (munch_weaken _ W) in MU; [| unfold W, sub_fp; cbn [outside]; intros; lia]. unfold W in MU.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    (* [comment removed for export] *)
    destruct (nth_error_split _ _ _ IDX) as (pre & post & EC & LP).
    assert (PAS : u64arr asegs m2 pa (wlist pre) /\ rw_cells asegs m2 (pa + 8 * idx) [C8 (Z_to_bv 64 a)] /\ u64arr asegs m2 (pa + 8 * idx + 8) (wlist post)).
    { rewrite EC in PA2. unfold wlist in PA2. rewrite map_app in PA2. cbn [map] in PA2. apply u64arr_app in PA2. destruct PA2 as [P1 P2].
      rewrite length_map, LP, Z2Nat.id in P2 by lia. apply u64arr_cons in P2. destruct P2 as [P2 P3]. unfold wlist. auto. }
    destruct PAS as (PA1 & SLOT & PA3). clear PA2.
    assert (L1 : Z.of_nat (length (wlist pre)) = idx) by (unfold wlist; rewrite length_map; lia).
    assert (L3 : Z.of_nat (length (wlist post)) = nch - 1 - idx).
    { unfold wlist. rewrite length_map. rewrite EC in LEN. unfold zlen in LEN. rewrite length_app in LEN. cbn [length] in LEN. lia. }
    remember (pa + 8 * idx) as SA eqn:ESA in *.
    region_table.
    (* [comment removed for export] *)
    st1. st1. subst SA.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (PA4 : u64arr asegs mm pa (wlist chunks))
        by (rewrite EC; unfold wlist; rewrite map_app; cbn [map]; apply u64arr_app; split; [exact PA1|];
            rewrite length_map, LP, Z2Nat.id by lia; apply u64arr_cons; split; [exact SLOT| exact PA3]) end.
    clear PA1 SLOT PA3.
    apply (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 sz)] [C8 (Z_to_bv 64 idx)]) in HDR2. destruct HDR2 as [HDR2 HC3].
    cbn [cells_size csize Nat.add] in HC3. replace (a + Z.of_nat 24) with (a + 24) in HC3 by lia.
    apply (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 msz)] [C8 (Z_to_bv 64 sz)]) in HDR2. destruct HDR2 as [HDR2 _].
    eapply dealloc1_tail; try eassumption.
    intros m' MU' WM'. try rewrite LA. eapply rw_cells_transport; [exact HC3| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize length Nat.add]. region_decide.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis PLCL : hidden ((lst + 4096 <= a \/ a + msz <= lst) /\ (pa + 8 * nch <= lst \/ lst + 4096 <= pa) /\ (TH + 4096 <= lst \/ lst + 4096 <= TH)).
  Theorem dealloc1_mid : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (lidx : Z),
    idx < nch - 1 ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs m1 6976264 [C8 (wz nres); C8 (wz nch); C8 (wz 0)] ->
    stk asegs m1 6976288 6976832 -> rw_cells asegs m1 6976832 [C8 (wz 0)] -> stk asegs m1 6976840 6976880 ->
    u64arr asegs m1 pa (wlist chunks) ->
    rw_cells asegs m1 a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)] ->
    rw_cells asegs m1 (lst + 24) [C8 (wz lidx)] ->
    stk asegs m1 (TH + 2800) (TH + 3168) ->
    evt asegs (dealloc1_post ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 F fc m1 W lo a msz nres nch pa TH
                              (firstn (Z.to_nat idx) chunks ++ lst :: skipn (S (Z.to_nat idx)) chunks)
                              (fun m' => rw_cells asegs m' (lst + 24) [C8 (wz idx)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + 64)) (wz (AINST + 688)) (wz (a + 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1997e0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until lidx. intros IL MI ST INST64 NRES SST MTX GST PA HDR LST TST.
    eapply evt_cut. { eapply dealloc1_head; eassumption. }
    cbv beta. intros ms' (x6 & x28 & x29 & x30 & x31 & nf & ca & m2 & -> & MU & WM & MI2 & ST2 & FR2 & INST2 & NRES2 & SS1 & CJ & SS2 & MTX2 & GST2 & PA2 & HDR2 & TST2).
    prep. unfold wz in *.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    region_table.
    assert (LST2 : rw_cells asegs m2 (lst + 24) [C8 (Z_to_bv 64 lidx)]).
    { eapply rw_cells_transport; [exact LST| exact MU| exact WM|]. cbn [disjoint_from cells_size csize length Nat.add]. region_decide. }
    clear MI ST INST64 NRES SST MTX GST PA HDR TST LST.
    apply (munch_weaken _ W) in MU; [| unfold W, sub_fp; cbn [outside]; intros; lia]. unfold W in MU.
    (* [comment removed for export] *)
    destruct (nth_error_split _ _ _ IDX) as (pre & post & EC & LP).
    assert (PAS : u64arr asegs m2 pa (wlist pre) /\ rw_cells asegs m2 (pa + 8 * idx) [C8 (Z_to_bv 64 a)] /\ u64arr asegs m2 (pa + 8 * idx + 8) (wlist post)).
    { rewrite EC in PA2. unfold wlist in PA2. rewrite map_app in PA2. cbn [map] in PA2. apply u64arr_app in PA2. destruct PA2 as [P1 P2].
      rewrite length_map, LP, Z2Nat.id in P2 by lia. apply u64arr_cons in P2. destruct P2 as [P2 P3]. unfold wlist. auto. }
    destruct PAS as (PA1 & SLOT & PA3). clear PA2.
    assert (L1 : Z.of_nat (length (wlist pre)) = idx) by (unfold wlist; rewrite length_map; lia).
    assert (L3 : Z.of_nat (length (wlist post)) = nch - 1 - idx).
    { unfold wlist. rewrite length_map. rewrite EC in LEN. unfold zlen in LEN. rewrite length_app in LEN. cbn [length] in LEN. lia. }
    remember (pa + 8 * idx) as SA eqn:ESA in *.
    region_table.
    (* [comment removed for export] *)
    st1. st1. subst SA.
    (* [comment removed for export] *)
    destruct (firstn_skipn_mid pre post a) as [E1 E2]. rewrite LP in E1, E2. rewrite <- EC in E1, E2. rewrite E1, E2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (PA4 : u64arr asegs mm pa (wlist (pre ++ lst :: post)))
        by (unfold wlist; rewrite map_app; cbn [map]; apply u64arr_app; split; [exact PA1|];
            rewrite length_map, LP, Z2Nat.id by lia; apply u64arr_cons; split; [exact SLOT| exact PA3]) end.
    assert (L4 : Z.of_nat (length (wlist (pre ++ lst :: post))) = nch).
    { clear - L1 L3; try acb. unfold wlist in *. rewrite length_map in *. rewrite length_app. cbn [length]. lia. }
    clear PA1 SLOT PA3.
    apply (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 msz)] [C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 idx)]) in HDR2. destruct HDR2 as [HDR2 _].
    eapply dealloc1_tail; try eassumption.
    intros m' MU' WM'. eapply rw_cells_transport; [exact LST2| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize length Nat.add]. region_decide.
  Qed.
End Dealloc1.

