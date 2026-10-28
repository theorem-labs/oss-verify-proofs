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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_Efs AW_Populate.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma u32arr_app : forall m A ws1 ws2,
  u32arr asegs m A (ws1 ++ ws2) <-> u32arr asegs m A ws1 /\ u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1. revert A. induction ws1 as [|w ws1 IH]; intros A ws2.
  - cbn [app length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. split; [intros H; split; [| exact H] | intros [_ H]; exact H].
    pose proof (u32arr_bound _ _ _ _ H) as B. apply u32arr_nil. cbn [length Z.of_nat] in B. lia.
  - cbn [app]. rewrite u32arr_cons, (u32arr_cons m A w ws1), IH. cbn [length].
    replace (A + 4 + 4 * Z.of_nat (length ws1)) with (A + 4 * Z.of_nat (S (length ws1))) by lia. tauto.
Qed.

Lemma wlist_length : forall l, length (wlist l) = length l.
Proof. intros. unfold wlist. apply length_map. Qed.

Lemma le4_sx32 : forall w : word, le4 (sx32 w) = le4 w.
Proof.
  intros w. transitivity (le4 (Z_to_bv 64 (bv_unsigned w))); [| f_equal; apply Z_to_bv_bv_unsigned].
  unfold sx32. apply le4_congr. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite Zminus_mod_idemp_l. replace (bv_unsigned w + 2^31 - 2^31) with (bv_unsigned w) by lia. reflexivity.
Qed.

Lemma rw_cells_C4_sx32 : forall m A w, rw_cells asegs m A [C4 (sx32 w)] -> rw_cells asegs m A [C4 w].
Proof.
  intros mq A w C. destruct C as [[Hwf Hb] Hw]. split; [split|]; [exact Hwf| |exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. rewrite le4_sx32. exact (fun x => x).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition copy_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (CH SA n : Z) (ws : list word) : machine_state -> Prop :=
  fun ms' => exists (a2 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz (CH + 4 * n)) a4 a5 a6 a7 s2 s3 (wz (SA + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c034) fc None m' (seg_rom asegs)
    /\ munch [(CH, CH + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' CH ws /\ u32arr asegs m' SA ws.
End HCW2.

Section CopyLoop.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (CH SA n : Z) (ws : list word).
  Hypothesis CHR : akobj CH (4 * n) /\ CH + 4 * n <= aceil /\ CH mod 4 = 0.
  Hypothesis SR : AHI_LO <= SA /\ SA + 4 * n <= aceil /\ SA mod 4 = 0.
  Hypothesis DISJ : CH + 4 * n <= SA \/ SA + 4 * n <= CH.
  Hypothesis NR : 0 < n. Hypothesis WSL : length ws = Z.to_nat n.

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Lemma copy_loop : forall (k : nat) (i : Z) (a2 : word) (m1 : mem),
    Z.to_nat (n - i) = k -> 0 <= i < n ->
    mem_inv asegs m1 -> munch [(CH, CH + 4 * n)]%Z m m1 -> wmono asegs m m1 ->
    stk asegs m1 (CH + 4 * i) (CH + 4 * n) ->
    u32arr asegs m1 CH (firstn (Z.to_nat i) ws) -> u32arr asegs m1 SA ws ->
    evt asegs (copy_post ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (CH + 4 * n)) a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m CH SA n ws)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (CH + 4 * n)) a2 (wz (CH + 4 * i)) a4 a5 a6 a7 s2 s3 (wz (SA + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c020) fc None m1 (seg_rom asegs)).
  Proof.
    unfold AHI_LO in *. acb.
    induction k as [|k IH]; intros i a2 m1 HK HI MI1 MU1 WM1 JK ARR SRC. { exfalso. clear - HK HI; try acb. lia. }
    unfold wz.
    (* [comment removed for export] *)
    assert (NTH : exists w, nth_error ws (Z.to_nat i) = Some w).
    { destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:E; [exists w; reflexivity|]. exfalso. apply nth_error_None in E. clear - E HI WSL; try acb. lia. }
    destruct NTH as [w NTH].
    pose proof (u32arr_read asegs _ _ _ i w (Z_to_bv 64 (SA + 4 * i)) SRC NTH ltac:(hci; clear - HI; try acb; lia) ltac:(hci; symmetry; apply wa_of_Z_to_bv; clear - SR HI; try acb; lia)) as RD.
    (* [comment removed for export] *)
    step. clear RD.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (CH + 4 * i + 4) _ JK ltac:(hci; clear - HI; try acb; lia)) as [SK1 SK2]. clear JK.
    destruct (stk_cells _ _ _ SK1 ltac:(hci; clear; lia)) as [jw JW]. clear SK1.
    replace (CH + 4 * i + 4 - (CH + 4 * i)) with 4 in JW by lia. change (Z.to_nat 4) with 4%nat in JW.
    assert (LF : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length_le; [reflexivity| clear - WSL HI; try acb; lia]).
    remember (CH + 4 * i) as D eqn:ED in JW |- *.
    (* [comment removed for export] *)
    step. subst D.
    (* [comment removed for export] *)
    step. step. step.
    apply rw_cells_C4_sx32 in JW.
    assert (ARR' : u32arr asegs m0 CH (firstn (Z.to_nat (i + 1)) ws)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HI; try acb; lia).
      rewrite (firstn_S_nth _ _ w NTH). apply u32arr_app. split; [exact ARR|]. rewrite LF.
      replace (CH + 4 * Z.of_nat (Z.to_nat i)) with (CH + 4 * i) by (clear - HI; try acb; lia).
      apply u32arr_cons. split; [exact JW|]. apply u32arr_nil. clear - CHR HI; try acb. aunf; lia. }
    clear ARR JW LF.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (SA + 4 * i + 4) with (SA + 4 * (i + 1)) by (clear; lia).
      eapply (IH (i + 1)); try eassumption. { clear - HK HI K; try acb; lia. }
      { revert K. rewrite ?unsigned_lit by (clear - HI NR CHR; try acb; aunf; lia). clear - HI; try acb. intros K. lia. }
    - (* [comment removed for export] *)
      assert (i + 1 = n) as EQ by (revert K; rewrite ?unsigned_lit by (clear - HI NR CHR; try acb; aunf; lia); clear - HI; try acb; intros K; lia).
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (SA + 4 * i + 4) with (SA + 4 * (i + 1)) by (clear; lia).
      rewrite EQ in ARR' |- *. rewrite <- WSL, firstn_all in ARR'.
      apply evt_done. unfold copy_post. do 2 eexists.
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ARR'| exact SRC].
  Qed.
End CopyLoop.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_head_post (ra sp gp tp s0 s1 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R FAB nf n : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 x5 x6 x7 x8 x9 : word) m' (j24 : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz AINST) (wz (R + 8)) a1 a2 a3 a4 (wz nf) a6 a7
                  s2 (wz (2^61)) (wz FAB) x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if nf <? n then 0x19c14c else 0x19c004)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (R, R + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 24 j24; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' R [C8 (wz kWriterLock)].
End HCW2.

Section Head.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo SB ARI c nf n : Z) (rtail : list cell).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 128 <= bv_unsigned sp.
  Hypothesis Ha2 : a2 = wz c. Hypothesis Ha4 : a4 = wz n.
  Hypothesis CR : 1 <= c < kNumClasses. Hypothesis NFR : 0 <= nf < 2^32. Hypothesis NNR : 0 <= n < 2^32.
  Hypothesis ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0.
  Hypothesis SBR : AHI_LO <= SB /\ SB + 2^37 <= aceil /\ SB mod 4096 = 0.
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz SB)].
  Hypothesis IRI : rw_cells asegs m (AINST + 48) [C8 (wz ARI)].
  Hypothesis RI0 : rw_cells asegs m R [C8 (wz 0)].
  Hypothesis RNF : rw_cells asegs m (R + 16) [C8 (wz nf)].

  Theorem gfa_head :
    evt asegs (gfa_head_post ra sp gp tp s0 s1 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R (SB + c * 2^32 + kFreeArrayOffset) nf n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz AINST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19beac) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kNumClasses, REGIONINFO_SIZE, AINST, kFreeArrayOffset in *. subst a2 a4.
    change (6976152 + 32) with 6976184 in ISB. change (6976152 + 48) with 6976200 in IRI.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (ARI + 128 * c, ARI + 128 * c + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 128%nat ST. do 13 step.
    (* [comment removed for export] *)
    do 18 step.
    rewrite (unsigned_lit c) by (clear - CR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 7), (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    change (2^7) with 128. replace (ARI + c * 128) with R by (subst R; clear; lia).
    replace (SB + (c * 2^32 + 3758096384)) with (SB + c * 2^32 + 3758096384) by (clear; lia).
    (* [comment removed for export] *)
    do 8 step.
    if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    assert (AL8 : R mod 8 = 0) by (subst R; clear - ARIR; try acb; Z.div_mod_to_equations; lia).
    assert (ALR : 0 <= R < 2^64) by (subst R; clear - ARIR CR; try acb; lia).
    astep.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    astep. fix_lit_store.
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step.
    replace (bv_ltu (Z_to_bv 64 nf) (Z_to_bv 64 n)) with (nf <? n).
    2:{ symmetry. unfold bv_ltu. rewrite !unsigned_lit by (clear - NFR NNR; try acb; lia). reflexivity. }
    apply evt_done. unfold gfa_head_post. do 12 eexists.
    split. { change (2^61) with 2305843009213693952. destruct (nf <? n); reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. unfold kWriterLock, wz. exact RI0.
  Qed.
End Head.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_call : forall (ra sp gp tp t0 t1 t2 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (R CH nf n : Z),
  0 <= nf <= n -> n < 2^32 ->
  evt asegs (fun ms' => ms' = MS (mkR (wz 0x19c168) sp gp tp t0 t1 t2 (wz R) (wz AINST) (wz AINST) a1 a2 (wz R) (wz (n - nf)) (wz nf) a6 a7
                                     (wz (R + 8)) s3 s4 (wz CH) (wz n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x19c1b4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz R) (wz AINST) (wz (R + 8)) a1 a2 (wz CH) (wz n) (wz nf) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19c14c) fc None m (seg_rom asegs)).
Proof.
  intros. unfold wz, AINST. do 7 step. rewrite (unsigned_lit n), (unsigned_lit nf) by lia.
  replace (n + - nf) with (n - nf) by lia. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_mid : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (R nf n : Z),
  0 < n <= nf -> nf < 2^32 -> AHI_LO <= R /\ R + 128 <= aceil ->
  mem_inv asegs m -> rw_cells asegs m (R + 16) [C8 (wz nf)] ->
  evt asegs (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz R) s1 a0 a1 a2 a3 (wz n) (wz (nf - n)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x19c010) fc None m' (seg_rom asegs)
                        /\ munch [(R + 16, R + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                        /\ rw_cells asegs m' (R + 16) [C8 (wz (nf - n))])
    (MS (mkR ra sp gp tp t0 t1 t2 (wz R) s1 a0 a1 a2 a3 (wz n) (wz nf) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19c004) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros NR NF RR MI RNF. unfold AHI_LO in RR. acb.
  pose proof (munch_refl [(R + 16, R + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold wz in *.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit n), (unsigned_lit nf) by lia. replace (nf + - n) with (nf - n) by lia.
  step. step. if_cases K; zify_cond K. { deadK K. } clear K.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_back : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (R CH nf n : Z),
  0 < n <= nf -> nf < 2^32 -> AHI_LO <= R /\ R + 128 <= aceil ->
  mem_inv asegs m -> rw_cells asegs m (R + 16) [C8 (wz nf)] ->
  evt asegs (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz R) (wz AINST) (wz (R + 8)) a1 a2 (wz CH) (wz n) (wz (nf - n)) a6 a7
                                                  (wz (R + 8)) s3 s4 (wz CH) (wz n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x19c010) fc None m' (seg_rom asegs)
                        /\ munch [(R + 16, R + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                        /\ rw_cells asegs m' (R + 16) [C8 (wz (nf - n))])
    (MS (mkR ra sp gp tp t0 t1 t2 (wz R) (wz AINST) (wz 1) a1 a2 a3 a4 a5 a6 a7 (wz (R + 8)) s3 s4 (wz CH) (wz n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19c168) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros NR NF RR MI RNF. unfold AHI_LO in RR. acb.
  pose proof (munch_refl [(R + 16, R + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold wz, AINST in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. { deadK K. } clear K.
  step. step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
  step. step. rewrite (unsigned_lit n), (unsigned_lit nf) by lia. replace (nf + - n) with (nf - n) by lia.
  step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_tail_post (sp gp tp : word) (fr : list cell) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R CH FAB nfn n : Z) (fl : list Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    match fr with
    | [CB 24 j24; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] =>
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + 128)) gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
    | _ => False end
    /\ munch [(bv_unsigned sp, bv_unsigned sp + 128); (CH, CH + 4 * n); (R, R + 8); (R + 72, R + 80)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + 128)
    /\ u32arr asegs m' CH (wlist (rev (firstn (Z.to_nat n) fl))) /\ stk asegs m' (CH + 4 * n) (CH + 64)
    /\ u32arr asegs m' FAB (wlist (rev fl))
    /\ rw_cells asegs m' R [C8 (wz 0)]
    /\ stk asegs m' (R + 69) (R + 128).
End HCW2.

Section Tail.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fr : list cell)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R CH FAB nfn n : Z) (fl : list Z) (j24 : list byte) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo <= bv_unsigned sp. Hypothesis SPH : bv_unsigned sp + 128 < 2^64.
  Hypothesis FRE : fr = [CB 24 j24; C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0; C8 fra].
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp) fr.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0.
  Hypothesis CHR : akobj CH 64 /\ CH + 64 <= aceil /\ CH mod 16 = 0.
  Hypothesis FABR : AHI_LO <= FAB /\ FAB + 4 * (nfn + n) <= aceil /\ FAB mod 4096 = 0.
  Hypothesis SEP : hidden ((CH + 64 <= FAB \/ FAB + 4 * (nfn + n) <= CH) /\ (CH + 64 <= R \/ R + 128 <= CH) /\ (R + 128 <= FAB \/ FAB + 4 * (nfn + n) <= R)).
  Hypothesis NR : 0 < n <= 16. Hypothesis NFN : 0 <= nfn. Hypothesis FLL : length fl = Z.to_nat (nfn + n).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis CHJ : stk asegs m CH (CH + 64).
  Hypothesis RLK : rw_cells asegs m R [C8 (wz kWriterLock)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).

  Let CHE : 4096 <= CH /\ CH + 64 <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Theorem gfa_tail :
    evt asegs (gfa_tail_post sp gp tp fr F fc m lo R CH FAB nfn n fl)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz R) s1 a0 a1 a2 (wz CH) (wz n) (wz nfn) a6 a7 s2 (wz (2^61)) (wz FAB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c010) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kWriterLock in *. acb. subst fr.
    pose proof SEP as SEPx. destruct SEPx as [SEPx].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 128); (CH, CH + 4 * n); (R, R + 8); (R + 72, R + 80)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (EFL : wlist (rev fl) = wlist (rev (skipn (Z.to_nat n) fl)) ++ wlist (rev (firstn (Z.to_nat n) fl))).
    { unfold wlist. rewrite <- map_app, <- rev_app_distr, firstn_skipn. reflexivity. }
    assert (LLO : length (wlist (rev (skipn (Z.to_nat n) fl))) = Z.to_nat nfn) by (rewrite wlist_length, length_rev, length_skipn, FLL; clear - NR NFN; try acb; lia).
    assert (LHI : length (wlist (rev (firstn (Z.to_nat n) fl))) = Z.to_nat n) by (rewrite wlist_length, length_rev, firstn_length_le; [reflexivity| rewrite FLL; clear - NR NFN; try acb; lia]).
    rewrite EFL in FARR. apply u32arr_app in FARR. destruct FARR as [FLO FHI]. rewrite LLO in FHI.
    replace (FAB + 4 * Z.of_nat (Z.to_nat nfn)) with (FAB + 4 * nfn) in FHI by (clear - NFN; try acb; lia).
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (CH + 4 * n) _ CHJ ltac:(hci; clear - NR; try acb; lia)) as [CJ1 CJ2]. clear CHJ.
    assert (ARR0 : u32arr asegs m CH (firstn (Z.to_nat 0) (wlist (rev (firstn (Z.to_nat n) fl))))).
    { change (Z.to_nat 0) with 0%nat. cbn [firstn]. apply u32arr_nil. clear - CHR; try acb; aunf; lia. }
    pose proof (munch_refl [(CH, CH + 4 * n)]%Z m) as MU0.
    replace CH with (CH + 4 * 0) in CJ1 at 1 by (clear; lia).
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite (unsigned_lit nfn), (unsigned_lit n) by (clear - NR NFN FABR; try acb; lia).
    rewrite (Z.shiftl_mul_pow2 nfn 2), (Z.shiftl_mul_pow2 n 2) by (clear; lia). change (2^2) with 4.
    replace (FAB + nfn * 4) with (FAB + 4 * nfn) by (clear; lia). replace (CH + n * 4) with (CH + 4 * n) by (clear; lia).
    (* [comment removed for export] *)
    assert (CHR' : akobj CH (4 * n) /\ CH + 4 * n <= aceil /\ CH mod 4 = 0) by (clear - CHR NR; split; [eapply akobj_sub; [exact (proj1 CHR)| lia| lia] | try acb; Z.div_mod_to_equations; lia]).
    assert (SR' : 17594333495296 <= FAB + 4 * nfn /\ FAB + 4 * nfn + 4 * n <= aceil /\ (FAB + 4 * nfn) mod 4 = 0) by (clear - FABR NR NFN; try acb; Z.div_mod_to_equations; lia).
    assert (DISJ' : CH + 4 * n <= FAB + 4 * nfn \/ FAB + 4 * nfn + 4 * n <= CH) by (clear - SEPx NR NFN; try acb; lia).
    assert (NR' : 0 < n) by (clear - NR; try acb; lia).
    replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * 0)) by (f_equal; clear; lia).
    replace (Z_to_bv 64 (FAB + 4 * nfn)) with (Z_to_bv 64 (FAB + 4 * nfn + 4 * 0)) by (f_equal; clear; lia).
    callD (copy_loop ra _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m CH (FAB + 4 * nfn) n (wlist (rev (firstn (Z.to_nat n) fl)))
             CHR' SR' DISJ' NR' LHI (Z.to_nat n) 0 _ m ltac:(hci; rewrite Z.sub_0_r; reflexivity) ltac:(hci; clear - NR; try acb; lia) MI MU0 WM CJ1 ARR0 FHI).
    clear MU0. rename PC into CARR. rename POST into FHI'.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (R + 72) _ RST ltac:(hci; clear; lia)) as [RS1 RS2].
    destruct (stk_split asegs _ _ (R + 80) _ RS2 ltac:(hci; clear; lia)) as [RS3 RS4]. clear RS2 RST.
    destruct (stk_cells _ _ _ RS3 ltac:(hci; clear; lia)) as [jst JST]. clear RS3.
    replace (R + 80 - (R + 72)) with 8 in JST by (clear; lia). change (Z.to_nat 8) with 8%nat in JST.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    do 15 step.
    zb_fold_lits.
    (* [comment removed for export] *)
    step. step. zb_fold_lits. step. if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    step. zb_fold_lits. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. zb_fold_lits. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    match goal with |- context [v_sltu ?a ?b] => let v := eval vm_compute in (v_sltu a b) in change (v_sltu a b) with v end.
    rewrite ?unsigned_lit by (clear; lia). zb_fold_lits. rewrite ?unsigned_lit by (clear; lia). zb_fold_lits.
    (* [comment removed for export] *)
    assert (AL8 : R mod 8 = 0) by (clear - RR; try acb; Z.div_mod_to_equations; lia). assert (ALR : 0 <= R < 2^64) by (clear - RR; try acb; lia).
    astep. step. if_cases K; zify_cond K. { deadK K. } clear K.
    astep. fix_lit_store. step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. do 13 step. step. step.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells asegs _ _ _ JST) as RS3. cbn [cells_size csize Nat.add] in RS3.
    assert (RSTn : stk asegs m1 (R + 69) (R + 128)).
    { eapply stk_merge; [exact RS1| |clear; lia]. eapply stk_merge; [| exact RS4| clear; lia].
      replace (R + 80) with (R + 72 + Z.of_nat 8) by (clear; lia). exact RS3. }
    assert (FARR' : u32arr asegs m1 FAB (wlist (rev fl))).
    { rewrite EFL. apply u32arr_app. split; [exact FLO|]. rewrite LLO.
      replace (FAB + 4 * Z.of_nat (Z.to_nat nfn)) with (FAB + 4 * nfn) by (clear - NFN; try acb; lia). exact FHI'. }
    release_frame FR ST (bv_unsigned sp + 128).
    apply evt_done. unfold gfa_tail_post. do 14 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact ST|].
    split; [exact CARR|]. split; [exact CJ2|]. split; [exact FARR'|]. split; [exact RLK| exact RSTn].
  Qed.
End Tail.

