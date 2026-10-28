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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_Efs AW_Populate AW_Gfa AW_MaybeRelease.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocTacX.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Definition rcopy_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (CH D n : Z) (ws : list word) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz (CH + 4 * n)) s7 s8 (wz (D + 4 * n)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x199ce0) fc None m' (seg_rom asegs)
    /\ munch [(D, D + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' D ws /\ u32arr asegs m' CH ws.
End HCW2.

Section CopyLoop.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (CH D n : Z) (ws : list word).
  Hypothesis CHR : akobj CH (4 * n) /\ CH + 4 * n <= aceil /\ CH mod 4 = 0.
  Hypothesis DR : 4096 <= D /\ D + 4 * n <= aceil /\ D mod 4 = 0.
  Hypothesis DISJ : CH + 4 * n <= D \/ D + 4 * n <= CH.
  Hypothesis NR : 0 < n. Hypothesis WSL : length ws = Z.to_nat n.

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Lemma rcopy_loop : forall (k : nat) (i : Z) (a1 : word) (m1 : mem),
    Z.to_nat (n - i) = k -> 0 <= i < n ->
    mem_inv asegs m1 -> munch [(D, D + 4 * n)]%Z m m1 -> wmono asegs m m1 ->
    stk asegs m1 (D + 4 * i) (D + 4 * n) ->
    u32arr asegs m1 D (firstn (Z.to_nat i) ws) -> u32arr asegs m1 CH ws ->
    evt asegs (rcopy_post ra sp gp tp t0 t1 t2 s0 s1 (wz (CH + 4 * n)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 F fc m CH D n ws)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (CH + 4 * n)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz (CH + 4 * i)) s7 s8 (wz (D + 4 * i)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199ccc) fc None m1 (seg_rom asegs)).
  Proof.
    unfold AHI_LO in *. acb.
    induction k as [|k IH]; intros i a1 m1 HK HI MI1 MU1 WM1 JK ARR SRC. { exfalso. clear - HK HI; try acb. lia. }
    unfold wz.
    (* [comment removed for export] *)
    assert (NTH : exists w, nth_error ws (Z.to_nat i) = Some w).
    { destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:E; [exists w; reflexivity|]. exfalso. apply nth_error_None in E. clear - E HI WSL; try acb. lia. }
    destruct NTH as [w NTH].
    pose proof (u32arr_read asegs _ _ _ i w (Z_to_bv 64 (CH + 4 * i)) SRC NTH ltac:(hci; clear - HI; try acb; lia) ltac:(hci; symmetry; apply wa_of_Z_to_bv; clear - CHR HI; try acb; aunf; lia)) as RD.
    (* [comment removed for export] *)
    step. clear RD. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (D + 4 * i + 4) _ JK ltac:(hci; clear - HI; try acb; lia)) as [SK1 SK2]. clear JK.
    destruct (stk_cells _ _ _ SK1 ltac:(hci; clear; lia)) as [jw JW]. clear SK1.
    replace (D + 4 * i + 4 - (D + 4 * i)) with 4 in JW by lia. change (Z.to_nat 4) with 4%nat in JW.
    assert (LF : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length_le; [reflexivity| clear - WSL HI; try acb; lia]).
    remember (D + 4 * i) as DD eqn:ED in JW |- *.
    (* [comment removed for export] *)
    step. subst DD.
    (* [comment removed for export] *)
    step. step.
    apply rw_cells_C4_sx32 in JW.
    assert (ARR' : u32arr asegs m0 D (firstn (Z.to_nat (i + 1)) ws)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HI; try acb; lia).
      rewrite (firstn_S_nth _ _ w NTH). apply u32arr_app. split; [exact ARR|]. rewrite LF.
      replace (D + 4 * Z.of_nat (Z.to_nat i)) with (D + 4 * i) by (clear - HI; try acb; lia).
      apply u32arr_cons. split; [exact JW|]. apply u32arr_nil. clear - DR HI; try acb. aunf; lia. }
    clear ARR JW LF.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) in * by (clear; lia).
      eapply (IH (i + 1)); try eassumption. { clear - HK HI K; try acb; lia. }
      { revert K. rewrite ?unsigned_lit by (clear - HI NR CHR DR; try acb; aunf; lia). clear - HI; try acb. intros K. lia. }
    - (* [comment removed for export] *)
      assert (i + 1 = n) as EQ by (revert K; rewrite ?unsigned_lit by (clear - HI NR CHR DR; try acb; aunf; lia); clear - HI; try acb; intros K; lia).
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) in * by (clear; lia).
      rewrite EQ in ARR' |- *. rewrite <- WSL, firstn_all in ARR'.
      apply evt_done. unfold rcopy_post. do 2 eexists.
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ARR'| exact SRC].
  Qed.
End CopyLoop.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R CH FAB nf n mfa au mu : Z) (ws : list word) (fl : list Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FAB + 4 * nf, FAB + 4 * (nf + n))]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf + n)); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
    /\ stk asegs m' (R + 69) (R + 128)
    /\ u32arr asegs m' FAB (wlist (rev fl) ++ ws) /\ stk asegs m' (FAB + 4 * (nf + n)) (FAB + mfa)
    /\ u32arr asegs m' CH ws.
End HCW2.

Section Tail.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp : word) (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo sb ARI c CH FAB nf n mfa au mu : Z) (ws : list word) (fl : list Z) (j16 : list byte).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 208 <= bv_unsigned sp.
  Hypothesis CR : 1 <= c < kNumClasses. Hypothesis NR : 1 <= n. Hypothesis NFR : 0 <= nf /\ 4 * (nf + n) <= mfa /\ mfa <= kFreeArraySize.
  Hypothesis ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0.
  Hypothesis CHR : akobj CH (4 * n) /\ CH + 4 * n <= aceil /\ CH mod 4 = 0.
  Hypothesis FABR : AHI_LO <= FAB /\ FAB + mfa <= aceil /\ FAB mod 4096 = 0.
  Hypothesis SEP : hidden ((CH + 4 * n <= FAB + 4 * nf \/ FAB + 4 * (nf + n) <= CH) /\ (CH + 4 * n <= R \/ R + 128 <= CH) /\ (R + 128 <= FAB \/ FAB + mfa <= R)).
  Hypothesis IRI : rw_cells asegs m (AINST + 48) [C8 (wz ARI)].
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)].   (* [comment removed for export] *)
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -128)
                    [CB 16 j16; C8 (wz (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis SRC : u32arr asegs m CH ws. Hypothesis WSL : length ws = Z.to_nat n.
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)). Hypothesis FLL : length fl = Z.to_nat nf.
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Theorem rta_tail :
    evt asegs (rta_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo R CH FAB nf n mfa au mu ws fl)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz 1) a1 a2 a3 a4 a5 a6 a7
               (wz c) mm (wz AINST) (wz n) (wz CH) (wz (nf + n)) (wz (2^61)) (wz FAB) (wz (2^60 + 2^20 - 1)) (wz (2^60)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x199cb4) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kNumClasses, kFreeArraySize, REGIONINFO_SIZE, AINST, AGOT_LO, APAGESZ in *. unfold AGOT_VALS in GOT. cbn [map] in GOT.
    acb.
    change (6976152 + 48) with 6976200 in IRI. change (6976152 + 32) with 6976184 in ISB. unfold rinfo_cells, kWriterLock in RI.
    pose proof SEP as SEPx. destruct SEPx as [SEPx].
    assert (LFL : length (wlist (rev fl)) = Z.to_nat nf) by (rewrite wlist_length, length_rev; exact FLL).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (RR : 17594333495296 <= R /\ R + 128 <= aceil /\ R mod 128 = 0) by (subst R; clear - ARIR CR; try acb; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FAB + 4 * nf, FAB + 4 * (nf + n))]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - SPR HI LO; try acb; lia).
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (FAB + 4 * (nf + n)) _ FAJ ltac:(hci; clear - NR NFR; try acb; lia)) as [CJ1 CJ2]. clear FAJ.
    assert (ARR0 : u32arr asegs m (FAB + 4 * nf) (firstn (Z.to_nat 0) ws)).
    { change (Z.to_nat 0) with 0%nat. cbn [firstn]. apply u32arr_nil. clear - FABR NFR NR; try acb; lia. }
    pose proof (munch_refl [(FAB + 4 * nf, FAB + 4 * nf + 4 * n)]%Z m) as MU0.
    unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - NR NFR; try acb; lia). clear - NR; try acb. intros K. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite ?(unsigned_lit nf), ?(unsigned_lit n) by (clear - NR NFR FABR; try acb; lia).
    rewrite (Z.shiftl_mul_pow2 nf 2), (Z.shiftl_mul_pow2 n 2) by (clear; lia). change (2^2) with 4.
    replace (FAB + nf * 4) with (FAB + 4 * nf + 4 * 0) by (clear; lia). replace (CH + n * 4) with (CH + 4 * n) by (clear; lia).
    (* [comment removed for export] *)
    assert (DR' : 4096 <= FAB + 4 * nf /\ FAB + 4 * nf + 4 * n <= aceil /\ (FAB + 4 * nf) mod 4 = 0) by (clear - FABR NR NFR; try acb; Z.div_mod_to_equations; lia).
    assert (DISJ' : CH + 4 * n <= FAB + 4 * nf \/ FAB + 4 * nf + 4 * n <= CH) by (clear - SEPx NR NFR; try acb; lia).
    assert (NR' : 0 < n) by (clear - NR; try acb; lia).
    replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * 0)) by (f_equal; clear; lia).
    replace (FAB + 4 * (nf + n)) with (FAB + 4 * nf + 4 * n) in CJ1 by (clear; lia).
    replace (FAB + 4 * nf) with (FAB + 4 * nf + 4 * 0) in CJ1 at 1 by (clear; lia).
    callD (rcopy_loop _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m CH (FAB + 4 * nf) n ws
             CHR DR' DISJ' NR' WSL (Z.to_nat n) 0 _ m ltac:(hci; rewrite Z.sub_0_r; reflexivity) ltac:(hci; clear - NR; try acb; lia) MI MU0 WM CJ1 ARR0 SRC).
    clear MU0.
    lazymatch goal with H : u32arr _ _ (FAB + 4 * nf) ws |- _ => rename H into DARR end.
    lazymatch goal with H : u32arr _ _ CH ws |- _ => rename H into SRC' end.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (R + 80) _ RST ltac:(hci; clear; lia)) as [RS1 RS2]. clear RST.
    destruct (stk_split asegs _ _ (R + 88) _ RS2 ltac:(hci; clear; lia)) as [RS3 RS4]. clear RS2.
    destruct (stk_split asegs _ _ (R + 96) _ RS4 ltac:(hci; clear; lia)) as [RS5 RS6]. clear RS4.
    destruct (stk_cells _ _ _ RS3 ltac:(hci; clear; lia)) as [jst JST]. clear RS3.
    replace (R + 88 - (R + 80)) with 8 in JST by (clear; lia). change (Z.to_nat 8) with 8%nat in JST.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with H : rw_cells _ mq R _ |- _ => rename H into RIq end;
      lazymatch goal with H : rw_cells _ mq (R + 80) _ |- _ => rename H into J80 end;
      lazymatch goal with H : stk _ mq lo _ |- _ => rename H into STq end;
      lazymatch goal with H : mem_inv _ mq |- _ => rename H into MIq end
    end.
    change ([C8 (Z_to_bv 64 1152921504606846976); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
             C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)])
      with ([C8 (Z_to_bv 64 1152921504606846976); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (nf + n))] ++
            [C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]) in RIq.
    apply rw_cells_app in RIq. destruct RIq as [RIa RIbc]. apply rw_cells_app in RIbc. destruct RIbc as [RIb RIc].
    cbn [cells_size csize Nat.add] in RIb, RIc. change (Z.of_nat 16) with 16 in RIb, RIc. change (Z.of_nat 8) with 8 in RIc.
    replace (R + 16 + 8) with (R + 24) in RIc by (clear; lia).
    pose proof (stk_of_rw_cells asegs _ _ _ J80) as RS3. cbn [cells_size csize Nat.add] in RS3. change (Z.of_nat 8) with 8 in RS3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (RS8 : stk asegs mq (R + 80) (R + 96)) by
        (eapply stk_merge; [exact RS3| replace (R + 80 + 8) with (R + 88) by (clear; lia); exact RS5| clear; lia])
    end.
    clear RS3 J80.
    assert (NFR' : 0 <= nf + n < 2^64) by (clear - NFR NR; try acb; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      callD (mrto_spec _ (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq lo sb ARI c (nf + n)
               MIq ltac:(hci; rewrite E128; exact STq) LO ltac:(hci; rewrite E128; clear - HI; try acb; lia) eq_refl eq_refl eq_refl CR NFR' ARIR IRI ISB GOT PSC RIb RS8)
    end.
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
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    do 13 step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with H : stk _ mq lo _ |- _ => release_frame FR H (bv_unsigned sp) end;
      assert (RIn : rw_cells asegs mq R [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
                                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]);
      [ change ([C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)])
          with ([C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (nf + n))] ++
                [C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]);
        apply rw_cells_app; split; [assumption|]; apply rw_cells_app; split; cbn [cells_size csize Nat.add];
        [ change (Z.of_nat 16) with 16; assumption | change (Z.of_nat 16) with 16; change (Z.of_nat 8) with 8; replace (R + 16 + 8) with (R + 24) by (clear; lia); assumption ]
      | ];
      assert (RSTn : stk asegs mq (R + 69) (R + 128));
      [ eapply stk_merge; [eassumption| eapply stk_merge; [eassumption | eassumption | clear; lia] | clear; lia] | ];
      assert (FARRn : u32arr asegs mq FAB (wlist (rev fl) ++ ws));
      [ apply u32arr_app; split; [assumption|]; rewrite LFL; replace (FAB + 4 * Z.of_nat (Z.to_nat nf)) with (FAB + 4 * nf) by (clear - NFR; try acb; lia); assumption | ]
    end.
    apply evt_done. unfold rta_tail_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [exact RIn|]. split; [exact RSTn|]. split; [exact FARRn|]. split; [exact CJ2| assumption].
  Qed.
End Tail.

