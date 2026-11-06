(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit
  Lept_objkit RT_trans Ed_iface Ed_fpkit Ed_fp Numa_kit Ed_numa_ival.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition MLW (sb fr : Z) : list (Z * Z) := [(sb - 16, sb); (sb + 16, sb + 32); (fr + 32, fr + 36); (fr + 48, fr + 52)].
(* [comment removed for export] *)
Definition JMAX : Z := 20001.

(* [comment removed for export] *)
Definition meas_loop_post (gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 : word) (sb fr lo n : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (wv wn : word) (nj js : Z),
    ms' = MS (mkR ra' (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7
                  (Z_to_bv 64 n) s9 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) t3 t4 t5 t6)
             F' (Z_to_bv 64 0x12c6e8) (frm_clear fc') None m' (seg_rom asegs)
    /\ munch (MLW sb fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sb
    /\ rw_cells asegs m' (fr + 32) [C4 wv] /\ rw_cells asegs m' (fr + 48) [C4 wn]
    /\ rw_cells asegs m' (sb + 16) [C8 (Z_to_bv 64 nj); C8 (Z_to_bv 64 js)] /\ 0 <= nj <= n - 1 /\ 0 <= js <= (n - 1) * JMAX.

Lemma nth_error_ex' : forall {X} (l : list X) (i : nat), (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
  intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma outside_MLW_leaf : forall sb fr x, outside (MLW sb fr) x -> outside [(sb - 16, sb); (fr + 48, fr + 48 + 4)] x.
Proof. intros sb fr x H. unfold MLW in H. cbn [outside] in *. destruct H as (A & B & C & D & _). repeat split; try exact I; lia. Qed.

(* [comment removed for export] *)
Lemma sx32_int : forall k, - 2^31 <= k < 2^31 -> sx32 (Z_to_bv 64 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sub_int : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma swrap32_mod : forall x d, - 2^31 <= d < 2^31 -> (x - d) mod 2^64 = 0 -> bv_swrap 32 x = d.
Proof.
  intros x d Hd Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  apply Z.mod_divide in Hx; [| lia]. destruct Hx as [t Ht].
  replace (x + 2147483648) with ((d + 2147483648) + (t * 4294967296) * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma subw_int : forall a b, - 2^31 <= a - b < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b))) = Z_to_bv 64 (a - b).
Proof.
  intros a b H. f_equal. apply swrap32_mod; [exact H|]. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Zminus_mod. rewrite (Zminus_mod (a mod 2 ^ 64) (b mod 2 ^ 64)). rewrite !Z.mod_mod by lia. rewrite <- (Zminus_mod a b). rewrite Z.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ints_nth_ok : forall vals ks i k, numa_ints vals ks -> nth_error ks i = Some k -> -1 <= k <= 20000.
Proof.
  intros vals ks i k [_ F] H. rewrite Forall_forall in F. specialize (F k (nth_error_In _ _ H)). unfold loc_ok, LOC_LO, LOC_HI in F. exact F.
Qed.

Lemma meas_loop : forall (k : nat) (i : Z)
    (ra a0 a1 a2 a3 a4 a5 a6 a7 gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (sb fr lo n : Z) (live : list (Z * Z)) (na cap arr : Z) (vals : list word) (ks : list Z) (wn : word) (kp nj js : Z),
  Z.of_nat k = n - i -> 1 <= i < n -> n <= 20000 ->
  rw_cells asegs m (sb + 16) [C8 (Z_to_bv 64 nj); C8 (Z_to_bv 64 js); C8 (Z_to_bv 64 (fr + 64))] ->
  0 <= nj <= i - 1 -> 0 <= js <= (i - 1) * JMAX ->
  rw_cells asegs m (sb + 48) [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 1)] ->
  nth_error ks (Z.to_nat (i - 1)) = Some kp -> rw_cells asegs m (fr + 32) [C4 (Z_to_bv 64 kp)] ->
  rw_cells asegs m (fr + 48) [C4 wn] -> rw_cells asegs m (fr + 64) [C8 (Z_to_bv 64 na)] ->
  rw_cells asegs m (fr / 8 + SHB + 6) [C1 (Z_to_bv 8 4)] ->
  numa_obj live m na cap arr vals -> numa_ints vals ks -> Z.of_nat (length ks) = n ->
  (forall b kk x, In (b, kk) live -> b <= x < b + kk -> outside (MLW sb fr) x) ->
  acc asegs m na 32 -> acc asegs m arr (4 * cap) ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> ED_RO m ->
  mem_inv asegs m -> stk asegs m lo sb ->
  lo <= sb - 16 -> sb + 208 <= 2^47 -> sb mod 16 = 0 -> 0x10007fff8000 <= lo ->
  na + 32 <= lo -> arr + 4 * cap <= lo -> fr + 128 <= lo ->
  (na + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= na) -> (na + 32 <= 0x10000 \/ SEGTOP_A <= na) ->
  (arr + 4 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * cap <= 0x10000 \/ SEGTOP_A <= arr) ->
  (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) -> SEGTOP_A <= fr -> fr mod 64 = 0 ->
  (fr + 128 <= na \/ na + 32 <= fr) -> (fr + 128 <= arr \/ arr + 4 * cap <= fr) ->
  evt asegs (meas_loop_post gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 sb fr lo n m)
    (MS (mkR ra (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
              (Z_to_bv 64 i) s9 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x12c4a0) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra a0 a1 a2 a3 a4 a5 a6 a7 gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 F fc m sb fr lo n live na cap arr vals ks wn kp nj js
    HK HI HN SP16 NJB JSB SP48 HKP VAL NVAL NAP SHN NOBJ NINT KLEN LOUT ACCn ACCa G1 G2 RO MI ST LO SHI SAL LOH NLO ALO FLO NSH NSEG ASH ASEG FRSH FRSEG FR64 FNA FARR.
  { lia. }
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (NLEN & NCAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NNE).
  destruct (nth_error_ex' ks (Z.to_nat i) ltac:(lia)) as [ki Hki].
  pose proof (ints_nth_ok _ _ _ _ NINT Hki) as KI. pose proof (ints_nth_ok _ _ _ _ NINT HKP) as KP.
  destruct HI as [HIa HIb]. destruct NJB as [NJa NJb]. destruct JSB as [JSa JSb]. destruct KI as [KIa KIb]. destruct KP as [KPa KPb].
  unfold JMAX in *.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(sb - 16, sb); (sb + 16, sb + 32); (fr + 32, fr + 36); (fr + 48, fr + 52)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lwalk [e_numaGetIValue].
  eapply evt_cut.
  { eapply (numaGetIValue_evt _ gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 i) s9 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) t3 t4 t5 t6
              F fc m sb lo live na cap arr vals ks i (fr + 48) ki wn);
      first [ exact NOBJ | exact NINT | exact ACCn | exact ACCa | exact Hki | exact NVAL | exact G1 | exact G2 | exact RO | exact MI | exact ST
            | apply (acc_ushadow asegs m (fr + 48) 4); [clear - FR64; Z.div_mod_to_equations; lia | lia | lia
                | change (ushadow 4) with [Z_to_bv 8 4]; replace (shad (fr + 48)) with (fr / 8 + 2147450880 + 6) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                  destruct SHN as [[_ B] _]; exact B ]
            | unfold SEGTOP_A; clear - HIa HIb HN LO SHI SAL LOH NLO ALO FLO NSH NSEG ASH ASEG FRSH FRSEG FR64 FNA FARR NA0 AR0 NCAP; first [lia | Z.div_mod_to_equations; lia] ]. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & F' & fc' & m' & -> & MU' & WM' & MI' & ST' & NVAL').
  rewrite (ret_pc_even 0x12c4b4) by (lia || reflexivity).
  (* [comment removed for export] *)
  assert (AGL : agree_on (outside [(sb - 16, sb); (fr + 48, fr + 48 + 4)]) m m') by (intros x Hx; exact (MU' x Hx)).
  assert (SHR : forall x, fr / 8 + 2147450880 <= x <= fr / 8 + 2147450880 + 16 -> outside [(sb - 16, sb); (fr + 48, fr + 48 + 4)] x).
  { intros x Hx. cbn [outside]. clear - Hx FRSH FRSEG LOH LO FLO SHI. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  repeat match goal with
  | H : rw_cells asegs m ?A ?cs |- _ =>
      lazymatch A with
      | (fr + 48) => clear H
      | (fr / 8 + _ + _) => apply (rw_cells_agree_nw asegs m m' A cs) in H;
          [| eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply SHR; clear - Hx; lia]
      | _ => apply (rw_cells_agree_nw asegs m m' A cs) in H;
          [| eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside];
             clear - Hx LO FLO; repeat split; try exact I; lia]
      end
  | H : ro_cells asegs m ?A ?cs |- _ =>
      apply (ro_cells_agree asegs m m' A cs) in H;
        [| eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside];
           clear - Hx LO FLO LOH FRSEG; repeat split; try exact I; lia]
  end.
  assert (RO' : ED_RO m').
  { unfold ED_RO, RO_SIGN_TAB, RO_HALF, RO_GUARD_LO, RO_GUARD_HI in *. destruct RO as (RO1 & RO2 & RO3 & RO4).
    split; [| split; [| split]]; [apply (ro_cells_agree asegs m m' _ _ RO1)| apply (ro_cells_agree asegs m m' _ _ RO2)| apply (ro_cells_agree asegs m m' _ _ RO3)| apply (ro_cells_agree asegs m m' _ _ RO4)];
      (eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside];
       clear - Hx LO FLO LOH FRSEG; repeat split; try exact I; lia). }
  assert (NOBJ' : numa_obj live m' na cap arr vals).
  { apply (numa_obj_keep live m m' na cap arr vals); [| exact NOBJ]. intros b kk Hin a Ha. apply MU'.
    apply outside_MLW_leaf. exact (LOUT b kk (bv_unsigned a) Hin Ha). }
  assert (ACCn' : acc asegs m' na 32).
  { apply (acc_transport _ m m' na 32 ACCn MU'); [lia|]. unfold shad, SHB. cbn [disjoint_from].
    clear - NLO LOH LO NSH FRSH FRSEG NA0 SHI FLO. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  assert (ACCa' : acc asegs m' arr (4 * cap)).
  { apply (acc_transport _ m m' arr (4 * cap) ACCa MU'); [lia|]. unfold shad, SHB. cbn [disjoint_from].
    clear - ALO LOH LO ASH FRSH FRSEG AR0 NCAP SHI FLO. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  pose proof (munch_trans [(sb - 16, sb); (sb + 16, sb + 32); (fr + 32, fr + 36); (fr + 48, fr + 52)] _ _ _ MU (munch_weaken _ _ m m' (outside_MLW_leaf sb fr) MU')) as MU2.
  pose proof (wmono_trans asegs _ _ _ WM WM') as WM2.
  clear MU WM AGL SHR RO NOBJ ACCn ACCa MI ST MU' WM'.
  rename MU2 into MU. rename WM2 into WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(sb + 16, sb + 32); (fr + 32, fr + 36)] m') as MUS.
  (* [comment removed for export] *)
  assert (TAIL : forall (mx : mem) (a1x a2x a3x a4x a5x a6x a7x : word) (njx jsx : Z),
    rw_cells asegs mx (sb + 16) [C8 (Z_to_bv 64 njx); C8 (Z_to_bv 64 jsx); C8 (Z_to_bv 64 (fr + 64))] ->
    0 <= njx <= i -> 0 <= jsx <= i * 20001 ->
    rw_cells asegs mx (sb + 48) [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 1)] ->
    rw_cells asegs mx (fr + 32) [C4 (Z_to_bv 64 kp)] -> rw_cells asegs mx (fr + 48) [C4 (Z_to_bv 64 ki)] -> rw_cells asegs mx (fr + 64) [C8 (Z_to_bv 64 na)] ->
    rw_cells asegs mx (fr / 8 + 2147450880 + 6) [C1 (Z_to_bv 8 4)] ->
    ro_cells asegs mx 1897472 [C8 (Z_to_bv 64 1985336)] -> ro_cells asegs mx 1985336 [C8 (Z_to_bv 64 2147450880)] ->
    mem_inv asegs mx -> stk asegs mx lo sb ->
    munch [(sb - 16, sb); (sb + 16, sb + 32); (fr + 32, fr + 36); (fr + 48, fr + 52)] m mx -> wmono asegs m mx ->
    munch [(sb + 16, sb + 32); (fr + 32, fr + 36)] m' mx ->
    evt asegs (meas_loop_post gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 sb fr lo n m)
      (MS (mkR (Z_to_bv 64 0x12c4b4) (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) (Z_to_bv 64 ki) a1x a2x a3x a4x a5x a6x a7x s2 s3 s4 s5 s6 s7
                (Z_to_bv 64 i) s9 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) t3 t4 t5 t6)
          F' (Z_to_bv 64 0x12c490) (frm_clear fc') None mx (seg_rom asegs))).
  { clear SP16 SP48 VAL NVAL' NAP SHN G1 G2 MI' ST' MU WM MUS.
    intros mx a1x a2x a3x a4x a5x a6x a7x njx jsx SP16 [NXa NXb] [JXa JXb] SP48 VAL NVAL NAP SHN G1 G2 MI ST MU WM MUS.
    lwalk [0x12c4a0; 0x12c6e8].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      assert (NOBJ0 : numa_obj live m0 na cap arr vals)
        by (apply (numa_obj_keep live m' m0 na cap arr vals); [| exact NOBJ'];
            let b := fresh "b" in let kk := fresh "kk" in let Hin := fresh "Hin" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros b kk Hin a Ha; apply MUS; pose proof (LOUT b kk (bv_unsigned a) Hin Ha) as O; unfold MLW in O; cbn [outside] in O |- *; tauto);
      assert (RO0 : ED_RO m0)
        by (unfold ED_RO, RO_SIGN_TAB, RO_HALF, RO_GUARD_LO, RO_GUARD_HI in *; destruct RO' as (RO1 & RO2 & RO3 & RO4);
            split; [| split; [| split]];
            [ apply (ro_cells_agree asegs m' m0 _ _ RO1) | apply (ro_cells_agree asegs m' m0 _ _ RO2) | apply (ro_cells_agree asegs m' m0 _ _ RO3) | apply (ro_cells_agree asegs m' m0 _ _ RO4) ];
            (intros x Hx; apply MUS; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; clear - Hx FRSEG LO LOH; lia));
      assert (ACCn0 : acc asegs m0 na 32)
        by (apply (acc_transport _ m' m0 na 32 ACCn' MUS); [lia|]; unfold shad, SHB; cbn [disjoint_from];
            clear - NLO LOH LO NSH FRSH FRSEG NA0 SHI FLO; repeat split; try exact I; Z.div_mod_to_equations; lia);
      assert (ACCa0 : acc asegs m0 arr (4 * cap))
        by (apply (acc_transport _ m' m0 arr (4 * cap) ACCa' MUS); [lia|]; unfold shad, SHB; cbn [disjoint_from];
            clear - ALO LOH LO ASH FRSH FRSEG AR0 NCAP SHI FLO; repeat split; try exact I; Z.div_mod_to_equations; lia)
    end.
    destruct k as [|k'].
    - (* [comment removed for export] *)
      brT.
      apply evt_done. unfold meas_loop_post.
      do 9 eexists. exists F', fc'. eexists. do 2 eexists. exists njx, jsx.
      split; [replace (i + 1) with n by lia; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split; [eassumption|]. split; [eassumption|].
      split; [split_at SP16 2%nat SPx; exact SP16|].
      split; [lia| unfold JMAX; lia].
    - (* [comment removed for export] *)
      brF.
      assert (HKI : nth_error ks (Z.to_nat (i + 1 - 1)) = Some ki) by (replace (i + 1 - 1) with i by lia; exact Hki).
      eapply evt_cut.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
          eapply (IH (i + 1) _ _ _ _ _ _ _ _ _ gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 F' fc' m0 sb fr lo n live na cap arr vals ks (Z_to_bv 64 ki) ki njx jsx) end.
        all: first [ eassumption | lia | unfold JMAX; lia ].
      + intros ms' PO. apply evt_done. unfold meas_loop_post in PO |- *.
        destruct PO as (ra'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & F'' & fc'' & m'' & wv'' & wn'' & nj'' & js'' & E & MU'' & WM'' & R).
        do 9 eexists. exists F'', fc'', m'', wv'', wn'', nj'', js''.
        split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM WM'')| exact R]. }
  (* [comment removed for export] *)
  lwalk [0x12c4c4; 0x12c7d0].
  rewrite !(sx32_int ki) by (clear - KIa KIb; lia). rewrite ?(sx32_int kp) by (clear - KPa KPb; lia).
  rewrite (subw_int ki kp) by (clear - KIa KIb KPa KPb; lia). rewrite (sub_int ki kp).
  lwalk [0x12c4c8; 0x12c7d0].
  (* [comment removed for export] *)
  assert (JUMP : forall (ad : Z) (a2x : word), 0 <= ad <= 20001 ->
    evt asegs (meas_loop_post gp tp t0 t1 t2 s0 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 sb fr lo n m)
      (MS (mkR (Z_to_bv 64 0x12c4b4) (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) (Z_to_bv 64 ki) (Z_to_bv 64 ad) a2x a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7
                (Z_to_bv 64 i) s9 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) t3 t4 t5 t6)
          F' (Z_to_bv 64 0x12c4d8) (frm_clear fc') None m' (seg_rom asegs))).
  { intros ad a2x [ADa ADb].
    lwalk [0x12c490; 0x12c4e0; 0x12c7d0].
    destruct (Z_lt_ge_dec ad 1) as [J0|J1].
    - (* [comment removed for export] *)
      brT.
      eapply (TAIL m' _ _ _ _ _ _ _ nj js); first [eassumption | lia].
    - (* [comment removed for export] *)
      brF.
      lwalk [0x12c490; 0x12c4e8; 0x12c7d0].
      rewrite (swrap32_small (nj + 1)) by (clear - NJa NJb HIb HN; lia).
      lwalk [0x12c490; 0x12c4fc; 0x12c7d0].
      (* [comment removed for export] *)
      assert (HR : ov_read_bytes asegs m' (wa (sb + 24)) 4 = Some (le4 (Z_to_bv 64 js))).
      { pose proof SP16 as [[_ B] _]. replace (sb + 24) with (sb + 16 + 8) by lia.
        rewrite (bytes_at_read asegs m' (sb + 16) _ 8 4 B); [| lia| cbn; lia]. reflexivity. }
      lwalk [0x12c490; 0x12c4f0; 0x12c7d0].
      rewrite (sx32_small js) by (clear - JSa JSb HIb HN; lia).
      lwalk [0x12c490; 0x12c4fc; 0x12c7d0].
      rewrite (swrap32_small (js + ad)) by (clear - JSa JSb ADa ADb HIb HN; lia).
      lwalk [0x12c490; 0x12c7d0].
      eapply (TAIL _ _ _ _ _ _ _ _ (nj + 1) (js + ad)); first [eassumption | lia]. }
  lstep.
  destruct (Z_lt_ge_dec (ki - kp) 0) as [DN|DP].
  - (* [comment removed for export] *)
    brF.
    lwalk [0x12c4d8; 0x12c7d0].
    replace (bv_swrap 32 (0 - Z.land (ki - kp) 18446744073709551615)) with (kp - ki).
    2: { symmetry. apply swrap32_mod; [clear - KIa KIb KPa KPb; lia|].
         change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
         replace (0 - (ki - kp) mod 2 ^ 64 - (kp - ki)) with ((ki - kp) - (ki - kp) mod 2 ^ 64) by lia.
         rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. }
    eapply (JUMP (kp - ki)). clear - DN KIa KIb KPa KPb. lia.
  - (* [comment removed for export] *)
    brT.
    eapply (JUMP (ki - kp)). clear - DP KIa KIb KPa KPb. lia.
Qed.
