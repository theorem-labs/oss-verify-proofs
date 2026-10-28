(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP SFModel Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits Fz_W1_bits2 Fz_W1_bioflags Fz_W1_sync Fz_W1_write Fz_W1_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma t_swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

Section Scan.
  Variables (x1 x2 gp tp t1 t2 x8 x9 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (DO j : Z) (bs : list byte).
  Hypothesis U : u8ro usegs m DO bs.
  Hypothesis HJ : 0 < j < 2 ^ 31 - 1.
  Hypothesis HL : j <= Z.of_nat (length bs).
  Hypothesis HDO : 0 < DO /\ DO + j < 2 ^ 63.
  Variable POST : machine_state -> Prop.

  (* [comment removed for export] *)
  Notation ST pc y5 y12 y13 y16 y17 :=
    (MS (mkR x1 x2 gp tp y5 t1 t2 x8 x9 (Z_to_bv 64 j) (Z_to_bv 64 DO) y12 y13 (Z_to_bv 64 1) (Z_to_bv 64 10) y16 y17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Hypothesis NEXT : forall k y5 y13 y16 y17, 1 <= k <= j -> evt usegs POST (ST 0x1836d8 y5 (Z_to_bv 64 k) y13 y16 y17).

  Lemma gets_scan : forall (r : nat) (t : Z) y5, Z.of_nat r = j - t -> 0 <= t < j ->
    evt usegs POST (ST 0x1836a4 y5 (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (j - t)) (Z_to_bv 64 (DO + t)) (Z_to_bv 64 (DO + t))).
  Proof.
    induction r as [|r IH]; intros t y5 Hr Ht; [lia|].
    assert (HN : exists b, nth_error bs (Z.to_nat t) = Some b).
    { destruct (nth_error bs (Z.to_nat t)) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia. }
    destruct HN as [b Hb].
    pose proof (u8ro_read usegs m DO bs t b _ U Hb ltac:(lia) eq_refl) as RD.
    zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    zstep. zstep. zstep.
    rewrite ?(unsigned_lit (DO + t)) by lia. try change (bv_wrap 64 1) with 1.
    replace (DO + t <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. th_if_lit.
    zstep. ubs_if.
    zstep. zstep. if_cases KN; zify_cond KN.
    - apply NEXT. lia.
    - zstep. zstep. zstep. zstep.
      zstep. if_cases KL; zify_cond KL.
      + replace (DO + t + 1) with (DO + (t + 1)) by lia. replace (t + 2) with (t + 1 + 1) by lia. replace (j - t + -1) with (j - (t + 1)) by lia.
        apply IH; lia.
      + zstep. apply NEXT. lia.
  Qed.

  Lemma gets_scan0 : forall y5, evt usegs POST (ST 0x1836a4 y5 (Z_to_bv 64 1) (Z_to_bv 64 j) (Z_to_bv 64 DO) (Z_to_bv 64 DO)).
  Proof.
    intros y5. pose proof (gets_scan (Z.to_nat j) 0 y5 ltac:(lia) ltac:(lia)) as G.
    replace (DO + 0) with DO in G by lia. replace (j - 0) with j in G by lia. exact G.
  Qed.
End Scan.

Definition W1_gets_data_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off fl size OUT : Z) (rmaxw flw : word) (junk ojunk : list byte),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 size -> 0 < BI -> 0 < OUT -> 2 <= size < 2 ^ 31 ->
    rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < RP -> rw_cells usegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off -> off < len -> len <= max -> max < 2 ^ 31 - 1 -> D + max < 2 ^ 63 ->
    length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    length ojunk = Z.to_nat size -> rw_cells usegs m OUT [CB (Z.to_nat size) ojunk] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 128 ->
    BI + 72 <= lo -> BB + 16 <= lo -> RP + 32 <= lo -> D + max <= lo ->
    (D + max <= RP \/ RP + 32 <= D) -> (OUT + size <= D \/ D + max <= OUT) -> (OUT + size <= RP \/ RP + 32 <= OUT) ->
    tbox ((OUT + size <= lo \/ bv_unsigned sp <= OUT) /\ (OUT + size <= BI + 48 \/ BI + 52 <= OUT)
          /\ (BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48) /\ (BI + 52 <= BB \/ BB + 16 <= BI + 48)
          /\ (OUT + size <= BB \/ BB + 16 <= OUT) /\ (BB + 16 <= RP \/ RP + 32 <= BB)) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rmaxw' : word) (fl' k : Z) (ojunk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ 1 <= k <= Z.min (len - off) (size - 1)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + size); (RP, RP + 24)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 fl')]
                 /\ rw_cells usegs m' RP (readp_cells len D (off + k) rmaxw' flw)
                 /\ length ojunk' = Z.to_nat size /\ nth_error ojunk' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ rw_cells usegs m' OUT [CB (Z.to_nat size) ojunk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1835f0) fc None m (seg_rom usegs)).

Theorem W1_gets_data_proof : W1_gets_data_stmt.
Proof.
  unfold W1_gets_data_stmt, readp_cells. intros until ojunk.
  intros -> -> -> HBI HOUT HSZ FLC FLOK PTRC HBB HBB63 BBC HRP RPC HD HOFF0 HOFF HLEN HMAX HD63 LJ DBLK LOJ OUTB ALBI ALBB ALRP ST LO0 LO SBI SBB SRP SD APDR APOD APOR BOX MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + size); (RP, RP + 24)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (fl_ok_sel fl FLOK) as SEL. destruct FLOK as [FLR FLB].
  pose proof (rw_cells_bound _ _ _ _ OUTB) as OB. cbn [cells_size csize Nat.add] in OB. rewrite Nat.add_0_r, Z2Nat.id in OB by lia.
  box RPC. box DBLK. box OUTB.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MUp. pose proof (wmono_refl usegs m) as WMp.
  ths. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 7 ths.
  ths. ubs_if. ths. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. rewrite (t_sx32_small fl) by lia. ths. ths. ths. ths.
  rewrite SEL.
  ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  box BBC.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 48, BI + 52)]%Z ma) as MUq.
  tcallr W1_bio_clear15_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox RPC. unbox DBLK. unbox OUTB. unbox BBC. unfold tbox in BOX. destruct BOX as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (RPCb : rw_cells usegs mb RP [C8 (Z_to_bv 64 (len - off)); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 flw])
    by (eapply rw_cells_transport; [exact RPC| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (DBLKb : rw_cells usegs mb D [CB (Z.to_nat max) junk])
    by (eapply rw_cells_transport; [exact DBLK| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (OUTBb : rw_cells usegs mb OUT [CB (Z.to_nat size) ojunk])
    by (eapply rw_cells_transport; [exact OUTB| exact MUp| exact WMp| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (BBCb : ro_cells usegs mb BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)])
    by (eapply ro_cells_transport; [exact BBC| exact MUq| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  clear RPC DBLK OUTB BBC MUp WMp MUq B5.
  (* [comment removed for export] *)
  ths. ubs_if. ths. ths. ubs_if.
  ths. ths. if_cases KS; zify_cond KS; rewrite (swrap32_small (size + -1)) in KS by lia; signed_lits_in KS. { exfalso. lia. }
  ths. ths. ths. ths. if_cases KI; zify_cond KI. { exfalso. rewrite ?unsigned_lit in KI by lia. lia. }
  ths. if_cases KJ; zify_cond KJ; rewrite ?(swrap32_small (size + -1)) in KJ by lia; signed_lits_in KJ.
  - (* [comment removed for export] *)
    ths. ths. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply andb_false_iff in KZ. destruct KZ as [KZ|KZ]; apply Z.ltb_ge in KZ; lia. }
    ths. ths. rewrite ?(t_sextw_small (len - off)) by lia.
    ths. ths. ths. ths. ths.
    rewrite ?v_sltu_b2z, ?(unsigned_lit 0), ?(unsigned_lit (D + off)) by lia.
    replace (0 <? D + off) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    destruct (rw_cells_CB_split_at usegs mb D (Z.to_nat max) junk (Z.to_nat off) ltac:(lia) DBLKb) as [_ DB].
    rewrite Z2Nat.id in DB by lia.
    pose proof (rw_cells_bytes_at usegs mb (D + off) _ DB) as UB. cbn [cells_bytes cbytes] in UB. rewrite app_nil_r in UB. clear DB.
    eapply gets_scan0 with (bs := skipn (Z.to_nat off) junk); [exact UB| lia| rewrite skipn_length; lia| lia|].
    intros k y5 y13 y16 y17 HK.
    ths. rewrite ?(t_sextw_small k) by lia. ths. ths. ths.
    destruct (rw_cells_CB_split_at usegs mb OUT (Z.to_nat size) ojunk (Z.to_nat k) ltac:(lia) OUTBb) as [OA OR].
    rewrite Z2Nat.id in OR by lia. clear OUTBb.
    assert (KSZ : k < size) by lia.
    assert (APODk : OUT + k <= D \/ D + max <= OUT) by (clear - APOD KSZ; lia).
    assert (APORk : OUT + k <= RP \/ RP + 32 <= OUT) by (clear - APOR KSZ; lia).
    assert (BOXk : tbox ((OUT + k <= lo \/ bv_unsigned sp + -48 <= OUT) /\ (OUT + k <= BI + 48 \/ BI + 52 <= OUT)
                         /\ (BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48)))
      by (unfold tbox; clear - B1 B2 B3 B4 KSZ; repeat split; lia).
    assert (ORAT : forall mx, munch [(bv_unsigned sp + -48 - 80, bv_unsigned sp + -48); (BI + 48, BI + 52); (OUT, OUT + k); (RP, RP + 24)]%Z mb mx -> wmono usegs mb mx ->
                              rw_cells usegs mx (OUT + k) [CB (Z.to_nat size - Z.to_nat k) (skipn (Z.to_nat k) ojunk)]).
    { intros mx MX WX. eapply rw_cells_transport; [exact OR| exact MX| exact WX|]. clear - APOR B1 B2 KSZ HK OB LO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    clear OR.
    pose proof (munch_refl [(bv_unsigned sp + -48 - 80, bv_unsigned sp + -48); (BI + 48, BI + 52); (OUT, OUT + k); (RP, RP + 24)]%Z mb) as MUr. pose proof (wmono_refl usegs mb) as WMr.
    box B2. box B3. box B4. box B6. box B7. box APOD. box APOR.
    pose proof W1_read_data_proof as RD. unfold W1_read_data_stmt, readp_cells in RD.
    tcall (RD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BI BB BM RP D len max off (Z.land fl 18446744073709551600) k OUT rmaxw flw junk
              (firstn (Z.to_nat k) ojunk)).
    all: try first [eassumption | reflexivity | lia | rewrite firstn_length; lia | apply fl_ok_land; [split; assumption| lia]].
    clear RD. cbv beta delta [mkR]. rewrite (Z.min_l k (len - off)) in * by lia.
    pose proof (ORAT _ MUr WMr) as OR1. clear MUr WMr ORAT. unbox B2. unbox APOR.
    ths. if_cases KP; zify_cond KP. { exfalso. apply andb_false_iff in KP. destruct KP as [KP|KP]; apply Z.ltb_ge in KP; lia. }
    ths. ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    ths. ubs_if. ths. ubs_if.
    ths. ths.
    lazymatch goal with H : rw_cells usegs ?mm (OUT + k) _ |- _ =>
      destruct (rw_cells_CB_split_at usegs mm (OUT + k) (Z.to_nat size - Z.to_nat k)%nat (skipn (Z.to_nat k) ojunk) 1%nat ltac:(lia) H) as [OZ OT]; clear H end.
    remember (OUT + k) as Pk eqn:EPk.
    ths.
    do 6 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    subst Pk.
    lazymatch goal with Ha : rw_cells _ ?mm OUT [CB (Z.to_nat k) ?oj], Hz : rw_cells _ ?mm (OUT + k) [C1 _], Ht : rw_cells _ ?mm (OUT + k + Z.of_nat 1) _ |- _ =>
      apply (th_cells_congr usegs mm (OUT + k) _ [CB 1 [Z_to_bv 8 0]]) in Hz; [| reflexivity | reflexivity | cbn; tauto];
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ Ha ltac:(rewrite Z2Nat.id by lia; exact Hz)) as J1;
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, Z2Nat.id by lia; rewrite Z.add_assoc; exact Ht)) as J2 end.
    replace (Z.to_nat k + 1 + (Z.to_nat size - Z.to_nat k - 1))%nat with (Z.to_nat size) in J2 by lia.
    apply evt_done. do 15 eexists. eexists. exists k. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [lia|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [| split; [| exact J2]].
    + lazymatch goal with HL : length ?oj = Z.to_nat k |- _ => rewrite !length_app, HL end. cbn [length]. rewrite !skipn_length. lia.
    + lazymatch goal with HL : length ?oj = Z.to_nat k |- _ =>
        rewrite nth_error_app1 by (rewrite length_app, HL; cbn [length]; lia); rewrite nth_error_app2 by (rewrite HL; lia); rewrite HL, Nat.sub_diag; reflexivity end.
  - (* [comment removed for export] *)
    ths. if_cases KZ; zify_cond KZ.
    { exfalso. rewrite ?(swrap32_small (size + -1)) in KZ by lia. rewrite <- (unsigned_lit_land (size + -1)), unsigned_lit in KZ by lia.
      apply andb_false_iff in KZ. destruct KZ as [KZ|KZ]; apply Z.ltb_ge in KZ; lia. }
    rewrite ?(unsigned_lit size) by lia. rewrite ?(swrap32_small (size + -1)) by lia.
    ths. ths. rewrite ?(t_sextw_small (size + -1)) by lia.
    ths. ths. ths. ths. ths.
    rewrite ?v_sltu_b2z, ?(unsigned_lit 0), ?(unsigned_lit (D + off)) by lia.
    replace (0 <? D + off) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    destruct (rw_cells_CB_split_at usegs mb D (Z.to_nat max) junk (Z.to_nat off) ltac:(lia) DBLKb) as [_ DB].
    rewrite Z2Nat.id in DB by lia.
    pose proof (rw_cells_bytes_at usegs mb (D + off) _ DB) as UB. cbn [cells_bytes cbytes] in UB. rewrite app_nil_r in UB. clear DB.
    eapply gets_scan0 with (bs := skipn (Z.to_nat off) junk); [exact UB| lia| rewrite skipn_length; lia| lia|].
    intros k y5 y13 y16 y17 HK.
    ths. rewrite ?(t_sextw_small k) by lia. ths. ths. ths.
    destruct (rw_cells_CB_split_at usegs mb OUT (Z.to_nat size) ojunk (Z.to_nat k) ltac:(lia) OUTBb) as [OA OR].
    rewrite Z2Nat.id in OR by lia. clear OUTBb.
    assert (KSZ : k < size) by lia.
    assert (APODk : OUT + k <= D \/ D + max <= OUT) by (clear - APOD KSZ; lia).
    assert (APORk : OUT + k <= RP \/ RP + 32 <= OUT) by (clear - APOR KSZ; lia).
    assert (BOXk : tbox ((OUT + k <= lo \/ bv_unsigned sp + -48 <= OUT) /\ (OUT + k <= BI + 48 \/ BI + 52 <= OUT)
                         /\ (BI + 52 <= D \/ D + max <= BI + 48) /\ (BI + 52 <= RP \/ RP + 32 <= BI + 48)))
      by (unfold tbox; clear - B1 B2 B3 B4 KSZ; repeat split; lia).
    assert (ORAT : forall mx, munch [(bv_unsigned sp + -48 - 80, bv_unsigned sp + -48); (BI + 48, BI + 52); (OUT, OUT + k); (RP, RP + 24)]%Z mb mx -> wmono usegs mb mx ->
                              rw_cells usegs mx (OUT + k) [CB (Z.to_nat size - Z.to_nat k) (skipn (Z.to_nat k) ojunk)]).
    { intros mx MX WX. eapply rw_cells_transport; [exact OR| exact MX| exact WX|]. clear - APOR B1 B2 KSZ HK OB LO. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    clear OR.
    pose proof (munch_refl [(bv_unsigned sp + -48 - 80, bv_unsigned sp + -48); (BI + 48, BI + 52); (OUT, OUT + k); (RP, RP + 24)]%Z mb) as MUr. pose proof (wmono_refl usegs mb) as WMr.
    box B2. box B3. box B4. box B6. box B7. box APOD. box APOR.
    pose proof W1_read_data_proof as RD. unfold W1_read_data_stmt, readp_cells in RD.
    tcall (RD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo BI BB BM RP D len max off (Z.land fl 18446744073709551600) k OUT rmaxw flw junk
              (firstn (Z.to_nat k) ojunk)).
    all: try first [eassumption | reflexivity | lia | rewrite firstn_length; lia | apply fl_ok_land; [split; assumption| lia]].
    clear RD. cbv beta delta [mkR]. rewrite (Z.min_l k (len - off)) in * by lia.
    pose proof (ORAT _ MUr WMr) as OR1. clear MUr WMr ORAT. unbox B2. unbox APOR.
    ths. if_cases KP; zify_cond KP. { exfalso. apply andb_false_iff in KP. destruct KP as [KP|KP]; apply Z.ltb_ge in KP; lia. }
    ths. ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
    ths. ubs_if. ths. ubs_if.
    ths. ths.
    lazymatch goal with H : rw_cells usegs ?mm (OUT + k) _ |- _ =>
      destruct (rw_cells_CB_split_at usegs mm (OUT + k) (Z.to_nat size - Z.to_nat k)%nat (skipn (Z.to_nat k) ojunk) 1%nat ltac:(lia) H) as [OZ OT]; clear H end.
    remember (OUT + k) as Pk eqn:EPk.
    ths.
    do 6 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    subst Pk.
    lazymatch goal with Ha : rw_cells _ ?mm OUT [CB (Z.to_nat k) ?oj], Hz : rw_cells _ ?mm (OUT + k) [C1 _], Ht : rw_cells _ ?mm (OUT + k + Z.of_nat 1) _ |- _ =>
      apply (th_cells_congr usegs mm (OUT + k) _ [CB 1 [Z_to_bv 8 0]]) in Hz; [| reflexivity | reflexivity | cbn; tauto];
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ Ha ltac:(rewrite Z2Nat.id by lia; exact Hz)) as J1;
      pose proof (rw_cells_CB_join usegs mm OUT _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, Z2Nat.id by lia; rewrite Z.add_assoc; exact Ht)) as J2 end.
    replace (Z.to_nat k + 1 + (Z.to_nat size - Z.to_nat k - 1))%nat with (Z.to_nat size) in J2 by lia.
    apply evt_done. do 15 eexists. eexists. exists k. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [lia|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [| split; [| exact J2]].
    + lazymatch goal with HL : length ?oj = Z.to_nat k |- _ => rewrite !length_app, HL end. cbn [length]. rewrite !skipn_length. lia.
    + lazymatch goal with HL : length ?oj = Z.to_nat k |- _ =>
        rewrite nth_error_app1 by (rewrite length_app, HL; cbn [length]; lia); rewrite nth_error_app2 by (rewrite HL; lia); rewrite HL, Nat.sub_diag; reflexivity end.
Qed.
