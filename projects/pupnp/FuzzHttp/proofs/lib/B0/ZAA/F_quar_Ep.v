(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ATacA PEnv LJ LJU APrim APrimLem APrimPop APrimSpec APrimSpec2 APrimQ AFrame ASec AQuar.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ENQP.
Context {HC : HasCeiling}.
Variables (AL : alayout).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

Hypothesis RP : RPRIM_pop_stmt AL.
Hypothesis RPF : RPRIM_frame_stmt AL.

Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (q lo : Z) (l : list qbatch) (ch : qchunk) (hs : list (Z * Z)).

#[using="Type"] Lemma bytes_as_u64s : forall (k : nat) (bs : list byte), length bs = (8 * k)%nat -> exists ws, length ws = k /\ u64s ws = bs.
Proof.
  induction k as [|k IH]; intros bs Lb.
  - destruct bs; [exists []; split; reflexivity| cbn in Lb; lia].
  - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Lw & Ew).
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn [length]; lia|].
    cbn [u64s]. rewrite Ew, (InitStack.le8_of_bytes (firstn 8 bs)) by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.

#[using="Type"] Lemma u64arr_of_CB : forall (mm : mem) A (k : nat) bs, rw_cells asegs mm A [CB (8 * k) bs] -> exists ws, length ws = k /\ u64arr asegs mm A ws.
Proof.
  intros mm A k bs [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [Lb _].
  destruct (bytes_as_u64s k bs Lb) as (ws & Lw & Ew). exists ws. split; [exact Lw|].
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
  split; [rewrite Ew; exact BY|]. rewrite Lw. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia. exact WR.
Qed.

#[using="Type"] Lemma held_qb_in : forall (P0 : prim) (hs0 : list (Z * Z)) (l0 : list qbatch),
  held_ok P0 hs0 -> incl (map (fun b => (K_BCLASS, qb_v b)) l0) hs0 -> Forall (qb_in (p_au (get_cls P0 K_BCLASS))) l0.
Proof.
  intros P0 hs0 l0 [_ HF] INC. apply Forall_forall. intros b Hb.
  assert (HI : In (K_BCLASS, qb_v b) hs0) by (apply INC; apply (in_map (fun b => (K_BCLASS, qb_v b))); exact Hb).
  pose proof (proj1 (Forall_forall _ _) HF _ HI) as H1.
  destruct H1 as (_ & V0 & VB & VA & _). cbn [fst snd] in *. change (class_size K_BCLASS) with Q_BBYTES in *.
  unfold qb_in. split; [exact V0|]. split; [exact VA| exact VB].
Qed.

#[using="Type"] Lemma le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w EQ. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), EQ. reflexivity. Qed.

#[using="Type"] Lemma u64arr_of_C8_CB : forall (mm : mem) A (w : word) (k : nat) bs,
  rw_cells asegs mm A [C8 w; CB (8 * k) bs] -> exists ws, length ws = k /\ u64arr asegs mm A (w :: ws).
Proof.
  intros mm A w k bs R. apply (proj1 (rw_cells_app asegs mm A [C8 w] [CB (8 * k) bs])) in R as [R1 R2].
  cbn [cells_size csize Nat.add] in R2. destruct (u64arr_of_CB mm _ k bs R2) as (ws & Lw & [BY2 WR2]).
  exists ws. split; [exact Lw|]. destruct R1 as [[_ BY1] WR1]. cbn [cells_bytes cbytes cells_size csize Nat.add] in BY1, WR1. rewrite app_nil_r in BY1.
  split.
  - cbn [u64s]. apply bytes_at_app. split; [exact BY1|]. rewrite length_le8. exact BY2.
  - cbn [length]. destruct WR1 as (W0 & W1 & W2). destruct WR2 as (V0 & V1 & V2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_ge_dec i 8) as [Lt|Ge]; [apply W2; lia|].
    specialize (V2 (i - 8) ltac:(lia)). replace (A + Z.of_nat 8 + (i - 8)) with (A + i) in V2 by lia. exact V2.
Qed.

#[using="Type"] Lemma cache_alloc_held_ok : forall (P0 : prim) (hs0 : list (Z * Z)) (c : Z), held_ok P0 hs0 -> 1 <= c <= 31 -> length (pr_cls P0) = 32%nat ->
  pclass_wf c (get_cls P0 c) -> 0 < p_cnt (get_cls P0 c) ->
  held_ok (fst (cache_alloc P0 c)) ((c, snd (cache_alloc P0 c)) :: hs0).
Proof.
  intros P0 hs0 c HOK Hc LEN WF CNT.
  pose proof WF as (_ & CN & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). apply NoDup_ListNoDup in ND.
  unfold cache_alloc. destruct (cache_alloc_cls (get_cls P0 c) c) as [k' v0] eqn:EC. cbn [fst snd].
  pose proof (fun x => cache_pop_free (get_cls P0 c) c x CN CNT ND) as PF. cbn zeta in PF. rewrite EC in PF. cbn [fst snd] in PF.
  eapply (held_ok_pop P0 _ hs0 c v0 HOK Hc WF).
  - exact (proj1 (PF 0)).
  - intros c' NE. unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia.
  - rewrite get_cls_set_same by (try exact LEN; lia). exact (proj2 (proj2 (PF 0))).
  - intros x. rewrite get_cls_set_same by (try exact LEN; lia). exact (proj1 (proj2 (PF x))).
Qed.

Definition qlast_iv (l0 : list qbatch) : list (Z * Z) :=
  match rev l0 with [] => [] | b :: _ => [(qb_addr AL b, qb_addr AL b + Q_BBYTES)] end.
Definition enq_popW (P1 : prim) : list (Z * Z) :=
  [(q - 64, q); (THR + 2128, THR + 2132); (THR + 2784, THR + 2792); (TQ, TQ + 32)] ++ qlast_iv l
  ++ [(region AL K_BCLASS + 16 * snd (cache_alloc P1 K_BCLASS), region AL K_BCLASS + 16 * snd (cache_alloc P1 K_BCLASS) + Q_BBYTES)].

#[using="RP RPF"] Lemma enq_pop : forall (P1 : prim) (m1 : mem) (junk8 : list byte) (rra x5 x6 x7 r0 r1 a2 a6 a7 r2 r3 r4 r5 x28 x29 x30 x31 : word),
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 64 -> q <= 2^47 ->
  RPRIM AL P1 m1 -> prim_ok P1 -> 0 < p_cnt (get_cls P1 K_BCLASS) ->
  held_ok P1 hs -> incl (map (fun b => (K_BCLASS, qb_v b)) l) hs -> List.NoDup (map qb_v l) ->
  Z.of_nat (length l) < 2^32 -> qchunk_wf ch -> need_batch l = true ->
  qcache_rep AL m1 TQ l -> mem_inv asegs m1 -> stk asegs m1 lo (q + -64) ->
  rw_cells asegs m1 (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt asegs (fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (enq_popW P1) m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m' /\ stk asegs m' lo q
      /\ RPRIM AL (fst (cache_alloc P1 K_BCLASS)) m' /\ prim_ok (fst (cache_alloc P1 K_BCLASS))
      /\ qcache_rep AL m' TQ (q_enq l ch (snd (cache_alloc P1 K_BCLASS))))
    (MS (mkR rra (wz (q + -64)) gp (wz A0_TP) x5 x6 x7 r0 r1 (wz TQ) (wz CACHE) a2 (wz (qc_hdr AL ch)) (wz (qc_n ch))
             (wz (p_cnt (get_cls P1 K_BCLASS))) a6 a7 r2 r3 r4 r5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x37b3c) fc None m1 (seg_rom asegs)).
Proof.
  intros until x31. intros AO HLO CLO LOQ QHI RPR1 POK1 CNT1 HOK1 INC NDV LEN32 CHW NB QC1 MI1 ST1 FR1.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TL & _). pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 3%nat LP03. layout_apart_fact AO 0%nat 2%nat LP02.

  destruct (RP P1 m1 K_BCLASS RPR1 POK1 ltac:(lia) CNT1) as (INI & V0 & VAU & VAL & AUF & PENV & PCL & (ws & ARR & LWS & NTHW) & STATS & FCH & CLOSE).
  set (k1 := get_cls P1 K_BCLASS) in *. set (cnt := p_cnt k1) in *.
  set (v := nth (Z.to_nat (cnt - 1)) (p_chunks k1) 0) in *.
  change (class_size 24) with 8192 in *. change (max_count 24) with 2 in *.
  assert (WFk : 1 <= cnt <= 2).
  { destruct RPR1 as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & CR & _) & _). fold k1 in CR. fold cnt in CR.
    change (max_count 24) with 2 in CR. lia. }
  assert (V32 : 0 <= v < 2^28) by lia.
  unfold pcl_addr in PCL, ARR, CLOSE. replace (THR + CACHE_OFF + 80 * 24) with (THR + 2128) in PCL, ARR, CLOSE by lia.
  replace (THR + 2128 + 16) with (THR + 2144) in ARR by lia.
  replace (THR + 2768 + 16) with (THR + 2784) in STATS, CLOSE by lia.
  unfold prim_env in PENV.
  destruct FCH as [[jb FB] FS]. change (class_size 24) with 8192 in FB, FS. change (8192 / 8) with 1024 in FS.
  remember (region AL 24 + 16 * v) as NBA eqn:ENBA in *.
  assert (NBR : al_space AL + K_REGION <= NBA /\ NBA + 8192 <= al_space AL + K_SPACE) by (rewrite ENBA; unfold region; lia).
  assert (NB8 : NBA mod 8 = 0) by (rewrite ENBA; unfold region; clear - SPM VAL; Z.div_mod_to_equations; lia).
  assert (SHN : 2147450880 <= sh NBA /\ sh NBA + 1024 <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - NBR SP1 SP5; Z.div_mod_to_equations; lia).
  hide NB8. hide FS.

  hide T1. hide T5. hide LP02. hide T6. hide SPM.
  destruct QC1 as [TQC QL].

  assert (VFREE : In v (cls_free k1)).
  { unfold cls_free. apply in_or_app. right. unfold v. apply nth_In.
    destruct RPR1 as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & CE & _) & _). fold k1 in CE. fold cnt in CE. lia. }
  assert (VNL : ~ In v (map qb_v l)).
  { intros IN. apply in_map_iff in IN as (b0 & Eb0 & Hb0).
    assert (HI : In (K_BCLASS, qb_v b0) hs) by (apply INC; apply (in_map (fun b => (K_BCLASS, qb_v b))); exact Hb0).
    destruct HOK1 as [_ HF]. pose proof (proj1 (Forall_forall _ _) HF _ HI) as (_ & _ & _ & _ & NF). cbn [fst snd] in NF.
    apply NF. fold k1. rewrite Eb0. exact VFREE. }
  pose proof (held_qb_in P1 hs l HOK1 INC) as QBI. fold k1 in QBI.
  assert (B8 : p_au k1 mod 8 = 0).
  { destruct RPR1 as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & AUM & _) & _).
    fold k1 in AUM. change (class_size K_BCLASS) with 8192 in AUM. clear - AUM. Z.div_mod_to_equations. lia. }
  assert (LSPLIT : l = [] \/ exists l' b, l = l' ++ [b]).
  { destruct (rev l) as [|b r] eqn:ER; [left; apply (f_equal (@rev _)) in ER; rewrite rev_involutive in ER; exact ER|].
    right. exists (rev r), b. rewrite <- (rev_involutive l), ER. reflexivity. }
  destruct LSPLIT as [EL|(l' & b & EL)].
  -
    rewrite EL in TQC. cbn [length qfirst qlast rev qbytes fold_right Z.of_nat] in TQC.

  pose proof (munch_refl [(THR + 2128, THR + 2132); (THR + 2784, THR + 2792)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstep. zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep. zstep.

  assert (E4 : Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30 = 4 * (cnt - 1)).
  { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
    replace ((cnt + -1) * 2 ^ 32) with ((4 * (cnt - 1)) * 2 ^ 30) by lia. apply Z.div_mul. lia. }
  rewrite ?E4.
  assert (NTH : nth_error ws (Z.to_nat (cnt - 1)) = Some (wz v)).
  { rewrite <- NTHW. apply nth_error_nth'. rewrite LWS. lia. }
  pose proof (u32arr_read asegs _ (THR + 2144) ws (cnt - 1) _ (wa (THR + 2144 + 4 * (cnt - 1))) ARR NTH ltac:(lia) eq_refl) as HR.

  zstep.
  assert (ZX : zx32 (Z_to_bv 64 v) = Z_to_bv 64 v) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
  rewrite ?ZX. clear HR.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (THR + 2784)) = true) by (apply amo_aligned_intro_d; [lia| clear - T7; Z.div_mod_to_equations; lia]).
  amo_step_h AMO.
  hide T7.

  cbn [amo_val] in STATS. rewrite ?lit_add_lit in STATS.
  replace (cnt + -1) with (cnt - 1) in PCL by lia.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  assert (MUc : munch [(THR + 2128, THR + 2128 + 4); (THR + 2784, THR + 2768 + 24)] m1 mA) by (refine (munch_weaken _ _ _ _ _ MU); clear; sub_fp_solve).
  destruct (CLOSE _ MUc WM PCL STATS) as (RPR2 & POK2 & EV).
  set (PN1 := fst (cache_alloc P1 K_BCLASS)) in *.
  clear CLOSE MUc. clear PCL STATS ARR.

    apply (munch_extend _ [(q - 64, q); (TQ, TQ + 32); (NBA, NBA + 32)]) in MU. cbn [List.app] in MU.
    pose proof (munch_refl [(q - 64, q); (TQ, TQ + 32); (NBA, NBA + 32)] mA) as MU2. pose proof (wmono_refl asegs mA) as WM2.
    zstep. zstep.
    clear PENV.
    zstep. zstep. zstep. zstep. zstep.

    rewrite (Z.shiftl_mul_pow2 v 4) by lia. change (2 ^ 4) with 16.
    replace (v * 16 + (al_space AL + 103079215104)) with NBA by (rewrite ENBA; unfold region; lia).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
    zstep. zstep. zstep.
    zstep.

    pose proof (rw_cells_split_CB asegs mA NBA [] _ jb [] [32%nat; Z.to_nat 8160] FB ltac:(cbn [sum_nat]; lia)) as SPB.
    cbn [mk_CB_cells app] in SPB.
    apply (proj1 (rw_cells_app asegs mA NBA [_] [_])) in SPB as [FB0 FBR]. cbn [cells_size csize Nat.add] in FBR.
    change (Z.of_nat 32) with 32 in FBR. clear FB.
    remember (firstn 32 jb) as j32 eqn:Ej32. clear Ej32. remember (firstn (Z.to_nat 8160) (skipn 32 jb)) as jr eqn:Ejr. clear Ejr.
    hide FBR.
    sstep. zstep. sstep. zstep.

    zstep. if_true_z.
    zstep.
    sstep.
    zstep.
    do 3 zstep.
    do 7 zstep.
    zstep. replace (q + -64 + 64) with q by lia. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    apply evt_done. do 15 eexists. exists mZ.
    split; [reflexivity|].

    assert (HOKN : held_ok PN1 ((24, v) :: hs)).
    { rewrite <- EV. unfold PN1. destruct RPR1 as (LEN1 & _ & CLS1 & _). destruct (CLS1 24 ltac:(lia)) as (WF1 & _).
      apply cache_alloc_held_ok; [exact HOK1| lia| exact LEN1| exact WF1| exact CNT1]. }

    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).

    unhide FS. unhide FBR.
    pose proof (rw_cells_transport asegs _ m1 mZ _ _ FS MU WM ltac:(cbn [disjoint_from cells_size csize]; clear - T3 T4 SHN HLO CLO LOQ SP1 NBR; lia)) as TRz. clear FS. rename TRz into FS.
    pose proof (rw_cells_transport asegs _ mA mZ _ _ FBR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; clear - T3 T4 LP03 NBR SP2 CLO LOQ; lia)) as TRz. clear FBR. rename TRz into FBR.
    split. { unfold enq_popW, qlast_iv. rewrite EV, <- ENBA, EL. cbn [rev app]. refine (munch_weaken _ _ _ _ _ MU). clear. sub_fp_solve. }
    split; [exact WM|]. split; [exact MI1|].
    split. { pose proof (stk_release asegs mZ lo (q + -64) _ ST1 FR1 ltac:(lia)) as SR. cbn [cells_size csize Nat.add] in SR.
             replace (q + -64 + Z.of_nat 64) with q in SR by lia. exact SR. }
    split. { apply (RPF PN1 _ mA mZ RPR2 MU2 WM2). unfold prim_clear.
             repeat (apply Forall_cons || apply Forall_nil).
             - left. unfold prim_out. cbn [fst snd]. clear - LOQ CLO ACR T3 T4 SP2 SHS. repeat split; lia.
             - left. unfold prim_out. cbn [fst snd]. clear - LP03 T3 T4 SHS SHS0 SP1. repeat split; lia.
             - right. exists 24, v. split; [destruct HOKN as [_ HF]; exact (Forall_inv HF)|].
               left. unfold chunk_iv. cbn [fst snd]. change (class_size 24) with 8192. rewrite <- ENBA. lia. }
    split; [exact POK2|].
    rewrite EV, EL. unfold q_enq. cbn [rev]. set (bn := mkQB v (qc_n ch + 8192) [ch]).
    assert (EA : qb_addr AL bn = NBA) by (rewrite ENBA; reflexivity).
    unfold qcache_rep. split.
    + cbn [length qfirst qlast rev app qbytes fold_right]. rewrite EA. unfold bn at 1. cbn [qb_size].
      replace (qc_n ch + 8192 + 0) with (0 + (qc_n ch + 8192)) by lia. exact TQC.
    + cbn [qlist_rep]. split; [| exact I]. unfold qbatch_rep. rewrite EA. unfold bn. cbn [qb_size qb_chunks qb_count length map]. fold bn.
      apply (proj1 (rw_cells_app asegs mZ NBA [_; _; _] [_])) in FB0 as [FB3 FBH]. cbn [cells_size csize Nat.add] in FBH. change (Z.of_nat 24) with 24 in FBH.
      split; [exact FB3|]. split.
      * replace (Z.to_nat 8160) with (8 * 1020)%nat in FBR by lia.
        assert (HB : rw_cells asegs mZ (NBA + 24) [C8 (Z_to_bv 64 (qc_hdr AL ch)); CB (8 * 1020) jr]).
        { apply (proj2 (rw_cells_app asegs mZ (NBA + 24) [_] [_])). split; [exact FBH|]. cbn [cells_size csize Nat.add].
          replace (NBA + 24 + Z.of_nat 8) with (NBA + 32) by lia. exact FBR. }
        destruct (u64arr_of_C8_CB mZ _ _ _ _ HB) as (ws0 & LW0 & ARR0).
        exists (Z_to_bv 64 (qc_hdr AL ch) :: ws0). split; [exact ARR0|]. split; [cbn [length]; rewrite LW0; reflexivity| reflexivity].
      * change (Z.to_nat 1024) with 1024%nat in FS. exact FS.

  -
    assert (LENP : Z.of_nat (length l) = Z.of_nat (length l') + 1) by (rewrite EL, length_app; cbn [length]; lia).
    assert (BFULL : qb_count b = Q_BATCH) by (rewrite EL, need_batch_snoc in NB; apply Z.eqb_eq; exact NB).
    rewrite EL in QL, INC, NDV, QBI, VNL. apply qlist_rep_snoc in QL as [QLp QB]. destruct QB as (BC & (wsb & BARR & LWSb & FWSb) & BSH).
    hide BARR. hide BSH.
    apply Forall_app in QBI as [QBIp QBIb]. apply Forall_cons_iff in QBIb as [(BV0 & BVA & BVF) _].
    assert (BVF2 := Z.le_trans _ _ _ BVF AUF). clear BVF. rename BVF2 into BVF.
    assert (SHB : 2147450880 <= sh (qb_addr AL b) /\ sh (qb_addr AL b) + 1024 <= 17594333495296) by (unfold sh, SHADOW_OFF, qb_addr, region; clear - BV0 BVF SP1 SP5; Z.div_mod_to_equations; lia).
    assert (BA : al_space AL + K_REGION <= qb_addr AL b /\ qb_addr AL b + Q_BBYTES <= al_space AL + K_SPACE) by (unfold qb_addr, region; clear - BV0 BVF; lia).
    assert (ELA : qlast AL l = qb_addr AL b) by (rewrite EL; apply qlast_snoc).
    rewrite ELA in TQC.
    assert (BNE : qb_v b <> v). { intros X. apply VNL. rewrite map_app. apply in_or_app. right. left. exact X. }
    assert (APB : qb_addr AL b + 8192 <= NBA \/ NBA + 8192 <= qb_addr AL b).
    { pose proof (chunks_apart 24 (qb_v b) v ltac:(lia) BVA VAL BNE) as AP. change (class_size 24) with 8192 in AP. rewrite ENBA. unfold qb_addr. clear - AP. lia. }

  pose proof (munch_refl [(THR + 2128, THR + 2132); (THR + 2784, THR + 2792)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstep. zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep. zstep.

  assert (E4 : Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30 = 4 * (cnt - 1)).
  { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
    replace ((cnt + -1) * 2 ^ 32) with ((4 * (cnt - 1)) * 2 ^ 30) by lia. apply Z.div_mul. lia. }
  rewrite ?E4.
  assert (NTH : nth_error ws (Z.to_nat (cnt - 1)) = Some (wz v)).
  { rewrite <- NTHW. apply nth_error_nth'. rewrite LWS. lia. }
  pose proof (u32arr_read asegs _ (THR + 2144) ws (cnt - 1) _ (wa (THR + 2144 + 4 * (cnt - 1))) ARR NTH ltac:(lia) eq_refl) as HR.

  zstep.
  assert (ZX : zx32 (Z_to_bv 64 v) = Z_to_bv 64 v) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
  rewrite ?ZX. clear HR.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (THR + 2784)) = true) by (apply amo_aligned_intro_d; [lia| clear - T7; Z.div_mod_to_equations; lia]).
  amo_step_h AMO.
  hide T7.

  cbn [amo_val] in STATS. rewrite ?lit_add_lit in STATS.
  replace (cnt + -1) with (cnt - 1) in PCL by lia.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  assert (MUc : munch [(THR + 2128, THR + 2128 + 4); (THR + 2784, THR + 2768 + 24)] m1 mA) by (refine (munch_weaken _ _ _ _ _ MU); clear; sub_fp_solve).
  destruct (CLOSE _ MUc WM PCL STATS) as (RPR2 & POK2 & EV).
  set (PN1 := fst (cache_alloc P1 K_BCLASS)) in *.
  clear CLOSE MUc. clear PCL STATS ARR.

    apply (munch_extend _ [(q - 64, q); (TQ, TQ + 32); (NBA, NBA + 32); (qb_addr AL b, qb_addr AL b + 8)]) in MU. cbn [List.app] in MU.
    pose proof (munch_refl [(q - 64, q); (TQ, TQ + 32); (NBA, NBA + 32); (qb_addr AL b, qb_addr AL b + 8)] mA) as MU2. pose proof (wmono_refl asegs mA) as WM2.
    zstep. zstep.
    clear PENV.
    zstep. zstep. zstep. zstep. zstep.

    rewrite (Z.shiftl_mul_pow2 v 4) by lia. change (2 ^ 4) with 16.
    replace (v * 16 + (al_space AL + 103079215104)) with NBA by (rewrite ENBA; unfold region; lia).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
    zstep. zstep. zstep.
    zstep.

    pose proof (rw_cells_split_CB asegs mA NBA [] _ jb [] [32%nat; Z.to_nat 8160] FB ltac:(cbn [sum_nat]; lia)) as SPB.
    cbn [mk_CB_cells app] in SPB.
    apply (proj1 (rw_cells_app asegs mA NBA [_] [_])) in SPB as [FB0 FBR]. cbn [cells_size csize Nat.add] in FBR.
    change (Z.of_nat 32) with 32 in FBR. clear FB.
    remember (firstn 32 jb) as j32 eqn:Ej32. clear Ej32. remember (firstn (Z.to_nat 8160) (skipn 32 jb)) as jr eqn:Ejr. clear Ejr.
    hide FBR.
    sstep. zstep. sstep. zstep.

    zstep. if_false_z.
    zstep.
    zstep.
    zstep. zstep.
    zstep.
    zstep.
    do 3 zstep.
    do 7 zstep.
    zstep. replace (q + -64 + 64) with q by lia. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    apply evt_done. do 15 eexists. exists mZ.
    split; [reflexivity|].

    assert (HOKN : held_ok PN1 ((24, v) :: hs)).
    { rewrite <- EV. unfold PN1. destruct RPR1 as (LEN1 & _ & CLS1 & _). destruct (CLS1 24 ltac:(lia)) as (WF1 & _).
      apply cache_alloc_held_ok; [exact HOK1| lia| exact LEN1| exact WF1| exact CNT1]. }

    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
    assert (SHS1 : sh (al_space AL + K_SPACE) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).

    unhide FS. unhide FBR. unhide BARR. unhide BSH.
    pose proof (rw_cells_transport asegs _ m1 mZ _ _ FS MU WM ltac:(cbn [disjoint_from cells_size csize]; clear - T3 T4 SHN HLO CLO LOQ SP1 NBR BA; lia)) as TRz. clear FS. rename TRz into FS.
    pose proof (rw_cells_transport asegs _ mA mZ _ _ FBR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; clear - T3 T4 LP03 NBR SP2 CLO LOQ APB; lia)) as TRz. clear FBR. rename TRz into FBR.
    pose proof (rw_cells_transport asegs _ m1 mZ _ _ BSH MU WM ltac:(cbn [disjoint_from cells_size csize]; clear - T3 T4 SHB HLO CLO LOQ SP1 NBR BA; lia)) as TRz. clear BSH. rename TRz into BSH.
    pose proof (u64arr_transport asegs _ m1 mZ _ _ BARR MU WM ltac:(cbn [disjoint_from]; rewrite LWSb; clear - T3 T4 LP03 BA SP2 CLO LOQ APB; lia)) as TRz. clear BARR. rename TRz into BARR.
    split. { unfold enq_popW, qlast_iv. rewrite EV, <- ENBA, EL, rev_app_distr. cbn [rev app]. refine (munch_weaken _ _ _ _ _ MU). clear. sub_fp_solve. }
    split; [exact WM|]. split; [exact MI1|].
    split. { pose proof (stk_release asegs mZ lo (q + -64) _ ST1 FR1 ltac:(lia)) as SR. cbn [cells_size csize Nat.add] in SR.
             replace (q + -64 + Z.of_nat 64) with q in SR by lia. exact SR. }
    split. { apply (RPF PN1 _ mA mZ RPR2 MU2 WM2). unfold prim_clear.
             repeat (apply Forall_cons || apply Forall_nil).
             - left. unfold prim_out. cbn [fst snd]. clear - LOQ CLO ACR T3 T4 SP2 SHS. repeat split; lia.
             - left. unfold prim_out. cbn [fst snd]. clear - LP03 T3 T4 SHS SHS0 SP1. repeat split; lia.
             - right. exists 24, v. split; [destruct HOKN as [_ HF]; exact (Forall_inv HF)|].
               left. unfold chunk_iv. cbn [fst snd]. change (class_size 24) with 8192. rewrite <- ENBA. lia.
             - right. exists 24, (qb_v b). split.
               + destruct HOKN as [_ HF]. apply Forall_inv_tail in HF. apply (proj1 (Forall_forall _ _) HF). apply INC. rewrite map_app. apply in_or_app. right. left. reflexivity.
               + left. unfold chunk_iv. cbn [fst snd]. unfold qb_addr. change (class_size 24) with 8192. lia. }
    split; [exact POK2|].
    rewrite EV. rewrite EL at 1. rewrite q_enq_snoc, BFULL. change (1021 =? 1021) with true. cbv iota.
    set (bn := mkQB v (qc_n ch + 8192) [ch]).
    assert (EA : qb_addr AL bn = NBA) by (rewrite ENBA; reflexivity).
    unfold qcache_rep. split.
    + replace (Z.of_nat (length ((l' ++ [b]) ++ [bn]))) with (Z.of_nat (length l) + 1) by (rewrite EL, !length_app; cbn [length]; lia).
      replace (qfirst AL ((l' ++ [b]) ++ [bn])) with (qfirst AL l) by (rewrite EL; destruct l'; reflexivity).
      rewrite qlast_snoc, EA.
      replace (qbytes ((l' ++ [b]) ++ [bn])) with (qbytes l + (qc_n ch + 8192)) by (rewrite EL, !qbytes_app; unfold qbytes, bn; cbn [fold_right qb_size]; lia).
      exact TQC.
    + apply qlist_rep_snoc. split.
      * apply qlist_rep_snoc. rewrite EA. split.
        -- eapply (qlist_rep_frame_clear AL _ (p_au k1) m1 mZ l' _ AO AUF B8 QLp MU WM QBIp).
           repeat (apply Forall_cons || apply Forall_nil).
           ++ left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS1 SHS0 SP1. split; lia.
           ++ left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS1 SHS0 SP1. split; lia.
           ++ left. unfold space_out. cbn [fst snd]. clear - LOQ CLO ACR SP2 SHS1. split; right; lia.
           ++ left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS1 SHS0 SP1. split; lia.
           ++ right. left. exists v. split; [intros X; apply VNL; rewrite map_app; apply in_or_app; left; exact X|].
              split; [exact V0|]. split; [exact VAL|]. split; [clear - VAU AUF; lia|]. left. cbn [fst snd]. rewrite <- ENBA. lia.
           ++ right. left. exists (qb_v b). split.
              { rewrite map_app in NDV. cbn [map] in NDV. apply NoDup_remove in NDV as [_ NI]. rewrite app_nil_r in NI. exact NI. }
              split; [exact BV0|]. split; [exact BVA|]. split; [clear - BVF; lia|]. left. cbn [fst snd]. unfold qb_addr. lia.
        -- split; [exact BC|]. split; [exists wsb; split; [exact BARR|]; split; [exact LWSb| exact FWSb]| exact BSH].
      * unfold qbatch_rep. rewrite EA. unfold bn. cbn [qb_size qb_chunks qb_count length map]. fold bn.
        apply (proj1 (rw_cells_app asegs mZ NBA [_; _; _] [_])) in FB0 as [FB3 FBH]. cbn [cells_size csize Nat.add] in FBH. change (Z.of_nat 24) with 24 in FBH.
        split; [exact FB3|]. split.
        -- replace (Z.to_nat 8160) with (8 * 1020)%nat in FBR by lia.
           assert (HB : rw_cells asegs mZ (NBA + 24) [C8 (Z_to_bv 64 (qc_hdr AL ch)); CB (8 * 1020) jr]).
           { apply (proj2 (rw_cells_app asegs mZ (NBA + 24) [_] [_])). split; [exact FBH|]. cbn [cells_size csize Nat.add].
             replace (NBA + 24 + Z.of_nat 8) with (NBA + 32) by lia. exact FBR. }
           destruct (u64arr_of_C8_CB mZ _ _ _ _ HB) as (ws0 & LW0 & ARR0).
           exists (Z_to_bv 64 (qc_hdr AL ch) :: ws0). split; [exact ARR0|]. split; [cbn [length]; rewrite LW0; reflexivity| reflexivity].
        -- change (Z.to_nat 1024) with 1024%nat in FS. exact FS.

Qed.

End ENQP.
