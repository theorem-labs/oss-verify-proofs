(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit Sj_num_akit Sj_acps. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_anndefs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA El_xs_adaptA El_xs_kitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Definition EL_LRET_XA : Z := 0xb1f04.
Definition XS_FREE_A : Z := 0x82e78.
Ltac ulX := unfold XS_SPLO, RT_STACK, STACK_WIN, USTACK_TOP, NORET_DEPTH, SEGTOP_A, EL_EHG_XA, EL_UNW_XA, EL_XDATA_XA, EL_XDATA2_XA, EL_CANARY_XA, EL_AUXVC_XA in *.

Definition xden (R : bvmap 5 word) (usp : Z) (ws : list word) (e : expr) : word :=
  match e with
  | EVar n => if (n <? 32)%nat then reg_get R (Z_to_bv 5 (Z.of_nat n)) else nth (n - 49)%nat ws (Z_to_bv 64 0)
  | ELit z => Z_to_bv 64 z
  | EAlu ALU_ADD (EVar 2) (ELit k) => Z_to_bv 64 (usp + k)
  | _ => Z_to_bv 64 0
  end.

Definition xexp_ok (e : expr) : bool :=
  match e with
  | EVar n => (Nat.ltb n 32 || (Nat.leb 49 n && Nat.ltb n 149))%bool
  | ELit z => (Z.leb 0 z && Z.ltb z two64)%bool
  | EAlu ALU_ADD (EVar 2) (ELit k) => (Z.leb 0 k && Z.leb k 4096)%bool
  | _ => false
  end.

Lemma kn_word_norm_sound : forall E (M : word -> option byte) kn a w v,
  know_ok asegs E M kn -> kn_word_norm kn a w v = true ->
  rdn asegs M (adenot E a) w = Some (word_to_le_bytes w (edenot E v)) /\ flat E a (Z.of_nat w) /\ (w <= 8)%nat.
Proof.
  intros E M kn a w v HK H. unfold kn_word_norm in H. apply existsb_exists in H as (K0 & HIn & HK1).
  destruct K0 as [a' w' v'| | | | | | | | |]; try discriminate.
  apply andb_prop in HK1 as [HK1 H3]. apply andb_prop in HK1 as [H1 H2].
  unfold saddr_eqb in H1. destruct a as [b k], a' as [b' k']. cbn [a_base a_off] in H1. apply andb_prop in H1 as [H1a H1b].
  apply expr_eqb_eq in H1a. apply Z.eqb_eq in H1b. apply Nat.eqb_eq in H2. apply expr_eqb_eq in H3. subst b' k' w'.
  unfold know_ok in HK. rewrite Forall_forall in HK. specialize (HK _ HIn). cbn [kentry_ok] in HK. destruct HK as (Hw & Hfl & Hrd).
  rewrite <- (norm_sound E v'), H3 in Hrd. split; [exact Hrd|]. split; [exact Hfl| exact Hw].
Qed.

Lemma exit_okA_some : forall FSZ xr xk o, exit_okA FSZ xr xk o = true -> exists sf, o = Some sf /\ exit_checkA FSZ xr xk sf = true.
Proof. intros FSZ xr xk [sf|] H; [exists sf; split; [reflexivity| exact H]| discriminate H]. Qed.

Lemma exit_checkA_sound : forall FSZ xr xk s, exit_checkA FSZ xr xk s = true ->
  s_pc s = XS_END_A /\ s_log s = []
  /\ norm (sr_get (s_regs s) (Z_to_bv 5 10)) = XBLK /\ norm (sr_get (s_regs s) (Z_to_bv 5 8)) = XBLK
  /\ norm (sr_get (s_regs s) (Z_to_bv 5 1)) = ELit XS_FREERET_A /\ norm (sr_get (s_regs s) (Z_to_bv 5 2)) = xspk (FSZ - 32)
  /\ norm (sr_get (s_regs s) (Z_to_bv 5 3)) = EVar 3 /\ norm (sr_get (s_regs s) (Z_to_bv 5 4)) = ELit TPV_XA
  /\ (forall re, In re xr -> norm (sr_get (s_regs s) (Z_to_bv 5 (Z.of_nat (fst re)))) = snd re)
  /\ kn_word_norm (s_know s) (SA (ELit 0) EL_EHG_XA) 8 (ELit 0) = true /\ kn_word_norm (s_know s) (SA (ELit 0) (EL_EHG_XA + 8)) 4 (ELit 0) = true
  /\ (forall i, (i < 8)%nat -> kn_word_norm (s_know s) (SA (ELit 0) (EL_UNW_XA + Z.of_nat i)) 1 (ELit (nth i (uw_bytesA true) 0)) = true)
  /\ (forall ke, In ke xk -> kn_word_norm (s_know s) (SA XSP (fst ke)) 8 (snd ke) = true).
Proof.
  intros FSZ xr xk s H. unfold exit_checkA in H.
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H HU]. apply andb_prop in H as [H HE2]. apply andb_prop in H as [H HE1].
  apply andb_prop in H as [H HXR]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2].
  apply andb_prop in H as [H H1]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H10]. apply andb_prop in H as [HPC HL].
  apply Z.eqb_eq in HPC. apply expr_eqb_eq in H10. apply expr_eqb_eq in H8. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. apply expr_eqb_eq in H4.
  destruct (s_log s); [|discriminate].
  repeat split; try assumption; try reflexivity.
  - intros re Hre. rewrite forallb_forall in HXR. apply expr_eqb_eq. exact (HXR re Hre).
  - intros i Hi. rewrite forallb_forall in HU. apply HU. apply in_seq. lia.
  - intros ke Hke. rewrite forallb_forall in HK. exact (HK ke Hke).
Qed.

Lemma itab_leaf_soundA : itab_sound asegs PTLeaf.
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.
Lemma itab_of_ranges_soundA : forall rs, itab_sound asegs (itab_of_ranges asegs rs PTLeaf).
Proof. intros rs. apply itab_of_ranges_sound. apply itab_leaf_soundA. Qed.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation mem := (word -> option byte).

Lemma free_wrap_walkA : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
  a0 = wz A -> (A + 144 <= 0x10000 \/ SEGTOP_A <= A) -> 0 < A -> A + 144 <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists a1' a2' a4',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz XS_FREE_A) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz XS_END_A) fc None m (seg_rom asegs)).
Proof.
  intros until A. intros -> HA HA0 HA47 MI. unfold XS_FREE_A, XS_END_A. unfold SEGTOP_A in HA.
  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K.
  - zstep. apply evt_done. do 3 eexists. reflexivity.
  - zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia]. zstep. apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma endcatch_epilogue_walkA : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (u lret : Z) (v0 v1 : word),
  sp = wz u -> 16384 <= u -> u + 32 <= 2^62 -> 0 <= lret < 2^32 -> lret mod 2 = 0 ->
  ro_cells asegs m (u + 8) [C8 v1; C8 v0; C8 (wz lret)] -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR (wz lret) (wz (u + 32)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz lret) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz XS_FREERET_A) fc None m (seg_rom asegs)).
Proof.
  intros until v1. intros -> HU1 HU2 LR LE RA MI. unfold XS_FREERET_A.
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. rewrite ret_pc_even by lia. reflexivity.
Qed.

Section AEvt2.
  Variable RT : rt_sig.
  Variable PMc : Model -> Prop.
  Lemma aevt_call2 : forall (Σ : rts RT) K ms (Q : config -> Prop),
    cps asegs (ASTA RT Σ PMc (eq ms)) Q ->
    (forall c, Q c -> exists (Σ' : rts RT) (Pm : machine_state -> Prop), ASTA RT Σ' PMc Pm c /\ forall ms', Pm ms' -> aevt RT PMc Σ' K ms') ->
    aevt RT PMc Σ K ms.
  Proof.
    intros Σ K ms Q H HQ T c Hc Hk. apply (H T c Hc). intros c' Hq.
    destruct (HQ c' Hq) as (Σ' & Pm & HA & HP). destruct (ASTA_unpack RT Σ' PMc Pm c' HA) as (ms' & HPm & Hc'). exact (HP ms' HPm T c' Hc' Hk).
  Qed.
End AEvt2.

Lemma xden_sound : forall (E : env) (R : bvmap 5 word) usp ws e,
  (forall k, (k < 32)%nat -> ev E k = reg_get R (Z_to_bv 5 (Z.of_nat k))) -> (forall k, (k < 100)%nat -> ev E (49 + k) = nth k ws (Z_to_bv 64 0)) ->
  bv_unsigned (ev E 2) = usp -> 0 <= usp -> usp + 4096 < 2^64 ->
  xexp_ok e = true -> edenot E e = xden R usp ws e.
Proof.
  intros E R usp ws e ER EH E2 U1 U2 HX. destruct e as [z|n|op a b| | | | |]; cbn [xexp_ok] in HX; try discriminate.
  - reflexivity.
  - cbn [edenot xden]. destruct (Nat.ltb_spec n 32); [apply ER; assumption|]. cbn [orb] in HX. apply andb_prop in HX as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2.
    rewrite <- (EH (n - 49)%nat) by lia. f_equal. lia.
  - destruct op; try discriminate. destruct a as [|na| | | | | |]; try discriminate. destruct na as [|[|[|na]]]; try discriminate.
    destruct b as [k| | | | | | |]; try discriminate. apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [edenot xden]. rewrite PropExec.alu_add. unfold PropExec.v_add. rewrite E2, unsigned_lit by lia. reflexivity.
Qed.

Lemma aclient_up' : forall live frames s (s' : Z) a, aclient live frames s a -> s <= s' -> aclient live frames s' a \/ (s <= a < s').
Proof.
  intros live frames s s' a H Hle. unfold aclient in *.
  destruct H as [H|H]; [| left; right; exact H]. destruct (Z.lt_ge_cases a s'); [right; lia| left; left; lia].
Qed.

Lemma w2lb1 : forall z, 0 <= z < 256 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold word_to_le_bytes. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma in_live_remove : forall q (l : list (Z * Z)) e, In e (live_remove q l) -> In e l /\ fst e <> q.
Proof.
  intros q l e. induction l as [|x l IH]; intros H; [destruct H|].
  rewrite RT_anndefs.live_remove_cons' in H. destruct (Z.eqb_spec (fst x) q) as [EQ|NE].
  - destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
  - destruct H as [<-|H]; [split; [left; reflexivity| exact NE]|]. destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

Lemma client_static_bounds : forall a, client_static a -> 0x16e760 <= a < 0x6c9858.
Proof.
  intros a [(lo & hi & HIn & Ha) _]. unfold CLIENT_STATIC in HIn. cbn in HIn.
  destruct HIn as [HIn|[HIn|[HIn|[]]]]; injection HIn as <- <-; lia.
Qed.

Section ThrowA.
  Variable RT : rt_sig.
  Variable WIN : rt_win RT.
  Variable c : Z.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis TLS : tls_icG (RTX RT WIN c) TPV_XA XS_TLS_A.
  Hypothesis XROW : forall Σ0 (m : mem), ARTW RT WIN c Σ0 m -> el_xroA m.

  Variables (FSZ : Z) (hcs : list hcellA) (RA : Z) (xr : xregs_exit) (xk : xstack_exit) (IT : itab) (es0 es1 : expr).
  Hypothesis FSZR : 32 <= FSZ <= 4096 /\ FSZ mod 16 = 0.
  Hypothesis HCO : forall o w v, In (o, w, v) hcs -> 0 <= o /\ o + Z.of_nat w <= FSZ.
  Hypothesis HCN : (length hcs < 100)%nat.
  Hypothesis RAR : 0 <= RA < 2^64.
  Hypothesis XROK : forall re, In re xr -> xexp_ok (snd re) = true /\ (18 <= fst re <= 27)%nat.
  Hypothesis XK0 : In (FSZ - 8, ELit EL_LRET_XA) xk.
  Hypothesis XK1 : In (FSZ - 16, es0) xk /\ xexp_ok es0 = true.
  Hypothesis XK2 : In (FSZ - 24, es1) xk /\ xexp_ok es1 = true.
  Hypothesis ITS : itab_sound asegs IT.
  Hypothesis RUN : forall uw : bool, exit_okA FSZ xr xk (xautoXA FSZ IT XS_END_A XSA_FUEL XSA_K (xs_ss0A FSZ hcs RA uw)) = true.

  Variable Σ : rts RT.
  Variables (sp gp t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (blk lo spx : Z) (code : word) (uw : bool) (ws : list word).
  Let usp := bv_unsigned sp.
  Let R := mkR (Z_to_bv 64 RA) sp gp (Z_to_bv 64 TPV_XA) t0 t1 t2 (Z_to_bv 64 (blk + 128)) s1 (Z_to_bv 64 (blk + 128)) (Z_to_bv 64 EL_TINFO_XA) (Z_to_bv 64 EL_DTOR_XA)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  Hypothesis HB : rw_cells asegs m blk [CB 128 (repeat (Z_to_bv 8 0) 128); C8 (Z_to_bv 64 EL_VPTR_XA); C4 code; C4 (Z_to_bv 64 0)].
  Hypothesis INB : In (blk, 144) (rt_live RT Σ).
  Hypothesis LPOS : forall p n, In (p, n) (rt_live RT Σ) -> 0 < n.
  Hypothesis RB : 0 < blk /\ blk mod 16 = 0 /\ blk + 144 <= rt_sp0 RT Σ - STACK_WIN /\ (blk + 144 <= 0x10000 \/ SEGTOP_A <= blk).
  Hypothesis ST : stk asegs m lo (usp + FSZ).
  Hypothesis LO1 : 0x7fff7f800000 <= lo.
  Hypothesis LO2 : rt_sp0 RT Σ - STACK_WIN <= lo.
  Hypothesis LO3 : lo + RT_STACK <= usp + XS_SPLO.
  Hypothesis SP1 : usp + FSZ + 0xb0 <= rt_sp0 RT Σ.
  Hypothesis SP2 : rt_sp0 RT Σ - (usp + XS_SPLO) <= NORET_DEPTH.
  Hypothesis SP3 : rt_sp0 RT Σ <= USTACK_TOP.
  Hypothesis AL : usp mod 16 = 0.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis HA : ARTW RT WIN c Σ m.
  Hypothesis EHG : rw_cells asegs m EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
  Hypothesis UNW : bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m EL_UNW_XA 8.
  Hypothesis XD : el_xdataA m.
  Hypothesis CAN : exists g : word, cells_at asegs m EL_CANARY_XA [C8 g].
  Hypothesis AUX : el_auxvA spx m.
  Hypothesis SPX : usp + FSZ <= spx.
  Hypothesis HC : hcells_okA m usp 0 hcs ws.

  Definition xs_postA (Σ2 : rts RT) (m2 : mem) : Prop :=
    ARTW RT WIN c Σ2 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + FSZ)
    /\ rt_live RT Σ2 = live_remove blk (rt_live RT Σ) /\ rt_frames RT Σ2 = rt_frames RT Σ /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ
    /\ rw_cells asegs m2 EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ bytes_at asegs m2 EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA true)) /\ wr_at asegs m2 EL_UNW_XA 8
    /\ (forall a : word, aclient (live_remove blk (rt_live RT Σ)) (rt_frames RT Σ) (usp + XS_SPLO) (bv_unsigned a) ->
          ~ (usp + XS_SPLO <= bv_unsigned a < usp + FSZ) -> ~ (EL_EHG_XA <= bv_unsigned a < EL_EHG_XA + 12) -> ~ (EL_UNW_XA <= bv_unsigned a < EL_UNW_XA + 8) ->
          m2 a = m a).

  Theorem xs_throwA : forall K : config -> Prop,
    (forall (Σ2 : rts RT) (m2 : mem) (F2 : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
       xs_postA Σ2 m2 ->
       (forall re, In re xr -> reg_get (mkR (Z_to_bv 64 EL_LRET_XA) (Z_to_bv 64 (usp + FSZ)) gp (Z_to_bv 64 TPV_XA) t0' t1' t2' (xden R usp ws es0) (xden R usp ws es1)
                                          a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6') (Z_to_bv 5 (Z.of_nat (fst re)))
                               = xden R usp ws (snd re)) ->
       aevt (RTX RT WIN c) PMc Σ2 K (MS (mkR (Z_to_bv 64 EL_LRET_XA) (Z_to_bv 64 (usp + FSZ)) gp (Z_to_bv 64 TPV_XA) t0' t1' t2' (xden R usp ws es0) (xden R usp ws es1)
                                             a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                                        F2 (Z_to_bv 64 EL_LRET_XA) fc None m2 (seg_rom asegs))) ->
    aevt (RTX RT WIN c) PMc Σ K (MS R F (Z_to_bv 64 EL_CXA_THROW_XA) fc None m (seg_rom asegs)).
  Proof.
    intros K HK.
    pose proof (w_facts RT WIN c) as AF. change (art_facts (RTX RT WIN c)) in AF.
    assert (HA' : ART (RTX RT WIN c) Σ m) by exact HA.

    destruct (xs_entryA (RTX RT WIN c) Σ FSZ hcs ws RA ltac:(lia) HCO HCN RAR sp gp t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m blk lo spx code uw
                HB INB RB ST LO1 LO2 LO3 SP1 SP2 SP3 AL MI HA' (XROW Σ m HA) EHG UNW XD CAN AUX SPX HC) as (E & HCIX & EREG & E40 & EHC).

    destruct (exit_okA_some _ _ _ _ (RUN uw)) as (sf & HX & RUNu).
    destruct (exit_checkA_sound FSZ xr xk sf RUNu) as (Hpc & Hlog & N10 & N8 & N1 & N2 & N3 & N4 & NXR & KE1 & KE2 & KU & KK).
    apply (xautoXA_sound RT WIN c PMc FDO MST Σ TLS XROW FSZ lo IT ITS fc XSA_FUEL XSA_K _ sf E m m _ HX HCIX K).
    intros E' base' ms' [HAG _] _ [Hnx HC'].
    destruct (HC' E' (eagree_refl _ _)) as (R' & F' & Hms' & HR' & HLF' & HK' & HFR' & HMI' & HWM' & HB' & _ & HG' & HART' & HST').
    rewrite Hpc, Hlog in Hms'. cbn [mem_denot] in Hms'. rewrite Hms' in HMI', HWM', HART', HST' |- *. unfold MS in HMI', HWM', HART', HST'. cbn [ms_mem] in HMI', HWM', HART', HST'.
    cbn [s_next xs_ss0A] in HAG.

    assert (ER' : forall k, (k < 32)%nat -> ev E' k = reg_get R (Z_to_bv 5 (Z.of_nat k))) by (intros k Hk; rewrite <- (HAG k) by lia; apply EREG; exact Hk).
    assert (EH' : forall k, (k < 100)%nat -> ev E' (49 + k) = nth k ws (Z_to_bv 64 0)) by (intros k Hk; rewrite <- (HAG (49 + k)%nat) by lia; apply EHC).
    assert (E40' : ev E' 40 = Z_to_bv 64 blk) by (rewrite <- (HAG 40%nat) by lia; exact E40).
    destruct (mkR_sel7 (Z_to_bv 64 RA) sp gp (Z_to_bv 64 TPV_XA) t0 t1 t2 (Z_to_bv 64 (blk + 128)) s1 (Z_to_bv 64 (blk + 128)) (Z_to_bv 64 EL_TINFO_XA) (Z_to_bv 64 EL_DTOR_XA)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as (Q1 & Q2 & Q4 & Q8 & Q10 & Q11 & Q12).
    assert (E2 : ev E' 2 = sp) by (rewrite (ER' 2%nat) by lia; exact Q2).
    assert (E3 : ev E' 3 = gp) by (rewrite (ER' 3%nat) by lia; reflexivity).

    assert (RV : forall r e, norm (sr_get (s_regs sf) r) = e -> reg_get R' r = edenot E' e).
    { intros r e Hn. rewrite (regs_val E' _ R' r HR' HFR'). rewrite <- (norm_sound E'). rewrite Hn. reflexivity. }
    pose proof (RV _ _ N10) as V10. pose proof (RV _ _ N8) as V8. pose proof (RV _ _ N1) as V1. pose proof (RV _ _ N2) as V2.
    pose proof (RV _ _ N3) as V3. pose proof (RV _ _ N4) as V4.
    cbn [edenot XBLK] in V10, V8, V1, V3, V4. rewrite E40' in V10, V8. rewrite E3 in V3.
    assert (V2' : reg_get R' (Z_to_bv 5 2) = Z_to_bv 64 (usp + FSZ - 32)).
    { rewrite V2. unfold xspk. destruct (Z.eqb_spec (FSZ - 32) 0) as [EQ|NE].
      - cbn [edenot XSP]. rewrite E2. replace (usp + FSZ - 32) with usp by lia. symmetry. apply Z_to_bv_bv_unsigned.
      - cbn [edenot XSP]. rewrite E2, PropExec.alu_add. unfold PropExec.v_add. rewrite unsigned_lit by lia. f_equal. unfold usp. lia. }
    destruct HFR' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 &
                      y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ER2). subst R'.
    destruct (mkR_sel7 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) as (Y1 & Y2 & Y4 & Y8 & Y10 & Y11 & Y12).
    rewrite Y1 in V1. rewrite Y2 in V2'. rewrite Y4 in V4. rewrite Y8 in V8. rewrite Y10 in V10.
    assert (Y3 : reg_get (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 3) = y3) by (vm_compute; reflexivity).
    rewrite Y3 in V3. subst y1 y2 y3 y4 y8 y10.

    assert (U0 : bv_unsigned (edenot E' (ELit 0)) = 0) by (cbn [edenot]; apply unsigned_lit; lia).
    assert (KL : forall a w z, kn_word_norm (s_know sf) (SA (ELit 0) a) w (ELit z) = true -> bytes_at asegs base' a (word_to_le_bytes w (Z_to_bv 64 z))).
    { intros a w z Hk. destruct (kn_word_norm_sound E' base' _ _ _ _ HK' Hk) as (Rd & Fl & Hw).
      pose proof (flat_u E' _ _ Fl) as EU. rewrite estart_lit in EU.
      apply (bytes_at_of_rdnG w); [| destruct Fl as (?&?&?&?); rewrite estart_lit in *; lia| destruct Fl as (?&?&?&?); rewrite estart_lit in *; lia].
      rewrite rdn_common. unfold wa. rewrite <- EU, Z_to_bv_bv_unsigned. cbn [edenot] in Rd. exact Rd. }
    assert (KS : forall o e, In (o, e) xk -> xexp_ok e = true ->
              Common.PropExec.rdn asegs base' (wa (usp + o)) 8 = Some (word_to_le_bytes 8 (xden R usp ws e)) /\ 0 <= usp + o /\ usp + o + 8 <= 2^64).
    { intros o e Hin Hx. destruct (kn_word_norm_sound E' base' _ _ _ _ HK' (KK _ Hin)) as (Rd & Fl & Hw). cbn [fst snd] in Rd, Fl.
      pose proof (flat_u E' _ _ Fl) as EU. destruct Fl as (F1 & F2 & F3 & F4). unfold estart in EU, F1, F2, F4. cbn [a_base a_off edenot XSP] in EU, F1, F2, F4.
      rewrite E2 in EU, F1, F2, F4. fold usp in EU, F1, F2, F4.
      split; [| lia]. unfold wa. rewrite <- EU, Z_to_bv_bv_unsigned. rewrite <- rdn_common || idtac.
      rewrite <- (xden_sound E' R usp ws e ER' EH' ltac:(rewrite E2; reflexivity) ltac:(ulX; lia) ltac:(ulX; lia) Hx). exact Rd. }

    assert (XRV : forall re, In re xr -> reg_get (mkR (Z_to_bv 64 XS_FREERET_A) (Z_to_bv 64 (usp + FSZ - 32)) gp (Z_to_bv 64 TPV_XA) y5 y6 y7 (Z_to_bv 64 blk) y9 (Z_to_bv 64 blk) y11 y12 y13 y14 y15 y16 y17
                     y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (Z_to_bv 5 (Z.of_nat (fst re))) = xden R usp ws (snd re)).
    { intros re Hre. destruct (XROK re Hre) as [Hx Hr]. rewrite (RV _ _ (NXR re Hre)).
      apply (xden_sound E' R usp ws (snd re) ER' EH' ltac:(rewrite E2; reflexivity) ltac:(ulX; lia) ltac:(ulX; lia) Hx). }

    destruct RB as (RB1 & RB2 & RB3 & RB4). pose proof FSZR as [FS1 FS16].
    apply (aevt_evt (RTX RT WIN c) AF PMc MST).
    eapply evt_mono; [apply (free_wrap_walkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc base' blk eq_refl RB4 RB1 ltac:(ulX; lia) HMI')|].
    intros ms1 (a1' & a2' & a4' & ->).

    assert (COK : call_ok (RTX RT WIN c) Σ base' (Z_to_bv 64 (usp + FSZ - 32)) lo).
    { unfold call_ok. rewrite unsigned_lit by (ulX; lia). cbn [rt_sp0 RTX rt_sigW].
      split; [apply (proj1 (stk_split asegs base' lo (usp + FSZ - 32) _ HST' ltac:(unfold El_xs_coreA.uE; cbn [edenot XSP]; rewrite E2; fold usp; ulX; lia)))|].
      split; [exact LO2|]. split; [ulX; lia|]. split; [ulX; lia|].
      rewrite <- Z.add_sub_assoc, Z.add_mod, AL by lia. replace ((FSZ - 32) mod 16) with 0 by (rewrite Zminus_mod, FS16; reflexivity). reflexivity. }
    assert (UOK : unwind_ok (Z_to_bv 64 XS_FREERET_A) (Z_to_bv 64 blk) (Z_to_bv 64 (usp + FSZ - 32))).
    { left. rewrite !unsigned_lit by (ulX; lia). ulX. lia. }
    apply (aevt_call2 (RTX RT WIN c) PMc Σ K _ _
             (rc_free (RTX RT WIN c) (w_rc RT WIN c) Σ PMc (Z_to_bv 64 XS_FREERET_A) (Z_to_bv 64 (usp + FSZ - 32)) gp (Z_to_bv 64 TPV_XA) y5 y6 y7 (Z_to_bv 64 blk) y9
                (Z_to_bv 64 blk) a1' a2' y13 a4' y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 F' fc base' blk 144 lo FDO MST INB eq_refl eq_refl HART' HMI' COK UOK)).
    intros c0 (Σ2 & v & HQ & LV2 & FR2 & SP02 & _). exists Σ2. eexists. split; [exact HQ|].
    intros ms2 (m2 & RS & (HA2 & HMI2 & HST2) & PR2).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite unsigned_lit in HST2, PR2 by (ulX; lia). cbn [rt_live rt_frames RTX rt_sigW] in PR2, LV2, FR2, SP02, HA2.

    assert (AGF : forall a : word, usp + FSZ - 32 <= bv_unsigned a < usp + FSZ -> m2 a = base' a).
    { intros a Ha. apply PR2. left. ulX. lia. }
    destruct (KS _ _ (proj1 XK2) (proj2 XK2)) as (RD1 & _ & _). destruct (KS _ _ (proj1 XK1) (proj2 XK1)) as (RD0 & _ & _). destruct (KS _ _ XK0 eq_refl) as (RDR & _ & _).
    cbn [xden] in RDR.
    assert (CELLS : ro_cells asegs m2 (usp + FSZ - 32 + 8) [C8 (xden R usp ws es1); C8 (xden R usp ws es0); C8 (Z_to_bv 64 EL_LRET_XA)]).
    { apply (D_kit.ro_cells_agree asegs base' m2).
      - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply (proj2 (Mem.bytes_at_app asegs base' _ _ _)). split; [apply (bytes_at_of_rdnG 8); [replace (usp + FSZ - 32 + 8) with (usp + (FSZ - 24)) by lia; exact RD1| ulX; lia| ulX; lia]|].
        rewrite Mem.length_le8. apply (proj2 (Mem.bytes_at_app asegs base' _ _ _)). split; [apply (bytes_at_of_rdnG 8); [replace (usp + FSZ - 32 + 8 + Z.of_nat 8) with (usp + (FSZ - 16)) by lia; exact RD0| ulX; lia| ulX; lia]|].
        rewrite Mem.length_le8. apply (bytes_at_of_rdnG 8); [replace (usp + FSZ - 32 + 8 + Z.of_nat 8 + Z.of_nat 8) with (usp + (FSZ - 8)) by lia; exact RDR| ulX; lia| ulX; lia].
      - intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AGF. lia. }

    rewrite (ret_pc_even XS_FREERET_A) by (unfold XS_FREERET_A; lia).
    apply (aevt_evt (RTX RT WIN c) AF PMc MST).
    eapply evt_mono; [apply (endcatch_epilogue_walkA _ _ gp _ u0 u1 u2 _ _ v b1 b2 b3 b4 b5 b6 b7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6 F2 fc m2 (usp + FSZ - 32) EL_LRET_XA
                               (xden R usp ws es0) (xden R usp ws es1) eq_refl ltac:(ulX; lia) ltac:(ulX; lia) ltac:(unfold EL_LRET_XA; lia) eq_refl CELLS HMI2)|].
    intros ms3 ->. replace (usp + FSZ - 32 + 32) with (usp + FSZ) by lia.

    apply (HK Σ2 m2 F2 u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6).
    2:{ intros re Hre. rewrite <- (XRV re Hre). destruct (XROK re Hre) as [_ Hr].
        assert (CS : (fst re = 18 \/ fst re = 19 \/ fst re = 20 \/ fst re = 21 \/ fst re = 22 \/ fst re = 23 \/ fst re = 24 \/ fst re = 25 \/ fst re = 26 \/ fst re = 27)%nat) by lia.
        destruct CS as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; vm_compute; reflexivity. }
    unfold xs_postA. split; [exact HA2|]. split; [exact HMI2|].
    split. {
      apply (stk_merge asegs m2 lo (usp + FSZ - 32) (usp + FSZ) HST2); [| ulX; lia].
      apply (D_kit.stk_agree_nw asegs base' m2); [| intros a Ha; apply AGF; exact Ha].
      apply (proj2 (stk_split asegs base' lo (usp + FSZ - 32) (usp + FSZ) ltac:(unfold El_xs_coreA.uE in HST'; cbn [edenot XSP] in HST'; rewrite E2 in HST'; exact HST') ltac:(ulX; lia))). }
    split; [exact LV2|]. split; [exact FR2|]. split; [exact SP02|].

    assert (AGS : forall a : word, (EL_EHG_XA <= bv_unsigned a < EL_EHG_XA + 12 \/ EL_UNW_XA <= bv_unsigned a < EL_UNW_XA + 8) -> m2 a = base' a).
    { intros a Ha. apply PR2. right; left. apply xstatics_client. lia. }
    split. { apply (D_kit.rw_cells_agree_nw asegs base' m2).
      - split; [split; [cbn; tauto|]|].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (Mem.bytes_at_app asegs base' _ _ _)). split; [exact (KL _ _ _ KE1)|]. rewrite Mem.length_le8. exact (KL _ _ _ KE2).
        + cbn [cells_size csize Nat.add]. destruct EHG as [_ WE]. cbn [cells_size csize Nat.add] in WE.
          destruct WE as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply HWM'. exact (W3 i Hi).
      - intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AGS. lia. }

    assert (UB : bytes_at asegs base' EL_UNW_XA (map (fun b : Z => Z_to_bv 8 b) (uw_bytesA true))).
    { cbn [map uw_bytesA].
      pose proof (KL _ _ _ (KU 0%nat ltac:(lia))) as B0. pose proof (KL _ _ _ (KU 1%nat ltac:(lia))) as B1. pose proof (KL _ _ _ (KU 2%nat ltac:(lia))) as B2.
      pose proof (KL _ _ _ (KU 3%nat ltac:(lia))) as B3. pose proof (KL _ _ _ (KU 4%nat ltac:(lia))) as B4. pose proof (KL _ _ _ (KU 5%nat ltac:(lia))) as B5.
      pose proof (KL _ _ _ (KU 6%nat ltac:(lia))) as B6. pose proof (KL _ _ _ (KU 7%nat ltac:(lia))) as B7.
      cbn [nth uw_bytesA Z.of_nat Pos.of_succ_nat Pos.succ] in B0, B1, B2, B3, B4, B5, B6, B7. rewrite w2lb1 in B0, B1, B2, B3, B4, B5, B6, B7 by lia.
      rewrite Z.add_0_r in B0.
      repeat (lazymatch goal with
              | |- bytes_at _ _ ?a (?b :: ?rest) =>
                  lazymatch rest with
                  | [] => first [exact B0| exact B1| exact B2| exact B3| exact B4| exact B5| exact B6| exact B7]
                  | _ => change (b :: rest) with ([b] ++ rest); apply (proj2 (Mem.bytes_at_app asegs base' _ _ _)); split;
                         [first [exact B0| exact B1| exact B2| exact B3| exact B4| exact B5| exact B6| exact B7]| cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
                          lazymatch goal with |- bytes_at _ _ ?a' _ => let t := eval cbv in a' in change a' with t end]
                  end
              end). }
    split. { apply (D_kit.bytes_at_agree asegs base' m2 EL_UNW_XA _ UB). intros a Ha. apply AGS. cbn [map length uw_bytesA Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. lia. }
    split. { destruct UNW as [_ (W1 & W2 & W3)]. split; [exact W1|]. split; [exact W2|]. intros i Hi.
             rewrite (D_kit.wview_agree asegs base' m2); [apply HWM'; exact (W3 i Hi)|]. apply AGS. unfold wa. rewrite unsigned_lit by (ulX; lia). lia. }

    intros a Hca Hns Hne Hnu.
    assert (NB : ~ (blk <= bv_unsigned a < blk + 144)).
    { intros Hb. destruct Hca as [S|[CS|[LV|[FR|FS]]]].
      - ulX. lia.
      - pose proof (client_static_bounds _ CS). ulX. lia.
      - destruct LV as (p & n & HIn & Hp). destruct (in_live_remove _ _ _ HIn) as [HIn' NE]. cbn [fst] in NE.
        destruct (in_split _ _ INB) as (l1 & l2 & EL).
        assert (HIn2 : In (p, n) (l1 ++ l2)).
        { rewrite EL in HIn'. apply in_app_iff in HIn'. apply in_app_iff. destruct HIn' as [H1|[H1|H1]]; [left; exact H1| exfalso; injection H1; lia| right; exact H1]. }
        pose proof (af_live_disj (RTX RT WIN c) AF Σ m blk 144 p n l1 l2 HA' EL HIn2). lia.
      - destruct FR as (f & k & HIn & Hf). destruct (af_frames_range (RTX RT WIN c) AF Σ m f k HA' HIn) as (_ & _ & _ & DJ). pose proof (DJ blk 144 INB). lia.
      - destruct FS as (f & k & HIn & Hf). destruct (af_fshadow_apart (RTX RT WIN c) AF Σ m f k HA' HIn) as [DJ _]. pose proof (DJ blk 144 INB). lia. }
    rewrite PR2.
    - apply HB'.
      + unfold El_xs_coreA.uE. cbn [edenot XSP]. rewrite E2. fold usp. cbn [rt_live rt_frames RTX rt_sigW].
        eapply Sj_acps.aclient_mono; [exact Hca| intros e He; exact (proj1 (in_live_remove _ _ _ He))| auto| lia].
      + intros (wb & wlo & whi & HIn & Hx). unfold xs_WA in HIn. cbn in HIn.
        destruct HIn as [HIn|[HIn|[HIn|[HIn|[]]]]]; injection HIn as <- <- <-; cbn [edenot XSP XBLK] in Hx; rewrite ?E2, ?E40', ?U0 in Hx;
          rewrite ?unsigned_lit in Hx by (ulX; lia); fold usp in Hx; ulX; lia.
    - destruct (aclient_up' _ _ _ (usp + FSZ - 32) _ Hca ltac:(ulX; lia)) as [H|H]; [rewrite LV2; exact H| exfalso; ulX; lia].
  Qed.
End ThrowA.
