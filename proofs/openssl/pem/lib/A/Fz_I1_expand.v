(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_split Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LHI_SPLIT_PRE : Z := 0x2005c8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lhs_cells (B nn na p pmax items : Z) (x40 x48 err pad : word) : list cell :=
  [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 2096404); C8 (Z_to_bv 64 2096272); C8 (Z_to_bv 64 2096512); C8 (Z_to_bv 64 2096544); C8 x40; C8 x48;
   C4 (Z_to_bv 64 nn); C4 (Z_to_bv 64 na); C4 (Z_to_bv 64 p); C4 (Z_to_bv 64 pmax); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err; C4 pad].

(* [comment removed for export] *)
Definition lhi_spill (lh data : Z) : list cell :=
  [C8 (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)); C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 (lh + 88)); C8 (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880))].

Definition lhi_split_post (sp gp tp s0 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B nn na p' pmax items data nni p : Z) (x40 x48 err pad : word) (cp cn : Z) (nsp : list (bptr * Z))
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (stay' moved' : list (bptr * Z)),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880)) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) s5 s6
                  (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 nni) (Z_to_bv 64 p) t3' t4' t5' t6')
             F (Z_to_bv 64 LHI_SPLIT_EXIT) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ wmono asegs m m'
    /\ rw_cells asegs m' lh (lhs_cells B (nn + 1) na p' pmax items x40 x48 err pad)
    /\ chain asegs LH_CEIL (DVerr GOBJ) m' (ownL L) cp stay' /\ chain asegs LH_CEIL (DVerr GOBJ) m' (ownL L) cn moved'
    /\ Permutation (stay' ++ moved') nsp
    /\ LhRep.agree_on asegs (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W cp cn nsp a)) m m'.

(* [comment removed for export] *)
Lemma lhi_split : forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B nn na p p' pmax0 pmaxf na0 items data usp : Z) (x40 x48 err pad : word) (nsp : list (bptr * Z)),
  rw_cells asegs m lh (lhs_cells B nn na p pmaxf items x40 x48 err pad) ->
  rw_cells asegs m (usp + -144) (lhi_spill lh data) ->
  chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * p) nsp -> chain asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * nn) [] ->
  nsep nsp (B + 8 * p) (B + 8 * nn) ->
  nn = pmax0 + p -> 0 <= p < pmax0 -> 8 <= pmax0 -> nn < na -> na <= 16004 -> 0 < na0 < 2^31 -> 0 <= p' < 2^31 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= 2^47 ->
  acc asegs m B (8 * na) -> B mod 8 = 0 -> 0x10007fff8000 <= B -> B + 8 * na <= 2^47 ->
  (forall X, In X (map snd nsp) -> acc asegs m X 24 /\ X mod 8 = 0 /\ 0x10007fff8000 <= X /\ X + 24 <= 2^47) ->
  (lh + 104 <= B \/ B + 8 * na <= lh) -> Forall (fun A => A + 24 <= lh \/ lh + 104 <= A) (map snd nsp) ->
  s0 = Z_to_bv 64 usp -> 0x10007fff8000 + 192 <= usp -> usp <= 2^47 -> lh + 104 <= usp - 192 -> B + 8 * na <= usp - 192 ->
  Forall (fun A => A + 24 <= usp - 192) (map snd nsp) ->
  mem_inv asegs m ->
  evt asegs (lhi_split_post sp gp tp s0 s5 s6 F fc m GOBJ L lh B nn na p' pmaxf items data na0 p x40 x48 err pad (B + 8 * p) (B + 8 * nn) nsp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880)) (Z_to_bv 64 (lh + 64)) a1 a2 (Z_to_bv 64 p') a4 a5 (Z_to_bv 64 (lh ≫ 3)) a7
               (Z_to_bv 64 pmax0) (Z_to_bv 64 ((lh + 64) ≫ 3 + 2147450880)) (Z_to_bv 64 lh) s5 s6 s7 s8 (Z_to_bv 64 2147450880) (Z_to_bv 64 na0) (Z_to_bv 64 p)
               t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_SPLIT_PRE) fc None m (seg_rom asegs)).
Proof.
  intros until nsp. intros SC FRS CHP CHN NSEP ENN PR PM NNA NAB NA0 PR' ACL ALL HIL TL ACB ALB HIB TB ACCS SLB SLN -> U0 U1 U2 U3 U4 MI.
  unfold lhs_cells in SC. unfold lhi_spill in FRS. unfold LHI_SPLIT_PRE.
  remember (B + 8 * p) as cp eqn:ECP. remember (B + 8 * nn) as cn eqn:ECNN.
  pose proof CHN as (cn' & ECN & TERMN). cbn [lseg] in ECN. subst cn'. unfold wz in TERMN.
  pose proof (chain_chainv asegs LH_CEIL _ _ _ _ _ CHP) as (hp0 & CPC & CVP). unfold wz in CPC.
  cl_eu usp 0 EU0. rewrite Z.add_0_r in EU0.
  pose proof (munch_refl [(lh + 56, lh + 68); (cn, cn + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  (* [comment removed for export] *)
  zstep. zstep. th_if_lit. zstep.
  (* [comment removed for export] *)
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small nn) by lia. zstep. zstep. zstep. zstep. zstep. th_if_lit.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  assert (E2 : Z.land ((pmax0 + p) ≪ 32) 18446744073709551615 ≫ 29 = 8 * nn).
  { rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace ((pmax0 + p) * 2 ^ 32) with ((8 * nn) * 2 ^ 29) by lia. apply Z.div_mul. lia. }
  rewrite E2. zstep. replace (B + 8 * nn) with cn by lia.
  (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  assert (E1 : B + p ≪ 3 = cp) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite E1.
  zstep. th_fix_lit_store.
  do 4 zstep. zstep. th_if_lit.
  destruct NSEP as (FOP & BKC & CPN).
  assert (NODES : forall X, In X (map snd nsp) -> (X + 24 <= lh \/ lh + 104 <= X) /\ apartc X cp /\ apartc X cn).
  { intros X HX. split; [exact (proj1 (Forall_forall _ _) SLN X HX)| exact (proj1 (Forall_forall _ _) BKC X HX)]. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  pose proof (LhRep.agree_on_of_munch asegs _ _ _ MU WM) as AG0.
  assert (CVPc : chainv asegs LH_CEIL (DVerr GOBJ) mc (ownL L) hp0 nsp).
  { eapply chainv_agree; [exact CVP|]. eapply LhRep.agree_on_mono; [exact AG0|]. intros a (p0 & X & HX & Ha). apply (in_map snd) in HX. cbn [snd] in HX.
    destruct (NODES X HX) as (N1 & _ & N3). unfold apartc in N3. cbn [outside]. lia. }
  assert (AGP : LhRep.agree_on asegs (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W cp cn nsp a)) m mc).
  { eapply LhRep.agree_on_mono; [exact AG0|]. intros a NW. cbn [outside]. unfold split_W in NW. split; [tauto|]. split; [tauto| exact I]. }
  destruct nsp as [|[pn A] rest].
  - (* [comment removed for export] *)
    cbn [chainv] in CVP. subst hp0.
    zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    apply evt_done. unfold lhi_split_post, lhs_cells. do 16 eexists. exists mc, [], []. split; [reflexivity|].
    split; [eassumption|]. split; [exact WM|]. split; [eassumption|].
    split; [exists cp; split; [reflexivity| eassumption]|]. split; [exists cn; split; [reflexivity| eassumption]|]. split; [apply Permutation_refl| exact AGP].
  - cbn [chainv] in CVPc. destruct CVPc as (-> & OWN & RG & NC & nxt & NXC & CVR). unfold LH_CEIL, USTACK_TOP in RG. unfold wz in NXC.
    destruct (ACCS A ltac:(left; reflexivity)) as (QA1 & QA2 & QA3 & QA4).
    zstep. zstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    eapply evt_cut.
    { eapply (split_loop GOBJ L cp cn na0 p ((pn, A) :: rest) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest [] [] cp pn A nxt 0 _ _ mc);
        try eassumption; try reflexivity; try lia.
      - cbn [app]. rewrite app_nil_r. apply Permutation_refl.
      - split; [exact FOP|]. split; [exact BKC| exact CPN].
      - intros X HX. destruct (ACCS X HX) as (Q1 & Q2 & Q3 & Q4). split; [exact (acc_munch_sh _ m _ _ _ Q1 MU HWS ltac:(lia) ltac:(lia))| auto].
      - apply (acc_munch_sh _ m _ _ _ (acc_sub asegs m B (8 * na) cp 8 ACB ltac:(lia) ltac:(lia)) MU HWS); lia.
      - try (subst cp; Z.div_mod_to_equations; lia). apply (acc_munch_sh _ m _ _ _ (acc_sub asegs m B (8 * na) cn 8 ACB ltac:(lia) ltac:(lia)) MU HWS); lia.
      all: try (subst cn; Z.div_mod_to_equations; lia). all: try (unfold LH_CEIL, USTACK_TOP; exact RG). }
    intros ms' (b1 & b2 & b5 & mf & stay' & moved' & -> & MIf & C1 & C2 & PMf & AGf & WMf).
    apply evt_done. unfold lhi_split_post, lhs_cells. do 16 eexists. exists mf, stay', moved'. split; [reflexivity|].
    split; [exact MIf|]. split; [eapply wmono_trans; eassumption|].
    split. { eapply LhRep.rw_cells_agree; [exact AGf| eassumption|]. intros a Ha NW. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
             unfold split_W in NW. destruct NW as [NW|[NW|(p0 & X & HX & NW)]]; [lia| lia|]. apply (in_map snd) in HX. cbn [snd] in HX. destruct (NODES X HX) as (N1 & _). lia. }
    split; [exact C1|]. split; [exact C2|]. split; [exact PMf|].
    eapply LhRep.agree_on_trans; [exact AGP|]. eapply LhRep.agree_on_mono; [exact AGf|]. intros a NW NW2. apply NW. right. exact NW2.
Qed.
