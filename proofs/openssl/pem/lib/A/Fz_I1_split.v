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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LHI_SPLIT_HEAD : Z := 0x20064c.   (* [comment removed for export] *)
Definition LHI_SPLIT_EXIT : Z := 0x200484.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition split_iter_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c A nxt hm cn nni p : Z) : machine_state -> Prop :=
  fun ms' => exists (a2' a5' : word) (c' : Z) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cn) (Z_to_bv 64 c') a2' (Z_to_bv 64 (cn ≫ 3 + 2147450880)) (Z_to_bv 64 nxt) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8
                  (Z_to_bv 64 2147450880) (Z_to_bv 64 nni) (Z_to_bv 64 p) t3 t4 t5 t6)
             F (Z_to_bv 64 (if nxt =? 0 then LHI_SPLIT_EXIT else LHI_SPLIT_HEAD)) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m'
    /\ ((c' = A + 8 /\ m' = m)
        \/ (c' = c /\ munch [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z m m' /\ wmono asegs m m'
            /\ rw_cells asegs m' c [C8 (Z_to_bv 64 nxt)] /\ rw_cells asegs m' (A + 8) [C8 (Z_to_bv 64 hm)] /\ rw_cells asegs m' cn [C8 (Z_to_bv 64 A)])).

Lemma split_iter : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c A nxt hm cn nni p : Z) (hN : word),
  rw_cells asegs m c [C8 (Z_to_bv 64 A)] -> rw_cells asegs m (A + 8) [C8 (Z_to_bv 64 nxt)] -> rw_cells asegs m (A + 16) [C8 hN] ->
  rw_cells asegs m cn [C8 (Z_to_bv 64 hm)] ->
  acc asegs m A 24 -> A mod 8 = 0 -> acc asegs m c 8 -> c mod 8 = 0 -> acc asegs m cn 8 -> cn mod 8 = 0 ->
  0x10007fff8000 <= A -> A + 24 <= 2^47 -> 0x10007fff8000 <= c -> c + 8 <= 2^47 -> 0x10007fff8000 <= cn -> cn + 8 <= 2^47 -> 0 <= nxt < 2^63 ->
  (c + 8 <= A \/ A + 24 <= c) -> (cn + 8 <= A \/ A + 24 <= cn) -> (c + 8 <= cn \/ cn + 8 <= c) ->
  0 < nni < 2^32 -> 0 <= p < 2^32 ->
  mem_inv asegs m ->
  evt asegs (split_iter_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m c A nxt hm cn nni p)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cn) (Z_to_bv 64 c) a2 (Z_to_bv 64 (cn ≫ 3 + 2147450880)) (Z_to_bv 64 A) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
               (Z_to_bv 64 2147450880) (Z_to_bv 64 nni) (Z_to_bv 64 p) t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_SPLIT_HEAD) fc None m (seg_rom asegs)).
Proof.
  intros until hN. intros CC NX NH CN ACA ALA ACc ALc ACn ALn HA HA2 Hc Hc2 Hn Hn2 NXR S1 S2 S3 NNI HP MI. unfold LHI_SPLIT_HEAD.
  pose proof (munch_refl [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit. zstep. zstep.
  rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit nni) by lia.
  zstep. zstep. if_cases K.
  - (* [comment removed for export] *)
    do 3 zstep. zstep. th_if_lit. do 3 zstep. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. th_if_lit. zstep. zstep. zstep.
    do 3 zstep. zstep. th_if_lit. zstep.
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + apply evt_done. unfold split_iter_post. do 2 eexists. exists c. eexists. split; [replace (nxt =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity|].
      split; [eassumption|]. right. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. auto.
    + apply evt_done. unfold split_iter_post. do 2 eexists. exists c. eexists. split; [replace (nxt =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      split; [eassumption|]. right. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. auto.
  - (* [comment removed for export] *)
    zstep. zstep. do 3 zstep. zstep. th_if_lit. zstep.
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + apply evt_done. unfold split_iter_post. do 2 eexists. exists (A + 8), m. split; [replace (nxt =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity|].
      split; [exact MI|]. left. auto.
    + apply evt_done. unfold split_iter_post. do 2 eexists. exists (A + 8), m. split; [replace (nxt =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      split; [exact MI|]. left. auto.
Qed.

(* [comment removed for export] *)
Definition split_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (cp cn nni p : Z) (ALL : list (bptr * Z)) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a5' : word) (m' : mem) (stay' moved' : list (bptr * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cn) a1' a2' (Z_to_bv 64 (cn ≫ 3 + 2147450880)) (Z_to_bv 64 0) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8
                  (Z_to_bv 64 2147450880) (Z_to_bv 64 nni) (Z_to_bv 64 p) t3 t4 t5 t6)
             F (Z_to_bv 64 LHI_SPLIT_EXIT) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m'
    /\ chain asegs LH_CEIL (DVerr GOBJ) m' (ownL L) cp stay' /\ chain asegs LH_CEIL (DVerr GOBJ) m' (ownL L) cn moved'
    /\ Permutation (stay' ++ moved') ALL
    /\ LhRep.agree_on asegs (fun a => ~ split_W cp cn ALL a) m m' /\ wmono asegs m m'.

Lemma split_loop : forall (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (cp cn nni p : Z) (ALL : list (bptr * Z))
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (rem stay moved : list (bptr * Z)) (c : Z) (pn : bptr) (A nxt hm : Z) (a2 a5 : word) (m : mem),
  Permutation (stay ++ (pn, A) :: rem ++ moved) ALL -> nsep ALL cp cn ->
  (forall X, In X (map snd ALL) -> acc asegs m X 24 /\ X mod 8 = 0 /\ 0x10007fff8000 <= X /\ X + 24 <= 2^47) ->
  acc asegs m cp 8 -> cp mod 8 = 0 -> 0x10007fff8000 <= cp -> cp + 8 <= 2^47 ->
  acc asegs m cn 8 -> cn mod 8 = 0 -> 0x10007fff8000 <= cn -> cn + 8 <= 2^47 ->
  0 < nni < 2^32 -> 0 <= p < 2^32 ->
  lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) cp stay c -> rw_cells asegs m c [C8 (Z_to_bv 64 A)] ->
  ownL L pn A 24 24 -> (0 < A /\ A + 24 <= LH_CEIL) -> node_cells asegs (DVerr GOBJ) m A ->
  rw_cells asegs m (A + 8) [C8 (Z_to_bv 64 nxt)] -> chainv asegs LH_CEIL (DVerr GOBJ) m (ownL L) nxt rem ->
  rw_cells asegs m cn [C8 (Z_to_bv 64 hm)] -> chainv asegs LH_CEIL (DVerr GOBJ) m (ownL L) hm moved ->
  mem_inv asegs m ->
  evt asegs (split_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m GOBJ L cp cn nni p ALL)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cn) (Z_to_bv 64 c) a2 (Z_to_bv 64 (cn ≫ 3 + 2147450880)) (Z_to_bv 64 A) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
               (Z_to_bv 64 2147450880) (Z_to_bv 64 nni) (Z_to_bv 64 p) t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_SPLIT_HEAD) fc None m (seg_rom asegs)).
Proof.
  intros GOBJ L cp cn nni p ALL ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc rem.
  induction rem as [|[q Bq] rem' IH]; intros stay moved c pn A nxt hm a2 a5 m PERM NSEP ACCS ACP ALP HIP TP ACN ALN HIN TN NNI HP LSEG CC OWN RG NC NX CVR CN CVM MI.
  all: pose proof (nsep_perm _ _ _ _ NSEP (Permutation_sym PERM)) as (FO & BK & CPN).
  all: rewrite map_app in FO, BK; cbn [map snd] in FO, BK.
  all: destruct (fop_app_inv _ _ _ FO) as (FOS & FOR & XSA); inversion FOR as [|x l FA FO2]; subst x l.
  all: apply Forall_app in BK; destruct BK as [BKS BKR]; inversion BKR as [|x l [BKA1 BKA2] BKR2]; subst x l.
  all: pose proof NC as (d & hN & N1 & DVd & N2).
  all: assert (INA : In (pn, A) ALL) by (eapply Permutation_in; [exact PERM| apply in_or_app; right; left; reflexivity]).
  all: destruct (ACCS A ltac:(apply in_map_iff; exists (pn, A); split; [reflexivity| exact INA])) as (ACA & ALA & HIA & TA).
  (* [comment removed for export] *)
  all: assert (CLOC : c = cp \/ exists X, In X (map snd stay) /\ c = X + 8).
  1,3: (clear - LSEG; revert LSEG; generalize cp; induction stay as [|[q0 B0] stay IHs]; intros z R; cbn [lseg] in R; [left; symmetry; exact R|];
        destruct R as (_ & _ & _ & _ & R); destruct (IHs _ R) as [E|(X & HX & E)]; right; [exists B0; split; [left; reflexivity| exact E]| exists X; split; [right; exact HX| exact E]]).
  all: assert (SCA : c + 8 <= A \/ A + 24 <= c) by (unfold apartc, apart24 in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (XSA X A HX ltac:(left; reflexivity)); lia).
  all: assert (SCN : c + 8 <= cn \/ cn + 8 <= c) by (unfold apartc in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (proj1 (Forall_forall _ _) BKS X HX) as [_ Y]; lia).
  all: assert (ACc : acc asegs m c 8 /\ c mod 8 = 0 /\ 0x10007fff8000 <= c /\ c + 8 <= 2^47).
  1,3: (destruct CLOC as [->|(X & HX & ->)]; [auto|];
        destruct (ACCS X ltac:(eapply Permutation_in; [apply Permutation_map; exact PERM|]; rewrite map_app; apply in_or_app; left; exact HX)) as (Q1 & Q2 & Q3 & Q4);
        split; [apply (acc_sub asegs m X 24 (X + 8) 8 Q1); lia|]; split; [Z.div_mod_to_equations; lia| lia]).
  all: destruct ACc as (ACc & ALc & HIc & Tc).
  all: unfold apartc in BKA1, BKA2.
  (* [comment removed for export] *)
  all: assert (OUTS : forall a, lseg_fp cp stay a -> outside [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z a)
         by (intros a Ha; pose proof (lseg_fp_end asegs LH_CEIL _ _ _ _ _ _ LSEG FOS ltac:(eapply Forall_impl; [| exact BKS]; intros ? [? _]; assumption) a Ha) as NE;
             cbn [outside]; destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)];
             [lia| apply (in_map snd) in HX; cbn [snd] in HX; pose proof (XSA X A HX ltac:(left; reflexivity)) as Z1;
                   pose proof (proj1 (Forall_forall _ _) BKS X HX) as [_ Z2]; unfold apart24, apartc in *; lia]).
  all: lazymatch type of FA with Forall _ ?others =>
         assert (OUTN : forall X, In X others -> forall a, X <= a < X + 24 -> outside [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z a)
           by (intros X HX a Ha; pose proof (proj1 (Forall_forall _ _) FA X HX) as Z1; pose proof (proj1 (Forall_forall _ _) BKR2 X HX) as [Z2 Z3];
               cbn [outside]; unfold apart24, apartc in *; destruct CLOC as [->|(Y & HY & ->)]; [lia|]; pose proof (XSA Y X HY ltac:(right; exact HX)); lia) end.
  all: unfold LH_CEIL, USTACK_TOP in RG.
  - (* [comment removed for export] *)
    cbn [chainv] in CVR. subst nxt.
    eapply evt_cut; [eapply (split_iter ra sp gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m c A 0 hm cn nni p hN); try eassumption; lia|].
    intros ms1 (a2' & a5' & c' & m1 & -> & MI1 & ARM). change (0 =? 0) with true. cbv iota.
    apply evt_done. destruct ARM as [[-> ->]|(-> & MU1 & WM1 & CC1 & NX1 & CN1)].
    + exists (Z_to_bv 64 (A + 8)), a2', a5', m, (stay ++ [(pn, A)]), moved.
      split; [reflexivity|]. split; [exact MI|].
      split. { exists (A + 8). split; [| exact NX]. eapply lseg_app; [exact LSEG|]. cbn [lseg]. split; [exact CC|]. split; [exact OWN|]. split; [unfold LH_CEIL, USTACK_TOP; exact RG|]. split; [exact NC| reflexivity]. }
      split; [exact (chainv_chain asegs LH_CEIL _ _ _ _ _ _ CN CVM)|].
      split; [rewrite <- app_assoc; exact PERM|]. split; [apply LhRep.agree_on_refl| apply wmono_refl].
    + pose proof (LhRep.agree_on_of_munch asegs _ _ _ MU1 WM1) as AG1.
      exists (Z_to_bv 64 c), a2', a5', m1, stay, ((pn, A) :: moved).
      split; [reflexivity|]. split; [exact MI1|].
      split. { exists c. split; [| exact CC1]. eapply lseg_agree; [exact LSEG| | intros ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact AG1| exact OUTS]. }
      split. { eapply chainv_chain; [exact CN1|]. cbn [chainv]. split; [reflexivity|]. split; [exact OWN|]. split; [unfold LH_CEIL, USTACK_TOP; exact RG|].
        split. { exists d, hN. split; [| split; [exact DVd|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
                 cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        exists hm. split; [exact NX1|]. eapply chainv_agree; [exact CVM|]. eapply LhRep.agree_on_mono; [exact AG1|].
        intros a (p0 & X & HX & Ha). apply (OUTN X); [apply (in_map snd) in HX; exact HX| exact Ha]. }
      split; [exact PERM|]. split; [| exact WM1].
      eapply LhRep.agree_on_mono; [exact AG1|]. intros a NW. cbn [outside]. unfold split_W in NW.
      split; [| split; [| split; [| exact I]]]; intros Hin; apply NW.
      * destruct CLOC as [->|(X & HX & ->)]; [left; exact Hin|]. right; right.
        apply in_map_iff in HX. destruct HX as ([p0 X0] & E & HX). cbn [snd] in E. subst X0. exists p0, X. split; [| lia].
        eapply Permutation_in; [exact PERM| apply in_or_app; left; exact HX].
      * right; right. exists pn, A. split; [exact INA| lia].
      * right; left. exact Hin.
  - (* [comment removed for export] *)
    cbn [chainv] in CVR. destruct CVR as (-> & OWNq & RGq & NCq & nx2 & NXq & CVR'). unfold LH_CEIL, USTACK_TOP in RGq.
    assert (INQ : In Bq (Bq :: map snd (rem' ++ moved))) by (left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) FA Bq INQ) as QA. pose proof (proj1 (Forall_forall _ _) BKR2 Bq INQ) as [QCP QCN].
    assert (QC : c + 8 <= Bq \/ Bq + 24 <= c) by (unfold apartc, apart24 in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (XSA X Bq HX ltac:(right; exact INQ)); lia).
    unfold apart24, apartc in QA, QCP, QCN.
    eapply evt_cut; [eapply (split_iter ra sp gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m c A Bq hm cn nni p hN); try eassumption; lia|].
    intros ms1 (a2' & a5' & c' & m1 & -> & MI1 & ARM). replace (Bq =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    destruct ARM as [[-> ->]|(-> & MU1 & WM1 & CC1 & NX1 & CN1)].
    + (* [comment removed for export] *)
      eapply (IH (stay ++ [(pn, A)]) moved (A + 8) q Bq nx2 hm a2' a5' m); try eassumption.
      * rewrite <- app_assoc. exact PERM.
      * eapply lseg_app; [exact LSEG|]. cbn [lseg]. split; [exact CC|]. split; [exact OWN|]. split; [unfold LH_CEIL, USTACK_TOP; exact RG|]. split; [exact NC| reflexivity].
    + (* [comment removed for export] *)
      pose proof (LhRep.agree_on_of_munch asegs _ _ _ MU1 WM1) as AG1.
      lazymatch type of MU1 with munch ?W _ _ => assert (HWS1 : sh_fp W) by sh_fp_lia end.
      assert (AGW : LhRep.agree_on asegs (fun a => ~ split_W cp cn ALL a) m m1).
      { eapply LhRep.agree_on_mono; [exact AG1|]. intros a NW. cbn [outside]. unfold split_W in NW.
        split; [| split; [| split; [| exact I]]]; intros Hin; apply NW.
        * destruct CLOC as [->|(X & HX & ->)]; [left; exact Hin|]. right; right.
          apply in_map_iff in HX. destruct HX as ([p0 X0] & E & HX). cbn [snd] in E. subst X0. exists p0, X. split; [| lia].
          eapply Permutation_in; [exact PERM| apply in_or_app; left; exact HX].
        * right; right. exists pn, A. split; [exact INA| lia].
        * right; left. exact Hin. }
      eapply evt_mono.
      { eapply (IH stay ((pn, A) :: moved) c q Bq nx2 A a2' a5' m1); try eassumption.
        - eapply Permutation_trans; [| exact PERM]. apply Permutation_app_head. apply Permutation_sym.
          exact (Permutation_cons_app ((q, Bq) :: rem') moved (pn, A) (Permutation_refl _)).
        - intros X HX. destruct (ACCS X HX) as (Q1 & Q2 & Q3 & Q4). split; [exact (acc_munch_sh _ m _ _ _ Q1 MU1 HWS1 ltac:(lia) ltac:(lia))| auto].
        - exact (acc_munch_sh _ m _ _ _ ACP MU1 HWS1 ltac:(lia) ltac:(lia)).
        - exact (acc_munch_sh _ m _ _ _ ACN MU1 HWS1 ltac:(lia) ltac:(lia)).
        - eapply lseg_agree; [exact LSEG| | intros ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact AG1| exact OUTS].
        - destruct NCq as (dq & hq & Q1 & DVq & Q2). exists dq, hq. split; [| split; [exact DVq|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
            cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
        - eapply rw_cells_transport; [exact NXq| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
        - eapply chainv_agree; [exact CVR'|]. eapply LhRep.agree_on_mono; [exact AG1|].
          intros a (p0 & X & HX & Ha). apply (OUTN X); [| exact Ha]. right. apply in_map_iff. exists (p0, X). split; [reflexivity| apply in_or_app; left; exact HX].
        - cbn [chainv]. split; [reflexivity|]. split; [exact OWN|]. split; [unfold LH_CEIL, USTACK_TOP; exact RG|].
          split. { exists d, hN. split; [| split; [exact DVd|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
                   cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
          exists hm. split; [exact NX1|]. eapply chainv_agree; [exact CVM|]. eapply LhRep.agree_on_mono; [exact AG1|].
          intros a (p0 & X & HX & Ha). apply (OUTN X); [| exact Ha]. right. apply in_map_iff. exists (p0, X). split; [reflexivity| apply in_or_app; right; exact HX]. }
      intros ms' (b1 & b2 & b5 & mf & st' & mv' & -> & MIf & C1f & C2f & PMf & AGf & WMf).
      exists b1, b2, b5, mf, st', mv'. split; [reflexivity|]. split; [exact MIf|]. split; [exact C1f|]. split; [exact C2f|]. split; [exact PMf|].
      split; [eapply LhRep.agree_on_trans; eassumption| eapply wmono_trans; eassumption].
Qed.
