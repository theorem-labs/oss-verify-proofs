(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AzReadS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AzReadS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys5q OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages.AsAinvMainFactsA.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition wpair_eqb (x y : word * word) : bool := Z.eqb (u (fst x)) (u (fst y)) && Z.eqb (u (snd x)) (u (snd y)).
Lemma wpair_eqb_eq : forall x y, wpair_eqb x y = true <-> x = y.
Proof.
  intros [a n] [b m]. unfold wpair_eqb. cbn [fst snd]. rewrite andb_true_iff, !Z.eqb_eq. split.
  - intros [H1 H2]. f_equal; apply bv_eq; assumption.
  - intros E. injection E as -> ->. split; reflexivity.
Qed.
Fixpoint remove1 (x : word * word) (l : list (word * word)) : list (word * word) :=
  match l with [] => [] | y :: t => if wpair_eqb x y then t else y :: remove1 x t end.
Lemma remove1_perm : forall x l, In x l -> Permutation l (x :: remove1 x l).
Proof.
  intros x l. induction l as [|y t IH]; intros Hin; [destruct Hin|]. cbn [remove1].
  destruct (wpair_eqb x y) eqn:E.
  - apply wpair_eqb_eq in E. subst y. apply Permutation_refl.
  - destruct Hin as [-> | Hin]; [pose proof (proj2 (wpair_eqb_eq x x) eq_refl); congruence|].
    eapply Permutation_trans; [apply perm_skip; exact (IH Hin) | apply perm_swap].
Qed.
Lemma remove1_In : forall x l y, In y (remove1 x l) -> In y l.
Proof.
  intros x l. induction l as [|z t IH]; intros y Hy; [exact Hy|]. cbn [remove1] in Hy.
  destruct (wpair_eqb x z); [right; exact Hy|]. destruct Hy as [-> | Hy]; [left; reflexivity | right; exact (IH y Hy)].
Qed.

Section MainA2.
  Context {RC : run_ceil}.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_in_hull : forall a : word, APS.in_hull AT_A (u a) = false -> find_segment ASEGS (u a) 1 = None.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= u a /\ u (edenot E ISP_S) <= u a.
  Lemma HULL_ok : APS.hull_ok AT_A.
  Proof. unfold APS.hull_ok. cbn. unfold KHI. repeat split; reflexivity || lia. Qed.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : APS.cs_ok ASEGS AT_A LIMIT_S SINV argH ISP_S FS0 E HS_2 R FULL model.
  (* [comment removed for export] *)
  Hypothesis HCEIL : page_floor (alloc_top (m_vmmaps model)) = GlzConst.RunCeil.CEIL.
  #[local] Notation h := (m_vmmaps model).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition uv (i : nat) : Z := u (ev E i).
  Definition e_ttop : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10)).
  Definition w6 : word := Z_to_bv 64 (4096 * uv 227).
  Definition n6 : word := Z_to_bv 64 0x2000011000.
  (* [comment removed for export] *)
  Definition aa0 : list (Z * Z) := (APS.pagedown (AsVocab.SB + GlzConst.RunCeil.CEIL / 8), AsVocab.SB + 2 ^ 44) :: APS.allowA AT_A E HS_2.
  Definition hv : bvars :=
    BVARS (uv 227) (uv 229) (uv 246) (uv 247) (uv 248) (uv 330) (uv 397) (uv 517) (uv 518)
          (u (edenot E e_ttop)) 17355219521686432423 2 aa0
          (remove1 (w6, n6) (vm_maps h)) (vm_noaccess h) (m_vm_lazy model) (m_vm_materialized model) (eager_used model)
          (vm_brk h) (vm_start_brk h) (vm_mmap_base h) (vm_init_sp h) (vm_reserved h).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rng : forall i lo hi, In (KRange (EVar i) lo hi) (kn HS_2) -> lo <= uv i <= hi.
  Proof. intros i lo hi HK. exact (AsAinvMainLib.krange_bounds CS _ _ _ HK). Qed.
  Lemma R227 : 4295491576 <= uv 227 <= 34326181871. Proof. exact (rng _ _ _ K2.rng_v227). Qed.
  Lemma R229 : 1 <= uv 229 <= 16. Proof. exact (rng _ _ _ K2.rng_v229). Qed.
  Lemma R246 : 1629 <= uv 246 <= 34359734272. Proof. exact (rng _ _ _ K2.rng_v246). Qed.
  Lemma R247 : 1 <= uv 247 <= 34359736319. Proof. exact (rng _ _ _ K2.rng_v247). Qed.
  Lemma R248 : 1629 <= uv 248 <= 34359736304. Proof. exact (rng _ _ _ K2.rng_v248). Qed.
  Lemma R330 : 1 <= uv 330 <= 34359736319. Proof. exact (rng _ _ _ K2.rng_v330). Qed.
  Lemma R397 : 1629 <= uv 397 <= 34359733495. Proof. exact (rng _ _ _ K2.rng_v397). Qed.
  Lemma R517 : 1629 <= uv 517 <= 34359736064. Proof. exact (rng _ _ _ K2.rng_v517). Qed.
  Lemma R518 : 1629 <= uv 518 <= 34359734272. Proof. exact (rng _ _ _ K2.rng_v518). Qed.

  (* [comment removed for export] *)
  Lemma u_page : forall i, uv i <= 2 ^ 51 -> u (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar i))) = 4096 * uv i.
  Proof.
    intros i Hi. unfold uv in *. cbn [edenot]. pose proof (u64_range (ev E i)).
    rewrite u_mul64, u64_lit by lia. apply Z.mod_small. lia.
  Qed.
  Lemma estart_page : forall i o, uv i <= 2 ^ 51 -> estart E (SA (EMd Instr.M_MUL (ELit 4096) (EVar i)) o) = 4096 * uv i + o.
  Proof. intros i o Hi. unfold estart. cbn [a_base a_off]. rewrite (u_page i Hi). reflexivity. Qed.
  Lemma estart_lit : forall o, estart E (SA (ELit 0) o) = o.
  Proof. intros o. unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.
  Lemma elenZ_lit : forall z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
  Proof. intros z Hz. unfold elenZ. cbn [edenot]. apply u64_lit. exact Hz. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition grant_am (i : nat) (n : Z) (k : mkind) : amap := AM (EMd Instr.M_MUL (ELit 4096) (EVar i)) (ELit n) k.
  Lemma In_maps : forall m, In m (a_maps HS_2) -> is_fog m = false -> In (APS.amap_den E m) (vm_maps h).
  Proof. intros m Hm Hf. exact (APS.maps_match_In E (a_maps HS_2) (vm_maps h) m (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ CS) Hm Hf). Qed.
  Lemma bounds_of : forall (iv : word * word), In iv (vm_maps h) ->
    0 < u (snd iv) /\ u (fst iv) mod 4096 = 0 /\ u (snd iv) mod 4096 = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= alloc_top h
    /\ (u (fst iv) + u (snd iv) <= img_lo AT_A \/ img_hi AT_A <= u (fst iv)).
  Proof. intros iv Hin. pose proof (APS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ CS) as B. rewrite Forall_forall in B. exact (B iv Hin). Qed.

  (* [comment removed for export] *)
  Lemma grant_facts : forall i n k, In (grant_am i n k) (a_maps HS_2) -> is_tok_kind k = false -> uv i <= 2 ^ 51 -> 0 <= n < 2 ^ 64 ->
    In (Z_to_bv 64 (4096 * uv i), Z_to_bv 64 n) (vm_maps h)
    /\ 0 < n /\ 0 < 4096 * uv i /\ 4096 * uv i + n <= GlzConst.RunCeil.CEIL /\ (4096 * uv i + n <= 0x10000 \/ 0x65d000 <= 4096 * uv i).
  Proof.
    intros i n k Hm Hk Hi Hn.
    pose proof (In_maps (grant_am i n k) Hm Hk) as HIn.
    assert (U0 : 0 <= uv i) by (unfold uv; pose proof (u64_range (ev E i)); lia).
    assert (ED : APS.amap_den E (grant_am i n k) = (Z_to_bv 64 (4096 * uv i), Z_to_bv 64 n)).
    { unfold APS.amap_den, grant_am. cbn [am_base am_len].
      assert (E1 : edenot E (EMd Instr.M_MUL (ELit 4096) (EVar i)) = Z_to_bv 64 (4096 * uv i)) by (apply bv_eq; rewrite (u_page i Hi), u64_lit by lia; reflexivity).
      rewrite E1. reflexivity. }
    rewrite ED in HIn. split; [exact HIn|].
    destruct (bounds_of _ HIn) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [fst snd] in *. rewrite !u64_lit in * by lia.
    pose proof ceil_rng as CR. unfold page_floor in HCEIL.
    split; [exact B1|]. split; [exact B4|]. split; [| exact B6].
    (* [comment removed for export] *)
    assert (AL : (4096 * uv i + n) mod 4096 = 0) by (rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; exact B3).
    clear -B5 AL HCEIL. Z.div_mod_to_equations. lia.
  Qed.

  Definition gfacts (g n : Z) : Prop :=
    In (Z_to_bv 64 g, Z_to_bv 64 n) (vm_maps h) /\ 0 < n /\ 0 < g /\ g + n <= GlzConst.RunCeil.CEIL /\ (g + n <= 0x10000 \/ 0x65d000 <= g).
  Lemma G227 : gfacts (4096 * uv 227) 0x2000011000. Proof. apply (grant_facts 227 _ KMIXED); [vm_compute; tauto | reflexivity | pose proof R227; lia | lia]. Qed.
  Lemma G246 : gfacts (4096 * uv 246) (2 ^ 23).     Proof. apply (grant_facts 246 _ KNONELAZY); [vm_compute; tauto | reflexivity | pose proof R246; lia | lia]. Qed.
  Lemma G247 : gfacts (4096 * uv 247) PG.           Proof. apply (grant_facts 247 _ KRW); [vm_compute; tauto | reflexivity | pose proof R247; lia | unfold PG; lia]. Qed.
  Lemma G248 : gfacts (4096 * uv 248) 0x10000.      Proof. apply (grant_facts 248 _ KRW); [vm_compute; tauto | reflexivity | pose proof R248; lia | lia]. Qed.
  Lemma G330 : gfacts (4096 * uv 330) PG.           Proof. apply (grant_facts 330 _ KRW); [vm_compute; tauto | reflexivity | pose proof R330; lia | unfold PG; lia]. Qed.
  Lemma G397 : gfacts (4096 * uv 397) FAKE_SIZE.    Proof. apply (grant_facts 397 _ KRW); [vm_compute; tauto | reflexivity | pose proof R397; lia | unfold FAKE_SIZE; lia]. Qed.
  Lemma G517 : gfacts (4096 * uv 517) (2 ^ 20).     Proof. apply (grant_facts 517 _ KRW); [vm_compute; tauto | reflexivity | pose proof R517; lia | lia]. Qed.
  Lemma G518 : gfacts (4096 * uv 518) (2 ^ 23).     Proof. apply (grant_facts 518 _ KRWLAZY); [vm_compute; tauto | reflexivity | pose proof R518; lia | lia]. Qed.

  (* [comment removed for export] *)
  Lemma disj_pages : forall i n j m,
    In (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar i)) 0) (ELit n) (SA (EMd Instr.M_MUL (ELit 4096) (EVar j)) 0) (ELit m)) (kn HS_2) ->
    uv i <= 2 ^ 51 -> uv j <= 2 ^ 51 -> 0 <= n < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
    apart (4096 * uv i) n (4096 * uv j) m.
  Proof.
    intros i n j m HK Hi Hj Hn Hm. pose proof (AsAinvMainLib.kdisj_apart CS _ _ _ _ HK) as D.
    rewrite !estart_page, !elenZ_lit in D by assumption. unfold apart. lia.
  Qed.
  Lemma disj_page_lit : forall i n b m,
    In (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar i)) 0) (ELit n) (SA (ELit 0) b) (ELit m)) (kn HS_2) ->
    uv i <= 2 ^ 51 -> 0 <= n < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
    apart (4096 * uv i) n b m.
  Proof.
    intros i n b m HK Hi Hn Hm. pose proof (AsAinvMainLib.kdisj_apart CS _ _ _ _ HK) as D.
    rewrite !estart_page, !estart_lit, !elenZ_lit in D by assumption. unfold apart. lia.
  Qed.
  Lemma apart_sym : forall a n b m, apart a n b m -> apart b m a n.
  Proof. intros a n b m H. unfold apart in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma offband : forall g n, apart g n 2147446784 17592186048512 -> (g + n <= AS_LO \/ AS_HEAPLO <= g).
  Proof. intros g n H. unfold apart, AS_LO, AS_HEAPLO in *. lia. Qed.

  Lemma rng_ok_of : forall g n, gfacts g n -> apart g n 2147446784 17592186048512 -> rng_ok g (g + n).
  Proof.
    intros g n (G1 & G2 & G3 & G4 & G5) D. unfold rng_ok. cbn [ia_img_lo ia_img_hi asan_addrs].
    split; [lia|]. split; [lia|]. split; [lia|]. exact (offband g n D).
  Qed.

  (* [comment removed for export] *)
  Lemma lazy_hosts : forall a : word, page_in_ranges (page_base a) (m_vm_lazy model) = true ->
    let z := u a in
    (4096 * uv 227 <= z < 4096 * uv 227 + 0x2000011000) \/ (4096 * uv 246 <= z < 4096 * uv 246 + 2 ^ 23)
    \/ (4096 * uv 518 <= z < 4096 * uv 518 + 2 ^ 23)
    \/ (0x7fff7000 <= z < 0x8fff7000) \/ (0x8fff7000 <= z < 0x2008fff7000) \/ (0x2008fff7000 <= z < 0x10007fff8000).
  Proof.
    intros a Hl. cbn zeta. destruct (APS.co_lazysub _ _ _ _ _ _ _ _ _ _ _ _ CS a Hl) as (m & Hm & Hh & Hr).
    pose proof R227 as X1. pose proof R246 as X2. pose proof R518 as X3.
    assert (U0 : forall i, 0 <= uv i) by (intros i; unfold uv; pose proof (u64_range (ev E i)); lia).
    revert Hm Hh Hr. generalize m. intros m0 Hm.
    (* [comment removed for export] *)
    let L := eval vm_compute in (a_maps HS_2) in change (a_maps HS_2) with L in Hm.
    cbn [In] in Hm.
    repeat match type of Hm with _ \/ _ => destruct Hm as [Hm | Hm] | False => destruct Hm end;
      subst m0; cbn [am_kind lazy_host]; intros Hh Hr; try discriminate Hh;
      unfold APS.amap_den in Hr; cbn [am_base am_len fst snd edenot] in Hr;
      rewrite ?u_mul64, ?u_add64, ?u64_lit in Hr by lia.
    all: try (unfold uv in *; rewrite ?Z.mod_small in Hr by (pose proof (u64_range (ev E 227)); pose proof (u64_range (ev E 246)); pose proof (u64_range (ev E 518)); lia); lia).
  Qed.

  (* [comment removed for export] *)
  Definition am_RI : amap :=
    AM (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 227)) (EMd Instr.M_MUL (ELit 4096) (EVar 229))) (ELit 137438953472))
       (ELit 4096) KEAGER.
  Lemma den_RI : u (fst (APS.amap_den E am_RI)) = SPB hv + KSPACE /\ u (snd (APS.amap_den E am_RI)) = PG.
  Proof.
    pose proof R227. pose proof R229. pose proof (u_page 227 ltac:(lia)) as U1. pose proof (u_page 229 ltac:(lia)) as U2.
    unfold APS.amap_den, am_RI, SPB, KSPACE, PG. cbn [fst snd am_base am_len bt_ia hv b_g6 b_w6]. cbn [edenot] in *.
    rewrite !u_add64, U1, U2, !u64_lit by lia. rewrite (Z.mod_small (4096 * uv 227 + 4096 * uv 229)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma RI_not_lazy : forall a, SPB hv + KSPACE <= a < SPB hv + KSPACE + PG -> ~ pg_in_ivz (m_vm_lazy model) a.
  Proof.
    intros a Ha Hl. destruct Hl as [_ Hl].   (* [comment removed for export] *)
    pose proof (APS.co_etok _ _ _ _ _ _ _ _ _ _ _ _ CS) as ET. rewrite Forall_forall in ET.
    destruct (ET am_RI ltac:(vm_compute; tauto) eq_refl) as (_ & _ & X).
    destruct den_RI as [D1 D2]. pose proof R227. pose proof R229. unfold SPB, KSPACE, PG in *. cbn [hv b_g6 b_w6] in *.
    destruct (X (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; lia)) as [_ NL]. rewrite NL in Hl. discriminate Hl.
  Qed.

  (* [comment removed for export] *)
  Lemma LZ_off : forall a, pg_in_ivz (m_vm_lazy model) a -> 0 <= a < GlzConst.RunCeil.CEIL -> ~ in_band a ->
    (4096 * uv 227 <= a < 4096 * uv 227 + 0x2000011000) \/ (4096 * uv 246 <= a < 4096 * uv 246 + 2 ^ 23) \/ (4096 * uv 518 <= a < 4096 * uv 518 + 2 ^ 23).
  Proof.
    intros a Hl Ha Hb. pose proof ceil_rng. pose proof (lazy_hosts (Z_to_bv 64 a) (proj2 Hl)) as X. cbn zeta in X. rewrite u64_lit in X by lia.
    unfold in_band, AS_LO, AS_HEAPLO in Hb. lia.
  Qed.
  Lemma LZ_band : forall a, pg_in_ivz (m_vm_lazy model) a -> 0 <= a < GlzConst.RunCeil.CEIL -> in_band a -> shmaps a \/ (AS_GAPLO <= a < AS_GAPHI).
  Proof.
    intros a Hl Ha Hb. pose proof ceil_rng. pose proof (lazy_hosts (Z_to_bv 64 a) (proj2 Hl)) as X. cbn zeta in X. rewrite u64_lit in X by lia.
    pose proof (proj2 (proj2 (proj2 (proj2 G227)))) as O6. pose proof (proj2 (proj2 (proj2 (proj2 G246)))) as O8. pose proof (proj2 (proj2 (proj2 (proj2 G518)))) as O22.
    pose proof (offband _ _ (disj_page_lit 227 _ _ _ K2.disj_g6_band ltac:(pose proof R227; lia) ltac:(lia) ltac:(lia))) as B6.
    pose proof (offband _ _ (disj_page_lit 246 _ _ _ K2.disj_g8_band ltac:(pose proof R246; lia) ltac:(lia) ltac:(lia))) as B8.
    pose proof (offband _ _ (disj_page_lit 518 _ _ _ K2.disj_g22_band ltac:(pose proof R518; lia) ltac:(lia) ltac:(lia))) as B22.
    unfold in_band, shmaps, AS_LO, AS_HEAPLO, AS_GAPLO, AS_GAPHI in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma seps_remove1 : forall l x y, APS.seps l -> In x l -> In y (remove1 x l) -> APS.iv_disjoint x y \/ APS.iv_disjoint y x.
  Proof.
    induction l as [|z t IH]; intros x y HS Hx Hy; [destruct Hy|].
    inversion HS as [| z' t' Hf Ht]; subst. cbn [remove1] in Hy. destruct (wpair_eqb x z) eqn:Exz.
    - apply wpair_eqb_eq in Exz. subst z. left. rewrite Forall_forall in Hf. exact (Hf y Hy).
    - assert (Hxt : In x t) by (destruct Hx as [-> | Hx]; [pose proof (proj2 (wpair_eqb_eq x x) eq_refl); congruence | exact Hx]).
      destruct Hy as [<- | Hy]; [right; rewrite Forall_forall in Hf; exact (Hf x Hxt) | exact (IH x y Ht Hxt Hy)].
  Qed.
  Lemma maps0_off6 : forall b n a, In (b, n) (remove1 (w6, n6) (vm_maps h)) -> u b <= a < u b + u n ->
    ~ (4096 * uv 227 <= a < 4096 * uv 227 + 0x2000011000).
  Proof.
    intros b n a Hin Ha X. destruct G227 as (I6 & _ & P6 & _). pose proof R227.
    pose proof (seps_remove1 (vm_maps h) (w6, n6) (b, n) (APS.co_seps _ _ _ _ _ _ _ _ _ _ _ _ CS) I6 Hin) as D.
    unfold APS.iv_disjoint, w6, n6 in D. cbn [fst snd] in D. rewrite !u64_lit in D by lia. lia.
  Qed.
  Lemma maps0_pos : Forall (fun e : word * word => 0 < u (snd e)) (remove1 (w6, n6) (vm_maps h)).
  Proof. apply Forall_forall. intros e He. exact (proj1 (bounds_of e (remove1_In _ _ _ He))). Qed.

  (* [comment removed for export] *)
  Lemma range_allowed_iv : forall AA L H lo hi, In (L, H) AA -> L mod 4096 = 0 -> H mod 4096 = 0 -> L <= lo -> hi <= H ->
    0 <= L -> H <= 2 ^ 64 -> range_allowed AA lo hi.
  Proof.
    intros AA L H lo hi Hin HL HH H1 H2 H0 H64 a Ha. unfold page_allowedb. apply existsb_exists. exists (L, H). split; [exact Hin|].
    cbn [fst snd]. unfold page_base, page_base_of, page_size. rewrite (u64_lit a) by lia.
    rewrite u64_lit by (Z.div_mod_to_equations; lia). apply andb_true_iff. rewrite !Z.leb_le. Z.div_mod_to_equations. lia.
  Qed.
  Lemma pagedown_le : forall z, APS.pagedown z <= z /\ APS.pagedown z mod 4096 = 0 /\ z < APS.pagedown z + 4096.
  Proof. intros z. unfold APS.pagedown. Z.div_mod_to_equations. lia. Qed.
  Lemma pageup_ge : forall z, z <= APS.pageup z /\ APS.pageup z mod 4096 = 0 /\ APS.pageup z < z + 4096.
  Proof. intros z. unfold APS.pageup. Z.div_mod_to_equations. lia. Qed.
  Lemma allow_vis : forall p, In p (a_vis HS_2) ->
    In (APS.pagedown (APS.uE E (fst p)), APS.pageup (APS.uE E (fst p) + APS.uE E (snd p))) aa0
    /\ In (APS.pagedown (APS.sh_lo AT_A E p), APS.pageup (APS.sh_hi AT_A E p)) aa0.
  Proof.
    intros p Hp. unfold aa0, APS.allowA. split; right; apply in_flat_map; exists p; (split; [apply in_app_iff; left; exact Hp|]); unfold APS.allow1; cbn; tauto.
  Qed.
  Lemma AW0 : A_wf aa0.
  Proof.
    unfold aa0. apply Forall_cons; [| apply APS.A_wf_allowA]. cbn [fst snd]. pose proof ceil_rng as CR.
    pose proof (pagedown_le (AsVocab.SB + GlzConst.RunCeil.CEIL / 8)) as (P1 & P2 & P3). unfold page_size, AsVocab.SB in *. split; [| split; [exact P2 | reflexivity]].
    clear -CR P1. Z.div_mod_to_equations. lia.
  Qed.
  Lemma ASHC0 : forall lo hi, In (lo, hi) (SHC asan_addrs (4096 * uv 397)) -> range_allowed aa0 lo hi.
  Proof.
    intros lo hi Hin. pose proof ceil_rng as CR. pose proof ceil_pg as CP. pose proof R397 as RF.
    unfold SHC in Hin. cbn [In ia_img_lo ia_img_hi asan_addrs] in Hin. destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-.
    - (* [comment removed for export] *)
      pose proof (pagedown_le (AsVocab.SB + GlzConst.RunCeil.CEIL / 8)) as (P1 & P2 & P3).
      apply (range_allowed_iv aa0 (APS.pagedown (AsVocab.SB + GlzConst.RunCeil.CEIL / 8)) (AsVocab.SB + 2 ^ 44)); [left; reflexivity | exact P2 | reflexivity | unfold sh_lo; exact P1 | lia | |];
        unfold AsVocab.SB in *; clear -CR P1 P3; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      destruct (allow_vis (ELit 65536, ELit 6606848) ltac:(vm_compute; tauto)) as [_ HI].
      unfold APS.sh_lo, APS.sh_hi, APS.uE in HI. cbn [fst snd edenot shadow_off AT_A] in HI. rewrite !u64_lit in HI by lia.
      pose proof (pagedown_le (2147450880 + 65536 / 8)) as (P1 & P2 & P3). pose proof (pageup_ge (2147450880 + (65536 + 6606848) / 8)) as (Q1 & Q2 & Q3).
      eapply range_allowed_iv; [exact HI | exact P2 | exact Q2 | unfold sh_lo, AsVocab.SB; exact P1 | | |];
        unfold APS.pageup, APS.pagedown, AsVocab.sh_hi, AsVocab.SB; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      destruct (allow_vis (EMd Instr.M_MUL (ELit 4096) (EVar 397), ELit 11571200) ltac:(vm_compute; tauto)) as [_ HI].
      unfold APS.sh_lo, APS.sh_hi, APS.uE in HI. cbn [fst snd shadow_off AT_A] in HI. rewrite (u_page 397) in HI by lia. cbn [edenot] in HI. rewrite !u64_lit in HI by lia.
      pose proof (pagedown_le (2147450880 + 4096 * uv 397 / 8)) as (P1 & P2 & P3). pose proof (pageup_ge (2147450880 + (4096 * uv 397 + 11571200) / 8)) as (Q1 & Q2 & Q3).
      eapply range_allowed_iv; [exact HI | exact P2 | exact Q2 | unfold sh_lo, AsVocab.SB; exact P1 | | |];
        unfold AsVocab.sh_hi, AsVocab.SB, FAKE_SIZE in *; clear HI P2 Q2; Z.div_mod_to_equations; lia.
  Qed.
  Lemma AST0 : range_allowed aa0 (4096 * uv 518) (4096 * uv 518 + 2 ^ 23).
  Proof.
    pose proof R518 as RS. destruct (allow_vis (EMd Instr.M_MUL (ELit 4096) (EVar 518), ELit 8388608) ltac:(vm_compute; tauto)) as [HI _].
    unfold APS.uE in HI. cbn [fst snd] in HI. rewrite (u_page 518) in HI by lia. cbn [edenot] in HI. rewrite !u64_lit in HI by lia.
    pose proof (pagedown_le (4096 * uv 518)) as (P1 & P2 & P3). pose proof (pageup_ge (4096 * uv 518 + 8388608)) as (Q1 & Q2 & Q3).
    eapply range_allowed_iv; [exact HI | exact P2 | exact Q2 | exact P1 | exact Q1 | clear -P1 P3 RS; lia | clear -Q3 RS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ALIGN : (4096 * (uv 227 + uv 229)) mod 2 ^ 16 = 0.
  Proof.
    pose proof R227 as X227. pose proof R229 as X229.
    pose proof (AsAinvMainLib.krange_bounds CS _ _ _ K2.align_w6) as KR. cbn [edenot] in KR.
    change (Z_to_bv 64 65535) with (Z_to_bv 64 (2 ^ 16 - 1)) in KR. rewrite (and_lowmask_val _ 16) in KR by lia.
    rewrite !u_add64, !u_mul64, !u_lit64a in KR. change (u (ev E 229)) with (uv 229) in KR. change (u (ev E 227)) with (uv 227) in KR.
    replace ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096) in KR by reflexivity.
    replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in KR by reflexivity.
    replace (4096 mod 2 ^ 64) with 4096 in KR by reflexivity. replace (65536 mod 2 ^ 64) with 65536 in KR by reflexivity.
    rewrite (Z.mod_small (4096 * uv 227) (2 ^ 64)) in KR by lia.
    set (m := (4096 * uv 227) mod 2 ^ 16) in KR. pose proof (Z.mod_pos_bound (4096 * uv 227) (2 ^ 16) ltac:(lia)) as MB. fold m in MB.
    rewrite (Z.mod_small m (2 ^ 64)) in KR by lia.
    replace (((2 ^ 64 - 4096) * uv 229) mod 2 ^ 64) with (2 ^ 64 - 4096 * uv 229) in KR
      by (apply Z.mod_unique with (q := uv 229 - 1); [left; lia | lia]).
    assert (W6 : 4096 * uv 229 + m = 65536).
    { destruct (Z.eqb_spec m 0) as [E0 | NE].
      - rewrite E0, Z.mul_0_r, Z.mod_0_l, Z.add_0_r in KR by lia. rewrite (Z.mod_small (2 ^ 64 - 4096 * uv 229) (2 ^ 64)) in KR by lia.
        replace ((2 ^ 64 - 4096 * uv 229 + 65536) mod 2 ^ 64) with (65536 - 4096 * uv 229) in KR
          by (apply Z.mod_unique with (q := 1); [left; lia | lia]).
        lia.
      - replace (((2 ^ 64 - 1) * m) mod 2 ^ 64) with (2 ^ 64 - m) in KR by (apply Z.mod_unique with (q := m - 1); [left; lia | lia]).
        replace ((2 ^ 64 - 4096 * uv 229 + (2 ^ 64 - m)) mod 2 ^ 64) with (2 ^ 64 - 4096 * uv 229 - m) in KR
          by (apply Z.mod_unique with (q := 1); [left; lia | lia]).
        destruct (Z.lt_ge_cases (2 ^ 64 - 4096 * uv 229 - m + 65536) (2 ^ 64)) as [LT | GE].
        + rewrite Z.mod_small in KR by lia. lia.
        + replace ((2 ^ 64 - 4096 * uv 229 - m + 65536) mod 2 ^ 64) with (2 ^ 64 - 4096 * uv 229 - m + 65536 - 2 ^ 64) in KR
            by (apply Z.mod_unique with (q := 1); [left; lia | lia]).
          lia. }
    subst m. clear KR MB. Z.div_mod_to_equations. lia.
  Qed.
  Theorem main_vars_ok : vars_ok hv.
  Proof.
    pose proof R227 as X227. pose proof R229 as X229. pose proof R246 as X246. pose proof R247 as X247. pose proof R248 as X248.
    pose proof R397 as X397. pose proof R517 as X517. pose proof R518 as X518. pose proof R330 as X330.
    unfold vars_ok. cbn [b_g6 b_w6 b_g8 b_g9 b_g10 b_g12 b_g16 b_g21 b_g22 b_hash b_sz b_aa b_maps0 b_lazy hv].
    Ltac dj H i j := first [ apply (disj_pages i _ j _ H); unfold FAKE_SIZE, PG; lia | apply apart_sym; apply (disj_pages j _ i _ H); unfold FAKE_SIZE, PG; lia ].
    split; [exact (rng_ok_of _ _ G227 (disj_page_lit 227 _ _ _ K2.disj_g6_band ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G246 (disj_page_lit 246 _ _ _ K2.disj_g8_band ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G397 (disj_page_lit 397 _ _ _ K2.disj_g16_band ltac:(lia) ltac:(unfold FAKE_SIZE; lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G247 (disj_page_lit 247 _ _ _ K2.disj_g9_band ltac:(lia) ltac:(unfold PG; lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G517 (disj_page_lit 517 _ _ _ K2.disj_g21_band ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G518 (disj_page_lit 518 _ _ _ K2.disj_g22_band ltac:(lia) ltac:(lia) ltac:(lia)))|].
    split; [exact (rng_ok_of _ _ G248 (disj_page_lit 248 _ _ _ K2.disj_g10_band ltac:(lia) ltac:(lia) ltac:(lia)))|].
    (* [comment removed for export] *)
    split; [dj K2.disj_g21_g22 517%nat 518%nat|]. split; [dj K2.disj_g16_g22 397%nat 518%nat|]. split; [dj K2.disj_g10_g22 248%nat 518%nat|].
    split; [dj K2.disj_g9_g22 247%nat 518%nat|]. split; [dj K2.disj_g8_g22 246%nat 518%nat|]. split; [dj K2.disj_g6_g22 227%nat 518%nat|].
    split; [dj K2.disj_g16_g21 397%nat 517%nat|]. split; [dj K2.disj_g10_g21 248%nat 517%nat|]. split; [dj K2.disj_g9_g21 247%nat 517%nat|].
    split; [dj K2.disj_g8_g21 246%nat 517%nat|]. split; [dj K2.disj_g6_g21 227%nat 517%nat|].
    split; [dj K2.disj_g10_g16 248%nat 397%nat|]. split; [dj K2.disj_g9_g16 247%nat 397%nat|]. split; [dj K2.disj_g8_g16 246%nat 397%nat|].
    split; [dj K2.disj_g6_g16 227%nat 397%nat|].
    split; [dj K2.disj_g9_g10 247%nat 248%nat|]. split; [dj K2.disj_g8_g10 246%nat 248%nat|]. split; [dj K2.disj_g6_g10 227%nat 248%nat|].
    split; [dj K2.disj_g8_g9 246%nat 247%nat|]. split; [dj K2.disj_g6_g9 227%nat 247%nat|].
    split; [dj K2.disj_g6_g8 227%nat 246%nat|].
    split; [unfold SPB; cbn [hv b_g6 b_w6]; exact ALIGN|]. split; [exact X229|].
    split; [exact LZ_off|]. split; [exact LZ_band|]. split; [exact RI_not_lazy|].
    split; [exact maps0_off6|]. split; [exact maps0_pos|].
    split; [lia|]. split; [lia|].
    split; [exact AW0|]. split; [exact ASHC0|]. split; [exact AST0|].
    (* [comment removed for export] *)
    split; [exact (rng_ok_of _ _ G330 (disj_page_lit 330 _ _ _ K2.disj_g12_band ltac:(lia) ltac:(unfold PG; lia) ltac:(lia)))|].
    split; [dj K2.disj_g6_g12 227%nat 330%nat|]. split; [dj K2.disj_g8_g12 246%nat 330%nat|]. split; [dj K2.disj_g12_g16 397%nat 330%nat|].
    split; [dj K2.disj_g9_g12 247%nat 330%nat|]. split; [dj K2.disj_g12_g21 517%nat 330%nat|]. split; [dj K2.disj_g12_g22 518%nat 330%nat|].
    dj K2.disj_g10_g12 248%nat 330%nat.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_perm : exists w n : word, u w = 4096 * uv 227 /\ u n = 0x2000011000 /\ Permutation (vm_maps h) ((w, n) :: remove1 (w6, n6) (vm_maps h)).
  Proof.
    pose proof R227. destruct G227 as (I6 & _). exists w6, n6. unfold w6, n6 in *. rewrite !u64_lit by lia.
    split; [reflexivity|]. split; [reflexivity|]. apply remove1_perm. exact I6.
  Qed.

  (* [comment removed for export] *)
  Lemma lazy_first_page : forall (b n : word), In (b, n) (m_vm_lazy model) -> u b mod 4096 = 0 -> 4096 <= u n -> u b + u n <= 2 ^ 64 ->
    page_in_ranges (page_base b) (m_vm_lazy model) = true.
  Proof.
    intros b n Hin Hb Hn Hw. unfold page_in_ranges. apply existsb_exists. exists (b, n). split; [exact Hin|]. cbn [fst snd].
    unfold page_base, page_base_of, page_size. pose proof (u64_range b).
    rewrite u64_lit by (Z.div_mod_to_equations; lia). apply andb_true_iff. rewrite !Z.leb_le. Z.div_mod_to_equations. lia.
  Qed.
  Lemma L_lazywf : Forall (fun iv : word * word => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= GlzConst.RunCeil.CEIL
                                            /\ (u (fst iv) + u (snd iv) <= ia_img_lo asan_addrs \/ ia_img_hi asan_addrs <= u (fst iv))) (m_vm_lazy model).
  Proof.
    apply Forall_forall. intros [b n] Hin. cbn [fst snd ia_img_lo ia_img_hi asan_addrs].
    pose proof (APS.co_lazyal _ _ _ _ _ _ _ _ _ _ _ _ CS) as AL. rewrite Forall_forall in AL. destruct (AL _ Hin) as (A1 & A2 & A3). cbn [fst snd] in A1, A2, A3.
    pose proof (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ CS) as LB. rewrite Forall_forall in LB. destruct (LB _ Hin) as [B1 B2]. cbn [fst snd img_lo img_hi AT_A] in B1, B2.
    pose proof (u64_range b) as Rb. pose proof (u64_range n) as Rn. pose proof ceil_rng as CR. unfold page_floor in HCEIL.
    assert (TOP : alloc_top h < 2 ^ 64).
    { (* [comment removed for export] *) clear -HCEIL CR. Z.div_mod_to_equations. unfold PG in *. lia. }
    assert (LZP : page_in_ranges (page_base b) (m_vm_lazy model) = true).
    { apply (lazy_first_page b n Hin A1); [clear -A2 A3 Rn; Z.div_mod_to_equations; lia | lia]. }
    pose proof (lazy_hosts b LZP) as HOST. cbn zeta in HOST.
    pose proof R227. pose proof R246. pose proof R518.
    unfold PG. split; [exact A1|]. split; [exact A2|]. split; [clear -HOST H H0 H1; lia|]. split; [| exact B1].
    assert (ALh : (u b + u n) mod 4096 = 0) by (clear -A1 A2 Rb Rn; Z.div_mod_to_equations; lia).
    clear -B2 ALh HCEIL Rb Rn. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_limit : StoreOk.RunLim.LMIN <= vm_limit h.
  Proof. exact (APS.co_limit _ _ _ _ _ _ _ _ _ _ _ _ CS). Qed.

  (* [comment removed for export] *)
  Lemma aa0_bytes : A_bytes aa0 <= 2 ^ 44 - GlzConst.RunCeil.CEIL / 8 + 4096 + a_abytes HS_2.
  Proof.
    unfold aa0. cbn [A_bytes fst snd]. pose proof (APS.co_abytes _ _ _ _ _ _ _ _ _ _ _ _ CS) as AB.
    pose proof (pagedown_le (AsVocab.SB + GlzConst.RunCeil.CEIL / 8)) as (P1 & P2 & P3). pose proof ceil_rng. unfold AsVocab.SB in *.
    clear -AB P1 P3 H. Z.div_mod_to_equations. lia.
  Qed.
  Lemma B_minv : MInv aa0 model.
  Proof.
    unfold aa0. change (?x :: APS.allowA AT_A E HS_2) with ([x] ++ APS.allowA AT_A E HS_2).
    apply APS.MInv_app; [exact (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ CS)|].
    change ([?x] ++ APS.allowA AT_A E HS_2) with aa0. pose proof aa0_bytes as AB. pose proof (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ CS) as EG.
    pose proof L_limit as LL. pose proof ceil_rng as CR. assert (EA : a_eager HS_2 = 16515072 /\ a_abytes HS_2 = 59290624) by (vm_compute; split; reflexivity).
    destruct EA as [E1 E2]. rewrite E1 in EG. rewrite E2 in AB. pose proof kbase_lmin as KL. unfold KBASE, ROOMSLACK in KL. clear -AB EG CR LL KL. Z.div_mod_to_equations. lia.   (* [comment removed for export] *)
  Qed.
  Lemma B_kbase : eager_used model + A_bytes aa0 <= KBASE.
  Proof.
    pose proof aa0_bytes as AB. pose proof (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ CS) as EG. pose proof ceil_rng as CR.
    assert (EA : a_eager HS_2 = 16515072 /\ a_abytes HS_2 = 59290624) by (vm_compute; split; reflexivity).
    destruct EA as [E1 E2]. rewrite E1 in EG. rewrite E2 in AB. unfold KBASE. clear -AB EG CR. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Definition am_losh : amap := AM (ELit 2147446784) (ELit 268435456) KRWLAZY.
  Definition am_hish : amap := AM (ELit 2201439137792) (ELit 15392894357504) KRWLAZY.
  Lemma SH_def : forall z, shmaps z -> FULL (Z_to_bv 64 z) <> None.
  Proof.
    intros z Hz.
    pose proof (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ CS) as KD. rewrite Forall_forall in KD.
    assert (GO : forall m lo n, In m (a_maps HS_2) -> am_kind m = KRWLAZY -> APS.amap_den E m = (Z_to_bv 64 lo, Z_to_bv 64 n) ->
                 0 <= lo -> lo + n < 2 ^ 64 -> lo <= z < lo + n -> FULL (Z_to_bv 64 z) <> None).
    { intros m lo n Hm Hk Hd Hlo Hhi Hzz.
      apply (APS.co_mdef _ _ _ _ _ _ _ _ _ _ _ _ CS (Z_to_bv 64 z)).
      - apply APS.in_ivs_true. exists (Z_to_bv 64 lo, Z_to_bv 64 n).
        pose proof (In_maps m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as X. rewrite Hd in X.
        split; [exact X|]. cbn [fst snd]. rewrite !u64_lit by lia. exact Hzz.
      - pose proof (f_equal fst Hd) as Hb. pose proof (f_equal snd Hd) as Hn'. unfold APS.amap_den in Hb, Hn'. cbn [fst snd] in Hb, Hn'.
        destruct (KD m Hm Hk (Z_to_bv 64 z)) as [NA _]; [| exact NA]. rewrite Hb, Hn'. rewrite !u64_lit by lia. exact Hzz. }
    unfold shmaps, AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in Hz. destruct Hz as [Hz | Hz].
    - apply (GO am_losh 2147446784 268435456); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia].
    - apply (GO am_hish 2201439137792 15392894357504); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation Mr := (APS.Mr AT_A argH E HS_2 model FULL).
  Lemma KN1 : know_ok ASEGS E Mr (kn HS_2).
  Proof. exact (AsAinvMainLib.KN CS). Qed.
  Lemma IMG_le : AP.img_lo AT_A <= AP.img_hi AT_A. Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma cellN_full : forall a n v, cellN ASEGS Mr a n v -> cellZ ASEGS FULL a n v.
  Proof. intros a n v C. unfold cellZ, cellN in *. exact (AsAinvMainLib.rdn_full SEGS_in_hull HULL_ok argH_high E HS_2 FULL model _ _ _ C). Qed.
  Lemma present_full : forall a : word, Mr a <> None -> FULL a <> None /\ store_ok ASEGS FULL a 1%nat = true.
  Proof.
    intros a Ha. destruct (APS.Mr AT_A argH E HS_2 model FULL a) as [b|] eqn:Eb; [| exfalso; exact (Ha eq_refl)].
    pose proof (AsAinvMainLib.Mr_some a b Eb) as F.
    split; [rewrite F; discriminate | apply store_ok1_some; rewrite F; discriminate].
  Qed.
  Lemma u_spb : APS.uE E RS.e_SPB = SPB hv.
  Proof.
    pose proof R227 as X227. pose proof R229 as X229. unfold APS.uE, RS.e_SPB, RS.vpg, RS.V_G6, RS.V_W6, SPB. cbn [edenot b_g6 b_w6 hv].
    rewrite u_add64, !u_mul64. change (u (ev E 227)) with (uv 227). change (u (ev E 229)) with (uv 229). rewrite !u64_lit by lia.
    rewrite (Z.mod_small (4096 * uv 227)) by lia. rewrite (Z.mod_small (4096 * uv 229)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma u_vpg : forall i, uv i <= 2 ^ 51 -> APS.uE E (RS.vpg i) = 4096 * uv i.
  Proof. intros i Hi. unfold APS.uE, RS.vpg. exact (u_page i Hi). Qed.

  (* [comment removed for export] *)
  Lemma CZ0 : forall a n v, (1 <= n <= 8)%nat -> RS.cell_z (kn HS_2) (ELit 0) a n v = true -> cellZ ASEGS FULL a n v.
  Proof. intros a n v Hn H. pose proof (RS.cell_z_sound E Mr (kn HS_2) (ELit 0) a n v KN1 Hn H) as C. rewrite RS.estart_lit in C. exact (cellN_full _ _ _ C). Qed.
  Lemma CZP : forall i o n v, uv i <= 2 ^ 51 -> (1 <= n <= 8)%nat -> RS.cell_z (kn HS_2) (RS.vpg i) o n v = true -> cellZ ASEGS FULL (4096 * uv i + o) n v.
  Proof. intros i o n v Hi Hn H. pose proof (RS.cell_z_sound E Mr (kn HS_2) (RS.vpg i) o n v KN1 Hn H) as C. unfold RS.vpg in C. rewrite (estart_page i o Hi) in C. exact (cellN_full _ _ _ C). Qed.
  Lemma CE0 : forall a n e, (1 <= n <= 8)%nat -> RS.cell_e (kn HS_2) (ELit 0) a n e = true -> cellZ ASEGS FULL a n (u (edenot E e)).
  Proof. intros a n e Hn H. pose proof (RS.cell_e_sound E Mr (kn HS_2) (ELit 0) a n e KN1 Hn H) as C. rewrite RS.estart_lit in C. exact (cellN_full _ _ _ C). Qed.
  Lemma CEP : forall i o n e, uv i <= 2 ^ 51 -> (1 <= n <= 8)%nat -> RS.cell_e (kn HS_2) (RS.vpg i) o n e = true -> cellZ ASEGS FULL (4096 * uv i + o) n (u (edenot E e)).
  Proof. intros i o n e Hi Hn H. pose proof (RS.cell_e_sound E Mr (kn HS_2) (RS.vpg i) o n e KN1 Hn H) as C. unfold RS.vpg in C. rewrite (estart_page i o Hi) in C. exact (cellN_full _ _ _ C). Qed.
  Lemma ZF0 : forall lo hi, RS.zfill_x (kn HS_2) (ELit 0) lo hi = true -> fillZ ASEGS FULL lo hi 0.
  Proof.
    intros lo hi H i Hi. pose proof (RS.zfill_x_sound E Mr (kn HS_2) (ELit 0) lo hi KN1 H i) as C.
    unfold APS.uE in C. cbn [edenot] in C. rewrite u64_lit in C by lia. exact (cellN_full _ _ _ (C ltac:(lia))).
  Qed.
  Lemma ZFP : forall j lo hi, uv j <= 2 ^ 51 -> RS.zfill_x (kn HS_2) (RS.vpg j) lo hi = true -> fillZ ASEGS FULL (4096 * uv j + lo) (4096 * uv j + hi) 0.
  Proof.
    intros j lo hi Hj H i Hi. pose proof (RS.zfill_x_sound E Mr (kn HS_2) (RS.vpg j) lo hi KN1 H i) as C. rewrite (u_vpg j Hj) in C.
    exact (cellN_full _ _ _ (C ltac:(lia))).
  Qed.
  Lemma ZFS : forall lo hi, RS.zfill_x (kn HS_2) RS.e_SPB lo hi = true -> fillZ ASEGS FULL (SPB hv + lo) (SPB hv + hi) 0.
  Proof.
    intros lo hi H i Hi. pose proof (RS.zfill_x_sound E Mr (kn HS_2) RS.e_SPB lo hi KN1 H i) as C. rewrite u_spb in C.
    exact (cellN_full _ _ _ (C ltac:(lia))).
  Qed.
  Lemma WWP : forall j lo hi, uv j <= 2 ^ 51 -> lo < hi -> RS.wwin_x AT_A (kn HS_2) (RS.vpg j) lo hi = true ->
    writableZ ASEGS FULL (4096 * uv j + lo) (4096 * uv j + hi).
  Proof.
    intros j lo hi Hj Hlt H i Hi. destruct (RS.wwin_x_sound AT_A SEGS_in_hull HULL_ok IMG_le E Mr (kn HS_2) (RS.vpg j) lo hi KN1 Hlt H i ltac:(rewrite (u_vpg j Hj); lia)) as [D _].
    exact (present_full _ D).
  Qed.
  Lemma WWS : forall lo hi, lo < hi -> RS.wwin_x AT_A (kn HS_2) RS.e_SPB lo hi = true -> writableZ ASEGS FULL (SPB hv + lo) (SPB hv + hi).
  Proof.
    intros lo hi Hlt H i Hi. destruct (RS.wwin_x_sound AT_A SEGS_in_hull HULL_ok IMG_le E Mr (kn HS_2) RS.e_SPB lo hi KN1 Hlt H i ltac:(rewrite u_spb; lia)) as [D _].
    exact (present_full _ D).
  Qed.
  Lemma KI : forall lo hi, RS.kimg_in (kn HS_2) lo hi = true -> forall a n, lo <= a -> a + Z.of_nat n <= hi -> cellZ ASEGS FULL a n 0.
  Proof. intros lo hi H a n H1 H2. exact (cellN_full _ _ _ (RS.kimg_in_sound E Mr (kn HS_2) lo hi KN1 H a n H1 H2)). Qed.

  (* [comment removed for export] *)
  Definition CONSTS_CV : list (Z * nat * RS.cval) := [
   (0xff250, 8%nat, RS.CZ 0x197020);
   (0xff260, 8%nat, RS.CZ 0x1990a8);
   (0xff268, 8%nat, RS.CZ 0x104d78);
   (0xff270, 8%nat, RS.CZ 0x107578);
   (0xff278, 8%nat, RS.CZ 0x108268);
   (0xff280, 8%nat, RS.CZ 0x108270);
   (0xff288, 8%nat, RS.CZ 0x108260);
   (0xff290, 8%nat, RS.CZ 0x1011b0);
   (0xffdd8, 8%nat, RS.CZ 0x108259);
   (0xffec8, 8%nat, RS.CZ 0x10);
   (0x10490, 8%nat, RS.CZ 0x218a392cd3d5dbf);
   (0x10504, 1%nat, RS.CZ 0x3);
   (0x10608, 1%nat, RS.CZ 0x4);
   (0x10631, 1%nat, RS.CZ 0xb);
   (0x103b8, 8%nat, RS.CZ 0xcc6e96b9cc6e96b9);
   (0x10408, 8%nat, RS.CZ 0x101010101010100);
   (0x103e8, 8%nat, RS.CZ 0x8080808080808080);
   (0x101030, 8%nat, RS.CZ 0xf5930);
   (0x1011a8, 8%nat, RS.CZ 0xf52e0);
   (0x1011b0, 8%nat, RS.CZ 0xf56e4);
   (0x103f18, 8%nat, RS.CE RS.e_P6);
   (0x103f20, 8%nat, RS.CZ 0x2000011000);
   (0x103f38, 8%nat, RS.CE RS.e_SPB);
   (0x103f40, 4%nat, RS.CZ 0xffffffff);
   (0x103f48, 8%nat, RS.CE RS.e_RI);
   (0x103f50, 1%nat, RS.CZ 0x0);
   (0x103f58, 8%nat, RS.CZ 0x1000);
   (0x103f60, 8%nat, RS.CE (RS.vpg RS.V_G8));
   (0x103f68, 8%nat, RS.CE (RS.vpg RS.V_G8));
   (0x103f70, 8%nat, RS.CZ 0x800000);
   (0x104230, 8%nat, RS.CZ 0x10000000);
   (0x104238, 8%nat, RS.CZ 0xe666661);
   (0x104240, 8%nat, RS.CZ 0x100000);
   (0x104d38, 8%nat, RS.CZ 0x10000000000);
   (0x104d40, 2%nat, RS.CZ 0x10);
   (0x104d42, 2%nat, RS.CZ 0x800);
   (0x104d44, 1%nat, RS.CZ 0x1);
   (0x104d84, 4%nat, RS.CZ 0x10);
   (0x104d88, 4%nat, RS.CZ 0x800);
   (0x104da4, 4%nat, RS.CZ 0x1000);
   (0x104da8, 4%nat, RS.CZ 0x0);
   (0x104dac, 1%nat, RS.CZ 0xbe);
   (0x104dac, 4%nat, RS.CZ 0xbe);
   (0x104dcd, 1%nat, RS.CZ 0x1);
   (0x104db0, 4%nat, RS.CZ 0x55);
   (0x104db4, 1%nat, RS.CZ 0x1);
   (0x104dd8, 1%nat, RS.CZ 0x1);
   (0x106ddc, 1%nat, RS.CZ 0x1);
   (0x106de0, 1%nat, RS.CZ 0x1);
   (0x106de4, 4%nat, RS.CZ 0x0);
   (0x108258, 1%nat, RS.CZ 0x1);
   (0x108259, 1%nat, RS.CZ 0x1);
   (0x108260, 8%nat, RS.CZ 0x7fffffffffff);
   (0x108268, 8%nat, RS.CZ 0x0);
   (0x108270, 8%nat, RS.CZ 0x0);
   (0x10827c, 4%nat, RS.CZ 0x1e);
   (0x1897e1, 1%nat, RS.CZ 0x1);
   (0x1897e2, 1%nat, RS.CZ 0x0);
   (0x197020, 8%nat, RS.CZ 0x1000);
   (0x199040, 8%nat, RS.CZ 0x0);
   (0x199048, 8%nat, RS.CZ 0x0);
   (0x1990ca, 1%nat, RS.CZ 0x1);
   (0x199120, 8%nat, RS.CZ 0xffffffffffffffff);
   (0x1991a3, 1%nat, RS.CZ 0x1);
   (0x63a6e8, 8%nat, RS.CZ 0x65bae8);
   (0x65bae8, 8%nat, RS.CE (RS.vpg RS.V_G10));
   (0x63a750, 4%nat, RS.CZ 0x0);
   (0xff2c0, 8%nat, RS.CZ 0x197018);
   (0x197018, 4%nat, RS.CZ 0x0);
   (0x10310, 8%nat, RS.CZ 0xc6a4a7935bd1e995);
   (0x10350, 8%nat, RS.CZ 0x35253c9ade8f4ca8);
   (0x10450, 8%nat, RS.CZ 0x9747b28c9747b28c);
   (0x107578, 8%nat, RS.CZ 0x7fff8000);
   (0x107580, 4%nat, RS.CZ 0x1);
   (0xff2b0, 8%nat, RS.CZ 0x1);
   (0xff2b8, 8%nat, RS.CZ 0x19909c);
   (0x19909c, 4%nat, RS.CZ 0x0);
   (0x199138, 8%nat, RS.CZ 0x0);
   (0xfffb8, 8%nat, RS.CZ 0x65a780);
   (0x33518, 2%nat, RS.CZ 0xff04);
   (0x334b4, 4%nat, RS.CZ 0xb3134);
   (0x65aa00, 8%nat, RS.CZ 0x1000);
   (0x10470, 8%nat, RS.CZ 0xafffff00000fffff);
   (0x100010, 8%nat, RS.CZ 0x1);
   (0x100018, 8%nat, RS.CZ 0xfffffffffffff800);
   (0x100020, 8%nat, RS.CZ 0x8);
   (0x1010d0, 8%nat, RS.CZ 0xf5fbc);
   (0x199131, 1%nat, RS.CZ 0x1);
   (0x1991ac, 1%nat, RS.CZ 0x0);
   (0xff258, 8%nat, RS.CZ 0x1011e8);
   (0x1011e8, 8%nat, RS.CZ 0x1a2c0);
   (0x104e30, 8%nat, RS.CZ 0x0);
   (0x199198, 4%nat, RS.CZ 0x0);
   (0x1e23c, 8%nat, RS.CZ 0x612079726f6d656d);
   (0x1e244, 8%nat, RS.CZ 0x7365726464612074);
   (0x1e24c, 4%nat, RS.CZ 0x70252073);
   (0x1e250, 1%nat, RS.CZ 0x0);
   (0x22760, 4%nat, RS.CZ 0x60940);
   (0x104b0, 8%nat, RS.CZ 0xaaaaaaaaaaaaaaaa);
   (0x63a738, 8%nat, RS.CZ 0x63a760);
   (0x63a768, 8%nat, RS.CZ 0x63af40)
  ].
  Lemma CONSTS_CV_den :
    map (fun c => (fst (fst c), snd (fst c), RS.cval_den E (snd c))) CONSTS_CV
    = asan_consts (4096 * uv 227) (SPB hv) (4096 * uv 246) (4096 * uv 248).
  Proof.
    pose proof R227 as X227. pose proof R229 as X229. pose proof R246 as X246. pose proof R248 as X248.
    unfold CONSTS_CV, asan_consts. cbn [map fst snd RS.cval_den].
    unfold RS.e_P6, RS.e_RI. change (u (edenot E RS.e_SPB)) with (APS.uE E RS.e_SPB). rewrite u_spb.
    unfold RS.vpg, RS.V_G6, RS.V_W6, RS.V_G8, RS.V_G10.
    rewrite (u_page 227), (u_page 246), (u_page 248) by lia.
    assert (ERI : u (edenot E (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 227)) (EMd Instr.M_MUL (ELit 4096) (EVar 229))) (ELit 137438953472)))
                  = SPB hv + 2 ^ 37).
    { pose proof u_spb as US. unfold APS.uE, RS.e_SPB, RS.vpg, RS.V_G6, RS.V_W6 in US. cbn [edenot] in US.
      cbn [edenot]. rewrite u_add64. rewrite US. rewrite u64_lit by lia. unfold SPB. cbn [b_g6 b_w6 hv]. rewrite Z.mod_small by lia. reflexivity. }
    rewrite ERI. reflexivity.
  Qed.
  Lemma CONSTS : forallb (RS.const_x (kn HS_2)) CONSTS_CV = true ->
    cells_hold ASEGS FULL (asan_consts (4096 * uv 227) (SPB hv) (4096 * uv 246) (4096 * uv 248)).
  Proof.
    intros H. unfold cells_hold. rewrite <- CONSTS_CV_den. pose proof (RS.consts_x_sound E Mr (kn HS_2) CONSTS_CV KN1 H) as F.
    rewrite Forall_forall in F |- *. intros c Hc. exact (cellN_full _ _ _ (F c Hc)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cellZ_at : forall a a' n v v', cellZ ASEGS FULL a n v -> a = a' -> v = v' -> cellZ ASEGS FULL a' n v'.
  Proof. intros a a' n v v' C -> ->. exact C. Qed.
  Lemma fillZ_at : forall lo lo' hi hi' b, fillZ ASEGS FULL lo hi b -> lo = lo' -> hi = hi' -> fillZ ASEGS FULL lo' hi' b.
  Proof. intros lo lo' hi hi' b C -> ->. exact C. Qed.
  Lemma writableZ_at : forall lo lo' hi hi', writableZ ASEGS FULL lo hi -> lo = lo' -> hi = hi' -> writableZ ASEGS FULL lo' hi'.
  Proof. intros lo lo' hi hi' C -> ->. exact C. Qed.
  Lemma R0 : 4294901760 <= uv 0 <= 4294967295. Proof. exact (rng _ _ _ K2.rng_v0). Qed.
  Lemma R10 : 0 <= uv 10 <= 8. Proof. exact (rng _ _ _ K2.rng_v10). Qed.
  Lemma TOPv : u (edenot E e_ttop) = 32768 * uv 0 + 4096 * uv 10.
  Proof.
    pose proof R0 as X0. pose proof R10 as X10. unfold e_ttop. cbn [edenot]. rewrite u_add64, !u_mul64, !u64_lit by lia.
    change (u (ev E 0)) with (uv 0). change (u (ev E 10)) with (uv 10).
    rewrite (Z.mod_small (32768 * uv 0)) by lia. rewrite (Z.mod_small (4096 * uv 10)) by lia. apply Z.mod_small. lia.
  Qed.
  Lemma BOTv : u (edenot E RS.e_BOT) = u (edenot E e_ttop) - 0x800000.
  Proof.
    pose proof R0 as X0. pose proof R10 as X10. unfold RS.e_BOT. cbn [edenot]. rewrite u_add64, u_lit64a.
    change (edenot E RS.e_TOP) with (edenot E e_ttop). rewrite TOPv.
    replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
    symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia].
  Qed.
  Definition B1 : Z := 748199.   (* [comment removed for export] *)

  Ltac chk := vm_compute; reflexivity.
  Theorem main_facts_2 : main_facts (asan_bt hv) FULL model.
  Proof.
    pose proof R227 as X227. pose proof R229 as X229. pose proof R246 as X246. pose proof R247 as X247. pose proof R248 as X248.
    pose proof R397 as X397. pose proof R517 as X517. pose proof R518 as X518. pose proof R0 as X0. pose proof R10 as X10.
    unfold main_facts. cbn zeta.
    change (bt_segs (asan_bt hv)) with ASEGS. change (bt_consts (asan_bt hv)) with (asan_consts (4096 * uv 227) (SPB hv) (4096 * uv 246) (4096 * uv 248)).
    change (IB (asan_bt hv)) with 1064728. change (bt_thread (asan_bt hv)) with (4096 * uv 247). change (bt_tctx (asan_bt hv)) with (4096 * uv 248).
    change (bt_stack_top (asan_bt hv)) with (u (edenot E e_ttop)). change (bt_stack_bottom (asan_bt hv)) with (u (edenot E e_ttop) - 0x800000).
    change (bt_fs (asan_bt hv)) with (4096 * uv 397). change (bt_spacebeg (asan_bt hv)) with (SPB hv).
    change (DEPOT_TAB (asan_bt hv)) with 2004056. change (DEPOT_NIDS (asan_bt hv)) with (2004056 + 0x400000). change (DEPOT_MAP1 (asan_bt hv)) with (2004056 + 0x400010).
    change (bt_nodes0 (asan_bt hv)) with (4096 * uv 517). change (bt_store0 (asan_bt hv)) with (4096 * uv 518). change (SSOBJ (asan_bt hv)) with 1938504.
    change (bt_tls_fs (asan_bt hv)) with 6530880. change (IA_FLAG (asan_bt hv)) with 1667080. change (IA_INST (asan_bt hv)) with 1083264.
    change (bt_dep0 (asan_bt hv)) with (asan_dep0 hv). change (bt_resv6 (asan_bt hv)) with (4096 * uv 227). change (bt_resv6_len (asan_bt hv)) with 0x2000011000.
    change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)). change (bt_noacc0 (asan_bt hv)) with (vm_noaccess h). change (bt_lazy0 (asan_bt hv)) with (m_vm_lazy model).
    change (bt_ia (asan_bt hv)) with asan_addrs. change (bt_reserved (asan_bt hv)) with (vm_reserved h). change (bt_brk (asan_bt hv)) with (vm_brk h).
    change (bt_start_brk (asan_bt hv)) with (vm_start_brk h). change (bt_mmap_base (asan_bt hv)) with (vm_mmap_base h). change (bt_init_sp (asan_bt hv)) with (vm_init_sp h).
    change (bt_aa0 (asan_bt hv)) with aa0.
    (* [comment removed for export] *)
    split; [exact (CONSTS ltac:(chk))|].
    (* [comment removed for export] *)
    split; [exact (CZ0 (1064728 + 112) 8 0 ltac:(lia) ltac:(chk))|]. split; [exact (CZ0 (1064728 + 120) 8 0 ltac:(lia) ltac:(chk))|].
    split; [exact (CZ0 (1064728 + 680) 1 0 ltac:(lia) ltac:(chk))|]. split; [exact (CZ0 (1064728 + 880) 1 0 ltac:(lia) ltac:(chk))|].
    split; [exact (CZ0 (1064728 + 881) 1 0 ltac:(lia) ltac:(chk))|].
    split; [exact (CZ0 (1064728 + 984) 1 0 ltac:(lia) ltac:(chk))|]. split; [exact (ZF0 (1064728 + 888) (1064728 + 920) ltac:(chk))|].
    (* [comment removed for export] *)
    split. { eapply cellZ_at; [exact (CEP 247 0 8 (RS.vpg 248) ltac:(lia) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 248) by lia; reflexivity]. }
    split. { exact (CEP 247 8 8 RS.e_TOP ltac:(lia) ltac:(lia) ltac:(chk)). }
    split. { eapply cellZ_at; [exact (CEP 247 16 8 RS.e_BOT ltac:(lia) ltac:(lia) ltac:(chk)) | lia | exact BOTv]. }
    split; [exact (CZP 247 40 1 0 ltac:(lia) ltac:(lia) ltac:(chk))|].
    split. { eapply cellZ_at; [exact (CEP 247 72 8 (RS.vpg 397) ltac:(lia) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 397) by lia; reflexivity]. }
    split; [exact (ZFP 247 80 3169 ltac:(lia) ltac:(chk))|].
    split. { eapply writableZ_at; [exact (WWP 247 0 4096 ltac:(lia) ltac:(lia) ltac:(chk)) | lia | unfold PG; lia]. }
    split. { eapply cellZ_at; [exact (CEP 248 152 8 (RS.vpg 247) ltac:(lia) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 247) by lia; reflexivity]. }
    split; [exact (CZP 248 8 4 0 ltac:(lia) ltac:(lia) ltac:(chk))|].
    (* [comment removed for export] *)
    split. { eapply fillZ_at; [exact (ZFS (2 ^ 37) (2 ^ 37 + 4096) ltac:(chk)) | unfold KSPACE; lia | unfold KSPACE, PG; lia]. }
    split. { eapply writableZ_at; [exact (WWS (2 ^ 37) (2 ^ 37 + 4096) ltac:(lia) ltac:(chk)) | unfold KSPACE; lia | unfold KSPACE, PG; lia]. }
    (* [comment removed for export] *)
    split. { intros i Hi. cbn [dp_tab asan_dep0 b_hash hv]. change (17355219521686432423 mod 2 ^ 20) with B1.
             destruct (Z.eqb_spec i B1) as [-> | NE]; [exact (CZ0 (2004056 + 4 * B1) 4 1 ltac:(lia) ltac:(chk))|].
             destruct (Z.lt_ge_cases i B1) as [LT | GE].
             - exact (KI 2004056 (2004056 + 4 * B1) ltac:(chk) (2004056 + 4 * i) 4%nat ltac:(lia) ltac:(unfold B1 in *; cbn [Z.of_nat]; lia)).
             - exact (KI (2004056 + 4 * B1 + 4) (2004056 + 4 * 2 ^ 20) ltac:(chk) (2004056 + 4 * i) 4%nat ltac:(unfold B1 in *; lia) ltac:(cbn [Z.of_nat]; lia)). }
    split; [exact (CZ0 (2004056 + 0x400000) 4 1 ltac:(lia) ltac:(chk))|]. split; [exact (CZ0 (2004056 + 0x400000 + 8) 1 0 ltac:(lia) ltac:(chk))|].
    split. { eapply cellZ_at; [exact (CE0 (2004056 + 0x400010) 8 (RS.vpg 517) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 517) by lia; reflexivity]. }
    split. { intros i Hi. exact (KI (2004056 + 0x400018) (2004056 + 0x400010 + 8 * 2 ^ 15) ltac:(chk) (2004056 + 0x400010 + 8 * i) 8%nat ltac:(lia) ltac:(cbn [Z.of_nat]; lia)). }
    split. { cbn [dp_hash asan_dep0 b_hash hv Z.eqb Pos.eqb]. exact (CZP 517 16 8 17355219521686432423 ltac:(lia) ltac:(lia) ltac:(chk)). }
    split. { cbn [dp_link asan_dep0]. exact (CZP 517 24 4 0 ltac:(lia) ltac:(lia) ltac:(chk)). }
    split. { cbn [dp_store asan_dep0 Z.eqb Pos.eqb]. exact (CZP 517 28 4 1 ltac:(lia) ltac:(lia) ltac:(chk)). }
    split. { eapply writableZ_at; [exact (WWP 517 0 (2 ^ 20) ltac:(lia) ltac:(lia) ltac:(chk)) | lia | lia]. }
    split. { cbn [dp_frames asan_dep0 b_sz hv]. exact (CZ0 1938504 8 2 ltac:(lia) ltac:(chk)). }
    split. { eapply cellZ_at; [exact (CE0 (1938504 + 16) 8 (RS.vpg 518) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 518) by lia; reflexivity]. }
    split. { cbn [dp_stored asan_dep0 b_sz hv Z.eqb]. exact (CZ0 (1938504 + 24) 4 2 ltac:(lia) ltac:(chk)). }
    split; [exact (CZ0 (1938504 + 28) 1 0 ltac:(lia) ltac:(chk))|].
    split. { intros i Hi. pose proof (KI (1938504 + 32) (1938504 + 16 + 16 * 2 ^ 12) ltac:(chk)) as K.
             split; [exact (K (1938504 + 16 + 16 * i) 8%nat ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
             split; [exact (K (1938504 + 24 + 16 * i) 4%nat ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
             exact (K (1938504 + 28 + 16 * i) 1%nat ltac:(lia) ltac:(cbn [Z.of_nat]; lia)). }
    split. { eapply writableZ_at; [exact (WWP 518 0 (2 ^ 23) ltac:(lia) ltac:(lia) ltac:(chk)) | lia | lia]. }
    (* [comment removed for export] *)
    split. { eapply fillZ_at; [exact (ZFP 397 0 88 ltac:(lia) ltac:(chk)) | lia | lia]. }
    split. { unfold FSLOG. exact (CZP 397 88 8 20 ltac:(lia) ltac:(lia) ltac:(chk)). }
    split. { eapply fillZ_at; [exact (ZFP 397 96 11571200 ltac:(lia) ltac:(chk)) | lia | unfold FAKE_SIZE; lia]. }
    split. { eapply writableZ_at; [exact (WWP 397 0 11571200 ltac:(lia) ltac:(lia) ltac:(chk)) | lia | unfold FAKE_SIZE; lia]. }
    split. { eapply cellZ_at; [exact (CE0 6530880 8 (RS.vpg 397) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 397) by lia; reflexivity]. }
    (* [comment removed for export] *)
    split; [exact (CZ0 1667080 1 0 ltac:(lia) ltac:(chk))|]. split; [exact (CZ0 (1667080 + 1) 1 0 ltac:(lia) ltac:(chk))|].
    split; [exact (ZF0 (1083264 + 8) (1083264 + 8 + 0x40000) ltac:(chk))|].
    (* [comment removed for export] *)
    split; [exact L_perm|]. split; [intros a; apply iff_refl|]. split; [intros a; apply iff_refl|]. split; [exact L_lazywf|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HCEIL|]. split; [exact L_limit|].
    split; [exact (APS.co_napos _ _ _ _ _ _ _ _ _ _ _ _ CS)|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    split; [exact B_minv|]. split; [exact B_kbase|].
    (* [comment removed for export] *)
    split; [exact (CZ0 1078648 8 2147450880 ltac:(lia) ltac:(chk))|]. split; [exact (CZ0 1078656 4 1 ltac:(lia) ltac:(chk))|].
    (* [comment removed for export] *)
    split; [exact SH_def|].
    (* [comment removed for export] *)
    split; [exact (APS.co_wf _ _ _ _ _ _ _ _ _ _ _ _ CS)|].
    (* [comment removed for export] *)
    pose proof R330 as X330.
    change (bt_tp (asan_bt hv)) with 6530880. change (bt_dtls (asan_bt hv)) with (4096 * uv 330). change (bt_tls_fs (asan_bt hv)) with 6530880.
    split; [exact (CZP 247 48 8 (6530880 + 0x738) ltac:(lia) ltac:(lia) ltac:(chk))|].
    split; [exact (CZP 247 56 8 (6530880 + 0x814) ltac:(lia) ltac:(lia) ltac:(chk))|].
    split. { eapply cellZ_at; [exact (CE0 (6530880 + 8) 8 (RS.vpg 330) ltac:(lia) ltac:(chk)) | lia | unfold RS.vpg; rewrite (u_page 330) by lia; reflexivity]. }
    exact (CZP 330 24 8 6530880 ltac:(lia) ltac:(lia) ltac:(chk)).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma In_remove1 : forall x l y, In y l -> y <> x -> In y (remove1 x l).
  Proof.
    intros x l. induction l as [|z t IH]; intros y Hy NE; [destruct Hy|]. cbn [remove1].
    destruct (wpair_eqb x z) eqn:EQ.
    - apply wpair_eqb_eq in EQ. subst z. destruct Hy as [-> | Hy]; [exfalso; exact (NE eq_refl) | exact Hy].
    - destruct Hy as [-> | Hy]; [left; reflexivity | right; exact (IH y Hy NE)].
  Qed.
  Theorem shpage_boot_main : forall pb n, 0 < n ->
    (AsVocab.AS_LO <= pb /\ pb + n <= AsVocab.AS_GAPLO) \/ (AsVocab.AS_GAPHI <= pb /\ pb + n <= AsVocab.AS_HEAPLO) ->
    AsKSys10.AsKSys5.shpage_boot (asan_bt hv) pb n.
  Proof.
    intros pb n Hn Hr. pose proof R227 as X227.
    pose proof (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ CS) as KD. rewrite Forall_forall in KD.
    unfold AsKSys10.AsKSys5.shpage_boot. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)). change (bt_lazy0 (asan_bt hv)) with (m_vm_lazy model).
    change (bt_noacc0 (asan_bt hv)) with (vm_noaccess h). change (bt_reserved (asan_bt hv)) with (vm_reserved h).
    assert (GO : forall m lo len, In m (a_maps HS_2) -> am_kind m = KRWLAZY -> APS.amap_den E m = (Z_to_bv 64 lo, Z_to_bv 64 len) ->
                 0 <= lo -> lo + len < 2 ^ 64 -> lo <= pb -> pb + n <= lo + len ->
                 (exists b m0 : word, In (b, m0) (remove1 (w6, n6) (vm_maps h)) /\ u b <= pb /\ pb + n <= u b + u m0)
                 /\ (forall a, pb <= a < pb + n -> pg_in_ivz (m_vm_lazy model) a /\ ~ in_ivz (vm_noaccess h) a)).
    { intros m lo len Hm Hk Hd Hlo Hhi H1 H2.
      pose proof (f_equal fst Hd) as Hb. pose proof (f_equal snd Hd) as Hn'. unfold APS.amap_den in Hb, Hn'. cbn [fst snd] in Hb, Hn'.
      split.
      - exists (Z_to_bv 64 lo), (Z_to_bv 64 len). split; [| rewrite !u64_lit by lia; lia].
        apply In_remove1; [| intros EE; pose proof (f_equal (fun p => u (fst p)) EE) as E1; cbn [fst] in E1; unfold w6 in E1; rewrite !u64_lit in E1 by lia; unfold AsVocab.AS_LO, AsVocab.AS_GAPLO, AsVocab.AS_GAPHI, AsVocab.AS_HEAPLO in Hr; lia].
        pose proof (In_maps m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as X. rewrite Hd in X. exact X.
      - intros a Ha. destruct (KD m Hm Hk (Z_to_bv 64 a)) as [NA LZ]; [rewrite Hb, Hn'; rewrite !u64_lit by lia; lia|].
        split; [split; [lia | exact LZ]|]. intros (b & m0 & Hin & Hbm). rewrite u64_lit in NA by lia.
        assert (T : APS.in_ivs a (vm_noaccess h) = true) by (apply APS.in_ivs_true; exists (b, m0); exact (conj Hin Hbm)).
        rewrite T in NA. discriminate NA. }
    assert (MAIN : (exists b m0 : word, In (b, m0) (remove1 (w6, n6) (vm_maps h)) /\ u b <= pb /\ pb + n <= u b + u m0)
                   /\ (forall a, pb <= a < pb + n -> pg_in_ivz (m_vm_lazy model) a /\ ~ in_ivz (vm_noaccess h) a)).
    { unfold AsVocab.AS_LO, AsVocab.AS_GAPLO, AsVocab.AS_GAPHI, AsVocab.AS_HEAPLO in Hr. destruct Hr as [[H1 H2] | [H1 H2]].
      - apply (GO am_losh 2147446784 268435456); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia | lia].
      - apply (GO am_hish 2201439137792 15392894357504); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia | lia]. }
    destruct MAIN as [M1 M2]. split; [exact M1|]. split; [exact M2|].
    rewrite (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ CS).
    assert (RS : forallb (fun iv : word * word => u (fst iv) + u (snd iv) <=? AsVocab.AS_LO) (segments_reserved ASEGS) = true) by (vm_compute; reflexivity).
    intros iv Hin. apply Z.leb_le. exact (proj1 (forallb_forall _ _) RS iv Hin).
  Qed.

  (* [comment removed for export] *)
  Theorem boot_low_main : AsKSys7b.res_low (asan_bt hv) /\ AsKSys8.noacc0_sub (asan_bt hv).
  Proof.
    split.
    - unfold AsKSys7b.res_low. change (bt_reserved (asan_bt hv)) with (vm_reserved h). rewrite (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ CS).
      assert (RS : forallb (fun iv : word * word => u (fst iv) + u (snd iv) <=? AsVocab.AS_LO) (segments_reserved ASEGS) = true) by (vm_compute; reflexivity).
      intros iv Hin. apply Z.leb_le. exact (proj1 (forallb_forall _ _) RS iv Hin).
    - unfold AsKSys8.noacc0_sub. change (bt_noacc0 (asan_bt hv)) with (vm_noaccess h). change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)).
      intros a (b & m & Hin & Hr).
      assert (T : APS.in_ivs a (vm_noaccess h) = true) by (apply APS.in_ivs_true; exists (b, m); exact (conj Hin Hr)).
      pose proof (APS.co_nasub _ _ _ _ _ _ _ _ _ _ _ _ CS a T) as T2. apply APS.in_ivs_true in T2. destruct T2 as ([b2 m2] & Hin2 & Hr2). cbn [fst snd] in Hr2.
      destruct (wpair_eqb (w6, n6) (b2, m2)) eqn:EQ.
      + apply wpair_eqb_eq in EQ. injection EQ as <- <-. left. pose proof R227. unfold in_resv6, w6, n6 in *. rewrite !u64_lit in Hr2 by lia.
        cbn [bt_resv6 bt_resv6_len asan_bt hv b_g6]. exact Hr2.
      + right. exists b2, m2. split; [| exact Hr2]. apply In_remove1; [exact Hin2|]. intros EE. rewrite EE in EQ.
        assert (X : wpair_eqb (w6, n6) (w6, n6) = true) by (apply wpair_eqb_eq; reflexivity). rewrite X in EQ. discriminate EQ.
  Qed.

  (* [comment removed for export] *)
  Lemma in_maps0_grant : forall g n a, gfacts g n -> n <> 0x2000011000 -> 0 <= g -> g + n < 2 ^ 64 -> g <= a < g + n ->
    in_ivz (remove1 (w6, n6) (vm_maps h)) a.
  Proof.
    intros g n a (I0 & P0 & _) NE G0 G1 Ha. exists (Z_to_bv 64 g), (Z_to_bv 64 n). split; [| rewrite !u64_lit by lia; exact Ha].
    apply In_remove1; [exact I0|]. intros EE. pose proof (f_equal (fun p : word * word => u (snd p)) EE) as E1. cbn [snd] in E1.
    unfold n6 in E1. rewrite !u64_lit in E1 by lia. exact (NE E1).
  Qed.
  Lemma in_maps0_lit : forall m lo len a, In m (a_maps HS_2) -> is_fog m = false -> APS.amap_den E m = (Z_to_bv 64 lo, Z_to_bv 64 len) ->
    len <> 0x2000011000 -> 0 <= lo -> 0 < len -> lo + len < 2 ^ 64 -> lo <= a < lo + len -> in_ivz (remove1 (w6, n6) (vm_maps h)) a.
  Proof.
    intros m lo len a Hm Hf Hd NE L0 L1 L2 Ha. exists (Z_to_bv 64 lo), (Z_to_bv 64 len). split; [| rewrite !u64_lit by lia; exact Ha].
    apply In_remove1; [pose proof (In_maps m Hm Hf) as X; rewrite Hd in X; exact X|].
    intros EE. pose proof (f_equal (fun p : word * word => u (snd p)) EE) as E1. cbn [snd] in E1. unfold n6 in E1. rewrite !u64_lit in E1 by lia. exact (NE E1).
  Qed.
  Definition am_gap : amap := AM (ELit 2415882240) (ELit 2199023255552) KNONELAZY.

  Theorem boot_geom_main : AsKSys10.AsKSys9.boot_geom (asan_bt hv).
  Proof.
    destruct boot_low_main as [RL NS]. split; [exact RL|]. split; [exact NS|]. pose proof ceil_rng as CR.
    split; [| split].
    - (* [comment removed for export] *) unfold AsKSys10.AsKSys9.fixed_cov. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)).
      intros lo hi a Hin NE Ha. cbn [bt_fixed asan_bt asan_fixed hv b_g6 b_g8 b_g16 b_g9 b_g21 b_g22 b_g10 b_g12] in Hin.
      cbn [bt_resv6 bt_resv6_len asan_bt hv b_g6] in NE.
      destruct Hin as [E0 | [E0 | [E0 | [E0 | [E0 | [E0 | [E0 | [E0 | []]]]]]]]]; injection E0 as <- <-.
      + exfalso. apply NE. reflexivity.
      + pose proof G246 as GF. apply (in_maps0_grant _ _ a GF); [lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G397 as GF. apply (in_maps0_grant _ _ a GF); [unfold FAKE_SIZE; lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G247 as GF. apply (in_maps0_grant _ _ a GF); [unfold PG; lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G517 as GF. apply (in_maps0_grant _ _ a GF); [lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G518 as GF. apply (in_maps0_grant _ _ a GF); [lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G248 as GF. apply (in_maps0_grant _ _ a GF); [lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
      + pose proof G330 as GF. apply (in_maps0_grant _ _ a GF); [unfold PG; lia | destruct GF as (_ & _ & X & Y & _); lia | destruct GF as (_ & _ & X & Y & _); lia | exact Ha].
    - (* [comment removed for export] *) unfold AsKSys10.AsKSys9.band_cov. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)).
      intros a Ha. unfold in_band, AS_LO, AS_HEAPLO in Ha.
      destruct (Z_lt_ge_dec a 2415882240) as [LO | X1]; [| destruct (Z_lt_ge_dec a 2201439137792) as [GAP | HI]].
      + apply (in_maps0_lit am_losh 2147446784 268435456 a); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia | lia | lia].
      + apply (in_maps0_lit am_gap 2415882240 2199023255552 a); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia | lia | lia].
      + apply (in_maps0_lit am_hish 2201439137792 15392894357504 a); [vm_compute; tauto | reflexivity | reflexivity | lia | lia | lia | lia | lia].
    - (* [comment removed for export] *) unfold AsKSys10.AsKSys9.res_hull. change (bt_reserved (asan_bt hv)) with (vm_reserved h). rewrite (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ CS).
      intros a n Hn H64 Hrf. cbn [bt_ia asan_bt ia_img_lo ia_img_hi asan_addrs].
      destruct (Z_le_gt_dec (u a + u n) 0x10000) as [L|G1]; [left; exact L|]. destruct (Z_le_gt_dec 0x65d000 (u a)) as [R'|G2]; [right; exact R'|]. exfalso.
      set (z := Z.max (u a) 0x10000).
      assert (Hz1 : img_lo AT_A <= z < img_hi AT_A) by (cbn [img_lo img_hi AT_A]; unfold z; lia).
      pose proof (asan_S_res_tile z Hz1) as Hin.
      apply APS.in_ivs_true in Hin. destruct Hin as ([b m] & Hbm & Hr). cbn [fst snd] in Hr.
      pose proof (RefNodes.region_free_In _ a n b m Hrf Hbm) as AP. unfold z in Hr. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem shadow_boot_main : AsKSys10.AsKSys5q.shadow_boot (asan_bt hv).
  Proof. intros pb n Hn Hr. exact (shpage_boot_main pb n Hn Hr). Qed.
  Theorem ptr8_entry_main : AsKSys10.AsAinvBootF3.ptr8_entry (asan_bt hv).
  Proof.
    unfold AsKSys10.AsAinvBootF3.ptr8_entry. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)).
    cbn [bt_ptrarr asan_bt hv b_g8]. pose proof G246 as (I0 & _).
    apply In_remove1; [exact I0|]. intros EE. pose proof (f_equal (fun p : word * word => u (snd p)) EE) as E1. cbn [snd] in E1.
    unfold n6 in E1. rewrite !u64_lit in E1 by lia. lia.
  Qed.
  Theorem res_in_hull_main : AsKSys10.AsAinvBootF3.res_in_hull (asan_bt hv).
  Proof.
    unfold AsKSys10.AsAinvBootF3.res_in_hull. change (bt_reserved (asan_bt hv)) with (vm_reserved h). rewrite (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ CS).
    cbn [bt_ia asan_bt ia_img_lo ia_img_hi asan_addrs].
    assert (RS : forallb (fun iv : word * word => (0x10000 <=? u (fst iv)) && (u (fst iv) + u (snd iv) <=? 0x65d000)) (segments_reserved ASEGS) = true) by (vm_compute; reflexivity).
    intros iv Hin. pose proof (proj1 (forallb_forall _ _) RS iv Hin) as X. apply andb_true_iff in X. destruct X as [X1 X2].
    apply Z.leb_le in X1. apply Z.leb_le in X2. split; assumption.
  Qed.
  Lemma seps_remove1_seps : forall l x, APS.seps l -> APS.seps (remove1 x l).
  Proof.
    induction l as [|z t IH]; intros x HS; [constructor|]. inversion HS as [| z' t' Hf Ht]; subst. cbn [remove1].
    destruct (wpair_eqb x z); [exact Ht|]. constructor; [| exact (IH x Ht)].
    rewrite Forall_forall in Hf |- *. intros y Hy. exact (Hf y (remove1_In _ _ _ Hy)).
  Qed.
  Lemma seps_split : forall l1 x l2 y, APS.seps (l1 ++ x :: l2) -> In y (l1 ++ l2) -> APS.iv_disjoint x y \/ APS.iv_disjoint y x.
  Proof.
    induction l1 as [|z t IH]; intros x l2 y HS Hy; cbn [app] in *; inversion HS as [| z' t' Hf Ht]; subst.
    - left. rewrite Forall_forall in Hf. exact (Hf y Hy).
    - destruct Hy as [<- | Hy]; [right; rewrite Forall_forall in Hf; apply Hf; apply in_or_app; right; left; reflexivity | exact (IH x l2 y Ht Hy)].
  Qed.
  Theorem ptr8_sep_main : AsKSys10.AsAinvBootF3.ptr8_sep (asan_bt hv).
  Proof.
    unfold AsKSys10.AsAinvBootF3.ptr8_sep. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)). cbn [bt_ptrarr asan_bt hv b_g8].
    intros l1 l2 y EQ Hy. pose proof R246 as X246.
    pose proof (seps_remove1_seps (vm_maps h) (w6, n6) (APS.co_seps _ _ _ _ _ _ _ _ _ _ _ _ CS)) as SS. rewrite EQ in SS.
    destruct (seps_split l1 _ l2 y SS Hy) as [D | D]; unfold APS.iv_disjoint in D; cbn [fst snd] in D; rewrite !u64_lit in D by lia; lia.
  Qed.
  Theorem stack_geom_main : AsKSys10.AsAinvBootF3.stack_geom (asan_bt hv).
  Proof.
    pose proof main_vars_ok as VO. unfold vars_ok in VO. do 22 (apply proj2 in VO). apply proj1 in VO.
    unfold AsKSys10.AsAinvBootF3.stack_geom. cbn [bt_tctx bt_thread bt_stack_top bt_stack_bottom asan_bt hv b_g9 b_g10 b_top] in *.
    pose proof R0 as X0. pose proof R10 as X10. rewrite TOPv. unfold apart, PG in *. cbn [b_g9 b_g10 hv] in VO. lia.
  Qed.
  Theorem boot_facts_main_2 : AsKSys10.AsAinvBootF3.boot_facts (asan_bt hv).
  Proof. split; [exact (asan_boot_ok hv main_vars_ok) | split; [exact boot_geom_main | split; [exact shadow_boot_main | split; [exact ptr8_entry_main | split; [exact res_in_hull_main | split; [exact stack_geom_main | exact ptr8_sep_main]]]]]]. Qed.

  (* [comment removed for export] *)
  Theorem AAINV_DR_at_main_2 : AsAllocFFam.AsAinvDrvHist3.AAINV_DR (asan_bt hv) [] [] 0 0 0 FULL model.
  Proof. exact (AsAllocFFam.AsAinvDrvHist3.AAINV_DR_main (asan_bt hv) FULL model (asan_boot_ok hv main_vars_ok) main_facts_2). Qed.
  (* [comment removed for export] *)
  Lemma sum_sizes_gw : forall l, APS.sum_sizes l = BackingAlgebra.AsanPlacement.gw_sizes l.
  Proof. induction l as [|x t IH]; cbn [APS.sum_sizes BackingAlgebra.AsanPlacement.gw_sizes]; [reflexivity | rewrite IH; reflexivity]. Qed.
  Lemma gw_sizes_perm : forall l l', Permutation l l' -> BackingAlgebra.AsanPlacement.gw_sizes l = BackingAlgebra.AsanPlacement.gw_sizes l'.
  Proof. induction 1; cbn [BackingAlgebra.AsanPlacement.gw_sizes]; lia. Qed.
  Theorem boot_totals_main : AsKSys10.AsKSys11.boot_totals (asan_bt hv).
  Proof.
    unfold AsKSys10.AsKSys11.boot_totals. change (bt_maps0 (asan_bt hv)) with (remove1 (w6, n6) (vm_maps h)). change (bt_reserved (asan_bt hv)) with (vm_reserved h).
    change (bt_resv6_len (asan_bt hv)) with 0x2000011000.
    destruct L_perm as (w & n & _ & UN & PM).
    pose proof (Permutation_length PM) as PL. cbn [length] in PL.
    pose proof (APS.maps_match_length E _ _ (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ CS)) as ML.
    assert (A18 : (length (a_maps HS_2) <= 24)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    assert (R4 : (length (vm_reserved h) <= 6)%nat) by (rewrite (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ CS); apply Nat.leb_le; vm_compute; reflexivity).
    pose proof (APS.co_totsz _ _ _ _ _ _ _ _ _ _ _ _ CS) as TS. rewrite sum_sizes_gw in TS.
    assert (AT : a_totsz HS_2 <= 17730000000000) by (apply Z.leb_le; vm_compute; reflexivity).
    rewrite AsKSys10.AsKSys11.gw_sizes_app in TS |- *. rewrite (gw_sizes_perm _ _ PM) in TS. cbn [BackingAlgebra.AsanPlacement.gw_sizes snd] in TS. rewrite UN in TS.
    rewrite length_app. unfold AsKSys10.AsKSys11.BOOTCNT, AsKSys10.AsKSys11.BOOTSZ. split; lia.
  Qed.
End MainA2.
