(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA MmStep StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed XB_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanPS AsanRep AsanKern AsanWf1 AsanBudget AsanBudget2 AsanRealloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_free_kit BF_poison BF_mmfix1 BF_rarmap B_policy5 B_slack5 B_budget5 B_mmchk5 B_bundle B_benv5 B_balloc5 B_bpolicy5 B_bevents5 B_rtok5 BF_unwind BF_qkit BF_alloc_iface BF_populate_iface BF_popdefs BF_pop0 BF_pop1 BF_pop2 BF_pop3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma wz_mod : forall x, Z_to_bv 64 (x mod 2^64) = Z_to_bv 64 x.
Proof. aceil. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_mod. lia. Qed.

Lemma wz_mod_add : forall x d, Z_to_bv 64 (x mod 2^64 + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. reflexivity.
Qed.

Lemma sA_self : forall s, sA (aps_alloc s) s = s.
Proof. aceil. intros s. destruct s. reflexivity. Qed.
Lemma sA_sA : forall a a' s, sA a (sA a' s) = sA a s.
Proof. aceil. intros a a' s. destruct s. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pop_row : forall mtx r,
  C8 (Z_to_bv 64 mtx) :: List.tl (region_cells r)
  = ri_cells mtx (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (rg_n_freed r).
Proof. aceil. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zlen_pop_fresh : forall au size new, 0 <= new -> zlen (pop_fresh au size new) = new.
Proof. aceil. intros. unfold pop_fresh, zlen. rewrite length_rev, length_map, length_ziota. lia. Qed.

Lemma ziota_seq : forall k a, ziota a k = map (fun i => a + Z.of_nat i) (seq 0 k).
Proof. aceil.
  induction k as [|k IH]; intros a; [reflexivity|]. cbn [ziota seq map]. rewrite Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map, IH. apply map_ext. intros; lia.
Qed.
Lemma upd_app_mid : forall {X} (l1 l2 : list X) (w x : X), upd (l1 ++ [w] ++ l2) (length l1) x = l1 ++ [x] ++ l2.
Proof. aceil. intros X l1. induction l1 as [|y l1 IH]; intros l2 w x; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma filln_spec : forall (n : nat) (pre mid junk : list word) (j : nat) (au size tf : Z),
  (length pre + n = Z.to_nat tf - j)%nat -> (j <= Z.to_nat tf)%nat -> 0 <= tf -> length mid = n ->
  filln n (pre ++ mid ++ junk) j au size tf
  = pre ++ rev (map (fun k => Z_to_bv 64 ((au + Z.of_nat (j + k) * size) / 16)) (seq 0 n)) ++ junk.
Proof. aceil.
  induction n as [|n IH]; intros pre mid junk j au size tf HL HJ TF HM.
  - destruct mid; [| cbn in HM; lia]. reflexivity.
  - cbn [filln].
    destruct mid as [|w0 mid' _] using rev_ind; [cbn in HM; lia|].
    rewrite length_app in HM. cbn in HM.
    replace (Z.to_nat (tf - 1 - Z.of_nat j)) with (length (pre ++ mid')) by (rewrite length_app; lia).
    replace (pre ++ (mid' ++ [w0]) ++ junk) with ((pre ++ mid') ++ [w0] ++ junk) by (rewrite <- !app_assoc; reflexivity).
    rewrite upd_app_mid.
    replace ((pre ++ mid') ++ [Z_to_bv 64 ((au + Z.of_nat j * size) / 16)] ++ junk)
      with (pre ++ mid' ++ ([Z_to_bv 64 ((au + Z.of_nat j * size) / 16)] ++ junk)) by (rewrite <- !app_assoc; reflexivity).
    rewrite (IH pre mid' ([Z_to_bv 64 ((au + Z.of_nat j * size) / 16)] ++ junk) (Datatypes.S j) au size tf ltac:(lia) ltac:(lia) TF ltac:(lia)).
    cbn [seq map rev]. rewrite <- seq_shift, map_map. rewrite <- !app_assoc. cbn [app]. rewrite Nat.add_0_r.
    do 3 f_equal. apply map_ext. intros k. do 2 f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma filln_fresh : forall new (free junk : list word) au size nf,
  0 <= new -> 0 <= nf -> length free = Z.to_nat nf -> (Z.to_nat new <= length junk)%nat ->
  filln (Z.to_nat new) (free ++ junk) 0 au size (nf + new)
  = free ++ map (fun z => Z_to_bv 64 z) (pop_fresh au size new) ++ skipn (Z.to_nat new) junk.
Proof. aceil.
  intros new free junk au size nf NEW NF LF LJ.
  rewrite <- (firstn_skipn (Z.to_nat new) junk) at 1.
  rewrite (filln_spec (Z.to_nat new) free (firstn (Z.to_nat new) junk) (skipn (Z.to_nat new) junk) 0 au size (nf + new));
    [| rewrite LF; lia| lia| lia| rewrite firstn_length; lia].
  do 2 f_equal. unfold pop_fresh. rewrite ziota_seq, map_map, <- !map_rev, map_map. apply map_ext. intros k. cbn [Nat.add]. do 2 f_equal; lia.
Qed.

Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).

Lemma rw_cells_CB0 : forall m X, 0 <= X -> X <= 2^64 -> rw_cells bsegs m X [CB 0 []].
Proof.
  intros m X H1 H2. unfold rw_cells, cells_at. cbn. repeat split; cbn [length Z.of_nat]; try lia. all: try (intros i Hi; cbn in Hi; lia).
Qed.

Lemma acc_ok_empty : forall L S (x : Z), acc_ok L S (Z_to_bv 64 x, 0%nat).
Proof.
  intros L S x. right. split; [unfold acc_nowrap; cbn [fst snd]; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 x)); unfold bv_modulus in *; lia| intros kk Hkk; cbn in Hkk; lia].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_wr_at : forall m A n bs, rw_cells bsegs m A [CB n bs] -> wr_at bsegs m A (Z.of_nat n).
Proof. intros m A n bs [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. exact W. Qed.

Lemma wr_at_join' : forall m a n1 n2, wr_at bsegs m a n1 -> wr_at bsegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at bsegs m a (n1 + n2).
Proof.
  intros m a n1 n2 (A1 & B1 & W1) (A2 & B2 & W2) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1); [apply W1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Section PopT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation STAT := (ae_thread E0 + kThrCacheStats).
#[local] Notation tpw := (Z_to_bv 64 0x5e1550).
#[local] Notation INST := 0xaaf58.

(* [comment removed for export] *)
Section CALL.
Variables (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (mo : Model) (s : aps) (Pq : list Z) (Dq : list batch) (c req lo usp C C' : Z) (fjunk : list word) (shj fshj : list byte) (K : TSet).
#[local] Notation a := (aps_alloc s).
#[local] Notation r := (get_region (aps_alloc s) c).
#[local] Notation RIc := (BF_popdefs.RIc c RI).
#[local] Notation RB := (SB + c * 4294967296).
#[local] Notation FA := (SB + c * 4294967296 + 3758096384).
#[local] Notation size := (class_size c).
Hypothesis KN : K [].
Hypothesis TOK : RTOKc C C' s mo.
Hypothesis AK : AKern E0 a mo.
Hypothesis WF : AWf E0 Pq Dq a.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HREQ : 1 <= req <= hint c.
Hypothesis R700 : rg_mapped_user r + kUserMapSize <= kFreeArrayOffset.
Hypothesis RFA : 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) + kFreeArrayMapSize <= kFreeArraySize.
Hypothesis RFA1 : 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) <= rg_mapped_fa r + kFreeArrayMapSize.
Hypothesis RR : kUserMapSize + kFreeArrayMapSize <= gapR a.
Hypothesis SK : stk bsegs m lo usp.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 1536.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis SPH : usp < 2^47.
Hypothesis USPR : 0 <= usp < 2^64.
Hypothesis MI : mem_inv bsegs m.
Hypothesis T8 : T mod 8 = 0.
Hypothesis TC : thread_cells m tpw 0x6028f8 CTX T.
Hypothesis PC : pop_cells E0 a c m fjunk shj fshj.
Hypothesis PST : pop_statics m.
Hypothesis CONT : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     pop_post E0 FSB0 HR0 L0 RES0 EB0 a a' c req m m' mo mo' s C C' lo usp ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (Z_to_bv 64 usp) gp tpw t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K.

(* [comment removed for export] *)
Ltac facts :=
  pose proof alloc_ceiling_range as CEILB;
  pose proof B_bundle.kHighMemBeg_val as KHB;
  pose proof (proj1 WF) as WE;
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & _);
  assert (ENV : ENVOK E0 FSB0 s) by (destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0_ & R0'_ & T0_ & _); exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ T0_));
  assert (EE : aps_env s = E0) by (destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _); exact EE);
  assert (HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling)
    by (rewrite KHB in E2; split; [clear -E2 E3; lia|]; split; [clear -E1; Z.div_mod_to_equations; nia| clear -E4 E5; unfold kSpaceSize in E4 |- *; lia]);
  assert (HSBH : kHighMemBeg <= SB) by (clear -E2 E3; lia);
  assert (HRI : RI = SB + kSpaceSize) by reflexivity;
  pose proof HC as HC30; unfold kLargestClassID in HC30;
  pose proof (proj2 (proj1 (proj2 WF)) c HC) as RG; cbv zeta in RG; unfold region_of in RG;
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12);
  pose proof PC as (INS & ROW & WRU & FAR & FAL & SHU & SHF & TST & CST);
  unfold A_INST in INS; change (0xaaf58 + 32) with 0xaaf78 in INS; rewrite (pop_row (2^60) r) in ROW;
  change (kUserMapSize / 8) with 32768 in SHU; change (kFreeArrayMapSize / 8) with 32768 in SHF;
  change kRegSize with 128 in ROW; change (RI + 128 * c) with RIc in ROW;
  assert (MUA : rg_mapped_user r mod 4096 = 0) by (clear -R2; unfold kUserMapSize in R2; Z.div_mod_to_equations; lia);
  assert (MUR : rg_mapped_user r + 262144 <= 3758096384) by (clear -R700; unfold kUserMapSize, kFreeArrayOffset in R700; lia);
  pose proof TC as (TC1 & TC2 & TC3 & TC4 & TC5).

(* [comment removed for export] *)
Definition PP (s1 : aps) (mo1 : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo1) (aSc s1) x.

Lemma PP_KIP : forall a1 mo1 R R', ATOKc R R' (sA a1 s) mo1 -> KIP (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) (PP (sA a1 s) mo1) mo1.
Proof. intros a1 mo1 R R' T1. split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ T1)| intros x Hx; exact Hx]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WZ (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (lo <= fst iv /\ snd iv <= usp) \/ (SB <= fst iv /\ snd iv <= SB + kSpaceSize + 4096)
                    \/ (kShadowBase + SB / 8 <= fst iv /\ snd iv <= kShadowBase + (SB + kSpaceSize) / 8) \/ (T <= fst iv /\ snd iv <= T + 4096)) W.

Lemma WZ_outside : forall W x, WZ W ->
  (x < lo \/ usp <= x) -> (x < SB \/ SB + kSpaceSize + 4096 <= x) ->
  (x < kShadowBase + SB / 8 \/ kShadowBase + (SB + kSpaceSize) / 8 <= x) -> (x < T \/ T + 4096 <= x) -> outside W x.
Proof.
  intros W x HW H1 H2 H3 H4. apply (proj2 (outside_forall W x)). intros l h Hin.
  pose proof (proj1 (Forall_forall _ _) HW _ Hin) as Z0. cbn [fst snd] in Z0. clear -Z0 H1 H2 H3 H4. lia.
Qed.

(* [comment removed for export] *)
Lemma WZ_img : forall W m1 m2 x, WZ W -> munch W m1 m2 -> 0x10000 <= x < 0x603000 -> m2 (wa x) = m1 (wa x).
Proof.
  intros W m1 m2 x HW MU Hx. facts. pose proof WE as WE'. wfe_open WE'.
  destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2. unfold img_sep in WE32. rewrite EI1 in WE32.
  apply MU. rewrite wa_unsigned by (clear -Hx; lia).
  apply (WZ_outside W x HW); unfold kShadowBase, kSpaceSize in *; rewrite ?A_SB_val; clear -Hx LOC CEILB HSB WE32 EI2; lia.
Qed.

(* [comment removed for export] *)
Lemma WZ_ctx : forall W m1 m2 x, WZ W -> munch W m1 m2 -> CTX <= x < CTX + 160 -> m2 (wa x) = m1 (wa x).
Proof.
  intros W m1 m2 x HW MU Hx. facts.
  destruct PL0OK as ((c0 & cl & (CR1 & (P1 & P2 & P3 & P4) & CR3 & CR4 & CR5 & CR6 & CR7 & CR8) & CC1 & CC2) & _ & _ & CT & _).
  unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kResvLen in *.
  apply MU. rewrite wa_unsigned by (clear -Hx P1 P2 CC1 CC2 CEILB; lia).
  apply (WZ_outside W x HW); unfold kShadowBase, kSpaceSize in *; rewrite ?A_SB_val.
  - clear -Hx P2 CC1 CC2 LOC. lia.
  - rewrite KHB in E2. clear -Hx CR4 CC1 CC2 E2 E3 E4. lia.
  - rewrite KHB in E2. clear -Hx P4 CC1 CC2 E2 E3 E4 E5 CEILB. lia.
  - clear -Hx CT CC1 CC2. lia.
Qed.

Lemma WZ_statics : forall W m1 m2, WZ W -> munch W m1 m2 -> wmono bsegs m1 m2 -> pop_statics m1 -> pop_statics m2.
Proof.
  intros W m1 m2 HW MU WM [ST PG]. split.
  - unfold statics in *. decompose [and] ST.
    repeat split; (eapply (BF_unwind.rw_cells_agree bsegs m1 m2); [| eassumption]; cbn; intros x Hx; apply (WZ_img W m1 m2 x HW MU);
      unfold GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in Hx; clear -Hx; lia).
  - eapply poison_globals_agree; [exact PG|]. intros x Hx. apply (WZ_img W m1 m2 x HW MU). clear -Hx. lia.
Qed.

Lemma WZ_thread_cells : forall W m1 m2, WZ W -> munch W m1 m2 -> thread_cells m1 tpw 0x6028f8 CTX T -> thread_cells m2 tpw 0x6028f8 CTX T.
Proof.
  intros W m1 m2 HW MU (X1 & X2 & X3 & X4 & X5).
  split; [| split; [| split; [| split]]].
  1-4: eapply (BF_unwind.rw_cells_agree bsegs m1 m2); [| eassumption]; cbn; rewrite ?unsigned_lit by (clear; lia); intros x Hx; apply (WZ_img W m1 m2 x HW MU); clear -Hx; lia.
  eapply (BF_unwind.rw_cells_agree bsegs m1 m2); [| exact X5]. cbn. intros x Hx. apply (WZ_ctx W m1 m2 x HW MU). clear -Hx. lia.
Qed.

Lemma WZ_ins : forall W m1 m2 cs, WZ W -> munch W m1 m2 -> Z.of_nat (cells_size cs) <= 64 -> rw_cells bsegs m1 0xaaf78 cs -> rw_cells bsegs m2 0xaaf78 cs.
Proof.
  intros W m1 m2 cs HW MU L X. eapply (BF_unwind.rw_cells_agree bsegs m1 m2); [| exact X]. intros x Hx. apply (WZ_img W m1 m2 x HW MU). clear -Hx L. lia.
Qed.

Ltac wz_split := repeat (apply Forall_cons; [cbn [fst snd]|]); [.. | apply Forall_nil].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma thr_facts :
  placed_s T 4096 /\ placed CTX 4096 /\ (CTX + 160 <= T \/ T + 4096 <= CTX)
  /\ (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) /\ (CTX + 160 <= SB \/ SB + kSpaceSize + 4096 <= CTX)
  /\ (exists c0 cl, resv_range_ok E0 c0 cl /\ c0 <= CTX /\ CTX + 160 <= c0 + cl).
Proof.
  facts. pose proof WE as WE'. wfe_open WE'.
  destruct PL0OK as ((c0 & cl & (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8) & CC1 & CC2) & _ & (TR1 & TR2 & _) & CT & _ & _ & [IA1 IA2]).
  destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof WE35rest as IS. unfold img_sep in IS. rewrite EI1 in IS. unfold app_mem in WE25. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE25. unfold kIArenaLen in *.
  split; [exact TR2|]. split.
  { unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. clear -IA1 IA2 WE25 WE26 IS EI2. lia. }
  split; [exact CT|]. split.
  { unfold kSpaceSize in E4 |- *. unfold kResvLen in *. clear -WE19 E3 E4. lia. }
  split.
  { unfold kSpaceSize in E4 |- *. unfold kResvLen in *. clear -CR4 CC1 CC2 E3 E4. lia. }
  exists c0, cl. split; [| split; [exact CC1| exact CC2]]. split; [exact CR1|]. split; [exact CR2|]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma T_app : (0 < T /\ T + 4096 <= 0x7fff7000) \/ (0x10007fff8000 <= T /\ T + 4096 <= alloc_ceiling).
Proof. pose proof (proj1 WF) as WE'. wfe_open WE'. unfold app_mem in WE14. rewrite kHighMemBeg_val, kLowAppEnd_val in WE14. exact WE14. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acc_ok_lazy_sub : forall Lz Lz' (Sa Sb : word -> Prop) x,
  (forall e', In e' Lz' -> exists e, In e Lz /\ elo e <= elo e' /\ ehi e' <= ehi e) ->
  (forall w, Sa w -> Sb w) -> acc_ok Lz Sa x -> acc_ok Lz' Sb x.
Proof.
  intros Lz Lz' Sa Sb x SUB HS [[NW O]|[NW IN]].
  - left. split; [exact NW|]. intros l sz Hin. destruct (SUB _ Hin) as ([lo0 sz0] & Hin0 & L1 & L2).
    unfold elo, ehi in L1, L2. cbn [fst snd] in L1, L2. pose proof (O lo0 sz0 Hin0). clear -H L1 L2. lia.
  - right. split; [exact NW| intros k Hk; apply HS, IN, Hk].
Qed.

Lemma commit_ks : forall (a1 a2 : astate) (moX : Model) (R R' A L : Z),
  ATOKc R R' (sA a1 s) moX -> AKern E0 a1 moX ->
  A mod 4096 = 0 -> L mod 4096 = 0 -> 0 < L -> L <= 4096 * R -> 0 <= A -> A + L <= alloc_ceiling -> commit_site E0 a1 A L ->
  a_eager_bytes a2 = a_eager_bytes a1 + L -> as_sec a2 = as_sec a1 -> as_residue a2 = as_residue a1 ->
  as_node_blocks a2 = as_node_blocks a1 -> as_store_blocks a2 = as_store_blocks a1 ->
  (forall mo2 mo', AKern E0 a1 mo2 -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo2) -> ivs_wf (vm_noaccess (m_vmmaps mo2)) ->
     vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mo2)) A (A + L) ->
     (forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mo2) /\ elo e <= elo e' /\ ehi e' <= ehi e
                   /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + L <= elo e'))) ->
     AKern E0 a2 mo') ->
  forall mo2, magree moX mo2 -> KIA (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) mo2 ->
     (forall eff, mmap_CHK A L 3 50 mo2 eff <> CheckUnmodeled)
  /\ (exists eff mo', mmap_CHK A L 3 50 mo2 eff = CheckOk mo' [] /\ node_refusal (NMmap A L 3 50) mo2 (eff_ret eff) = false)
  /\ (forall eff mo', mmap_CHK A L 3 50 mo2 eff = CheckOk mo' [] -> node_refusal (NMmap A L 3 50) mo2 (eff_ret eff) = false ->
        eff = mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] []
        /\ ATOKc (R - L / 4096) R' (sA a2 s) mo' /\ AKern E0 a2 mo'
        /\ (forall Sx x, acc_ok (m_vm_lazy mo2) Sx x -> acc_ok (m_vm_lazy mo') Sx x)
        /\ (forall w, aSc (sA a1 s) w -> aSc (sA a2 s) w)
        /\ m_fs mo' = m_fs mo2 /\ m_fds mo' = m_fds mo2 /\ m_tid mo' = m_tid mo2).
Proof.
  intros a1 a2 moX R R' A L ATK AK1 AA LA L0p LR A0 AHI SITE EB Es Er En Est GROW mo2 AG KIA2. pose proof alloc_ceiling_range as CEILB.
  destruct (ev_commit_kernel E0 FSB0 HR0 L0 RES0 EB0 HR0_ok RES0_low R R' (sA a1 s) moX mo2 A L Pq Dq a ATK AK1 WF AG KIA2 AA LA L0p LR SITE) as (NU & GR & ALL).
  split; [exact NU|]. split; [exact GR|].
  intros eff mo' HC' NR. destruct (ALL eff mo' HC' NR) as (-> & MMA & -> & KIA' & KVM' & LIM' & OSL' & PSL' & NAV & LAV).
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK AG KIA2) as ATK2.
  pose proof (magree_frame _ _ AG) as (Ffds & Fvm & Flz & _).
  pose proof (AKern_frame _ _ _ _ Fvm Flz AK1) as AK2.
  destruct ATK2 as (_ & [O0 _] & EV & _ & KVM2 & [P0 _]).
  pose proof KVM2 as (_ & _ & _ & KWF2 & _).
  assert (HE : A + L < 2^64) by (clear -AHI CEILB; lia).
  split; [reflexivity|].
  split. { rewrite <- (sA_sA a2 a1 s). apply (ATOK_commit E0 FSB0 HR0 L0 RES0 EB0 R R' (sA a1 s) a2 (m_commit mo2 A L) L KIA' KVM' LIM' O0 OSL' EV P0 PSL'); cbn [aps_alloc sA aps_set_alloc]; assumption. }
  split. { apply (GROW mo2); [exact AK2| apply commit_maps| exact (proj1 (proj2 KWF2))| apply commit_noaccess; assumption| exact LAV]. }
  split. { intros Sx x HX. eapply acc_ok_lazy_sub; [| intros w Hw; exact Hw| exact HX]. intros e' He'. destruct (LAV e' He') as (e & He & X1 & X2 & _). exists e. auto. }
  split. { intros w Hw. unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *. rewrite Es, Er, Est. exact Hw. }
  unfold m_commit, vm_forget_range, with_vmmaps. destruct mo2. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pop_phaseE : forall (a2 : astate) (m2 : mem) (mo2 : Model) (junk2 : list word)
    (t0' t1' t2' a1x a2x a3x a4x a5x a6x a7x s6x t3' t4' t5' t6' : word),
  let r2 := get_region a2 c in let mu2 := rg_mapped_user r2 in let mfa2 := rg_mapped_fa r2 in
  let new := (mu2 - rg_alloc_user r) / size in let tf := rg_num_freed r + new in
  (* [comment removed for export] *)
  AKern E0 a2 mo2 -> RTOKc C C' (sA a2 s) mo2 ->
  rg_alloc_user r2 = rg_alloc_user r -> rg_free r2 = rg_free r -> rg_n_allocated r2 = rg_n_allocated r -> rg_n_freed r2 = rg_n_freed r ->
  rg_mapped_user r <= mu2 <= 3758096384 -> rg_mapped_fa r <= mfa2 -> 4 * tf <= mfa2 -> mfa2 <= 536870912 ->
  (forall c', 1 <= c' <= kLargestClassID -> c' <> c -> get_region a2 c' = get_region a c') ->
  pop_same a a2 ->
  (exists f orc evs orc', arun f (populate_free_array E0 c req a) orc = Some (st_fin c a2, ONorm true, evs, orc')) ->
  m_fs mo2 = m_fs mo /\ m_fds mo2 = m_fds mo /\ m_tid mo2 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m2 -> stk bsegs m2 lo (usp - 64) -> BF_pop1.pop_frame usp m2 ra s0 s1 s2 s3 s4 s5 s6 ->
  rw_cells bsegs m2 RIc (ri_cells (2^60) (rg_num_freed r) mfa2 (rg_alloc_user r) mu2 (rg_n_allocated r) (rg_n_freed r)) ->
  rw_cells bsegs m2 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  wr_at bsegs m2 RB mu2 ->
  u32arr bsegs m2 FA (map (fun z => Z_to_bv 64 z) (rg_free r) ++ junk2) -> 4 * (zlen (rg_free r) + zlen junk2) = mfa2 ->
  rw_cells bsegs m2 (T + kThrStats + 72) [C8 (Z_to_bv 64 (ts_mmaps (as_ts a2))); C8 (Z_to_bv 64 (ts_mmaped (as_ts a2)))] ->
  rw_cells bsegs m2 (STAT + 24) [C8 (Z_to_bv 64 (as_cache_mapped a2))] ->
  thread_cells m2 tpw 0x6028f8 CTX T -> pop_statics m2 ->
  wmono bsegs m m2 -> munch (pop_W E0 a a2 c usp) m m2 ->
  rw_cells bsegs m2 (kShadowBase + (RB + rg_mapped_user r) / 8)
     [CB (Z.to_nat ((mu2 - rg_mapped_user r) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu2 - rg_mapped_user r) / 8)))] ->
  rw_cells bsegs m2 (kShadowBase + (FA + rg_mapped_fa r) / 8)
     [CB (Z.to_nat ((mfa2 - rg_mapped_fa r) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mfa2 - rg_mapped_fa r) / 8)))] ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (Z_to_bv 64 A_POP_EFARET) (Z_to_bv 64 (usp - 64)) gp tpw t0' t1' t2' (Z_to_bv 64 RIc) (Z_to_bv 64 tf) (Z_to_bv 64 1)
                    a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 (mu2 - rg_alloc_user r)) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 A_POP_EFARET) fc None m2 (seg_rom bsegs)) mo2) K.
Proof.
  intros until t6'. cbv zeta. intros AK2 TOK2 Eau Efr Ena Enf MU2 MFA2 TF4 MFAS OTH PS RUN FS MI2 SK2 FR2 ROW2 INS2 WRU2 FAR2 FAL2 TST2 CST2 TCm2 PST2 WM2 MU02 SHUP SHFP.
  facts.
  set (mu2 := rg_mapped_user (get_region a2 c)) in *. assert (Emu2 : mu2 = rg_mapped_user (get_region a2 c)) by reflexivity. clearbody mu2.
  set (mfa2 := rg_mapped_fa (get_region a2 c)) in *. assert (Emfa2 : mfa2 = rg_mapped_fa (get_region a2 c)) by reflexivity. clearbody mfa2.
  set (au := rg_alloc_user r) in *. assert (Eau0 : au = rg_alloc_user r) by reflexivity.
  set (mu := rg_mapped_user r) in *. assert (Emu : mu = rg_mapped_user r) by reflexivity.
  set (mfa := rg_mapped_fa r) in *. assert (Emfa : mfa = rg_mapped_fa r) by reflexivity.
  set (nf := rg_num_freed r) in *. assert (Enf0 : nf = rg_num_freed r) by reflexivity.
  pose proof (proj2 (class_size_mod c HC30)) as CS.
  set (new := (mu2 - au) / size) in *.
  assert (NEW0 : 0 <= new) by (subst new; apply Z.div_pos; clear -MU2 R1 CS Eau0 Emu; subst; lia).
  set (tf := nf + new) in *.
  assert (NF0 : 0 <= nf) by (rewrite Enf0; unfold rg_num_freed; clear; lia).
  (* [comment removed for export] *)
  set (P2 := PP (sA a2 s) mo2).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK2) as (R2_ & R2' & ATK2 & _).
  pose proof (PP_KIP a2 mo2 _ _ ATK2) as KIP2.
  assert (AK2s : AKern E0 (aps_alloc (sA a2 s)) mo2) by exact AK2.
  assert (PSTK2 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo2 AK2s WE ENV0); clear -H1 H2 LOC SPH CEILB; lia. }
  assert (PRIR2 : forall x k, RIc <= x -> x + Z.of_nat k <= RIc + 128 -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a2 s) mo2 WE); unfold BF_popdefs.RIc in H1, H2; rewrite HRI in H1, H2;
      change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
  (* [comment removed for export] *)
  assert (PFA2 : forall x k, FA + 4 * nf <= x -> x + Z.of_nat k <= FA + 4 * tf -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. destruct k as [|k']; [apply acc_ok_empty|].
    assert (HU : 0 < rg_mapped_fa (get_region a2 c)) by (rewrite <- Emfa2; clear -H1 H2 TF4 NF0 NEW0; subst tf; lia).
    pose proof (ak_fa _ _ _ AK2 c HC HU) as U. pose proof (eager_rw_lazy_disjoint _ _ _ U) as LD. rewrite <- Emfa2 in LD.
    unfold free_array, region_beg in LD. change kRegionSize with 4294967296 in LD. change kFreeArrayOffset with 3758096384 in LD.
    eapply (acc_ok_of_lazy_disjoint mo2 _ _ _ _ _ LD); unfold kSpaceSize in HSB; clear -H1 H2 HSB HC30 TF4 MFAS NF0 CEILB NEW0; subst tf; lia. }
  (* [comment removed for export] *)
  set (QK := fun ms' => forall mo', magree mo2 mo' -> KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2 mo' -> realizes_cfg acfg bsegs (mkCfg ms' mo') K).
  eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2 QK); [| exact KIP2| intros ms' mo' HQ AG KP; exact (HQ mo' AG KP)].
  assert (LWS : 4 * Z.of_nat (length (map (fun z => Z_to_bv 64 z) (rg_free r) ++ junk2)) = mfa2)
    by (rewrite length_app, length_map; unfold zlen in FAL2; clear -FAL2; lia).
  eapply (pop_finish P2 gp tpw s7 s8 s9 s10 s11 F fc usp lo SB c RI LOC LO HSB HC HRI PSTK2 PRIR2 m2 (map (fun z => Z_to_bv 64 z) (rg_free r) ++ junk2)
            ra s0 s1 s2 s3 s4 s5 s6 s6x t0' t1' t2' a1x a2x a3x a4x a5x a6x a7x t3' t4' t5' t6' (2^60) nf mfa2 au mu2 (rg_n_allocated r) (rg_n_freed r) QK
            MI2 SK2 FR2 ROW2).
  - clear -R1 MU2 Eau0 Emu. subst. lia.
  - clear -MU2. lia.
  - exact NF0.
  - clear -TF4 LWS. subst tf new. lia.
  - exact LWS.
  - clear -MFAS. lia.
  - exact FAR2.
  - exact PFA2.
  - (* [comment removed for export] *)
    intros m3 a2' a3' a4' a5' MI3 SK3 MU3 WM3 ROW3 FAR3. apply evtA_done. intros mo3 AG3 KP3.
    pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
    assert (WZ3 : WZ [(usp - 64, usp); (FA + 4 * nf, FA + 4 * tf); (RIc + 16, RIc + 24); (RIc + 32, RIc + 40); (RIc + 68, RIc + 69)]).
    { unfold WZ, BF_popdefs.RIc. rewrite HRI. unfold kSpaceSize, kShadowBase. unfold kSpaceSize in HSB.
      repeat (apply Forall_cons; [cbn [fst snd]|]); [.. | apply Forall_nil].
      - left. clear -LO. lia.
      - right; left. subst tf. clear -HC30 NF0 TF4 MFAS NEW0. lia.
      - right; left. clear -HC30. lia.
      - right; left. clear -HC30. lia.
      - right; left. clear -HC30. lia. }
    set (a' := st_fin c a2).
    assert (RG' : get_region a' c = mkRegion mu2 (au + new * size) (rg_free r ++ pop_fresh au size new) mfa2 (rg_n_allocated r) (rg_n_freed r)).
    { subst a'. rewrite st_fin_region. cbv zeta. rewrite Eau, Efr, Ena, Enf, <- Emu2, <- Emfa2. reflexivity. }
    assert (OTH' : forall c', c <> c' -> get_region a' c' = get_region a2 c') by (intros c' Hc'; subst a'; apply st_fin_other; exact Hc').
    pose proof (pop_same_fin c a2) as PSF. pose proof (same_fp_st_fin E0 c a2 HC30) as SFP. fold a' in PSF, SFP.
    assert (AK' : AKern E0 a' mo3).
    { eapply (AKern_mapped_ext E0 a2 a' mo3).
      - intros c0 Hc0. destruct (Z.eq_dec c c0) as [<-|NE]; [rewrite RG'; cbn [rg_mapped_user rg_mapped_fa]; rewrite Emu2, Emfa2; split; reflexivity|].
        rewrite (OTH' c0 NE). split; reflexivity.
      - destruct PSF as (_ & _ & _ & _ & X & _). exact X.
      - destruct PSF as (_ & _ & _ & _ & _ & X & _). exact X.
      - unfold pop_same in PSF. decompose [and] PSF. assumption.
      - unfold pop_same in PSF. decompose [and] PSF. assumption.
      - exact (AKern_frame _ _ _ _ Fvm3 Flz3 AK2). }
    assert (TOK' : RTOKc C C' (sA a' s) mo3).
    { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a2 a' mo3).
      - eapply RTOK_magree; [exact TOK2| exact AG3| exact (proj1 KP3)].
      - exact SFP.
      - unfold pop_same in PSF. decompose [and] PSF. assumption.
      - unfold pop_same in PSF. decompose [and] PSF. assumption. }
    assert (LFREE : length (map (fun z : Z => Z_to_bv 64 z) (rg_free r)) = Z.to_nat nf) by (rewrite length_map; rewrite Enf0; unfold rg_num_freed; clear; lia).
    assert (LJ : (Z.to_nat new <= length junk2)%nat) by (unfold zlen in FAL2; clear -FAL2 TF4 NEW0 NF0 LFREE; rewrite length_map in LFREE; subst tf; lia).
    pose proof FAR3 as FAR3'. subst tf. rewrite (filln_fresh new _ junk2 au size nf NEW0 NF0 LFREE LJ) in FAR3'.
    (* [comment removed for export] *)
    pose proof WE as WE'. wfe_open WE'.
    assert (TRS : T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) by (unfold kSpaceSize in E4 |- *; clear -WE19 E3 E4; lia).
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo3 a').
    split. { exact RUN. }
    split; [exact AK'|]. split; [exact TOK'|].
    destruct FS as (FS1 & FS2 & FS3).
    split; [rewrite Ffs3; exact FS1|]. split; [rewrite Ffds3; exact FS2|]. split; [rewrite Ftid3; exact FS3|].
    split; [exact SK3|]. split; [exact MI3|]. split; [exact (wmono_trans _ _ _ _ WM2 WM3)|].
    split.
    { (* [comment removed for export] *)
      unfold pop_W in MU02 |- *. cbv zeta in MU02. cbv zeta. rewrite RG'. cbn [rg_mapped_user rg_mapped_fa].
      rewrite <- Emu2, <- Emfa2 in MU02. rewrite <- ?Emu, <- ?Emfa in MU02 |- *.
      change (zlen (rg_free r)) with (rg_num_freed r) in MU02 |- *. rewrite <- Enf0 in MU02 |- *.
      unfold K_POP, free_array in MU02 |- *. unfold region_beg in MU02 |- *. change kRegionSize with 4294967296 in MU02 |- *. change kFreeArrayOffset with 3758096384 in MU02 |- *.
      change kRegSize with 128 in MU02 |- *. change (RI + 128 * c) with RIc in MU02 |- *.
      eapply munch_trans; [eapply munch_cover; [exact MU02| apply covers_self]| eapply munch_cover; [exact MU3|]].
      clear -NF0 TF4 NEW0 HC30. solve_covers. }
    split.
    { (* [comment removed for export] *)
      exists (skipn (Z.to_nat new) junk2). unfold pop_cells_out. cbv zeta. rewrite RG'. cbn [rg_mapped_user rg_free rg_mapped_fa].
      split. { unfold A_INST. change (0xaaf58 + 32) with 0xaaf78. eapply (WZ_ins _ m2 m3); [exact WZ3| exact MU3| cbn [cells_size csize Nat.add]; clear; lia| exact INS2]. }
      split. { rewrite (pop_row (2^60)). cbn [rg_num_freed rg_mapped_fa rg_alloc_user rg_mapped_user rg_n_allocated rg_n_freed rg_free].
               unfold rg_num_freed. rewrite length_app. pose proof (zlen_pop_fresh au size new NEW0) as ZP. unfold zlen in ZP.
               replace (Z.of_nat (length (rg_free r) + length (pop_fresh au size new))%nat) with (nf + new) by (rewrite Nat2Z.inj_add, ZP, Enf0; unfold rg_num_freed; clear; lia).
               change kRegSize with 128. change (RI + 128 * c) with RIc. exact ROW3. }
      split; [eapply wr_at_transport; [exact WRU2| exact WM3]|].
      split; [rewrite map_app, <- app_assoc; exact FAR3'|].
      split. { unfold zlen. rewrite length_app, length_skipn. pose proof (zlen_pop_fresh au size new NEW0) as ZP. unfold zlen in ZP, FAL2.
               rewrite length_map in LFREE. clear -ZP FAL2 LJ LFREE NEW0 NF0. lia. }
      subst a'. rewrite st_fin_ts, st_fin_cm. unfold kThrStats, kThrCacheStats in TST2, CST2 |- *.
      split; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3|]); cbn [disjoint_from cells_size csize fst snd Nat.add];
        unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -TRS LOC LO HC30 CEILB E5 E4 E3 WE15 NF0 TF4 MFAS NEW0; repeat split; lia. }
    split; [exact (WZ_statics _ m2 m3 WZ3 MU3 WM3 PST2)|].
    (* [comment removed for export] *)
    rewrite RG'. cbn [rg_mapped_user rg_mapped_fa]. rewrite <- ?Emu2, <- ?Emfa2, <- ?Emu, <- ?Emfa.
    unfold free_array in SHUP, SHFP |- *. unfold region_beg in SHUP, SHFP |- *. change kRegionSize with 4294967296 in SHUP, SHFP |- *. change kFreeArrayOffset with 3758096384 in SHUP, SHFP |- *.
    assert (W8 : 0 <= (mu2 - mu) / 8 /\ 0 <= (mfa2 - mfa) / 8) by (split; apply Z.div_pos; clear -MU2 MFA2; lia).
    split; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3|]); cbn [disjoint_from cells_size csize fst snd Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear -W8; lia);
      unfold BF_popdefs.RIc, kShadowBase; rewrite HRI; unfold kSpaceSize in *; rewrite KHB in HSBH; unfold kFreeArraySize in R7; clear -LOC LO HC30 CEILB HSBH HSB MU2 MFAS W8 R7 MFA2 R1 R5 NF0; repeat split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pop_phaseD : forall (a1 : astate) (m1 : mem) (mo1 : Model)
    (ra0 s1x a1x a2x a4x a5x a6x a7x s3x s6x t0' t1' t2' t3' t4' t5' t6' : word) (f1 : nat) (o1 : list aans) (evs1 : list aev),
  let r1 := get_region a1 c in let mu1 := rg_mapped_user r1 in
  (* [comment removed for export] *)
  AKern E0 a1 mo1 -> RTOKc C C' (sA a1 s) mo1 -> kFreeArrayMapSize <= gapR a1 ->
  rg_alloc_user r1 = rg_alloc_user r -> rg_free r1 = rg_free r -> rg_mapped_fa r1 = rg_mapped_fa r ->
  rg_n_allocated r1 = rg_n_allocated r -> rg_n_freed r1 = rg_n_freed r ->
  (forall c', c <> c' -> get_region a1 c' = get_region a c') -> pop_same a a1 ->
  rg_alloc_user r + req * size <= mu1 -> rg_mapped_user r <= mu1 <= rg_mapped_user r + kUserMapSize -> mu1 <= 3758096384 ->
  (forall orc, arun f1 (pop_phase1 E0 c req a a) (o1 ++ orc) = Some (a1, ONorm true, evs1, orc)) ->
  m_fs mo1 = m_fs mo /\ m_fds mo1 = m_fds mo /\ m_tid mo1 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m1 -> stk bsegs m1 lo (usp - 64) -> BF_pop1.pop_frame usp m1 ra s0 s1 s2 s3 s4 s5 s6 ->
  rw_cells bsegs m1 RIc (ri_cells (2^60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) mu1 (rg_n_allocated r) (rg_n_freed r)) ->
  rw_cells bsegs m1 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  wr_at bsegs m1 RB mu1 ->
  u32arr bsegs m1 FA (map (fun z => Z_to_bv 64 z) (rg_free r) ++ fjunk) ->
  rw_cells bsegs m1 (kShadowBase + (FA + rg_mapped_fa r) / 8) [CB (Z.to_nat 32768) fshj] ->
  rw_cells bsegs m1 (T + kThrStats + 72) [C8 (Z_to_bv 64 (ts_mmaps (as_ts a1))); C8 (Z_to_bv 64 (ts_mmaped (as_ts a1)))] ->
  rw_cells bsegs m1 (STAT + 24) [C8 (Z_to_bv 64 (as_cache_mapped a1))] ->
  thread_cells m1 tpw 0x6028f8 CTX T -> pop_statics m1 ->
  wmono bsegs m m1 -> munch (pop_W E0 a a1 c usp) m m1 ->
  rw_cells bsegs m1 (kShadowBase + (RB + rg_mapped_user r) / 8)
     [CB (Z.to_nat ((mu1 - rg_mapped_user r) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu1 - rg_mapped_user r) / 8)))] ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR ra0 (Z_to_bv 64 (usp - 64)) gp tpw t0' t1' t2' (Z_to_bv 64 RIc) s1x (Z_to_bv 64 INST) a1x a2x (Z_to_bv 64 (rg_alloc_user r)) a4x a5x a6x a7x
                    (Z_to_bv 64 RB) s3x (Z_to_bv 64 mu1) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 A_POP_MID) fc None m1 (seg_rom bsegs)) mo1) K.
Proof.
  intros until evs1. cbv zeta. intros AK1 TOK1 RR1 Eau Efr Emfa1 Ena Enf OTH1 PS1 GROWN MU1K MU1 PH1 FS1 MI1 SK1 FR1 ROW1 INS1 WRU1 FAR1 SHF1 TST1 CST1 TCm1 PST1 WM1 MU01 SHUP1.
  facts.
  pose proof (proj2 (class_size_mod c HC30)) as CS.
  set (new := (rg_mapped_user (get_region a1 c) - rg_alloc_user r) / size) in *.
  assert (NEW0 : 0 <= new) by (subst new; apply Z.div_pos; clear -GROWN R1 CS HREQ; nia).
  set (tf := rg_num_freed r + new) in *.
  assert (NF0 : 0 <= rg_num_freed r) by (unfold rg_num_freed; clear; lia).
  assert (NFE : rg_num_freed r = zlen (rg_free r)) by reflexivity.
  (* [comment removed for export] *)
  assert (NEWLE : new <= (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / size) by (subst new; apply Z.div_le_mono; [clear -CS; lia| clear -MU1K; lia]).
  assert (TF1 : 4 * tf <= rg_mapped_fa r + 262144) by (subst tf; unfold kFreeArrayMapSize in RFA1; clear -RFA1 NEWLE; lia).
  assert (TFS : 4 * tf + 262144 <= 536870912) by (subst tf; unfold kFreeArrayMapSize, kFreeArraySize, kRegionSize, kFreeArrayOffset in RFA; clear -RFA NEWLE; lia).
  (* [comment removed for export] *)
  set (P2 := PP (sA a1 s) mo1).
  destruct (RTOK_elim_roomR _ _ _ _ _ _ _ _ _ _ kFreeArrayMapSize TOK1 RR1) as (R & R' & ATK1 & HCR & HCR' & LR & GD0 & GP0 & GLE).
  pose proof (PP_KIP a1 mo1 _ _ ATK1) as KIP1.
  assert (AK1s : AKern E0 (aps_alloc (sA a1 s)) mo1) by exact AK1.
  assert (PSTK2 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. apply (pol_stack' E0 FSB0 HR0 (sA a1 s) mo1 AK1s WE ENV0); clear -H1 H2 LOC SPH CEILB; lia. }
  assert (PDAT2 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. apply (pol_img' E0 FSB0 HR0 (sA a1 s) mo1 AK1s WE ENV ENV0); clear -H1 H2; lia. }
  assert (PRIR2 : forall x k, RIc <= x -> x + Z.of_nat k <= RIc + 128 -> P2 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P2, PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a1 s) mo1 WE); unfold BF_popdefs.RIc in H1, H2; rewrite HRI in H1, H2;
      change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
  (* [comment removed for export] *)
  set (QK := fun ms' => forall mo', magree mo1 mo' -> KIP (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) P2 mo' -> realizes_cfg acfg bsegs (mkCfg ms' mo') K).
  eapply (rzA_seg_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) P2 QK); [| exact KIP1| intros ms' mo' HQ AG KP; exact (HQ mo' AG KP)].
  eapply (pop_mid P2 gp tpw s7 s8 s9 s10 s11 F fc usp lo SB c RI LOC LO HSB HC HRI PRIR2 m1 ra0 s1x s3x s6x t0' t1' t2' a1x a2x a4x a5x a6x a7x t3' t4' t5' t6'
            (2^60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user (get_region a1 c)) (rg_n_allocated r) (rg_n_freed r) QK MI1 ROW1).
  - clear -GROWN R1 HREQ CS. nia.
  - exact MU1.
  - split; [exact NF0|]. clear -R8 R7 NF0. unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. lia.
  - (* [comment removed for export] *)
    replace ((rg_num_freed r) + ((rg_mapped_user (get_region a1 c)) - (rg_alloc_user r)) / size) with tf by reflexivity.
    eapply (efa_pre_gen P2 gp tpw F fc lo SB c RI LOC HSB HC HRI PDAT2 PRIR2 m1 (Z_to_bv 64 A_POP_EFARET) (usp - 64)
              t0' t1' t2' (Z_to_bv 64 RIc) (Z_to_bv 64 tf) a4x a5x a6x a7x (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 ((rg_mapped_user (get_region a1 c)) - (rg_alloc_user r))) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3' t4' t5' t6'
              tf (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user (get_region a1 c)) (rg_n_allocated r) (rg_n_freed r) (2^60) QK MI1 SK1).
    + clear -LO. lia.
    + clear -SPH. lia.
    + clear -SPA. Z.div_mod_to_equations. lia.
    + intros x k H1 H2. apply PSTK2; [exact H1| clear -H2; lia].
    + exact INS1.
    + exact ROW1.
    + clear -NF0 NEW0. subst tf. lia.
    + exact TF1.
    + clear -R5. lia.
    + clear -R6. unfold kFreeArrayMapSize in R6. exact R6.
    + clear -R7. unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. lia.
    + intros GROW0. clear -GROW0 TFS. lia.
    + (* [comment removed for export] *)
      intros m2 ENOUGH MI2 SK2 MU12 WM12. apply evtA_done. intros mo2 AG2 KP2.
      pose proof (magree_frame _ _ AG2) as (Ffds2 & Fvm2 & Flz2 & Ffs2 & Fh2 & Ftid2 & _).
      replace (ret_pc (Z_to_bv 64 A_POP_EFARET)) with (Z_to_bv 64 A_POP_EFARET) by (symmetry; apply ret_pc_even; [unfold A_POP_EFARET; clear; lia| reflexivity]).
      assert (WZ2 : WZ [(usp - 64 + -48, usp - 64)]).
      { unfold WZ. wz_split. left. clear -LO. lia. }
      assert (PTF : pop_tf c a1 = tf) by (unfold pop_tf, rg_num_freed; cbv zeta; rewrite Eau, Efr; subst tf new; reflexivity).
      eapply (pop_phaseE a1 m2 mo2 fjunk); rewrite ?Emfa1.
      * exact (AKern_frame _ _ _ _ Fvm2 Flz2 AK1).
      * eapply RTOK_magree; [exact TOK1| exact AG2| exact (proj1 KP2)].
      * exact Eau. * exact Efr. * exact Ena. * exact Enf.
      * clear -MU1K MU1. lia.
      * clear. lia.
      * (* [comment removed for export] *) clear -ENOUGH. subst tf new. lia.
      * clear -R7. unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. lia.
      * intros c' Hc' NE. apply OTH1. clear -NE. lia.
      * exact PS1.
      * (* [comment removed for export] *)
        destruct (phase2_true E0 c a1 0%nat [] a1 true [] [] ltac:(apply (efa_run_nogrow E0 c a1); rewrite PTF, Emfa1; clear -ENOUGH; lia) eq_refl eq_refl) as [f2 RUN2].
        destruct (pop_run E0 c req a f1 f2 (o1 ++ []) a1 true evs1 [] (st_fin c a1) (ONorm true) [] [] (PH1 []) RUN2) as [f RUN].
        exists f, (o1 ++ []), (evs1 ++ []), []. exact RUN.
      * rewrite Ffs2, Ffds2, Ftid2. exact FS1.
      * exact MI2.
      * exact SK2.
      * eapply rw_cells_transport; [exact FR1| exact MU12| exact WM12| unfold BF_pop1.pop_frame; cbn [disjoint_from cells_size csize fst snd Nat.add]; clear; lia].
      * eapply rw_cells_transport; [exact ROW1| exact MU12| exact WM12| unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]; unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -LOC LO HSB CEILB HC30; lia].
      * eapply (WZ_ins _ m1 m2); [exact WZ2| exact MU12| | exact INS1]. cbn [cells_size csize Nat.add]. clear. lia.
      * eapply wr_at_transport; [exact WRU1| exact WM12].
      * eapply u32arr_transport; [exact FAR1| exact MU12| exact WM12|]. cbn [disjoint_from fst snd]. rewrite length_app, length_map. unfold zlen in FAL.
        unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. unfold kSpaceSize in HSB. clear -LOC LO HSB CEILB HC30 FAL R7. lia.
      * exact FAL.
      * eapply rw_cells_transport; [exact TST1| exact MU12| exact WM12| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrStats; pose proof WE as WE'; wfe_open WE'; clear -LOC LO WE15; lia].
      * eapply rw_cells_transport; [exact CST1| exact MU12| exact WM12| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrCacheStats; pose proof WE as WE'; wfe_open WE'; clear -LOC LO WE15; lia].
      * exact (WZ_thread_cells _ m1 m2 WZ2 MU12 TCm1).
      * exact (WZ_statics _ m1 m2 WZ2 MU12 WM12 PST1).
      * exact (wmono_trans _ _ _ _ WM1 WM12).
      * eapply munch_trans; [exact MU01|]. eapply munch_cover; [exact MU12|]. unfold pop_W, K_POP. cbv zeta. clear -LO. solve_covers.
      * eapply rw_cells_transport; [exact SHUP1| exact MU12| exact WM12|]. cbn [disjoint_from cells_size csize fst snd Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear -MU1K; lia).
        unfold kShadowBase, kUserMapSize in *. unfold kSpaceSize in HSB. clear -LOC LO HSB CEILB HC30 MU1K MU1 R1. split; [| exact I]. left. Z.div_mod_to_equations. lia.
      * replace ((rg_mapped_fa r - rg_mapped_fa r) / 8) with 0 by (rewrite Z.sub_diag; reflexivity). cbn [Z.to_nat repeat].
        apply rw_cells_CB0; unfold kShadowBase; unfold kSpaceSize in HSB; clear -HSB HC30 R5 R7 CEILB; unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7; Z.div_mod_to_equations; lia.
    + (* [comment removed for export] *)
      intros m2 j GROW MI2 SK2 MU12 WM12 EFR. apply evtA_done. intros mo2 AG2 KP2.
      pose proof (magree_frame _ _ AG2) as (Ffds2 & Fvm2 & Flz2 & Ffs2 & Fh2 & Ftid2 & _).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK1 AG2 (proj1 KP2)) as ATK2.
      pose proof (AKern_frame _ _ _ _ Fvm2 Flz2 AK1) as AK2.
      assert (WZ2 : WZ [(usp - 64 + -48, usp - 64)]) by (unfold WZ; wz_split; left; clear -LO; lia).
      pose proof WE as WE'. wfe_open WE'.
      set (A := FA + rg_mapped_fa r) in *.
      assert (HA : 0x603000 <= A /\ A + 262144 <= SB + kSpaceSize /\ A mod 4096 = 0).
      { subst A. unfold kSpaceSize. unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. clear -HSB HC30 R5 R6 R7 TFS TF1 NF0 NEW0 GROW. subst tf.
        unfold kFreeArrayMapSize in R6. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
      destruct HA as (HA1 & HA2 & HA3). pose proof HSB as (SB1 & SB2 & SB3).
      (* [comment removed for export] *)
      assert (USP112 : bv_unsigned (Z_to_bv 64 (usp - 64 + -48)) = usp - 64 + -48) by (apply unsigned_lit; clear -LO LOC CEILB SPH; lia).
      eapply (rzA_mm_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) P2 (NMmap A 262144 3 MAP_FIXED_RW) (mmap_CHK A 262144 3 MAP_FIXED_RW) (dec_zs A 262144)
                (rar_map_gen_post (fun x r u => x = (r, u)) (Z_to_bv 64 A_EFA_MMRET) (Z_to_bv 64 (usp - 64 + -48)) gp tpw
                   (Z_to_bv 64 (rg_mapped_fa r + 262144)) (Z_to_bv 64 A) (Z_to_bv 64 262144) (Z_to_bv 64 RIc)
                   (Z_to_bv 64 (rg_mapped_user (get_region a1 c) - rg_alloc_user r)) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 F fc A 262144 lo m2)
                _ mo2 K).
      * apply mm_node_mmap.
      * left. reflexivity.
      * eapply (rar_map_gen_specA P2 PDAT2 (dec_zs A 262144) (fun x r u => x = (r, u))); rewrite ?USP112;   (* [comment removed for export] *)
          [ intros rsp x D; destruct (dec_zs_Some _ _ _ _ D) as (r' & u' & -> & ->); exists r', u'; split; reflexivity
          | exact SK2 | exact LOC | clear -LO; lia | clear -SPH; lia | exact MI2 | exact (proj1 (WZ_statics _ m1 m2 WZ2 MU12 WM12 PST1))
          | reflexivity | reflexivity | exact HA3 | reflexivity
          | unfold b_image_end; exact HA1 | clear; lia | rewrite mmap_len_alignedA by reflexivity; unfold kSpaceSize in HA2, SB3; clear -HA2 SB3 LOC; lia
          | intros x k H1 H2; apply PSTK2; [exact H1| clear -H2; lia] ].
      * exact KP2.
      * exact KN.
      * intros moK AGK KIAK.
        assert (SITE : commit_site E0 a1 A 262144).
        { left. unfold kResvLen, kPtrArrayLen, kPtrArrayCommit. unfold kSpaceSize in HA2, E4. split; [clear -E3 R5 HC30; subst A; lia|].
          split; [clear -HA2 E4; lia|]. destruct (as_ptr_committed a1 =? 0); clear -WE20 HA2 E3 E4 R5 HC30; subst A; lia. }
        assert (GROWFA : forall mox mo', AKern E0 a1 mox -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mox) -> ivs_wf (vm_noaccess (m_vmmaps mox)) ->
           vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mox)) A (A + 262144) ->
           (forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mox) /\ elo e <= elo e' /\ ehi e' <= ehi e
                         /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + 262144 <= elo e'))) ->
           AKern E0 (st_fa c a1) mo').
        { intros mox mo' Kx MAPS WFN NOACC LAV.
          eapply (AKern_grow_fa E0 a1 (st_fa c a1) mox mo' A 262144 Kx WE MAPS ltac:(clear -HA1; lia) ltac:(clear; lia) WFN NOACC LAV
                    ltac:(destruct a1; reflexivity) ltac:(destruct a1; reflexivity) ltac:(destruct a1; reflexivity) c HC).
          - subst A. rewrite Emfa1. reflexivity.
          - rewrite Emfa1. exact R5.
          - rewrite st_fa_region. cbn [rg_mapped_fa]. reflexivity.
          - rewrite st_fa_region. cbn [rg_mapped_user]. reflexivity.
          - intros c' Hc' NE. apply st_fa_other. clear -NE. lia.
          - destruct a1; reflexivity.
          - rewrite Emfa1. unfold kRegionSize, kFreeArrayOffset. clear -GROW TFS. lia. }
        destruct (commit_ks a1 (st_fa c a1) mo2 R R' A 262144 ATK2 AK2 HA3 eq_refl ltac:(clear; lia) ltac:(unfold kFreeArrayMapSize in LR; exact LR)
                    ltac:(clear -HA1; lia) ltac:(unfold kSpaceSize in HA2, SB3; clear -HA2 SB3; lia) SITE
                    (a_eager_bytes_st_fa E0 c a1 HC30)
                    ltac:(destruct a1; reflexivity) ltac:(destruct a1; reflexivity) ltac:(destruct a1; reflexivity) ltac:(destruct a1; reflexivity)
                    GROWFA moK AGK KIAK) as (NU & GR & ALL).
        split; [exact NU|]. split; [exact GR|].
        intros eff mo' HC' NR. destruct (ALL eff mo' HC' NR) as (-> & ATK' & AK' & LZ & ES & FSK).
        exists (Z_to_bv 64 A, true).
        split. { replace (mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 262144)] [] [] []) with (zshape A 262144 (Z_to_bv 64 A) true)
                   by (unfold zshape; rewrite mmap_len_alignedA by reflexivity; reflexivity). apply dec_zs_zshape. }
        exists (aSc (sA (st_fa c a1) s)), (aNc (sA (st_fa c a1) s)), (aEBc (sA (st_fa c a1) s)).
        split; [exact (proj1 (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK'))|].
        pose proof (magree_frame _ _ AGK) as (FfdsK & FvmK & FlzK & FfsK & FhK & FtidK & _).
        split. { intros x Hx. unfold P2, PP in Hx. apply LZ. rewrite FlzK, Flz2. eapply acc_ok_lazy_sub; [| exact ES| exact Hx]. intros e' He'; exists e'; split; [exact He'| clear; lia]. }
        intros ms3 mo3 HQ AG3 KIA3 POL3.
        destruct HQ as (r' & u' & m3 & ESK & MU3 & WM3 & MI3 & ST3 & ZB3 & HR).
        injection HR as <- <-.
        assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
        assert (RRV : rar_ret (Z_to_bv 64 A) = true) by (unfold rar_ret, is_err; rewrite UA; apply andb_true_intro; split; apply negb_true_iff; [apply Z.ltb_ge| apply Z.eqb_neq]; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
        assert (IE : is_err (Z_to_bv 64 A) = false) by (unfold is_err; rewrite UA; apply Z.ltb_ge; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
        destruct (ESK RRV) as ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & E) & SK3). clear ESK. subst ms3. specialize (ZB3 eq_refl). unfold rar_W in MU3. rewrite USP112 in MU3, SK3.
        rewrite mmap_len_alignedA in MU3, ZB3 by reflexivity.
        replace (ret_pc (Z_to_bv 64 A_EFA_MMRET)) with (Z_to_bv 64 A_EFA_MMRET) by (symmetry; apply ret_pc_even; [unfold A_EFA_MMRET; clear; lia| reflexivity]).
        pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
        set (a2 := st_fa c a1) in *.
        pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK' AG3 KIA3) as ATK3.
        pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK') as AK3.
        assert (GR2 : gapR a2 = gapR a1 - 262144) by (subst a2; rewrite (gapR_st_fa E0 c a1 HC30); reflexivity).
        assert (GD2 : gapD a2 = gapD a1) by (subst a2; destruct a1; reflexivity).
        assert (GP2 : gapP a2 = gapP a1) by (subst a2; destruct a1; reflexivity).
        assert (TOK3 : RTOKc C C' (sA a2 s) mo3).
        { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 C C' (sA a2 s) mo3 (R - 262144 / 4096) R' ATK3); cbn [aps_alloc sA aps_set_alloc];
            cbn [aps_alloc sA aps_set_alloc] in GLE, GD0, GP0; rewrite ?GR2, ?GD2, ?GP2; unfold kFreeArrayMapSize in RR1; clear -HCR HCR' GLE GD0 GP0 RR1; lia. }
        (* [comment removed for export] *)
        set (P3 := PP (sA a2 s) mo3).
        assert (KIP3 : KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 mo3) by (split; [exact KIA3| intros x Hx; exact Hx]).
        assert (AK3s : AKern E0 (aps_alloc (sA a2 s)) mo3) by exact AK3.
        assert (PSTK3 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV0); clear -H1 H2 LOC SPH CEILB; lia. }
        assert (PDAT3 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV ENV0); clear -H1 H2; lia. }
        assert (PRIR3 : forall x k, RIc <= x -> x + Z.of_nat k <= RIc + 128 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a2 s) mo3 WE); unfold BF_popdefs.RIc in H1, H2; rewrite HRI in H1, H2;
            change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
        assert (PSH3 : forall x k, kShadowBase + A / 8 <= x -> x + Z.of_nat k <= kShadowBase + A / 8 + 32768 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, PP. apply (pol_space_shadow' E0 FSB0 HR0 (sA a2 s) mo3 WE); unfold kShadowBase in H1, H2; rewrite A_SB_val;
            change kSpaceSize with (2^37) in HA2; clear -H1 H2 HA1 HA2 SB1 HC30 R5; subst A; Z.div_mod_to_equations; lia. }
        destruct thr_facts as (PLT & PLC & HTC & TRS & CRS & (c0' & cl' & CR & CC1 & CC2)). pose proof T_app as TAPP.
        assert (PCTX3 : P3 (Z_to_bv 64 (CTX + 152), 8%nat)).
        { unfold P3, PP. apply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo3 AK3s c0' cl' _ _ CR); clear -CC1 CC2; cbn; lia. }
        assert (PT3 : forall x k, T <= x -> x + Z.of_nat k <= T + 4096 -> P3 (Z_to_bv 64 x, k)).
        { intros x k H1 H2. unfold P3, PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE); assumption. }
        assert (WZ3 : WZ [(usp - 64 + -48 - 400, usp - 64 + -48); (A, A + 262144)]).
        { unfold WZ. wz_split; [left; clear -LO; lia| right; left; unfold kSpaceSize in HA2 |- *; clear -HA1 HA2 SB1 R5 HC30; subst A; lia]. }
        (* [comment removed for export] *)
        assert (EFR3 : efa_frame_gen m3 (usp - 64) j (Z_to_bv 64 A_POP_EFARET) (Z_to_bv 64 RIc) (Z_to_bv 64 tf) (Z_to_bv 64 RB) (Z_to_bv 64 new)).
        { unfold efa_frame_gen in EFR |- *. eapply rw_cells_transport; [exact EFR| exact MU3| exact WM3| cbn [disjoint_from cells_size csize fst snd Nat.add]; clear -LO LOC HA1 SB3 HA2; unfold kSpaceSize in *; lia]. }
        assert (ROW2 : rw_cells bsegs m2 RIc (ri_cells (2 ^ 60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user (get_region a1 c)) (rg_n_allocated r) (rg_n_freed r))).
        { eapply rw_cells_transport; [exact ROW1| exact MU12| exact WM12| unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]; unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -LOC LO HSB CEILB HC30; lia]. }
        assert (ROW3 : rw_cells bsegs m3 RIc (ri_cells (2 ^ 60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user (get_region a1 c)) (rg_n_allocated r) (rg_n_freed r))).
        { eapply rw_cells_transport; [exact ROW2| exact MU3| exact WM3| unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]; unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -LOC LO HSB CEILB HC30 HA1 HA2; lia]. }
        pose proof (WZ_statics _ m1 m2 WZ2 MU12 WM12 PST1) as PST2. pose proof (WZ_statics _ m2 m3 WZ3 MU3 WM3 PST2) as PST3.
        pose proof (WZ_thread_cells _ m1 m2 WZ2 MU12 TCm1) as TCm2. pose proof (WZ_thread_cells _ m2 m3 WZ3 MU3 TCm2) as TCm3.
        assert (SHF3 : rw_cells bsegs m3 (kShadowBase + A / 8) [CB (Z.to_nat 32768) fshj]).
        { subst A. eapply rw_cells_transport; [eapply rw_cells_transport; [exact SHF1| exact MU12| exact WM12|]| exact MU3| exact WM3|];
            cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kShadowBase; unfold kSpaceSize in *; rewrite KHB in HSBH; clear -LOC LO HSB HSBH CEILB HC30 HA1 HA2 R5;
            rewrite ?Nat.add_0_r, ?(Z2Nat.id 32768) by (clear; lia); repeat split; Z.div_mod_to_equations; lia. }
        assert (TST3 : rw_cells bsegs m3 (T + 2872) [C8 (Z_to_bv 64 ((ts_mmaps (as_ts a1)) mod 2^64)); C8 (Z_to_bv 64 ((ts_mmaped (as_ts a1)) mod 2^64))]).
        { rewrite !wz_mod. unfold kThrStats in TST1. replace (T + 2800 + 72) with (T + 2872) in TST1 by (clear; lia).
          eapply rw_cells_transport; [eapply rw_cells_transport; [exact TST1| exact MU12| exact WM12|]| exact MU3| exact WM3|];
            cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kSpaceSize in *; clear -LOC LO WE15 TRS HA1 HA2 HC30 R5; subst A; lia. }
        assert (SHU3 : rw_cells bsegs m3 (kShadowBase + (RB + rg_mapped_user r) / 8)
                 [CB (Z.to_nat ((rg_mapped_user (get_region a1 c) - rg_mapped_user r) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((rg_mapped_user (get_region a1 c) - rg_mapped_user r) / 8)))]).
        { assert (W8 : 0 <= (rg_mapped_user (get_region a1 c) - rg_mapped_user r) / 8) by (apply Z.div_pos; clear -MU1K; lia).
          eapply rw_cells_transport; [eapply rw_cells_transport; [exact SHUP1| exact MU12| exact WM12|]| exact MU3| exact WM3|];
            cbn [disjoint_from cells_size csize fst snd Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by exact W8;
            unfold kShadowBase, kUserMapSize in *; unfold kSpaceSize in *; rewrite KHB in HSBH; clear -LOC LO HSB HSBH CEILB HC30 MU1K MU1 R1 R5 HA1 HA2 W8; subst A; repeat split; Z.div_mod_to_equations; lia. }
        (* [comment removed for export] *)
        set (QK3 := fun ms' => forall mo'', magree mo3 mo'' -> KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 mo'' -> realizes_cfg acfg bsegs (mkCfg ms' mo'') K).
        eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 QK3); [| exact KIP3| intros ms' mo'' HQ AG KP; exact (HQ mo'' AG KP)].
        subst A.
        eapply (efa_grow_ok_gen P3 gp tpw F fc lo SB c RI LOC HSB HSBH HC HRI PDAT3 PRIR3 m3 (Z_to_bv 64 A_POP_EFARET) (usp - 64)
                  v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 RIc) (Z_to_bv 64 tf) (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 (rg_mapped_user (get_region a1 c) - rg_alloc_user r)) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 v3 v4 v5 v6
                  (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user (get_region a1 c)) (rg_n_allocated r) (rg_n_freed r) (2^60) j fshj
                  0x6028f8 CTX T ((ts_mmaps (as_ts a1)) mod 2^64) ((ts_mmaped (as_ts a1)) mod 2^64) QK3 MI3 SK3).
        -- clear -LO. lia.
        -- clear -SPH. lia.
        -- clear -SPA. Z.div_mod_to_equations. lia.
        -- intros x k H1 H2. apply PSTK3; [exact H1| clear -H2; lia].
        -- exact EFR3.
        -- exact ROW3.
        -- exact R5.
        -- clear -R6. unfold kFreeArrayMapSize in R6. exact R6.
        -- clear -GROW TFS. lia.
        -- exact (proj2 PST3).
        -- exact SHF3.
        -- exact PSH3.
        -- exact TCm3.
        -- clear; lia.
        -- clear; lia.
        -- exact PLC.
        -- exact PLT.
        -- rewrite unsigned_lit by (clear; lia). clear; lia.
        -- exact HTC.
        -- exact TRS.
        -- exact CRS.
        -- exact PCTX3.
        -- exact PT3.
        -- exact TST3.
        -- apply Z.mod_pos_bound. clear; lia.
        -- apply Z.mod_pos_bound. clear; lia.
        -- (* [comment removed for export] *)
           intros m4 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 MI4 SK4 MU4 WM4 ROW4 PG4 SHFP4 TCm4 TST4. apply evtA_done. intros mo4 AG4 KP4.
           pose proof (magree_frame _ _ AG4) as (Ffds4 & Fvm4 & Flz4 & Ffs4 & Fh4 & Ftid4 & _).
           rewrite ?USP112 in *. replace (ret_pc (Z_to_bv 64 A_POP_EFARET)) with (Z_to_bv 64 A_POP_EFARET) by (symmetry; apply ret_pc_even; [unfold A_POP_EFARET; clear; lia| reflexivity]).
           assert (WZ4 : WZ [(usp - 64 - 112, usp - 64); (kShadowBase + (FA + rg_mapped_fa r) / 8, kShadowBase + (FA + rg_mapped_fa r) / 8 + 32768); (T + 2872, T + 2888); (RIc + 24, RIc + 32)]).
           { unfold WZ, BF_popdefs.RIc. rewrite HRI. unfold kShadowBase, kSpaceSize. unfold kSpaceSize in HA2. wz_split.
             - left. clear -LO. lia.
             - right; right; left. clear -HA1 HA2 SB1 HC30 R5. Z.div_mod_to_equations. lia.
             - right; right; right. clear. lia.
             - right; left. clear -HC30. lia. }
           assert (RG2 : get_region a2 c = mkRegion (rg_mapped_user (get_region a1 c)) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r + kFreeArrayMapSize) (rg_n_allocated r) (rg_n_freed r)).
           { subst a2. rewrite st_fa_region. cbv zeta. rewrite Eau, Efr, Emfa1, Ena, Enf. reflexivity. }
           assert (PTF : pop_tf c a1 = tf) by (unfold pop_tf, rg_num_freed; cbv zeta; rewrite Eau, Efr; subst tf new; reflexivity).
           (* [comment removed for export] *)
           assert (FAR2 : u32arr bsegs m2 FA (map (fun z => Z_to_bv 64 z) (rg_free r) ++ fjunk)).
           { eapply u32arr_transport; [exact FAR1| exact MU12| exact WM12|]. cbn [disjoint_from fst snd]. rewrite length_app, length_map. unfold zlen in FAL.
             unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. unfold kSpaceSize in HSB. clear -LOC LO HSB CEILB HC30 FAL R7. lia. }
           assert (FAR3 : u32arr bsegs m3 FA ((map (fun z => Z_to_bv 64 z) (rg_free r) ++ fjunk) ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536))).
           { apply u32arr_app.
             - eapply u32arr_transport; [exact FAR2| exact MU3| exact WM3|]. cbn [disjoint_from fst snd]. rewrite length_app, length_map. unfold zlen in FAL.
               unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. unfold kSpaceSize in HSB. clear -LOC LO HSB CEILB HC30 FAL R7. lia.
             - rewrite length_app, length_map. unfold zlen in FAL. replace (FA + 4 * Z.of_nat (length (rg_free r) + length fjunk)%nat) with (FA + rg_mapped_fa r) by (clear -FAL; lia).
               apply (u32arr_of_zeros m3 _ 262144 65536); [exact ZB3| reflexivity| clear; lia]. }
           assert (FAR4 : u32arr bsegs m4 FA (map (fun z => Z_to_bv 64 z) (rg_free r) ++ (fjunk ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)))).
           { rewrite app_assoc. eapply u32arr_transport; [exact FAR3| exact MU4| exact WM4|]. cbn [disjoint_from fst snd]. rewrite !length_app, length_map, repeat_length. unfold zlen in FAL.
             unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. unfold BF_popdefs.RIc. rewrite HRI. unfold kShadowBase. unfold kSpaceSize in *. rewrite KHB in HSBH.
             clear -LOC LO HSB HSBH CEILB HC30 FAL R7 R5 TRS WE15. repeat split; try exact I; Z.div_mod_to_equations; lia. }
           subst tf new. replace (rg_mapped_user (get_region a1 c)) with (rg_mapped_user (get_region a2 c)) by (rewrite RG2; reflexivity).
           eapply (pop_phaseE a2 m4 mo4 (fjunk ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536))); rewrite ?RG2; cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
           ++ exact (AKern_frame _ _ _ _ Fvm4 Flz4 AK3).
           ++ eapply RTOK_magree; [exact TOK3| exact AG4| exact (proj1 KP4)].
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ clear -MU1K MU1. lia.
           ++ unfold kFreeArrayMapSize. clear. lia.
           ++ unfold kFreeArrayMapSize. clear -TF1. lia.
           ++ unfold kFreeArrayMapSize. clear -GROW TFS. lia.
           ++ intros c' Hc' NE. subst a2. rewrite st_fa_other by (clear -NE; lia). apply OTH1. clear -NE. lia.
           ++ eapply pop_same_trans; [exact PS1| subst a2; apply pop_same_fa].
           ++ destruct (phase2_true E0 c a1 1%nat [AnsOk (FA + rg_mapped_fa r)] (st_fa c a1) true [AEvMmap (FA + rg_mapped_fa r) kFreeArrayMapSize kProtRw kFlagsFixedRw] []) as [f2 RUN2].
             { rewrite <- Emfa1. apply (efa_run_grant E0 c a1); rewrite ?Emfa1, ?PTF; [exact R5| exact R6| unfold kFreeArrayMapSize; exact TF1| unfold kFreeArrayMapSize, kFreeArraySize, kRegionSize, kFreeArrayOffset; clear -GROW TFS; lia| clear -GROW; lia]. }
             { subst a2; rewrite st_fa_region; reflexivity. }
             { subst a2; rewrite st_fa_region; reflexivity. }
             destruct (pop_run E0 c req a f1 f2 (o1 ++ [AnsOk (FA + rg_mapped_fa r)]) a1 true evs1 [AnsOk (FA + rg_mapped_fa r)] (st_fin c (st_fa c a1)) (ONorm true) _ [] (PH1 _) RUN2) as [f RUN].
             subst a2. eexists f, _, _, []. exact RUN.
           ++ rewrite Ffs4, Ffds4, Ftid4, Ffs3, Ffds3, Ftid3. destruct FSK as (K1 & K2 & K3). rewrite K1, K2, K3.
             rewrite FfsK, FfdsK, FtidK, Ffs2, Ffds2, Ftid2. exact FS1.
           ++ exact MI4.
           ++ exact SK4.
           ++ eapply rw_cells_transport; [| exact MU4| exact WM4| unfold BF_pop1.pop_frame; cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold BF_popdefs.RIc; rewrite HRI; unfold kShadowBase, kSpaceSize; unfold kSpaceSize in HSB; rewrite KHB in HSBH; unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7; clear -LO LOC HSB HSBH CEILB HC30 R5 R7 WE15; repeat split; try exact I; Z.div_mod_to_equations; lia].
             eapply rw_cells_transport; [| exact MU3| exact WM3| unfold BF_pop1.pop_frame; cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kSpaceSize in HA2, HSB; clear -LO LOC HA1 HA2 HSB; lia].
             eapply rw_cells_transport; [exact FR1| exact MU12| exact WM12| unfold BF_pop1.pop_frame; cbn [disjoint_from cells_size csize fst snd Nat.add]; clear; lia].
           ++ unfold kFreeArrayMapSize. exact ROW4.
           ++ eapply (WZ_ins _ m3 m4); [exact WZ4| exact MU4| | eapply (WZ_ins _ m2 m3); [exact WZ3| exact MU3| | eapply (WZ_ins _ m1 m2); [exact WZ2| exact MU12| | exact INS1]]]; cbn [cells_size csize Nat.add]; clear; lia.
           ++ eapply wr_at_transport; [| exact WM4]. eapply wr_at_transport; [| exact WM3]. eapply wr_at_transport; [exact WRU1| exact WM12].
           ++ exact FAR4.
           ++ unfold zlen in FAL |- *. rewrite length_app, repeat_length. unfold kFreeArrayMapSize. clear -FAL. lia.
           ++ subst a2. rewrite st_fa_ts. cbn [ts_mmaps ts_mmaped ts_on_mmap]. unfold kThrStats. replace (T + 2800 + 72) with (T + 2872) by (clear; lia).
             rewrite <- (wz_mod_add (ts_mmaps (as_ts a1)) 1), <- (wz_mod_add (ts_mmaped (as_ts a1)) kFreeArrayMapSize). unfold kFreeArrayMapSize. exact TST4.
           ++ subst a2. rewrite st_fa_cm.
             eapply rw_cells_transport; [| exact MU4| exact WM4| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold BF_popdefs.RIc; rewrite HRI; unfold kShadowBase, kSpaceSize, kThrCacheStats; unfold kSpaceSize in HSB, TRS; rewrite KHB in HSBH; unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7; clear -LO LOC HSB HSBH CEILB HC30 R5 R7 TRS WE15 TAPP; repeat split; try exact I; Z.div_mod_to_equations; lia].
             eapply rw_cells_transport; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrCacheStats; unfold kSpaceSize in *; clear -LOC LO WE15 TRS HA1 HA2 HC30 R5; lia].
             eapply rw_cells_transport; [exact CST1| exact MU12| exact WM12| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrCacheStats; clear -LOC LO WE15; lia].
           ++ exact TCm4.
           ++ split; [| exact PG4]. exact (proj1 (WZ_statics _ m3 m4 WZ4 MU4 WM4 PST3)).
           ++ exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 (wmono_trans _ _ _ _ WM3 WM4))).
           ++ (* [comment removed for export] *)
             unfold pop_W in MU01 |- *. cbv zeta in MU01. cbv zeta. rewrite RG2. cbn [rg_mapped_user rg_mapped_fa].
             unfold K_POP, free_array in MU01 |- *. unfold region_beg in MU01 |- *. change kRegionSize with 4294967296 in MU01 |- *. change kFreeArrayOffset with 3758096384 in MU01 |- *.
             change kRegSize with 128 in MU01 |- *. change (RI + 128 * c) with RIc in MU01 |- *.
             pose proof R8 as R8'. unfold rg_num_freed in R8'. rewrite ?Emfa1 in MU01.
             eapply munch_trans; [eapply munch_cover; [exact MU01|]| eapply munch_trans; [eapply munch_cover; [exact MU12|]| eapply munch_trans; [eapply munch_cover; [exact MU3|]| eapply munch_cover; [exact MU4|]]]];
               unfold BF_popdefs.RIc, kFreeArrayMapSize, kThrStats, kThrCacheStats, zlen; clear -MU1K R5 R8' HC30; solve_covers.
           ++ eapply rw_cells_transport; [| exact MU4| exact WM4|].
             2:{ cbn [disjoint_from cells_size csize fst snd Nat.add]. assert (W8 : 0 <= (rg_mapped_user (get_region a1 c) - rg_mapped_user r) / 8) by (apply Z.div_pos; clear -MU1K; lia).
                 rewrite ?Nat.add_0_r, ?Z2Nat.id by exact W8. unfold BF_popdefs.RIc; rewrite HRI; unfold kShadowBase, kSpaceSize, kUserMapSize in *; rewrite KHB in HSBH.
                 clear -LOC LO HSB HSBH CEILB HC30 MU1K MU1 R1 R5 W8 WE15 TRS TAPP. repeat split; try exact I; Z.div_mod_to_equations; lia. }
             exact SHU3.
           ++ replace (rg_mapped_fa r + kFreeArrayMapSize - rg_mapped_fa r) with kFreeArrayMapSize by (clear; lia). change (kFreeArrayMapSize / 8) with 32768. exact SHFP4.
Qed.

Lemma pop_main :
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (Z_to_bv 64 usp) gp tpw t0 t1 t2 s0 s1 (Z_to_bv 64 A_INST) (Z_to_bv 64 (T + kThrCacheStats)) (Z_to_bv 64 c) (Z_to_bv 64 (RI + kRegSize * c)) (Z_to_bv 64 req) a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 A_POPULATE) fc None m (seg_rom bsegs)) mo) K.
Proof.
  facts.
  (* [comment removed for export] *)
  set (P1 := PP s mo).
  assert (PSTK1 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P1 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P1, PP. apply (pol_stack E0 FSB0 HR0 s mo Pq Dq AK WF ENV0); clear -H1 H2 LOC SPH CEILB; lia. }
  assert (PDAT1 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P1 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P1, PP. apply (pol_img E0 FSB0 HR0 s mo Pq Dq AK WF ENV ENV0); clear -H1 H2; lia. }
  assert (PRIR1 : forall x k, RIc <= x -> x + Z.of_nat k <= RIc + 128 -> P1 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P1, PP. apply (pol_reginfo E0 FSB0 HR0 s mo Pq Dq WF); unfold BF_popdefs.RIc in H1, H2; rewrite HRI in H1, H2;
      change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
  (* [comment removed for export] *)
  destruct (RTOK_elim_roomR _ _ _ _ _ _ _ _ _ _ kUserMapSize TOK ltac:(revert RR; clear; unfold kUserMapSize, kFreeArrayMapSize; intros RR; lia)) as (R0 & R0' & TOK0 & HCR & HCR' & LR & GD0 & GP0 & GLE).
  assert (KIP0 : KIP (aSc s) (aNc s) (aEBc s) P1 mo) by (split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK0)| intros x Hx; exact Hx]).
  (* [comment removed for export] *)
  set (QK := fun ms' => forall mo', magree mo mo' -> KIP (aSc s) (aNc s) (aEBc s) P1 mo' -> realizes_cfg acfg bsegs (mkCfg ms' mo') K).
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P1 QK); [| exact KIP0| intros ms' mo' HQ AG KP; exact (HQ mo' AG KP)].
  unfold A_POPULATE. change kRegSize with 128. change (RI + 128 * c) with RIc.
  eapply (pop_pre P1 gp _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo SB c RI STAT req LOC LO SPH SPA HSB HC HRI HREQ PSTK1 PDAT1 PRIR1
            ra s0 s1 s2 s3 s4 s5 s6 t0 t1 t2 a5 a6 a7 m (2^60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (rg_n_freed r) QK
            SK MI INS ROW ltac:(clear -R1; lia) MUA MUR).
  - (* [comment removed for export] *)
    intros m1 a5' a6' NG MI1 SK1 MU1 WM1 FR1. apply evtA_done. intros mo1 AG1 KP1.
    pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
    assert (WZ1 : WZ [(usp - 64, usp)]) by (unfold WZ; wz_split; left; clear -LO; lia).
    pose proof WE as WE'. wfe_open WE'.
    eapply (pop_phaseD a m1 mo1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%nat [] []).
    + exact (AKern_frame _ _ _ _ Fvm1 Flz1 AK).
    + rewrite sA_self. eapply RTOK_magree; [exact TOK| exact AG1| exact (proj1 KP1)].
    + clear -RR. unfold kUserMapSize, kFreeArrayMapSize in *. lia.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + intros c' _. reflexivity.
    + apply pop_same_refl.
    + exact NG.
    + clear. unfold kUserMapSize. lia.
    + clear -MUR. lia.
    + intros orc. exact (run_phase1_nogrow E0 c req a NG orc).
    + rewrite Ffs1, Ffds1, Ftid1. split; [reflexivity| split; reflexivity].
    + exact MI1.
    + exact SK1.
    + exact FR1.
    + eapply rw_cells_transport; [exact ROW| exact MU1| exact WM1| unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]; unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -LOC LO HSB CEILB HC30; lia].
    + eapply (WZ_ins _ m m1); [exact WZ1| exact MU1| | exact INS]. cbn [cells_size csize Nat.add]. clear. lia.
    + eapply wr_at_transport; [exact WRU| exact WM1].
    + eapply u32arr_transport; [exact FAR| exact MU1| exact WM1|]. cbn [disjoint_from fst snd]. rewrite length_app, length_map. unfold zlen in FAL.
      unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. unfold kSpaceSize in HSB. clear -LOC LO HSB CEILB HC30 FAL R7. lia.
    + eapply rw_cells_transport; [exact SHF| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize fst snd Nat.add]. rewrite ?Nat.add_0_r, ?(Z2Nat.id 32768) by (clear; lia).
      unfold kShadowBase. unfold kSpaceSize in *. rewrite KHB in HSBH. unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7. clear -LOC LO HSB HSBH CEILB HC30 R5 R7. Z.div_mod_to_equations. lia.
    + eapply rw_cells_transport; [exact TST| exact MU1| exact WM1| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrStats; clear -LOC LO WE15; lia].
    + eapply rw_cells_transport; [exact CST| exact MU1| exact WM1| cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrCacheStats; clear -LOC LO WE15; lia].
    + exact (WZ_thread_cells _ m m1 WZ1 MU1 TC).
    + exact (WZ_statics _ m m1 WZ1 MU1 WM1 PST).
    + exact WM1.
    + eapply munch_cover; [exact MU1|]. unfold pop_W, K_POP. cbv zeta. clear -LO. solve_covers.
    + replace ((rg_mapped_user r - rg_mapped_user r) / 8) with 0 by (rewrite Z.sub_diag; reflexivity). cbn [Z.to_nat repeat].
      apply rw_cells_CB0; unfold kShadowBase; unfold kSpaceSize in HSB; clear -HSB HC30 R1 MUR CEILB; Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *)
    intros m1 a5' a6' GR MI1 SK1 MU1 WM1 FR1. apply evtA_done. intros mo1 AG1 KP1.
    pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK0 AG1 (proj1 KP1)) as ATK1.
    assert (ATK1s : ATOKc R0 R0' (sA a s) mo1) by (rewrite sA_self; exact ATK1).
    pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 AK) as AK1.
    assert (WZ1 : WZ [(usp - 64, usp)]) by (unfold WZ; wz_split; left; clear -LO; lia).
    pose proof WE as WE'. wfe_open WE'.
    pose proof (proj2 (class_size_mod c HC30)) as CS.
    assert (RSZ : req * size <= 65536).
    { pose proof (hint_size_bound c HC30) as [HS _]. assert (RS : req * size <= hint c * size) by (apply Z.mul_le_mono_nonneg_r; clear -HREQ CS; lia). clear -HS RS. lia. }
    set (A := RB + rg_mapped_user r) in *.
    assert (HA : 0x603000 <= A /\ A + 262144 <= SB + kSpaceSize /\ A mod 4096 = 0).
    { subst A. unfold kSpaceSize. clear -HSB HC30 R1 MUA MUR. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
    destruct HA as (HA1 & HA2 & HA3). pose proof HSB as (SB1 & SB2 & SB3).
    (* [comment removed for export] *)
    assert (USP64 : bv_unsigned (Z_to_bv 64 (usp - 64)) = usp - 64) by (apply unsigned_lit; clear -LO LOC CEILB SPH; lia).
    eapply (rzA_mm_cfg bsegs (aSc s) (aNc s) (aEBc s) P1 (NMmap A 262144 3 MAP_FIXED_RW) (mmap_CHK A 262144 3 MAP_FIXED_RW) (dec_zs A 262144)
              (rar_map_gen_post (fun x r u => x = (r, u)) (Z_to_bv 64 A_POP_MMRET) (Z_to_bv 64 (usp - 64)) gp tpw
                 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT) (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 F fc A 262144 lo m1)
              _ mo1 K).
    * apply mm_node_mmap.
    * left. reflexivity.
    * eapply (rar_map_gen_specA P1 PDAT1 (dec_zs A 262144) (fun x r u => x = (r, u))); rewrite ?USP64;   (* [comment removed for export] *)
        [ intros rsp x D; destruct (dec_zs_Some _ _ _ _ D) as (r' & u' & -> & ->); exists r', u'; split; reflexivity
        | exact SK1 | exact LOC | clear -LO; lia | clear -SPH; lia | exact MI1 | exact (proj1 (WZ_statics _ m m1 WZ1 MU1 WM1 PST))
        | reflexivity | reflexivity | exact HA3 | reflexivity
        | unfold b_image_end; exact HA1 | clear; lia | rewrite mmap_len_alignedA by reflexivity; unfold kSpaceSize in HA2, SB3; clear -HA2 SB3 LOC; lia
        | intros x k H1 H2; apply PSTK1; [exact H1| clear -H2; lia] ].
    * exact KP1.
    * exact KN.
    * intros moK AGK KIAK.
      assert (SITE : commit_site E0 a A 262144).
      { left. unfold kResvLen, kPtrArrayLen, kPtrArrayCommit. unfold kSpaceSize in HA2, E4. split; [clear -E3 R1 HC30; subst A; lia|].
        split; [clear -HA2 E4; lia|]. destruct (as_ptr_committed a =? 0); clear -WE20 HA2 E3 E4 R1 HC30; subst A; lia. }
      assert (GROWU : forall mox mo', AKern E0 a mox -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mox) -> ivs_wf (vm_noaccess (m_vmmaps mox)) ->
         vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mox)) A (A + 262144) ->
         (forall e', In e' (m_vm_lazy mo') -> exists e, In e (m_vm_lazy mox) /\ elo e <= elo e' /\ ehi e' <= ehi e
                       /\ ((elo e' = elo e /\ elo e' < A /\ ehi e' <= A) \/ (ehi e' = ehi e /\ A + 262144 <= elo e'))) ->
         AKern E0 (st_user c a) mo').
      { intros mox mo' Kx MAPS WFN NOACC LAV.
        eapply (AKern_grow_user E0 a (st_user c a) mox mo' A 262144 Kx WE MAPS ltac:(clear -HA1; lia) ltac:(clear; lia) WFN NOACC LAV
                  ltac:(destruct a; reflexivity) ltac:(destruct a; reflexivity) ltac:(destruct a; reflexivity) c HC).
        - subst A. reflexivity.
        - clear -R1. lia.
        - rewrite st_user_region. cbn [rg_mapped_user]. reflexivity.
        - rewrite st_user_region. cbn [rg_mapped_fa]. reflexivity.
        - intros c' Hc' NE. apply st_user_other. clear -NE. lia.
        - destruct a; reflexivity.
        - exact R700. }
      destruct (commit_ks a (st_user c a) mo1 R0 R0' A 262144 ATK1s AK1 HA3 eq_refl ltac:(clear; lia) ltac:(unfold kUserMapSize in LR; exact LR)
                  ltac:(clear -HA1; lia) ltac:(unfold kSpaceSize in HA2, SB3; clear -HA2 SB3; lia) SITE
                  (a_eager_bytes_st_user E0 c a HC30)
                  ltac:(destruct a; reflexivity) ltac:(destruct a; reflexivity) ltac:(destruct a; reflexivity) ltac:(destruct a; reflexivity)
                  GROWU moK AGK KIAK) as (NU & GRT & ALL).
      split; [exact NU|]. split; [exact GRT|].
      intros eff mo' HC' NR. destruct (ALL eff mo' HC' NR) as (-> & ATK' & AK' & LZ & ES & FSK).
      exists (Z_to_bv 64 A, true).
      split. { replace (mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 262144)] [] [] []) with (zshape A 262144 (Z_to_bv 64 A) true)
                 by (unfold zshape; rewrite mmap_len_alignedA by reflexivity; reflexivity). apply dec_zs_zshape. }
      exists (aSc (sA (st_user c a) s)), (aNc (sA (st_user c a) s)), (aEBc (sA (st_user c a) s)).
      split; [exact (proj1 (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK'))|].
      pose proof (magree_frame _ _ AGK) as (FfdsK & FvmK & FlzK & FfsK & FhK & FtidK & _).
      split. { intros x Hx. unfold P1, PP in Hx. apply LZ. rewrite FlzK, Flz1. eapply acc_ok_lazy_sub; [| exact ES| exact Hx]. intros e' He'; exists e'; split; [exact He'| clear; lia]. }
      intros ms3 mo3 HQ AG3 KIA3 POL3.
      destruct HQ as (r' & u' & m3 & ESK & MU3 & WM3 & MI3 & ST3 & ZB3 & HR).
      injection HR as <- <-.
      assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
      assert (RRV : rar_ret (Z_to_bv 64 A) = true) by (unfold rar_ret, is_err; rewrite UA; apply andb_true_intro; split; apply negb_true_iff; [apply Z.ltb_ge| apply Z.eqb_neq]; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
      assert (IE : is_err (Z_to_bv 64 A) = false) by (unfold is_err; rewrite UA; apply Z.ltb_ge; unfold kSpaceSize in HA2, SB3; clear -HA1 HA2 SB3 CEILB; lia).
      destruct (ESK RRV) as ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & E) & SK3). clear ESK. subst ms3. specialize (ZB3 eq_refl). unfold rar_W in MU3. rewrite USP64 in MU3, SK3.
      rewrite mmap_len_alignedA in MU3, ZB3 by reflexivity.
      replace (ret_pc (Z_to_bv 64 A_POP_MMRET)) with (Z_to_bv 64 A_POP_MMRET) by (symmetry; apply ret_pc_even; [unfold A_POP_MMRET; clear; lia| reflexivity]).
      pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
      set (a2 := st_user c a) in *.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK' AG3 KIA3) as ATK3.
      pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK') as AK3.
      assert (GR2 : gapR a2 = gapR a - 262144) by (subst a2; rewrite (gapR_st_user E0 c a HC30); reflexivity).
      assert (GD2 : gapD a2 = gapD a) by (subst a2; destruct a; reflexivity).
      assert (GP2 : gapP a2 = gapP a) by (subst a2; destruct a; reflexivity).
      assert (TOK3 : RTOKc C C' (sA a2 s) mo3).
      { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 C C' (sA a2 s) mo3 (R0 - 262144 / 4096) R0' ATK3); cbn [aps_alloc sA aps_set_alloc];
          rewrite ?GR2, ?GD2, ?GP2; unfold kUserMapSize, kFreeArrayMapSize in RR; clear -HCR HCR' GLE GD0 GP0 RR; lia. }
      (* [comment removed for export] *)
      set (P3 := PP (sA a2 s) mo3).
      assert (KIP3 : KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 mo3) by (split; [exact KIA3| intros x Hx; exact Hx]).
      assert (AK3s : AKern E0 (aps_alloc (sA a2 s)) mo3) by exact AK3.
      assert (PSTK3 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P3 (Z_to_bv 64 x, k)).
      { intros x k H1 H2. unfold P3, PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV0); clear -H1 H2 LOC SPH CEILB; lia. }
      assert (PDAT3 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P3 (Z_to_bv 64 x, k)).
      { intros x k H1 H2. unfold P3, PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE ENV ENV0); clear -H1 H2; lia. }
      assert (PRIR3 : forall x k, RIc <= x -> x + Z.of_nat k <= RIc + 128 -> P3 (Z_to_bv 64 x, k)).
      { intros x k H1 H2. unfold P3, PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a2 s) mo3 WE); unfold BF_popdefs.RIc in H1, H2; rewrite HRI in H1, H2;
          change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
      assert (PSH3 : forall x k, kShadowBase + A / 8 <= x -> x + Z.of_nat k <= kShadowBase + A / 8 + 32768 -> P3 (Z_to_bv 64 x, k)).
      { intros x k H1 H2. unfold P3, PP. apply (pol_space_shadow' E0 FSB0 HR0 (sA a2 s) mo3 WE); unfold kShadowBase in H1, H2; rewrite A_SB_val;
          change kSpaceSize with (2^37) in HA2; clear -H1 H2 HA1 HA2 SB1 HC30 R1; subst A; Z.div_mod_to_equations; lia. }
      destruct thr_facts as (PLT & PLC & HTC & TRS & CRS & (c0' & cl' & CR & CC1 & CC2)). pose proof T_app as TAPP.
      assert (PCTX3 : P3 (Z_to_bv 64 (CTX + 152), 8%nat)).
      { unfold P3, PP. apply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo3 AK3s c0' cl' _ _ CR); clear -CC1 CC2; cbn; lia. }
      assert (PT3 : forall x k, T <= x -> x + Z.of_nat k <= T + 4096 -> P3 (Z_to_bv 64 x, k)).
      { intros x k H1 H2. unfold P3, PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3s WE); assumption. }
      assert (WZ3 : WZ [(usp - 64 - 400, usp - 64); (A, A + 262144)]).
      { unfold WZ. wz_split; [left; clear -LO; lia| right; left; unfold kSpaceSize in HA2 |- *; clear -HA1 HA2 SB1 R1 HC30; subst A; lia]. }
      (* [comment removed for export] *)
      assert (FR3 : BF_pop1.pop_frame usp m3 ra s0 s1 s2 s3 s4 s5 s6).
      { eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3| unfold BF_pop1.pop_frame; cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kSpaceSize in HA2, HSB; clear -LO LOC HA1 HA2 HSB; lia]. }
      assert (ROW3 : rw_cells bsegs m3 RIc (ri_cells (2 ^ 60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (rg_n_freed r))).
      { eapply rw_cells_transport; [eapply rw_cells_transport; [exact ROW| exact MU1| exact WM1|]| exact MU3| exact WM3|];
          unfold ri_cells; cbn [disjoint_from cells_size csize fst snd Nat.add length]; unfold BF_popdefs.RIc; rewrite HRI; unfold kSpaceSize in *; clear -LOC LO HSB CEILB HC30 HA1 HA2; lia. }
      pose proof (WZ_statics _ m m1 WZ1 MU1 WM1 PST) as PST1. pose proof (WZ_statics _ m1 m3 WZ3 MU3 WM3 PST1) as PST3.
      pose proof (WZ_thread_cells _ m m1 WZ1 MU1 TC) as TCm1. pose proof (WZ_thread_cells _ m1 m3 WZ3 MU3 TCm1) as TCm3.
      assert (SHU3 : rw_cells bsegs m3 (kShadowBase + A / 8) [CB (Z.to_nat 32768) shj]).
      { eapply rw_cells_transport; [eapply rw_cells_transport; [exact SHU| exact MU1| exact WM1|]| exact MU3| exact WM3|];
          cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kShadowBase; unfold kSpaceSize in *; rewrite KHB in HSBH; clear -LOC LO HSB HSBH CEILB HC30 HA1 HA2 R1;
          rewrite ?Nat.add_0_r, ?(Z2Nat.id 32768) by (clear; lia); subst A; repeat split; Z.div_mod_to_equations; lia. }
      assert (TST3 : rw_cells bsegs m3 (T + 2872) [C8 (Z_to_bv 64 ((ts_mmaps (as_ts a)) mod 2^64)); C8 (Z_to_bv 64 ((ts_mmaped (as_ts a)) mod 2^64))]).
      { rewrite !wz_mod. pose proof TST as TST0. unfold kThrStats in TST0. replace (T + 2800 + 72) with (T + 2872) in TST0 by (clear; lia).
        eapply rw_cells_transport; [eapply rw_cells_transport; [exact TST0| exact MU1| exact WM1|]| exact MU3| exact WM3|];
          cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kSpaceSize in *; clear -LOC LO WE15 TRS HA1 HA2 HC30 R1; subst A; lia. }
      assert (CST3 : rw_cells bsegs m3 (STAT + 24) [C8 (Z_to_bv 64 ((as_cache_mapped a) mod 2^64))]).
      { rewrite !wz_mod. eapply rw_cells_transport; [eapply rw_cells_transport; [exact CST| exact MU1| exact WM1|]| exact MU3| exact WM3|];
          cbn [disjoint_from cells_size csize fst snd Nat.add]; unfold kThrCacheStats; unfold kSpaceSize in *; clear -LOC LO WE15 TRS HA1 HA2 HC30 R1; subst A; lia. }
      (* [comment removed for export] *)
      set (QK3 := fun ms' => forall mo'', magree mo3 mo'' -> KIP (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 mo'' -> realizes_cfg acfg bsegs (mkCfg ms' mo'') K).
      eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 QK3); [| exact KIP3| intros ms' mo'' HQ AG KP; exact (HQ mo'' AG KP)].
      subst A.
      eapply (pop_grow_ok P3 gp tpw s7 s8 s9 s10 s11 v3 v4 v5 v6 F fc usp lo SB c RI STAT req LOC LO SPH SPA HSB HSBH HC HRI HREQ PSTK3 PDAT3 PRIR3
                v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 m3 (2^60) (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) (rg_n_allocated r) (rg_n_freed r) shj
                0x6028f8 CTX T ((ts_mmaps (as_ts a)) mod 2^64) ((ts_mmaped (as_ts a)) mod 2^64) ((as_cache_mapped a) mod 2^64)
                ra s0 s1 s2 s3 s4 s5 s6 QK3 MI3 SK3 FR3 ROW3).
      -- clear -R1. lia.
      -- exact MUA.
      -- exact MUR.
      -- apply Z.mod_pos_bound. clear; lia.
      -- apply Z.mod_pos_bound. clear; lia.
      -- apply Z.mod_pos_bound. clear; lia.
      -- exact (proj2 PST3).
      -- exact SHU3.
      -- exact PSH3.
      -- exact TCm3.
      -- clear; lia.
      -- clear; lia.
      -- exact PLC.
      -- exact PLT.
      -- rewrite unsigned_lit by (clear; lia). clear; lia.
      -- exact HTC.
      -- reflexivity.
      -- exact T8.
      -- exact TRS.
      -- exact CRS.
      -- exact PCTX3.
      -- exact PT3.
      -- exact TST3.
      -- exact CST3.
      -- (* [comment removed for export] *)
         intros m4 w0 w1 w2 d1 d2 d4 d5 d6 d7 w3 w4 w5 w6 MI4 SK4 MU4 WM4 FR4 ROW4 PG4 SHUP4 TCm4 TST4 CST4. apply evtA_done. intros mo4 AG4 KP4.
         pose proof (magree_frame _ _ AG4) as (Ffds4 & Fvm4 & Flz4 & Ffs4 & Fh4 & Ftid4 & _).
         assert (WZ4 : WZ [(usp - 1536, usp - 64); (kShadowBase + (RB + rg_mapped_user r) / 8, kShadowBase + (RB + rg_mapped_user r) / 8 + 32768); (T + 2872, T + 2888); (STAT + 24, STAT + 32); (RIc + 48, RIc + 56)]).
         { unfold WZ, BF_popdefs.RIc. rewrite HRI. unfold kShadowBase, kSpaceSize, kThrCacheStats. unfold kSpaceSize in HA2. wz_split.
           - left. clear -LO. lia.
           - right; right; left. clear -HA1 HA2 SB1 HC30 R1. Z.div_mod_to_equations. lia.
           - right; right; right. clear. lia.
           - right; right; right. clear. lia.
           - right; left. clear -HC30. lia. }
         assert (RG2 : get_region a2 c = mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r)).
         { subst a2. rewrite st_user_region. reflexivity. }
         replace (rg_mapped_user r + 262144) with (rg_mapped_user (get_region a2 c)) by (rewrite RG2; reflexivity).
         eapply (pop_phaseD a2 m4 mo4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%nat [AnsOk (region_beg SB c + rg_mapped_user r)] [AEvMmap (region_beg SB c + rg_mapped_user r) kUserMapSize kProtRw kFlagsFixedRw]);
           rewrite ?RG2; cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
         ++ exact (AKern_frame _ _ _ _ Fvm4 Flz4 AK3).
         ++ eapply RTOK_magree; [exact TOK3| exact AG4| exact (proj1 KP4)].
         ++ rewrite GR2. unfold kUserMapSize, kFreeArrayMapSize in RR |- *. clear -RR. lia.
         ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
         ++ intros c' NE. subst a2. apply st_user_other. exact NE.
         ++ subst a2. apply pop_same_user.
         ++ unfold kUserMapSize. clear -R1 RSZ. lia.
         ++ unfold kUserMapSize. clear. lia.
         ++ unfold kUserMapSize. clear -MUR. lia.
         ++ intros orc. exact (run_phase1_grant E0 c req a RSZ ltac:(clear -R1; lia) R700 GR orc).
         ++ rewrite Ffs4, Ffds4, Ftid4, Ffs3, Ffds3, Ftid3. destruct FSK as (K1 & K2 & K3). rewrite K1, K2, K3, FfsK, FfdsK, FtidK, Ffs1, Ffds1, Ftid1.
            split; [reflexivity| split; reflexivity].
         ++ exact MI4.
         ++ exact SK4.
         ++ exact FR4.
         ++ exact ROW4.
         ++ eapply (WZ_ins _ m3 m4); [exact WZ4| exact MU4| | eapply (WZ_ins _ m1 m3); [exact WZ3| exact MU3| | eapply (WZ_ins _ m m1); [exact WZ1| exact MU1| | exact INS]]]; cbn [cells_size csize Nat.add]; clear; lia.
         ++ pose proof (rw_cells_CB_wr_at m3 _ _ _ ZB3) as ZW. rewrite Z2Nat.id in ZW by (clear; lia).
            eapply wr_at_transport; [| exact WM4]. unfold kUserMapSize. apply wr_at_join'; [| exact ZW| clear -R1; lia| clear; lia].
            eapply wr_at_transport; [| exact WM3]. eapply wr_at_transport; [exact WRU| exact WM1].
         ++ eapply u32arr_transport; [eapply u32arr_transport; [eapply u32arr_transport; [exact FAR| exact MU1| exact WM1|]| exact MU3| exact WM3|]| exact MU4| exact WM4|];
              cbn [disjoint_from fst snd]; rewrite ?length_app, ?length_map; unfold zlen in FAL; unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7;
              unfold BF_popdefs.RIc; rewrite ?HRI; unfold kShadowBase, kThrCacheStats; unfold kSpaceSize in *; rewrite KHB in HSBH;
              clear -LOC LO HSB HSBH CEILB HC30 FAL R5 R7 R1 MUR TRS WE15 HA1 HA2; repeat split; try exact I; Z.div_mod_to_equations; lia.
         ++ eapply rw_cells_transport; [eapply rw_cells_transport; [eapply rw_cells_transport; [exact SHF| exact MU1| exact WM1|]| exact MU3| exact WM3|]| exact MU4| exact WM4|];
              cbn [disjoint_from cells_size csize fst snd Nat.add]; rewrite ?Nat.add_0_r, ?(Z2Nat.id 32768) by (clear; lia); unfold kFreeArraySize, kRegionSize, kFreeArrayOffset in R7;
              unfold BF_popdefs.RIc; rewrite ?HRI; unfold kShadowBase, kThrCacheStats; unfold kSpaceSize in *; rewrite KHB in HSBH;
              clear -LOC LO HSB HSBH CEILB HC30 R5 R7 R1 MUR TRS WE15 HA1 HA2 TAPP; repeat split; try exact I; Z.div_mod_to_equations; lia.
         ++ subst a2. rewrite st_user_ts. cbn [ts_mmaps ts_mmaped ts_on_mmap]. unfold kThrStats. replace (T + 2800 + 72) with (T + 2872) by (clear; lia).
            rewrite <- (wz_mod_add (ts_mmaps (as_ts a)) 1), <- (wz_mod_add (ts_mmaped (as_ts a)) kUserMapSize). unfold kUserMapSize. exact TST4.
         ++ subst a2. rewrite st_user_cm. rewrite <- (wz_mod_add (as_cache_mapped a) kUserMapSize). unfold kUserMapSize. exact CST4.
         ++ exact TCm4.
         ++ split; [| exact PG4]. exact (proj1 (WZ_statics _ m3 m4 WZ4 MU4 WM4 PST3)).
         ++ exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM3 WM4)).
         ++ (* [comment removed for export] *)
            unfold pop_W. cbv zeta. rewrite RG2. cbn [rg_mapped_user rg_mapped_fa].
            unfold K_POP, free_array, region_beg. change kRegionSize with 4294967296. change kFreeArrayOffset with 3758096384. change kUserMapSize with 262144.
            change kRegSize with 128. change (RI + 128 * c) with RIc. unfold kThrStats, kThrCacheStats.
            eapply munch_trans; [eapply munch_cover; [exact MU1|]| eapply munch_trans; [eapply munch_cover; [exact MU3|]| eapply munch_cover; [exact MU4|]]];
              unfold BF_popdefs.RIc, kThrCacheStats, zlen; clear -LO R1 R5 HC30; solve_covers.
         ++ replace (rg_mapped_user r + kUserMapSize - rg_mapped_user r) with kUserMapSize by (clear; lia). change (kUserMapSize / 8) with 32768. exact SHUP4.
Qed.
End CALL.

Theorem populate_srz : populate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold populate_srz_stmt. intros until K. intros KN TOK AK WF HC HREQ R700 RFA RFA1 RR SK LOC LO SPA SPH MI TP T8 TC PC PST CONT.
  remember (bv_unsigned sp) as usp eqn:Husp.
  assert (Esp : sp = Z_to_bv 64 usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp in CONT |- *. clear Esp Husp. subst tp. unfold K_POP in LO.
  eapply pop_main; eassumption.
Qed.
End PopT.
End RC__1.
