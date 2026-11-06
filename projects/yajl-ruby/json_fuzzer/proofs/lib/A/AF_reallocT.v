(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow StepA StepA2 SysStepA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot AsanGap AsanSlack
  AsanWf1 AsanRealloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base A_alloc_iface A_iface AF_fakestack_rep AF_place AF_unwind AF_unwind_walk2 AF_kit AF_kit3 AF_free_kit AF_ia
  AF_realloc1 AF_realloc2 AF_reallocG AM_memcpy
  AX_unreg AX_Exit AF_statics A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 A_init5 A_instD5 A_balloc5 A_bpolicy5 A_rtok5 A_bframe A_bframe2
  AF_tkit AF_alloc_iface AF_free_iface AF_glue_kit AF_mallocT2 AF_caT AF_shell_rep5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac unset_all := repeat match goal with x := _ |- _ => subst x end.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma sA_self : forall s, sA (aps_alloc s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma sA_sA : forall a a' s, sA a (sA a' s) = sA a s.
Proof. intros a a' s. destruct s. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma arun_orc_app : forall {R} f (t : stree aev aans (astate * aout R)) orc s o evs orc',
  arun f t orc = Some (s, o, evs, orc') ->
  exists used, orc = used ++ orc' /\ forall tail, arun f t (used ++ tail) = Some (s, o, evs, tail).
Proof.
  intros R f. induction f as [|f IH]; intros t orc s o evs orc' H; destruct t as [[s0 o0]|e k]; cbn in H |- *.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc; discriminate.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc as [|a rest]; [discriminate|].
    destruct (arun f (k a) rest) as [[[[s1 o1] evs1] orc1]|] eqn:HR; [| discriminate]. injection H as <- <- <- <-.
    destruct (IH _ _ _ _ _ _ HR) as (used & -> & RUN). exists (a :: used). split; [reflexivity|].
    intros tail. cbn [app]. rewrite (RUN tail). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_blocks_nodup : forall E a, AWf E [] [] a -> List.NoDup (map fst (live_blocks a)).
Proof.
  intros E a Hwf. unfold live_blocks, chunk_list. rewrite map_map. cbn [fst].
  set (L := map_to_list (as_chunks a)).
  assert (HK : List.NoDup (map fst L)) by (apply NoDup_ListNoDup; apply NoDup_fst_map_to_list).
  assert (HF : forall q, In q L -> cm_user_beg (snd q) = fst q + kChunkHeaderSize).
  { intros [cb cm] Hp. cbn. assert (Hl : as_chunks a !! cb = Some cm).
    { apply (elem_of_map_to_list (as_chunks a) cb cm). apply base.list_elem_of_In. exact Hp. }
    pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hl) as (_ & _ & EQ). unfold user_lo in EQ. lia. }
  clearbody L. induction L as [|q L IH]; cbn; [constructor|].
  inversion HK as [|x l Hx Hl]; subst.
  destruct (match cm_state (snd q) with CAllocated _ => true | CQuarantined _ _ => false end); cbn.
  - constructor.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as (q' & Eq & Hq). apply filter_In in Hq as [Hq _].
      apply Hx. rewrite (HF q (or_introl eq_refl)) in Eq. rewrite (HF q' (or_intror Hq)) in Eq.
      apply in_map_iff. exists q'. split; [lia| exact Hq].
    + apply IH; [exact Hl| intros q' Hq'; apply HF; right; exact Hq'].
  - apply IH; [exact Hl| intros q' Hq'; apply HF; right; exact Hq'].
Qed.

(* [comment removed for export] *)
Lemma live_blocks_sep : forall E a p1 n1 p2 n2, AWf E [] [] a ->
  In (p1, n1) (live_blocks a) -> In (p2, n2) (live_blocks a) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros E a p1 n1 p2 n2 Hwf H1 H2 NE.
  destruct (live_blocks_chunk _ _ _ H1) as (cb1 & cm1 & i1 & Hc1 & HA1 & Hn1 & _).
  destruct (live_blocks_chunk _ _ _ H2) as (cb2 & cm2 & i2 & Hc2 & HA2 & Hn2 & _).
  pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hc1) as (_ & _ & E1).
  pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hc2) as (_ & _ & E2).
  assert (Hcb : cb1 <> cb2) by (unfold user_lo in *; rewrite HA1 in E1; rewrite HA2 in E2; lia).
  pose proof (live_blocks_disjoint _ _ _ _ _ _ _ _ Hwf Hc1 Hc2 Hcb) as D.
  unfold user_lo, user_hi in D. rewrite HA1, HA2, Hn1, Hn2 in D. exact D.
Qed.

(* [comment removed for export] *)
Lemma live_block_aw_ok : forall E a a2 r n x y lo sp, AWf E [] [] a -> In (r, n) (live_blocks a) ->
  r <= x -> y <= r + n -> aw_ok E a a2 lo sp (x, y).
Proof.
  intros E a a2 r n x y lo sp Hwf Hin Hx Hy.
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & _).
  pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hcm) as (U1 & U2 & _). unfold user_lo, user_hi in U1, U2. rewrite HA, Hn in *.
  pose proof (proj1 Hwf) as (_ & _ & W3 & W4 & _).
  destruct (block_where E [] [] a cb cm Hwf Hcm) as [(I1 & I2 & _)|(sc & Hsc & _ & L1 & L2)]; unfold aw_ok; cbn [fst snd].
  - do 3 right; left. unfold kResvLen. unfold kSpaceSize in *. lia.
  - do 5 right; left. exists sc. split; [left; exact Hsc| unfold kPageSize in L1; lia].
Qed.

(* [comment removed for export] *)
Lemma ab_find_nodup : forall A sz LB, List.NoDup (map ab_addr LB) -> In (mkABlock A sz) LB -> ab_find A LB = Some (mkABlock A sz).
Proof.
  intros A sz LB. induction LB as [|b LB IH]; intros ND HIN; [destruct HIN|].
  unfold ab_find. cbn [List.find]. inversion ND as [| x l NI ND']; subst.
  destruct HIN as [->| HIN].
  - cbn [ab_addr]. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (ab_addr b) A) as [E|E].
    + exfalso. apply NI. apply in_map_iff. exists (mkABlock A sz). split; [cbn [ab_addr]; symmetry; exact E| exact HIN].
    + unfold ab_find in IH. apply IH; assumption.
Qed.
Lemma arefund_at_found : forall A sz LB, List.NoDup (map ab_addr LB) -> In (mkABlock A sz) LB -> arefund_at arefund A LB = arefund sz.
Proof. intros A sz LB ND HIN. unfold arefund_at. rewrite (ab_find_nodup A sz LB ND HIN). reflexivity. Qed.
Lemma ab_remove_split : forall A sz LB, List.NoDup (map ab_addr LB) -> In (mkABlock A sz) LB ->
  DEP (ab_remove A LB) + arefund sz = DEP LB
  /\ Permutation (map (fun b => (ab_addr b, ab_size b)) LB) ((A, sz) :: map (fun b => (ab_addr b, ab_size b)) (ab_remove A LB)).
Proof.
  intros A sz LB. induction LB as [|b LB IH]; intros ND HIN; [destruct HIN|].
  inversion ND as [| x l NI ND']; subst. cbn [ab_remove map DEP fold_right].
  destruct HIN as [->| HIN].
  - cbn [ab_addr ab_size]. rewrite Z.eqb_refl. split; [unfold DEP; lia| apply Permutation_refl].
  - destruct (Z.eqb_spec (ab_addr b) A) as [E|E].
    + exfalso. apply NI. apply in_map_iff. exists (mkABlock A sz). split; [cbn [ab_addr]; symmetry; exact E| exact HIN].
    + destruct (IH ND' HIN) as [D PM]. split; [cbn [map fold_right]; unfold DEP in D |- *; cbn [fold_right]; lia|].
      cbn [map]. etransitivity; [apply perm_skip; exact PM| apply perm_swap].
Qed.
Lemma ab_remove_cons_neq : forall A b LB, ab_addr b <> A -> ab_remove A (b :: LB) = b :: ab_remove A LB.
Proof. intros A b LB NE. cbn [ab_remove]. destruct (Z.eqb_spec (ab_addr b) A) as [E|E]; [contradiction| reflexivity]. Qed.
Lemma ab_remove_sub : forall A LB b, In b (ab_remove A LB) -> In b LB.
Proof.
  intros A LB. induction LB as [|x LB IH]; intros b Hb; [exact Hb|]. cbn [ab_remove] in Hb.
  destruct (ab_addr x =? A); [right; exact Hb|]. destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (IH _ Hb)].
Qed.
Lemma ab_remove_neq : forall A LB b, List.NoDup (map ab_addr LB) -> In b (ab_remove A LB) -> ab_addr b <> A.
Proof.
  intros A LB. induction LB as [|x LB IH]; intros b ND Hb; [destruct Hb|]. cbn [ab_remove] in Hb. cbn [map] in ND.
  apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (Z.eqb_spec (ab_addr x) A) as [E|NE].
  - intros Eb. apply NI. rewrite E, <- Eb. apply in_map. exact Hb.
  - destruct Hb as [<-|Hb]; [exact NE| exact (IH _ ND Hb)].
Qed.

Lemma disjoint_from_Forall : forall W A n, Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) W -> disjoint_from W A n.
Proof. intros W A n FW. induction FW as [|[u v] W H FW IH]; [exact I|]. cbn [disjoint_from fst snd] in *. split; [exact H| exact IH]. Qed.

(* [comment removed for export] *)
Lemma live_bytes_pres : forall (W : list (Z * Z)) (m m' : mem) L blo bsz bs,
  munch W m m' -> Forall (fun iv : Z * Z => forall b s, In (b, s) L -> snd iv <= fst iv \/ snd iv <= b \/ b + s <= fst iv) W ->
  In (blo, bsz) L -> Z.of_nat (length bs) = bsz -> bytes_at asegs m blo bs -> bytes_at asegs m' blo bs.
Proof.
  intros W m m' L blo bsz bs MU FW Hin HL BA. eapply bytes_at_transport; [exact BA| exact (munch_nonempty _ _ _ MU)|].
  apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv. apply nonempty_ivls_In in Hiv as [Hiv LT].
  pose proof (proj1 (Forall_forall _ _) FW iv Hiv blo bsz Hin) as X. rewrite HL. lia.
Qed.

(* [comment removed for export] *)
Lemma obj_c8 : forall m B (X : word) len, 0 <= len < 2^32 ->
  rw_cells asegs m B [C8 X; C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] -> rw_cells asegs m B [C8 X; C8 (Z_to_bv 64 len)].
Proof.
  intros m B X len HL RC. eapply rw_cells_reshape; [| | exact RC]; [cbn; tauto|]. f_equal.
  change (cells_bytes ([C8 X] ++ [C8 (Z_to_bv 64 len)]) = cells_bytes ([C8 X] ++ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)])).
  rewrite !cells_bytes_app. f_equal. rewrite <- (Z.add_0_r len) at 1. change 0 with (2^32 * 0) at 1. apply c8_c4c4; lia.
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_sub : forall LB LB' LF SP m m', (forall b, In b LB' -> In b LB) ->
  aheap_pres asegs ACONSTS LB LF SP m m' -> aheap_pres asegs ACONSTS LB' LF SP m m'.
Proof.
  intros LB LB' LF SP m m' SUB HP a Ha HC. apply HP; [exact Ha|].
  destruct HC as [X|[X|X]]; [left; exact X| right; left| right; right; exact X].
  destruct X as (b & Hb & R). exists b. split; [apply SUB; exact Hb| exact R].
Qed.


(* [comment removed for export] *)
Section ReallocT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.
(* [comment removed for export] *)
Hypothesis ALLOC : allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Hypothesis DEALLOC : dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.

#[local] Notation AHKc := (AF_tkit.AHKc E0 FSB0 HR0 L0 RES0 EB0 PL0).
#[local] Notation SR := stdio_rep.
#[local] Notation RT := (rt_misc5 FSB0 PL0).
#[local] Notation rt_fpE := (fun E a => rt_fpc E FSB0 PL0 a).
#[local] Notation DR := (DepotR asegs E0).
Ltac cstat := try clear ALLOC; try clear DEALLOC; try clear HS_tot; try clear ENV_depot; try clear EB0_ok; try clear HR0_ok; try clear PL0OK; try clear ENV0.

Lemma shell_st_ts0 : forall n a, shell_st true (ts_on_realloc n (as_ts a)) a = ts0 n (ia0 a).
Proof. intros n a. destruct a. reflexivity. Qed.
Lemma same_fp_shell_st : forall ii ts a, same_fp a (shell_st ii ts a).
Proof. intros ii ts a. destruct a. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition PP (s : aps) (mo : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo) (aS E0 FSB0 HR0 s) x.
Lemma EPOL : forall s mo a k, POL E0 FSB0 HR0 s mo a k = PP s mo (Z_to_bv 64 a, k). Proof. intros; reflexivity. Qed.
(* [comment removed for export] *)
Definition shell_facts2 (a : astate) (m : mem) : Prop :=
     rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (AsanRep.boolz (as_ia_inited a))); C1 zb0]
  /\ (as_ia_inited a = true -> rw_cells asegs m (IA + 0x40dc0) [C8 (wz 4096); C8 (wz (IA + 0x40dd0))])
  /\ u8arr asegs m (IA + 8) (zeros (Z.to_nat 0x40000)) /\ wr_at asegs m IA 0x81030
  /\ rw_cells asegs m (ae_thread E0 + 2856) [C8 (wz (ts_reallocs (as_ts a))); C8 (wz (ts_realloced (as_ts a)))]
  /\ rw_cells asegs m GOT_REAL_MEMCPY [C8 (wz REAL_MEMCPY_VAR)] /\ rw_cells asegs m REAL_MEMCPY_VAR [C8 (wz MUSL_MEMCPY)].

Lemma shell_facts2_of : forall s LB LF m mo, AHKc s LB LF m mo -> shell_facts2 (aps_alloc s) m.
Proof.
  clear DEALLOC ALLOC HS_tot ENV_depot EB0_ok HR0_ok. intros s LB LF m mo AH. unfold AF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. rewrite EE in *.
  pose proof Hrep as REP. destruct REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & Ghk & Gia & Gipv & Giz & Giwr).
  pose proof ENV0 as EV. destruct EV as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & NB0 & NT47 & IC0 & NTD & NDP).
  rewrite IC0 in Grm, Gia, Gipv, Giz, Giwr.
  cbn [aic_REAL_memcpy_var aic_musl_memcpy aic_musl_memset aic_internal_alloc_initialized aic_internal_allocator_instance asan_ic] in Grm, Gia, Gipv, Giz, Giwr.
  pose proof Hrt as (_ & _ & _ & AMS & _). pose proof AMS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GOTM & GSN1 & GSN2 & _).
  unfold shell_facts2.
  split; [exact Gia|]. split; [unfold IA; unfold kIaPageSizeOff, kIaChunksPtrOff, kPageSize in Gipv; exact Gipv|].
  split; [unfold IA; exact Giz|]. split; [unfold IA; exact Giwr|].
  split. { unfold kThrStats in Tst.
    pose proof (AsanRepHit.u64arr_cell asegs m _ _ 7 _ Tst eq_refl) as X7. pose proof (AsanRepHit.u64arr_cell asegs m _ _ 8 _ Tst eq_refl) as X8.
    pose proof (rwc_join_at asegs m _ _ _ _ X7 X8 ltac:(cbn; lia)) as J. cbn [app] in J.
    replace (ae_thread E0 + 2856) with (ae_thread E0 + 2800 + 8 * Z.of_nat 7) by (clear; lia). exact J. }
  split; [unfold GOT_REAL_MEMCPY, REAL_MEMCPY_VAR; exact GOTM|].
  pose proof (rwc_split asegs m _ [C8 (AsanRep.zw 646364)] [C8 (AsanRep.zw 647392)] Grm) as [X _]. unfold REAL_MEMCPY_VAR, MUSL_MEMCPY. exact X.
Qed.

(* [comment removed for export] *)
Lemma old_header : forall a m p sz, AWf E0 [] [] a -> ARep asegs E0 DR a m -> In (p, sz) (live_blocks a) ->
  1 <= sz < 2^40 /\ exists (hb1 : byte) (hid : Z),
    rw_cells asegs m (p + -16) [C1 (Z_to_bv 8 2); C1 hb1; C2 (wz (sz / 2^32)); C4 (wz sz); C8 (wz hid)].
Proof.
  cstat. intros a m p sz Hwf REP Hin.
  destruct (live_block_meta E0 [] [] a p sz Hwf Hin) as (meta & aid & Hm & ST & UB & HN).
  pose proof Hwf as (_ & _ & _ & [WK _] & _). destruct (WK _ _ Hm) as (_ & Kn & _).
  destruct REP as (_ & _ & _ & _ & _ & Rch & _). destruct (Rch _ _ Hm) as [ECB [(b1 & Hb1 & HDR) _]].
  rewrite ST in HDR. cbn [hdr_state hdr_alloc_id] in HDR. unfold kChunkAllocated in HDR. rewrite HN in HDR.
  split; [rewrite <- HN; exact Kn|]. exists (AsanRep.zb b1), aid.
  rewrite <- ECB in HDR. unfold kChunkHeaderSize in HDR. replace (p + -16) with (p - 16) by lia. exact HDR.
Qed.

(* [comment removed for export] *)
Lemma above_sp_agree : forall a a' mo' lo sp W (m m' : mem) A k,
  munch W m m' -> Forall (aw_ok E0 a a' lo sp) W -> AWf E0 [] [] a -> AWf E0 [] [] a' -> AKern E0 a' mo' ->
  sp <= A -> alloc_ceiling <= A -> A + k <= 2^64 -> agree_on m m' A k.
Proof.
  clear DEALLOC ALLOC HS_tot ENV_depot EB0_ok HR0_ok PL0OK. intros a a' mo' lo sp W m m' A k MU FW WF WF' K' H1 H2 H3 x Hx. pose proof alloc_ceiling_range as CR.
  apply (munch_nonempty _ _ _ MU). rewrite wa_unsigned by (clear -Hx H2 H3 CR; lia).
  eapply outside_of_Forall; [apply Forall_forall; intros iv Hiv; exact Hiv|]. cbv beta. intros iv Hiv R.
  apply nonempty_ivls_In in Hiv as [Hiv LT]. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as F1.
  destruct (aw_ok_below E0 ENV0 a a' mo' lo sp iv F1 WF WF' K' LT); clear -H H1 H2 Hx R; lia.
Qed.

Lemma u64arr_agree : forall m m' A0 ws,
  (forall x, A0 <= x < A0 + 8 * Z.of_nat (length ws) -> m' (wa x) = m (wa x)) ->
  u64arr asegs m A0 ws -> u64arr asegs m' A0 ws.
Proof.
  cstat. intros m m' A0 ws AG [(B0 & B1 & BR) (W0 & W1 & WR)]. rewrite u64s_length in B1, BR.
  split; [split; [exact B0| split; [rewrite u64s_length; exact B1|]]|].
  - rewrite u64s_length. intros k Hk. rewrite <- (BR k Hk). unfold mrd. rewrite AG by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros k Hk. specialize (WR k Hk). unfold wview in *. rewrite AG by lia. exact WR.
Qed.

(* [comment removed for export] *)
Lemma aw_ok_preW : forall a a' lo usp, Forall (aw_ok E0 a a' lo usp) (preW usp lo (ae_thread E0)).
Proof.
  cstat. intros a a' lo usp. unfold preW.
  constructor. { left. cbn [fst snd]. clear; lia. }
  constructor. { right; left. exists (aic_internal_allocator_instance asan_ic, 0x81030). split; [unfold img_mut; cbn; tauto| unfold AF_shell_rep5.IA; cbn; clear; lia]. }
  constructor. { right; left. exists (aic_internal_alloc_initialized asan_ic, 4). split; [unfold img_mut; cbn; tauto| cbn; clear; lia]. }
  constructor. { do 2 right; left. exists (ae_thread E0 + kThrUnwinding, 1). split; [unfold arep_thr_ranges; cbn; tauto| unfold kThrUnwinding; cbn; clear; lia]. }
  constructor. { do 2 right; left. exists (ae_thread E0 + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; cbn; tauto| unfold kThrStats; cbn; clear; lia]. }
  constructor.
Qed.

(* [comment removed for export] *)
Definition rmid_facts (s : aps) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) (usp lo A n : Z) (m2 : mem) (mo1 : Model)
    (ws tr : list word) (bpw s4w : word) (j1800 j8 j8b j8c : list byte) (ra s0 s1 s2 s3 s4 s5 s6 : word) : Prop :=
  let a := aps_alloc s in let T := ae_thread E0 in
  let a1 := shell_st true (ts_on_realloc n (as_ts a)) a in
     AHKc (sA a1 s) LB LF m2 mo1
  /\ munch (preW usp lo T) m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp - 2208)
  /\ rw_cells asegs m2 (usp + -2136) [C8 (wz (usp + -2120)); C4 (wz (Z.of_nat (length tr))); C4 (wz 0)]
  /\ u64arr asegs m2 (usp + -2120) ws /\ length ws = 30%nat /\ (1 <= length tr <= 30)%nat
  /\ rw_cells asegs m2 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m2 (usp + -1880) [CB 1800 j1800] /\ rw_cells asegs m2 (usp + -80) [C8 bpw] /\ rw_cells asegs m2 (usp + -72) [CB 8 j8]
  /\ rw_cells asegs m2 (usp + -2144) [CB 8 j8b] /\ rw_cells asegs m2 (usp + -2160) [CB 8 j8c; C8 (wz REA_ASAN_RET)]
  /\ rw_cells asegs m2 (usp - 2208) [C8 s4w; C8 (wz REA_PC0); C8 (wz A); C8 (wz n); C8 (wz usp); C8 (wz 210468)]
  /\ m_fs mo1 = m_fs mo /\ m_fds mo1 = m_fds mo
  /\ aheap_pres asegs ACONSTS LB LF usp m m2.

(* [comment removed for export] *)
Lemma realloc_enter :
  forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (A sz n lo : Z) (Tk : TSet),
  AHKc s LB LF m mo -> In (mkABlock A sz) LB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
  uanchor asegs m (bv_unsigned sp) ra s0 -> 0 < n <= 2^27 -> nbig LB <= 8000 ->
  (forall (t0' t1' a6' a7' s4w : word) (m2 : mem) (mo1 : Model) (ws tr : list word) (bpw : word) (j1800 j8 j8b j8c : list byte),
     rmid_facts s LB LF m mo (bv_unsigned sp) lo A n m2 mo1 ws tr bpw s4w j1800 j8 j8b j8c ra s0 s1 s2 s3 s4 s5 s6 ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR (wz REA_ALLOC_RET) (wz (bv_unsigned sp - 2208)) gp (wz 0x5e0b10) t0' t1' t2 (wz (bv_unsigned sp + -2136)) (wz A)
                                     (wz AINST) (wz n) (wz 8) (wz (bv_unsigned sp + -2136)) (wz 1) (wz 1) a6' a7'
                                     (wz AINST) (wz n) s4w (wz (bv_unsigned sp + -2136)) (wz (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ALLOCATE_FN) fc None m2 (seg_rom asegs)) mo1) Tk) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp (wz 0x5e0b10) t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_realloc ACONSTS)) fc None m (seg_rom asegs)) mo) Tk.
Proof.
  intros until Tk. intros AH HLB SK LOC LO SPA SPH UA Hn2 NBIG INNER.
  destruct (shell_facts_of E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK _ _ _ _ _ AH) as (Gai & Gmcs & GCF & Gfu & GPSC & Gps & TC & HCTX & HT & HTC & HTB & (c0 & cl & RRC & CLO & CHI)).
  destruct (shell_facts2_of _ _ _ _ _ AH) as (Gia & Gipv & Giz & Giwr & STATS & GOTM & RMV).
  pose proof AH as AH0. unfold AF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in *.
  destruct Hkm as (Khalt & Kminv & Klim).
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp. clear Esp Husp. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  pose proof (proj1 Hwf) as WE.
  (* [comment removed for export] *)
  assert (HLIVE : In (A, sz) (live_blocks (aps_alloc s))) by (exact (blocks_match_In LB (aps_alloc s) (mkABlock A sz) Hbm HLB)).
  pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo A sz AH0 HLIVE) as (GA1 & GA2 & GA3 & GA4 & GA5).
  (* [comment removed for export] *)
  assert (PSTK : forall a' k, lo <= a' -> a' + Z.of_nat k <= 2^64 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC; lia. }
  assert (PDAT : forall a' k, 0xa4000 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENVOK0 ENV0); clear -H1 H2; lia. }
  assert (PCTX : PP s mo (Z_to_bv 64 (fp_ctx PL0 + 152), 8%nat)).
  { rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 s mo Hkern c0 cl); [exact RRC| clear -CLO; lia| clear -CHI; cbn; lia]. }
  assert (PTHR : forall a' k, ae_thread E0 <= a' -> a' + Z.of_nat k <= ae_thread E0 + 4096 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); assumption. }
  assert (KIP0 : KIP (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo) mo) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH0)| intros x Hx; exact Hx]).
  assert (HA' : 0 < A < 2^47) by (clear -GA1 GA2 GA4 CEILB; lia).
  assert (HN' : 0 < n < 2^64) by (clear -Hn2; lia).
  assert (HTSD' : 0x5cfdd0 <= 0x601eb8 /\ 0x601eb8 + 8 <= 0x603000) by (clear; lia).
  assert (HTP' : 0x5cfdd0 + 88 <= bv_unsigned (wz 0x5e0b10) /\ bv_unsigned (wz 0x5e0b10) + 60 <= 0x603000) by (rewrite unsigned_lit by (clear; lia); clear; lia).
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg asegs (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo)); [| exact KIP0|].
  { stepA.
    lazymatch goal with |- evtA _ _ _ (MS ?r ?f ?pc ?x1 ?x2 ?x3 ?x4) => let v := eval vm_compute in (bv_unsigned pc) in change pc with (Z_to_bv 64 v) end.
    eapply (rea_pre (PP s mo) gp (wz 0x5e0b10) t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo A n (as_ia_inited (aps_alloc s)) (zeros (Z.to_nat 0x40000)) 0x601eb8 (fp_ctx PL0) (ae_thread E0) (ae_stack_top E0) (ae_stack_bottom E0)
              LOC ltac:(clear -LO; lia) SPH SPA HTB HA' HN' ltac:(unfold zeros; reflexivity) HTSD' HCTX HT HTC HTP' PSTK PDAT PCTX PTHR);
      [ exact SK| exact Hmi| exact Gai| exact GPSC| exact Gps| exact Gmcs| exact GCF| exact Gfu| exact Gia
      | exact Giwr| exact Giz| unfold IA in Gipv; exact Gipv| exact TC| exact UA| exact STATS ]. }
  intros ms2 mo1 POST1 Hag1 KP1.
  destruct POST1 as (t0' & t1' & a6' & a7' & s4w & m2 & ws & tr & bpw & j1800 & j8 & j8b & j8c & -> & MU1 & WM1 & MI2 & SK2 & IAF2 & IPV2 & IZ2 & IWR2 & TU2 & ST2 & OBJ & ARR & LEN30 & FTR & LTR
                       & FR8 & FJ1800 & FBP & FJ8 & FJ8B & FRA & FR6).
  (* [comment removed for export] *)
  set (ts := as_ts (aps_alloc s)) in *. set (ts1 := ts_on_realloc n ts). set (a1 := shell_st true ts1 (aps_alloc s)).
  pose proof (model_shell_st E0 true ts1 (aps_alloc s)) as (MW & MR & MQ & MD & MB & MLB & MNP & MND & MRES & MIA & MTS & MSS & MCS).
  fold a1 in MW, MR, MQ, MD, MB, MLB, MNP, MND, MRES, MIA, MTS, MSS, MCS.
  pose proof (blocks_sep_of E0 (aps_alloc s) mo ENV0 Hwf Hkern) as BS0.
  pose proof (magree_frame _ _ Hag1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & _).
  assert (K1 : AKern E0 a1 mo1) by (apply AKern_shell_st; eapply AKern_frame; [exact Qvm1| exact Qlz1| exact Hkern]).
  assert (FWpre : Forall (shell_iv E0 lo) (preW usp lo (ae_thread E0))).
  { unfold preW, shell_iv. repeat apply Forall_cons; cbn [fst snd]; [left; clear; lia| right; left; unfold AF_shell_rep5.IA; clear; lia| right; right; left; clear; lia
      | do 4 right; clear; lia| do 3 right; left; clear; lia| apply Forall_nil]. }
  pose proof TU2 as (TC2 & T40b & T8b & TUNW2).
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGE). rewrite EE in IMGE.
  assert (REP1 : ARep asegs E0 DR a1 m2).
  { subst a1. eapply (ARep_shell E0 PL0 ENV0 PL0OK IMGE (aps_alloc s) m m2 mo (preW usp lo (ae_thread E0)) lo true ts1);
      [exact Hrep| exact Hwf| exact Hkern| exact BS0| exact WM1| exact MU1| exact LOC| exact FWpre| exact IAF2| intros _; exact IPV2| exact IZ2
      | subst ts1 ts; apply ts_agree78_realloc| exact ST2| exact TUNW2]. }
  (* [comment removed for export] *)
  pose proof (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot s LB LF m mo AH0 NBIG) as TOK0.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK0 Hag1 (proj1 KP1)) as TOK0'. rewrite <- (sA_self s) in TOK0'.
  pose proof (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s (aps_alloc s) a1 mo1 TOK0' (same_fp_shell_st true ts1 (aps_alloc s)) MNP MND) as TOK1.
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK1) as (R1 & R1' & ATOK1 & _ & _).
  (* [comment removed for export] *)
  pose proof Hbud as (BU0 & BU1 & BU2 & BU3).
  assert (AH1 : AHKc (sA a1 s) LB LF m2 mo1).
  { unfold AF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              s (sA a1 s) LB LF m mo a1 m2 mo1 LB (preW usp lo (ae_thread E0)) lo usp R1 R1' AH0);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact REP1| exact (MW Hwf)| exact K1| exact (MR Hres)| exact (MQ Hqb)| exact (MD Hdi)| exact (MB Hbinv)| exact (MSS Hss)| exact (MCS Hcs)
      | unfold blocks_match; rewrite MLB; exact Hbm| exact ATOK1| exact MI2| exact MU1| apply aw_ok_preW| exact LOC
      | cbn [aps_credit sA aps_set_alloc]; exact BU0| rewrite MNP; exact BU1| rewrite MND; exact BU2| ].
    cbn [aps_credit aps_alloc sA aps_set_alloc]. rewrite MNP, MND, MRES. clear. lia. }
  (* [comment removed for export] *)
  assert (HP1 : aheap_pres asegs ACONSTS LB LF usp m m2).
  { eapply (aw_client_pres E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK s LB LF m mo a1 mo1 m2 (preW usp lo (ae_thread E0)) lo usp LB AH0 (MW Hwf) K1 MU1 WM1);
      [apply aw_ok_preW| exact LOC| clear -LO; lia|].
    intros b Hb. split; [exact Hb|]. pose proof (blocks_match_In _ _ _ Hbm Hb) as HbL.
    pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HbL) as [B1 B2].
    pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo _ _ AH0 HbL) as (B3 & _).
    unfold preW, AF_shell_rep5.IA. repeat apply Forall_cons; cbn [fst snd];
      [clear -B1 LOC; lia| clear -B3; lia| clear -B3; lia| clear -B2; lia| clear -B2; lia| apply Forall_nil]. }
  apply (INNER t0' t1' a6' a7' s4w m2 mo1 ws tr bpw j1800 j8 j8b j8c). unfold rmid_facts. cbv zeta. fold ts ts1 a1.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: clear -LTR; lia.
Qed.

(* [comment removed for export] *)
Lemma rmid_pre : forall s LB LF m mo usp lo A n m2 mo1 ws tr bpw s4w j1800 j8 j8b j8c ra s0 s1 s2 s3 s4 s5 s6,
  AHKc s LB LF m mo -> acharge n + 1 <= aps_credit s -> nbig LB <= 8000 ->
  rmid_facts s LB LF m mo usp lo A n m2 mo1 ws tr bpw s4w j1800 j8 j8b j8c ra s0 s1 s2 s3 s4 s5 s6 ->
  let a1 := shell_st true (ts_on_realloc n (as_ts (aps_alloc s))) (aps_alloc s) in
  RTOK E0 FSB0 HR0 L0 RES0 EB0 (aps_credit s) OPSLACK (sA a1 s) mo1 /\ AINV E0 FSB0 PL0 a1 m2 mo1
  /\ abudget_pre a1 n /\ nbig_live a1 <= 8000.
Proof.
  intros until s6. intros AH CHG NBIG MID. cbv zeta.
  set (a1 := shell_st true (ts_on_realloc n (as_ts (aps_alloc s))) (aps_alloc s)).
  pose proof (model_shell_st E0 true (ts_on_realloc n (as_ts (aps_alloc s))) (aps_alloc s)) as (MW & MR & MQ & MD & MB & MLB & MNP & MND & MRES & MIA & MTS & MSS & MCS).
  fold a1 in MW, MR, MQ, MD, MB, MLB, MNP, MND, MRES, MIA, MTS, MSS, MCS.
  destruct MID as (AH1 & MU1 & WM1 & MI2 & _).
  pose proof AH as AH0. unfold AF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. rewrite EE in *.
  split; [exact (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot (sA a1 s) LB LF m2 mo1 AH1 NBIG)|].
  pose proof AH1 as AH1c. unfold AF_tkit.AHKc in AH1c.
  destruct AH1c as (Hrep1 & Hwf1 & Hkern1 & _ & Hres1 & Hqb1 & Hdi1 & Hbinv1 & _ & _ & _ & _ & _ & Hrt1 & _ & _ & _ & _ & Hmi1 & _ & _ & Hss1 & Hcs1).
  cbn [aps_alloc aps_env aps_fsbase sA aps_set_alloc] in Hrep1, Hwf1, Hkern1, Hres1, Hqb1, Hdi1, Hbinv1, Hrt1, Hss1, Hcs1. rewrite EE in *.
  split. { split; [exact Hrep1|]. split; [exact Hwf1|]. split; [exact Hkern1|]. split; [exact Hres1|]. split; [exact Hqb1|]. split; [exact Hdi1|]. split; [exact Hbinv1|]. split; [exact Hmi1| split; [exact Hrt1| split; [exact Hss1| exact Hcs1]]]. }
  split.
  { pose proof Hbud as (BU0 & BU1 & BU2 & BU3). unfold ACC in BU3. unfold abudget_pre. rewrite MNP, MND.
    pose proof (DEP_nonneg LB) as DEPnn. pose proof (AsanBudget2.zlen_nonneg (as_residue (aps_alloc s))) as ZR. cstat. clear -BU0 BU1 BU2 BU3 DEPnn ZR CHG. lia. }
  unfold nbig_live. rewrite MLB. unfold nbig in NBIG. unfold blocks_match in Hbm.
  assert (FM : forall (l : list ablock), List.filter (fun b : Z * Z => 64512 <? snd b) (map (fun b => (ab_addr b, ab_size b)) l)
                                      = map (fun b => (ab_addr b, ab_size b)) (List.filter (fun b => 64512 <? ab_size b) l)).
  { clear. induction l as [|b l IH]; [reflexivity|]. cbn [map List.filter snd]. destruct (64512 <? ab_size b); cbn [map]; rewrite IH; reflexivity. }
  rewrite <- (Permutation_length (Permutation_filterb _ _ _ Hbm)), FM, length_map. exact NBIG.
Qed.

(* [comment removed for export] *)
Theorem realloc_contract : arealloc_rz_stmt asegs ACONSTS aps AHKc aps_so (arealloc_rel E0) aps_credit acharge arefund (AF_unwind.uanchor asegs).
Proof.
  unfold arealloc_rz_stmt. intros until K. intros KN AH HLB HOLD HLEN SK LOC LO SPA SPH TP UA FRM A0 A1 Hn2 CHG NBIG CONT. subst a0 a1 tp. cbn [c_tp ACONSTS].
  eapply realloc_enter; [exact AH| exact HLB| exact SK| exact LOC| exact LO| exact SPA| exact SPH| exact UA| exact Hn2| exact NBIG|].
  intros t0' t1' a6' a7' s4w m2 mo1 ws tr bpw j1800 j8 j8b j8c MID.
  destruct (rmid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AH CHG NBIG MID) as (TOK1 & AINV1 & ABUD & NBL).
  set (ts := as_ts (aps_alloc s)) in *. set (ts1 := ts_on_realloc n ts) in *. set (a1 := shell_st true ts1 (aps_alloc s)) in *.
  pose proof MID as (AH1 & MU1 & WM1 & MI2 & SK2 & OBJ & ARR & LEN30 & LTR & FR8 & FJ1800 & FBP & FJ8 & FJ8B & FRA & FR6 & Qfs1 & Qfds1 & HP1).
  pose proof (bv_unsigned_in_range 64 sp) as USPR. unfold bv_modulus in USPR. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned). rewrite Esp in CONT. clear Esp Husp.
  assert (OBJ2 : rw_cells asegs m2 (usp + -2136) [C8 (wz (usp + -2120)); C8 (wz (Z.of_nat (length tr)))]) by (apply obj_c8; [clear -LTR; lia| exact OBJ]).
  (* [comment removed for export] *)
  eapply (ALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mo1 (sA a1 s) n lo (usp + -2136) (usp + -2120) (Z.of_nat (length tr)) (aps_credit s) OPSLACK ws K);
    [ exact KN | exact TOK1 | cbn [aps_credit sA aps_set_alloc]; clear -CHG; lia | unfold ASLACK, OPSLACK; clear; lia | exact AINV1 | exact ABUD | exact Hn2 | exact NBL
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); exact SK2 | exact LOC
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); unfold K_ALLOC; clear -LO; lia
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear -SPA; Z.div_mod_to_equations; lia
    | reflexivity
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear; lia
    | clear; lia
    | unfold zlen; rewrite LEN30; clear -SPH LO LOC CEILB; lia
    | exact OBJ2 | exact ARR
    | unfold zlen; rewrite LEN30; clear -LTR; lia
    | unfold zlen; rewrite LEN30; clear; lia | ].
  cbv beta. intros t0'' t1'' t2'' a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 mo2 aa2 rnew POST2.
  destruct POST2 as (SK3 & WM3 & (W3 & MUA & FWA & FBA) & RUN1 & AINV2 & TOK2 & Ffs2 & Ffds2 & Ftid2 & ACCT & EA0 & AR & PERM & [junk [LJ JC]] & BSH).
  rewrite unsigned_lit in SK3, FWA by (clear -LO LOC USPR CEILB; lia).
  cbn [aps_alloc sA aps_set_alloc] in FWA, FBA, RUN1, ACCT, PERM. rewrite sA_sA in TOK2.
  pose proof AINV2 as (Hrep2 & WF2 & K2 & RO2 & QB2 & DI2 & BI2 & MI3 & Hrt2 & SS2 & CS2).
  pose proof AH as AH0. unfold AF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in *.
  pose proof AH1 as AH1c. unfold AF_tkit.AHKc in AH1c.
  destruct AH1c as (Hrep1 & Hwf1 & Hkern1 & _ & _ & _ & _ & _ & Hbm1 & _ & _ & _ & _ & Hrt1 & _ & _ & _ & Hbud1 & Hmi1 & Henv1 & _).
  cbn [aps_alloc aps_env aps_fsbase sA aps_set_alloc] in Hrep1, Hwf1, Hkern1, Hbm1, Hrt1, Hbud1, Henv1. rewrite EE in *.
  pose proof (model_shell_st E0 true ts1 (aps_alloc s)) as (MW & MR & MQ & MD & MB & MLB & MNP & MND & MRES & MIA & MTS & MSS & MCS).
  fold a1 in MW, MR, MQ, MD, MB, MLB, MNP, MND, MRES, MIA, MTS, MSS, MCS.
  destruct (shell_facts_of E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK _ _ _ _ _ AH0) as (_ & _ & _ & _ & _ & _ & TC & HCTX & HT & HTC & HTB & (c0 & cl & RRC & CLO & CHI)).
  (* [comment removed for export] *)
  assert (HLIVE : In (A, sz) (live_blocks (aps_alloc s))) by (exact (blocks_match_In LB (aps_alloc s) (mkABlock A sz) Hbm HLB)).
  pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo A sz AH0 HLIVE) as (GA1 & GA2 & GA3 & GA4 & GA5).
  pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HLIVE) as [_ GAT].
  (* [comment removed for export] *)
  Ltac survive H MUA WM3 FWA Hwf1 WF2 K2 := eapply (shell_cells_pres E0 ENV0 _ _ _ _ _ _ _ _ _ _ MUA WM3 FWA Hwf1 WF2 K2) in H; [| lia| lia].
  pose proof (cb_of_u64arr asegs _ _ _ ARR) as ARRC. rewrite LEN30 in ARRC. cbn [Nat.mul] in ARRC.
  survive FR6 MUA WM3 FWA Hwf1 WF2 K2. survive FRA MUA WM3 FWA Hwf1 WF2 K2. survive FJ8B MUA WM3 FWA Hwf1 WF2 K2.
  survive OBJ MUA WM3 FWA Hwf1 WF2 K2. survive ARRC MUA WM3 FWA Hwf1 WF2 K2. survive FJ1800 MUA WM3 FWA Hwf1 WF2 K2.
  survive FBP MUA WM3 FWA Hwf1 WF2 K2. survive FJ8 MUA WM3 FWA Hwf1 WF2 K2. survive FR8 MUA WM3 FWA Hwf1 WF2 K2.
  assert (ARR3 : u64arr asegs m3 (usp + -2120) ws).
  { destruct ARRC as [[_ B] Wr]. split; [cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
    cbn [cells_size csize Nat.add] in Wr. rewrite LEN30. exact Wr. }
  pose proof LEN30 as LEN3.
  (* [comment removed for export] *)
  assert (HP2 : aheap_pres asegs ACONSTS LB LF usp m2 m3).
  { eapply aheap_pres_sp_mono; [eapply (aw_client_pres_all E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (sA a1 s) LB LF m2 mo1 W3 m3 mo2 aa2 lo (usp - 2208) AH1 LOC ltac:(clear -LO; lia) MUA WM3 FWA)| clear; lia].
    - cbn [aps_alloc sA aps_set_alloc]. rewrite MLB. exact FBA.
    - exact WF2. - exact K2. }
  (* [comment removed for export] *)
  subst a0'. destruct AR as (AR1 & AR2 & AR3 & AR4 & AR5). cbn [c_img_hi ACONSTS] in AR5.
  set (LB2 := mkABlock rnew n :: LB).
  set (sq := mkAPS (aps_env s) aa2 (aps_fs s) (aps_fsbase s) (aps_so s) (aps_errno s) (aps_initialized s) (aps_credit s - acharge n)).
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK2) as (R2 & R2' & ATOK2 & _ & _).
  assert (BM2 : blocks_match LB2 aa2).
  { unfold blocks_match. subst LB2. cbn [map ab_addr ab_size]. etransitivity; [| apply Permutation_sym; exact PERM]. apply perm_skip. rewrite MLB. exact Hbm. }
  pose proof ACCT as (AC1 & AC2 & AC3 & AC4). pose proof Hbud1 as (BV0 & BV1 & BV2 & BV3). cbn [aps_credit sA aps_set_alloc] in BV0, BV3.
  assert (AH2 : AHKc sq LB2 LF m3 mo2).
  { unfold AF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              (sA a1 s) sq LB LF m2 mo1 aa2 m3 mo2 LB2 W3 lo (usp - 2208) R2 R2' AH1);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hrep2| exact WF2| exact K2| exact RO2| exact QB2| exact DI2| exact BI2| exact SS2| exact CS2| exact BM2| exact ATOK2| exact MI3| exact MUA| exact FWA| exact LOC
      | cbn [aps_credit sq]; clear -CHG; lia
      | clear -BV1 AC1; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
      | clear -BV2 AC2; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
      | ].
    cbn [aps_credit aps_alloc sq sA aps_set_alloc]. subst LB2. rewrite DEP_cons. cbn [ab_size]. cstat. clear -AC4. unset_all. lia. }
  (* [comment removed for export] *)
  assert (HLIVE2 : In (A, sz) (live_blocks aa2)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| right; rewrite MLB; exact HLIVE]).
  assert (HNEW2 : In (rnew, n) (live_blocks aa2)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| left; reflexivity]).
  assert (RNEWFRESH : forall blo bsz, In (blo, bsz) (live_blocks (aps_alloc s)) -> rnew <> blo).
  { intros blo bsz Hin E. pose proof (live_blocks_nodup E0 aa2 WF2) as ND. pose proof (Permutation_NoDup (Permutation_map fst PERM) ND) as ND'.
    cbn [map fst] in ND'. apply NoDup_cons_iff in ND' as [NI _]. apply NI. rewrite MLB. apply in_map_iff. exists (blo, bsz). split; [cbn; symmetry; exact E| exact Hin]. }
  assert (NEQ : rnew <> A) by (exact (RNEWFRESH A sz HLIVE)).
  pose proof (live_blocks_sep E0 aa2 _ _ _ _ WF2 HLIVE2 HNEW2 ltac:(clear -NEQ; congruence)) as SEP.
  destruct (old_header aa2 m3 A sz WF2 Hrep2 HLIVE2) as (SZB & hb1 & hid & HDR3).
  (* [comment removed for export] *)
  assert (OLD2 : bytes_at asegs m2 A old).
  { eapply bytes_at_transport; [exact HOLD| exact MU1|]. rewrite HLEN.
    unfold preW, AF_shell_rep5.IA. cbn [disjoint_from]. clear -GA1 GA2 GA4 GAT LOC. lia. }
  assert (OLD3 : bytes_at asegs m3 A old) by (eapply (live_bytes_pres W3 m2 m3 (live_blocks a1) A sz old MUA FBA ltac:(rewrite MLB; exact HLIVE) HLEN OLD2)).
  destruct (shell_facts2_of _ _ _ _ _ AH2) as (_ & _ & _ & _ & _ & GOTM3 & RMV3).
  (* [comment removed for export] *)
  set (mn := Z.min n sz) in *.
  assert (HM : 0 <= mn <= sz /\ mn <= n) by (subst mn; clear -Hn2 GA4; lia).
  assert (NEW3 : rw_cells asegs m3 rnew [CB (Z.to_nat mn) (firstn (Z.to_nat mn) junk); CB (Z.to_nat (n - mn)) (skipn (Z.to_nat mn) junk)]).
  { eapply rw_cells_reshape; [| | exact JC].
    - cbn. rewrite length_firstn, length_skipn. clear -HM LJ. repeat split; lia.
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. rewrite firstn_skipn. reflexivity. }
  (* [comment removed for export] *)
  pose proof AH2 as AH2c. unfold AF_tkit.AHKc in AH2c.
  destruct AH2c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkm2 & Hli2 & _ & _ & Henv2 & _). destruct Hkm2 as (Khalt2 & Kminv2 & Klim2).
  pose proof (proj1 WF2) as WE2.
  assert (K2q : AKern E0 (aps_alloc sq) mo2) by exact K2.
  assert (PSTK2 : forall a'' k, lo <= a'' -> a'' + Z.of_nat k <= 2^64 -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 sq mo2 K2q WE2 ENV0); clear -H1 H2 LOC; lia. }
  assert (PDAT2 : forall a'' k, 0xa4000 <= a'' -> a'' + Z.of_nat k <= 0x603000 -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 sq mo2 K2q WE2 Henv2 ENV0); clear -H1 H2; lia. }
  assert (PBLK : forall blo bsz a'' k, In (blo, bsz) (live_blocks aa2) -> blo - 16 <= a'' -> a'' + Z.of_nat k <= blo + bsz -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros blo bsz a'' k Hin H1 H2. pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 sq LB2 LF m3 mo2 _ _ AH2 Hin) as (B1 & B2 & _).
    eapply (acc_ok_of_lazy_disjoint mo2 (aS E0 FSB0 HR0 sq) (blo - 16) (blo + bsz)); [| clear -B1; lia| clear -B2 CEILB; lia| exact H1| exact H2].
    eapply (lazy_disjoint_block E0 FSB0 sq mo2 blo bsz); [cbn [aps_env aps_alloc sq]; rewrite EE; exact K2| cbn [aps_env aps_alloc sq]; rewrite EE; exact WF2| exact Henv2| exact Hin]. }
  assert (KIP2 : KIP (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2) mo2) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH2)| intros x Hx; exact Hx]).
  assert (HA' : 0 < A < 2^47) by (clear -GA1 GA2 GA4 CEILB; lia).
  assert (HN' : 0 < n < 2^64) by (clear -Hn2; lia).
  eapply (rzA_seg_cfg asegs (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2)); [| exact KIP2|].
  { rewrite (ret_pc_even REA_ALLOC_RET) by (unfold REA_ALLOC_RET; clear; lia).
    eapply (rea_mid (PP sq mo2) gp (wz 0x5e0b10) s7 s8 s9 s10 s11 F fc usp A n HA' HN' PDAT2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 rnew sz hb1 (wz hid) old (firstn (Z.to_nat mn) junk) (skipn (Z.to_nat mn) junk));
      [exact MI3| clear -GA2 CEILB; lia| exact AR1| clear -AR4 Hn2 CEILB; lia| clear -SZB; lia| exact HDR3| exact GOTM3| exact RMV3| exact OLD3| rewrite <- HLEN, Nat2Z.id; reflexivity| exact NEW3| exact SEP
      | intros a'' k H1 H2; eapply (PBLK A sz); [exact HLIVE2| exact H1| exact H2]
      | intros a'' k H1 H2; eapply (PBLK rnew n); [exact HNEW2| clear -H1; lia| exact H2] ]. }
  intros ms5 mo3 POST5 Hag5 KP5.
  destruct POST5 as (v0 & v1 & v2 & v6 & v7 & v3 & v4 & v5 & v8 & m4 & -> & MI4 & WM4 & MU4 & DST4 & OLD4).
  (* [comment removed for export] *)
  assert (AH3 : AHKc sq LB2 LF m4 mo3).
  { unfold AF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 sq LB2 LF m4 mo2 mo3); [| exact Hag5| exact (proj1 (proj1 KP5))].
    eapply (AHK_frame_cl SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where
              sq LB2 LF m3 m4 mo2 _ AH2 MU4 WM4).
    constructor; [| apply Forall_nil]. right; left. exists (mkABlock rnew n). split; [left; reflexivity| cbn [ab_addr ab_size fst snd]; clear -HM; lia]. }
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ (RTOK_aps E0 FSB0 HR0 L0 RES0 EB0 _ _ _ sq _ TOK2 eq_refl eq_refl eq_refl) Hag5 (proj1 KP5)) as TOK3.
  pose proof AH3 as AH3c. unfold AF_tkit.AHKc in AH3c.
  destruct AH3c as (Hrep3 & Hwf3 & Hkern3 & _ & Hres3 & Hqb3 & Hdi3 & Hbinv3 & Hbm3 & _ & _ & _ & _ & Hrt3 & _ & Hkm3 & Hli3 & Hbud3 & Hmi3 & Henv3 & _ & Hss3 & Hcs3).
  cbn [aps_alloc aps_env aps_fsbase sq] in Hrep3, Hwf3, Hkern3, Hres3, Hqb3, Hdi3, Hbinv3, Hbm3, Hrt3, Hbud3, Henv3, Hss3, Hcs3. rewrite EE in *.
  assert (AINV3 : AINV E0 FSB0 PL0 aa2 m4 mo3).
  { split; [exact Hrep3|]. split; [exact Hwf3|]. split; [exact Hkern3|]. split; [exact Hres3|]. split; [exact Hqb3|]. split; [exact Hdi3|]. split; [exact Hbinv3|]. split; [exact MI4| split; [exact Hrt3| split; [exact Hss3| exact Hcs3]]]. }
  assert (FBUD : fbudget_pre aa2).
  { pose proof Hbud3 as (BW0 & BW1 & BW2 & BW3). unfold ACC in BW3. cbn [aps_credit aps_alloc sq] in BW0, BW1, BW2, BW3.
    pose proof (DEP_nonneg LB2) as DEPnn. pose proof (AsanBudget2.zlen_nonneg (as_residue aa2)) as ZR. unfold fbudget_pre. cstat. clear -BW1 BW2 BW3 DEPnn ZR CHG. unset_all. lia. }
  assert (BLKHI : rnew + n <= lo) by (clear -AR4 LOC; lia).
  Ltac xfer4 H MU4 WM4 BLKHI HM LO := eapply (fun (RC : rw_cells asegs _ _ _) => rw_cells_transport asegs _ _ _ _ _ RC MU4 WM4) in H; [| cbn; clear -BLKHI HM LO; lia].
  assert (SK4 : stk asegs m4 lo (usp - 2208)) by (eapply stk_transport_disjoint; [exact SK3| exact MU4| exact WM4| cbn; clear -BLKHI HM LO; lia]).
  xfer4 FR6 MU4 WM4 BLKHI HM LO. xfer4 FRA MU4 WM4 BLKHI HM LO. xfer4 FJ8B MU4 WM4 BLKHI HM LO. xfer4 OBJ MU4 WM4 BLKHI HM LO.
  xfer4 FJ1800 MU4 WM4 BLKHI HM LO. xfer4 FBP MU4 WM4 BLKHI HM LO. xfer4 FJ8 MU4 WM4 BLKHI HM LO. xfer4 FR8 MU4 WM4 BLKHI HM LO.
  assert (ARR4 : u64arr asegs m4 (usp + -2120) ws) by (eapply u64arr_transport; [exact ARR3| exact MU4| exact WM4| rewrite LEN3; cbn; clear -BLKHI HM LO; lia]).
  assert (OBJ4 : rw_cells asegs m4 (usp + -2136) [C8 (wz (usp + -2120)); C8 (wz (Z.of_nat (length tr)))]) by (apply obj_c8; [clear -LTR; lia| exact OBJ]).
  (* [comment removed for export] *)
  eapply (DEALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4 mo3 sq A sz lo (usp + -2136) (usp + -2120) (Z.of_nat (length tr)) (aps_credit s - acharge n) (OPSLACK - ASLACK) ws K);
    [ exact KN | exact TOK3 | clear -CHG; lia | unfold OPSLACK, ASLACK, FSLACK; clear; lia | exact AINV3 | exact FBUD | exact HLIVE2
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); exact SK4 | exact LOC
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); unfold K_FREE; clear -LO; lia
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear -SPA; Z.div_mod_to_equations; lia
    | reflexivity
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear; lia
    | clear; lia
    | unfold zlen; rewrite LEN3; clear -SPH LO LOC CEILB; lia
    | exact OBJ4 | exact ARR4
    | unfold zlen; rewrite LEN3; clear -LTR; lia
    | unfold zlen; rewrite LEN3; clear; lia | ].
  cbv beta. intros w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m5 mo4 aa3 POST6.
  destruct POST6 as (SK5 & (W5 & MUD & FWD & FBD) & RUN2 & AINV5 & TOK5 & Ffs5 & Ffds5 & Ftid5 & FACCT & PERM2).
  rewrite unsigned_lit in SK5, FWD by (clear -LO LOC USPR CEILB; lia).
  cbn [aps_alloc sq] in FWD, FBD, RUN2, FACCT, PERM2, TOK5.
  pose proof AINV5 as (Hrep5 & WF5 & K5 & RO5 & QB5 & DI5 & BI5 & MI5 & Hrt5 & SS5 & CS5).
  (* [comment removed for export] *)
  destruct (AHK_blocks _ _ _ _ _ _ _ _ s LB LF m mo AH0) as (_ & _ & NDLB).
  destruct (ab_remove_split A sz LB NDLB HLB) as [DEPR PERMR].
  set (LB3 := mkABlock rnew n :: ab_remove A LB).
  set (sr := mkAPS (aps_env s) aa3 (aps_fs s) (aps_fsbase s) (aps_so s) (aps_errno s) (aps_initialized s) (aps_credit s - acharge n - 1 + arefund sz)).
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK5) as (R4 & R4' & ATOK4 & _ & _).
  assert (BM3 : blocks_match LB3 aa3).
  { unfold blocks_match. subst LB3. cbn [map ab_addr ab_size]. apply Permutation_cons_inv with (a := (A, sz)).
    etransitivity; [apply perm_swap|]. etransitivity; [apply perm_skip; apply Permutation_sym; exact PERMR|].
    etransitivity; [| exact PERM2]. exact BM2. }
  pose proof Hbud3 as (BW0 & BW1 & BW2 & BW3). cbn [aps_credit aps_alloc sq] in BW0, BW1, BW2, BW3.
  pose proof FACCT as (FA1 & FA2 & FA3). pose proof (arefund_nonneg sz) as RFN.
  assert (AH4 : AHKc sr LB3 LF m5 mo4).
  { unfold AF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              sq sr LB2 LF m4 mo3 aa3 m5 mo4 LB3 W5 lo (usp - 2208) R4 R4' AH3);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hrep5| exact WF5| exact K5| exact RO5| exact QB5| exact DI5| exact BI5| exact SS5| exact CS5| exact BM3| exact ATOK4| exact MI5| exact MUD| exact FWD| exact LOC
      | cbn [aps_credit sr]; clear -CHG RFN; lia
      | clear -BW1 FA1; unset_all; lia
      | clear -BW2 FA3; unset_all; lia
      | ].
    clear -FA1 FA2 FA3 DEPR. unset_all. cbn [aps_credit aps_alloc].
    rewrite !DEP_cons. cbn [ab_size]. rewrite FA1, FA2. lia. }
  (* [comment removed for export] *)
  pose proof AH4 as AH4c. unfold AF_tkit.AHKc in AH4c.
  destruct AH4c as (_ & WF6 & K6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkm4 & Hli4 & _ & _ & Henv4 & _). destruct Hkm4 as (Khalt4 & Kminv4 & Klim4).
  cbn [aps_alloc aps_env sr] in WF6, K6. rewrite EE in WF6, K6.
  assert (K6q : AKern E0 (aps_alloc sr) mo4) by exact K6. pose proof (proj1 WF6) as WE6.
  assert (PSTK4 : forall a'' k, lo <= a'' -> a'' + Z.of_nat k <= 2^64 -> PP sr mo4 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 sr mo4 K6q WE6 ENV0); clear -H1 H2 LOC; lia. }
  assert (KIP4 : KIP (aS E0 FSB0 HR0 sr) (aN E0 FSB0 HR0 sr) (aEB EB0 sr) (PP sr mo4) mo4) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH4)| intros x Hx; exact Hx]).
  (* [comment removed for export] *)
  assert (AGS : forall X k, usp - 2208 <= X -> X + k <= usp -> agree_on m4 m5 X k).
  { intros X k H1 H2. eapply (above_sp_agree aa2 aa3 mo4 lo (usp - 2208) W5 m4 m5); [exact MUD| exact FWD| exact WF2| exact WF5| exact K5| exact H1| clear -H1 LO LOC; lia| clear -H2 USPR; lia]. }
  Ltac xfer5 H AGS := eapply rw_cells_agree' in H; [| apply AGS; cbn; clear; lia].
  xfer5 FR6 AGS. xfer5 FRA AGS. xfer5 FJ8B AGS. xfer5 OBJ AGS. xfer5 FJ1800 AGS. xfer5 FBP AGS. xfer5 FJ8 AGS. xfer5 FR8 AGS.
  assert (ARR5 : u64arr asegs m5 (usp + -2120) ws) by (apply (u64arr_agree m4 m5 (usp + -2120) ws); [apply AGS; rewrite ?LEN3; cbn; clear; lia| exact ARR4]).
  eapply (rzA_seg_cfg asegs (aS E0 FSB0 HR0 sr) (aN E0 FSB0 HR0 sr) (aEB EB0 sr) (PP sr mo4)); [| exact KIP4|].
  { eapply (rea_suf_ok (PP sr mo4) gp (wz 0x5e0b10) s7 s8 s9 s10 s11 F fc usp lo A n (fp_ctx PL0) (ae_thread E0) LOC ltac:(clear -LO; lia) SPH SPA HCTX HT PSTK4
              ra s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ _ _ _ _ _ _ _ s4w _ _ _ _ bpw m5 rnew j8 j8b j8c j1800 ws (Z.of_nat (length tr)));
      [exact SK5| exact MI5| clear -AR1 AR4 Hn2 CEILB; lia| exact FR6| exact FRA| exact FJ8B| exact OBJ| exact ARR5| exact LEN3| exact FJ1800| exact FBP| exact FJ8| exact FR8]. }
  intros ms7 mo5 POST7 Hag7 KP7.
  destruct POST7 as (u0 & u1 & u2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & u3 & u4 & u5 & u6 & m6 & -> & _ & MI6 & SK6 & WM6 & MU6 & _).
  assert (AH5 : AHKc sr LB3 LF m6 mo5).
  { unfold AF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 sr LB3 LF m6 mo4 mo5); [| exact Hag7| exact (proj1 (proj1 KP7))].
    eapply (AHK_frame_cl SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where
              sr LB3 LF m5 m6 mo4 _ AH4 MU6 WM6).
    constructor; [left; cbn [fst]; clear -LO LOC; lia| constructor]. }
  (* [comment removed for export] *)
  pose proof (magree_frame _ _ Hag5) as (Qfds5 & Qvm5 & Qlz5 & Qfs5 & _). pose proof (magree_frame _ _ Hag7) as (Qfds7 & Qvm7 & Qlz7 & Qfs7 & _).
  assert (SUBR : forall b, In b (ab_remove A LB) -> In b LB) by (intros b Hb; exact (ab_remove_sub _ _ _ Hb)).
  apply (CONT u0 u1 u2 (wz rnew) z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 F fc m6 mo5 sr rnew); [exact SK6| exact FRM| reflexivity| | | | cbn [aps_credit sr]; clear -RFN; lia| reflexivity| | exact AH5| | | |].
  - (* [comment removed for export] *)
    split; [| split; [cbn [aps_credit sr]; clear -RFN; lia| repeat split; reflexivity]].
    destruct RUN1 as (f1 & orc1 & evs1 & orc1' & RUN1). destruct RUN2 as (f2 & orc2 & evs2 & orc2' & RUN2).
    subst a1 ts1 ts. rewrite shell_st_ts0 in RUN1.
    destruct (arun_orc_app _ _ _ _ _ _ _ RUN1) as (used & _ & RUNX).
    destruct (live_block_meta E0 [] [] aa2 A sz WF2 HLIVE2) as (meta & aid & Hm & STm & UBm & _).
    destruct (arealloc_run_some E0 (bst_key (Z.of_nat (length tr)) ws) A n (aps_alloc s) f1 f2 (used ++ orc2) aa2 rnew evs1 orc2 meta aid aa3 evs2 orc2'
                ltac:(clear -GA1; lia) ltac:(clear -Hn2; lia) (RUNX orc2) Hm STm UBm RUN2) as [f RUN].
    cbn [aps_alloc sr]. exists (bst_key (Z.of_nat (length tr)) ws), f, (used ++ orc2), (evs1 ++ evs2), orc2'. exact RUN.
  - rewrite Qfs7, Ffs5, Qfs5, Ffs2, Qfs1. reflexivity.
  - rewrite Qfds7, Ffds5, Qfds5, Ffds2, Qfds1. reflexivity.
  - split; [exact AR1|]. split; [exact AR2|]. split; [exact AR3|]. split; [exact AR4| cbn [c_img_hi ACONSTS]; exact AR5].
  - rewrite (arefund_at_found A sz LB NDLB HLB). cbn [aps_credit sr]. clear; lia.
  - (* [comment removed for export] *)
    eapply aheap_pres_trans; [eapply aheap_pres_sub; [exact SUBR| exact HP1]|].
    eapply aheap_pres_trans; [eapply aheap_pres_sub; [exact SUBR| exact HP2]|].
    eapply aheap_pres_trans.
    { eapply aheap_pres_sp_mono with (SP' := usp - 2208); [| clear; lia].
      eapply (aw_client_pres E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK sq LB2 LF m3 mo2 aa2 mo2 m4 [(rnew, rnew + mn)] lo (usp - 2208) (ab_remove A LB) AH2 WF2 K2 MU4 WM4);
        [constructor; [apply (live_block_aw_ok E0 aa2 aa2 rnew n); [exact WF2| exact HNEW2| clear; lia| clear -HM; lia]| apply Forall_nil]| exact LOC| clear -LO; lia|].
      intros b Hb. pose proof (SUBR b Hb) as HbL. split; [right; exact HbL|].
      constructor; [| apply Forall_nil]. cbn [fst snd].
      pose proof (blocks_match_In _ _ _ Hbm HbL) as HbA.
      assert (HbA2 : In (ab_addr b, ab_size b) (live_blocks aa2)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| right; rewrite MLB; exact HbA]).
      pose proof (live_blocks_sep E0 aa2 _ _ _ _ WF2 HNEW2 HbA2 (RNEWFRESH _ _ HbA)) as D. clear -D HM. lia. }
    eapply aheap_pres_trans.
    { eapply aheap_pres_sp_mono with (SP' := usp - 2208); [| clear; lia].
      eapply (aw_client_pres_nw E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK sq LB2 LF m4 mo3 aa3 mo4 m5 W5 lo (usp - 2208) (ab_remove A LB) AH3 WF5 K5 MUD);
        [exact FWD| exact LOC| clear -LO; lia|].
      intros b Hb. pose proof (SUBR b Hb) as HbL. split; [right; exact HbL|].
      apply Forall_forall. intros iv Hiv.
      pose proof (blocks_match_In _ _ _ Hbm HbL) as HbA.
      assert (HbA2 : In (ab_addr b, ab_size b) (live_blocks aa2)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| right; rewrite MLB; exact HbA]).
      apply (proj1 (Forall_forall _ _) FBD iv Hiv (ab_addr b) (ab_size b) HbA2).
      intros E. injection E as E1 E2. exact (ab_remove_neq A LB b NDLB Hb E1). }
    eapply aheap_pres_sub; [| eapply (aheap_pres_shell E0 FSB0 HR0 L0 RES0 EB0 PL0 _ _ _ _ _ _ _ _ AH4 MU6 WM6); [clear -LO LOC; lia| constructor; [left; cbn; clear -LO LOC; lia| apply Forall_nil]]].
    intros b Hb. subst LB3. right. exact Hb.
  - (* [comment removed for export] *)
    exists (skipn (Z.to_nat mn) junk).
    assert (DST5 : rw_cells asegs m5 rnew [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old); CB (Z.to_nat (n - mn)) (skipn (Z.to_nat mn) junk)]).
    { eapply rw_cells_agree'; [| exact DST4]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat2Z.inj_add, !Z2Nat.id in Hx by (clear -HM Hn2; lia).
      apply MUD. rewrite wa_unsigned by (clear -Hx AR1 AR4 HM CEILB; lia). eapply outside_of_Forall; [exact FBD|]. intros iv Hiv R.
      destruct (Hiv rnew n HNEW2 ltac:(intros E; injection E as E1 E2; exact (NEQ E1))) as [X|[X|X]]; clear -Hx R X HM; lia. }
    eapply rw_cells_transport; [exact DST5| exact MU6| exact WM6| cbn [cells_size csize Nat.add disjoint_from]; rewrite Nat2Z.inj_add, !Z2Nat.id by (clear -HM Hn2; lia); clear -AR4 HM LOC LO Hn2; lia].
  - (* [comment removed for export] *)
    exact (proj1 (AHK_block_oshadow SR RT E0 FSB0 HR0 L0 RES0 EB0 sr LB3 LF m6 mo5 (mkABlock rnew n) AH5 ltac:(left; reflexivity) ltac:(cbn [ab_size]; clear -Hn2; lia))).
Qed.

(* [comment removed for export] *)
Lemma shell_st_ia0 : forall a, shell_st true (as_ts a) a = ia0 a.
Proof. intros a. destruct a. reflexivity. Qed.

Lemma aw_ok_preW0 : forall a a' lo usp, Forall (aw_ok E0 a a' lo usp) (preW0 usp lo (ae_thread E0)).
Proof.
  cstat. intros a a' lo usp. pose proof (aw_ok_preW a a' lo usp) as H. unfold preW in H. unfold preW0.
  repeat match type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] end.
  repeat (apply Forall_cons; [assumption|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
Theorem realloc_null_contract : arealloc_null_rz_stmt asegs ACONSTS aps AHKc aps_so (arealloc_rel E0) aps_credit acharge (AF_unwind.uanchor asegs).
Proof.
  unfold arealloc_null_rz_stmt. intros until K. intros KN AH SK LOC LO SPA SPH TP UA FRM A0 A1 Hn2 CHG NBIG CONT. subst a0 a1 tp. cbn [c_tp ACONSTS]. unfold KLink.wz. cbn [c_wrap_realloc ACONSTS].
  destruct (shell_facts_of E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK _ _ _ _ _ AH) as (Gai & Gmcs & GCF & Gfu & GPSC & Gps & TC & HCTX & HT & HTC & HTB & (c0 & cl & RRC & CLO & CHI)).
  destruct (shell_facts2_of _ _ _ _ _ AH) as (Gia & Gipv & Giz & Giwr & STATS & GOTM & RMV).
  pose proof AH as AH0. unfold AF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in *.
  destruct Hkm as (Khalt & Kminv & Klim).
  pose proof (bv_unsigned_in_range 64 sp) as USPR. unfold bv_modulus in USPR. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned). rewrite Esp in CONT |- *. clear Esp Husp.
  pose proof (proj1 Hwf) as WE.
  (* [comment removed for export] *)
  assert (PSTK : forall a' k, lo <= a' -> a' + Z.of_nat k <= 2^64 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC; lia. }
  assert (PDAT : forall a' k, 0xa4000 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENVOK0 ENV0); clear -H1 H2; lia. }
  assert (PCTX : PP s mo (Z_to_bv 64 (fp_ctx PL0 + 152), 8%nat)).
  { rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 s mo Hkern c0 cl); [exact RRC| clear -CLO; lia| clear -CHI; cbn; lia]. }
  assert (PTHR : forall a' k, ae_thread E0 <= a' -> a' + Z.of_nat k <= ae_thread E0 + 4096 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); assumption. }
  assert (KIP0 : KIP (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo) mo) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH0)| intros x Hx; exact Hx]).
  assert (HN' : 0 < n < 2^64) by (clear -Hn2; lia).
  assert (HTSD' : 0x5cfdd0 <= 0x601eb8 /\ 0x601eb8 + 8 <= 0x603000) by (clear; lia).
  assert (HTP' : 0x5cfdd0 + 88 <= bv_unsigned (wz 0x5e0b10) /\ bv_unsigned (wz 0x5e0b10) + 60 <= 0x603000) by (rewrite unsigned_lit by (clear; lia); clear; lia).
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg asegs (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo)); [| exact KIP0|].
  { stepA.
    lazymatch goal with |- evtA _ _ _ (MS ?r ?f ?pc ?x1 ?x2 ?x3 ?x4) => let v := eval vm_compute in (bv_unsigned pc) in change pc with (Z_to_bv 64 v) end.
    eapply (rea0_pre (PP s mo) gp (wz 0x5e0b10) t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo n (as_ia_inited (aps_alloc s)) (zeros (Z.to_nat 0x40000)) 0x601eb8 (fp_ctx PL0) (ae_thread E0) (ae_stack_top E0) (ae_stack_bottom E0)
              LOC ltac:(clear -LO; lia) SPH HTB HN' ltac:(unfold zeros; reflexivity) HTSD' HCTX HT HTC HTP' PSTK PDAT PCTX PTHR);
      [ exact SK| exact Hmi| exact Gai| exact GPSC| exact Gps| exact Gmcs| exact GCF| exact Gfu| exact Gia
      | exact Giwr| exact Giz| unfold IA in Gipv; exact Gipv| exact TC| exact UA ]. }
  intros ms2 mo1 POST1 Hag1 KP1.
  destruct POST1 as (t0' & t1' & a7' & s4w & m2 & ws & tr & bpw & j1800 & j8 & j8b & j8c & -> & MU1 & WM1 & MI2 & SK2 & IAF2 & IPV2 & IZ2 & IWR2 & TU2 & OBJ & ARR & LEN30 & FTR & LTR
                       & FR8 & FJ1800 & FBP & FJ8 & FJ8B & FRA).
  (* [comment removed for export] *)
  set (ts := as_ts (aps_alloc s)) in *. set (a1 := shell_st true ts (aps_alloc s)).
  pose proof (model_shell_st E0 true ts (aps_alloc s)) as (MW & MR & MQ & MD & MB & MLB & MNP & MND & MRES & MIA & MTS & MSS & MCS).
  fold a1 in MW, MR, MQ, MD, MB, MLB, MNP, MND, MRES, MIA, MTS, MSS, MCS.
  pose proof (blocks_sep_of E0 (aps_alloc s) mo ENV0 Hwf Hkern) as BS0.
  pose proof (magree_frame _ _ Hag1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & _).
  assert (K1 : AKern E0 a1 mo1) by (apply AKern_shell_st; eapply AKern_frame; [exact Qvm1| exact Qlz1| exact Hkern]).
  assert (FWpre : Forall (shell_iv E0 lo) (preW0 usp lo (ae_thread E0))).
  { unfold preW0, shell_iv. repeat apply Forall_cons; cbn [fst snd]; [left; clear; lia| right; left; unfold AF_shell_rep5.IA; clear; lia| right; right; left; clear; lia
      | do 4 right; clear; lia| apply Forall_nil]. }
  pose proof TU2 as (TC2 & T40b & T8b & TUNW2).
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGE). rewrite EE in IMGE.
  assert (ST2 : rw_cells asegs m2 (ae_thread E0 + 2856) [C8 (wz (ts_reallocs ts)); C8 (wz (ts_realloced ts))]).
  { eapply rw_cells_transport; [exact STATS| exact MU1| exact WM1| unfold preW0, AF_shell_rep5.IA; cbn; clear -HT LOC CEILB; lia]. }
  assert (REP1 : ARep asegs E0 DR a1 m2).
  { subst a1. eapply (ARep_shell E0 PL0 ENV0 PL0OK IMGE (aps_alloc s) m m2 mo (preW0 usp lo (ae_thread E0)) lo true ts);
      [exact Hrep| exact Hwf| exact Hkern| exact BS0| exact WM1| exact MU1| exact LOC| exact FWpre| exact IAF2| intros _; exact IPV2| exact IZ2
      | apply ts_agree78_refl| exact ST2| exact TUNW2]. }
  pose proof (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot s LB LF m mo AH0 NBIG) as TOK0.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK0 Hag1 (proj1 KP1)) as TOK0'. rewrite <- (sA_self s) in TOK0'.
  pose proof (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s (aps_alloc s) a1 mo1 TOK0' (same_fp_shell_st true ts (aps_alloc s)) MNP MND) as TOK1.
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK1) as (R1 & R1' & ATOK1 & _ & _).
  pose proof Hbud as (BU0 & BU1 & BU2 & BU3).
  assert (AH1 : AHKc (sA a1 s) LB LF m2 mo1).
  { unfold AF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              s (sA a1 s) LB LF m mo a1 m2 mo1 LB (preW0 usp lo (ae_thread E0)) lo usp R1 R1' AH0);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact REP1| exact (MW Hwf)| exact K1| exact (MR Hres)| exact (MQ Hqb)| exact (MD Hdi)| exact (MB Hbinv)| exact (MSS Hss)| exact (MCS Hcs)
      | unfold blocks_match; rewrite MLB; exact Hbm| exact ATOK1| exact MI2| exact MU1| apply aw_ok_preW0| exact LOC
      | cbn [aps_credit sA aps_set_alloc]; exact BU0| rewrite MNP; exact BU1| rewrite MND; exact BU2| ].
    cbn [aps_credit aps_alloc sA aps_set_alloc]. rewrite MNP, MND, MRES. clear. lia. }
  assert (HP1 : aheap_pres asegs ACONSTS LB LF usp m m2).
  { eapply (aw_client_pres E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK s LB LF m mo a1 mo1 m2 (preW0 usp lo (ae_thread E0)) lo usp LB AH0 (MW Hwf) K1 MU1 WM1);
      [apply aw_ok_preW0| exact LOC| clear -LO; lia|].
    intros b Hb. split; [exact Hb|]. pose proof (blocks_match_In _ _ _ Hbm Hb) as HbL.
    pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HbL) as [B1 B2].
    pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo _ _ AH0 HbL) as (B3 & _).
    unfold preW0, AF_shell_rep5.IA. repeat apply Forall_cons; cbn [fst snd];
      [clear -B1 LOC; lia| clear -B3; lia| clear -B3; lia| clear -B2; lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot (sA a1 s) LB LF m2 mo1 AH1 NBIG) as TOKA.
  cbn [aps_credit sA aps_set_alloc] in TOKA.
  pose proof AH1 as AH1c. unfold AF_tkit.AHKc in AH1c.
  destruct AH1c as (Hrep1 & Hwf1 & Hkern1 & _ & Hres1 & Hqb1 & Hdi1 & Hbinv1 & Hbm1 & _ & _ & _ & _ & Hrt1 & _ & _ & _ & Hbud1 & Hmi1 & Henv1 & _ & Hss1 & Hcs1).
  cbn [aps_alloc aps_env aps_fsbase sA aps_set_alloc] in Hrep1, Hwf1, Hkern1, Hres1, Hqb1, Hdi1, Hbinv1, Hbm1, Hrt1, Hbud1, Henv1, Hss1, Hcs1. rewrite EE in *.
  assert (AINV1 : AINV E0 FSB0 PL0 a1 m2 mo1).
  { split; [exact Hrep1|]. split; [exact Hwf1|]. split; [exact Hkern1|]. split; [exact Hres1|]. split; [exact Hqb1|]. split; [exact Hdi1|]. split; [exact Hbinv1|]. split; [exact MI2| split; [exact Hrt1| split; [exact Hss1| exact Hcs1]]]. }
  assert (ABUD : abudget_pre a1 n).
  { unfold abudget_pre. rewrite MNP, MND. unfold ACC in BU3.
    pose proof (DEP_nonneg LB) as DEPnn. pose proof (AsanBudget2.zlen_nonneg (as_residue (aps_alloc s))) as ZR. cstat. clear -BU0 BU1 BU2 BU3 DEPnn ZR CHG. unset_all. lia. }
  assert (NBL : nbig_live a1 <= 8000).
  { unfold nbig_live. rewrite MLB. unfold nbig in NBIG. unfold blocks_match in Hbm.
    assert (FM : forall (l : list ablock), List.filter (fun b : Z * Z => 64512 <? snd b) (map (fun b => (ab_addr b, ab_size b)) l)
                                        = map (fun b => (ab_addr b, ab_size b)) (List.filter (fun b => 64512 <? ab_size b) l)).
    { clear. induction l as [|b l IH]; [reflexivity|]. cbn [map List.filter snd]. destruct (64512 <? ab_size b); cbn [map]; rewrite IH; reflexivity. }
    rewrite <- (Permutation_length (Permutation_filterb _ _ _ Hbm)), FM, length_map. exact NBIG. }
  assert (OBJ2 : rw_cells asegs m2 (usp + -2136) [C8 (wz (usp + -2120)); C8 (wz (Z.of_nat (length tr)))]) by (apply obj_c8; [clear -LTR; lia| exact OBJ]).
  (* [comment removed for export] *)
  eapply (ALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mo1 (sA a1 s) n lo (usp + -2136) (usp + -2120) (Z.of_nat (length tr)) (aps_credit s) OPSLACK ws K);
    [ exact KN | exact TOKA | clear -CHG; lia | unfold ASLACK, OPSLACK; clear; lia | exact AINV1 | exact ABUD | exact Hn2 | exact NBL
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); exact SK2 | exact LOC
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); unfold K_ALLOC; clear -LO; lia
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear -SPA; Z.div_mod_to_equations; lia
    | reflexivity
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear; lia
    | clear; lia
    | unfold zlen; rewrite LEN30; clear -SPH LO LOC CEILB; lia
    | exact OBJ2 | exact ARR
    | unfold zlen; rewrite LEN30; clear -LTR; lia
    | unfold zlen; rewrite LEN30; clear; lia | ].
  cbv beta. intros t0'' t1'' t2'' a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 mo2 aa2 rnew POST2.
  destruct POST2 as (SK3 & WM3 & (W3 & MUA & FWA & FBA) & RUN1 & AINV2 & TOK2 & Ffs2 & Ffds2 & Ftid2 & ACCT & EA0 & AR & PERM & [junk [LJ JC]] & BSH).
  rewrite unsigned_lit in SK3, FWA by (clear -LO LOC USPR CEILB; lia).
  cbn [aps_alloc sA aps_set_alloc] in FWA, FBA, RUN1, ACCT, PERM. rewrite sA_sA in TOK2.
  pose proof AINV2 as (Hrep2 & WF2 & K2 & RO2 & QB2 & DI2 & BI2 & MI3 & Hrt2 & SS2 & CS2).
  (* [comment removed for export] *)
  Ltac survive0 H MUA WM3 FWA Hwf1 WF2 K2 := eapply (shell_cells_pres E0 ENV0 _ _ _ _ _ _ _ _ _ _ MUA WM3 FWA Hwf1 WF2 K2) in H; [| lia| lia].
  pose proof (cb_of_u64arr asegs _ _ _ ARR) as ARRC. rewrite LEN30 in ARRC. cbn [Nat.mul] in ARRC.
  survive0 FRA MUA WM3 FWA Hwf1 WF2 K2. survive0 FJ8B MUA WM3 FWA Hwf1 WF2 K2.
  survive0 OBJ MUA WM3 FWA Hwf1 WF2 K2. survive0 ARRC MUA WM3 FWA Hwf1 WF2 K2. survive0 FJ1800 MUA WM3 FWA Hwf1 WF2 K2.
  survive0 FBP MUA WM3 FWA Hwf1 WF2 K2. survive0 FJ8 MUA WM3 FWA Hwf1 WF2 K2. survive0 FR8 MUA WM3 FWA Hwf1 WF2 K2.
  assert (ARR3 : u64arr asegs m3 (usp + -2120) ws).
  { destruct ARRC as [[_ B] Wr]. split; [cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
    cbn [cells_size csize Nat.add] in Wr. rewrite LEN30. exact Wr. }
  assert (HP2 : aheap_pres asegs ACONSTS LB LF usp m2 m3).
  { eapply aheap_pres_sp_mono; [eapply (aw_client_pres_all E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (sA a1 s) LB LF m2 mo1 W3 m3 mo2 aa2 lo (usp - 2160) AH1 LOC ltac:(clear -LO; lia) MUA WM3 FWA)| clear; lia].
    - cbn [aps_alloc sA aps_set_alloc]. rewrite MLB. exact FBA.
    - exact WF2. - exact K2. }
  (* [comment removed for export] *)
  subst a0'. destruct AR as (AR1 & AR2 & AR3 & AR4 & AR5). cbn [c_img_hi ACONSTS] in AR5.
  set (LB2 := mkABlock rnew n :: LB).
  set (sq := mkAPS (aps_env s) aa2 (aps_fs s) (aps_fsbase s) (aps_so s) (aps_errno s) (aps_initialized s) (aps_credit s - acharge n)).
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK2) as (R2 & R2' & ATOK2 & _ & _).
  assert (BM2 : blocks_match LB2 aa2).
  { unfold blocks_match. subst LB2. cbn [map ab_addr ab_size]. etransitivity; [| apply Permutation_sym; exact PERM]. apply perm_skip. rewrite MLB. exact Hbm. }
  pose proof ACCT as (AC1 & AC2 & AC3 & AC4). pose proof Hbud1 as (BV0 & BV1 & BV2 & BV3). cbn [aps_credit sA aps_set_alloc] in BV0, BV3.
  assert (AH2 : AHKc sq LB2 LF m3 mo2).
  { unfold AF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              (sA a1 s) sq LB LF m2 mo1 aa2 m3 mo2 LB2 W3 lo (usp - 2160) R2 R2' AH1);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hrep2| exact WF2| exact K2| exact RO2| exact QB2| exact DI2| exact BI2| exact SS2| exact CS2| exact BM2| exact ATOK2| exact MI3| exact MUA| exact FWA| exact LOC
      | cbn [aps_credit sq]; clear -CHG BV0; lia
      | clear -BV1 AC1; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
      | clear -BV2 AC2; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
      | ].
    cbn [aps_credit aps_alloc sq sA aps_set_alloc]. subst LB2. rewrite DEP_cons. cbn [ab_size]. cstat. clear -AC4. unset_all. lia. }
  (* [comment removed for export] *)
  pose proof AH2 as AH2c. unfold AF_tkit.AHKc in AH2c.
  destruct AH2c as (_ & WF2b & K2b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkm2 & Hli2 & _ & _ & Henv2 & _). destruct Hkm2 as (Khalt2 & Kminv2 & Klim2).
  cbn [aps_alloc aps_env sq] in WF2b, K2b. rewrite EE in WF2b, K2b.
  assert (K2q : AKern E0 (aps_alloc sq) mo2) by exact K2. pose proof (proj1 WF2) as WE2.
  assert (PSTK2 : forall a'' k, lo <= a'' -> a'' + Z.of_nat k <= 2^64 -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 sq mo2 K2q WE2 ENV0); clear -H1 H2 LOC; lia. }
  assert (KIP2 : KIP (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2) mo2) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH2)| intros x Hx; exact Hx]).
  eapply (rzA_seg_cfg asegs (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2)); [| exact KIP2|].
  { eapply (rea0_suf_ok (PP sq mo2) gp (wz 0x5e0b10) s7 s8 s9 s10 s11 F fc usp lo n (fp_ctx PL0) (ae_thread E0) LOC ltac:(clear -LO; lia) SPH SPA HCTX HT PSTK2
              ra s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ _ _ _ _ _ _ s4w _ _ _ _ bpw m3 rnew j8 j8b j8c j1800 ws (Z.of_nat (length tr)));
      [exact SK3| exact MI3| clear -AR1 AR4 Hn2 CEILB; lia| exact FRA| exact FJ8B| exact OBJ| exact ARR3| exact LEN30| exact FJ1800| exact FBP| exact FJ8| exact FR8]. }
  intros ms4 mo3 POST4 Hag3 KP3.
  destruct POST4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m6 & -> & _ & MI6 & SK6 & WM6 & MU6 & _).
  assert (AH3 : AHKc sq LB2 LF m6 mo3).
  { unfold AF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 sq LB2 LF m6 mo2 mo3); [| exact Hag3| exact (proj1 (proj1 KP3))].
    eapply (AHK_frame_cl SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where
              sq LB2 LF m3 m6 mo2 _ AH2 MU6 WM6).
    constructor; [left; cbn [fst]; clear -LO LOC; lia| apply Forall_nil]. }
  pose proof (magree_frame _ _ Hag3) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & _).
  apply (CONT u0 u1 u2 (wz rnew) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F fc m6 mo3 sq rnew); [exact SK6| | | exact FRM| reflexivity| | | | cbn [aps_credit sq]; clear; lia| reflexivity| | exact AH3| |].
  - eapply aheap_pres_trans; [exact HP1| eapply aheap_pres_trans; [exact HP2|]].
    eapply aheap_pres_sub with (LB := LB2); [intros b Hb; subst LB2; right; exact Hb|].
    eapply (aheap_pres_shell E0 FSB0 HR0 L0 RES0 EB0 PL0 _ _ _ _ _ _ _ _ AH2 MU6 WM6); [clear -LO LOC; lia|].
    constructor; [left; cbn; clear -LO LOC; lia| apply Forall_nil].
  - eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM3| exact WM6]].
  - split; [| split; [cbn [aps_credit sq]; clear; lia| repeat split; reflexivity]].
    destruct RUN1 as (fuel & orc & evs & orc' & RUN1). cbn [aps_alloc sq]. subst a1 ts. rewrite shell_st_ia0 in RUN1.
    destruct (arealloc_run_null E0 (bst_key (Z.of_nat (length tr)) ws) n (aps_alloc s) fuel orc aa2 (Some rnew) evs orc' RUN1) as [f' RUN'].
    exists (bst_key (Z.of_nat (length tr)) ws), f', orc, evs, orc'. exact RUN'.
  - rewrite Qfs3, Ffs2, Qfs1. reflexivity.
  - rewrite Qfds3, Ffds2, Qfds1. reflexivity.
  - split; [exact AR1|]. split; [exact AR2|]. split; [exact AR3|]. split; [exact AR4| cbn [c_img_hi ACONSTS]; exact AR5].
  - exists junk. split; [exact LJ|]. eapply rw_cells_transport; [exact JC| exact MU6| exact WM6|].
    cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -Hn2; lia). clear -AR4 LO LOC Hn2. lia.
  - exact (proj1 (AHK_block_oshadow SR RT E0 FSB0 HR0 L0 RES0 EB0 sq LB2 LF m6 mo3 (mkABlock rnew n) AH3 ltac:(left; reflexivity) ltac:(cbn [ab_size]; clear -Hn2; lia))).
Qed.

End ReallocT.
End RC__1.
