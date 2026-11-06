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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanPS AsanRep AsanKern AsanWf1 AsanBudget AsanBudget2 AsanRealloc AsanDepot AsanHit AsanSlack AsanRepFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_free_kit B_policy5 B_slack5 B_budget5 B_mmchk5 B_bundle B_benv5 B_balloc5 B_bpolicy5 B_bevents5 B_bevents5b B_rtok5 BF_unwind BF_alloc_iface BF_dput_iface BF_tkit B_live BF_lalloc1 BF_grant BF_lalloc3 BF_depot1 BF_depot2 BF_depot3 BF_depot4 BF_depot5 BF_depot6 BF_depot7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma sA_self : forall s, sA (aps_alloc s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma sA_sA : forall a a' s, sA a (sA a' s) = sA a s.
Proof. intros a a' s. destruct s. reflexivity. Qed.

Section DputT.
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
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.
Lemma LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0. Proof. exact (proj1 L0OK). Qed.
Lemma GS_L0 : In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0. Proof. exact (proj1 (proj2 L0OK)). Qed.
Lemma HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0. Proof. exact (proj1 (proj2 (proj2 L0OK))). Qed.
Lemma RES0_cover : forall x, 0x10000 <= x < 0x603000 -> exists e, In e RES0 /\ elo e <= x < ehi e. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 L0OK))))). Qed.
Lemma RSVD : forall rr x, In rr (ae_reserved E0) -> fst rr <= x < fst rr + snd rr -> (exists e, In e (RES0 ++ L0) /\ elo e <= x < ehi e) \/ alloc_ceiling <= x.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 L0OK)))))). Qed.
Lemma RSVD_pos : Forall (fun rr => 0 < snd rr) (ae_reserved E0). Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 L0OK)))))). Qed.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation T := (ae_thread E0).
#[local] Notation DR := (DepotR bsegs E0).
Ltac cstat := try clear ENV_depot; try clear RES0_low; try clear PL0OK; try clear ENV0; try clear HR0_ok.

Definition PP (s1 : aps) (mo1 : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo1) (aSc s1) x.
(* [comment removed for export] *)
Lemma DepotRep_upd_ndepot : forall f a m, DepotRep bsegs E0 (upd_ndepot f a) m <-> DepotRep bsegs E0 a m.
Proof. intros f a m. destruct a; reflexivity. Qed.
Lemma DepotFPd_upd_ndepot : forall f a z, DepotFPd E0 (upd_ndepot f a) z <-> DepotFPd E0 a z.
Proof. intros f a z. destruct a; reflexivity. Qed.
Lemma same_fp_upd_ndepot : forall f a, same_fp a (upd_ndepot f a).
Proof. intros f a. destruct a; repeat split; reflexivity. Qed.
Lemma gapR_upd_ndepot : forall f a, gapR (upd_ndepot f a) = gapR a.
Proof. intros f a. destruct a; reflexivity. Qed.
Lemma gapD_upd_ndepot1 : forall a, gapD (upd_ndepot (fun k => k + 1) a) = gapD a + 4096.
Proof. intros a. unfold gapD. destruct a. cbn -[Z.mul Z.add Z.sub zlen]. clear. lia. Qed.
Lemma AKern_upd_ndepot : forall f a mo, AKern E0 a mo -> AKern E0 (upd_ndepot f a) mo.
Proof. intros f a mo K. eapply AKern_ext; [..| exact K]; destruct a; reflexivity. Qed.
Lemma zlen_bst_key : forall len ws, 0 <= len <= zlen ws -> zlen (bst_key len ws) = len.
Proof. intros len ws H. unfold bst_key, zlen in *. rewrite length_map, length_firstn. clear -H. rewrite Nat.min_l by lia. lia. Qed.
Ltac agz AG H := eapply (rw_cells_agree bsegs); [| exact H]; cbn; intros x Hx; apply AG; clear -Hx; lia.
(* [comment removed for export] *)
Lemma dput_statics_agree : forall m m', dput_statics m -> (forall x, 0xa5000 <= x < 0x140c80 -> m' (wa x) = m (wa x)) -> dput_statics m'.
Proof. aceil.
  intros m m' (ST & CF) AG.
  unfold dput_statics, statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in *.
  destruct ST as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  split; [| agz AG CF].
  split; [agz AG S1|]. split; [agz AG S2|]. split; [agz AG S3|]. split; [agz AG S4|]. split; [agz AG S5|]. split; [agz AG S6| agz AG S7].
Qed.
Lemma dput_mutexes_agree : forall m m', dput_mutexes m -> (forall x, 0x180488 <= x < 0x603000 -> m' (wa x) = m (wa x)) -> dput_mutexes m'.
Proof. aceil.
  intros m m' (M1 & M2) AG. unfold dput_mutexes, dTD, dSS, kStoreBlockCount in *. split.
  - eapply (rw_cells_agree bsegs); [| exact M1]; cbn; intros x Hx; apply AG; clear -Hx; lia.
  - intros k Hk. eapply (rw_cells_agree bsegs); [| exact (M2 k Hk)]; cbn; intros x Hx; apply AG; clear -Hx Hk; lia.
Qed.
(* [comment removed for export] *)
Lemma rw_CB_wr_at : forall m A n bs, rw_cells bsegs m A [CB n bs] -> wr_at bsegs m A (Z.of_nat n).
Proof. intros m A n bs [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. exact W. Qed.
Lemma rw_CB_u8arr : forall mX AX nX bsX, rw_cells bsegs mX AX [CB nX bsX] -> length bsX = nX -> u8arr bsegs mX AX bsX.
Proof.
  intros mX AX nX bsX [[_ B] W] L. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. cbn [cells_size csize] in W. rewrite Nat.add_0_r, <- L in W.
  split; [exact B| exact W].
Qed.
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> (outside W1 x /\ outside W2 x).
Proof.
  induction W1 as [|[lo' hi'] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma munch_app : forall W1 W2 (m0 m1 m2 : mem), munch W1 m0 m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m0 m2.
Proof.
  intros W1 W2 m0 m1 m2 H1 H2 x Hx. apply outside_app in Hx. destruct Hx as [X1 X2]. rewrite (H2 x X2). exact (H1 x X1).
Qed.
(* [comment removed for export] *)
Lemma arun_sbind0 : forall {R S} (t : stree aev aans (astate * aout R)) (k : astate * aout R -> stree aev aans (astate * aout S))
    f orc s1 o1 evs1 orc1 s2 o2 evs2 orc2,
  arun f t orc = Some (s1, o1, evs1, orc1) -> arun 0%nat (k (s1, o1)) orc1 = Some (s2, o2, evs2, orc2) ->
  arun f (sbind t k) orc = Some (s2, o2, evs1 ++ evs2, orc2).
Proof. intros. rewrite <- (Nat.add_0_r f). eapply arun_sbind; eassumption. Qed.
Lemma arun_acall : forall e s ans rest, arun 1%nat (acall e s) (ans :: rest) = Some (s, ONorm ans, [e], rest).
Proof. reflexivity. Qed.
Lemma arun_call_mmap_ordie : forall len flags s r rest,
  (r mod kPageSize =? 0) && (0 <? r) && (r + len <=? alloc_ceiling) && ranges_free (known_ranges E0 s) r len = true ->
  app_mem_b r len && negb (in_primary (ae_space_beg E0) r) && negb (in_primary (ae_space_beg E0) (r + len - 1)) && (r + len <=? kHighMemEnd + 1) = true ->
  arun 1%nat (call_mmap_ordie E0 len flags s) (AnsOk r :: rest) = Some (s, ONorm r, [AEvMmap 0 len kProtRw flags], rest).
Proof.
  intros len flags s r rest V1 V2. unfold call_mmap_ordie. unfold abind at 1. unfold aget. cbn [sbind fst snd].
  unfold abind, acall. cbn [arun sbind fst snd]. rewrite V1, V2. reflexivity.
Qed.
(* [comment removed for export] *)
Definition st_bump (count : Z) (a : astate) : astate := upd_keys (fun ks => ks) (fun f => f + count) a.
Lemma arun_store_alloc_once_fit : forall count s orc,
  let fr := as_frames s in
  fr / kStoreBlockFrames = (fr + count - 1) / kStoreBlockFrames ->
  ~ (0 < fr / kStoreBlockFrames /\ zlen (as_store_blocks s) < fr / kStoreBlockFrames) ->
  arun 0%nat (store_alloc_once E0 count s) orc = Some (st_bump count s, ONorm (Some fr), [], orc).
Proof.
  intros count s orc fr EB NG. unfold store_alloc_once. unfold abind at 1. unfold aget. cbn [sbind fst snd].
  unfold abind at 1. cbn [aupd sbind fst snd]. fold fr. rewrite (proj2 (Z.eqb_eq _ _) EB).
  unfold abind at 1. cbn [sbind fst snd].
  assert (ESB : as_store_blocks (upd_keys (fun ks => ks) (fun f => f + count) s) = as_store_blocks s) by (destruct s; reflexivity). rewrite ESB.
  destruct ((0 <? fr / kStoreBlockFrames) && (zlen (as_store_blocks s) <? fr / kStoreBlockFrames)) eqn:C.
  - exfalso. apply NG. apply andb_prop in C. destruct C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. split; assumption.
  - unfold abind. cbn [aret sbind fst snd]. reflexivity.
Qed.
Lemma arun_store_alloc_once_grow : forall count s r rest,
  let fr := as_frames s in
  fr / kStoreBlockFrames = (fr + count - 1) / kStoreBlockFrames ->
  0 < fr / kStoreBlockFrames -> zlen (as_store_blocks s) < fr / kStoreBlockFrames ->
  (r mod kPageSize =? 0) && (0 <? r) && (r + kStoreBlockBytes <=? alloc_ceiling) && ranges_free (known_ranges E0 (st_bump count s)) r kStoreBlockBytes = true ->
  app_mem_b r kStoreBlockBytes && negb (in_primary (ae_space_beg E0) r) && negb (in_primary (ae_space_beg E0) (r + kStoreBlockBytes - 1)) && (r + kStoreBlockBytes <=? kHighMemEnd + 1) = true ->
  arun 1%nat (store_alloc_once E0 count s) (AnsOk r :: rest)
    = Some (upd_store_blocks (fun l => l ++ [r]) (st_bump count s), ONorm (Some fr), [AEvMmap 0 kStoreBlockBytes kProtRw kFlagsNoReserveRw], rest).
Proof.
  intros count s r rest fr EB B0 BG V1 V2. unfold store_alloc_once. unfold abind at 1. unfold aget. cbn [sbind fst snd].
  unfold abind at 1. cbn [aupd sbind fst snd]. fold fr. rewrite (proj2 (Z.eqb_eq _ _) EB).
  unfold abind at 1. cbn [sbind fst snd].
  assert (ESB : as_store_blocks (upd_keys (fun ks => ks) (fun f => f + count) s) = as_store_blocks s) by (destruct s; reflexivity). rewrite ESB.
  rewrite (proj2 (Z.ltb_lt _ _) B0), (proj2 (Z.ltb_lt _ _) BG). cbn [andb].
  unfold abind at 1. cbn [sbind fst snd]. fold (st_bump count s).
  etransitivity; [eapply arun_sbind0; [eapply arun_sbind0; [apply arun_call_mmap_ordie; [exact V1| exact V2]| cbn [fst snd]; reflexivity]| cbn [fst snd]; reflexivity]| reflexivity].
Qed.
Lemma arun_store_alloc_once_straddle : forall count s orc,
  let fr := as_frames s in let b := fr / kStoreBlockFrames in let b' := (fr + count - 1) / kStoreBlockFrames in
  b <> b' ->
  arun 0%nat (store_alloc_once E0 count s) orc
    = Some (upd_store_stored (fun st => <[b' := (match st !! b' with Some v => v | None => 0 end) + (count - (kStoreBlockFrames - fr mod kStoreBlockFrames))]>
                                      (<[b := (match st !! b with Some v => v | None => 0 end) + (kStoreBlockFrames - fr mod kStoreBlockFrames)]> st)) (st_bump count s),
            ONorm None, [], orc).
Proof.
  intros count s orc fr b b' NE. unfold store_alloc_once. unfold abind at 1. unfold aget. cbn [sbind fst snd].
  unfold abind at 1. cbn [aupd sbind fst snd]. fold fr b b'. rewrite (proj2 (Z.eqb_neq _ _) NE).
  unfold abind. cbn [aupd aret sbind fst snd]. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (mo : Model) (s : aps) (Pq : list Z) (Dq : list batch) (lo A len C C' : Z) (ws : list word) (K : TSet).
#[local] Notation a := (aps_alloc s).
#[local] Notation usp := (bv_unsigned sp).
Hypothesis KN : K [].
Hypothesis TOK : RTOKc C C' s mo.
Hypothesis C1 : 1 <= C.
Hypothesis CSL : DSLACK <= C'.
Hypothesis AK : AKern E0 a mo.
Hypothesis WF : AWf E0 Pq Dq a.
Hypothesis NBZ : zlen (as_node_blocks a) <= 1832.
Hypothesis SBZ : zlen (as_store_blocks a) <= 7400.
Hypothesis SECB : AsanState.sec_bytes a <= 2^39.
Hypothesis NDI : as_ndepot_ins a + 1 <= kInitialCredit.
Hypothesis REP : DR a m.
Hypothesis MTX : dput_mutexes m.
Hypothesis STAT : dput_statics m.
Hypothesis MI : mem_inv bsegs m.
Hypothesis SK : stk bsegs m lo usp.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - K_DEPOT.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis UA : usp <= A.
Hypothesis A47 : A + 8 * zlen ws < 2^47.
Hypothesis TR : u64arr bsegs m A ws.
Hypothesis LEN : 1 <= len <= zlen ws.
Hypothesis LWS : zlen ws <= 30.
Hypothesis CONT : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate) (id : Z),
     dput_post_state E0 FSB0 HR0 L0 RES0 EB0 a a' m m' mo mo' s C C' lo usp (bst_key len ws) id ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz id) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K.

(* [comment removed for export] *)
Definition N : Z := zlen (depot_keys E0 a).
Definition HS : list Z := depot_hashes E0 a.
Definition NB : list Z := node_blocks E0 a.
Definition SBL : list Z := store_blocks E0 a.
Definition key : list Z := bst_key len ws.
Definition h : Z := depot_hash key.
Definition bkt : Z := bucket_of h.
Definition kb : Z := (N + 1) / kDepotNodesPerBlock.
Definition fr : Z := as_frames a.
Lemma EkeyZ : BF_depot6.keyZ len ws = key. Proof. reflexivity. Qed.
Lemma Eh : BF_depot6.h len ws = h. Proof. reflexivity. Qed.
Lemma Ebkt : BF_depot6.bkt len ws = bkt. Proof. reflexivity. Qed.
Lemma Ekb : BF_depot6.kb N = kb. Proof. reflexivity. Qed.
Lemma ETBA : BF_depot6.TBA len ws = 1639576 + 4 * bkt. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma USPR : 0 <= usp < 2^64. Proof. pose proof (bv_unsigned_in_range 64 sp) as X. unfold bv_modulus in X. exact X. Qed.
Lemma Esp : sp = wz usp. Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma DINV : depot_inv E0 a. Proof. exact (proj1 REP). Qed.
Lemma DREP : DepotRep bsegs E0 a m. Proof. exact (proj2 REP). Qed.
Lemma WE : wf_env E0. Proof. exact (proj1 WF). Qed.
Lemma WDEP : wf_depot E0 a. Proof. pose proof WF as (_ & _ & _ & _ & _ & _ & X). exact X. Qed.
Lemma ATK0 : exists R0 R0', ATOKc R0 R0' s mo /\ C <= R0 /\ C' <= R0'.
Proof. exact (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK). Qed.
Lemma ENV : ENVOK E0 FSB0 s.
Proof. destruct ATK0 as (R0 & R0' & ATK & _). exact (ATOK_ENVOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK). Qed.
Lemma EE : aps_env s = E0. Proof. pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma IMGE : fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0).
Proof. pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X). rewrite EE in X. exact X. Qed.
Lemma IC0 : ae_ic E0 = both_ic.
Proof. pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma EN : N = depot_n_ids E0 a.
Proof. unfold N, depot_keys, depot_n_ids, zlen. rewrite length_app. clear. lia. Qed.
Lemma EN2 : N = zlen (ae_keys0 E0) + zlen (as_keys a).
Proof. unfold N, depot_keys, zlen. rewrite length_app. clear. lia. Qed.
Lemma EHSN : N = zlen HS. Proof. unfold N, HS, depot_hashes, zlen. rewrite length_map. reflexivity. Qed.
Lemma ENB : zlen NB = zlen (as_node_blocks a) + 1. Proof. unfold NB, node_blocks, zlen. cbn [length]. clear. lia. Qed.
Lemma ESBL : zlen SBL = zlen (as_store_blocks a) + 1. Proof. unfold SBL, store_blocks, zlen. cbn [length]. clear. lia. Qed.
Lemma HN : 0 <= N /\ N + 2 < 2^31 /\ N = zlen HS.
Proof.
  split; [unfold N, zlen; clear; lia|]. split; [| exact EHSN].
  pose proof WDEP as (_ & WD2 & _). pose proof EN2. pose proof (zlen_nonneg (ae_keys0 E0)). unfold kInitialCredit in NDI. clear -WD2 NDI ENV_depot H H0. lia.
Qed.
Lemma HSR : forall i, 0 <= nth_hash HS i < 2^64. Proof. intros i. unfold HS, depot_hashes. apply nth_hash_range. Qed.
Lemma NBC : forall i, 1 <= i <= N -> i / kDepotNodesPerBlock < zlen NB.
Proof.
  intros i Hi. rewrite ENB. rewrite EN in Hi. pose proof DINV as (_ & _ & _ & _ & DI5 & _). unfold kDepotNodesPerBlock in *.
  apply Z.div_lt_upper_bound; [clear; lia|]. clear -DI5 Hi. lia.
Qed.
Lemma KBLE : kb <= zlen NB.
Proof.
  unfold kb. rewrite ENB, EN. pose proof DINV as (_ & _ & _ & _ & DI5 & _). unfold kDepotNodesPerBlock in *. apply Z.div_le_upper_bound; [clear; lia|]. clear -DI5. lia.
Qed.
Lemma KB0 : 0 <= kb < kNodesMap1.
Proof.
  unfold kb, kDepotNodesPerBlock, kNodesMap1. pose proof HN as (H1 & H2 & _). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
(* [comment removed for export] *)
Lemma BSEP : forall blk len', (In blk (as_node_blocks a) /\ len' = kDepotNodeBlockBytes) \/ (In blk (as_store_blocks a) /\ len' = kStoreBlockBytes) ->
  placed blk len' /\ blk mod 4096 = 0.
Proof. aceil.
  intros blk len' Hb. destruct (ak_blocks_sep _ _ _ AK blk len' Hb) as (B1 & B2 & B3 & B4 & B5 & B6).
  assert (RIMG : In (ae_img E0) (ae_reserved E0)) by (pose proof WE as X; unfold wf_env in X; decompose [and] X; assumption).
  destruct IMGE as [EI1 EI2]. pose proof (B6 _ RIMG) as X. rewrite EI1 in X.
  assert (LEN' : 2^20 <= len') by (destruct Hb as [[_ ->]|[_ ->]]; unfold kDepotNodeBlockBytes, kStoreBlockBytes; clear; lia).
  unfold placed, app_mem, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kPageSize in *. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in B1.
  clear -B1 B2 B3 X EI2 LEN' CEILB. split; [| exact B3]. lia.
Qed.
Lemma NBR : forall blk, In blk NB -> placed blk kDepotNodeBlockBytes.
Proof. intros blk [<-|Hb]; [pose proof ENV0 as (_ & _ & N3 & _); exact N3| exact (proj1 (BSEP blk _ (or_introl (conj Hb eq_refl))))]. Qed.
Lemma NBAL : forall blk, In blk NB -> blk mod 16 = 0.
Proof.
  intros blk [<-|Hb].
  - pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N15 & _). clear -N15. Z.div_mod_to_equations; lia.
  - pose proof (proj2 (BSEP blk _ (or_introl (conj Hb eq_refl)))) as B3. clear -B3. Z.div_mod_to_equations; lia.
Qed.
Lemma SBR : forall blk, In blk SBL -> placed blk kStoreBlockBytes /\ blk mod 4096 = 0.
Proof.
  intros blk [<-|Hb]; [| exact (BSEP blk _ (or_intror (conj Hb eq_refl)))].
  pose proof ENV0 as (_ & _ & _ & N4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & N14 & _). split; [exact N4| exact N14].
Qed.
(* [comment removed for export] *)
Lemma D_tab : forall b, 0 <= b < kTabSize -> rw_cells bsegs m (1639576 + 4 * b) [C4 (wz (bucket_head HS b))].
Proof. intros b Hb. pose proof (proj1 DREP) as D1. rewrite IC0 in D1. exact (D1 b Hb). Qed.
Lemma D_nuq : rw_cells bsegs m (1639576 + 4194304) [C4 (wz N)].
Proof. pose proof (proj1 (proj2 DREP)) as D2. rewrite IC0 in D2. exact D2. Qed.
Lemma D_map1 : forall k, 0 <= k < kNodesMap1 -> rw_cells bsegs m (1639576 + 4194320 + 8 * k) [C8 (wz (nthz NB k))].
Proof. intros k Hk. pose proof (proj1 (proj2 (proj2 DREP))) as D3. rewrite IC0 in D3. exact (D3 k Hk). Qed.
Lemma D_nodes : forall i, 1 <= i <= N -> exists sid,
  rw_cells bsegs m (nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock)) [C8 (wz (nth_hash HS i)); C4 (wz (node_link HS i)); C4 sid].
Proof. intros i Hi. pose proof (proj1 (proj2 (proj2 (proj2 DREP)))) as D4. exact (D4 i Hi). Qed.
Lemma D_nbw : forall b, In b NB -> wr_at bsegs m b kDepotNodeBlockBytes.
Proof. pose proof DREP as (_ & _ & _ & _ & D5 & _). exact D5. Qed.
Lemma D_fr : rw_cells bsegs m 1574024 [C8 (wz fr)].
Proof. pose proof DREP as (_ & _ & _ & _ & _ & D6 & _). rewrite IC0 in D6. exact D6. Qed.
Lemma D_al : exists al, rw_cells bsegs m (1574024 + 8) [C8 al].
Proof. pose proof DREP as (_ & _ & _ & _ & _ & _ & D7 & _). rewrite IC0 in D7. exact D7. Qed.
Lemma D_blk : forall k, 0 <= k < kStoreBlockCount ->
  rw_cells bsegs m (1574024 + 16 + 16 * k) [C8 (wz (nthz SBL k)); C4 (wz (stored_of fr k))] /\ exists mx, rw_cells bsegs m (1574024 + 28 + 16 * k) [C4 mx].
Proof. pose proof DREP as (_ & _ & _ & _ & _ & _ & _ & D8 & _). rewrite IC0 in D8. exact D8. Qed.
Lemma D_sbw : forall b, In b SBL -> exists bs, u8arr bsegs m b bs /\ Z.of_nat (length bs) = kStoreBlockBytes.
Proof. pose proof DREP as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & _). exact D9. Qed.
Lemma D_mu : rw_cells bsegs m (1639576 + 4194312) [C4 (wz 0)].
Proof. pose proof DREP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). rewrite IC0 in D10. exact D10. Qed.
Lemma D_mtx : forall k, 0 <= k < kStoreBlockCount -> rw_cells bsegs m (1574024 + 28 + 16 * k) [C4 (wz 0)].
Proof. pose proof DREP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D11). rewrite IC0 in D11. exact D11. Qed.
Lemma M_tlm : rw_cells bsegs m (1639576 + 4194312) [C4 (wz 0)].
Proof. exact (proj1 MTX). Qed.
Lemma M_blk : forall k, 0 <= k < kStoreBlockCount -> rw_cells bsegs m (1574024 + 28 + 16 * k) [C4 (wz 0)].
Proof. exact (proj2 MTX). Qed.
(* [comment removed for export] *)
Lemma EPOL : forall s' mo' a' k, POL E0 FSB0 HR0 s' mo' a' k = PP s' mo' (wz a', k). Proof. intros; reflexivity. Qed.
Lemma PSTK0 : forall a' k, lo <= a' -> a' + Z.of_nat k <= A + 8 * zlen ws -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 s mo AK WE ENV0); clear -H1 H2 LOC A47; aceil; lia. Qed.
Lemma PIMG0 : forall a' k, 0 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo AK WE ENV ENV0); [exact H1| exact H2]. Qed.
Lemma PNB0 : forall blk a' k, In blk NB -> blk <= a' -> a' + Z.of_nat k <= blk + kDepotNodeBlockBytes -> PP s mo (wz a', k).
Proof. intros blk a' k Hb H1 H2. rewrite <- EPOL. eapply (pol_node_block' E0 FSB0 HR0 s mo AK ENV0); [exact Hb| exact H1| exact H2]. Qed.
Lemma PSB0 : forall blk a' k, In blk SBL -> blk <= a' -> a' + Z.of_nat k <= blk + kStoreBlockBytes -> PP s mo (wz a', k).
Proof. intros blk a' k Hb H1 H2. rewrite <- EPOL. eapply (pol_store_block' E0 FSB0 HR0 s mo AK ENV0); [exact Hb| exact H1| exact H2]. Qed.
Lemma KIP0 : KIP (aSc s) (aNc s) (aEBc s) (PP s mo) mo.
Proof. destruct ATK0 as (R0 & R0' & ATK & _). split; [exact (ATOK_KIA E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK)| intros x Hx; exact Hx]. Qed.
(* [comment removed for export] *)
Lemma FRF : 0 <= fr /\ fr + 64 <= 2^32 /\ BF_depot7.b fr + 1 < kStoreBlockCount.
Proof.
  pose proof (depot_frames_bound E0 a DINV ltac:(clear -ENV_depot; lia) ltac:(unfold kInitialCredit in NDI; clear -NDI; lia)) as (X1 & X2 & X3).
  unfold fr, BF_depot7.b, kStoreBlockCount, kStoreBlockFrames in *. split; [exact X1|]. split; [clear -X2; lia| exact X3].
Qed.
Lemma FRLE : fr <= kStoreBlockFrames * zlen SBL.
Proof. rewrite ESBL. unfold fr. pose proof DINV as (_ & _ & _ & _ & _ & _ & DI7). exact DI7. Qed.
Lemma PIMG0' : forall a' k, 0xa5000 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. apply PIMG0; [clear -H1; lia| exact H2]. Qed.
(* [comment removed for export] *)
Lemma ROOM_N : (N + 1) mod kDepotNodesPerBlock = 0 -> 4096 * 4096 <= gapD a.
Proof.
  intros MZ. pose proof DINV as (DI1 & DI2 & DI3 & DI4 & DI5 & DI6 & DI7). pose proof WDEP as (_ & WD2 & WD3). pose proof EN2 as E2. pose proof EN as E1.
  pose proof (zlen_nonneg (as_node_blocks a)) as Z1. pose proof (zlen_nonneg (as_store_blocks a)) as Z2. pose proof (zlen_nonneg (ae_keys0 E0)) as Z3.
  unfold gapD, kGapDPad, kDepotNodesPerBlock, kStoreBlockFrames in *. rewrite <- E1 in DI1, DI5.
  clear -MZ DI1 DI2 DI3 DI5 WD2 E2 Z1 Z2 Z3 ENV_depot. Z.div_mod_to_equations. nia.
Qed.
Lemma ROOM_S : forall fs, kStoreBlockFrames * (zlen (as_store_blocks a) + 1) <= fs -> fs <= fr + 62 -> 4096 * 2400 <= gapD a.
Proof.
  intros fs H1 H2. pose proof DINV as (DI1 & DI2 & DI3 & DI4 & DI5 & DI6 & DI7). pose proof WDEP as (_ & WD2 & WD3). pose proof EN2 as E2. pose proof EN as E1.
  pose proof (zlen_nonneg (as_node_blocks a)) as Z1. pose proof (zlen_nonneg (as_store_blocks a)) as Z2. pose proof (zlen_nonneg (ae_keys0 E0)) as Z3.
  unfold fr, gapD, kGapDPad, kDepotNodesPerBlock, kStoreBlockFrames in *. rewrite <- E1 in DI1, DI5.
  clear -H1 H2 DI1 DI2 DI3 DI5 WD2 E2 Z1 Z2 Z3 ENV_depot. nia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opt_list (nbx : option Z) : list Z := match nbx with Some r => [r] | None => [] end.
Definition opt_iv (nbx : option Z) (len' : Z) : list (Z * Z) := match nbx with Some r => [(r, r + len')] | None => [] end.
Definition nd_st (nbx : option Z) : astate :=
  match nbx with None => upd_ndepot (fun k => k + 1) a | Some r => upd_node_blocks (fun l => l ++ [r]) (upd_ndepot (fun k => k + 1) a) end.
Definition ngcost (nbx : option Z) : Z := match nbx with Some _ => kDepotNodeBlockBytes + NMAXA + 4095 | None => 0 end.
(* [comment removed for export] *)
Definition S_sa (rax : word) (blk : Z) (x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 : word) (m' : mem) : machine_state :=
  MS (put_regs sp gp tp s10 s11 len ws HS N rax (Z_to_bv 64 blk) x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6) F (Z_to_bv 64 0x73f78) fc None m' (seg_rom bsegs).
(* [comment removed for export] *)
Definition nbx_ok (nbx : option Z) (blk : Z) : Prop :=
  match nbx with
  | None => (N + 1) mod kDepotNodesPerBlock <> 0
  | Some r => r = blk /\ (N + 1) mod kDepotNodesPerBlock = 0
            /\ (r mod kPageSize =? 0) && (0 <? r) && (r + kDepotNodeBlockBytes <=? alloc_ceiling) && ranges_free (known_ranges E0 a) r kDepotNodeBlockBytes = true
            /\ app_mem_b r kDepotNodeBlockBytes && negb (in_primary (ae_space_beg E0) r) && negb (in_primary (ae_space_beg E0) (r + kDepotNodeBlockBytes - 1)) && (r + kDepotNodeBlockBytes <=? kHighMemEnd + 1) = true
  end.
(* [comment removed for export] *)
Definition WB (nbx : option Z) : list (Z * Z) :=
  [(usp - 464, usp); (1639576 + 4 * bkt, 1639576 + 4 * bkt + 4); (5833880, 5833884); (5833888, 5833892); (5833896 + 8 * kb, 5833904 + 8 * kb)] ++ opt_iv nbx kDepotNodeBlockBytes.
Definition npost (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (m2 : mem) (mo2 : Model) : Prop :=
  let NB2 := NB ++ opt_list nbx in let a1 := nd_st nbx in
     placed blk kDepotNodeBlockBytes /\ blk mod 4096 = 0
  /\ nthz NB2 kb = blk /\ kb < zlen NB2 /\ node_blocks E0 a1 = NB2
  /\ munch (WB nbx) m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp - 112)
  /\ rw_cells bsegs m2 (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8)
  /\ rw_cells bsegs m2 (1639576 + 4 * bkt) [C4 wl] /\ rw_cells bsegs m2 5833880 [C4 (Z_to_bv 64 (N + 1))]
  /\ rw_cells bsegs m2 5833888 [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m2 (5833896 + 8 * kb) [C8 (Z_to_bv 64 blk)]
  /\ wr_at bsegs m2 blk kDepotNodeBlockBytes
  /\ m_fs mo2 = m_fs mo /\ m_fds mo2 = m_fds mo /\ m_tid mo2 = m_tid mo
  /\ AKern E0 a1 mo2 /\ RTOKc (C - 1) (C' - ngcost nbx) (sA a1 s) mo2
  /\ KIP (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) (PP (sA a1 s) mo2) mo2
  /\ nbx_ok nbx blk.

(* [comment removed for export] *)
Lemma kb_cases : (kb < zlen NB /\ (N + 1) mod kDepotNodesPerBlock <> 0) \/ (kb = zlen NB /\ (N + 1) mod kDepotNodesPerBlock = 0 /\ N + 1 = kDepotNodesPerBlock * kb).
Proof.
  pose proof DINV as (DI1 & _ & _ & _ & DI5 & _). rewrite <- EN in DI1, DI5. pose proof ENB as E. unfold kb, kDepotNodesPerBlock in *.
  destruct (Z.eq_dec ((N + 1) mod 65536) 0) as [Z0|NZ].
  - right. clear -DI1 DI5 E Z0. Z.div_mod_to_equations. nia.
  - left. clear -DI1 DI5 E NZ. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma nd_node_blocks : forall nbx, node_blocks E0 (nd_st nbx) = NB ++ opt_list nbx.
Proof. intros [r|]; unfold nd_st, NB, node_blocks; destruct (aps_alloc s); cbn; [reflexivity| rewrite app_nil_r; reflexivity]. Qed.
Lemma nd_same_fp_none : same_fp a (nd_st None). Proof. apply same_fp_upd_ndepot. Qed.
Lemma nd_fields : forall nbx,
  as_regions (nd_st nbx) = as_regions a /\ as_ptr_committed (nd_st nbx) = as_ptr_committed a /\ as_sec (nd_st nbx) = as_sec a
  /\ as_store_blocks (nd_st nbx) = as_store_blocks a /\ as_residue (nd_st nbx) = as_residue a /\ as_nprim_ever (nd_st nbx) = as_nprim_ever a
  /\ as_ndepot_ins (nd_st nbx) = as_ndepot_ins a + 1 /\ as_keys (nd_st nbx) = as_keys a /\ as_frames (nd_st nbx) = as_frames a
  /\ as_node_blocks (nd_st nbx) = as_node_blocks a ++ opt_list nbx /\ as_store_stored (nd_st nbx) = as_store_stored a.
Proof. intros [r|]; unfold nd_st; destruct (aps_alloc s); cbn; repeat split; try reflexivity. rewrite app_nil_r. reflexivity. Qed.

Lemma aS_nd : forall nbx w, aSc (sA (nd_st nbx) s) w <-> aSc s w.
Proof.
  intros nbx w. pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & _).
  unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores. cbn [aps_alloc]. rewrite F3, F5, F4. split; intros X; exact X.
Qed.
Lemma get_region_nd : forall nbx c, get_region (nd_st nbx) c = get_region a c.
Proof. intros nbx c. unfold get_region. rewrite (proj1 (nd_fields nbx)). reflexivity. Qed.
Lemma gapR_nd : forall nbx, gapR (nd_st nbx) = gapR a.
Proof. intros nbx. pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & F6 & _). unfold gapR, regions_bytes. rewrite F6.
  f_equal. clear -F1. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold get_region. rewrite F1. reflexivity. Qed.
Lemma gapP_nd : forall nbx, gapP (nd_st nbx) = gapP a.
Proof. intros nbx. pose proof (nd_fields nbx) as (F1 & F2 & _). unfold gapP. rewrite F2. reflexivity. Qed.
Lemma gapD_nd : forall nbx, gapD (nd_st nbx) = gapD a + 4096 - 4096 * 256 * zlen (opt_list nbx).
Proof. intros nbx. pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). unfold gapD. rewrite F7, F10, F4.
  unfold zlen. rewrite length_app, Nat2Z.inj_add. clear. lia. Qed.

Lemma anon_io : forall mo' r L, m_fs (m_anon mo' r L) = m_fs mo' /\ m_fds (m_anon mo' r L) = m_fds mo' /\ m_tid (m_anon mo' r L) = m_tid mo'.
Proof. intros; repeat split; reflexivity. Qed.
Lemma anon_nr_io : forall mo' r L, m_fs (m_anon_nr mo' r L) = m_fs mo' /\ m_fds (m_anon_nr mo' r L) = m_fds mo' /\ m_tid (m_anon_nr mo' r L) = m_tid mo'.
Proof. intros. unfold m_anon_nr, vm_add_lazy. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma jmp_back : forall P rax x10 x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 m',
  evtA bsegs P (fun ms' => ms' = MS (put_regs sp gp tp s10 s11 len ws HS N rax x10 x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6) F (Z_to_bv 64 0x73f78) fc None m' (seg_rom bsegs))
               (MS (put_regs sp gp tp s10 s11 len ws HS N rax x10 x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6) F (Z_to_bv 64 0x74010) fc None m' (seg_rom bsegs)).
Proof. intros. unfold put_regs. cstep. apply evtA_done. reflexivity. Qed.
(* [comment removed for export] *)
Lemma node_store_disjoint : forall aX moX nb sb', KVM L0 RES0 moX aX -> AKern E0 aX moX ->
  In nb (node_blocks E0 aX) -> In sb' (store_blocks E0 aX) -> nb + kDepotNodeBlockBytes <= sb' \/ sb' + kStoreBlockBytes <= nb.
Proof. aceil.
  intros aX moX nb sb' KV AKX Hn Hs. pose proof KV as (_ & (fog & PM & _ & _) & [MW1 MW2] & _).
  pose proof ENV0 as (EN1 & EN2 & EN3 & EN4 & _).
  destruct Hn as [<-|Hn]; destruct Hs as [<-|Hs].
  - pose proof (ak_store_sep _ _ _ AKX) as (_ & _ & _ & X & _). unfold kDepotNodeBlockBytes, kStoreBlockBytes. clear -X. lia.
  - destruct (ak_blocks_sep _ _ _ AKX sb' kStoreBlockBytes (or_intror (conj Hs eq_refl))) as (_ & _ & _ & _ & _ & B6).
    pose proof (B6 _ EN1) as X. cbn [fst snd] in X. clear -X. lia.
  - destruct (ak_blocks_sep _ _ _ AKX nb kDepotNodeBlockBytes (or_introl (conj Hn eq_refl))) as (_ & _ & _ & _ & _ & B6).
    pose proof (B6 _ EN2) as X. cbn [fst snd] in X. clear -X. lia.
  - pose proof (proj1 (ak_blocks_sep _ _ _ AKX nb kDepotNodeBlockBytes (or_introl (conj Hn eq_refl)))) as P1.
    pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX nb kDepotNodeBlockBytes (or_introl (conj Hn eq_refl))))) as P2.
    pose proof (proj1 (ak_blocks_sep _ _ _ AKX sb' kStoreBlockBytes (or_intror (conj Hs eq_refl)))) as Q1.
    pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX sb' kStoreBlockBytes (or_intror (conj Hs eq_refl))))) as Q2.
    unfold app_mem in P1, Q1. rewrite kLowAppEnd_val, kHighMemBeg_val in P1, Q1.
    assert (I1 : In (went nb kDepotNodeBlockBytes) (vm_maps (m_vmmaps moX))).
    { eapply Permutation_in; [apply Permutation_sym; exact PM|]. apply in_app_iff; right. apply in_app_iff; right. unfold amaps.
      apply in_app_iff; right. apply in_app_iff; left. apply in_map_iff. exists nb. split; [reflexivity| exact Hn]. }
    assert (I2 : In (went sb' kStoreBlockBytes) (vm_maps (m_vmmaps moX))).
    { eapply Permutation_in; [apply Permutation_sym; exact PM|]. apply in_app_iff; right. apply in_app_iff; right. unfold amaps.
      apply in_app_iff; right. apply in_app_iff; right. apply in_map_iff. exists sb'. split; [reflexivity| exact Hs]. }
    apply In_nth_error in I1 as [i Hi]. apply In_nth_error in I2 as [j Hj].
    assert (NE : i <> j).
    { intros ->. assert (EE : went nb kDepotNodeBlockBytes = went sb' kStoreBlockBytes) by congruence.
      apply (f_equal (fun e => bv_unsigned (snd e))) in EE. cbn [snd went] in EE. unfold kwz in EE.
      rewrite !unsigned_lit in EE by (unfold kDepotNodeBlockBytes, kStoreBlockBytes; clear; lia). unfold kDepotNodeBlockBytes, kStoreBlockBytes in EE. clear -EE. lia. }
    pose proof (MW1 i j _ _ Hi Hj NE) as D. unfold elo, ehi, went, kwz in D. cbn [fst snd] in D.
    pose proof alloc_ceiling_range as CR. unfold kDepotNodeBlockBytes, kStoreBlockBytes in *.
    rewrite !unsigned_lit in D by (clear -P1 P2 Q1 Q2 CR; lia). exact D.
Qed.
(* [comment removed for export] *)
Lemma grant_apart_inside : forall moX (r : word) (L b' len' : Z),
  AsanKern.inside (vm_maps (m_vmmaps moX)) b' len' ->
  region_free (vm_reserved (m_vmmaps moX) ++ vm_maps (m_vmmaps moX)) r (Z_to_bv 64 L) = true ->
  0 < L -> bv_unsigned r + L < 2^64 ->
  forall x, b' <= x < b' + len' -> ~ (bv_unsigned r <= x < bv_unsigned r + L).
Proof.
  intros moX r L b' len' (e & He & E1 & E2) RF HL HE x Hx.
  eapply (region_free_apart_pt _ r L e x HL HE RF); [apply in_app_iff; right; exact He| clear -E1 E2 Hx; lia].
Qed.
Lemma node_block_inside : forall aX moX nb, AKern E0 aX moX -> In nb (node_blocks E0 aX) -> AsanKern.inside (vm_maps (m_vmmaps moX)) nb kDepotNodeBlockBytes.
Proof.
  intros aX moX nb AKX [<-|Hn]; [exact (proj1 (ak_depot_nodes _ _ _ AKX))| exact (proj1 (proj2 (ak_node_blocks _ _ _ AKX nb Hn)))].
Qed.
Lemma store_block_inside : forall aX moX sb', AKern E0 aX moX -> In sb' (store_blocks E0 aX) -> AsanKern.inside (vm_maps (m_vmmaps moX)) sb' kStoreBlockBytes.
Proof.
  intros aX moX sb' AKX [<-|Hs]; [exact (proj1 (ak_store _ _ _ AKX))| exact (proj1 (ak_store_blocks _ _ _ AKX sb' Hs))].
Qed.

(* [comment removed for export] *)
Lemma kvm_amaps_apart : forall moX aX p q e1 e2, KVM L0 RES0 moX aX ->
  p <> q -> nth_error (amaps aX) p = Some e1 -> nth_error (amaps aX) q = Some e2 -> ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Proof.
  intros moX aX p q e1 e2 KV NE H1 H2. pose proof KV as (_ & (fog & PM & _ & _) & [MW1 MW2] & _).
  apply Permutation_nth_error in PM as [_ (f & INJ & NTH)].
  set (off := length (L0 ++ fog)).
  assert (E1' : nth_error (vm_maps (m_vmmaps moX)) (f (off + p)%nat) = Some e1).
  { rewrite <- NTH. rewrite app_assoc, nth_error_app2 by (subst off; lia). subst off. rewrite Nat.add_comm, Nat.add_sub. exact H1. }
  assert (E2' : nth_error (vm_maps (m_vmmaps moX)) (f (off + q)%nat) = Some e2).
  { rewrite <- NTH. rewrite app_assoc, nth_error_app2 by (subst off; lia). subst off. rewrite Nat.add_comm, Nat.add_sub. exact H2. }
  apply (MW1 _ _ _ _ E1' E2'). intros EQ. apply INJ in EQ. lia.
Qed.

Lemma amaps_nth_node : forall aX k b', nth_error (as_node_blocks aX) k = Some b' ->
  nth_error (amaps aX) (length (as_sec aX) + k)%nat = Some (went b' kDepotNodeBlockBytes).
Proof.
  intros aX k b' H. unfold amaps.
  rewrite nth_error_app2 by (rewrite length_map; lia). rewrite length_map.
  replace (length (as_sec aX) + k - length (as_sec aX))%nat with k by lia.
  rewrite nth_error_app1 by (rewrite length_map; exact (nth_error_lt _ _ _ H)).
  rewrite nth_error_map, H. reflexivity.
Qed.
Lemma amaps_nth_store : forall aX k b', nth_error (as_store_blocks aX) k = Some b' ->
  nth_error (amaps aX) (length (as_sec aX) + length (as_node_blocks aX) + k)%nat = Some (went b' kStoreBlockBytes).
Proof.
  intros aX k b' H. unfold amaps.
  rewrite nth_error_app2 by (rewrite length_map; lia). rewrite length_map.
  rewrite nth_error_app2 by (rewrite length_map; lia). rewrite length_map.
  replace (length (as_sec aX) + length (as_node_blocks aX) + k - length (as_sec aX) - length (as_node_blocks aX))%nat with k by lia.
  rewrite nth_error_map, H. reflexivity.
Qed.

Lemma nth_error_nthz : forall (l : list Z) k, 0 <= k < zlen l -> nth_error l (Z.to_nat k) = Some (nthz l k).
Proof.
  intros l k Hk. unfold nthz. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
  apply nth_error_nth'. unfold zlen in Hk. lia.
Qed.

(* [comment removed for export] *)
Lemma node_blocks_apart : forall moX aX p q, KVM L0 RES0 moX aX -> AKern E0 aX moX ->
  0 <= p < zlen (node_blocks E0 aX) -> 0 <= q < zlen (node_blocks E0 aX) -> p <> q ->
  nthz (node_blocks E0 aX) p + kDepotNodeBlockBytes <= nthz (node_blocks E0 aX) q \/ nthz (node_blocks E0 aX) q + kDepotNodeBlockBytes <= nthz (node_blocks E0 aX) p.
Proof. aceil.
  intros moX aX p q KV AKX Hp Hq NE. pose proof ENV0 as (EN1 & _).
  assert (DYN : forall k, 1 <= k < zlen (node_blocks E0 aX) -> nthz (node_blocks E0 aX) k = nthz (as_node_blocks aX) (k - 1) /\ In (nthz (as_node_blocks aX) (k - 1)) (as_node_blocks aX)
                      /\ 0 <= k - 1 < zlen (as_node_blocks aX)).
  { intros k Hk. unfold node_blocks, zlen in *. cbn [length] in Hk. rewrite Nat2Z.inj_succ in Hk.
    assert (R : 0 <= k - 1 < Z.of_nat (length (as_node_blocks aX))) by lia.
    split; [| split; [| exact R]].
    - unfold nthz. unfold zlen. cbn [length]. rewrite Nat2Z.inj_succ.
      rewrite (proj2 (Z.leb_le 0 k)), (proj2 (Z.ltb_lt _ _)), (proj2 (Z.leb_le 0 (k - 1))), (proj2 (Z.ltb_lt (k - 1) _)) by lia. cbn [andb].
      replace (Z.to_nat k) with (Datatypes.S (Z.to_nat (k - 1))) by lia. reflexivity.
    - unfold nthz. rewrite (proj2 (Z.leb_le 0 (k - 1))), (proj2 (Z.ltb_lt (k - 1) _)) by (unfold zlen; lia). cbn [andb]. apply nth_In. lia. }
  assert (Z0 : nthz (node_blocks E0 aX) 0 = ae_depot_nodes E0).
  { unfold nthz. rewrite (proj2 (Z.leb_le 0 0)) by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. reflexivity. }
  assert (B0D : forall k, 1 <= k < zlen (node_blocks E0 aX) ->
            ae_depot_nodes E0 + kDepotNodeBlockBytes <= nthz (node_blocks E0 aX) k \/ nthz (node_blocks E0 aX) k + kDepotNodeBlockBytes <= ae_depot_nodes E0).
  { intros k Hk. destruct (DYN k Hk) as (-> & IN & _).
    destruct (ak_blocks_sep _ _ _ AKX _ kDepotNodeBlockBytes (or_introl (conj IN eq_refl))) as (_ & _ & _ & _ & _ & B6).
    pose proof (B6 _ EN1) as X. cbn [fst snd] in X. clear -X. lia. }
  destruct (Z.eq_dec p 0) as [->|P0]; [rewrite Z0; pose proof (B0D q ltac:(lia)); lia|].
  destruct (Z.eq_dec q 0) as [->|Q0]; [rewrite Z0; pose proof (B0D p ltac:(lia)); lia|].
  destruct (DYN p ltac:(lia)) as (-> & INp & Rp). destruct (DYN q ltac:(lia)) as (-> & INq & Rq).
  set (NBd := as_node_blocks aX) in *.
  assert (NEQ : (length (as_sec aX) + Z.to_nat (p - 1))%nat <> (length (as_sec aX) + Z.to_nat (q - 1))%nat) by (clear -P0 Q0 NE Rp Rq; lia).
  pose proof (kvm_amaps_apart moX aX _ _ _ _ KV NEQ (amaps_nth_node aX (Z.to_nat (p - 1)) _ (nth_error_nthz _ _ Rp)) (amaps_nth_node aX (Z.to_nat (q - 1)) _ (nth_error_nthz _ _ Rq))) as X.
  pose proof (proj1 (ak_blocks_sep _ _ _ AKX _ kDepotNodeBlockBytes (or_introl (conj INp eq_refl)))) as P1.
  pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX _ kDepotNodeBlockBytes (or_introl (conj INp eq_refl))))) as P2.
  pose proof (proj1 (ak_blocks_sep _ _ _ AKX _ kDepotNodeBlockBytes (or_introl (conj INq eq_refl)))) as Q1.
  pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX _ kDepotNodeBlockBytes (or_introl (conj INq eq_refl))))) as Q2.
  unfold app_mem in P1, Q1. rewrite kLowAppEnd_val, kHighMemBeg_val in P1, Q1. pose proof alloc_ceiling_range as CR.
  unfold elo, ehi, went, kwz in X. cbn [fst snd] in X. unfold kDepotNodeBlockBytes in *.
  rewrite !unsigned_lit in X by (clear -P1 P2 Q1 Q2 CR; lia). exact X.
Qed.

(* [comment removed for export] *)
Lemma nthz_app_old : forall (l : list Z) x k, k < zlen l -> nthz (l ++ [x]) k = nthz l k.
Proof.
  intros l x k Hk. unfold nthz. unfold zlen in *. rewrite length_app. cbn [length].
  destruct (Z.leb_spec0 0 k); cbn [andb]; [| reflexivity].
  rewrite (proj2 (Z.ltb_lt _ _) Hk). rewrite (proj2 (Z.ltb_lt _ _)) by (clear -Hk; lia). apply app_nth1. clear -Hk l0. lia.
Qed.
Lemma nthz_opt_old : forall (l : list Z) ox k, k < zlen l -> nthz (l ++ opt_list ox) k = nthz l k.
Proof. intros l [x|] k Hk; cbn [opt_list]; [apply nthz_app_old; exact Hk| rewrite app_nil_r; reflexivity]. Qed.

Lemma nthz_app_other : forall (l : list Z) x k, k <> zlen l -> nthz (l ++ [x]) k = nthz l k.
Proof.
  intros l x k Hk. destruct (Z.lt_ge_cases k (zlen l)) as [LT|GE]; [apply nthz_app_old; exact LT|].
  unfold nthz. unfold zlen in *. rewrite length_app. cbn [length].
  rewrite (proj2 (Z.ltb_ge k (Z.of_nat (length l)))) by (clear -GE; lia).
  rewrite (proj2 (Z.ltb_ge k (Z.of_nat (length l + 1)))) by (clear -GE Hk; lia). rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_blocks_apart : forall moX aX b1 b2, KVM L0 RES0 moX aX -> AKern E0 aX moX ->
  In b1 (store_blocks E0 aX) -> In b2 (store_blocks E0 aX) -> b1 <> b2 -> b1 + kStoreBlockBytes <= b2 \/ b2 + kStoreBlockBytes <= b1.
Proof. aceil.
  intros moX aX b1 b2 KV AKX H1 H2 NE. pose proof ENV0 as (_ & EN2 & _). pose proof alloc_ceiling_range as CR.
  assert (B0D : forall b', In b' (as_store_blocks aX) -> ae_store_blk E0 + kStoreBlockBytes <= b' \/ b' + kStoreBlockBytes <= ae_store_blk E0).
  { intros b' Hb. destruct (ak_blocks_sep _ _ _ AKX _ kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B6).
    pose proof (B6 _ EN2) as X. cbn [fst snd] in X. clear -X. lia. }
  destruct H1 as [<-|H1]; destruct H2 as [<-|H2]; [exfalso; exact (NE eq_refl)| pose proof (B0D _ H2); lia| pose proof (B0D _ H1); lia|].
  apply In_nth_error in H1 as [p Hp]. apply In_nth_error in H2 as [q Hq].
  assert (PQ : p <> q) by (intros ->; rewrite Hp in Hq; injection Hq as E; exact (NE E)).
  assert (NEQ : (length (as_sec aX) + length (as_node_blocks aX) + p)%nat <> (length (as_sec aX) + length (as_node_blocks aX) + q)%nat) by (clear -PQ; lia).
  pose proof (kvm_amaps_apart moX aX _ _ _ _ KV NEQ (amaps_nth_store aX p _ Hp) (amaps_nth_store aX q _ Hq)) as X.
  apply nth_error_In in Hp. apply nth_error_In in Hq.
  pose proof (proj1 (ak_blocks_sep _ _ _ AKX _ kStoreBlockBytes (or_intror (conj Hp eq_refl)))) as P1.
  pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX _ kStoreBlockBytes (or_intror (conj Hp eq_refl))))) as P2.
  pose proof (proj1 (ak_blocks_sep _ _ _ AKX _ kStoreBlockBytes (or_intror (conj Hq eq_refl)))) as Q1.
  pose proof (proj1 (proj2 (ak_blocks_sep _ _ _ AKX _ kStoreBlockBytes (or_intror (conj Hq eq_refl))))) as Q2.
  unfold app_mem in P1, Q1. rewrite kLowAppEnd_val, kHighMemBeg_val in P1, Q1.
  unfold elo, ehi, went, kwz in X. cbn [fst snd] in X. unfold kStoreBlockBytes in *.
  rewrite !unsigned_lit in X by (clear -P1 P2 Q1 Q2 CR; lia). exact X.
Qed.
Lemma nodes_stage : forall (x12 x13 x14 x15 x16 : word) (m1 : mem) (mo1 : Model) (j8 : list byte) (wl : word) (ms1 : machine_state),
  (forall j, 1 <= j <= N -> nth_hash HS j <> h) ->
  munch [(usp - 224, usp); (1639576 + 4 * bkt, 1639576 + 4 * bkt + 4); (5833880, 5833884)] m m1 ->
  wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp - 112) ->
  rw_cells bsegs m1 (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8) ->
  rw_cells bsegs m1 (1639576 + 4 * bkt) [C4 wl] -> rw_cells bsegs m1 5833880 [C4 (wz (N + 1))] ->
  magree mo mo1 -> KIP (aSc s) (aNc s) (aEBc s) (PP s mo) mo1 ->
  ( (kb < zlen NB /\ ms1 = MS (put_regs sp gp tp s10 s11 len ws HS N (wz 0x73f10) (wz (nthz NB kb)) (wz kb) x12 x13 x14 x15 x16 a7 t0 t1 t2 t3 t4 t5 t6)
                                F (wz 0x73f78) fc None m1 (seg_rom bsegs))
 \/ (kb = zlen NB /\ ms1 = MS (put_regs sp gp tp s10 s11 len ws HS N (wz 0x74010) (wz 5833888) (wz kb) x12 x13 x14 x15 x16 a7 t0 t1 t2 t3 t4 t5 t6)
                                F (wz 0x74594) fc None m1 (seg_rom bsegs)) ) ->
  (forall rax x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 (m2 : mem) (mo2 : Model) (nbx : option Z) (blk : Z),
     npost j8 wl nbx blk m2 mo2 ->
     realizes_cfg acfg bsegs (mkCfg (S_sa rax blk x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 m2) mo2) K) ->
  realizes_cfg acfg bsegs (mkCfg ms1 mo1) K.
Proof.
  intros until ms1. intros MISSF MU1 WM1 MI1 SK1 FR1 TBA1 NUQ1 AG1 KP1 ARMS CONTn.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. unfold K_DEPOT in LO.
  pose proof (magree_frame _ _ AG1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & Qtid1 & _).
  pose proof (AKern_frame _ _ _ _ Qvm1 Qlz1 AK) as AK1.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 C C' s mo mo1 TOK AG1 (proj1 KP1)) as TOK1.
  pose proof KB0 as KB. pose proof HN as (HN0 & HN1 & HN2).
  assert (AGlo : forall z, 0 <= z < usp - 224 -> (z < 1639576 + 4 * bkt \/ 1639576 + 4 * bkt + 4 <= z) -> (z < 5833880 \/ 5833884 <= z) -> m1 (wa z) = m (wa z)).
  { intros z Hz H1 H2. apply MU1. rewrite wa_unsigned by (clear -Hz USPR'; lia). cbn. clear -Hz H1 H2. lia. }
  pose proof (Z.mod_pos_bound h kTabSize ltac:(unfold kTabSize; clear; lia)) as BKR. change (h mod kTabSize) with bkt in BKR. unfold kTabSize in BKR.
  destruct ARMS as [[KBL ->]|[KBE ->]].
  - (* [comment removed for export] *)
    destruct kb_cases as [[_ NZ]|[KE _]]; [| exfalso; clear -KBL KE; lia].
    set (blk := nthz NB kb).
    assert (INb : In blk NB).
    { subst blk. unfold nthz. rewrite (proj2 (Z.leb_le 0 kb)) by (clear -KB; lia). rewrite (proj2 (Z.ltb_lt _ _) KBL). cbn [andb]. apply nth_In. unfold zlen in KBL. clear -KBL KB. lia. }
    pose proof (NBR blk INb) as PL. pose proof PL as (PL1 & PL2 & PL3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in PL1, PL2, PL3.
    assert (AL : blk mod 4096 = 0).
    { destruct INb as [E|Hb]; [| exact (proj2 (BSEP blk _ (or_introl (conj Hb eq_refl))))].
      pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N15 & _). rewrite <- E. exact N15. }
    apply (CONTn (wz 0x73f10) (wz kb) x12 x13 x14 x15 x16 a7 t0 t1 t2 t3 t4 t5 t6 m1 mo1 None blk).
    unfold npost. cbv zeta. cbn [opt_list opt_iv ngcost nbx_ok]. rewrite app_nil_r, Z.sub_0_r.
    assert (TOK2 : RTOKc (C - 1) C' (sA (nd_st None) s) mo1).
    { rewrite <- (sA_self s) in TOK1.
      exact (RTOK_same_fp_pay E0 FSB0 HR0 L0 RES0 EB0 C C' (C - 1) s a (upd_ndepot (fun k => k + 1) a) mo1 TOK1 (same_fp_upd_ndepot _ _)
               ltac:(rewrite gapR_upd_ndepot; clear; lia) ltac:(rewrite gapD_upd_ndepot1; clear; lia) ltac:(clear -C1; lia)
               ltac:(rewrite gapR_upd_ndepot, gapD_upd_ndepot1; clear; lia)). }
    split; [exact PL|]. split; [exact AL|]. split; [reflexivity|]. split; [exact KBL|]. split; [rewrite nd_node_blocks; cbn [opt_list]; rewrite app_nil_r; reflexivity|].
    split. { unfold WB. cbn [opt_iv]. rewrite app_nil_r. eapply munch_weaken; [| exact MU1]. intros y Hy. cbn in Hy |- *. clear -Hy. lia. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact SK1|]. split; [exact FR1|]. split; [exact TBA1|]. split; [exact NUQ1|].
    split. { eapply (rw_cells_agree bsegs); [| exact M_tlm]. cbn. intros x Hx. apply AGlo; clear -Hx BKR LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact (D_map1 kb KB)]. cbn. intros x Hx. apply AGlo; clear -Hx BKR KB LO LOC' CEILB; unfold kNodesMap1 in KB; lia. }
    split; [eapply wr_at_transport; [exact (D_nbw blk INb)| exact WM1]|].
    split; [exact Qfs1|]. split; [exact Qfds1|]. split; [exact Qtid1|].
    split; [apply AKern_upd_ndepot; exact AK1|].
    split; [exact TOK2|].
    split. { destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK2) as (R2 & R2' & ATK2 & _).
             split; [exact (ATOK_KIA E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK2)| intros x Hx; exact Hx]. }
    exact NZ.
  - (* [comment removed for export] *)
    destruct kb_cases as [[KL _]|(_ & MZ & NK)]; [exfalso; clear -KBE KL; lia|].
    assert (USP112 : bv_unsigned (wz (usp - 112)) = usp - 112) by (apply unsigned_lit; clear -USPR' LO LOC' CEILB; lia).
    assert (STA1 : dput_statics m1).
    { apply (dput_statics_agree m m1 STAT). intros x Hx. apply AGlo; clear -Hx BKR LO LOC' CEILB; lia. }
    assert (TLM1 : rw_cells bsegs m1 5833888 [C4 (wz 0)]).
    { eapply (rw_cells_agree bsegs); [| exact M_tlm]. cbn. intros x Hx. apply AGlo; clear -Hx BKR LO LOC' CEILB; lia. }
    assert (MAP1 : rw_cells bsegs m1 (5833888 + 8 + 8 * kb) [C8 (wz 0)]).
    { pose proof (D_map1 kb KB) as X. unfold nthz in X. rewrite KBE, (proj2 (Z.ltb_ge (zlen NB) (zlen NB))) in X by (clear; lia). rewrite andb_false_r in X.
      rewrite <- KBE in X. replace (5833888 + 8 + 8 * kb) with (1639576 + 4194320 + 8 * kb) by (clear; lia).
      eapply (rw_cells_agree bsegs); [| exact X]. cbn. intros x Hx. apply AGlo; clear -Hx BKR KB LO LOC' CEILB; unfold kNodesMap1 in KB; lia. }
    unfold put_regs.
    eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) (PP s mo)); [| exact KP1|].
    { eapply (cr_A (PP s mo) PIMG0' ); [rewrite USP112; exact SK1| exact LOC'| rewrite USP112; clear -LO; lia| rewrite USP112; clear -UA A47 LEN; lia| exact MI1| exact (proj1 STA1)
        | exact TLM1| exact MAP1| unfold kNodesMap1 in KB; exact KB
        | rewrite USP112; intros y k Hy Hk; apply PSTK0; [exact Hy| clear -Hk UA LEN; lia]
        | intros y k Hy Hk; apply PIMG0; [unfold TLM in Hy; clear -Hy; lia| unfold TLM in Hk; clear -Hk; lia] ]. }
    intros ms2 mo2 POST2 AG2 KP2.
    destruct POST2 as (y13 & y14 & y15 & m2 & -> & MU2 & WM2 & MI2 & SK2 & FR2 & TLM2 & MAP2 & STA2). rewrite USP112 in MU2, SK2, FR2 |- *.
    replace (usp - 112 - 32) with (usp - 144) in MU2, SK2, FR2 |- * by (clear; lia).
    pose proof (magree_frame _ _ AG2) as (Qfds2 & Qvm2 & Qlz2 & Qfs2 & Qh2 & Qtid2 & _).
    pose proof (AKern_frame _ _ _ _ Qvm2 Qlz2 AK1) as AK2.
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 C C' s mo1 mo2 TOK1 AG2 (proj1 KP2)) as TOK2.
    (* [comment removed for export] *)
    destruct (RTOK_elim_roomD E0 FSB0 HR0 L0 RES0 EB0 C C' s mo2 256 TOK2 ltac:(pose proof (ROOM_N MZ) as RM; clear -RM; lia)) as (R & R' & ATK2 & HCR & HCR' & R256 & G1 & G3 & FIT).
    assert (USP144 : bv_unsigned (wz (usp - 144)) = usp - 144) by (apply unsigned_lit; clear -USPR' LO LOC' CEILB; lia).
    eapply (rzA_mm_cfg bsegs (aSc s) (aNc s) (aEBc s) (PP s mo) (NMmap 0 kDepotNodeBlockBytes 3 MAP_ANON_RW) (mmap_CHK 0 kDepotNodeBlockBytes 3 0x22) (dec_as kDepotNodeBlockBytes lo)
              (die_post (fun x r u => x = (r, u)) (wz CR_RET) (wz (usp - 144)) gp tp (wz TLM) (wz (TLM + 8 * kb)) (wz V_PAGESIZE)
                 (wz (BF_depot6.h len ws)) (wz (TD + 4194312)) (wz (BF_depot6.head len ws HS)) (wz 65535) (wz (N + 1)) (wz (TD + 4194320)) (wz (BF_depot6.head len ws HS)) s10 s11
                 F fc kDepotNodeBlockBytes lo m2) _ mo2 K).
    + unfold mmap_CHK, MAP_ANON_RW. apply mm_node_mmap.
    + left. reflexivity.
    + eapply (mmap_die_specA (PP s mo) PIMG0' (dec_as kDepotNodeBlockBytes lo) (fun x r u => x = (r, u)));
        [ exact (dec_as_ok kDepotNodeBlockBytes lo) | rewrite USP144; exact SK2 | exact LOC' | rewrite USP144; clear -LO; lia | rewrite USP144; clear -UA A47 LEN; lia
        | exact MI2 | exact STA2 | reflexivity | unfold A_NAME_TLM; rewrite unsigned_lit by (clear; lia); clear; lia | reflexivity
        | reflexivity | unfold kDepotNodeBlockBytes; clear; lia | unfold kDepotNodeBlockBytes; clear; lia
        | rewrite USP144; intros y k Hy Hk; apply PSTK0; [exact Hy| clear -Hk UA LEN; lia] ].
    + exact KP2.
    + exact KN.
    + intros mo3 AG3 KIA3.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK2 AG3 KIA3) as ATK3.
      pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK3) as KV3. pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3) as EV3.
      pose proof (magree_frame _ _ AG3) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & Qh3 & Qtid3 & _).
      pose proof (AKern_frame _ _ _ _ Qvm3 Qlz3 AK2) as AK3.
      destruct (ev_anon_rw E0 FSB0 HR0 L0 RES0 EB0 HR0_ok LS_L0 GS_L0 HS_L0 RES0_cover RSVD RSVD_pos R R' s mo2 mo3 kDepotNodeBlockBytes ATK2 AG3 KIA3 eq_refl
                  ltac:(unfold kDepotNodeBlockBytes, NMAXA; clear; lia) ltac:(unfold kDepotNodeBlockBytes; clear -R256; lia)) as (NU & OKG & ALL).
      split; [exact NU|]. split; [exact OKG|].
      intros eff mo' HCK NR.
      destruct (ALL eff mo' HCK NR) as (MMA & r & -> & RA & RPL & RSV & RF & RR & -> & KIA' & LIM & MAPS & NOACC & LAZY & RES & MWF & TOP' & NAO & MWF2 & OS2' & PS2').
      set (rZ := bv_unsigned r) in *.
      pose proof (bv_unsigned_in_range 64 r) as RRG. change (bv_modulus 64) with (2^64)%Z in RRG. fold rZ in RRG.
      pose proof (placed_num _ _ RPL ltac:(unfold kDepotNodeBlockBytes; clear; lia)) as (RH & R47 & RB). pose proof RPL as (_ & RCL & _).
      assert (RCL' : rZ + 1048576 <= alloc_ceiling) by exact RCL. assert (RH' : 6303744 <= rZ) by exact RH.
      set (a1 := nd_st (Some rZ)).
      pose proof (nd_fields (Some rZ)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). cbn [opt_list] in F10. fold a1 in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11.
      pose proof (get_region_nd (Some rZ)) as GR. fold a1 in GR.
      assert (R0 : 0 <= R) by (clear -HCR; lia).
      assert (RG0 : 0 <= R' - (kDepotNodeBlockBytes + NMAXA + 4095)) by (unfold DSLACK, kDepotNodeBlockBytes, NMAXA in *; clear -HCR' CSL; lia).
      pose proof (ATOK_node_append E0 FSB0 HR0 L0 RES0 EB0 s a1 mo3 (m_anon mo3 rZ kDepotNodeBlockBytes) r R (R' - (kDepotNodeBlockBytes + NMAXA + 4095))
                    F10 F3 F5 GR F2 F4 KIA' LIM MAPS RES MWF TOP' NAO MWF2 KV3 (conj R0 OS2') (conj RG0 PS2') EV3 R256) as ATK4.
      pose proof (AKern_node_append E0 L0 RES0 s a1 mo3 (m_anon mo3 rZ kDepotNodeBlockBytes) r F10 F3 GR F2 F4 RA RPL RSV MAPS NOACC LAZY RF KV3 Pq Dq AK3 WF) as AK4.
      pose proof (grant_validates E0 L0 RES0 Pq Dq mo3 a r kDepotNodeBlockBytes KV3 AK3 WF RF RA RPL ltac:(unfold kDepotNodeBlockBytes; clear; lia) RSV) as [GV1 GV2]. fold rZ in GV1, GV2.
      exists (r, true). split; [apply dec_as_grant; [unfold b_image_end; fold rZ; clear -RH; lia| fold rZ; clear -RCL LOC'; lia]|].
      exists (aSc (sA a1 s)), (aNc (sA a1 s)), (aEBc (sA a1 s)). split; [exact (ATOK_LI _ _ _ _ _ _ _ _ _ _ ATK4)|].
      split. { intros x Hx. unfold PP in Hx |- *. eapply acc_ok_monoS; [intros w Hw; apply (proj2 (aS_nd (Some rZ) w)); exact Hw|]. rewrite LAZY, Qlz3, Qlz2, Qlz1. exact Hx. }
      intros ms4 mo4 HQ AG4 KIA4 POL4.
      destruct HQ as (r' & u & Eru & HQ). injection Eru as <- <-. cbv iota in HQ.
      destruct HQ as (q0 & q1 & q2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & m4 & -> & MU4 & WM4 & MI4 & SK4 & STA4 & ZN4).
      rewrite USP144 in MU4, SK4. fold rZ in MU4, ZN4.
      replace (ret_pc (Z_to_bv 64 CR_RET)) with (Z_to_bv 64 CR_RET) by (symmetry; apply ret_pc_even; [unfold CR_RET; clear; lia| reflexivity]).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK4 AG4 KIA4) as ATK5.
      pose proof (magree_frame _ _ AG4) as (Qfds4 & Qvm4 & Qlz4 & Qfs4 & Qh4 & Qtid4 & _).
      pose proof (AKern_frame _ _ _ _ Qvm4 Qlz4 AK4) as AK5.
      (* [comment removed for export] *)
      assert (AG24 : forall z, usp - 144 <= z < usp \/ (0 <= z < usp - 464 /\ (z < rZ \/ rZ + kDepotNodeBlockBytes <= z)) -> m4 (wa z) = m2 (wa z)).
      { intros z Hz. apply MU4. rewrite wa_unsigned by (clear -Hz USPR' LO LOC' CEILB; lia). cbn. clear -Hz RCL' LOC' LO. unfold kDepotNodeBlockBytes in *. lia. }
      assert (FR4 : rw_cells bsegs m4 (usp - 112 - 32) [C8 (wz (BF_depot6.TBA len ws)); C8 (wz (N + 1)); C8 (wz 0); C8 (wz 475152)]).
      { replace (usp - 112 - 32) with (usp - 144) by (clear; lia). eapply (rw_cells_agree bsegs); [| exact FR2]. cbn. intros x Hx. apply AG24. clear -Hx. lia. }
      assert (TLM4 : rw_cells bsegs m4 TLM [C4 (wz 1)]).
      { eapply (rw_cells_agree bsegs); [| exact TLM2]. unfold TLM. cbn. intros x Hx. apply AG24. right. unfold kDepotNodeBlockBytes. clear -Hx RH LO LOC' CEILB. lia. }
      assert (MAP4 : rw_cells bsegs m4 (TLM + 8 + 8 * kb) [C8 (wz 0)]).
      { eapply (rw_cells_agree bsegs); [| exact MAP2]. unfold TLM. cbn. intros x Hx. apply AG24. right. unfold kDepotNodeBlockBytes, kNodesMap1 in *. clear -Hx RH KB LO LOC' CEILB. lia. }
      replace (usp - 144) with (usp - 112 - 32) in SK4 |- * by (clear; lia).
      eapply (rzA_seg_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) (PP (sA a1 s) mo4));
        [| split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK5)| intros x Hx; exact Hx]|].
      { eapply (cr_B (PP (sA a1 s) mo4));
          [ intros y k Hy Hk; rewrite <- EPOL; eapply (pol_img' E0 FSB0 HR0 (sA a1 s) mo4 AK5 WE (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK5) ENV0); [clear -Hy; lia| exact Hk]
          | exact SK4| exact LOC'| clear -LO; lia| clear -UA A47 LEN; lia| exact MI4| exact FR4| exact TLM4| exact MAP4| unfold kNodesMap1 in KB; exact KB|].
        intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA a1 s) mo4 AK5 WE ENV0); [exact (Z.le_trans _ _ _ LOC' Hy)|]. clear -Hk UA A47 LEN. lia. }
      intros ms5 mo5 POST5 AG5 KP5.
      destruct POST5 as (m5 & -> & MU5 & WM5 & MI5 & SK5 & TLM5 & MAP5).
      replace (ret_pc (Z_to_bv 64 475152)) with (Z_to_bv 64 475152) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK5 AG5 (proj1 KP5)) as ATK6.
      pose proof (magree_frame _ _ AG5) as (Qfds5 & Qvm5 & Qlz5 & Qfs5 & Qh5 & Qtid5 & _).
      pose proof (AKern_frame _ _ _ _ Qvm5 Qlz5 AK5) as AK6.
      (* [comment removed for export] *)
      eapply (rzA_seg_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) (PP (sA a1 s) mo4)); [| exact KP5|].
      { apply (jmp_back (PP (sA a1 s) mo4) (wz 475152) r p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 m5). }
      intros ms6 mo6 -> AG6 KP6.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK6 AG6 (proj1 KP6)) as ATK7.
      pose proof (magree_frame _ _ AG6) as (Qfds6 & Qvm6 & Qlz6 & Qfs6 & Qh6 & Qtid6 & _).
      pose proof (AKern_frame _ _ _ _ Qvm6 Qlz6 AK6) as AK7.
      rewrite RR. apply (CONTn (wz 475152) p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 m5 mo6 (Some rZ) rZ).
      (* [comment removed for export] *)
      assert (AG12 : forall z, 0 <= z < 2^64 -> (z < usp - 144 \/ usp - 112 <= z) -> (z < 5833888 \/ 5833892 <= z) -> m2 (wa z) = m1 (wa z)).
      { intros z Hz H1 H2. apply MU2. rewrite wa_unsigned by exact Hz. unfold TLM. cbn. clear -H1 H2. lia. }
      assert (AG45 : forall z, 0 <= z < 2^64 -> (z < 5833888 \/ 5833892 <= z) -> (z < 5833896 + 8 * kb \/ 5833904 + 8 * kb <= z) -> m5 (wa z) = m4 (wa z)).
      { intros z Hz H1 H2. apply MU5. rewrite wa_unsigned by exact Hz. unfold TLM. cbn. clear -H1 H2. lia. }
      assert (AG15 : forall z, (usp - 112 <= z < usp \/ 0 <= z < 5833888) -> m5 (wa z) = m1 (wa z)).
      { intros z Hz. unfold kDepotNodeBlockBytes, kNodesMap1 in *.
        rewrite AG45 by (clear -Hz USPR' LO LOC' CEILB BKR KB; lia). rewrite AG24 by (clear -Hz USPR' LO LOC' CEILB BKR RH' RCL'; lia).
        apply AG12; clear -Hz USPR' LO LOC' CEILB BKR; lia. }
      pose proof (gapR_nd (Some rZ)) as QR. pose proof (gapP_nd (Some rZ)) as QP. pose proof (gapD_nd (Some rZ)) as QD. fold a1 in QR, QP, QD.
      cbn [opt_list] in QD. replace (zlen [rZ]) with 1 in QD by reflexivity. pose proof (ROOM_N MZ) as RM.
      assert (TOK7 : RTOKc (C - 1) (C' - (kDepotNodeBlockBytes + NMAXA + 4095)) (sA a1 s) mo6).
      { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ (R - 256) (R' - (kDepotNodeBlockBytes + NMAXA + 4095)) ATK7); cbn [aps_alloc sA aps_set_alloc]; rewrite ?QR, ?QD, ?QP.
        - clear -C1; lia.
        - exact G1.
        - clear -RM; lia.
        - clear -FIT; lia.
        - unfold DSLACK, kDepotNodeBlockBytes, NMAXA in HCR', CSL |- *; clear -HCR' CSL; lia. }
      unfold npost. cbv zeta. cbn [opt_list opt_iv ngcost nbx_ok].
      split; [exact RPL|]. split; [exact RA|].
      split. { unfold nthz. rewrite KBE. unfold zlen. rewrite length_app. cbn [length].
               rewrite (proj2 (Z.leb_le _ _)) by (clear; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (clear; lia). cbn [andb]. rewrite Nat2Z.id. apply nth_middle. }
      split; [rewrite KBE; unfold zlen; rewrite length_app; cbn [length]; clear; lia|].
      split; [exact (nd_node_blocks (Some rZ))|].
      split. { unfold WB. cbn [opt_iv app].
               eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]]]];
                 unfold TLM; intros y Hy; cbn in Hy |- *; clear -Hy; lia. }
      split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM4 WM5)))|].
      split; [exact MI5|]. split; [exact SK5|].
      split. { eapply (rw_cells_agree bsegs); [| exact FR1]. intros x Hx. apply AG15. left. unfold put_frame in Hx. cbn in Hx. clear -Hx. lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact TBA1]. cbn. intros x Hx. apply AG15. right. clear -Hx BKR. lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact NUQ1]. cbn. intros x Hx. apply AG15. right. clear -Hx. lia. }
      split; [exact TLM5|].
      split; [rewrite <- RR; unfold TLM in MAP5; replace (5833896 + 8 * kb) with (5833888 + 8 + 8 * kb) by (clear; lia); exact MAP5|].
      split. { pose proof (rw_CB_wr_at _ _ _ _ ZN4) as W4. rewrite Z2Nat.id in W4 by (unfold kDepotNodeBlockBytes; clear; lia).
               exact (wr_at_transport bsegs _ _ _ _ W4 WM5). }
      pose proof (anon_io mo3 rZ kDepotNodeBlockBytes) as (Xfs & Xfds & Xtid).
      split; [rewrite Qfs6, Qfs5, Qfs4, Xfs, Qfs3, Qfs2; exact Qfs1|].
      split; [rewrite Qfds6, Qfds5, Qfds4, Xfds, Qfds3, Qfds2; exact Qfds1|].
      split; [rewrite Qtid6, Qtid5, Qtid4, Xtid, Qtid3, Qtid2; exact Qtid1|].
      split; [exact AK7|]. split; [exact TOK7|].
      split; [split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK7)| intros x Hx; exact Hx]|].
      split; [reflexivity|]. split; [exact MZ|]. split; [exact GV1| exact GV2].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sg_st (sbx : option Z) (a1 : astate) : astate := match sbx with None => a1 | Some r => upd_store_blocks (fun l => l ++ [r]) a1 end.
Definition sgcost (sbx : option Z) : Z := match sbx with Some _ => kStoreBlockBytes + NMAXA + 4095 | None => 0 end.
#[local] Notation countN := (BF_depot7.count len).
#[local] Notation strd := (BF_depot7.straddles len fr).
#[local] Notation bFv := (BF_depot7.bF len fr).
#[local] Notation fstv := (BF_depot7.fst_start len fr).
#[local] Notation b0 := (BF_depot7.b fr).
#[local] Notation headv := (BF_depot6.head len ws HS).
#[local] Notation NAv := (BF_depot7.NA N).
Definition frE : Z := fstv + countN.
(* [comment removed for export] *)
Definition S_se (x1 x5 x6 x7 : word) (sbF : Z) (x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : mem) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 (Z_to_bv 64 fstv) (Z_to_bv 64 BF_depot3.SS) (Z_to_bv 64 sbF) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 countN)
          (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1)) (Z_to_bv 64 (BF_depot3.TD + 0x400010)) (Z_to_bv 64 headv) s10 s11 x28 x29 x30 x31)
     F (Z_to_bv 64 0x718f4) fc None m' (seg_rom bsegs).
(* [comment removed for export] *)
Definition WC (nbx sbx : option Z) (blk : Z) : list (Z * Z) :=
  (usp - 576, usp) :: WB nbx ++ [(NAv blk, NAv blk + 8); (1574024, 1574024 + 16 + 16 * 4096)] ++ opt_iv sbx kStoreBlockBytes.
Definition spost (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (sbx : option Z) (sbF : Z) (js : list byte) (j1 j2 : word) (m3 : mem) (mo3 : Model) : Prop :=
  let T1 := nd_st nbx in let T2 := sg_st sbx T1 in let SBL2 := SBL ++ opt_list sbx in
     placed blk kDepotNodeBlockBytes /\ blk mod 4096 = 0 /\ nthz (NB ++ opt_list nbx) kb = blk /\ kb < zlen (NB ++ opt_list nbx) /\ nbx_ok nbx blk
  /\ bFv < zlen SBL2 /\ nthz SBL2 bFv = sbF /\ placed sbF kStoreBlockBytes /\ sbF mod 4096 = 0 /\ store_blocks E0 T2 = SBL2 /\ node_blocks E0 T2 = NB ++ opt_list nbx
  /\ munch (WC nbx sbx blk) m m3 /\ wmono bsegs m m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 lo (usp - 224)
  /\ rw_cells bsegs m3 (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8)
  /\ rw_cells bsegs m3 (usp - 144) (BF_depot7.store_frame js (BF_depot7.packv len fr))
  /\ rw_cells bsegs m3 (usp - 208) (BF_depot7.Store_frame len ws HS N blk fstv)
  /\ rw_cells bsegs m3 (usp - 224) (BF_depot7.Alloc_frame sp)
  /\ rw_cells bsegs m3 (NAv blk) [C8 (Z_to_bv 64 h); C4 j1; C4 j2]
  /\ rw_cells bsegs m3 (1639576 + 4 * bkt) [C4 wl] /\ rw_cells bsegs m3 5833880 [C4 (Z_to_bv 64 (N + 1))]
  /\ rw_cells bsegs m3 5833888 [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m3 (5833896 + 8 * kb) [C8 (Z_to_bv 64 blk)]
  /\ wr_at bsegs m3 blk kDepotNodeBlockBytes
  /\ rw_cells bsegs m3 1574024 [C8 (Z_to_bv 64 frE)]
  /\ (exists al, rw_cells bsegs m3 1574032 [C8 al])
  /\ (forall k, 0 <= k < kStoreBlockCount -> k <> bFv ->
        rw_cells bsegs m3 (1574024 + 16 + 16 * k) [C8 (Z_to_bv 64 (nthz SBL2 k)); C4 (Z_to_bv 64 (stored_of frE k))] /\ rw_cells bsegs m3 (1574024 + 28 + 16 * k) [C4 (Z_to_bv 64 0)])
  /\ rw_cells bsegs m3 (1574024 + 16 + 16 * bFv) [C8 (Z_to_bv 64 sbF); C4 (Z_to_bv 64 (fstv mod kStoreBlockFrames))] /\ rw_cells bsegs m3 (1574024 + 28 + 16 * bFv) [C4 (Z_to_bv 64 0)]
  /\ (exists bs, u8arr bsegs m3 sbF bs /\ Z.of_nat (length bs) = kStoreBlockBytes)
  /\ (forall b', In b' SBL -> b' <> sbF -> exists bs, u8arr bsegs m3 b' bs /\ Z.of_nat (length bs) = kStoreBlockBytes)
  /\ m_fs mo3 = m_fs mo /\ m_fds mo3 = m_fds mo /\ m_tid mo3 = m_tid mo
  /\ AKern E0 T2 mo3 /\ RTOKc (C - 1) (C' - ngcost nbx - sgcost sbx) (sA T2 s) mo3
  /\ KIP (aSc (sA T2 s)) (aNc (sA T2 s)) (aEBc (sA T2 s)) (PP (sA T2 s) mo3) mo3
  /\ match sbx with
     | None => ~ (0 < bFv /\ zlen (as_store_blocks a) < bFv)
     | Some r => r = sbF /\ 0 < bFv /\ zlen (as_store_blocks a) < bFv
               /\ (r mod kPageSize =? 0) && (0 <? r) && (r + kStoreBlockBytes <=? alloc_ceiling) && ranges_free (known_ranges E0 T1) r kStoreBlockBytes = true
               /\ app_mem_b r kStoreBlockBytes && negb (in_primary (ae_space_beg E0) r) && negb (in_primary (ae_space_beg E0) (r + kStoreBlockBytes - 1)) && (r + kStoreBlockBytes <=? kHighMemEnd + 1) = true
     end.

(* [comment removed for export] *)
Lemma sg_fields : forall sbx a1,
  as_regions (sg_st sbx a1) = as_regions a1 /\ as_ptr_committed (sg_st sbx a1) = as_ptr_committed a1 /\ as_sec (sg_st sbx a1) = as_sec a1
  /\ as_store_blocks (sg_st sbx a1) = as_store_blocks a1 ++ opt_list sbx /\ as_residue (sg_st sbx a1) = as_residue a1 /\ as_nprim_ever (sg_st sbx a1) = as_nprim_ever a1
  /\ as_ndepot_ins (sg_st sbx a1) = as_ndepot_ins a1 /\ as_keys (sg_st sbx a1) = as_keys a1 /\ as_frames (sg_st sbx a1) = as_frames a1
  /\ as_node_blocks (sg_st sbx a1) = as_node_blocks a1 /\ as_store_stored (sg_st sbx a1) = as_store_stored a1.
Proof. intros [r|] a1; unfold sg_st; destruct a1; cbn; repeat split; try reflexivity. rewrite app_nil_r. reflexivity. Qed.
Lemma aS_sg_grow : forall sbx a1 w, aSc (sA a1 s) w -> aSc (sA (sg_st sbx a1) s) w.
Proof.
  intros [r|] a1 w H; [| exact H]. unfold sg_st.
  unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *. destruct a1; cbn in *.
  destruct H as [AL [H|[H|[H|H]]]]; split; try exact AL; [left; exact H| right; left; exact H| right; right; left; exact H| right; right; right].
  destruct H as (b' & Hb & R). exists b'. split; [apply in_app_iff; left; exact Hb| exact R].
Qed.
Lemma get_region_sg : forall sbx a1 c, get_region (sg_st sbx a1) c = get_region a1 c.
Proof. intros sbx a1 c. unfold get_region. rewrite (proj1 (sg_fields sbx a1)). reflexivity. Qed.
Lemma gapR_sg : forall sbx a1, gapR (sg_st sbx a1) = gapR a1.
Proof. intros sbx a1. pose proof (sg_fields sbx a1) as (F1 & F2 & F3 & F4 & F5 & F6 & _). unfold gapR, regions_bytes. rewrite F6.
  f_equal. clear -F1. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold get_region. rewrite F1. reflexivity. Qed.
Lemma gapP_sg : forall sbx a1, gapP (sg_st sbx a1) = gapP a1.
Proof. intros sbx a1. pose proof (sg_fields sbx a1) as (F1 & F2 & _). unfold gapP. rewrite F2. reflexivity. Qed.
Lemma gapD_sg : forall sbx a1, gapD (sg_st sbx a1) = gapD a1 - 4096 * 2050 * zlen (opt_list sbx).
Proof. intros sbx a1. pose proof (sg_fields sbx a1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). unfold gapD. rewrite F7, F10, F4.
  unfold zlen. rewrite length_app, Nat2Z.inj_add. clear. lia. Qed.
Lemma known_ranges_bump : forall c a1, known_ranges E0 (st_bump c a1) = known_ranges E0 a1.
Proof. intros c a1. destruct a1; reflexivity. Qed.
Lemma known_ranges_stored : forall g a1, known_ranges E0 (upd_store_stored g a1) = known_ranges E0 a1.
Proof. intros g a1. destruct a1; reflexivity. Qed.
(* [comment removed for export] *)
Lemma jmp_back2 : forall P x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
  evtA bsegs P (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x718f4) fc None m' (seg_rom bsegs))
               (MS (mkR x1 (Z_to_bv 64 (usp - 224)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x719ac) fc None m' (seg_rom bsegs)).
Proof. intros. cstep. apply evtA_done. reflexivity. Qed.

(* [comment removed for export] *)
Definition storedC (k : Z) : Z := if k =? bFv then fstv mod kStoreBlockFrames else stored_of frE k.
Definition W4 (nbx : option Z) (blk : Z) : list (Z * Z) :=
  WB nbx ++ [(NAv blk, NAv blk + 8); (1574024, 1574032); (BF_depot7.BI b0 + 8, BF_depot7.BI b0 + 12); (BF_depot7.BI (b0 + 1) + 8, BF_depot7.BI (b0 + 1) + 12)].
Definition qpost (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (js : list byte) (j1 j2 : word) (m4 : mem) (mo4 : Model) : Prop :=
  let T1 := nd_st nbx in
     munch (W4 nbx blk) m m4 /\ wmono bsegs m m4 /\ mem_inv bsegs m4 /\ stk bsegs m4 lo (usp - 224)
  /\ rw_cells bsegs m4 (usp - 112) (put_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A len j8)
  /\ rw_cells bsegs m4 (usp - 144) (BF_depot7.store_frame js (BF_depot7.packv len fr))
  /\ rw_cells bsegs m4 (usp - 208) (BF_depot7.Store_frame len ws HS N blk 0)
  /\ rw_cells bsegs m4 (usp - 224) (BF_depot7.Alloc_frame sp)
  /\ rw_cells bsegs m4 (NAv blk) [C8 (Z_to_bv 64 h); C4 j1; C4 j2]
  /\ rw_cells bsegs m4 1574024 [C8 (Z_to_bv 64 frE)]
  /\ (forall k, 0 <= k < kStoreBlockCount ->
        rw_cells bsegs m4 (1574024 + 16 + 16 * k) [C8 (Z_to_bv 64 (nthz SBL k)); C4 (Z_to_bv 64 (storedC k))] /\ rw_cells bsegs m4 (1574024 + 28 + 16 * k) [C4 (Z_to_bv 64 0)])
  /\ m_fs mo4 = m_fs mo /\ m_fds mo4 = m_fds mo /\ m_tid mo4 = m_tid mo
  /\ AKern E0 T1 mo4 /\ RTOKc (C - 1) (C' - ngcost nbx) (sA T1 s) mo4
  /\ KIP (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo4) mo4.

(* [comment removed for export] *)
Lemma storedC_facts :
  (forall k, 0 <= k -> k <> b0 -> k <> b0 + 1 -> storedC k = stored_of fr k)
  /\ (strd = false -> storedC b0 = stored_of fr b0 /\ storedC (b0 + 1) = stored_of fr (b0 + 1))
  /\ (strd = true -> storedC b0 = kStoreBlockFrames /\ storedC (b0 + 1) = countN - BF_depot7.in_first fr)
  /\ 0 <= fstv mod kStoreBlockFrames < kStoreBlockFrames /\ storedC bFv = fstv mod kStoreBlockFrames.
Proof.
  pose proof FRF as (FR0 & FR32 & FRB). pose proof LEN as LEN'. pose proof LWS as LWS'.
  pose proof (Z.div_mod fr kStoreBlockFrames ltac:(unfold kStoreBlockFrames; clear; lia)) as DM.
  pose proof (Z.mod_pos_bound fr kStoreBlockFrames ltac:(unfold kStoreBlockFrames; clear; lia)) as MB.
  assert (Eb : BF_depot7.b fr = fr / kStoreBlockFrames) by reflexivity. assert (Ec : BF_depot7.count len = len + 1) by reflexivity.
  assert (Ei : BF_depot7.in_first fr = kStoreBlockFrames - fr mod kStoreBlockFrames) by reflexivity.
  unfold storedC, frE. split; [| split; [| split]].
  - intros k Hk K1 K2. destruct (BF_depot7.straddles len fr) eqn:STR.
    + pose proof (straddles_true len ws N fr ltac:(unfold zlen in LEN'; exact LEN') ltac:(unfold zlen in LWS'; exact LWS') FR0 STR) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). rewrite D2, D3. rewrite (proj2 (Z.eqb_neq _ _) K2).
      unfold straddles in STR. apply negb_true_iff in STR. apply Z.leb_gt in STR.
      unfold stored_of. rewrite Eb, Ec, Ei in *. unfold kStoreBlockFrames in *. clear -Hk K1 K2 DM MB STR LEN' LWS' FR0. nia.
    + pose proof (straddles_false len ws N fr ltac:(unfold zlen in LEN'; exact LEN') FR0 STR) as (D1 & D2 & D3 & D4). rewrite D2, D3. rewrite (proj2 (Z.eqb_neq _ _) K1).
      unfold straddles in STR. apply negb_false_iff in STR. apply Z.leb_le in STR.
      unfold stored_of. rewrite Eb, Ec in *. unfold kStoreBlockFrames in *. clear -Hk K1 K2 DM MB STR LEN' LWS' FR0. nia.
  - intros STR. pose proof (straddles_false len ws N fr ltac:(unfold zlen in LEN'; exact LEN') FR0 STR) as (D1 & D2 & D3 & D4). rewrite D2, D3. rewrite Z.eqb_refl.
    assert (NE : b0 + 1 =? b0 = false) by (apply Z.eqb_neq; clear; lia). rewrite NE.
    unfold straddles in STR. apply negb_false_iff in STR. apply Z.leb_le in STR.
    unfold stored_of. rewrite Eb, Ec in *. unfold kStoreBlockFrames in *. clear -DM MB STR LEN' LWS' FR0. split; nia.
  - intros STR. pose proof (straddles_true len ws N fr ltac:(unfold zlen in LEN'; exact LEN') ltac:(unfold zlen in LWS'; exact LWS') FR0 STR) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). rewrite D2, D3. rewrite Z.eqb_refl.
    assert (NE : b0 =? b0 + 1 = false) by (apply Z.eqb_neq; clear; lia). rewrite NE.
    unfold straddles in STR. apply negb_true_iff in STR. apply Z.leb_gt in STR.
    unfold stored_of. rewrite Eb, Ec, Ei in *. unfold kStoreBlockFrames in *. clear -DM MB STR LEN' LWS' FR0 D5. split; [nia|].
    rewrite (Z.mod_eq (fr + (len + 1)) (2^20)) by (clear; lia). rewrite D5. rewrite (Z.mod_eq fr (2^20)) in * by (clear; lia). nia.
  - rewrite Z.eqb_refl. split; [apply Z.mod_pos_bound; unfold kStoreBlockFrames; clear; lia| reflexivity].
Qed.

Lemma AWf_nd : forall nbx, AWf E0 Pq Dq (nd_st nbx).
Proof.
  intros nbx. pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & _).
  eapply (AWf_depot_only E0 Pq Dq a (nd_st nbx)); [| exact F8| rewrite F9; clear; lia| rewrite F7; clear; lia| exact WF].
  unfold same_alloc. destruct nbx; unfold nd_st; destruct (aps_alloc s); cbn; repeat split; reflexivity.
Qed.

Lemma sd_stage : forall (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (js : list byte) (j1 j2 : word) (m4 : mem) (mo4 : Model)
    (x6 x7 x14 x16 x17 x28 x29 x30 x31 : word),
  qpost j8 wl nbx blk js j1 j2 m4 mo4 ->
  placed blk kDepotNodeBlockBytes -> blk mod 4096 = 0 -> nthz (NB ++ opt_list nbx) kb = blk -> kb < zlen (NB ++ opt_list nbx) -> node_blocks E0 (nd_st nbx) = NB ++ opt_list nbx ->
  rw_cells bsegs m4 (1639576 + 4 * bkt) [C4 wl] -> rw_cells bsegs m4 5833880 [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells bsegs m4 5833888 [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m4 (5833896 + 8 * kb) [C8 (Z_to_bv 64 blk)] -> wr_at bsegs m4 blk kDepotNodeBlockBytes ->
  nbx_ok nbx blk ->
  (forall (x1 x5 x6' x7' : word) (sbF : Z) (q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (m3 : mem) (mo3 : Model) (sbx : option Z) (js' : list byte) (j1' j2' : word),
     spost j8 wl nbx blk sbx sbF js' j1' j2' m3 mo3 ->
     realizes_cfg acfg bsegs (mkCfg (S_se x1 x5 x6' x7' sbF q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3) mo3) K) ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (BF_depot7.alloc_regs2 sp gp tp s10 s11 len ws HS N (Z_to_bv 64 0x717ec) (Z_to_bv 64 bFv) x6 x7 (Z_to_bv 64 len) x14 x16 x17 x28 x29 x30 x31 fstv)
               F (Z_to_bv 64 0x718c4) fc None m4 (seg_rom bsegs)) mo4) K.
Proof.
  intros until x31. intros QP PL AL NTH KBL NBE TBA4 NUQ4 TLM4 MAP4 WR4 BRn CONTs.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. unfold K_DEPOT in LO.
  pose proof KB0 as KB. pose proof HN as (HN0 & HN1 & HN2). pose proof FRF as (FR0 & FR32 & FRB). pose proof FRLE as FRLE'.
  pose proof (Z.mod_pos_bound h kTabSize ltac:(unfold kTabSize; clear; lia)) as BKR. change (h mod kTabSize) with bkt in BKR. unfold kTabSize in BKR.
  pose proof PL as (PL1 & PL2 & PL3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in PL1, PL2, PL3.
  pose proof (Z.mod_pos_bound (N + 1) kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; clear; lia)) as NMR. unfold kDepotNodesPerBlock in NMR.
  assert (ENA : BF_depot7.NA N blk = blk + 16 * ((N + 1) mod 65536)) by reflexivity.
  destruct QP as (MU4 & WM4 & MI4 & SK4 & FR4 & SF4 & STF4 & AFR4 & NODE4 & SS4 & BLK4 & Qfs4 & Qfds4 & Qtid4 & AK4 & TOK4 & KP4).
  set (T1 := nd_st nbx) in *.
  pose proof (fst_facts len ws N fr ltac:(unfold zlen in LEN; exact LEN) ltac:(unfold zlen in LWS; exact LWS) FR0 FR32 FRB) as (FS0 & FS32 & FSM & FSB & FSR & PKR).
  pose proof storedC_facts as (SC1 & SC2 & SC3 & SCM & SCB).
  assert (Eb : BF_depot7.b fr = fr / kStoreBlockFrames) by reflexivity. assert (Ec : BF_depot7.count len = len + 1) by reflexivity.
  assert (B0nn : 0 <= BF_depot7.b fr) by (rewrite Eb; apply Z.div_pos; [exact FR0| unfold kStoreBlockFrames; clear; lia]).
  pose proof FRB as FRB'. unfold kStoreBlockCount in FRB'.
  (* [comment removed for export] *)
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK4) as (R2 & R2' & ATK4 & _).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK4) as EV4. pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK4) as KV4. cbn [aps_alloc sA aps_set_alloc] in KV4.
  assert (PSTK1 : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> PP (sA T1 s) mo4 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T1 s) mo4 AK4 WE ENV0); clear -Hy Hk LOC' A47; lia. }
  assert (PIMG1 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA T1 s) mo4 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA T1 s) mo4 AK4 WE EV4 ENV0); [clear -Hy; lia| exact Hk]. }
  assert (SBLR : forall sb', In sb' SBL -> 0x603000 <= sb' /\ sb' + kStoreBlockBytes <= alloc_ceiling).
  { intros sb' Hsb. pose proof (proj1 (SBR sb' Hsb)) as (P1 & P2 & P3). split; [exact P1| exact P2]. }
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo4)); [| exact KP4|].
  { eapply (put_sd (PP (sA T1 s) mo4) sp gp tp s10 s11 F fc lo (A + 8 * zlen ws) len ws HS N blk fr SBL);
      [ exact LOC'| clear -LO; lia| clear -UA LEN; lia| unfold zlen in LEN; exact LEN| unfold zlen in LWS; exact LWS| exact FR0| exact FR32| exact FRB| exact FRLE'
      | exact SBLR| exact PSTK1| exact PIMG1| exact MI4| exact STF4|].
    intros k Hk. exists (Z_to_bv 64 (storedC k)). unfold BF_depot7.BI, BF_depot3.SS. exact (proj1 (BLK4 k Hk)). }
  intros ms5 mo5 POST5 AG5 KP5.
  destruct POST5 as (m5 & MU5 & WM5 & MI5 & STF5 & ARMS).
  pose proof (magree_frame _ _ AG5) as (Qfds5 & Qvm5 & Qlz5 & Qfs5 & Qh5 & Qtid5 & _).
  pose proof (AKern_frame _ _ _ _ Qvm5 Qlz5 AK4) as AK5.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK4 AG5 (proj1 KP5)) as TOK5.
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK5) as (R5 & R5' & ATK5 & _). pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK5) as EV5.
  pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK5) as KV5. cbn [aps_alloc sA aps_set_alloc] in KV5.
  assert (AG45 : forall z, 0 <= z < 2^64 -> (z < usp - 208 \/ usp - 200 <= z) -> m5 (wa z) = m4 (wa z)).
  { intros z Hz H1. apply MU5. rewrite wa_unsigned by exact Hz. cbn. clear -H1. lia. }
  (* [comment removed for export] *)
  assert (INblk : In blk (node_blocks E0 T1)).
  { rewrite NBE, <- NTH. unfold nthz. rewrite (proj2 (Z.leb_le 0 kb)) by (clear -KB; lia). rewrite (proj2 (Z.ltb_lt _ _) KBL). cbn [andb]. apply nth_In. unfold zlen in KBL. clear -KBL KB. lia. }
  assert (ESBL1 : store_blocks E0 T1 = SBL).
  { unfold store_blocks, SBL. pose proof (nd_fields nbx) as (_ & _ & _ & F4 & _). fold T1 in F4. rewrite F4. reflexivity. }
  assert (DJNS : forall b', In b' SBL -> blk + kDepotNodeBlockBytes <= b' \/ b' + kStoreBlockBytes <= blk).
  { intros b' Hb. apply (node_store_disjoint T1 mo4 blk b' KV4 AK4 INblk). rewrite ESBL1. exact Hb. }
  assert (AG04s : forall b' z, In b' SBL -> b' <= z < b' + kStoreBlockBytes -> m4 (wa z) = m (wa z)).
  { intros b' z Hb Hz. pose proof (SBLR b' Hb) as [S1 S2]. pose proof (DJNS b' Hb) as DJ.
    apply MU4. rewrite wa_unsigned by (clear -Hz S1 S2 CEILB; unfold kStoreBlockBytes in *; lia). unfold W4, WB. rewrite ENA.
    destruct nbx as [r|]; [rewrite (proj1 BRn)|]; cbn [outside opt_iv app fst snd]; unfold BF_depot7.BI, BF_depot3.SS, kDepotNodeBlockBytes, kStoreBlockBytes in *;
      clear -Hz S1 S2 DJ CEILB LO LOC' NMR FRB BKR KB; unfold kStoreBlockCount, kNodesMap1 in *; lia. }
  assert (AGlo5 : forall z, 0 <= z < usp - 208 -> m5 (wa z) = m4 (wa z)) by (intros z Hz; apply AG45; clear -Hz USPR' LO LOC' CEILB; lia).
  destruct D_al as [al AL0].
  assert (AL5 : rw_cells bsegs m5 (SSo + 8) [C8 al]).
  { eapply (rw_cells_agree bsegs); [| exact AL0]. unfold SSo. cbn. intros x Hx. rewrite AGlo5 by (clear -Hx LO LOC' CEILB; lia).
    apply MU4. rewrite wa_unsigned by (clear -Hx; lia). unfold W4, WB. rewrite ENA.
    destruct nbx as [r|]; [rewrite (proj1 BRn)|]; cbn [outside opt_iv app fst snd]; unfold BF_depot7.BI, BF_depot3.SS, kDepotNodeBlockBytes in *;
      clear -Hx LO LOC' CEILB PL1 NMR BKR KB B0nn FRB'; unfold kNodesMap1 in *; lia. }
  destruct ARMS as [[BFL ->]|[BFE ->]].
  - (* [comment removed for export] *)
    set (sbF := nthz SBL bFv).
    assert (INsb : In sbF SBL).
    { subst sbF. unfold nthz. rewrite (proj2 (Z.leb_le 0 bFv)) by (clear -FSR; lia). rewrite (proj2 (Z.ltb_lt _ _) BFL). cbn [andb]. apply nth_In. unfold zlen in BFL. clear -BFL FSR. lia. }
    pose proof (SBR sbF INsb) as [SPL SAL]. pose proof (SBLR sbF INsb) as [SB1 SB2].
    apply (CONTs (Z_to_bv 64 0x717ec) (Z_to_bv 64 bFv) x6 x7 sbF (Z_to_bv 64 BF_depot3.SS) (Z_to_bv 64 (BF_depot7.BI bFv - 16)) (Z_to_bv 64 (usp - 136)) x14 (Z_to_bv 64 countN) x16 x17 x28 x29 x30 x31 m5 mo5 None js j1 j2).
    unfold spost. cbv zeta. cbn [opt_list opt_iv sg_st sgcost]. rewrite !app_nil_r, Z.sub_0_r.
    split; [exact PL|]. split; [exact AL|]. split; [exact NTH|]. split; [exact KBL|]. split; [exact BRn|].
    split; [exact BFL|]. split; [reflexivity|]. split; [exact SPL|]. split; [exact SAL|]. split; [exact ESBL1|]. split; [exact NBE|].
    split. { unfold WC, W4 in *. eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]];
             intros y Hy; unfold WB, BF_depot7.BI, BF_depot3.SS in *; cbn [opt_iv app] in Hy |- *.
             - destruct nbx; cbn [app] in Hy |- *; clear -Hy FRB' B0nn; cbn in Hy |- *; lia.
             - destruct nbx; cbn [app] in Hy |- *; clear -Hy; cbn in Hy |- *; lia. }
    split; [exact (wmono_trans _ _ _ _ WM4 WM5)|]. split; [exact MI5|].
    split; [eapply (stk_transport_disjoint bsegs); [exact SK4| exact MU5| exact WM5| cbn; clear; lia]|].
    split. { eapply (rw_cells_agree bsegs); [| exact FR4]. unfold put_frame. cbn. intros x Hx. apply AG45; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact SF4]. unfold BF_depot7.store_frame. cbn. intros x Hx. apply AG45; clear -Hx USPR' LO LOC' CEILB; lia. }
    split; [exact STF5|].
    split. { eapply (rw_cells_agree bsegs); [| exact AFR4]. unfold BF_depot7.Alloc_frame. cbn. intros x Hx. apply AG45; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact NODE4]. rewrite ENA. cbn. intros x Hx. apply AGlo5. clear -Hx PL1 PL2 NMR LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact TBA4]. cbn. intros x Hx. apply AGlo5. clear -Hx BKR LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact NUQ4]. cbn. intros x Hx. apply AGlo5. clear -Hx LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact TLM4]. cbn. intros x Hx. apply AGlo5. clear -Hx LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact MAP4]. cbn. intros x Hx. apply AGlo5. unfold kNodesMap1 in KB. clear -Hx KB LO LOC' CEILB; lia. }
    split; [exact (wr_at_transport bsegs _ _ _ _ WR4 WM5)|].
    split. { eapply (rw_cells_agree bsegs); [| exact SS4]. cbn. intros x Hx. apply AGlo5. clear -Hx LO LOC' CEILB; lia. }
    split. { exists al. unfold SSo in AL5. exact AL5. }
    split. { intros k Hk NEk. pose proof (BLK4 k Hk) as [B1 B2]. unfold storedC in B1. rewrite (proj2 (Z.eqb_neq _ _) NEk) in B1. unfold kStoreBlockCount in Hk. split.
             - eapply (rw_cells_agree bsegs); [| exact B1]. cbn. intros x Hx. apply AGlo5. clear -Hx Hk LO LOC' CEILB; lia.
             - eapply (rw_cells_agree bsegs); [| exact B2]. cbn. intros x Hx. apply AGlo5. clear -Hx Hk LO LOC' CEILB; lia. }
    pose proof (BLK4 bFv FSR) as [Bf1 Bf2]. rewrite SCB in Bf1. pose proof FSR as FSR'. unfold kStoreBlockCount in FSR'.
    split. { eapply (rw_cells_agree bsegs); [| exact Bf1]. cbn. intros x Hx. apply AGlo5. clear -Hx FSR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact Bf2]. cbn. intros x Hx. apply AGlo5. clear -Hx FSR' LO LOC' CEILB; lia. }
    split. { destruct (D_sbw sbF INsb) as (bs & U & L). exists bs. split; [| exact L]. eapply u8arr_agree; [| exact U]. intros x Hx. rewrite L in Hx.
             rewrite AGlo5 by (clear -Hx SB1 SB2 LO LOC' CEILB; unfold kStoreBlockBytes in *; lia). apply (AG04s sbF); [exact INsb| exact Hx]. }
    split. { intros b' Hb _. destruct (D_sbw b' Hb) as (bs & U & L). exists bs. split; [| exact L]. pose proof (SBLR b' Hb) as [Y1 Y2]. eapply u8arr_agree; [| exact U]. intros x Hx. rewrite L in Hx.
             rewrite AGlo5 by (clear -Hx Y1 Y2 LO LOC' CEILB; unfold kStoreBlockBytes in *; lia). apply (AG04s b'); [exact Hb| exact Hx]. }
    split; [rewrite Qfs5; exact Qfs4|]. split; [rewrite Qfds5; exact Qfds4|]. split; [rewrite Qtid5; exact Qtid4|].
    split; [exact AK5|]. split; [exact TOK5|].
    split; [split; [exact (proj1 KP5)| intros x Hx; exact Hx]|].
    rewrite ESBL in BFL. clear -BFL. lia.
  - (* [comment removed for export] *)
    assert (BFz : bFv = zlen (as_store_blocks a) + 1) by (rewrite ESBL in BFE; exact BFE).
    assert (USP224 : bv_unsigned (Z_to_bv 64 (usp - 224)) = usp - 224) by (apply unsigned_lit; clear -USPR' LO LOC' CEILB; lia).
    assert (NTH0 : nthz SBL bFv = 0).
    { unfold nthz. rewrite BFE. rewrite (proj2 (Z.ltb_ge (zlen SBL) (zlen SBL))) by (clear; lia). rewrite andb_false_r. reflexivity. }
    pose proof (BLK4 bFv FSR) as [Bf1 Bf2]. rewrite SCB, NTH0 in Bf1. pose proof FSR as FSR'. unfold kStoreBlockCount in FSR'.
    (* [comment removed for export] *)
    eapply (rzA_seg_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo5)); [| split; [exact (proj1 KP5)| intros x Hx; exact Hx]|].
    { eapply (gc_A (PP (sA T1 s) mo5)).
      - intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA T1 s) mo5 AK5 WE EV5 ENV0); [clear -Hy; lia| exact Hk].
      - rewrite USP224. eapply (stk_transport_disjoint bsegs); [exact SK4| exact MU5| exact WM5| cbn; clear; lia].
      - exact LOC'.
      - rewrite USP224. clear -LO; lia.
      - rewrite USP224. clear -UA A47 LEN; lia.
      - exact MI5.
      - exact AL5.
      - unfold SSo. eapply (rw_cells_agree bsegs); [| exact Bf1]. cbn. intros x Hx. apply AGlo5. clear -Hx FSR' LO LOC' CEILB; lia.
      - unfold SSo. eapply (rw_cells_agree bsegs); [| exact Bf2]. cbn. intros x Hx. apply AGlo5. clear -Hx FSR' LO LOC' CEILB; lia.
      - exact FSR'.
      - clear -SCM. unfold kStoreBlockFrames in *. lia.
      - rewrite USP224. intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T1 s) mo5 AK5 WE ENV0); clear -Hy Hk LOC' UA A47 LEN; lia. }
    intros ms6 mo6 POST6 AG6 KP6.
    destruct POST6 as (p2 & p3 & p4 & p5 & al' & m6 & -> & MU6 & WM6 & MI6 & SK6 & FR6 & AL6 & BF6 & MX6). rewrite USP224 in MU6, SK6, FR6 |- *.
    replace (usp - 224 - 32) with (usp - 256) in MU6, SK6, FR6 |- * by (clear; lia).
    pose proof (magree_frame _ _ AG6) as (Qfds6 & Qvm6 & Qlz6 & Qfs6 & Qh6 & Qtid6 & _).
    pose proof (AKern_frame _ _ _ _ Qvm6 Qlz6 AK5) as AK6.
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK5 AG6 (proj1 KP6)) as TOK6.
    assert (AG56 : forall z, 0 <= z < 2^64 -> (z < usp - 256 \/ usp - 224 <= z) -> (z < SSo + 28 + 16 * bFv \/ SSo + 32 + 16 * bFv <= z) -> (z < SSo + 8 \/ SSo + 16 <= z) -> m6 (wa z) = m5 (wa z)).
    { intros z Hz H1 H2 H3. apply MU6. rewrite wa_unsigned by exact Hz. cbn. clear -H1 H2 H3. lia. }
    assert (STA6 : dput_statics m6).
    { apply (dput_statics_agree m m6 STAT). intros x Hx. unfold SSo in AG56. rewrite AG56 by (clear -Hx USPR' LO LOC' CEILB FSR'; lia). rewrite AGlo5 by (clear -Hx LO LOC' CEILB; lia).
      apply MU4. rewrite wa_unsigned by (clear -Hx; lia). unfold W4, WB. rewrite ENA.
      destruct nbx as [r|]; [rewrite (proj1 BRn)|]; cbn [outside opt_iv app fst snd]; unfold BF_depot7.BI, BF_depot3.SS, kDepotNodeBlockBytes in *;
        clear -Hx LO LOC' CEILB PL1 NMR BKR KB B0nn FRB'; unfold kNodesMap1 in *; lia. }
    (* [comment removed for export] *)
    assert (FSLE : kStoreBlockFrames * (zlen (as_store_blocks a) + 1) <= fstv).
    { rewrite <- BFz, FSB. apply Z.mul_div_le. unfold kStoreBlockFrames; clear; lia. }
    assert (FSHI : fstv <= fr + 62).
    { destruct (BF_depot7.straddles len fr) eqn:STR.
      - destruct (straddles_true len ws N fr ltac:(unfold zlen in LEN; exact LEN) ltac:(unfold zlen in LWS; exact LWS) FR0 STR) as (_ & _ & E3 & _). rewrite E3, Ec. clear -LEN LWS; lia.
      - destruct (straddles_false len ws N fr ltac:(unfold zlen in LEN; exact LEN) FR0 STR) as (_ & _ & E3 & _). rewrite E3. clear; lia. }
    pose proof (ROOM_S fstv FSLE FSHI) as RM.
    assert (ZL : 0 <= zlen (opt_list nbx) <= 1) by (clear; destruct nbx as [rq|]; [change (zlen (opt_list (Some rq))) with 1| change (zlen (opt_list None)) with 0]; lia).
    assert (RMS : 4096 * 2050 <= gapD T1).
    { change (gapD T1) with (gapD (nd_st nbx)). rewrite gapD_nd. clear -RM ZL. nia. }
    destruct (RTOK_elim_roomD E0 FSB0 HR0 L0 RES0 EB0 _ _ _ mo6 2050 TOK6 RMS) as (R & R' & ATK6 & HCR & HCR' & R2050 & G1 & G3 & FIT). cbn [aps_alloc sA aps_set_alloc] in G1, G3, FIT.
    assert (USP256 : bv_unsigned (Z_to_bv 64 (usp - 256)) = usp - 256) by (apply unsigned_lit; clear -USPR' LO LOC' CEILB; lia).
    set (P2 := fun x : acc => exists y n, x = (Z_to_bv 64 y, n) /\ ((lo <= y /\ y + Z.of_nat n <= usp - 256) \/ (0xa5000 <= y /\ y + Z.of_nat n <= 0x603000))).
    assert (P2pol : forall aX moX, AKern E0 aX moX -> ENVOK E0 FSB0 (sA aX s) -> forall x, P2 x -> acc_ok (m_vm_lazy moX) (aSc (sA aX s)) x).
    { intros aX moX AKX EVX x (y & n & -> & [[H1 H2]|[H1 H2]]).
      - eapply (pol_stack' E0 FSB0 HR0 (sA aX s) moX AKX WE ENV0); clear -H1 H2 LOC' LO USPR'; lia.
      - eapply (pol_img' E0 FSB0 HR0 (sA aX s) moX AKX WE EVX ENV0); [clear -H1; lia| exact H2]. }
    assert (P2dat : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P2 (Z_to_bv 64 y, k)) by (intros y k Hy Hk; exists y, k; split; [reflexivity| right; split; assumption]).
    assert (P2stk : forall y k, lo <= y -> y + Z.of_nat k <= usp - 256 -> P2 (Z_to_bv 64 y, k)) by (intros y k Hy Hk; exists y, k; split; [reflexivity| left; split; assumption]).
    eapply (rzA_mm_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) P2 (NMmap 0 kStoreBlockBytes 3 MAP_ANON_NR) (mmap_CHK 0 kStoreBlockBytes 3 0x4022) (dec_as kStoreBlockBytes lo)
              (die_post (fun x r u => x = (r, u)) (Z_to_bv 64 GC_RET) (Z_to_bv 64 (usp - 256)) gp tp (Z_to_bv 64 (SSo + 28 + 16 * bFv)) (Z_to_bv 64 (SSo + 16 + 16 * bFv)) (Z_to_bv 64 countN)
                 (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 65535) (Z_to_bv 64 (N + 1)) (Z_to_bv 64 (BF_depot3.TD + 4194320)) (Z_to_bv 64 headv) s10 s11
                 F fc kStoreBlockBytes lo m6) _ mo6 K).
    + unfold mmap_CHK, MAP_ANON_NR. apply mm_node_mmap.
    + left. reflexivity.
    + eapply (mmap_nrdie_specA P2 P2dat (dec_as kStoreBlockBytes lo) (fun x r u => x = (r, u)));
        [ exact (dec_as_ok kStoreBlockBytes lo) | rewrite USP256; exact SK6 | exact LOC' | rewrite USP256; clear -LO; lia | rewrite USP256; clear -UA A47 LEN; lia
        | exact MI6 | exact (proj1 STA6) | reflexivity | unfold A_NAME_SS; rewrite unsigned_lit by (clear; lia); clear; lia
        | reflexivity | unfold kStoreBlockBytes; clear; lia | unfold kStoreBlockBytes; clear; lia
        | rewrite USP256; exact P2stk ].
    + split; [exact (proj1 KP6)| exact (P2pol T1 mo6 AK6 (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK6))].
    + exact KN.
    + intros mo7 AG7 KIA7.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK6 AG7 KIA7) as ATK7.
      pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK7) as KV7. cbn [aps_alloc sA aps_set_alloc] in KV7. pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK7) as EV7.
      pose proof (magree_frame _ _ AG7) as (Qfds7 & Qvm7 & Qlz7 & Qfs7 & Qh7 & Qtid7 & _).
      pose proof (AKern_frame _ _ _ _ Qvm7 Qlz7 AK6) as AK7.
      destruct (ev_anon_nr E0 FSB0 HR0 L0 RES0 EB0 LS_L0 GS_L0 HS_L0 RES0_cover RSVD RSVD_pos R R' (sA T1 s) mo6 mo7 kStoreBlockBytes ATK6 AG7 KIA7 eq_refl
                  ltac:(unfold kStoreBlockBytes, NMAXA; clear; lia)) as (NU & OKG & ALL).
      split; [exact NU|]. split; [exact OKG|].
      intros eff mo' HCK NR.
      destruct (ALL eff mo' HCK NR) as (MMA & r & -> & RA & RPL & RSV & RF & RR & -> & KIA' & LIM & MAPS & NOACC & LAZY & RES & MWF & TOP' & NAO & MWF2 & OS2' & PS2').
      set (rZ := bv_unsigned r) in *.
      pose proof (bv_unsigned_in_range 64 r) as RRG. change (bv_modulus 64) with (2^64)%Z in RRG. fold rZ in RRG.
      pose proof (placed_num _ _ RPL ltac:(unfold kStoreBlockBytes; clear; lia)) as (RH & R47 & RB). pose proof RPL as (_ & RCL & _).
      assert (RCL' : rZ + 8388608 <= alloc_ceiling) by exact RCL. assert (RH' : 6303744 <= rZ) by exact RH.
      set (T2 := sg_st (Some rZ) T1).
      pose proof (sg_fields (Some rZ) T1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11). cbn [opt_list] in F4. fold T2 in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11.
      pose proof (get_region_sg (Some rZ) T1) as GR. fold T2 in GR.
      assert (R0 : 0 <= R) by (clear -HCR; lia).
      assert (RG0 : 0 <= R' - (kStoreBlockBytes + NMAXA + 4095)).
      { assert (NGB : 0 <= ngcost nbx <= kDepotNodeBlockBytes + NMAXA + 4095) by (clear; destruct nbx; cbn [ngcost]; unfold kDepotNodeBlockBytes, NMAXA; lia).
        pose proof CSL as X. unfold DSLACK, kStoreBlockBytes, kDepotNodeBlockBytes, NMAXA in NGB, X, HCR' |- *. clear -HCR' X NGB; lia. }
      pose proof (ATOK_store_append E0 FSB0 HR0 L0 RES0 EB0 HR0_ok (sA T1 s) T2 mo7 (m_anon_nr mo7 rZ kStoreBlockBytes) r R (R' - (kStoreBlockBytes + NMAXA + 4095))
                    F4 F3 F5 GR F2 F10 KIA' LIM MAPS RES MWF TOP' NAO MWF2 KV7 (conj R0 OS2') (conj RG0 PS2') EV7 R2050) as ATK8.
      rewrite sA_sA in ATK8.
      pose proof (AKern_store_append E0 L0 RES0 (sA T1 s) T2 mo7 (m_anon_nr mo7 rZ kStoreBlockBytes) r F4 F3 GR F2 F10 RA RPL RSV MAPS NOACC LAZY RF KV7 Pq Dq AK7 (AWf_nd nbx)) as AK8.
      pose proof (grant_validates E0 L0 RES0 Pq Dq mo7 T1 r kStoreBlockBytes KV7 AK7 (AWf_nd nbx) RF RA RPL ltac:(unfold kStoreBlockBytes; clear; lia) RSV) as [GV1 GV2]. fold rZ in GV1, GV2.
      exists (r, true). split; [apply dec_as_grant; [unfold b_image_end; fold rZ; clear -RH; lia| fold rZ; clear -RCL LOC'; lia]|].
      exists (aSc (sA T2 s)), (aNc (sA T2 s)), (aEBc (sA T2 s)). split; [exact (ATOK_LI _ _ _ _ _ _ _ _ _ _ ATK8)|].
      split. { intros x Hx. apply (P2pol T2 _ AK8 (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK8) x Hx). }
      intros ms8 mo8 HQ AG8 KIA8 POL8.
      destruct HQ as (r' & u & Eru & HQ). injection Eru as <- <-. cbv iota in HQ.
      destruct HQ as (q0 & q1 & q2 & p1 & p2' & p3' & p4' & p5' & p6 & p7 & q3 & q4 & q5 & q6 & m8 & -> & MU8 & WM8 & MI8 & SK8 & STA8 & ZN8).
      rewrite USP256 in MU8, SK8. fold rZ in MU8, ZN8.
      replace (ret_pc (Z_to_bv 64 GC_RET)) with (Z_to_bv 64 GC_RET) by (symmetry; apply ret_pc_even; [unfold GC_RET; clear; lia| reflexivity]).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK8 AG8 KIA8) as ATK9.
      pose proof (magree_frame _ _ AG8) as (Qfds8 & Qvm8 & Qlz8 & Qfs8 & Qh8 & Qtid8 & _).
      pose proof (AKern_frame _ _ _ _ Qvm8 Qlz8 AK8) as AK9.
      assert (AG68 : forall z, usp - 256 <= z < usp \/ (0 <= z < usp - 576 /\ (z < rZ \/ rZ + kStoreBlockBytes <= z)) -> m8 (wa z) = m6 (wa z)).
      { intros z Hz. apply MU8. rewrite wa_unsigned by (clear -Hz USPR' LO LOC' CEILB; lia). cbn. clear -Hz RCL' LOC' LO. unfold kStoreBlockBytes in *. lia. }
      assert (FR8 : rw_cells bsegs m8 (usp - 224 - 32) [C8 (Z_to_bv 64 countN); C8 (Z_to_bv 64 BF_depot3.SS); C8 (Z_to_bv 64 fstv); C8 (Z_to_bv 64 465324)]).
      { replace (usp - 224 - 32) with (usp - 256) by (clear; lia). eapply (rw_cells_agree bsegs); [| exact FR6]. cbn. intros x Hx. apply AG68. clear -Hx. lia. }
      assert (BF8 : rw_cells bsegs m8 (SSo + 16 + 16 * bFv) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (fstv mod kStoreBlockFrames))]).
      { eapply (rw_cells_agree bsegs); [| exact BF6]. unfold SSo. cbn. intros x Hx. apply AG68. right. unfold kStoreBlockBytes. clear -Hx RH' FSR' LO LOC' CEILB. lia. }
      assert (MX8 : rw_cells bsegs m8 (SSo + 28 + 16 * bFv) [C4 (Z_to_bv 64 1)]).
      { eapply (rw_cells_agree bsegs); [| exact MX6]. unfold SSo. cbn. intros x Hx. apply AG68. right. unfold kStoreBlockBytes. clear -Hx RH' FSR' LO LOC' CEILB. lia. }
      replace (usp - 256) with (usp - 224 - 32) in SK8 |- * by (clear; lia).
      eapply (rzA_seg_cfg bsegs (aSc (sA T2 s)) (aNc (sA T2 s)) (aEBc (sA T2 s)) (PP (sA T2 s) mo8));
        [| split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK9)| intros x Hx; exact Hx]|].
      { eapply (gc_B (PP (sA T2 s) mo8));
          [ intros y k Hy Hk; rewrite <- EPOL; eapply (pol_img' E0 FSB0 HR0 (sA T2 s) mo8 AK9 WE (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK9) ENV0); [clear -Hy; lia| exact Hk]
          | exact SK8| exact LOC'| clear -LO; lia| clear -UA A47 LEN; lia| exact MI8| exact FR8| exact BF8| exact MX8| exact FSR'| clear -SCM; unfold kStoreBlockFrames in *; lia|].
        intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T2 s) mo8 AK9 WE ENV0); [exact (Z.le_trans _ _ _ LOC' Hy)|]. clear -Hk UA A47 LEN. lia. }
      intros ms9 mo9 POST9 AG9 KP9.
      destruct POST9 as (m9 & -> & MU9 & WM9 & MI9 & SK9 & BF9 & MX9).
      replace (ret_pc (Z_to_bv 64 465324)) with (Z_to_bv 64 465324) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK9 AG9 (proj1 KP9)) as ATK10.
      pose proof (magree_frame _ _ AG9) as (Qfds9 & Qvm9 & Qlz9 & Qfs9 & Qh9 & Qtid9 & _).
      pose proof (AKern_frame _ _ _ _ Qvm9 Qlz9 AK9) as AK10.
      replace (usp - 224 - 32) with (usp - 256) in SK9 |- * by (clear; lia). replace (usp - 256 + 32) with (usp - 224) by (clear; lia).
      (* [comment removed for export] *)
      eapply (rzA_seg_cfg bsegs (aSc (sA T2 s)) (aNc (sA T2 s)) (aEBc (sA T2 s)) (PP (sA T2 s) mo8)); [| exact KP9|].
      { apply (jmp_back2 (PP (sA T2 s) mo8)). }
      intros ms10 mo10 -> AG10 KP10.
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK10 AG10 (proj1 KP10)) as ATK11.
      pose proof (magree_frame _ _ AG10) as (Qfds10 & Qvm10 & Qlz10 & Qfs10 & Qh10 & Qtid10 & _).
      pose proof (AKern_frame _ _ _ _ Qvm10 Qlz10 AK10) as AK11.
      rewrite RR.
      apply (CONTs (Z_to_bv 64 0x719ac) q0 q1 q2 rZ p1 p2' p3' p4' p5' p6 p7 q3 q4 q5 q6 m9 mo10 (Some rZ) js j1 j2).
      (* [comment removed for export] *)
      assert (DJ2 : blk + kDepotNodeBlockBytes <= rZ \/ rZ + kStoreBlockBytes <= blk).
      { pose proof (grant_apart_inside mo7 r kStoreBlockBytes blk kDepotNodeBlockBytes (node_block_inside T1 mo7 blk AK7 INblk) RF ltac:(unfold kStoreBlockBytes; clear; lia)
                      ltac:(fold rZ; clear -RCL' CEILB; unfold kStoreBlockBytes; lia)) as X. fold rZ in X.
        unfold kDepotNodeBlockBytes, kStoreBlockBytes in *.
        destruct (Z.lt_ge_cases rZ (blk + 1048576)); [| left; lia]. right.
        destruct (Z.lt_ge_cases blk (rZ + 8388608)); [| lia]. exfalso.
        destruct (Z.lt_ge_cases blk rZ); [apply (X rZ); clear -H H0 H1 PL1; lia| apply (X blk); clear -H H0 H1; lia]. }
      assert (DJS : forall b', In b' SBL -> forall x, b' <= x < b' + kStoreBlockBytes -> ~ (rZ <= x < rZ + kStoreBlockBytes)).
      { intros b' Hb x Hx. pose proof (grant_apart_inside mo7 r kStoreBlockBytes b' kStoreBlockBytes (store_block_inside T1 mo7 b' AK7 ltac:(rewrite ESBL1; exact Hb)) RF
                      ltac:(unfold kStoreBlockBytes; clear; lia) ltac:(fold rZ; clear -RCL' CEILB; unfold kStoreBlockBytes; lia) x Hx) as X. fold rZ in X. exact X. }
      assert (AG89 : forall z, 0 <= z < 2^64 -> (z < SSo + 16 + 16 * bFv \/ SSo + 24 + 16 * bFv <= z) -> (z < SSo + 28 + 16 * bFv \/ SSo + 32 + 16 * bFv <= z) -> m9 (wa z) = m8 (wa z)).
      { intros z Hz H1 H2. apply MU9. rewrite wa_unsigned by exact Hz. cbn. clear -H1 H2. lia. }
      (* [comment removed for export] *)
      assert (AGfr : forall z, usp - 224 <= z < usp -> (z < usp - 208 \/ usp - 200 <= z) -> m9 (wa z) = m4 (wa z)).
      { intros z Hz H1. unfold SSo in *. rewrite AG89 by (clear -Hz USPR' LO LOC' CEILB FSR'; lia). rewrite AG68 by (left; clear -Hz; lia).
        rewrite AG56 by (clear -Hz USPR' LO LOC' CEILB FSR'; lia). apply AG45; clear -Hz H1 USPR' LO LOC' CEILB; lia. }
      (* [comment removed for export] *)
      assert (AGst : forall z, 0 <= z < 0x603000 -> (z < SSo + 8 \/ SSo + 16 <= z) -> (z < SSo + 16 + 16 * bFv \/ SSo + 24 + 16 * bFv <= z) ->
                               (z < SSo + 28 + 16 * bFv \/ SSo + 32 + 16 * bFv <= z) -> m9 (wa z) = m4 (wa z)).
      { intros z Hz H1 H2 H3. unfold SSo in *.
        rewrite AG89 by (clear -Hz H1 H2 H3 LO LOC' CEILB FSR'; lia). rewrite AG68 by (right; unfold kStoreBlockBytes; clear -Hz RH' LO LOC' CEILB; lia).
        rewrite AG56 by (clear -Hz H1 H2 H3 LO LOC' CEILB FSR'; lia). apply AGlo5. clear -Hz LO LOC' CEILB; lia. }
      pose proof (gapR_sg (Some rZ) T1) as QR. pose proof (gapP_sg (Some rZ) T1) as QP. pose proof (gapD_sg (Some rZ) T1) as QD. fold T2 in QR, QP, QD.
      cbn [opt_list] in QD. replace (zlen [rZ]) with 1 in QD by reflexivity.
      assert (TOK11 : RTOKc (C - 1) (C' - ngcost nbx - (kStoreBlockBytes + NMAXA + 4095)) (sA T2 s) mo10).
      { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ (R - 2050) (R' - (kStoreBlockBytes + NMAXA + 4095)) ATK11); cbn [aps_alloc sA aps_set_alloc]; rewrite ?QR, ?QD, ?QP.
        - clear -C1; lia.
        - exact G1.
        - clear -RMS; lia.
        - clear -FIT; lia.
        - assert (NGB : 0 <= ngcost nbx <= kDepotNodeBlockBytes + NMAXA + 4095) by (clear; destruct nbx; cbn [ngcost]; unfold kDepotNodeBlockBytes, NMAXA; lia).
          pose proof CSL as X. unfold DSLACK, kStoreBlockBytes, kDepotNodeBlockBytes, NMAXA in NGB, X, HCR' |- *. clear -HCR' X NGB; lia. }
      unfold spost. cbv zeta. cbn [opt_list opt_iv sgcost]. fold T2.
      split; [exact PL|]. split; [exact AL|]. split; [exact NTH|]. split; [exact KBL|]. split; [exact BRn|].
      split; [rewrite BFE; unfold zlen; rewrite length_app; cbn [length]; clear; lia|].
      split. { unfold nthz. rewrite BFE. unfold zlen. rewrite length_app. cbn [length].
               rewrite (proj2 (Z.leb_le _ _)) by (clear; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (clear; lia). cbn [andb]. rewrite Nat2Z.id. apply nth_middle. }
      split; [exact RPL|]. split; [exact RA|].
      split; [unfold store_blocks; rewrite F4; unfold SBL, store_blocks; rewrite <- (proj1 (proj2 (proj2 (proj2 (nd_fields nbx))))); reflexivity|].
      split; [unfold node_blocks; rewrite F10; exact NBE|].
      split. { unfold WC, W4 in *.
               eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_trans; [eapply munch_weaken; [| exact MU6]|
                 eapply munch_trans; [eapply munch_weaken; [| exact MU8]| eapply munch_weaken; [| exact MU9]]]]];
                 intros y Hy; unfold WB, BF_depot7.BI, BF_depot3.SS, SSo in *; cbn [opt_iv app] in Hy |- *.
               - destruct nbx; cbn [app] in Hy |- *; clear -Hy FRB' B0nn; cbn in Hy |- *; lia.
               - destruct nbx; cbn [app] in Hy |- *; clear -Hy; cbn in Hy |- *; lia.
               - destruct nbx; cbn [app] in Hy |- *; clear -Hy FSR'; cbn in Hy |- *; lia.
               - destruct nbx; cbn [app] in Hy |- *; clear -Hy; cbn in Hy |- *; unfold kStoreBlockBytes in *; lia.
               - destruct nbx; cbn [app] in Hy |- *; clear -Hy FSR'; cbn in Hy |- *; lia. }
      split; [exact (wmono_trans _ _ _ _ WM4 (wmono_trans _ _ _ _ WM5 (wmono_trans _ _ _ _ WM6 (wmono_trans _ _ _ _ WM8 WM9))))|].
      split; [exact MI9|]. split; [exact SK9|].
      split. { eapply (rw_cells_agree bsegs); [| exact FR4]. unfold put_frame. cbn. intros x Hx. apply AGfr; clear -Hx USPR' LO LOC' CEILB; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact SF4]. unfold BF_depot7.store_frame. cbn. intros x Hx. apply AGfr; clear -Hx USPR' LO LOC' CEILB; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact STF5]. unfold BF_depot7.Store_frame, SSo in *. cbn. intros x Hx.
               rewrite AG89 by (clear -Hx USPR' LO LOC' CEILB FSR'; lia). rewrite AG68 by (left; clear -Hx; lia). apply AG56; clear -Hx USPR' LO LOC' CEILB FSR'; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact AFR4]. unfold BF_depot7.Alloc_frame. cbn. intros x Hx. apply AGfr; clear -Hx USPR' LO LOC' CEILB; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact NODE4]. rewrite ENA. cbn. intros x Hx. unfold SSo in *.
               rewrite AG89 by (clear -Hx PL1 PL2 NMR LO LOC' CEILB FSR'; lia).
               rewrite AG68 by (right; split; [clear -Hx PL1 PL2 NMR LO LOC' CEILB; lia| unfold kDepotNodeBlockBytes, kStoreBlockBytes in *; clear -Hx DJ2 NMR; lia]).
               rewrite AG56 by (clear -Hx PL1 PL2 NMR LO LOC' CEILB FSR'; lia). apply AGlo5. clear -Hx PL1 PL2 NMR LO LOC' CEILB; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact TBA4]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx BKR FSR'; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact NUQ4]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx FSR'; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact TLM4]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx FSR'; lia. }
      split. { eapply (rw_cells_agree bsegs); [| exact MAP4]. cbn. intros x Hx. apply AGst; unfold SSo, kNodesMap1 in *; clear -Hx KB FSR'; lia. }
      split; [exact (wr_at_transport bsegs _ _ _ _ WR4 (wmono_trans _ _ _ _ WM5 (wmono_trans _ _ _ _ WM6 (wmono_trans _ _ _ _ WM8 WM9))))|].
      split. { eapply (rw_cells_agree bsegs); [| exact SS4]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx FSR'; lia. }
      split. { exists al'. eapply (rw_cells_agree bsegs); [| exact AL6]. unfold SSo in *. cbn. intros x Hx.
               rewrite AG89 by (clear -Hx LO LOC' CEILB FSR'; lia). apply AG68. right. unfold kStoreBlockBytes. clear -Hx RH' LO LOC' CEILB; lia. }
      split. { intros k Hk NEk. pose proof (BLK4 k Hk) as [B1 B2]. unfold storedC in B1. rewrite (proj2 (Z.eqb_neq _ _) NEk) in B1. unfold kStoreBlockCount in Hk.
               assert (NZK : nthz (SBL ++ [rZ]) k = nthz SBL k) by (apply nthz_app_other; rewrite <- BFE; exact NEk).
               rewrite NZK. split.
               - eapply (rw_cells_agree bsegs); [| exact B1]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx Hk NEk FSR'; lia.
               - eapply (rw_cells_agree bsegs); [| exact B2]. cbn. intros x Hx. apply AGst; unfold SSo; clear -Hx Hk NEk FSR'; lia. }
      split; [rewrite <- RR; unfold SSo in BF9; exact BF9|].
      split; [unfold SSo in MX9; exact MX9|].
      split. { exists (repeat zb0 (Z.to_nat kStoreBlockBytes)). split; [| rewrite repeat_length, Z2Nat.id by (unfold kStoreBlockBytes; clear; lia); reflexivity].
               eapply u8arr_agree; [| exact (rw_CB_u8arr _ _ _ _ ZN8 (repeat_length _ _))]. intros x Hx. rewrite repeat_length, Z2Nat.id in Hx by (unfold kStoreBlockBytes; clear; lia).
               apply AG89; unfold SSo; clear -Hx RH' RCL' CEILB FSR'; unfold kStoreBlockBytes in *; lia. }
      split. { intros b' Hb _. destruct (D_sbw b' Hb) as (bs & U & L). exists bs. split; [| exact L]. pose proof (SBLR b' Hb) as [Y1 Y2]. eapply u8arr_agree; [| exact U]. intros x Hx. rewrite L in Hx.
               unfold SSo in *. rewrite AG89 by (clear -Hx Y1 Y2 CEILB FSR'; unfold kStoreBlockBytes in *; lia).
               rewrite AG68 by (right; split; [clear -Hx Y1 Y2 LO LOC' CEILB; unfold kStoreBlockBytes in *; lia| pose proof (DJS b' Hb x Hx) as X; clear -X; unfold kStoreBlockBytes in *; lia]).
               rewrite AG56 by (clear -Hx Y1 Y2 LO LOC' CEILB FSR'; unfold kStoreBlockBytes in *; lia). rewrite AGlo5 by (clear -Hx Y1 Y2 LO LOC' CEILB; unfold kStoreBlockBytes in *; lia).
               apply (AG04s b'); [exact Hb| exact Hx]. }
      pose proof (anon_nr_io mo7 rZ kStoreBlockBytes) as (Xfs & Xfds & Xtid).
      split; [rewrite Qfs10, Qfs9, Qfs8, Xfs, Qfs7, Qfs6, Qfs5; exact Qfs4|].
      split; [rewrite Qfds10, Qfds9, Qfds8, Xfds, Qfds7, Qfds6, Qfds5; exact Qfds4|].
      split; [rewrite Qtid10, Qtid9, Qtid8, Xtid, Qtid7, Qtid6, Qtid5; exact Qtid4|].
      split; [exact AK11|]. split; [exact TOK11|].
      split; [split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ ATK11)| intros x Hx; exact Hx]|].
      split; [reflexivity|]. split; [unfold zlen in BFz; clear -BFz; lia|]. split; [clear -BFz; lia|]. split; [exact GV1| exact GV2].
Qed.
Lemma store_stage : forall (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (m2 : mem) (mo2 : Model)
    (rax x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 : word),
  npost j8 wl nbx blk m2 mo2 ->
  (forall (x1 x5 x6 x7 : word) (sbF : Z) (q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (m3 : mem) (mo3 : Model) (sbx : option Z) (js : list byte) (j1 j2 : word),
     spost j8 wl nbx blk sbx sbF js j1 j2 m3 mo3 ->
     realizes_cfg acfg bsegs (mkCfg (S_se x1 x5 x6 x7 sbF q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3) mo3) K) ->
  realizes_cfg acfg bsegs (mkCfg (S_sa rax blk x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 m2) mo2) K.
Proof.
  intros until z6. intros NP CONTs.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. unfold K_DEPOT in LO.
  pose proof KB0 as KB. pose proof HN as (HN0 & HN1 & HN2). pose proof FRF as (FR0 & FR32 & FRB). pose proof FRLE as FRLE'.
  pose proof (Z.mod_pos_bound h kTabSize ltac:(unfold kTabSize; clear; lia)) as BKR. change (h mod kTabSize) with bkt in BKR. unfold kTabSize in BKR.
  destruct NP as (PL & AL & NTH & KBL & NBE & MU2 & WM2 & MI2 & SK2 & FR2 & TBA2 & NUQ2 & TLM2 & MAP2 & WR2 & Qfs2 & Qfds2 & Qtid2 & AK2 & TOK2 & KP2 & BR).
  set (T1 := nd_st nbx) in *.
  pose proof PL as (PL1 & PL2 & PL3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in PL1, PL2, PL3.
  assert (BLKR : placed blk kDepotNodeBlockBytes /\ blk mod 16 = 0) by (split; [exact PL| clear -AL; Z.div_mod_to_equations; lia]).
  pose proof (Z.mod_pos_bound (N + 1) kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; clear; lia)) as NMR. unfold kDepotNodesPerBlock in NMR.
  assert (ENA : BF_depot7.NA N blk = blk + 16 * ((N + 1) mod 65536)) by reflexivity.
  (* [comment removed for export] *)
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK2) as (R2 & R2' & ATK2 & _).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK2) as EV2. pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK2) as KV2. cbn [aps_alloc sA aps_set_alloc] in KV2.
  assert (PSTK1 : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> PP (sA T1 s) mo2 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T1 s) mo2 AK2 WE ENV0); clear -Hy Hk LOC' A47; lia. }
  assert (PIMG1 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA T1 s) mo2 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA T1 s) mo2 AK2 WE EV2 ENV0); [clear -Hy; lia| exact Hk]. }
  assert (PNA1 : forall y k, BF_depot7.NA N blk <= y -> y + Z.of_nat k <= BF_depot7.NA N blk + 16 -> PP (sA T1 s) mo2 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_node_block' E0 FSB0 HR0 (sA T1 s) mo2 AK2 ENV0 blk).
    - cbn [aps_alloc sA aps_set_alloc]. change (In blk (node_blocks E0 T1)). rewrite NBE, <- NTH. unfold nthz.
      rewrite (proj2 (Z.leb_le 0 kb)) by (clear -KB; lia). rewrite (proj2 (Z.ltb_lt _ _) KBL). cbn [andb]. apply nth_In. unfold zlen in KBL. clear -KBL KB. lia.
    - rewrite ENA in Hy. clear -Hy NMR. lia.
    - rewrite ENA in Hk. unfold kDepotNodeBlockBytes. clear -Hk NMR. lia. }
  assert (PSB1 : forall b' y k, In b' SBL -> b' <= y -> y + Z.of_nat k <= b' + kStoreBlockBytes -> PP (sA T1 s) mo2 (Z_to_bv 64 y, k)).
  { intros b' y k Hb Hy Hk. rewrite <- EPOL. eapply (pol_store_block' E0 FSB0 HR0 (sA T1 s) mo2 AK2 ENV0 b'); [| exact Hy| exact Hk].
    cbn [aps_alloc sA aps_set_alloc]. pose proof (nd_fields nbx) as (_ & _ & _ & F4 & _). fold T1 in F4. rewrite F4. exact Hb. }
  (* [comment removed for export] *)
  destruct (wr_at_node m2 (BF_depot7.NA N blk) ltac:(eapply (BF_lkit.wr_at_sub bsegs); [exact WR2| rewrite ENA; clear -NMR; lia| rewrite ENA; unfold kDepotNodeBlockBytes; clear -NMR; lia]))
    as (j0 & j1 & j2 & NEWN).
  (* [comment removed for export] *)
  unfold S_sa.
  eapply (rzA_seg_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo2)); [| exact KP2|].
  { eapply (put_sa (PP (sA T1 s) mo2) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (A + 8 * zlen ws) A len ws HS N blk);
      [ exact LOC'| clear -LO; lia| clear -UA LEN; lia| exact A47| unfold zlen in LEN; exact LEN| unfold zlen in LWS; exact LWS| unfold zlen; clear -UA; lia
      | clear -HN0 HN1; lia| exact BLKR| exact PSTK1| exact PNA1| exact SK2| exact MI2| exact FR2| exact NEWN]. }
  intros ms3 mo3 POST3 AG3 KP3.
  destruct POST3 as (x5 & x6 & x7 & x14 & x16 & x17 & x28 & x29 & x30 & x31 & js & m3 & -> & MU3 & WM3 & MI3 & SK3 & FR3 & SF3 & STF3 & AFR3 & NODE3).
  pose proof (magree_frame _ _ AG3) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & Qh3 & Qtid3 & _).
  pose proof (AKern_frame _ _ _ _ Qvm3 Qlz3 AK2) as AK3.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK2 AG3 (proj1 KP3)) as TOK3.
  (* [comment removed for export] *)
  assert (AG02 : forall z, 0xa5000 <= z < 0x603000 -> (z < 1639576 + 4 * bkt \/ 1639576 + 4 * bkt + 4 <= z) -> (z < 5833880 \/ 5833884 <= z) ->
                           (z < 5833888 \/ 5833892 <= z) -> (z < 5833896 + 8 * kb \/ 5833904 + 8 * kb <= z) -> m2 (wa z) = m (wa z)).
  { intros z Hz H1 H2 H3 H4. apply MU2. rewrite wa_unsigned by (clear -Hz; lia). unfold WB. cbn [outside app opt_iv fst snd].
    destruct nbx as [r|]; [rewrite (proj1 BR)|]; cbn [outside opt_iv app fst snd]; unfold kDepotNodeBlockBytes; clear -Hz H1 H2 H3 H4 LO LOC' CEILB PL1; lia. }
  assert (AG23 : forall z, 0 <= z < usp - 224 -> (z < BF_depot7.NA N blk \/ BF_depot7.NA N blk + 8 <= z) -> m3 (wa z) = m2 (wa z)).
  { intros z Hz H1. apply MU3. rewrite wa_unsigned by (clear -Hz USPR' LO LOC' CEILB; lia). cbn. clear -Hz H1. lia. }
  assert (AGS3 : forall z, 1574024 <= z < 1574024 + 16 + 16 * 4096 -> m3 (wa z) = m (wa z)).
  { intros z Hz. rewrite AG23 by (rewrite ?ENA; clear -Hz LO LOC' CEILB PL1 NMR; lia). apply AG02; clear -Hz BKR KB; unfold kNodesMap1 in KB; lia. }
  assert (SS3 : rw_cells bsegs m3 BF_depot3.SS [C8 (Z_to_bv 64 fr)]).
  { eapply (rw_cells_agree bsegs); [| exact D_fr]. unfold BF_depot3.SS. cbn. intros x Hx. apply AGS3. clear -Hx. lia. }
  assert (BLK3 : forall k, 0 <= k < kStoreBlockCount ->
            rw_cells bsegs m3 (BF_depot7.BI k) [C8 (Z_to_bv 64 (nthz SBL k)); C4 (Z_to_bv 64 (stored_of fr k))] /\ rw_cells bsegs m3 (1574024 + 28 + 16 * k) [C4 (Z_to_bv 64 0)]).
  { intros k Hk. unfold kStoreBlockCount in Hk. split.
    - eapply (rw_cells_agree bsegs); [| exact (proj1 (D_blk k Hk))]. unfold BF_depot7.BI, BF_depot3.SS. cbn. intros x Hx. apply AGS3. clear -Hx Hk. lia.
    - eapply (rw_cells_agree bsegs); [| exact (M_blk k Hk)]. cbn. intros x Hx. apply AGS3. clear -Hx Hk. lia. }
  (* [comment removed for export] *)
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK3) as (R3 & R3' & ATK3 & _).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3) as EV3.
  assert (PSTK3 : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> PP (sA T1 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T1 s) mo3 AK3 WE ENV0); clear -Hy Hk LOC' A47; lia. }
  assert (PIMG3 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA T1 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA T1 s) mo3 AK3 WE EV3 ENV0); [clear -Hy; lia| exact Hk]. }
  pose proof FRB as FRB'. unfold kStoreBlockCount in FRB'.
  assert (B0nn : 0 <= BF_depot7.b fr) by (unfold BF_depot7.b; apply Z.div_pos; [exact FR0| unfold kStoreBlockFrames; clear; lia]).
  (* [comment removed for export] *)
  assert (AG23s : forall z, 0 <= z < 0x603000 -> m3 (wa z) = m2 (wa z)).
  { intros z Hz. apply AG23; [clear -Hz LO LOC' CEILB; lia| rewrite ENA; clear -Hz PL1 NMR; lia]. }
  destruct (BF_depot7.straddles len fr) eqn:STR.
  - (* [comment removed for export] *)
    pose proof (straddles_true len ws N fr ltac:(unfold zlen in LEN; exact LEN) ltac:(unfold zlen in LWS; exact LWS) FR0 STR) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    pose proof SF3 as SF3'. unfold BF_depot7.store_frame in SF3'.
    change ([CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x73f98)]) with ([CB 8 js] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x73f98)]) in SF3'.
    apply rw_cells_app_split in SF3'. destruct SF3' as [SFa SF3']. apply rw_cells_app_split in SF3'. destruct SF3' as [PK3 SFc].
    cbn [cells_size csize Nat.add app] in PK3, SFc. replace (usp - 144 + Z.of_nat 8) with (usp - 136) in PK3 by (clear; lia).
    replace (usp - 144 + Z.of_nat 8 + Z.of_nat 8) with (usp - 128) in SFc by (clear; lia).
    eapply (rzA_seg_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo3)); [| split; [exact (proj1 KP3)| intros x Hx; exact Hx]|].
    { eapply (put_sc (PP (sA T1 s) mo3) sp gp tp s10 s11 F fc lo (A + 8 * zlen ws) A len ws HS N blk fr);
        [ exact LOC'| clear -LO; lia| clear -UA LEN; lia| exact A47| unfold zlen in LEN; exact LEN| unfold zlen in LWS; exact LWS| unfold zlen; clear -UA; lia
        | exact FR0| exact FR32| exact FRB| exact PSTK3| exact PIMG3| exact STR| exact MI3| exact SS3
        | exact (proj1 (BLK3 (BF_depot7.b fr) ltac:(clear -B0nn FRB'; unfold kStoreBlockCount; lia)))
        | exact (proj1 (BLK3 (BF_depot7.b fr + 1) ltac:(clear -B0nn FRB'; unfold kStoreBlockCount; lia)))
        | exact PK3]. }
    intros ms4 mo4 POST4 AG4 KP4.
    destruct POST4 as (x6' & x7' & x14' & x16' & x17' & x28' & m4 & -> & MU4 & WM4 & MI4 & SS4 & BA4 & BB4 & PK4).
    pose proof (magree_frame _ _ AG4) as (Qfds4 & Qvm4 & Qlz4 & Qfs4 & Qh4 & Qtid4 & _).
    pose proof (AKern_frame _ _ _ _ Qvm4 Qlz4 AK3) as AK4.
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK3 AG4 (proj1 KP4)) as TOK4.
    assert (ER : BF_depot7.alloc_regs2 sp gp tp s10 s11 len ws HS N (Z_to_bv 64 464876) (Z_to_bv 64 (BF_depot7.b fr + 1)) x6' x7' (Z_to_bv 64 len) x14' x16' x17' x28' x29 x30 x31 (fr + BF_depot7.count len)
               = BF_depot7.alloc_regs2 sp gp tp s10 s11 len ws HS N (Z_to_bv 64 0x717ec) (Z_to_bv 64 bFv) x6' x7' (Z_to_bv 64 len) x14' x16' x17' x28' x29 x30 x31 fstv) by (rewrite D2, D3; reflexivity).
    rewrite ER. clear ER.
    assert (AG34 : forall z, 0 <= z < 2^64 -> (z < 1574024 \/ 1574032 <= z) -> (z < BF_depot7.BI (BF_depot7.b fr) + 8 \/ BF_depot7.BI (BF_depot7.b fr) + 12 <= z) ->
                             (z < BF_depot7.BI (BF_depot7.b fr + 1) + 8 \/ BF_depot7.BI (BF_depot7.b fr + 1) + 12 <= z) -> (z < usp - 136 \/ usp - 128 <= z) -> m4 (wa z) = m3 (wa z)).
    { intros z Hz H1 H2 H3 H4. apply MU4. rewrite wa_unsigned by exact Hz. unfold BF_depot7.BI, BF_depot3.SS in *. cbn. clear -H1 H2 H3 H4. lia. }
    assert (AG24t : forall z, 1639576 <= z < 0x603000 -> m4 (wa z) = m2 (wa z)).
    { intros z Hz. rewrite AG34 by (unfold BF_depot7.BI, BF_depot3.SS; clear -Hz FRB' B0nn LO LOC' CEILB; lia). apply AG23s. clear -Hz; lia. }
    apply (sd_stage j8 wl nbx blk js j1 j2 m4 mo4 x6' x7' x14' x16' x17' x28' x29 x30 x31);
      [| exact PL| exact AL| exact NTH| exact KBL| exact NBE
       | eapply (rw_cells_agree bsegs); [| exact TBA2]; cbn; intros x Hx; apply AG24t; clear -Hx BKR; lia
       | eapply (rw_cells_agree bsegs); [| exact NUQ2]; cbn; intros x Hx; apply AG24t; clear -Hx; lia
       | eapply (rw_cells_agree bsegs); [| exact TLM2]; cbn; intros x Hx; apply AG24t; clear -Hx; lia
       | eapply (rw_cells_agree bsegs); [| exact MAP2]; cbn; intros x Hx; apply AG24t; clear -Hx KB; unfold kNodesMap1 in *; lia
       | eapply wr_at_transport; [exact WR2| exact (wmono_trans _ _ _ _ WM3 WM4)]
       | exact BR| exact CONTs].
    (* [comment removed for export] *)
    pose proof storedC_facts as (SC1 & SC2 & SC3 & SCM & SCB). destruct (SC3 STR) as [SB0 SB1].
    assert (AGhi : forall z, usp - 128 <= z < 2^64 -> m4 (wa z) = m3 (wa z)).
    { intros z Hz. apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hz FRB' B0nn LO LOC' CEILB USPR'; lia. }
    assert (AGmid : forall z, 0x603000 <= z < usp - 136 -> m4 (wa z) = m3 (wa z)).
    { intros z Hz. apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hz FRB' B0nn LO LOC' CEILB USPR'; lia. }
    unfold qpost.
    split. { unfold W4. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]];
             intros y Hy; unfold WB, BF_depot7.BI, BF_depot3.SS in *; rewrite ?ENA in Hy |- *; cbn [opt_iv app] in Hy |- *.
             all: destruct nbx; cbn [app] in Hy |- *; cbn in Hy |- *; clear -Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 WM4))|].
    split; [exact MI4|].
    split; [eapply (stk_transport_disjoint bsegs); [exact SK3| exact MU4| exact WM4| unfold BF_depot7.BI, BF_depot3.SS; cbn; clear -FRB' B0nn LO LOC' CEILB; lia]|].
    split. { eapply (rw_cells_agree bsegs); [| exact FR3]. unfold put_frame. cbn. intros x Hx. apply AGhi; clear -Hx USPR'; lia. }
    split. { unfold BF_depot7.store_frame. rewrite D4.
             change ([CB 8 js; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x73f98)]) with ([CB 8 js] ++ [C8 (Z_to_bv 64 1)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x73f98)]).
             apply rw_cells_app_join; [| apply rw_cells_app_join]; cbn [cells_size csize Nat.add app].
             - eapply (rw_cells_agree bsegs); [| exact SFa]. cbn. intros x Hx. apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hx FRB' B0nn LO LOC' CEILB USPR'; lia.
             - replace (usp - 144 + Z.of_nat 8) with (usp - 136) by (clear; lia). exact PK4.
             - replace (usp - 144 + Z.of_nat 8 + Z.of_nat 8) with (usp - 128) by (clear; lia). eapply (rw_cells_agree bsegs); [| exact SFc]. cbn. intros x Hx. apply AGhi; clear -Hx USPR'; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact STF3]. unfold BF_depot7.Store_frame. cbn. intros x Hx. apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hx FRB' B0nn LO LOC' CEILB USPR'; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact AFR3]. unfold BF_depot7.Alloc_frame. cbn. intros x Hx. apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hx FRB' B0nn LO LOC' CEILB USPR'; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact NODE3]. cbn. intros x Hx. rewrite ENA in Hx. apply AGmid; clear -Hx PL1 PL2 NMR LO LOC' CEILB; lia. }
    split. { unfold frE. rewrite D3. unfold BF_depot3.SS in SS4. exact SS4. }
    split. { intros k Hk. unfold kStoreBlockCount in Hk. split.
             - destruct (Z.eq_dec k (BF_depot7.b fr)) as [->|NE0]; [rewrite SB0; unfold BF_depot7.BI, BF_depot3.SS in BA4; exact BA4|].
               destruct (Z.eq_dec k (BF_depot7.b fr + 1)) as [->|NE1]; [rewrite SB1; unfold BF_depot7.BI, BF_depot3.SS in BB4; exact BB4|].
               rewrite (SC1 k ltac:(clear -Hk; lia) NE0 NE1).
               eapply (rw_cells_agree bsegs); [| exact (proj1 (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk)))]. unfold BF_depot7.BI, BF_depot3.SS. cbn. intros x Hx.
               apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hx Hk NE0 NE1 FRB' B0nn LO LOC' CEILB; lia.
             - eapply (rw_cells_agree bsegs); [| exact (proj2 (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk)))]. cbn. intros x Hx.
               apply AG34; unfold BF_depot7.BI, BF_depot3.SS; clear -Hx Hk FRB' B0nn LO LOC' CEILB; lia. }
    split; [rewrite Qfs4, Qfs3; exact Qfs2|]. split; [rewrite Qfds4, Qfds3; exact Qfds2|]. split; [rewrite Qtid4, Qtid3; exact Qtid2|].
    split; [exact AK4|]. split; [exact TOK4|]. split; [exact (proj1 KP4)| intros x Hx; exact Hx].
  - (* [comment removed for export] *)
    pose proof (straddles_false len ws N fr ltac:(unfold zlen in LEN; exact LEN) FR0 STR) as (D1 & D2 & D3 & D4).
    eapply (rzA_seg_cfg bsegs (aSc (sA T1 s)) (aNc (sA T1 s)) (aEBc (sA T1 s)) (PP (sA T1 s) mo3)); [| split; [exact (proj1 KP3)| intros x Hx; exact Hx]|].
    { eapply (put_sb (PP (sA T1 s) mo3) sp gp tp s10 s11 F fc lo (A + 8 * zlen ws) A len ws HS N blk fr);
        [ exact LOC'| clear -LO; lia| exact A47| unfold zlen in LEN; exact LEN| unfold zlen; clear -UA; lia| exact FR0| exact FR32| exact PIMG3| exact STR| exact MI3| exact SS3]. }
    intros ms4 mo4 POST4 AG4 KP4.
    destruct POST4 as (x14' & x6' & m4 & -> & MU4 & WM4 & MI4 & SS4).
    pose proof (magree_frame _ _ AG4) as (Qfds4 & Qvm4 & Qlz4 & Qfs4 & Qh4 & Qtid4 & _).
    pose proof (AKern_frame _ _ _ _ Qvm4 Qlz4 AK3) as AK4.
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK3 AG4 (proj1 KP4)) as TOK4.
    assert (ER : BF_depot7.alloc_regs2 sp gp tp s10 s11 len ws HS N (Z_to_bv 64 464876) (Z_to_bv 64 (BF_depot7.b fr)) x6' x7 (Z_to_bv 64 len) x14' x16 x17 x28 x29 x30 x31 fr
               = BF_depot7.alloc_regs2 sp gp tp s10 s11 len ws HS N (Z_to_bv 64 0x717ec) (Z_to_bv 64 bFv) x6' x7 (Z_to_bv 64 len) x14' x16 x17 x28 x29 x30 x31 fstv) by (rewrite D2, D3; reflexivity).
    rewrite ER. clear ER.
    assert (AG34 : forall z, 0 <= z < 2^64 -> (z < 1574024 \/ 1574032 <= z) -> m4 (wa z) = m3 (wa z)).
    { intros z Hz H1. apply MU4. rewrite wa_unsigned by exact Hz. unfold BF_depot3.SS. cbn. clear -H1. lia. }
    assert (AG24t : forall z, 1639576 <= z < 0x603000 -> m4 (wa z) = m2 (wa z)).
    { intros z Hz. rewrite AG34 by (clear -Hz; lia). apply AG23s. clear -Hz; lia. }
    assert (AGx : forall z, 1574032 <= z < 2^64 -> m4 (wa z) = m3 (wa z)) by (intros z Hz; apply AG34; clear -Hz; lia).
    apply (sd_stage j8 wl nbx blk js j1 j2 m4 mo4 x6' x7 x14' x16 x17 x28 x29 x30 x31);
      [| exact PL| exact AL| exact NTH| exact KBL| exact NBE
       | eapply (rw_cells_agree bsegs); [| exact TBA2]; cbn; intros x Hx; apply AG24t; clear -Hx BKR; lia
       | eapply (rw_cells_agree bsegs); [| exact NUQ2]; cbn; intros x Hx; apply AG24t; clear -Hx; lia
       | eapply (rw_cells_agree bsegs); [| exact TLM2]; cbn; intros x Hx; apply AG24t; clear -Hx; lia
       | eapply (rw_cells_agree bsegs); [| exact MAP2]; cbn; intros x Hx; apply AG24t; clear -Hx KB; unfold kNodesMap1 in *; lia
       | eapply wr_at_transport; [exact WR2| exact (wmono_trans _ _ _ _ WM3 WM4)]
       | exact BR| exact CONTs].
    pose proof storedC_facts as (SC1 & SC2 & SC3 & SCM & SCB). destruct (SC2 STR) as [SB0 SB1].
    unfold qpost.
    split. { unfold W4. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]];
             intros y Hy; unfold WB, BF_depot7.BI, BF_depot3.SS in *; rewrite ?ENA in Hy |- *; cbn [opt_iv app] in Hy |- *.
             all: destruct nbx; cbn [app] in Hy |- *; cbn in Hy |- *; clear -Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 WM4))|].
    split; [exact MI4|].
    split; [eapply (stk_transport_disjoint bsegs); [exact SK3| exact MU4| exact WM4| unfold BF_depot3.SS; cbn; clear -LO LOC' CEILB; lia]|].
    split. { eapply (rw_cells_agree bsegs); [| exact FR3]. unfold put_frame. cbn. intros x Hx. apply AGx; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { rewrite D4. eapply (rw_cells_agree bsegs); [| exact SF3]. unfold BF_depot7.store_frame. cbn. intros x Hx. apply AGx; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact STF3]. unfold BF_depot7.Store_frame. cbn. intros x Hx. apply AGx; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact AFR3]. unfold BF_depot7.Alloc_frame. cbn. intros x Hx. apply AGx; clear -Hx USPR' LO LOC' CEILB; lia. }
    split. { eapply (rw_cells_agree bsegs); [| exact NODE3]. cbn. intros x Hx. rewrite ENA in Hx. apply AGx; clear -Hx PL1 PL2 NMR CEILB; lia. }
    split. { unfold frE. rewrite D3. unfold BF_depot3.SS in SS4. exact SS4. }
    split. { intros k Hk. unfold kStoreBlockCount in Hk.
             assert (SCk : storedC k = stored_of fr k).
             { destruct (Z.eq_dec k (BF_depot7.b fr)) as [->|NE0]; [exact SB0|]. destruct (Z.eq_dec k (BF_depot7.b fr + 1)) as [->|NE1]; [exact SB1|]. exact (SC1 k ltac:(clear -Hk; lia) NE0 NE1). }
             rewrite SCk. split.
             - eapply (rw_cells_agree bsegs); [| exact (proj1 (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk)))]. unfold BF_depot7.BI, BF_depot3.SS. cbn. intros x Hx. apply AGx; clear -Hx Hk; lia.
             - eapply (rw_cells_agree bsegs); [| exact (proj2 (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk)))]. cbn. intros x Hx. apply AGx; clear -Hx Hk; lia. }
    split; [rewrite Qfs4, Qfs3; exact Qfs2|]. split; [rewrite Qfds4, Qfds3; exact Qfds2|]. split; [rewrite Qtid4, Qtid3; exact Qtid2|].
    split; [exact AK4|]. split; [exact TOK4|]. split; [exact (proj1 KP4)| intros x Hx; exact Hx].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opt_ans (x : option Z) : list aans := match x with Some r => [AnsOk r] | None => [] end.
Definition MARKf (a1 : astate) : gmap Z Z -> gmap Z Z :=
  fun st => <[ (as_frames a1 + countN - 1) / kStoreBlockFrames :=
                 (match st !! ((as_frames a1 + countN - 1) / kStoreBlockFrames) with Some v => v | None => 0 end) + (countN - (kStoreBlockFrames - as_frames a1 mod kStoreBlockFrames)) ]>
            (<[ as_frames a1 / kStoreBlockFrames :=
                 (match st !! (as_frames a1 / kStoreBlockFrames) with Some v => v | None => 0 end) + (kStoreBlockFrames - as_frames a1 mod kStoreBlockFrames) ]> st).
Definition once2 (str : bool) (a1 : astate) : astate :=
  if str then st_bump countN (upd_store_stored (MARKf a1) (st_bump countN a1)) else st_bump countN a1.
Definition st_final (nbx : option Z) (str : bool) (sbx : option Z) : astate :=
  upd_keys (fun ks => ks ++ [key]) (fun f => f) (sg_st sbx (once2 str (nd_st nbx))).

Lemma arun_aget : forall sX orc, arun 0%nat (aget sX) orc = Some (sX, ONorm sX, [], orc).
Proof. reflexivity. Qed.
Lemma frames_bump : forall c x, as_frames (st_bump c x) = as_frames x + c. Proof. intros c x; destruct x; reflexivity. Qed.
Lemma frames_stored : forall g x, as_frames (upd_store_stored g x) = as_frames x. Proof. intros g x; destruct x; reflexivity. Qed.
Lemma sblocks_bump : forall c x, as_store_blocks (st_bump c x) = as_store_blocks x. Proof. intros c x; destruct x; reflexivity. Qed.
Lemma sblocks_stored : forall g x, as_store_blocks (upd_store_stored g x) = as_store_blocks x. Proof. intros g x; destruct x; reflexivity. Qed.

(* [comment removed for export] *)
Lemma bump_fields : forall c x,
  as_regions (st_bump c x) = as_regions x /\ as_ptr_committed (st_bump c x) = as_ptr_committed x /\ as_sec (st_bump c x) = as_sec x /\ as_residue (st_bump c x) = as_residue x
  /\ as_nprim_ever (st_bump c x) = as_nprim_ever x /\ as_ndepot_ins (st_bump c x) = as_ndepot_ins x /\ as_node_blocks (st_bump c x) = as_node_blocks x
  /\ as_store_blocks (st_bump c x) = as_store_blocks x /\ as_keys (st_bump c x) = as_keys x /\ as_frames (st_bump c x) = as_frames x + c.
Proof. intros c x; destruct x; repeat split; reflexivity. Qed.
Lemma stored_fields : forall g x,
  as_regions (upd_store_stored g x) = as_regions x /\ as_ptr_committed (upd_store_stored g x) = as_ptr_committed x /\ as_sec (upd_store_stored g x) = as_sec x /\ as_residue (upd_store_stored g x) = as_residue x
  /\ as_nprim_ever (upd_store_stored g x) = as_nprim_ever x /\ as_ndepot_ins (upd_store_stored g x) = as_ndepot_ins x /\ as_node_blocks (upd_store_stored g x) = as_node_blocks x
  /\ as_store_blocks (upd_store_stored g x) = as_store_blocks x /\ as_keys (upd_store_stored g x) = as_keys x /\ as_frames (upd_store_stored g x) = as_frames x.
Proof. intros g x; destruct x; repeat split; reflexivity. Qed.
Lemma keys_fields : forall fk x, let y := upd_keys fk (fun f => f) x in
  as_regions y = as_regions x /\ as_ptr_committed y = as_ptr_committed x /\ as_sec y = as_sec x /\ as_residue y = as_residue x
  /\ as_nprim_ever y = as_nprim_ever x /\ as_ndepot_ins y = as_ndepot_ins x /\ as_node_blocks y = as_node_blocks x
  /\ as_store_blocks y = as_store_blocks x /\ as_keys y = fk (as_keys x) /\ as_frames y = as_frames x.
Proof. intros fk x; destruct x; repeat split; reflexivity. Qed.
Lemma once2_fields : forall str x, let y := once2 str x in
  as_regions y = as_regions x /\ as_ptr_committed y = as_ptr_committed x /\ as_sec y = as_sec x /\ as_residue y = as_residue x
  /\ as_nprim_ever y = as_nprim_ever x /\ as_ndepot_ins y = as_ndepot_ins x /\ as_node_blocks y = as_node_blocks x
  /\ as_store_blocks y = as_store_blocks x /\ as_keys y = as_keys x /\ as_frames y = as_frames x + (if str then countN + countN else countN).
Proof.
  intros str x. cbv zeta. unfold once2. destruct str.
  - pose proof (bump_fields countN (upd_store_stored (MARKf x) (st_bump countN x))) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    pose proof (stored_fields (MARKf x) (st_bump countN x)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof (bump_fields countN x) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10, ?D1, ?D2, ?D3, ?D4, ?D5, ?D6, ?D7, ?D8, ?D9, ?D10.
    repeat split; try reflexivity. clear; lia.
  - cbn iota. exact (bump_fields countN x).
Qed.

(* [comment removed for export] *)
Lemma final_fields : forall nbx str sbx, let a' := st_final nbx str sbx in let T2 := sg_st sbx (nd_st nbx) in
     as_regions a' = as_regions T2 /\ as_ptr_committed a' = as_ptr_committed T2 /\ as_sec a' = as_sec T2 /\ as_residue a' = as_residue T2
  /\ as_nprim_ever a' = as_nprim_ever T2 /\ as_ndepot_ins a' = as_ndepot_ins T2 /\ as_node_blocks a' = as_node_blocks T2 /\ as_store_blocks a' = as_store_blocks T2
  /\ as_keys a' = as_keys a ++ [key] /\ as_frames a' = fr + (if str then countN + countN else countN)
  /\ as_ndepot_ins a' = as_ndepot_ins a + 1 /\ as_nprim_ever a' = as_nprim_ever a
  /\ as_node_blocks a' = as_node_blocks a ++ opt_list nbx /\ as_store_blocks a' = as_store_blocks a ++ opt_list sbx
  /\ as_regions a' = as_regions a /\ as_ptr_committed a' = as_ptr_committed a /\ as_sec a' = as_sec a /\ as_residue a' = as_residue a.
Proof.
  intros nbx str sbx. cbv zeta. unfold st_final.
  pose proof (keys_fields (fun ks => ks ++ [key]) (sg_st sbx (once2 str (nd_st nbx)))) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10). cbv zeta in K1, K2, K3, K4, K5, K6, K7, K8, K9, K10.
  pose proof (sg_fields sbx (once2 str (nd_st nbx))) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (once2_fields str (nd_st nbx)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10). cbv zeta in O1, O2, O3, O4, O5, O6, O7, O8, O9, O10.
  pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  pose proof (sg_fields sbx (nd_st nbx)) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).
  rewrite ?K1, ?K2, ?K3, ?K4, ?K5, ?K6, ?K7, ?K8, ?K9, ?K10. rewrite ?G1, ?G2, ?G3, ?G4, ?G5, ?G6, ?G7, ?G8, ?G9, ?G10. rewrite ?O1, ?O2, ?O3, ?O4, ?O5, ?O6, ?O7, ?O8, ?O9, ?O10.
  rewrite ?S1, ?S2, ?S3, ?S4, ?S5, ?S6, ?S7, ?S8, ?S9, ?S10. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10.
  unfold fr. repeat split; try reflexivity; rewrite <- ?app_assoc; reflexivity.
Qed.

Lemma same_fp_final : forall nbx str sbx, same_fp (sg_st sbx (nd_st nbx)) (st_final nbx str sbx).
Proof.
  intros nbx str sbx. pose proof (final_fields nbx str sbx) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
  unfold same_fp. rewrite F3, F2, F4, F7, F8. repeat split; try reflexivity.
  unfold regions_bytes. clear -F1. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold get_region. rewrite F1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arun_miss : forall nbx blk sbx sbF,
  depot_lookup E0 a key = None ->
  nbx_ok nbx blk ->
  match sbx with
  | None => ~ (0 < bFv /\ zlen (as_store_blocks a) < bFv)
  | Some r => r = sbF /\ 0 < bFv /\ zlen (as_store_blocks a) < bFv
            /\ (r mod kPageSize =? 0) && (0 <? r) && (r + kStoreBlockBytes <=? alloc_ceiling) && ranges_free (known_ranges E0 (nd_st nbx)) r kStoreBlockBytes = true
            /\ app_mem_b r kStoreBlockBytes && negb (in_primary (ae_space_beg E0) r) && negb (in_primary (ae_space_beg E0) (r + kStoreBlockBytes - 1)) && (r + kStoreBlockBytes <=? kHighMemEnd + 1) = true
  end ->
  exists f evs, arun f (depot_put E0 key a) (opt_ans nbx ++ opt_ans sbx) = Some (st_final nbx strd sbx, ONorm (N + 1), evs, []).
Proof.
  intros nbx blk sbx sbF DL NBX0 SBRx.
  pose proof HN as (HN0 & HN1 & _). pose proof FRF as (FR0 & FR64 & FRB). pose proof LEN as LEN'. pose proof LWS as LWS'.
  pose proof (nd_fields nbx) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
  assert (Ecnt : zlen key + 1 = countN) by (unfold key; rewrite zlen_bst_key by (clear -LEN'; lia); reflexivity).
  assert (Eb : BF_depot7.b fr = fr / kStoreBlockFrames) by reflexivity. assert (Ec : BF_depot7.count len = len + 1) by reflexivity.
  assert (KNB : known_ranges E0 (upd_ndepot (fun k => k + 1) a) = known_ranges E0 a) by (destruct (aps_alloc s); reflexivity).
  (* [comment removed for export] *)
  assert (SA : exists f evs, arun f (store_alloc E0 countN (nd_st nbx)) (opt_ans sbx) = Some (sg_st sbx (once2 strd (nd_st nbx)), ONorm fstv, evs, [])).
  { unfold store_alloc, once2.
    destruct (BF_depot7.straddles len fr) eqn:STR.
    - pose proof (straddles_true len ws N fr ltac:(unfold zlen in LEN'; exact LEN') ltac:(unfold zlen in LWS'; exact LWS') FR0 STR) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      assert (NE1 : as_frames (nd_st nbx) / kStoreBlockFrames <> (as_frames (nd_st nbx) + countN - 1) / kStoreBlockFrames) by (rewrite F9; unfold fr in *; rewrite <- Eb, D1; clear; lia).
      set (a1' := upd_store_stored (MARKf (nd_st nbx)) (st_bump countN (nd_st nbx))).
      assert (FR1' : as_frames a1' = fr + countN) by (subst a1'; rewrite frames_stored, frames_bump, F9; reflexivity).
      assert (EQ2 : as_frames a1' / kStoreBlockFrames = (as_frames a1' + countN - 1) / kStoreBlockFrames) by (rewrite FR1'; unfold fr in *; rewrite D5, D6; reflexivity).
      assert (SB1' : as_store_blocks a1' = as_store_blocks a) by (subst a1'; rewrite sblocks_stored, sblocks_bump; exact F4).
      assert (BQ : as_frames a1' / kStoreBlockFrames = bFv) by (rewrite FR1', D2; unfold fr in *; rewrite D5; reflexivity).
      destruct sbx as [r2|].
      + destruct SBRx as (_ & B0 & BG & V1 & V2). do 2 eexists.
        eapply arun_abind; [apply arun_store_alloc_once_straddle; exact NE1|]. cbv beta iota. fold (MARKf (nd_st nbx)). fold a1'.
        eapply arun_abind.
        * apply arun_store_alloc_once_grow; [exact EQ2| rewrite BQ; exact B0| rewrite SB1', BQ; exact BG| rewrite known_ranges_bump; subst a1'; rewrite known_ranges_stored, known_ranges_bump; exact V1| exact V2].
        * cbv beta iota. rewrite FR1', D3. apply arun_aret.
      + do 2 eexists.
        eapply arun_abind; [apply arun_store_alloc_once_straddle; exact NE1|]. cbv beta iota. fold (MARKf (nd_st nbx)). fold a1'.
        eapply arun_abind.
        * apply arun_store_alloc_once_fit; [exact EQ2| rewrite SB1', BQ; exact SBRx].
        * cbv beta iota. rewrite FR1', D3. apply arun_aret.
    - pose proof (straddles_false len ws N fr ltac:(unfold zlen in LEN'; exact LEN') FR0 STR) as (D1 & D2 & D3 & D4).
      assert (EQ1 : as_frames (nd_st nbx) / kStoreBlockFrames = (as_frames (nd_st nbx) + countN - 1) / kStoreBlockFrames) by (rewrite F9; unfold fr in *; rewrite <- Eb, D1; reflexivity).
      assert (BQ : as_frames (nd_st nbx) / kStoreBlockFrames = bFv) by (rewrite F9, D2; reflexivity).
      destruct sbx as [r2|].
      + destruct SBRx as (_ & B0 & BG & V1 & V2). do 2 eexists.
        eapply arun_abind.
        * apply arun_store_alloc_once_grow; [exact EQ1| rewrite BQ; exact B0| rewrite F4, BQ; exact BG| rewrite known_ranges_bump; exact V1| exact V2].
        * cbv beta iota. rewrite F9, D3. apply arun_aret.
      + do 2 eexists.
        eapply arun_abind.
        * apply arun_store_alloc_once_fit; [exact EQ1| rewrite F4, BQ; exact SBRx].
        * cbv beta iota. rewrite F9, D3. apply arun_aret. }
  destruct SA as (fS & evsS & SA).
  unfold depot_put.
  Ltac dp_head DL EN HN1 := eapply arun_abind; [apply arun_aget|]; cbv beta; eapply arun_abind; [apply arun_aupd|]; cbv beta; rewrite DL; cbv zeta;
    rewrite <- EN; unfold acheck; rewrite (proj2 (Z.ltb_lt (N + 1) (2^31))) by (clear -HN1; lia); eapply arun_abind; [apply arun_aret|]; cbv beta.
  destruct nbx as [r1|].
  - destruct NBX0 as (_ & MZ & V1 & V2). do 2 eexists. dp_head DL EN HN1.
    eapply arun_abind.
    + rewrite (proj2 (Z.eqb_eq _ _) MZ). eapply arun_abind; [apply arun_call_mmap_ordie; [rewrite KNB; exact V1| exact V2]|]. cbv beta. apply arun_aupd.
    + cbv beta. rewrite Ecnt. change (upd_node_blocks (fun l => l ++ [r1]) (upd_ndepot (fun k => k + 1) a)) with (nd_st (Some r1)).
      eapply arun_abind; [exact SA|]. cbv beta. eapply arun_abind; [apply arun_aupd| apply arun_aret].
  - do 2 eexists. dp_head DL EN HN1.
    eapply arun_abind.
    + rewrite (proj2 (Z.eqb_neq _ _) NBX0). apply arun_aret.
    + cbv beta. rewrite Ecnt. change (upd_ndepot (fun k => k + 1) a) with (nd_st None).
      eapply arun_abind; [exact SA|]. cbv beta. eapply arun_abind; [apply arun_aupd| apply arun_aret].
Qed.

(* [comment removed for export] *)
Lemma se_fin : forall (j8 : list byte) (wl : word) (nbx : option Z) (blk : Z) (sbx : option Z) (sbF : Z) (js : list byte) (j1 j2 : word) (m3 : mem) (mo3 : Model)
    (x1 x5 x6 x7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
  depot_lookup E0 a key = None -> (forall j, 1 <= j <= N -> nth_hash HS j <> h) ->
  spost j8 wl nbx blk sbx sbF js j1 j2 m3 mo3 ->
  realizes_cfg acfg bsegs (mkCfg (S_se x1 x5 x6 x7 sbF q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3) mo3) K.
Proof.
  intros until q31. intros DL MISSF SP.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. unfold K_DEPOT in LO.
  pose proof KB0 as KB. pose proof HN as (HN0 & HN1 & HN2). pose proof FRF as (FR0 & FR64 & FRB). pose proof FRB as FRB'. unfold kStoreBlockCount in FRB'.
  pose proof (Z.mod_pos_bound h kTabSize ltac:(unfold kTabSize; clear; lia)) as BKR. change (h mod kTabSize) with bkt in BKR. unfold kTabSize in BKR.
  pose proof (Z.mod_pos_bound (N + 1) kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; clear; lia)) as NMR. unfold kDepotNodesPerBlock in NMR.
  assert (ENA : BF_depot7.NA N blk = blk + 16 * ((N + 1) mod 65536)) by reflexivity.
  pose proof (fst_facts len ws N fr ltac:(unfold zlen in LEN; exact LEN) ltac:(unfold zlen in LWS; exact LWS) FR0 FR64 FRB) as (FS0 & FS32 & FSM & FSB & FSR & PKR).
  pose proof FSR as FSR'. unfold kStoreBlockCount in FSR'.
  destruct SP as (PL & AL & NTH & KBL & NBX & BFL & SNTH & SPL & SAL & ESB2 & ENB2 & MU3 & WM3 & MI3 & SK3 & FR3 & SF3 & STF3 & AFR3 & NODE3 & TBA3 & NUQ3 & TLM3 & MAP3 & WR3
                  & SS3 & [al AL3] & BLK3 & BF3 & MX3 & [bs0 [U3 L3]] & OSB3 & Qfs3 & Qfds3 & Qtid3 & AK3 & TOK3 & KP3 & SBX).
  set (T2 := sg_st sbx (nd_st nbx)) in *.
  pose proof PL as (PL1 & PL2 & PL3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in PL1, PL2, PL3.
  pose proof SPL as (SP1 & SP2 & SP3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kStoreBlockBytes in SP1, SP2, SP3.
  assert (BLKR : placed blk kDepotNodeBlockBytes /\ blk mod 16 = 0) by (split; [exact PL| clear -AL; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK3) as (R3 & R3' & ATK3 & _).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3) as EV3. pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK3) as KV3. cbn [aps_alloc sA aps_set_alloc] in KV3.
  assert (PSTK2 : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> PP (sA T2 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA T2 s) mo3 AK3 WE ENV0); clear -Hy Hk LOC' A47; lia. }
  assert (PIMG2 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA T2 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA T2 s) mo3 AK3 WE EV3 ENV0); [clear -Hy; lia| exact Hk]. }
  assert (INblk : In blk (node_blocks E0 T2)).
  { rewrite ENB2, <- NTH. unfold nthz. rewrite (proj2 (Z.leb_le 0 kb)) by (clear -KB; lia). rewrite (proj2 (Z.ltb_lt _ _) KBL). cbn [andb]. apply nth_In. unfold zlen in KBL. clear -KBL KB. lia. }
  assert (INsb : In sbF (store_blocks E0 T2)).
  { rewrite ESB2, <- SNTH. unfold nthz. rewrite (proj2 (Z.leb_le 0 bFv)) by (clear -FSR; lia). rewrite (proj2 (Z.ltb_lt _ _) BFL). cbn [andb]. apply nth_In. unfold zlen in BFL. clear -BFL FSR. lia. }
  assert (PNA2 : forall y k, BF_depot7.NA N blk <= y -> y + Z.of_nat k <= BF_depot7.NA N blk + 16 -> PP (sA T2 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_node_block' E0 FSB0 HR0 (sA T2 s) mo3 AK3 ENV0 blk); [exact INblk| rewrite ENA in Hy; clear -Hy NMR; lia| rewrite ENA in Hk; unfold kDepotNodeBlockBytes; clear -Hk NMR; lia]. }
  assert (PSB2 : forall y k, sbF <= y -> y + Z.of_nat k <= sbF + kStoreBlockBytes -> PP (sA T2 s) mo3 (Z_to_bv 64 y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_store_block' E0 FSB0 HR0 (sA T2 s) mo3 AK3 ENV0 sbF); [exact INsb| exact Hy| exact Hk]. }
  pose proof (node_store_disjoint T2 mo3 blk sbF KV3 AK3 INblk INsb) as DJ.
  (* [comment removed for export] *)
  assert (AG03 : forall z, 0xa5000 <= z < 0x140c80 -> m3 (wa z) = m (wa z)).
  { intros z Hz. apply MU3. rewrite wa_unsigned by (clear -Hz; lia). unfold WC, WB. rewrite ENA.
    destruct nbx as [r1|]; [rewrite (proj1 NBX)|]; destruct sbx as [r2|]; [rewrite (proj1 SBX)| |rewrite (proj1 SBX)|];
      cbn [outside opt_iv app fst snd]; unfold kDepotNodeBlockBytes, kStoreBlockBytes in *; clear -Hz LO LOC' CEILB PL1 SP1 NMR BKR KB; unfold kNodesMap1 in *; lia. }
  pose proof STAT as [STA0 CF0]. pose proof STA0 as (G1 & G2 & G3 & V1 & V2 & V3 & V4).
  assert (GOT3 : rw_cells bsegs m3 0xa5590 [C8 (Z_to_bv 64 0x1400e8)]).
  { eapply (rw_cells_agree bsegs); [| exact G2]. unfold GOT_CFLAGS, V_CFLAGS. cbn. intros x Hx. apply AG03. clear -Hx; lia. }
  assert (CF3 : rw_cells bsegs m3 (0x1400e8 + 240) [C4 (Z_to_bv 64 0)]).
  { eapply (rw_cells_agree bsegs); [| exact CF0]. unfold V_CFLAGS. cbn. intros x Hx. apply AG03. clear -Hx; lia. }
  (* [comment removed for export] *)
  unfold S_se.
  eapply (rzA_seg_cfg bsegs (aSc (sA T2 s)) (aNc (sA T2 s)) (aEBc (sA T2 s)) (PP (sA T2 s) mo3)); [| exact KP3|].
  { eapply (put_se (PP (sA T2 s) mo3) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (A + 8 * zlen ws) A len ws HS N blk fr LOC');
      [ clear -LO; lia| clear -UA LEN; lia| exact A47| unfold zlen in LEN; exact LEN| unfold zlen in LWS; exact LWS| unfold zlen; clear -UA; lia
      | clear -HN0 HN1; lia| exact BLKR| exact FR0| exact FR64| exact FRB| exact PSTK2| exact PIMG2| exact PNA2
      | exact SK3| exact MI3| exact FR3| exact SF3| exact STF3| exact AFR3| exact NODE3| | exact TBA3| exact BF3| exact U3| exact L3
      | clear -SP1; lia| exact SP2| rewrite ENA; unfold kDepotNodeBlockBytes, kStoreBlockBytes in DJ |- *; clear -DJ NMR; lia| exact GOT3| exact CF3| exact PSB2].
    (* [comment removed for export] *)
    eapply u64arr_agree; [| exact TR]. intros x Hx. unfold zlen in A47. apply MU3. rewrite wa_unsigned by (clear -Hx UA A47 USPR'; lia). unfold WC, WB. rewrite ENA.
    destruct nbx as [r1|]; [rewrite (proj1 NBX)|]; destruct sbx as [r2|]; [rewrite (proj1 SBX)| |rewrite (proj1 SBX)|];
      cbn [outside opt_iv app fst snd]; unfold kDepotNodeBlockBytes, kStoreBlockBytes in *; clear -Hx UA LO LOC' CEILB PL1 PL2 SP1 SP2 NMR BKR KB; unfold kNodesMap1 in *; lia. }
  intros ms4 mo4 POST4 AG4 KP4.
  destruct POST4 as (w0 & w1 & w2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & w3 & w4 & w5 & w6 & m4 & bs' & pk & -> & MU4 & WM4 & MI4 & SK4 & TBA4 & [sid NODE4] & BF4 & U4 & L4 & PK).
  pose proof (magree_frame _ _ AG4) as (Qfds4 & Qvm4 & Qlz4 & Qfs4 & Qh4 & Qtid4 & _).
  pose proof (AKern_frame _ _ _ _ Qvm4 Qlz4 AK3) as AK4.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK3 AG4 (proj1 KP4)) as TOK4.
  set (a' := st_final nbx strd sbx).
  pose proof (final_fields nbx strd sbx) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18).
  fold a' in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18. fold T2 in E1, E2, E3, E4, E5, E6, E7, E8.
  assert (EFR : as_frames a' = frE).
  { rewrite E10. unfold frE. destruct (BF_depot7.straddles len fr) eqn:STR.
    - destruct (straddles_true len ws N fr ltac:(unfold zlen in LEN; exact LEN) ltac:(unfold zlen in LWS; exact LWS) FR0 STR) as (_ & _ & D3 & _). rewrite D3. clear; lia.
    - destruct (straddles_false len ws N fr ltac:(unfold zlen in LEN; exact LEN) FR0 STR) as (_ & _ & D3 & _). rewrite D3. clear; lia. }
  assert (EDK : depot_keys E0 a' = depot_keys E0 a ++ [key]) by (unfold depot_keys; rewrite E9, app_assoc; reflexivity).
  assert (EHS : depot_hashes E0 a' = HS ++ [h]) by (unfold depot_hashes, HS, h; rewrite EDK, map_app; reflexivity).
  assert (ENB' : node_blocks E0 a' = NB ++ opt_list nbx) by (unfold node_blocks, NB; rewrite E13; cbn; reflexivity).
  assert (ESB' : store_blocks E0 a' = SBL ++ opt_list sbx) by (unfold store_blocks, SBL; rewrite E14; cbn; reflexivity).
  (* [comment removed for export] *)
  destruct (arun_miss nbx blk sbx sbF DL NBX SBX) as (fA & evsA & RUN). fold a' in RUN.
  assert (DI' : depot_inv E0 a').
  { eapply (hoareW_arun (fun s0 => s0 = aps_alloc s) (depot_put E0 key) (fun s' _ => depot_inv E0 s') (aps_alloc s));
      [eapply depot_put_di; [rewrite zlen_bst_key; [clear -LEN LWS; lia| clear -LEN; lia]| exact DINV]| reflexivity| exact RUN]. }
  (* [comment removed for export] *)
  assert (TOK5 : RTOKc (C - 1) (C' - DSLACK) (sA a' s) mo4).
  { pose proof (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s T2 a' mo4 TOK4 (same_fp_final nbx strd sbx) E5 E6) as T5.
    eapply (RTOK_le E0 FSB0 HR0 L0 RES0 EB0); [exact T5| clear -C1; lia|].
    assert (NGB : 0 <= ngcost nbx <= kDepotNodeBlockBytes + NMAXA + 4095) by (clear; destruct nbx; cbn [ngcost]; unfold kDepotNodeBlockBytes, NMAXA; lia).
    assert (SGB : 0 <= sgcost sbx <= kStoreBlockBytes + NMAXA + 4095) by (clear; destruct sbx; cbn [sgcost]; unfold kStoreBlockBytes, NMAXA; lia).
    pose proof CSL as X. unfold DSLACK, kStoreBlockBytes, kDepotNodeBlockBytes, NMAXA in NGB, SGB, X |- *. clear -X NGB SGB; lia. }
  (* [comment removed for export] *)
  assert (AG34 : forall z, 0 <= z < 2^64 -> (z < usp - 224 \/ usp <= z) -> (z < BF_depot7.NA N blk + 8 \/ BF_depot7.NA N blk + 16 <= z) ->
                           (z < 1639576 + 4 * bkt \/ 1639576 + 4 * bkt + 4 <= z) -> (z < 1574024 + 16 + 16 * bFv + 8 \/ 1574024 + 16 + 16 * bFv + 12 <= z) ->
                           (z < sbF + 8 * (fstv mod kStoreBlockFrames) \/ sbF + 8 * (fstv mod kStoreBlockFrames) + 8 * countN <= z) -> m4 (wa z) = m3 (wa z)).
  { intros z Hz H1 H2 H3 H4 H5. apply MU4. rewrite wa_unsigned by exact Hz. unfold BF_depot7.se_fp, BF_depot6.TBA, BF_depot7.BI, BF_depot3.TD, BF_depot3.SS.
    change (BF_depot6.bkt len ws) with bkt. cbn. clear -H1 H2 H3 H4 H5. lia. }
  assert (AG03s : forall z, 0 <= z < 0x603000 -> (z < 1639576 + 4 * bkt \/ 1639576 + 4 * bkt + 4 <= z) -> (z < 5833880 \/ 5833884 <= z) -> (z < 5833888 \/ 5833892 <= z) ->
                            (z < 5833896 + 8 * kb \/ 5833904 + 8 * kb <= z) -> (z < 1574024 \/ 1574024 + 16 + 16 * 4096 <= z) -> m3 (wa z) = m (wa z)).
  { intros z Hz H1 H2 H3 H4 H5. apply MU3. rewrite wa_unsigned by (clear -Hz; lia). unfold WC, WB. rewrite ENA.
    destruct nbx as [r1|]; [rewrite (proj1 NBX)|]; destruct sbx as [r2|]; [rewrite (proj1 SBX)| |rewrite (proj1 SBX)|];
      cbn [outside opt_iv app fst snd]; unfold kDepotNodeBlockBytes, kStoreBlockBytes in *; clear -Hz H1 H2 H3 H4 H5 LO LOC' CEILB PL1 SP1 NMR; lia. }
  assert (AG34s : forall z, 0 <= z < 0x603000 -> (z < 1639576 + 4 * bkt \/ 1639576 + 4 * bkt + 4 <= z) -> (z < 1574024 + 16 + 16 * bFv + 8 \/ 1574024 + 16 + 16 * bFv + 12 <= z) -> m4 (wa z) = m3 (wa z)).
  { intros z Hz H1 H2. apply AG34; [clear -Hz; lia| clear -Hz LO LOC' CEILB; lia| rewrite ENA; clear -Hz PL1 NMR; lia| exact H1| exact H2| clear -Hz SP1 FSM FS0; unfold kStoreBlockFrames in *; Z.div_mod_to_equations; lia]. }
  apply (CONT w0 w1 w2 p1 p2 p3 p4 p5 p6 p7 w3 w4 w5 w6 m4 mo4 a' (N + 1)). unfold dput_post_state.
  split; [exact SK4|]. split; [exact (wmono_trans _ _ _ _ WM3 WM4)|]. split; [exact MI4|].
  split. { (* [comment removed for export] *)
    exists (WC nbx sbx blk ++ BF_depot7.se_fp sp len ws N blk fr sbF). split; [exact (munch_app _ _ _ _ _ MU3 MU4)|].
    assert (INblk' : In blk (ae_depot_nodes E0 :: as_node_blocks a')) by (change (In blk (node_blocks E0 a')); rewrite ENB', <- ENB2; exact INblk).
    assert (INsb' : In sbF (ae_store_blk E0 :: as_store_blocks a')) by (change (In sbF (store_blocks E0 a')); rewrite ESB', <- ESB2; exact INsb).
    assert (DS1 : In (1639576, 4456464) (depot_static E0)) by (unfold depot_static; rewrite IC0; left; reflexivity).
    assert (DS2 : In (1574024, 65552) (depot_static E0)) by (unfold depot_static; rewrite IC0; right; left; reflexivity).
    assert (WFR : forall x y, lo <= x -> y <= usp -> dput_w_ok E0 a' lo usp (x, y)) by (intros x y Hx Hy; left; cbn [fst snd]; split; assumption).
    assert (WTD : forall x y, 1639576 <= x -> y <= 1639576 + 4456464 -> dput_w_ok E0 a' lo usp (x, y)) by (intros x y Hx Hy; right; left; exists (1639576, 4456464); split; [exact DS1| cbn [fst snd]; split; assumption]).
    assert (WSS : forall x y, 1574024 <= x -> y <= 1574024 + 65552 -> dput_w_ok E0 a' lo usp (x, y)) by (intros x y Hx Hy; right; left; exists (1574024, 65552); split; [exact DS2| cbn [fst snd]; split; assumption]).
    assert (WNB : forall b' x y, In b' (ae_depot_nodes E0 :: as_node_blocks a') -> b' <= x -> y <= b' + kDepotNodeBlockBytes -> dput_w_ok E0 a' lo usp (x, y)) by (intros b' x y Hb Hx Hy; right; right; left; exists b'; split; [exact Hb| cbn [fst snd]; split; assumption]).
    assert (WSB : forall b' x y, In b' (ae_store_blk E0 :: as_store_blocks a') -> b' <= x -> y <= b' + kStoreBlockBytes -> dput_w_ok E0 a' lo usp (x, y)) by (intros b' x y Hb Hx Hy; right; right; right; exists b'; split; [exact Hb| cbn [fst snd]; split; assumption]).
    unfold WC, WB. rewrite <- app_comm_cons. unfold BF_depot7.se_fp, BF_depot6.TBA, BF_depot7.BI, BF_depot3.TD, BF_depot3.SS. change (BF_depot6.bkt len ws) with bkt. rewrite ENA.
    pose proof LO as LO'. unfold kNodesMap1 in KB.
    apply Forall_cons; [apply WFR; clear -LO'; lia|].
    repeat rewrite <- app_assoc.
    apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]].
    - repeat apply Forall_cons; [apply WFR; clear -LO'; lia| apply WTD; clear -BKR; lia| apply WTD; clear; lia| apply WTD; clear; lia| apply WTD; clear -KB; lia| apply Forall_nil].
    - destruct nbx as [r1|]; cbn [opt_iv]; [| apply Forall_nil]. rewrite (proj1 NBX). apply Forall_cons; [apply (WNB blk); [exact INblk'| clear; lia| clear; lia]| apply Forall_nil].
    - repeat apply Forall_cons; [apply (WNB blk); [exact INblk'| clear -NMR; lia| unfold kDepotNodeBlockBytes; clear -NMR; lia]| apply WSS; clear; lia| apply Forall_nil].
    - destruct sbx as [r2|]; cbn [opt_iv]; [| apply Forall_nil]. rewrite (proj1 SBX). apply Forall_cons; [apply (WSB sbF); [exact INsb'| clear; lia| clear; lia]| apply Forall_nil].
    - repeat apply Forall_cons;
        [ apply WFR; clear -LO'; lia
        | apply (WNB blk); [exact INblk'| clear -NMR; lia| unfold kDepotNodeBlockBytes; clear -NMR; lia]
        | apply WTD; clear -BKR; lia
        | apply WSS; clear -FSR'; lia
        | apply (WSB sbF); [exact INsb'| clear -FSM FS0; unfold kStoreBlockFrames in *; Z.div_mod_to_equations; lia| clear -FSM FS0; unfold kStoreBlockFrames, kStoreBlockBytes in *; Z.div_mod_to_equations; lia]
        | apply Forall_nil ]. }
  split; [exists fA, (opt_ans nbx ++ opt_ans sbx), evsA, []; exact RUN|].
  split; [clear -HN0 HN1; lia|].
  split. { (* [comment removed for export] *)
    split; [exact DI'|].
    unfold DepotRep. rewrite IC0. cbn [aic_theDepot aic_stackStore both_ic]. rewrite EHS, EDK, ENB', ESB', EFR.
    split. { intros b' Hb. rewrite bucket_head_app1. change (bucket_of h) with bkt. destruct (Z.eqb_spec bkt b') as [<-|NE].
             - rewrite <- EHSN. unfold BF_depot6.TBA, BF_depot3.TD in TBA4. change (BF_depot6.bkt len ws) with bkt in TBA4. exact TBA4.
             - eapply (rw_cells_agree bsegs); [| exact (D_tab b' Hb)]. cbn. intros x Hx. unfold kTabSize in Hb.
               rewrite AG34s by (clear -Hx Hb NE BKR FSR'; lia). apply AG03s; clear -Hx Hb NE BKR KB; unfold kNodesMap1 in *; lia. }
    split. { unfold zlen. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. fold (zlen (depot_keys E0 a)). fold N.
             eapply (rw_cells_agree bsegs); [| exact NUQ3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR FSR'; lia. }
    split. { intros k Hk. unfold kNodesMap1 in Hk. destruct (Z.eq_dec k kb) as [->|NE].
             - rewrite NTH. eapply (rw_cells_agree bsegs); [| exact MAP3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR KB FSR'; unfold kNodesMap1 in *; lia.
             - assert (EQ : nthz (NB ++ opt_list nbx) k = nthz NB k).
               { destruct nbx as [r1|]; cbn [opt_list]; [| rewrite app_nil_r; reflexivity]. apply nthz_app_other.
                 pose proof (proj1 (proj2 NBX)) as MZ. destruct kb_cases as [[_ X]|(KE & _)]; [exfalso; exact (X MZ)|]. rewrite <- KE. exact NE. }
               rewrite EQ. eapply (rw_cells_agree bsegs); [| exact (D_map1 k ltac:(unfold kNodesMap1; exact Hk))]. cbn. intros x Hx.
               rewrite AG34s by (clear -Hx Hk BKR FSR'; lia). apply AG03s; clear -Hx Hk NE BKR KB; lia. }
    split. { intros i Hi. unfold zlen in Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite Nat2Z.inj_add in Hi. change (Z.of_nat 1) with 1 in Hi.
             fold (zlen (depot_keys E0 a)) in Hi. fold N in Hi.
             destruct (Z.eq_dec i (N + 1)) as [->|NE].
             - (* [comment removed for export] *)
               exists sid. unfold node_addr. rewrite ENB'. fold kb. rewrite NTH. rewrite EHSN at 2 3. rewrite nth_hash_app_new, node_link_app_new.
               change (bucket_head HS (bucket_of h)) with (BF_depot6.head len ws HS). rewrite <- ENA. exact NODE4.
             - assert (Hi' : 1 <= i <= N) by (clear -Hi NE; lia).
               pose proof (NBC i Hi') as IB. destruct (D_nodes i Hi') as (sid' & ND).
               exists sid'. unfold node_addr. rewrite ENB'. rewrite nthz_opt_old by exact IB.
               rewrite EHSN in Hi'. rewrite nth_hash_app_old, node_link_app_old by exact Hi'. rewrite <- EHSN in Hi'.
               pose proof (node_addr_in_block E0 a i ltac:(clear -Hi'; lia) IB) as (b' & Hb' & L1 & L2). unfold node_addr in L1, L2. fold NB in L1, L2.
               pose proof (NBR b' Hb') as (Q1 & Q2 & Q3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in Q1, Q2, Q3, L2.
               (* [comment removed for export] *)
               assert (IBr : 0 <= i / kDepotNodesPerBlock < zlen NB) by (split; [apply Z.div_pos; [clear -Hi'; lia| unfold kDepotNodesPerBlock; clear; lia]| exact IB]).
               pose proof (Z.mod_pos_bound i kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; clear; lia)) as IMR. unfold kDepotNodesPerBlock in IMR.
               set (ob := nthz NB (i / kDepotNodesPerBlock)) in *.
               assert (OBr : 0x603000 <= ob /\ ob + 1048576 <= alloc_ceiling).
               { assert (INob : In ob NB) by (subst ob; unfold nthz; rewrite (proj2 (Z.leb_le _ _) (proj1 IBr)), (proj2 (Z.ltb_lt _ _) (proj2 IBr)); cbn [andb]; apply nth_In; unfold zlen in IBr; clear -IBr; lia).
                 pose proof (NBR ob INob) as (Y1 & Y2 & Y3). unfold A_IMG_END, kDepotNodeBlockBytes in Y1, Y2. split; [exact Y1| exact Y2]. }
               (* [comment removed for export] *)
               assert (NSLOT : ob + 16 * (i mod kDepotNodesPerBlock) + 16 <= BF_depot7.NA N blk \/ BF_depot7.NA N blk + 16 <= ob + 16 * (i mod kDepotNodesPerBlock)).
               { rewrite ENA. unfold kDepotNodesPerBlock in *. destruct (Z.eq_dec (i / 65536) kb) as [EQ|NEQ].
                 - assert (Eob : ob = blk) by (subst ob; rewrite EQ, <- NTH; symmetry; apply nthz_opt_old; rewrite <- EQ; exact IB).
                   rewrite Eob. unfold kb, kDepotNodesPerBlock in EQ. clear -EQ NE Hi' IMR NMR. Z.div_mod_to_equations. first [lia | nia].
                 - assert (P1 : 0 <= i / 65536 < zlen (node_blocks E0 T2)) by (rewrite ENB2; unfold zlen in *; rewrite length_app; clear -IBr; lia).
                   assert (P2 : 0 <= kb < zlen (node_blocks E0 T2)) by (rewrite ENB2; split; [clear -KB; lia| exact KBL]).
                   pose proof (node_blocks_apart mo3 T2 (i / 65536) kb KV3 AK3 P1 P2 NEQ) as X. clear P1 P2.
                   rewrite ENB2, NTH in X. rewrite nthz_opt_old in X by exact IB. fold ob in X. unfold kDepotNodeBlockBytes in X. clear -X IMR NMR. lia. }
               (* [comment removed for export] *)
               assert (NSB : ob + 1048576 <= sbF \/ sbF + 8388608 <= ob).
               { assert (INob2 : In ob (node_blocks E0 T2)) by (rewrite ENB2; apply in_app_iff; left; subst ob; unfold nthz; rewrite (proj2 (Z.leb_le _ _) (proj1 IBr)), (proj2 (Z.ltb_lt _ _) (proj2 IBr)); cbn [andb]; apply nth_In; unfold zlen in IBr; clear -IBr; lia).
                 pose proof (node_store_disjoint T2 mo3 ob sbF KV3 AK3 INob2 INsb) as X. unfold kDepotNodeBlockBytes, kStoreBlockBytes in X. exact X. }
               (* [comment removed for export] *)
               assert (NNB : match nbx with Some r1 => ob + 1048576 <= r1 \/ r1 + 1048576 <= ob | None => True end).
               { destruct nbx as [r1|]; [| exact I]. pose proof (proj1 NBX) as ->.
                 destruct (Z.eq_dec (i / kDepotNodesPerBlock) kb) as [EQ|NEQ].
                 - exfalso. pose proof (proj1 (proj2 NBX)) as MZ. destruct kb_cases as [[_ X]|(KE & _)]; [exact (X MZ)| rewrite EQ, KE in IB; clear -IB; lia].
                 - assert (P1 : 0 <= i / kDepotNodesPerBlock < zlen (node_blocks E0 T2)) by (rewrite ENB2; unfold zlen in *; rewrite length_app; clear -IBr; lia).
                   assert (P2 : 0 <= kb < zlen (node_blocks E0 T2)) by (rewrite ENB2; split; [clear -KB; lia| exact KBL]).
                   pose proof (node_blocks_apart mo3 T2 (i / kDepotNodesPerBlock) kb KV3 AK3 P1 P2 NEQ) as X. clear P1 P2.
                   rewrite ENB2, NTH in X. rewrite nthz_opt_old in X by exact IB. fold ob in X. unfold kDepotNodeBlockBytes in X. exact X. }
               unfold kDepotNodesPerBlock in *.
               eapply (rw_cells_agree bsegs); [| exact ND]. cbn. intros x Hx.
               rewrite AG34 by (rewrite ?ENA in *; clear -Hx OBr IMR NMR NSLOT NSB LO LOC' CEILB BKR FSR' SP1 FSM FS0; unfold kStoreBlockFrames in *; first [lia | (Z.div_mod_to_equations; lia)]).
               apply MU3. rewrite wa_unsigned by (clear -Hx OBr CEILB; lia). unfold WC, WB. rewrite ENA. rewrite ENA in NSLOT.
               destruct nbx as [r1|]; [rewrite (proj1 NBX) in NNB |- *|]; destruct sbx as [r2|]; [rewrite (proj1 SBX) in *| |rewrite (proj1 SBX) in *|];
                 cbn [outside opt_iv app fst snd]; unfold kDepotNodeBlockBytes, kStoreBlockBytes in *; clear -Hx OBr IMR NMR NSLOT NSB NNB LO LOC' CEILB BKR KB; unfold kNodesMap1 in *; lia. }
    split. { (* [comment removed for export] *)
             intros b' Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
             - eapply wr_at_transport; [exact (D_nbw b' Hb)| exact (wmono_trans _ _ _ _ WM3 WM4)].
             - destruct nbx as [r1|]; [| destruct Hb]. destruct Hb as [<-|[]]. rewrite (proj1 NBX). eapply wr_at_transport; [exact WR3| exact WM4]. }
    split. { eapply (rw_cells_agree bsegs); [| exact SS3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR FSR'; lia. }
    split. { exists al. eapply (rw_cells_agree bsegs); [| exact AL3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR FSR'; lia. }
    split. { intros k Hk. unfold kStoreBlockCount in Hk. destruct (Z.eq_dec k bFv) as [->|NEk].
             - rewrite SNTH. split; [| exists (Z_to_bv 64 0); eapply (rw_cells_agree bsegs); [| exact MX3]; cbn; intros x Hx; apply AG34s; clear -Hx Hk BKR FSR'; lia].
               replace (stored_of frE bFv) with (fstv mod kStoreBlockFrames + countN); [unfold BF_depot7.BI, BF_depot3.SS in BF4; exact BF4|].
               unfold stored_of, frE. rewrite FSB. clear -FSM FS0 LEN. unfold kStoreBlockFrames, BF_depot7.count in *. Z.div_mod_to_equations. lia.
             - destruct (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk) NEk) as [B1 B2]. split; [| exists (Z_to_bv 64 0)].
               + eapply (rw_cells_agree bsegs); [| exact B1]. cbn. intros x Hx. apply AG34s; clear -Hx Hk NEk BKR FSR'; lia.
               + eapply (rw_cells_agree bsegs); [| exact B2]. cbn. intros x Hx. apply AG34s; clear -Hx Hk NEk BKR FSR'; lia. }
    split. { (* [comment removed for export] *)
             intros b' Hb.
             destruct (Z.eq_dec b' sbF) as [->|NEb].
             - exists bs'. split; [exact U4| exact L4].
             - assert (Hb0 : In b' SBL).
               { apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact Hb|]. destruct sbx as [r2|]; [| destruct Hb]. destruct Hb as [<-|[]]. exfalso. apply NEb. exact (proj1 SBX). }
               destruct (OSB3 b' Hb0 NEb) as (bs1 & U1 & L1). exists bs1. split; [| exact L1].
               pose proof (SBR b' Hb0) as [(Y1 & Y2 & Y3) Y4]. unfold A_IMG_END, kStoreBlockBytes in Y1, Y2.
               (* [comment removed for export] *)
               assert (APT : forall x, b' <= x < b' + 8388608 -> x < sbF + 8 * (fstv mod kStoreBlockFrames) \/ sbF + 8 * (fstv mod kStoreBlockFrames) + 8 * countN <= x).
               { intros x Hx2. assert (INb2 : In b' (store_blocks E0 T2)) by (rewrite ESB2; apply in_app_iff; left; exact Hb0).
                 pose proof (store_blocks_apart mo3 T2 b' sbF KV3 AK3 INb2 INsb NEb) as X. unfold kStoreBlockBytes in X.
                 clear -Hx2 X FSM FS0. unfold kStoreBlockFrames in *. Z.div_mod_to_equations. lia. }
               eapply u8arr_agree; [| exact U1]. intros x Hx. rewrite L1 in Hx. unfold kStoreBlockBytes in Hx.
               pose proof (node_store_disjoint T2 mo3 blk b' KV3 AK3 INblk ltac:(rewrite ESB2; apply in_app_iff; left; exact Hb0)) as XD. unfold kDepotNodeBlockBytes, kStoreBlockBytes in XD.
               apply AG34; [clear -Hx Y1 Y2 CEILB; lia| clear -Hx Y1 Y2 LO LOC' CEILB; lia| rewrite ENA; clear -Hx Y1 PL1 NMR XD; lia| clear -Hx Y1 BKR; lia| clear -Hx Y1 FSR'; lia| exact (APT x Hx)]. }
    split. { eapply (rw_cells_agree bsegs); [| exact TLM3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR FSR'; lia. }
    intros k Hk. unfold kStoreBlockCount in Hk. destruct (Z.eq_dec k bFv) as [->|NEk].
    - eapply (rw_cells_agree bsegs); [| exact MX3]. cbn. intros x Hx. apply AG34s; clear -Hx Hk BKR FSR'; lia.
    - destruct (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk) NEk) as [_ B2]. eapply (rw_cells_agree bsegs); [| exact B2]. cbn. intros x Hx. apply AG34s; clear -Hx Hk NEk BKR FSR'; lia. }
  split. { (* [comment removed for export] *)
    split.
    - unfold dTD. eapply (rw_cells_agree bsegs); [| exact TLM3]. cbn. intros x Hx. apply AG34s; clear -Hx BKR FSR'; lia.
    - intros k Hk. unfold dSS, kStoreBlockCount in *. destruct (Z.eq_dec k bFv) as [->|NEk].
      + eapply (rw_cells_agree bsegs); [| exact MX3]. cbn. intros x Hx. apply AG34s; clear -Hx Hk BKR FSR'; lia.
      + destruct (BLK3 k ltac:(unfold kStoreBlockCount; exact Hk) NEk) as [_ B2]. eapply (rw_cells_agree bsegs); [| exact B2]. cbn. intros x Hx. apply AG34s; clear -Hx Hk NEk BKR FSR'; lia. }
  split. { apply (dput_statics_agree m m4 STAT). intros x Hx. rewrite AG34s by (clear -Hx BKR FSR'; lia). apply AG03. exact Hx. }
  split. { eapply AKern_ext; [exact E1| exact E2| exact E3| exact E7| exact E8| exact AK4]. }
  split; [exact TOK5|].
  split; [rewrite Qfs4; exact Qfs3|]. split; [rewrite Qfds4; exact Qfds3| rewrite Qtid4; exact Qtid3].
Qed.
(* [comment removed for export] *)
Lemma dput_call :
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (wz A_DEPOT_PUT) fc None m (seg_rom bsegs)) mo) K.
Proof.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. pose proof LO as LO'. unfold K_DEPOT in LO'.
  pose proof HN as (HN0 & HN1 & HN2). pose proof KB0 as KB.
  assert (BKR : 0 <= bkt < kTabSize) by (unfold bkt, bucket_of; apply Z.mod_pos_bound; unfold kTabSize; clear; lia).
  pose proof WDEP as (WD1 & WD2 & WD3).
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) (PP s mo)); [| exact KIP0|].
  { unfold A_DEPOT_PUT.
    eapply (put_head (PP s mo) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (A + 8 * zlen ws) A len ws NB HS N);
      [ exact SK| exact LOC'| clear -LO'; lia| unfold zlen; clear -UA; lia| exact A47| exact MI| exact TR| unfold zlen in LEN; clear -LEN; lia| unfold zlen in LWS; clear -LWS; lia
      | unfold zlen; clear -UA; lia| exact HN| exact HSR| exact (D_tab bkt BKR)| exact D_nuq| exact D_map1| exact D_nodes| exact NBC| exact KBLE| exact NBR
      | exact PSTK0| exact PIMG0'| intros a' k H1 H2; apply PIMG0; [clear -H1; lia| clear -H2; lia]| exact PNB0 ]. }
  intros ms1 mo1 POST1 AG1 KP1.
  pose proof (magree_frame _ _ AG1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & Qtid1 & _).
  destruct POST1 as [HIT | MISS].
  - (* [comment removed for export] *)
    destruct HIT as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & id & -> & HID & HHASH & MU1 & WM1 & MI1 & SK1).
    assert (DL : depot_lookup E0 a key = Some id).
    { pose proof (depot_lookup_hashes E0 a key) as DLH. fold HS h in DLH. rewrite <- EHSN in DLH.
      destruct (depot_lookup E0 a key) as [id'|] eqn:DL0.
      - f_equal. symmetry. apply (depot_lookup_unique E0 a key id' id WD1 DL0); fold HS; [rewrite <- EHSN; exact HID| exact HHASH].
      - exfalso. exact (DLH id HID HHASH). }
    set (a' := upd_ndepot (fun k => k + 1) a).
    assert (RUN : arun (0 + (0 + 0))%nat (depot_put E0 key a) [] = Some (a', ONorm id, [] ++ ([] ++ []), [])).
    { unfold depot_put. eapply (arun_abind aget); [reflexivity|]. eapply arun_abind; [apply arun_aupd|]. rewrite DL. apply arun_aret. }
    assert (AGlo : forall z, 0 <= z < lo -> m' (wa z) = m (wa z)).
    { intros z Hz. apply MU1. rewrite wa_unsigned by (clear -Hz LO' USPR'; lia). cbn. clear -Hz LO'. lia. }
    assert (AGD : forall z, DepotFPd E0 a z -> m' (wa z) = m (wa z)).
    { intros z Hz. apply AGlo. destruct Hz as [(r & Hr & Hrz)|[(b & Hb & Hbz)|(b & Hb & Hbz)]].
      - rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore both_ic] in Hr. unfold kDepotStaticBytes, kStoreStaticBytes in Hr.
        destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Hrz; clear -Hrz LOC' CEILB; lia.
      - pose proof (NBR b Hb) as (P1 & P2 & P3). unfold A_IMG_END, kDepotNodeBlockBytes in *. clear -P1 P2 Hbz LOC' CEILB. lia.
      - pose proof (proj1 (SBR b Hb)) as (P1 & P2 & P3). unfold A_IMG_END, kStoreBlockBytes in *. clear -P1 P2 Hbz LOC' CEILB. lia. }
    assert (TOK1 : RTOKc (C - 1) (C' - DSLACK) (sA a' s) mo1).
    { pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 C C' s mo mo1 TOK AG1 (proj1 KP1)) as T1.
      rewrite <- (sA_self s) in T1.
      pose proof (RTOK_same_fp_pay E0 FSB0 HR0 L0 RES0 EB0 C C' (C - 1) s a a' mo1 T1 (same_fp_upd_ndepot _ _)
                    ltac:(subst a'; rewrite gapR_upd_ndepot; clear; lia) ltac:(subst a'; rewrite gapD_upd_ndepot1; clear; lia) ltac:(clear -C1; lia)
                    ltac:(subst a'; rewrite gapR_upd_ndepot, gapD_upd_ndepot1; clear; lia)) as T2.
      eapply (RTOK_le E0 FSB0 HR0 L0 RES0 EB0); [exact T2| clear -C1; lia| clear -CSL; unfold DSLACK in *; lia]. }
    assert (DI' : depot_inv E0 a').
    { eapply (hoareW_arun (fun s0 => s0 = a) (depot_put E0 key) (fun s' _ => depot_inv E0 s') a); [eapply depot_put_di; [rewrite zlen_bst_key; [clear -LEN LWS; lia| clear -LEN; lia]| exact DINV]| reflexivity| exact RUN]. }
    apply (CONT t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo1 a' id). unfold dput_post_state.
    split; [exact SK1|]. split; [exact WM1|]. split; [exact MI1|].
    split; [exists [(usp - 224, usp)]; split; [exact MU1| constructor; [left; cbn [fst snd]; clear -LO'; lia| constructor]]|].
    split; [exists (0 + (0 + 0))%nat, [], ([] ++ ([] ++ [])), []; exact RUN|].
    split; [clear -HID HN0 HN1; lia|].
    split; [split; [exact DI'| apply (proj2 (DepotRep_upd_ndepot _ _ _)); eapply (DepotRep_frame' bsegs E0); [exact DINV| exact DREP| exact WM1| exact AGD]]|].
    split; [eapply dput_mutexes_agree; [exact MTX| intros x Hx; apply AGlo; clear -Hx LOC' CEILB; lia]|].
    split; [eapply dput_statics_agree; [exact STAT| intros x Hx; apply AGlo; clear -Hx LOC' CEILB; lia]|].
    split; [apply AKern_upd_ndepot; eapply AKern_frame; [exact Qvm1| exact Qlz1| exact AK]|].
    split; [exact TOK1|].
    split; [exact Qfs1|]. split; [exact Qfds1| exact Qtid1].
  - (* [comment removed for export] *)
    destruct MISS as (a2' & a3' & a4' & a5' & a6' & m1 & j8 & wl & MISSF & MU1 & WM1 & MI1 & SK1 & FR1 & TBA1 & NUQ1 & ARMS).
    assert (DL : depot_lookup E0 a key = None).
    { pose proof (depot_lookup_hashes E0 a key) as DLH. fold HS h in DLH. rewrite <- EHSN in DLH.
      destruct (depot_lookup E0 a key) as [id'|] eqn:DL0; [| reflexivity]. exfalso. destruct DLH as [X1 X2]. exact (MISSF id' X1 X2). }
    apply (nodes_stage a2' a3' a4' a5' a6' m1 mo1 j8 wl _ MISSF MU1 WM1 MI1 SK1 FR1 TBA1 NUQ1 AG1 KP1 ARMS).
    intros rax x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 m2 mo2 nbx blk NP.
    apply (store_stage j8 wl nbx blk m2 mo2 rax x11 y2 y3 y4 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 NP).
    intros x1 x5 x6 x7 sbF q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3 mo3 sbx js j1 j2 SP.
    exact (se_fin j8 wl nbx blk sbx sbF js j1 j2 m3 mo3 x1 x5 x6 x7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 DL MISSF SP).
Qed.
End Call.

Theorem depot_put_srz : depot_put_srz_stmt E0 FSB0 HR0 L0 RES0 EB0.
Proof.
  unfold depot_put_srz_stmt. intros until K. cbv zeta. intros KN TOK C1 CSL AK WF NBZ SBZ SECB NDI REP MTX STAT MI SK LOC LO SPA UA A47 TR LEN LWS CONT.
  exact (dput_call ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s Pq Dq lo A len C C' ws K
           KN TOK C1 CSL AK WF NBZ SBZ SECB NDI REP MTX STAT MI SK LOC LO UA A47 TR LEN LWS CONT).
Qed.
End DputT.
End RC__1.
