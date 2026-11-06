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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf9
  AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepCa AsanRepX AsanFrame AsanRepFlip AsanRealloc AsanRefillM.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_iface AF_place AF_fakestack_rep AF_kit AF_kit2 AF_poison AF_free_kit AF_qkit AF_free1 AF_free1b AF_free1e AF_free1c AF_free1d AF_free3 AF_free4 AF_free12
  A_policy5 A_slack5 A_budget5 A_live A_bundle A_benv5 A_init5 A_instD5 A_balloc5 A_bpolicy5 A_rtok5 A_bevents5 A_bframe
  AF_alloc_iface AF_dput_iface AF_free_iface AF_refill_iface AF_tkit AF_ainv_kit AX_unreg AX_Exit AF_statics AF_caT AF_casT AF_refill_room AF_deallocT1 AF_deallocT2 AF_deallocT3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blen_qcount : forall l, blen l = qcount l. Proof. intros l. reflexivity. Qed.
Lemma bhd_first : forall l, bhd l = list_first l. Proof. intros [|b l]; reflexivity. Qed.
Lemma blast_snoc : forall l b, blast (l ++ [b]) = b_addr b.
Proof.
  intros l b. induction l as [|b0 l IH]; [reflexivity|]. destruct l as [|b1 l']; [reflexivity|].
  cbn [app] in IH |- *. change (blast (b0 :: b1 :: l' ++ [b])) with (blast (b1 :: l' ++ [b])). exact IH.
Qed.
Lemma blast_last : forall l, blast l = list_last l.
Proof. intros l. destruct (snoc_case l) as [->|(l' & b & ->)]; [reflexivity|]. rewrite list_last_snoc. apply blast_snoc. Qed.

Lemma arep_batch_list_views : forall (sx : astate) l m, arep_batch_list asegs sx l m -> bcells m l /\ bitemsl m l.
Proof.
  intros sx l m. induction l as [|b l IH]; intros H; [split; exact I|].
  destruct H as [[HB HI] HR]. destruct (IH HR) as [BC BI].
  split; [| split; [exact HI| exact BI]].
  split; [| exact BC]. destruct l; exact HB.
Qed.

(* [comment removed for export] *)
Lemma wf_bok : forall E P (sx : astate) mo lo, AWf E P [] sx -> AKern E sx mo -> alloc_ceiling <= lo ->
  forall b, In b (as_tq sx ++ as_gq sx) -> bok lo (ae_thread E) b.
Proof.
  intros E P sx mo lo WF K LOC b Hb. pose proof ceil_range as CR.
  pose proof WF as (WE & WR & _ & WCH & (Q1 & _) & _). destruct (Q1 b Hb) as [(CV & _ & _ & _ & CAP & BSZ & _) _].
  pose proof (wf_env_thread _ WE) as (_ & _ & _ & WT4 & _). pose proof WE as (_ & WEhi & _ & _ & WEce & _). rewrite kHighMemBeg_val in WEhi.
  pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; clear; lia)) as (RG1 & RG2 & RG3 & _). cbv zeta in RG1, RG2, RG3. unfold region_of in RG1, RG2, RG3.
  change kFreeArrayOffset with 3758096384 in RG3.
  assert (SZ : 8192 <= b_size b).
  { rewrite BSZ. unfold kBatchSize. assert (0 <= fold_right (fun cb acc => chunk_used_size sx cb + acc) 0 (b_items b)); [| lia].
    clear -WCH. induction (b_items b) as [|y k IHk]; cbn; [lia|]. pose proof (chunk_used_size_nonneg E P [] sx y WCH). lia. }
  destruct CV as (k & K0 & KE & KB). unfold region_of in KB. change (class_size kBatchClass) with 8192 in KE, KB.
  unfold bok. rewrite KE. unfold region_beg, kBatchClass in *. change kRegionSize with 4294967296 in *. unfold kBatchCap in CAP. unfold zlen in CAP.
  clear -K0 KB RG1 RG3 G1 G2 G3 WT4 WEhi WEce CR LOC SZ CAP KE. rewrite <- KE. rewrite KE. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma wf_bapart : forall E P (sx : astate) l, AWf E P [] sx -> incl l (as_tq sx ++ as_gq sx) -> List.NoDup (map b_addr l) -> bapart l.
Proof.
  intros E P sx l WF INCL ND. pose proof WF as (WE & WR & _ & _ & (Q1 & _) & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  induction l as [|b l IH]; [exact I|]. cbn [map] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NIN ND'].
  split; [| apply IH; [intros y Hy; apply INCL; right; exact Hy| exact ND']].
  apply Forall_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as (b' & <- & Hb').
  destruct (Q1 b (INCL b (or_introl eq_refl))) as [(CV & _) _]. destruct (Q1 b' (INCL b' (or_intror Hb'))) as [(CV' & _) _].
  destruct (carved_blocks_disjoint E sx kBatchClass (b_addr b) kBatchClass (b_addr b') HB24 HB24 WR CV CV') as [[_ EQ]|D].
  - exfalso. apply NIN. rewrite EQ. apply in_map. exact Hb'.
  - unfold far. change (class_size kBatchClass) with 8192 in D. exact D.
Qed.

(* [comment removed for export] *)
Section DeallocT4.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaa518.
#[local] Notation PP := (AF_deallocT1.PP E0 FSB0 HR0).
#[local] Notation xfer_st := (AF_deallocT3.xfer_st).
#[local] Notation drainWu := (AF_deallocT3.drainWu E0).

(* [comment removed for export] *)
Definition rmerge (gq : list batch) : list batch * list batch :=
  if (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) then merge_batches gq else (gq, []).

(* [comment removed for export] *)
Definition FPW4 (gq5 : list batch) (lo : Z) (z : Z) : Prop :=
     lo <= z
  \/ (ae_instance E0 + kInsQMutex <= z < ae_instance E0 + kInsQMutex + 4)
  \/ (ae_instance E0 + kInsQGlobal <= z < ae_instance E0 + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (exists b, In b gq5 /\ b_addr b <= z < b_addr b + 8192).
Definition R4_stmt : Prop :=
  forall (a4 : astate) (m6 m8 : mem) (lo : Z) (gq1 emp popped kept : list batch),
  let gq5 := as_gq a4 ++ as_tq a4 in
  let a6 := upd_gq (fun _ => kept) (xfer_st a4) in
  as_tq a4 <> [] -> ARep asegs E0 (DepotR asegs E0) a4 m6 -> AWf E0 [] [] a4 -> AF_deallocT2.renv_ok E0 a4 ->
  wmono asegs m6 m8 -> (forall z, 0 <= z < 2^64 -> ~ FPW4 gq5 lo z -> m8 (wa z) = m6 (wa z)) -> alloc_ceiling <= lo ->
  rmerge gq5 = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  rw_cells asegs m8 (ae_instance E0 + kInsQMutex) [C4 (wz 0)] ->
  rw_cells asegs m8 (ae_instance E0 + kInsQGlobal) [C8 (wz (blen kept)); C8 (wz (bhd kept)); C8 (wz (blast kept)); C8 (wz (qbytes kept))] ->
  rw_cells asegs m8 (T + kThrQCache) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  bcells m8 kept -> bitemsl m8 kept ->
  ARep asegs E0 (DepotR asegs E0) a6 m8.
Hypothesis R4 : R4_stmt.

(* [comment removed for export] *)
Definition QDR_post (s : aps) (mo : Model) (m : mem) (usp lo cb B C C' : Z) (key : list Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
    forall (t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid : Z),
  let a := aps_alloc s in let n := cm_n cm in let a3 := AsanRepFlip.s3 a2 cb cm aid fid in
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep asegs E0 (DepotR asegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv asegs m6 -> stk asegs m6 lo (usp - 80) -> wmono asegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells asegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  kThreadQuarantineMax < tq_bytes a4 ->
  forall (m7 : mem) (mo7 : Model) (t0' t1' a4x a5x a6x a7x : word),
  kQuarantineMax < gq_bytes a4 + tq_bytes a4 ->
  mem_inv asegs m7 -> stk asegs m7 lo (usp - 80) -> wmono asegs m6 m7 -> munch (drainWu usp (as_gq a4)) m6 m7 ->
  magree mo6 mo7 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo7 ->
  rw_cells asegs m7 0xaa888 [C4 (wz 256)] ->
  rw_cells asegs m7 0xaa890 [C8 (wz (qcount (as_gq a4) + qcount (as_tq a4))); C8 (wz (match as_gq a4 with [] => list_first (as_tq a4) | _ => list_first (as_gq a4) end));
                          C8 (wz (list_last (as_tq a4))); C8 (wz (gq_bytes a4 + tq_bytes a4))] ->
  rw_cells asegs m7 (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall l0 b0, as_gq a4 = l0 ++ [b0] -> rw_cells asegs m7 (b_addr b0) [C8 (wz (list_first (as_tq a4)))]) ->
  forall (m8 : mem) (mo8 : Model) (gq1 emp popped kept : list batch) (t0x t1x t2x a4y a5y a6y a7y t3x t4x t5x x8 x9 x18 x19 x20 : word),
  let gq5 := as_gq a4 ++ as_tq a4 in let a5 := xfer_st a4 in let D := emp ++ popped in
  rmerge gq5 = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  mem_inv asegs m8 -> stk asegs m8 lo (usp - 160) -> munch (rheadW (usp - 80) gq5) m7 m8 -> wmono asegs m7 m8 ->
  magree mo7 mo8 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo8 ->
  rw_cells asegs m8 0xaa888 [C4 (wz 0)] ->
  rw_cells asegs m8 0xaa890 [C8 (wz (blen kept)); C8 (wz (bhd kept)); C8 (wz (blast kept)); C8 (wz (qbytes kept))] ->
  bcells m8 kept -> bitemsl m8 kept ->
  rw_cells asegs m8 (usp - 160) [C8 (wz (blen D)); C8 (wz (bhd D)); C8 (wz (blast D)); C8 (wz (qbytes D));
                                 C8 (wz (T + 208)); C8 (wz B); C8 (wz n); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x36fe8)] ->
  bcells m8 D -> bitemsl m8 D -> qbytes kept <= kQuarantineMin ->
  Forall (bok lo T) (kept ++ D) -> bapart (kept ++ D) -> (forall b, In b (kept ++ D) -> In (b_addr b) (map b_addr gq5)) ->
  realizes_cfg acfg asegs
    (mkCfg (MS (mkR (wz 0x34b28) (wz (usp - 160)) gp tp t0x t1x t2x x8 x9 (wz (INST + 728)) (wz (usp - 160)) (wz (T + 208)) (wz B) a4y a5y a6y a7y
                    x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3x t4x t5x t6) F (wz 0x34d20) fc None m8 (seg_rom asegs)) mo8) K.

(* [comment removed for export] *)
Lemma views_xfer : forall (m6 m7 : mem) (usp lo : Z) (gq tq : list batch),
  bcells m6 tq -> bitemsl m6 tq -> bcells m6 gq -> bitemsl m6 gq ->
  Forall (bok lo T) (gq ++ tq) -> bapart (gq ++ tq) -> lo <= usp - 128 ->
  munch (drainWu usp gq) m6 m7 -> wmono asegs m6 m7 ->
  (forall l0 b0, gq = l0 ++ [b0] -> rw_cells asegs m7 (b_addr b0) [C8 (wz (list_first tq))]) ->
  bcells m7 (gq ++ tq) /\ bitemsl m7 (gq ++ tq).
Proof.
  intros m6 m7 usp lo gq tq BCt BIt BCg BIg OK AP LO MU WM GLB.
  assert (OKf : forall b, In b (gq ++ tq) -> bok lo T b) by (apply Forall_forall; exact OK).
  destruct (snoc_case gq) as [Eg|(l0 & b0 & Eg)].
  - (* [comment removed for export] *)
    rewrite Eg in *. cbn [app] in *.
    assert (DJ : forall b off k, In b tq -> 0 <= off -> off + k <= 8192 -> disjoint_from (drainWu usp []) (b_addr b + off) k).
    { intros b off k Hb H1 H2. pose proof (OKf b Hb) as (B1 & B2 & B3 & _). unfold drainWu. cbn [disjoint_from app].
      clear -B1 B2 B3 H1 H2 LO. repeat split; lia. }
    split.
    + eapply bcellsn_transport; [exact BCt| exact MU| exact WM|]. apply Forall_forall. intros b Hb.
      replace (b_addr b) with (b_addr b + 0) by (clear; lia). apply DJ; [exact Hb| clear; lia| clear; lia].
    + eapply bitemsl_transport; [exact BIt| exact MU| exact WM|]. apply Forall_forall. intros b Hb. apply DJ; [exact Hb| clear; lia| clear; lia].
  - pose proof (GLB l0 b0 Eg) as G7.
    assert (FAR : forall b, In b (l0 ++ tq) -> far (b_addr b0) (b_addr b)).
    { intros b Hb. rewrite Eg in AP. rewrite <- app_assoc in AP. apply bapart_app in AP. destruct AP as (AP1 & AP2 & AP3).
      apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - apply far_sym. apply AP3; [exact Hb| left; reflexivity].
      - cbn [app] in AP2. exact (bapart_hd b0 tq b AP2 Hb). }
    assert (DJ : forall b off k, In b (gq ++ tq) -> 0 <= off -> off + k <= 8192 -> (b = b0 -> 8 <= off) ->
                 disjoint_from (drainWu usp gq) (b_addr b + off) k).
    { intros b off k Hb H1 H2 H3. pose proof (OKf b Hb) as (B1 & B2 & B3 & _). unfold drainWu. rewrite Eg. rewrite list_last_snoc.
      assert (X : b_addr b + off + k <= b_addr b0 \/ b_addr b0 + 8 <= b_addr b + off).
      { rewrite Eg, <- app_assoc in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        - pose proof (FAR b ltac:(apply in_app_iff; left; exact Hb)) as F. unfold far in F. clear -F H1 H2. lia.
        - destruct Hb as [<-|Hb]; [specialize (H3 eq_refl); clear -H3 H1 H2; lia|].
          pose proof (FAR b ltac:(apply in_app_iff; right; exact Hb)) as F. unfold far in F. clear -F H1 H2. lia. }
      destruct l0; cbn [disjoint_from app]; clear -B1 B2 B3 H1 H2 LO X; repeat split; lia. }
    split.
    + apply (proj2 (bcellsn_app m7 gq tq 0)). split.
      * rewrite Eg. apply (proj2 (bcellsn_app m7 l0 [b0] _)). cbn [bhd_or bcellsn].
        rewrite Eg in BCg. apply (proj1 (bcellsn_app m6 l0 [b0] 0)) in BCg. cbn [bhd_or bcellsn] in BCg. destruct BCg as [BCl [Bb0 _]].
        split.
        -- eapply bcellsn_transport; [exact BCl| exact MU| exact WM|]. apply Forall_forall. intros b Hb.
           replace (b_addr b) with (b_addr b + 0) by (clear; lia). apply DJ; [rewrite Eg; apply in_app_iff; left; apply in_app_iff; left; exact Hb| clear; lia| clear; lia|].
           intros ->. exfalso. pose proof (FAR b0 ltac:(apply in_app_iff; left; exact Hb)) as F. unfold far in F. clear -F. lia.
        -- split; [| exact I]. pose proof (rwc_split asegs m6 (b_addr b0) [C8 (wz 0)] [C8 (wz (b_size b0)); C8 (wz (bcnt b0))] Bb0) as [_ Bb8]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Bb8.
           assert (Bb8' : rw_cells asegs m7 (b_addr b0 + 8) [C8 (wz (b_size b0)); C8 (wz (bcnt b0))]).
           { eapply rw_cells_transport; [exact Bb8| exact MU| exact WM|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
             apply DJ; [rewrite Eg; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia| clear; lia]. }
           pose proof (rwc_join_at asegs m7 (b_addr b0) (b_addr b0 + 8) _ _ G7 Bb8' eq_refl) as J. cbn [app] in J.
           replace (bhd_or tq 0) with (list_first tq); [exact J|]. destruct tq; reflexivity.
      * eapply bcellsn_transport; [exact BCt| exact MU| exact WM|]. apply Forall_forall. intros b Hb.
        replace (b_addr b) with (b_addr b + 0) by (clear; lia). apply DJ; [apply in_app_iff; right; exact Hb| clear; lia| clear; lia|].
        intros ->. exfalso. pose proof (FAR b0 ltac:(apply in_app_iff; right; exact Hb)) as F. unfold far in F. clear -F. lia.
    + apply (proj2 (bitemsl_app m7 gq tq)). split.
      * eapply bitemsl_transport; [exact BIg| exact MU| exact WM|]. apply Forall_forall. intros b Hb.
        apply DJ; [apply in_app_iff; left; exact Hb| clear; lia| clear; lia| clear; lia].
      * eapply bitemsl_transport; [exact BIt| exact MU| exact WM|]. apply Forall_forall. intros b Hb.
        apply DJ; [apply in_app_iff; right; exact Hb| clear; lia| clear; lia| clear; lia].
Qed.

(* [comment removed for export] *)
Lemma recycle_head_srz :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (lo B C C' : Z) (key : list Z) (K : TSet)
         (t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 : word) (m6 : mem) (mo6 : Model) (a2 a4 : astate) (cm : chunkmeta) (aid fid cb : Z)
         (m7 : mem) (mo7 : Model) (t0' t1' a4x a5x a6x a7x : word),
  let a := aps_alloc s in let usp := bv_unsigned sp in let n := cm_n cm in let a3 := AsanRepFlip.s3 a2 cb cm aid fid in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> fbudget_pre a -> In (cb + 16, n) (live_blocks a) ->
  alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e0b10 ->
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 ->
  (exists fuel orc evs orc', arun fuel (depot_put E0 key (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> dsame (upd_ts (ts_on_free n) a) a2 -> as_ndepot_ins a2 = as_ndepot_ins a + 1 ->
  (exists fuel orc evs orc', arun fuel (enqueue E0 cb n a3) orc = Some (a4, ONorm tt, evs, orc')) ->
  as_chunks a4 = as_chunks a3 /\ as_sec a4 = as_sec a /\ as_ptr_committed a4 = as_ptr_committed a /\ as_gq a4 = as_gq a
  /\ as_nprim_ever a4 = as_nprim_ever a /\ as_residue a4 = as_residue a /\ as_ndepot_ins a4 = as_ndepot_ins a2
  /\ as_node_blocks a4 = as_node_blocks a2 /\ as_store_blocks a4 = as_store_blocks a2 /\ as_sec_stats a4 = as_sec_stats a ->
  AWf E0 [] [] a4 -> ARep asegs E0 (DepotR asegs E0) a4 m6 -> AKern E0 a4 mo6 ->
  RTOKc (C - 1) (C' - DSLACK) (sA a4 s) mo6 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo6 ->
  res_ok a4 -> gq_bytes a4 <= kQuarantineMax -> 0 <= tq_bytes a4 <= kThreadQuarantineMax + 2^28 -> depot_inv E0 a4 -> sstats_ok a4 -> csmall a4 ->
  m_fs mo6 = m_fs mo -> m_fds mo6 = m_fds mo -> m_tid mo6 = m_tid mo ->
  mem_inv asegs m6 -> stk asegs m6 lo (usp - 80) -> wmono asegs m m6 -> rt_misc5 FSB0 PL0 E0 m6 ->
  (exists W, munch W m m6 /\ Forall (aw_ok E0 a a4 lo usp) W
             /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (cb + 16, n) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W) ->
  rw_cells asegs m6 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m6 (T + 80) [C8 (wz (qcount (as_tq a4))); C8 (wz (list_first (as_tq a4))); C8 (wz (list_last (as_tq a4))); C8 (wz (tq_bytes a4))] ->
  kThreadQuarantineMax < tq_bytes a4 ->
  kQuarantineMax < gq_bytes a4 + tq_bytes a4 ->
  mem_inv asegs m7 -> stk asegs m7 lo (usp - 80) -> wmono asegs m6 m7 -> munch (drainWu usp (as_gq a4)) m6 m7 ->
  magree mo6 mo7 -> KIA (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) mo7 ->
  rw_cells asegs m7 0xaa888 [C4 (wz 256)] ->
  rw_cells asegs m7 0xaa890 [C8 (wz (qcount (as_gq a4) + qcount (as_tq a4))); C8 (wz (match as_gq a4 with [] => list_first (as_tq a4) | _ => list_first (as_gq a4) end));
                          C8 (wz (list_last (as_tq a4))); C8 (wz (gq_bytes a4 + tq_bytes a4))] ->
  rw_cells asegs m7 (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall l0 b0, as_gq a4 = l0 ++ [b0] -> rw_cells asegs m7 (b_addr b0) [C8 (wz (list_first (as_tq a4)))]) ->
  (* [comment removed for export] *)
  QDR_post s mo m usp lo cb B C C' key ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg asegs
    (mkCfg (MS (mkR (wz 0x36fe8) (wz (usp - 80)) gp tp t0' t1' t2 (wz (INST + 728)) (wz (T + 80)) (wz (INST + 728)) (wz kQuarantineMin) (wz (T + 208)) (wz B) a4x a5x a6x a7x
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x349b8) fc None m7 (seg_rom asegs)) mo7) K.
Proof.
  intros until a7x. cbv zeta. intros KN TOK HC1 HCS AIV FB LIVE LOC LO SPA SPH TP.
  intros Hcm ST UB RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6 GT.
  intros GTQ MI7 SK7 WM7 MU7 AG7 KIA7 QM7 GQ7 QC7 GLB7 QDRPOST.
  pose proof alloc_ceiling_range as CR. pose proof A_bundle.kHighMemBeg_val as KHB.
  set (a := aps_alloc s) in *. set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  unfold K_FREE in LO.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  (* [comment removed for export] *)
  pose proof (magree_frame _ _ AG7) as (Ffds7 & Fvm7 & Flz7 & Ffs7 & Fh7 & Ftid7 & _).
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG7 KIA7) as TOK7. pose proof (AKern_frame _ _ _ _ Fvm7 Flz7 AK4) as AK7.
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK7) as (R7 & R7' & ATK7 & _).
  assert (ENV4 : ENVOK E0 FSB0 (sA a4 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK7).
  pose proof (proj1 WF4) as WE4. pose proof WF4 as (_ & WR4 & _ & _ & (Q1 & _) & _).
  set (P7 := PP (sA a4 s) mo7).
  pose proof (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a4 s) mo7 R7 R7' ATK7) as KIP7.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp - 80 -> P7 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P7. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a4 s) mo7 AK7 WE4 ENV0); clear -H1 H2 LOC USPR CR; lia. }
  assert (PDAT : forall y k, 0xa4000 <= y -> y + Z.of_nat k <= 0x603000 -> P7 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P7. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 (sA a4 s) mo7 AK7 WE4 ENV4 ENV0); clear -H1 H2; lia. }
  assert (PUSR : forall y k, region_beg SB kBatchClass <= y -> y + Z.of_nat k <= region_beg SB kBatchClass + rg_mapped_user (get_region a4 kBatchClass) -> P7 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P7. rewrite <- EPOL.
    apply (pol_user E0 FSB0 HR0 (sA a4 s) mo7 [] [] AK7 WF4 kBatchClass); [unfold kBatchClass, kLargestClassID; clear; lia| exact H1| exact H2| clear; lia]. }
  assert (Hsp : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; clear -USPR LO LOC CR; lia).
  (* [comment removed for export] *)
  pose proof (ak_resv_geom _ _ _ AK4) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  destruct (proj2 WR4 kBatchClass ltac:(unfold kBatchClass, kLargestClassID; clear; lia)) as (RG1' & RG2' & RG3' & _).
  cbv zeta in RG1', RG2', RG3'. unfold region_of in RG1', RG2', RG3'. change kFreeArrayOffset with 3758096384 in RG3'.
  assert (BLK : forall bb, carved E0 a4 kBatchClass bb ->
            region_beg SB kBatchClass <= bb /\ bb + 8192 <= region_beg SB kBatchClass + rg_mapped_user (get_region a4 kBatchClass)).
  { intros bb (k & K0 & KE & KB). unfold region_of in KB. change (class_size kBatchClass) with 8192 in KE, KB.
    unfold region_beg, kBatchClass in *. change kRegionSize with 4294967296 in *.
    clear -K0 KE KB RG1' RG3' G1 G2 G3 CR. repeat split; lia. }
  (* [comment removed for export] *)
  set (ax5 := xfer_st a4).
  assert (WF5 : AWf E0 [] [] ax5) by exact (AWf_transfer E0 [] [] a4 WF4).
  assert (AK5 : AKern E0 ax5 mo7) by (apply (AKern_ext E0 a4); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK7]).
  assert (E5 : as_tq ax5 ++ as_gq ax5 = as_gq a4 ++ as_tq a4) by reflexivity.
  set (gq5 := as_gq a4 ++ as_tq a4) in *.
  assert (OK5 : Forall (bok lo T) gq5).
  { apply Forall_forall. intros b Hb. apply (wf_bok E0 [] ax5 mo7 lo WF5 AK5 LOC b). rewrite E5. exact Hb. }
  assert (AP5 : bapart gq5).
  { apply (wf_bapart E0 [] ax5 gq5 WF5); [rewrite E5; intros y Hy; exact Hy|].
    pose proof WF5 as (_ & _ & _ & _ & (_ & _ & ND5 & _) & _). unfold all_batches in ND5. cbn [as_tq ax5 xfer_st upd_tq upd_gq app] in ND5. rewrite app_nil_r in ND5. exact ND5. }
  (* [comment removed for export] *)
  pose proof (gq_weights E0 [] [] a4 WF4) as [WG WT]. unfold kBatchSize in WG, WT. unfold kThreadQuarantineMax in GT, TQ4. unfold kQuarantineMax in GQ4, GTQ.
  set (cnt := qcount (as_tq a4)) in *. set (gcnt := qcount (as_gq a4)) in *.
  assert (TQNE : as_tq a4 <> []) by (intros E; unfold tq_bytes in GT; rewrite E in GT; cbn in GT; clear -GT; lia).
  assert (Eblen : blen gq5 = gcnt + cnt) by (subst gq5 gcnt cnt; unfold qcount; rewrite length_app; clear; lia).
  assert (Ebhd : bhd gq5 = match as_gq a4 with [] => list_first (as_tq a4) | _ => list_first (as_gq a4) end).
  { subst gq5. destruct (as_gq a4); [cbn [app]; apply bhd_first| reflexivity]. }
  assert (Eblast : blast gq5 = list_last (as_tq a4)) by (subst gq5; rewrite (blast_app _ _ TQNE); apply blast_last).
  assert (Eqb : qbytes gq5 = gq_bytes a4 + tq_bytes a4) by (subst gq5; rewrite qbytes_app; reflexivity).
  (* [comment removed for export] *)
  pose proof REP4 as (_ & _ & _ & _ & _ & _ & [RBt RBg] & _).
  destruct (arep_batch_list_views a4 (as_tq a4) m6 RBt) as [BCt BIt]. destruct (arep_batch_list_views a4 (as_gq a4) m6 RBg) as [BCg BIg].
  destruct (views_xfer m6 m7 usp lo (as_gq a4) (as_tq a4) BCt BIt BCg BIg OK5 AP5 ltac:(clear -LO; lia) MU7 WM7 GLB7) as [BC7 BI7].
  fold gq5 in BC7, BI7.
  assert (GQ7' : rw_cells asegs m7 0xaa890 [C8 (wz (blen gq5)); C8 (wz (bhd gq5)); C8 (wz (blast gq5)); C8 (wz (qbytes gq5))]).
  { rewrite Eblen, Ebhd, Eblast, Eqb. exact GQ7. }
  assert (PQB : forall b y k, In b gq5 -> b_addr b <= y -> y + Z.of_nat k <= b_addr b + 8192 -> P7 (Z_to_bv 64 y, k)).
  { intros b y k Hb H1 H2. pose proof WF5 as (_ & _ & _ & _ & (Q5 & _) & _). rewrite E5 in Q5. destruct (Q5 b Hb) as [(CVb & _) _].
    destruct (BLK (b_addr b) CVb) as [L1 L2]. apply PUSR; [clear -H1 L1; lia| clear -H2 L2; lia]. }
  assert (HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling) by (clear -Tlo Thi Timg; repeat split; lia).
  assert (HMIN : 0 <= kQuarantineMin < 2^40) by (unfold kQuarantineMin; clear; lia).
  assert (LENL : blen gq5 < 2^40) by (rewrite Eblen; clear -WG WT GQ4 TQ4; lia).
  assert (QBL : 8192 * qbytes gq5 < 2^60) by (rewrite Eqb; clear -GQ4 TQ4; lia).
  set (DQh := fun ms8 : machine_state =>
       exists (m8 : mem) (gq1 emp popped kept : list batch) (t0x t1x t2x a4y a5y a6y a7y t3x t4x t5x x8 x9 x18 x19 x20 : word),
         ms8 = MS (mkR (wz 0x34b28) (wz (usp - 160)) gp tp t0x t1x t2x x8 x9 (wz (INST + 728)) (wz (usp - 160)) (wz (T + 208)) (wz B) a4y a5y a6y a7y
                       x18 x19 x20 (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3x t4x t5x t6) F (wz 0x34d20) fc None m8 (seg_rom asegs)
         /\ rmerge gq5 = (gq1, emp) /\ pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept)
         /\ mem_inv asegs m8 /\ stk asegs m8 lo (usp - 160) /\ munch (rheadW (usp - 80) gq5) m7 m8 /\ wmono asegs m7 m8
         /\ rw_cells asegs m8 0xaa888 [C4 (wz 0)]
         /\ rw_cells asegs m8 0xaa890 [C8 (wz (blen kept)); C8 (wz (bhd kept)); C8 (wz (blast kept)); C8 (wz (qbytes kept))]
         /\ bcells m8 kept /\ bitemsl m8 kept
         /\ rw_cells asegs m8 (usp - 160) [C8 (wz (blen (emp ++ popped))); C8 (wz (bhd (emp ++ popped))); C8 (wz (blast (emp ++ popped))); C8 (wz (qbytes (emp ++ popped)));
                                        C8 (wz (T + 208)); C8 (wz B); C8 (wz (cm_n cm)); C8 (wz (T + 80)); C8 (wz (INST + 728)); C8 (wz 0x36fe8)]
         /\ bcells m8 (emp ++ popped) /\ bitemsl m8 (emp ++ popped) /\ qbytes kept <= kQuarantineMin
         /\ Forall (bok lo T) (kept ++ (emp ++ popped)) /\ bapart (kept ++ (emp ++ popped))
         /\ (forall b, In b (kept ++ (emp ++ popped)) -> In (b_addr b) (map b_addr gq5))).
  eapply (rzA_seg_cfg asegs (aSc (sA a4 s)) (aNc (sA a4 s)) (aEBc (sA a4 s)) P7 DQh).
  { replace (INST + 728) with 698352 by reflexivity.
    eapply (recycle_head P7 ra gp tp (wz 698352) (wz (T + 80)) (wz (cm_n cm)) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DQh
              (usp - 80) lo T kQuarantineMin LOC ltac:(clear -LO; lia) ltac:(clear -SPH LO LOC CR; lia) HT HMIN PSTK PDAT
              gq5 m7 (wz 0x36fe8) t0' t1' t2 (wz (T + 208)) (wz B) a4x a5x a6x a7x OK5 AP5 LENL QBL PQB MI7 SK7 QM7 GQ7' BC7 BI7).
    intros m8 gq1 emp popped kept t0x t1x t2x a4y a5y a6y a7y t3x t4x t5x x8 x9 x18 x19 x20 MRG POP MI8 SK8 MU8 WM8 QM8 GQ8 BCk BIk FR8 BCd BId QK OK8 AP8 SUB8.
    replace (usp - 80 + -80) with (usp - 160) in * by (clear; lia).
    apply evtA_done. unfold DQh. exists m8, gq1, emp, popped, kept, t0x, t1x, t2x, a4y, a5y, a6y, a7y, t3x, t4x, t5x, x8, x9, x18, x19, x20.
    replace (INST + 728) with 698352 by reflexivity.
    repeat match goal with |- _ /\ _ => split end; try assumption. reflexivity. }
  { exact KIP7. }
  intros ms8 mo8 HQ8 AG8 KIP8. unfold DQh in HQ8.
  destruct HQ8 as (m8 & gq1 & emp & popped & kept & t0x & t1x & t2x & a4y & a5y & a6y & a7y & t3x & t4x & t5x & x8 & x9 & x18 & x19 & x20 & -> &
                   MRG & POP & MI8 & SK8 & MU8 & WM8 & QM8 & GQ8 & BCk & BIk & FR8 & BCd & BId & QK & OK8 & AP8 & SUB8).
  destruct KIP8 as [KIA8 _].
  eapply (QDRPOST t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 t3 t4 t5 t6 m6 mo6 a2 a4 cm aid fid Hcm ST UB RUNd FID DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4
            RES4 ltac:(unfold kQuarantineMax; exact GQ4) ltac:(unfold kThreadQuarantineMax; exact TQ4) DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW PF6 QC6
            ltac:(unfold kThreadQuarantineMax; exact GT) m7 mo7 t0' t1' a4x a5x a6x a7x ltac:(unfold kQuarantineMax; exact GTQ) MI7 SK7 WM7 MU7 AG7 KIA7 QM7 GQ7 QC7 GLB7
            m8 mo8 gq1 emp popped kept t0x t1x t2x a4y a5y a6y a7y t3x t4x t5x x8 x9 x18 x19 x20
            MRG POP MI8 SK8 MU8 WM8 AG8 KIA8 QM8 GQ8 BCk BIk FR8 BCd BId QK OK8 AP8 SUB8).
Qed.

End DeallocT4.
End RC__1.
