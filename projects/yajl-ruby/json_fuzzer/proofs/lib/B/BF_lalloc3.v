(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow NodesA_mm BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed XB_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanRepFrame AsanFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lkit BF_kit BF_kit2 BF_unwind BF_poison BF_poison2 BF_swar BF_mmfix0 BF_mmfix1 BF_lalloc1 BF_lalloc2 B_base BF_place B_policy5 B_slack5 B_bundle B_benv5 B_mmchk5 B_balloc5 B_bpolicy5 B_bevents5 BF_grant.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import CompatE2 LiaA NodesA_mmW.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition lal_commit (a : astate) : astate :=
  if n_chunks a =? as_ptr_committed a then upd_ptr_committed (as_ptr_committed a + kChunksBlockCount) a else a.

Definition lal_state (a : astate) (mb msz need : Z) : astate :=
  let a1 := lal_commit (upd_ts (ts_on_mmap msz) a) in
  let idx := n_chunks a in
  upd_glob (fun x => x + msz) (fun x => x + msz)
    (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st + 1) (ss_n_frees st) (ss_cur st + msz) (Z.max (ss_max st) (ss_cur st + msz))
                                         (bump (ss_by_size_log st) (zlog2 msz) 1))
      (upd_sec_stale (delete idx)
        (upd_sec (fun l => l ++ [mkSec mb msz need])
          (upd_residue (fun r => r ++ residue_pages mb msz) a1)))).

(* [comment removed for export] *)
Definition lal_a2 (a : astate) (mb msz need : Z) : astate :=
  upd_sec (fun l => l ++ [mkSec mb msz need]) (upd_residue (fun r => r ++ residue_pages mb msz) a).
Definition lal_a3 (a : astate) (mb msz need : Z) : astate :=
  if n_chunks a =? as_ptr_committed a then upd_ptr_committed (as_ptr_committed a + kChunksBlockCount) (lal_a2 a mb msz need)
  else lal_a2 a mb msz need.

Lemma firstn_repeat' : forall {X} (x : X) k m, (k <= m)%nat -> firstn k (repeat x m) = repeat x k.
Proof. aceil. intros X x k. induction k as [|k IH]; intros [|m] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma skipn_repeat' : forall {X} (x : X) k m, skipn k (repeat x m) = repeat x (m - k).
Proof. aceil. intros X x k. induction k as [|k IH]; intros [|m]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_splitL : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.

Lemma AKern_ext' : forall E s s' mo,
  as_regions s' = as_regions s -> as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s ->
  AKern E s mo -> AKern E s' mo.
Proof. aceil.
  intros E s s' mo R P S NB SB K.
  assert (GR : forall c, get_region s' c = get_region s c) by (intros c; unfold get_region; rewrite R; reflexivity).
  destruct K; constructor; rewrite ?GR, ?P, ?S, ?NB, ?SB; auto.
  - intros c Hc. rewrite GR. auto.
  - intros c Hc. rewrite GR. auto.
  - intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; intros c Hc; rewrite GR; auto.
Qed.

Lemma lal_state_fp : forall a mb msz need, same_fp (lal_a3 a mb msz need) (lal_state a mb msz need).
Proof. aceil.
  intros a mb msz need. unfold lal_state, lal_a3, lal_a2, lal_commit, same_fp, regions_bytes.
  unfold n_chunks. cbn.
  destruct (Z.of_nat (length (as_sec a)) =? as_ptr_committed a); cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition dec_as (L lo : Z) (e : resp) : option (word * bool) :=
  match e with
  | mkEffectU r [] [] [] [] [] => if bv_eqb r (Z_to_bv 64 18446744073709551604) then Some (r, false) else None
  | mkEffectU r [] [z] [] [] [] =>
      if (bv_eqb (fst z) r && bv_eqb (snd z) (Z_to_bv 64 L) && (b_image_end <=? bv_unsigned r) && (bv_unsigned r + L <=? lo))%bool
      then Some (r, true) else None
  | _ => None
  end.

Lemma dec_as_ok : forall L lo, mod_dec_ok (dec_as L lo) (fun x r u => x = (r, u)) L lo.
Proof. aceil.
  intros L lo [r ws zs us cps ci] x D. unfold dec_as in D.
  destruct ws; [|discriminate]. destruct zs as [|[za zn] [|]]; destruct us; try discriminate; destruct cps; try discriminate; destruct ci; try discriminate.
  - destruct (bv_eqb r (Z_to_bv 64 18446744073709551604)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. injection D as <-.
    exists r, false. split; [reflexivity|]. split; [reflexivity|]. exact E.
  - cbn [fst snd] in D.
    destruct (bv_eqb za r) eqn:E1; [|discriminate]. destruct (bv_eqb zn (Z_to_bv 64 L)) eqn:E2; [|discriminate].
    destruct (Z.leb_spec b_image_end (bv_unsigned r)); [|discriminate]. destruct (Z.leb_spec (bv_unsigned r + L) lo); [|discriminate].
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. injection D as <-.
    exists r, true. split; [reflexivity|]. split; [reflexivity|]. split; assumption.
Qed.

Lemma dec_as_grant : forall L lo r, b_image_end <= bv_unsigned r -> bv_unsigned r + L <= lo ->
  dec_as L lo (mkEffectU r [] [(r, Z_to_bv 64 L)] [] [] []) = Some (r, true).
Proof. aceil.
  intros L lo r H1 H2. unfold dec_as. cbn [fst snd]. rewrite !(proj2 (bv_eqb_eq _ _) eq_refl).
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma dec_as_enomem : forall L lo, dec_as L lo (mkEffectU (Z_to_bv 64 18446744073709551604) [] [] [] [] []) = Some (Z_to_bv 64 18446744073709551604, false).
Proof. aceil. intros. unfold dec_as. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). reflexivity. Qed.

Lemma errno_enomem : forall r, errno_ret_in Mmap.mmap_errnos r = true -> r = Z_to_bv 64 18446744073709551604.
Proof. aceil.
  intros r H. unfold errno_ret_in, Mmap.mmap_errnos in H. cbn [existsb] in H. rewrite Bool.orb_false_r in H.
  apply bv_eqb_eq in H. subst r. apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma is_err_smallL : forall z, 0 <= z < 2^47 -> is_err (Z_to_bv 64 z) = false.
Proof. aceil. intros z Hz. unfold is_err. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia). apply Z.ltb_ge. lia. Qed.

Lemma errno_is_errL : forall r, errno_ret_in Mmap.mmap_errnos r = true -> is_err r = true.
Proof. aceil. intros r H. rewrite (errno_enomem r H). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u64s_zero : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof. aceil.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH.
  replace (8 * Datatypes.S k)%nat with (8 + 8 * k)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma u64arr_of_cb_zero : forall m A k,
  rw_cells bsegs m A [CB (8 * k) (repeat (Z_to_bv 8 0) (8 * k))] -> u64arr bsegs m A (repeat (Z_to_bv 64 0) k).
Proof. aceil.
  intros m A k [[WFc Hb] Hw]. split.
  - rewrite u64s_zero. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite repeat_length. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia. exact Hw.
Qed.

Lemma u64arr_of_cb_zeroZ : forall m A k, 0 <= k ->
  rw_cells bsegs m A [CB (Z.to_nat (8 * k)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * k)))] -> u64arr bsegs m A (repeat (Z_to_bv 64 0) (Z.to_nat k)).
Proof. aceil. intros m A k Hk H. rewrite (Z2Nat.inj_mul 8 k) in H by lia. change (Z.to_nat 8) with 8%nat in H. apply u64arr_of_cb_zero. exact H. Qed.

(* [comment removed for export] *)
Lemma acc_ok_lazy_sub : forall Lz Lz' (Sa Sb : word -> Prop) x,
  (forall e', In e' Lz' -> exists e, In e Lz /\ elo e <= elo e' /\ ehi e' <= ehi e) ->
  (forall w, Sa w -> Sb w) -> acc_ok Lz Sa x -> acc_ok Lz' Sb x.
Proof. aceil.
  intros Lz Lz' Sa Sb x SUB HS [[NW O]|[NW IN]].
  - left. split; [exact NW|]. intros lo sz Hin. destruct (SUB _ Hin) as ([lo0 sz0] & Hin0 & L1 & L2).
    unfold elo, ehi in L1, L2. cbn [fst snd] in L1, L2. pose proof (O lo0 sz0 Hin0). lia.
  - right. split; [exact NW| intros k Hk; apply HS, IN, Hk].
Qed.

Section LAL.
(* [comment removed for export] *)
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0.
Hypothesis GS_L0 : In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0.
Hypothesis HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0.
Hypothesis RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0.
Hypothesis RES0_cover : forall x, 0x10000 <= x < 0x603000 -> exists e, In e RES0 /\ elo e <= x < ehi e.
Hypothesis RSVD : forall rr x, In rr (ae_reserved E0) -> fst rr <= x < fst rr + snd rr ->
  (exists e, In e (RES0 ++ L0) /\ elo e <= x < ehi e) \/ alloc_ceiling <= x.
Hypothesis RSVD_pos : Forall (fun rr => 0 < snd rr) (ae_reserved E0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).

(* [comment removed for export] *)
Variables (s : aps) (Pq : list Z) (Dq : list batch) (need : Z).
#[local] Notation a := (aps_alloc s).
Hypothesis WF : AWf E0 Pq Dq a.
Hypothesis RESOK : res_ok a.
Hypothesis NEED : 0x10000 < need /\ need mod 8 = 0 /\ need <= 2^27 + 2^12.
Hypothesis NCH : n_chunks a < kChunksBlockCount.
#[local] Notation msz := (lal_msz need).
#[local] Notation PA := (ae_ptr_array E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation n := (n_chunks a).
#[local] Notation ptrc := (as_ptr_committed a).

(* [comment removed for export] *)
Variables (ws bsl : list word) (na nf cur mx ga gm tmm tmd : Z) (TSD CTX r0 rl : Z).
Hypothesis LWS : length ws = Z.to_nat ptrc.
Hypothesis LBSL : length bsl = 64%nat.
Hypothesis HV : 0 <= na < 2^64 /\ 0 <= nf < 2^64 /\ 0 <= cur /\ cur + msz < 2^64 /\ 0 <= mx < 2^64 /\ 0 <= ga < 2^64 /\ 0 <= gm < 2^64.
Hypothesis HVT : 0 <= tmm < 2^64 /\ 0 <= tmd < 2^64.     (* [comment removed for export] *)
Hypothesis HT1 : 0x5d0810 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
(* [comment removed for export] *)
Hypothesis HC : resv_range_ok E0 r0 rl /\ r0 <= CTX /\ CTX + 160 <= r0 + rl.
Hypothesis HC4 : CTX + 4096 <= alloc_ceiling.           (* [comment removed for export] *)
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTR : placed_s T 4096.

(* [comment removed for export] *)
Definition lal_statics (m : mem) : Prop :=
  statics m /\ poison_globals m
  /\ rw_cells bsegs m GOT_SECNAME [C8 (Z_to_bv 64 V_SECNAME)] /\ rw_cells bsegs m V_SECNAME [C8 (Z_to_bv 64 A_SECNAME)].

Lemma lal_statics_agree : forall m m', lal_statics m -> (forall x, 0xa5000 <= x < 0x140810 -> m' (wa x) = m (wa x)) -> lal_statics m'.
Proof. aceil.
  intros m m' (ST & PG & G1 & G2) AG.
  Ltac agx AG H := eapply (rw_cells_agree bsegs); [| exact H]; cbn; intros x Hx; apply AG; clear -Hx; aceil; lia.
  unfold lal_statics, statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG, GOT_SECNAME, V_SECNAME in *.
  destruct ST as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  split; [| split; [eapply poison_globals_agree; [exact PG| intros; apply AG; lia]| split; [agx AG G1| agx AG G2]]].
  split; [agx AG S1|]. split; [agx AG S2|]. split; [agx AG S3|]. split; [agx AG S4|]. split; [agx AG S5|]. split; [agx AG S6| agx AG S7].
Qed.

Lemma lal_statics_agree2 : forall m m', lal_statics m ->
  (forall x, 0xa5000 <= x < 0x140810 -> x < 0xaaf40 \/ 0xab240 <= x -> m' (wa x) = m (wa x)) -> lal_statics m'.
Proof. aceil.
  intros m m' (ST & PG & Y1 & Y2) AG.
  unfold lal_statics, statics, poison_globals, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG, GOT_SECNAME, V_SECNAME in *.
  destruct ST as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  Ltac agy AG H := eapply (rw_cells_agree bsegs); [| exact H]; cbn; intros x Hx; apply AG; clear -Hx; aceil; lia.
  split; [| split; [| split; [agy AG Y1| agy AG Y2]]].
  - split; [agy AG S1|]. split; [agy AG S2|]. split; [agy AG S3|]. split; [agy AG S4|]. split; [agy AG S5|]. split; [agy AG S6| agy AG S7].
  - split; [agy AG G1|]. split; [agy AG G2|]. split; [agy AG G3|]. split; [agy AG G4|]. split; [agy AG G5|]. split; [agy AG G6| agy AG G7].
Qed.

(* [comment removed for export] *)
Definition fresh_shadow_ok (m : mem) (mo : Model) : Prop :=
  forall mo1 (r : word) (L : Z), magree mo mo1 ->
    region_free (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1)) r (Z_to_bv 64 L) = true ->
    placed (bv_unsigned r) L -> (forall rr, In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r) ->
    bv_unsigned r mod 4096 = 0 -> L mod 4096 = 0 -> 0 < L ->
    rw_cells bsegs m (kShadowBase + bv_unsigned r / 8) [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))].

Lemma acc_ok_monoS : forall Lz (S S' : word -> Prop) x, (forall w, S w -> S' w) -> acc_ok Lz S x -> acc_ok Lz S' x.
Proof. aceil. intros Lz S S' x HS [O|[NW IN]]; [left; exact O| right]. split; [exact NW|]. intros k Hk. apply HS, IN, Hk. Qed.

Lemma aS_app_mono : forall mb needx w, aSc s w -> aSc (sA (lal_a2 a mb msz needx) s) w.
Proof. aceil.
  intros mb needx w [M C]. unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores, lal_a2 in *. cbn [aps_alloc aps_env aps_fsbase] in *. cbn.
  split; [exact M|].
  destruct C as [C|[(sc & Hsc & C)|[C|C]]]; [left; exact C| right; left| right; right; left| right; right; right; exact C].
  - exists sc. split; [apply in_or_app; left; exact Hsc| exact C].
  - apply in_or_app. left. exact C.
Qed.

Lemma res_ok_a2 : forall mb needx, res_ok (lal_a2 a mb msz needx).
Proof. aceil.
  intros mb needx sc Hsc. unfold lal_a2 in *. cbn in *. apply in_app_iff in Hsc as [Hsc|[<-|[]]].
  - intros p Hp. apply in_or_app. left. exact (RESOK sc Hsc p Hp).
  - intros p Hp. apply in_or_app. right. exact Hp.
Qed.

(* [comment removed for export] *)
Definition lal_W (usp mb : Z) (first : bool) : list (Z * Z) :=
  [(usp - 720, usp); (0xab200, 0xab204); (0xaafc8, 0xaafd9); (0xaafe0, 0xaafe8); (0xaaff0, 0xab000);
   (0xab000 + 8 * Z.log2 msz, 0xab000 + 8 * Z.log2 msz + 8); (0xab218, 0xab228);
   (T + 2872, T + 2888); (mb, mb + msz); (kShadowBase + mb / 8, kShadowBase + mb / 8 + msz / 8)]
  ++ (if first then [(PA, PA + kPtrArrayCommit)] else [(PA + 8 * n, PA + 8 * n + 8)]).

(* [comment removed for export] *)
Definition lal_gcost : Z := msz + NMAXA + 4095.

Definition lal_post_ok (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (mo mo' : Model) (R R' : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (mb : Z) (hj' : list byte) (bsl' ws' : list word),
    let first := (n =? ptrc) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mb + 4096)) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch (lal_W (bv_unsigned sp) mb first) m m' /\ wmono bsegs m m'
    /\ mb mod 4096 = 0 /\ placed mb msz                                                     (* [comment removed for export] *)
    /\ (forall rr, In rr (ae_reserved E0) -> mb + msz <= fst rr \/ fst rr + snd rr <= mb)  (* [comment removed for export] *)
    /\ ranges_free (known_ranges E0 a) mb msz = true /\ in_primary (ae_space_beg E0) mb = false /\ in_primary (ae_space_beg E0) (mb + msz - 1) = false
    /\ (mb mod kPageSize =? 0) && (0 <? mb) && (mb + msz <=? alloc_ceiling) && ranges_free (known_ranges E0 a) mb msz = true    (* [comment removed for export] *)
    /\ app_mem_b mb msz && negb (in_primary (ae_space_beg E0) mb) && negb (in_primary (ae_space_beg E0) (mb + msz - 1)) && (mb + msz <=? kHighMemEnd + 1) = true
    /\ rw_cells bsegs m' 0xab200 [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xaafc8 [C8 (Z_to_bv 64 (as_ptr_committed (lal_a3 a mb msz need))); C8 (Z_to_bv 64 (n + 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0xaafe0 [C8 (Z_to_bv 64 (na + 1)); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 (cur + msz)); C8 (Z_to_bv 64 (Z.max mx (cur + msz)))]
    /\ u64arr bsegs m' 0xab000 bsl' /\ length bsl' = 64%nat
    /\ rw_cells bsegs m' 0xab218 [C8 (Z_to_bv 64 (ga + msz)); C8 (Z_to_bv 64 (gm + msz))]
    /\ u64arr bsegs m' PA ws' /\ ws' = upd (if first then repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount) else ws) (Z.to_nat n) (Z_to_bv 64 mb)
    /\ rw_cells bsegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 need); C8 (Z_to_bv 64 n)]
    /\ rw_cells bsegs m' (mb + 32) [CB (Z.to_nat (msz - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (msz - 32)))]
    /\ rw_cells bsegs m' (kShadowBase + mb / 8) [CB 512%nat (repeat (Z_to_bv 8 250) 512%nat)]
    /\ rw_cells bsegs m' (kShadowBase + mb / 8 + 512) [CB (Z.to_nat (need / 8)) hj']
    /\ rw_cells bsegs m' (kShadowBase + (mb + 4096 + need) / 8) [CB (Z.to_nat ((msz - 4096 - need) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((msz - 4096 - need) / 8)))]
    /\ rw_cells bsegs m' (T + 2872) [C8 (Z_to_bv 64 (tmm + 1)); C8 (Z_to_bv 64 (tmd + msz))]
    /\ lal_statics m'
    /\ ATOKc (R - cost2 msz - (if first then 32 else 0)) (R' - lal_gcost) (sA (lal_state a mb msz need) s) mo' /\ AKern E0 (lal_state a mb msz need) mo'
    /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo.

Theorem lalloc_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (usp lo R R' : Z) (K : TSet),
  K [] ->
  ATOKc R R' s mo -> AKern E0 a mo -> cost2 msz + (if n =? ptrc then 32 else 0) <= R (* [comment removed for export] *) -> lal_gcost <= R' ->
  (* [comment removed for export] *)
  usp mod 16 = 0 -> stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 720 -> usp <= 2^47 -> mem_inv bsegs m ->
  bv_unsigned tp = 0x5e1550 ->
  rw_cells bsegs m 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))] ->
  rw_cells bsegs m 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)] ->
  u64arr bsegs m 0xab000 bsl ->
  rw_cells bsegs m 0xab200 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
  u64arr bsegs m PA ws ->
  thread_cells m tp TSD CTX T ->
  rw_cells bsegs m (T + 2872) [C8 (Z_to_bv 64 tmm); C8 (Z_to_bv 64 tmd)] ->
  lal_statics m ->
  fresh_shadow_ok m mo ->
  (* [comment removed for export] *)
  (forall ms' mo', lal_post_ok ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m mo mo' R R' ms' ->
     realizes_cfg acfg bsegs (mkCfg ms' mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf98) (Z_to_bv 64 0xab208) (Z_to_bv 64 need) (Z_to_bv 64 8)
                                   a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_ENTRY) fc None m (seg_rom bsegs)) mo) K.
Proof. aceil.
  intros until K. intros HK TOK AK RC RG U16 SK LOC LO SPH MI TP SEC NRS SST BSL MTX GST ARR TC TST LST FSH CONT_OK.
  assert (RC0 : cost2 msz <= R) by (clear -RC; destruct (n =? ptrc); lia).
  (* [comment removed for export] *)
  pose proof LOC as LOC0. aceil.
  pose proof kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  destruct NEED as (N1 & N8 & N2). assert (N0 : 0 < need) by lia.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  pose proof WF as WF0. destruct WF0 as (WE & WR & WC & WK & WQ & WS & WD).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                    WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).
  destruct WS as (WS1 & WS2 & WS3 & WS4 & WS5).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK).
  pose proof (ATOK_KIA _ _ _ _ _ _ _ _ _ _ TOK) as KIA0.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EEs & EFSs & [EI1 EI2]). rewrite EEs in EI1, EI2.
  assert (USP : bv_unsigned (Z_to_bv 64 usp) = usp).
  { apply Z_to_bv_small. change (bv_modulus 64) with (2^64). pose proof (stk_lo_nonneg _ _ _ _ SK). lia. }
  assert (MSZ : msz <= 2^27 + 2^14) by (clear -CEILB N2 MF3; lia).
  assert (LR2 : msz <= 4096 * R).
  { unfold cost2 in RC0. destruct (kBigMapSize <=? msz); destruct (msz <? kBigMapSize); clear -CEILB RC0 MF1 MF2 N0; Z.div_mod_to_equations; lia. }
  pose proof LST as (STA & PG & GS1 & GS2).
  (* [comment removed for export] *)
  pose proof (placed_s_num _ _ HTR ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & TQ4). pose proof HTR as (_ & TQ5 & _).
  pose proof HC as ((HCin & HCpl & HCrest) & HCa & HCb). pose proof (placed_s_num _ _ HCpl ltac:(clear -HCa HCb; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof HCpl as (_ & CQ5 & _).
  pose proof (ptr_placed E0 FSB0 s WE ENV) as PPL. pose proof (placed_num _ _ PPL ltac:(unfold kPtrArrayLen; clear; lia)) as (PQ1 & PQ2 & PQ3).
  pose proof PPL as (_ & PQ5 & _). unfold kPtrArrayLen in PQ2, PQ3, PQ5.
  (* [comment removed for export] *)
  set (P1 := fun x : acc => acc_ok (m_vm_lazy mo) (aSc s) x).
  assert (PSTK1 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P1 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P1. apply (pol_stack' E0 FSB0 HR0 s mo AK WE ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
  assert (PDAT1 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P1 (Z_to_bv 64 x, k)).
  { intros x k H1 H2. unfold P1. apply (pol_img' E0 FSB0 HR0 s mo AK WE ENV ENV0); clear -CEILB H1 H2; lia. }
  eapply (srzA_seg bsegs (aSc s) (aNc s) (aEBc s) P1).
  { eapply (lal_A P1 PDAT1); [ rewrite USP; exact SK | exact LOC0 | rewrite USP; clear -CEILB LO; lia | rewrite USP; exact SPH | exact MI
      | exact SEC | exact GS1 | exact GS2 | exact N0 | clear -CEILB N2; lia | rewrite USP; exact PSTK1 ]. }
  { split; [exact KIA0| intros x Hx; exact Hx]. }
  intros ms1 mo1 (j0 & m1 & -> & MU1 & WM1 & MI1 & SK1 & FR1) AG1 [KIA1 POL1]. rewrite USP in MU1, SK1, FR1. rewrite USP.
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 AK) as AK1.
  assert (LST1 : lal_statics m1).
  { apply (lal_statics_agree m m1 LST). intros x Hx. apply MU1. rewrite wa_unsigned by (clear -CEILB Hx; lia). cbn. clear -CEILB Hx LOC LO. lia. }
  assert (USP96 : bv_unsigned (Z_to_bv 64 (usp - 96)) = usp - 96) by (apply unsigned_lit; clear -CEILB LOC LO SPH; lia).
  (* [comment removed for export] *)
  eapply (rzA_mm_cfg bsegs (aSc s) (aNc s) (aEBc s) P1 (NMmap 0 msz 3 MAP_ANON_RW) (mmap_CHK 0 msz 3 0x22) (dec_as msz lo)
            (mod_post (fun x r u => x = (r, u)) (Z_to_bv 64 LAL_RET1) (Z_to_bv 64 (usp - 96)) gp tp (Z_to_bv 64 0xab208) (Z_to_bv 64 0xaaf98)
                      (Z_to_bv 64 msz) (Z_to_bv 64 need) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 F fc msz lo m1) _ mo1 K).
  - unfold mmap_CHK, MAP_ANON_RW. apply mm_node_mmap.
  - left. reflexivity.
  - eapply (mmap_ordie_specA P1 PDAT1 (dec_as msz lo) (fun x r u => x = (r, u)));
      [ exact (dec_as_ok msz lo) | rewrite USP96; exact SK1 | exact LOC0 | rewrite USP96; clear -CEILB LO; lia | rewrite USP96; clear -CEILB SPH LO LOC; lia | exact MI1 | exact (proj1 LST1)
      | reflexivity | unfold A_SECNAME; rewrite unsigned_lit by lia; lia | exact MF1 | clear -CEILB MF2 N0; lia | clear -CEILB MSZ; lia
      | rewrite USP96; intros; apply PSTK1; lia ].
  - split; [exact KIA1| exact POL1].
  - exact HK.
  - intros mo2 AG2 KIA2.
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK1 AG2 KIA2) as TOK2.
    pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ TOK2) as KV2.
    pose proof (magree_frame _ _ AG2) as (Ffds2 & Fvm2 & Flz2 & Ffs2 & Fh2 & Ftid2 & _).
    pose proof (AKern_frame _ _ _ _ Fvm2 Flz2 AK1) as AK2.
    destruct (ev_anon_rw E0 FSB0 HR0 L0 RES0 EB0 HR0_ok LS_L0 GS_L0 HS_L0 RES0_cover RSVD RSVD_pos R R' s mo1 mo2 msz TOK1 AG2 KIA2 MF1
                ltac:(unfold NMAXA; clear -CEILB MF2 N1 MSZ; lia) LR2) as (NU & OKG & ALL).
    split; [exact NU|]. split; [exact OKG|].
    intros eff mo' HCK NR.
    destruct (ALL eff mo' HCK NR) as (MMA & r & -> & RA & RPL & RSV & RF & RR & -> & KIA' & LIM & MAPS & NOACC & LAZY & RES & MWF & TOP' & NAO & MWF2 & OS2' & PS2').
    (* [comment removed for export] *)
    set (mb := bv_unsigned r) in *.
    pose proof (bv_unsigned_in_range 64 r) as RRG. change (bv_modulus 64) with (2^64)%Z in RRG. fold mb in RRG.
    pose proof (placed_num _ _ RPL ltac:(clear -MF2 N0; lia)) as (RH & R47 & RB). pose proof RPL as (_ & RCL & _). pose proof RCL as RCL0. aceil.
    set (sc := mkSec mb msz need). set (a2 := lal_a2 a mb msz need).
    pose proof TOK2 as (_ & OS2 & EV2 & _ & _ & PS2).
    assert (RG0 : 0 <= R' - lal_gcost) by (clear -RG; lia).
    pose proof (ATOK_sec_append E0 FSB0 HR0 L0 RES0 EB0 HR0_ok s a2 mo2 (m_anon mo2 mb msz) r msz sc R (R' - lal_gcost)
                  eq_refl eq_refl eq_refl eq_refl (fun c => eq_refl) eq_refl eq_refl eq_refl
                  ltac:(clear -CEILB MF2 N0; lia) MF1 KIA' LIM MAPS RES MWF TOP' NAO MWF2 KV2 OS2 (conj RG0 PS2') EV2 ltac:(clear -CEILB RC0; lia)) as TOK3.
    pose proof (AKern_sec_append E0 L0 RES0 s a2 mo2 (m_anon mo2 mb msz) r msz sc eq_refl eq_refl eq_refl (fun c => eq_refl) eq_refl eq_refl eq_refl
                  ltac:(clear -CEILB MF2 N0; lia) MF1 RA RPL MAPS NOACC LAZY RF KV2 Pq Dq AK2 WF) as AK3.
    pose proof (fresh_eager_rw E0 L0 RES0 s mo2 (m_anon mo2 mb msz) r msz ltac:(clear -CEILB MF2 N0; lia) RA RPL MAPS NOACC LAZY RF KV2 Pq Dq AK2 WF) as EG3.
    pose proof (grant_known_free E0 L0 RES0 Pq Dq mo2 a r msz KV2 AK2 WF RF ltac:(fold mb; clear -RH; lia) RCL ltac:(clear -CEILB MF2 N0; lia) RSV) as (GKF1 & GKF2 & GKF3).
    pose proof (grant_validates E0 L0 RES0 Pq Dq mo2 a r msz KV2 AK2 WF RF RA RPL ltac:(clear -CEILB MF2 N0; lia) RSV) as [GV1 GV2].
    fold mb in GKF1, GKF2, GKF3, GV1, GV2, RSV.
    exists (r, true). split; [apply dec_as_grant; [unfold b_image_end; fold mb; clear -CEILB RH; lia| fold mb; clear -CEILB RCL LOC; lia]|].
    exists (aSc (sA a2 s)), (aNc (sA a2 s)), (aEBc (sA a2 s)). split; [exact (ATOK_LI _ _ _ _ _ _ _ _ _ _ TOK3)|].
    split. { intros x Hx. unfold P1 in Hx. eapply acc_ok_monoS; [apply aS_app_mono|]. rewrite LAZY, Flz2, Flz1. exact Hx. }
    intros ms3 mo3 HQ AG3 KIA3 POL3.
    destruct HQ as (rw0 & uw0 & q0 & q1 & q2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & q3 & q4 & q5 & q6 & m3 & E & MU3 & WM3 & MI3 & SK3 & STA3 & ZN & HR).
    injection HR as <- <-. cbv iota in E, MU3. subst ms3. specialize (ZN eq_refl). fold mb in MU3, ZN. rewrite USP96 in MU3, SK3.
    rewrite RR. fold mb.
    replace (ret_pc (Z_to_bv 64 LAL_RET1)) with (Z_to_bv 64 LAL_RET1) by (symmetry; apply ret_pc_even; [unfold LAL_RET1; lia| reflexivity]).
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG3 KIA3) as TOK4.
    pose proof (magree_frame _ _ AG3) as (Ffds3 & Fvm3 & Flz3 & Ffs3 & Fh3 & Ftid3 & _).
    pose proof (AKern_frame _ _ _ _ Fvm3 Flz3 AK3) as AK4.
    assert (EG4 : eager_rw mo3 mb msz) by (unfold eager_rw in *; rewrite Fvm3, Flz3; exact EG3).
    assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK4).
    (* [comment removed for export] *)
    assert (DRS : forall x l, In (x, l) (ae_reserved E0) -> mb + msz <= x \/ x + l <= mb) by (intros x l HI; exact (RSV _ HI)).
    pose proof (DRS _ _ WE13) as DT.
    pose proof (DRS _ _ WE8) as DPA.
    pose proof (DRS _ _ HCin) as DCTX.
    (* [comment removed for export] *)
    assert (HM8 : mb = 8 * (mb / 8) /\ msz = 8 * (msz / 8)) by (clear -CEILB RA MF1; Z.div_mod_to_equations; lia).
    assert (SHW : 0x800b8600 <= kShadowBase + mb / 8 /\ kShadowBase + mb / 8 + msz / 8 <= 0x10007fef8000)
      by (unfold kShadowBase; clear -CEILB RH RCL HM8 MF2 N0; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (MU13 : munch [(usp - 416, usp); (mb, mb + msz)] m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU3]]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia. }
    pose proof (wmono_trans _ _ _ _ WM1 WM3) as WM13.
    Ltac x13 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn].
    assert (SHm : rw_cells bsegs m (kShadowBase + mb / 8) [CB (Z.to_nat (msz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8)))]).
    { apply (FSH mo2 r msz (magree_trans _ _ _ AG1 AG2) RF RPL RSV RA MF1 ltac:(clear -CEILB MF2 N0; lia)). }
    assert (SH3 : rw_cells bsegs m3 (kShadowBase + mb / 8) [CB (Z.to_nat (msz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8)))]).
    { x13 SHm MU13 WM13. unfold kShadowBase in *. clear -CEILB LOC LO RH RB RCL HM8 MF2 N0 SHW. lia. }
    assert (SEC3 : rw_cells bsegs m3 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))]) by (x13 SEC MU13 WM13; clear -CEILB LOC LO RH; lia).
    assert (NRS3 : rw_cells bsegs m3 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)]) by (x13 NRS MU13 WM13; clear -CEILB LOC LO RH; lia).
    assert (SST3 : rw_cells bsegs m3 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)]) by (x13 SST MU13 WM13; clear -CEILB LOC LO RH; lia).
    assert (MTX3 : rw_cells bsegs m3 0xab200 [C4 (Z_to_bv 64 0)]) by (x13 MTX MU13 WM13; clear -CEILB LOC LO RH; lia).
    assert (GST3 : rw_cells bsegs m3 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)]) by (x13 GST MU13 WM13; clear -CEILB LOC LO RH; lia).
    assert (BSL3 : u64arr bsegs m3 0xab000 bsl) by (eapply u64arr_transport; [exact BSL| exact MU13| exact WM13|]; rewrite LBSL; cbn; clear -CEILB LOC LO RH; lia).
    assert (ARR3 : u64arr bsegs m3 PA ws).
    { eapply u64arr_transport; [exact ARR| exact MU13| exact WM13|]. rewrite LWS. cbn.
      pose proof WS1 as X. change kChunksBlockCount with 16384 in X. clear -CEILB LOC LO PQ1 PQ5 DPA X. destruct X as [[-> _]| ->]; cbn; lia. }
    assert (TST3 : rw_cells bsegs m3 (T + 2872) [C8 (Z_to_bv 64 tmm); C8 (Z_to_bv 64 tmd)]) by (x13 TST MU13 WM13; clear -CEILB LOC LO TQ1 TQ5 DT; lia).
    assert (TC3 : thread_cells m3 tp TSD CTX T).
    { destruct TC as (X1 & X2 & X3 & X4 & X5). unfold thread_cells.
      split; [x13 X1 MU13 WM13| split; [x13 X2 MU13 WM13| split; [x13 X3 MU13 WM13| split; [x13 X4 MU13 WM13| x13 X5 MU13 WM13]]]];
        clear -CEILB LOC LO RH TP HT1 HT2 CQ1 CQ5 HCa HCb DCTX; lia. }
    assert (FR3 : rw_cells bsegs m3 (usp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)).
    { eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. unfold lal_frame. cbn. clear -CEILB LO LOC RH RCL. lia. }
    assert (LST3 : lal_statics m3).
    { apply (lal_statics_agree m1 m3 LST1). intros x Hx. apply MU3. rewrite wa_unsigned by (clear -CEILB Hx; lia). cbn. clear -CEILB Hx LOC LO RH. lia. }
    clear SHm SEC NRS SST MTX GST BSL ARR TST TC FR1 LST1 MI1 SK1 STA3.
    (* [comment removed for export] *)
    set (k1 := need / 8) in *. set (k2 := (msz - 4096 - need) / 8) in *.
    assert (HKK : msz / 8 = 512 + k1 + k2 /\ 0 <= k1 /\ 0 <= k2 /\ need = 8 * k1 /\ msz - 4096 - need = 8 * k2) by (subst k1 k2; clear -CEILB N8 MF1 MF2 N0; Z.div_mod_to_equations; lia).
    destruct HKK as (HK0 & HK1 & HK2 & HK3 & HK4).
    apply (rw_cells_split_CB bsegs _ _ [] (Z.to_nat (msz / 8)) _ [] [512; Z.to_nat k1; Z.to_nat k2]%nat) in SH3; [| cbn [sum_nat]; clear -CEILB HK0 HK1 HK2; lia].
    cbn [app mk_CB_cells] in SH3. rewrite !firstn_repeat', !skipn_repeat' in SH3 by (clear -CEILB HK0 HK1 HK2; lia).
    rewrite !firstn_repeat' in SH3 by (clear -CEILB HK0 HK1 HK2; lia).
    pose proof SH3 as SHX. apply (rw_cells_app_splitL bsegs _ _ [_] [_; _]) in SHX. destruct SHX as [SHa SHX]. cbn [cells_size csize Nat.add Z.of_nat] in SHX.
    apply (rw_cells_app_splitL bsegs _ _ [_] [_]) in SHX. destruct SHX as [SHb SHc]. cbn [cells_size csize] in SHc.
    rewrite Nat.add_0_r, Z2Nat.id in SHc by (clear -CEILB HK1; lia). change (Z.of_nat 512) with 512 in SHb. change (Z.of_nat 512) with 512 in SHc.
    apply (rw_cells_split_CB bsegs _ _ [] (Z.to_nat msz) _ [] [32; Z.to_nat (msz - 32)]%nat) in ZN; [| cbn [sum_nat]; clear -CEILB MF2 N0; lia].
    cbn [app mk_CB_cells] in ZN. rewrite !firstn_repeat', !skipn_repeat' in ZN by (clear -CEILB MF2 N0; lia). rewrite !firstn_repeat' in ZN by (clear -CEILB MF2 N0; lia).
    pose proof ZN as ZNX. apply (rw_cells_app_splitL bsegs _ _ [_] [_]) in ZNX. destruct ZNX as [HDR3 ZREST3]. cbn [cells_size csize Nat.add Z.of_nat] in ZREST3.
    change (Z.of_nat 32) with 32 in ZREST3. clear ZN SH3.
    (* [comment removed for export] *)
    set (P2 := fun x : acc => acc_ok (m_vm_lazy mo3) (aSc (sA a2 s)) x).
    assert (PSTK2 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P2 (Z_to_bv 64 x, k)).
    { intros x k H1 H2. unfold P2. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE ENV0); clear -CEILB H1 H2 LOC0 SPH; lia. }
    assert (PDAT2 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P2 (Z_to_bv 64 x, k)).
    { intros x k H1 H2. unfold P2. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE ENV2 ENV0); clear -CEILB H1 H2; lia. }
    assert (PMAP2 : forall x k, mb <= x -> x + Z.of_nat k <= mb + msz -> P2 (Z_to_bv 64 x, k)).
    { intros x k H1 H2. unfold P2. eapply (acc_ok_of_lazy_disjoint mo3 _ mb (mb + msz)); [apply eager_rw_lazy_disjoint; exact EG4| clear -CEILB RH; lia| clear -CEILB RCL; lia| exact H1| exact H2]. }
    assert (PTHR2 : forall x k, T <= x -> x + Z.of_nat k <= T + 4096 -> P2 (Z_to_bv 64 x, k)).
    { intros x k H1 H2. unfold P2. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE); assumption. }
    assert (PCTX2 : P2 (Z_to_bv 64 (CTX + 152), 8%nat)).
    { unfold P2. apply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo3 AK4 r0 rl); [exact (proj1 HC)| clear -CEILB HCa; lia| clear -CEILB HCb; cbn; lia]. }
    assert (PSH2 : forall x k, kShadowBase + mb / 8 <= x -> x + Z.of_nat k <= kShadowBase + mb / 8 + msz / 8 -> P2 (Z_to_bv 64 x, k)).
    { intros x k H1 H2. unfold P2. apply (pol_sec_shadow' E0 FSB0 HR0 (sA a2 s) mo3 sc x k (res_ok_a2 mb need)).
      - unfold a2, lal_a2. cbn. apply in_or_app. right. left. reflexivity.
      - exact RA.
      - cbn [sc_map_beg sc]. clear -CEILB RH. lia.
      - exact RCL0.
      - cbn [sc_map_size sc]. clear -CEILB MF2 N0; lia.
      - exact MF1.
      - cbn [sc_map_beg sc]. rewrite A_SB_val. unfold kShadowBase in H1. exact H1.
      - cbn [sc_map_beg sc_map_size sc]. rewrite A_SB_val. unfold kShadowBase in H2. clear -CEILB H2 HM8. lia. }
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (lal_B1 P2 PDAT2); [exact MI3| exact SEC3| exact N0| exact N8| clear -CEILB N2; lia| clear -CEILB RH; lia| exact RA| exact RCL0]. }
    { split; [exact KIA3| intros x Hx; exact Hx]. }
    intros ms4 mo4 -> AG4 [KIA4 POL4].
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (poison_walk2 P2); rewrite ?USP96;
        [ exact SK3 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB SPH LO LOC; lia | exact MI3 | exact (proj1 (proj2 LST3))
        | clear -CEILB RA; Z.div_mod_to_equations; lia | reflexivity | lia | clear -CEILB RH; lia | clear -CEILB RCL MF2 N0; lia
        | rewrite KHB; clear -CEILB RB MF2 N0; lia | lia | left; lia
        | change (Z.to_nat (4096 / 8)) with 512%nat; exact SHa | intros; apply PSTK2; lia | exact PDAT2
        | intros; apply PSH2; [lia| change (4096 / 8) with 512 in *; clear -CEILB H H0 HK0 HK1 HK2; lia] ]. }
    { split; [exact KIA4| exact POL4]. }
    intros ms5 mo5 HQ AG5 [KIA5 POL5].
    destruct HQ as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m5 & -> & MU5 & WM5 & MI5 & SK5 & SH5a & PG5).
    rewrite USP96 in MU5, SK5. change (4096 / 8) with 512 in MU5, SH5a. change (Z.to_nat 512) with 512%nat in SH5a.
    replace (ret_pc (Z_to_bv 64 LAL_RET2)) with (Z_to_bv 64 LAL_RET2) by (symmetry; apply ret_pc_even; [unfold LAL_RET2; lia| reflexivity]).
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (lal_B2 P2); [exact MI5| exact N0| clear -CEILB RH; lia| clear -CEILB RCL; lia]. }
    { split; [exact KIA5| exact POL5]. }
    intros ms6 mo6 -> AG6 [KIA6 POL6].
    assert (SH6c : rw_cells bsegs m5 (kShadowBase + (mb + 4096 + need) / 8) [CB (Z.to_nat ((msz - 4096 - need) / 8)) (repeat zb0 (Z.to_nat k2))]).
    { replace ((msz - 4096 - need) / 8) with k2 by (clear -CEILB HK4; lia).
      replace (kShadowBase + (mb + 4096 + need) / 8) with (kShadowBase + mb / 8 + 512 + k1) by (clear -CEILB HK3 HM8; Z.div_mod_to_equations; lia).
      x13 SHc MU5 WM5. unfold kShadowBase in *. clear -CEILB LOC LO RH RCL HK1 HK2 SHW. lia. }
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (poison_walk2 P2); rewrite ?USP96;
        [ exact SK5 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB SPH LO LOC; lia | exact MI5 | exact PG5
        | clear -CEILB RA N8; Z.div_mod_to_equations; lia | clear -CEILB HK4; lia | clear -CEILB HK4 HK2; lia
        | clear -CEILB RH MF2 N0; lia | clear -CEILB RCL MF2 N0; lia | rewrite KHB; clear -CEILB RB MF2 N0 N1 HK4 HK2; lia
        | lia | left; lia | exact SH6c | intros; apply PSTK2; lia | exact PDAT2
        | intros; apply PSH2; [clear -CEILB H RA N8 N0; Z.div_mod_to_equations; lia| clear -CEILB H H0 HK0 HK1 HK2 HK3 HK4 HM8; Z.div_mod_to_equations; lia] ]. }
    { split; [exact KIA6| exact POL6]. }
    intros ms7 mo7 HQ AG7 [KIA7 POL7].
    destruct HQ as (y0' & y1' & y2' & z0' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & y3' & y4' & y5' & y6' & m7 & -> & MU7 & WM7 & MI7 & SK7 & SH7c & PG7).
    rewrite USP96 in MU7, SK7.
    replace (ret_pc (Z_to_bv 64 LAL_RET3)) with (Z_to_bv 64 LAL_RET3) by (symmetry; apply ret_pc_even; [unfold LAL_RET3; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MU37 : munch [(usp - 160, usp - 96); (kShadowBase + mb / 8, kShadowBase + mb / 8 + msz / 8)] m3 m7).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU7]]; intros y Hy; cbn in Hy |- *; [clear -CEILB Hy HK0 HK1 HK2; lia|].
      clear -CEILB Hy HK0 HK1 HK2 HK3 HK4 HM8 RA N8. Z.div_mod_to_equations. lia. }
    pose proof (wmono_trans _ _ _ _ WM5 WM7) as WM37.
    assert (TC7 : thread_cells m7 tp TSD CTX T).
    { destruct TC3 as (X1 & X2 & X3 & X4 & X5). unfold thread_cells. unfold kShadowBase in MU37.
      split; [x13 X1 MU37 WM37| split; [x13 X2 MU37 WM37| split; [x13 X3 MU37 WM37| split; [x13 X4 MU37 WM37| x13 X5 MU37 WM37]]]];
        unfold kShadowBase in *; clear -CEILB LOC LO RH RCL TP HT1 HT2 CQ1 CQ4 CQ5 HCa HCb SHW HM8; lia. }
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply evtA_cut; [eapply (lal_B3 P2); exact MI7|]. cbv beta. intros ms' ->.
      eapply (gcts_walk P2); rewrite ?USP96;
        [ exact SK7 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB SPH LO LOC; lia | exact MI7 | exact TC7 | clear -CEILB HT1; lia | exact HT2
        | clear -CEILB CQ1 HCa; lia | exact HC4 | clear -CEILB TQ1 TQ2; lia | rewrite TP; lia | intros; apply PSTK2; lia | exact PDAT2 | exact PCTX2 ]. }
    { split; [exact KIA7| exact POL7]. }
    intros ms8 mo8 HQ AG8 [KIA8 POL8].
    destruct HQ as (z1'' & m8 & -> & MU8 & WM8 & MI8 & SK8). rewrite USP96 in MU8, SK8.
    replace (ret_pc (Z_to_bv 64 LAL_RET4)) with (Z_to_bv 64 LAL_RET4) by (symmetry; apply ret_pc_even; [unfold LAL_RET4; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MU38 : munch [(usp - 160, usp - 96); (2147450880 + mb / 8, 2147450880 + mb / 8 + msz / 8)] m3 m8).
    { eapply munch_trans; [exact MU37| eapply munch_weaken; [| exact MU8]]. intros y Hy; cbn in Hy |- *. clear -CEILB Hy. lia. }
    pose proof (wmono_trans _ _ _ _ WM37 WM8) as WM38.
    unfold kShadowBase in SHW.
    assert (ZREST8 : rw_cells bsegs m8 (mb + 32) [CB (Z.to_nat (msz - 32)) (repeat zb0 (Z.to_nat (msz - 32)))]).
    { eapply rw_cells_transport; [exact ZREST3| exact MU38| exact WM38|].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB MF2 N0; lia). cbn. clear -CEILB LOC LO RH RB RCL HM8 MF2 N0 SHW. lia. }
    assert (SEC8 : rw_cells bsegs m8 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))]) by (x13 SEC3 MU38 WM38; clear -CEILB LOC LO SHW; lia).
    assert (NRS8 : rw_cells bsegs m8 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)]) by (x13 NRS3 MU38 WM38; clear -CEILB LOC LO SHW; lia).
    assert (SST8 : rw_cells bsegs m8 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)]) by (x13 SST3 MU38 WM38; clear -CEILB LOC LO SHW; lia).
    assert (MTX8 : rw_cells bsegs m8 0xab200 [C4 (Z_to_bv 64 0)]) by (x13 MTX3 MU38 WM38; clear -CEILB LOC LO SHW; lia).
    assert (GST8 : rw_cells bsegs m8 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)]) by (x13 GST3 MU38 WM38; clear -CEILB LOC LO SHW; lia).
    assert (TST8 : rw_cells bsegs m8 (T + 2872) [C8 (Z_to_bv 64 tmm); C8 (Z_to_bv 64 tmd)]) by (x13 TST3 MU38 WM38; clear -CEILB LOC LO TQ1 TQ4 TQ5 SHW; lia).
    assert (HDR8 : rw_cells bsegs m8 mb [CB 32 (repeat zb0 32)]) by (x13 HDR3 MU38 WM38; clear -CEILB LOC LO RH RB RCL HM8 MF2 N0 SHW; lia).
    assert (FR8 : rw_cells bsegs m8 (usp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)).
    { eapply rw_cells_transport; [exact FR3| exact MU38| exact WM38|]. unfold lal_frame. cbn. clear -CEILB LO LOC SHW. lia. }
    assert (BSL8 : u64arr bsegs m8 0xab000 bsl) by (eapply u64arr_transport; [exact BSL3| exact MU38| exact WM38|]; rewrite LBSL; cbn; clear -CEILB LOC LO SHW; lia).
    assert (ARR8 : u64arr bsegs m8 PA ws).
    { eapply u64arr_transport; [exact ARR3| exact MU38| exact WM38|]. rewrite LWS. cbn.
      pose proof WS1 as X. change kChunksBlockCount with 16384 in X. clear -CEILB LOC LO PQ1 PQ3 PQ5 X SHW. destruct X as [[-> _]| ->]; cbn; lia. }
    assert (LST8 : lal_statics m8).
    { apply (lal_statics_agree m3 m8 LST3). intros x Hx. apply MU38. rewrite wa_unsigned by (clear -CEILB Hx; lia). cbn. clear -CEILB Hx LOC LO SHW. lia. }
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (lal_C P2 PDAT2);
        [ exact MI8 | exact SEC8 | exact NRS8 | exact MTX8 | exact TST8 | exact HDR8 | exact N0 | exact N8 | clear -CEILB N2; lia | clear -CEILB RH; lia | exact RA | exact RCL0
        | clear -CEILB TQ1 TQ3; lia | exact TQ5 | exact DT | clear -CEILB HVT; lia | clear -CEILB HVT; lia
        | pose proof WS1 as X; change kChunksBlockCount with 16384 in X; clear -CEILB X; lia
        | pose proof NCH as X; unfold n_chunks, zlen in *; change kChunksBlockCount with 16384 in X; clear -CEILB X; lia
        | exact PTHR2 | intros; apply PMAP2; [lia| clear -CEILB H0 MF2 N0; lia] ]. }
    { split; [exact KIA8| exact POL8]. }
    intros ms9 mo9 HQ AG9 [KIA9 POL9].
    destruct HQ as (x5' & x6' & x8' & x9' & hj9 & m9 & -> & MU9 & WM9 & MI9 & MTX9 & TST9 & HDR9).
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (lal_beq P2); [exact MI9| pose proof NCH as X; unfold n_chunks, zlen in *; change kChunksBlockCount with 16384 in X; clear -CEILB X; lia
                           | pose proof WS1 as X; change kChunksBlockCount with 16384 in X; clear -CEILB X; lia]. }
    { split; [exact KIA9| exact POL9]. }
    intros ms10 mo10 -> AG10 [KIA10 POL10].
    pose proof (magree_trans _ _ _ AG4 (magree_trans _ _ _ AG5 (magree_trans _ _ _ AG6 (magree_trans _ _ _ AG7 (magree_trans _ _ _ AG8 (magree_trans _ _ _ AG9 AG10)))))) as AG310.
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK4 AG310 KIA10) as TOK10.
    pose proof (magree_frame _ _ AG310) as (Ffds10 & Fvm10 & Flz10 & Ffs10 & Fh10 & Ftid10 & _).
    pose proof (AKern_frame _ _ _ _ Fvm10 Flz10 AK4) as AK10.
    (* [comment removed for export] *)
    assert (MU39 : munch [(usp - 160, usp - 96); (2147450880 + mb / 8, 2147450880 + mb / 8 + msz / 8); (T + 2872, T + 2888); (mb, mb + 24); (0xab200, 0xab204)] m3 m9).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU38]| eapply munch_weaken; [| exact MU9]]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia. }
    pose proof (wmono_trans _ _ _ _ WM38 WM9) as WM39.
    assert (MU79 : munch [(usp - 128, usp - 96); (T + 2872, T + 2888); (mb, mb + 24); (0xab200, 0xab204)] m7 m9)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU8]| eapply munch_weaken; [| exact MU9]]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia).
    assert (MU59 : munch [(usp - 160, usp - 96); (kShadowBase + (mb + 4096 + need) / 8, kShadowBase + (mb + 4096 + need) / 8 + (msz - 4096 - need) / 8);
                          (T + 2872, T + 2888); (mb, mb + 24); (0xab200, 0xab204)] m5 m9)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU7]| eapply munch_weaken; [| exact MU79]]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia).
    assert (LST9 : lal_statics m9).
    { apply (lal_statics_agree2 m8 m9 LST8). intros x Hx Hx'. apply MU9. rewrite wa_unsigned by (clear -CEILB Hx; lia). cbn. clear -CEILB Hx Hx' TQ1 TQ3 RH. lia. }
    assert (SEC9 : rw_cells bsegs m9 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))]) by (x13 SEC8 MU9 WM9; clear -CEILB TQ1 TQ3 RH; lia).
    assert (NRS9 : rw_cells bsegs m9 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)]) by (x13 NRS8 MU9 WM9; clear -CEILB TQ1 TQ3 RH; lia).
    assert (SST9 : rw_cells bsegs m9 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)]) by (x13 SST8 MU9 WM9; clear -CEILB TQ1 TQ3 RH; lia).
    assert (GST9 : rw_cells bsegs m9 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)]) by (x13 GST8 MU9 WM9; clear -CEILB TQ1 TQ3 RH; lia).
    assert (FR9 : rw_cells bsegs m9 (usp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)).
    { eapply rw_cells_transport; [exact FR8| exact MU9| exact WM9|]. unfold lal_frame. cbn. clear -CEILB LO LOC RH RCL TQ1 TQ5 MF2 N0. lia. }
    assert (BSL9 : u64arr bsegs m9 0xab000 bsl) by (eapply u64arr_transport; [exact BSL8| exact MU9| exact WM9|]; rewrite LBSL; cbn; clear -CEILB TQ1 TQ3 RH; lia).
    assert (ARR9 : u64arr bsegs m9 PA ws)
      by (eapply u64arr_transport; [exact ARR8| exact MU9| exact WM9|]; rewrite LWS; cbn; pose proof WS1 as X; change kChunksBlockCount with 16384 in X;
          clear -CEILB PQ1 PQ5 DPA DT WE23 X HM8 RH MF2 N0; destruct X as [[-> _]| ->]; cbn; lia).
    assert (ZREST9 : rw_cells bsegs m9 (mb + 32) [CB (Z.to_nat (msz - 32)) (repeat zb0 (Z.to_nat (msz - 32)))])
      by (eapply rw_cells_transport; [exact ZREST8| exact MU9| exact WM9|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB MF2 N0; lia); cbn;
          clear -CEILB RH RCL DT HM8 MF2 N0; lia).
    assert (SH9a : rw_cells bsegs m9 (kShadowBase + mb / 8) [CB 512 (repeat (Z_to_bv 8 250) 512)])
      by (eapply rw_cells_transport; [exact SH5a| exact MU59 | exact (wmono_trans _ _ _ _ WM7 (wmono_trans _ _ _ _ WM8 WM9)) |]; cbn; unfold kShadowBase;
          clear -CEILB LOC LO RH RB RCL TQ1 TQ4 TQ5 HM8 HK0 HK1 HK2 HK3 HK4 MF2 N0 N8 RA SHW; Z.div_mod_to_equations; lia).
    assert (MU39p : munch [(usp - 160, usp - 96); (kShadowBase + mb / 8, kShadowBase + mb / 8 + 512);
                           (kShadowBase + (mb + 4096 + need) / 8, kShadowBase + (mb + 4096 + need) / 8 + (msz - 4096 - need) / 8);
                           (T + 2872, T + 2888); (mb, mb + 24); (0xab200, 0xab204)] m3 m9)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU59]]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia).
    assert (SH9b : rw_cells bsegs m9 (kShadowBase + mb / 8 + 512) [CB (Z.to_nat k1) (repeat zb0 (Z.to_nat k1))])
      by (eapply rw_cells_transport; [exact SHb| exact MU39p| exact WM39|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB HK1; lia); cbn; unfold kShadowBase;
          clear -CEILB LOC LO RH RB RCL TQ1 TQ4 TQ5 HM8 HK0 HK1 HK2 HK3 HK4 MF2 N0 N8 RA SHW; Z.div_mod_to_equations; lia).
    assert (SH9c : rw_cells bsegs m9 (kShadowBase + (mb + 4096 + need) / 8) [CB (Z.to_nat ((msz - 4096 - need) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((msz - 4096 - need) / 8)))])
      by (eapply rw_cells_transport; [exact SH7c| exact MU79 | exact (wmono_trans _ _ _ _ WM8 WM9) |]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB HK4 HK2; lia); cbn;
          unfold kShadowBase; clear -CEILB LOC LO RH RB RCL TQ1 TQ4 TQ5 HM8 HK0 HK1 HK2 HK3 HK4 MF2 N0 N8 RA SHW; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (LG : 0 <= Z.log2 msz < 28) by (split; [apply Z.log2_nonneg| apply (proj1 (Z.log2_lt_pow2 msz 28 ltac:(clear -CEILB MF2 N0; lia))); clear -CEILB MF3 N2 N0; lia]).
    pose proof NCH as NLT; unfold n_chunks, zlen in NLT; change kChunksBlockCount with 16384 in NLT.
    assert (SK9 : stk bsegs m9 lo (usp - 96)) by (eapply (stk_transport_disjoint bsegs); [exact SK8| exact MU9| exact WM9|]; cbn; clear -CEILB LOC LO TQ1 TQ5 RH RCL MF2 N0; lia).
    Ltac djs := cbn [disjoint_from outside map fst snd]; unfold n_chunks, zlen; repeat match goal with |- _ /\ _ => split end; try exact I.
    Ltac x911 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [map fst snd cells_size csize]; rewrite ?Nat.add_0_r, ?repeat_length].
    destruct (Z.eqb_spec n ptrc) as [EQNP|NENP].
    1: (assert (RC1 : cost2 msz + 32 <= R) by (generalize RC; clear -EQNP; try rewrite (proj2 (Z.eqb_eq _ _) EQNP); cbn [Z.eqb]; intros RC; lia)); clear RC; rename RC1 into RC.
    2: { (* [comment removed for export] *)
      assert (P16 : ptrc = kChunksBlockCount) by (pose proof NCH as X; destruct WS1 as [[X1 _]|X1]; [exfalso; clear -CEILB X X1 NENP WS2; unfold n_chunks, zlen in *; lia| exact X1]).
      assert (PPA2 : forall x k, PA <= x -> x + Z.of_nat k <= PA + 8 * Z.of_nat (length ws) -> P2 (Z_to_bv 64 x, k))
        by (intros x k H1 H2; unfold P2; rewrite LWS, P16 in H2; change (8 * Z.of_nat (Z.to_nat kChunksBlockCount)) with kPtrArrayCommit in H2;
            apply (pol_ptr_head' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE); [exact P16| exact H1| exact H2]).
      assert (LWS' : Z.of_nat (length ws) = 16384) by (rewrite LWS, P16; reflexivity).
      eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
      { eapply (lal_D P2 PDAT2);
          [ exact SK9 | exact LOC0 | clear -CEILB LO; lia | exact SPH | exact MI9 | exact FR9 | exact SEC9 | exact NRS9 | exact SST9 | exact BSL9 | exact LBSL | exact MTX9 | exact GST9 | exact ARR9
          | pose proof NCH as X; unfold n_chunks, zlen in X; unfold n_chunks, zlen; change kChunksBlockCount with 16384 in X; clear -CEILB X LWS'; lia
          | exact HDR9 | exact N0 | clear -CEILB N2; lia | clear -CEILB RH; lia | exact RCL0 | exact PQ1 | rewrite LWS'; clear -CEILB PQ5; lia | rewrite LWS'; clear -CEILB DPA; lia
          | pose proof NCH as X; unfold n_chunks, zlen in *; change kChunksBlockCount with 16384 in X; clear -CEILB X; lia
          | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | exact PSTK2
          | intros; apply PMAP2; [lia| clear -CEILB H0 MF2 N0; lia] | rewrite LWS'; intros; apply PPA2; [assumption| rewrite LWS'; assumption] ]. }
      { split; [exact KIA10| exact POL10]. }
      cbv beta. intros ms11 mo11 HQ AG11 [KIA11 POL11].
      destruct HQ as (w11 & w12 & w13 & w14 & w15 & w16 & bsl' & m11 & -> & MU11 & WM11 & MI11 & SK11 & NRS11 & SST11 & BSL11 & LBSL11 & MTX11 & GST11 & ARR11 & HDR11).
      pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK10 AG11 KIA11) as TOK11.
      pose proof (magree_frame _ _ AG11) as (Ffds11 & Fvm11 & Flz11 & Ffs11 & Fh11 & Ftid11 & _).
      pose proof (AKern_frame _ _ _ _ Fvm11 Flz11 AK10) as AK11.
      apply CONT_OK. unfold lal_post_ok. rewrite USP. rewrite (proj2 (Z.eqb_neq n ptrc) NENP).
      exists y0', y1', y2', w11, w12, w13, w14, w15, w16, z7', y3', y4', y5', y6', m11, mb, (repeat zb0 (Z.to_nat k1)), bsl', (upd ws (Z.to_nat n) (Z_to_bv 64 mb)).
      split; [reflexivity|]. split; [exact MI11|]. split; [exact SK11|].
      split. { unfold lal_W. cbn [app].
               eapply munch_trans; [eapply munch_weaken; [| exact MU13]| eapply munch_trans; [eapply munch_weaken; [| exact MU39]| eapply munch_weaken; [| exact MU11]]];
                 intros y Hy; cbn in Hy |- *; unfold kShadowBase in *; [clear -CEILB Hy| clear -CEILB Hy RH RCL MF2 N0 TQ1 DT HK0 HK1 HK2| clear -CEILB Hy MF2 N0]; lia. }
      split; [exact (wmono_trans _ _ _ _ WM13 (wmono_trans _ _ _ _ WM39 WM11))|].
      split; [exact RA|]. split; [exact RPL|]. split; [exact RSV|]. split; [exact GKF1|]. split; [exact GKF2|]. split; [exact GKF3|]. split; [exact GV1|]. split; [exact GV2|]. split; [exact MTX11|].
      split; [unfold lal_a3; rewrite (proj2 (Z.eqb_neq _ _) NENP); exact NRS11|].
      split; [exact SST11|]. split; [exact BSL11|]. split; [exact LBSL11|]. split; [exact GST11|]. split; [exact ARR11|]. split; [reflexivity|]. split; [exact HDR11|].
      split; [x911 ZREST9 MU11 WM11; rewrite Z2Nat.id by (clear -CEILB MF2 N0; lia); djs; clear -CEILB RH RCL MF2 N0 PQ1 PQ5 DPA NLT LG; lia|].
      split; [x911 SH9a MU11 WM11; unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 PQ1 PQ3 PQ5 DPA NLT HM8 LG SHW; lia|].
      split; [x911 SH9b MU11 WM11; rewrite Z2Nat.id by (clear -CEILB HK1; lia); unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 PQ1 PQ3 PQ5 DPA NLT HM8 HK1 HK3 LG SHW; lia|].
      split; [x911 SH9c MU11 WM11; rewrite Z2Nat.id by (clear -CEILB HK2 HK4; lia); unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 N8 RA PQ1 PQ3 PQ5 DPA NLT HM8 HK1 HK2 HK3 HK4 LG SHW; Z.div_mod_to_equations; lia|].
      split; [x911 TST9 MU11 WM11; djs; clear -CEILB RH RCL MF2 N0 TQ1 TQ3 TQ5 PQ1 PQ5 DT WE23 NLT LG; lia|].
      split; [apply (lal_statics_agree2 m9 m11 LST9); intros x Hx Hx'; apply MU11; rewrite wa_unsigned by (clear -CEILB Hx; lia); djs; clear -CEILB Hx Hx' PQ1 RH LG NLT; lia|].
      assert (E3S : lal_a3 a mb msz need = a2) by (unfold lal_a3; rewrite (proj2 (Z.eqb_neq _ _) NENP); reflexivity).
      split; [replace (R - cost2 msz - 0) with (R - cost2 msz) by lia; apply (ATOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s a2); [exact TOK11| rewrite <- E3S; apply lal_state_fp]|].
      split; [apply (AKern_ext' E0 a2); [| | | | | exact AK11]; pose proof (lal_state_fp a mb msz need) as (X1 & X2 & X3 & X4 & X5 & X6); rewrite E3S in *;
              [| exact X3| exact X2| exact X5| exact X6]; unfold lal_state, lal_commit, a2, lal_a2, n_chunks; cbn; destruct (Z.of_nat (length (as_sec a)) =? as_ptr_committed a); reflexivity|].
      rewrite Ffs11, Ffds11, Ftid11, Ffs10, Ffds10, Ftid10, Ffs3, Ffds3, Ftid3.
      change (m_fs (m_anon mo2 mb msz)) with (m_fs mo2). change (m_fds (m_anon mo2 mb msz)) with (m_fds mo2). change (m_tid (m_anon mo2 mb msz)) with (m_tid mo2).
      rewrite Ffs2, Ffds2, Ftid2, Ffs1, Ffds1, Ftid1. split; [reflexivity| split; reflexivity]. }
    (* [comment removed for export] *)
    assert (P0 : ptrc = 0 /\ n = 0 /\ as_sec a = [])
      by (destruct WS1 as [[X1 X2]|X1]; [rewrite <- EQNP in X1 |- *; auto| exfalso; rewrite <- EQNP in X1; clear -CEILB X1 NLT; unfold n_chunks, zlen in *; change kChunksBlockCount with 16384 in X1; lia]).
    destruct P0 as (PT0 & NN0 & SEC0).
    eapply (srzA_seg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2).
    { eapply (lal_E1 P2 PDAT2); [exact (Z_to_bv 64 0)| exact MI9| exact SEC9| rewrite NN0; lia| clear -CEILB PQ1; lia| rewrite NN0; clear -CEILB PQ2; lia| clear -CEILB RH RCL MF2 N0; lia]. }
    { split; [exact KIA10| exact POL10]. }
    intros ms11 mo11 -> AG11 [KIA11 POL11].
    rewrite NN0, Z.mul_0_r, Z.add_0_r.
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK10 AG11 KIA11) as TOK11.
    pose proof (magree_frame _ _ AG11) as (Ffds11 & Fvm11 & Flz11 & Ffs11 & Fh11 & Ftid11 & _).
    pose proof (AKern_frame _ _ _ _ Fvm11 Flz11 AK10) as AK11.
    assert (PAA : PA mod 4096 = 0)
      by (pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ TOK11) as (_ & _ & [_ MW] & _); pose proof (proj1 (Forall_forall _ _) MW _ (ak_ptr E0 a2 mo11 AK11)) as (_ & X & _);
          unfold went, kwz, elo in X; cbn [fst snd] in X; rewrite u64_small in X by (clear -CEILB PQ1 PQ2; lia); exact X).
    eapply (rzA_mm_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2 (NMmap PA kPtrArrayCommit 3 MAP_FIXED_RW)
              (mmap_CHK PA kPtrArrayCommit 3 0x32) (dec_zs PA kPtrArrayCommit)
              (mmap_fixed_gen_post (fun x r u => x = (r, u)) (Z_to_bv 64 LAL_RET5) (Z_to_bv 64 (usp - 96)) gp tp (Z_to_bv 64 0xab208) (Z_to_bv 64 0xaaf98)
                 (Z_to_bv 64 msz) (Z_to_bv 64 (swar_res msz)) (Z_to_bv 64 (mb + 4096)) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + msz)) (Z_to_bv 64 (mb + 4096 + need))
                 (Z_to_bv 64 7) (Z_to_bv 64 (mb + 4096)) s10 s11 F fc PA kPtrArrayCommit 0 lo m9) _ mo11 K).
    { unfold mmap_CHK, MAP_FIXED_RW. apply mm_node_mmap. }
    { left. reflexivity. }
    { eapply (mmap_fixed_gen_specA P2 PDAT2 (dec_zs PA kPtrArrayCommit) (fun x r u => x = (r, u))); rewrite ?USP96;
        [ intros rsp x D; destruct (dec_zs_Some _ _ _ _ D) as (r' & u' & -> & ->); exists r', u'; split; reflexivity
        | exact SK9 | exact LOC0 | clear -CEILB LO; lia | clear -CEILB LO LOC SPH; lia | exact MI9 | exact (proj1 LST9) | reflexivity | reflexivity | reflexivity | left; reflexivity
        | exact PAA | reflexivity | unfold b_image_end; exact PQ1 | unfold kPtrArrayCommit; lia
        | rewrite mmap_len_alignedA by reflexivity; unfold kPtrArrayCommit; clear -CEILB PQ5 LOC; lia | intros; apply PSTK2; lia ]. }
    { split; [exact KIA11| exact POL11]. }
    { exact HK. }
    intros mo12 AG12 KIA12.
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK11 AG12 KIA12) as TOK12.
    pose proof (magree_frame _ _ AG12) as (Ffds12 & Fvm12 & Flz12 & Ffs12 & Fh12 & Ftid12 & _).
    pose proof (AKern_frame _ _ _ _ Fvm12 Flz12 AK11) as AK12.
    destruct (ev_commit_kernel E0 FSB0 HR0 L0 RES0 EB0 HR0_ok RES0_low (R - cost2 msz) (R' - lal_gcost) (sA a2 s) mo11 mo12 PA kPtrArrayCommit Pq Dq a TOK11 AK11 WF AG12 KIA12 PAA eq_refl
                ltac:(unfold kPtrArrayCommit; lia) ltac:(unfold kPtrArrayCommit; clear -CEILB RC; lia) ltac:(right; split; [reflexivity| split; [reflexivity| exact PT0]])) as (NUc & GRc & ALLc).
    split; [exact NUc|]. split; [exact GRc|].
    intros eff mo' HC' NR'. destruct (ALLc eff mo' HC' NR') as (-> & MMAc & -> & KIAc & KVc & LIMc & OSc & PSc & NAVc & LAVc).
    (* [comment removed for export] *)
    exists (Z_to_bv 64 PA, true). split; [change (dec_zs PA kPtrArrayCommit (zshape PA kPtrArrayCommit (Z_to_bv 64 PA) true) = Some (Z_to_bv 64 PA, true)); apply dec_zs_zshape|].
    set (a3 := lal_a3 a mb msz need).
    assert (EA3 : a3 = upd_ptr_committed (ptrc + kChunksBlockCount) a2) by (unfold a3, lal_a3; rewrite (proj2 (Z.eqb_eq _ _) EQNP); reflexivity).
    assert (P316 : as_ptr_committed a3 = kChunksBlockCount) by (rewrite EA3; cbn [as_ptr_committed upd_ptr_committed]; rewrite PT0; reflexivity).
    pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ TOK12) as (_ & _ & _ & KWF12 & _).
    assert (HLP : 0 < kPtrArrayCommit) by (unfold kPtrArrayCommit; clear; lia).
    assert (HEP : PA + kPtrArrayCommit < 2^64) by (unfold kPtrArrayCommit; clear -CEILB PQ2; lia).
    assert (PA0 : 0 <= PA) by (clear -CEILB PQ1; lia).
    pose proof (AKern_commit_ptr E0 a2 a3 mo12 (m_commit mo12 PA kPtrArrayCommit) PA kPtrArrayCommit AK12 WE (commit_maps _ _ _) PA0 HLP (proj1 (proj2 KWF12))
                  (commit_noaccess _ _ _ PA0 HLP HEP) LAVc ltac:(rewrite EA3; reflexivity) ltac:(rewrite EA3; reflexivity) ltac:(rewrite EA3; reflexivity)
                  eq_refl eq_refl PT0 P316 ltac:(intros c Hc; rewrite EA3; reflexivity)) as AK13.
    pose proof TOK12 as (_ & [O12 _] & EV12 & _).
    assert (EB3 : a_eager_bytes a3 = a_eager_bytes a2 + kPtrArrayCommit).
    { unfold a_eager_bytes. rewrite P316. change (as_ptr_committed a2) with ptrc. rewrite PT0.
      change (if kChunksBlockCount =? 0 then 0 else kPtrArrayCommit) with kPtrArrayCommit. change (if 0 =? 0 then 0 else kPtrArrayCommit) with 0.
      rewrite EA3. unfold regions_bytes, AsanState.sec_bytes, get_region. cbn [as_regions as_sec upd_ptr_committed]. clear; lia. }
    pose proof (ATOK_commit E0 FSB0 HR0 L0 RES0 EB0 (R - cost2 msz) (R' - lal_gcost) (sA a2 s) a3 (m_commit mo12 PA kPtrArrayCommit) kPtrArrayCommit
                  KIAc KVc LIMc O12 OSc EV12 RG0 PSc EB3 ltac:(rewrite EA3; reflexivity) ltac:(rewrite EA3; reflexivity) ltac:(rewrite EA3; reflexivity) ltac:(rewrite EA3; reflexivity)
                  HLP eq_refl ltac:(unfold kPtrArrayCommit; clear -CEILB RC; lia)) as TOK13.
    change (kPtrArrayCommit / 4096) with 32 in TOK13. change (sA a3 (sA a2 s)) with (sA a3 s) in TOK13.
    assert (ES3 : forall w, aSc (sA a2 s) w -> aSc (sA a3 s) w)
      by (intros w Hw; unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *; rewrite EA3; cbn [aps_alloc aps_env aps_fsbase as_sec as_residue as_store_blocks upd_ptr_committed] in *; exact Hw).
    exists (aSc (sA a3 s)), (aNc (sA a3 s)), (aEBc (sA a3 s)). split; [exact (ATOK_LI _ _ _ _ _ _ _ _ _ _ TOK13)|].
    split; [intros x Hx; unfold P2 in Hx; eapply acc_ok_lazy_sub; [| exact ES3| exact Hx]; intros e' He'; rewrite <- Flz10, <- Flz11, <- Flz12;
            destruct (LAVc e' He') as (e & He & X1 & X2 & _); exists e; split; [exact He| split; [exact X1| exact X2]]|].
    intros ms13 mo13 HQ AG13 KIA13 POL13.
    destruct HQ as (r' & u' & ra' & sp' & s4' & e4 & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m13 & E & MU13x & WM13x & MI13 & SK13 & ST13 & ZB13 & DIE & HR).
    injection HR as <- <-.
    assert (UPA : bv_unsigned (Z_to_bv 64 PA) = PA) by (apply u64_small; clear -CEILB PQ1 PQ2; lia).
    rewrite (mfr_ret_noerr (Z_to_bv 64 PA) 0) in E, SK13 by (rewrite UPA; clear -CEILB PQ1 PQ2; lia). rewrite is_err_smallL in E by (clear -CEILB PQ1 PQ2; lia).
    subst ms13. specialize (ZB13 eq_refl). clear DIE. rewrite ?USP96 in SK13. unfold mfr_W in MU13x. rewrite ?USP96 in MU13x.
    replace (ret_pc (Z_to_bv 64 LAL_RET5)) with (Z_to_bv 64 LAL_RET5) by (symmetry; apply ret_pc_even; [unfold LAL_RET5; lia| reflexivity]).
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK13 AG13 KIA13) as TOK14.
    pose proof (magree_frame _ _ AG13) as (Ffds13 & Fvm13 & Flz13 & Ffs13 & Fh13 & Ftid13 & _).
    pose proof (AKern_frame _ _ _ _ Fvm13 Flz13 AK13) as AK14.
    rewrite (mmap_len_alignedA kPtrArrayCommit eq_refl) in MU13x, ZB13. unfold kPtrArrayCommit in MU13x, ZB13.
    replace (2 ^ 17) with (8 * kChunksBlockCount) in ZB13 by reflexivity.
    assert (KC0 : 0 <= kChunksBlockCount) by (unfold kChunksBlockCount; clear; lia).
    pose proof (u64arr_of_cb_zeroZ m13 PA kChunksBlockCount KC0 ZB13) as ARR13.
    assert (LR13 : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount))) = 16384) by (rewrite repeat_length; reflexivity).
    assert (ENV3 : ENVOK E0 FSB0 (sA a3 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ TOK14).
    (* [comment removed for export] *)
    set (P3 := fun x : acc => acc_ok (m_vm_lazy mo13) (aSc (sA a3 s)) x).
    assert (PSTK3 : forall x k, lo <= x -> x + Z.of_nat k <= usp -> P3 (Z_to_bv 64 x, k))
      by (intros x k H1 H2; unfold P3; apply (pol_stack' E0 FSB0 HR0 (sA a3 s) mo13 AK14 WE ENV0); clear -CEILB H1 H2 LOC0 SPH; lia).
    assert (PDAT3 : forall x k, 0xa5000 <= x -> x + Z.of_nat k <= 0x603000 -> P3 (Z_to_bv 64 x, k))
      by (intros x k H1 H2; unfold P3; apply (pol_img' E0 FSB0 HR0 (sA a3 s) mo13 AK14 WE ENV3 ENV0); clear -CEILB H1 H2; lia).
    assert (PMAP3 : forall x k, mb <= x -> x + Z.of_nat k <= mb + msz -> P3 (Z_to_bv 64 x, k))
      by (intros x k H1 H2; unfold P3; eapply (acc_ok_of_lazy_disjoint mo13 _ mb (mb + msz));
          [apply eager_rw_lazy_disjoint; exact (proj2 (ak_sec E0 a3 mo13 AK14 sc ltac:(rewrite EA3; unfold a2, lal_a2; cbn; apply in_or_app; right; left; reflexivity)))
          | clear -CEILB RH; lia| clear -CEILB RCL; lia| exact H1| exact H2]).
    assert (PPA3 : forall x k, PA <= x -> x + Z.of_nat k <= PA + 8 * Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount))) -> P3 (Z_to_bv 64 x, k))
      by (intros x k H1 H2; unfold P3; rewrite LR13 in H2; apply (pol_ptr_head' E0 FSB0 HR0 (sA a3 s) mo13 AK14 WE); [exact P316| exact H1| unfold kPtrArrayCommit; clear -CEILB H2; lia]).
    (* [comment removed for export] *)
    assert (MU9_13 : munch [(usp - 464, usp - 96); (PA, PA + 131072)] m9 m13) by (eapply munch_weaken; [| exact MU13x]; intros y Hy; cbn in Hy |- *; clear -CEILB Hy; lia).
    assert (SEC13 : rw_cells bsegs m13 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))]) by (x13 SEC9 MU9_13 WM13x; clear -CEILB LOC LO PQ1; lia).
    assert (NRS13 : rw_cells bsegs m13 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)]) by (x13 NRS9 MU9_13 WM13x; clear -CEILB LOC LO PQ1; lia).
    assert (SST13 : rw_cells bsegs m13 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)]) by (x13 SST9 MU9_13 WM13x; clear -CEILB LOC LO PQ1; lia).
    assert (MTX13 : rw_cells bsegs m13 0xab200 [C4 (Z_to_bv 64 1)]) by (x13 MTX9 MU9_13 WM13x; clear -CEILB LOC LO PQ1; lia).
    assert (GST13 : rw_cells bsegs m13 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)]) by (x13 GST9 MU9_13 WM13x; clear -CEILB LOC LO PQ1; lia).
    assert (TST13 : rw_cells bsegs m13 (T + 2872) [C8 (Z_to_bv 64 (tmm + 1)); C8 (Z_to_bv 64 (tmd + msz))]) by (x13 TST9 MU9_13 WM13x; clear -CEILB LOC LO TQ1 TQ5 PQ1 PQ5 WE23; lia).
    assert (HDR13 : rw_cells bsegs m13 mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 need); CB 8 hj9]) by (x13 HDR9 MU9_13 WM13x; clear -CEILB LOC LO RH RCL DPA MF2 N0; lia).
    assert (FR13 : rw_cells bsegs m13 (usp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
      by (eapply rw_cells_transport; [exact FR9| exact MU9_13| exact WM13x|]; unfold lal_frame; cbn; clear -CEILB LO LOC PQ1 PQ5; lia).
    assert (BSL13 : u64arr bsegs m13 0xab000 bsl) by (eapply u64arr_transport; [exact BSL9| exact MU9_13| exact WM13x|]; rewrite LBSL; cbn; clear -CEILB LOC LO PQ1; lia).
    assert (ZREST13 : rw_cells bsegs m13 (mb + 32) [CB (Z.to_nat (msz - 32)) (repeat zb0 (Z.to_nat (msz - 32)))])
      by (eapply rw_cells_transport; [exact ZREST9| exact MU9_13| exact WM13x|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB MF2 N0; lia); cbn; clear -CEILB LOC LO RH RCL DPA MF2 N0; lia).
    assert (SH13a : rw_cells bsegs m13 (kShadowBase + mb / 8) [CB 512 (repeat (Z_to_bv 8 250) 512)]) by (x13 SH9a MU9_13 WM13x; unfold kShadowBase; clear -CEILB LOC LO RH RCL PQ1 PQ3 PQ5 HM8 MF2 N0 SHW; lia).
    assert (SH13b : rw_cells bsegs m13 (kShadowBase + mb / 8 + 512) [CB (Z.to_nat k1) (repeat zb0 (Z.to_nat k1))])
      by (eapply rw_cells_transport; [exact SH9b| exact MU9_13| exact WM13x|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB HK1; lia); cbn; unfold kShadowBase;
          clear -CEILB LOC LO RH RCL PQ1 PQ3 PQ5 HM8 HK1 HK3 N2 MF3 MF2 N0 SHW; lia).
    assert (SH13c : rw_cells bsegs m13 (kShadowBase + (mb + 4096 + need) / 8) [CB (Z.to_nat ((msz - 4096 - need) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((msz - 4096 - need) / 8)))])
      by (eapply rw_cells_transport; [exact SH9c| exact MU9_13| exact WM13x|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -CEILB HK4 HK2; lia); cbn; unfold kShadowBase;
          clear -CEILB LOC LO RH RCL PQ1 PQ3 PQ5 HM8 HK1 HK2 HK3 HK4 MF2 N0 N8 RA SHW; Z.div_mod_to_equations; lia).
    assert (LST13 : lal_statics m13) by (apply (lal_statics_agree2 m9 m13 LST9); intros x Hx Hx'; apply MU9_13; rewrite wa_unsigned by (clear -CEILB Hx; lia); cbn; clear -CEILB Hx LOC LO PQ1; lia).
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a3 s)) (aNc (sA a3 s)) (aEBc (sA a3 s)) P3).
    { eapply (lal_E2 P3 PDAT3); [exact MI13| exact NRS13| rewrite NN0; clear; lia| rewrite PT0; clear; lia| clear -CEILB RH RCL MF2 N0; lia]. }
    { split; [exact KIA13| intros x Hx; exact Hx]. }
    cbv beta. intros ms14 mo14 HQ AG14 [KIA14 POL14].
    destruct HQ as (m14 & -> & MU14 & WM14 & MI14 & NRS14).
    assert (SEC14 : rw_cells bsegs m14 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 (2^23))]) by (x911 SEC13 MU14 WM14; cbn; clear; lia).
    assert (SST14 : rw_cells bsegs m14 0xaafe0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)]) by (x911 SST13 MU14 WM14; cbn; clear; lia).
    assert (MTX14 : rw_cells bsegs m14 0xab200 [C4 (Z_to_bv 64 1)]) by (x911 MTX13 MU14 WM14; cbn; clear; lia).
    assert (GST14 : rw_cells bsegs m14 0xab218 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)]) by (x911 GST13 MU14 WM14; cbn; clear; lia).
    assert (TST14 : rw_cells bsegs m14 (T + 2872) [C8 (Z_to_bv 64 (tmm + 1)); C8 (Z_to_bv 64 (tmd + msz))]) by (x911 TST13 MU14 WM14; cbn; clear -CEILB TQ1 TQ3; lia).
    assert (HDR14 : rw_cells bsegs m14 mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 need); CB 8 hj9]) by (x911 HDR13 MU14 WM14; cbn; clear -CEILB RH; lia).
    assert (FR14 : rw_cells bsegs m14 (usp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
      by (eapply rw_cells_transport; [exact FR13| exact MU14| exact WM14|]; unfold lal_frame; cbn; clear -CEILB LO LOC; lia).
    assert (BSL14 : u64arr bsegs m14 0xab000 bsl) by (eapply u64arr_transport; [exact BSL13| exact MU14| exact WM14|]; rewrite LBSL; cbn; clear; lia).
    assert (ARR14 : u64arr bsegs m14 PA (repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount)))
      by (eapply u64arr_transport; [exact ARR13| exact MU14| exact WM14|]; cbn [map fst snd]; rewrite LR13; cbn; clear -CEILB PQ1; lia).
    assert (ZREST14 : rw_cells bsegs m14 (mb + 32) [CB (Z.to_nat (msz - 32)) (repeat zb0 (Z.to_nat (msz - 32)))]) by (x911 ZREST13 MU14 WM14; rewrite Z2Nat.id by (clear -CEILB MF2 N0; lia); cbn; clear -CEILB RH; lia).
    assert (SH14a : rw_cells bsegs m14 (kShadowBase + mb / 8) [CB 512 (repeat (Z_to_bv 8 250) 512)]) by (x911 SH13a MU14 WM14; unfold kShadowBase; cbn; clear -CEILB RH HM8; lia).
    assert (SH14b : rw_cells bsegs m14 (kShadowBase + mb / 8 + 512) [CB (Z.to_nat k1) (repeat zb0 (Z.to_nat k1))]) by (x911 SH13b MU14 WM14; rewrite Z2Nat.id by (clear -CEILB HK1; lia); unfold kShadowBase; cbn; clear -CEILB RH HM8 HK1; lia).
    assert (SH14c : rw_cells bsegs m14 (kShadowBase + (mb + 4096 + need) / 8) [CB (Z.to_nat ((msz - 4096 - need) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((msz - 4096 - need) / 8)))])
      by (x911 SH13c MU14 WM14; rewrite Z2Nat.id by (clear -CEILB HK4 HK2; lia); unfold kShadowBase; cbn; clear -CEILB RH HM8 HK2 HK4 N8 RA N0; Z.div_mod_to_equations; lia).
    assert (LST14 : lal_statics m14) by (apply (lal_statics_agree2 m13 m14 LST13); intros x Hx Hx'; apply MU14; rewrite wa_unsigned by (clear -CEILB Hx; lia); cbn; clear -CEILB Hx Hx'; lia).
    assert (SK14 : stk bsegs m14 lo (usp - 96)) by (eapply (stk_transport_disjoint bsegs); [exact SK13| exact MU14| exact WM14|]; cbn; clear -CEILB LOC LO; lia).
    (* [comment removed for export] *)
    eapply (srzA_seg bsegs (aSc (sA a3 s)) (aNc (sA a3 s)) (aEBc (sA a3 s)) P3).
    { eapply (lal_D P3 PDAT3);
        [ exact SK14 | exact LOC0 | clear -CEILB LO; lia | exact SPH | exact MI14 | exact FR14 | exact SEC14 | exact NRS14 | exact SST14 | exact BSL14 | exact LBSL | exact MTX14 | exact GST14 | exact ARR14
        | rewrite repeat_length, NN0; unfold kChunksBlockCount; clear; lia | exact HDR14 | exact N0 | clear -CEILB N2; lia | clear -CEILB RH; lia | exact RCL0 | exact PQ1
        | rewrite LR13; clear -CEILB PQ5; lia | rewrite LR13; clear -CEILB DPA; lia | rewrite NN0; clear; lia
        | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | clear -CEILB HV; lia | exact PSTK3
        | intros; apply PMAP3; [lia| clear -CEILB H0 MF2 N0; lia] | exact PPA3 ]. }
    { split; [exact KIA14| exact POL14]. }
    cbv beta. intros ms15 mo15 HQ AG15 [KIA15 POL15].
    destruct HQ as (w11 & w12 & w13 & w14 & w15 & w16 & bsl' & m15 & -> & MU15 & WM15 & MI15 & SK15 & NRS15 & SST15 & BSL15 & LBSL15 & MTX15 & GST15 & ARR15 & HDR15).
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK14 (magree_trans _ _ _ AG14 AG15) KIA15) as TOK15.
    pose proof (magree_frame _ _ (magree_trans _ _ _ AG14 AG15)) as (Ffds15 & Fvm15 & Flz15 & Ffs15 & Fh15 & Ftid15 & _).
    pose proof (AKern_frame _ _ _ _ Fvm15 Flz15 AK14) as AK15.
    apply CONT_OK. unfold lal_post_ok. rewrite USP. rewrite (proj2 (Z.eqb_eq n ptrc) EQNP).
    exists v0, v1, v2, w11, w12, w13, w14, w15, w16, c7, v3, v4, v5, v6, m15, mb, (repeat zb0 (Z.to_nat k1)), bsl', (upd (repeat (Z_to_bv 64 0) (Z.to_nat kChunksBlockCount)) (Z.to_nat n) (Z_to_bv 64 mb)).
    split; [reflexivity|]. split; [exact MI15|]. split; [exact SK15|].
    split; [unfold lal_W; cbn [app];
            eapply munch_trans; [eapply munch_weaken; [| exact MU13]| eapply munch_trans; [eapply munch_weaken; [| exact MU39]| eapply munch_trans; [eapply munch_weaken; [| exact MU9_13]|
              eapply munch_trans; [eapply munch_weaken; [| exact MU14]| eapply munch_weaken; [| exact MU15]]]]];
            intros y Hy; cbn in Hy |- *; unfold kShadowBase, kPtrArrayCommit in *;
            [clear -CEILB Hy| clear -CEILB Hy RH RCL MF2 N0 TQ1 DT HK0 HK1 HK2| clear -CEILB Hy | clear -CEILB Hy| clear -CEILB Hy MF2 N0 NN0]; lia|].
    split; [exact (wmono_trans _ _ _ _ WM13 (wmono_trans _ _ _ _ WM39 (wmono_trans _ _ _ _ WM13x (wmono_trans _ _ _ _ WM14 WM15))))|].
    split; [exact RA|]. split; [exact RPL|]. split; [exact RSV|]. split; [exact GKF1|]. split; [exact GKF2|]. split; [exact GKF3|]. split; [exact GV1|]. split; [exact GV2|]. split; [exact MTX15|].
    split; [unfold lal_a3; rewrite (proj2 (Z.eqb_eq _ _) EQNP); cbn [as_ptr_committed upd_ptr_committed]; change (as_ptr_committed (lal_a2 a mb msz need)) with ptrc; exact NRS15|].
    split; [exact SST15|]. split; [exact BSL15|]. split; [exact LBSL15|]. split; [exact GST15|]. split; [exact ARR15|]. split; [reflexivity|]. split; [exact HDR15|].
    split; [x911 ZREST14 MU15 WM15; rewrite Z2Nat.id by (clear -CEILB MF2 N0; lia); djs; clear -CEILB RH RCL MF2 N0 PQ1 PQ5 DPA NLT LG NN0; lia|].
    split; [x911 SH14a MU15 WM15; unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 PQ1 PQ3 PQ5 DPA NLT HM8 LG NN0 SHW; lia|].
    split; [x911 SH14b MU15 WM15; rewrite Z2Nat.id by (clear -CEILB HK1; lia); unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 PQ1 PQ3 PQ5 DPA NLT HM8 HK1 HK3 LG NN0 SHW; lia|].
    split; [x911 SH14c MU15 WM15; rewrite Z2Nat.id by (clear -CEILB HK2 HK4; lia); unfold kShadowBase; djs; clear -CEILB RH RB RCL MF2 N0 N8 RA PQ1 PQ3 PQ5 DPA NLT HM8 HK1 HK2 HK3 HK4 LG NN0 SHW; Z.div_mod_to_equations; lia|].
    split; [x911 TST14 MU15 WM15; djs; clear -CEILB RH RCL MF2 N0 TQ1 TQ3 TQ5 PQ1 PQ5 DT WE23 NLT LG NN0; lia|].
    split; [apply (lal_statics_agree2 m14 m15 LST14); intros x Hx Hx'; apply MU15; rewrite wa_unsigned by (clear -CEILB Hx; lia); djs; clear -CEILB Hx Hx' PQ1 RH LG NLT NN0; lia|].
    split; [apply (ATOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s a3); [exact TOK15| apply lal_state_fp]|].
    split; [apply (AKern_ext' E0 a3); [| | | | | exact AK15]; pose proof (lal_state_fp a mb msz need) as (X1 & X2 & X3 & X4 & X5 & X6); fold a3 in X2, X3, X5, X6;
            [| exact X3| exact X2| exact X5| exact X6]; unfold lal_state, lal_commit, a3, lal_a3, a2, lal_a2, n_chunks; cbn; destruct (Z.of_nat (length (as_sec a)) =? as_ptr_committed a); reflexivity|].
    rewrite Ffs15, Ffds15, Ftid15, Ffs13, Ffds13, Ftid13.
    change (m_fs (m_commit mo12 PA kPtrArrayCommit)) with (m_fs mo12). change (m_fds (m_commit mo12 PA kPtrArrayCommit)) with (m_fds mo12). change (m_tid (m_commit mo12 PA kPtrArrayCommit)) with (m_tid mo12).
    rewrite Ffs12, Ffds12, Ftid12, Ffs11, Ffds11, Ftid11, Ffs10, Ffds10, Ftid10, Ffs3, Ffds3, Ftid3.
    change (m_fs (m_anon mo2 mb msz)) with (m_fs mo2). change (m_fds (m_anon mo2 mb msz)) with (m_fds mo2). change (m_tid (m_anon mo2 mb msz)) with (m_tid mo2).
    rewrite Ffs2, Ffds2, Ftid2, Ffs1, Ffds1, Ftid1. split; [reflexivity| split; reflexivity].
Qed.
End LAL.
End RC__1.
