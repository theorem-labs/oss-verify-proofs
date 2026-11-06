(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 537 of its 623 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/relay_finish_seg.v, with its module names changed; 787 of its 829 lines of code are new or changed and 581 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/list_push.v, with its module paths and module names changed; 625 of its 676 lines of code are new or changed and 778 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Open Scope Z_scope.

Lemma lfx_jmp : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x154a0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step.
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_drop_c list_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import list_free_run KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF ListTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.

Lemma lfx_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lfx_ok_b8 : YK0s.ret_ok (Z_to_bv 64 0x154b8).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

Lemma lfx_ok_c4 : YK0s.ret_ok (Z_to_bv 64 0x154c4).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

Lemma lfx_cs : forall (P : Z -> Prop), P 2 -> P 3 -> P 4 -> P 8 -> P 9 -> P 18 -> P 19 -> P 20 -> P 21 -> P 22 ->
  P 23 -> P 24 -> P 25 -> P 26 -> P 27 -> forall r, callee_saved r -> P r.
Proof.
  intros P H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; assumption|]); subst r; assumption.
Qed.

Lemma lfx_ndf : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l x a b ND. induction l as [|[y c] l IH]; intros Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hy ND].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - inversion Ea; inversion Eb; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hy. exact (in_map fst _ _ Hb).
  - inversion Eb; subst. exfalso. apply Hy. exact (in_map fst _ _ Ha).
  - exact (IH ND Ha Hb).
Qed.

Lemma lfx_skipn_cons : forall {X} (l : list X) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] d H; cbn in *; [lia | lia | reflexivity | apply IH; lia]. Qed.

Lemma lfx_nth_firstn : forall {X} (l : list X) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros X l. induction l as [|x l IH]; intros [|n] [|k] d H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma lfx_drop_recs : forall {X} (l : list X) k, (S k <= length l)%nat ->
  firstn k (firstn (S k) l) ++ skipn (S k) (firstn (S k) l) = firstn k l.
Proof.
  intros X l k H. rewrite firstn_firstn, Nat.min_l by lia.
  rewrite skipn_all2 by (rewrite firstn_length_le by lia; lia). apply app_nil_r.
Qed.

Lemma lfx_in_mid : forall {X} (b1 b2 : list X) x y, In y (b1 ++ x :: b2) -> y <> x -> In y (b1 ++ b2).
Proof.
  intros X b1 b2 x y H Ne. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma lfx_in_mid2 : forall {X} (b1 b2 : list X) x y, In y (b1 ++ b2) -> In y (b1 ++ x :: b2).
Proof.
  intros X b1 b2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma lfx_nd_mid : forall (b1 b2 : list (Z * Z)) q n q' n', List.NoDup (map fst (b1 ++ (q, n) :: b2)) ->
  In (q', n') (b1 ++ b2) -> q' <> q.
Proof.
  intros b1 b2 q n q' n' ND H E. subst q'. rewrite map_app in ND. cbn [map fst] in ND.
  apply List.NoDup_remove_2 in ND. apply ND. rewrite <- map_app. exact (in_map fst _ (q, n') H).
Qed.

Lemma lfx_firstn_S : forall {X} (l : list X) k x, In x (firstn k l) -> In x (firstn (S k) l).
Proof.
  intros X l. induction l as [|y l IH]; intros [|k] x H; cbn in *;
    [destruct H | destruct H | destruct H | destruct H as [H|H]; [left; exact H | right; apply IH, H]].
Qed.

Definition lfx_drops_t (rs : list (tad * list Z)) (k : nat) : list tev := recs_drop_tr (List.rev (skipn k rs)).

Lemma lfx_drops_t_step : forall rs k d, (k < length rs)%nat ->
  lfx_drops_t rs k = lfx_drops_t rs (S k) ++ rec_drop_tr (nth k rs d).
Proof.
  intros rs k d H. unfold lfx_drops_t, recs_drop_tr. rewrite (lfx_skipn_cons rs k d H). cbn [List.rev].
  rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma nret_lfx_drops_t : forall rs k, nretF (lfx_drops_t rs k) = 0%nat.
Proof. intros rs k. apply nret_recs_drop. Qed.

Lemma lfx_rec_drop_t : forall (nm : Z -> tad) (r : Z * list byte),
  rec_drop_tr (shr nm r) = [RFree (Z.of_nat (length (snd r)) + 1) (nm (fst r))].
Proof. intros nm r. unfold rec_drop_tr, rec_len, shr, bzs. cbn [fst snd]. rewrite length_map. reflexivity. Qed.

Lemma lfx_drop_tr_at : forall (nm : Z -> tad) (l : hlist) k, (k < length (hl_recs l))%nat ->
  list_drop_tr (sh_of nm l) k =
  [RFree (Z.of_nat (length (snd (nth k (hl_recs l) (0, [])))) + 1) (nm (fst (nth k (hl_recs l) (0, []))))].
Proof.
  intros nm l k H. unfold list_drop_tr, sh_of. cbn [sh_recs].
  rewrite nth_indep with (d' := shr nm (0, [])) by (rewrite length_map; exact H).
  rewrite map_nth. apply lfx_rec_drop_t.
Qed.

Lemma lfx_runF_app0 : forall F qs b (t1 t2 : trF), nretF t1 = 0%nat ->
  runF F qs b (t1 ++ t2) = runF F qs (runF F qs b t1) t2.
Proof. intros F qs b t1 t2 H. unfold runF, run_tr. rewrite run_from_app, H. reflexivity. Qed.

Lemma lfx_rw_munch : forall segs W m m' a cs, rw_cells segs m a cs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0 <= a + i < 2 ^ 64 /\ outside W (a + i)) ->
  rw_cells segs m' a cs.
Proof.
  intros segs W m m' a cs H MU D. apply (rw_cells_transfer segs m); [exact H|].
  intros i Hi. destruct (D i Hi) as [R O].
  split; [exact (munch_mbyte segs W m m' (a + i) MU R O) | apply (munch_writable segs W m m' (a + i) MU R O)].
Qed.

Section LFU.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable Fr : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis NDB : blocks_nodup Bm API.
Hypothesis ERRNO_LOW : errno_addr Bm + 4 <= YM05.alloc_ceiling.
Hypothesis HFREE : ms_free Bm = 0x15f4c.
Local Notation MR := (aa_MR API).

Lemma lfx_blk : forall L1 A1 m1 md1 q k, MR L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) ->
  4096 <= q /\ q + k <= YM05.alloc_ceiling.
Proof.
  intros L1 A1 m1 md1 q k HM H. destruct (lf_blocks_in L1 A1 q k H) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L1 A1 m1 md1 p k HM Hp).
Qed.

Lemma lfx_list_at_munch : forall L1 A1 m m' a0 lk ln W, list_at Bm L1 A1 m a0 lk ln -> munch W m m' ->
  (forall a, (a0 <= a < a0 + 16 \/ exists q k, In (q, k) (blocks L1 A1) /\ q <= a < q + k) ->
     0 <= a < 2 ^ 64 /\ outside W a) ->
  list_at Bm L1 A1 m' a0 lk ln.
Proof.
  intros L1 A1 m m' a0 lk ln W (HD & NC & AR & ND & NV & RC) MU HO.
  split.
  { apply (lfx_rw_munch _ W m m' _ _ HD MU). intros i Hi. apply HO. left. cbn [cells_size csize] in Hi. lia. }
  split; [exact NC|].
  split.
  { destruct AR as [X|(C1 & C2 & C3 & C4 & C5)]; [left; exact X|right].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    apply (lfx_rw_munch _ W m m' _ _ C5 MU). intros i Hi. apply HO. right. exists (hl_v lk), (16 * hl_cap lk).
    split; [exact C2|]. cbn [cells_size csize] in Hi. lia. }
  split; [exact ND|]. split; [exact NV|].
  eapply Forall_impl; [|exact RC]. intros r (R1 & R2 & R3 & R4 & R5).
  split; [exact R1|]. split; [exact R2|]. split; [|split; [exact R4 | exact R5]].
  apply (lfx_rw_munch _ W m m' _ _ R3 MU). intros i Hi. apply HO. right.
  exists (fst r), (Z.of_nat (length (snd r)) + 1).
  split; [exact R1|]. cbn [cells_size csize] in Hi. lia.
Qed.

Lemma lfx_jmp_sr : forall R pc m md1 (P : config -> Prop), pc = Z_to_bv 64 0x154b8 ->
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  (forall R', (forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
     SR rsegs (mkCfg (YK11.mkst R' (Z_to_bv 64 0x154a0) m (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (YK11.mkst R pc m (seg_rom rsegs)) md1) P.
Proof.
  intros R pc m md1 P -> Hh Hl K.
  eapply (kseg_raw R (Z_to_bv 64 0x154b8) m md1); [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. apply lfx_jmp. }
  { intros s0 ->. do 3 eexists. reflexivity. }
  intros R0 pc' m0 R' HQ GR.
  injection HQ as ER EP EM. subst pc' m0.
  assert (GR' : forall r, getr R' r = getr R0 r) by exact GR.
  subst R0. apply K. apply lfx_cs; cbv beta; rewrite GR'; reflexivity.
Qed.

Lemma lfx_sptr_keep : forall K sp E F L1 A1 m1 md1 L2 A2 m2 md2 a n,
  rmid Bm API K sp E F L1 A1 m1 md1 L2 A2 m2 md2 ->
  NoDup (map fst (blocks L1 A1)) -> NoDup (map fst (blocks L2 A2)) ->
  In (a, n) (blocks L1 A1) -> 0 < n -> ~ F a -> sptr_of L2 A2 a = sptr_of L1 A1 a.
Proof.
  intros K sp E F L1 A1 m1 md1 L2 A2 m2 md2 a n (_ & _ & _ & _ & _ & PA & SV & _) N N' Hin Hn HF.
  destruct (sptr_of_spec L1 A1 a n N Hin) as (Hp & Ha).
  assert (HF' : ~ F (ptr_addr L1 (sptr_of L1 A1 a))) by (rewrite Ha; exact HF).
  pose proof (SV _ _ Hp Hn HF') as Hp'.
  pose proof (PA _ _ Hp Hp' HF') as Ea.
  rewrite <- Ha at 1. rewrite <- Ea. exact (sptr_of_eq L2 A2 _ n N' Hp').
Qed.

Section Run.
Hypothesis SEG : ms_segs Bm = rsegs.
Hypothesis LDC : list_drop_contract Bm API Fr.
Hypothesis FRC : free_contract_rt Bm API Fr.
Hypothesis FNC : free_null_contract Bm.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (bnd : rt_R Fr) (l : hlist) (lines : bool).

Local Notation LA := (bv_unsigned (getr regs (Z_to_bv 5 10))).
Local Notation S0 := (spZ regs).
Local Notation SRS := (map (shr (known_at L A)) (hl_recs l)).

Hypothesis PRE : call_pre_k Bm MR LIST_FREE_K L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis RO : ro_agree (ms_segs Bm) mem.
Hypothesis PLR : forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr (ms_segs Bm) (Z_to_bv 64 a) = false.
Hypothesis LAL : LA mod 8 = 0.
Hypothesis LST : list_at Bm L A mem LA l lines.
Hypothesis RES : rt_ok Fr A bnd.

Definition lfE (a : Z) : Prop := LA <= a < LA + 16.
Definition lfF (q : Z) : Prop := In q (list_blocks l).

Definition lfval (r : Z) : word :=
  match r with
  | 2 => Z_to_bv 64 (S0 + -16)
  | 8 => Z_to_bv 64 LA
  | _ => getr regs (Z_to_bv 5 r)
  end.

Definition lfRF (R : bvmap 5 word) : Prop := forall r, callee_saved r -> getr R (Z_to_bv 5 r) = lfval r.

Definition lfJ (k : nat) (lk : hlist) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model) : Prop :=
  rmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L1 A1 m1 md1 /\
  st_init_done A1 = true /\ ro_agree (ms_segs Bm) m1 /\
  rt_ok Fr A1 (runF Fr [] bnd (lfx_drops_t SRS k)) /\
  list_at Bm L1 A1 m1 LA lk lines /\ hl_v lk = hl_v l /\ hl_cap lk = hl_cap l /\ hl_recs lk = firstn k (hl_recs l) /\
  (0 < hl_cap l -> sptr_of L1 A1 (hl_v l) = sptr_of L A (hl_v l)) /\
  (forall r, In r (firstn k (hl_recs l)) -> sptr_of L1 A1 (fst r) = sptr_of L A (fst r)) /\
  rw_cells (ms_segs Bm) m1 (S0 - 16) [C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] /\
  (list_blocks l = [] -> blocks L1 A1 = blocks L A) /\
  (forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks l) -> In (q, n) (blocks L1 A1)) /\
  (forall q n, In (q, n) (blocks L1 A1) -> In (q, n) (blocks L A) /\ ~ In q (map fst (skipn k (hl_recs l)))).

Definition LPOST (c' : config) : Prop :=
  exists L' A' regs' mem' md',
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom (ms_segs Bm))) md' /\
    relay_post Bm API LIST_FREE_K (fun a => LA <= a < LA + 16) (fun q => In q (list_blocks l))
      L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (list_free_tr (sh_of (known_at L A) l)) /\
       rt_ok Fr A' (runF Fr qs bnd (list_free_tr (sh_of (known_at L A) l)))) /\
    ro_agree (ms_segs Bm) mem' /\
    list_at Bm L' A' mem' LA empty_list lines /\
    (list_blocks l = [] -> blocks L' A' = blocks L A) /\
    (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (list_blocks l)).

Lemma gfacts : MR L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\ S0 mod 16 = 0 /\
  YM05.alloc_ceiling + LIST_FREE_K <= S0 /\ S0 < 2 ^ 63 /\
  (forall a, S0 - LIST_FREE_K <= a < S0 -> writable_at (ms_segs Bm) mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp Bm) /\
  (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> writable_at (ms_segs Bm) mem a) /\
  2 ^ 46 <= YM05.alloc_ceiling /\ YM05.alloc_ceiling < 2 ^ 47 /\ 0 <= LA /\ LA + 16 <= 2 ^ 21 /\
  LIST_FREE_K = 8256.
Proof.
  pose proof PRE as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (P0 : LA <= LA < LA + 16) by lia.
  assert (P15 : LA <= LA + 15 < LA + 16) by lia.
  pose proof (in_img_low Bm SEG LA (proj1 (proj1 (PLR LA P0)))) as L0.
  pose proof (in_img_low Bm SEG (LA + 15) (proj1 (proj1 (PLR (LA + 15) P15)))) as L1.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HRA|]. split; [exact HAL|].
  split; [exact HCE|]. split; [exact H63|]. split; [exact HWS|]. split; [exact HTP|].
  split; [exact HER|]. split; [lia|]. split; [exact ACL|]. split; [lia|]. split; [lia|]. reflexivity.
Qed.

Lemma lfx_keep : forall R R', lfRF R -> (forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
  lfRF R'.
Proof. intros R R' H K r Hr. rewrite (K r Hr). exact (H r Hr). Qed.

Lemma lfx_sp : forall R, lfRF R -> spZ R = S0 - 16.
Proof.
  intros R RF. pose proof gfacts as (_ & _ & _ & _ & _ & HCE & H63 & _ & _ & _ & AC1 & _ & _ & _ & EK).
  transitivity (bv_unsigned (getr R (Z_to_bv 5 2))); [reflexivity|].
  rewrite (RF 2 ltac:(unfold callee_saved; lia)). cbn [lfval]. rewrite hg_unsigned by lia. lia.
Qed.

Lemma lfx_tp : forall R, lfRF R -> getr R (Z_to_bv 5 4) = Z_to_bv 64 (ms_tp Bm).
Proof.
  intros R RF. pose proof gfacts as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _).
  rewrite (RF 4 ltac:(unfold callee_saved; lia)). cbn [lfval]. exact HTP.
Qed.

Lemma tail : forall Ex L2 A2 R2 m2 md2 (v c : word) pc, pc = Z_to_bv 64 0x154c4 ->
  rmid Bm API LIST_FREE_K S0 Ex lfF L A mem md L2 A2 m2 md2 ->
  (forall a, Ex a -> lfE a \/ (a < YM05.alloc_ceiling /\ ~ in_img Bm a /\
     forall p n, In (p, n) (user_blocks A) -> ~ lfF (ptr_addr L p) -> ~ (ptr_addr L p <= a < ptr_addr L p + n))) ->
  st_init_done A2 = true -> ro_agree (ms_segs Bm) m2 ->
  rt_ok Fr A2 (runF Fr [] bnd (list_free_tr (sh_of (known_at L A) l))) -> lfRF R2 ->
  rw_cells (ms_segs Bm) m2 LA [C8 v; C4 (Z_to_bv 64 0); C4 c] ->
  rw_cells (ms_segs Bm) m2 (S0 - 16) [C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))] ->
  (list_blocks l = [] -> blocks L2 A2 = blocks L A) ->
  (forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks l) -> In (q, n) (blocks L2 A2)) ->
  (forall q n, In (q, n) (blocks L2 A2) -> In (q, n) (blocks L A) /\ ~ In q (list_blocks l)) ->
  SR rsegs (mkCfg (YK11.mkst R2 pc m2 (seg_rom rsegs)) md2) LPOST.
Proof.
  intros Ex L2 A2 R2 m2 md2 v c pc -> RM2 EXS IN2 RO2 RS2 RF2 HD2 FR2 BE2 BA2 BB2.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1 & EK).
  pose proof (aa_laws API) as LAWS.
  pose proof RM2 as (M2 & W2 & B2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  destruct (mr_model _ _ LAWS _ _ _ _ M2) as (Hh2 & Hl2 & _).
  assert (SPr : bv_unsigned (getr regs (Z_to_bv 5 2)) = S0) by reflexivity.
  assert (RO2r : ro_agree rsegs m2) by (rewrite <- SEG; exact RO2).
  assert (HD2n : rw_cells rsegs (normalize rsegs m2) LA [C8 v; C4 (Z_to_bv 64 0); C4 c]).
  { apply (rw_cells_normalize rsegs m2 _ _ RO2r); [rewrite <- SEG; exact HD2|].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite <- SEG. exact (proj2 (PLR (LA + i) ltac:(lia))). }
  assert (FR2n : rw_cells rsegs (normalize rsegs m2) (S0 + -16)
                   [C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))]).
  { replace (S0 + -16) with (S0 - 16) by lia. apply (rw_cells_normalize rsegs m2 _ _ RO2r); [rewrite <- SEG; exact FR2|].
    intros i Hi. cbn [cells_size csize] in Hi. apply ro_addr_hi. lia. }
  assert (G2 : getr R2 (Z_to_bv 5 2) = Z_to_bv 64 (S0 + -16)) by exact (RF2 2 ltac:(unfold callee_saved; lia)).
  assert (G8 : getr R2 (Z_to_bv 5 8) = Z_to_bv 64 LA) by exact (RF2 8 ltac:(unfold callee_saved; lia)).
  eapply (kseg R2 (Z_to_bv 64 0x154c4) m2 md2); [exact lfx_wx | exact RO2r | exact Hh2 | exact Hl2 | | |].
  { unfold Regs6ss.mkR_of. eapply lfu_tail with (LA := LA) (B := S0 + -16).
    - exact G8.
    - lia.
    - lia.
    - exact G2.
    - lia.
    - lia.
    - left. lia.
    - apply mem_inv_normalize.
    - exact HD2n.
    - exact FR2n. }
  { intros s0 (m' & -> & _). do 3 eexists. reflexivity. }
  intros R pc' m0 regs3 m3 HQ GR MREL ROS.
  destruct HQ as (m0' & EQ & MU & WM & MI & HZ & FZ).
  injection EQ as ER EP EM. subst pc' m0.
  assert (GR3 : forall r, getr regs3 r = getr R r) by exact GR.
  subst R. clear GR.
  destruct (rmid_norm Bm API LIST_FREE_K S0 lfE lfF L2 A2 m2 md2 m0' m3 [(LA, LA + 16)]
              SEG RO2r MREL ROS MU WM M2 W2 B2 ltac:(lia) SC2) as (RM3 & MU3 & WM3).
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-.
    right. unfold lfE. lia. }
  { intros a Ho. apply hg_out. intros lo hi [E|[]]. injection E as <- <-.
    destruct (Z_lt_le_dec a LA) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (LA + 16) a) as [D'|D']; [right; exact D'|].
    exfalso. exact (hg_img_not_owned Bm API AX L2 A2 m2 md2 a M2 (proj1 (PLR a ltac:(lia))) Ho). }
  { intros p n j Hp Hj O. exfalso. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-.
    apply (ax_blocks_img AX L2 A2 m2 md2 p n j M2 Hp Hj).
    exact (proj1 (proj1 (PLR (ptr_addr L2 p + j) ltac:(lia)))). }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM2 RM3) as RMall.
  assert (PR3 : forall r, callee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { apply lfx_cs; cbv beta; rewrite GR3.
    { transitivity (Z_to_bv 64 (S0 + -16 + 16)); [reflexivity|].
      replace (S0 + -16 + 16) with S0 by lia. rewrite <- SPr. apply Z_to_bv_bv_unsigned. }
    all: first [reflexivity | match goal with |- _ = getr regs (Z_to_bv 5 ?n) =>
           transitivity (getr R2 (Z_to_bv 5 n)); [reflexivity | exact (RF2 n ltac:(unfold callee_saved; lia))] end]. }
  apply SR_ret. exists L2, A2, regs3, m3, md2.
  split; [rewrite SEG; f_equal; f_equal; exact (ret_pc_of_ok _ HRA)|].
  split.
  { apply (rp_shrink Bm API LIST_FREE_K (fun a => Ex a \/ lfE a)).
    - apply rp_join.
      + apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMall); [intros a X; exact X | intros q [X|X]; exact X].
      + exact PR3.
    - intros a [X|X]; [exact (EXS a X) | left; exact X]. }
  split; [exact IN2|]. split; [exists []; split; [exact (eq_sym (nret_list_free _)) | exact RS2]|].
  split; [rewrite SEG; exact (ro_agree_same rsegs m2 m3 RO2r ROS)|].
  split.
  { unfold list_at. split; [rewrite SEG; exact (rw_cells_of_rel rsegs m3 m0' _ _ MREL HZ)|].
    split; [unfold hl_n, empty_list; cbn [hl_recs hl_cap length]; lia|]. split; [left; split; reflexivity|].
    split; [constructor|]. split; [intros []|]. constructor. }
  split; [exact BE2|]. split; [exact BA2|]. exact BB2.
Qed.

Lemma fin : forall lk L1 A1 R1 m1 md1, lfJ 0 lk L1 A1 m1 md1 -> lfRF R1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x154a0) m1 (seg_rom rsegs)) md1) LPOST.
Proof.
  intros lk L1 A1 R1 m1 md1 (RM1 & IN1 & RO1 & RS1 & LT1 & HV1 & HC1 & HR1 & VX1 & SX1 & FR1 & BE1 & BA1 & BB1) RF1.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1 & EK).
  pose proof (aa_laws API) as LAWS.
  assert (EA : ALLOC_STACK = 8192) by reflexivity.
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & _).
  assert (HN1 : hl_n lk = 0) by (unfold hl_n; rewrite HR1; reflexivity).
  destruct LT1 as (HD1 & NC1 & AR1 & _).
  rewrite HN1, HV1, HC1 in HD1. rewrite HV1, HC1 in AR1.
  assert (HD1r : rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (hl_cap l))])
    by (rewrite <- SEG; exact HD1).
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEG; exact RO1).
  assert (G8 : getr R1 (Z_to_bv 5 8) = Z_to_bv 64 LA) by exact (RF1 8 ltac:(unfold callee_saved; lia)).
  eapply (kseg_raw R1 (Z_to_bv 64 0x154a0) m1 md1); [exact Hh1 | exact Hl1 | | |].
  { unfold Regs6ss.mkR_of. eapply lfu_head_free with (LA := LA); [exact G8 | lia | lia | exact HD1r]. }
  { intros s0 ->. do 3 eexists. reflexivity. }
  intros R pc' m0 regs2 HQ GR.
  injection HQ as ER EP EM. subst pc' m0.
  assert (GR2 : forall r, getr regs2 r = getr R r) by exact GR.
  subst R. clear GR.
  assert (KEEP2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r))
    by (apply lfx_cs; cbv beta; rewrite GR2; reflexivity).
  assert (RF2 : lfRF regs2) by exact (lfx_keep R1 regs2 RF1 KEEP2).
  assert (G2_1 : getr regs2 1 = Z_to_bv 64 0x154c4) by (rewrite GR2; reflexivity).
  assert (G2_10 : getr regs2 10 = Z_to_bv 64 (hl_v l)) by (rewrite GR2; reflexivity).
  assert (RA2 : YK0s.ret_ok (getr regs2 1)) by exact (eq_ind_r YK0s.ret_ok lfx_ok_c4 G2_1).
  assert (SP2 : spZ regs2 = S0 - 16) by exact (lfx_sp regs2 RF2).
  assert (TR : list_free_tr (sh_of (known_at L A) l) = lfx_drops_t SRS 0 ++
                 (if hl_cap l =? 0 then [] else [RFree (16 * hl_cap l) (Known (sptr_of L A (hl_v l)))])) by reflexivity.
  destruct AR1 as [(C0 & V0) | (CP & VB1 & _)].
  - pose proof FNC as FN. unfold free_null_contract in FN. rewrite HFREE, SEG in FN.
    eapply SR_bind.
    { apply (FN regs2 m1 md1); [exact RA2 | exact (eq_trans G2_10 (f_equal (Z_to_bv 64) V0)) | exact Hh1 | exact Hl1]. }
    intros c ->.
    apply (tail lfE L1 A1 regs2 m1 md1 (Z_to_bv 64 (hl_v l)) (Z_to_bv 64 (hl_cap l)) _ G2_1 RM1).
    + intros a X. left. exact X.
    + exact IN1.
    + exact RO1.
    + rewrite TR, C0. cbn [Z.eqb]. rewrite app_nil_r. exact RS1.
    + exact RF2.
    + exact HD1.
    + exact FR1.
    + exact BE1.
    + exact BA1.
    + intros q n H. destruct (BB1 q n H) as [H1 H2]. split; [exact H1|]. unfold list_blocks. rewrite C0.
      cbn [Z.eqb app]. exact H2.
  - assert (CNZ : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (VF : lfF (hl_v l)) by (unfold lfF, list_blocks; rewrite CNZ; left; reflexivity).
    destruct (lf_blocks_in L1 A1 (hl_v l) (16 * hl_cap l) VB1) as (p & Hp & Ep).
    assert (ND1 : List.NoDup (map fst (blocks L1 A1))).
    { first [exact (NDB L1 A1 m1 md1 M1) | apply NoDup_ListNoDup; exact (NDB L1 A1 m1 md1 M1)]. }
    assert (CP2 : call_pre Bm MR L1 A1 regs2 m1 md1).
    { apply call_pre_k_alloc.
      eapply cpk_of_rmid; [exact RM1 | exact IN1 | exact RA2 | exact (lfx_tp regs2 RF2)
                           | rewrite SP2; clear - HAL; Z.div_mod_to_equations; lia | rewrite SP2; lia
                           | rewrite SP2; lia | lia | rewrite SP2; lia | rewrite SP2; lia]. }
    assert (ESP : sptr_of L1 A1 (hl_v l) = p) by (rewrite <- Ep; exact (sptr_of_eq L1 A1 p _ (NDB L1 A1 m1 md1 M1) Hp)).
    pose proof FRC as FC. unfold free_contract_rt in FC. rewrite HFREE, SEG in FC.
    eapply SR_bind.
    { apply (FC L1 A1 regs2 m1 md1 p (16 * hl_cap l) (runF Fr [] bnd (lfx_drops_t SRS 0)) CP2 RO1r Hp);
        [rewrite Ep; exact G2_10 | exact RS1]. }
    intros c (L2 & A2 & regs3 & m2 & md2 & -> & CPo & (b1 & b2 & EB1 & EB2) & _ & RO2 & _ & SURV & INI & LN & RS2).
    rewrite Ep in CPo, EB1.
    apply call_post_k_alloc in CPo.
    pose proof (YO10.user_block_ptrs_NoDup A1 W1) as NDp.
    destruct (rmid_of_cpk Bm API ALLOC_STACK _ (fun x => x = hl_v l) L1 A1 regs2 m1 md1 L2 A2 regs3 m2 md2
                AX CTX M1 CPo LN) as (RMf & PRf).
    { intros p' n' Hp' _ NF. apply SURV; [exact Hp'|]. intros E'. subst p'. apply NF. exact Ep. }
    { intros p' Hp'. apply SURV; [exact Hp'|]. intros E'. subst p'. pose proof (lfx_ndf _ _ _ _ NDp Hp Hp'). lia. }
    rewrite SP2 in RMf.
    pose proof (lfx_blk L1 A1 m1 md1 _ _ M1 VB1) as VR.
    assert (WR1 : forall a, S0 - LIST_FREE_K <= a < S0 -> writable_at (ms_segs Bm) m1 a)
      by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
    assert (NEf : forall a, S0 - LIST_FREE_K <= a < S0 -> ~ (hl_v l <= a < hl_v l + 16 * hl_cap l))
      by (intros a Ha X; lia).
    pose proof (rmid_widen Bm API ALLOC_STACK (S0 - 16) LIST_FREE_K S0 _ _ _ _ _ _ _ _ _ _ M1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR1 NEf RMf) as RMfw.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMfw) as RMs.
    assert (RM2 : rmid Bm API LIST_FREE_K S0 (fun a => lfE a \/ hl_v l <= a < hl_v l + 16 * hl_cap l) lfF
                    L A mem md L2 A2 m2 md2).
    { apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMs); [intros a X; exact X|].
      intros q [X|X]; [exact X | cbv beta in X; subst q; exact VF]. }
    assert (FR2 : rw_cells (ms_segs Bm) m2 (S0 - 16) [C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))]).
    { apply (rmid_rw_hi Bm API ALLOC_STACK (S0 - 16) _ _ L1 A1 m1 md1 L2 A2 m2 md2 (S0 - 16) _
               ltac:(lia) ltac:(lia) M1 RMf FR1 ltac:(lia) ltac:(cbn [cells_size csize]; lia)).
      intros i Hi X. cbv beta in X. lia. }
    assert (HD2 : rw_cells (ms_segs Bm) m2 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (hl_cap l))]).
    { apply (rmid_rw_img Bm API AX ALLOC_STACK (S0 - 16) _ _ L1 A1 m1 md1 L2 A2 m2 md2 LA _ (hg_img_low Bm SEG)
               ltac:(lia) M1 RMf HD1).
      intros i Hi. cbn [cells_size csize] in Hi. split; [apply PLR; lia|]. intros X. cbv beta in X.
      apply (ax_blocks_img AX L1 A1 m1 md1 p (16 * hl_cap l) (LA + i - hl_v l) M1 Hp ltac:(lia)).
      rewrite Ep. replace (hl_v l + (LA + i - hl_v l)) with (LA + i) by lia.
      exact (proj1 (proj1 (PLR (LA + i) ltac:(lia)))). }
    rewrite EB1 in ND1.
    apply (tail (fun a => lfE a \/ hl_v l <= a < hl_v l + 16 * hl_cap l) L2 A2 regs3 m2 md2
             (Z_to_bv 64 (hl_v l)) (Z_to_bv 64 (hl_cap l)) _ G2_1 RM2).
    + intros a [X|X]; [left; exact X | right].
      split; [lia|]. split.
      * intros Y. apply (ax_blocks_img AX L1 A1 m1 md1 p (16 * hl_cap l) (a - hl_v l) M1 Hp ltac:(lia)).
        rewrite Ep. replace (hl_v l + (a - hl_v l)) with a by lia. exact Y.
      * intros p' n' Hp' NF Y.
        pose proof LST as (_ & _ & [(C0 & _)|(_ & VB0 & _)] & _); [lia|].
        assert (Hne : ptr_addr L p' <> hl_v l) by (intros E; apply NF; rewrite E; exact VF).
        destruct (blocks_disjoint Bm API L A mem md _ _ _ _ HM (lf_blocks_of L A p' n' Hp') VB0 Hne); lia.
    + exact (INI IN1).
    + rewrite SEG. exact RO2.
    + rewrite TR, CNZ, lfx_runF_app0 by apply nret_lfx_drops_t. rewrite <- (VX1 CP), ESP. exact RS2.
    + exact (lfx_keep regs2 regs3 RF2 PRf).
    + exact HD2.
    + exact FR2.
    + intros E. exfalso. unfold list_blocks in E. rewrite CNZ in E. discriminate.
    + intros q n H Hn. rewrite EB2. pose proof (BA1 q n H Hn) as H1. rewrite EB1 in H1.
      apply (lfx_in_mid b1 b2 (hl_v l, 16 * hl_cap l)); [exact H1|]. intros E. apply Hn. injection E as E1 _.
      rewrite E1. exact VF.
    + intros q n H. rewrite EB2 in H. pose proof (lfx_nd_mid b1 b2 (hl_v l) (16 * hl_cap l) q n ND1 H) as Hne.
      pose proof (lfx_in_mid2 b1 b2 (hl_v l, 16 * hl_cap l) _ H) as H1. rewrite <- EB1 in H1.
      destruct (BB1 q n H1) as [H2 H3]. split; [exact H2|].
      unfold list_blocks. rewrite CNZ. intros X. apply in_app_or in X.
      destruct X as [[X|[]]|X]; [exact (Hne (eq_sym X)) | exact (H3 X)].
Qed.

Lemma loop : forall k lk L1 A1 R1 m1 md1, (k <= length (hl_recs l))%nat ->
  lfJ k lk L1 A1 m1 md1 -> lfRF R1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x154a0) m1 (seg_rom rsegs)) md1) LPOST.
Proof.
  induction k as [|k IH]; intros lk L1 A1 R1 m1 md1 Hk HJ RF1; [exact (fin lk L1 A1 R1 m1 md1 HJ RF1)|].
  pose proof HJ as (RM1 & IN1 & RO1 & RS1 & LT1 & HV1 & HC1 & HR1 & VX1 & SX1 & FR1 & BE1 & BA1 & BB1).
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1 & EK).
  pose proof (aa_laws API) as LAWS.
  assert (EKd : LIST_DROP_K = 8240) by reflexivity.
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & _).
  assert (HN1 : hl_n lk = Z.of_nat (S k)) by (unfold hl_n; rewrite HR1, firstn_length_le by exact Hk; reflexivity).
  pose proof LT1 as (HD1 & NC1 & _).
  assert (HD1r : rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v lk)); C4 (Z_to_bv 64 (Z.of_nat (S k)));
                                       C4 (Z_to_bv 64 (hl_cap lk))]).
  { rewrite <- HN1, <- SEG. exact HD1. }
  assert (RO1r : ro_agree rsegs m1) by (rewrite <- SEG; exact RO1).
  assert (Hkl : (k < length (hl_recs l))%nat) by lia.
  assert (G8 : getr R1 (Z_to_bv 5 8) = Z_to_bv 64 LA) by exact (RF1 8 ltac:(unfold callee_saved; lia)).
  eapply (kseg_raw R1 (Z_to_bv 64 0x154a0) m1 md1); [exact Hh1 | exact Hl1 | | |].
  { unfold Regs6ss.mkR_of.
    eapply lfu_head_drop with (LA := LA) (n := Z.of_nat (S k)); [exact G8 | lia | lia | lia | exact HD1r]. }
  { intros s0 (a2' & a3' & a4' & a5' & a6' & a7' & ->). do 3 eexists. reflexivity. }
  intros R pc' m0 regs2 HQ GR.
  destruct HQ as (a2' & a3' & a4' & a5' & a6' & a7' & EQ).
  injection EQ as ER EP EM. subst pc' m0.
  assert (GR2 : forall r, getr regs2 r = getr R r) by exact GR.
  subst R. clear GR.
  assert (KEEP2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r))
    by (apply lfx_cs; cbv beta; rewrite GR2; reflexivity).
  assert (RF2 : lfRF regs2) by exact (lfx_keep R1 regs2 RF1 KEEP2).
  assert (G2_1 : getr regs2 1 = Z_to_bv 64 0x154b8) by (rewrite GR2; reflexivity).
  assert (G2_10 : getr regs2 10 = Z_to_bv 64 LA) by (rewrite GR2; reflexivity).
  assert (G2_11 : getr regs2 11 = Z_to_bv 64 (Z.of_nat (S k) - 1)) by (rewrite GR2; reflexivity).
  assert (U10 : bv_unsigned (getr regs2 10) = LA) by (rewrite G2_10; apply hg_unsigned; lia).
  assert (U11 : bv_unsigned (getr regs2 11) = Z.of_nat k) by (rewrite G2_11; rewrite hg_unsigned by lia; lia).
  assert (SP2 : spZ regs2 = S0 - 16) by exact (lfx_sp regs2 RF2).
  pose proof LDC as LDc. unfold list_drop_contract in LDc.
  specialize (LDc L1 A1 regs2 m1 md1 (runF Fr [] bnd (lfx_drops_t SRS (S k))) lk lines).
  cbv zeta in LDc. rewrite U10, U11, Nat2Z.id, HN1, SEG in LDc. unfold LIST_DROP in LDc.
  eapply SR_bind.
  { apply LDc; clear LDc.
    - reflexivity.
    - eapply cpk_of_rmid; [exact RM1 | exact IN1 | exact (eq_ind_r YK0s.ret_ok lfx_ok_b8 G2_1)
                           | exact (lfx_tp regs2 RF2)
                           | rewrite SP2; clear - HAL; Z.div_mod_to_equations; lia | rewrite SP2; lia
                           | rewrite SP2; lia | lia | rewrite SP2; lia | rewrite SP2; lia].
    - exact IN1.
    - exact RO1r.
    - intros a Ha. rewrite <- SEG. exact (PLR a Ha).
    - exact LAL.
    - exact LT1.
    - lia.
    - exact RS1. }
  intros c (L2 & A2 & regs3 & m2 & md2 & l' & -> & RP & IN2 & (qs & _ & RS2 & _ & _) & RO2 & LT2 & HV2 & HC2 & HR2 & _
    & BLK).
  set (r := nth k (hl_recs lk) (0, [])) in *.
  assert (NR : r = nth k (hl_recs l) (0, [])) by (unfold r; rewrite HR1; apply lfx_nth_firstn; lia).
  assert (RIN : In r (hl_recs l)) by (rewrite NR; apply nth_In; exact Hkl).
  assert (FQ : lfF (fst r)) by (unfold lfF, list_blocks; apply in_or_app; right; apply in_map; exact RIN).
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMd & PRd).
  rewrite SP2 in RMd.
  assert (EdE : forall a, (LA + 8 <= a < LA + 12 \/
                           hl_v lk + 16 * Z.of_nat k <= a < hl_v lk + 16 * (Z.of_nat (S k) - 1)) -> lfE a)
    by (intros a [X|X]; unfold lfE; lia).
  assert (FR2 : rw_cells (ms_segs Bm) m2 (S0 - 16) [C8 (getr regs (Z_to_bv 5 8)); C8 (getr regs (Z_to_bv 5 1))]).
  { apply (rmid_rw_hi Bm API LIST_DROP_K (S0 - 16) _ _ L1 A1 m1 md1 L2 A2 m2 md2 (S0 - 16) _
             ltac:(lia) ltac:(lia) M1 RMd FR1 ltac:(lia) ltac:(cbn [cells_size csize]; lia)).
    intros i Hi X. pose proof (EdE _ X) as Y. unfold lfE in Y. cbn [cells_size csize] in Hi. lia. }
  assert (WR1 : forall a, S0 - LIST_FREE_K <= a < S0 -> writable_at (ms_segs Bm) m1 a)
    by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
  assert (NE1 : forall a, S0 - LIST_FREE_K <= a < S0 ->
            ~ (LA + 8 <= a < LA + 12 \/ hl_v lk + 16 * Z.of_nat k <= a < hl_v lk + 16 * (Z.of_nat (S k) - 1)))
    by (intros a Ha X; pose proof (EdE a X) as Y; unfold lfE in Y; lia).
  pose proof (rmid_widen Bm API LIST_DROP_K (S0 - 16) LIST_FREE_K S0 _ _ _ _ _ _ _ _ _ _ M1
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR1 NE1 RMd) as RMw.
  pose proof (rmid_EF Bm API _ _ _ lfE _ lfF _ _ _ _ _ _ _ _ RMw EdE
                ltac:(intros q E; cbv beta in E; rewrite E; exact FQ)) as RMe.
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMe) as RMs.
  assert (RM2 : rmid Bm API LIST_FREE_K S0 lfE lfF L A mem md L2 A2 m2 md2).
  { apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMs); intros x [X|X]; exact X. }
  destruct BLK as (b1 & b2 & EB1 & EB2).
  assert (ND1 : List.NoDup (map fst (blocks L1 A1))).
  { first [exact (NDB L1 A1 m1 md1 M1) | apply NoDup_ListNoDup; exact (NDB L1 A1 m1 md1 M1)]. }
  rewrite EB1 in ND1.
  assert (BE2 : list_blocks l = [] -> blocks L2 A2 = blocks L A).
  { intros E. exfalso. unfold list_blocks in E. apply app_eq_nil in E as [_ E2]. apply map_eq_nil in E2.
    rewrite E2 in Hkl. cbn in Hkl. lia. }
  assert (BA2 : forall q n, In (q, n) (blocks L A) -> ~ In q (list_blocks l) -> In (q, n) (blocks L2 A2)).
  { intros q n H Hn. rewrite EB2. pose proof (BA1 q n H Hn) as H1. rewrite EB1 in H1.
    apply (lfx_in_mid b1 b2 (fst r, text_len r)); [exact H1|]. intros E. apply Hn. injection E as E1 _.
    rewrite E1. exact FQ. }
  assert (BB2 : forall q n, In (q, n) (blocks L2 A2) ->
                  In (q, n) (blocks L A) /\ ~ In q (map fst (skipn k (hl_recs l)))).
  { intros q n H. rewrite EB2 in H. pose proof (lfx_nd_mid b1 b2 _ _ q n ND1 H) as Hne.
    pose proof (lfx_in_mid2 b1 b2 (fst r, text_len r) _ H) as H1. rewrite <- EB1 in H1.
    destruct (BB1 q n H1) as [H2 H3]. split; [exact H2|].
    rewrite (lfx_skipn_cons (hl_recs l) k (0, []) Hkl). cbn [map]. rewrite <- NR.
    intros [X|X]; [exact (Hne (eq_sym X)) | exact (H3 X)]. }
  assert (Hlk : (k < length (hl_recs lk))%nat) by (rewrite HR1, firstn_length_le by exact Hk; lia).
  assert (RINk : In r (hl_recs lk)) by (unfold r; apply nth_In; exact Hlk).
  assert (RS2' : rt_ok Fr A2 (runF Fr [] bnd (lfx_drops_t SRS k))).
  { rewrite (lfx_drop_tr_at (known_at L1 A1) lk k Hlk) in RS2. fold r in RS2.
    rewrite (lfx_drops_t_step SRS k (shr (known_at L A) (0, [])) ltac:(rewrite length_map; exact Hkl)),
      lfx_runF_app0 by apply nret_lfx_drops_t.
    rewrite map_nth, lfx_rec_drop_t, <- NR.
    unfold known_at in RS2 |- *. rewrite (SX1 r ltac:(rewrite <- HR1; exact RINk)) in RS2. exact RS2. }
  pose proof RM2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct (mr_model _ _ LAWS _ _ _ _ M2) as (Hh2 & Hl2 & _).
  pose proof (NDB L1 A1 m1 md1 M1) as NB1.
  pose proof (NDB L2 A2 m2 md2 M2) as NB2.
  pose proof LT1 as (_ & _ & AR1 & _ & NV1 & RC1).
  assert (VX2 : 0 < hl_cap l -> sptr_of L2 A2 (hl_v l) = sptr_of L A (hl_v l)).
  { intros CP. rewrite <- (VX1 CP).
    destruct AR1 as [(C0 & _)|(_ & VB1 & _)]; [rewrite HC1 in C0; lia|]. rewrite HV1, HC1 in VB1.
    apply (lfx_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMd NB1 NB2 VB1 ltac:(lia)).
    intros E. cbv beta in E. apply NV1. rewrite HV1, E. apply in_map. exact RINk. }
  assert (SX2 : forall r', In r' (firstn k (hl_recs l)) -> sptr_of L2 A2 (fst r') = sptr_of L A (fst r')).
  { intros r' H. rewrite <- (SX1 r' (lfx_firstn_S _ _ _ H)).
    assert (H1 : In r' (hl_recs lk)) by (rewrite HR1; exact (lfx_firstn_S _ _ _ H)).
    rewrite Forall_forall in RC1.
    apply (lfx_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMd NB1 NB2 (proj1 (RC1 r' H1)) ltac:(lia)).
    intros E. cbv beta in E.
    pose proof LT2 as (_ & _ & _ & _ & _ & RC2). rewrite Forall_forall in RC2.
    assert (H2 : In r' (hl_recs l')) by (rewrite HR2, HR1, lfx_drop_recs by exact Hk; exact H).
    pose proof (proj1 (RC2 r' H2)) as B2. rewrite EB2 in B2.
    exact (lfx_nd_mid b1 b2 _ _ _ _ ND1 B2 E). }
  apply (lfx_jmp_sr regs3 _ m2 md2 LPOST G2_1 Hh2 Hl2).
  intros regs4 KEEP4.
  apply (IH l' L2 A2 regs4 m2 md2 ltac:(lia)).
  - split; [exact RM2|]. split; [exact IN2|]. split; [rewrite SEG; exact RO2|]. split; [exact RS2'|].
    split; [exact LT2|]. split; [rewrite HV2; exact HV1|]. split; [rewrite HC2; exact HC1|].
    split; [rewrite HR2, HR1; apply lfx_drop_recs; exact Hk|]. split; [exact VX2|]. split; [exact SX2|].
    split; [exact FR2|]. split; [exact BE2|]. split; [exact BA2|]. exact BB2.
  - exact (lfx_keep regs3 regs4 (lfx_keep regs2 regs3 RF2 PRd) KEEP4).
Qed.

Lemma run_main : SR (ms_segs Bm) (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_FREE) mem (seg_rom (ms_segs Bm))) md) LPOST.
Proof.
  pose proof gfacts as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & AC1 & AC2 & LA0 & LA1 & EK).
  pose proof (aa_laws API) as LAWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HM) as (Hh & Hl & _).
  assert (ROr : ro_agree rsegs mem) by (rewrite <- SEG; exact RO).
  assert (ST : stk rsegs mem (S0 - LIST_FREE_K) S0).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as STn.
  rewrite SEG.
  eapply (kseg regs (Z_to_bv 64 LIST_FREE) mem md); [exact lfx_wx | exact ROr | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of, LIST_FREE.
    eapply lfu_entry with (lo := S0 - LIST_FREE_K) (LA := LA).
    - exact STn.
    - match goal with |- _ <= ?x => change x with S0 end. lia.
    - apply mem_inv_normalize.
    - symmetry. apply Z_to_bv_bv_unsigned.
    - lia.
    - exact LAL. }
  { intros s0 (a0' & m' & -> & _). do 3 eexists. reflexivity. }
  intros R pc' m0 regs1 m1 HQ GR MREL ROS.
  destruct HQ as (a0' & m0' & EQ & MU & WM & MI & FRM & STK).
  injection EQ as ER EP EM. subst pc' m0.
  assert (GR1 : forall r, getr regs1 r = getr R r) by exact GR.
  subst R. clear GR.
  destruct (rmid_norm Bm API LIST_FREE_K S0 lfE lfF L A mem md m0' m1 [(S0 - 16, S0)]
              SEG ROr MREL ROS MU WM HM HW HB ltac:(lia)) as (RM0 & MUr & WMr).
  { unfold sk. intros a [X|X]; [apply HWS; lia | apply HER; exact X]. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. left. lia. }
  { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Ho). apply hg_out. intros lo hi [E|[]].
    injection E as <- <-. left. lia. }
  { intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HM Hp Hi) as (_ & B1 & B2 & _).
    destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
  assert (RO1 : ro_agree (ms_segs Bm) m1) by (rewrite SEG; exact (ro_agree_same rsegs mem m1 ROr ROS)).
  apply (loop (length (hl_recs l)) l L A regs1 m1 md (le_n _)).
  - split; [exact RM0|]. split; [exact INIT|]. split; [exact RO1|].
    split.
    { assert (LD : lfx_drops_t SRS (length (hl_recs l)) = []).
      { unfold lfx_drops_t. rewrite skipn_all2 by (rewrite length_map; lia). reflexivity. }
      rewrite LD. exact RES. }
    split.
    { apply (lfx_list_at_munch L A mem m1 LA l lines [(S0 - 16, S0)] LST MUr).
      intros a Ha.
      assert (Hlo : 0 <= a < YM05.alloc_ceiling).
      { destruct Ha as [Ha|(q & k & Hq & Ha)]; [lia|]. pose proof (lfx_blk L A mem md q k HM Hq). lia. }
      split; [lia|]. apply hg_out. intros lo hi [E|[]]. injection E as <- <-. left. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [symmetry; apply firstn_all|].
    split; [intros _; reflexivity|]. split; [intros r' _; reflexivity|].
    split.
    { rewrite SEG. replace (S0 - 16) with (S0 + -16) by lia. exact (rw_cells_of_rel rsegs m1 m0' _ _ MREL FRM). }
    split; [intros _; reflexivity|]. split; [intros q n H _; exact H|].
    intros q n H. split; [exact H|]. rewrite skipn_all. intros [].
  - unfold lfRF. apply lfx_cs; cbv beta; rewrite GR1; reflexivity.
Qed.

End Run.

Theorem list_free_holds : list_drop_contract Bm API Fr -> free_contract_rt Bm API Fr -> free_null_contract Bm ->
  list_free_contract Bm API Fr.
Proof.
  intros LDC FRC FNC. unfold list_free_contract.
  intros L A regs mem md bnd l lines. cbv zeta. intros SEG PRE INIT RO PLR LAL LST RES.
  exact (run_main SEG LDC FRC FNC L A regs mem md bnd l lines PRE INIT RO PLR LAL LST RES).
Qed.

End LFU.
