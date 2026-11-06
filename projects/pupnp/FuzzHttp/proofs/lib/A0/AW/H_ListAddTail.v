(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA H_freelist AWRng.
Import ListNotations.
Open Scope Z_scope.

Definition ListAddTail_entryA : Z := 0x8b500.

Definition lhead_cells (first last size : Z) : list cell :=
  [C8 (wz 0); C8 (wz first); C8 (wz 0); C8 (wz last); C8 (wz 0); C8 (wz 0); C8 (wz size)].

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma aseg1 : forall (lo L IT : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  0 < L -> L + 96 < 2^64 -> 0 <= IT < 2^64 ->
  evt asegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x8b53c) (wz (q + -48)) gp tp t0 t1 t2 (wz L) (wz IT) (wz (L + 56)) (wz IT) a2 a3 a4 a5 a6 a7
                    s2 (wz 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FreeListAlloc_entryA) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q + -48) /\ rw_cells asegs m' (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz L) (wz IT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListAddTail_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo L IT ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 L0 LHI ITR. unfold ListAddTail_entryA, FreeListAlloc_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 48%nat ST.
  walk_lia_to 0x8b538%Z. step.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Definition link_post (lo L IT N first last size : Z) (lastnode : option (Z * Z)) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((L, L + 56) :: (N, N + 24) :: (lo, q) :: match lastnode with None => [] | Some _ => [(last, last + 24)] end)%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' L (lhead_cells (match lastnode with None => N | Some _ => first end) N (size + 1))
    /\ rw_cells asegs m' N (node_cells last (L + 24) IT)
    /\ match lastnode with None => True | Some (pl, il) => rw_cells asegs m' last (node_cells pl N il) end.

#[using="IC"] Lemma aseg2 : forall (lo L IT N first last size : Z) (lastnode : option (Z * Z)) (nj : list byte)
    ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x18 x20
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -48) -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m L (lhead_cells first last size) -> 0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 56 ->
  0 <= first < 2^64 -> 0 <= size -> size + 1 < 2^63 -> 0 <= IT < 2^64 ->
  rw_cells asegs m N [CB 24 nj] -> 0x609000 <= N -> N + 24 <= alloc_ceiling -> N mod 8 = 0 -> shw m N 24 ->
  (L + 56 <= N \/ N + 24 <= L) ->
  match lastnode with
  | None => last = L
  | Some (pl, il) => rw_cells asegs m last (node_cells pl (L + 24) il) /\ 0x609000 <= last /\ last + 24 <= alloc_ceiling /\ last mod 8 = 0
                     /\ shw m last 24 /\ (N + 24 <= last \/ last + 24 <= N) /\ (L + 56 <= last \/ last + 24 <= L)
                     /\ 0 <= pl < 2^64 /\ 0 <= il < 2^64
  end ->
  evt asegs (link_post lo L IT N first last size lastnode ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (q + -48)) gp tp t0 t1 t2 (wz L) (wz IT) (wz N) a1 a2 a3 a4 a5 a6 a7
             x18 (wz 0x7fff8000) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8b53c) fc None m (seg_rom asegs)).
Proof.
  intros lo L IT N first last size lastnode nj ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x18 x20 F fc m.
  intros ST CLO LO QHI MI AE0 FR LC LLO LHI LAL SHWL FR0 SZ0 SZ ITR NC NLO NHI NAL SHWN DJLN LASTH.
  unfold lhead_cells, node_cells in *. unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  apply (rw_cells_split_CB asegs m N [] 24 nj [] [16; 8]%nat) in NC; [| reflexivity]. cbn [app mk_CB_cells] in NC.
  destruct (proj1 (rw_cells_app asegs m N [CB 16 (firstn 16 nj)] _) NC) as [NC16 NC8]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in NC8. clear NC.
  destruct lastnode as [[pl il]|].
  - destruct LASTH as (LNC & LSLO & LSHI & LSAL & SHWS & DJNS & DJLS & PLR & ILR).
    pose proof (munch_refl [(L, L + 56); (N, N + 24); (lo, q); (last, last + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    walk_lia_to 0x8b550%Z.
    step. all_win_ok.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_memset IC) with (P := N) (c := 0) (n := 16) (lo := lo);
        first [ rng_tac | exact NC16 | exact MI | exact AE0 | exact ST | reflexivity
              | (eapply accessible_sub; [exact (proj1 SHWN) | lia | lia])
              | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWN)) | lia | lia | lia])
              | lia | (unfold A0_RT_STACK; lia)
              | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
      | post_call asegs mm ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    apply (rw_cells_split_CB asegs m1 N [] 16 _ [] [8; 8]%nat) in POST; [| reflexivity]. cbn [app mk_CB_cells] in POST.
    change (Z.of_nat 16) with 16 in NC8.
    walk_lia_to 0x8b608%Z.
    env_now AE0 MU WM. release_to q. step.
    pose proof (proj2 (rw_cells_app asegs m2 N _ _) (conj POST NC8)) as NCF. cbn [app] in NCF.
    apply evt_done. unfold link_post, lhead_cells, node_cells. do 15 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). exact LNC.
  - subst last.
    pose proof (munch_refl [(L, L + 56); (N, N + 24); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    walk_lia_to 0x8b550%Z.
    step. all_win_ok.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_memset IC) with (P := N) (c := 0) (n := 16) (lo := lo);
        first [ rng_tac | exact NC16 | exact MI | exact AE0 | exact ST | reflexivity
              | (eapply accessible_sub; [exact (proj1 SHWN) | lia | lia])
              | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWN)) | lia | lia | lia])
              | lia | (unfold A0_RT_STACK; lia)
              | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
      | post_call asegs mm ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    apply (rw_cells_split_CB asegs m1 N [] 16 _ [] [8; 8]%nat) in POST; [| reflexivity]. cbn [app mk_CB_cells] in POST.
    change (Z.of_nat 16) with 16 in NC8.
    walk_lia_to 0x8b608%Z.
    env_now AE0 MU WM. release_to q. step.
    pose proof (proj2 (rw_cells_app asegs m2 N _ _) (conj POST NC8)) as NCF. cbn [app] in NCF.
    apply evt_done. unfold link_post, lhead_cells, node_cells. do 15 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). exact I.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation bsub := (bsub FI AI).
Local Notation dlseg := (dlseg FI AI).
Local Notation hd_addr := (hd_addr FI AI).
Local Notation last_addr := (last_addr FI AI).

Definition ListAddTail_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB LBK : BL) (ns : list (BLK * Z)) (L IT fk lo : Z) (m : mem) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (ns' : list (BLK * Z)),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(L, L + 56)] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB' /\ bsub (map fst ns') LB' /\ NoDup (map blk_id (map fst ns' ++ LBK))
    /\ rw_cells asegs m' L (lhead_cells (hd_addr ns' (L + 24)) (last_addr ns' L) (zlength ns'))
    /\ rw_cells asegs m' (L + 56) (fl_cells 0 fk)
    /\ dlseg m' ns' L (L + 24)
    /\ am_nsec FI AI s' = ns0
    /\ exists k, r <> 0 /\ ns' = ns ++ [((k, r, 24), IT)] /\ LB' = (k, r, 24) :: LB.

Definition ListAddTail_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB LBK : BL) (st : fsstate FI) (ns : list (BLK * Z)) (L IT fk lo : Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - 16 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) ->
  rw_cells asegs m (L + 56) (fl_cells 0 fk) -> dlseg m ns L (L + 24) ->
  mlocNB FI AI q st L 96 -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  zlength ns < 2^40 -> 0 <= IT < 2^64 -> am_budget FI AI s LB 24 ->
  bsub (map fst ns) LB -> bsub LBK LB -> NoDup (map blk_id (map fst ns ++ LBK)) ->
  a0 = wz L -> a1 = wz IT ->
  AJ FI AI J (ListAddTail_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK ns L IT fk lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListAddTail_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="IC AC ASL AMS"] Theorem ListAddTail_spec_A : ListAddTail_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBK st ns L IT fk lo.
  intros HR RF AE ST CLO LO QAL QTOP MI LC FLC DL LL LHI LAL SHWL LEN ITR BUD NSUB KSUB ND -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4). unfold zlength in *.
  assert (LO' : lo <= q - 48 - 16 - 4096) by (unfold A0_RT_STACK in LO; exact LO).
  assert (QC : alloc_ceiling <= q + -48) by lia.
  pose proof (mlocNB_mblocA FI AI LB q st L 96 LL) as LM.
  destruct (mblocA_range FI AI s LB _ q st m L 96 HR (fun b H => H) RF LM ltac:(lia) ltac:(lia)) as (LLO & _ & _).
  assert (ASUB : bsub (map fst ns ++ LBK) LB) by (apply (bsub_app FI AI); split; assumption).

  assert (NF : forall b it, In (b, it) ns -> In b LB /\ blk_size b = 24 /\ 0x609000 <= blk_addr b /\ blk_addr b + 24 <= alloc_ceiling /\ blk_addr b mod 8 = 0).
  { intros b it H. assert (Hb : In b LB) by (apply NSUB; apply (in_map fst _ _ H)).
    destruct (dlseg_facts FI AI _ _ _ _ _ _ DL H) as (SZ & _). destruct (am_block_range FI AI _ _ _ _ HR Hb) as (R1 & R2 & _ & R4 & R5 & R5d & _).
    rewrite SZ in R4. split; [exact Hb|]. split; [exact SZ|]. split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
  assert (FIRSTR : 0 <= hd_addr ns (L + 24) < 2^64).
  { destruct ns as [|[b it] ns']; cbn; [lia|]. destruct (NF b it (or_introl eq_refl)) as (_ & _ & ? & ? & _). lia. }
  eapply (aj_evt FI AI J). { eapply (aseg1 lo L IT); try eassumption; lia. }
  intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (shw_frame _ m m1 L 96 SHWL MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWL1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ LC MU1 WM1 ltac:(unfold lhead_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as LC1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ FLC MU1 WM1 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC1.
  assert (DL1 : dlseg m1 ns L (L + 24)).
  { eapply (dlseg_transport FI AI); [exact DL| exact MU1| exact WM1|]. intros b it H. destruct (NF b it H) as (_ & _ & ? & ? & _). cbn. lia. }
  assert (HP1 : apx FI AI [(L, L + 56)] LBK q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  clear MU1 WM1.

  assert (LM1 : mblocA FI AI LB (q + -48) st L 96) by (eapply (mblocA_weaken FI AI); [exact LM| lia| auto| auto]).
  eapply (aj_bind FI AI J).
  { eapply (FreeListAlloc_spec_A FI AI J AC ASL) with (lo := lo) (FL := L + 56) (fk := fk) (ras := []) (st := st).
    - exact HR1.
    - exact RF1.
    - exact AE1.
    - exact ST1.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI1.
    - cbn [fpchain]. unfold valid_frame. rewrite unsigned_lit by (clear - LLO LHI ACR; lia). clear - LHI CLO LO'. lia.
    - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
    - exact FLC1.
    - clear - LLO. lia.
    - clear - LHI. lia.
    - clear - LAL. Z.div_mod_to_equations. lia.
    - eapply shw_sub; [exact SHWL1| lia| lia| lia].
    - exact BUD.
    - reflexivity. }
  intros sx2 LB2 ms2 P. unfold malloc_post_A in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & k & N & junk & -> & AFR & -> & HR2 & NBLK & NSH & WM2 & NS2).
  replace (if a0_cls 24 =? 0 then 1 else 0) with 0 in NS2 by reflexivity. rewrite Z.add_0_r in NS2.
  destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
  replace (ret_pc (Z_to_bv 64 570684)) with (Z_to_bv 64 570684) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (NEW : In (k, N, 24) ((k, N, 24) :: LB)) by (left; reflexivity).
  destruct (am_block_range FI AI sx2 _ m2 _ HR2 NEW) as (U1 & U2 & U3 & U4 & U5 & U5d & U6). cbn [blk_addr blk_size fst snd] in U1, U2, U3, U4, U5, U5d, U6.
  pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR1 ltac:(apply aclient_range_above; cbn; lia)) as FR2.
  assert (LC2 : rw_cells asegs m2 L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (Z.of_nat (length ns)))).
  { eapply (apres_rw_cells FI AI); [exact AP2| exact LC1|]. unfold lhead_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
    eapply (mblocA_client FI AI); [exact RF1|]. eapply (mblocA_sub FI AI); [exact LM1| lia| lia]. }
  assert (FLC2 : rw_cells asegs m2 (L + 56) (fl_cells 0 fk)).
  { eapply (apres_rw_cells FI AI); [exact AP2| exact FLC1|]. unfold fl_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
    eapply (mblocA_client FI AI); [exact RF1|]. eapply (mblocA_sub FI AI); [exact LM1| lia| lia]. }
  assert (DL2 : dlseg m2 ns L (L + 24)).
  { eapply (dlseg_apres FI AI); [exact DL1| exact AP2|]. intros b it H. destruct (NF b it H) as (Hb & _). exact Hb. }
  assert (HP2 : apx FI AI [(L, L + 56)] LBK q m m2).
  { eapply (apx_trans FI AI); [exact HP1|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| exact KSUB]. }
  pose proof (mblocA_shw_apres FI AI AMS sx2 _ _ (q + -48) st m1 m2 L 96 LM1 SHWL1 AP2 RF1 HR2 (fun b H => or_intror H) QC) as SHWL2.
  pose proof (block_shw FI AI sx2 _ m2 (k, N, 24) N 24 HR2 NEW ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWN2.
  pose proof (mlocNB_apart FI AI sx2 _ m2 st q L 96 (k, N, 24) HR2 RF2 LL NEW ltac:(lia) ltac:(lia)) as DJLN. cbn [blk_addr blk_size fst snd] in DJLN.
  assert (ND2 : NoDup (map blk_id ((k, N, 24) :: (map fst ns ++ LBK)))) by (eapply (fresh_nodup FI AI); [exact HR2| exact ASUB| exact ND]).

  assert (NDJ : forall b it, In (b, it) ns -> N + 24 <= blk_addr b \/ blk_addr b + 24 <= N).
  { intros b it H. destruct (NF b it H) as (Hb & SZ & _).
    assert (NE : (k, N, 24) <> b).
    { intros <-. cbn in ND2. inversion ND2 as [|x_ l_ NI X_]; subst. apply NI. apply base.list_elem_of_In. change k with (blk_id (k, N, 24)). apply in_map. apply in_or_app. left. exact (in_map fst _ _ H). }
    destruct (am_blocks_disjoint FI AI _ _ _ _ _ HR2 NEW (or_intror Hb) NE) as [D|D]; cbn in D; rewrite ?SZ in D; lia. }
  assert (LM2 : mblocA FI AI ((k, N, 24) :: LB) q st L 96) by (apply (mlocNB_mblocA FI AI); exact LL).
  assert (LM56 : mblocA FI AI ((k, N, 24) :: LB) q st L 56) by (eapply (mblocA_sub FI AI); [exact LM2| lia| lia]).
  assert (SHWL56 : shw m2 L 56) by (eapply shw_sub; [exact SHWL2| lia| lia| lia]).
  assert (KSUB2 : forall b, In b LBK -> In b ((k, N, 24) :: LB)) by (intros b Hb; right; apply KSUB; exact Hb).
  assert (KNE : forall b0, In b0 LBK -> In b0 ((k, N, 24) :: LB) /\ b0 <> (k, N, 24)).
  { intros b0 Hb0. split; [apply KSUB2; exact Hb0|]. intros ->.
    cbn in ND2. inversion ND2 as [|x_ l_ NI X_]; subst. apply NI. apply base.list_elem_of_In. change k with (blk_id (k, N, 24)). apply in_map. apply in_or_app; right; exact Hb0. }
  assert (NSC : ns = [] \/ ns <> []) by (destruct ns; [left; reflexivity| right; discriminate]).
  destruct NSC as [->|NNE].
  +
    cbn [HObjA.hd_addr HObjA.last_addr length Z.of_nat] in LC2.
    eapply (aj_evt FI AI J).
    { eapply (aseg2 lo L IT N (L + 24) L 0 None junk); try eassumption; try lia; try reflexivity. }
    intros ms' P. unfold link_post in P.
    destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & LC3 & NC3 & _). cbn [app] in MU3.
    pose proof (rw_cells_transport asegs _ m2 _ _ _ FLC2 MU3 WM3 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC3.
    apply (aj_ret FI AI J). unfold ListAddTail_post_A.
    do 14 eexists. exists m3, N, [((k, N, 24), IT)]. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
             constructor; [eapply (rf_ok_mbloc FI AI sx2 _ _ q st m2 L 56 HR2 (fun b H => H) LM56); lia|].
             constructor; [eapply (rf_ok_blk FI AI sx2 _ m2 st (k, N, 24)); [exact HR2| exact NEW| cbn; lia| cbn; lia| lia]|].
             constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP2|]. eapply (apx_seg FI AI ASL sx2 _ _ q _ _ m2 m2 m3 HR2 KSUB2 MU3 WM3).
             constructor; [right; right; cbn; lia|].
             constructor. { right; left. cbn [fst snd]. intros a Ha.
                            eapply (fresh_block_not_aclient FI AI ASL sx2 _ LBK (k, N, 24) q m2 a HR2 NEW KNE); [lia| cbn; lia]. }
             constructor; [left; cbn; lia| constructor]. }
    split. { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
             constructor; [exact (mblocA_hf FI AI _ _ q st m2 L 56 RF2 LM56 ltac:(lia) (fun b1 H => H))|].
             constructor; [right; right; left; exists (k, N, 24); split; [exact NEW| cbn; lia]|].
             constructor; [left; cbn; lia| constructor]. }
    split; [exact KSUB2|].
    split. { intros b [<-|[]]. exact NEW. }
    split. { cbn. cbn in ND2. exact ND2. }
    split; [exact LC3|]. split; [exact FLC3|]. split.
    { cbn. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact NC3| exact I]. }
    split; [exact NS2|]. exists k. split; [lia|]. split; reflexivity.
  + destruct (exists_last NNE) as (ns0 & [bl itl] & E).
    pose proof DL2 as DLx. rewrite E in DLx. destruct (dlseg_last_cells FI AI _ _ _ _ _ _ DLx) as (LNC & BSZ & BNZ & BNT). clear DLx.
    assert (HBL : In (bl, itl) ns) by (rewrite E; apply in_or_app; right; left; reflexivity).
    destruct (NF bl itl HBL) as (BIN & _ & BLO & BHI2 & BAL).
    assert (LADDR : last_addr ns L = blk_addr bl) by (rewrite E, (last_addr_app FI AI); reflexivity).
    rewrite LADDR in LC2.

    assert (PLR : forall nsx pv, 0 <= pv < 2^64 -> (forall b it, In (b, it) nsx -> In (b, it) ns) -> 0 <= last_addr nsx pv < 2^64).
    { induction nsx as [|[b0 it0] nsx IH]; intros pv Hpv Hsub; cbn; [exact Hpv|]. apply IH.
      - destruct (NF b0 it0 (Hsub _ _ (or_introl eq_refl))) as (_ & _ & ? & ? & _). lia.
      - intros bx itx Hx. apply Hsub. right. exact Hx. }
    assert (PL0 : 0 <= last_addr ns0 L < 2^64).
    { apply PLR; [lia|]. intros b0 it0 H0. rewrite E. apply in_or_app. left. exact H0. }
    destruct (dlseg_facts FI AI _ _ _ _ _ _ DL2 HBL) as (_ & _ & _ & ITLR).
    assert (BIN2 : In bl ((k, N, 24) :: LB)) by (right; exact BIN).
    pose proof (block_shw FI AI sx2 _ m2 bl (blk_addr bl) 24 HR2 BIN2 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWB.
    pose proof (mlocNB_apart FI AI sx2 _ m2 st q L 96 bl HR2 RF2 LL BIN2 ltac:(lia) ltac:(lia)) as DJLB. rewrite BSZ in DJLB.
    eapply (aj_evt FI AI J).
    { eapply (aseg2 lo L IT N (hd_addr ns (L + 24)) (blk_addr bl) (Z.of_nat (length ns)) (Some (last_addr ns0 L, itl)) junk); try eassumption; try lia.
      split; [exact LNC|]. split; [lia|]. split; [lia|]. split; [exact BAL|]. split; [exact SHWB|]. split; [exact (NDJ bl itl HBL)|]. split; [lia|]. split; [exact PL0| exact ITLR]. }
    intros ms' P. unfold link_post in P.
    destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & LC3 & NC3 & LASTC). cbn [app] in MU3.
    pose proof (rw_cells_transport asegs _ m2 _ _ _ FLC2 MU3 WM3 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC3.

    assert (PRE : forall b0 it0, In (b0, it0) ns0 -> b0 <> bl /\ In (b0, it0) ns).
    { intros b0 it0 H0. assert (H0' : In (b0, it0) ns) by (rewrite E; apply in_or_app; left; exact H0). split; [| exact H0'].
      intros ->. pose proof ND as NDn. rewrite E, !map_app in NDn. cbn in NDn. rewrite <- app_assoc in NDn. apply list.NoDup_app in NDn.
      destruct NDn as (_ & DJn & _). apply (DJn (blk_id bl)). { apply base.list_elem_of_In. apply in_map. exact (in_map fst _ _ H0). } left. }
    assert (DL3 : dlseg m3 (ns ++ [((k, N, 24), IT)]) L (L + 24)).
    { eapply (dlseg_snoc FI AI); [exact DL2| exact MU3| exact WM3| | | rewrite LADDR; exact NC3| reflexivity| cbn; lia| cbn; lia| exact ITR].
      - intros b0 it0 H0. rewrite E, removelast_app in H0 by congruence. cbn [removelast] in H0. rewrite app_nil_r in H0.
        destruct (PRE b0 it0 H0) as [NE0 H0']. destruct (NF b0 it0 H0') as (B0IN & B0SZ & B0LO & B0HI & _).
        pose proof (NDJ b0 it0 H0') as DJ0.
        pose proof (mlocNB_apart FI AI s LB m st q L 96 b0 HR RF LL B0IN ltac:(lia) ltac:(lia)) as DJL0. rewrite B0SZ in DJL0.
        destruct (am_blocks_disjoint FI AI _ _ _ _ _ HR B0IN BIN NE0) as [D|D]; cbn in D |- *; rewrite ?B0SZ, ?BSZ in D; lia.
      - intros ns0' bl' itl' E'. rewrite E in E'. apply app_inj_tail in E'. destruct E' as [-> E2]. injection E2 as -> ->. exact LASTC. }
    assert (BNE : forall b0, In b0 LBK -> In b0 ((k, N, 24) :: LB) /\ b0 <> bl).
    { intros b0 Hb0. split; [apply KSUB2; exact Hb0|]. intros ->.
      rewrite map_app in ND. apply list.NoDup_app in ND. destruct ND as (_ & DJn & _). apply (DJn (blk_id bl)).
      - apply base.list_elem_of_In. apply in_map. exact (in_map fst _ _ HBL).
      - apply base.list_elem_of_In. apply in_map. exact Hb0. }
    apply (aj_ret FI AI J). unfold ListAddTail_post_A.
    do 14 eexists. exists m3, N, (ns ++ [((k, N, 24), IT)]). split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
             constructor; [eapply (rf_ok_mbloc FI AI sx2 _ _ q st m2 L 56 HR2 (fun b H => H) LM56); lia|].
             constructor; [eapply (rf_ok_blk FI AI sx2 _ m2 st (k, N, 24)); [exact HR2| exact NEW| cbn; lia| cbn; lia| lia]|].
             constructor; [apply (rf_ok_stack FI); cbn; lia|].
             constructor; [eapply (rf_ok_blk FI AI sx2 _ m2 st bl); [exact HR2| exact BIN2| cbn; lia| cbn; lia| lia]| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP2|]. eapply (apx_seg FI AI ASL sx2 _ _ q _ _ m2 m2 m3 HR2 KSUB2 MU3 WM3).
             constructor; [right; right; cbn; lia|].
             constructor. { right; left. cbn [fst snd]. intros a Ha.
                            eapply (fresh_block_not_aclient FI AI ASL sx2 _ LBK (k, N, 24) q m2 a HR2 NEW KNE); [lia| cbn; lia]. }
             constructor; [left; cbn; lia|].
             constructor; [| constructor]. right; left. cbn [fst snd]. intros a Ha.
             eapply (fresh_block_not_aclient FI AI ASL sx2 _ LBK bl q m2 a HR2 BIN2 BNE); [lia| rewrite BSZ; lia]. }
    split. { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|].
             constructor; [exact (mblocA_hf FI AI _ _ q st m2 L 56 RF2 LM56 ltac:(lia) (fun b1 H => H))|].
             constructor; [right; right; left; exists (k, N, 24); split; [exact NEW| cbn; lia]|].
             constructor; [left; cbn; lia|].
             constructor; [right; right; left; exists bl; split; [exact BIN2| rewrite BSZ; cbn; lia]| constructor]. }
    split; [exact KSUB2|].
    split. { intros b Hb. rewrite map_app in Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [right; apply NSUB; exact Hb| exact NEW]. }
    split. { rewrite !map_app, <- app_assoc. cbn [map app blk_id fst]. change (fst (fst (k, N, 24))) with k.
             cbn in ND2. rewrite !map_app in ND2. inversion ND2 as [|x_ l_ NI X_]; subst.
             apply list.NoDup_app in X_. destruct X_ as (Y1 & Y2 & Y3).
             apply list.NoDup_app. split; [exact Y1|]. split.
             - intros y Hy [->|Hy2]%list.elem_of_cons. { apply NI. apply list.elem_of_app. left. exact Hy. } exact (Y2 y Hy Hy2).
             - constructor; [| exact Y3]. intros Hk. apply NI. apply list.elem_of_app. right. exact Hk. }
    split. { rewrite (hd_addr_app FI AI) by exact NNE. rewrite (last_addr_app FI AI). cbn [HObjA.last_addr]. unfold zlength. rewrite length_app. cbn [length].
             rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. exact LC3. }
    split; [exact FLC3|]. split; [exact DL3|].
    split; [exact NS2|]. exists k. split; [lia|]. split; reflexivity.
Qed.
End W.
