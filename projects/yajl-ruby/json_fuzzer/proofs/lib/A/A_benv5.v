(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanDepot AsanBudget AsanRepFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_bundle AI_shadow AI_lowshadow AYajlRep AF_fakestack_rep AF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_cells (cells : list (Z * Z)) (x : Z) : Prop := exists c, In c cells /\ fst c <= x < fst c + snd c.
Lemma in_cells_here : forall c l x, fst c <= x < fst c + snd c -> in_cells (c :: l) x.
Proof. intros c l x H. exists c. split; [left; reflexivity| exact H]. Qed.
Lemma in_cells_later : forall c l x, in_cells l x -> in_cells (c :: l) x.
Proof. intros c l x (c' & Hc & R). exists c'. split; [right; exact Hc| exact R]. Qed.
Lemma in_cells_app : forall l1 l2 x, in_cells (l1 ++ l2) x <-> in_cells l1 x \/ in_cells l2 x.
Proof.
  intros l1 l2 x. unfold in_cells. split.
  - intros (c & Hc & R). apply in_app_iff in Hc. destruct Hc; [left| right]; exists c; auto.
  - intros [(c & Hc & R)|(c & Hc & R)]; exists c; (split; [apply in_app_iff; auto| exact R]).
Qed.
Lemma in_cells_nil : forall x, ~ in_cells [] x.
Proof. intros x (c & Hc & _). exact Hc. Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma rw_cells_agree_pt : forall (m m' : mem) A cs,
  rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) -> rw_cells asegs m' A cs.
Proof.
  intros m m' A cs H AG. apply (rw_cells_agree_eq asegs m m'); [| exact H]. intros a Ha. pose proof (AG a Ha) as E.
  split; [exact E|]. unfold wview. rewrite E. intros X; exact X.
Qed.
End RC__1.

(* [comment removed for export] *)
Ltac solve_in_cells :=
  cbn [List.app];
  let rec go := first [ apply in_cells_here; cbn [fst snd]; lia | apply in_cells_later; go ] in go.
(* [comment removed for export] *)
Ltac agree_xfer AG H FP :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1 H2]; split; [agree_xfer AG H1 FP | agree_xfer AG H2 FP]
  | exists x, _ => let x' := fresh "x" in let H1 := fresh "H" in destruct H as [x' H1]; exists x'; agree_xfer AG H1 FP
  | rw_cells _ _ _ _ => eapply rw_cells_agree_pt; [exact H | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; apply AG; FP a Ha]
  | (forall i : nat, _) => let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; specialize (H i Hi); agree_xfer AG H FP
  | _ => exact H
  end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cl_cells (a : Z) : Prop :=
  (c_initialized ACONSTS <= a < c_initialized ACONSTS + 32) \/ (c_errno ACONSTS <= a < c_errno ACONSTS + 4)
  \/ (0x5d01d0 <= a < 0x5d01d0 + 65536)
  \/ (c_initialized ACONSTS + 0x20990 <= a < c_initialized ACONSTS + 0x20990 + 544).
(* [comment removed for export] *)
Definition stdio_w_ivs : list (Z * Z) :=
  [(c_stderr_F ACONSTS, c_stderr_F ACONSTS + 232); (c_stdout_F ACONSTS, c_stdout_F ACONSTS + 232); (c_stdout_buf ACONSTS - 8, c_stdout_buf ACONSTS + 1024)].
Definition stdio_w (a : Z) : Prop :=
  (c_stderr_F ACONSTS <= a < c_stderr_F ACONSTS + 232) \/ (c_stdout_F ACONSTS <= a < c_stdout_F ACONSTS + 232)
  \/ (c_stdout_buf ACONSTS - 8 <= a < c_stdout_buf ACONSTS + 1024).
Lemma stdio_w_In : forall iv x, In iv stdio_w_ivs -> fst iv <= x < snd iv -> stdio_w x.
Proof. intros iv x Hin Hx. unfold stdio_w. unfold stdio_w_ivs in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hx; tauto. Qed.

(* [comment removed for export] *)
Definition icp_globals_cellsL : list (Z * Z) :=
  [(A_GOT_SBPTR, 8); (A_SBVAR, 8); (A_GOT_RIC, 8); (A_RIC, 1); (A_REAL_MEMCPY, 8); (A_REAL_MEMSET, 8); (A_GOT_MIDBEG, 8); (A_MIDBEG, 8);
   (A_GOT_MIDEND, 8); (A_MIDEND, 8); (A_GOT_HIGHEND, 8); (A_HIGHEND, 8); (A_INITED, 1)].
Definition ay_statics_cellsL : list (Z * Z) := [(AY_GOT_SHADOW, 8); (AY_SHADOW_VAR, 8); (AY_GOT_UAR, 8); (AY_UAR_VAR, 4)].
Definition ay_cells_cellsL : list (Z * Z) := [(AY_CALLBACKS, 88); (AY_BUF_ALLOC_ERROR, 32); (AY_NOOP_ALLOCS, 32)].
(* [comment removed for export] *)
Definition LSLO : Z := 0x7fffa000.
Definition LSHI : Z := 0x800b8600.

(* [comment removed for export] *)
Definition img_mut : list (Z * Z) :=
  [(aic_instance asan_ic, 3632); (aic_internal_alloc_initialized asan_ic, 4); (aic_internal_allocator_instance asan_ic, 0x81030);
   (aic_theDepot asan_ic, 0x440010); (aic_stackStore asan_ic, 0x10010); (c_errno ACONSTS, 4)].

Lemma img_mut_low : forall r, In r img_mut -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Proof.
  intros r Hr. unfold img_mut in Hr.
  cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma img_cells_not_mut : forall x,
  in_cells icp_globals_cellsL x \/ in_cells ay_statics_cellsL x \/ in_cells ay_cells_cellsL x -> 0x10000 <= x < 0x603000 /\ ~ in_cells img_mut x.
Proof.
  intros x H.
  assert (R : forall l x, in_cells l x -> Exists (fun c => fst c <= x < fst c + snd c) l).
  { intros l y (c & Hc & Hr). apply Exists_exists. exists c. auto. }
  unfold icp_globals_cellsL, ay_statics_cellsL, ay_cells_cellsL, img_mut in *.
  unfold A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND,
         A_GOT_HIGHEND, A_HIGHEND, A_INITED, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS in *.
  cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS] in *.
  split.
  - destruct H as [H|[H|H]]; apply R in H; repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn in H; lia|]); apply Exists_nil in H; destruct H.
  - intros M. apply R in M.
    destruct H as [H|[H|H]]; apply R in H;
      repeat (apply Exists_cons in H; destruct H as [H|H];
              [cbn in H; repeat (apply Exists_cons in M; destruct M as [M|M]; [cbn in M; lia|]); apply Exists_nil in M; destruct M|]);
      apply Exists_nil in H; destruct H.
Qed.

(* [comment removed for export] *)
Lemma stdio_w_not_mut : forall x, stdio_w x -> 0x10000 <= x < 0x603000 /\ ~ in_cells img_mut x.
Proof.
  intros x H. unfold stdio_w in H. cbn [c_stderr_F c_stdout_F c_stdout_buf ACONSTS] in H.
  split; [lia|]. intros (c & Hc & R). unfold img_mut in Hc.
  cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS] in Hc.
  repeat (destruct Hc as [<-|Hc]; [cbn in R; lia|]). destruct Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma icp_globals_agree : forall m m' SB,
  icp_globals asegs m SB -> (forall a, in_cells icp_globals_cellsL a -> m' (wa a) = m (wa a)) -> icp_globals asegs m' SB.
Proof.
  intros m m' SB G AG. unfold icp_globals in *. unfold icp_globals_cellsL in AG.
  Ltac fpi a Ha := unfold A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
                          A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED in *; solve_in_cells.
  agree_xfer AG G fpi.
Qed.
Lemma ay_statics_agree : forall m m',
  ay_statics m -> (forall a, in_cells ay_statics_cellsL a -> m' (wa a) = m (wa a)) -> ay_statics m'.
Proof.
  intros m m' G AG. unfold ay_statics in *. unfold ay_statics_cellsL in AG.
  Ltac fpy a Ha := unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR in *; solve_in_cells.
  agree_xfer AG G fpy.
Qed.
Lemma ay_cells_agree : forall m m',
  ay_cells m -> (forall a, in_cells ay_cells_cellsL a -> m' (wa a) = m (wa a)) -> ay_cells m'.
Proof.
  intros m m' G AG. unfold ay_cells in *. unfold ay_cells_cellsL in AG.
  Ltac fpc a Ha := unfold AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS in *; solve_in_cells.
  agree_xfer AG G fpc.
Qed.
Lemma low_shadow_agree : forall m m',
  low_shadow_ok m -> (forall a, LSLO <= a < LSHI -> m' (wa a) = m (wa a)) -> low_shadow_ok m'.
Proof.
  intros m m' H AG a Ha. destruct (H a Ha) as [W R]. pose proof (AG a Ha) as E.
  split; [unfold wview in *; rewrite E; exact W| unfold mrd in *; rewrite E; exact R].
Qed.
(* [comment removed for export] *)
Definition fs_fp (fsbase a : Z) : Prop :=
  (fsbase <= a < fsbase + kFsBytes) \/ (fs_shadow fsbase <= a < fs_shadow fsbase + kFsBytes / 8).
Lemma FSRep_agree : forall E fsbase fs LF m m',
  (forall a, fs_fp fsbase a -> m' (wa a) = m (wa a)) -> FSRep asegs E fsbase fs LF m -> FSRep asegs E fsbase fs LF m'.
Proof.
  intros E fsbase fs LF m m' AG FS.
  assert (HA : forall a, fs_fp fsbase a -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)).
  { intros a Ha. pose proof (AG a Ha) as EQ. split; [exact EQ| unfold wview; rewrite EQ; intros X; exact X]. }
  clear AG. destruct FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
  assert (NF : forall cid, 0 <= cid <= 1 -> 0 < fs_nframes cid <= 16384).
  { intros cid Hc. unfold fs_nframes, kFsLog, kFsMinFrameLog in *.
    split; [apply Z.pow_pos_nonneg; lia|]. change 16384 with (2 ^ 14). apply Z.pow_le_mono_r; lia. }
  assert (FB : forall cid, 0 <= cid <= 1 -> 64 <= fs_frame_bytes cid <= 65536 /\ fs_frame_bytes cid * fs_nframes cid = 2 ^ 20 /\ fs_frame_bytes cid mod 8 = 0).
  { intros cid Hc. unfold fs_frame_bytes, fs_nframes, kFsLog, kFsMinFrameLog in *. split; [| split].
    - split; [change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia | change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia].
    - rewrite <- Z.pow_add_r by lia. f_equal. lia.
    - replace (6 + cid) with (3 + (3 + cid)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_comm. apply Z_mod_mult. }
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split. { intros cid Hc. destruct (HH cid Hc) as [h Hh]. exists h. apply (rw_cells_agree_eq asegs m m'); [| exact Hh]. intros a Ha. apply HA. unfold fs_fp, kFsBytes, kFsClasses in *. cbn in Ha. lia. }
  split. { apply (rw_cells_agree_eq asegs m m'); [| exact HL]. intros a Ha. apply HA. unfold fs_fp, kFsBytes. cbn in Ha. lia. }
  split. { apply (rw_cells_agree_eq asegs m m'); [| exact HG]. intros a Ha. apply HA. unfold fs_fp, kFsBytes. cbn in Ha. lia. }
  split. { intros cid pos Hp. apply (rw_cells_agree_eq asegs m m'); [| exact (HF cid pos Hp)]. intros a Ha. apply HA. cbn in Ha.
           destruct Hp as [Hc Hq]. pose proof (NF cid Hc).
           unfold fs_fp, fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset, kFsBytes, kFsClasses in *.
           destruct (cid =? 0); unfold fs_nframes, kFsLog, kFsMinFrameLog in *; cbn in *; lia. }
  split. { intros cid pos Hp. destruct (HW cid pos Hp) as [W1 W2].
           destruct Hp as [Hc Hq]. pose proof (NF cid Hc) as N1. pose proof (FB cid Hc) as (F1 & F2 & F3).
           assert (R : fsbase + 4096 <= fs_frame_addr fsbase cid pos /\ fs_frame_addr fsbase cid pos + fs_frame_bytes cid <= fsbase + kFsBytes
                       /\ fs_frame_addr fsbase cid pos mod 8 = 0).
           { unfold fs_frame_addr, fs_frames_base, kFsFlagsOffset, kFsBytes, kFsLog, kFsMinFrameLog.
             cbn [Z.pow Z.add Z.sub Pos.add Z.mul Pos.mul].
             assert (fs_frame_bytes cid * pos + fs_frame_bytes cid <= 2 ^ 20) by nia. split; [nia|]. split; [nia|].
             clear -G1 F3 Hq. Z.div_mod_to_equations. nia. }
           split.
           - apply (stk_agree_eq asegs m m'); [| exact W1]. intros a Ha. apply HA. left. unfold kFsBytes in *. lia.
           - apply (stk_agree_eq asegs m m'); [| exact W2]. intros a Ha. apply HA. right.
             unfold fs_shadow, kFsBytes in *. clear -Ha R G1 F3. Z.div_mod_to_equations. nia. }
  split; [exact ND| exact HLF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ENV.
Variable E0 : aenv.
(* [comment removed for export] *)
Definition resv_range_ok (r0 rl : Z) : Prop :=
     In (r0, rl) (ae_reserved E0) /\ placed_s r0 rl /\ img_sep E0 r0 rl
  /\ (r0 + rl <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= r0)
  /\ (r0 + rl <= ae_fs_beg E0 \/ ae_fs_beg E0 + ae_fs_len E0 <= r0)
  /\ (r0 + rl <= ae_store_blk E0 \/ ae_store_blk E0 + 2^23 <= r0)
  /\ (r0 + rl <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= r0)
  /\ (r0 + rl <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= r0).

Definition env0_ok5 : Prop :=
     In (ae_depot_nodes E0, kDepotNodeBlockBytes) (ae_reserved E0) /\ In (ae_store_blk E0, kStoreBlockBytes) (ae_reserved E0)
  /\ placed (ae_depot_nodes E0) kDepotNodeBlockBytes /\ placed (ae_store_blk E0) kStoreBlockBytes
  /\ img_sep E0 (ae_depot_nodes E0) kDepotNodeBlockBytes /\ img_sep E0 (ae_store_blk E0) kStoreBlockBytes
  /\ (ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= ae_depot_nodes E0)
  /\ (ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_fs_beg E0 \/ ae_fs_beg E0 + ae_fs_len E0 <= ae_depot_nodes E0)
  /\ (ae_store_blk E0 + kStoreBlockBytes <= ae_fs_beg E0 \/ ae_fs_beg E0 + ae_fs_len E0 <= ae_store_blk E0)
  /\ (ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_iarena E0 \/ ae_iarena E0 + kIArenaLen <= ae_depot_nodes E0)
  /\ (ae_store_blk E0 + kStoreBlockBytes <= ae_iarena E0 \/ ae_iarena E0 + kIArenaLen <= ae_store_blk E0)
     (* [comment removed for export] *)
  /\ (forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000)
  /\ (forall r x, In r (arep_img_ranges E0 ++ depot_static E0) -> fst r <= x < fst r + snd r -> ~ cl_cells x /\ ~ stdio_w x)
  /\ ae_store_blk E0 mod 4096 = 0 /\ ae_depot_nodes E0 mod 4096 = 0
     (* [comment removed for export] *)
  /\ 0 <= ae_stack_bottom E0 /\ ae_stack_top E0 <= 2^47
  /\ ae_ic E0 = asan_ic
     (* [comment removed for export] *)
  /\ (ae_thread E0 + 4096 <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_thread E0)
  /\ (ae_depot_nodes E0 + kDepotNodeBlockBytes <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= ae_depot_nodes E0).

(* [comment removed for export] *)
Variable PL0 : fs_plumb.
Definition pl0_ok5 : Prop :=
     (exists c0 cl, resv_range_ok c0 cl /\ c0 <= fp_ctx PL0 /\ fp_ctx PL0 + 160 <= c0 + cl)
  /\ (exists d0 dl, resv_range_ok d0 dl /\ d0 <= fp_dtls PL0 /\ fp_dtls PL0 + 4096 <= d0 + dl)
  /\ resv_range_ok (ae_thread E0) 4096
  /\ (fp_ctx PL0 + 160 <= ae_thread E0 \/ ae_thread E0 + 4096 <= fp_ctx PL0)
  /\ (fp_dtls PL0 + 4096 <= ae_thread E0 \/ ae_thread E0 + 4096 <= fp_dtls PL0)
  /\ (fp_ctx PL0 + 160 <= fp_dtls PL0 \/ fp_dtls PL0 + 4096 <= fp_ctx PL0)
     (* [comment removed for export] *)
  /\ (ae_iarena E0 <= fp_ctx PL0 /\ fp_ctx PL0 + 4096 <= ae_iarena E0 + kIArenaLen).

(* [comment removed for export] *)
Definition rt_high (a : Z) : Prop :=
  (ae_thread E0 <= a < ae_thread E0 + 4096) \/ (fp_ctx PL0 <= a < fp_ctx PL0 + 160) \/ (fp_dtls PL0 <= a < fp_dtls PL0 + 4096).
(* [comment removed for export] *)
Definition rt_high2 (a : Z) : Prop :=
  ((ae_thread E0 <= a < ae_thread E0 + 8) \/ (ae_thread E0 + 48 <= a < ae_thread E0 + 64))
  \/ (fp_ctx PL0 <= a < fp_ctx PL0 + 160) \/ (fp_dtls PL0 <= a < fp_dtls PL0 + 4096).
Lemma rt_high2_high : forall a, rt_high2 a -> rt_high a.
Proof. intros a [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]. Qed.

(* [comment removed for export] *)
Lemma resv_range_num : forall r0 rl, resv_range_ok r0 rl -> 0 <= rl ->
  0x1000 <= r0 /\ r0 + rl <= alloc_ceiling /\ (r0 + rl <= 0x10000 \/ 0x603000 <= r0) /\ (r0 + rl <= 0x7fff7000 \/ 0x10007fff8000 <= r0).
Proof. intros r0 rl (_ & P & _) Hl. pose proof (placed_s_num r0 rl P Hl). destruct P as (_ & P2 & _). tauto. Qed.
End ENV.

(* [comment removed for export] *)
Definition l0_ok5 (E0 : aenv) (L0 RES0 : list (word * word)) : Prop :=
     In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0                                   (* [comment removed for export] *)
  /\ In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0                                   (* [comment removed for export] *)
  /\ In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0                          (* [comment removed for export] *)
  /\ Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0                         (* [comment removed for export] *)
  /\ (forall x, 0x10000 <= x < 0x603000 -> exists e, In e RES0 /\ elo e <= x < ehi e)     (* [comment removed for export] *)
  /\ (forall rr x, In rr (ae_reserved E0) -> fst rr <= x < fst rr + snd rr ->
        (exists e, In e (RES0 ++ L0) /\ elo e <= x < ehi e) \/ alloc_ceiling <= x)         (* [comment removed for export] *)
  /\ Forall (fun rr => 0 < snd rr) (ae_reserved E0).                                     (* [comment removed for export] *)
End RC__2.
