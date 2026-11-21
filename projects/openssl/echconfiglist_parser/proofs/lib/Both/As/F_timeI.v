(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: time() is proved at the run instance KHr (atime_inst_run: the walk over the run's segment list, the vDSO call node, and the shadow of the vDSO string table opened for the call and closed after it); atime_inst at KHp and ECALL_time are removed; ati_auxv_pair reads the auxv claim's first pair, which is all of the vector the claim holds at LPS c0dd863a. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable RunTailLazy.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require PairCleanAll.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import VdNode VdNodeLazy.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import AuxvTable VdsoImg InNth.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsStrcmp AVdsoAddr AVdsoWalk AsSRRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Exec CellsX Arr TacX Frame MState Mem Cells.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes LazyFdNodes LazyCgNode. From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsDriverLaws AsSR AsChain FakeStackRep
     AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash ECH_AImg ECH_Iface AsAuxv F_strspn F_time F_timeW
     AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* WHAT IS PROVED.  [atime_inst_run]: time()'s statement (Both/As/F_time.v [atime_stmt]) at the run
   instance [KHr p tail vlo vb vhi] (Both/As/AsSRRun.v), whose reach is an [sreach] over the run's
   segment list [asegs ++ tail] (the binary's segments and the vDSO pair) from the state with
   that list's read-only backing.  The walk is Both/As/F_timeW.v's:
   1. [atime_front_v]: time() and clock_gettime() to the vDSO entry (through cgt_init and
      __vdsosym on the first call);
   2. the vDSO call, Spec/VdNodeLazy.v [sreach_vd_lazy];
   3. [atime_back_v]: back to time()'s caller.
   The lazy view stays over [asegs] (Common/Cfg/RunTailLazy.v [evt_sreach_lazy_av]); the hidden
   bytes avoid the run's list because no lazy address lies in the pair's window [vlo, vhi)
   ([lzt_L_off_window] from each half's maps_off, then [lzt_hid_avoids]).
   __vdsosym's strcmp interceptor reads the shadow of the vDSO string table, the window
   [pw_win vb] = [sh vb + 72, sh vb + 104), which is lazily reserved and hidden.  The walk runs
   with that window open (LazySR.lzok_open_hidden_window_wb: its bytes read 0; the budget is
   [pw_ok]'s 4096-byte reserve of [ABUDGET]).  The walk writes nothing in it (its footprint is
   the stack and vdso_func), so after the walk the window is closed again ([ati_close]): the
   pages the walk materialized stay in [all_pages (a_S s)] because the window's one page is the
   page of [pw_ok]'s marker byte ([ati_win_page]), and the window's bytes still read 0 in the
   full state.  The instance state is unchanged.  The pair's window invariants are carried
   through the reach by [PairCleanAll.sreach_keep_vcm], once for each half. *)

(* ---------------- facts that name no binary ---------------- *)

(* Ref/F_timeRun.v's [ts_*] and [vwf_*] lemmas (they name no binary), restated here so that this
   file needs nothing of the plain binary's library. *)
Lemma ati_sub_lit : forall a b : Z, (Z_to_bv 64 a - Z_to_bv 64 b)%bv = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma ati_image_in : forall ims bs im, vdso_image_of_bytes ims bs = Some im -> In im ims.
Proof.
  induction ims as [|i ims IH]; intros bs im H; cbn [vdso_image_of_bytes] in H; [discriminate H|].
  destruct (pstrings_eqb (vi_bytes i) bs).
  - injection H as E. left. exact E.
  - right. exact (IH bs im H).
Qed.

(* An exported entry means the text segment holds the one measured image (Vdso.v:287-315),
   whose largest frame is 240 bytes. *)
Lemma ati_vframe_of_entry : forall segs a f, vdso_entry_fn segs a = Some f -> vdso_frame segs = 240%N.
Proof.
  intros segs a f H. unfold vdso_entry_fn in H. unfold vdso_frame.
  revert H. unfold vdso_image.
  destruct (vdso_text_seg segs) as [seg0|]; [| intros H; discriminate H].
  destruct (vdso_image_of_bytes vdso_images (seg_bytes seg0)) as [im0|] eqn:E2; [| intros H; discriminate H].
  intros _. apply ati_image_in in E2.
  destruct E2 as [<- | []]. reflexivity.
Qed.

(* [VdNode.vd_npost] of a clock_gettime call that returns 0 and writes the 16 bytes [bs] at [tp]. *)
Lemma ati_npost_MS : forall (segs : list Segment) (tp : Z) (d : VdsoDraw) (calls : N)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m ro : word -> option byte) (bs : list byte),
  vdso_frame segs = 240%N ->
  exists (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (fr : list byte),
    vd_npost segs (VDRealtime tp d calls)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F pc fc rv m ro)
      (mkEffectU (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] [] [] [] [])
    = MS (mkR y1 x2 x3 x4 y5 y6 y7 x8 x9 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
         F x1 fc rv
         (write_to_mem (vdso_write_frame segs m (x2 - Z_to_bv 64 240)%bv (firstn 240%nat fr)) (Z_to_bv 64 tp) bs) ro.
Proof.
  intros segs tp d calls x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
         x24 x25 x26 x27 x28 x29 x30 x31 F pc fc rv m ro bs HF.
  unfold vd_npost. cbv beta iota zeta. rewrite HF.
  lazymatch goal with |- context [d calls ?u ?v ?w] => destruct (d calls u v w) as [vs fr] end.
  exists (nth_default x1 vs 0%nat), (nth_default x5 vs 1%nat), (nth_default x6 vs 2%nat), (nth_default x7 vs 3%nat),
         (nth_default x11 vs 5%nat), (nth_default x12 vs 6%nat), (nth_default x13 vs 7%nat), (nth_default x14 vs 8%nat),
         (nth_default x15 vs 9%nat), (nth_default x16 vs 10%nat), (nth_default x17 vs 11%nat), (nth_default x28 vs 12%nat),
         (nth_default x29 vs 13%nat), (nth_default x30 vs 14%nat), (nth_default x31 vs 15%nat), fr.
  cbn [vl_regs vl_frame].
  do 16 (destruct vs as [|? vs]; [reflexivity|]).
  reflexivity.
Qed.

(* auxv pair 0 is (AT_SYSINFO_EHDR, its value), Lib/AuxvTable.v:59-68; LPS c0dd863a: the claim
   ([AsAuxv.aauxv_ok]) holds exactly that pair, [firstn 2] of the vector. *)
Lemma ati_auxv_pair : forall segs m av v rnd execfn r,
  bytes_at segs m av (u64s (firstn 2 (map (Z_to_bv 64) (auxv_words_Z v rnd execfn r)))) ->
  cells_at segs m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 (ax_sysinfo v))].
Proof.
  intros segs m av v rnd execfn r H. split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r.
  unfold auxv_words_Z in H. cbn [map app firstn u64s] in H.
  first [ exact H | rewrite app_nil_r in H; exact H
        | rewrite app_assoc in H; apply bytes_at_app in H; exact (proj1 H) ].
Qed.

Lemma ati_cells_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (H0 & H1 & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2.
  rewrite cells_size_app in H1, Hw.
  split.
  - split; [split; [exact W1 | exact B1]|]. split; [exact H0|]. split; [lia|].
    intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2]|]. split; [lia|]. split; [lia|].
    intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* [Run.vdso_write_frame] (Run.v:563-573) writes a byte only where the writable view has one,
   and only at the addresses it walks. *)
Lemma ati_vwf_cases_g : forall segs bs m (a x : word),
  vdso_write_frame segs m a bs x = m x
  \/ (wview segs m x <> None /\ exists b, vdso_write_frame segs m a bs x = Some b).
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a x; [left; reflexivity|].
  cbn [vdso_write_frame].
  destruct (wview segs m a) as [b0|] eqn:E; cbv beta iota.
  - lazymatch goal with |- context [vdso_write_frame segs ?mm ?aa bs x] =>
      destruct (IH mm aa x) as [H1 | (H1 & b1 & H2)] end.
    + rewrite H1. cbv beta. destruct (bv_eqb x a) eqn:Exa.
      * right. split; [| exists b; reflexivity].
        apply Fs.bv_eqb_eq in Exa. rewrite Exa, E. discriminate.
      * left. reflexivity.
    + right. split; [| exists b1; exact H2].
      destruct (bv_eqb x a) eqn:Exa.
      * apply Fs.bv_eqb_eq in Exa. rewrite Exa, E. discriminate.
      * revert H1. unfold wview. cbv beta. rewrite Exa. exact (fun H => H).
  - apply IH.
Qed.

Lemma ati_vwf_wmono : forall segs bs m (a x : word),
  wview segs m x <> None -> wview segs (vdso_write_frame segs m a bs) x <> None.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a x H; [exact H|].
  cbn [vdso_write_frame]. apply IH.
  destruct (wview segs m a) as [b0|] eqn:E; cbv beta iota; [|exact H].
  revert H. unfold wview. cbv beta.
  destruct (bv_eqb x a); [intros _; cbv iota; discriminate | exact (fun H => H)].
Qed.

Lemma ati_vwf_out : forall segs bs m (z : Z) (x : word),
  (forall i, (i < length bs)%nat -> x <> wa (z + Z.of_nat i)) ->
  vdso_write_frame segs m (wa z) bs x = m x.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m z x Hx; [reflexivity|].
  cbn [vdso_write_frame]. rewrite wa_succ. rewrite IH.
  - destruct (wview segs m (wa z)); cbv beta iota; [|reflexivity].
    destruct (bv_eqb x (wa z)) eqn:E; [|reflexivity].
    exfalso. apply Fs.bv_eqb_eq in E. apply (Hx 0%nat); [cbn [length]; lia|].
    replace (z + Z.of_nat 0) with z by lia. exact E.
  - intros i Hi. replace (z + 1 + Z.of_nat i) with (z + Z.of_nat (S i)) by lia.
    apply Hx. cbn [length]. lia.
Qed.

Lemma ati_vwf_munch : forall segs bs m (z : Z), 0 <= z -> z + Z.of_nat (length bs) <= 2^64 ->
  munch [(z, z + Z.of_nat (length bs))] m (vdso_write_frame segs m (wa z) bs).
Proof.
  intros segs bs m z Hz Hl x Hx. apply ati_vwf_out. intros i Hi E. subst x.
  cbn [outside] in Hx. destruct Hx as [Hx _]. apply Hx.
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma ati_vwf_mem_inv : forall segs bs m (a : word), mem_inv segs m -> mem_inv segs (vdso_write_frame segs m a bs).
Proof.
  intros segs bs m a MI x b Hx.
  destruct (ati_vwf_cases_g segs bs m a x) as [E | (Hw & _)].
  - rewrite E in Hx. exact (MI x b Hx).
  - destruct (m x) as [b0|] eqn:Em; [exact (MI x b0 Em) | exact (wview_not_ro segs m x Hw Em)].
Qed.

Lemma ati_vwf_stk : forall segs bs m (a : word) lo hi,
  stk segs m lo hi -> stk segs (vdso_write_frame segs m a bs) lo hi.
Proof.
  intros segs bs m a lo hi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros y Hy. destruct (H y Hy) as [Hw (b & Hb)].
  split; [exact (ati_vwf_wmono segs bs m a _ Hw)|].
  destruct (ati_vwf_cases_g segs bs m a (wa y)) as [E | (_ & b' & E)].
  - exists b. unfold mrd in *. rewrite E. exact Hb.
  - exists b'. unfold mrd. rewrite E. reflexivity.
Qed.

(* The memory with the window [W] open: each of its bytes reads 0 (LazySR.lzok_open_hidden_window). *)
Definition ati_open (W : word * word) (m : mem) : mem :=
  fun a => if zin_rangeb (bv_unsigned a) W then Some (Z_to_bv 8 0) else m a.

Lemma ati_open_out : forall W m (a : word), zin_rangeb (bv_unsigned a) W = false -> ati_open W m a = m a.
Proof. intros W m a H. unfold ati_open. rewrite H. reflexivity. Qed.

Lemma ati_open_in : forall W m (a : word), zin_rangeb (bv_unsigned a) W = true -> ati_open W m a = Some (Z_to_bv 8 0).
Proof. intros W m a H. unfold ati_open. rewrite H. reflexivity. Qed.

(* the restriction does not read the read-only backing *)
Lemma ati_restrict_wrom : forall L S msF r, restrict L S (wrom msF r) = wrom (restrict L S msF) r.
Proof. intros L S [] r. reflexivity. Qed.

(* the state a restriction shows, seen through another restriction with another backing *)
Lemma ati_restrict_rewin : forall L S1 S2 msF R F pc fc rv (m ro r : word -> option byte),
  restrict L S1 msF = MS R F pc fc rv m ro ->
  restrict L S2 (wrom msF r) = MS R F pc fc rv (restrict_mem L S2 (ms_mem msF)) r.
Proof.
  intros L S1 S2 msF R F pc fc rv m ro r E.
  pose proof (f_equal ms_regs E) as E1. pose proof (f_equal ms_fregs E) as E2.
  pose proof (f_equal ms_pc_val E) as E3. pose proof (f_equal ms_svc_pending E) as E4.
  pose proof (f_equal ms_resv E) as E5. pose proof (f_equal ms_fcsr E) as E6.
  destruct msF as [rg fr pcv sv rs fcs mm rm]. cbn in E1, E2, E3, E4, E5, E6.
  subst. reflexivity.
Qed.

(* [lzok] reads no byte of the read-only backing (Both/As/AsSRRun.v [akrel_wrom]) *)
Lemma ati_lzok_wrom : forall (sg : list Segment) L S Zr msF mo r,
  lzok sg L S Zr (mkCfg msF mo) -> lzok sg L S Zr (mkCfg (wrom msF r) mo).
Proof.
  intros sg L S Zr msF mo r [HL Hinv Hh HZ HSZ HZL HLM].
  constructor; [exact HL | exact Hinv | exact Hh | exact HZ | exact HSZ | exact HZL | exact HLM].
Qed.

(* a one-byte cell's read, and the eight bytes of a zero word *)
Lemma ati_c1_mrd : forall (segs : list Segment) (m : word -> option byte) A b rest,
  cells_at segs m A (C1 b :: rest) -> mrd segs m (wa A) = Some b.
Proof.
  intros segs m A b rest [_ (_ & _ & H)].
  pose proof (H 0%nat ltac:(cbn [cells_bytes cbytes app length]; lia)) as H0.
  change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma ati_c8z_mrd : forall (segs : list Segment) (m : word -> option byte) A,
  cells_at segs m A [C8 (Z_to_bv 64 0)] ->
  forall a, A <= a < A + 8 -> mrd segs m (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros segs m A [_ (_ & _ & H)] a Ha.
  replace a with (A + Z.of_nat (Z.to_nat (a - A))) by lia.
  rewrite H.
  - assert (Hi : (Z.to_nat (a - A) < 8)%nat) by lia.
    revert Hi. generalize (Z.to_nat (a - A)) as i. intros i Hi.
    do 8 (destruct i as [|i]; [vm_compute; reflexivity|]).
    exfalso. lia.
  - change (length (cells_bytes [C8 (Z_to_bv 64 0)])) with 8%nat. lia.
Qed.

(* the predicates read a memory only at the addresses they name *)
Lemma ati_wview_pt : forall (sg : list Segment) (m m' : word -> option byte) (x : word),
  m' x = m x -> wview sg m' x = wview sg m x.
Proof. intros sg m m' x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma ati_stk_ext : forall (sg : list Segment) (m m' : word -> option byte) lo hi,
  stk sg m lo hi -> (forall a, lo <= a < hi -> m' (wa a) = m (wa a)) -> stk sg m' lo hi.
Proof.
  intros sg m m' lo hi (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [Hw Hb]. split.
  - rewrite (ati_wview_pt sg m m' (wa a) (E a Ha)). exact Hw.
  - unfold mrd in *. rewrite (E a Ha). exact Hb.
Qed.

Lemma ati_rw_cells_ext : forall (sg : list Segment) (m m' : word -> option byte) A cs,
  rw_cells sg m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells sg m' A cs.
Proof.
  intros sg m m' A cs [[Hwf (B0 & B1 & B)] (W0 & W1 & Wv)] E.
  pose proof (cells_bytes_length cs Hwf) as HL.
  split; [split; [exact Hwf | split; [exact B0 | split; [exact B1 |]]] | split; [exact W0 | split; [exact W1 |]]].
  - intros i Hi. unfold mrd. rewrite (E (A + Z.of_nat i)) by lia. exact (B i Hi).
  - intros i Hi. rewrite (ati_wview_pt sg m m' (wa (A + i)) (E (A + i) ltac:(lia))). exact (Wv i Hi).
Qed.

Lemma ati_mem_inv_sub : forall (sg : list Segment) (m m' : word -> option byte),
  mem_inv sg m -> (forall x, m' x = None \/ m' x = m x) -> mem_inv sg m'.
Proof.
  intros sg m m' MI H a b Ha.
  destruct (H a) as [E | E]; rewrite E in Ha; [discriminate Ha | exact (MI a b Ha)].
Qed.

(* off the window [W], opening it changes no restriction *)
Lemma ati_rm_cons : forall L S (M : word -> option byte) (W : word * word) (x : word),
  zin_rangeb (bv_unsigned x) W = false -> restrict_mem L S M x = restrict_mem L (W :: S) M x.
Proof.
  intros L S M W x H. unfold restrict_mem, restrict_mem_by. cbv beta.
  rewrite (hiddenb_cons_window L W S x), H. cbn [negb]. rewrite andb_true_r. reflexivity.
Qed.

(* the model fields time() keeps: the maps, the lazy ranges, and every non-VM subsystem *)
Definition ati_mrel (mo mo' : Model) : Prop :=
  m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo /\ nonvm_same mo mo'.

Lemma ati_mrel_trans : forall a b c, ati_mrel a b -> ati_mrel b c -> ati_mrel a c.
Proof.
  intros a b c (E1 & E2 & N1) (F1 & F2 & N2).
  split; [congruence|]. split; [congruence|]. exact (nonvm_same_trans a b c N1 N2).
Qed.

Lemma ati_mrel_sbm : forall mo mo', same_but_materialized mo mo' -> ati_mrel mo mo'.
Proof.
  intros mo mo' H. split; [exact (same_but_materialized_vmmaps _ _ H)|].
  split; [exact (same_but_materialized_lazy _ _ H) | exact (nonvm_same_mat _ _ H)].
Qed.

(* [State.with_vdso_bump] rebuilds [m_vm] with a new vDSO count and copies every other field *)
Lemma ati_mrel_bump : forall mo, ati_mrel mo (with_vdso_bump mo).
Proof.
  intros mo. split; [reflexivity|]. split; [reflexivity|]. unfold nonvm_same. repeat split; reflexivity.
Qed.

(* a stack byte of the restricted memory has a writable view, so it is not hidden *)
Lemma ati_stk_visible : forall (segs : list Segment) L S1 (M : word -> option byte) lo hi n,
  hid_avoids_segs segs (hiddenb L S1) ->
  stk segs (restrict_mem L S1 M) lo hi -> 0 < n -> lo <= hi - n ->
  range_visible (hiddenb L S1) (Z_to_bv 64 hi - Z_to_bv 64 n)%bv (Z.to_nat n).
Proof.
  intros segs L S1 M lo hi n HA (H0 & H1 & H) Hn Hlo i Hi.
  assert (Hi' : Z.of_nat i < n) by lia.
  rewrite wa_add_nat. rewrite ati_sub_lit. rewrite unsigned_lit by lia.
  destruct (H (hi - n + Z.of_nat i) ltac:(lia)) as [Hw _].
  unfold restrict_mem in Hw. rewrite (wview_restrict segs (hiddenb L S1) HA) in Hw.
  destruct (hiddenb L S1 (wa (hi - n + Z.of_nat i))); [exfalso; apply Hw; reflexivity | reflexivity].
Qed.

(* the page arithmetic of the window: for a page-aligned [v], [sh v mod 4096] is a multiple of 512,
   so [sh v + 72, sh v + 104) lies in the page of [sh v] *)
Lemma ati_page_lo : forall v, v mod 4096 = 0 -> 0 <= v -> (sh v + 72) / 4096 * 4096 = sh v / 4096 * 4096.
Proof. intros v H0 H1. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma ati_page_hi : forall v, v mod 4096 = 0 -> 0 <= v ->
  (sh v + 72 + 32 + 4096 - 1) / 4096 * 4096 = sh v / 4096 * 4096 + 4096.
Proof. intros v H0 H1. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma ati_divmul_bound : forall z, 0 <= z -> 0 <= z / 4096 * 4096 <= z.
Proof. intros z H. Z.div_mod_to_equations. lia. Qed.

(* the shadow the strcmp check reads for the vDSO string table (AsStrcmp.astrcmp_shz at
   x = v + AVW_STRTAB, n = AVW_STRSZ - 1) is [sh v + 72, sh v + 104) *)
Lemma ati_strtab_range : forall v a, v mod 4096 = 0 -> 0 <= v ->
  8 * (sh (v + AVW_STRTAB) / 8) <= a < 8 * (sh (v + AVW_STRTAB + (AVW_STRSZ - 1)) / 8) + 8 ->
  sh v + 72 <= a < sh v + 104.
Proof. intros v a H0 H1 Ha. unfold sh, ASHADOW_BASE, AVW_STRTAB, AVW_STRSZ in *. Z.div_mod_to_equations. lia. Qed.

(* ---------------- time() at the run instance ---------------- *)

Section RunTime.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Variables vlo vb vhi : Z.
  Hypothesis Hvtop : AIMG_TOP <= vlo.
  (* The launch facts the top proves from the launch (Ref/VdsoLaunch.v proves them for Ref,
     where [vd_lo] is vlo, [vd_mid] is vb and [vd_top] is vhi):
     - Htw, Hne, Hvhi: every tail byte lies in the window [vlo, vhi); each tail segment has a
       byte; the window does not wrap (RunTailLazy.lzt_hid_avoids, lzt_mem_inv_keep and the
       lzt_*_back lemmas);
     - ROM, HVB, HENT, HUNM: the vDSO text at [vb] (its clock_gettime entry is hvdso), that
       entry an exported function, and the machine declining to run there (the walk's premises
       and the vDSO call node, Spec/VdNode.vd_at_node);
     - HVLO, Hvord, Hvb2, HVHI: the pair lies above the high shadow (AHI_LO <= vlo), so the
       shadow of its text, [pw_win vb], lies below the window and inside the lazily reserved
       high shadow [sh AHI_LO, sh aceil) of AllocRepX.akernel; the text [vb, vb + RVDSO_SPAN)
       lies in the window; the window lies below the stack ceiling (vhi <= aceil: the pair's top
       is page-aligned at or below hceil), which gives the walk's premise
       [vb + RVDSO_SPAN <= lo] and keeps the stack apart from the window. *)
  Hypothesis Htw : forall (x : Z) s, find_segment tail x 1 = Some s -> vlo <= x < vhi.
  Hypothesis Hne : forall s, In s tail -> (0 < seg_size s)%N.
  Hypothesis Hvhi : vhi <= 2 ^ 64.
  Hypothesis ROM : rvdso_rom (asegs ++ tail) vb.
  Hypothesis HVB : vb + 1460 = hvdso.
  Hypothesis HENT : vdso_entry_fn (asegs ++ tail) (Z_to_bv 64 hvdso) = Some VdsoClockGettime.
  Hypothesis HUNM : forall ms, ms_pc ms = Z_to_bv 64 hvdso ->
    RiscvSemantics.step (asegs ++ tail) ms = MachineUnmodeled.
  Hypothesis HVLO : AHI_LO <= vlo.
  Hypothesis Hvord : vlo <= vb.
  Hypothesis Hvb2 : vb + RVDSO_SPAN <= vhi.
  Hypothesis HVHI : vhi <= aceil.

  Local Notation VS := (asegs ++ tail).
  Local Notation LROM := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.seg_rom (only parsing).
  Local Notation PROM := OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (only parsing).

  (* where the window [pw_win vb] lies *)
  Lemma ati_qr :
       0x2008fff7000 <= sh vb /\ sh AHI_LO <= sh vb /\ sh vb + 1024 <= sh aceil
    /\ sh vb + 65536 <= 0x10007fff8000 /\ sh vb + 104 <= vlo /\ sh vb + 104 <= aceil
    /\ vb + 8192 <= aceil /\ vb mod 4096 = 0 /\ 0x1000000 <= vlo /\ 0 < vb.
  Proof.
    pose proof ROM as (R0 & RM & RH & _). rewrite RVDSO_SPAN_val in RH.
    pose proof Hvb2 as V2. rewrite RVDSO_SPAN_val in V2.
    pose proof Hvord as V1. pose proof HVLO as HL. pose proof HVHI as HH.
    pose proof aceil_facts as (A1 & A2 & A3).
    unfold sh, ASHADOW_BASE, AHI_LO in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [exact RM|]. split; lia.
  Qed.

  Lemma ati_zin_true : forall a : word, sh vb + 72 <= bv_unsigned a < sh vb + 104 ->
    zin_rangeb (bv_unsigned a) (pw_win vb) = true.
  Proof.
    intros a Ha. pose proof ati_qr as (QA & _ & _ & QD & _).
    unfold zin_rangeb, pw_win. cbn [fst snd]. rewrite !unsigned_lit by lia.
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma ati_zin_inv : forall a : word, zin_rangeb (bv_unsigned a) (pw_win vb) = true ->
    sh vb + 72 <= bv_unsigned a < sh vb + 104.
  Proof.
    intros a Ha. pose proof ati_qr as (QA & _ & _ & QD & _).
    unfold zin_rangeb, pw_win in Ha. cbn [fst snd] in Ha. rewrite !unsigned_lit in Ha by lia.
    apply andb_true_iff in Ha. destruct Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  Qed.

  Lemma ati_zin_false : forall a : word, ~ (sh vb + 72 <= bv_unsigned a < sh vb + 104) ->
    zin_rangeb (bv_unsigned a) (pw_win vb) = false.
  Proof.
    intros a Ha. destruct (zin_rangeb (bv_unsigned a) (pw_win vb)) eqn:E; [|reflexivity].
    exfalso. apply Ha. exact (ati_zin_inv a E).
  Qed.

  (* the window's one page is the page of [sh vb] *)
  Lemma ati_win_page : forall pg, In pg (win_pages (pw_win vb)) -> bv_unsigned pg = sh vb / page_size * page_size.
  Proof.
    intros pg Hp. pose proof ati_qr as (QA & _ & _ & QD & _ & _ & _ & QH & _ & QJ).
    assert (CL : cl_lo (pw_win vb) = sh vb / page_size * page_size).
    { unfold cl_lo, pw_win. cbn [fst]. rewrite unsigned_lit by lia. unfold page_size.
      apply ati_page_lo; [exact QH | lia]. }
    assert (CH : cl_hi (pw_win vb) = sh vb / page_size * page_size + page_size).
    { unfold cl_hi, pw_win. cbn [fst snd]. rewrite !unsigned_lit by lia. unfold page_size.
      apply ati_page_hi; [exact QH | lia]. }
    unfold win_pages in Hp. apply in_map_iff in Hp. destruct Hp as (i & Ei & Hi). apply in_seq in Hi.
    assert (NP : win_npages (pw_win vb) = 1%nat).
    { unfold win_npages, win_npagesZ. rewrite CL, CH.
      replace (sh vb / page_size * page_size + page_size - sh vb / page_size * page_size) with page_size by lia.
      rewrite Z.div_same by (unfold page_size; lia). reflexivity. }
    rewrite NP in Hi. assert (i = 0%nat) by lia. subst i pg.
    unfold win_page. rewrite CL. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
    pose proof (ati_divmul_bound (sh vb) ltac:(lia)) as DB. unfold page_size in *.
    apply unsigned_lit. lia.
  Qed.

  (* the akernel conjunct of AllocRepX.v:201: the high shadow is lazily reserved *)
  Lemma ati_ak_hi : forall (s : ast) mo, akernel s mo ->
    forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil ->
      in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true.
  Proof.
    intros s mo AK x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _). exact (K9 x Hx).
  Qed.

  (* the walk's footprint holds no cell of ACONST *)
  Lemma ati_aconst_stack : forall lo hi, aceil <= lo -> aconst_ok (lo, hi).
  Proof.
    intros lo hi H. pose proof aceil_facts as (A1 & _).
    apply aconst_ok_intro; unfold AsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
      ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL,
      sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE; lia.
  Qed.

  Lemma ati_aconst_vf : aconst_ok (A_vdso_func, A_vdso_func + 8).
  Proof.
    apply aconst_ok_intro; unfold A_vdso_func, AsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL,
      APGSZ_CELL, ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL,
      sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE; lia.
  Qed.

  (* ---- the binary's list and the run's list (Common/Cfg/RunTailLazy.v) ---- *)

  Lemma ati_wview_VS : forall (m : word -> option byte) x, wview VS m x = wview asegs m x.
  Proof. intros m x. apply wview_app_nw; first [exact Hnw | exact Hnx]. Qed.

  Lemma ati_rw_keep : forall m A cs, rw_cells asegs m A cs -> rw_cells VS m A cs.
  Proof. intros m A cs H. eapply lzt_rw_cells_keep; first [exact Hnx | exact Hnw | exact H]. Qed.

  Lemma ati_ro_keep : forall m A cs, ro_cells asegs m A cs -> ro_cells VS m A cs.
  Proof. intros m A cs H. eapply lzt_ro_cells_keep; first [exact Hnx | exact Hnw | exact H]. Qed.

  Lemma ati_stk_keep : forall m lo hi, stk asegs m lo hi -> stk VS m lo hi.
  Proof. intros m lo hi H. eapply lzt_stk_keep; first [exact Hnx | exact Hnw | exact H]. Qed.

  (* no segment of the run's list above the image is writable (PairCleanAll's [Hnw]) *)
  Lemma ati_nw_hi : forall lo' hi', AIMG_TOP <= lo' -> forall (x : word) s0, lo' <= bv_unsigned x < hi' ->
    find_segment VS (bv_unsigned x) 1 = Some s0 -> seg_writable s0 = false.
  Proof.
    intros lo' hi' Hl x s0 Hx Hf. rewrite find_segment_app in Hf.
    rewrite (asegs_find_none (bv_unsigned x)) in Hf by lia.
    change (find_segment tail (bv_unsigned x) 1 = Some s0) in Hf.
    exact (Hnw s0 (find_segment_in _ _ _ _ Hf)).
  Qed.

  (* ---- the memory with the window open ---- *)

  Lemma ati_munch_open : forall m, munch [(sh vb + 72, sh vb + 104)] m (ati_open (pw_win vb) m).
  Proof.
    intros m x Hx. cbn [outside] in Hx. destruct Hx as [Hx _].
    exact (ati_open_out (pw_win vb) m x (ati_zin_false x Hx)).
  Qed.

  Lemma ati_wmono_open : forall (sg : list Segment) m, wmono sg m (ati_open (pw_win vb) m).
  Proof.
    intros sg m x Hx. unfold ati_open, wview. cbv beta.
    destruct (zin_rangeb (bv_unsigned x) (pw_win vb)); [cbv iota; discriminate | exact Hx].
  Qed.

  Lemma ati_rw_open : forall m A cs, rw_cells VS m A cs ->
    (A + Z.of_nat (cells_size cs) <= sh vb + 72 \/ sh vb + 104 <= A) ->
    rw_cells VS (ati_open (pw_win vb) m) A cs.
  Proof.
    intros m A cs H D.
    apply (rw_cells_transport VS [(sh vb + 72, sh vb + 104)] m _ A cs H (ati_munch_open m) (ati_wmono_open VS m)).
    cbn [disjoint_from]. split; [exact D | exact I].
  Qed.

  Lemma ati_ro_open : forall m A cs, ro_cells VS m A cs ->
    (A + Z.of_nat (cells_size cs) <= sh vb + 72 \/ sh vb + 104 <= A) ->
    ro_cells VS (ati_open (pw_win vb) m) A cs.
  Proof.
    intros m A cs H D.
    apply (ro_cells_transport VS [(sh vb + 72, sh vb + 104)] m _ A cs H (ati_munch_open m)).
    cbn [disjoint_from]. split; [exact D | exact I].
  Qed.

  Lemma ati_stk_open : forall m lo hi, stk VS m lo hi -> sh vb + 104 <= lo -> stk VS (ati_open (pw_win vb) m) lo hi.
  Proof.
    intros m lo hi H D.
    apply (stk_transport VS [(sh vb + 72, sh vb + 104)] m _ lo hi H (ati_munch_open m) (ati_wmono_open VS m)).
    intros x Hx. left. cbn [outside]. split; [lia | exact I].
  Qed.

  (* the window's bytes are in no segment: above the image and below the pair *)
  Lemma ati_mem_inv_open : forall m, mem_inv VS m -> mem_inv VS (ati_open (pw_win vb) m).
  Proof.
    intros m MI a b Ha. pose proof ati_qr as (QA & _ & _ & _ & QE & _).
    unfold ati_open in Ha. destruct (zin_rangeb (bv_unsigned a) (pw_win vb)) eqn:Ez; [| exact (MI a b Ha)].
    pose proof (ati_zin_inv a Ez) as Ha'.
    unfold ro_addr. rewrite find_segment_app.
    rewrite (asegs_find_none (bv_unsigned a)) by (unfold AIMG_TOP; lia).
    destruct (find_segment tail (bv_unsigned a) 1) as [sg|] eqn:Et; [|reflexivity].
    exfalso. pose proof (Htw _ _ Et) as Hw. lia.
  Qed.

  (* the strcmp premise for a string whose shadow lies in one zero word [W0] *)
  Lemma ati_shz_word : forall m x n W0, 0 <= x -> 0 <= n -> x + n < AAPP_HI ->
    rw_cells VS m W0 [C8 (Z_to_bv 64 0)] -> 8 * (sh x / 8) = W0 -> 8 * (sh (x + n) / 8) = W0 ->
    astrcmp_shz tail m x n.
  Proof.
    intros m x n W0 H0 H1 H2 C E1 E2. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
    intros a Ha. apply (ati_c8z_mrd VS m W0 (proj1 C)). lia.
  Qed.

  (* Closing the window.  The walk ran on [ati_open (pw_win vb) m] ([m] the memory the state's
     [a_S] shows, the window hidden in it) and left [m3], the memory [pw_win vb :: S] shows of
     the full memory [MF].  The memory [S] shows of [MF] differs from [m3] only in the window,
     where it is [None] as [m] is, and [m] has no writable view there (no segment holds it). *)
  Lemma ati_close : forall L S (m MF m3 : word -> option byte) (FP : list ivl),
    (forall x : word, zin_rangeb (bv_unsigned x) (pw_win vb) = true -> hiddenb L S x = true /\ m x = None) ->
    restrict_mem L (pw_win vb :: S) MF = m3 ->
    munch FP (ati_open (pw_win vb) m) m3 ->
    wmono VS (ati_open (pw_win vb) m) m3 ->
    munch FP m (restrict_mem L S MF) /\ wmono asegs m (restrict_mem L S MF).
  Proof.
    intros L S m MF m3 FP Hh E3 MU WM. subst m3. split.
    - intros x Hx. destruct (zin_rangeb (bv_unsigned x) (pw_win vb)) eqn:Ez.
      + destruct (Hh x Ez) as [Hx1 Hx2]. rewrite Hx2. exact (restrict_mem_hidden L S MF x Hx1).
      + rewrite (ati_rm_cons L S MF (pw_win vb) x Ez), (MU x Hx). exact (ati_open_out (pw_win vb) m x Ez).
    - intros x Hx. destruct (zin_rangeb (bv_unsigned x) (pw_win vb)) eqn:Ez.
      + exfalso. apply Hx. destruct (Hh x Ez) as [_ Hx2].
        pose proof (ati_zin_inv x Ez) as Hr. pose proof ati_qr as (QA & _).
        unfold wview. rewrite Hx2.
        rewrite (asegs_find_none (bv_unsigned x)) by (unfold AIMG_TOP; lia). reflexivity.
      + pose proof (WM x) as WMx. rewrite !ati_wview_VS in WMx.
        rewrite (ati_wview_pt asegs m (ati_open (pw_win vb) m) x (ati_open_out (pw_win vb) m x Ez)) in WMx.
        rewrite (ati_wview_pt asegs (restrict_mem L (pw_win vb :: S) MF) (restrict_mem L S MF) x
                   (ati_rm_cons L S MF (pw_win vb) x Ez)).
        exact (WMx Hx).
  Qed.

  (* a cell below the window, read across the opening: from the binary's list over [m] to the
     run's list over the opened memory *)
  Local Ltac kopen H :=
    apply ati_rw_open;
    [ apply ati_rw_keep; exact H
    | left; cbn [cells_size csize Nat.add];
      unfold AAUXV_CELL, AINITED_CELL, ATIMEP_CELL, AGOT_SSP, AGOT_SSP_CELL, ASSPGUARD, ACANARY_CELL, A_vdso_func,
        AGOT_CFLAGS, AGOT_SHBASE, AsConst.ASHBASE_CELL, AllocRep.ASHBASE_CELL, ACF_ISTRCMP_CELL, ACF_STRICT_CELL, ASHW_VWNAME, ASHW_VWVER,
        ASTRCMP_GOT_CFLAGS, ASTRCMP_GOT_SHBASE, ASTRCMP_SHBASE_CELL, ASTRCMP_INITED, ASTRCMP_ISTRCMP_CELL,
        ASTRCMP_STRICT_CELL;
      lia ].

  (* a cell across a call whose footprint is [MU]'s, as Ref/F_timeRun.v's [trw] *)
  Local Ltac trw H MU WM :=
    lazymatch type of MU with
    | munch ?W ?m0 ?m1 =>
        apply (rw_cells_transport _ W m0 m1) in H;
        [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold A_vdso_func, ACANARY_CELL; lia]
    end.

  Theorem atime_inst_run : atime_stmt (KHr p tail vlo vb vhi).
  Proof.
    unfold atime_stmt, atime_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo x LB lo B vf errv.
    intros VIS A0 HP K RAUX AUX HB ST CLO LO ERR MI TP AC ARL VF HVF RAE.
    destruct x as [s d].
    change (restrict (a_L s) (a_S s) msF
            = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 P_time) fc None m (LROM asegs)) in VIS.
    change (IRHEAP p (IST s d) LB m) in HP.
    change ((lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) /\ IK p (IST s d) mo)
            /\ vcm2 vlo vb vhi (mkCfg msF mo) /\ pw_ok vb (IST s d)) in K.
    change (B + 16 <= 2 ^ 47) in RAUX.
    cbn [as_SR KHr]. unfold sr_run.
    change (cwrom (mkCfg msF mo) (PROM VS)) with (mkCfg (wrom msF (PROM VS)) mo).
    destruct K as ((OK & IKx) & V12 & PW).
    pose proof V12 as [VC1 VC2].
    pose proof PW as (PWm & PWw & PWa). cbn [i_s] in PWm, PWw, PWa.
    pose proof IKx as ((AMx & AK) & _ & _). cbn [i_s] in AMx, AK.
    pose proof AMx as (_ & _ & [AB0 AB1]).
    pose proof HP as HP0. unfold IRHEAP in HP0. cbn [i_s i_d] in HP0.
    destruct HP0 as (HR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [PI _]).
    pose proof (PROOM_of_PINV (a_st s) (proj2 (proj1 (proj1 HR))) PI) as PRM.
    pose proof ati_qr as (QA & QB & QC & QD & QE & QF & QG & QH & QI & QJ).
    pose proof aceil_facts as (ACF1 & ACF2 & ACF3).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof AUX as (av & v & rnd & execfn & r & AVC & AVL & HCB & HBA & HAV0 & HVv & HRN & HEX & HVD).
    assert (VBE : ax_sysinfo v = vb) by lia.
    unfold ATIME_STACK in LO.
    destruct (inst_canary_law p (IST s d) LB m HP) as (can & GOTC & CANC & CANR).

    (* the window: hidden (lazily reserved by akernel, not visible by pw_ok) and inside Zr *)
    assert (HWin : forall a : word, zin_rangeb (bv_unsigned a) (pw_win vb) = true ->
                     in_rangesb a (a_Zr s) = true /\ hiddenb (a_L s) (a_S s) a = true).
    { intros a Ha. pose proof (ati_zin_inv a Ha) as Ha'.
      destruct (ati_ak_hi s mo AK a ltac:(lia)) as [Z1 L1].
      split; [exact Z1|]. unfold hiddenb. rewrite L1, (PWw a Ha'). reflexivity. }
    (* no lazy address in the pair's window, from each half's maps_off: the hidden bytes avoid
       the run's list *)
    assert (HLw : forall x0 : word, vlo <= bv_unsigned x0 < vhi -> in_rangesb x0 (a_L s) = false).
    { intros x0 Hx0. destruct VC1 as (_ & MO1 & _). destruct VC2 as (_ & MO2 & _).
      destruct (Z.lt_ge_cases (bv_unsigned x0) vb) as [Hx1 | Hx1].
      - exact (lzt_L_off_window asegs (a_L s) (a_S s) (a_Zr s) _ vlo vb OK MO1 x0 ltac:(lia)).
      - exact (lzt_L_off_window asegs (a_L s) (a_S s) (a_Zr s) _ vb vhi OK MO2 x0 ltac:(lia)). }
    assert (HAV : forall S1, hid_avoids_segs VS (hiddenb (a_L s) S1)).
    { intros S1. eapply lzt_hid_avoids; first [exact Htw | exact Hne | exact Hvhi | exact (lzok_ranges OK) | exact HLw]. }
    (* the overlay holds no byte of the window [vlo, vhi), from the two halves *)
    assert (VCF : vclean vlo vhi (ms_mem msF)).
    { intros y Hy. destruct VC1 as ((VL1 & _) & _). destruct VC2 as ((VL2 & _) & _).
      destruct (Z.lt_ge_cases (bv_unsigned y) vb) as [Hy1 | Hy1];
        [exact (VL1 y ltac:(lia)) | exact (VL2 y ltac:(lia))]. }
    assert (Em : restrict_mem (a_L s) (a_S s) (ms_mem msF) = m)
      by (change (ms_mem (restrict (a_L s) (a_S s) msF) = m); rewrite VIS; reflexivity).
    assert (VCm : vclean vlo vhi m) by (rewrite <- Em; eapply lzt_vclean_restrict; exact VCF).

    (* open the window: pw_ok's 4096-byte reserve pays its page *)
    assert (BUD : eager_used mo + (bv_unsigned (snd (pw_win vb)) / page_size + 2 + pages_total (a_S s)) * page_size
                  <= vm_limit (m_vmmaps mo)).
    { unfold pw_win. cbn [snd]. rewrite unsigned_lit by lia. unfold aPhi in AB1. unfold page_size in *. lia. }
    pose proof (ati_lzok_wrom asegs (a_L s) (a_S s) (a_Zr s) msF mo (PROM VS) OK) as OKr.
    destruct (lzok_open_hidden_window_wb asegs (a_L s) (a_S s) (a_Zr s) (pw_win vb) (wrom msF (PROM VS)) mo
                (pages_total (a_S s)) OKr (fun a Ha => proj1 (HWin a Ha)) (fun a Ha => proj2 (HWin a Ha))
                (Z.le_refl _) BUD) as [OKo OE].
    assert (VISo : restrict (a_L s) (pw_win vb :: a_S s) (wrom msF (PROM VS))
                   = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_time) fc None (ati_open (pw_win vb) m) (LROM VS)).
    { rewrite OE, ati_restrict_wrom, VIS. reflexivity. }

    (* the walk's premises, over the run's list, on the opened memory *)
    assert (MIv : mem_inv VS m) by (eapply lzt_mem_inv_keep; first [exact Htw | exact MI | exact VCm]).
    pose proof (ati_mem_inv_open m MIv) as MIw.
    assert (STw : stk VS (ati_open (pw_win vb) m) lo (bv_unsigned sp))
      by (apply ati_stk_open; [exact (ati_stk_keep m lo _ ST) | lia]).
    assert (CELLw : ro_cells VS (ati_open (pw_win vb) m) AAUXV_CELL [C8 (Z_to_bv 64 av)]).
    { apply ati_ro_open; [apply ati_ro_keep; exact (proj1 AVC) | left; cbn [cells_size csize Nat.add]; unfold AAUXV_CELL; lia]. }
    assert (AUXw : ro_cells VS (ati_open (pw_win vb) m) av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)]).
    { apply ati_ro_open; [| right; lia]. apply ati_ro_keep. rewrite <- VBE.
      exact (ati_auxv_pair asegs m av v rnd execfn r AVL). }
    assert (VBLO : vb + RVDSO_SPAN <= lo) by (rewrite RVDSO_SPAN_val; lia).
    assert (SPA : bv_unsigned sp <= av) by lia.
    assert (INITw : rw_cells VS (ati_open (pw_win vb) m) AINITED_CELL [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
    { pose proof (ACONST_cell m AINITED_CELL [C1 (b8 1); C1 (b8 1)] AC ltac:(in_nth)) as K4. kopen K4. }
    assert (TIMEPw : rw_cells VS (ati_open (pw_win vb) m) ATIMEP_CELL [C8 (Z_to_bv 64 AREAL_TIME)]).
    { destruct (ACONST_icpt m AC) as (_ & _ & _ & TIMEP & _). kopen TIMEP. }
    assert (GOTw : rw_cells VS (ati_open (pw_win vb) m) AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)]) by kopen GOTC.
    assert (CANw : rw_cells VS (ati_open (pw_win vb) m) ACANARY_CELL [C8 (Z_to_bv 64 can)]) by kopen CANC.
    assert (VFw : rw_cells VS (ati_open (pw_win vb) m) A_vdso_func [C8 (Z_to_bv 64 vf)]) by kopen VF.
    assert (CELLSw : astrcmp_cells tail (ati_open (pw_win vb) m)).
    { pose proof (ACONST_cell m AGOT_CFLAGS [C8 (wz ASTRCMP_CFLAGS)] AC ltac:(in_nth)) as K1.
      destruct (ACONST_shbase m AC) as [K2 K3].
      pose proof (ACONST_cell m AINITED_CELL [C1 (b8 1); C1 (b8 1)] AC ltac:(in_nth)) as K4.
      pose proof (ACONST_istrcmp m AC) as K5.
      destruct (ACONST_cflags m AC) as [_ K6].
      assert (K1o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_GOT_CFLAGS [C8 (Z_to_bv 64 ASTRCMP_CFLAGS)]) by kopen K1.
      assert (K2o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_GOT_SHBASE [C8 (Z_to_bv 64 ASTRCMP_SHBASE_CELL)]) by kopen K2.
      assert (K3o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_SHBASE_CELL [C8 (Z_to_bv 64 ASHADOW_BASE)]) by kopen K3.
      assert (K4o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_INITED [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by kopen K4.
      assert (K5o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_ISTRCMP_CELL [C1 (Z_to_bv 8 1)]) by kopen K5.
      assert (K6o : rw_cells VS (ati_open (pw_win vb) m) ASTRCMP_STRICT_CELL [C1 (Z_to_bv 8 0)]) by kopen K6.
      split; [exact (proj1 K1o)|]. split; [exact (proj1 K2o)|]. split; [exact (proj1 K3o)|].
      split; [exact (ati_c1_mrd _ _ _ _ _ (proj1 K4o))|]. split; [exact (ati_c1_mrd _ _ _ _ _ (proj1 K5o))|].
      exact (ati_c1_mrd _ _ _ _ _ (proj1 K6o)). }
    destruct (ACONST_vw_shz m AC) as [SWN SWV].
    assert (SZNw : astrcmp_shz tail (ati_open (pw_win vb) m) VW_NAME 20).
    { apply (ati_shz_word _ VW_NAME 20 ASHW_VWNAME).
      - unfold VW_NAME. lia.
      - lia.
      - unfold VW_NAME, AAPP_HI. lia.
      - kopen SWN.
      - unfold VW_NAME. symmetry. exact ASHW_VWNAME_val.
      - unfold VW_NAME. exact ASHW_VWNAME_nul. }
    assert (SZVw : astrcmp_shz tail (ati_open (pw_win vb) m) VW_VERNAME 10).
    { apply (ati_shz_word _ VW_VERNAME 10 ASHW_VWVER).
      - unfold VW_VERNAME. lia.
      - lia.
      - unfold VW_VERNAME, AAPP_HI. lia.
      - kopen SWV.
      - unfold VW_VERNAME. symmetry. exact ASHW_VWVER_val.
      - unfold VW_VERNAME. exact ASHW_VWVER_nul. }
    (* the vDSO string table's shadow: the opened window, which reads 0 *)
    assert (SZTw : astrcmp_shz tail (ati_open (pw_win vb) m) (vb + AVW_STRTAB) (AVW_STRSZ - 1)).
    { split; [unfold AVW_STRTAB; lia|]. split; [unfold AVW_STRSZ; lia|].
      split; [unfold AVW_STRTAB, AVW_STRSZ, AAPP_HI; lia|].
      intros a Ha. pose proof (ati_strtab_range vb a QH ltac:(lia) Ha) as Ha'.
      unfold mrd, ati_open. cbv beta. rewrite (ati_zin_true (wa a)); [reflexivity|].
      rewrite wa_unsigned by lia. exact Ha'. }

    (* where the walk ends: the window still open, the lazy view over asegs, the model's fields
       that time() keeps *)
    pose (Pend := fun c : config =>
      exists (u0 u1 u2 tv w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 : word) (m3 : mem),
        restrict (a_L s) (pw_win vb :: a_S s) (cfg_ms c)
          = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 tv w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
               F (ret_pc ra) fc None m3 (LROM VS)
        /\ munch [(bv_unsigned sp - 8192, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)] (ati_open (pw_win vb) m) m3
        /\ wmono VS (ati_open (pw_win vb) m) m3 /\ mem_inv VS m3 /\ stk VS m3 lo (bv_unsigned sp)
        /\ rw_cells VS m3 A_vdso_func [C8 (Z_to_bv 64 hvdso)]
        /\ lzok asegs (a_L s) (pw_win vb :: a_S s) (a_Zr s) c
        /\ ati_mrel mo (cfg_model c)).
    assert (S1 : sreach VS Pend (mkCfg (wrom msF (PROM VS)) mo)).
    { (* 1. time() and clock_gettime() to the vDSO entry *)
      eapply (evt_sreach_lazy_av asegs VS (a_L s) (pw_win vb :: a_S s) (a_Zr s) _ (wrom msF (PROM VS)) _ mo _
                (HAV _) OKo VISo);
        [ exact (atime_front_v tail ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                   F fc (ati_open (pw_win vb) m) lo av vb vf can CELLw AUXw ROM QJ HVB SPA VBLO INITw TIMEPw GOTw CANw CANR VFw HVF
                   CELLSw SZNw SZVw SZTw STw CLO LO MIw A0) |].
      intros msF1 mo1 OK1 SBM1 HS1 P1.
      unfold atime_front_post_v in P1.
      destruct P1 as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1
                      & junk16 & junk8 & junkA & junkB & E1 & FRa & FRb & FRc & VF1 & GOT1 & CAN1 & MU1 & WM1 & MI1 & ST1).
      unfold ATIME_STACK in MU1.
      assert (Em1 : restrict_mem (a_L s) (pw_win vb :: a_S s) (ms_mem msF1) = m1)
        by (change (ms_mem (restrict (a_L s) (pw_win vb :: a_S s) msF1) = m1); rewrite E1; reflexivity).
      (* 2. the vDSO call; its frame [sp' - 240, sp') is stack, so visible *)
      assert (VFR : vdso_frame VS = 240%N) by exact (ati_vframe_of_entry _ _ _ HENT).
      assert (WR16 : wr_at VS m1 (bv_unsigned sp + -2192) 16)
        by (apply (rw_cells_wr_at VS m1 _ _ 16 FRa); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      assert (VIS240 : range_visible (hiddenb (a_L s) (pw_win vb :: a_S s))
                         (Z_to_bv 64 (bv_unsigned sp + -2224) - Z_to_bv 64 240)%bv (Z.to_nat 240)).
      { assert (STr : stk VS (restrict_mem (a_L s) (pw_win vb :: a_S s) (ms_mem msF1)) lo (bv_unsigned sp + -2224))
          by (rewrite Em1; exact ST1).
        exact (ati_stk_visible VS (a_L s) (pw_win vb :: a_S s) (ms_mem msF1) lo (bv_unsigned sp + -2224) 240
                 (HAV _) STr ltac:(lia) ltac:(lia)). }
      eapply (sreach_vd_lazy VS asegs (a_L s) (pw_win vb :: a_S s) (a_Zr s) msF1 mo1 _ (bv_unsigned sp + -2192)
                (vdr_draw (m_vdso mo1)) (vdr_calls (m_vdso mo1)) _ (HAV _) OK1 E1).
      { split; [reflexivity|]. split; [exact HENT|]. split; [apply HUNM; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact WR16 | unfold TASK_SIZE; lia]. }
      { split; reflexivity. }
      { apply HUNM. rewrite <- (restrict_pc (a_L s) (pw_win vb :: a_S s) msF1), E1. reflexivity. }
      { rewrite VFR. exact VIS240. }
      intros bs msF2 mo2 HBS L16 OK2 SBM2 E2 HS2.
      lazymatch type of E2 with
      | _ = vd_npost ?sg (VDRealtime ?tpz ?dd ?cc)
              (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20
                       ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?F0 ?pc0 ?fc0 ?rv0 ?mm ?ro0)
              (mkEffectU _ [(_, ?bb)] _ _ _ _) =>
          destruct (ati_npost_MS sg tpz dd cc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
                      r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F0 pc0 fc0 rv0 mm ro0 bb VFR)
            as (z1 & z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & fr & EQ);
          rewrite EQ in E2; clear EQ
      end.
      rewrite (ati_sub_lit (bv_unsigned sp + -2224) 240) in E2.
      replace (bv_unsigned sp + -2224 - 240) with (bv_unsigned sp + -2464) in E2 by lia.
      change (Z_to_bv 64 (bv_unsigned sp + -2464)) with (wa (bv_unsigned sp + -2464)) in E2.
      pose proof (firstn_le_length 240 fr) as FL.
      assert (SP2464 : 0 <= bv_unsigned sp + -2464) by lia.
      (* the frame write: only [sp - 2464, sp - 2224), only where the writable view has a byte *)
      pose proof (ati_vwf_munch VS (firstn 240%nat fr) m1 (bv_unsigned sp + -2464) SP2464 ltac:(lia)) as MUf.
      pose proof (ati_vwf_mem_inv VS (firstn 240%nat fr) m1 (wa (bv_unsigned sp + -2464)) MI1) as MIf.
      pose proof (ati_vwf_stk VS (firstn 240%nat fr) m1 (wa (bv_unsigned sp + -2464)) lo _ ST1) as STf.
      assert (WMf : wmono VS m1 (vdso_write_frame VS m1 (wa (bv_unsigned sp + -2464)) (firstn 240%nat fr)))
        by (intros xq Hxq; exact (ati_vwf_wmono VS _ m1 _ xq Hxq)).
      set (m1f := vdso_write_frame VS m1 (wa (bv_unsigned sp + -2464)) (firstn 240%nat fr)) in *.
      trw FRa MUf WMf. trw FRb MUf WMf. trw FRc MUf WMf. trw VF1 MUf WMf. trw CAN1 MUf WMf.
      destruct (ati_cells_split VS m1f (bv_unsigned sp + -2192) [CB 16 junk16]
                  [C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 ATW_ICPT_RET)] FRa) as [FR16 FRr].
      cbn [cells_size csize Nat.add] in FRr.
      replace (bv_unsigned sp + -2192 + Z.of_nat 16) with (bv_unsigned sp + -2176) in FRr by lia.
      (* the effect: the timespec's 16 bytes *)
      pose proof (rw_cells_CB_prefix_write VS m1f (bv_unsigned sp + -2192) 16 junk16 bs FR16 ltac:(lia)) as W16.
      rewrite L16 in W16. change (16 - 16)%nat with 0%nat in W16.
      pose proof (mem_inv_syswrite VS m1f (bv_unsigned sp + -2192) 16 junk16 bs MIf FR16 ltac:(lia)) as MI2.
      apply (rw_cells_frame VS _ _ _ (bv_unsigned sp + -2192) bs) in FRr; [| lia | lia | cbn [cells_size csize Nat.add]; lia].
      apply (rw_cells_frame VS _ _ _ (bv_unsigned sp + -2192) bs) in FRb; [| lia | lia | cbn [cells_size csize Nat.add]; lia].
      apply (rw_cells_frame VS _ _ _ (bv_unsigned sp + -2192) bs) in FRc; [| lia | lia | cbn [cells_size csize Nat.add]; lia].
      apply (rw_cells_frame VS _ _ _ (bv_unsigned sp + -2192) bs) in VF1;
        [| lia | lia | cbn [cells_size csize Nat.add]; unfold A_vdso_func; lia].
      apply (rw_cells_frame VS _ _ _ (bv_unsigned sp + -2192) bs) in CAN1;
        [| lia | lia | cbn [cells_size csize Nat.add]; unfold ACANARY_CELL; lia].
      pose proof (stk_write VS m1f lo (bv_unsigned sp + -2224) (bv_unsigned sp + -2192) bs STf ltac:(lia) ltac:(lia)) as ST2.
      assert (MUd : munch [(bv_unsigned sp - 8192, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)] (ati_open (pw_win vb) m)
                          (write_to_mem m1f (wa (bv_unsigned sp + -2192)) bs)).
      { apply munch_write; [| lia | lia | cbn [inside]; left; lia].
        apply (munch_trans _ (ati_open (pw_win vb) m) m1 m1f); [exact MU1 |].
        eapply munch_weaken; [| exact MUf]. intros xq Hxq. cbn [outside] in Hxq |- *. lia. }
      assert (WMd : wmono VS (ati_open (pw_win vb) m) (write_to_mem m1f (wa (bv_unsigned sp + -2192)) bs))
        by (apply wmono_write; exact (wmono_trans VS _ m1 m1f WM1 WMf)).
      change (write_to_mem m1f (Z_to_bv 64 (bv_unsigned sp + -2192)) bs)
        with (write_to_mem m1f (wa (bv_unsigned sp + -2192)) bs) in E2.
      set (m2 := write_to_mem m1f (wa (bv_unsigned sp + -2192)) bs) in *.
      (* 3. clock_gettime's return of 0 and time()'s epilogue *)
      eapply (evt_sreach_lazy_av asegs VS (a_L s) (pw_win vb :: a_S s) (a_Zr s) _ msF2 _ mo2 _ (HAV _) OK2 E2);
        [ exact (atime_back_v tail z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
                   sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 s4 F fc m2 lo can bs (skipn 16 junk16) junk8 junkA junkB
                   W16 FRr FRb FRc CAN1 CANR ST2 CLO LO MI2) |].
      intros msF3 mo3 OK3 SBM3 HS3 P3.
      unfold atime_back_post_v in P3.
      destruct P3 as (u0 & u1 & u2 & tv & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3
                      & E3 & MU3 & WM3 & MI3 & ST3).
      unfold ATIME_STACK in MU3.
      trw VF1 MU3 WM3.
      apply sr_done. unfold Pend. cbv beta. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, tv, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m3.
      split; [exact E3|]. split.
      { apply (munch_trans _ _ m2 m3); [exact MUd |].
        eapply munch_weaken; [| exact MU3]. intros xq Hxq. cbn [outside] in Hxq |- *. lia. }
      split; [exact (wmono_trans VS _ m2 m3 WMd WM3)|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact VF1|]. split; [exact OK3|].
      eapply ati_mrel_trans; [exact (ati_mrel_sbm _ _ SBM1)|].
      eapply ati_mrel_trans; [exact (ati_mrel_bump mo1)|].
      eapply ati_mrel_trans; [exact (ati_mrel_sbm _ _ SBM2) | exact (ati_mrel_sbm _ _ SBM3)]. }

    (* the pair's window invariants through the reach, once for each half *)
    assert (S2 : sreach VS (fun c => (Pend c /\ PairCleanAll.vcm_cfg vlo vb c) /\ PairCleanAll.vcm_cfg vb vhi c)
                   (mkCfg (wrom msF (PROM VS)) mo)).
    { eapply PairCleanAll.sreach_keep_vcm;
        first [ exact VC2
              | exact (ati_nw_hi vb vhi ltac:(lia))
              | eapply PairCleanAll.sreach_keep_vcm; first [exact S1 | exact VC1 | exact (ati_nw_hi vlo vb Hvtop)] ]. }
    eapply sreach_mono; [exact S2|].
    intros [msF3 mo3] ((PE & V1) & V2).
    unfold Pend in PE. cbv beta in PE. cbn [cfg_ms cfg_model] in PE.
    destruct PE as (u0 & u1 & u2 & tv & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3
                    & E3 & MU3 & WM3 & MI3 & ST3 & VF3 & OK3 & (EM1 & EM2 & NV)).
    assert (Em3 : restrict_mem (a_L s) (pw_win vb :: a_S s) (ms_mem msF3) = m3)
      by (change (ms_mem (restrict (a_L s) (pw_win vb :: a_S s) msF3) = m3); rewrite E3; reflexivity).
    assert (Er : ms_rom msF3 = PROM VS)
      by (change (ms_rom (restrict (a_L s) (pw_win vb :: a_S s) msF3) = PROM VS); rewrite E3; reflexivity).
    (* close the window *)
    assert (HWm : forall x0 : word, zin_rangeb (bv_unsigned x0) (pw_win vb) = true ->
                    hiddenb (a_L s) (a_S s) x0 = true /\ m x0 = None).
    { intros x0 Hx0. split; [exact (proj2 (HWin x0 Hx0))|].
      rewrite <- Em. exact (restrict_mem_hidden (a_L s) (a_S s) (ms_mem msF) x0 (proj2 (HWin x0 Hx0))). }
    destruct (ati_close (a_L s) (a_S s) m (ms_mem msF3) m3 _ HWm Em3 MU3 WM3) as [MUc WMc].
    assert (MI3a : mem_inv asegs m3) by (eapply lzt_mem_inv_back; exact MI3).
    assert (ETP : bv_unsigned tp + -164 = ATP - 164)
      by (rewrite TP, unsigned_lit by (unfold AsIface.ATP, AllocRep.ATP; lia); unfold AsIface.ATP, AllocRep.ATP; lia).
    exists (mkCfg (wrom msF3 (LROM asegs)) mo3).
    split.
    { unfold cwrom. cbn [cfg_ms cfg_model]. f_equal. rewrite <- Er. symmetry. exact (wrom_eta msF3). }
    unfold atime_post.
    exists u0, u1, u2, tv, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, (restrict_mem (a_L s) (a_S s) (ms_mem msF3)).
    split.
    { exact (ati_restrict_rewin (a_L s) (pw_win vb :: a_S s) (a_S s) msF3 _ _ _ _ _ _ _ (LROM asegs) E3). }
    split.
    { change ((lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg (wrom msF3 (LROM asegs)) mo3) /\ IK p (IST s d) mo3)
              /\ vcm2 vlo vb vhi (mkCfg (wrom msF3 (LROM asegs)) mo3) /\ pw_ok vb (IST s d)).
      split; [split | split].
      - constructor; cbn [cfg_ms cfg_model].
        + exact (lzok_ranges OK).
        + (* the pages the walk materialized lie in the window's page, the marker's *)
          eapply lazy_inv_rewindow; [exact (lzok_inv OK3) | |].
          * intros pg Hpg. pose proof (li_incl _ _ _ (lzok_inv OK3) pg Hpg) as Hin.
            cbn [all_pages] in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [| exact Hin].
            apply (window_page_in_all_pages (a_S s) (Z_to_bv 64 (sh vb)) pg PWm).
            rewrite (ati_win_page pg Hin), unsigned_lit by lia. reflexivity.
          * pose proof (li_budget _ _ _ (lzok_inv OK)) as BU. cbn [cfg_model] in BU.
            assert (EE : eager_used mo3 = eager_used mo) by (unfold eager_used; rewrite EM1, EM2; reflexivity).
            rewrite EE, EM1. exact BU.
        + exact (lzok_halted OK3).
        + (* the window's bytes still read 0: the walk wrote none of them *)
          intros a Ha Hz. change (ms_mem msF3 a = Some (Z_to_bv 8 0)).
          destruct (zin_rangeb (bv_unsigned a) (pw_win vb)) eqn:Ez.
          * assert (Hv : hiddenb (a_L s) (pw_win vb :: a_S s) a = false).
            { rewrite hiddenb_cons_window, Ez. cbn [negb]. apply andb_false_r. }
            assert (E3a : restrict_mem (a_L s) (pw_win vb :: a_S s) (ms_mem msF3) a = ms_mem msF3 a).
            { unfold restrict_mem, restrict_mem_by. cbv beta. rewrite Hv. reflexivity. }
            rewrite <- E3a, Em3.
            pose proof (ati_zin_inv a Ez) as Ha'.
            rewrite (MU3 a); [exact (ati_open_in (pw_win vb) m a Ez) |].
            cbn [outside]. unfold A_vdso_func. lia.
          * apply (lzok_zero OK3 a); [| exact Hz].
            rewrite hiddenb_cons_window, Ha, Ez. reflexivity.
        + exact (lzok_SZr OK).
        + exact (lzok_ZrL OK).
        + exact (lzok_LM OK3).
      - exact (IK_vm_ext p (IST s d) mo mo3 EM1 EM2 IKx).
      - split; [exact V1 | exact V2].
      - exact PW. }
    split; [exact NV|].
    split.
    { apply (ati_mem_inv_sub asegs m3); [exact MI3a|].
      intros x0. destruct (zin_rangeb (bv_unsigned x0) (pw_win vb)) eqn:Ez.
      - left. exact (restrict_mem_hidden (a_L s) (a_S s) (ms_mem msF3) x0 (proj2 (HWin x0 Ez))).
      - right. rewrite (ati_rm_cons (a_L s) (a_S s) (ms_mem msF3) (pw_win vb) x0 Ez), Em3. reflexivity. }
    split.
    { apply (ati_stk_ext asegs m3).
      - eapply lzt_stk_back; first [exact Hnx | exact Hnw | exact Htw | exact ST3 | (right; lia)].
      - intros a Ha.
        assert (Ez : zin_rangeb (bv_unsigned (wa a)) (pw_win vb) = false)
          by (apply ati_zin_false; rewrite wa_unsigned by lia; lia).
        rewrite (ati_rm_cons (a_L s) (a_S s) (ms_mem msF3) (pw_win vb) (wa a) Ez), Em3. reflexivity. }
    split.
    { eapply ACONST_frame; [exact AC | exact MUc | exact WMc |].
      constructor; [apply ati_aconst_stack; lia | constructor; [exact ati_aconst_vf | constructor]]. }
    split.
    { eapply rw_cells_transport; [exact ERR | exact MUc | exact WMc |].
      rewrite ETP. cbn [disjoint_from cells_size csize Nat.add]. unfold AsIface.ATP, AllocRep.ATP, A_vdso_func. lia. }
    split; [exact RAUX|].
    split.
    { eapply aauxv_ok_frame; [exact AUX | exact MUc | exact WMc |].
      constructor; [apply aauxv_win_ok_stack; lia|].
      constructor; [| constructor].
      apply aauxv_win_ok_low; [lia | unfold A_vdso_func; lia | left; unfold A_vdso_func, AAUXV_CELL; lia]. }
    split.
    { eapply (inst_RHEAP_frame p (IST s d) LB m (restrict_mem (a_L s) (a_S s) (ms_mem msF3)));
        [exact HP | exact MUc | exact WMc |].
      constructor; [left; cbn [fst]; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold aimg_client_w, A_vdso_func. lia. }
    split.
    { eapply munch_weaken; [| exact MUc]. intros xq Hxq. cbn [outside] in Hxq |- *. unfold ATIME_STACK in Hxq. lia. }
    split; [exact WMc|].
    apply (ati_rw_cells_ext asegs m3).
    - eapply lzt_rw_cells_back;
        first [exact Hnx | exact Hnw | exact Htw | exact VF3 | (left; cbn [cells_size csize Nat.add]; unfold A_vdso_func; lia)].
    - intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold A_vdso_func in Ha.
      assert (Ez : zin_rangeb (bv_unsigned (wa a)) (pw_win vb) = false)
        by (apply ati_zin_false; rewrite wa_unsigned by lia; lia).
      rewrite (ati_rm_cons (a_L s) (a_S s) (ms_mem msF3) (pw_win vb) (wa a) Ez), Em3. reflexivity.
  Qed.
End RunTime.
