(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* The seat and the landing of a phase of the walk of fuzz_grant's entry function
   LLVMFuzzerTestOneInput, stated once for all of its phases.

   A phase of GrantEntryDefs.v carries its machine state as `ge_body` and its own
   facts; the walk engine wants a symbolic state (`st_ok_pi`). `ge_seat` turns the
   first into the second at the phase's entry pc, and `ge_land` turns the symbolic
   state back into `ge_body` at the phase's exit. The region list in between is
   `ge_regions`, the same for every phase but for the chunks a phase knows and the
   blocks it holds, which it passes as `extra`.

   The atom numbers are the ones the ported walk tactics know (GrantACja's awrFL,
   keptFL, fs_roF, fs_rwF, aconstsF and ACbf's add_flag_region): 2 the caller's stack
   pointer, 32 the shadow base, 60 the realigned stack pointer, 516 the frame on the
   side stack, 528 its flag word, 529 its shadow bytes, and 241, 242, 273, 274 the
   image objects 0, 1, 32 and 33. A phase's own atoms go in 33..59, 61..239 or 530 up;
   240..511 are the image. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC88 GrantFrame GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the atoms of this walk ---- *)
Definition GA_SP : nat := 2%nat.     (* the caller's stack pointer            *)
Definition GA_SB : nat := 32%nat.    (* SHADOW_OFF                            *)
Definition GA_SP1 : nat := 60%nat.   (* the realigned stack pointer, s1       *)
Definition GA_F : nat := 516%nat.    (* the frame on the side stack           *)
Definition GA_FL : nat := 528%nat.   (* its flag word                         *)
Definition GA_FSH : nat := 529%nat.  (* its shadow bytes                      *)

(* The saved words of the machine frame: ra at the caller's sp - 8, then s0, s1,
   s2 .. s11 at sp - 16 - 8j, which are the registers x8, x9, x18 .. x27. *)
Definition ge_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1%nat 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8%nat 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9%nat 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18%nat 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19%nat 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 20%nat 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21%nat 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 22%nat 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23%nat 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24%nat 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25%nat 0));
    YP09.mkChunk (-96) (CVal 8 (SOff 26%nat 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27%nat 0)) ].

(* The machine frame's saved words. The body never writes them, so the window is
   read-only; the epilogue reads them back. *)
Definition ge_saved_region : YP09.region :=
  YP09.mkRegion (Some GA_SP) (-104) 0 0 0 ge_saved_chunks.
(* The spill slots above the realigned stack pointer, which the body reads back after
   every call. *)
Definition ge_spill_region (scs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some GA_SP1) 0 184 0 184 scs.
(* The frame on the side stack, with its flag word at F + 1016. *)
Definition ge_frame_region (fcs : list YP09.chunk) : YP09.region :=
  fframe_region GA_F GA_FL GE_CID fcs.
(* Its shadow bytes; a phase says which of them it may write. *)
Definition ge_shadow_region (wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
  fshadow_region GA_FSH GE_CID wlo whi cs.
(* The GOT word and the cell of the shadow base, and of the use-after-return flag. *)
Definition ge_obj_regions : YP09.smem :=
  [ got_regionP; bcell_regionP GA_SB; uar_got_regionP (A_OBJ 33); uar_cell_regionP (A_OBJ 33) ].

Fixpoint ge_sh_chunks_from (i : Z) (sh : list Z) : list YP09.chunk :=
  match sh with
  | [] => []
  | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: ge_sh_chunks_from (i + 1) t
  end.
(* The frame's shadow bytes as chunks, one per byte. *)
Definition ge_sh_chunks (sh : list Z) : list YP09.chunk := ge_sh_chunks_from 0 sh.

(* A phase's spill slots, as (offset, value) pairs. *)
Definition ge_slot_chunks (l : list (Z * Z)) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (fst p) (CVal 8 (SLit (snd p)))) l.

Lemma ge_nth_map_seq : forall (f : nat -> Z) n i, (i < n)%nat -> nth i (map f (seq 0 n)) 0 = f i.
Proof.
  intros f n i Hi. rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma ge_all_disj_app : forall (E : env) r l1 l2,
  YP09.all_disjoint E r l1 -> YP09.all_disjoint E r l2 -> YP09.all_disjoint E r (l1 ++ l2).
Proof.
  intros E r l1. induction l1 as [|x l1 IH]; intros l2 H1 H2; cbn [app YP09.all_disjoint] in *;
    [exact H2|]. destruct H1 as [Hx Hr]. split; [exact Hx | exact (IH l2 Hr H2)].
Qed.

Lemma ge_pwd_app : forall (E : env) l1 l2,
  YP09.pairwise_disjoint E l1 -> YP09.pairwise_disjoint E l2 ->
  Forall (fun r => YP09.all_disjoint E r l2) l1 ->
  YP09.pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|r l1 IH]; intros l2 H1 H2 HF; cbn [app]; [exact H2|].
  cbn [YP09.pairwise_disjoint] in H1 |- *. destruct H1 as [Ha Hp].
  inversion HF as [|x y Hx Ht]; subst.
  split; [apply ge_all_disj_app; [exact Ha | exact Hx] | exact (IH l2 Hp H2 Ht)].
Qed.

Lemma ge_sh_chunks_from_In : forall sh i j, (i < length sh)%nat ->
  In (YP09.mkChunk (j + Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (ge_sh_chunks_from j sh).
Proof.
  intros sh. induction sh as [|v t IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [ge_sh_chunks_from nth].
  - left. rewrite Z.add_0_r. reflexivity.
  - right. replace (j + Z.of_nat (S i)) with (j + 1 + Z.of_nat i) by lia.
    apply IH. cbn [length] in Hi. lia.
Qed.

Lemma ge_sh_chunks_In : forall sh i, (i < length sh)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (ge_sh_chunks sh).
Proof.
  intros sh i Hi. unfold ge_sh_chunks.
  replace (Z.of_nat i) with (0 + Z.of_nat i) by lia. apply ge_sh_chunks_from_In. exact Hi.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the environment a phase runs in ---- *)
Definition ge_E (cx : ecx) (fp : Z) (E : env) : Prop :=
  (forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
  ew E GA_SB = w64 SHADOW_OFF /\
  ew E GA_SP1 = w64 (c_sp1 cx) /\
  ew E GA_F = w64 (gF cx fp) /\
  ew E GA_FL = w64 (gFL cx fp) /\
  ew E GA_FSH = w64 (gSH cx fp).

(* ---- the region list of a phase ---- *)
Definition ge_regions0 (cx : ecx) (fp : Z) (sh : list Z) (scs fcs : list YP09.chunk)
  (wlo whi : Z) : YP09.smem :=
  ge_saved_region :: ge_spill_region scs :: ge_frame_region fcs
  :: ge_shadow_region wlo whi (ge_sh_chunks sh) :: ge_obj_regions.
Definition ge_regions (cx : ecx) (fp : Z) (sh : list Z) (scs fcs : list YP09.chunk)
  (wlo whi : Z) (extra : YP09.smem) : YP09.smem :=
  ge_regions0 cx fp sh scs fcs wlo whi ++ extra.
Definition ge_ss (cx : ecx) (fp : Z) (pc : Z) (sr : list sv) (sh : list Z)
  (scs fcs : list YP09.chunk) (wlo whi : Z) (extra : YP09.smem) (G : facts) : sstate :=
  mkSS pc sr (ge_regions cx fp sh scs fcs wlo whi extra) None G.
(* The same state with the shadow region's chunks given directly, so that a phase that
   no longer tracks the shadow bytes (a run of shadow stores) can still land. *)
Definition ge_ss_c (cx : ecx) (fp : Z) (pc : Z) (sr : list sv) (scs fcs : list YP09.chunk)
  (wlo whi : Z) (cs : list YP09.chunk) (extra : YP09.smem) (G : facts) : sstate :=
  mkSS pc sr (ge_saved_region :: ge_spill_region scs :: ge_frame_region fcs
              :: ge_shadow_region wlo whi cs :: ge_obj_regions ++ extra) None G.

(* A phase's spill slots and their values. *)
Definition ge_slots (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (l : list (Z * Z)) : Prop :=
  Forall (fun p => gslot cx W3 ms3 (fst p) (snd p) /\ 0 <= snd p < 2 ^ 64) l.

Lemma ge_sv_SOff0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

Section d.
Variable cx : ecx.
Variable fp : Z.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* ---- the chunks of a phase ---- *)

Lemma ge_slot_chunk_ok : forall (E : env) off v,
  gslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E M3 (c_sp1 cx) (YP09.mkChunk off (CVal 8 (SLit v))).
Proof.
  intros E off v Hv Hr.
  apply (chunk_ok_val SEGS E M3 (c_sp1 cx) off 8%N (SLit v) v).
  - reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hr.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hv.
Qed.

Lemma ge_slot_chunks_ok : forall (E : env) l,
  ge_slots cx W3 ms3 l ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) (ge_slot_chunks l).
Proof.
  intros E l. induction l as [|p t IH]; intros H; cbn [ge_slot_chunks map]; [constructor|].
  inversion H as [|x y [Hp Hr] Ht]; subst. constructor.
  - exact (ge_slot_chunk_ok E (fst p) (snd p) Hp Hr).
  - exact (IH Ht).
Qed.

Lemma ge_sh_chunks_from_ok : forall (E : env) sh i,
  (forall j, (j < length sh)%nat ->
     aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E M3 (gSH cx fp)) (ge_sh_chunks_from i sh).
Proof.
  intros E sh. induction sh as [|v t IH]; intros i H; cbn [ge_sh_chunks_from]; [constructor|].
  constructor.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
    rewrite Z.add_0_r in H0.
    destruct (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + i) v H0) as [Hm Hb].
    apply (chunk_ok_val SEGS E M3 (gSH cx fp) i 1%N (SLit v) v).
    + reflexivity.
    + cbn [Z.of_N]. change (8 * 1) with 8. exact Hb.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. exact Hm.
  - apply IH. intros j Hj. pose proof (H (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
    replace (gSH cx fp + (i + 1 + Z.of_nat j)) with (gSH cx fp + (i + Z.of_nat (S j))) by lia.
    exact Hs.
Qed.

Lemma ge_sh_chunks_ok : forall (E : env) sh,
  gshadow cx fp W3 ms3 sh ->
  Forall (YP09.chunk_ok SEGS E M3 (gSH cx fp)) (ge_sh_chunks sh).
Proof.
  intros E sh H. apply ge_sh_chunks_from_ok. intros j Hj.
  replace (gSH cx fp + (0 + Z.of_nat j)) with (gSH cx fp + Z.of_nat j) by lia.
  exact (H j Hj).
Qed.

(* ---- the bytes a phase's facts speak about, and what keeps them ---- *)
(* A call that leaves this phase's own memory alone keeps every byte at or above the
   realigned stack pointer, the caller's input block, the frame and its shadow, and
   the blocks the phase holds (`rs`, as (address, size) pairs). *)
Definition ge_keep_at (rs : list (Z * Z)) (a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/
  c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + fs_frame_bytes GE_CID \/
  gSH cx fp <= a < gSH cx fp + fs_frame_bytes GE_CID / 8 \/
  Exists (fun r => fst r <= a < fst r + snd r) rs.
Definition ge_keep (rs : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, ge_keep_at rs a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma ge_keep_refl : forall rs m, ge_keep rs m m.
Proof. intros rs m a _. reflexivity. Qed.

Lemma ge_keep_trans : forall rs m1 m2 m3,
  ge_keep rs m1 m2 -> ge_keep rs m2 m3 -> ge_keep rs m1 m3.
Proof. intros rs m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma ge_keep_pointwise : forall rs m m',
  (forall x, m' x = m x) -> ge_keep rs m m'.
Proof.
  intros rs m m' Hm a _. unfold aview, YP09.mbyte, mrestrict. rewrite Hm. reflexivity.
Qed.

Lemma ge_keep_sub : forall rs rs' m m',
  (forall r, In r rs -> In r rs') -> ge_keep rs' m m' -> ge_keep rs m m'.
Proof.
  intros rs rs' m m' Hin Hk a Ha. apply Hk.
  unfold ge_keep_at in Ha |- *.
  destruct Ha as [H|[H|[H|[H|H]]]]; [left|right;left|right;right;left|right;right;right;left|].
  1-4: exact H.
  right; right; right; right. apply Exists_exists in H as (r & Hr & Hb).
  apply Exists_exists. exists r. split; [exact (Hin r Hr) | exact Hb].
Qed.

Lemma ge_rdword_keep : forall rs m m' a v,
  ge_keep rs m m' -> (forall i, 0 <= i < 8 -> ge_keep_at rs (a + i)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros rs m m' a v Hk Hin Hr.
  assert (K : forall i, 0 <= i < 8 ->
    aview SEGS (w_H W3) m' (a + i) = aview SEGS (w_H W3) m (a + i))
    by (intros i Hi; apply Hk; apply Hin; lia).
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Lemma ge_garr8_keep : forall rs m m' a l,
  ge_keep rs m m' ->
  (forall i, 0 <= i < Z.of_nat (length l) -> ge_keep_at rs (a + i)) ->
  garr8 SEGS (mrestrict (w_H W3) m) a l ->
  garr8 SEGS (mrestrict (w_H W3) m') a l.
Proof.
  intros rs m m' a l Hk Hin Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (a + Z.of_nat j)
             (Hk (a + Z.of_nat j) (Hin (Z.of_nat j) ltac:(lia)))).
  exact Hv0.
Qed.

(* ---- the geometry a phase runs in ---- *)
Section e.
Variable ly3 : alayout.
Variable S3 : astate.
Variable md3 : Model.
Variable k : Z.
Hypothesis HB : ge_base B MT cx.
Hypothesis HJ : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
  (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(GE_CID, fp)].

Lemma ge_fin : In (GE_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

Lemma ge_frame_addr_eq : frame_addr ly3 GE_CID fp = gF cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  unfold gF. apply Efa.
Qed.

Lemma ge_sp_facts :
  spZ (c_regs cx) mod 16 = 0 /\
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288.
Proof.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (Hac & _).
  assert (Hx : 0 <= spZ (c_regs cx) + -288) by (unfold GE_STK in *; lia).
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hmp.
  split; [exact Hal16|]. split; [unfold GE_STK in *; lia|]. split; [lia|].
  rewrite Hsp1. lia.
Qed.

Lemma ge_F_facts :
  4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
  in_app (gF cx fp) 1024 /\
  (gF cx fp + 1024 <= IMG_LO \/ IMG_TOP <= gF cx fp) /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8.
Proof.
  pose proof HJ as (HAR3 & _).
  pose proof (frames_bounds _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 ge_fin) as HFo.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  rewrite ge_frame_addr_eq in HF0, HFc, HFia, HFo. rewrite Hfb in HFc, HFia, HFo.
  unfold off_img in HFo.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  reflexivity.
Qed.

Lemma ge_base_sp : forall E, ge_E cx fp E -> YP09.base_val E (Some GA_SP) = spZ (c_regs cx).
Proof.
  intros E (AG & _). destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Husp & _).
  cbn [YP09.base_val]. rewrite (AG GA_SP ltac:(unfold GA_SP; lia)). exact Husp.
Qed.

Lemma ge_region_saved : forall E, ge_E cx fp E -> gsaved cx W3 ms3 ->
  YP09.region_ok SEGS E M3 ge_saved_region.
Proof.
  intros E HE Hsv. pose proof (ge_base_sp E HE) as Ub.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & _).
  destruct HE as (AG & _).
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & _).
  pose proof asan_consts as (Hac & _).
  assert (HSV : forall (n : nat) (r : bv 5) off,
    Z.of_nat n = bv_unsigned r -> (n < 33)%nat ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) + off) =
      Some (bv_unsigned (getr (c_regs cx) r)) ->
    YP09.chunk_ok SEGS E M3 (spZ (c_regs cx)) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
  { intros n r off Hn Hlt Hrd.
    apply (chunk_ok_val SEGS E M3 (spZ (c_regs cx)) off 8%N (SOff n 0)
             (bv_unsigned (getr (c_regs cx) r))).
    - rewrite ge_sv_SOff0, (AG n Hlt), (HE0 n r Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hrd. }
  destruct Hsv as (Hra & Hsj).
  unfold YP09.region_ok, ge_saved_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold ge_saved_chunks.
  apply Forall_cons;
    [apply (HSV 1%nat (Z_to_bv 5 1) (-8)); [vm_compute; reflexivity | lia |
      replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact Hra] | ].
  apply Forall_cons;
    [apply (HSV 8%nat (Z_to_bv 5 (if 0 <? 2 then 8 + 0 else 16 + 0)) (-16));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia;
       exact (Hsj 0 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 9%nat (Z_to_bv 5 (if 1 <? 2 then 8 + 1 else 16 + 1)) (-24));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -24) with (spZ (c_regs cx) - 16 - 8 * 1) by lia;
       exact (Hsj 1 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 18%nat (Z_to_bv 5 (if 2 <? 2 then 8 + 2 else 16 + 2)) (-32));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -32) with (spZ (c_regs cx) - 16 - 8 * 2) by lia;
       exact (Hsj 2 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 19%nat (Z_to_bv 5 (if 3 <? 2 then 8 + 3 else 16 + 3)) (-40));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -40) with (spZ (c_regs cx) - 16 - 8 * 3) by lia;
       exact (Hsj 3 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 20%nat (Z_to_bv 5 (if 4 <? 2 then 8 + 4 else 16 + 4)) (-48));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -48) with (spZ (c_regs cx) - 16 - 8 * 4) by lia;
       exact (Hsj 4 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 21%nat (Z_to_bv 5 (if 5 <? 2 then 8 + 5 else 16 + 5)) (-56));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -56) with (spZ (c_regs cx) - 16 - 8 * 5) by lia;
       exact (Hsj 5 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 22%nat (Z_to_bv 5 (if 6 <? 2 then 8 + 6 else 16 + 6)) (-64));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -64) with (spZ (c_regs cx) - 16 - 8 * 6) by lia;
       exact (Hsj 6 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 23%nat (Z_to_bv 5 (if 7 <? 2 then 8 + 7 else 16 + 7)) (-72));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -72) with (spZ (c_regs cx) - 16 - 8 * 7) by lia;
       exact (Hsj 7 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 24%nat (Z_to_bv 5 (if 8 <? 2 then 8 + 8 else 16 + 8)) (-80));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -80) with (spZ (c_regs cx) - 16 - 8 * 8) by lia;
       exact (Hsj 8 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 25%nat (Z_to_bv 5 (if 9 <? 2 then 8 + 9 else 16 + 9)) (-88));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -88) with (spZ (c_regs cx) - 16 - 8 * 9) by lia;
       exact (Hsj 9 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 26%nat (Z_to_bv 5 (if 10 <? 2 then 8 + 10 else 16 + 10)) (-96));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -96) with (spZ (c_regs cx) - 16 - 8 * 10) by lia;
       exact (Hsj 10 ltac:(lia))] | ].
  apply Forall_cons;
    [apply (HSV 27%nat (Z_to_bv 5 (if 11 <? 2 then 8 + 11 else 16 + 11)) (-104));
      [vm_compute; reflexivity | lia |
       replace (spZ (c_regs cx) + -104) with (spZ (c_regs cx) - 16 - 8 * 11) by lia;
       exact (Hsj 11 ltac:(lia))] | ].
  apply Forall_nil.
Qed.

Lemma ge_region_spill : forall E scs, ge_E cx fp E ->
  Forall (YP09.chunk_ok SEGS E M3 (c_sp1 cx)) scs ->
  YP09.region_ok SEGS E M3 (ge_spill_region scs).
Proof.
  intros E scs HE Hcs.
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  destruct HE as (AG & Hsb & Hsp1E & _).
  assert (Ub : YP09.base_val E (Some GA_SP1) = c_sp1 cx).
  { cbn [YP09.base_val]. rewrite Hsp1E. apply unsigned_lit_small. lia. }
  unfold YP09.region_ok, ge_spill_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GE_STK. lia.
Qed.

Lemma ge_flag_addr_eq : flag_addr ly3 GE_CID fp = gFL cx fp.
Proof.
  destruct HB as (HPRE & _). destruct HPRE as (HAR0 & _).
  pose proof HJ as (_ & Hly3 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  pose proof (Efa 0 0) as E00. unfold frame_addr in E00.
  unfold gFL, flag_addr. lia.
Qed.

Lemma ge_region_frame : forall E fcs, ge_E cx fp E ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp) ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  YP09.region_ok SEGS E M3 (ge_frame_region fcs).
Proof.
  intros E fcs HE Hfl Hcs.
  pose proof ge_F_facts as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (_ & _ & HFpres & _).
  rewrite ge_frame_addr_eq, Hfb in HFpres.
  destruct (al_flag _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (_ & _ & Hfia & Hflt).
  rewrite ge_flag_addr_eq in Hfia, Hflt.
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (Ub : YP09.base_val E (Some GA_F) = gF cx fp).
  { cbn [YP09.base_val]. rewrite HFE. apply unsigned_lit_small. lia. }
  assert (HflZ : 0 <= gFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  unfold YP09.region_ok, ge_frame_region, fframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub, Hfb. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (gF cx fp + o) ltac:(lia))).
  - apply Forall_app. split; [exact Hcs|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (gF cx fp) (1024 - 8) 8%N (SOff GA_FL 0) (gFL cx fp)).
    + rewrite ge_sv_SOff0, HFLE. reflexivity.
    + cbn [Z.of_N]. change (8 * 8) with 64. exact HflZ.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. replace (gF cx fp + (1024 - 8)) with (gF cx fp + 1016) by lia.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hfl.
Qed.

Lemma ge_sh_range : 0 <= gSH cx fp /\ gSH cx fp + 128 <= 2 ^ 64.
Proof.
  pose proof ge_F_facts as (HF0 & HFc & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000)
    by (apply Z.div_le_upper_bound; lia).
  rewrite HSHeq. unfold SHADOW_OFF. lia.
Qed.

Lemma ge_region_shadow : forall E sh wlo whi, ge_E cx fp E ->
  0 <= wlo -> whi <= 128 -> gshadow cx fp W3 ms3 sh ->
  YP09.region_ok SEGS E M3 (ge_shadow_region wlo whi (ge_sh_chunks sh)).
Proof.
  intros E sh wlo whi HE Hwlo Hwhi Hsh.
  pose proof ge_sh_range as (Hs0 & Hs1).
  pose proof ge_F_facts as (_ & _ & _ & _ & HSHeq).
  pose proof HJ as (HAR3 & _).
  assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (_ & _ & _ & HFSpres).
  rewrite ge_frame_addr_eq, Hfb8 in HFSpres.
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp)
    by (unfold shadow_addr; rewrite HSHeq; reflexivity).
  rewrite Hsa in HFSpres.
  pose proof (ge_sh_chunks_ok E sh Hsh) as Hcs.
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (Ub : YP09.base_val E (Some GA_FSH) = gSH cx fp).
  { cbn [YP09.base_val]. rewrite HFSE. apply unsigned_lit_small. lia. }
  unfold YP09.region_ok, ge_shadow_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub, Hfb8. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
Qed.

Lemma ge_region_objs : forall E, ge_E cx fp E -> img_env VAL A_LIM E ->
  Forall (YP09.region_ok SEGS E M3) ge_obj_regions.
Proof.
  intros E HE HEI.
  pose proof HJ as (HAR3 & _).
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & Kuar & Kgot & Kguar).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot.
  rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar.
  rewrite (pal_uar_cell B TL) in Kuar.
  destruct HE as (AG & Hsb & _).
  pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
  pose proof (pa_obj_img 32 ltac:(lia)) as Ho32. pose proof (pa_obj_img 33 ltac:(lia)) as Ho33.
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  unfold ge_obj_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 1)) 0 8%N (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32))).
    - rewrite ge_sv_SOff0. apply (img_env_atomP E (A_OBJ 32) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
    - cbn [Z.of_N]. change (8 * 8) with 64. pose proof (pa_val_range (A_OBJ 32)). lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kgot. }
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 32)) 0 8%N (SOff GA_SB 0) SHADOW_OFF).
    - rewrite ge_sv_SOff0. exact Hsb.
    - cbn [Z.of_N]. change (8 * 8) with 64. unfold SHADOW_OFF. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kcell. }
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 0)) 0 8%N (SOff (A_OBJ 33) 0) (VAL (A_OBJ 33))).
    - rewrite ge_sv_SOff0. apply (img_env_atomP E (A_OBJ 33) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
    - cbn [Z.of_N]. change (8 * 8) with 64. pose proof (pa_val_range (A_OBJ 33)). lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kguar. }
  apply Forall_cons; [|apply Forall_nil].
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 33) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 33)) 0 4%N (SLit 1) 1).
    - reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rd32 SEGS (w_H W3) (ms_mem ms3)). exact Kuar. }
Qed.

Lemma ge_disj : forall E sh scs fcs wlo whi, ge_E cx fp E -> img_env VAL A_LIM E ->
  YP09.pairwise_disjoint E (ge_regions0 cx fp sh scs fcs wlo whi).
Proof.
  intros E sh scs fcs wlo whi HE HEI.
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof ge_F_facts as (HF0 & HFc & HFia & HFo & HSHeq).
  pose proof ge_sh_range as (Hs0 & Hs1).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
  pose proof (pa_obj_img 32 ltac:(lia)) as Ho32. pose proof (pa_obj_img 33 ltac:(lia)) as Ho33.
  pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep.
  cbn [zseps zseps_from fst snd] in Hsep.
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  pose proof (ge_base_sp E HE) as Ub2.
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  destruct HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (Ub60 : YP09.base_val E (Some GA_SP1) = c_sp1 cx)
    by (cbn [YP09.base_val]; rewrite Hsp1E; apply unsigned_lit_small; lia).
  assert (Ub516 : YP09.base_val E (Some GA_F) = gF cx fp)
    by (cbn [YP09.base_val]; rewrite HFE; apply unsigned_lit_small; lia).
  assert (Ub529 : YP09.base_val E (Some GA_FSH) = gSH cx fp)
    by (cbn [YP09.base_val]; rewrite HFSE; apply unsigned_lit_small; lia).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
  apply pairwise_disjoint_of_extents.
  unfold ge_regions0, ge_saved_region, ge_spill_region, ge_frame_region, fframe_region,
    ge_shadow_region, fshadow_region, ge_obj_regions, got_regionP, bcell_regionP,
    uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite Ub2, Ub60, Ub516, Ub529, Hfb8, Hfb.
  rewrite (EA (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (EA (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (EA (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (EA (A_OBJ 33) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HSHeq.
  unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  repeat split; lia.
Qed.

(* ---- the seat: a phase's machine state as the engine's symbolic state ---- *)
Theorem ge_seat : forall E pc sr sh l fcs wlo whi extra G,
  ge_E cx fp E -> img_env VAL A_LIM E ->
  ge_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  ge_slots cx W3 ms3 l ->
  Forall (YP09.chunk_ok SEGS E M3 (gF cx fp)) fcs ->
  0 <= wlo -> whi <= 128 ->
  YP09.regions_wf (ge_regions cx fp sh (ge_slot_chunks l) fcs wlo whi extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (ge_regions0 cx fp sh (ge_slot_chunks l) fcs wlo whi) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (ge_ss cx fp pc sr sh (ge_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HEI HBD HR HSL HFC Hwlo Hwhi Hwf Hex Hexp Hexd HG.
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & Hgregs & Hsaved & Hshadow
                     & Hflag & Hlen & Hgarr).
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold ge_ss, ge_regions.
  apply pa_entry_st_ok_full; [exact HR | exact Hwf | | | exact HG].
  - apply Forall_app. split; [|exact Hex].
    unfold ge_regions0. apply Forall_cons; [exact (ge_region_saved E HE Hsaved)|].
    apply Forall_cons; [exact (ge_region_spill E (ge_slot_chunks l) HE (ge_slot_chunks_ok E l HSL))|].
    apply Forall_cons; [exact (ge_region_frame E fcs HE Hflag HFC)|].
    apply Forall_cons; [exact (ge_region_shadow E sh wlo whi HE Hwlo Hwhi Hshadow)|].
    exact (ge_region_objs E HE HEI).
  - apply ge_pwd_app; [exact (ge_disj E sh (ge_slot_chunks l) fcs wlo whi HE HEI) | exact Hexp | exact Hexd].
Qed.

(* ---- the landing: the engine's symbolic state back as a phase's machine state ---- *)
(* The common part: everything but the shadow bytes comes out of the symbolic state. *)
Theorem ge_land_core : forall E pc sr scs fcs wlo whi cs extra G sh,
  ge_E cx fp E ->
  st_ok_pi SEGS VAL E (ge_ss_c cx fp pc sr scs fcs wlo whi cs extra G) (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  gshadow cx fp W3 ms3 sh -> length sh = GE_NSH ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  ge_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr scs fcs wlo whi cs extra G sh HE HS Hr2 Hr8 Hr9 Hr3 Hr4 SHW Hlen Hgarr.
  pose proof (ge_base_sp E HE) as Ub2.
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  pose proof ge_sh_range as (Hs0 & Hs1).
  pose proof ge_F_facts as (HF0 & HFc & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (_ & _ & Hfia & Hflt).
  rewrite ge_flag_addr_eq in Hfia, Hflt.
  assert (HflZ : 0 <= gFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & Husp & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  cbn [YP09.base_val] in Ub2.
  assert (Rsaved : YP09.region_ok SEGS E M3 ge_saved_region).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 0%nat _ HS eq_refl). }
  assert (Rframe : YP09.region_ok SEGS E M3 (ge_frame_region fcs)).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 2%nat _ HS eq_refl). }
  assert (SAV : forall (n : nat) (r : bv 5) od,
    Z.of_nat n = bv_unsigned r -> (n < 33)%nat ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) ge_saved_chunks ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) + od) =
      Some (bv_unsigned (getr (c_regs cx) r))).
  { intros n r od Hn Hlt Hin.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|apply u64_range].
    apply (field_of_region E M3 GA_SP (spZ (c_regs cx)) ge_saved_chunks (-104) 0 0 0 od 8%N
             (SOff n 0) (bv_unsigned (getr (c_regs cx) r)) Rsaved Ub2 Hin).
    - rewrite ge_sv_SOff0, (AG n Hlt), (HE0 n r Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia. }
  assert (FLG : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp)).
  { assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact HflZ].
    replace (gF cx fp + 1016) with (gF cx fp + (fs_frame_bytes GE_CID - 8)) by (rewrite Hfb; lia).
    apply (field_of_region E M3 GA_F (gF cx fp) (fcs ++ [YP09.mkChunk (fs_frame_bytes GE_CID - 8)
             (CVal 8 (SOff GA_FL 0))]) 0 (fs_frame_bytes GE_CID) 0 (fs_frame_bytes GE_CID)
             (fs_frame_bytes GE_CID - 8) 8%N (SOff GA_FL 0) (gFL cx fp) Rframe).
    - rewrite HFE. apply unsigned_lit_small. lia.
    - apply in_or_app. right. left. reflexivity.
    - rewrite ge_sv_SOff0, HFLE. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. exact HflZ.
    - cbn [Z.of_N]. lia. }
  pose proof HS as (Hfr & Hpcv & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
  unfold ge_ss_c, abs_ss, setpc in Hpcv, Hresv, Hregs.
  cbn [ss_pc ss_regs ss_resv resv_denot restrict
       ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs]
    in Hfr, Hpcv, Hpend, Hresv, Hfcsr, Hrom, Hregs.
  unfold ge_body.
  split; [rewrite Hpcv; reflexivity|].
  split; [exact Hresv|]. split; [exact Hpend|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfcsr|].
  split.
  { unfold gregs.
    split; [rewrite (Hregs (2%bv : bv 5)), Hr2, ge_sv_SOff0, Hsp1E; reflexivity|].
    split; [rewrite (Hregs (8%bv : bv 5)), Hr8, ge_sv_SOff0, (AG GA_SP ltac:(unfold GA_SP; lia));
            rewrite <- Husp; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [rewrite (Hregs (9%bv : bv 5)), Hr9, ge_sv_SOff0, Hsp1E; reflexivity|].
    split; [rewrite (Hregs (3%bv : bv 5)), Hr3, ge_sv_SOff0, (AG 3%nat ltac:(lia));
            exact (HE0 3%nat (3%bv : bv 5) eq_refl)|].
    rewrite (Hregs (4%bv : bv 5)), Hr4, ge_sv_SOff0, (AG 4%nat ltac:(lia)).
    exact (HE0 4%nat (4%bv : bv 5) eq_refl). }
  split.
  { unfold gsaved. split.
    - replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) + -8) by lia.
      exact (SAV 1%nat (1%bv : bv 5) (-8) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(unfold ge_saved_chunks; cbn [In]; tauto)).
    - assert (SJ : forall (j : Z) (n : nat) (od : Z),
        Z.of_nat n = bv_unsigned (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) -> (n < 33)%nat ->
        In (YP09.mkChunk od (CVal 8 (SOff n 0))) ge_saved_chunks ->
        od = -16 - 8 * j ->
        rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16 - 8 * j) =
          Some (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
      { intros j n od Hn Hlt Hin Hod.
        replace (spZ (c_regs cx) - 16 - 8 * j) with (spZ (c_regs cx) + od) by lia.
        exact (SAV n (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) od Hn Hlt Hin). }
      intros j Hj.
      assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                      j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 0 8%nat (-16));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 1 9%nat (-24));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 2 18%nat (-32));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 3 19%nat (-40));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 4 20%nat (-48));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 5 21%nat (-56));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 6 22%nat (-64));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 7 23%nat (-72));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 8 24%nat (-80));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 9 25%nat (-88));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      destruct Hcase as [Hc|Hcase]; [subst j; apply (SJ 10 26%nat (-96));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]|].
      subst j. apply (SJ 11 27%nat (-104));
        [vm_compute; reflexivity | lia | unfold ge_saved_chunks; cbn [In]; tauto | lia]. }
  split; [exact SHW|]. split; [exact FLG|]. split; [exact Hlen | exact Hgarr].
Qed.

Theorem ge_land : forall E pc sr sh l fcs wlo whi extra G,
  ge_E cx fp E ->
  st_ok_pi SEGS VAL E (ge_ss cx fp pc sr sh (ge_slot_chunks l) fcs wlo whi extra G)
    (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  length sh = GE_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  ge_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh l fcs wlo whi extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hlen Hsh256 Hgarr.
  pose proof ge_sh_range as (Hs0 & Hs1).
  pose proof HE as (_ & _ & _ & _ & _ & HFSE).
  assert (Rshadow : YP09.region_ok SEGS E M3 (ge_shadow_region wlo whi (ge_sh_chunks sh))).
  { exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 3%nat _ HS eq_refl). }
  assert (SHW : gshadow cx fp W3 ms3 sh).
  { intros i Hi.
    assert (Hb : 0 <= nth i sh 0 < 256).
    { rewrite Forall_forall in Hsh256. apply Hsh256. apply nth_In. exact Hi. }
    apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [|exact Hb].
    apply (field_of_region E M3 GA_FSH (gSH cx fp) (ge_sh_chunks sh) 0
             (fs_frame_bytes GE_CID / 8) wlo whi (Z.of_nat i) 1%N (SLit (nth i sh 0))
             (nth i sh 0) Rshadow).
    - rewrite HFSE. apply unsigned_lit_small. lia.
    - apply ge_sh_chunks_In. exact Hi.
    - reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia. }
  exact (ge_land_core E pc sr (ge_slot_chunks l) fcs wlo whi (ge_sh_chunks sh) extra G sh
           HE HS Hr2 Hr8 Hr9 Hr3 Hr4 SHW Hlen Hgarr).
Qed.

(* The frame's shadow bytes, as the memory holds them. *)
Definition ge_sh_now : list Z :=
  map (fun i => match aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + Z.of_nat i) with
                | Some v => v | None => 0 end) (seq 0 GE_NSH).

Lemma ge_gshadow_now : gshadow cx fp W3 ms3 ge_sh_now /\ length ge_sh_now = GE_NSH.
Proof.
  pose proof HJ as (HAR3 & _).
  pose proof ge_F_facts as (_ & _ & _ & _ & HSHeq).
  assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 ge_fin) as (_ & _ & _ & HFSpres).
  rewrite ge_frame_addr_eq, Hfb8 in HFSpres.
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp)
    by (unfold shadow_addr; rewrite HSHeq; reflexivity).
  rewrite Hsa in HFSpres.
  assert (Hlen : length ge_sh_now = GE_NSH) by (unfold ge_sh_now; rewrite length_map, length_seq; reflexivity).
  split; [|exact Hlen].
  intros i Hi. rewrite Hlen in Hi.
  unfold ge_sh_now. rewrite ge_nth_map_seq by exact Hi. cbv beta.
  pose proof (aview_some_of_apresent SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + Z.of_nat i)
                (proj1 (HFSpres (Z.of_nat i) ltac:(unfold GE_NSH in Hi; lia)))) as Hsome.
  destruct (aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + Z.of_nat i)) as [v|];
    [reflexivity | exfalso; exact (Hsome eq_refl)].
Qed.

(* Landing with a shadow region of any chunks: the shadow bytes are the ones the memory
   holds, present because the frame is. *)
Theorem ge_land_ex : forall E pc sr scs fcs wlo whi cs extra G,
  ge_E cx fp E ->
  st_ok_pi SEGS VAL E (ge_ss_c cx fp pc sr scs fcs wlo whi cs extra G) (restrict (w_H W3) ms3) ->
  sr_get sr 2 = SOff GA_SP1 0 -> sr_get sr 8 = SOff GA_SP 0 -> sr_get sr 9 = SOff GA_SP1 0 ->
  sr_get sr 3 = SOff 3%nat 0 -> sr_get sr 4 = SOff 4%nat 0 ->
  garr8 SEGS M3 (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  exists sh, ge_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr scs fcs wlo whi cs extra G HE HS Hr2 Hr8 Hr9 Hr3 Hr4 Hgarr.
  destruct ge_gshadow_now as (SHW & Hlen).
  exists ge_sh_now.
  exact (ge_land_core E pc sr scs fcs wlo whi cs extra G ge_sh_now
           HE HS Hr2 Hr8 Hr9 Hr3 Hr4 SHW Hlen Hgarr).
Qed.

(* ---- the call chain this call hands to the functions it calls ---- *)
(* cgif lib/A/ACf5.v:172 `rt_chain`: the caller's own frame goes on the chain when it
   fits under the layout's top, and its two words are where the chain wants them. *)
Lemma ge_achain : forall (rd' : reader) sp',
  (forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
     rd' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
  rdword rd' (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword rd' (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain (c_ly cx) rd' sp' (spZ (c_regs cx)) (gch cx).
Proof.
  intros rd' sp' Hk H8 H16 Hsp'.
  destruct HB as (HPRE & _).
  pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
    destruct Hal16 as [q Hq]. exists (2 * q). lia. }
  unfold gch.
  destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd'
             (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hk);
      [ replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact H8
      | replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16) by lia; exact H16
      | exact Hra4 | lia | exact Hal8 | lia | exact Hsp' ].
  - left. split; [right; left; lia | reflexivity].
Qed.

(* ---- a call that leaves this phase's own memory alone ---- *)
(* The journal of a call made from the realigned stack pointer that takes no frame of
   its own and leaves the blocks as it found them keeps every byte this phase's facts
   speak about. *)
Lemma ge_keep_call : forall rs STK1 memc mdc mem2 md2 k1,
  alloc_ceiling <= c_sp1 cx ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun r => exists n, In (fst r, n) (ablocks B ly3 S3) /\ 0 <= snd r <= req_size n) rs ->
  ajournal SEGS B STK1 (c_sp1 cx) [] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  ge_keep rs memc mem2.
Proof.
  intros rs STK1 memc mdc mem2 md2 k1 Hceil Hbl Hrs HJ1 a Ha.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct HB as (_ & _ & _ & Hpn & _).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp).
  { pose proof ge_F_facts as (_ & _ & _ & _ & HSHeq). unfold shadow_addr. rewrite HSHeq. reflexivity. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) (Hbl _ _ Hin) (Hbl _ _ Hin)); [lia | apply inFP_nil].
  - apply (F4 GE_CID fp a ge_fin); [|apply inFP_nil].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite ge_frame_addr_eq. rewrite Hfb in Ha. lia.
  - apply (F4 GE_CID fp a ge_fin); [|apply inFP_nil].
    right. unfold in_zr. cbn [fst snd]. rewrite ge_frame_addr_eq, Hsa. exact Ha.
  - apply Exists_exists in Ha as (r & Hr & Hb).
    rewrite Forall_forall in Hrs. destruct (Hrs r Hr) as (n & Hin & Hn).
    replace a with (fst r + (a - fst r)) by lia.
    apply (F2 (fst r) n (a - fst r) Hin Hin); [lia | apply inFP_nil].
Qed.

(* ---- a phase's facts across such a call ---- *)
Lemma ge_map_length : forall (f : byte -> Z) (xs : list byte), length (map f xs) = length xs.
Proof. intros f xs. induction xs as [|x xs IHx]; cbn [map length]; [reflexivity | rewrite IHx; reflexivity]. Qed.

Lemma ge_gsaved_keep : forall rs (ms ms' : machine_state),
  ge_keep rs (ms_mem ms) (ms_mem ms') -> gsaved cx W3 ms -> gsaved cx W3 ms'.
Proof.
  intros rs ms ms' Hk (Hra & Hsj).
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  split.
  - apply (ge_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hra].
  - intros j Hj. apply (ge_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
      [intros i Hi; left; lia | exact (Hsj j Hj)].
Qed.

Lemma ge_gshadow_keep : forall rs (ms ms' : machine_state) sh,
  ge_keep rs (ms_mem ms) (ms_mem ms') ->
  Z.of_nat (length sh) <= fs_frame_bytes GE_CID / 8 ->
  gshadow cx fp W3 ms sh -> gshadow cx fp W3 ms' sh.
Proof.
  intros rs ms ms' sh Hk Hlen Hs i Hi.
  rewrite (Hk (gSH cx fp + Z.of_nat i)); [exact (Hs i Hi)|].
  right; right; right; left. lia.
Qed.

Lemma ge_gslot_keep : forall rs (ms ms' : machine_state) off v,
  ge_keep rs (ms_mem ms) (ms_mem ms') -> 0 <= off -> off <= 184 ->
  gslot cx W3 ms off v -> gslot cx W3 ms' off v.
Proof.
  intros rs ms ms' off v Hk H0 H1 Hv.
  pose proof ge_sp_facts as (Hal & Hlo & Hhi & Hsp1).
  apply (ge_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [intros i Hi; left; lia | exact Hv].
Qed.

Lemma ge_gfb_keep : forall rs (ms ms' : machine_state) off v,
  ge_keep rs (ms_mem ms) (ms_mem ms') -> 0 <= off < fs_frame_bytes GE_CID ->
  gfb cx fp W3 ms off v -> gfb cx fp W3 ms' off v.
Proof.
  intros rs ms ms' off v Hk Hoff Hv. unfold gfb in Hv |- *.
  rewrite (Hk (gF cx fp + off)); [exact Hv|]. right; right; left. lia.
Qed.

Lemma ge_flag_keep : forall rs (ms ms' : machine_state),
  ge_keep rs (ms_mem ms) (ms_mem ms') ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (gF cx fp + 1016) = Some (gFL cx fp) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016) = Some (gFL cx fp).
Proof.
  intros rs ms ms' Hk Hv.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  apply (ge_rdword_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk);
    [intros i Hi; right; right; left; lia | exact Hv].
Qed.

Lemma ge_gfarr_keep : forall rs (ms ms' : machine_state) off l,
  ge_keep rs (ms_mem ms) (ms_mem ms') -> 0 <= off ->
  off + Z.of_nat (length l) <= fs_frame_bytes GE_CID ->
  gfarr cx fp W3 ms off l -> gfarr cx fp W3 ms' off l.
Proof.
  intros rs ms ms' off l Hk H0 H1 Hg. unfold gfarr in Hg |- *.
  apply (ge_garr8_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [|exact Hg].
  intros i Hi. rewrite ge_map_length in Hi. right; right; left. lia.
Qed.

Lemma ge_input_keep : forall rs (ms ms' : machine_state),
  ge_keep rs (ms_mem ms) (ms_mem ms') ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)).
Proof.
  intros rs ms ms' Hk Hg.
  apply (ge_garr8_keep rs (ms_mem ms) (ms_mem ms') _ _ Hk); [|exact Hg].
  intros i Hi. rewrite ge_map_length in Hi. right; left. unfold c_n. lia.
Qed.

Lemma ge_gtab_keep : forall rs (ms ms' : machine_state) t T,
  ge_keep rs (ms_mem ms) (ms_mem ms') -> In (t, 460) rs ->
  gtab B cx ly3 S3 W3 ms t T -> gtab B cx ly3 S3 W3 ms' t T.
Proof.
  intros rs ms ms' t T Hk Hin (Hb & Ht & Hl & Hbytes).
  split; [exact Hb|]. split; [exact Ht|]. split; [exact Hl|].
  intros i Hi H438 H439 H451.
  rewrite (Hk (t + i)); [exact (Hbytes i Hi H438 H439 H451)|].
  right; right; right; right. apply Exists_exists. exists (t, 460).
  split; [exact Hin | cbn [fst snd]; lia].
Qed.

End e.

End d.

End c.
End b.
End a.
