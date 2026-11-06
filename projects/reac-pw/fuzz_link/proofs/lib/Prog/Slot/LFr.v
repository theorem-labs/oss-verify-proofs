(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 235 of its 337 lines of code are new or changed and 478 lines of the source are left out. *)
(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: its SR frame (the allocator-aware
   level). The entry ghost and its premises (lg, LGV), the frame relation at a cut (LFR), the cut template
   (CUT), the regions a segment / an allocator call keeps (lkeep, lcarry, mlocal), and the bookkeeping of the
   slot's own heap blocks hb (pcap's RESB: res_ok_slots A (sb_hb b0 hb) with blocks L A a permutation of
   hb ++ the entry blocks).

   The obligation the glue ends in is lib/Reusable/YL0i.v lib_contract_x_T at lib/MemFileRI.v mf_shape with
   G = llvm_G (the frame lane's widened frame_G), GI = llvm_GI (lib/MemFile.v mf_gi and the NUL at
   long_alias[300]) and output fun _ => [] (lib/Prog/LLVMFuzzerTestOneInput_c.v). The slot's kept set T is []
   until the first mark and [(f, 1304)] (the memory FILE mark_quietly opens) from then on.

   Shapes ported from libreac/fuzz_boxreg lib/Prog/LLVMFuzzerTestOneInput_fr.v (lf_fr) and libreac/fuzz_pcap
   lib/Prog/Slot/PInv.v (FR, CUTST, RESB); every constant is link's (lib/FrameAPI.v frame_facts_plain, the plain
   image). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The plain image's reserved segments lie below 0x97000 (= link_mem A_IMG_TOP)
   ========================================================================== *)

Definition LF_TOP : Z := 0x97000.

Lemma lfr_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma lfr_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? LF_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lfr_rsegs_nonnil : rsegs <> [].
Proof.
  assert (E : (match rsegs with [] => true | _ => false end) = false) by (vm_compute; reflexivity).
  intros H. rewrite H in E. discriminate E.
Qed.

Lemma lfr_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= LF_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) lfr_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma lfr_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= LF_TOP.
Proof.
  intros a n seg E. destruct (lfr_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (lfr_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma lfr_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < LF_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (lfr_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma lfr_find_img : forall B a seg, ms_segs B = rsegs -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros B a seg HS E. destruct (lfr_find_segment_in rsegs a 1 seg E) as (Hin & H1 & H2).
  destruct (lfr_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; exact lfr_rsegs_nonnil|].
  exists (segment_reservation seg). split; [rewrite HS; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

Lemma lfr_wview_out : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros B m a HS Hn Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (lfr_find_img B a seg HS E)).
Qed.

Lemma lfr_wview_hi : forall m a, LF_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold LF_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (lfr_find_top a 1 seg E). unfold LF_TOP in *. lia.
Qed.

Lemma lfr_present_of_writable : forall B m a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  writable_at rsegs m a -> present m a.
Proof.
  intros B m a HS Hn Ha W. unfold writable_at in W. rewrite (lfr_wview_out B m a HS Hn Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; exact E | contradiction].
Qed.

Lemma lfr_stk : forall m lo hi, LF_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold LF_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (lfr_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (lfr_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma lfr_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma lfr_munch_at : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha O. apply H. rewrite (MState.unsigned_lit a Ha). exact O. Qed.

Lemma lfr_ro_addr_out : forall B a, ms_segs B = rsegs -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros B a HS Hn Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hn (lfr_find_img B a seg HS E)).
Qed.

(* An image byte in a writable segment with file bytes: every memory may store to it (pcap PTac.v wr_chk). *)
Definition lfr_wr_chk (a : Z) : bool :=
  match find_segment rsegs a 1 with
  | Some seg => seg_writable seg &&
      match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with
      | Some _ => true
      | None => false
      end
  | None => false
  end.

Lemma lfr_wr_chk_ok : forall m a, 0 <= a < 2 ^ 64 -> lfr_wr_chk a = true ->
  writable_at rsegs m a /\ Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros m a Ha H. unfold lfr_wr_chk in H. unfold writable_at, wview, Mem.ro_addr.
  rewrite (MState.unsigned_lit a Ha).
  destruct (find_segment rsegs a 1) as [seg|]; [|discriminate H].
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn iota. split; [|reflexivity].
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b|];
    [discriminate | discriminate H2].
Qed.

Definition lfr_rng_chk (lo n : Z) : bool := forallb (fun i => lfr_wr_chk (lo + Z.of_nat i)) (seq 0 (Z.to_nat n)).

Lemma lfr_rng_chk_ok : forall lo n, lfr_rng_chk lo n = true -> forall a, lo <= a < lo + n -> lfr_wr_chk a = true.
Proof.
  intros lo n H a Ha. unfold lfr_rng_chk in H. rewrite forallb_forall in H.
  replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia.
  apply H. apply in_seq. lia.
Qed.


(* ==========================================================================
   2. The slot's own heap blocks hb and the allocator's bound (pcap PInv.v RESB)
   ========================================================================== *)

Definition hb_bytes (hb : list (Z * Z)) : Z := fold_right Z.add 0 (map snd hb).
Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).

Lemma hb_bytes_app : forall h1 h2, hb_bytes (h1 ++ h2) = hb_bytes h1 + hb_bytes h2.
Proof.
  intros h1 h2. unfold hb_bytes. rewrite map_app.
  induction (map snd h1) as [|x l IH]; cbn [app fold_right]; lia.
Qed.

Lemma hb_bytes_cons : forall x l, hb_bytes (x :: l) = snd x + hb_bytes l.
Proof. intros x l. reflexivity. Qed.

Lemma sb_hb_perm : forall b0 h h', Permutation h h' -> sb_hb b0 h = sb_hb b0 h'.
Proof.
  intros b0 h h' HP. unfold sb_hb. rewrite (Permutation_length HP).
  assert (E : hb_bytes h = hb_bytes h').
  { induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
    - reflexivity.
    - rewrite IH. reflexivity.
    - ring.
    - rewrite IH1, IH2. reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma sb_hb_nil : forall b0, sb_hb b0 [] = b0.
Proof. intros [l y c]. unfold sb_hb, hb_bytes. cbn. f_equal; lia. Qed.

Lemma sb_hb_cons : forall b0 r n hb, sb_hb b0 ((r, n) :: hb) = sb_malloc (sb_hb b0 hb) n.
Proof.
  intros b0 r n hb. unfold sb_malloc, sb_hb. rewrite hb_bytes_cons. cbn [length snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma sb_hb_remove : forall b0 hb1 a n hb2,
  sb_hb b0 (hb1 ++ hb2) = sb_free (sb_hb b0 (hb1 ++ (a, n) :: hb2)) n.
Proof.
  intros b0 hb1 a n hb2. unfold sb_free, sb_hb. rewrite !hb_bytes_app, hb_bytes_cons, !length_app.
  cbn [length snd sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

(* the slot holds at most 8 blocks of its own, of at most 2^20 bytes in all (it holds 5 at most: the model,
   the marks, the FILE and two text_buf / text_of blocks; 8856 + 516 + 1304 + 2 * 320 bytes) *)
Definition lroom_hb (hb : list (Z * Z)) : Prop :=
  (length hb <= 8)%nat /\ 0 <= hb_bytes hb <= 2 ^ 20.

(* the block an allocator-facing call may answer: a0 = 0 (no block) or a fresh block of n bytes *)
Definition opt_hb (r n : Z) (hb : list (Z * Z)) : list (Z * Z) := if r =? 0 then hb else (r, n) :: hb.

(* ==========================================================================
   3. The entry ghost
   ========================================================================== *)

Record lghost : Type := LGhost {
  lg_regs : bvmap 5 word;          (* regs0, at ENTRY *)
  lg_mem : word -> option byte;    (* mem0 *)
  lg_md : Model;                   (* md0 *)
  lg_L : layout;                   (* L0 *)
  lg_A : astate;                   (* A0 *)
  lg_b : sbound;                   (* b0: the driver's bound, res_ok_slots A0 b0 *)
  lg_T : list (Z * Z);             (* T0: the blocks kept from earlier driver calls *)
  lg_p : Z;                        (* the payload *)
  lg_n : Z;
  lg_pl : list byte;
  lg_j : nat;                      (* the driver's call index *)
  lg_ra : Z;
  lg_empty : Z
}.

Definition lg_S (g : lghost) : Z := spZ (lg_regs g).

(* the entry blocks (the driver's: the payload, and T0's FILE when T0 <> []) *)
Definition in_blk0 (g : lghost) (x : Z) : Prop := in_tb (blocks (lg_L g) (lg_A g)) x.

(* the kept set at a cut: T0 when it is not empty; else [] before the first mark and the FILE block the
   first mark allocated (one of the slot's own blocks) after it *)
Definition lkept (g : lghost) (hb T : list (Z * Z)) : Prop :=
  (lg_T g <> [] /\ T = lg_T g) \/
  (lg_T g = [] /\ (T = [] \/ exists f, T = [(f, MF_BLOCK)] /\ In (f, MF_BLOCK) hb)).

(* bytes and writability of the regions U kept from m to m' (both normalized memories) *)
Definition lcarry (U : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, U a -> mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a).

(* a memory predicate local to the regions U (S-FR item 4) *)
Definition mlocal (U : Z -> Prop) (Pm : (word -> option byte) -> Prop) : Prop :=
  forall m m', lcarry U m m' -> Pm m -> Pm m'.

Section LF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).

(* The frame's facts for this image (lib/FrameAPI.v frame_facts_plain at this RunCeil): LFF_of_plain below. *)
Definition LFF : Prop :=
  ms_segs B = rsegs /\
  ms_malloc B = 0x17514 /\ ms_free B = 0x173d4 /\ ms_realloc B = None /\ ms_calloc B = Some 0x1729c /\
  errno_addr B + 4 <= YM05.alloc_ceiling /\
  ms_guard B = 0x95878 /\ ms_got_guard B = 0x208d8 /\
  ms_ctx B = 0x95910 /\ ms_lock B = 0x95908 /\ ms_libc B = 0x95898 /\ ms_size_classes B = 0x10798 /\
  ms_small_cnt B = 0x107f8 /\ ms_med_cnt B = 0x10813 /\ ms_debruijn B = 0x10778 /\ ms_tp B = 0x75608 /\
  ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
  @sk_ofl_head SH = 0x95cc8 /\ @sk_ofl_lock SK = 0x95cc0 /\ @sk_threaded SK = 0x95898 + 1 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall fx' : YK11.FPState, @frame_allocator rc fx' B API).

(* the image bytes a call of the allocator keeps: in the image, not the allocator's, not errno *)
Definition lf_img (a : Z) : Prop :=
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).

(* ENTRY: the premises lib_contract_x_T gives (LLVMFuzzerTestOneInput_contract, at j < 4, ra even) *)
Definition LGV (g : lghost) : Prop :=
  lib_pre_x (LS:=mf_shape) B API SLOT_STACK (lg_empty g) (lg_L g) (lg_A g) (lg_regs g) (lg_mem g) (lg_md g)
    (lg_ra g) (lg_p g) (lg_n g) (lg_pl g) (lg_b g) /\
  llvm_GI B (lg_j g) (lg_T g) (lg_mem g) /\
  tb_live (lg_L g) (lg_A g) (lg_T g) /\
  (0 < lg_n g -> ~ In (lg_p g, lg_n g) (lg_T g)) /\
  G_img segs frame_RELRO (lg_mem g) /\
  lg_ra g mod 2 = 0 /\ (lg_j g < 4)%nat.

(* The frame relation at a cut, against the entry: the entry's premises, the allocator's state, the model
   only grown in its maps, memory above the allocator's ceiling unchanged outside the slot's stack window, the
   image unchanged outside the allocator's statics / errno / G, the entry blocks' bytes unchanged except the
   kept FILE's, the stack window and errno writable, the GOT guard, ro_agree, the allocator's bound with the
   slot's own blocks hb (blocks L A is hb ++ the entry blocks, up to order), the kept set T and the FILE's
   invariant mf_gi T. The registers (sp, gp, tp, the saved ones) are the cut predicate's (LDefs lh_ms). *)
Definition LFR (g : lghost) (hb T : list (Z * Z)) (L : layout) (A : astate)
    (mem : word -> option byte) (md : Model) : Prop :=
  LGV g /\
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (lg_md g)) /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lg_S g - SLOT_STACK <= a < lg_S g) ->
     mbyte segs mem a = mbyte segs (lg_mem g) a /\
     (writable_at segs (lg_mem g) a <-> writable_at segs mem a)) /\
  (forall a, lf_img a -> ~ in_globals llvm_G a ->
     mbyte segs mem a = mbyte segs (lg_mem g) a /\
     (writable_at segs (lg_mem g) a <-> writable_at segs mem a)) /\
  (forall a k i, In (a, k) (blocks (lg_L g) (lg_A g)) -> ~ In (a, k) (lg_T g) -> 0 <= i < k ->
     mbyte segs mem (a + i) = mbyte segs (lg_mem g) (a + i)) /\
  (forall a, lg_S g - SLOT_STACK <= a < lg_S g -> writable_at segs mem a) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  (forall i, 0 <= i < 8 -> mbyte segs mem (ms_got_guard B + i) = mbyte segs (lg_mem g) (ms_got_guard B + i)) /\
  ro_agree segs mem /\
  res_ok_slots A (sb_hb (lg_b g) hb) /\
  Permutation (blocks L A) (hb ++ blocks (lg_L g) (lg_A g)) /\
  lkept g hb T /\
  mf_gi B link_mf T mem.

(* the evt-level view of a config: its registers as they are, its FP state, and its memory with the
   read-only and the unmapped high bytes dropped (MemNorm.normalize_cj: mem_inv and task_mem hold of it) *)
Definition lcanon (fx' : YK11.FPState) (regs : bvmap 5 word) (pc : Z) (mem : word -> option byte) : machine_state :=
  MS regs (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None (normalize_cj rsegs mem) (seg_rom rsegs).

(* A cut at pc: the config, the frame relation with the slot's blocks hb and kept set T, and the evt-level cut
   predicate P of its view, up to ms_eqv (the arm files' cut predicates are in mkR form; LDefs eqv_cl). *)
Definition CUT (g : lghost) (pc : Z) (hb T : list (Z * Z)) (P : machine_state -> Prop) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx') /\
    LFR g hb T L A mem md /\
    eqv_cl P (lcanon fx' regs pc mem).

(* The regions an allocator call (calloc, free, text_buf, text_of) keeps, bytes and writability: the slot's
   frame above its sp, the image bytes that are not the allocator's or errno, the slot's own blocks and the
   entry blocks (minus what the call itself writes). The stack below sp, errno and the GOT guard come back as
   facts of their own (lpost_mem). *)
Definition lkeep (g : lghost) (hb : list (Z * Z)) (x : Z) : Prop :=
  (lg_S g - SLOT_FRAME <= x < lg_S g) \/ lf_img x \/ in_tb hb x \/ in_blk0 g x.

(* what holds of the evt-level view m' after every allocator call *)
Definition lpost_mem (g : lghost) (m' : word -> option byte) : Prop :=
  mem_inv rsegs m' /\ task_mem rsegs m' /\ stk rsegs m' (lg_S g - SLOT_STACK) (lg_S g - SLOT_FRAME) /\
  wr_at rsegs m' A_ERRNO 4 /\ guard_m m'.

(* a block the allocator just handed out: in the heap, below the stack window, apart from the image, from
   the slot's blocks and from the entry blocks *)
Definition lfresh (g : lghost) (hb : list (Z * Z)) (r n : Z) : Prop :=
  r <> 0 /\ 4096 <= r /\ r + n <= lg_S g - SLOT_STACK /\
  (forall i, 0 <= i < n -> ~ in_img B (r + i)) /\
  (forall a k, In (a, k) hb -> r + n <= a \/ a + k <= r) /\
  (forall a k, In (a, k) (blocks (lg_L g) (lg_A g)) -> r + n <= a \/ a + k <= r).

Lemma cut_close : forall (fx' : YK11.FPState) g pc hb T (P : machine_state -> Prop) L A regs mem md,
  frm_zero (@fp_csr fx') -> LFR g hb T L A mem md -> eqv_cl P (lcanon fx' regs pc mem) ->
  CUT g pc hb T P (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md).
Proof.
  intros fx' g pc hb T P L A regs mem md Hf H1 H2. exists fx', L, A, regs, mem, md.
  split; [reflexivity|]. split; [exact Hf|]. split; [exact H1 | exact H2].
Qed.

Lemma cut_open : forall g pc hb T P c (Q : config -> Prop),
  CUT g pc hb T P c ->
  (forall (fx' : YK11.FPState) L A regs mem md, frm_zero (@fp_csr fx') -> LFR g hb T L A mem md ->
     eqv_cl P (lcanon fx' regs pc mem) ->
     SR segs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) Q) ->
  SR segs c Q.
Proof.
  intros g pc hb T P c Q (fx' & L & A & regs & mem & md & -> & Hf & H1 & H2) K.
  exact (K fx' L A regs mem md Hf H1 H2).
Qed.

Lemma cut_mono : forall g pc hb T (P P' : machine_state -> Prop) c,
  (forall ms, P ms -> P' ms) -> CUT g pc hb T P c -> CUT g pc hb T P' c.
Proof.
  intros g pc hb T P P' c HP (fx' & L & A & regs & mem & md & E & Hf & H1 & (c0 & Hc & He)).
  exists fx', L, A, regs, mem, md. split; [exact E|]. split; [exact Hf|]. split; [exact H1|].
  exists c0. split; [exact (HP c0 Hc) | exact He].
Qed.

(* ---- the facts LFF gives ---- *)
Hypothesis FF : LFF.

Lemma lff_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma lff_alloc : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
  exact H.
Qed.

Lemma lff_ax : AllocExtra B (aa_MR API).
Proof.
  destruct (lff_alloc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma lff_errno : errno_addr B = A_ERRNO.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & EO & _).
  unfold errno_addr, A_ERRNO, A_TP, ERRNO_TP_OFF. rewrite TP, EO. reflexivity.
Qed.

Lemma lff_errc : errno_addr B + 4 <= YM05.alloc_ceiling.
Proof. destruct FF as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lff_tp : ms_tp B = A_TP.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _). exact TP. Qed.

Lemma lff_got : ms_got_guard B = A_GOT_GUARD_S.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lff_guard : ms_guard B = A_GUARD_S.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(* ---- the room of every allocation of the slot ---- *)
Lemma lroom : forall g hb n, LGV g -> lroom_hb hb -> 0 <= n <= 2 ^ 20 -> room_slots (sb_hb (lg_b g) hb) n.
Proof.
  intros g hb n (Hpre & _) (Hlen & Hhb) Hn.
  destruct Hpre as (_ & _ & _ & HR & Hroom & _).
  cbn [lib_room mf_shape] in Hroom. destruct Hroom as (HL & HB & HC).
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & HL0 & HB0 & _).
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [lia|]. split; [unfold CAPMAX in *; lia|].
  rewrite HC. apply (CAPOK_mono CAPMAX CAPMAX (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
Qed.

End LF.

(* the frame's record (lib/FrameAPI.v frame_facts_plain) gives LFF at every RunCeil *)
Lemma LFF_of_plain : forall (rc : YM05.RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> @LFF rc B (APIf rc) SH SK.
Proof.
  intros rc B APIf LS SH SK ra empty
    (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
     & EOFF & REP & VML & DBL & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC).
  unfold LFF. repeat (split; [assumption|]). split; [exact (ERRC rc)|].
  repeat (split; [assumption|]). intros fx'. exact (ALLOC rc fx').
Qed.
