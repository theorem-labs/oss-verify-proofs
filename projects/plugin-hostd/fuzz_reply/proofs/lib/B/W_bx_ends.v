(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, block `ends` of image B's SEG_EXIT (fuzz_reply.asan-ubsan
   0x84f08-0x84fe8, lib/B/W_bx_defs.v lx_ends_S): the two nested loops after relay_finish that call
   check_shape_ends(&g_s[k], "", &at) for every open g_s[k] whose fd is order[i].  Ported from the PROVED image-A
   donor b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v:3016-5868 (AX_call to the end
   of lx_ends' proof: XEWalk, XETrans, the pure model lemmas, xe_call, the loops and lx_ends).
   B vs A, each read from the objdump of fuzz_reply.asan-ubsan (sha256
   10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c):
   - the entry 0x84f08 spills norder to F+152 AND SB + g_s/8 to F+144 (`sd a0,144(s1)` at 0x84f28; A kept it in s5),
     takes SB from s11 (x27; A: s10), and loads .str.3 (0x20ee0, A_OBJ 25) into s3 once (A: auipc a1 at every call).
     F+144 and F+152 are not cells of bx_frame, and the walk owns them inside the frame region (awr F (sp0 - F)).
   - the registers of the loops: g_s in s8 (x24; A: s6), SB + (g_s+4)/8 in s6 (x22; A: s8), .str.3 in s3 (x19),
     order cell s10 (x26; A: s9), trips left s7 (x23; A: s11), slot cursors s4 = s5 (x20, x21; A: s3, s4), shadow
     cursors s9 = SB + HA/8 (x25; A: s7, reloaded from F+144 at each outer head) and s11 = SB + (HA+4)/8 (x27;
     A: s10).  B's loop CLOBBERS s3, s10, s11.
   - the partial-granule arms 0x84fac / 0x84fc0 branch to __asan_report_load4 (0x8510c / 0x85110) with bge (A: blt
     back); their shadow byte is 0 (g_s is zero-shadowed), so the symbolic run never takes them.
   - the struct source fields the loop reads are fd at +0 and open at +4 (lw 0(s4) / lw 4(s4)), as on A; g_s is
     0x5d8e60 (A_OBJ 19), ASRC = 96, the shadow step 12.
   - check_shape_ends is B's lx_cshe_spec (W_bx_defs.v): its stack budget is 112 + LDROP_STK, its post also keeps
     errno's view, and the prefix's home is one disjunction (taken here at its in_rom /\ ashp arm with XE_LIT_S).
   - the frame after the entry is bx_frame (aframe_at without F+152). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Variable B : asyms. Variable MT : ameter_ops. Variables XM_LIB XN_LIB : Z -> Z. Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop. Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop. Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop. Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
(* ---- the hypotheses this block uses, each verbatim from lib/B/W_LLVMFuzzerTestOneInput_exit.v's Section lx ---- *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Hypothesis MLM : ameter_laws MT.
Hypothesis ERR : errno_law B.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis CSHE : lx_cshe_spec B MT (BASE + AF_fr_check_shape_ends).
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis XE_LIT_S : ashp B (VAL AX_lit_empty) 1.
(* ---- the derived facts the spine proves from them (the brief's list (b)), verbatim ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis HG_MODEL : forall a,
  inG [(rg_src fr_RG, 8); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_send_dead fr_RG, 1);
       (rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis XE_ERR_HI : rg_out fr_RG + 8 <= as_errno B.
Hypothesis XE_ERR_S : as_errno B + 4 <= rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= as_errno B.
Hypothesis XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Hypothesis XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).

(* the statements' defs at this Section's variables, under the donor's names *)
#[local] Notation lx_ends_cost := (W_bx_defs.lx_ends_cost MT).
#[local] Notation lx_cshe_cost := (W_bx_defs.lx_cshe_cost MT).
#[local] Notation lx_cshe_home := (W_bx_defs.lx_cshe_home B).
#[local] Notation lx_ends_post := (W_bx_defs.lx_ends_post B MT G_fr fr_FP).

(* the symbolic-run scaffolding the walk uses (the entry run is journalled; the other three runs use XEWalk's
   journal-free xw_run / xw_run_to below) *)
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* read-only image ranges: one segment check by vm_compute (the donor's :440-449) *)
Definition xe_romseg (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? lo) &&
    (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma xe_romseg_ok : forall lo hi a, xe_romseg lo hi = true -> lo <= a < hi -> in_rom segs a.
Proof.
  intros lo hi a H Ha. unfold xe_romseg in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
(* ============================================================ the pieces of the block ============== *)
(* the slot the inner loop stands at, and the callee's OWN G (the expected / held cells of that slot) *)
Definition xe_HA (k : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat k.
Definition xe_G (k : nat) : list (Z * Z) := [(xe_HA k + 64, 32)].

(* the model's slot update (W_LLVMFuzzerTestOneInput_drain.v set_nth), with errno floated *)
Fixpoint xe_set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: xe_set_nth n' x l'
  | _, [] => []
  end.
Definition xe_set_slot (m : lmod) (k : nat) (o : option hsrc) (ev : Z) : lmod :=
  LM (lm_k m) (xe_set_nth k o (lm_hs m)) (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).

(* ---- what check_shape_ends' journal keeps, in the six shapes this file reads it in ---- *)
Definition xe_kept_by (G FP : list (Z * Z)) (F AT : Z) (W : world segs) (mem : word -> option byte)
    (W' : world segs) (mem' : word -> option byte) (ly : alayout) (S : astate) (ly' : alayout) (S' : astate)
  : Prop :=
  (forall a, in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> ~ inFP FP a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (F - lx_CSHE_STK <= a < F + AX_XO) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, F <= a < F + AX_XO -> ~ (AT <= a < AT + 8) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, F - lx_CSHE_STK <= a < F + AX_XO -> apresent (w_H W') mem' a).

(* a present byte is writable (LPS's wview reads the memory first) *)
Lemma xe_wr_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a [EH [b Eb]]. unfold writable_at, wview, mrestrict. rewrite EH, Eb. discriminate.
Qed.

(* the journal of one check_shape_ends call, read as the six keeps above *)
Lemma xe_keeps_of_journal : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx segs B G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S W mem md [] ly' S' W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner segs B G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds segs B LAWS ly' S' W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.

(* ---- the state the two loops carry (the cut's facts, the model's evolution and the meter).  B: the frame is
   bx_frame, and the two cells the entry wrote (F+152 norder, F+144 SB + g_s/8) are carried ---- *)
Definition xe_inv (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk) /\
  bx_frame cx (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
  amodel_at B ly S W mem m /\
  ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly S /\
  (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m0 ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  length (lm_hs m) = 4%nat /\
  (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m0) None) (nth j (lm_hs m) None)) /\
  lm_k m = lm_k m0 /\ lm_G m = lm_G m0 /\ lm_es m = lm_es m0 /\
  lm_c m = lx_ctl_ev (lm_c m0) (ct_ev (lm_c m)) /\
  lm_O m = lm_O m0 /\ lm_mx m = lm_mx m0 /\ lm_cap m = lm_cap m0 /\ lm_out m = lm_out m0 /\
  lm_gn m = lm_gn m0 /\ lm_nfd m = lm_nfd m0 /\
  frames S = frames S3 /\
  mo_le MT S3 S (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m)) /\
  mo_ok MT S (lx_ends_cost (lm_hs m)) /\
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A /\ 0 <= A <= Z.of_nat (length (lm_O m0)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder /\ 1 <= norder <= 4 /\
  val_mem segs (arm W mem) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31).

(* The registers of the two loops (B's objdump 0x84f08-0x84fe8; x18 = s2 .. x27 = s11).
   s3 / s6 / s8 hold .str.3, SB + (g_s+4)/8 and g_s for every trip; the inner loop keeps them. *)
Definition xe_regs_keep (cx : lfcx) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 19 = w64 (VAL AX_lit_empty) /\ getr regs 22 = w64 (shadow_addr (rg_s fr_RG + 4)) /\
  getr regs 24 = w64 (rg_s fr_RG).
(* 0x84f3c, the outer loop's head: the trip counter i in s2.  norder is NOT in a register here (s3 holds .str.3;
   the tail reads norder back from F+152), so the norder parameter is carried only to name the trip. *)
Definition xe_regs_outer (cx : lfcx) (i norder : Z) (regs : bvmap 5 word) : Prop :=
  xe_regs_keep cx regs /\ getr regs 18 = w64 i.
(* 0x84f5c, the inner loop's head, and 0x84f90, its advance: the slot cursor s4 = s5, its two shadow cursors
   s9 / s11, the frame cell of order[i] in s10, and the trips left in s7 *)
Definition xe_regs_slot (cx : lfcx) (i : Z) (k : nat) (n : Z) (regs : bvmap 5 word) : Prop :=
  xe_regs_keep cx regs /\ getr regs 18 = w64 i /\
  getr regs 20 = w64 (xe_HA k) /\ getr regs 21 = w64 (xe_HA k) /\
  getr regs 25 = w64 (shadow_addr (xe_HA k)) /\ getr regs 27 = w64 (shadow_addr (xe_HA k + 4)) /\
  getr regs 26 = w64 (lf_F cx + AX_ORDER + 4 * i) /\ getr regs 23 = w64 n.

(* ============================================================ XEWalk: the tools of the four runs ======== *)
(* The run chain of W_journal.v:632-703 (SRr_chain_pi_tok_AJX / SRr_run_to_pi_tok_AJX) without the journal: the
   same symbolic engine (YP0c.v sym_run_pi_tok_sound / sym_run_to_pi_tok_sound) and the same post, minus the
   journal clause.  xe_head_run / xe_inner_run / xe_adv_run carry no journal, so their runs use these. *)
Definition xw_post (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
    (r : ptrun_status wsym) (ms : machine_state) (mdc : Model) (Q : world segs -> config -> Prop) : Prop :=
  forall ws ms' mat',
    length ws = sh_j st' ->
    img_env VAL A_LIM (extK E K ws) ->
    match r with
    | PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (SIGMA s)) (restrict (w_H W) ms')
    | _ => st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
    end ->
    sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma xw_run_nj : forall W n E K Bx Bspan SH ss st' r ms mdc Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH n ss = (st', r) ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  xw_post W E K Bx SH ss st' r ms mdc Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E K Bx Bspan SH ss st' r ms mdc Q HK HE HS Hsh Hchk Hrun Hobl Hk.
  change (@pl_tpi _ PL_fr) with (ptree_of_list fr_prog_listing) in Hrun.
  rewrite <- (@pl_tw_eq _ PL_fr) in Hrun.
  destruct (sym_run_pi_tok_sound wsym segs (clookup pa_tbl) VAL SIGMA fr_prog_listing pa_fetch_ok pa_cert
              pa_B_ok A_LIM A_LIM_text pl_lim pl_len K Bx Bspan SH HK n E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
    as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs pa_wx W ms msr' mdc Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb mdc model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
  apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
  - rewrite Hmm. exact Hsh'.
  - cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
  - rewrite Hmm. exact Hfr.
  - rewrite Hmm. exact Hgr.
Qed.
Lemma xw_run_to_nj : forall W n stop E K Bx Bspan SH ss st' r ms mdc Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH n stop ss = (st', r) ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  xw_post W E K Bx SH ss st' r ms mdc Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E K Bx Bspan SH ss st' r ms mdc Q HK HE HS Hsh Hchk Hrun Hobl Hk.
  change (@pl_tpi _ PL_fr) with (ptree_of_list fr_prog_listing) in Hrun.
  rewrite <- (@pl_tw_eq _ PL_fr) in Hrun.
  destruct (sym_run_to_pi_tok_sound wsym segs (clookup pa_tbl) VAL SIGMA fr_prog_listing pa_fetch_ok pa_cert
              pa_B_ok A_LIM A_LIM_text pl_lim pl_len K Bx Bspan SH HK n stop E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
    as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs pa_wx W ms msr' mdc Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb mdc model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
  apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
  - rewrite Hmm. exact Hsh'.
  - cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
  - rewrite Hmm. exact Hfr.
  - rewrite Hmm. exact Hgr.
Qed.
(* paj_after_run_tok (W_kit.v:470) without the journal hypothesis *)
Ltac xw_after_run HS SHOK :=
  let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
  let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  let HEI := fresh "HEI" in
  intros ws ms' mat' Hlen HEI HS SHOK HF HFr HG;
  cbn [sh_j sh_ss] in Hlen, HS, SHOK;
  repeat (let w := fresh "w" in
    destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
  (destruct ws; [clear Hlen | discriminate Hlen]);
  cbn [extK length Nat.add] in HS, SHOK, HEI;
  cbn [ms_mem mkst] in HF, HFr, HG;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.
(* paj_run_tok / paj_run_to_tok (W_kit.v:491-536) over xw_run_nj / xw_run_to_nj *)
Ltac xw_run HS SHOK Bspan :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run: no img_env" end in
        eapply (xw_run_nj W FUEL E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
                  ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
Ltac xw_run_to HS SHOK Bspan stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in
        (sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run_to: no img_env" end in
        eapply (xw_run_to_nj W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS
                  SHOK ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
Definition xw_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers' environment of an entry state: the registers, then the extra atoms 32.. *)
Ltac xw_env regs extra E HE HEI HAE EEo :=
  remember (Eimg (Ereg regs extra)) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs extra) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
Lemma xw_den : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v HU Hv. apply bv_eq. rewrite unsigned_lit_small by lia. exact HU. Qed.
Lemma xw_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. apply bv_eq. fold (U E (SOff n 0)). rewrite U_SOff, Z.add_0_r. unfold zcanon, M64.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  apply Z.mod_small. lia.
Qed.
(* a register of a symbolic state, as the denotation of its symbolic value (prreg without the normalization) *)
Ltac xw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr; cbn [ms_regs restrict mkst] in Hr
  end.
Lemma xw_rg_s : rg_s fr_RG = 0x5d8e60.
Proof. reflexivity. Qed.
(* B: HA and HA + 4 share g_s's first shadow granule's byte: SHADOW_OFF + 0x5d8e60 / 8 = 0x7fff8000 + 0xbb1cc *)
Lemma xw_shgs : shadow_addr (rg_s fr_RG) = 0x800b31cc /\ shadow_addr (rg_s fr_RG + 4) = 0x800b31cc.
Proof. split; vm_compute; reflexivity. Qed.

(* ---- (2) the outer head 0x84f3c: s10 = F + 192 + 4 i, s7 = 4, s4 = s5 = g_s (s8), s11 = s6, s9 = F+144 (read
   through s1: atom 32 = SB + g_s / 8) ---- *)
Definition XW_KEPT_HEAD : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 22; 24; 28; 29; 30; 31]%bv.
Definition xw_hd_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))] ].
Definition xw_ss_head : sstate := mkSS AX_outer sr_atoms xw_hd_regions None (mkFacts [] [] []).

(* ---- arithmetic of the cursors ---- *)
Lemma xw_atom_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H1 H2 H3. apply xw_den; [exact (U_atom_off E n v c H1 H2 H3) | exact H3]. Qed.
Lemma xw_sh96 : forall x, shadow_addr x + 12 = shadow_addr (x + 96).
Proof.
  intros x. unfold shadow_addr. replace (x + 96) with (x + 12 * 8) by ring. rewrite Z.div_add by lia. lia.
Qed.
Lemma xw_sh_rng : forall x, 0 <= x < 2 ^ 40 -> 0 <= shadow_addr x < 2 ^ 41.
Proof.
  intros x Hx. unfold shadow_addr, SHADOW_OFF.
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma xw_HA_rng : forall k, (k < 5)%nat -> 0x5d8e60 <= xe_HA k <= 0x5d8e60 + 384 /\ xe_HA k mod 8 = 0.
Proof.
  intros k Hk. unfold xe_HA, ASRC. rewrite xw_rg_s.
  destruct k as [|[|[|[|[|k]]]]]; [..|lia]; (split; [cbn; lia | reflexivity]).
Qed.

(* a run over read-only regions leaves the memory as it was (the drain's ds_meq) *)
Ltac xw_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* the final registers and materialization of a run's end state, for the post's existentials *)
Ltac xw_ex := lazymatch goal with |- context [mkCfg (mkst ?r _ _ _) (with_vm_backing _ ?X _)] => exists r, X end.

(* ---- (4) the inner advance 0x84f90 and the outer tail 0x84fd0: norder at F+152 through s1, read-only ---- *)
Definition xw_adv_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))] ].
Definition xw_adv_facts : facts :=
  mkFacts [ (18%nat, mkAF 0 3 0); (23%nat, mkAF 1 4 0); (32%nat, mkAF 1 4 0) ] [] [].
Definition xw_ss_adv : sstate := mkSS AX_adv sr_atoms xw_adv_regions None xw_adv_facts.
Definition XW_KEPT_ADV : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 22; 24; 26; 28; 29; 30; 31]%bv.

(* ---- (3) the inner head 0x84f5c: the slot's fd and open fields through s4 (shadow-checked: their shadow byte is
   the zero byte of g_s's granule, so the run decides both checks and never reaches 0x84fac / 0x84fc0), order[i]
   through s10 (the frame, not checked).  atoms 32 = fd, 33 = open, 34 = order[i], 35 = SB; s9 / s11 are pinned to
   their shadow-address form ---- *)
Definition xw_in_sr : list sv :=
  sr_set (sr_set sr_atoms 25 (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))))
    27 (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3))).
Definition xw_in_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0))];
    YP09.mkRegion (Some 26%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))] ].
Definition xw_in_facts : facts :=
  mkFacts [ (20%nat, mkAF 0x5d8e60 (0x5d8e60 + 288) 3); (32%nat, mkAF 0 (2 ^ 31 - 1) 0);
            (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition xw_ss_in : sstate := mkSS AX_inner xw_in_sr xw_in_regions None xw_in_facts.
Definition xw_in_SH : list shent := [ mkSHE 20 0 96 ].
Definition xw_in_Bx : sv := SOff 35 0.
Definition xw_in_extra (fd op oi : Z) : list word := map (Z_to_bv 64) [fd; op; oi; SB].
Definition XW_KEPT_IN : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 28; 29; 30; 31]%bv.
Lemma xw_shU : forall E n a v, ew E n = Z_to_bv 64 SB -> U E a = v -> 0 <= v < 2 ^ 40 ->
  U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SRL a (SLit 3))) = shadow_addr v.
Proof.
  intros E n a v Hn Ha Hv. rewrite !U_SAlu, (U_atom E n SB Hn), Ha, U_lit by (unfold SB; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= v / 8) by (apply Z.div_pos; lia).
  assert (v / 8 <= v) by (apply Z.div_le_upper_bound; lia).
  unfold zcanon, M64, shadow_addr, SHADOW_OFF, SB. rewrite (Z.mod_small (v / 8)) by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac xw_in_slot KR N25 N27 P25 P27 :=
  unfold xe_regs_slot, xe_regs_keep;
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)),
    (KR 20%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)), (KR 26%bv ltac:(cbv; tauto)),
    (KR 23%bv ltac:(cbv; tauto));
  rewrite N25, N27, <- P25, <- P27;
  repeat split; assumption.

(* ---- (1) the entry 0x84f08: norder stored at F+152 and SB + g_s / 8 at F+144 through s1 (the frame cells,
   written), g_s in s8, SB + (g_s+4)/8 in s6, .str.3 in s3; atoms 19 = norder, 27 = SB ---- *)
Definition xw_en_regions : smem := [ YP09.mkRegion (Some 9%nat) 144 160 144 160 [] ].
Definition xw_en_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (19%nat, mkAF 1 4 0); (27%nat, mkAF SB SB 0) ] [] [].
Definition xw_ss_en : sstate := mkSS AX_after_rf sr_atoms xw_en_regions None xw_en_facts.
Definition XW_KEPT_EN : list (bv 5) := [1; 2; 3; 4; 8; 9; 27]%bv.
Lemma xw_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma xw_img_off : forall E, img_env VAL A_LIM E -> forall a c, (A_TEXT <= a < A_LIM)%nat ->
  0 <= VAL a + c < 2 ^ 64 -> U E (SOff a c) = VAL a + c.
Proof. intros E HE a c Ha Hc. rewrite U_SOff, (HE a Ha). apply zcanon_id. unfold M64. lia. Qed.
(* the auipc atoms of 0x84f14 (g_s, A_OBJ 19) and 0x84f34 (.str.3, A_OBJ 25) *)
Lemma xw_val_gs : VAL 260 = rg_s fr_RG.
Proof. vm_compute. reflexivity. Qed.
Lemma xw_val_lit : VAL 266 = VAL AX_lit_empty.
Proof. reflexivity. Qed.

(* ---- the four runs.  Only the first writes memory (the frame cells F+144 and F+152); the others are register
   arithmetic, one read of F+144 or F+152, two shadow-checked reads of the slot and one read of order[i]. ---- *)
(* (1) 0x84f08 -> 0x84f3c: g_nout = 0 is NOT here (lx_rf_site did it); this run stores norder at F+152 and the
   shadow cursor of g_s at F+144, and sets up the counter, g_s, its second shadow cursor and .str.3. *)
Lemma xe_entry_run : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 27 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem'
         (with_vm_backing (m_vm_lazy md) X md) kk /\
       xe_regs_outer cx 0 norder regs' /\
       val_mem segs (arm W mem') (lf_F cx + AX_NORDER) 8 norder /\
       val_mem segs (arm W mem') (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
  intros cx W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder HJ R2 R9 R8 R3 R4 R19 R27 Hn
    HSTK HXO HF0 HF1 HAWR.
  pose proof asan_consts as (CC1 & _).
  destruct xw_shgs as (SG0 & SG4).
  xw_env regs (@nil word) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 norder) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_en
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_after_rf)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_en. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_en_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. unfold AX_XO in HXO. exact (HAWR o ltac:(lia)).
    - cbn [pairwise_disjoint all_disjoint xw_en_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E19, E27, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 27 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_after_rf)) with (Z_to_bv 64 (BASE + AX_after_rf)).
  paj_run_to_tok RUNTO HS HJ SHOK xw_span AX_outer.
  { cbn [ss_mem add_cond xw_ss_en xw_en_regions].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
        unfold AX_XO in HXO; left; split; [left; lia | lia]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem xw_ss_en xw_en_regions In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite U9 in Hr. unfold AX_GS8 in Hna. lia. }
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (xw_pres_grows W _ _ a HG1 Hp)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (VG : U E (SOff 260 0) = rg_s fr_RG)
    by (rewrite (U_img_atom E HEI 260) by (unfold A_TEXT, A_LIM; lia); exact xw_val_gs).
  assert (VG4 : U E (SOff 260 4) = rg_s fr_RG + 4)
    by (rewrite (xw_img_off E HEI 260 4) by (unfold A_TEXT, A_LIM in *; rewrite ?xw_val_gs, ?xw_rg_s; lia);
        rewrite xw_val_gs; reflexivity).
  assert (VL : U E (SOff 266 0) = VAL AX_lit_empty)
    by (rewrite (U_img_atom E HEI 266) by (unfold A_TEXT, A_LIM; lia); exact xw_val_lit).
  assert (SVN : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_NORDER) 8 norder).
  { unfold arm, AX_NORDER.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 152 8%N (SOff 19 0) norder RG0).
    - exact U9.
    - right. left. reflexivity.
    - rewrite xw_den_atom. exact E19.
    - zside.
    - zside. }
  assert (SVG : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG))).
  { unfold arm, AX_GS8.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N
      (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 0) (SLit 3))) (shadow_addr (rg_s fr_RG)) RG0).
    - exact U9.
    - left. reflexivity.
    - apply xw_den; [apply xw_shU; [exact E27 | exact VG | rewrite xw_rg_s; lia] | rewrite SG0; lia].
    - rewrite SG0. zside.
    - zside. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_EN HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (18%bv : bv 5) N18. xw_reg HS (19%bv : bv 5) N19. xw_reg HS (22%bv : bv 5) N22.
  xw_reg HS (24%bv : bv 5) N24.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) (with_vm_backing _ ?X _)] => exists r, mm, X end.
  split; [reflexivity|]. split; [exact HJ|].
  split.
  { unfold xe_regs_outer, xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)).
    split; [|rewrite N18; reflexivity].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split.
    { rewrite N19. unfold w64. pose proof (pa_val_range AX_lit_empty) as VR.
      apply xw_den; [exact VL | exact VR]. }
    split.
    { rewrite N22. unfold w64.
      apply xw_den; [apply xw_shU; [exact E27 | exact VG4 | rewrite xw_rg_s; lia] | rewrite SG4; lia]. }
    { rewrite N24. unfold w64. apply xw_den; [exact VG | rewrite xw_rg_s; lia]. } }
  split; [exact SVN|]. split; [exact SVG|]. split; [exact K1 | exact P1].
Qed.

(* (2) 0x84f3c -> 0x84f5c: the slot cursors of trip i.  One read, F+144. *)
Lemma xe_head_run : forall cx (W : world segs) regs mem md i norder,
  xe_regs_outer cx i norder regs -> 0 <= i < 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) ->
  SRr segs W (cfg_at segs (BASE + AX_outer) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       c' = cfg_at segs (BASE + AX_inner) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
       xe_regs_slot cx i 0 4 regs').
Proof.
  intros cx W regs mem md i norder HR Hi HF0 HF1 Mg.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18).
  pose proof asan_consts as (CC1 & _).
  destruct xw_shgs as (SG0 & SG4).
  xw_env regs [Z_to_bv 64 (shadow_addr (rg_s fr_RG))] E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 (shadow_addr (rg_s fr_RG)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_head
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_outer)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_head. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_hd_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lf_F cx) 144 8 (SOff 32 0) (shadow_addr (rg_s fr_RG)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite SG0; zside | zside |].
      exact Mg.
    - cbn [pairwise_disjoint all_disjoint xw_hd_regions]. exact (conj I I).
    - split; [exact I | split; [exact I | exact I]]. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 27 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_outer)) with (Z_to_bv 64 (BASE + AX_outer)).
  xw_run_to HS SHOK xw_span AX_inner.
  xw_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_HEAD HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (20%bv : bv 5) N20. xw_reg HS (21%bv : bv 5) N21. xw_reg HS (25%bv : bv 5) N25.
  xw_reg HS (26%bv : bv 5) N26. xw_reg HS (27%bv : bv 5) N27. xw_reg HS (23%bv : bv 5) N23.
  pmkst HS. rewrite Em.
  apply SRr_ret. split; [reflexivity|]. xw_ex. split; [reflexivity|].
  unfold xe_regs_slot, xe_regs_keep.
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)).
  split; [repeat split; assumption|]. split; [assumption|].
  split; [rewrite N20, xw_den_atom, (EEo 24%nat 24%bv eq_refl), R24; unfold xe_HA; f_equal; lia|].
  split; [rewrite N21, xw_den_atom, (EEo 24%nat 24%bv eq_refl), R24; unfold xe_HA; f_equal; lia|].
  split; [rewrite N25, xw_den_atom, E32; unfold xe_HA, w64; do 2 f_equal; lia|].
  split; [rewrite N27, xw_den_atom, (EEo 22%nat 22%bv eq_refl), R22; unfold xe_HA; do 2 f_equal; lia|].
  split; [|rewrite N23; reflexivity].
  rewrite N26. unfold w64. apply xw_den; [|unfold AX_ORDER; lia].
  assert (E18 : ew E 18 = Z_to_bv 64 i) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
  rewrite !U_SAlu, (U_atom_off E 9 (lf_F cx) 192 E9), (U_atom E 18 i E18), U_lit by lia.
  cbn [zalu_raw]. change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  unfold zcanon, M64, AX_ORDER. rewrite (Z.mod_small (i * 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* (4) 0x84f90 -> 0x84f5c (the next slot), or through the outer tail 0x84fd0 -> 0x84f3c / 0x84fe8.  The tail
   reads norder back from F+152.  No memory write. *)
Lemma xe_adv_run : forall cx (W : world segs) regs mem md i (k : nat) norder,
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       (((S k < 4)%nat /\
         c' = cfg_at segs (BASE + AX_inner) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_slot cx i (S k) (4 - Z.of_nat (S k)) regs') \/
        ((S k = 4)%nat /\ i + 1 < norder /\
         c' = cfg_at segs (BASE + AX_outer) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_outer cx (i + 1) norder regs') \/
        ((S k = 4)%nat /\ i + 1 = norder /\
         c' = cfg_at segs (BASE + AX_done) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_keep cx regs'))).
Proof.
  intros cx W regs mem md i k norder HR Hk Hi Hn HF0 HF1 Mn.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
  pose proof asan_consts as (CC1 & _).
  pose proof (xw_HA_rng k ltac:(lia)) as (HA1 & HA2).
  xw_env regs [Z_to_bv 64 norder] E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = Z_to_bv 64 i) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew E 20 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E25 : ew E 25 = Z_to_bv 64 (shadow_addr (xe_HA k)))
    by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 (shadow_addr (xe_HA k + 4)))
    by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E23 : ew E 23 = Z_to_bv 64 (4 - Z.of_nat k)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E32 : ew E 32 = Z_to_bv 64 norder)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_adv
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_adv)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_adv. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_adv_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lf_F cx) 152 8 (SOff 32 0) norder);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mn.
    - cbn [pairwise_disjoint all_disjoint xw_adv_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_adv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18, E23, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 27 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_adv)) with (Z_to_bv 64 (BASE + AX_adv)).
  xw_run HS SHOK xw_span.
  xw_meq HF Em1. clear HF HFr HG0.
  assert (SHR1 : 0 <= shadow_addr (xe_HA k) < 2 ^ 41) by (apply xw_sh_rng; lia).
  assert (SHR2 : 0 <= shadow_addr (xe_HA k + 4) < 2 ^ 41) by (apply xw_sh_rng; lia).
  psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
  - (* 0x84fa4 bnez s7 taken: another slot, back to 0x84f5c *)
    rewrite branch_ne_U, (U_atom_off E 23 (4 - Z.of_nat k) (-1) E23), U_lit in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    xw_run_to HS SHOK xw_span AX_inner.
    xw_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    xw_reg HS (18%bv : bv 5) N18. xw_reg HS (20%bv : bv 5) N20. xw_reg HS (21%bv : bv 5) N21.
    xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27. xw_reg HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1.
    apply SRr_ret. split; [reflexivity|]. xw_ex. left.
    split; [lia|]. split; [reflexivity|].
    unfold xe_regs_slot, xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
      (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 26%bv ltac:(cbv; tauto)).
    split; [repeat split; assumption|].
    split; [rewrite N18, xw_den_atom, E18; reflexivity|].
    split; [rewrite N20, (xw_atom_off E 20 (xe_HA k) 96 E20) by lia; unfold w64, xe_HA, ASRC; apply (f_equal (Z_to_bv 64)); lia|].
    split; [rewrite N21, (xw_atom_off E 21 (xe_HA k) 96 E21) by lia; unfold w64, xe_HA, ASRC; apply (f_equal (Z_to_bv 64)); lia|].
    split.
    { rewrite N25, (xw_atom_off E 25 (shadow_addr (xe_HA k)) 12 E25) by lia. unfold w64. apply (f_equal (Z_to_bv 64)).
      rewrite xw_sh96. apply (f_equal shadow_addr). unfold xe_HA, ASRC. lia. }
    split.
    { rewrite N27, (xw_atom_off E 27 (shadow_addr (xe_HA k + 4)) 12 E27) by lia. unfold w64. apply (f_equal (Z_to_bv 64)).
      rewrite xw_sh96. apply (f_equal shadow_addr). unfold xe_HA, ASRC. lia. }
    split; [assumption|].
    rewrite N23, (xw_atom_off E 23 (4 - Z.of_nat k) (-1) E23) by lia. unfold w64. apply (f_equal (Z_to_bv 64)). lia.
  - (* 0x84fa4 bnez s7 not taken: the slot was the last one, 0x84fa8 j 0x84fd0, the outer tail *)
    rewrite branch_ne_U, (U_atom_off E 23 (4 - Z.of_nat k) (-1) E23), U_lit in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hk3 : k = 3%nat) by lia. clear Hc.
    xw_run HS SHOK xw_span.
    xw_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
    + (* 0x84fd8 bne s2,a0 taken: i + 1 < norder, back to the outer head *)
      rewrite branch_ne_U, (U_atom_off E 18 i 1 E18), (U_atom E 32 norder E32) in Hc by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      xw_run_to HS SHOK xw_span AX_outer.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (18%bv : bv 5) N18.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right; left.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      unfold xe_regs_outer, xe_regs_keep.
      rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
        (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
        (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)).
      split; [repeat split; assumption|].
      rewrite N18, (xw_atom_off E 18 i 1 E18) by lia. reflexivity.
    + (* 0x84fd8 bne s2,a0 not taken: i + 1 = norder, 0x84fdc j 0x84fe8 *)
      rewrite branch_ne_U, (U_atom_off E 18 i 1 E18), (U_atom E 32 norder E32) in Hc by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      xw_run_to HS SHOK xw_span AX_done.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right; right.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      unfold xe_regs_keep.
      rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
        (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
        (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)).
      repeat split; assumption.
Qed.

(* (3) 0x84f5c -> 0x84f8c (the call) or 0x84f90 (the next slot): the two inlined shadow checks of g_s[k].open
   and g_s[k].fd (their shadow byte is 0 - g_s is in the instance's zero-shadow ranges - so the partial-granule
   arms 0x84fac / 0x84fc0 are not taken), then the two tests; the call's arguments a0 = s4, a1 = s3 (.str.3),
   a2 = F + 208. *)
Lemma xe_inner_run : forall cx (W : world segs) regs mem md ly S md0 i (k : nat) (n : Z) (op fd oi : Z),
  AR segs B ly S W mem md0 ->
  xe_regs_slot cx i k n regs -> (k < 4)%nat -> 0 <= i < 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (xe_HA k) 4 fd -> 0 <= fd < 2 ^ 31 ->
  val_mem segs (arm W mem) (xe_HA k + 4) 4 op -> 0 <= op < 2 ^ 31 ->
  val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 oi -> 0 <= oi < 2 ^ 31 ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       ((op <> 0 /\ oi = fd /\
         c' = cfg_at segs (BASE + AX_call) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         getr regs' 10 = w64 (xe_HA k) /\ getr regs' 11 = w64 (VAL AX_lit_empty) /\
         getr regs' 12 = w64 (lf_F cx + AX_AT) /\
         xe_regs_slot cx i k n regs') \/
        ((op = 0 \/ oi <> fd) /\
         c' = cfg_at segs (BASE + AX_adv) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_slot cx i k n regs'))).
Proof.
  intros cx W regs mem md ly S md0 i k n op fd oi HAR HR Hk Hi HF0 HF1 Mfd Hfd Mop Hop Moi Hoi.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
  pose proof asan_consts as (CC1 & _).
  pose proof (xw_HA_rng k ltac:(lia)) as (HA1 & HA2).
  assert (HA3 : xe_HA k <= 0x5d8e60 + 288) by (unfold xe_HA, ASRC; rewrite xw_rg_s; lia).
  xw_env regs (xw_in_extra fd op oi) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (VAL AX_lit_empty)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E26 : ew E 26 = Z_to_bv 64 (lf_F cx + AX_ORDER + 4 * i))
    by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 oi)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (U20 : bv_unsigned (ew E 20) = xe_HA k) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = lf_F cx + AX_ORDER + 4 * i)
    by (rewrite E26; apply unsigned_lit_small; unfold AX_ORDER; lia).
  assert (P25 : getr regs 25 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
  { rewrite R25. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom E 20 _ E20 ltac:(lia)) | lia]. }
  assert (P27 : getr regs 27 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
  { rewrite R27. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k + 4) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom_off E 20 _ 4 E20 ltac:(lia) ltac:(lia)) | lia]. }
  assert (HS : st_ok_pi segs VAL E xw_ss_in
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_inner)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_in. apply pa_entry_st_ok_full.
    - unfold xw_in_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE; assumption.
    - vm_compute. reflexivity.
    - unfold xw_in_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val segs E _ (xe_HA k) 0 4 (SOff 32 0) fd);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          rewrite Z.add_0_r. exact Mfd.
        * apply (chunk_ok_val segs E _ (xe_HA k) 4 4 (SOff 33 0) op);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          exact Mop.
      + rewrite U26. unfold AX_ORDER in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (lf_F cx + 192 + 4 * i) 0 4 (SOff 34 0) oi);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Moi.
    - unfold xw_in_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U26. unfold AX_ORDER.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xw_in_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (HBx : U E xw_in_Bx = SHADOW_OFF)
    by (unfold xw_in_Bx; rewrite (U_atom E 35 SB E35) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs xw_in_Bx xw_in_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable B LAWS ly S W mem md0 (xe_HA k) 96 HAR).
      destruct AZS_s as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi. rewrite xw_rg_s in Hzlo, Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 20 _ E20) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (BASE + AX_inner)) with (Z_to_bv 64 (BASE + AX_inner)).
  xw_run HS SHOK xw_span.
  xw_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
  - (* 0x84f68 beqz a0 taken: the slot is closed, on to 0x84f90 *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    xw_run_to HS SHOK xw_span AX_adv.
    xw_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
    pmkst HS. rewrite Em2, Em1.
    apply SRr_ret. split; [reflexivity|]. xw_ex. right.
    split; [left; exact Hc|]. split; [reflexivity|].
    xw_in_slot KR N25 N27 P25 P27.
  - (* 0x84f68 beqz a0 not taken: the slot is open; the shadow check of s->fd, s->fd and order[i] *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    xw_run HS SHOK xw_span.
    xw_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
    + (* 0x84f7c bne taken: another fd, on to 0x84f90 *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
      xw_run_to HS SHOK xw_span AX_adv.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right.
      split; [right; lia|]. split; [reflexivity|].
      xw_in_slot KR N25 N27 P25 P27.
    + (* 0x84f7c bne not taken: the slot's fd is order[i]; the call's arguments, to the jal at 0x84f8c *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
      xw_run_to HS SHOK xw_span AX_call.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
      xw_reg HS (10%bv : bv 5) N10. xw_reg HS (11%bv : bv 5) N11. xw_reg HS (12%bv : bv 5) N12.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. left.
      split; [exact Hc|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite N10, xw_den_atom, E20; reflexivity|].
      split; [rewrite N11, xw_den_atom, E19; reflexivity|].
      split; [rewrite N12, (xw_atom_off E 9 (lf_F cx) 208 E9) by lia; reflexivity|].
      xw_in_slot KR N25 N27 P25 P27.
Qed.
(* ============================================================ XETrans: the transport kit ============== *)
(* the model's globals outside g_s (every byte amodel_at reads in the image, but errno and g_s) *)
Definition XE_GLOBS : list (Z * Z) :=
  [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8);
   (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1);
   (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_gone fr_RG, 1); (rg_lock fr_RG, 12);
   (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Ltac xe_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac xe_or n := lazymatch n with
  | O => first [left; lia | lia]
  | S ?m => right; xe_or m
  end.
Lemma xe_inG_of : forall G lo n a, In (lo, n) G -> lo <= a < lo + n -> inG G a.
Proof.
  intros G lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.
Lemma xe_inG_xeG : forall k a, inG (xe_G k) a -> xe_HA k + 64 <= a < xe_HA k + 96.
Proof.
  intros k a Ha. unfold inG, xe_G in Ha. apply Exists_exists in Ha as (r & [<- | []] & Hz).
  unfold in_zr in Hz. cbn [fst snd] in Hz. lia.
Qed.
Lemma xe_globs_rng : forall a, inG XE_GLOBS a ->
  0 <= a < rg_out fr_RG + 8 /\ (a < rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= a).
Proof.
  intros a Ha. unfold inG, XE_GLOBS in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  unfold in_zr in Hz. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [fst snd fr_RG fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max
          rg_send_eintr rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in Hz |- *;
     unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC in *; lia |]).
  destruct Hr.
Qed.
Lemma xe_globs_G : forall a, inG XE_GLOBS a -> inG G_fr a.
Proof.
  intros a Ha. unfold inG, XE_GLOBS in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  unfold in_zr in Hz. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [fst snd] in Hz;
     first [ solve [apply HG_MODEL; eapply xe_inG_of; [ | exact Hz]; xe_in]
           | solve [apply HG_RFc; eapply xe_inG_of; [ | exact Hz]; xe_in]
           | solve [apply HG_SL; unfold G_SL; eapply xe_inG_of; [ | exact Hz]; xe_in] ] |]).
  destruct Hr.
Qed.

(* views and writability, one byte at a time *)
Definition xe_bk (W : world segs) (mem : word -> option byte) (W' : world segs) (mem' : word -> option byte)
    (b : Z * Z) : Prop :=
  forall a, fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W' mem' a.
Lemma xe_vm_view : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat k)); [exact (Hv k Hk)|].
  apply HK. lia.
Qed.
Lemma xe_garr8_view : forall (W W' : world segs) mem mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  garr8 segs (arm W mem) a l -> garr8 segs (arm W' mem') a l.
Proof.
  intros W W' mem mem' a l HK Hg. apply (garr8_frame segs (arm W mem) (arm W' mem') a l Hg).
  intros x Hx. unfold arm. apply (mbyte_of_aview segs). exact (HK x Hx).
Qed.
Lemma xe_awr_pres : forall (W' : world segs) mem' a n,
  (forall x, a <= x < a + n -> apresent (w_H W') mem' x) -> awr W' mem' a n.
Proof. intros W' mem' a n HP i Hi. apply xe_wr_of_present. apply HP. lia. Qed.
Lemma xe_div8 : forall x, 0 <= x -> 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* lists of slots *)
Lemma xe_nth_some : forall {T : Type} k (l : list (option T)) x, nth k l None = Some x ->
  nth_error l k = Some (Some x) /\ (k < length l)%nat.
Proof.
  intros T k l x. revert k. induction l as [|y l IH]; intros [|k] H; cbn [nth nth_error length] in *; try discriminate.
  - subst. split; [reflexivity | lia].
  - destruct (IH k H) as [H1 H2]. split; [exact H1 | lia].
Qed.
Lemma xe_set_nth_length : forall {T : Type} k (x : T) l, length (xe_set_nth k x l) = length l.
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma xe_nth_set_eq : forall {T : Type} k (x d : T) l, (k < length l)%nat -> nth k (xe_set_nth k x l) d = x.
Proof.
  intros T k x d l. revert k. induction l as [|y l IH]; intros [|k] Hk; cbn [length] in Hk; try lia;
    cbn [xe_set_nth nth]; [reflexivity | apply IH; lia].
Qed.
Lemma xe_nth_set_ne : forall {T : Type} k j (x d : T) l, j <> k -> nth j (xe_set_nth k x l) d = nth j l d.
Proof.
  intros T k j x d l. revert k j. induction l as [|y l IH]; intros [|k] [|j] Hjk; cbn [xe_set_nth nth];
    try reflexivity; try lia.
  apply IH. lia.
Qed.
Lemma xe_set_set : forall {T : Type} k (x y : T) l, xe_set_nth k x (xe_set_nth k y l) = xe_set_nth k x l.
Proof.
  intros T k x y l. revert k. induction l as [|z l IH]; intros [|k]; cbn [xe_set_nth]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma xe_in_set : forall {T : Type} k (x o : T) l, In o (xe_set_nth k x l) -> o = x \/ In o l.
Proof.
  intros T k x o l. revert k. induction l as [|y l IH]; intros [|k] H; cbn [xe_set_nth] in H.
  - destruct H.
  - destruct H.
  - destruct H as [<- | H]; [left; reflexivity | right; right; exact H].
  - destruct H as [<- | H]; [right; left; reflexivity|].
    destruct (IH k H) as [E | H']; [left; exact E | right; right; exact H'].
Qed.

(* the live blocks: pairwise distinct, and counted *)
Lemma xe_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma xe_nodup_app : forall {T : Type} (l1 l2 : list T) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros T l1 l2 x. induction l1 as [|y l1 IH]; intros Hn H1 H2; [destruct H1|].
  cbn [app] in Hn. apply NoDup_cons_iff in Hn as [Hy Hn'].
  destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH Hn' H1 H2)].
Qed.
Definition xe_eqd : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma xe_cnt_cons : forall (b : Z * Z) l z,
  count_occ xe_eqd (b :: l) z = ((if xe_eqd b z then 1 else 0) + count_occ xe_eqd l z)%nat.
Proof. intros b l z. cbn [count_occ]. destruct (xe_eqd b z); lia. Qed.
Ltac xe_cnt_in H := repeat (rewrite count_occ_app in H || rewrite xe_cnt_cons in H).
Ltac xe_cnt_goal := repeat (rewrite count_occ_app || rewrite xe_cnt_cons).
Lemma xe_concat_set : forall k (hs : list (option hsrc)) o, nth_error hs k = Some o ->
  Permutation (concat (map slot_blks hs)) (slot_blks o ++ concat (map slot_blks (xe_set_nth k None hs))).
Proof.
  intros k hs. revert k. induction hs as [|y hs IH]; intros [|k] o H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [xe_set_nth map concat slot_blks app]. apply Permutation_refl.
  - cbn [xe_set_nth map concat]. specialize (IH k o H).
    apply (Permutation_count_occ xe_eqd). intros z.
    pose proof (proj1 (Permutation_count_occ xe_eqd _ _) IH z) as E.
    xe_cnt_in E. xe_cnt_goal. lia.
Qed.
(* slot k's blocks but its held list, and the blocks the call neither frees nor rewrites *)
Definition xe_skh (h : hsrc) : list (Z * Z) :=
  (hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h).
Definition xe_BL (cx : lfcx) (m : lmod) (k : nat) : list (Z * Z) :=
  input_blks cx ++ (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
  concat (map slot_blks (xe_set_nth k None (lm_hs m))) ++ aout_blks (lm_cap m) (lm_out m).
Lemma xe_mblks_split : forall cx m k h R, nth k (lm_hs m) None = Some h ->
  Permutation (input_blks cx ++ model_blks m ++ R) (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R).
Proof.
  intros cx m k h R Hk. destruct (xe_nth_some k (lm_hs m) h Hk) as [He _].
  pose proof (xe_concat_set k (lm_hs m) (Some h) He) as HC. cbn [slot_blks] in HC. unfold asrc_blks in HC.
  unfold model_blks, xe_BL, xe_skh.
  apply (Permutation_count_occ xe_eqd). intros z.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) HC z) as Hz. clear HC.
  xe_cnt_in Hz. xe_cnt_goal. lia.
Qed.
Lemma xe_perm_comb : forall (L L' AH AH' D Y BL R : list (Z * Z)),
  Permutation L (AH ++ Y ++ BL ++ R) -> Permutation L' (AH' ++ Y ++ BL ++ R) -> Permutation AH (D ++ AH') ->
  Permutation L (D ++ L').
Proof.
  intros L L' AH AH' D Y BL R H1 H2 H3.
  apply (Permutation_count_occ xe_eqd). intros z.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H1 z) as E1.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H2 z) as E2.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H3 z) as E3.
  xe_cnt_in E1. xe_cnt_in E2. xe_cnt_in E3. xe_cnt_goal. lia.
Qed.
Lemma xe_held_in_model : forall m k h, nth k (lm_hs m) None = Some h ->
  forall b, In b (alist_blks (hs_held h)) -> In b (model_blks m).
Proof.
  intros m k h Hh b Hb. destruct (xe_nth_some k (lm_hs m) h Hh) as [He _].
  unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
  apply in_concat. exists (slot_blks (Some h)). split; [apply in_map; eapply nth_error_In; exact He|].
  cbn [slot_blks]. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xe_held_pos : forall l q n, In (q, n) (alist_blks l) -> n <> 0.
Proof.
  intros l q n Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [destruct Hb|].
    destruct Hb as [E | []]. injection E as _ E2. subst n. unfold AREC. lia.
  - apply in_map_iff in Hb as (r & E & _). injection E as _ E2. subst n. lia.
Qed.
Lemma xe_model_sub : forall m k h H' ev, nth k (lm_hs m) None = Some h ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) -> hl_recs H' = [] ->
  forall b, In b (model_blks (xe_set_slot m k (Some (CheckRep.set_held h H')) ev)) -> In b (model_blks m).
Proof.
  intros m k h H' ev Hh Hv Hcap Hrecs b Hb. destruct (xe_nth_some k (lm_hs m) h Hh) as [He _].
  unfold model_blks, xe_set_slot in Hb |- *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
  destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
  apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_or_app; right; exact Hb]. apply in_or_app. left.
  apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (o & <- & Ho).
  apply in_concat. destruct (xe_in_set k _ o _ Ho) as [-> | Ho'].
  - exists (slot_blks (Some h)). split; [apply in_map; eapply nth_error_In; exact He|].
    cbn [slot_blks] in Hb |- *. unfold asrc_blks in Hb |- *.
    cbn [CheckRep.set_held hs_partial hs_pending hs_expected hs_held] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity | right].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
    unfold alist_blks in Hb |- *. rewrite Hv, Hcap, Hrecs in Hb. cbn [map] in Hb. rewrite app_nil_r in Hb.
    apply in_or_app. left. exact Hb.
  - exists (slot_blks o). split; [apply in_map; exact Ho' | exact Hb].
Qed.
Lemma xe_BL_cover : forall cx m k b, length (lm_hs m) = 4%nat ->
  ((exists i, (i < 4)%nat /\ i <> k /\ In b (slot_blks (nth i (lm_hs m) None))) \/
   In b (arelay_blks (lm_G m) (lm_es m)) \/ In b (aout_blks (lm_cap m) (lm_out m))) ->
  In b (xe_BL cx m k).
Proof.
  intros cx m k b Hl Hb. unfold xe_BL. apply in_or_app. right.
  destruct Hb as [(i & Hi & Hik & Hb) | [Hb | Hb]].
  - right. apply in_or_app. right. apply in_or_app. left.
    apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
    apply in_map. rewrite <- (xe_nth_set_ne k i None None (lm_hs m) Hik). apply nth_In.
    rewrite xe_set_nth_length. lia.
  - unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
    right. apply in_or_app. left. exact Hb.
  - right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

(* the blocks each representation predicate names are live *)
Lemma xe_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - rewrite Forall_forall in H9. apply in_map_iff in Hb as (r & <- & Hr). exact (proj1 (H9 r Hr)).
Qed.
Lemma xe_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h HS b Hb.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
                    Hexp & Hheld & _).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xe_alist_blks _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (xe_alist_blks _ _ _ _ _ _ _ Hexp b Hb) | exact (xe_alist_blks _ _ _ _ _ _ _ Hheld b Hb)].
Qed.
Lemma xe_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + rewrite Forall_forall in K15. apply in_map_iff in Hb as (kk & <- & Hk). exact (proj1 (K15 kk Hk)).
Qed.
Lemma xe_arelay_blks : forall RG ly S (W : world segs) mem G es,
  arelay_at B RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact R8|].
  apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
  rewrite Forall_forall in R10. exact (xe_aentry_blks _ _ _ _ _ (R10 e He) b Hb).
Qed.
Lemma xe_aout_blks : forall RG ly S (W : world segs) mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem c O mx no cap out HO b Hb.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & _ & Hblk).
  unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
  destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* the footprint of each predicate is kept when its own cells and its blocks are *)
Lemma xe_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma xe_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, xe_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma xe_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
Lemma xe_alist_ak : forall ly S (W : world segs) mem (W' : world segs) mem' LA l lines,
  alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (alist_blks l) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (alist_fp LA l).
Proof.
  intros ly S W mem W' mem' LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HS HB r Hr a Ha.
  unfold xe_bk in HB. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; apply HS; lia|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|]. destruct Hr as [<- | []].
    cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, length_app, xe_concat_len in Ha.
    apply (HB (hl_v l, AREC * hl_cap l)).
    + unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (AREC * hl_cap l) 0); unfold hl_n, AREC in *; lia.
  - apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (HB (fst x, Z.of_nat (length (snd x)) + 1)).
    + unfold alist_blks. apply in_or_app. right. apply in_map_iff. exists x. split; [reflexivity | exact Hx].
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (snd x)) + 1) 0); lia.
Qed.
Lemma xe_asrc_ak : forall ly S (W : world segs) mem (W' : world segs) mem' HA h,
  asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (asrc_blks h) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (asrc_fp HA h).
Proof.
  intros ly S W mem W' mem' HA h HS HK HB.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
                    Hexp & Hheld & _).
  intros r Hr a Ha. unfold asrc_fp in Hr.
  destruct Hr as [<- | [<- | Hr]].
  - apply HK. cbn [fst snd] in Ha. exact Ha.
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
    apply (HB (hs_partial h, APARTIAL)); [unfold asrc_blks; left; reflexivity|].
    cbn [fst snd]. change (req_size APARTIAL) with APARTIAL. exact Ha.
  - apply in_app_or in Hr as [Hr | Hr].
    + refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hpend _ _ r Hr a Ha).
      * intros x Hx. apply HK. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. left. exact Hb.
    + apply in_app_or in Hr as [Hr | Hr].
      * refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hexp _ _ r Hr a Ha).
        -- intros x Hx. apply HK. unfold ASRC. lia.
        -- intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
      * refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hheld _ _ r Hr a Ha).
        -- intros x Hx. apply HK. unfold ASRC. lia.
        -- intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xe_aentry_ak : forall ly S (W : world segs) mem (W' : world segs) mem' e,
  aentry_ok B ly S W mem e ->
  (forall b, In b (aentry_blks e) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (aentry_fp e).
Proof.
  intros ly S W mem W' mem' e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15)
    HB r Hr a Ha.
  unfold xe_bk in HB. unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|]. destruct Hr as [<- | []].
    cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, length_app in Ha.
    apply (HB (re_buf e, re_cap e)).
    + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (re_cap e) 0); lia.
  - destruct Hr as [<- | Hr].
    + cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, xe_key_ptrs_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hks in Ha. cbn [length] in Ha. lia.
      * apply (HB (re_hp e, re_kh e)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
           rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- cbn [fst snd]. unfold req_size. unfold re_nheld in Hk1. destruct (Z.eqb_spec (re_kh e) 0); lia.
    + apply in_map_iff in Hr as (kk & <- & Hk). cbn [gfp fst snd] in Ha. unfold bzs in Ha.
      rewrite length_map, length_app in Ha. cbn [length] in Ha.
      eapply HB.
      * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists kk. split; [reflexivity | exact Hk].
      * cbn [fst snd]. unfold req_size. match goal with |- context [?n =? 0] => destruct (Z.eqb_spec n 0) end; lia.
Qed.
Lemma xe_arelay_ak : forall RG ly S (W : world segs) mem (W' : world segs) mem' G es,
  arelay_at B RG ly S W mem G es ->
  (forall a, (rg_src RG <= a < rg_src RG + 8) \/ (rg_nsrc RG <= a < rg_nsrc RG + 4) \/
     (rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (arelay_blks G es) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (arelay_fp RG G es).
Proof.
  intros RG ly S W mem W' mem' G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HGl HB r Hr a Ha.
  unfold arelay_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  - apply HGl. left. exact Ha.
  - apply HGl. right. left. exact Ha.
  - apply HGl. right. right. exact Ha.
  - unfold xe_bk in HB. apply (HB (G, ATABLE)); [unfold arelay_blks; left; reflexivity|].
    cbn [fst snd]. change (req_size ATABLE) with ATABLE. exact Ha.
  - apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    rewrite Forall_forall in R10.
    refine (xe_aentry_ak _ _ _ _ _ _ e (R10 e He) _ r Hr a Ha).
    intros b Hb. apply HB. unfold arelay_blks. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hb].
Qed.
(* the stream, with errno floated to the value it has after the call *)
Lemma xe_aout_tr : forall RG ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out ev,
  aout_at B RG ly S W mem c O mx no cap out ->
  (forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8) \/
     (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) \/
     (rg_client RG <= a < rg_client RG + 4) \/ (rg_client_broken RG <= a < rg_client_broken RG + 1) \/
     (rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  aout_at B RG ly' S' W' mem' (lx_ctl_ev c ev) O mx no cap out.
Proof.
  intros RG ly S W mem ly' S' W' mem' c O mx no cap out ev
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB Hev Hevw Hevb.
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 0%nat | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 0%nat | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 1%nat | exact H3]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 1%nat | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 2%nat | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 2%nat | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 3%nat | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 3%nat | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 4%nat | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 4%nat | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 5%nat | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 5%nat | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 6%nat | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 6%nat | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 7%nat | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 7%nat | exact H16]|].
  split; [exact Hev|]. split; [exact Hevw|]. split; [exact Hevb|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (HB (out, cap) ltac:(unfold aout_blks; rewrite Ec; left; reflexivity)) as [Hin' Hbk].
  unfold xe_bk in Hbk. cbn [fst snd] in Hbk.
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin'|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply Hbk. unfold req_size. destruct (Z.eqb_spec cap 0); lia.
Qed.
(* the model, its slot kx given at the new state, errno at its new value, everything else kept *)
Lemma xe_amodel_tr : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' m (kx : nat) hs' ev,
  amodel_at B ly S W mem m ->
  length hs' = 4%nat ->
  ((kx < 4)%nat -> aslot B ly' S' W' mem' kx (nth kx hs' None)) ->
  (forall i, (i < 4)%nat -> i <> kx -> nth i hs' None = nth i (lm_hs m) None) ->
  (forall i, (i < 4)%nat -> i <> kx -> forall a, xe_HA i <= a < xe_HA i + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall b, ((exists i, (i < 4)%nat /\ i <> kx /\ In b (slot_blks (nth i (lm_hs m) None))) \/
              In b (arelay_blks (lm_G m) (lm_es m)) \/ In b (aout_blks (lm_cap m) (lm_out m))) ->
     In b (ablocks B ly S) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b) ->
  (forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_at B ly' S' W' mem' (LM (lm_k m) hs' (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m) (lm_mx m)
    (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m)).
Proof.
  intros ly S W mem ly' S' W' mem' m kx hs' ev (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13)
    Hlen HP HnP HS HB HGl Hev Hevw Hevb.
  assert (KG : forall lo n a, In (lo, n) XE_GLOBS -> lo <= a < lo + n -> abyte_kept W mem W' mem' a)
    by (intros lo n a Hin Ha; apply HGl; exact (xe_inG_of _ lo n a Hin Ha)).
  unfold amodel_at. cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact Hlen|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i kx) as [-> | Hne]; [exact (HP Hi)|].
    rewrite (HnP i Hi Hne). specialize (M2 i Hi). unfold aslot in M2 |- *.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ei.
    - assert (HBi : forall b, In b (asrc_blks hi) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b).
      { intros b Hb. apply HB; [left; exists i; rewrite Ei; split; [exact Hi | split; [exact Hne | exact Hb]]|].
        exact (xe_asrc_blks _ _ _ _ _ _ M2 b Hb). }
      apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ hi M2).
      + apply (xe_asrc_ak ly S W mem W' mem' _ hi M2); [|intros b Hb; exact (proj2 (HBi b Hb))].
        intros a Ha. apply (HS i Hi Hne). unfold xe_HA. exact Ha.
      + intros b Hb. exact (proj1 (HBi b Hb)).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (HS i Hi Hne). unfold xe_HA, ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply (HS i Hi Hne). unfold xe_HA. exact Hx. }
  split.
  { assert (HBr : forall b, In b (arelay_blks (lm_G m) (lm_es m)) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b)
      by (intros b Hb; exact (HB b (or_intror (or_introl Hb)) (xe_arelay_blks _ _ _ _ _ _ _ M3 b Hb))).
    apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ M3).
    - apply (xe_arelay_ak fr_RG ly S W mem W' mem' _ _ M3); [|intros b Hb; exact (proj2 (HBr b Hb))].
      intros a [Ha | [Ha | Ha]].
      + apply (KG (rg_src fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_nsrc fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_capsrc fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
    - intros b Hb. exact (proj1 (HBr b Hb)). }
  split.
  { apply (xe_aout_tr fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ ev M4).
    - intros a Ha.
      destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]].
      + apply (KG (rg_send_max fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_nout fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_capout fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_out fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_client fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_client_broken fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_send_dead fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_send_eintr fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
    - intros b Hb. exact (HB b (or_intror (or_intror Hb)) (xe_aout_blks _ _ _ _ _ _ _ _ _ _ _ M4 b Hb)).
    - exact Hev.
    - exact Hevw.
    - exact Hevb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_gone fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_lock fr_RG) 12 a); [unfold XE_GLOBS; xe_in | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_wake fr_RG + 4) 4 a); [unfold XE_GLOBS; xe_in | lia]. }
  split; [apply (akept_vm W mem); [intros x Hx; apply (KG AG_NFD 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M8]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (KG AG_NFD 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M9]|].
  split; [exact M10|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KG AG_THREAD_UP 1 x); [unfold XE_GLOBS; xe_in | lia]
    | exact M11]|].
  destruct M12 as (lst & M12).
  split; [exists lst; apply (akept_vm W mem); [intros x Hx; apply (KG AG_LISTEN 4 x); [unfold XE_GLOBS; xe_in | lia]
    | exact M12]|].
  apply (akept_awr W mem); [intros x Hx; apply (KG AG_LISTEN 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M13].
Qed.
(* the frame and the fake frame, read by view, written by presence.  B: bx_frame, none of whose cells is in
   [F+144, F+160) (the two cells the entry writes) or [F+208, F+216) (`at`) *)
Lemma xe_bxframe_tr : forall cx FF (W : world segs) mem (W' : world segs) mem',
  bx_frame cx FF W mem ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
     ~ (lf_F cx + AX_AT <= a < lf_F cx + AX_AT + 8) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  awr W' mem' (lf_F cx) (spZ (c_regs cx) - lf_F cx) ->
  (forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  awr W' mem' FF 128 -> awr W' mem' (SB + FF / 8) 16 ->
  bx_frame cx FF W' mem'.
Proof.
  intros cx FF W mem W' mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 &
    A16 & A17 & A18 & A19 & A20 & A21) Hsp HV HW HFV HFW HSW.
  unfold sv8 in *. unfold bx_frame, sv8. cbv zeta.
  assert (KC : forall o v, 0 <= o -> o + 8 <= AX_GS8 \/ AX_GS8 + 16 <= o -> o + 8 <= AX_AT ->
      val_mem segs (arm W mem) (lf_F cx + o) 8 v -> val_mem segs (arm W' mem') (lf_F cx + o) 8 v).
  { intros o v H0 H1 H2 Hv. apply (xe_vm_view W W' mem mem'); [|exact Hv].
    intros x Hx. apply HV; unfold AX_GS8, AX_AT in *; lia. }
  split.
  { intros o r Hin. apply (xe_vm_view W W' mem mem'); [|exact (A1 o r Hin)]. intros x Hx.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    apply HV; unfold AX_GS8, AX_AT in *; lia. }
  split; [exact HW|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A3]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A4]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A5]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A6]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A7]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A8]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A9]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A10]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A11]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A12]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A13]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A14]|].
  split; [apply KC; [lia | unfold AX_GS8; lia | unfold AX_AT; lia | exact A15]|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A16]|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A17]|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A18]|].
  split; [exact HFW|].
  split; [|exact HSW].
  apply (xe_garr8_view W W' mem mem'); [|exact A20].
  intros x Hx. apply HFV. right. unfold fake_shadow in Hx. cbn [length] in Hx. lia.
Qed.
Lemma xe_ainput_tr : forall cx ly S (W : world segs) mem ly' S' (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S') /\ xe_bk W mem W' mem' (c_p cx, c_n cx)) ->
  ainput_at B cx ly' S' W' mem'.
Proof.
  intros cx ly S W mem ly' S' W' mem' (I1 & I2) Hlen HB.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)].
  - split; [left; split; assumption|]. apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map, Hlen, Hn in Hx. lia.
  - destruct (HB ltac:(lia)) as [Hin' Hbk]. split; [right; split; [exact Hn | exact Hin']|].
    apply (akept_garr8 W mem); [|exact I2]. intros x Hx. rewrite length_map, Hlen in Hx.
    apply Hbk. cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
Qed.
Lemma xe_jt_tr : forall (W : world segs) mem (W' : world segs) mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W mem W' mem' HR HR' HJ i Hi. apply (xe_vm_view W W' mem mem'); [|exact (HJ i Hi)].
  intros x Hx. pose proof (XRF_JTAB_ROM x ltac:(lia)) as Hr. rewrite (HR x Hr), (HR' x Hr). reflexivity.
Qed.

(* the cut's facts across the entry run's two stores (norder into F+152, SB + g_s / 8 into F+144), the shape of
   W_LLVMFuzzerTestOneInput_drain.v de_carry; the entry's aframe_at is weakened to bx_frame first *)
Lemma xe_carry : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem' /\
  (forall a n v, lf_F cx + AX_ORDER <= a -> a + Z.of_nat n <= lf_F cx + AX_AT + 8 ->
     val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hin1 Hlen Hsp HFA HMOD HIN HRV HJT HV HPR.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by lia.
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HWK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
    by (intros a Hw; exact (writable_kept (w_H W) mem mem' a (HPR a) Hw)).
  assert (KL : forall a, 0 <= a < alloc_ceiling -> abyte_kept W mem W mem' a).
  { intros a Ha. split; [apply HV; unfold AX_GS8; lia | exact (HWK a)]. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly3 1 fpos) ltac:(lia)) as HFF8.
  assert (HEL : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd).
  { assert (Hg0 : inG G_fr (as_errno B))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    assert (Hg3 : inG G_fr (as_errno B + 3))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    pose proof (Hsl _ (proj1 (HG _ Hg0))). pose proof (Hsl _ (proj1 (HG _ Hg3))). lia. }
  split.
  { pose proof HFA as (_ & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A19 & _ & A21).
    apply (xe_bxframe_tr cx _ W mem W mem' HFA HFhi).
    - intros a Ha Hn _. apply HV; [lia | exact Hn].
    - intros i Hi. exact (HWK _ (A2 i Hi)).
    - intros a Ha. unfold SB in Ha. apply HV; [lia | unfold AX_GS8; lia].
    - intros i Hi. exact (HWK _ (A19 i Hi)).
    - intros i Hi. exact (HWK _ (A21 i Hi)). }
  split.
  { destruct m as [mk mhs mG mes [cl br dd ei ev0] mO mmx mcap mout mgn mnfd].
    pose proof HMOD as (M1 & _ & _ & M4 & _).
    pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hevw & Hevb & _).
    refine (xe_amodel_tr ly3 S3 W mem ly3 S3 W mem' _ 4 mhs ev0 HMOD M1 _ _ _ _ _ _ _ _).
    - intros H4. lia.
    - intros i _ _. reflexivity.
    - intros i Hi _ a Ha. apply KL. unfold xe_HA, ASRC in Ha. cbn [fr_RG fr_globals_b rg_s] in Ha. lia.
    - intros b _ Hb. split; [exact Hb|]. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      destruct (al_blocks _ _ LAWS ly3 S3 W mem md p n HAR Hb) as (_ & H4096 & Hce & _). apply KL. lia.
    - intros a Ha. apply KL. destruct (xe_globs_rng a Ha) as [H1 _]. cbn [fr_RG fr_globals_b rg_out] in H1. lia.
    - apply (akept_vm W mem); [intros x Hx; apply KL; lia | exact Hev].
    - apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact Hevw].
    - exact Hevb. }
  split.
  { apply (xe_ainput_tr cx ly3 S3 W mem ly3 S3 W mem' HIN Hlen). intros Hn.
    destruct HIN as [[(Hn0 & _) | (Hn0 & Hinb)] _]; [lia|]. split; [exact Hinb|].
    intros a Ha. cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS ly3 S3 W mem md _ _ HAR Hinb) as (_ & H4096 & Hce & _). apply KL. lia. }
  assert (HRV' : rom_view segs W mem').
  { intros a Ha. rewrite <- (HRV a Ha).
    assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
    pose proof (Hsl a Hin). exact (proj1 (KL a ltac:(lia))). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W mem' HRV HRV' HJT)|].
  intros a n v H1 H2 Hv. apply (xe_vm_view W W mem mem'); [|exact Hv].
  intros x Hx. apply HV; unfold AX_ORDER, AX_AT, AX_GS8 in *; lia.
Qed.
(* ---- the model's remaining work at (i, k): scan the slots from k on with order[i], then the outer trips
   left.  xe_fin at (0, 0) is lx_ends_run, and at (i, 4) it is the next trip's. ---- *)
Definition xe_fin (gone : Z) (ob : list byte) (ord : Z -> Z) (norder i : Z) (k : nat) (A : Z)
    (sl : list lx_ends_rslot) : option Z :=
  match lx_ends_scan gone ob (ord i) A (skipn k sl) with
  | None => None
  | Some (sfx, A1) =>
      match lx_ends_outer gone ob ord (Z.to_nat (norder - (i + 1))) (i + 1) A1 (firstn k sl ++ sfx) with
      | Some (_, afin) => Some afin
      | None => None
      end
  end.

(* ============================================================ the pure model lemmas of the block ==========
   No journal, no walk: the empty prefix, CheckRep.ends_run's bookkeeping, the scan / outer / xe_fin steps, and
   the meter of a slot update. *)
Lemma xm_prefixb_nil : forall x, CheckRep.prefixb [] x = true.
Proof. intros x. reflexivity. Qed.

Lemma xm_want_nil : forall rs, CheckRep.want_of [] rs = length rs.
Proof.
  (* want_of counts with stdpp's filter; its empty-prefix test is true by computation *)
  intros rs. unfold CheckRep.want_of. induction rs as [|r rs IH]; [reflexivity|].
  exact (f_equal S IH).
Qed.

Lemma xm_filter_nil_t : forall (rs : list (Z * list byte)), filter (fun r => CheckRep.prefixb [] (snd r)) rs = rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  exact (f_equal (cons r) IH).
Qed.

Lemma xm_filter_nil_f : forall (rs : list (Z * list byte)), filter (fun r => negb (CheckRep.prefixb [] (snd r))) rs = [].
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  exact IH.
Qed.

(* find_text returns an index of the list *)
Lemma xm_find_text_lt : forall y rs i, CheckRep.find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [CheckRep.find_text] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H.
  - injection H as <-. cbn [length]. lia.
  - destruct (CheckRep.find_text y rs) as [j|] eqn:E; cbn [option_map] in H; [|discriminate].
    injection H as <-. specialize (IH j eq_refl). cbn [length]. lia.
Qed.

(* split_nul cuts d into a line, its NUL, and the rest *)
Lemma xm_split_nul_len : forall d l d', CheckRep.split_nul d = Some (l, d') ->
  (length l + 1 + length d' = length d)%nat.
Proof.
  induction d as [|b d IH]; intros l d' H; cbn [CheckRep.split_nul] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H.
  - injection H as E1 E2. subst l d'. cbn [length]. lia.
  - destruct (CheckRep.split_nul d) as [[l1 r1]|] eqn:E; cbv beta iota in H; [|discriminate].
    injection H as E1 E2. subst l d'. pose proof (IH _ _ eq_refl) as X. cbn [length]. lia.
Qed.

(* the record ends_run takes out, put in front *)
Lemma xm_perm_nth : forall i (rs : list (Z * list byte)) d0, (i < length rs)%nat ->
  Permutation rs (nth i rs d0 :: CheckRep.drop_nth i rs).
Proof.
  unfold CheckRep.drop_nth.
  induction i as [|i IH]; intros [|r rs] d0 H; cbn [length] in H; try lia.
  - cbn [nth firstn skipn app]. apply Permutation_refl.
  - cbn [nth firstn skipn app].
    eapply perm_trans; [apply perm_skip, (IH rs d0); lia|].
    apply perm_swap.
Qed.

(* one step of ends_run drops one record and consumes one NUL-terminated line of d *)
Lemma xm_ends_run : forall P rs d w rs' ds c, CheckRep.ends_run P rs d w = Some (rs', ds, c) ->
  Permutation rs (ds ++ rs') /\ length ds = w /\ 0 <= c <= Z.of_nat (length d).
Proof.
  intros P rs d w. revert rs d. induction w as [|w IH]; intros rs d rs' ds c H; cbn [CheckRep.ends_run] in H.
  - injection H as E1 E2 E3. subst rs' ds c. cbn [app length].
    split; [apply Permutation_refl|]. split; [reflexivity|]. lia.
  - destruct (CheckRep.split_nul d) as [[l d1]|] eqn:Hs; cbv beta iota zeta in H; [|discriminate].
    match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H; [|discriminate].
    match type of H with context [CheckRep.find_text ?y rs] =>
      destruct (CheckRep.find_text y rs) as [i|] eqn:Hf end; cbv beta iota in H; [|discriminate].
    destruct (CheckRep.ends_run P (CheckRep.drop_nth i rs) d1 w) as [[[rs1 ds1] c1]|] eqn:He;
      cbv beta iota in H; [|discriminate].
    injection H as E1 E2 E3. subst rs' ds c.
    destruct (IH _ _ _ _ _ He) as (HP & HL & HC).
    pose proof (xm_find_text_lt _ _ _ Hf) as Hi.
    pose proof (xm_split_nul_len _ _ _ Hs) as HS.
    split; [|split].
    + eapply perm_trans; [exact (xm_perm_nth i rs (0, []) Hi)|].
      cbn [app]. apply perm_skip. exact HP.
    + cbn [length]. rewrite HL. reflexivity.
    + lia.
Qed.

Lemma xm_c1 : forall gone ob recs A recs' A1, lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  recs' = [] /\ A <= A1 <= A + Z.of_nat (length (skipn (Z.to_nat A) ob)).
Proof.
  intros gone ob recs A recs' A1 H. unfold lx_ends_c1 in H.
  destruct (gone =? 0).
  - destruct (CheckRep.ends_run [] recs (skipn (Z.to_nat A) ob) (CheckRep.want_of [] recs))
      as [[[r ds] c]|] eqn:E; cbv beta iota in H; [|discriminate].
    injection H as E1 E2. subst r A1.
    destruct (xm_ends_run _ _ _ _ _ _ _ E) as (HP & HL & HC).
    rewrite xm_want_nil in HL.
    apply Permutation_length in HP. rewrite length_app, HL in HP.
    split; [|lia].
    destruct recs' as [|x l]; [reflexivity|]. cbn [length] in HP. lia.
  - injection H as E1 E2. subst recs' A1. split; [apply xm_filter_nil_f|]. lia.
Qed.

(* the records the call drops, as the blocks side needs them *)
Lemma xm_c1_ds : forall gone ob recs A recs' A1, lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  (gone <> 0 -> Permutation recs (filter (fun r => CheckRep.prefixb [] (snd r)) recs)) /\
  (gone = 0 -> forall ds c, CheckRep.ends_run [] recs (skipn (Z.to_nat A) ob) (CheckRep.want_of [] recs) = Some (recs', ds, c) ->
     Permutation recs ds).
Proof.
  intros gone ob recs A recs' A1 H. split.
  - intros _. rewrite xm_filter_nil_t. apply Permutation_refl.
  - intros _ ds c E.
    destruct (xm_c1 _ _ _ _ _ _ H) as (-> & _).
    destruct (xm_ends_run _ _ _ _ _ _ _ E) as (HP & _). rewrite app_nil_r in HP. exact HP.
Qed.

Lemma xm_scan_app : forall gone ob oi A l1 l2,
  lx_ends_scan gone ob oi A (l1 ++ l2) =
  match lx_ends_scan gone ob oi A l1 with
  | Some (l1', A1) => match lx_ends_scan gone ob oi A1 l2 with
                      | Some (l2', A2) => Some (l1' ++ l2', A2) | None => None end
  | None => None end.
Proof.
  intros gone ob oi A l1 l2. revert A. induction l1 as [|o l1 IH]; intros A.
  - cbn [app lx_ends_scan]. destruct (lx_ends_scan gone ob oi A l2) as [[l2' A2]|]; reflexivity.
  - destruct o as [[fd recs]|]; cbn [app lx_ends_scan].
    + destruct (fd =? oi); cbv beta iota.
      * destruct (lx_ends_c1 gone ob recs A) as [[recs' A1]|]; cbv beta iota; [|reflexivity].
        rewrite IH. destruct (lx_ends_scan gone ob oi A1 l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
        destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
      * rewrite IH. destruct (lx_ends_scan gone ob oi A l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
        destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
    + rewrite IH. destruct (lx_ends_scan gone ob oi A l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
      destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
Qed.

(* xe_set_nth commutes with map *)
Lemma xm_set_nth_map : forall {T U : Type} (f : T -> U) k x (l : list T),
  map f (xe_set_nth k x l) = xe_set_nth k (f x) (map f l).
Proof.
  intros T U f k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma xm_slot0_set : forall k (hs : list (option hsrc)) (h' : hsrc),
  map lx_ends_slot0 (xe_set_nth k (Some h') hs) = xe_set_nth k (lx_ends_slot0 (Some h')) (map lx_ends_slot0 hs).
Proof. intros k hs h'. apply xm_set_nth_map. Qed.

Lemma xm_cost_set : forall k (hs : list (option hsrc)) h H', (k < length hs)%nat -> nth k hs None = Some h ->
  hl_recs H' = [] ->
  lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) hs) = lx_ends_cost hs - hl_n (hs_held h) * mo_free MT.
Proof.
  intros k hs h H' _ Hn HR. revert k Hn. induction hs as [|o hs IH]; intros [|k] Hn; cbn [nth] in Hn.
  - discriminate.
  - discriminate.
  - subst o. cbn [xe_set_nth lx_ends_cost CheckRep.set_held hs_held].
    assert (E : hl_n H' = 0) by (unfold hl_n; rewrite HR; reflexivity). rewrite E. ring.
  - destruct o as [h0|]; cbn [xe_set_nth lx_ends_cost]; rewrite (IH k Hn); ring.
Qed.

(* the slot k of a list, and the cut at it *)
Lemma xm_skipn_nth : forall {T : Type} (l : list T) k s, nth_error l k = Some s ->
  skipn k l = s :: skipn (S k) l /\ firstn (S k) l = firstn k l ++ [s].
Proof.
  intros T l. induction l as [|y l IH]; intros [|k] s H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [skipn firstn app]. split; reflexivity.
  - destruct (IH k s H) as [E1 E2]. cbn [skipn firstn app]. rewrite E2. split; [exact E1|reflexivity].
Qed.

Lemma xm_set_nth_skipn : forall {T : Type} k (x : T) l, skipn (S k) (xe_set_nth k x l) = skipn (S k) l.
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth skipn]; try reflexivity.
  apply IH.
Qed.

Lemma xm_set_nth_firstn : forall {T : Type} k (x : T) l, (k < length l)%nat ->
  firstn (S k) (xe_set_nth k x l) = firstn k l ++ [x].
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k] Hk; cbn [length] in Hk; try lia;
    cbn [xe_set_nth firstn app]; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.

(* the four steps of xe_fin the loop takes *)
Lemma xm_fin_skip : forall gone ob ord norder i (k : nat) A sl s,
  nth_error sl k = Some s -> (s = None \/ (exists fd recs, s = Some (fd, recs) /\ fd <> ord i)) ->
  xe_fin gone ob ord norder i k A sl = xe_fin gone ob ord norder i (S k) A sl.
Proof.
  intros gone ob ord norder i k A sl s Hs Hc. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  destruct (xm_skipn_nth sl k s Hs) as [E1 E2]. rewrite E1, E2.
  assert (ES : lx_ends_scan gone ob (ord i) A (s :: skipn (S k) sl) =
    match lx_ends_scan gone ob (ord i) A (skipn (S k) sl) with
    | Some (sfx, A1) => Some (s :: sfx, A1) | None => None end).
  { destruct Hc as [->|(fd & recs & -> & Hne)]; cbn [lx_ends_scan].
    - reflexivity.
    - rewrite (proj2 (Z.eqb_neq fd (ord i)) Hne). reflexivity. }
  rewrite ES. destruct (lx_ends_scan gone ob (ord i) A (skipn (S k) sl)) as [[sfx A1]|]; cbv beta iota;
    [|reflexivity].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma xm_fin_call : forall gone ob ord norder i (k : nat) A sl fd recs recs' A1,
  nth_error sl k = Some (Some (fd, recs)) -> fd = ord i ->
  lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  xe_fin gone ob ord norder i k A sl = xe_fin gone ob ord norder i (S k) A1 (xe_set_nth k (Some (fd, recs')) sl).
Proof.
  intros gone ob ord norder i k A sl fd recs recs' A1 Hs Hfd Hc. subst fd. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (Hk : (k < length sl)%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
  destruct (xm_skipn_nth sl k _ Hs) as [E1 _].
  rewrite E1, xm_set_nth_skipn, (xm_set_nth_firstn k _ sl Hk).
  cbn [lx_ends_scan]. rewrite Z.eqb_refl. cbv beta iota. rewrite Hc. cbv beta iota.
  destruct (lx_ends_scan gone ob (ord i) A1 (skipn (S k) sl)) as [[sfx A2]|]; cbv beta iota; [|reflexivity].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma xm_fin_next : forall gone ob ord norder i A sl, length sl = 4%nat -> 0 <= i -> i + 1 < norder ->
  xe_fin gone ob ord norder i 4 A sl = xe_fin gone ob ord norder (i + 1) 0 A sl.
Proof.
  intros gone ob ord norder i A sl Hl Hi Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (E1 : skipn 4 sl = []) by (apply skipn_all2; lia).
  assert (E2 : firstn 4 sl = sl) by (apply firstn_all2; lia).
  rewrite E1, E2. cbn [lx_ends_scan skipn firstn app]. rewrite app_nil_r.
  replace (Z.to_nat (norder - (i + 1))) with (S (Z.to_nat (norder - (i + 1 + 1)))) by lia.
  cbn [lx_ends_outer].
  (* stdpp marks skipn simpl-nomatch on a variable list *)
  change (skipn 0 sl) with sl.
  destruct (lx_ends_scan gone ob (ord (i + 1)) A sl) as [[sfx A1]|]; reflexivity.
Qed.

Lemma xm_fin_done : forall gone ob ord norder i A sl, length sl = 4%nat -> i + 1 = norder ->
  xe_fin gone ob ord norder i 4 A sl = Some A.
Proof.
  intros gone ob ord norder i A sl Hl Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (E1 : skipn 4 sl = []) by (apply skipn_all2; lia).
  rewrite E1. cbn [lx_ends_scan]. cbv beta iota.
  replace (Z.to_nat (norder - (i + 1))) with 0%nat by lia.
  cbn [lx_ends_outer]. reflexivity.
Qed.

Lemma xm_fin_start : forall gone ob ord norder A sl, 1 <= norder ->
  xe_fin gone ob ord norder 0 0 A sl =
  match lx_ends_outer gone ob ord (Z.to_nat norder) 0 A sl with Some (_, afin) => Some afin | None => None end.
Proof.
  intros gone ob ord norder A sl Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  replace (Z.to_nat norder) with (S (Z.to_nat (norder - (0 + 1)))) by lia.
  cbn [lx_ends_outer]. change (skipn 0 sl) with sl.
  destruct (lx_ends_scan gone ob (ord 0) A sl) as [[sfx A1]|]; reflexivity.
Qed.

(* a matched slot's call cannot fail when the remaining run succeeds (feeds xe_call's premise) *)
Lemma xm_fin_c1_ne : forall gone ob ord norder i (k : nat) A sl fd recs afin,
  nth_error sl k = Some (Some (fd, recs)) -> fd = ord i ->
  xe_fin gone ob ord norder i k A sl = Some afin -> lx_ends_c1 gone ob recs A <> None.
Proof.
  intros gone ob ord norder i k A sl fd recs afin Hs Hfd Hf Hc. subst fd. unfold xe_fin in Hf.
  try unfold lx_ends_rslot in *.
  destruct (xm_skipn_nth sl k _ Hs) as [E1 _]. rewrite E1 in Hf.
  cbn [lx_ends_scan] in Hf. rewrite Z.eqb_refl, Hc in Hf. cbv beta iota in Hf. discriminate.
Qed.

(* the meter of the slots is never negative *)
Lemma xe_cost_nonneg : forall hs, 0 <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; [cbn; lia|].
  destruct o as [h|]; cbn [lx_ends_cost]; [|exact IH].
  pose proof (mo_free_nonneg MT MLM) as Hf.
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
  nia.
Qed.

(* ---- small facts of the image and of the representation the call site needs ---- *)
(* the "" literal's 8 bytes (the NUL and strlen's word slack) are read-only image bytes: .rodata at 0x20ee0
   (one segment check by vm_compute).  They are NOT all outside the allocator's statics: .str.2's redzone
   (0x20ee1, 0x1f) is in Tfib_owned_static, so check_shape_ends takes them by in_rom, not by a home clause. *)
Lemma xe_lit_rom : forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 -> in_rom segs a.
Proof.
  intros a Ha. apply (xe_romseg_ok (VAL AX_lit_empty) (VAL AX_lit_empty + 8)); [vm_compute; reflexivity | exact Ha].
Qed.
Lemma xe_vals : VAL A_g_gone = rg_gone fr_RG /\ VAL A_g_nout = rg_nout fr_RG /\
  VAL A_g_out = rg_out fr_RG /\ VAL AX_g_s = rg_s fr_RG /\ VAL AX_lit_empty = 0x20ee0.
Proof. vm_compute. repeat split. Qed.
Lemma xe_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. split; [exact H8|]. lia.
Qed.
(* a real-stack range passes every shadow check (W_check_shape_event.v:182 range_addressable_stack) *)
Lemma xe_ra_stack : forall ly S (W : world segs) mem md a len,
  AR segs B ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  intros ly S W mem md a len HAR Hlo Hhi Hlen.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz.
  unfold page_aligned in Hpal, Hpah.
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as DA. pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as DC.
  rewrite Hpal, Z.add_0_r in DA. rewrite Hpah, Z.add_0_r in DC.
  assert (Hm1 : ly_stk_lo ly mod 8 = 0)
    by (rewrite DA; replace (4096 * (ly_stk_lo ly / 4096)) with ((512 * (ly_stk_lo ly / 4096)) * 8) by lia;
        apply Z_mod_mult).
  assert (Hm2 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0).
  { rewrite DA, DC.
    replace (4096 * (ly_stk_hi ly / 4096) - 4096 * (ly_stk_lo ly / 4096))
      with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8) by lia.
    apply Z_mod_mult. }
  eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
(* the stream's bytes, as check_shape_ends reads them, off aout_at's garr8 *)
Lemma xe_ob_of_garr8 : forall (W : world segs) mem OUT (O junk : list byte),
  garr8 segs (arm W mem) OUT (bzs (O ++ junk)) -> ob_at W mem OUT O.
Proof.
  intros W mem OUT O junk Hg i Hi.
  assert (Hj : (Z.to_nat i < length (O ++ junk))%nat) by (rewrite length_app; lia).
  assert (Hjb : (Z.to_nat i < length (bzs (O ++ junk)))%nat) by (unfold bzs; rewrite length_map; exact Hj).
  destruct (Hg (Z.to_nat i) Hjb) as [Hv Hr].
  rewrite Z2Nat.id in Hv by lia.
  rewrite (aview_of_val_mem1 segs (w_H W) mem _ _ Hv Hr). f_equal.
  unfold bzs. rewrite (nth_indep (map bz (O ++ junk)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite List.map_nth. unfold bz. rewrite app_nth1 by lia. reflexivity.
Qed.
(* the literal's first byte is the NUL the prefix ends with, and its 8 bytes are mapped *)
Lemma xe_lit_bytes : forall (W : world segs) mem, rom_view segs W mem ->
  aview segs (w_H W) mem (VAL AX_lit_empty) = Some 0 /\
  (forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 -> aview segs (w_H W) mem a <> None).
Proof.
  intros W mem HRV.
  assert (HPF : VAL AX_lit_empty = 0x20ee0) by (vm_compute; reflexivity).
  assert (HR : forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 ->
    aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))).
  { intros a Ha. apply HRV. exact (xe_lit_rom a Ha). }
  split.
  - assert (Ha0 : VAL AX_lit_empty <= VAL AX_lit_empty < VAL AX_lit_empty + 8) by lia.
    rewrite (HR _ Ha0), HPF. vm_compute. reflexivity.
  - intros a Ha. rewrite (HR a Ha). rewrite HPF in Ha.
    assert (Hc : a = 0x20ee0 \/ a = 0x20ee1 \/ a = 0x20ee2 \/ a = 0x20ee3 \/ a = 0x20ee4 \/ a = 0x20ee5 \/
                 a = 0x20ee6 \/ a = 0x20ee7) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; intros E; discriminate E.
Qed.
(* ---- the model after one call: every clause of xe_inv re-established at the slot check_shape_ends trimmed.
   The views come from xe_keeps_of_journal, the writability of the model's cells from GWR (they are bytes of
   G_fr), of the frame from the journal's presence clause and of the fake frame from AR's al_frames. ---- *)
Lemma xe_model_after : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx segs B (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St W mem md [] ly' St' W' mem' md' kk ->
  asrc_at B ly' St' W' mem' (xe_HA k) (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') -> hl_recs H' = [] ->
  Permutation (hl_recs (hs_held h)) ds ->
  val_mem segs (mrestrict (w_H W') mem') (lf_F cx + AX_AT) 8 (A + c) ->
  0 <= c -> A + c <= Z.of_nat (length (lm_O m0)) ->
  (forall rest, Permutation (ablocks B ly St) (lx_cshe_ds_blks ds ++ rest) ->
     Permutation (ablocks B ly' St') rest) ->
  frames St' = frames St ->
  mo_le MT St St' (lx_cshe_cost (hs_held h)) ->
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & HGS8 & Hord).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (al_blocks _ _ LAWS ly St W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (al_client_img _ _ LAWS ly St W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HP0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup ly St W mem md HAR)]. eapply perm_trans; [exact HP0 | exact HS1]. }
  destruct (ERR ly' St' W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
  set (M' := xe_set_slot m k (Some (CheckRep.set_held h H')) ev).
  assert (Hh' : nth k (lm_hs M') None = Some (CheckRep.set_held h H'))
    by (exact (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl)).
  assert (EBL : xe_BL cx M' k = xe_BL cx m k).
  { unfold xe_BL, M', xe_set_slot. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite xe_set_set. reflexivity. }
  assert (HAHs : Permutation (alist_blks (hs_held h)) (lx_cshe_ds_blks ds ++ alist_blks H')).
  { unfold alist_blks at 2. rewrite Hv, Hcap, Hrecs. cbn [map]. rewrite app_nil_r.
    unfold alist_blks, lx_cshe_ds_blks.
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_map; exact HPds | apply Permutation_app_comm]. }
  assert (HSPL : forall R, Permutation (input_blks cx ++ model_blks m ++ R)
      (lx_cshe_ds_blks ds ++ (input_blks cx ++ model_blks M' ++ R))).
  { intros R. pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R Hh') as X. rewrite EBL in X.
    exact (xe_perm_comb _ _ _ _ _ _ _ _ (xe_mblks_split cx m k h R Hh) X HAHs). }
  assert (HP0' : Permutation (ablocks B ly' St') (input_blks cx ++ model_blks M' ++ R0))
    by (apply HFRM; exact (perm_trans HP0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0)|].
    eapply Permutation_in; [exact (Permutation_sym HS1)|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HBLnew : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly' St')).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0')|].
    eapply Permutation_in; [exact (Permutation_sym HS1')|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the bytes the model reads, kept: blocks, globals, the other slots *)
  assert (KB : forall b, In b (xe_BL cx m k) -> xe_bk W mem W' mem' b).
  { intros [p n] Hb. unfold xe_bk. cbn [fst snd]. intros a Ha.
    pose proof (HBLold _ Hb) as Hin. pose proof (HBLnew _ Hb) as Hin'.
    split.
    - replace a with (p + (a - p)) by lia. apply (KK4 p n); [exact Hin | exact Hin' | lia |].
      intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq). cbn [fst snd] in Hra.
      assert (Hne : (q, n2) <> (p, n)).
      { intros E. rewrite E in Hq.
        exact (xe_nodup_app _ _ _ HNDL Hq ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)). }
      pose proof (sep_blocks segs B LAWS ly St W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (al_blocks _ _ LAWS ly' St' W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
      apply xe_wr_of_present. exact (proj1 (Hpr a Ha)). }
  assert (KG : forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct (xe_globs_rng a Ha) as (Hlo & Hout). pose proof (xe_globs_G a Ha) as HGa.
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_HI. lia.
    - intros _. apply GWR. exact HGa. }
  assert (KS : forall i, (i < 4)%nat -> i <> k -> forall a, xe_HA i <= a < xe_HA i + ASRC ->
      abyte_kept W mem W' mem' a).
  { intros i Hi Hik a Ha.
    assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_S as HE. unfold xe_HA, ASRC in *. lia.
    - intros _. apply GWR. exact HGa. }
  assert (HMOD' : amodel_at B ly' St' W' mem' M').
  { refine (xe_amodel_tr ly St W mem ly' St' W' mem' m k (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))
      ev HMOD _ _ _ _ _ _ Hev Hevw Hevb).
    - rewrite xe_set_nth_length. exact M1.
    - intros _. rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). exact HSRC.
    - intros i Hi Hik. exact (xe_nth_set_ne k i (Some (CheckRep.set_held h H')) None (lm_hs m) Hik).
    - exact KS.
    - intros b Hb _. pose proof (xe_BL_cover cx m k b M1 Hb) as HbB.
      split; [exact (HBLnew _ HbB) | exact (KB _ HbB)].
    - exact KG. }
  (* the frame and the fake frame *)
  assert (Efr : frame_addr ly' 1 fpos = frame_addr ly 1 fpos).
  { destruct (ajournal_gx_inner segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds segs B LAWS ly St W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (al_frames _ _ LAWS ly' St' W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame segs B LAWS ly St W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (al_blocks _ _ LAWS ly St W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx segs B G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St W mem md [] ly' St' W' mem' md' kk).
  { apply (ajournal_gx_G_mono segs B (xe_G k) G_fr); [|exact HJc].
    intros a Ha. apply HGs. pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  assert (HFPprov : forall a, inFP (blk_FP (alist_blks (hs_held h))) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly St) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly St) a).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
    cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
    destruct (HSEP2 (q, n2) (xe_held_in_model m k h Hh _ Hq)) as [Hno | Hfp].
    - right. exists q, n2. split; [exact Hq' | split; [exact Hno | exact Hra]].
    - left. split.
      + (* B's ablocks_sep names the block's request-size footprint, as blk_FP does *)
        apply Hfp. cbn [fst snd]. exact Hra.
      + exists q, n2. split; [exact Hq' | exact Hra]. }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' W' mem' md' (kk0 + kk)).
  { apply HJ2.
    - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - unfold AX_XO. lia.
    - intros a (r & [<- | []] & Hra). left. cbn [fst snd] in Hra. unfold AX_AT, LLVMF_STK in *. lia.
    - exact HG.
    - exact HFPprov. }
  pose proof HJ2' as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (HRO : rom_out segs B (xe_G k)).
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
    intros Hx. apply R1. apply HGs. pose proof (xe_inG_xeG k a Hx). unfold xe_HA, ASRC in *. lia. }
  pose proof (ajournal_gx_rom_view segs B pa_segs_low (xe_G k) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HRO HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv.
  split; [exists (kk0 + kk); exact HJ2'|].
  split.
  { rewrite Efr. apply (xe_bxframe_tr cx _ W mem W' mem' HFA HFhi).
    - intros a Ha _ Hat. destruct (Z_lt_le_dec a (lf_F cx + AX_XO)) as [Hl | Hl].
      + apply KK3; [lia | exact Hat].
      + apply KK2; [unfold AX_XO in *; lia | unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia].
    - apply xe_awr_pres. intros x Hx. apply Hpres2. unfold LLVMF_STK. lia.
    - exact KFF.
    - apply xe_awr_pres. intros x Hx. exact (proj1 (HFP x Hx)).
    - apply xe_awr_pres. intros x Hx.
      replace x with (shadow_addr (frame_addr ly 1 fpos) + (x - (SB + frame_addr ly 1 fpos / 8)))
        by (unfold shadow_addr, SHADOW_OFF, SB; lia).
      apply (HSP (x - (SB + frame_addr ly 1 fpos / 8))). lia. }
  split.
  { (* the fake frame's flag word, read by view *)
    rewrite Efr, (lx_fla_kept B HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply KFF. left. lia. }
  split; [rewrite Efr; exact HFAeq|].
  split; [exact HMOD'|].
  split.
  { apply (xe_ainput_tr cx ly St W mem ly' St' W' mem' HIN (eq_sym HlenP)).
    intros Hn. assert (Hb : In (c_p cx, c_n cx) (xe_BL cx m k)).
    { unfold xe_BL. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    exact (conj (HBLnew _ Hb) (KB _ Hb)). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W' mem' HRV HRV' HJT)|].
  split.
  { split; [exists R0; exact HP0'|]. intros b Hb. apply HSEP2.
    exact (xe_model_sub m k h H' ev Hh Hv Hcap Hrecs b Hb). }
  split; [intros rest Hr; apply HFRM; exact (perm_trans (HBF rest Hr) (HSPL rest))|].
  split; [exact (eq_trans (xe_set_nth_length k _ (lm_hs m)) M1)|].
  split.
  { intros j Hj. specialize (Hevo j Hj).
    change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    assert (Hn0 : hl_n H' = 0) by (unfold hl_n; rewrite Hrecs; reflexivity).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). rewrite Hh in Hevo.
      destruct Hevo as [E | (h0 & H0 & E1 & E2 & Hle)].
      + right. exists h, H'. split; [symmetry; exact E|]. split; [reflexivity|]. rewrite Hn0. unfold hl_n. lia.
      + right. exists h0, H'. split; [exact E1|]. injection E2 as E2. split; [rewrite E2; reflexivity|].
        rewrite Hn0. unfold hl_n. lia.
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact Hevo. }
  split; [exact Ek|]. split; [exact EG|]. split; [exact Ees|].
  split.
  { change (lx_ctl_ev (lm_c m) ev = lx_ctl_ev (lm_c m0) ev). rewrite Ec. reflexivity. }
  split; [exact EO|]. split; [exact Emx|]. split; [exact Ecap|]. split; [exact Eout|].
  split; [exact Egn|]. split; [exact Enfd|].
  split; [rewrite HFR; exact Hfrs|].
  change (lx_ends_cost (lm_hs M')) with (lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))).
  rewrite Ecost.
  split.
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold lx_cshe_cost in X.
    replace (lx_ends_cost (lm_hs m0) - (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m) + hl_n (hs_held h) * mo_free MT) by lia.
    exact X. }
  split.
  { apply (mo_ok_step MT MLM St St' (hl_n (hs_held h) * mo_free MT)); [|exact HMLE].
    replace (hl_n (hs_held h) * mo_free MT + (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m)) by lia. exact Hmok. }
  split.
  { intros j Hj. change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl).
      cbn [lx_ends_slot_ok CheckRep.set_held hs_held].
      split; [exact HND | unfold hl_n; rewrite Hrecs; cbn [length Z.of_nat]; lia].
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact (Hsok j Hj). }
  split; [exact HAT|]. split; [lia|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HNO]. intros x Hx. apply KK3; unfold AX_NORDER, AX_XO, AX_AT in *; lia. }
  split; [exact Hnord|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HGS8]. intros x Hx. apply KK3; unfold AX_GS8, AX_XO, AX_AT in *; lia. }
  intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
  apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia.
Qed.
(* ---- the call site's own kit (XECall) ---- *)
(* the jal at 0x84cf0: one machine step, ra := 0x84cf4, pc := check_shape_ends *)
Lemma xc_step_jal : forall regs mem,
  RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (BASE + AX_call)) mem (seg_rom segs)) =
  MachineOk (mkst (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv)))
    (Z_to_bv 64 (BASE + AF_fr_check_shape_ends)) mem (seg_rom segs)).
Proof.
  intros regs mem.
  assert (Hpl : plookup (pl_tpi (L := fr_prog_listing)) AX_call = Some (PW 0x7e4000ef))
    by (vm_compute; reflexivity).
  pose proof (pa_fetch_pw (PI := PB_fr) _ _ Hpl) as Hf.
  assert (Hd : decode_any (Z_to_bv 32 0x7e4000ef) = Some (Jal 1 (Z_to_bv 21 0x7e4), 4%Z)) by vm_refl_bv.
  rewrite (step_jal_link segs regs _ mem (seg_rom segs) (Z_to_bv 32 0x7e4000ef) 1 (Z_to_bv 21 0x7e4)
    Hf ltac:(eapply not_ecall_of_decode; [exact Hd | discriminate]) Hd).
  f_equal.
Qed.
(* reads of the registers the jal does not write *)
Lemma xc_getr_upd1 : forall regs v (r : bv 5), bv_unsigned r <> 1 -> getr (regupd regs 1 v) r = getr regs r.
Proof.
  intros regs v r Hr. unfold getr. destruct (bv_eqb r 0) eqn:E0; [reflexivity|].
  apply regupd_other. intros ->. apply Hr. reflexivity.
Qed.
Lemma xc_getr_upd1_same : forall regs v, getr (regupd regs 1 v) 1 = v.
Proof. intros regs v. unfold getr. cbn [bv_eqb]. apply regupd_same. Qed.
(* a callee-saved register across a call *)
Lemma xc_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the value of a register index, as a numeral (W_img.v's zlit idiom) *)
Ltac xc_bvz :=
  lazymatch goal with
  | |- acallee_saved ?x => let v := eval vm_compute in x in (change x with v; unfold acallee_saved; lia)
  | |- ?x <> 1 => let v := eval vm_compute in x in (change x with v; lia)
  end.
(* every register of xe_regs_slot is callee-saved and is not ra, so the call keeps them all *)
Lemma xc_slot_kept : forall cx i (k : nat) n regs regs' v,
  xe_regs_slot cx i k n regs -> aregs_preserved (regupd regs 1 v) regs' -> xe_regs_slot cx i k n regs'.
Proof.
  intros cx i k n regs regs' v HR HP.
  assert (K : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 1 ->
    getr regs' r = getr regs r).
  { intros r H1 H2. rewrite (xc_pres _ _ r HP H1). exact (xc_getr_upd1 regs v r H2). }
  unfold xe_regs_slot, xe_regs_keep in HR |- *.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
  repeat split;
    (rewrite K; [assumption | xc_bvz | xc_bvz]).
Qed.
(* the invariant across the step's materialization of the model *)
Lemma xc_inv_mat : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X ((kk & HJ) & REST).
  split; [|exact REST]. exists kk.
  eapply (ajournal_gx_materialize segs B LAWS pa_segs_low). exact HJ.
Qed.
(* the blocks a list owns, as hs_blocks names them *)
Lemma xc_lb_in : forall (l : hlist) (p : Z), In p (HarnessRep.list_blocks l) ->
  exists nn, In (p, nn) (alist_blks l).
Proof.
  intros l p Hin. unfold HarnessRep.list_blocks, alist_blks in *.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (hl_cap l =? 0) eqn:E; [destruct Hin|].
    destruct Hin as [<- | []]. exists (AREC * hl_cap l). apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hin as (r & <- & Hr). exists (Z.of_nat (length (snd r)) + 1).
    apply in_or_app. right. exact (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1)) _ r Hr).
Qed.
Lemma xc_hsb_in : forall (h : hsrc) (p : Z), In p (hs_blocks h) -> exists nn, In (p, nn) (asrc_blks h).
Proof.
  intros h p Hin. unfold hs_blocks, asrc_blks in *.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. left. exact Hnn.
  - apply in_app_iff in Hin as [Hin | Hin].
    + destruct Hin as [<- | []]. exists APARTIAL. left. reflexivity.
    + apply in_app_iff in Hin as [Hin | Hin].
      * destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. right.
        apply in_or_app. left. exact Hnn.
      * destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. right.
        apply in_or_app. right. exact Hnn.
Qed.
Lemma xc_nodup_of_pairwise : forall (l : list (Z * Z)),
  YG0f.pairwise YG0f.zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l) ->
  Forall (fun b : Z * Z => 0 <= snd b) l -> List.NoDup l.
Proof.
  induction l as [|x l IH]; intros Hp HF; [constructor|].
  cbn [map] in Hp. destruct Hp as [Hfa Hp]. inversion HF as [|x0 l0 Hx HF' Heq]; subst.
  constructor.
  - intros Hin.
    pose proof (proj1 (Forall_forall _ _) Hfa (fst x, req_size (snd x))
      (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l x Hin)) as Hd.
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos (snd x) Hx) as [H1 _]. lia.
  - exact (IH Hp HF').
Qed.
(* the live blocks are distinct (they are pairwise disjoint and each covers a byte) *)
Lemma xc_blocks_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
  apply pairwise_app_l in Hp as [Hp _].
  apply (xc_nodup_of_pairwise _ Hp).
  apply Forall_forall. intros [p nn] Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. lia.
Qed.
(* the stream's buffer is none of the source's blocks *)
Lemma xc_out_apart : forall cx m ly S (W : world segs) mem md (k : nat) h,
  AR segs B ly S W mem md -> ablocks_sep B fr_FP cx m ly S ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h -> lm_cap m <> 0 ->
  ~ In (lm_out m) (hs_blocks h).
Proof.
  intros cx m ly S W mem md k h HAR (HPm & _) Hk4 Hh Hcap Hin.
  destruct (xc_hsb_in h (lm_out m) Hin) as (nn & Hnn).
  destruct HPm as (rest & HP).
  assert (Hlen : (k < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases k (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
    rewrite (nth_overflow _ _ Hge) in Hh. discriminate Hh. }
  assert (Hslot : In (lm_out m, nn) (concat (map slot_blks (lm_hs m)))).
  { apply in_concat. exists (slot_blks (Some h)). split.
    - rewrite <- Hh. exact (in_map slot_blks (lm_hs m) (nth k (lm_hs m) None) (nth_In _ None Hlen)).
    - cbn [slot_blks]. exact Hnn. }
  assert (Hout : In (lm_out m, lm_cap m) (aout_blks (lm_cap m) (lm_out m))).
  { unfold aout_blks. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [exfalso; exact (Hcap E)|].
    left. reflexivity. }
  assert (I1 : In (lm_out m, nn) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hslot. }
  assert (I2 : In (lm_out m, lm_cap m) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hout. }
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR I1) as (_ & _ & _ & _ & _ & _ & Hn1).
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR I2) as (_ & _ & _ & _ & _ & _ & Hn2).
  destruct (Z.eq_dec nn (lm_cap m)) as [Ene | Ene].
  - (* the same pair twice: the model's block list holds it once *)
    subst nn. exfalso.
    assert (HND : List.NoDup (ablocks B ly S)) by exact (xc_blocks_nodup ly S W mem md HAR).
    assert (HNDm : List.NoDup (input_blks cx ++ model_blks m ++ rest))
      by exact (Permutation_NoDup HP HND).
    apply List.NoDup_app_remove_l in HNDm. apply List.NoDup_app_remove_r in HNDm.
    unfold model_blks in HNDm. apply List.NoDup_cons_iff in HNDm as (_ & HNDm).
    apply List.NoDup_app_remove_l in HNDm.
    destruct (in_split _ _ Hslot) as (l1 & l2 & Esplit).
    rewrite Esplit, <- app_assoc in HNDm. cbn [app] in HNDm.
    apply NoDup_remove_2 in HNDm.
    apply HNDm. apply in_or_app. right. apply in_or_app. right. exact Hout.
  - pose proof (sep_blocks segs B LAWS ly S W mem md _ _ _ _ HAR I1 I2
      ltac:(intros E; injection E as E1; exact (Ene E1))) as Hd.
    pose proof (req_size_pos nn ltac:(lia)) as [Hq1 _].
    pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq2 _].
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the meter: one slot's share of lx_ends_cost *)
Lemma xc_cost_nonneg : forall hs, 0 <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; cbn [lx_ends_cost]; [lia|].
  destruct o as [h0|]; [|exact IH].
  pose proof (mo_free_nonneg MT MLM) as Hf.
  pose proof (Zle_0_nat (length (hl_recs (hs_held h0)))) as Hn.
  unfold hl_n. nia.
Qed.
Lemma xc_cost_nth : forall hs (k : nat) h, nth k hs None = Some h ->
  hl_n (hs_held h) * mo_free MT <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; intros k h Hk.
  - destruct k; cbn in Hk; discriminate.
  - destruct k as [|k'].
    + cbn in Hk. subst o. cbn [lx_ends_cost]. pose proof (xc_cost_nonneg hs). lia.
    + cbn in Hk. pose proof (IH k' h Hk) as IHk. cbn [lx_ends_cost].
      destruct o as [h0|]; [|exact IHk].
      pose proof (mo_free_nonneg MT MLM) as Hf.
      pose proof (Zle_0_nat (length (hl_recs (hs_held h0)))) as Hn0.
      unfold hl_n in *. nia.
Qed.

(* ---------------- (3) the call site ---------------- *)
(* ---- one call of check_shape_ends at the slot the inner loop stands on: the contract at the slot's own G,
   its journal composed into this function's, and the model's slot replaced ---- *)
Lemma xe_call : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRr segs W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HFmod : lf_F cx mod 32 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D32.
    replace (lf_F cx) with (((spZ (c_regs cx) - 320) / 32) * 32) by lia. apply Z_mod_mult. }
  assert (HF64 : 0 <= lf_F cx < 2 ^ 64) by lia.
  destruct xe_vals as (Egone & Enout & Eoutv & Egs & Hlit).
  assert (Egsv : rg_s fr_RG = 6131296) by (vm_compute; reflexivity).
  (* ---- the jal at 0x84cf0 ---- *)
  unfold cfg_at.
  eapply (SRr_step segs pa_wx W); [reflexivity | |].
  - rewrite restrict_mkst_fx. apply xc_step_jal.
  - intros md1 Hsame.
    cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (HI1 : xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply xc_inv_mat. exact HI. }
    (* the registers after the link *)
    assert (Q1 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 1 = Z_to_bv 64 (BASE + AX_adv))
      by apply xc_getr_upd1_same.
    assert (Kr : forall r : bv 5, bv_unsigned r <> 1 ->
      getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) r = getr regs r)
      by (intros r Hr; apply xc_getr_upd1; exact Hr).
    pose proof HR as HRc.
    destruct HRc as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
    assert (S2 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 2 = w64 (lf_F cx))
      by (rewrite Kr; [exact R2 | xc_bvz]).
    assert (Hsp1 : spZ (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) = lf_F cx).
    { unfold spZ. rewrite S2. unfold w64. apply unsigned_lit_small. exact HF64. }
    (* the cut's facts at the materialized model *)
    pose proof HI1 as HI1c.
    destruct HI1c as ((kk & HJ1) & HFR1 & HFLW1 & HFA1 & HMOD1 & HIN1 & HRV1 & HJT1 & HSEP1 & HPERM1 & HLEN1 & HEVO1 &
      EK1 & EG1 & EES1 & EC1 & EO1 & EMX1 & ECAP1 & EOUT1 & EGN1 & ENFD1 & HFRS1 & HMLE1 & HMOK1 & HSLOK1 &
      HAT1 & HA01 & HNORD1 & HGS81 & HORD1).
    pose proof HJ1 as HJ1c.
    destruct HJ1c as (HSTKj & HXOj & (memS & HJi & Hagj) & Houtj).
    pose proof HJi as (HARly1 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _ & _ & _).
    destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
    destruct HMOD1 as (HLm & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDr & HTU & HLST & HLSTw).
    pose proof (HSL k Hk4) as HSLk. rewrite Hh in HSLk. cbn [aslot] in HSLk.
    pose proof (HSLOK1 k Hk4) as HSOK. rewrite Hh in HSOK. cbn [lx_ends_slot_ok] in HSOK.
    destruct HSOK as (HNDt & HNb).
    destruct HOUT as (HOmx & _ & HOno & _ & HOcap & _ & HOout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HOlen & HOcase).
    (* the callee's entry state *)
    assert (HPRE1 : exists ch, afn_pre segs B lx_CSHE_STK ly St W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG cx ly St fpos kk W mem md1
        (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) lx_CSHE_STK HB HJ1 HFR1 Hsp1).
      - rewrite Q1. apply ret_ok_codeptr_v;
          [unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput; lia | vm_compute; reflexivity].
      - unfold raZ. rewrite Q1.
        pose proof pa_B_ok as (HB0 & HB1 & _). pose proof (pa_base_lo (L := fr_prog_listing)) as HBlo.
        rewrite unsigned_lit_small by (unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput in *; lia).
        unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput. lia.
      - rewrite Kr; [exact R3 | xc_bvz].
      - rewrite Kr; [exact R4 | xc_bvz].
      - rewrite Kr; [exact R8 | xc_bvz].
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK. lia.
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia. }
    destruct HPRE1 as (ch & HPREc).
    (* the slot's G *)
    assert (HGk : gx_ok segs B (xe_G k)).
    { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG].
      intros a Ha. apply HGs. unfold xe_G in Ha. apply inG_cons in Ha as [Ha | Ha];
        [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, xe_HA, ASRC in *. cbn [fst snd] in Ha. lia. }
    (* the held list of the slot *)
    pose proof HSLk as HSLkc.
    destruct HSLkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HHELD & _).
    pose proof HHELD as HHELDc.
    destruct HHELDc as (_ & _ & _ & _ & _ & HVEC & _ & _ & HRECS).
    (* the stream, as check_shape_ends reads it *)
    assert (HSTR : ob_at W mem (lm_out m) (lm_O m) /\
      Z.of_nat (length (lm_O m)) <= 2 ^ 40 /\
      (0 < Z.of_nat (length (lm_O m)) -> Z.of_nat (length (lm_O m)) < 2 ^ 32) /\
      amem_range (lm_out m) (Z.of_nat (length (lm_O m)) + 8) /\
      (lm_O m = [] \/ exists CO, Z.of_nat (length (lm_O m)) <= CO /\
         In (lm_out m, CO) (ablocks B ly St) /\ ~ In (lm_out m) (hs_blocks h))).
    { destruct HOcase as [(Ecap & Eout0 & Elen0) | (Hcap0 & Hnocap & Hinb & junk & Hjl & Hg8)].
      - assert (HO0 : lm_O m = []) by (apply length_zero_iff_nil; lia).
        split; [intros j Hj; rewrite Elen0 in Hj; lia|].
        split; [rewrite Elen0; lia|].
        split; [rewrite Elen0; lia|].
        split; [unfold amem_range; left; rewrite Elen0, Eout0; unfold kLowMemEnd; lia|].
        left. exact HO0.
      - pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _ & _ & Hmm).
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [unfold MALLOC_MAX in Hmm; lia|].
        split; [intros _; unfold MALLOC_MAX in Hmm; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE (xe_G k) HGk W ly St (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRr_mono.
    { apply HC.
      + exact HPREc.
      + unfold AX_XO. lia.
      + vm_compute. reflexivity.
      + rewrite Hsp1, Etop. unfold AX_XO. lia.
      + rewrite Hsp1. intros a Ha. apply Hpresj. unfold AX_XO in Ha. unfold LLVMF_STK in *. lia.
      + rewrite Kr; [exact R10 | xc_bvz].
      + rewrite Kr; [exact R11 | xc_bvz].
      + rewrite Kr; [exact R12 | xc_bvz].
      + exact HSLk.
      + unfold xe_HA. rewrite Egsv.
        replace (6131296 + ASRC * Z.of_nat k) with ((766412 + 12 * Z.of_nat k) * 8) by (unfold ASRC; lia).
        apply Z_mod_mult.
      + unfold xe_HA, ASRC. rewrite Egsv. lia.
      + unfold xe_HA, ASRC, kLowMemEnd. rewrite Egsv. lia.
      + intros a Ha. unfold xe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + apply (xe_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact AZS_s | unfold xe_HA, ASRC; lia |
          unfold xe_HA, ASRC; lia].
      + unfold xe_HA. destruct xe_vals as (_ & _ & _ & Exgs & _). rewrite <- Exgs. reflexivity.
      + lia.
      + rewrite Hsp1. intros a Ha.
        unfold xe_HA, ASRC, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold lx_cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _ & _ & _ & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _ & _ & _ & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
          rewrite Eshi; unfold AX_AT in *; lia | lia].
      + exact HAT1.
      + intros Hc. destruct Hc.
      + cbn [length]. lia.
      + rewrite Hlit. lia.
      + rewrite Hlit. cbn [length]. lia.
      + cbn [length]. intros j Hj. lia.
      + cbn [length]. rewrite Z.add_0_r. exact (proj1 (xe_lit_bytes W mem HRV1)).
      + cbn [length]. intros a Ha.
        split; [apply (proj2 (xe_lit_bytes W mem HRV1)); rewrite Hlit in *; lia|].
        rewrite Hsp1; rewrite Hlit in *.
        unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St W mem md1 HARly1) ltac:(lia)).
      + (* the prefix's home: B's spec takes it as one disjunction; .str.3 is a read-only literal *)
        left. split; [cbn [length]; intros a Ha; apply xe_lit_rom; lia|].
        replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + rewrite Eoutv. exact HOout.
      + exact HOB.
      + reflexivity.
      + exact HObound.
      + exact HObound2.
      + exact HOmr.
      + exact HOdis.
      + rewrite EO1. lia.
      + intros Hg0 E'. apply Hnone. unfold lx_ends_c1.
        rewrite <- EGN1, Hg0, <- EO1. cbn [Z.eqb]. rewrite E'. reflexivity.
      + apply (mo_ok_le MT MLM St (lx_cshe_cost (hs_held h)) (lx_ends_cost (lm_hs m)) HMOK1).
        unfold lx_cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh). }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & _ & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2).
    rewrite Hsp1 in HJc.
    assert (HE : hl_recs H' = [] /\ Permutation (hl_recs (hs_held h)) ds /\
      A + c <= Z.of_nat (length (lm_O m0)) /\
      lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
    { destruct Harms as [(Hg & Hrecs & Hds & Hc) | (Hg & Hrun)].
      - assert (Hr0 : hl_recs H' = []) by (rewrite Hrecs; apply xm_filter_nil_f).
        assert (Hds0 : ds = hl_recs (hs_held h)) by (rewrite Hds; apply xm_filter_nil_t).
        split; [exact Hr0|].
        split; [rewrite Hds0; apply Permutation_refl|].
        split; [subst c; rewrite Z.add_0_r; lia|].
        unfold lx_ends_c1. rewrite <- EGN1.
        destruct (Z.eqb_spec (lm_gn m) 0) as [E0 | E0]; [exfalso; exact (Hg E0)|].
        rewrite Hr0, xm_filter_nil_f. subst c. rewrite Z.add_0_r. reflexivity.
      - assert (Hc1e : lx_ends_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
        { unfold lx_ends_c1. rewrite Hg. cbn [Z.eqb]. rewrite Hrun. reflexivity. }
        destruct (xm_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (Hr0 & Hb).
        destruct (xm_c1_ds (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (_ & Hds2).
        split; [exact Hr0|].
        split; [exact (Hds2 Hg ds c Hrun)|].
        rewrite length_skipn in Hb. rewrite EO1 in Hb.
        split; [lia|].
        rewrite <- EGN1, <- EO1. exact Hc1e. }
    destruct HE as (Hr0 & Hperm_ds & Hbound & Hends).
    destruct (xe_model_after cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.
(* a closed slot reads 0 in its fd and open fields (source_reset's 96 zero bytes) *)
Lemma xe_closed_vals : forall (W : world segs) mem HA, asrc_closed W mem HA ->
  val_mem segs (arm W mem) HA 4 0 /\ val_mem segs (arm W mem) (HA + 4) 4 0.
Proof.
  intros W mem HA (HGz & _).
  assert (Hr : forall n j, nth j (repeat 0%Z n) 0%Z = 0%Z).
  { induction n as [|n IH]; intros [|j]; cbn [repeat nth]; try reflexivity; apply IH. }
  assert (Hz : forall w k, YO0f.le_byte 0 w k = 0).
  { intros w k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. }
  assert (Hb : forall j, (j < 96)%nat -> mbyte segs (arm W mem) (HA + Z.of_nat j) = Some (Z_to_bv 8 0)).
  { intros j Hj. destruct (HGz j ltac:(rewrite repeat_length; unfold ASRC; cbn; lia)) as (HV & _).
    specialize (HV 0%nat ltac:(lia)). rewrite Z.add_0_r, Hr, Hz in HV. exact HV. }
  split; intros k Hk.
  - rewrite Hz. exact (Hb k ltac:(lia)).
  - rewrite Hz. replace (HA + 4 + Z.of_nat k) with (HA + Z.of_nat (4 + k)) by lia.
    exact (Hb (4 + k)%nat ltac:(lia)).
Qed.

(* a run leaves the model materialized; the loop's state does not read it but through the journal *)
Lemma xe_inv_materialize : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize segs B LAWS pa_segs_low); exact HJ | exact REST].
Qed.

(* the frame base is 320 to 351 bytes below the entry sp, above the allocation ceiling *)
Lemma xe_geom : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\
  alloc_ceiling < lf_F cx /\ lf_F cx + 320 <= 2 ^ 47.
Proof.
  intros cx (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (HLS : LLVMF_STK = 32768) by reflexivity. rewrite HLS in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320)
    by (unfold lf_F; pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ---- one trip of the inner loop: the two tests and, when they pass, the call ---- *)
Lemma xe_step_inner : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv).
  destruct HJx as (kk & HJ).
  assert (HAR : AR segs B ly St W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
  (* the slot's two fields, and the model's reduced slot *)
  pose proof (HSLOT k Hk4) as HSL. unfold aslot in HSL.
  assert (Hknth : nth_error (lm_hs m) k = Some (nth k (lm_hs m) None))
    by (apply nth_error_nth'; lia).
  assert (HNE : nth_error (map lx_ends_slot0 (lm_hs m)) k =
                Some (lx_ends_slot0 (nth k (lm_hs m) None))).
  { rewrite nth_error_map, Hknth. reflexivity. }
  destruct (nth k (lm_hs m) None) as [h|] eqn:Ehk.
  - (* an open source *)
    pose proof HSL as (Mfd & Mop & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    eapply SRr_bind.
    { eapply (xe_inner_run cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRr_mono.
      { eapply (xe_call cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                  HR' Ha0 Ha1 Ha2 Hk4 Ehk).
        exact (xm_fin_c1_ne (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                 (hs_fd h) (hl_recs (hs_held h)) afin HNE2 (eq_sym Hoi) HFIN). }
      cbv beta. intros W2 c2 _ (ly' & S' & regs2 & mem2 & md2 & m' & H' & A1 & -> & HINV2 & HR2 & HH' & HC1 & HHS).
      exists ly', S', regs2, mem2, md2, m', A1.
      split; [reflexivity|]. split; [exact HINV2|]. split; [exact HR2|].
      assert (ESL : map lx_ends_slot0 (lm_hs m') =
                    xe_set_nth k (Some (hs_fd h, hl_recs H')) (map lx_ends_slot0 (lm_hs m))).
      { rewrite HHS, xm_slot0_set. cbn [lx_ends_slot0 CheckRep.set_held hs_fd hs_held]. reflexivity. }
      rewrite ESL.
      rewrite <- (xm_fin_call (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (hs_fd h) (hl_recs (hs_held h)) (hl_recs H') A1 HNE2 (eq_sym Hoi) HC1).
      exact HFIN.
    + (* the slot is skipped *)
      apply SRr_ret.
      exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
      split; [reflexivity|].
      split; [exact (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
      split; [exact HR'|].
      rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (lx_ends_slot0 (Some h)) HNE).
      * exact HFIN.
      * right. exists (hs_fd h), (hl_recs (hs_held h)).
        split; [try rewrite Ehk; reflexivity|].
        destruct Hsk as [Hz | Hne]; [rewrite Hopen in Hz; discriminate | intros Heq; apply Hne; symmetry; exact Heq].
  - (* a closed slot: its fd and open fields read 0, so the loop skips it *)
    destruct (xe_closed_vals W mem (rg_s fr_RG + ASRC * Z.of_nat k) HSL) as (Mfd & Mop).
    assert (EHA : rg_s fr_RG + ASRC * Z.of_nat k = xe_HA k) by reflexivity.
    rewrite EHA in Mfd, Mop.
    eapply SRr_bind.
    { eapply (xe_inner_run cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply SRr_ret.
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.

(* ---- the two loops, from the advance point after the slot k of trip i ---- *)
Lemma xe_loop : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md) (lx_ends_post cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply SRr_bind.
  { eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply SRr_bind.
    { eapply (xe_step_inner cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                HR' Hk' Hi Hnord HFIN). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2 & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2 i (S k) afin HB Hk' Hi Hnord
             ltac:(lia) HINV2 HR2 HRUN HFIN2).
  - (* the next trip *)
    assert (HFIN' : xe_fin (lm_gn m0) (lm_O m0) ord norder (i + 1) 0 A (map lx_ends_slot0 (lm_hs m)) = Some afin).
    { rewrite <- (xm_fin_next (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
                    ltac:(lia) ltac:(lia)).
      rewrite <- Hk4'. exact HFIN. }
    eapply SRr_bind.
    { eapply (xe_head_run cx W regs' mem (with_vm_backing (m_vm_lazy md) X md) (i + 1) norder HR'
                ltac:(lia) HFlo HFhi HGS8). }
    cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
    eapply SRr_bind.
    { eapply (xe_step_inner cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
                HR2 ltac:(lia) ltac:(lia) Hnord HFIN'). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2' & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2' & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2' (i + 1) 0%nat afin HB
             ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV2 HR2' HRUN HFIN2).
  - (* the last trip is done: 0x84d4c, with the `at` cell at its final value *)
    apply SRr_ret.
    assert (EA : afin = A).
    { pose proof (xm_fin_done (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
        ltac:(lia)) as HD.
      rewrite <- Hk4' in HD. rewrite HD in HFIN. injection HFIN as <-. reflexivity. }
    pose proof HRK as (R2 & R9 & R8 & R3 & R4 & _).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), kk, m, A.
    split; [reflexivity|].
    split; [eapply (ajournal_gx_materialize segs B LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    eapply (mo_le_mono MT MLM); [exact HMLE|].
    pose proof (xe_cost_nonneg (lm_hs m)). lia.
Qed.


Lemma lx_ends : lx_ends_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Proof.
(* The block, assembled: the entry run stores norder at F+152 and the shadow cursor at F+144 and sets the cursors
   (xe_entry_run), the outer head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs
   (xe_step_inner) and the two loops then run to 0x84fe8 (xe_loop).  The model side is xe_fin, which at (0, 0) is
   lx_ends_run.  The entry's aframe_at is weakened to bx_frame: its F+152 cell is the one the entry overwrites. *)
  unfold lx_ends_S.
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR0 HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R27 R19 R3 R4 Hnord HAT HORD HB.
  pose proof (bx_frame_of_aframe _ _ _ _ HFR0) as HFR. clear HFR0.
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply SRr_bind.
  { eapply (xe_entry_run cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R27 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HGS1 & HKEEP & HPRES).
  destruct (xe_carry cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_GS8; lia. }
  assert (HINV : xe_inv cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
  { split; [exists kk; exact HJ1|].
    split; [exact HFR1|]. split; [exact HFL1|]. split; [reflexivity|]. split; [exact HMOD1|]. split; [exact HINP1|].
    split; [exact HRV1|]. split; [exact HJT1|]. split; [exact HSEP|].
    split; [intros rest HP; exact HP|].
    split; [exact (proj1 HMOD1)|].
    split; [intros j Hj; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (lm_c m); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [replace (lx_ends_cost (lm_hs m) - lx_ends_cost (lm_hs m)) with 0 by ring;
            exact (mo_le_refl MT MLM S3)|].
    split; [exact HMOK|].
    split; [exact HSLOK|].
    split; [exact (HVAL1 (lf_F cx + AX_AT) 8%nat 0 ltac:(unfold AX_ORDER, AX_AT; lia)
                     ltac:(unfold AX_AT; lia) HAT)|].
    split; [lia|].
    split; [exact HNO1|].
    split; [exact Hnord|].
    split; [exact HGS1|].
    intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
    exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
             ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply SRr_bind.
  { eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi HGS1). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply SRr_bind.
  { eapply (xe_step_inner cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.
End lx.
