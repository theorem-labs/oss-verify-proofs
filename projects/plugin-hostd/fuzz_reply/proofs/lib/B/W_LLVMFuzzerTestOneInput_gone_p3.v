(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: HLS1 carries gn_cst (relay_instance_gone's cost at q = 0) *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE 3: GRG 0x84b40 -> GC1 0 0x84b5c, the call relay_instance_gone(id) (fuzz_reply.c:642).  The image-B port of
   lib/A/W_LLVMFuzzerTestOneInput_gone_p3.v (a working branch 32b23a20c3e), at B's addresses,
   registers and frame (the objdump of the pinned binary fuzz_reply.asan-ubsan),
   over the base lib/B/W_LLVMFuzzerTestOneInput_gone_base.v (85b530db754):
     0x84b40  sd   s10,24(s1)          HI_G_NOUT to F+24 (B spills s10 here; 0x84cb0 reloads it)
     0x84b44  mv   a0,s5               the id
     0x84b48  jal  82ca0 <relay_instance_gone>
     0x84b4c  auipc a0,0x554; addi s4,a0,788    s4 = &g_s[0] (0x5d8e60)
     0x84b54  addi s5,s1,192           &reads[0]
     0x84b58  addi s6,s1,208           the loop's end pointer
   The callee's contract is W6's, taken verbatim (lib/B/W_contract.v:1474 rig_spec, :1174 rg_place); its journal is at
   G_RIG B fr_RG, lifted to G_fr with ajournal_gx_G_mono under GN_HG_RIG and spliced into the arm's with
   ajournal_gx_sub, as B's latch walk (lf_seg_latch) does for check_bounded.  The run before the call writes the frame
   cell F+24 (a plain frame store of the token run: every other byte is kept by the run's frame_of), so the cut point's
   facts are carried to the call's entry state with the base's transport kit (_gone_tk.v) and gp3_gframe_st.
   B against A in the Section hypotheses: A's GN_ROM_PIN and the errno-not-rom half of A's GP3_ERRNO_APART are
   replaced by HRO : rom_out segs B G_fr (lib/B/W_journal.v:397; B's add walk's HRO, discharged by
   lib/B/W_LLVMFuzzerTestOneInput_G.v c_rom_out at G_fr_c): on B rom_out names the sink head AOFL_HEAD, a field of the
   Context sink_head that no vm_compute decides here; the errno half over the four cells is DERIVED from the base's
   GN_CELLS_ERRNO (gp3_errno_g4), as A's composition derives gx_errno_apart. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* K0's caller-context tables (rig_spec's CTX_AFREE is image B's YCk0.CTX_AFREE at the instance) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
(* this file needs lia's division equations (the shadow addresses, sp mod 8) *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's stack budget, from the generated lib/B/YCfn.v, as the cut names it *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ generic list helpers *)
Lemma gp3_nodup_app : forall {A : Type} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hd. induction l1 as [|a l1 IH]; [exact H2|].
  apply List.NoDup_cons_iff in H1 as [Hna Hnd]. cbn [app]. apply List.NoDup_cons.
  - intros Hin. apply in_app_iff in Hin as [Hin | Hin];
      [exact (Hna Hin) | exact (Hd a (or_introl eq_refl) Hin)].
  - apply IH; [exact Hnd|]. intros x Hx. exact (Hd x (or_intror Hx)).
Qed.
Lemma gp3_nodup_app_neq : forall {A : Type} (l1 l2 : list A) (x : A),
  List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1 l2 x Hnd Hx Hy. induction l1 as [|a l1 IH]; [destruct Hx|].
  cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hna Hnd'].
  destruct Hx as [-> | Hx]; [apply Hna; apply in_app_iff; right; exact Hy | exact (IH Hnd' Hx)].
Qed.
Lemma gp3_perm_concat : forall {A : Type} (l1 l2 : list (list A)),
  Permutation l1 l2 -> Permutation (concat l1) (concat l2).
Proof.
  intros A l1 l2 HP. induction HP as [|x l1 l2 HP IH|x y l|l1 l2 l3 HP1 IH1 HP2 IH2].
  - apply perm_nil.
  - cbn [concat]. apply Permutation_app_head. exact IH.
  - cbn [concat]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - exact (perm_trans IH1 IH2).
Qed.
Lemma gp3_nodup_of_pairwise : forall (l : list (Z * Z)),
  (forall b, In b l -> 0 < req_size (snd b)) ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
  intros l. induction l as [|b l IH]; intros Hp Hpw; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw].
  apply List.NoDup_cons.
  - intros Hin. rewrite Forall_forall in Hf.
    pose proof (Hf (fst b, req_size (snd b))
      (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l b Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (Hp b (or_introl eq_refl)) as Hb. cbn [snd] in Hb. lia.
  - apply IH; [intros b' Hb'; exact (Hp b' (or_intror Hb')) | exact Hpw].
Qed.
(* the four slots, as a map over the index list *)
Lemma gp3_nth_map4 : forall {A : Type} (g : nat -> A) (d : A) (j : nat), (j < 4)%nat ->
  nth j (map g (seq 0 4)) d = g j.
Proof.
  intros A g d j Hj. cbn [seq map].
  destruct j as [|[|[|[|j]]]]; cbn [nth]; try reflexivity. lia.
Qed.
Lemma gp3_concat_map4 : forall {A : Type} (l : list A) (f : A -> list (Z * Z)) (d : A),
  length l = 4%nat ->
  concat (map (fun j => f (nth j l d)) (seq 0 4)) = concat (map f l).
Proof.
  intros A l f d Hl.
  destruct l as [|a0 [|a1 [|a2 [|a3 [|a4 l]]]]]; cbn [length] in Hl; try lia.
  cbn [seq map nth concat]. rewrite !app_nil_r. reflexivity.
Qed.
Lemma gp3_assoc4 : forall (x : Z * Z) (EB SRCS AO R : list (Z * Z)),
  (x :: EB ++ SRCS ++ AO) ++ R = x :: EB ++ SRCS ++ AO ++ R.
Proof. intros. cbn [app]. rewrite <- !app_assoc. reflexivity. Qed.
(* the two shapes of the block decomposition: ablocks_sep's and rig_spec's *)
Lemma gp3_perm_cong : forall (IN EB AOUT R0 S1 S2 : list (Z * Z)) (x : Z * Z),
  Permutation S1 S2 ->
  Permutation (IN ++ (x :: EB ++ S1 ++ AOUT) ++ R0) (IN ++ (x :: EB ++ S2 ++ AOUT) ++ R0).
Proof.
  intros IN EB AOUT R0 S1 S2 x HP.
  apply Permutation_app_head. apply Permutation_app_tail. apply perm_skip.
  apply Permutation_app_head. apply Permutation_app_tail. exact HP.
Qed.
Lemma gp3_perm_pre : forall (x : Z * Z) (IN EB SRCS OTH AOUT R0 : list (Z * Z)),
  Permutation (IN ++ (x :: EB ++ (SRCS ++ OTH) ++ AOUT) ++ R0)
              (x :: EB ++ SRCS ++ AOUT ++ (OTH ++ IN ++ R0)).
Proof.
  intros x IN EB SRCS OTH AOUT R0. cbn [app]. rewrite <- !app_assoc.
  etransitivity; [apply Permutation_sym; apply Permutation_middle|].
  apply perm_skip.
  etransitivity; [apply Permutation_app_comm|].
  rewrite <- !app_assoc.
  apply Permutation_app_head. apply Permutation_app_head.
  etransitivity; [apply Permutation_app_swap_app|].
  apply Permutation_app_head. apply Permutation_app_head.
  apply Permutation_app_comm.
Qed.

(* a run over read-only regions leaves the memory as it was *)
Ltac gp3_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ------------------------------------------------------------------ the phase's addresses *)
Definition AF_gp3_ret : Z := 0x2808.    (* 0x84b4c: back from relay_instance_gone *)

Section gp3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- what the other lanes owe (the texts the base fixes) ---- *)
Variable MMAX : Z.
(* relay_instance_gone, W6: lib/B/W_contract.v's rig_spec (Section s6 at CTX_AFREE := image B's K0 table
   YCk0.CTX_AFREE; its last premise is the free's caller context [0x82fb8; 0x84b4c(; 0x82240)]) and rg_place,
   verbatim.  The adaptation to the CTX_AFREE rig_spec is image A's (95cae0d4740), at B's numbers. *)
Hypothesis RIG : rig_spec (PI := PB_fr) B MT MMAX fr_RG YCk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place (PI := PB_fr) B fr_RG.
(* the model obligations, by the base's names *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis HLSRIG : GN_LS_rig MT LS RINV MMAX.
(* errno's place (the base's name): the transport of aout_at across the run's frame store reads it *)
Hypothesis ERRNO_LOW : GN_ERRNO_LOW B.
(* the cells amodel_at names lie in the entry's G_fr (the base's name), and the entry's law makes a byte of
   G_fr writable in any state (the cut's glob_wr_law) *)
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis GWR : glob_wr_law G_fr.
(* errno is none of the model's cells (the base's name) *)
Hypothesis HCE : GN_CELLS_ERRNO B.
(* the read-only bytes are off G_fr, pinned when the allocator owns them, off errno and off the sink head
   (lib/B/W_journal.v:397 rom_out; B's add walk's HRO; _G.v c_rom_out at G_fr_c): with GN_HG_RIG it gives rom_out at
   G_RIG (gp3_rom_out), so the cut's rom_view survives the callee's journal *)
Hypothesis HRO : rom_out segs B G_fr.

(* the four cells of amodel_at relay_instance_gone neither writes nor re-states *)
Definition gp3_g4 (a : Z) : Prop :=
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ AG_NFD <= a < AG_NFD + 4 \/
  AG_THREAD_UP <= a < AG_THREAD_UP + 1 \/ AG_LISTEN <= a < AG_LISTEN + 4.

(* ------------------------------------------------------------------ the live blocks are distinct and apart *)
Lemma gp3_nodup_blocks : forall ly S (W : world segs) mem md,
  AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hpw _].
  apply pairwise_app_l in Hpw as [Hpw _].
  apply gp3_nodup_of_pairwise; [|exact Hpw].
  intros b Hb. destruct b as [p n]. cbn [snd].
  destruct (gk_blk B LAWS ly S W mem md p n HAR Hb) as (_ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
Lemma gp3_apart : forall ly S (W : world segs) mem md (L1 L2 : list (Z * Z)) b1 b2 a,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) ->
  In b1 L1 -> In b2 L2 ->
  fst b1 <= a < fst b1 + req_size (snd b1) -> fst b2 <= a < fst b2 + req_size (snd b2) -> False.
Proof.
  intros ly S W mem md L1 L2 b1 b2 a HAR HP H1 H2 R1 R2.
  pose proof (Permutation_NoDup HP (gp3_nodup_blocks ly S W mem md HAR)) as HND.
  assert (Hne : b1 <> b2) by (intros ->; exact (gp3_nodup_app_neq L1 L2 b2 HND H1 H2)).
  assert (I1 : In b1 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; left; exact H1).
  assert (I2 : In b2 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; right; exact H2).
  destruct b1 as [p1 n1]; destruct b2 as [p2 n2]. cbn [fst snd] in *.
  pose proof (sep_blocks segs B LAWS ly S W mem md p1 n1 p2 n2 HAR I1 I2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* the footprint of a list of live blocks *)
Lemma gp3_inFP_fp : forall (bl : list (Z * Z)) a,
  inFP (ablocks_fp bl) a <-> (exists b, In b bl /\ fst b <= a < fst b + req_size (snd b)).
Proof.
  intros bl a. unfold inFP, ablocks_fp. split.
  - intros (r & Hin & Hr). apply in_map_iff in Hin as (b & <- & Hb).
    exists b. cbn [fst snd] in *. split; [exact Hb | lia].
  - intros (b & Hb & Hr). exists ((fst b, fst b + req_size (snd b)) : Z * Z). split.
    + apply in_map_iff. exists b. split; [reflexivity | exact Hb].
    + cbn [fst snd]. lia.
Qed.
Lemma gp3_fp_spares : forall ly S (W : world segs) mem md (bl : list (Z * Z)),
  AR segs B ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  forall a, fp_spares (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl HAR Hsub a. apply fp_spares_closed.
  apply sink_closed_ablocks_fp. apply Forall_forall. intros b Hb. destruct b as [p n].
  destruct (gk_blk B LAWS ly S W mem md p n HAR (Hsub _ Hb)) as (H1 & _). cbn [fst]. lia.
Qed.
Lemma gp3_not_fp_shadow : forall ly S (W : world segs) mem md (bl : list (Z * Z)) a,
  AR segs B ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  kLowShadowBeg <= a < kHighMemBeg -> ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl a HAR Hsub Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (Hsub _ Hb)) as (_ & H4096 & Hceil & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma gp3_not_fp_frame : forall ly S (W : world segs) mem md (bl : list (Z * Z)) cid pos a,
  AR segs B ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl cid pos a HAR Hsub Hf Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  pose proof (sep_block_frame segs B LAWS ly S W mem md p n cid pos HAR (Hsub _ Hb) Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
Lemma gp3_inner : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, ajournal segs B STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (ajournal_gx_inner segs B G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ)
    as (memS & HJi & Hag).
  rewrite !Z.add_0_r in HJi. exists memS. split; [exact HJi|].
  intros a Ha HnG. apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma gp3_keeps : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> alloc_ceiling <= a -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> 0 <= p + i < 2 ^ 64 -> ~ inG G (p + i) ->
     aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  AR segs B ly' S' W' mem' md' /\ frames S' = own ++ frames S /\
  layout_le (length (st_secs S)) ly ly' /\ wle W W'.
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (gp3_inner G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ) as (memS & HJi & Hag).
  pose proof HJi as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & C8 & C9 & C11 & C10 & C12 &
    C13 & Hstk & Cextra & HQT).
  split; [intros a Ha HnG Hc Hout; rewrite (C8 a ltac:(lia) ltac:(lia)); exact (Hag a Ha HnG)|].
  split.
  { intros p n i Hin Hin' Hi Hnf Hrng HnG.
    rewrite (C9 p n i Hin Hin' Hi Hnf). exact (Hag (p + i) Hrng HnG). }
  split.
  { intros cid pos a Hf Hr Hnf Ha HnG.
    rewrite (C10 cid pos a Hf Hr Hnf). exact (Hag a Ha HnG). }
  split.
  { intros a Himg Hown Herr Hsp Ha HnG.
    rewrite (C11 a Himg Hown Herr Hsp). exact (Hag a Ha HnG). }
  split; [exact C13|].
  split; [exact HAR'|]. split; [exact Hfrs|]. split; [exact Hly | exact Hwle].
Qed.
(* writability: from presence at the target state, or from presence kept at an image byte *)
Lemma gp3_wr_pres : forall (W : world segs) mem a, apresent (w_H W) mem a -> writable_at segs (arm W mem) a.
Proof. intros W mem a Hp. unfold arm. exact (apresent_writable segs _ _ _ Hp). Qed.

(* ------------------------------------------------------------------ the slots the callee drains *)
Lemma gp3_rig_slots_cons : forall e (h : hsrc * nat) ps,
  rig_slots ((e, h) :: ps) = (if re_eof e =? 0 then [snd h] else []) ++ rig_slots ps.
Proof. intros e h ps. unfold rig_slots. cbn [map concat]. reflexivity. Qed.
Lemma gp3_rig_srcs_cons : forall e (h : hsrc * nat) ps,
  rig_srcs ((e, h) :: ps) = (if re_eof e =? 0 then asrc_blks (fst h) else []) ++ rig_srcs ps.
Proof. intros e h ps. unfold rig_srcs. cbn [map concat]. reflexivity. Qed.
Lemma gp3_slot_in : forall es (hs : list (hsrc * nat)) i,
  length hs = length es -> (i < length es)%nat -> re_eof (nth i es gn_e0) = 0 ->
  In (snd (nth i hs gn_hj0)) (rig_slots (combine es hs)).
Proof.
  induction es as [|e es IH]; intros hs i Hlen Hi Heof; [cbn [length] in Hi; lia|].
  destruct hs as [|h hs]; [cbn [length] in Hlen; lia|].
  cbn [combine]. rewrite gp3_rig_slots_cons. apply in_app_iff.
  destruct i as [|i].
  - cbn [nth] in Heof |- *. rewrite Heof. cbn [Z.eqb]. left. left. reflexivity.
  - right. cbn [nth] in Heof |- *. apply IH; [cbn [length] in Hlen; lia | cbn [length] in Hi; lia | exact Heof].
Qed.
Lemma gp3_slots_inj : forall es (hs : list (hsrc * nat)) i1 i2,
  List.NoDup (rig_slots (combine es hs)) -> length hs = length es ->
  (i1 < length es)%nat -> (i2 < length es)%nat ->
  re_eof (nth i1 es gn_e0) = 0 -> re_eof (nth i2 es gn_e0) = 0 ->
  snd (nth i1 hs gn_hj0) = snd (nth i2 hs gn_hj0) -> i1 = i2.
Proof.
  induction es as [|e es IH]; intros hs i1 i2 HND Hlen H1 H2 E1 E2 Heq; [cbn [length] in H1; lia|].
  destruct hs as [|h hs]; [cbn [length] in Hlen; lia|].
  cbn [combine] in HND. rewrite gp3_rig_slots_cons in HND.
  destruct i1 as [|i1]; destruct i2 as [|i2].
  - reflexivity.
  - exfalso. cbn [nth] in E1, E2, Heq. rewrite E1 in HND. cbn [Z.eqb app] in HND.
    apply List.NoDup_cons_iff in HND as [Hna _]. apply Hna. rewrite Heq.
    apply (gp3_slot_in es hs i2); [cbn [length] in Hlen; lia | cbn [length] in H2; lia | exact E2].
  - exfalso. cbn [nth] in E1, E2, Heq. rewrite E2 in HND. cbn [Z.eqb app] in HND.
    apply List.NoDup_cons_iff in HND as [Hna _]. apply Hna. rewrite <- Heq.
    apply (gp3_slot_in es hs i1); [cbn [length] in Hlen; lia | cbn [length] in H1; lia | exact E1].
  - f_equal. cbn [nth] in E1, E2, Heq.
    apply (IH hs i1 i2); [| cbn [length] in Hlen; lia | cbn [length] in H1; lia
                         | cbn [length] in H2; lia | exact E1 | exact E2 | exact Heq].
    destruct (re_eof e =? 0) eqn:Eg; cbn [app] in HND;
      [apply List.NoDup_cons_iff in HND; exact (proj2 HND) | exact HND].
Qed.
Lemma gp3_srcs_of_slots : forall (g : nat -> list (Z * Z)) es (hs : list (hsrc * nat)),
  length hs = length es ->
  (forall i, (i < length es)%nat -> re_eof (nth i es gn_e0) = 0 ->
     g (snd (nth i hs gn_hj0)) = asrc_blks (fst (nth i hs gn_hj0))) ->
  concat (map g (rig_slots (combine es hs))) = rig_srcs (combine es hs).
Proof.
  induction es as [|e es IH]; intros hs Hlen Hg;
    [destruct hs; [reflexivity | cbn [length] in Hlen; lia]|].
  destruct hs as [|h hs]; [cbn [length] in Hlen; lia|].
  cbn [combine]. rewrite gp3_rig_slots_cons, gp3_rig_srcs_cons, map_app, concat_app. f_equal.
  - destruct (Z.eqb_spec (re_eof e) 0) as [Heq|Hne]; cbn [map concat].
    + rewrite app_nil_r. exact (Hg 0%nat ltac:(cbn [length]; lia) Heq).
    + reflexivity.
  - apply IH; [cbn [length] in Hlen; lia|].
    intros i Hi Heof. exact (Hg (S i) ltac:(cbn [length]; lia) Heof).
Qed.
Lemma gp3_newsrcs_of_slots : forall (g : nat -> list (Z * Z)) es (hs : list (hsrc * nat))
    (qs : list (rentry * hsrc)),
  length hs = length es -> length qs = length es ->
  (forall i, (i < length es)%nat -> re_eof (nth i es gn_e0) = 0 ->
     g (snd (nth i hs gn_hj0)) = asrc_blks (snd (nth i qs gn_q0))) ->
  concat (map g (rig_slots (combine es hs))) =
  concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
              (combine (combine es hs) qs)).
Proof.
  induction es as [|e es IH]; intros hs qs Hlen Hlq Hg;
    [destruct hs; [reflexivity | cbn [length] in Hlen; lia]|].
  destruct hs as [|h hs]; [cbn [length] in Hlen; lia|].
  destruct qs as [|q qs]; [cbn [length] in Hlq; lia|].
  cbn [combine]. rewrite gp3_rig_slots_cons, map_app, concat_app. cbn [map concat fst snd]. f_equal.
  - destruct (Z.eqb_spec (re_eof e) 0) as [Heq|Hne]; cbn [map concat].
    + rewrite app_nil_r. exact (Hg 0%nat ltac:(cbn [length]; lia) Heq).
    + reflexivity.
  - apply IH; [cbn [length] in Hlen; lia | cbn [length] in Hlq; lia|].
    intros i Hi Heof. exact (Hg (S i) ltac:(cbn [length]; lia) Heof).
Qed.
(* the slots no entry drains *)
Definition gp3_cs (js : list nat) : list nat := List.filter (fun j => negb (existsb (Nat.eqb j) js)) (seq 0 4).
Lemma gp3_cs_spec : forall js j, In j (gp3_cs js) <-> (j < 4)%nat /\ ~ In j js.
Proof.
  intros js j. unfold gp3_cs. rewrite List.filter_In, in_seq. split.
  - intros [Hseq Hneg]. split; [lia|]. intros Hin. rewrite negb_true_iff in Hneg.
    assert (Hex : existsb (Nat.eqb j) js = true)
      by (apply existsb_exists; exists j; split; [exact Hin | apply Nat.eqb_refl]).
    rewrite Hex in Hneg. discriminate.
  - intros [Hj Hnin]. split; [lia|].
    rewrite negb_true_iff. destruct (existsb (Nat.eqb j) js) eqn:Hex; [|reflexivity].
    exfalso. apply existsb_exists in Hex as (y & Hy & Hey). apply Nat.eqb_eq in Hey.
    subst y. exact (Hnin Hy).
Qed.
Lemma gp3_perm_slots : forall (hs4 : list (option hsrc)) (js : list nat),
  length hs4 = 4%nat -> List.NoDup js -> (forall j, In j js -> (j < 4)%nat) ->
  Permutation (concat (map slot_blks hs4))
    (concat (map (fun j => slot_blks (nth j hs4 None)) js) ++
     concat (map (fun j => slot_blks (nth j hs4 None)) (gp3_cs js))).
Proof.
  intros hs4 js H4 HND Hlt.
  assert (HP : Permutation (seq 0 4) (js ++ gp3_cs js)).
  { apply NoDup_Permutation.
    - apply seq_NoDup.
    - apply gp3_nodup_app; [exact HND | unfold gp3_cs; apply List.NoDup_filter; apply seq_NoDup |].
      intros x Hx Hxc. exact (proj2 (proj1 (gp3_cs_spec js x) Hxc) Hx).
    - intros x. rewrite in_seq, in_app_iff. split.
      + intros Hx. destruct (in_dec Nat.eq_dec x js) as [Hin | Hnin]; [left; exact Hin|].
        right. apply gp3_cs_spec. split; [lia | exact Hnin].
      + intros [Hx | Hx]; [pose proof (Hlt x Hx); lia | apply gp3_cs_spec in Hx; lia]. }
  rewrite <- (gp3_concat_map4 hs4 slot_blks None H4).
  rewrite <- concat_app, <- map_app.
  apply gp3_perm_concat. apply Permutation_map. exact HP.
Qed.
(* the slot j after the call: the source rig_post gives for the entry that drains j, else the slot as it was *)
Definition gp3_pick (es : list rentry) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc))
    (hs0 : list (option hsrc)) (j : nat) : option hsrc :=
  match find (fun i => andb (Z.eqb (re_eof (nth i es gn_e0)) 0) (Nat.eqb (snd (nth i hs gn_hj0)) j))
             (seq 0 (length es)) with
  | Some i => Some (snd (nth i qs gn_q0))
  | None => nth j hs0 None
  end.
Lemma gp3_in_slots_find : forall es (hs : list (hsrc * nat)) j, length hs = length es ->
  In j (rig_slots (combine es hs)) ->
  exists i, (i < length es)%nat /\ re_eof (nth i es gn_e0) = 0 /\ snd (nth i hs gn_hj0) = j.
Proof.
  induction es as [|e es IH]; intros hs j Hlen Hj.
  - cbn [combine] in Hj. unfold rig_slots in Hj. cbn [map concat] in Hj. destruct Hj.
  - destruct hs as [|h hs]; [cbn [length] in Hlen; lia|].
    cbn [combine] in Hj. rewrite gp3_rig_slots_cons in Hj. apply in_app_iff in Hj as [Hj | Hj].
    + destruct (Z.eqb_spec (re_eof e) 0) as [Heq|Hne]; [|destruct Hj].
      destruct Hj as [<- | []]. exists 0%nat. split; [cbn [length]; lia|]. split; [exact Heq | reflexivity].
    + destruct (IH hs j ltac:(cbn [length] in Hlen; lia) Hj) as (i & Hi & Heof & Hsl).
      exists (S i). split; [cbn [length]; lia|]. split; [exact Heof | exact Hsl].
Qed.
Lemma gp3_pick_none : forall es hs qs hs0 j, length hs = length es ->
  ~ In j (rig_slots (combine es hs)) -> gp3_pick es hs qs hs0 j = nth j hs0 None.
Proof.
  intros es hs qs hs0 j Hlen Hnin. unfold gp3_pick.
  destruct (find _ _) as [i|] eqn:Hf; [|reflexivity].
  exfalso. apply find_some in Hf as (Hseq & Hpred).
  apply andb_prop in Hpred as (Heof & Hsl).
  apply Z.eqb_eq in Heof. apply Nat.eqb_eq in Hsl. apply in_seq in Hseq.
  apply Hnin. rewrite <- Hsl. apply (gp3_slot_in es hs i); [exact Hlen | lia | exact Heof].
Qed.
Lemma gp3_pick_some : forall es hs qs hs0 i, (i < length es)%nat -> length hs = length es ->
  List.NoDup (rig_slots (combine es hs)) -> re_eof (nth i es gn_e0) = 0 ->
  gp3_pick es hs qs hs0 (snd (nth i hs gn_hj0)) = Some (snd (nth i qs gn_q0)).
Proof.
  intros es hs qs hs0 i Hi Hlen HND Heof. unfold gp3_pick.
  destruct (find _ _) as [i'|] eqn:Hf.
  - apply find_some in Hf as (Hseq & Hpred). apply andb_prop in Hpred as (Heof' & Hsl).
    apply Z.eqb_eq in Heof'. apply Nat.eqb_eq in Hsl. apply in_seq in Hseq.
    rewrite (gp3_slots_inj es hs i' i HND Hlen ltac:(lia) Hi Heof' Heof Hsl). reflexivity.
  - exfalso. assert (Hin : In i (seq 0 (length es))) by (apply in_seq; lia).
    pose proof (find_none _ _ Hf i Hin) as Hno. cbv beta in Hno.
    rewrite Heof, Nat.eqb_refl in Hno. discriminate.
Qed.


(* ------------------------------------------------------------------ the read-only bytes (rom_out at G_RIG) *)
(* G_RIG is its seven program ranges, then errno's four bytes *)
Definition gp3_G7 : list (Z * Z) :=
  [(rg_lock fr_RG, 12); (rg_s fr_RG, 4 * ASRC); (rg_client_broken fr_RG, 1); (rg_send_eintr fr_RG, 1);
   (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8)].
Lemma gp3_G_RIG : G_RIG B fr_RG = gp3_G7 ++ [(as_errno B, 4)].
Proof. reflexivity. Qed.
(* G_RIG lies in G_fr (GN_HG_RIG), so HRO's ROM bytes are off G_RIG; its other three clauses do not name G *)
Lemma gp3_rom_out : rom_out segs B (G_RIG B fr_RG).
Proof.
  intros a Hr. destruct (HRO a Hr) as (H1 & H2 & H3 & H4).
  split; [intros Hin; exact (H1 (HGRIG a Hin)) | split; [exact H2 | split; [exact H3 | exact H4]]].
Qed.

(* ------------------------------------------------------------------ the cells the callee does not touch *)
Lemma gp3_g4_cells : forall a, gp3_g4 a -> inG gn_cells a.
Proof.
  intros a H. unfold inG. apply Exists_exists.
  destruct H as [H | [H | [H | H]]];
    [exists ((rg_gone fr_RG, 1) : Z * Z) | exists ((AG_NFD, 4) : Z * Z) |
     exists ((AG_THREAD_UP, 1) : Z * Z) | exists ((AG_LISTEN, 4) : Z * Z)];
    (split; [unfold gn_cells; cbn [In]; repeat (first [left; reflexivity | right]) |
             unfold in_zr; cbn [fst snd]; lia]).
Qed.
Lemma gp3_wake_cell : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> inG gn_cells a.
Proof.
  intros a H. unfold inG. apply Exists_exists. exists ((rg_wake fr_RG + 4, 4) : Z * Z).
  split; [unfold gn_cells; cbn [In]; repeat (first [left; reflexivity | right]) |
          unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma gp3_not_RIG : forall a, ~ (as_errno B <= a < as_errno B + 4) ->
  gp3_g4 a \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> ~ inG (G_RIG B fr_RG) a.
Proof.
  intros a Herr H4 Hin. rewrite gp3_G_RIG in Hin. apply inG_app in Hin as [Hin | Hin].
  - unfold inG in Hin. apply Exists_exists in Hin as (r & Hr & Hz).
    unfold gp3_G7 in Hr. unfold gp3_g4, AG_NFD, AG_THREAD_UP, AG_LISTEN in H4.
    cbv [fr_RG fr_globals_b rg_gone rg_lock rg_s rg_client_broken rg_send_eintr rg_nout rg_capout rg_out
         rg_wake ASRC] in Hr, H4.
    cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|]).
    destruct Hr.
  - apply inG_cons in Hin as [Hz | Hin]; [unfold in_zr in Hz; cbn [fst snd] in Hz; exact (Herr Hz)|].
    exact (inG_nil a Hin).
Qed.
(* a callee-saved register across the call *)
Lemma gp3_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the view decides the byte *)
Lemma gp3_mbyte_of_view : forall (W W' : world segs) mem mem' a,
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> mbyte segs (arm W' mem') a = mbyte segs (arm W mem) a.
Proof.
  intros W W' mem mem' a H. unfold aview, arm in *.
  destruct (mbyte segs (mrestrict (w_H W') mem') a) as [b1|] eqn:E1;
    destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b2|] eqn:E2; cbn [option_map] in H;
    try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma gp3_vm_of_view : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v Hav Hv k Hk.
  rewrite (gp3_mbyte_of_view W W' mem mem' (a + Z.of_nat k) (Hav (a + Z.of_nat k) ltac:(lia))).
  exact (Hv k Hk).
Qed.
(* the jump table is read-only (W_LLVMFuzzerTestOneInput_gone_p5.v gp5_jt_in_rom, copied) *)
Definition gp3_inromb (a : Z) : bool :=
  existsb (fun sg => (negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) segs.
Lemma gp3_inromb_ok : forall a, gp3_inromb a = true -> in_rom segs a.
Proof.
  intros a H. unfold gp3_inromb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma gp3_jt_in_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof.
  intros a Ha. apply gp3_inromb_ok.
  assert (K : forallb (fun i => gp3_inromb (fr_jtab + Z.of_nat i)) (seq 0 36) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. replace a with (fr_jtab + Z.of_nat (Z.to_nat (a - fr_jtab))) by lia.
  apply K. apply in_seq. lia.
Qed.
Lemma gp3_jt_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HR HR' HJ i Hi.
  apply (gp3_vm_of_view W W' mem mem'); [|exact (HJ i Hi)].
  intros x Hx. assert (Hrx : in_rom segs x) by (apply gp3_jt_in_rom; cbn in Hx; lia).
  rewrite (HR' x Hrx), (HR x Hrx). reflexivity.
Qed.

(* ------------------------------------------------------------------ a slot's bytes: the struct, or a block *)
Lemma gp3_alist_split : forall ly S (W : world segs) mem LA l lines a,
  alist_at B ly S W mem LA l lines ->
  (exists r, In r (alist_fp LA l) /\ fst r <= a < snd r) ->
  LA <= a < LA + 16 \/ (exists b, In b (alist_blks l) /\ fst b <= a < fst b + snd b).
Proof.
  intros ly S W mem LA l lines a HL (r & Hin & Hr).
  pose proof HL as (_ & _ & _ & _ & _ & Hvec & _ & _ & HF).
  unfold alist_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Hr; lia|].
  right. apply in_app_iff in Hin as [Hin | Hin].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; [destruct Hin|].
    destruct Hin as [<- | []].
    destruct Hvec as [[Hc _] | (Hcp & Hinb & Hj & Hg)]; [lia|].
    exists ((hl_v l, AREC * hl_cap l) : Z * Z). split.
    + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
    + unfold gfp in Hr. cbn [fst snd] in Hr |- *.
      rewrite gk_bzs_len, length_app, gk_concat_len in Hr.
      unfold hl_n in Hj. unfold AREC in *. lia.
  - apply in_map_iff in Hin as (x & <- & Hx).
    exists ((fst x, Z.of_nat (length (snd x)) + 1) : Z * Z). split.
    + unfold alist_blks. apply in_app_iff. right. apply in_map_iff. exists x.
      split; [reflexivity | exact Hx].
    + unfold gfp in Hr. cbn [fst snd] in Hr |- *.
      rewrite gk_bzs_len, length_app in Hr. cbn [length] in Hr. lia.
Qed.
Lemma gp3_asrc_split : forall ly S (W : world segs) mem HA h a,
  asrc_at B ly S W mem HA h ->
  (exists r, In r (asrc_fp HA h) /\ fst r <= a < snd r) ->
  HA <= a < HA + ASRC \/ (exists b, In b (asrc_blks h) /\ fst b <= a < fst b + snd b).
Proof.
  intros ly S W mem HA h a HS (r & Hin & Hr).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  unfold asrc_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Hr; lia|].
  destruct Hin as [<- | Hin].
  - right. exists ((hs_partial h, APARTIAL) : Z * Z). split; [left; reflexivity|].
    unfold gfp in Hr. cbn [fst snd] in Hr |- *. rewrite gk_bzs_len, Hpj in Hr. lia.
  - apply in_app_iff in Hin as [Hin | Hin].
    + destruct (gp3_alist_split ly S W mem (HA + 16) (hs_pending h) false a Hpend
        (ex_intro _ r (conj Hin Hr))) as [Hhdr | (b & Hb & Hrb)]; [left; unfold ASRC in *; lia|].
      right. exists b. split; [|exact Hrb].
      unfold asrc_blks. right. apply in_app_iff. left. exact Hb.
    + apply in_app_iff in Hin as [Hin | Hin].
      * destruct (gp3_alist_split ly S W mem (HA + 64) (hs_expected h) true a Hexp
          (ex_intro _ r (conj Hin Hr))) as [Hhdr | (b & Hb & Hrb)]; [left; unfold ASRC in *; lia|].
        right. exists b. split; [|exact Hrb].
        unfold asrc_blks. right. apply in_app_iff. right. apply in_app_iff. left. exact Hb.
      * destruct (gp3_alist_split ly S W mem (HA + 80) (hs_held h) true a Hheld
          (ex_intro _ r (conj Hin Hr))) as [Hhdr | (b & Hb & Hrb)]; [left; unfold ASRC in *; lia|].
        right. exists b. split; [|exact Hrb].
        unfold asrc_blks. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
Qed.
Lemma gp3_slot_kept : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' i o,
  AR segs B ly S W mem md -> aslot B ly S W mem i o -> (i < 4)%nat ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (slot_blks o) -> In b (ablocks B ly' S') /\
     (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  aslot B ly' S' W' mem' i o.
Proof.
  intros ly S W mem md ly' S' W' mem' i o HAR Hs Hi KG KB.
  destruct o as [h|]; cbn [aslot slot_blks] in *.
  - apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ h Hs).
    + intros r Hr a Ha.
      destruct (gp3_asrc_split ly S W mem _ h a Hs (ex_intro _ r (conj Hr Ha)))
        as [Hin | (b & Hb & Hrb)]; [apply KG; exact Hin | exact (proj2 (KB b Hb) a Hrb)].
    + intros b Hb. exact (proj1 (KB b Hb)).
  - destruct Hs as [Hz Hw]. split.
    + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
      apply KG. unfold ASRC in *. lia.
    + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KG. lia.
Qed.
(* a closed slot's 4-byte fields read 0 *)
Lemma gp3_le_byte0 : forall w k, le_byte 0 w k = 0.
Proof.
  intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma gp3_closed_field : forall (W : world segs) mem HA off,
  garr8 segs (arm W mem) HA (repeat 0 (Z.to_nat ASRC)) -> 0 <= off -> off + 4 <= ASRC ->
  val_mem segs (arm W mem) (HA + off) 4 0.
Proof.
  intros W mem HA off Hz Hoff Hoff4 kk Hkk.
  destruct (Hz (Z.to_nat (off + Z.of_nat kk))
    ltac:(rewrite repeat_length; unfold ASRC in *; lia)) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
  replace (HA + off + Z.of_nat kk) with (HA + Z.of_nat (Z.to_nat (off + Z.of_nat kk)) + Z.of_nat 0) by lia.
  rewrite Hv, !gp3_le_byte0. reflexivity.
Qed.
(* errno is apart from the four cells: they are cells of gn_cells (GN_CELLS_ERRNO); A's GP3_ERRNO_APART's first half,
   derived as A's composition derives gx_errno_apart *)
Lemma gp3_errno_g4 : forall a, gp3_g4 a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a H. exact (HCE a (gp3_g4_cells a H)). Qed.
(* relay_instance_gone's aothers_at: the other three slots are closed or carry another fd (B's aothers_at compares
   the low 32 bits, W_contract.v:969; both fds are below 2 ^ 31, asrc_at) *)
Lemma gp3_others : forall cx t m ly S (W : world segs) mem (j : nat) (h : hsrc),
  RINV cx t m -> amodel_at B ly S W mem m -> (j < 4)%nat ->
  nth j (lm_hs m) None = Some h -> aothers_at (PI := PB_fr) fr_RG W mem j (hs_fd h).
Proof.
  intros cx t m ly S W mem j h HRI HMOD Hj Hnth i Hi Hij.
  destruct HMOD as (_ & HSLOT & _).
  pose proof (HSLOT j Hj) as Hslj. unfold aslot in Hslj. rewrite Hnth in Hslj.
  pose proof Hslj as (_ & _ & _ & _ & _ & _ & _ & _ & Hfdj & _).
  pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl.
  destruct (nth i (lm_hs m) None) as [h'|] eqn:Ei.
  - exists (hs_fd h'), (hs_open h').
    pose proof Hsl as (Hfd & Hopen & _ & _ & _ & _ & _ & Hop1 & Hfdi & _).
    split; [exact Hfd|]. split; [exact Hopen|].
    right. rewrite !Z.mod_small by lia. exact (HFDS cx t m i j h' h HRI Hi Hj Hij Ei Hnth).
  - exists 0, 0. destruct Hsl as [Hz _].
    split.
    { pose proof (gp3_closed_field W mem (rg_s fr_RG + ASRC * Z.of_nat i) 0 Hz ltac:(lia)
        ltac:(unfold ASRC; lia)) as HH. rewrite Z.add_0_r in HH. exact HH. }
    split; [|left; reflexivity].
    exact (gp3_closed_field W mem (rg_s fr_RG + ASRC * Z.of_nat i) 4 Hz ltac:(lia)
      ltac:(unfold ASRC; lia)).
Qed.
(* the id byte is in range *)
Lemma gp3_id_rng : forall cx m, - 2 ^ 31 <= gn_id cx m < 2 ^ 31.
Proof.
  intros cx m. unfold gn_id. destruct (gn_more cx m); [|lia].
  unfold in_byte. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (lm_k m + 1)) (c_pl cx) (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. lia.
Qed.

(* ------------------------------------------------------------------ the entry states of the two runs *)
(* 0x84b40: the frame cell F+24 (s1 + 24) is the run's one store, a window of its own; every other frame byte is
   kept by the run's frame_of *)
Definition gp3_extra : list word := map (Z_to_bv 64) [SB].
Definition gp3_frR : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition gp3_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0) ] [] [].
Definition gp3_facts2 : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp3a : sstate := mkSS AF_gn_rig sr_atoms [gp3_frR] None gp3_facts.
Definition ss_gp3b : sstate := mkSS AF_gp3_ret sr_atoms [] None gp3_facts2.
Definition gp3_Bx : sv := SOff 32 0.
Definition gp3_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma gp3_entry : forall (W : world segs) regs mem F,
  getr regs 9 = w64 F -> 2 ^ 46 <= F -> F + 32 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 32 ->
  st_ok_pi segs VAL (Eimg (Ereg regs gp3_extra)) ss_gp3a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_rig)) mem (seg_rom segs)))
  /\ sh_ok segs gp3_Bx [] (Eimg (Ereg regs gp3_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F R9 HF1 HF2 HF32 HFw. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs gp3_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E9 : ew E 9 = getr regs 9)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp3a. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + constructor; [|constructor]. unfold region_ok, gp3_frR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia | constructor].
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma gp3_entry2 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs gp3_extra)) ss_gp3b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gp3_ret)) mem (seg_rom segs)))
  /\ sh_ok segs gp3_Bx [] (Eimg (Ereg regs gp3_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs gp3_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_gp3b. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp3_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* the first run's write obligation: the window F+24 .. F+32 is in the function's own stack window *)
Local Ltac gp3_awr U9 :=
  cbn [ss_mem ss_gp3a];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [gp3_frR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?U9 in Ha;
      left; split; [left; unfold LLVMF_STK in *; lia | lia]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside F+24 .. F+32 is outside the first run's writable window *)
Local Ltac gp3_nowr U9 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem ss_gp3a In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [gp3_frR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

(* ------------------------------------------------------------------ the frame and the input, kept *)
(* B's gframe (no `full` flag): the saved registers, the frame's window, 14 slots F+32 .. F+184, the fake frame's
   three header words and window, its shadow and the shadow's window *)
Lemma gp3_gframe_kept : forall cx sh FF (W W' : world segs) mem mem',
  gframe cx sh FF W mem -> length sh = 16%nat -> lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  gframe cx sh FF W' mem'.
Proof.
  intros cx sh FF W W' mem mem' HF Hlen Hsp KS KF KH.
  destruct HF as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
    H17 & H18 & H19 & H20 & H21 & H22).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (H1 o r Hin)].
    assert (Ho : 8 <= o <= 104).
    { unfold saved_regs in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Heq | Hin]; [injection Heq as <- _; lia|]). destruct Hin. }
    intros x Hx. apply KS. lia. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KS; lia | exact H2]|].
  do 14 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KS; lia | assumption]|]).
  do 3 (split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact H20]|].
  split; [apply (akept_garr8 W mem); [intros x Hx; rewrite Hlen in Hx; apply KH; cbn in Hx; lia | exact H21]|].
  apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact H22].
Qed.
(* the same across the first run, whose one store F+24 .. F+32 is none of gframe's cells; the frame's window stays
   writable (the run only grows the memory) *)
Lemma gp3_gframe_st : forall cx sh FF (W : world segs) mem mem',
  gframe cx sh FF W mem -> length sh = 16%nat -> lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx + 32 <= a < spZ (c_regs cx) -> abyte_kept W mem W mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  gframe cx sh FF W mem'.
Proof.
  intros cx sh FF W mem mem' HF Hlen Hsp KS KF KH WK.
  destruct HF as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
    H17 & H18 & H19 & H20 & H21 & H22).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W mem mem'); [|exact (H1 o r Hin)].
    assert (Ho : 8 <= o <= 104).
    { unfold saved_regs in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Heq | Hin]; [injection Heq as <- _; lia|]). destruct Hin. }
    intros x Hx. apply KS. lia. }
  split; [intros i Hi; apply WK; exact (H2 i Hi)|].
  do 14 (split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KS; lia | assumption]|]).
  do 3 (split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KF; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact H20]|].
  split; [apply (akept_garr8 W mem); [intros x Hx; rewrite Hlen in Hx; apply KH; cbn in Hx; lia | exact H21]|].
  apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact H22].
Qed.
Lemma gp3_ainput_kept : forall cx ly S (W : world segs) mem ly' S' (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S') /\
     (forall a, c_p cx <= a < c_p cx + c_n cx -> abyte_kept W mem W' mem' a)) ->
  ainput_at B cx ly' S' W' mem'.
Proof.
  intros cx ly S W mem ly' S' W' mem' (Hblk & Hg) Hlen K.
  destruct Hblk as [(Hn & Hp) | (Hn & Hin)].
  - split; [left; split; assumption|]. apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. rewrite length_map in Hx. lia.
  - destruct (K ltac:(lia)) as (Hin' & KB). split; [right; split; [lia | exact Hin']|].
    apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite length_map in Hx. apply KB. lia.
Qed.
(* a concrete register is callee-saved (B's latch walk lt_cs) *)
Ltac gp3_csd := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; clear; lia.

(* the registers the first run does not write (a0 and ra) *)
Definition gp3_kept : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29;
   30; 31]%bv.
(* the registers the four instructions after the call do not write (a0, s4, s5, s6) *)
Definition gp3_kept2 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 23; 24; 25; 26; 27; 28; 29;
   30; 31]%bv.

(* the callee's afn_pre at sp = F: _gone_base.v's gn_afn_pre, with the chain's spine (empty, or the entry's return
   RA_LLVMF) and the room above sp that rig_spec's caller-context premise names (image A's gp3_afn_pre,
   95cae0d4740) *)
Lemma gp3_afn_pre : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [YCfn.RA_LLVMF]) /\
    spZ regs + 16 < ly_top ly3.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = YCfn.RA_LLVMF) by (unfold fr_lib_pre_cf in HPRE; tauto).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity
                     | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists []. split; [| split; [left; reflexivity | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Lemma gp3_rig_c1 : forall cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GRG B G_fr fr_FP LS RINV cx t m W c ->
  SRr segs W c (fun W' c' => exists m1, GC1 B MT G_fr fr_FP LS RINV cx t m m1 0%nat W' c').
Proof.
  intros cx t m W c HB HRG.
  destruct HRG as (regs & mem0 & md & ly3 & S3 & kk & fpos & -> &
    ((HJ0 & HFR0 & HFLAG0 & H16_0 & H144_0 & H88_0 & HIN0 & HRV0 & HJT0) & HMOD0 & HSEP) & HLS & HRI & HOP &
    HKR & R26 & R21 & HREADS0 & HAWR0 & HAT0 & HPFX0).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly3 S3 W mem0 md kk
    fpos HB HJ0 eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hspr & HFm32 & HFr & HFF0 & HFF1 & HFFapp & Hfrs & HAR0).
  destruct HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof YM05.alloc_ceiling_value as AC.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx)
    by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf in HPRE0; symmetry; tauto).
  destruct ERRNO_LOW as (HE0 & HE1).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  (* ---- 0x84b40-0x84b48: sd s10,24(s1); mv a0,s5; jal relay_instance_gone ---- *)
  assert (HFw32 : awr W mem0 (lf_F cx) 32).
  { intros i Hi. pose proof HFR0 as (_ & HFW0 & _). apply HFW0. lia. }
  destruct (gp3_entry W regs mem0 (lf_F cx) R9 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HFm32 HFw32)
    as [HS SHOK].
  remember (Eimg (Ereg regs gp3_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp3_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = Z_to_bv 64 (gn_id cx m)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl). exact R26. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)).
  pose (RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 []).
  paj_run_to_tok RUNTO HS HJ0 SHOK gp3_span AF_fr_relay_instance_gone.
  { gp3_awr U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFRr end.
  (* the run's one store: F+24 := HI_G_NOUT; every other byte kept, every writable byte still writable *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem0 a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFRr a Ha); gp3_nowr U9).
  assert (WK : forall a, writable_at segs (arm W mem0) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem0 (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows _ _ _ _ HGr Hp). }
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (KLO : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha; apply KEEP0; unfold GK_CEIL8 in *; lia).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SV24 : sv8 W (ms_mem ms) (lf_F cx + 24) HI_G_NOUT).
  { unfold sv8.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 24 8%N (SOff 26 0) HI_G_NOUT RG0) end.
    - exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold HI_G_NOUT. zside.
    - zside. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs gp3_extra gp3_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  set (mem := ms_mem ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  rename HJ0 into HJ.
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly3 S3 W mem mdc kk
    fpos HB HJ eq_refl) as NUMS2.
  cbv zeta in NUMS2. destruct NUMS2 as (_ & _ & _ & _ & _ & _ & _ & _ & HAR).
  (* ---- the cut point's facts at the call's entry ---- *)
  assert (HFR : gframe cx fake_shadow_open (frame_addr ly3 1 fpos) W mem).
  { apply (gp3_gframe_st cx _ _ W mem0 mem HFR0 eq_refl); [lia | | | | exact WK].
    - intros a Ha. apply KEEP0; lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8. lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8, SB in *. lia. }
  assert (HFLAG : sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KLO; unfold GK_CEIL8; lia | exact HFLAG0]).
  assert (H16 : sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H16_0]).
  assert (H144 : sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H144_0]).
  assert (H88 : sv8 W mem (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H88_0]).
  pose proof (gk_ainput_kept B LAWS cx ly3 S3 W mem0 md W mem HAR0 HIN0 HlenP KLO) as HIN.
  pose proof (gk_rom_kept W W mem0 mem HRV0 KLO) as HRV.
  pose proof (gk_jt_kept W W mem0 mem HJT0 KLO) as HJT.
  pose proof (gk_amodel_kept B LAWS ly3 S3 W mem0 md W mem m HAR0 HMOD0 HE0 ltac:(unfold GK_CEIL8; lia) KLO)
    as HMOD.
  assert (HREADS : forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem0); [|exact (HREADS0 j Hj)].
    intros x Hx. apply KEEP0; cbn in Hx; lia. }
  assert (HAWR : awr W mem (lf_F cx + 192) 16)
    by (apply (akept_awr W mem0); [intros x Hx; apply KEEP0; lia | exact HAWR0]).
  assert (HAT : sv8 W mem (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact HAT0]).
  assert (HPFX : gn_prefix_at cx m W mem (frame_addr ly3 1 fpos)).
  { destruct HPFX0 as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + i) ltac:(unfold GK_CEIL8; lia)));
            exact (P1 i Hi)|].
    split; [rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m)))
              ltac:(unfold GK_CEIL8; lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KLO a ltac:(unfold GK_CEIL8; lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  clear K1 KEEP0 KLO WK RG0 HFRr HGr.
  (* LS_cnt's msz_ok guard and gdone's msz_ok conjunct, from the model at GRG *)
  pose proof (gn_msz_ok B ly3 S3 W mem m HMOD) as HMSZ.
  pose proof HMOD as (HM4 & HSLOT & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDR & HTU &
    HLST & HLSTW).
  destruct (HPAIRS cx t m HRI) as (hs & HPOK).
  pose proof HPOK as (HLENhs & HFORALL & HNODUP).
  pose proof (proj1 (NoDup_ListNoDup _) HNODUP) as HNDl.
  assert (HPOKi : forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
      gn_pair_ok m (nth i (lm_es m) gn_e0) (nth i hs gn_hj0)).
  { intros i Hi Heof.
    assert (Hini : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)).
    { apply nth_In. rewrite length_combine. lia. }
    pose proof (proj1 (Forall_forall _ _) HFORALL _ Hini) as POK.
    rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in POK.
    cbn [fst snd] in POK. exact (POK Heof). }
  assert (HJS4 : forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat).
  { intros j Hj. apply in_concat in Hj as (l & Hl & Hjl).
    apply in_map_iff in Hl as (p & <- & Hp).
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Heq|Hne]; [|destruct Hjl].
    destruct Hjl as [<- | []].
    exact (proj1 (proj1 (Forall_forall _ _) HFORALL p Hp Heq)). }
  pose proof (gp3_perm_slots (lm_hs m) (rig_slots (combine (lm_es m) hs)) HM4 HNDl HJS4) as HPS.
  assert (HSRCS : concat (map (fun j => slot_blks (nth j (lm_hs m) None))
      (rig_slots (combine (lm_es m) hs))) = rig_srcs (combine (lm_es m) hs)).
  { apply (gp3_srcs_of_slots _ (lm_es m) hs HLENhs).
    intros i Hi Heof. destruct (HPOKi i Hi Heof) as (_ & Hnth & _).
    rewrite Hnth. reflexivity. }
  rewrite HSRCS in HPS.
  destruct HSEP as ((rest0 & HPERM0) & HSEPFP).
  set (OTH := concat (map (fun j => slot_blks (nth j (lm_hs m) None))
    (gp3_cs (rig_slots (combine (lm_es m) hs))))) in *.
  assert (HPERM1 : Permutation (ablocks B ly3 S3)
    ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ rig_srcs (combine (lm_es m) hs) ++
     aout_blks (lm_cap m) (lm_out m) ++ (OTH ++ input_blks cx ++ rest0))).
  { eapply Permutation_trans; [exact HPERM0|]. unfold model_blks.
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (lm_es m)))
         (aout_blks (lm_cap m) (lm_out m)) rest0 _ _ (lm_G m, ATABLE) HPS)|].
    apply gp3_perm_pre. }
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  destruct (gp3_afn_pre cx ly3 S3 fpos kk W mem mdc
    (ms_regs ms) RIG_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia)
    ltac:(unfold RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc & HSPINE & HTOP).
  (* GN_LS_rig's premises at GRG: gn_op (HOP), aentry_ok's |re_U| <= APARTIAL, the model blocks' sizes not negative
     (the AR block law over ablocks_sep's Permutation HPERM0), every open source's pending offset (asrc_at), and the
     entry pre's CAPOUT clause (fr_lib_pre_cf, its last conjunct); A f5d40188e29 *)
  pose proof HOP as (_ & HO0 & Ht0 & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAE & _).
    rewrite Forall_forall in GdAE |- *. intros ge gHe.
    destruct (GdAE ge gHe) as (_ & _ & _ & _ & _ & _ & GdC7 & GdC8 & _). lia. }
  assert (HMpos : forall b, In b (model_blks m) -> 0 <= snd b).
  { intros [gp gn] gHb. assert (gHin : In (gp, gn) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPERM0)). apply in_or_app. right. apply in_or_app. left. exact gHb. }
    destruct (gk_blk B LAWS ly3 S3 W mem mdc gp gn HAR gHin) as (_ & _ & GdN). cbn [snd]. lia. }
  assert (Hoff : forall k h, nth k (lm_hs m) None = Some h ->
      (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
      (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))).
  { intros gk gh gHk.
    assert (gHl : (gk < 4)%nat).
    { destruct (Nat.lt_ge_cases gk (length (lm_hs m))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in gHk by exact Hge. discriminate gHk. }
    pose proof (HSLOT gk gHl) as GdSl. unfold aslot in GdSl. rewrite gHk in GdSl.
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdOFF & _). exact GdOFF. }
  assert (HCAPO : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
  { pose proof HB as (_ & GdPRE). unfold fr_lib_pre_cf in GdPRE.
    repeat match type of GdPRE with _ /\ _ => destruct GdPRE as (_ & GdPRE) end. exact GdPRE. }
  pose proof (HLSRIG cx t m ly3 S3 hs HLS HRI HPOK HOP HUs HMpos Hoff HCAPO) as BUD. cbv zeta in BUD.
  destruct BUD as (Btr1 & Btr2 & Btr3 & _).
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_relay_instance_gone) (ms_regs ms) mem mdc) _).
  { apply (RIG W ly3 S3 (ms_regs ms) mem mdc ch (lm_G m) (gn_id cx m) (lm_es m) hs
      (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)).
    - exact HPREc.
    - rewrite Hsp1. exact HFm32.
    - rewrite Hfrs. change (count_cid 1 [(1, fpos)]) with 1. change (fs_frames 1) with 8192. lia.
    - exact RGP.
    - rewrite Q10, E21. reflexivity.
    - exact (gp3_id_rng cx m).
    - exact HLOCK.
    - exact HREL.
    - exact HOUT.
    - exact HRV.
    - exact HLENhs.
    - apply Forall_forall. intros p Hp Heof.
      apply (In_nth _ _ (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
      rewrite length_combine in Hi. rewrite <- Hpi in Heof |- *.
      rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in Heof |- *.
      cbn [fst snd] in Heof |- *.
      destruct (HPOKi i ltac:(lia) Heof) as (Hj4 & Hnth & Hfd & Hskip & HU & Hps1 & Hps2 & Hps3).
      split; [exact Hj4|]. split.
      + pose proof (HSLOT (snd (nth i hs gn_hj0)) Hj4) as Hsl.
        unfold aslot in Hsl. rewrite Hnth in Hsl. exact Hsl.
      + split.
        * rewrite <- Hfd. exact (gp3_others cx t m ly3 S3 W mem _ (fst (nth i hs gn_hj0)) HRI HMOD Hj4 Hnth).
        * split; [exact Hfd|]. split; [exact Hskip|]. split; [exact HU|].
          split; [exact Hps1|]. split; [exact Hps2 | exact Hps3].
    - exact HNODUP.
    - exists (OTH ++ input_blks cx ++ rest0). exact HPERM1.
    - exact Btr1.
    - exact Btr2.
    - exact Btr3.
    - (* rig_spec's room above sp: from the entry's astk_ok through the journal's layout *)
      exact HTOP.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82fb8; 0x84b4c(; 0x82240)]: relay_instance_gone's free
         returns to pc + 792 = 0x82fb8, relay_instance_gone to AF_gp3_ret = 0x84b4c, LLVMFuzzerTestOneInput to
         RA_LLVMF = 0x82240 when its record is on the chain *)
      destruct HSPINE as [Hsc | Hsc]; rewrite Hsc; unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        vm_compute; repeat (first [left; reflexivity | right]). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 c2 Hwle2 HPOST.
  destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & k4 & qs & c4 & O4 & cap4 & out4 & rest4 & -> &
    HJc & HPRES & HAPK & HMO & HLOCK4 & HRREL & HLENq & HREL4 & HOUT4 & HSRC4 & HKEEPS & HPERMa & HPERMb).
  rewrite Hsp1 in HJc. clear HCALL.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  (* ---- what relay_instance_gone's journal keeps ---- *)
  destruct (gp3_keeps (G_RIG B fr_RG) RIG_STK (lf_F cx)
    (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4 HJc)
    as (KHI & KBLKv & KFRMv & KIMGv & KPRESc & HAR4 & Hfrs4 & HLY & Hwle4).
  cbn [app] in Hfrs4.
  assert (HFFeq : frame_addr ly4 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (HFLeq : flag_addr ly4 1 fpos = flag_addr ly3 1 fpos).
  { unfold flag_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin1' : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  assert (HAsub : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMa)).
    rewrite <- gp3_assoc4. apply in_app_iff. left. exact Hb. }
  assert (HMODBLK : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b [<- | Hb]; [left; reflexivity|]. unfold model_blks. right.
    apply in_app_iff in Hb as [Hb | Hb]; [apply in_app_iff; left; exact Hb|].
    apply in_app_iff. right. apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym HPS)). apply in_app_iff. left. exact Hb.
    - apply in_app_iff. right. exact Hb. }
  assert (HFPS : forall a, fp_spares (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
    by exact (gp3_fp_spares ly3 S3 W mem mdc _ HAR HAsub).
  assert (HAPART : forall b a, In b rest4 -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
  { intros b a Hb Hr Hin. apply gp3_inFP_fp in Hin as (b' & Hb' & Hr').
    refine (gp3_apart ly3 S3 W mem mdc _ _ b' b a HAR _ Hb' Hb Hr' Hr).
    rewrite gp3_assoc4. exact HPERMa. }
  assert (HNGblk : forall b a, In b (ablocks B ly3 S3) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inG (G_RIG B fr_RG) a).
  { intros [p n] a Hb Hr HinG. cbn [fst snd] in Hr.
    exact (blk_img segs B LAWS ly3 S3 W mem mdc p n a HAR Hb Hr (proj1 (HG a (HGRIG a HinG)))). }
  (* ---- the callee's journal inside the arm's (W_journal.v ajournal_gx_sub) ---- *)
  assert (HFP1 : forall a, inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Hin. apply gp3_inFP_fp in Hin as (b & Hb & Hr).
    destruct (gn_sep_req B fr_FP cx m ly3 S3 (conj (ex_intro _ rest0 HPERM0) HSEPFP) b (HMODBLK b Hb))
      as [Hnew | Hfp].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing.
      split; [exact (HAsub b Hb)|]. split; [exact Hnew | exact Hr].
    - left. split; [exact (Hfp a Hr)|].
      exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact (HAsub b Hb) | exact Hr]. }
  assert (HJcG : ajournal_gx segs B G_fr 0 [] RIG_STK (lf_F cx)
      (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4).
  { apply (ajournal_gx_G_mono segs B (G_RIG B fr_RG) G_fr); [exact HGRIG | exact HJc]. }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk
     RIG_STK (lf_F cx) 0 [] (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) [] ly4 S4 W2 mem4 md4 k4
     HJ HJcG
     ltac:(unfold RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK in *; lia)
     ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
     HG HFP1) as HJ2.
  cbn [app] in HJ2.
  destruct (gp3_keeps G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W2 mem4 md4 (kk + k4) HJ2) as (_ & _ & _ & _ & KPRES2 & _).
  (* ---- the bytes the cut reads, kept across the call ---- *)
  assert (KSTKv : forall a, lf_F cx <= a < 2 ^ 64 ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KHI; [lia | | lia | lia].
    intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). lia. }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. split; [apply KSTKv; lia|]. intros _.
    apply gp3_wr_pres. apply KPRES2. unfold LLVMF_STK in *. lia. }
  assert (KFRM : forall a, frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
      by exact (gp3_not_fp_frame ly3 S3 W mem mdc _ 1 fpos a HAR HAsub Hin1
                  ltac:(change (fs_frame_bytes 1) with 128; lia)).
    split.
    - apply (KFRMv 1 fpos a Hin1);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
        | exact HNF | lia |].
      intros HinG. exact (frm_img segs B LAWS ly3 S3 W mem mdc 1 fpos a HAR Hin1
        ltac:(change (fs_frame_bytes 1) with 128; lia) (proj1 (HG a (HGRIG a HinG)))).
    - intros _. apply gp3_wr_pres.
      destruct (al_frames _ _ LAWS ly4 S4 W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & Hb & _).
      rewrite HFFeq in Hb. exact (proj1 (Hb a ltac:(change (fs_frame_bytes 1) with 128; lia))). }
  assert (KSH : forall a, SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
    { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      rewrite <- SB_SHADOW_OFF. lia. }
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
    { apply (gp3_not_fp_shadow ly3 S3 W mem mdc _ a HAR HAsub).
      unfold SB, kLowShadowBeg, kHighMemBeg in *. lia. }
    split.
    - apply (KFRMv 1 fpos a Hin1); [right; exact Hsh | exact HNF | unfold SB in *; lia |].
      intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). unfold SB in *. lia.
    - intros _. apply gp3_wr_pres.
      destruct (al_frames _ _ LAWS ly4 S4 W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & _ & Hsh4).
      rewrite HFFeq in Hsh4.
      assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 1 fpos) < fs_frame_bytes 1 / 8)
        by (unfold in_zr in Hsh; cbn [fst snd] in Hsh; lia).
      specialize (Hsh4 _ Hi).
      replace (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) with a
        in Hsh4 by lia.
      exact (proj1 Hsh4). }
  pose proof RGP as (_ & _ & _ & _ & _ & _ & RGP7 & _).
  assert (KIMG : forall a, inG gn_cells a -> ~ inG (G_RIG B fr_RG) a ->
      ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W2 mem4 a).
  { intros a Hc HnR Herr. pose proof (HGCELLS a Hc) as Hfr. destruct (HG a Hfr) as (Himg & Hown & _).
    split; [|intros _; exact (GWR _ _ a Hfr)].
    apply KIMGv; [exact Himg | exact Hown | exact Herr | apply HFPS | | exact HnR].
    pose proof (pa_img_range a Himg). lia. }
  assert (KG4 : forall a, gp3_g4 a -> abyte_kept W mem W2 mem4 a).
  { intros a H4. pose proof (gp3_errno_g4 a H4) as Herr.
    exact (KIMG a (gp3_g4_cells a H4) (gp3_not_RIG a Herr (or_introl H4)) Herr). }
  assert (KWAKE : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. pose proof (RGP7 a ltac:(unfold rg_rng; right; right; right; left; exact Ha)) as (_ & _ & Herr).
    exact (KIMG a (gp3_wake_cell a Ha) (gp3_not_RIG a Herr (or_intror Ha)) Herr). }
  assert (Hrest : Permutation rest4 (OTH ++ input_blks cx ++ rest0)).
  { apply (Permutation_app_inv_l ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m))).
    rewrite !gp3_assoc4. exact (Permutation_trans (Permutation_sym HPERMa) HPERM1). }
  assert (Hrest4 : forall b, In b rest4 -> In b (ablocks B ly4 S4)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMb)).
    right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
  assert (KBLK : forall b a, In b rest4 -> In b (ablocks B ly3 S3) ->
      fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W2 mem4 a).
  { intros b a Hb Hb3 Hr. pose proof (Hrest4 b Hb) as Hb4.
    pose proof (HAPART b a Hb Hr) as HNF. pose proof (HNGblk b a Hb3 Hr) as HNR.
    destruct b as [p n]. cbn [fst snd] in Hr.
    destruct (gk_blk B LAWS ly3 S3 W mem mdc p n HAR Hb3) as (P1 & P2 & P3).
    split.
    - replace a with (p + (a - p)) by lia.
      apply (KBLKv p n (a - p) Hb3 Hb4); [lia | | lia |];
        replace (p + (a - p)) with a by lia; assumption.
    - intros _. apply gp3_wr_pres.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (al_blocks _ _ LAWS ly4 S4 W2 mem4 md4 p n HAR4 Hb4))))) a Hr)). }
  (* ---- the model after the call ---- *)
  set (js := rig_slots (combine (lm_es m) hs)) in *.
  set (hs1 := map (gp3_pick (lm_es m) hs qs (lm_hs m)) (seq 0 4)).
  set (m1 := LM (gn_kq cx m) hs1 (lm_G m) (map fst qs) c4 O4 (lm_mx m) cap4 out4 (lm_gn m) (lm_nfd m)).
  assert (Hhs1 : forall j, (j < 4)%nat -> nth j hs1 None = gp3_pick (lm_es m) hs qs (lm_hs m) j)
    by (intros j Hj; exact (gp3_nth_map4 _ None j Hj)).
  assert (Hlen1 : length hs1 = 4%nat) by (unfold hs1; rewrite length_map, length_seq; reflexivity).
  assert (HAFTER : gn_after_rig cx m hs qs c4 O4 cap4 out4 m1).
  { unfold gn_after_rig, m1. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    do 10 (split; [reflexivity|]). split; [exact Hlen1|]. split.
    - intros j Hj Hnin. rewrite (Hhs1 j Hj). exact (gp3_pick_none _ _ _ _ j HLENhs Hnin).
    - intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4). exact (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). }
  assert (HMOD1 : amodel_at B ly4 S4 W2 mem4 m1).
  { unfold amodel_at, m1. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hlen1|].
    split.
    { intros i Hi. rewrite (Hhs1 i Hi).
      destruct (in_dec Nat.eq_dec i js) as [Hdr | Hnd].
      - destruct (gp3_in_slots_find (lm_es m) hs i HLENhs Hdr) as (i0 & Hi0 & Heof0 & Hsl0).
        subst i. rewrite (gp3_pick_some (lm_es m) hs qs (lm_hs m) i0 Hi0 HLENhs HNDl Heof0).
        exact (HSRC4 i0 Hi0 Heof0).
      - rewrite (gp3_pick_none (lm_es m) hs qs (lm_hs m) i HLENhs Hnd).
        apply (gp3_slot_kept ly3 S3 W mem mdc ly4 S4 W2 mem4 i _ HAR (HSLOT i Hi) Hi).
        + intros a Ha. apply HKEEPS; [unfold ASRC in *; lia|].
          intros j Hj Hrj.
          assert (Hji : j <> i) by (intros ->; exact (Hnd Hj)).
          pose proof (HJS4 j Hj) as Hj4.
          assert (HZ : Z.of_nat j <> Z.of_nat i) by (intros Heq; apply Hji; lia).
          unfold ASRC in *. lia.
        + intros b Hb.
          assert (HbO : In b OTH).
          { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
            apply in_map_iff. exists i. split; [reflexivity | apply gp3_cs_spec; split; [exact Hi | exact Hnd]]. }
          assert (Hbr : In b rest4)
            by (apply (Permutation_in _ (Permutation_sym Hrest)); apply in_app_iff; left; exact HbO).
          assert (Hb3 : In b (ablocks B ly3 S3)).
          { destruct (nth i (lm_hs m) None) as [h|] eqn:Ei; [|destruct Hb].
            pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl. rewrite Ei in Hsl.
            exact (proj2 (gk_asrc B LAWS ly3 S3 W mem mdc _ h HAR Hsl
              ltac:(unfold fr_RG; cbn; unfold ASRC; lia)
              ltac:(unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia)) b Hb). }
          split; [exact (Hrest4 b Hbr)|].
          intros a Ha. apply (KBLK b a Hbr Hb3). destruct b as [p n]. cbn [fst snd] in *.
          destruct (gk_blk B LAWS ly3 S3 W mem mdc p n HAR Hb3) as (_ & _ & Hn). lia. }
    split; [exact HREL4|].
    split; [exact HOUT4|].
    split.
    { apply (agone_at_kept fr_RG W mem W2 mem4 _ HGONE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KG4. unfold gp3_g4. lia. }
    split; [exact HLOCK4|].
    split.
    { apply (awake_at_kept fr_RG W mem W2 mem4 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KWAKE. lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HNFDW]|].
    split; [exact HNFDR|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HTU]|].
    split; [destruct HLST as [lst Hlst]; exists lst;
            apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HLSTW]. }
  (* the live blocks after the call: the model's, the input, and the same rest *)
  assert (HP1 : Permutation (ablocks B ly4 S4) (input_blks cx ++ model_blks m1 ++ rest0)).
  { assert (HOTH1 : concat (map (fun j => slot_blks (nth j hs1 None)) (gp3_cs js)) = OTH).
    { unfold OTH. f_equal. apply map_ext_in. intros j Hj. apply gp3_cs_spec in Hj as [Hj4 Hnin].
      rewrite (Hhs1 j Hj4), (gp3_pick_none _ _ _ _ j HLENhs Hnin). reflexivity. }
    assert (HNEW : concat (map (fun j => slot_blks (nth j hs1 None)) js) =
        concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
           (combine (combine (lm_es m) hs) qs))).
    { apply (gp3_newsrcs_of_slots _ (lm_es m) hs qs HLENhs HLENq).
      intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4), (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). reflexivity. }
    pose proof (gp3_perm_slots hs1 js Hlen1 HNDl HJS4) as HPS1.
    rewrite HNEW, HOTH1 in HPS1.
    eapply Permutation_trans; [exact HPERMb|].
    eapply Permutation_trans.
    { apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      exact Hrest. }
    apply Permutation_sym. unfold model_blks, m1. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (map fst qs)))
         (aout_blks cap4 out4) rest0 _ _ (lm_G m, ATABLE) HPS1)|].
    apply gp3_perm_pre. }
  assert (HSEP1 : ablocks_sep B fr_FP cx m1 ly4 S4).
  { split; [exists rest0; exact HP1|].
    intros b Hb.
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnent]; [|left; exact Hnent].
    assert (Hb4 : In b (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    destruct (in_dec DEC b (ablocks B ly3 S3)) as [Hb3 | Hnb3].
    - assert (Hbm : In b (model_blks m)).
      { pose proof (Permutation_in _ HPERM0 Hb3) as Hb0.
        pose proof (Permutation_NoDup HP1 (gp3_nodup_blocks ly4 S4 W2 mem4 md4 HAR4)) as ND1.
        apply in_app_iff in Hb0 as [Hb0 | Hb0].
        - exfalso. exact (gp3_nodup_app_neq _ _ b ND1 Hb0 ltac:(apply in_app_iff; left; exact Hb)).
        - apply in_app_iff in Hb0 as [Hb0 | Hb0]; [exact Hb0|]. exfalso.
          rewrite app_assoc in ND1.
          exact (gp3_nodup_app_neq _ _ b ND1 ltac:(apply in_app_iff; right; exact Hb) Hb0). }
      exact (HSEPFP b Hbm).
    - right. intros a Ha.
      destruct (gp3_inner G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk HJ) as (memS & HJi & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12 & _).
      destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (gk_blk B LAWS ly4 S4 W2 mem4 md4 p n HAR4 Hb4) as (_ & _ & Hn).
      replace a with (p + (a - p)) by lia.
      apply (C12 p n (a - p) Hent Hnb3). lia. }
  (* the arm's other facts *)
  assert (HFR1 : gframe cx fake_shadow_open (frame_addr ly4 1 fpos) W2 mem4).
  { rewrite HFFeq. apply (gp3_gframe_kept cx _ _ W W2 mem mem4 HFR eq_refl); [lia | exact KSTK | exact KFRM | exact KSH]. }
  assert (HFLAG' : sv8 W2 mem4 (frame_addr ly4 1 fpos + 120) (flag_addr ly4 1 fpos)).
  { rewrite HFFeq, HFLeq. apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KFRM; lia | exact HFLAG]. }
  assert (H16' : sv8 W2 mem4 (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H16]).
  assert (H144' : sv8 W2 mem4 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H144]).
  assert (H88' : sv8 W2 mem4 (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H88]).
  assert (SV24' : sv8 W2 mem4 (lf_F cx + 24) HI_G_NOUT)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact SV24]).
  assert (HIN' : ainput_at B cx ly4 S4 W2 mem4).
  { apply (gp3_ainput_kept cx ly3 S3 W mem ly4 S4 W2 mem4 HIN HlenP). intros Hn.
    assert (Hb0r : In (c_p cx, c_n cx) rest4).
    { apply (Permutation_in _ (Permutation_sym Hrest)). apply in_app_iff. right. apply in_app_iff. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    assert (Hb03 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct HIN as ([(Hn0 & _) | (_ & Hin)] & _); [lia | exact Hin]. }
    split; [exact (Hrest4 _ Hb0r)|].
    intros a Ha. apply (KBLK _ a Hb0r Hb03). cbn [fst snd]. unfold req_size.
    rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). lia. }
  assert (HRV' : rom_view segs W2 mem4)
    by exact (ajournal_gx_rom_view segs B pa_segs_low (G_RIG B fr_RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                HJc gp3_rom_out HRV).
  assert (HJT' : jt_rom W2 mem4) by exact (gp3_jt_kept W W2 mem mem4 HRV HRV' HJT).
  assert (HREADS' : forall j, (j < 4)%nat -> gn_sv4 W2 mem4 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem); [|exact (HREADS j Hj)].
    intros x Hx. apply KSTK. cbn in Hx. lia. }
  assert (HAWR' : awr W2 mem4 (lf_F cx + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KSTK; lia | exact HAWR]).
  assert (HAT' : sv8 W2 mem4 (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact HAT]).
  assert (HPFX' : gn_prefix_at cx m W2 mem4 (frame_addr ly3 1 fpos)).
  { destruct HPFX as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)));
            exact P2|].
    split; [intros a Ha; rewrite (proj1 (KFRM a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* what rig_post says of the new table: its functional relation, its length, and the model clauses of
     aentry_ok that its arelay_at gives of every entry (the base's gn_rig_ok) *)
  assert (HROK : gn_rig_ok cx m hs qs c4 O4 cap4).
  { split; [exact HRREL|]. split; [exact HLENq|].
    pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAEq & HNDq & _).
    split; [|exact HNDq].
    rewrite Forall_forall in HAEq |- *. intros e He.
    destruct (HAEq e He) as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & E11 & _ & _ & E14 & _).
    exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E11 E14)))))). }
  assert (HDONE : gdone RINV cx t m m1).
  { exists hs, qs, c4, O4, cap4, out4. split; [exact HPOK|]. split; [exact HAFTER|].
    split; [exact HROK|]. split; [exact HRI|]. split; [exact HOP|].
    (* the facts of amodel_at m (GRG's gst) that gdone carries for GN_RI_step / GN_RI_end *)
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & _).
    split.
    { (* aentry_ok's unfinished-line and key clauses (W_rep.v:128, :139-142), from arelay_at (W_rep.v:165) *)
      rewrite Forall_forall in HAE0 |- *. intros e He.
      destruct (HAE0 e He) as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & _ & HK).
      split; [exact HU|].
      rewrite Forall_forall in HK |- *. intros k Hk.
      destruct (HK k Hk) as (_ & _ & Hz & Hl). exact (conj Hz Hl). }
    split.
    { (* aout_at's capacity clause (W_rep.v:190-191) *)
      pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & GdC).
      destruct GdC as [(GdC & _) | (GdC & _)]; lia. }
    split.
    { (* aentry_ok's representation clauses (W_rep.v:127-128, :134-135) *)
      rewrite Forall_forall in HAE0 |- *. intros ge gHe.
      destruct (HAE0 ge gHe) as (_ & _ & _ & _ & _ & GdC6 & GdC7 & GdC8 & _ & _ & _ & GdC12 & _ & _ & _).
      split; [lia|]. split; [exact GdC6|].
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    split.
    2: {
      split; [exact HMpos|]. split; [exact HMSZ|].
      { (* GN_CNT_step's C2: the representation clause of the table relay_instance_gone leaves (rig_post's
         arelay_at .. (map fst qs), aentry_ok W_rep.v:134-135) *)
      pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAEq & _).
      rewrite Forall_forall in GdAEq |- *. intros ge gHe.
      destruct (GdAEq ge gHe) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdC12 & _ & _ & _).
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    }
    (* asrc_at's pending-offset clause (W_rep.v:107-108) and alist_at's non-empty pending records (W_rep.v:94) *)
    rewrite Forall_forall. intros go gHo. apply (In_nth (lm_hs m) go None) in gHo as (gi & gHi & <-).
    pose proof (HSLOT gi ltac:(lia)) as GdSl. unfold aslot in GdSl.
    destruct (nth gi (lm_hs m) None) as [gh0|]; [|exact I].
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdPL & _ & _ & _ & _ & GdOFF & _).
    split; [exact GdOFF|].
    destruct GdPL as (_ & _ & _ & _ & _ & _ & _ & _ & GdF).
    rewrite Forall_forall in GdF |- *. intros gr gHr. destruct (GdF gr gHr) as (_ & _ & _ & GdNe).
    exact (GdNe eq_refl). }
  (* the block relation from the LS state (ly3, S3) to the state after the call (ly4, S4): rig_post's two
     Permutations over one rest give HP1 at the SAME rest0 as the entry's ablocks_sep (HPERM0); any rest of
     (ly3, S3) is a permutation of rest0.  KF-COUNT: the meter cost is relay_instance_gone's own (rig_post's HMO), at
     the pairing hs gdone carries (gn_cst at q = 0) *)
  assert (HLS1 : exists ly0 S0 cst, LS cx t m ly0 S0 /\ mo_le MT S0 S4 cst /\ gn_cst MT cx m m1 0 cst /\
    gn_tie B cx m ly0 S0 m1 ly4 S4).
  { exists ly3, S3. eexists. split; [exact HLS|]. split; [exact HMO|].
    split.
    { eexists. split; [exists hs, qs, c4, O4, cap4, out4; split; [exact HPOK|]; split; [exact HAFTER | reflexivity]|].
      rewrite Z.add_0_r. apply Z.le_refl. }
    split; [exists rest0; exact HPERM0|].
    intros rest Hr.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      exact (Permutation_trans (Permutation_sym Hr) HPERM0). }
    eapply Permutation_trans; [exact HP1|].
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact Hrr. }
  (* ---- 0x84b4c: auipc a0,0x554; addi s4,a0,788; addi s5,s1,192; addi s6,s1,208, up to the loop's head ---- *)
  assert (HQ1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + AF_gp3_ret)) by (rewrite Q1; reflexivity).
  rewrite HQ1.
  (* NOTE: do not clear HFr; it is gn_nums' frame bound, which the run tactics' fresh HFr would shadow *)
  try clear HS SHOK HF.
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> getr regs4 r = getr regs r)
    by (intros r H1 H2; rewrite (gp3_pres (ms_regs ms) regs4 r HPRES H1); exact (KR r H2)).
  destruct (gp3_entry2 W2 regs4 mem4) as [HSb SHOKb].
  remember (Eimg (Ereg regs4 gp3_extra)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs4 gp3_extra) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb9 : ew Eb 9 = Z_to_bv 64 (lf_F cx)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl).
    rewrite (RR 9%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R9. }
  clear HEb.
  paj_run_to_tok RUNTO HSb HJ2 SHOKb gp3_span AF_gn_c1.
  { apply awr_ok_x_nil. }
  pmkst HSb.
  gp3_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs4 gp3_extra gp3_kept2 HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (21%bv : bv 5) Q21.
  prreg HSb (22%bv : bv 5) Q22.
  cbn [ms_regs restrict] in KR2.
  rewrite Em2 in *.
  (* the three registers the loop head reads *)
  assert (UF : bv_unsigned (Z_to_bv 64 (lf_F cx)) = lf_F cx).
  { apply unsigned_lit_small. clear - HFlo HFr Hspr AC C1. unfold LLVMF_STK in *. lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat 0)).
  { apply bv_eq. rewrite Q20, (HEIb 260%nat ltac:(unfold A_TEXT, A_LIM; lia)). vm_compute. reflexivity. }
  assert (R21' : getr (ms_regs ms0) 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat 0)).
  { rewrite Q21, Eb9, UF.
    replace (lf_F cx + 192 + 4 * Z.of_nat 0) with (lf_F cx + 192) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R22' : getr (ms_regs ms0) 22 = w64 (lf_F cx + 208)).
  { rewrite Q22, Eb9, UF. reflexivity. }
  (* the registers kept from the arm's entry *)
  assert (RF : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> In r gp3_kept2 ->
      getr (ms_regs ms0) r = getr regs r)
    by (intros r H1 H2 H3; rewrite (KR2 r H3); exact (RR r H1 H2)).
  apply SRr_ret.
  exists m1, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), ly4, S4, (kk + k4), fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD1 | exact HSEP1]].
    split; [exact HJ2|]. split; [exact HFR1|]. split; [exact HFLAG'|]. split; [exact H16'|].
    split; [exact H144'|]. split; [exact H88'|].
    split; [exact HIN'|]. split; [exact HRV' | exact HJT']. }
  split; [exact HDONE|]. split; [exact HLS1|].
  split.
  { rewrite HFFeq. unfold gn_kregs.
    do 7 (split; [match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end|]).
    match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end. }
  split; [exact SV24'|].
  split; [exact R20'|]. split; [exact R21'|]. split; [exact R22'|].
  split; [clear; lia|].
  split; [exact HREADS'|]. split; [exact HAWR'|]. split; [exact HAT'|].
  rewrite HFFeq. exact HPFX'.
Qed.

End gp3.
