(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillW.v (commit 3295f3a9fd5, CfInstMiss lane M field round 3 (cf-miss 3295f3a9fd5); file sha256 ede576499333) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/MnRefillW.v at commit f7d0d764e77, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   rule 24: no function proved (interface statements and window arithmetic over an abstract refill window; no machine
   walk is written).

   WHY.  AGif0n.AIfaceM.if_refill's post AGif0n.rleaf (AGif0n.v:253-268: view frame :262, raw frame :266, presence :267)
   and its add-ons ErrnoG.rleaf_ev / rleaf_e (ErrnoG.v:401-432) and MnRefill.rleaf_em (MnRefill.v:40-56: :49 / :52 /
   :55) fix the refill's stack window at ImgBaseAG.RSTACK = 1024 below the refill's sp.  A refill whose class-full path
   reports (Printf / SharedPrintfCode frames) writes more than that, so if_refill is false for it whatever the refill
   text.

   WHAT, additive (AGif0n, ErrnoG, MnRefill, AGif1m and every existing statement are unchanged), over a window RW:
   - [rleaf_w] / [rleaf_ev_w] / [rleaf_e_w] / [rleaf_em_w]: AGif0n.rleaf / ErrnoG.rleaf_ev / ErrnoG.rleaf_e /
     MnRefill.rleaf_em with RSTACK replaced by RW, and one conjunct more: the refill keeps the depot
     (`st_depot (snd r) = st_depot S0`; at P'' the trace premise reads the depot, see ifw_depot_miss below);
   - [refill_w_t] / [ame_refill_v_w_t] / [ame_refill_w_t] / [amm_refill_w_t]: AIfaceM.if_refill / ErrnoG.ame_refill_v_t /
     ErrnoG.ame_refill_t / MnRefill.amm_refill_t over those leaves, premises byte for byte;
   - [AIfaceMw] / [AIfaceMEw]: AGif0n.AIfaceM / ErrnoG.AIfaceME with the refill field(s) over RW, and the depot field
     at the pop state taking `st_depot Sp = st_depot S0` ([ifw_depot_miss], [ame_depot_miss_w_t]): at P'' a trace
     premise U (the cf instance's admits, YG01.v:155) reads the depot, and the entry state's U carries to the pop
     state only through the depot (YG01.admits_keep); the miss walks get the equation from the refill leaf;
   - the miss join's window uses (section j, under [176 + RW <= AFSTACK]): the four facts the miss arms read off the
     refill's window (AGim.v:400-422 / :657 / :677, AGin.v:438-459 / :697 / :717 / :843 / :853, AGk1.v:206-220 / :310 /
     :320): the window lies in Allocate's window [win_af_w], above the stack's base [win_stk_w]; the refill keeps the
     caller's stack outside the window [stack_kept_w]; Allocate's window is present after the refill [pres_af_w].
   EVENT-FREE: no event counter, event bound, meter or regime; the only event term is the tick update inside the
   refill fields' own statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
(* unsigned_lit_small *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT MnRefill.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
(* round 3: the read-only data predicate arodata_ok_cf (YG0dcf.v:82) reads CfImg's RELRO bounds *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg} {ci : CfImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The leaves over the window RW.                                                                                   *)

(* copy of AGif0n.v:253-268 with RSTACK -> RW *)
Definition rleaf_w (RW : Z) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ st_depot (snd r) = st_depot S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
(forall a, spZ regs - RW <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* copy of ErrnoG.v:401-416 with ImgBaseAG.RSTACK -> RW *)
Definition rleaf_ev_w (RW : Z) (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ st_depot (snd r) = st_depot S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
ErrnoG.errno_kept_v im_segs B W W' mem mem' /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
(forall a, spZ regs - RW <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* copy of ErrnoG.v:417-432 with ImgBaseAG.RSTACK -> RW *)
Definition rleaf_e_w (RW : Z) (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ st_depot (snd r) = st_depot S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
ErrnoG.errno_kept B mem mem' /\
(forall a, spZ regs - RW <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* copy of MnRefill.v:40-56 with ImgBaseAG.RSTACK -> RW *)
Definition rleaf_em_w (RW : Z) (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ st_depot (snd r) = st_depot S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
ErrnoG.errno_kept B mem mem' /\
MemnormT.memnorm_keep im_segs mem mem' /\
(forall a, spZ regs - RW <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* The forgetful maps (MnRefill.rleaf_em_e and the drop to rleaf, over RW). *)
Lemma rleaf_em_w_e : forall RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c',
rleaf_em_w RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c' ->
rleaf_e_w RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'.
Proof.
intros RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'
  (ly' & regs' & mem' & md' & H1 & H2 & H3 & H4 & H5 & HD & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _ & H13 & H14).
exists ly', regs', mem', md'. tauto.
Qed.
Lemma rleaf_e_w_w : forall RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c',
rleaf_e_w RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c' ->
rleaf_w RW ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'.
Proof.
intros RW B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'
  (ly' & regs' & mem' & md' & H1 & H2 & H3 & H4 & H5 & HD & H6 & H7 & H8 & H9 & H10 & H11 & _ & H12 & H13).
exists ly', regs', mem', md'. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill fields over RW, in AIfaceM's / ErrnoG's / MnRefill's form.                                            *)
Section v.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable rtree : Z -> M unit.
Variable RW : Z.

(* copy of AGif0n.v:283-298 (AIfaceM.if_refill) over rleaf_w RW *)
Definition refill_w_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> arodata_ok_cf im_segs B mem0 ->
0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_w RW ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* copy of ErrnoG.ame_refill_v_t (ErrnoG.v:469-483) over rleaf_ev_w RW *)
Definition ame_refill_v_w_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> arodata_ok_cf im_segs B mem0 ->
0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_ev_w RW B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* copy of ErrnoG.ame_refill_t (ErrnoG.v:484-498) over rleaf_e_w RW *)
Definition ame_refill_w_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> arodata_ok_cf im_segs B mem0 ->
0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_e_w RW B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* copy of MnRefill.amm_refill_t (MnRefill.v:76-90) over rleaf_em_w RW *)
Definition amm_refill_w_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> arodata_ok_cf im_segs B mem0 ->
0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_em_w RW B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* copy of MnRefill.amm_refill_e (MnRefill.v:92-99) over RW *)
Lemma amm_refill_w_e : amm_refill_w_t -> ame_refill_w_t.
Proof.
intros H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
  H20 H21.
eapply amreal_mono; [| exact (H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
  H14 H15 H16 H17 H18 H19 H20 H21)].
intros r W' c' HL. exact (rleaf_em_w_e RW B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem _ r W' c' HL).
Qed.

(* ame_refill_w_t gives refill_w_t (drop errno) *)
Lemma ame_refill_w_refill : ame_refill_w_t -> refill_w_t.
Proof.
intros H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
  H20 H21.
eapply amreal_mono; [| exact (H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
  H14 H15 H16 H17 H18 H19 H20 H21)].
intros r W' c' HL. exact (rleaf_e_w_w RW B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem _ r W' c' HL).
Qed.
End v.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The records.                                                                                                     *)

(* copy of AGif0n.v:271-391 (AIfaceM) with if_refill over RW (field [ifw_refill]) and the depot field at the pop state
   taking the depot equation (field [ifw_depot_miss]); the other fields are AIfaceM's, byte for byte, renamed
   if_ -> ifw_.                                                                                                     *)
Record AIfaceMw (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z)
(rtree : Z -> M unit) (RW : Z) : Prop := {
  ifw_mview : forall inst ly S W mem md n,
    ARX inst ly S W mem md -> 0 <= n -> from_primary n = true ->
    pc_chunks (cache S (chunk_class n)) = [] -> mview B W ly inst mem (chunk_class n);
  ifw_shape_miss : forall n tr S, 0 <= n -> from_primary n = true -> pc_chunks (cache S (chunk_class n)) = [] ->
    mt n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) mtag ;; rtree (chunk_class n) ;;
                 malloc_join_t stag n tr (chunk_class n)) S;
  ifw_refill : refill_w_t B ARX AOX rpre lpost rtree RW;
  ifw_post_miss : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly0 S0 W0 mem00 md00 -> rpre S0 n -> blocks_bytes S0 + n <= lmax ->
    ARX inst ly Sp W mem0 md0 -> n < nmax -> blocks_bytes Sp + n <= lmax -> U tr S0 ->
    49 <= n <= 64512 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
    at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
      (fun z m => dpost inst ly Sp W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final Sp (chunk_class n) l off n tr z);
  ifw_post_miss_k : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly0 S0 W0 mem00 md00 -> rpre S0 n -> blocks_bytes S0 + n <= lmax ->
    ARX inst ly Sp W mem0 md0 -> n < nmax -> blocks_bytes Sp + n <= lmax -> U tr S0 ->
    0 <= n <= 48 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) (off / 16) + K6.RZ - 15) 1 jb ->
    at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
      (fun z m => dpost inst ly Sp W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> K6.NPv n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final Sp (chunk_class n) l off n tr z);
  ifw_depot_miss : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly0 S0 W0 mem00 md00 -> U tr S0 ->
    ARX inst ly Sp W mem0 md0 -> st_depot Sp = st_depot S0 ->
    (forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly Sp W tr z mem');
  ifw_oom : forall inst ly S0 Sp W mem md n tr (sp0 : Z) mem' md',
    ARX inst ly Sp W mem md -> lpost Sp -> pc_chunks (cache Sp (chunk_class n)) = [] ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> im_oom -> ~ (im_errno <= a < im_errno + 4) ->
       aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
    (forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> im_oom -> ~ (im_errno <= bv_unsigned x < im_errno + 4) ->
       mem' x = mem x) ->
    (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
    ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
    val_mem im_segs (mrestrict (w_H W) mem') im_oom 1 1 -> same_io md md' -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
    (exists trc, apath (mt n tr S0) trc (PNull, Sp) /\ gflag trc = true) ->
    ARX inst ly Sp W mem' md' /\ lpost Sp /\ AOX ly Sp im_oom /\ AOX ly Sp (ly_T ly + t_unwinding);
  ifw_stack : forall inst ly S W mem md a, ARX inst ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S a;
  ifw_view_m : forall inst ly S W mem md n l off,
    ARX inst ly S W mem md -> 0 <= n -> from_primary n = true ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16);
  ifw_owned_m : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> 49 <= n <= 64512 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
    hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> AOX ly S a;
  ifw_owned_m_k : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> 0 <= n <= 48 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> K6.NPv n mod 8 <> 0) ->
    hit_writes_k ly n (chunk_class n) (off / 16) odd a -> AOX ly S a;
  ifw_mono_join : forall inst ly Sp W mem md n l off tr z a,
    ARX inst ly Sp W mem md -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    ~ (sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) <= a <
       sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) + req_size n) ->
    AOX ly Sp a -> AOX ly (st_final Sp (chunk_class n) l off n tr z) a
}.

(* copy of ErrnoG.v:501-522 (ame_depot_miss_t) with the depot equation, as ifw_depot_miss *)
Definition ame_depot_miss_w_t (B : asyms) (U : list Z -> astate -> Prop)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) : Prop :=
forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly0 S0 W0 mem00 md00 -> U tr S0 ->
ARX inst ly Sp W mem0 md0 -> st_depot Sp = st_depot S0 ->
(forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - ImgBaseAG.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  ErrnoG.errno_kept B mem mem' /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  dpost inst ly Sp W tr z mem').

(* copy of ErrnoG.v:536-541 (AIfaceME) with the refill fields over RW and the depot field with the depot equation *)
Record AIfaceMEw (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z)
(rtree : Z -> M unit) (RW : Z) : Prop := {
  amew_refill_v : ame_refill_v_w_t B ARX AOX rpre lpost rtree RW;
  amew_refill : ame_refill_w_t B ARX AOX rpre lpost rtree RW;
  amew_depot_miss : ame_depot_miss_w_t B U ARX dpost
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The miss join's window uses: the refill's window [spZ - RW, spZ) at spZ = sp0 - 176 lies in Allocate's window      *)
(* [sp0 - AFSTACK, sp0) when 176 + RW <= AFSTACK; each use below is one lia on that bound.                           *)
Section j.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.

(* the refill's window is in Allocate's window (AGim.v:657 / :677, AGin.v:697 / :717 / :843 / :853, AGk1.v:310 / :320) *)
Lemma win_af_w : forall (sp0 a : Z) (regs : bvmap 5 word), spZ regs = sp0 - 176 ->
spZ regs - RW <= a < spZ regs -> sp0 - AFSTACK <= a < sp0.
Proof. intros sp0 a regs E Ha. rewrite E in Ha. pose proof RWB. unfold AFSTACK in *. lia. Qed.

(* the refill's window is above the stack's base (the errno / stack apartness premise, ErrnoApart.errno_apart_stack) *)
Lemma win_stk_w : forall (ly : alayout) (sp0 : Z) (regs : bvmap 5 word), ly_stk_lo ly + AFSTACK <= sp0 ->
spZ regs = sp0 - 176 -> ly_stk_lo ly <= spZ regs - RW.
Proof. intros ly sp0 regs H E. rewrite E. pose proof RWB. unfold AFSTACK in *. lia. Qed.

(* the refill's frames restated outside Allocate's window (the miss join's NST uses) *)
Lemma frame_view_af_w : forall (AOX : alayout -> astate -> Z -> Prop) ly S0 ly' S' (W W' : world im_segs) mem mem' (sp0 : Z)
(regs : bvmap 5 word), spZ regs = sp0 - 176 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' S' a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' S' a -> ~ (sp0 - AFSTACK <= a < sp0) ->
aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a.
Proof.
intros AOX ly S0 ly' S' W W' mem mem' sp0 regs E FR a Ra N0 N1 NS.
apply (FR a Ra N0 N1). intros X. exact (NS (win_af_w sp0 a regs E X)).
Qed.
Lemma frame_raw_af_w : forall (AOX : alayout -> astate -> Z -> Prop) ly S0 ly' S' (mem mem' : word -> option byte) (sp0 : Z)
(regs : bvmap 5 word), spZ regs = sp0 - 176 ->
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) ->
forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) -> ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
mem' x = mem x.
Proof.
intros AOX ly S0 ly' S' mem mem' sp0 regs E FR x N0 N1 NS.
apply (FR x N0 N1). intros X. exact (NS (win_af_w sp0 (bv_unsigned x) regs E X)).
Qed.

(* the refill keeps the caller's stack outside its window (AGim.v:400-405 / AGin.v:438-443 / AGk1.v:206-211 STKkept,
   with the stack not owned at either end (if_stack / ifw_stack)) *)
Lemma stack_kept_w : forall (AOX : alayout -> astate -> Z -> Prop) ly S0 ly' S' (W W' : world im_segs) mem mem' (sp0 : Z)
(regs : bvmap 5 word), spZ regs = sp0 - 176 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' S' a -> ~ (spZ regs - RW <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) ->
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S0 a /\ ~ AOX ly' S' a) -> 0 <= ly_stk_lo ly -> ly_stk_hi ly <= 2 ^ 64 ->
forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 176 - RW <= a < sp0 - 176) ->
aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a.
Proof.
intros AOX ly S0 ly' S' W W' mem mem' sp0 regs E FR NOWN K1 K2 a Ha Hnw.
destruct (NOWN a Ha) as [N0 N1]. apply (FR a ltac:(lia) N0 N1). rewrite E. exact Hnw.
Qed.

(* Allocate's window is present after the refill (AGim.v:413-422 / AGin.v:451-459 / AGk1.v:212-220 PRES'): in the
   refill's window by its presence clause, elsewhere by the raw frame (the bytes are not owned at either end) and the
   world's order (a byte visible at W is visible at W') *)
Lemma pres_af_w : forall (AOX : alayout -> astate -> Z -> Prop) ly S0 ly' S' (W W' : world im_segs) (mem mem' : word -> option byte)
(sp0 : Z) (regs : bvmap 5 word), spZ regs = sp0 - 176 -> wle W W' ->
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
   ~ (spZ regs - RW <= bv_unsigned x < spZ regs) -> mem' x = mem x) ->
(forall a, spZ regs - RW <= a < spZ regs -> apresent (w_H W') mem' a) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> ~ AOX ly S0 a /\ ~ AOX ly' S' a) ->
0 <= sp0 - AFSTACK -> sp0 <= 2 ^ 64 ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros AOX ly S0 ly' S' W W' mem mem' sp0 regs E WLE FRR PRR NOWN K1 K2 PRES a Ha.
destruct (Z_lt_le_dec a (spZ regs - RW)) as [H1|H1]; [|destruct (Z_lt_le_dec a (spZ regs)) as [H2|H2]].
2:{ apply PRR. lia. }
all: destruct (PRES a Ha) as [Hh [b Hb]]; destruct (NOWN a Ha) as [N0 N1];
  assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia);
  split; [ destruct (w_H W' (Z_to_bv 64 a)) eqn:HW'; [rewrite (WLE _ HW') in Hh; discriminate | reflexivity] |];
  exists b; rewrite (FRR (Z_to_bv 64 a)); [exact Hb | rewrite Ex; exact N0 | rewrite Ex; exact N1 | rewrite Ex; lia].
Qed.
End j.
End g.
