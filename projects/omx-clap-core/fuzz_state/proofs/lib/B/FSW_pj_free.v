(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items_calls.v, with its module paths and module names changed; 3663 of its 3768 lines of code are new or changed and 1083 lines of the source are left out. *)
(* pj_free 0x83674 (pf.c:334-350) on fs.asan-ubsan (image B), 136 instructions: the symbolic walk of lib/B's
   FSH_Fn_reader.v pj_free_spec k, level-indexed k = 0..2 (statement FIXED, not edited here).
   rule 24: the function's released plain proof exists (lib/Prog/pj_free.v @ c8557374ad2e); no released ASan-image proof
   of any fs function exists (ossv proof index v5 built 2026-10-29T06:12:16Z; a Theorem Labs lane, sonic, `pj_free B: CONFIRM`).
   Written new from the image-A walk (a working branch lib/A/FSW_pj_free.v) as a template; no lib/A image-content
   file is loaded (lib/A FSupoison / FSupoisonU / FSH_YC20 / FSH_Gen only), every image name is lib/B's.

   THE PLAN (B's listing 0x83674 .. 0x83890, read before writing; B differs from A in four ways):
   (1) the frame is 128 (A 96) and holds THIRTEEN saved registers (ra, s0 .. s11, at sp - 8 .. sp - 104) and TWO SPILL
       slots: 8(sp) = (v + 24) >> 3 and 16(sp) = (v + 32) >> 3 (0x836e8 .. 0x836f4). The exit path reloads the spills
       (0x837c0, 0x837d8) instead of keeping a shadow register, so the walk's frame predicate pjf_frm carries the two
       spilled words beside the thirteen saved ones, and the resumed states' frame chunks name them as
       SAlu ALU_SRL (SOff 19 0) (SLit 3) / SAlu ALU_SRL (SOff 9 0) (SLit 3) (s3 = v + 24 and s1 = v + 32 are atoms of
       the resumed env).
   (2) the register allocation differs: s0 = v, s1 = v + 32, s2 = v + 40, s3 = v + 24, s6 = shadow (v + 40),
       s7 = SHADOW_OFF (A: s4), and in the loop s4 = shadow (v + 32), s5 = 56, s8 = 56 i, s9 = 8 i, s10 = i,
       s11 = shadow (v + 24).
   (3) B re-reads v->kids (0x83724) and v->n (0x837ac) inside the loop, so the loop's resumed states carry those
       fields; the kid pointer is kids + s8 (0x8375c), the key slot keys + s9 (0x83788).
   (4) B has UBSan checks A has not: the one trap site is the `unimp` 0x83858, reached from six branches. The walk
       decides each of them untaken; two (0x83744's `bltu a2, a0` and 0x83758's `bnez` on the mulh overflow test, and
       0x83778's `bltu a1, s9` on the key slot) are no range fact of the engine's, so the resumed state carries them
       as assumed conditions (acond) whose acond_ok the walk proves from the block bounds.
   Every inline ASan check (`lbu` of a shadow byte, `bnez` to __asan_report_load8) is decided UNTAKEN by the walk: the
   checked bytes are v's fields (v is a pobj, addressable) and keys[i] (the live keys block).
   The data lemmas are lib/B/FSW_pj_free_dat.v; the decode table lib/B/FSW_pj_free_tbl.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_reader
FSW_K FSW_ret FSW_rd FSW_pj FSW_K3 FSW_pj_free_tbl FSW_pj_free_dat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the canonical symbolic states ================= *)
(* every client pointer lies below alloc_ceiling <= 0x7fffff800000 (YCbq.v asan_consts) *)
Definition PJF_CEIL : Z := 140737479966720.
(* entry, v <> 0: v's fields str / kids / keys / n (atoms 33..36) read through a0 (atom 10) *)
Definition pjf_v0 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 16 48 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
     YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
(* ... n >= 1 (atom 36 at least 1) runs to the loop head 0x8371c *)
Definition pjf_ss0n : sstate :=
  fss0T_args A_pj_free 128 [pjf_v0] [(10%nat, mkAF 4096 PJF_CEIL 3); (36%nat, mkAF 1 (2 ^ 54) 0)].
(* ... n = 0 (the field holds the literal) runs to the exit 0x837c0 *)
Definition pjf_v0z : YP09.region :=
  YP09.mkRegion (Some 10%nat) 16 48 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
     YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SLit 0))].
Definition pjf_ss0z : sstate := fss0T_args A_pj_free 128 [pjf_v0z] [(10%nat, mkAF 4096 PJF_CEIL 3)].
Definition pjf_SH0 : list shent := [mkSHE 10 0 56].
(* the THIRTEEN saved registers in the frame [sp - 104, sp) after the prologue, as extra atoms xatom 0..12
   (atoms 33..45: ra, s0, s1, s2 .. s11), and the two spill words 8(sp) / 16(sp) *)
Definition pjf_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SAlu ALU_SRL (SOff 19 0) (SLit 3)));
   YP09.mkChunk 16 (CVal 8 (SAlu ALU_SRL (SOff 9 0) (SLit 3)));
   YP09.mkChunk 24 (CVal 8 (SOff 45 0)); YP09.mkChunk 32 (CVal 8 (SOff 44 0));
   YP09.mkChunk 40 (CVal 8 (SOff 43 0)); YP09.mkChunk 48 (CVal 8 (SOff 42 0));
   YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
   YP09.mkChunk 72 (CVal 8 (SOff 39 0)); YP09.mkChunk 80 (CVal 8 (SOff 38 0));
   YP09.mkChunk 88 (CVal 8 (SOff 37 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0));
   YP09.mkChunk 104 (CVal 8 (SOff 35 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0));
   YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
Definition pjf_sregs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition pjf_saved (regs : bvmap 5 word) : list word := map (YK11.getr regs) pjf_sregs.
(* a shadow byte holding 0, based at atom n; an 8-byte field at offset o of the object at atom n, holding atom x *)
Definition shr (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition fld (n : nat) (o : Z) (x : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SOff x 0))].
(* ... holding the literal 0 (a null field) *)
Definition fld0 (n : nat) (o : Z) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SLit 0))].
(* the resumed states: registers are the machine's (atoms), the frame, the two shadow-base cells, rs; atom 23 (s7) is
   the shadow base, so the token runs take Bx := SOff 23 0 *)
Definition pjf_Gc (at_ : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ::
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: at_) cs al.
Definition pjssc (pc : Z) (rs : list YP09.region) (at_ : list (nat * afact)) (cs : list acond)
  (al : list (sv * sv)) : sstate :=
  mkSS pc sr_atoms (fsT_ret_regions 128 pjf_cs rs) None (pjf_Gc at_ cs al).
Definition pjss (pc : Z) (rs : list YP09.region) (at_ : list (nat * afact)) (al : list (sv * sv)) : sstate :=
  pjssc pc rs at_ [] al.
Definition pBx : sv := SOff 23 0.

(* ---- the loop's states (MEASURED on fs.asan-ubsan with the engine; the runs reach the pcs below) ----
   the loop head 0x8371c at kid i: the shadow cell of v + 24 (s11, atom 27) reads 0, and kids (atom 46) sits at
   v + 24 through s3 (atom 19). The two assumed conditions are the UBSan checks of the kid pointer:
   `bltu a2, a0` 0x83744 (kids + 56 i does not wrap) and `bnez` 0x83758 (56 i does not overflow, as mulh). *)
Definition pjf_Cwrap : acond :=
  mkAC BC_GEU (SAlu ALU_ADD (SMd M_MUL (SOff 26 0) (SLit 56)) (SOff 46 0)) (SOff 46 0).
Definition pjf_Cmulh : acond :=
  mkAC BC_EQ (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 26 0) (SOff 21 0))
    (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63)))) (SLit 0).
Definition ss_L : sstate :=
  pjssc 0x8371c [shr 27; fld 19 0 46]
    [(46%nat, mkAF 4112 PJF_CEIL 4); (26%nat, mkAF 0 (2 ^ 54) 0); (21%nat, mkAF 56 56 0)]
    [pjf_Cwrap; pjf_Cmulh] [].
(* after the self call 0x83764, keys <> 0: the shadow cell of v + 32 (s4, atom 20), keys (atom 46) at v + 32 through
   s1 (atom 9), the key slot keys + 8 i (atom 47, an alias of keys + s9) and keys[i] (atom 48). The assumed condition
   is the UBSan check `bltu a1, s9` 0x83778 (~keys >= 8 i: the key slot does not wrap). *)
Definition pjf_Ckey : acond := mkAC BC_GEU (SAlu ALU_XOR (SOff 46 0) (SLit (-1))) (SOff 25 0).
Definition ss_R1a : sstate :=
  pjssc 0x83764 [shr 20; fld 9 0 46; fld 47 0 48]
    [(46%nat, mkAF 4112 PJF_CEIL 4); (47%nat, mkAF 4096 PJF_CEIL 3); (25%nat, mkAF 0 (2 ^ 57) 3)]
    [pjf_Ckey] [(SAlu ALU_ADD (SOff 46 0) (SOff 25 0), SOff 47 0)].
Definition SH_R1a : list shent := [mkSHE 47 0 8].
(* ... keys = 0 (the field holds the literal): the run reaches the loop tail 0x837a4 *)
Definition ss_Lz : sstate := pjssc 0x83764 [shr 20; fld0 9 0] [] [] [].
(* the loop tail 0x837a4: the shadow cell of v + 40 (s6, atom 22) and n (atom 46) at v + 40 through s2 (atom 18).
   The assumed condition is the `bltu s10, a0` of 0x837bc: BC_LTU for the back edge to 0x8371c, BC_GEU for the exit
   to 0x837c0. *)
Definition ss_T (c : branch_cond) : sstate :=
  pjssc 0x837a4 [shr 22; fld 18 0 46] [] [mkAC c (SOff 26 1) (SOff 46 0)] [].
(* the exit 0x837c0: the spill 8(sp) gives the shadow of v + 24, kids (atom 46) sits at v + 24 through s3 (atom 19) *)
Definition ss_T0 : sstate := pjssc 0x837c0 [fld 19 0 46] [(19%nat, mkAF 4096 PJF_CEIL 3)] [] [].
Definition SH_T0 : list shent := [mkSHE 19 0 8].
(* after fuzz_free (kids) 0x837d8: the spill 16(sp) gives the shadow of v + 32, keys (atom 46) at 32(s0) *)
Definition ss_X1 : sstate :=
  pjssc 0x837d8 [fld 8 32 46] [(8%nat, mkAF 4096 PJF_CEIL 3); (9%nat, mkAF 4096 PJF_CEIL 3)] [] [].
Definition SH_X1 : list shent := [mkSHE 9 0 8].
(* after fuzz_free (keys) 0x837f0: str (atom 46) at 16(s0), its shadow computed from s0 + 16 *)
Definition ss_X2 : sstate := pjssc 0x837f0 [fld 8 16 46] [(8%nat, mkAF 4096 PJF_CEIL 3)] [] [].
Definition SH_X2 : list shent := [mkSHE 8 16 24].
(* after fuzz_free (str) 0x8380c, after __asan_memset 0x8381c *)
Definition ss_X3 : sstate := pjssc 0x8380c [] [] [] [].
Definition ss_X4 : sstate := pjssc 0x8381c [] [] [] [].

(* the frame the prologue wrote (MEASURED: the entry run's region at the loop head and at the exit) *)
Definition pjf_ent_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0
    [YP09.mkChunk (-112) (CVal 8 (SAlu ALU_SRL (SOff 10 32) (SLit 3)));
     YP09.mkChunk (-120) (CVal 8 (SAlu ALU_SRL (SOff 10 24) (SLit 3)));
     YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the callee-saved registers at the final ret (the epilogue reloads ra and s0 .. s11 from the frame) *)
Definition pjf_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 128 | 8 => SOff 34 0 | 9 => SOff 35 0 | 18 => SOff 36 0 | 19 => SOff 37 0 | 20 => SOff 38 0
  | 21 => SOff 39 0 | 22 => SOff 40 0 | 23 => SOff 41 0 | 24 => SOff 42 0 | 25 => SOff 43 0 | 26 => SOff 44 0
  | 27 => SOff 45 0
  | z => SOff (Z.to_nat z) 0
  end.

(* a duplicate-free list has no element in two of its parts *)
Lemma pjf_nodup_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
inversion Hnd as [|? ? Hny Hnd']; subst. destruct H1 as [<-|H1].
- apply Hny. apply in_or_app. right. exact H2.
- exact (IH l2 x Hnd' H1 H2).
Qed.
Lemma pjf_nodup_mid : forall {X} (A M R : list X) x, List.NoDup (A ++ M ++ R) -> In x (A ++ R) -> In x M -> False.
Proof.
intros X A M R x Hnd Hx HM. apply in_app_or in Hx as [Hx|Hx].
- exact (pjf_nodup_disj A (M ++ R) x Hnd Hx (in_or_app _ _ _ (or_introl HM))).
- exact (pjf_nodup_disj M R x (List.NoDup_app_remove_l _ _ Hnd) HM Hx).
Qed.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pjf_same_below_wr : forall E rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a) -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E rs m m' lo HF Hw H64 x Hx. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (Hw _ Hin). lia.
Qed.
(* the write windows of the walk's resumed states: the frame only (rs read only) *)
Lemma pjf_wrange_ret : forall E cs rs a sp,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> bv_unsigned (ew E 2) = sp ->
  in_wrange E (fsT_ret_regions 128 cs rs) a -> sp <= a < sp + 128.
Proof.
intros E cs rs a sp HF E2 (r & Hin & Hr). unfold fsT_ret_regions in Hin. cbn [app In] in Hin.
destruct Hin as [<- | [<- | [<- | Hin]]].
- cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- rewrite Forall_forall in HF. pose proof (HF r Hin). lia.
Qed.
Lemma pjf_val_keep : forall (m m' : word -> option byte) a n v,
  (forall k, 0 <= k < Z.of_nat n -> mbyte tfibsegs m' (a + k) = mbyte tfibsegs m (a + k)) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hk Hv k Hk'. rewrite (Hk (Z.of_nat k) ltac:(lia)). exact (Hv k Hk'). Qed.
Lemma pjf_mbyte_of_aview : forall (H : word -> bool) m a z,
  aview tfibsegs H m a = Some z -> mbyte tfibsegs (mrestrict H m) a = Some (Z_to_bv 8 z).
Proof.
intros H m a z E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|]; [|discriminate E].
cbn in E. injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pjf_apresent_unpoison : forall U (H : word -> bool) m m' a,
  (apresent H m a -> apresent H m' a) -> apresent H (unpoison U m) a -> apresent H (unpoison U m') a.
Proof.
intros U H m m' a Hm Hp. unfold apresent, unpoison in *. destruct Hp as [Hh [b Hb]].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))).
- split; [exact Hh | exists (Z_to_bv 8 0); reflexivity].
- exact (Hm (conj Hh (ex_intro _ b Hb))).
Qed.
(* a pobj's bytes: present, not owned, outside the image, application bytes; an __asan_memset range with a visible
   shadow hull *)
Lemma pjf_place : forall B ly S (W : world tfibsegs) mx md m v,
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v ->
  (forall a, v <= a < v + 56 -> apresent (w_H W) mx a /\ ~ aowned B ly S a /\ ~ in_img tfibsegs a /\ app_addr a) /\
  amem_range v 56 /\ shadow_hull_vis (aview tfibsegs (w_H W) mx) v 56.
Proof.
intros B ly S W mx md m v HAR ([((cid & pos & Hin & Hc & Hal & H1 & H2) & Hv8 & Hr)|((b & n & Hin & H1 & H2) & Hv8 & Hr)] & Hw).
- pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_frames _ _ LAWS ly S W mx md cid pos HAR Hin) as (_ & Happ & Hb & _).
  destruct (frames_bounds tfibsegs B LAWS ly S W mx md cid pos HAR Hin) as (F1 & F2 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split].
  + intros a Ha. destruct (Hb a ltac:(lia)) as [Hp Hno]. split; [exact Hp|]. split; [exact Hno|]. split.
    * refine (proj2 (al_client_img _ _ LAWS ly S W mx md a HAR _)). right; left. exists cid, pos.
      split; [exact Hin | lia].
    * exact (in_app_addr _ _ a Happ ltac:(lia)).
  + destruct Happ as [Hh Hh2]. unfold amem_range, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + exact (fsw_afobj_hull B ly S W mx md cid pos v 56 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_blocks _ _ LAWS ly S W mx md b n HAR Hin) as (_ & H4096 & Hc & Happ & Hb & _).
  split; [|split].
  + intros a Ha. destruct (Hb a ltac:(unfold HEAD in *; lia)) as [Hp Hno]. split; [exact Hp|]. split; [exact Hno|].
    split.
    * refine (proj2 (al_client_img _ _ LAWS ly S W mx md a HAR _)). left. exists b, n.
      split; [exact Hin | unfold HEAD in *; lia].
    * exact (in_app_addr _ _ a Happ ltac:(unfold HEAD in *; lia)).
  + exact (amem_range_of_block tfibsegs B LAWS ly S W mx md b n v 56 HAR Hin ltac:(unfold HEAD in *; lia) H2).
  + exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W mx md b n v 56 HAR Hin ltac:(unfold HEAD in *; lia) H2
      ltac:(lia)).
Qed.
(* the shadow hull, from the AR memory to the machine's (a user-poisoned shadow byte reads 0xf7, visible) *)
Lemma pjf_hull_raw : forall (W : world tfibsegs) Uh mem mem' x n, upoisoned tfibsegs W mem Uh ->
  same_below mem mem' alloc_ceiling -> 0 <= x -> x + n <= alloc_ceiling -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison Uh mem)) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem') x n.
Proof.
intros W Uh mem mem' x n HP Hs Hx Hn Hn0 Hh s Hsr.
pose proof asan_consts as (C1 & _).
assert (Hs0 : 0 <= s < alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF in Hsr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
  set (q1 := (2147450880 + x / 8)) in *. set (q2 := (2147450880 + (x + n - 1) / 8)) in *.
  pose proof (Z.div_mod q1 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound q1 8 ltac:(lia)) as M3.
  pose proof (Z.div_mod q2 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound q2 8 ltac:(lia)) as M4.
  lia. }
rewrite (aview_below (w_H W) mem mem' alloc_ceiling s Hs Hs0).
destruct (in_ush Uh (bv_unsigned (Z_to_bv 64 s))) eqn:Ei.
- rewrite (wz s ltac:(lia)) in Ei. rewrite (HP s Ei). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) Uh mem s Ei). exact (Hh s Hsr).
Qed.
(* fs_glob reads only image cells *)
Lemma pjf_glob_keep : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall a v, (forall k, 0 <= k < 8 -> in_img tfibsegs (a + k)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') a 8 v).
{ intros a v Hi Hv k Hk8. rewrite (Hk (a + Z.of_nat k) (Hi (Z.of_nat k) ltac:(lia))). exact (Hv k Hk8). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [intros k Hk8; apply (pjf_img_cover G_LIVE (G_LIVE + 8) ltac:(vm_compute; reflexivity)); lia | exact G1]|].
split; [apply VB; [intros k Hk8; apply (pjf_img_cover G_PEAK (G_PEAK + 8) ltac:(vm_compute; reflexivity)); lia | exact G2]|].
split; [apply VB; [intros k Hk8; apply (pjf_img_cover G_COUNT (G_COUNT + 8) ltac:(vm_compute; reflexivity)); lia | exact G3]|].
split; [apply VB; [intros k Hk8; apply (pjf_img_cover G_FAIL (G_FAIL + 8) ltac:(vm_compute; reflexivity)); lia | exact G4]|].
exact R.
Qed.
(* the shadow cell of an 8-aligned, fully addressable 8-byte word reads 0 *)
Lemma pjf_sh0 : forall (rd : Z -> option Z) a, a mod 8 = 0 ->
  range_addressable rd SHADOW_OFF a 8 -> rd (shadow_of_addr SHADOW_OFF a) = Some 0.
Proof.
intros rd a Ha HR. destruct (HR (a + 7) ltac:(lia)) as (s & Hs & Hok).
assert (Es : shadow_of_addr SHADOW_OFF (a + 7) = shadow_of_addr SHADOW_OFF a).
{ unfold shadow_of_addr. f_equal. Z.div_mod_to_equations. lia. }
rewrite Es in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (H1 & H2)]; [reflexivity|].
exfalso. assert ((a + 7) mod 8 = 7) by (Z.div_mod_to_equations; lia). lia.
Qed.
(* one shadow entry of the token run, from addressability and an application home, at this walk's Bx = pBx (s7's atom
   in a resumed state) *)
Lemma pjf_shent : forall E m nn base lo hi, U E pBx = SHADOW_OFF -> U E (SOff nn 0) = base -> lo <= hi ->
  range_addressable (rd_of tfibsegs m) SHADOW_OFF (base + lo) (hi - lo) -> in_app (base + lo) (hi - lo) ->
  shent_ok tfibsegs pBx E m (mkSHE nn lo hi).
Proof.
intros E m nn base lo hi HB Hn Hlh Hra Happ. unfold shent_ok. cbn [she_m she_lo she_hi]. rewrite HB, Hn.
split; [exact Hra|]. unfold app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hn. intros a Ha.
rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* U of a register's own atom, and of the walk's shadow base pBx = SOff 23 0 (s7), in any Ereg env *)
Lemma pjf_U_atom : forall regsc extra (r : bv 5) nn z, Z.of_nat nn = bv_unsigned r ->
  YK11.getr regsc r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U (Ereg regsc extra) (SOff nn 0) = z.
Proof.
intros regsc extra r nn z Hnn Hr Hz. unfold U. rewrite fsw_SOff0, (ew_Ereg_nat regsc extra nn r Hnn), Hr.
apply wz. exact Hz.
Qed.
Lemma pjf_U_bx : forall regsc extra, YK11.getr regsc 23 = w64 SHADOW_OFF ->
  U (Ereg regsc extra) pBx = SHADOW_OFF.
Proof.
intros regsc extra H23. unfold pBx. apply (pjf_U_atom regsc extra 23%bv); [reflexivity | exact H23|].
unfold SHADOW_OFF. lia.
Qed.
(* one shadow entry at the entry state's Bx = fs_Bx (atom 32) *)
Lemma pjf_shent0 : forall E m nn base lo hi, YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff nn 0) = base -> lo <= hi ->
  range_addressable (rd_of tfibsegs m) SHADOW_OFF (base + lo) (hi - lo) -> in_app (base + lo) (hi - lo) ->
  shent_ok tfibsegs fs_Bx E m (mkSHE nn lo hi).
Proof.
intros E m nn base lo hi HB Hn Hlh Hra Happ. unfold shent_ok. cbn [she_m she_lo she_hi]. rewrite HB, Hn.
split; [exact Hra|]. unfold app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hn. intros a Ha.
rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma pjf_U_fsbx : forall regs0 xs, YP0e.U (Ereg regs0 (fs_extraT ++ xs)) fs_Bx = SHADOW_OFF.
Proof.
intros regs0 xs. unfold fs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.
(* the shadow address the entry run leaves in s6 / s4 / s11 and in the two spill words *)
Lemma pjf_U_shaddr : forall E x y, 0 <= YP0e.U E x / 8 + YP0e.U E y < 2 ^ 64 ->
  YP0e.U E (SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) y) = YP0e.U E x / 8 + YP0e.U E y.
Proof. intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3. apply zcanon_id. unfold M64. lia. Qed.
(* fs's image starts at 0x10000 *)
Lemma pjf_img_low : forall a, in_img tfibsegs a -> 0x10000 <= a.
Proof.
intros a (sg & Hin & Ha).
assert (Hall : forallb (fun s => 0x10000 <=? Z.of_N (seg_base s)) tfibsegs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall sg Hin). apply Z.leb_le in Hall. lia.
Qed.
(* fs's statics are no read-only bytes: they lie past the relro range and in writable segments only *)
Lemma pjf_pstat_not_roP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
assert (Hlo : 0xa41c0 <= a) by (destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia).
destruct Hro as [(s & Hs & Hw & Hsr) | Hr2]; [|unfold FS_RLO, FS_RHI in Hr2; lia].
assert (Hall : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa41c0)) tfibsegs
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall s Hs). rewrite Hw in Hall. cbn [orb] in Hall.
apply Z.leb_le in Hall. lia.
Qed.
(* a byte window of v next to an image byte range *)
Lemma pjf_disj_img : forall v0 lo hi c len, 0 <= lo -> lo < hi -> hi <= 56 -> 0 < len ->
  (forall x, v0 <= x < v0 + 56 -> ~ in_img tfibsegs x) -> (forall y, c <= y < c + len -> in_img tfibsegs y) ->
  v0 + hi <= c \/ c + len <= v0 + lo.
Proof.
intros v0 lo hi c len H0 H1 H2 H3 Hv Hc.
destruct (Z_le_gt_dec (v0 + hi) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + len) (v0 + lo)) as [R|R]; [right; exact R|].
exfalso. apply (Hv (Z.max c (v0 + lo))); [lia|]. apply Hc. lia.
Qed.
(* an 8-byte window off the image next to an 8-byte image cell: apart *)
Lemma pjf_disj_img_blk : forall a c, (forall y, a <= y < a + 8 -> ~ in_img tfibsegs y) ->
  (forall y, c <= y < c + 8 -> in_img tfibsegs y) -> a + 8 <= c \/ c + 8 <= a.
Proof.
intros a c Ha Hc.
destruct (Z_le_gt_dec (a + 8) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + 8) a) as [R|R]; [right; exact R|].
exfalso. apply (Ha (Z.max a c)); [lia|]. apply Hc. lia.
Qed.
(* the GOT word and the shadow-base cell are image bytes *)
Lemma pjf_got_img : forall y, tfib_D_GOT_asan_shadow_memory_dynamic_address <= y <
  tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs y.
Proof.
apply (pjf_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address
  (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8)). vm_compute. reflexivity.
Qed.
Lemma pjf_cell_img : forall y, tfib_D_asan_shadow_memory_dynamic_address <= y <
  tfib_D_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs y.
Proof.
apply (pjf_img_cover tfib_D_asan_shadow_memory_dynamic_address
  (tfib_D_asan_shadow_memory_dynamic_address + 8)). vm_compute. reflexivity.
Qed.
(* the shadow cell of an application address lies off the object it watches, off the two image cells and off the
   frame *)
Lemma pjf_shadow_apart : forall a, app_addr a ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF a <= SHADOW_OFF + 17592184995840 /\
  (a + 8 <= shadow_of_addr SHADOW_OFF a \/ shadow_of_addr SHADOW_OFF a + 8 <= a).
Proof.
intros a (H0 & Ha). pose proof asan_consts as (C1 & _).
unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_mod a 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Mq.
destruct Ha as [HL | [HH1 HH2]].
- split; [lia|]. left. lia.
- split; [lia|]. right. lia.
Qed.
(* an 8-byte window of application bytes is an in_app range *)
Lemma pjf_in_app8 : forall a, app_addr a -> app_addr (a + 7) -> in_app a 8.
Proof.
intros a (H0 & Ha) (H1 & Hb). pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
End H.

(* the callee-saved test of a concrete register (FSW_K's fsw_cs_cases shape) *)
Ltac pjf_cs_reg :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ================= image facts: fuzz/alloc.c's statics are no read-only bytes ================= *)
(* a concrete byte range that no non-writable segment covers and that misses the relro window is no read-only byte *)
Lemma pjt_roP_out : forall lo hi,
  forallb (fun s => (seg_writable s || (hi <=? Z.of_N (seg_base s)) ||
                     (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo))%bool) tfibsegs = true ->
  ((hi <=? FS_RLO) || (FS_RHI <=? lo))%bool = true ->
  forall a, lo <= a < hi -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros lo hi Hsegs Hrel a Ha [(s & Hs & Hw & Hr) | Hr].
- rewrite forallb_forall in Hsegs. pose proof (Hsegs s Hs) as E. rewrite Hw in E. cbn [orb] in E.
  apply orb_true_iff in E as [E|E]; apply Z.leb_le in E; lia.
- apply orb_true_iff in Hrel as [E|E]; apply Z.leb_le in E; lia.
Qed.
Lemma pjt_pstat_notro : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha;
  [ exact (pjt_roP_out 0xa41c0 0xa41c8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5daac0 0x5daac8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5daae0 0x5daae8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5dab00 0x5dab08 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)].
Qed.
(* the statics lie far below the shadow *)
Lemma pjt_pstat_low : forall a, inFP FS_PSTAT_FP a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; unfold SHADOW_OFF; lia.
Qed.
Lemma pjt_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn [fst]; lia. Qed.
(* ================= list algebra the tail needs on top of FSW_pj_free_dat.v ================= *)
Lemma pjt_rd_sum_nonneg : forall (A : list (Z * Z)), (forall a k, In (a, k) A -> 0 <= k) -> 0 <= rd_sum A.
Proof.
induction A as [|[a k] A IH]; intros H.
- cbn. lia.
- rewrite pjf_rd_sum_cons. cbn [snd].
  assert (Hk : 0 <= k) by (apply (H a k); left; reflexivity).
  assert (HA : 0 <= rd_sum A) by (apply IH; intros a0 k0 Hin; apply (H a0 k0); right; exact Hin).
  lia.
Qed.
Lemma pjt_inFP_nil : forall a, ~ inFP ([] : list (Z * Z)) a.
Proof. intros a (r & Hr & _). exact Hr. Qed.
Lemma pjt_rd_sum_one : forall a kb, rd_sum [(a, kb)] = kb.
Proof. intros a kb. rewrite pjf_rd_sum_cons. cbn [snd rd_sum fold_right]. lia. Qed.
Lemma pjt_nodup_app_disj : forall {X} (l1 l2 : list X) x,
  List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. apply NoDup_cons_iff in HN as [Hy HN'].
destruct H1 as [<-|H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
(* two (start, requested size) pairs of blocks of size >= 2 differ when the blocks do *)
Lemma pjt_rq_ne : forall b m q n : Z, 2 <= n -> ~ (b = q /\ m = n) -> (b, req_size m) <> (q, req_size n).
Proof.
intros b m q n Hn HNE E. injection E as E1 E2. apply HNE. split; [exact E1|].
unfold req_size in E2. destruct (Z.eqb_spec m 0) as [->|Hm]; destruct (Z.eqb_spec n 0) as [->|Hn0]; lia.
Qed.

Section Q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* AR_blocks_law's pairwise zdisjoint, pointwise *)
Lemma pjt_blocks_disj : forall ly S (W : world tfibsegs) mx md p1 n1 p2 n2 x,
  AR tfibsegs B ly S W mx md -> In (p1, n1) (ablocks B ly S) -> In (p2, n2) (ablocks B ly S) ->
  (p1, req_size n1) <> (p2, req_size n2) ->
  ~ (p1 <= x < p1 + req_size n1 /\ p2 <= x < p2 + req_size n2).
Proof.
intros ly S W mx md p1 n1 p2 n2 x HAR H1 H2 HNE [Hx1 Hx2].
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks tfibsegs B LAWS ly S W mx md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (p1, req_size n1) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (change (p1, req_size n1) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p1, n1));
      apply in_map; exact H1).
assert (I2 : In (p2, req_size n2) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (change (p2, req_size n2) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p2, n2));
      apply in_map; exact H2).
destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 HNE) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.
(* AR_sep_law: a live block and a live fake frame never share a byte *)
Lemma pjt_block_frame_disj : forall ly S (W : world tfibsegs) mx md p n cid pos x,
  AR tfibsegs B ly S W mx md -> In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  ~ (p <= x < p + req_size n /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S W mx md p n cid pos x HAR Hb Hf [Hx1 Hx2].
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_sep tfibsegs B LAWS ly S W mx md HAR) as (PS & _).
destruct (YG0s.pairwise_app_inv zdisjoint _ _ PS) as (_ & _ & PX).
pose proof (PX (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid)
  ltac:(change (p, req_size n) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p, n));
        apply in_map; exact Hb)
  ltac:(change (frame_addr ly cid pos, fs_frame_bytes cid)
          with ((fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (cid, pos));
        apply in_map; exact Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
End Q.

Ltac pjt_rd HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ _ ?sC _ =>
    let e := eval vm_compute in (sr_get (ss_regs sC) r) in
    change (sr_get (ss_regs sC) r) with e end;
  rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia).


Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0 lib/B/FSH_Base.v FsShadowSyms; owner RELOC: B's GOT word 0x9fc10 and cell 0xa8438 *)
Hypothesis HSS : FsShadowSyms B.
(* owner ALLOC (a Theorem Labs lane, lib/B/FSH_Fn_alloc.v): the room premise is on p <> 0 only (a null free has no event) *)
Hypothesis fs_fuzz_free_spec : @fuzz_free_spec fx rc SK tfibsegs B.
(* owner POISON-U (a Theorem Labs lane, lib/A/FSupoisonU.v, the ARU form of the donor's __asan_memset contract; named in
   lib/B/FSH_Fn_reader.v's premise table). PC_memset is lib/B/FSH_Base.v's 0x5222c (sym __asan_memset): the walk
   never names a tfib_[AE]_memset table entry, which now means musl's memset (a Theorem Labs lane, 2026-10-29 08:29Z). *)
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.
(* a reader block whose HEAD word lies off a callee's footprint survives the call *)
Lemma pjf_rblock_kept : forall STK1 sp1 FP1 lyc Sc Uc (Wc : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc p kp,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, p - HEAD <= x < p - HEAD + 8 -> ~ inFP FP1 x) ->
  fs_rblock tfibsegs B lyc Sc Wc memc p kp -> fs_rblock tfibsegs B ly' S' W' mem' p kp.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc Wc memc mdc ly' S' U' W' mem' md' kc p kp HJ HU HO' HP' HF (Hin & Hal & Hk & Hv).
pose proof (req_size_pos (kp + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
split; [|split; [exact Hal | split; [exact Hk|]]].
- apply (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc Wc (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
    (p - HEAD) (kp + HEAD) (p - HEAD) HJ Hin); [unfold HEAD in *; lia | apply HF; unfold HEAD; lia].
- intros j Hj.
  assert (E : mrestrict (w_H W') mem' (Z_to_bv 64 (p - HEAD + Z.of_nat j)) =
              mrestrict (w_H Wc) memc (Z_to_bv 64 (p - HEAD + Z.of_nat j))).
  { refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc Wc memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP'
      _ _)).
    - left. exists (p - HEAD), (kp + HEAD). split; [exact Hin | unfold HEAD in *; lia].
    - apply HF. lia. }
  unfold mbyte. rewrite E. exact (Hv j Hj).
Qed.

(* ================= the walk of one level, the entry state as Section variables ================= *)
Section N.
Variable k : nat.
(* the level-indexed induction (FSH_Fn_FORM.md 3b): level k + 1 for the kid calls; discharged in pj_free_holds *)
Hypothesis REC : @pj_free_spec fx rc SK tfibsegs B (S k).
Variables (ly : alayout) (S0 : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (v : Z) (D : list (Z * Z)) (live peak cnt fail : Z).
Hypothesis Hk : (k <= 2)%nat.
Hypothesis HPRE : fpreU tfibsegs B (STK_pj_free (2 - k)) ly S0 U W regs mem md ch.
Hypothesis HHD0 : FSupoisonU.fs_heads B ly S0 U.
Hypothesis H10 : YK11.getr regs 10 = w64 v.
Hypothesis HV : v <> 0.
Hypothesis HPO : pobj tfibsegs B ly S0 W mem v.
Hypothesis HVS : v + 56 <= spZ regs - STK_pj_free (2 - k) \/ spZ regs <= v.
Hypothesis HBK : rd_blocks_ok tfibsegs B ly S0 W mem D.
Hypothesis HUI : incl (rd_heads D) U.
Hypothesis HG : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis HSUM : rd_sum D <= live.
Hypothesis HEV : st_nev S0 + EV_pj_free D <= EV_MAX.
(* the node's shape (PjStruct.pj_fshape of pjf_fd_items at depth 2 - k) *)
Variables (ty num str kids keys n cap : Z) (ks : bool) (Ds Dk Dy Di : list (Z * Z)).
Hypothesis HND : NoDup D.
Hypothesis HAP : PjStruct.pj_apart D v.
Hypothesis HHDR : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys n cap.
Hypothesis HSTR : str = 0 /\ Ds = [] \/ exists k0, In (str, k0) D /\ Ds = [(str, k0)].
Hypothesis HKIDS : kids = 0 /\ n = 0 /\ Dk = [] \/ exists k0, In (kids, k0) D /\ 56 * n <= k0 /\ Dk = [(kids, k0)].
Hypothesis HKEYS : keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k0, In (keys, k0) D /\ 8 * n <= k0 /\ Dy = [(keys, k0)].
Hypothesis HPERM : Permutation D (Ds ++ Dk ++ Dy ++ Di).
Hypothesis HITEMS : PjStruct.pf_items tfibsegs (mrestrict (w_H W) mem) (fun a n0 => In (a, n0) D)
  (pjf_Pd tfibsegs (mrestrict (w_H W) mem) (fun a n0 => In (a, n0) D) (2 - k)) ks kids keys (Z.to_nat n) Di.

Let STK : Z := STK_pj_free (2 - k).
Let sp0 : Z := spZ regs.
Let FP : list (Z * Z) := (v, v + 56) :: ablocks_fp (rd_hblocks D) ++ FS_PSTAT_FP.
Let m0 : word -> option byte := mrestrict (w_H W) mem.
Let Qf : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' _ mem' _ =>
    Permutation (ablocks B ly S0) (rd_hblocks D ++ ablocks B ly' S') /\
    (v <> 0 -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W') mem') v /\ pobj tfibsegs B ly' S' W' mem' v) /\
    fs_glob tfibsegs W' mem' (live - rd_sum D) peak cnt fail.
Let GOAL : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B STK sp0 FP regs ly S0 U W mem md (EV_pj_free D) (udrop U (rd_heads D)) Qf.

(* the frame: the thirteen saved words and the two spilled shadow words (B's 8(sp) / 16(sp)) *)
Definition pjf_frm (Wc : world tfibsegs) (memc : word -> option byte) : Prop :=
  (forall j, (j < 13)%nat ->
     val_mem tfibsegs (mrestrict (w_H Wc) memc) (sp0 - 8 - 8 * Z.of_nat j) 8
       (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (sp0 - 120) 8 ((v + 24) / 8) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (sp0 - 112) 8 ((v + 32) / 8).
(* the registers every resumed point has (callee-saved, set at entry): sp, gp, tp as at entry, s0 .. s3, s6, s7 *)
Definition pjf_regs (r : bvmap 5 word) : Prop :=
  spZ r = sp0 - 128 /\ YK11.getr r 3 = YK11.getr regs 3 /\ YK11.getr r 4 = YK11.getr regs 4 /\
  YK11.getr r 8 = w64 v /\ YK11.getr r 9 = w64 (v + 32) /\ YK11.getr r 18 = w64 (v + 40) /\
  YK11.getr r 19 = w64 (v + 24) /\ YK11.getr r 22 = w64 (shadow_of_addr SHADOW_OFF (v + 40)) /\
  YK11.getr r 23 = w64 SHADOW_OFF.
(* ... in the loop at kid i: s4 / s11 the shadow bytes of v + 32 / v + 24, s5 = 56, s8 = 56 i, s9 = 8 i, s10 = i *)
Definition pjf_lregs (i : nat) (r : bvmap 5 word) : Prop :=
  pjf_regs r /\ YK11.getr r 20 = w64 (shadow_of_addr SHADOW_OFF (v + 32)) /\
  YK11.getr r 27 = w64 (shadow_of_addr SHADOW_OFF (v + 24)) /\ YK11.getr r 21 = w64 56 /\
  YK11.getr r 24 = w64 (56 * Z.of_nat i) /\ YK11.getr r 25 = w64 (8 * Z.of_nat i) /\
  YK11.getr r 26 = w64 (Z.of_nat i).
(* the bytes kept since entry while kid ik and key iy are next: v, the kids and keys slots not yet passed, and the
   blocks Dr of the items not yet freed *)
Definition pjf_FPS (ik iy : nat) (Dr : list (Z * Z)) (x : Z) : Prop :=
  (v <= x < v + 56) \/ (ks = true /\ keys + 8 * Z.of_nat iy <= x < keys + 8 * n) \/
  (kids + 56 * Z.of_nat ik <= x < kids + 56 * n) \/ (exists b, In b Dr /\ PjStruct.pj_holds b x).
(* the invariant of a resumed point: Dfr freed, Rem not yet (Permutation D (Dfr ++ Rem)), the bytes F kept *)
Definition pjf_inv (F : Z -> Prop) (Dfr Rem : list (Z * Z)) lyc Sc Uc (Wc : world tfibsegs) memc mdc : Prop :=
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) /\
  ARU tfibsegs B lyc Sc Uc Wc memc mdc /\ FSupoisonU.fs_heads B lyc Sc Uc /\ pjf_frm Wc memc /\
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) /\ Uc = udrop U (rd_heads Dfr) /\
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail /\ Permutation D (Dfr ++ Rem) /\
  rd_blocks_ok tfibsegs B lyc Sc Wc memc Rem /\ pobj tfibsegs B lyc Sc Wc memc v /\
  (forall x : word, F (bv_unsigned x) -> mrestrict (w_H Wc) memc x = m0 x) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).

(* ---- the entry's numerals and bounds (no literal STK_ numeral: the owner's stack budget moves, 2026-10-29 08:0xZ) ---- *)
Lemma pjf_STK : 128 + 4096 <= STK /\ STK_fuzz_free + 128 <= STK /\
  ((k < 2)%nat -> STK_pj_free (2 - S k) + 128 <= STK) /\ STK <= 2 ^ 20.
Proof.
assert (E0 : STK_pj_free 0 = ltac:(let z := eval vm_compute in (STK_pj_free 0) in exact z))
  by (vm_compute; reflexivity).
assert (E1 : STK_pj_free 1 = ltac:(let z := eval vm_compute in (STK_pj_free 1) in exact z))
  by (vm_compute; reflexivity).
assert (E2 : STK_pj_free 2 = ltac:(let z := eval vm_compute in (STK_pj_free 2) in exact z))
  by (vm_compute; reflexivity).
assert (Ef : STK_fuzz_free = ltac:(let z := eval vm_compute in STK_fuzz_free in exact z))
  by (vm_compute; reflexivity).
unfold STK. assert (Hc : (k = 0 \/ k = 1 \/ k = 2)%nat) by lia.
destruct Hc as [Hk0 | [Hk0 | Hk0]]; rewrite Hk0; cbn [Nat.sub]; rewrite ?E0, ?E1, ?E2, Ef; (split; [lia|]);
  (split; [lia|]); (split; [intros Hlt; cbn [Nat.sub]; rewrite ?E0, ?E1, ?E2; lia | lia]).
Qed.
(* the kid call's window, at level k + 1 *)
Lemma pjf_STK1 : (k < 2)%nat -> 0 <= STK_pj_free (2 - S k) /\ STK_pj_free (2 - S k) + 128 <= STK.
Proof.
intros Hk2.
assert (E0 : STK_pj_free 0 = ltac:(let z := eval vm_compute in (STK_pj_free 0) in exact z))
  by (vm_compute; reflexivity).
assert (E1 : STK_pj_free 1 = ltac:(let z := eval vm_compute in (STK_pj_free 1) in exact z))
  by (vm_compute; reflexivity).
assert (E2 : STK_pj_free 2 = ltac:(let z := eval vm_compute in (STK_pj_free 2) in exact z))
  by (vm_compute; reflexivity).
unfold STK. assert (Hc : (k = 0 \/ k = 1)%nat) by lia.
destruct Hc as [Hk0 | Hk0]; rewrite Hk0; cbn [Nat.sub]; rewrite ?E0, ?E1, ?E2; lia.
Qed.
Lemma pjf_entry_facts :
  spZ regs mod 16 = 0 /\ alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  4096 <= v /\ v + 56 <= alloc_ceiling /\ v mod 8 = 0 /\ YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs.
Proof.
destruct HPRE as [HAPU _].
pose proof (fsw_sp B _ ly S0 U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof HAPU as (HAP0 & _ & _). pose proof HAP0 as (HAR & Hra & Hra4 & _).
destruct (fsw_pobj_low B ly S0 W (unpoison U mem) md mem v HAR HPO) as (Hv0 & Hv1).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & H & _)|(_ & H & _)] _]; exact H).
unfold STK. repeat split; assumption.
Qed.

(* ---- the blocks of D: one size per start, and pairwise apart while live ---- *)
Lemma pjf_HAR0 : AR tfibsegs B ly S0 W (unpoison U mem) md.
Proof. exact (proj1 (proj1 (proj1 HPRE))). Qed.
Lemma pjf_req : forall n0, 1 <= n0 -> req_size n0 = n0.
Proof. intros n0 H. destruct (req_size_bounds n0 ltac:(lia)) as (E & _). lia. Qed.
Lemma pjf_D_uniq : forall a k1 k2, In (a, k1) D -> In (a, k2) D -> k1 = k2.
Proof.
intros a k1 k2 H1 H2. destruct (Z.eq_dec k1 k2) as [E|NE]; [exact E|exfalso].
destruct (HBK a k1 H1) as (B1 & _ & P1 & _). destruct (HBK a k2 H2) as (B2 & _ & P2 & _).
pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S0 W (unpoison U mem) md _ _ _ _ pjf_HAR0 B1 B2
  ltac:(intros E; injection E; intros; lia)) as Hd.
rewrite !pjf_req in Hd by (unfold HEAD; lia). unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia.
Qed.
Lemma pjf_blk_sep : forall lyc Sc (Wc : world tfibsegs) mx mdc memc a1 k1 a2 k2,
  AR tfibsegs B lyc Sc Wc mx mdc -> fs_rblock tfibsegs B lyc Sc Wc memc a1 k1 ->
  fs_rblock tfibsegs B lyc Sc Wc memc a2 k2 -> (a1, k1) <> (a2, k2) ->
  a1 + k1 <= a2 - HEAD \/ a2 + k2 <= a1 - HEAD.
Proof.
intros lyc Sc Wc mx mdc memc a1 k1 a2 k2 HAR (B1 & _ & P1 & _) (B2 & _ & P2 & _) Hne.
pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) lyc Sc Wc mx mdc _ _ _ _ HAR B1 B2
  ltac:(intros E; injection E; intros E1 E2; apply Hne; f_equal; lia)) as Hd.
rewrite !pjf_req in Hd by (unfold HEAD; lia). unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia.
Qed.
Lemma pjf_v_apart : forall lyc Sc (Wc : world tfibsegs) mx mdc memc a ka,
  AR tfibsegs B lyc Sc Wc mx mdc -> pobj tfibsegs B lyc Sc Wc memc v -> In (a, ka) D ->
  fs_rblock tfibsegs B lyc Sc Wc memc a ka -> v + 56 <= a - HEAD \/ a + ka <= v.
Proof.
intros lyc Sc Wc mx mdc memc a ka HAR HPOc HinD (Bk & _ & Pk & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Rk : req_size (ka + HEAD) = ka + HEAD) by (apply pjf_req; unfold HEAD; lia).
destruct HPOc as [[((cid & pos & Hin & Hc & Hal & H1 & H2) & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
- pose proof (sep_block_frame tfibsegs B LAWS lyc Sc Wc mx mdc _ _ cid pos HAR Bk Hin) as Hd.
  rewrite Rk in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia.
- assert (Hcase : (b = a - HEAD /\ m = ka + HEAD) \/ (b, m) <> (a - HEAD, ka + HEAD)).
  { destruct (Z.eq_dec b (a - HEAD)) as [E1|E1]; [destruct (Z.eq_dec m (ka + HEAD)) as [E2|E2]|].
    - left. split; assumption.
    - right. intros E. injection E as _ E'. exact (E2 E').
    - right. intros E. injection E as E' _. exact (E1 E'). }
  destruct Hcase as [(-> & ->) | NE].
  + rewrite Rk in H2. exfalso.
    apply (HAP (a, ka) v HinD); [unfold PjStruct.pj_holds; cbn [fst snd]; unfold HEAD in *; lia | lia].
  + pose proof (sep_blocks tfibsegs B LAWS lyc Sc Wc mx mdc _ _ _ _ HAR Hin Bk NE) as Hd.
    rewrite Rk in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia.
Qed.
Lemma pjf_rd_sum_nonneg : forall L, (forall a ka, In (a, ka) L -> 0 < ka) -> 0 <= rd_sum L.
Proof.
induction L as [|[a ka] L IH]; intros H; [cbn; lia|]. rewrite pjf_rd_sum_cons. cbn [snd].
pose proof (H a ka (or_introl eq_refl)). pose proof (IH (fun a' k' Hin => H a' k' (or_intror Hin))). lia.
Qed.
Lemma pjf_EV_nonneg : forall L, 0 <= EV_pj_free L.
Proof. intros L. unfold EV_pj_free, EV_fuzz_free. lia. Qed.

(* ---- the resumed env: the shadow base (fs_extraT), the thirteen saved registers, then the walk's own atoms ---- *)
Definition pjf_env (regsc : bvmap 5 word) (xs : list word) : env := Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs).
Lemma pjf_ew_saved : forall regsc xs j, (j < 13)%nat ->
  sv_denot (pjf_env regsc xs) (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0).
Proof.
intros regsc xs j Hj. unfold pjf_env. rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia.
rewrite ew_Ereg_extra. cbn [fs_extraT app nth]. apply app_nth1. unfold pjf_saved. rewrite length_map. cbn. lia.
Qed.
Lemma pjf_ew_sav : forall regsc xs nn j, nn = (33 + j)%nat -> (j < 13)%nat ->
  sv_denot (pjf_env regsc xs) (SOff nn 0) = nth j (pjf_saved regs) (Z_to_bv 64 0).
Proof. intros regsc xs nn j -> Hj. exact (pjf_ew_saved regsc xs j Hj). Qed.
(* ... and the walk's own atoms, from 46 (fs_extraT is one word, pjf_saved thirteen) *)
Lemma pjf_ew_x : forall regsc xs nn j, nn = (46 + j)%nat ->
  ew (pjf_env regsc xs) nn = nth j xs (Z_to_bv 64 0).
Proof.
intros regsc xs nn j ->. unfold pjf_env. replace (46 + j)%nat with (32 + S (13 + j))%nat by lia.
rewrite ew_Ereg_extra. cbn [fs_extraT app nth].
rewrite app_nth2 by (unfold pjf_saved, pjf_sregs; rewrite length_map; cbn [length]; lia).
unfold pjf_saved, pjf_sregs. rewrite length_map. cbn [length map].
replace (13 + j - 13)%nat with j by lia. reflexivity.
Qed.
(* the spilled shadow words, as the frame chunks name them *)
Lemma pjf_spill_denot : forall E nn a, bv_unsigned (ew E nn) = a -> 0 <= a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff nn 0) (SLit 3)) = Z_to_bv 64 (a / 8).
Proof.
intros E nn a Ha Hr. rewrite denot_lit_U, U_srl3. f_equal. f_equal.
rewrite U_SOff, Ha, Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.
(* the fifteen frame chunks, from the frame's words *)
Lemma pjf_cs_ok : forall E m, bv_unsigned (ew E 2) = sp0 - 128 ->
  (forall j, (j < 13)%nat -> sv_denot E (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0)) ->
  bv_unsigned (ew E 19) = v + 24 -> bv_unsigned (ew E 9) = v + 32 ->
  (forall j, (j < 13)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))) ->
  val_mem tfibsegs m (sp0 - 120) 8 ((v + 24) / 8) -> val_mem tfibsegs m (sp0 - 112) 8 ((v + 32) / 8) ->
  Forall (YP09.chunk_ok tfibsegs E m (sp0 - 128)) pjf_cs.
Proof.
intros E m E2 He E19 E9 Hv Hs1 Hs2.
pose proof pjf_entry_facts as (_ & _ & _ & Hv0 & Hv1 & _). pose proof asan_consts as (C1 & _).
assert (C : forall j off, (j < 13)%nat -> off = 120 - 8 * Z.of_nat j ->
  YP09.chunk_ok tfibsegs E m (sp0 - 128) (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0)))).
{ intros j off Hj ->. apply (chunk_ok_val tfibsegs E m (sp0 - 128) _ 8%N (SOff (33 + j) 0)
    (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))).
  - rewrite (He j Hj). symmetry. apply Z_to_bv_bv_unsigned.
  - apply u64_range.
  - cbn; lia.
  - change (N.to_nat 8) with 8%nat. replace (sp0 - 128 + (120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
    exact (Hv j Hj). }
unfold pjf_cs. apply Forall_cons.
{ apply (chunk_ok_val tfibsegs E m (sp0 - 128) 8 8%N (SAlu ALU_SRL (SOff 19 0) (SLit 3)) ((v + 24) / 8));
    [ exact (pjf_spill_denot E 19 (v + 24) E19 ltac:(lia)) | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia |].
  change (N.to_nat 8) with 8%nat. replace (sp0 - 128 + 8) with (sp0 - 120) by lia. exact Hs1. }
apply Forall_cons.
{ apply (chunk_ok_val tfibsegs E m (sp0 - 128) 16 8%N (SAlu ALU_SRL (SOff 9 0) (SLit 3)) ((v + 32) / 8));
    [ exact (pjf_spill_denot E 9 (v + 32) E9 ltac:(lia)) | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia |].
  change (N.to_nat 8) with 8%nat. replace (sp0 - 128 + 16) with (sp0 - 112) by lia. exact Hs2. }
repeat (apply Forall_cons; [first
  [ apply (C 12%nat); [lia | reflexivity] | apply (C 11%nat); [lia | reflexivity] | apply (C 10%nat); [lia | reflexivity]
  | apply (C 9%nat); [lia | reflexivity] | apply (C 8%nat); [lia | reflexivity] | apply (C 7%nat); [lia | reflexivity]
  | apply (C 6%nat); [lia | reflexivity] | apply (C 5%nat); [lia | reflexivity] | apply (C 4%nat); [lia | reflexivity]
  | apply (C 3%nat); [lia | reflexivity] | apply (C 2%nat); [lia | reflexivity] | apply (C 1%nat); [lia | reflexivity]
  | apply (C 0%nat); [lia | reflexivity]]|]).
apply Forall_nil.
Qed.
(* the frame's words, read back from a frame region of the walk's states *)
Lemma pjf_frm_of_region : forall E (m : word -> option byte),
  YP09.region_ok tfibsegs E m (fstk_ret 128 pjf_cs) -> bv_unsigned (ew E 2) = sp0 - 128 ->
  (forall j, (j < 13)%nat -> sv_denot E (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0)) ->
  bv_unsigned (ew E 19) = v + 24 -> bv_unsigned (ew E 9) = v + 32 ->
  (forall j, (j < 13)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))) /\
  val_mem tfibsegs m (sp0 - 120) 8 ((v + 24) / 8) /\ val_mem tfibsegs m (sp0 - 112) 8 ((v + 32) / 8).
Proof.
intros E m HR E2 He E19 E9.
pose proof pjf_entry_facts as (_ & _ & _ & Hv0 & Hv1 & _). pose proof asan_consts as (C1 & _).
split; [|split].
- intros j Hj.
  replace (sp0 - 8 - 8 * Z.of_nat j) with ((sp0 - 128) + (120 - 8 * Z.of_nat j)) by lia.
  apply (fsw_field E m 2 (sp0 - 128) pjf_cs 0 128 0 128 (120 - 8 * Z.of_nat j) 8%N (SOff (33 + j) 0));
    [exact HR | exact E2 | | | |].
  + unfold pjf_cs.
    assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10
                  \/ j = 11 \/ j = 12)%nat) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
      cbn; tauto.
  + rewrite (He j Hj). symmetry. apply Z_to_bv_bv_unsigned.
  + apply u64_range.
  + cbn; lia.
- replace (sp0 - 120) with ((sp0 - 128) + 8) by lia.
  apply (fsw_field E m 2 (sp0 - 128) pjf_cs 0 128 0 128 8 8%N (SAlu ALU_SRL (SOff 19 0) (SLit 3)));
    [exact HR | exact E2 | cbn; tauto | exact (pjf_spill_denot E 19 (v + 24) E19 ltac:(lia))
     | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia].
- replace (sp0 - 112) with ((sp0 - 128) + 16) by lia.
  apply (fsw_field E m 2 (sp0 - 128) pjf_cs 0 128 0 128 16 8%N (SAlu ALU_SRL (SOff 9 0) (SLit 3)));
    [exact HR | exact E2 | cbn; tauto | exact (pjf_spill_denot E 9 (v + 32) E9 ltac:(lia))
     | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia].
Qed.

(* ---- a resumed state, built from the machine's registers and memory ---- *)
Lemma pjf_reseatC : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc pc rs at_ cs al xs,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_regs regsc ->
  (forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pjf_frm Wc memc ->
  regions_wf (fsT_ret_regions 128 pjf_cs rs) = true ->
  Forall (YP09.region_ok tfibsegs (pjf_env regsc xs) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (pjf_env regsc xs) (fsT_ret_regions 128 pjf_cs rs) ->
  atoms_ok (pjf_env regsc xs) at_ ->
  alias_ok (pjf_env regsc xs) al ->
  conds_ok (pjf_env regsc xs) cs ->
  st_ok tfibsegs (pjf_env regsc xs) (pjssc pc rs at_ cs al)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc pc rs at_ cs al xs HARU HR Hpres Hfrm Hwf Hrs Hpd Hat Hal Hcs.
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof HSS as [Hgot Hcell].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HARU as (HAR & _ & _).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & _).
pose proof pjf_STK as (HSTK & _).
destruct (fsw_got_shadow B lyc Sc Wc (unpoison Uc memc) mdc Hgot Hcell HAR) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H Wc) memc) x = mbyte tfibsegs (mrestrict (w_H Wc) (unpoison Uc memc)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B lyc Sc Uc Wc memc mdc (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v', 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H Wc) (unpoison Uc memc)) a 8 v' -> val_mem tfibsegs (mrestrict (w_H Wc) memc) a 8 v').
{ intros a v' Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H Wc) memc) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H Wc) (unpoison Uc memc) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H Wc) memc) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H Wc) (unpoison Uc memc) _ _ Kcell)]. }
unfold pjf_env in Hrs, Hpd, Hat, Hal, Hcs |- *.
set (E := Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) in *.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 128)
  by (subst E; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regsc _ 23 23%bv eq_refl), H23; unfold w64; apply wz;
      unfold SHADOW_OFF; lia).
assert (E19 : bv_unsigned (ew E 19) = v + 24)
  by (subst E; rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19; unfold w64; apply wz; lia).
assert (E9 : bv_unsigned (ew E 9) = v + 32)
  by (subst E; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
pose proof Hfrm as (Hfj & Hf1 & Hf2).
rewrite restrict_mkst_fx. unfold pjssc. apply (entry_st_ok_full tfibsegs); fold E.
- apply regs_ok_Ereg.
- exact Hwf.
- unfold fsT_ret_regions. cbn [app]. constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    * apply (pjf_cs_ok E _ E2); [| exact E19 | exact E9 | exact Hfj | exact Hf1 | exact Hf2].
      intros j Hj. subst E. exact (pjf_ew_saved regsc xs j Hj).
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; [exact Hcs | exact Hal]]. cbn [f_atoms pjf_Gc atoms_ok]. unfold afact_ok at 1 2 3.
  cbn [af_lo af_hi af_al2]. rewrite E2, U32, U23. change (2 ^ 4) with 16. rewrite Z.pow_0_r.
  split; [split; [lia | split; [unfold sp0; rewrite Zminus_mod, Hal16; reflexivity | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact Hat].
Qed.
(* the cs = [] instance *)
Lemma pjf_reseat : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc pc rs at_ al xs,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_regs regsc ->
  (forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pjf_frm Wc memc ->
  regions_wf (fsT_ret_regions 128 pjf_cs rs) = true ->
  Forall (YP09.region_ok tfibsegs (pjf_env regsc xs) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (pjf_env regsc xs) (fsT_ret_regions 128 pjf_cs rs) ->
  atoms_ok (pjf_env regsc xs) at_ ->
  alias_ok (pjf_env regsc xs) al ->
  st_ok tfibsegs (pjf_env regsc xs) (pjss pc rs at_ al)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc pc rs at_ al xs HARU HR Hpres Hfrm Hwf Hrs Hpd Hat Hal.
unfold pjss.
exact (pjf_reseatC lyc Sc Uc Wc regsc memc mdc pc rs at_ [] al xs HARU HR Hpres Hfrm Hwf Hrs Hpd Hat Hal I).
Qed.

(* ---- the region shapes of the resumed states ---- *)
(* a shadow cell of an 8-aligned addressable word, as a one-byte region based at the register that holds its address *)
Lemma pjf_shr_ok : forall regsc xs (r : bv 5) nn (Wc : world tfibsegs) memc a,
  Z.of_nat nn = bv_unsigned r -> YK11.getr regsc r = w64 (shadow_of_addr SHADOW_OFF a) ->
  0 <= a -> a + 8 <= alloc_ceiling -> a mod 8 = 0 ->
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF a 8 ->
  YP09.region_ok tfibsegs (pjf_env regsc xs) (mrestrict (w_H Wc) memc) (shr nn).
Proof.
intros regsc xs r nn Wc memc a Hnn Hr Ha0 Ha1 Ha8 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS : 0 <= shadow_of_addr SHADOW_OFF a < 2 ^ 64)
  by (unfold shadow_of_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (E : base_val (pjf_env regsc xs) (Some nn) = shadow_of_addr SHADOW_OFF a).
{ cbn [base_val]. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ nn r Hnn), Hr. unfold w64. apply wz. exact HS. }
unfold region_ok, shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite E.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs (pjf_env regsc xs) _ (shadow_of_addr SHADOW_OFF a) 0 1 (SLit 0) 0);
  [reflexivity | cbn; lia | cbn; lia |].
intros j Hj. cbn [N.to_nat Pos.to_nat Pos.iter_op] in Hj. replace j with 0%nat by lia.
cbn [Z.of_nat]. rewrite !Z.add_0_r. cbn [YO0f.le_byte].
rewrite (pjf_mbyte_of_aview (w_H Wc) memc (shadow_of_addr SHADOW_OFF a) 0
  (pjf_sh0 (aview tfibsegs (w_H Wc) memc) a Ha8 HRA)).
reflexivity.
Qed.
Lemma pjf_fld_ok : forall regsc xs (r : bv 5) nn o x (Wc : world tfibsegs) memc a val,
  Z.of_nat nn = bv_unsigned r -> YK11.getr regsc r = w64 a -> 0 <= a -> a + o + 8 <= 2 ^ 64 -> 0 <= o ->
  sv_denot (pjf_env regsc xs) (SOff x 0) = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (a + o) 8 val ->
  YP09.region_ok tfibsegs (pjf_env regsc xs) (mrestrict (w_H Wc) memc) (fld nn o x).
Proof.
intros regsc xs r nn o x Wc memc a val Hnn Hr Ha0 Ha1 Ho Hx Hv Hm.
assert (E : base_val (pjf_env regsc xs) (Some nn) = a).
{ cbn [base_val]. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ nn r Hnn), Hr. unfold w64. apply wz. lia. }
unfold region_ok, fld. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite E.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs (pjf_env regsc xs) _ a o 8 (SOff x 0) val);
  [exact Hx | cbn; lia | cbn; lia | exact Hm].
Qed.
Lemma pjf_fld0_ok : forall regsc xs (r : bv 5) nn o (Wc : world tfibsegs) memc a,
  Z.of_nat nn = bv_unsigned r -> YK11.getr regsc r = w64 a -> 0 <= a -> a + o + 8 <= 2 ^ 64 -> 0 <= o ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (a + o) 8 0 ->
  YP09.region_ok tfibsegs (pjf_env regsc xs) (mrestrict (w_H Wc) memc) (fld0 nn o).
Proof.
intros regsc xs r nn o Wc memc a Hnn Hr Ha0 Ha1 Ho Hm.
assert (E : base_val (pjf_env regsc xs) (Some nn) = a).
{ cbn [base_val]. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ nn r Hnn), Hr. unfold w64. apply wz. lia. }
unfold region_ok, fld0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite E.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs (pjf_env regsc xs) _ a o 8 (SLit 0) 0);
  [reflexivity | cbn; lia | cbn; lia | exact Hm].
Qed.

(* ---- the three UBSan conditions the resumed states assume (B only) ---- *)
(* 0x83744 `bltu a2, a0`: the kid pointer kids + 56 i does not wrap *)
Lemma pjf_acond_wrap : forall E i kidsv, bv_unsigned (ew E 26) = Z.of_nat i -> bv_unsigned (ew E 46) = kidsv ->
  Z.of_nat i <= 2 ^ 54 -> 0 <= kidsv <= PJF_CEIL -> acond_ok E pjf_Cwrap.
Proof.
intros E i kidsv E26 E46 Hi Hkc.
assert (Hu26 : YP0e.U E (SOff 26 0) = Z.of_nat i)
  by (rewrite U_SOff, E26, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (Hu46 : YP0e.U E (SOff 46 0) = kidsv)
  by (rewrite U_SOff, E46, Z.add_0_r; apply zcanon_id; unfold M64, PJF_CEIL in *; lia).
assert (Hmul : YP0e.U E (SMd M_MUL (SOff 26 0) (SLit 56)) = Z.of_nat i * 56).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Hu26, U_SLit. change (zcanon 56) with 56.
  apply zcanon_id. unfold M64. lia. }
unfold acond_ok, pjf_Cwrap. cbn [ac_c ac_a ac_b branch_taken]. apply negb_true_iff.
unfold bv_ltu. apply Z.ltb_ge.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 26 0) (SLit 56)) (SOff 46 0))))
  with (YP0e.U E (SAlu ALU_ADD (SMd M_MUL (SOff 26 0) (SLit 56)) (SOff 46 0))).
change (bv_unsigned (sv_denot E (SOff 46 0))) with (YP0e.U E (SOff 46 0)).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hmul, Hu46.
rewrite zcanon_id by (unfold M64, PJF_CEIL in *; lia). lia.
Qed.
(* 0x83758 `bnez a1`: 56 i does not overflow (mulh i 56 = sra (mul i 56) 63 = 0) *)
Lemma pjf_acond_mulh : forall E i, bv_unsigned (ew E 26) = Z.of_nat i -> bv_unsigned (ew E 21) = 56 ->
  Z.of_nat i <= 2 ^ 54 -> acond_ok E pjf_Cmulh.
Proof.
intros E i E26 E21 Hi.
assert (Hu26 : YP0e.U E (SOff 26 0) = Z.of_nat i)
  by (rewrite U_SOff, E26, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (Hu21 : YP0e.U E (SOff 21 0) = 56)
  by (rewrite U_SOff, E21, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (Hmulh : YP0e.U E (SMd M_MULH (SOff 26 0) (SOff 21 0)) = 0).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Hu26, Hu21.
  rewrite (swrap64_id (Z.of_nat i)) by (unfold half64; lia).
  rewrite (swrap64_id 56) by (unfold half64; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (Hmul : YP0e.U E (SMd M_MUL (SOff 26 0) (SLit 56)) = Z.of_nat i * 56).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Hu26, U_SLit. change (zcanon 56) with 56.
  apply zcanon_id. unfold M64. lia. }
assert (Hsra : YP0e.U E (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Hmul, U_SLit. change (Z.land (zcanon 63) 63) with 63.
  rewrite (swrap64_id (Z.of_nat i * 56)) by (unfold half64; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (Hxor : YP0e.U E (SAlu ALU_XOR (SMd M_MULH (SOff 26 0) (SOff 21 0))
  (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63))) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Hmulh, Hsra. reflexivity. }
assert (Hsltu : YP0e.U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 26 0) (SOff 21 0))
  (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63)))) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Hxor, U_SLit. change (zcanon 0) with 0.
  replace (0 <? 0) with false by reflexivity. reflexivity. }
unfold acond_ok, pjf_Cmulh. cbn [ac_c ac_a ac_b branch_taken]. apply bv_eqb_true_iff. apply U_inj.
change (bv_unsigned (sv_denot E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 26 0) (SOff 21 0))
  (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63))))))
  with (YP0e.U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 26 0) (SOff 21 0))
  (SAlu ALU_SRA (SMd M_MUL (SOff 26 0) (SLit 56)) (SLit 63))))).
change (bv_unsigned (sv_denot E (SLit 0))) with (YP0e.U E (SLit 0)).
rewrite Hsltu, U_SLit. reflexivity.
Qed.
(* 0x83778 `bltu a1, s9`: the key slot keys + 8 i does not wrap *)
Lemma pjf_acond_key : forall E keysv ei, ew E 46 = Z_to_bv 64 keysv -> bv_unsigned (ew E 25) = ei ->
  0 <= keysv <= PJF_CEIL -> 0 <= ei <= 2 ^ 57 -> acond_ok E pjf_Ckey.
Proof.
intros E keysv ei E46 E25 Hkk He.
assert (Hnot : YP0e.U E (SAlu ALU_XOR (SOff 46 0) (SLit (-1))) = 2 ^ 64 - 1 - keysv)
  by (apply (U_not E 46 keysv E46); unfold PJF_CEIL in *; lia).
assert (Hei : YP0e.U E (SOff 25 0) = ei)
  by (rewrite U_SOff, E25, Z.add_0_r; apply zcanon_id; unfold M64; lia).
unfold acond_ok, pjf_Ckey. cbn [ac_c ac_a ac_b branch_taken]. apply negb_true_iff.
unfold bv_ltu. apply Z.ltb_ge.
change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff 46 0) (SLit (-1)))))
  with (YP0e.U E (SAlu ALU_XOR (SOff 46 0) (SLit (-1)))).
change (bv_unsigned (sv_denot E (SOff 25 0))) with (YP0e.U E (SOff 25 0)).
rewrite Hnot, Hei. unfold PJF_CEIL in *. lia.
Qed.

(* ---- the loop head 0x8371c at kid i: the resumed state ss_L ---- *)
Lemma pjf_lp_st : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc i kidsv,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc -> pjf_frm Wc memc ->
  (forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 24) 8 kidsv ->
  4112 <= kidsv -> kidsv mod 16 = 0 -> kidsv <= PJF_CEIL -> Z.of_nat i <= 2 ^ 54 ->
  st_ok tfibsegs (pjf_env regsc [w64 kidsv]) ss_L
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8371c) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc i kidsv HARU HL Hfrm Hpres HPOc Hkv Hk1 Hk2 Hk3 Hi54.
pose proof HL as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) HPOc) as (HPL & HAMR & HHULL).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct HPOc as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
assert (HAPP : app_addr (v + 24)) by exact (proj2 (proj2 (proj2 (HPL (v + 24) ltac:(lia))))).
destruct (pjf_shadow_apart (v + 24) HAPP) as (HS1 & HS2).
pose proof (pjf_disj_img v 24 32 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_got_img) as HdG.
pose proof (pjf_disj_img v 24 32 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_cell_img) as HdC.
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 2) = sp0 - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E19 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 19) = v + 24)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19; unfold w64; apply wz; lia).
assert (E27 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 27) = shadow_of_addr SHADOW_OFF (v + 24))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 27 27%bv eq_refl), H27; unfold w64; apply wz;
      unfold shadow_of_addr, SHADOW_OFF in *; lia).
assert (E26 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 26) = Z.of_nat i)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 26 26%bv eq_refl), H26; unfold w64; apply wz; lia).
assert (E21 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 21) = 56)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl), H21; unfold w64; apply wz; lia).
assert (E46 : ew (pjf_env regsc [w64 kidsv]) 46 = Z_to_bv 64 kidsv)
  by (rewrite (pjf_ew_x regsc [w64 kidsv] 46 0 eq_refl); reflexivity).
assert (E46u : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 46) = kidsv)
  by (rewrite E46; apply wz; unfold PJF_CEIL in *; lia).
unfold ss_L. apply (pjf_reseatC lyc Sc Uc Wc regsc memc mdc 0x8371c [shr 27; fld 19 0 46]
  [(46%nat, mkAF 4112 PJF_CEIL 4); (26%nat, mkAF 0 (2 ^ 54) 0); (21%nat, mkAF 56 56 0)]
  [pjf_Cwrap; pjf_Cmulh] [] [w64 kidsv] HARU (proj1 HL) Hpres Hfrm ltac:(vm_compute; reflexivity)).
- constructor; [|constructor; [|constructor]].
  + apply (pjf_shr_ok regsc [w64 kidsv] 27%bv 27 Wc memc (v + 24));
      [reflexivity | exact H27 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
    intros x Hx. apply HRA. lia.
  + apply (pjf_fld_ok regsc [w64 kidsv] 19%bv 19 0 46 Wc memc (v + 24) kidsv);
      [reflexivity | exact H19 | lia | lia | lia | rewrite fsw_SOff0; exact E46
       | unfold PJF_CEIL in *; lia | rewrite Z.add_0_r; exact Hkv].
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E19, E27.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E46u, E26, E21.
  change (2 ^ 4) with 16. rewrite Z.pow_0_r.
  split; [split; [unfold PJF_CEIL in *; lia | split; [exact Hk2 | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I].
- exact I.
- cbn [conds_ok]. split; [|split; [|exact I]].
  + exact (pjf_acond_wrap _ i kidsv E26 E46u Hi54 ltac:(unfold PJF_CEIL in *; lia)).
  + exact (pjf_acond_mulh _ i E26 E21 Hi54).
Qed.

(* the callee-saved registers the epilogue restores: sp + 128 and the twelve saved atoms of s0 .. s11 *)
Lemma pjf_expect_ok : forall regsc xs,
  bv_unsigned (ew (pjf_env regsc xs) 2) = spZ regs - 128 ->
  YK11.getr regsc 3 = YK11.getr regs 3 -> YK11.getr regsc 4 = YK11.getr regs 4 ->
  forall r, In r CALLEE_SAVED -> sv_denot (pjf_env regsc xs) (pjf_expect r) = YK11.getr regs r.
Proof.
intros regsc xs E2 H3 H4 r Hr. cbv [CALLEE_SAVED In] in Hr.
repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  (lazymatch goal with |- sv_denot _ (pjf_expect ?q) = _ =>
     let e := eval vm_compute in (pjf_expect q) in change (pjf_expect q) with e end).
- eapply fsw_sp_back. unfold pjf_env in E2 |- *. exact E2.
- rewrite fsw_SOff0. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 3 3%bv eq_refl). exact H3.
- rewrite fsw_SOff0. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 4 4%bv eq_refl). exact H4.
- rewrite (pjf_ew_sav regsc xs 34 1 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 35 2 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 36 3 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 37 4 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 38 5 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 39 6 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 40 7 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 41 8 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 42 9 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 43 10 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 44 11 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
- rewrite (pjf_ew_sav regsc xs 45 12 eq_refl ltac:(lia)). cbn [pjf_saved pjf_sregs map nth]. reflexivity.
Qed.
(* pj_zero across a memory change that keeps every byte below alloc_ceiling *)
Lemma pjf_zero_below : forall (Wc : world tfibsegs) m m', same_below m m' alloc_ceiling -> v + 56 <= alloc_ceiling ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H Wc) m) v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H Wc) m') v.
Proof.
intros Wc m m' Hs Hv1 [[Hal Hstk] Hbytes]. pose proof asan_consts as (C1 & _).
split; [split; [exact Hal|]|].
- apply (PjStruct.pj_stk_eq tfibsegs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') v (v + 56) Hstk).
  intros x Hx. apply (fsw_mrestrict_below (w_H Wc) m m' x Hs). lia.
- apply (PjStruct.pj_bytes_eq tfibsegs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') v _ Hbytes).
  intros x Hx. rewrite repeat_length in Hx. apply (fsw_mrestrict_below (w_H Wc) m m' x Hs). lia.
Qed.

(* ---- the last segment: from 0x8381c (after __asan_memset) to the `ret`, giving the spec's post ---- *)
Lemma pjf_end_ret : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc Dfr,
  st_ok tfibsegs (pjf_env regsc []) ss_X4
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8381c) memc (YK11.seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = sp0 - 128 ->
  YK11.getr regsc 3 = YK11.getr regs 3 -> YK11.getr regsc 4 = YK11.getr regs 4 ->
  Permutation D Dfr ->
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) ->
  Uc = udrop U (rd_heads Dfr) ->
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H Wc) memc) v ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8381c) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros lyc Sc Uc Wc regsc memc mdc Dfr HS HJ HARU Hsp H3 H4 HPD HBP HUc Hglob Hzero Hpo.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
assert (E2 : bv_unsigned (ew (pjf_env regsc []) 2) = sp0 + (-128))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
fsw_aj_runU pj_free_tbl_ok HS HJ HARU.
{ cbn [ss_mem ss_X4 pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil] ]. }
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc []) (ss_mem ss_X4) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc []) pjf_cs [] a (sp0 - 128) (Forall_nil _)
    ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha). unfold STK in *. lia. }
pose proof (fsw_reg_extra _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 1%bv 1 HS ltac:(vm_compute; reflexivity))
  as R1F.
cbn [nth app fs_extraT pjf_saved pjf_sregs map] in R1F.
assert (EEV : EV_pj_free D = EV_pj_free Dfr) by (apply pjf_EV_perm; exact HPD).
assert (EUD : udrop U (rd_heads D) = Uc)
  by (rewrite HUc; apply pjf_udrop_perm; unfold rd_heads; apply Permutation_map; exact HPD).
assert (ESUM : rd_sum D = rd_sum Dfr) by (apply pjf_rd_sum_perm; exact HPD).
unfold GOAL. rewrite EEV, EUD.
eapply (fsw_retU B pj_free_tbl pj_free_tbl_ok Wc (pjf_env regsc []) _ ms _ STK sp0 FP regs ly S0 U W mem md
  lyc Sc Uc (EV_pj_free Dfr) Qf HS eq_refl ltac:(vm_compute; reflexivity) ltac:(rewrite R1F; exact Hra) HJ HARU).
- apply (fsw_preserved _ (pjf_env regsc []) _ ms regs pjf_expect HS); [vm_compute; reflexivity|].
  apply (pjf_expect_ok regsc []); [unfold sp0 in E2 |- *; lia | exact H3 | exact H4].
- intros matq. unfold Qf. split; [|split].
  + etransitivity; [exact HBP|]. apply Permutation_app_tail. unfold rd_hblocks. apply Permutation_map.
    symmetry. exact HPD.
  + intros _. split.
    * exact (pjf_zero_below Wc memc (ms_mem ms) SB Hv1 Hzero).
    * exact (pobj_below B lyc Sc Wc _ _ memc (ms_mem ms) v (proj1 HARU) SB Hpo).
  + rewrite ESUM. exact (fs_glob_below Wc memc (ms_mem ms) _ peak cnt fail SB Hglob).
Qed.

(* ---- the __asan_memset (v, 0, 56) segment: 0x8380c .. the call, the call, and the resume at 0x8381c ---- *)
Lemma pjf_end_memset : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc Dfr,
  st_ok tfibsegs (pjf_env regsc []) ss_X3
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8380c) memc (YK11.seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_regs regsc -> pjf_frm Wc memc ->
  Permutation D Dfr ->
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) ->
  Uc = udrop U (rd_heads Dfr) ->
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8380c) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros lyc Sc Uc Wc regsc memc mdc Dfr HS HJ HARU HR Hfrm HPD HBP HUc Hglob Hpo.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 (proj1 HPRE)) as HAPf.
destruct HAPf as (HARe & Hrae & Hra4e & Hgpe & Htpe & Hstke & Hprese & Hche & HQTe).
destruct (al_layout _ _ LAWS ly S0 W (unpoison U mem) md lyc HARe Hly) as (Eab & Efa & Eown).
assert (E2 : bv_unsigned (ew (pjf_env regsc []) 2) = sp0 + (-128))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
assert (PLACE : forall mx md', AR tfibsegs B lyc Sc Wc mx md' ->
  (forall a, v <= a < v + 56 -> apresent (w_H Wc) mx a /\ ~ aowned B lyc Sc a /\ ~ in_img tfibsegs a /\ app_addr a) /\
  amem_range v 56 /\ shadow_hull_vis (aview tfibsegs (w_H Wc) mx) v 56)
  by (intros mx md' HARx; exact (pjf_place B lyc Sc Wc mx md' memc v HARx Hpo)).
destruct (PLACE (unpoison Uc memc) mdc (proj1 HARU)) as (HPL & HAMR & HHULL0).
assert (HRA0 : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HPOI : upoisoned tfibsegs Wc memc Uc) by exact (proj2 (proj2 HARU)).
(* ---- run 0x8380c .. the call of __asan_memset ---- *)
fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU PC_memset.
{ cbn [ss_mem ss_X3 pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil] ]. }
rename HS into HSc.
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc []) (ss_mem ss_X3) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc []) pjf_cs [] a (sp0 - 128) (Forall_nil _)
    ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; exact Hsp) Ha).
  unfold STK in *. lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x8381c HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 2%bv 2%bv 2 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 3%bv 3%bv 3 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 4%bv 4%bv 4 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 8%bv 8%bv 8 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 9%bv 9%bv 9 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 18%bv 18%bv 18 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R18.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 19%bv 19%bv 19 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R19.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 22%bv 22%bv 22 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R22.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 23%bv 23%bv 23 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R23.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 10%bv 8%bv 8 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_lit _ _ _ ms 11%bv 0 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ _ _ ms 12%bv 56 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
rewrite H8 in R10.
assert (HspC : spZ (ms_regs ms) = sp0 + (-128)) by (unfold spZ at 1; rewrite R2; unfold spZ in Hsp; lia).
assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
{ pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  refine (pjf_frm_of_region (pjf_env regsc []) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). unfold spZ in Hsp. exact Hsp.
  - intros i Hi. exact (pjf_ew_sav regsc [] (33 + i) i eq_refl Hi).
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
assert (Ho16 : (-128) mod 16 = 0) by reflexivity.
assert (Ho0 : (-128) <= 0) by lia.
assert (HoS : ESTACK - (-128) <= STK) by (unfold ESTACK; lia).
assert (Hrok : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hgpc : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3, H3; exact Hgpe).
assert (Htpc : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4, H4; exact Htpe).
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Uc Wc (ms_mem ms) _ (EV_pj_free Dfr)
  (ms_regs ms) (-128) HJ HARU HspC Ho16 Ho0 HoS Hrok Hgpc Htpc) as HPREc.
assert (HDEST : dest_ok tfibsegs B lyc Sc Wc (ms_regs ms) (ms_mem ms) v 56).
{ intros a Ha. split; [|split].
  - replace a with (v + (a - v)) by lia.
    apply (fsw_writable_below (w_H Wc) memc (ms_mem ms) (v + (a - v)) SB); [lia|]. apply (proj2 Hpo). lia.
  - exact (proj1 (proj2 (HPL a Ha))).
  - rewrite HspC. unfold ESTACK. lia. }
assert (HRAD : range_addressable (aview tfibsegs (w_H Wc) (ms_mem ms)) SHADOW_OFF v 56)
  by (apply (fsw_range_addressable_below (w_H Wc) memc (ms_mem ms) v 56 SB ltac:(lia) Hv1); exact HRA0).
assert (HHULL : shadow_hull_vis (aview tfibsegs (w_H Wc) (ms_mem ms)) v 56)
  by (apply (pjf_hull_raw Wc Uc memc (ms_mem ms) v 56 HPOI SB ltac:(lia) Hv1 ltac:(lia)); exact HHULL0).
set (Wr := fun a => v <= a < v + 56 \/ sp0 - 128 - 4096 <= a < sp0 - 128).
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Uc Wc (ms_mem ms) _ (EV_pj_free Dfr) Uc
    Wr (Z_to_bv 64 0x8381c) _
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
       (forall i, 0 <= i < 56 -> aview tfibsegs (w_H Wc) mem' (v + i) = Some (0 mod 256)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H Wc) mem' a = aview tfibsegs (w_H Wc) (ms_mem ms) a))
    HJ).
  - eapply SRr_mono; [exact (fs_memset_realizesU lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) _ v 0 56 HPREc R10 R11 R12
        ltac:(lia) ltac:(lia) ltac:(lia) HDEST HAMR HRAD (fun _ => HHULL) I)|].
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & Hres & Hbytes & Hfr & Hpr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold YG0d.cfg_at, raZ; rewrite R1, unsigned_lit_small by lia; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
      aview tfibsegs (w_H Wc) mem' a = aview tfibsegs (w_H Wc) (ms_mem ms) a).
    { intros a Ha HWa. apply Hfr; [exact Ha | intros H'; apply HWa; left; exact H' |].
      rewrite HspC. unfold ESTACK. intros H'; apply HWa; right; lia. }
    split.
    { intros a Ha HWa. destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      - apply (aview_unpoison_in tfibsegs). exact Ei.
      - rewrite !(aview_unpoison_out tfibsegs) by exact Ei. exact (Hfr' a Ha HWa). }
    split; [intros a; apply (pjf_apresent_unpoison Uc (w_H Wc) (ms_mem ms) mem' a); exact (Hpr a)|].
    split; [exact HP'|]. split; [exact Hbytes | exact Hfr'].
  - intros a [Ha | Ha].
    + assert (HinFP : inFP FP a) by (apply pjf_inFP_cons; left; cbn [fst snd]; lia).
      destruct Hpo as [[((cid & pos & Hinf & Hc0 & Hal8 & Hf1 & Hf2) & _ & _)
                       |((bb & nn & Hinb & Hb1 & Hb2) & _ & _)] _].
      * right. right. split; [exact HinFP|]. exists cid, pos. rewrite Hfrs in Hinf. cbn [app] in Hinf.
        split; [exact Hinf|]. pose proof (Efa cid pos) as Ef1. unfold in_zr, frame_rng. cbn [fst snd]. lia.
      * left. right. left. split; [exact HinFP|]. exists bb, nn. split; [exact Hinb | unfold HEAD in *; lia].
    + left. left. unfold STK in *. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hz2 & Hfr2).
(* ---- back at 0x8381c ---- *)
assert (P2 : YK11.getr regs2 2 = YK11.getr (ms_regs ms) 2)
  by exact (fsw_pres _ _ 2%bv HP2 ltac:(pjf_cs_reg)).
assert (P3 : YK11.getr regs2 3 = YK11.getr (ms_regs ms) 3)
  by exact (fsw_pres _ _ 3%bv HP2 ltac:(pjf_cs_reg)).
assert (P4 : YK11.getr regs2 4 = YK11.getr (ms_regs ms) 4)
  by exact (fsw_pres _ _ 4%bv HP2 ltac:(pjf_cs_reg)).
assert (P8 : YK11.getr regs2 8 = YK11.getr (ms_regs ms) 8)
  by exact (fsw_pres _ _ 8%bv HP2 ltac:(pjf_cs_reg)).
assert (P9 : YK11.getr regs2 9 = YK11.getr (ms_regs ms) 9)
  by exact (fsw_pres _ _ 9%bv HP2 ltac:(pjf_cs_reg)).
assert (P18 : YK11.getr regs2 18 = YK11.getr (ms_regs ms) 18)
  by exact (fsw_pres _ _ 18%bv HP2 ltac:(pjf_cs_reg)).
assert (P19 : YK11.getr regs2 19 = YK11.getr (ms_regs ms) 19)
  by exact (fsw_pres _ _ 19%bv HP2 ltac:(pjf_cs_reg)).
assert (P22 : YK11.getr regs2 22 = YK11.getr (ms_regs ms) 22)
  by exact (fsw_pres _ _ 22%bv HP2 ltac:(pjf_cs_reg)).
assert (P23 : YK11.getr regs2 23 = YK11.getr (ms_regs ms) 23)
  by exact (fsw_pres _ _ 23%bv HP2 ltac:(pjf_cs_reg)).
assert (HR2 : pjf_regs regs2).
{ unfold pjf_regs. rewrite P3, P4, P8, P9, P18, P19, P22, P23, R3, R4, R8, R9, R18, R19, R22, R23.
  split; [unfold spZ at 1; rewrite P2, R2; unfold spZ in Hsp; exact Hsp|].
  split; [exact H3|]. split; [exact H4|]. split; [exact H8|]. split; [exact H9|]. split; [exact H18|].
  split; [exact H19|]. split; [exact H22 | exact H23]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
  mbyte tfibsegs (mrestrict (w_H Wc) mem2) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a)
  by (intros a Ha HW; apply (mbyte_of_aview tfibsegs); exact (Hfr2 a Ha HW)).
assert (Hfrm2 : pjf_frm Wc mem2).
{ pose proof Hfrm1 as (Hfj & Hs1 & Hs2). split; [|split].
  - intros j Hj. apply (pjf_val_keep (mrestrict (w_H Wc) (ms_mem ms))); [|exact (Hfj j Hj)].
    intros i Hi. apply KEEP; [unfold STK in *; lia|]. unfold Wr. unfold STK in *. lia.
  - apply (pjf_val_keep (mrestrict (w_H Wc) (ms_mem ms))); [|exact Hs1].
    intros i Hi. apply KEEP; [unfold STK in *; lia|]. unfold Wr. unfold STK in *. lia.
  - apply (pjf_val_keep (mrestrict (w_H Wc) (ms_mem ms))); [|exact Hs2].
    intros i Hi. apply KEEP; [unfold STK in *; lia|]. unfold Wr. unfold STK in *. lia. }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HP2s : forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) mem2 a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc mem2 md2 a HARU2); [lia|]. apply Hpres2.
  unfold STK in *. lia. }
pose proof (pjf_reseat lyc Sc Uc Wc regs2 mem2 md2 0x8381c [] [] [] [] HARU2 HR2 HP2s Hfrm2
  ltac:(vm_compute; reflexivity) (Forall_nil _)
  ltac:(apply pairwise_disjoint_of_extents; unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region,
          extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        unfold pjf_env; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl);
        unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat match goal with |- _ /\ _ => split end; try exact I;
        pose proof (proj1 HR2) as Hsp2'; unfold spZ in Hsp2'; unfold STK, sp0 in *;
        first [left; lia | right; lia]) I I) as HS2.
assert (Hbz : forall i, 0 <= i < 56 -> mbyte tfibsegs (mrestrict (w_H Wc) mem2) (v + i) = Some (Z_to_bv 8 0))
  by (intros i Hi; exact (pjf_mbyte_of_aview (w_H Wc) mem2 (v + i) 0 (Hz2 i Hi))).
assert (Hap2 : forall a, v <= a < v + 56 -> apresent (w_H Wc) mem2 a).
{ intros a Ha. destruct (PLACE (unpoison Uc mem2) md2 HAR2) as (HPL2 & _ & _).
  destruct (HPL2 a Ha) as (Hp & _ & Hni & Hap).
  destruct Hp as [Hh [bb Hb]]. split; [exact Hh|]. exists bb.
  rewrite <- (fsw_unpoison_app B lyc Sc Uc Wc mem2 md2 a HARU2
    ltac:(unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)
    ltac:(unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia)).
  exact Hb. }
assert (Hzero2 : PjStruct.pj_zero tfibsegs (mrestrict (w_H Wc) mem2) v).
{ split; [split; [exact Hv8|]|].
  - split; [lia|]. split; [lia|]. intros a Ha. split.
    + apply (apresent_writable tfibsegs). exact (Hap2 a Ha).
    + replace a with (v + (a - v)) by lia. eexists. exact (Hbz (a - v) ltac:(lia)).
  - split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    pose proof (Hbz (Z.of_nat i) ltac:(lia)) as Hb. unfold mbyte in Hb.
    rewrite nth_error_repeat by lia. exact Hb. }
assert (Hpo2 : pobj tfibsegs B lyc Sc Wc mem2 v).
{ assert (HRA2 : range_addressable (aview tfibsegs (w_H Wc) mem2) SHADOW_OFF v 56).
  { intros x Hx. destruct (HRAD x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
    destruct (HPL x Hx) as (_ & _ & _ & Hax).
    rewrite (Hfr2 (shadow_of_addr SHADOW_OFF x)); [exact Es | |].
    - unfold shadow_of_addr, SHADOW_OFF in *. unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hax.
      pose proof (Z.div_mod x 8 ltac:(lia)). lia.
    - unfold Wr. unfold shadow_of_addr, SHADOW_OFF in *.
      unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hax.
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). unfold STK in *. lia. }
  destruct Hpo as [Hpl Hw]. split.
  - destruct Hpl as [(Hf & Ha8 & _)|(Hb & Ha8 & _)]; [left | right]; (split; [assumption|]);
      (split; [exact Ha8 | exact HRA2]).
  - intros i Hi. apply (apresent_writable tfibsegs). apply Hap2. lia. }
assert (Hglob2 : fs_glob tfibsegs Wc mem2 (live - rd_sum Dfr) peak cnt fail).
{ apply (pjf_glob_keep Wc Wc (ms_mem ms) mem2).
  - intros a Ha. pose proof (fs_segs_img a Ha) as Hi. unfold FS_IMG_END in Hi.
    apply KEEP; [lia|]. unfold Wr. intros [Hw2 | Hw2];
      [exact (proj1 (proj2 (proj2 (HPL a Hw2))) Ha) | unfold STK in *; lia].
  - apply (pjf_glob_keep Wc Wc memc (ms_mem ms)); [|exact Hglob].
    intros a Ha. apply (mbyte_below (w_H Wc) memc (ms_mem ms) alloc_ceiling a SB).
    pose proof (fs_segs_img a Ha). unfold FS_IMG_END in *. lia. }
exact (pjf_end_ret lyc Sc Uc Wc regs2 mem2 md2 Dfr HS2 HJ2 HARU2 (proj1 HR2)
  (proj1 (proj2 HR2)) (proj1 (proj2 (proj2 HR2))) HPD HBP HUc Hglob2 Hzero2 Hpo2).
Qed.

(* ================= the loop ================= *)
(* a byte of a live block's user part is writable in the machine's memory *)
Lemma pjf_blk_wr : forall lyc Sc Uc (Wc : world tfibsegs) memc mdc b m x,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc -> In (b, m) (ablocks B lyc Sc) -> b + HEAD <= x < b + req_size m ->
  writable_at tfibsegs (mrestrict (w_H Wc) memc) x.
Proof.
intros lyc Sc Uc Wc memc mdc b m x HARU Hin Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc b m (proj1 HARU) Hin) as (_ & _ & _ & _ & Hb & _).
destruct (Hb x ltac:(unfold HEAD in *; lia)) as [[Hh [bb Hbb]] _].
apply (apresent_writable tfibsegs). split; [exact Hh|]. exists bb.
pose proof (fsw_ablock_low B lyc Sc Wc (unpoison Uc memc) mdc b m (proj1 HARU) Hin) as (A1 & A2 & A3).
pose proof asan_consts as (C1 & _).
rewrite <- (fsw_unpoison_app B lyc Sc Uc Wc memc mdc x HARU ltac:(unfold HEAD in *; lia)); [exact Hbb|].
exact (fsw_ablock_off_shadow B lyc Sc Wc (unpoison Uc memc) mdc b m (proj1 HARU) Hin x ltac:(unfold HEAD in *; lia)).
Qed.
(* the kid call's footprint: the kid node, the kid's blocks with their heads, fs's statics *)
Lemma pjf_notFP_kid : forall v' D1 x,
  ~ (v' <= x < v' + 56) ->
  (forall a1 k1, In (a1, k1) D1 -> ~ (a1 - HEAD <= x < a1 - HEAD + req_size (k1 + HEAD))) ->
  ~ in_img tfibsegs x ->
  ~ inFP ((v', v' + 56) :: ablocks_fp (rd_hblocks D1) ++ FS_PSTAT_FP) x.
Proof.
intros v' D1 x H1 H2 H3 Hin. apply pjf_inFP_cons in Hin. cbn [fst snd] in Hin.
destruct Hin as [Hin | Hin]; [exact (H1 Hin)|]. apply pjf_inFP_app in Hin. destruct Hin as [Hin | Hin].
- apply pjf_inFP_hblocks in Hin. destruct Hin as (p & k1 & Hp & Hr). exact (H2 p k1 Hp Hr).
- exact (H3 (pjf_pstat_img x Hin)).
Qed.
(* the heads that stay after a callee frees D1 are heads of blocks that stay *)
Lemma pjf_heads_after : forall lyc Sc Uc ly' S' D1,
  FSupoisonU.fs_heads B lyc Sc Uc -> Permutation (ablocks B lyc Sc) (rd_hblocks D1 ++ ablocks B ly' S') ->
  FSupoisonU.fs_heads B ly' S' (udrop Uc (rd_heads D1)).
Proof.
intros lyc Sc Uc ly' S' D1 HH HP r Hr.
rewrite pjf_udrop_eq in Hr. apply List.filter_In in Hr as [Hr Hn].
destruct (HH r Hr) as (E16 & m & Hm & Hm16). split; [exact E16|].
apply (Permutation_in _ HP) in Hm. apply in_app_or in Hm as [Hm | Hm]; [|exists m; split; assumption].
exfalso. unfold rd_hblocks in Hm. apply in_map_iff in Hm as ([a1 k1] & E & Hin). cbn [fst snd] in E.
injection E as E1 E2.
assert (Hh : hd_in (rd_heads D1) r = true).
{ apply pjf_hd_in_iff. unfold rd_heads. apply in_map_iff. exists (a1, k1). split; [|exact Hin].
  destruct r as [r1 r2]. cbn [fst snd] in *. rewrite E1, E16. reflexivity. }
rewrite Hh in Hn. discriminate.
Qed.
(* the keep chain across a call *)
Lemma pjf_keep_call : forall (F F' : Z -> Prop) STK1 sp1 FP1 lyc Sc Uc (Wc : world tfibsegs) memc mdc memC
    ly' S' U' W' mem' md' kc,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc (unpoison Uc memC) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x : word, F (bv_unsigned x) -> mrestrict (w_H Wc) memc x = m0 x) ->
  same_below memc memC alloc_ceiling ->
  (forall x, F' x -> F x /\ ~ inFP FP1 x /\ x < alloc_ceiling /\
     ((exists p n0, In (p, n0) (ablocks B lyc Sc) /\ p <= x < p + req_size n0) \/
      (exists cid pos, In (cid, pos) (frames Sc) /\
         frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))) ->
  forall x : word, F' (bv_unsigned x) -> mrestrict (w_H W') mem' x = m0 x.
Proof.
intros F F' STK1 sp1 FP1 lyc Sc Uc Wc memc mdc memC ly' S' U' W' mem' md' kc HJc HU HO' HP' HK SB HF x Hx.
destruct (HF _ Hx) as (HFx & Hnf & Hlo & Hlive).
pose proof (u64_range x) as Rx.
rewrite <- (Z_to_bv_bv_unsigned 64 x).
rewrite (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc Wc memC mdc ly' S' U' W' mem' md' kc _ HJc HU HO' HP'
  Hlive Hnf)).
rewrite (fsw_mrestrict_belowZ (w_H Wc) memc memC (bv_unsigned x) SB ltac:(lia)).
rewrite Z_to_bv_bv_unsigned. exact (HK x HFx).
Qed.
(* the registers of pjf_regs / pjf_lregs, each kept *)
Lemma pjf_regs_of : forall regsc regsm, pjf_regs regsc ->
  YK11.getr regsm 2 = YK11.getr regsc 2 -> YK11.getr regsm 3 = YK11.getr regsc 3 ->
  YK11.getr regsm 4 = YK11.getr regsc 4 -> YK11.getr regsm 8 = YK11.getr regsc 8 ->
  YK11.getr regsm 9 = YK11.getr regsc 9 -> YK11.getr regsm 18 = YK11.getr regsc 18 ->
  YK11.getr regsm 19 = YK11.getr regsc 19 -> YK11.getr regsm 22 = YK11.getr regsc 22 ->
  YK11.getr regsm 23 = YK11.getr regsc 23 -> pjf_regs regsm.
Proof.
intros regsc regsm (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) E2 E3 E4 E8 E9 E18 E19 E22 E23.
unfold pjf_regs. unfold spZ in *. rewrite E2, E3, E4, E8, E9, E18, E19, E22, E23.
split; [exact Hsp|]. split; [exact H3|]. split; [exact H4|]. split; [exact H8|]. split; [exact H9|].
split; [exact H18|]. split; [exact H19|]. split; [exact H22 | exact H23].
Qed.
Lemma pjf_lregs_of : forall i regsc regsm, pjf_lregs i regsc ->
  YK11.getr regsm 2 = YK11.getr regsc 2 -> YK11.getr regsm 3 = YK11.getr regsc 3 ->
  YK11.getr regsm 4 = YK11.getr regsc 4 -> YK11.getr regsm 8 = YK11.getr regsc 8 ->
  YK11.getr regsm 9 = YK11.getr regsc 9 -> YK11.getr regsm 18 = YK11.getr regsc 18 ->
  YK11.getr regsm 19 = YK11.getr regsc 19 -> YK11.getr regsm 22 = YK11.getr regsc 22 ->
  YK11.getr regsm 23 = YK11.getr regsc 23 -> YK11.getr regsm 20 = YK11.getr regsc 20 ->
  YK11.getr regsm 27 = YK11.getr regsc 27 -> YK11.getr regsm 21 = YK11.getr regsc 21 ->
  YK11.getr regsm 24 = YK11.getr regsc 24 -> YK11.getr regsm 25 = YK11.getr regsc 25 ->
  YK11.getr regsm 26 = YK11.getr regsc 26 -> pjf_lregs i regsm.
Proof.
intros i regsc regsm (HR & H20 & H27 & H21 & H24 & H25 & H26) E2 E3 E4 E8 E9 E18 E19 E22 E23 E20 E27 E21 E24 E25 E26.
unfold pjf_lregs. rewrite E20, E27, E21, E24, E25, E26.
split; [exact (pjf_regs_of regsc regsm HR E2 E3 E4 E8 E9 E18 E19 E22 E23)|].
split; [exact H20|]. split; [exact H27|]. split; [exact H21|]. split; [exact H24|]. split; [exact H25 | exact H26].
Qed.
(* n's bound: the kids block holds 56 n bytes below alloc_ceiling *)
Lemma pjf_n_bound : (1 <= n)%Z -> n <= 2 ^ 54 /\ 56 * n <= alloc_ceiling.
Proof.
intros Hn1. pose proof asan_consts as (C1 & _).
destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & _)]; [lia|].
destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 pjf_HAR0 (HBK kids k0 Hk0D)). unfold HEAD in *. lia.
Qed.
(* the kept bytes all lie below alloc_ceiling (the entry's blocks of D) *)
Lemma pjf_FPS_low : forall ik iy Dr x, (forall b, In b Dr -> In b D) -> pjf_FPS ik iy Dr x -> 0 <= x < alloc_ceiling.
Proof.
intros ik iy Dr x HDr Hx. pose proof pjf_entry_facts as (_ & _ & _ & Hv0 & Hv1 & _).
unfold pjf_FPS in Hx. destruct Hx as [Hx | [(Hks & Hx) | [Hx | ((ba, bk) & Hb & Hx)]]].
- lia.
- destruct HKEYS as [(_ & Hksf & _) | (_ & ky & HkyD & Hkyn & _)]; [congruence|].
  destruct (fsw_rblock_low B ly S0 W _ md mem keys ky pjf_HAR0 (HBK keys ky HkyD)). unfold HEAD in *. lia.
- destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & _)]; [lia|].
  destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 pjf_HAR0 (HBK kids k0 Hk0D)). unfold HEAD in *. lia.
- unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
  destruct (fsw_rblock_low B ly S0 W _ md mem ba bk pjf_HAR0 (HBK ba bk (HDr _ Hb))). unfold HEAD in *. lia.
Qed.
(* the invariant across a run that writes only the frame *)
Lemma pjf_inv_below : forall F Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc mdc memc' mdc',
  pjf_inv F Dfr Rem lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc') mdc' (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memc' mdc' -> pjf_frm Wc memc' -> same_below memc memc' alloc_ceiling ->
  (forall x, F x -> 0 <= x < alloc_ceiling) ->
  pjf_inv F Dfr Rem lyc Sc Uc Wc memc' mdc'.
Proof.
intros F Dfr Rem lyc Sc Uc Wc memc mdc memc' mdc' HINV HJ' HARU' Hfrm' SB HFl.
destruct HINV as (_ & HARU & HHD & _ & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof (proj1 HARU) as HARc.
split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HHD|]. split; [exact Hfrm'|].
split; [exact HBP|]. split; [exact HUc|].
split; [exact (fs_glob_below Wc memc memc' _ peak cnt fail SB Hglob)|].
split; [exact HPD|].
split; [exact (rd_blocks_ok_below B lyc Sc Wc _ mdc memc memc' Rem HARc SB HRB)|].
split; [exact (pobj_below B lyc Sc Wc _ mdc memc memc' v HARc SB HPOc)|].
split; [|exact (arodata_below B Wc memc memc' SB HRO)].
intros x Hx. pose proof (u64_range x) as Rx. rewrite <- (HKEEP x Hx). rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (fsw_mrestrict_belowZ (w_H Wc) memc memc' _ SB). exact (HFl _ Hx).
Qed.

(* ---- the self call 0x83760: the loop head 0x8371c at kid i, the run to the call, pj_free (&kids[i]) at level
   k + 1 (REC), and the resume at 0x83764 with kid i's blocks freed ---- *)
Lemma pjf_seg_kid : forall i Dfr Dky D1 Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (k < 2)%nat -> (i < Z.to_nat n)%nat ->
  pjf_inv (pjf_FPS i i (Dky ++ D1 ++ Rest')) Dfr (Ds ++ Dk ++ Dy ++ Dky ++ D1 ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  PjStruct.pj_fd tfibsegs m0 (fun a n0 => In (a, n0) D) (1 - k) (kids + 56 * Z.of_nat i) D1 ->
  (forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) i (Dky ++ Rest')) (Dfr ++ D1) (Ds ++ Dk ++ Dy ++ Dky ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs i regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83764) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8371c) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Dky D1 Rest' lyc Sc Uc Wc regsc memc mdc Q Hk2 Hi HINV HL Hfd1 K.
destruct HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & HSTK3 & HSTK4). specialize (HSTK3 Hk2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 HARU) as HARc.
pose proof HSS as [Hgot Hcell].
set (Rem := Ds ++ Dk ++ Dy ++ Dky ++ D1 ++ Rest') in *.
(* the kids block (n >= 1) *)
destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & EDk)]; [lia|].
assert (HkR : In (kids, k0) Rem) by (subst Rem; rewrite EDk; apply in_or_app; right; left; reflexivity).
pose proof (HRB kids k0 HkR) as Hkblk. pose proof Hkblk as (Hkin & Hk16 & Hk0pos & _).
destruct (fsw_rblock_low B lyc Sc Wc _ mdc memc kids k0 HARc Hkblk) as (Hkl & Hkh).
(* NoDup of the live lists *)
assert (HNDR : List.NoDup (Dfr ++ Rem))
  by (apply (Permutation_NoDup HPD); first [exact HND | apply NoDup_ListNoDup; exact HND]).
(* the kids field at v + 24 *)
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
assert (Vk : val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 24) 8 kids).
{ intros j0 Hj0. unfold mbyte. rewrite (HKEEP (Z_to_bv 64 (v + 24 + Z.of_nat j0))).
  - exact (fsw_pj_u64_val tfibsegs _ _ _ Hkids j0 Hj0).
  - rewrite wz by lia. unfold pjf_FPS. left. lia. }
(* the frame bytes are present *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (Hpres : forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
assert (Hn1 : 1 <= n) by lia.
pose proof (pjf_n_bound Hn1) as (Hn54 & Hnb).
pose proof (pjf_lp_st lyc Sc Uc Wc regsc memc mdc i kids HARU HL Hfrm Hpres HPOc Vk
  ltac:(unfold HEAD in *; lia) Hk16 ltac:(unfold PJF_CEIL; lia) ltac:(lia)) as HS.
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 kids]) 2) = sp0 + (-128))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
(* ---- run 0x8371c .. the self call ---- *)
fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x83674.
{ cbn [ss_mem ss_L pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
rename HS into HSc.
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc [w64 kids]) (ss_mem ss_L) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 kids]) pjf_cs [shr 27; fld 19 0 46] a (sp0 - 128)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
    ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
  unfold sp0, STK in *. lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x83764 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs ms) 10 = w64 (kids + 56 * Z.of_nat i)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms 10%bv HSc).
  lazymatch type of HSc with st_ok _ _ ?ssf _ =>
    replace (sr_get (ss_regs ssf) 10%bv) with (SAlu ALU_ADD (SOff 24 0) (SOff 46 0)) by (vm_compute; reflexivity) end.
  cbn [sv_denot]. rewrite (pjf_ew_x regsc [w64 kids] 46 0 eq_refl). cbn [nth].
  assert (E24 : ew (pjf_env regsc [w64 kids]) 24 = YK11.getr regsc 24) by exact (ew_Ereg_nat regsc _ 24 24%bv eq_refl).
  rewrite E24, H24. unfold w64. rewrite !Z.add_0_r.
  rewrite (wz (56 * Z.of_nat i)) by (unfold HEAD in *; lia). rewrite (wz kids) by (unfold HEAD in *; lia).
  rewrite alu64_add_lit. f_equal. lia. }
assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regsc 2)
  by exact (fsw_reg_atom _ _ _ _ ms 2%bv 2%bv 2 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regsc 3)
  by exact (fsw_reg_atom _ _ _ _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regsc 4)
  by exact (fsw_reg_atom _ _ _ _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regsc 8)
  by exact (fsw_reg_atom _ _ _ _ ms 8%bv 8%bv 8 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regsc 9)
  by exact (fsw_reg_atom _ _ _ _ ms 9%bv 9%bv 9 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P18 : YK11.getr (ms_regs ms) 18 = YK11.getr regsc 18)
  by exact (fsw_reg_atom _ _ _ _ ms 18%bv 18%bv 18 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P19 : YK11.getr (ms_regs ms) 19 = YK11.getr regsc 19)
  by exact (fsw_reg_atom _ _ _ _ ms 19%bv 19%bv 19 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P20 : YK11.getr (ms_regs ms) 20 = YK11.getr regsc 20)
  by exact (fsw_reg_atom _ _ _ _ ms 20%bv 20%bv 20 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P21 : YK11.getr (ms_regs ms) 21 = YK11.getr regsc 21)
  by exact (fsw_reg_atom _ _ _ _ ms 21%bv 21%bv 21 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P22 : YK11.getr (ms_regs ms) 22 = YK11.getr regsc 22)
  by exact (fsw_reg_atom _ _ _ _ ms 22%bv 22%bv 22 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P23 : YK11.getr (ms_regs ms) 23 = YK11.getr regsc 23)
  by exact (fsw_reg_atom _ _ _ _ ms 23%bv 23%bv 23 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P24 : YK11.getr (ms_regs ms) 24 = YK11.getr regsc 24)
  by exact (fsw_reg_atom _ _ _ _ ms 24%bv 24%bv 24 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P25 : YK11.getr (ms_regs ms) 25 = YK11.getr regsc 25)
  by exact (fsw_reg_atom _ _ _ _ ms 25%bv 25%bv 25 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P26 : YK11.getr (ms_regs ms) 26 = YK11.getr regsc 26)
  by exact (fsw_reg_atom _ _ _ _ ms 26%bv 26%bv 26 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
  by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
assert (HspC : spZ (ms_regs ms) = sp0 + (-128)) by (unfold spZ at 1; rewrite P2; unfold spZ in Hsp; lia).
assert (HLc : pjf_lregs i (ms_regs ms))
  by (apply (pjf_lregs_of i regsc (ms_regs ms) HL); assumption).
assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
{ pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  refine (pjf_frm_of_region (pjf_env regsc [w64 kids]) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). unfold spZ in Hsp. exact Hsp.
  - intros i0 Hi0. exact (pjf_ew_sav regsc [w64 kids] (33 + i0) i0 eq_refl Hi0).
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
(* ---- the data the callee takes ---- *)
set (v' := kids + 56 * Z.of_nat i) in *.
assert (Hv'n : v' + 56 <= kids + k0) by (subst v'; lia).
assert (HRBc : rd_blocks_ok tfibsegs B lyc Sc Wc (ms_mem ms) Rem)
  by exact (rd_blocks_ok_below B lyc Sc Wc _ mdc memc (ms_mem ms) Rem HARc SB HRB).
assert (HPOm : pobj tfibsegs B lyc Sc Wc (ms_mem ms) v) by exact (pobj_below B lyc Sc Wc _ mdc memc (ms_mem ms) v HARc SB HPOc).
assert (HROm : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) (ms_mem ms)))
  by exact (arodata_below B Wc memc (ms_mem ms) SB HRO).
assert (HKEEPm : forall x : word, pjf_FPS i i (Dky ++ D1 ++ Rest') (bv_unsigned x) ->
  mrestrict (w_H Wc) (ms_mem ms) x = m0 x).
{ intros x Hx. pose proof (u64_range x) as Rx. rewrite <- (HKEEP x Hx).
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (fsw_mrestrict_belowZ (w_H Wc) memc (ms_mem ms) _ SB).
  split; [lia|]. unfold pjf_FPS in Hx.
  destruct Hx as [Hx | [(Hks & Hx) | [Hx | (b & Hb & Hx)]]]; [lia | | lia |].
  - destruct HKEYS as [(_ & Hksf & _) | (_ & ky & HkyD & Hkyn & EDy)]; [congruence|].
    destruct (HBK keys ky HkyD) as (_ & _ & Hky0 & _). pose proof (HBK keys ky HkyD) as Hkb.
    destruct (fsw_rblock_low B ly S0 W _ md mem keys ky pjf_HAR0 Hkb). lia.
  - destruct b as [ba bk]. unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
    assert (HbR : In (ba, bk) Rem) by (subst Rem; do 3 (apply in_or_app; right); exact Hb).
    destruct (fsw_rblock_low B lyc Sc Wc _ mdc memc ba bk HARc (HRB ba bk HbR)). lia. }
(* the kid: the item, the node and its blocks *)
assert (HD1R : forall a1 k1, In (a1, k1) D1 -> In (a1, k1) Rem)
  by (intros a1 k1 H; subst Rem; do 4 (apply in_or_app; right); apply in_or_app; left; exact H).
assert (HD1D : forall a1 k1, In (a1, k1) D1 -> In (a1, k1) D)
  by (intros a1 k1 H; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact (HD1R a1 k1 H)).
assert (HkD : In (kids, k0) D) by exact Hk0D.
(* kid i's node lies in the kids block's user part, apart from its own blocks *)
assert (Hfd1m : PjStruct.pj_fd tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) (fun a n0 => In (a, n0) D1) (1 - k) v' D1).
{ apply (pjf_fd_frame tfibsegs (1 - k) m0 (fun a n0 => In (a, n0) D) _ _ v' D1 Hfd1); [intros a1 k1 H; exact H|].
  intros x Hx. apply HKEEPm. unfold pjf_FPS. pose proof (u64_range x) as Rx.
  destruct Hx as [Hx | (b & Hb & Hx)].
  - right. right. left. subst v'. lia.
  - right. right. right. exists b. split; [|exact Hx].
    apply in_or_app; right; apply in_or_app; left. exact Hb. }
(* the callee's premise at the call *)
assert (Hra1 : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hgpc : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite P3, H3. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 HPRE)))))). }
assert (Htpc : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite P4, H4. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HPRE))))))). }
assert (HPREc : fpreU tfibsegs B (STK_pj_free (2 - S k)) lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) []).
{ apply (fsw_fpreU_atFP B STK sp0 FP ly S0 Uc W (unpoison U mem) md [] lyc Sc Wc (ms_mem ms) _ (EV_pj_free Dfr)
    (ms_regs ms) (STK_pj_free (2 - S k)) (-128) [] HJ HARU HROm HspC ltac:(reflexivity) ltac:(lia)
    (proj1 (pjf_STK1 Hk2)) ltac:(pose proof (proj2 (pjf_STK1 Hk2)); lia) Hra1
    ltac:(unfold raZ; rewrite R1, unsigned_lit_small by lia; lia) Hgpc Htpc).
  apply achain_low. unfold s0Z. rewrite P8, H8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
set (mdC := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
(* the blocks of the lists *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (HposR : forall a1 k1, In (a1, k1) Rem -> 0 < k1)
  by (intros a1 k1 H; exact (proj1 (proj2 (proj2 (HRB a1 k1 H))))).
assert (Hnng : forall L, (forall b, In b L -> In b Rem) -> 0 <= rd_sum L)
  by (intros L HLl; apply pjf_rd_sum_nonneg; intros a1 k1 H; exact (HposR a1 k1 (HLl _ H))).
assert (HDsR : forall b, In b Ds -> In b Rem) by (intros b H; subst Rem; apply in_or_app; left; exact H).
assert (HDkR : forall b, In b Dk -> In b Rem) by (intros b H; subst Rem; do 1 (apply in_or_app; right); apply in_or_app; left; exact H).
assert (HDyR : forall b, In b Dy -> In b Rem) by (intros b H; subst Rem; do 2 (apply in_or_app; right); apply in_or_app; left; exact H).
assert (HDkyR : forall b, In b Dky -> In b Rem) by (intros b H; subst Rem; do 3 (apply in_or_app; right); apply in_or_app; left; exact H).
assert (HRsR : forall b, In b Rest' -> In b Rem) by (intros b H; subst Rem; do 5 (apply in_or_app; right); exact H).
assert (HsumR : rd_sum Rem = rd_sum Ds + rd_sum Dk + rd_sum Dy + rd_sum Dky + rd_sum D1 + rd_sum Rest')
  by (subst Rem; rewrite !pjf_rd_sum_app; lia).
assert (HsumD1 : rd_sum D1 <= live - rd_sum Dfr).
{ rewrite (pjf_rd_sum_perm _ _ HPD), pjf_rd_sum_app, HsumR in HSUM.
  pose proof (Hnng _ HDsR). pose proof (Hnng _ HDkR). pose proof (Hnng _ HDyR). pose proof (Hnng _ HDkyR).
  pose proof (Hnng _ HRsR). lia. }
assert (HevD1 : st_nev Sc + EV_pj_free D1 <= EV_MAX).
{ rewrite (pjf_EV_perm _ _ HPD), pjf_EV_app in HEV. subst Rem. rewrite !pjf_EV_app in HEV.
  pose proof (pjf_EV_nonneg Ds). pose proof (pjf_EV_nonneg Dk). pose proof (pjf_EV_nonneg Dy).
  pose proof (pjf_EV_nonneg Dky). pose proof (pjf_EV_nonneg Rest'). lia. }
assert (HinclD1 : incl (rd_heads D1) Uc).
{ intros h Hh. unfold rd_heads in Hh. apply in_map_iff in Hh as ([a1 k1] & <- & Hin1). cbn [fst].
  rewrite HUc, pjf_udrop_eq. apply List.filter_In. split.
  - apply HUI. unfold rd_heads. apply in_map_iff. exists (a1, k1). split; [reflexivity | exact (HD1D a1 k1 Hin1)].
  - destruct (hd_in (rd_heads Dfr) (a1 - HEAD, HEAD)) eqn:E; [|reflexivity]. exfalso.
    apply pjf_hd_in_iff in E. unfold rd_heads in E. apply in_map_iff in E as ([a2 k2] & Ea2 & Hin2).
    cbn [fst] in Ea2. injection Ea2 as Ea2'. assert (a2 = a1) by lia. subst a2.
    assert (k2 = k1).
    { apply (pjf_D_uniq a1); [|exact (HD1D a1 k1 Hin1)].
      apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Hin2. }
    subst k2. exact (pjf_nodup_disj Dfr Rem (a1, k1) HNDR Hin2 (HD1R a1 k1 Hin1)). }
assert (HRB1 : rd_blocks_ok tfibsegs B lyc Sc Wc (ms_mem ms) D1) by (intros a1 k1 H; exact (HRBc a1 k1 (HD1R a1 k1 H))).
assert (Hpo' : pobj tfibsegs B lyc Sc Wc (ms_mem ms) v').
{ assert (Rk : req_size (k0 + HEAD) = k0 + HEAD) by (apply pjf_req; unfold HEAD; lia).
  split.
  - right. split; [exists (kids - HEAD), (k0 + HEAD); split; [exact Hkin | rewrite Rk; subst v'; unfold HEAD in *; lia]|].
    split; [subst v'; Z.div_mod_to_equations; lia|].
    apply (fsw_block_body_addressable B lyc Sc Uc Wc (ms_mem ms) mdC (kids - HEAD) (k0 + HEAD) v' 56 HARU HHD Hkin);
      [subst v'; unfold HEAD in *; lia | lia | rewrite Rk; subst v'; unfold HEAD in *; lia].
  - intros i0 Hi0. apply (pjf_blk_wr lyc Sc Uc Wc (ms_mem ms) mdC (kids - HEAD) (k0 + HEAD)); [exact HARU | exact Hkin |].
    rewrite Rk. subst v'. unfold HEAD in *. lia. }
assert (Hglobm : fs_glob tfibsegs Wc (ms_mem ms) (live - rd_sum Dfr) peak cnt fail)
  by exact (fs_glob_below Wc memc (ms_mem ms) _ peak cnt fail SB Hglob).
(* ---- pj_free (&kids[i]) at level k + 1 ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
assert (HSk : (S k <= 2)%nat) by lia.
assert (Hv'0 : v' <> 0) by (subst v'; unfold HEAD in *; lia).
assert (Hv'stk : v' + 56 <= spZ (ms_regs ms) - STK_pj_free (2 - S k))
  by (rewrite HspC; pose proof (proj2 (pjf_STK1 Hk2)); unfold sp0, STK in *; lia).
eapply SRr_bind.
{ exact (REC lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) mdC [] v' D1 (live - rd_sum Dfr) peak cnt fail HSk HPREc HHD
    R10 (or_intror (conj Hv'0 (conj Hfd1m (conj Hpo' (or_introl Hv'stk))))) HRB1 HinclD1 Hglobm HsumD1 HevD1). }
intros W4 c4 Hwle4 Hpost. unfold fpostU in Hpost. cbv beta in Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJc & OK4 & PO4 & HP4 & HBP4 & HZ4 & Hglob4).
subst c4. rewrite R1.
set (FP1 := (v', v' + 56) :: ablocks_fp (rd_hblocks D1) ++ FS_PSTAT_FP) in *.
set (U4 := udrop Uc (rd_heads D1)) in *.
(* the callee's footprint, as the caller's journal takes it *)
assert (HFPS : fsw_fp_sub B ly S0 lyc Sc [] FP FP1).
{ assert (Rk : req_size (k0 + HEAD) = k0 + HEAD) by (apply pjf_req; unfold HEAD; lia).
  intros a Ha. subst FP1. apply pjf_inFP_cons in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha].
  - left. split.
    + apply pjf_inFP_cons. right. apply pjf_inFP_app. left. apply pjf_inFP_hblocks.
      exists kids, k0. split; [exact HkD | rewrite Rk; subst v'; unfold HEAD in *; lia].
    + exists (kids - HEAD), (k0 + HEAD). split; [exact Hkin | rewrite Rk; subst v'; unfold HEAD in *; lia].
  - apply pjf_inFP_app in Ha. destruct Ha as [Ha | Ha].
    + left. pose proof Ha as Ha'. apply pjf_inFP_hblocks in Ha'. destruct Ha' as (p & k1 & Hp & Hr). split.
      * apply pjf_inFP_cons. right. apply pjf_inFP_app. left. apply pjf_inFP_hblocks.
        exists p, k1. split; [exact (HD1D p k1 Hp) | exact Hr].
      * exists (p - HEAD), (k1 + HEAD). split; [exact (proj1 (HRB p k1 (HD1R p k1 Hp))) | exact Hr].
    + right. right. left. split; [apply pjf_inFP_cons; right; apply pjf_inFP_app; right; exact Ha|].
      exact (pjf_pstat_img a Ha). }
assert (HP4sp : YK11.getr regs4 2 = YK11.getr (ms_regs ms) 2) by exact (fsw_pres _ _ 2%bv HP4 ltac:(pjf_cs_reg)).
assert (Hsp4 : spZ regs4 = sp0 - 128) by (unfold spZ at 1; rewrite HP4sp; unfold spZ in HspC; lia).
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc (ms_mem ms) mdC (EV_pj_free Dfr)
  (STK_pj_free (2 - S k)) FP1 128 (ms_regs ms) ly4 S4 U4 W4 regs4 mem4 md4 (EV_pj_free D1) (pjf_saved regs ++ [])
  pjf_cs [] [] 0x83764 Hgot Hcell HJ HARU HJc HFPS OK4 PO4 HP4) as (HJ4 & HARU4 & HS4).
- lia.
- lia.
- exact (proj1 (pjf_STK1 Hk2)).
- pose proof (proj2 (pjf_STK1 Hk2)). lia.
- reflexivity.
- vm_compute. reflexivity.
- unfold pjf_cs. repeat constructor; cbn; lia.
- assert (Q19 : YK11.getr regs4 19 = YK11.getr (ms_regs ms) 19) by exact (fsw_pres _ _ 19%bv HP4 ltac:(pjf_cs_reg)).
  assert (Q9 : YK11.getr regs4 9 = YK11.getr (ms_regs ms) 9) by exact (fsw_pres _ _ 9%bv HP4 ltac:(pjf_cs_reg)).
  pose proof Hfrm1 as (Hfj1 & Hfs1 & Hfs2).
  apply (pjf_cs_ok (Ereg regs4 (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H Wc) (ms_mem ms)));
    [rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Hsp4 | exact (pjf_ew_saved regs4 [])
     | rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl), Q19, P19, H19; unfold w64; apply wz; lia
     | rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl), Q9, P9, H9; unfold w64; apply wz; lia
     | exact Hfj1 | exact Hfs1 | exact Hfs2].
- constructor.
- apply pairwise_disjoint_of_extents. unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region,
    extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl).
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold spZ in Hsp4; unfold sp0, STK in *;
  first [left; lia | right; lia].
- exact I.
- (* ---- back at 0x83764: the invariant with kid i's blocks freed ---- *)
  assert (HNDRem : List.NoDup Rem) by exact (List.NoDup_app_remove_l _ _ HNDR).
  set (Rem' := Ds ++ Dk ++ Dy ++ Dky ++ Rest').
  assert (HR'R : forall b, In b Rem' -> In b Rem) by (intros b H; subst Rem Rem'; rewrite !in_app_iff in *; tauto).
  assert (HneD1 : forall b, In b Rem' -> In b D1 -> False).
  { intros b H1 H2. apply (pjf_nodup_mid (Ds ++ Dk ++ Dy ++ Dky) D1 Rest' b).
    - subst Rem. rewrite <- !app_assoc. exact HNDRem.
    - subst Rem'. rewrite !in_app_iff in *. tauto.
    - exact H2. }
  assert (HSEP : forall a1 k1 a2 k2, In (a1, k1) Rem -> In (a2, k2) Rem -> (a1, k1) <> (a2, k2) ->
    a1 + k1 <= a2 - HEAD \/ a2 + k2 <= a1 - HEAD)
    by (intros a1 k1 a2 k2 H1 H2 Hne; exact (pjf_blk_sep lyc Sc Wc _ mdC (ms_mem ms) a1 k1 a2 k2 (proj1 HARU)
          (HRBc a1 k1 H1) (HRBc a2 k2 H2) Hne)).
  assert (Hreq : forall k1, 0 < k1 -> req_size (k1 + HEAD) = k1 + HEAD) by (intros k1 H; apply pjf_req; unfold HEAD; lia).
  (* the kids block is apart from every other block of Rem *)
  assert (HNk : forall b, In b (Dy ++ Dky ++ D1 ++ Rest') -> b <> (kids, k0)).
  { intros b Hb E. subst b. apply (pjf_nodup_disj Dk (Dy ++ Dky ++ D1 ++ Rest') (kids, k0)).
    - subst Rem. exact (List.NoDup_app_remove_l _ _ HNDRem).
    - rewrite EDk. left. reflexivity.
    - exact Hb. }
  assert (HNkDs : forall b, In b Ds -> b <> (kids, k0)).
  { intros b Hb E. subst b. apply (pjf_nodup_disj Ds (Dk ++ Dy ++ Dky ++ D1 ++ Rest') (kids, k0)).
    - exact HNDRem.
    - exact Hb.
    - rewrite EDk. left. reflexivity. }
  (* off the kid call's footprint: a byte of a block of Rem' other than at the kid node *)
  assert (HOFF : forall a1 k1 x, In (a1, k1) Rem' -> a1 - HEAD <= x < a1 + k1 ->
    ((a1, k1) = (kids, k0) -> ~ (v' <= x < v' + 56)) -> ~ inFP FP1 x).
  { intros a1 k1 x Hin1 Hx Hnode. pose proof (HR'R _ Hin1) as HinR.
    pose proof (HposR a1 k1 HinR) as Hk1. subst FP1. apply pjf_notFP_kid.
    - assert (Hcase : (a1, k1) = (kids, k0) \/ (a1, k1) <> (kids, k0)).
      { destruct (Z.eq_dec a1 kids) as [Eq1|Eq1]; [destruct (Z.eq_dec k1 k0) as [Eq2|Eq2]|].
        - left. subst. reflexivity.
        - right. intros E. injection E as _ E'. exact (Eq2 E').
        - right. intros E. injection E as E' _. exact (Eq1 E'). }
      destruct Hcase as [E | Hne]; [exact (Hnode E)|].
      destruct (HSEP a1 k1 kids k0 HinR HkR Hne); subst v'; unfold HEAD in *; lia.
    - intros a2 k2 Hin2. pose proof (HD1R a2 k2 Hin2) as Hin2R. pose proof (HposR a2 k2 Hin2R) as Hk2'.
      rewrite (Hreq k2 Hk2').
      assert (Hne : (a1, k1) <> (a2, k2)) by (intros E; rewrite E in Hin1; exact (HneD1 _ Hin1 Hin2)).
      destruct (HSEP a1 k1 a2 k2 HinR Hin2R Hne); unfold HEAD in *; lia.
    - apply (blk_img tfibsegs B LAWS lyc Sc Wc _ mdC (a1 - HEAD) (k1 + HEAD) x (proj1 HARU)
        (proj1 (HRBc a1 k1 HinR))). rewrite (Hreq k1 Hk1). unfold HEAD in *. lia. }
  (* v off the kid call's footprint, and its placement *)
  destruct (pjf_place B lyc Sc Wc (unpoison Uc (ms_mem ms)) mdC (ms_mem ms) v (proj1 HARU) HPOm) as (HPLm & _ & _).
  assert (HvOFF : forall x, v <= x < v + 56 -> ~ inFP FP1 x).
  { intros x Hx. subst FP1. apply pjf_notFP_kid.
    - destruct (pjf_v_apart lyc Sc Wc _ mdC (ms_mem ms) kids k0 (proj1 HARU) HPOm HkD (HRBc kids k0 HkR));
        subst v'; unfold HEAD in *; lia.
    - intros a2 k2 Hin2. pose proof (HD1R a2 k2 Hin2) as Hin2R. rewrite (Hreq k2 (HposR a2 k2 Hin2R)).
      destruct (pjf_v_apart lyc Sc Wc _ mdC (ms_mem ms) a2 k2 (proj1 HARU) HPOm (HD1D a2 k2 Hin2)
        (HRBc a2 k2 Hin2R)); unfold HEAD in *; lia.
    - exact (proj1 (proj2 (proj2 (HPLm x Hx)))). }
  assert (HFP1sh : forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Ha. subst FP1. apply pjf_inFP_cons in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha].
    - apply (fsw_ablock_off_shadow B lyc Sc Wc _ mdC (kids - HEAD) (k0 + HEAD) (proj1 HARU) Hkin).
      rewrite (Hreq k0 Hk0pos). subst v'. unfold HEAD in *. lia.
    - apply pjf_inFP_app in Ha. destruct Ha as [Ha | Ha].
      + apply pjf_inFP_hblocks in Ha. destruct Ha as (p & k1 & Hp & Hr).
        exact (fsw_ablock_off_shadow B lyc Sc Wc _ mdC (p - HEAD) (k1 + HEAD) (proj1 HARU)
          (proj1 (HRB1 p k1 Hp)) a Hr).
      + destruct Ha as (r & Hr & Har). unfold FS_PSTAT_FP in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Har; unfold SHADOW_OFF; lia. }
  assert (HH4 : FSupoisonU.fs_heads B ly4 S4 U4) by exact (pjf_heads_after lyc Sc Uc ly4 S4 D1 HHD HBP4).
  apply (K ly4 S4 U4 W4 regs4 mem4 md4).
  + split; [rewrite <- pjf_EV_app in HJ4; exact HJ4|].
    split; [exact HARU4|]. split; [exact HH4|].
    split.
    { pose proof (fsw_region_nth _ _ _ 0 _ HS4 eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
      assert (Q19 : YK11.getr regs4 19 = YK11.getr (ms_regs ms) 19) by exact (fsw_pres _ _ 19%bv HP4 ltac:(pjf_cs_reg)).
      assert (Q9 : YK11.getr regs4 9 = YK11.getr (ms_regs ms) 9) by exact (fsw_pres _ _ 9%bv HP4 ltac:(pjf_cs_reg)).
      refine (pjf_frm_of_region (Ereg regs4 (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H W4) mem4) HR0 _ _ _ _).
      - rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl). exact Hsp4.
      - intros i0 Hi0. exact (pjf_ew_saved regs4 [] i0 Hi0).
      - rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl), Q19, P19, H19. unfold w64. apply wz. lia.
      - rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl), Q9, P9, H9. unfold w64. apply wz. lia. }
    split.
    { rewrite pjf_rd_hblocks_app, <- app_assoc. etransitivity; [exact HBP|]. apply Permutation_app_head. exact HBP4. }
    split; [subst U4; rewrite pjf_rd_heads_app, <- pjf_udrop_app, <- HUc; reflexivity|].
    split.
    { rewrite pjf_rd_sum_app. replace (live - (rd_sum Dfr + rd_sum D1)) with (live - rd_sum Dfr - rd_sum D1) by lia.
      exact Hglob4. }
    split.
    { etransitivity; [exact HPD|]. subst Rem Rem'. rewrite <- app_assoc. apply Permutation_app_head.
      rewrite !app_assoc. apply Permutation_app_tail.
      etransitivity; [apply Permutation_app_comm|]. rewrite !app_assoc. reflexivity. }
    split.
    { intros a1 k1 Hin1. pose proof (HR'R _ Hin1) as HinR.
      apply (pjf_rblock_kept (STK_pj_free (2 - S k)) (spZ (ms_regs ms)) FP1 lyc Sc Uc Wc (ms_mem ms) mdC ly4 S4 U4 W4
        mem4 md4 (EV_pj_free D1) a1 k1 HJc HARU OK4 PO4); [|exact (HRBc a1 k1 HinR)].
      intros x Hx. apply (HOFF a1 k1 x Hin1); [unfold HEAD in *; pose proof (HposR a1 k1 HinR); lia|].
      intros E. injection E as -> ->. subst v'. unfold HEAD in *. lia. }
    split.
    { exact (pobj_kept_call B (STK_pj_free (2 - S k)) (spZ (ms_regs ms)) FP1 lyc Sc Uc Wc (ms_mem ms) mdC ly4 S4 U4
        W4 mem4 md4 (EV_pj_free D1) v HJc HARU OK4 PO4 HvOFF HFP1sh HH4 HPOm). }
    split.
    { apply (pjf_keep_call (pjf_FPS i i (Dky ++ D1 ++ Rest')) (pjf_FPS (S i) i (Dky ++ Rest'))
        (STK_pj_free (2 - S k)) (spZ (ms_regs ms)) FP1 lyc Sc Uc Wc memc mdC (ms_mem ms) ly4 S4 U4 W4 mem4 md4
        (EV_pj_free D1) HJc HARU OK4 PO4 HKEEP SB).
      intros x Hx. unfold pjf_FPS in Hx |- *.
      destruct Hx as [Hx | [(Hks & Hx) | [Hx | ((ba, bk) & Hb & Hx)]]].
      - split; [left; exact Hx|]. split; [exact (HvOFF x Hx)|]. split; [lia|].
        destruct HPOm as [[((cid & pos & Hin & _ & _ & H1 & H2) & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
        + right. exists cid, pos. split; [exact Hin | lia].
        + left. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
      - destruct HKEYS as [(_ & Hksf & _) | (_ & ky & HkyD & Hkyn & EDy)]; [congruence|].
        assert (HyR : In (keys, ky) Rem') by (subst Rem'; rewrite EDy, !in_app_iff; cbn [In]; tauto).
        pose proof (HR'R _ HyR) as HyRR. pose proof (HposR _ _ HyRR) as Hky0.
        destruct (fsw_rblock_low B lyc Sc Wc _ mdC (ms_mem ms) keys ky (proj1 HARU) (HRBc _ _ HyRR)) as (Hy1 & Hy2).
        split; [right; left; split; [exact Hks | lia]|].
        split.
        { apply (HOFF keys ky x HyR); [unfold HEAD in *; lia|].
          intros E. exfalso. apply (HNk (keys, ky)); [rewrite EDy, !in_app_iff; cbn [In]; tauto | exact E]. }
        split; [lia|]. left. exists (keys - HEAD), (ky + HEAD).
        split; [exact (proj1 (HRBc _ _ HyRR)) | rewrite (Hreq ky Hky0); unfold HEAD in *; lia].
      - assert (HkR' : In (kids, k0) Rem') by (subst Rem'; rewrite EDk, !in_app_iff; cbn [In]; tauto).
        split; [right; right; left; lia|].
        split.
        { apply (HOFF kids k0 x HkR'); [unfold HEAD in *; lia|]. intros _. subst v'. lia. }
        split; [lia|]. left. exists (kids - HEAD), (k0 + HEAD).
        split; [exact Hkin | rewrite (Hreq k0 Hk0pos); unfold HEAD in *; lia].
      - unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
        assert (HbR' : In (ba, bk) Rem') by (subst Rem'; rewrite !in_app_iff in *; tauto).
        pose proof (HR'R _ HbR') as HbR. pose proof (HposR _ _ HbR) as Hbk.
        destruct (fsw_rblock_low B lyc Sc Wc _ mdC (ms_mem ms) ba bk (proj1 HARU) (HRBc _ _ HbR)) as (Hb1 & Hb2).
        split; [right; right; right; exists (ba, bk); split; [rewrite !in_app_iff in *; tauto | unfold PjStruct.pj_holds; cbn [fst snd]; lia]|].
        split.
        { apply (HOFF ba bk x HbR'); [unfold HEAD in *; lia|].
          intros E. exfalso. apply (HNk (ba, bk)); [rewrite !in_app_iff in *; tauto | exact E]. }
        split; [lia|]. left. exists (ba - HEAD), (bk + HEAD).
        split; [exact (proj1 (HRBc _ _ HbR)) | rewrite (Hreq bk Hbk); unfold HEAD in *; lia]. }
    { apply (arodata_kept B (STK_pj_free (2 - S k)) (spZ (ms_regs ms)) FP1 lyc Sc Uc Wc (ms_mem ms) mdC ly4 S4 U4 W4
        mem4 md4 (EV_pj_free D1) HJc HARU OK4 PO4); [| |exact HROm].
      - subst FP1. apply pjf_notFP_kid.
        + subst v'. unfold HEAD in *. lia.
        + intros a2 k2 Hin2. pose proof (HD1R a2 k2 Hin2) as Hin2R. rewrite (Hreq k2 (HposR a2 k2 Hin2R)).
          destruct (fsw_rblock_low B lyc Sc Wc _ mdC (ms_mem ms) a2 k2 (proj1 HARU) (HRBc _ _ Hin2R)).
          unfold HEAD in *. lia.
        + intros Hi0. pose proof (pjf_img_low 0 Hi0). lia.
      - intros a Ha Hin. subst FP1. pose proof (fsw_roP_img a Ha) as Hai.
        apply pjf_inFP_cons in Hin. cbn [fst snd] in Hin. destruct Hin as [Hin | Hin].
        + apply (blk_img tfibsegs B LAWS lyc Sc Wc _ mdC (kids - HEAD) (k0 + HEAD) a (proj1 HARU) Hkin);
            [rewrite (Hreq k0 Hk0pos); subst v'; unfold HEAD in *; lia | exact Hai].
        + apply pjf_inFP_app in Hin. destruct Hin as [Hin | Hin]; [|exact (pjf_pstat_not_roP a Ha Hin)].
          apply pjf_inFP_hblocks in Hin. destruct Hin as (p & k1 & Hp & Hr).
          exact (blk_img tfibsegs B LAWS lyc Sc Wc _ mdC (p - HEAD) (k1 + HEAD) a (proj1 HARU) (proj1 (HRB1 p k1 Hp))
            Hr Hai). }
  + apply (pjf_lregs_of i (ms_regs ms) regs4 HLc); (apply (fsw_pres _ _ _ HP4); pjf_cs_reg).
Qed.


(* ---- the resume at 0x837a4 after fuzz_free (keys[i]): the invariant with keys[i]'s string block (if any) freed.
   The callee's footprint FP1 is fs's statics and the freed block. ---- *)
Lemma pjf_key_resume : forall i Dfr Dky Rest' lyc Sc Uc (Wc : world tfibsegs) memc mdc regsC memC mdC FP1 kc
    ly' S' U' (W' : world tfibsegs) regs' mem' md' (Q : world tfibsegs -> config -> Prop),
  (i < Z.to_nat n)%nat ->
  pjf_inv (pjf_FPS (S i) i (Dky ++ Rest')) Dfr (Ds ++ Dk ++ Dy ++ Dky ++ Rest') lyc Sc Uc Wc memc mdc ->
  same_below memc memC alloc_ceiling ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memC) mdC (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdC ->
  pjf_frm Wc memC -> pjf_lregs i regsC ->
  ajournal tfibsegs B STK_fuzz_free (spZ regsC) FP1 lyc Sc Wc (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem')
    md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regsC regs' ->
  kc = EV_pj_free Dky ->
  Permutation (ablocks B lyc Sc) (rd_hblocks Dky ++ ablocks B ly' S') ->
  U' = udrop Uc (rd_heads Dky) -> FSupoisonU.fs_heads B ly' S' U' ->
  fs_glob tfibsegs W' mem' (live - rd_sum Dfr - rd_sum Dky) peak cnt fail ->
  (forall a, inFP FP1 a -> inFP FS_PSTAT_FP a \/ exists a1 k1, In (a1, k1) Dky /\ a1 - HEAD <= a < a1 + k1) ->
  (forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') (Dfr ++ Dky) (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs i regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x837a4) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x837a4) mem' (YK11.seg_rom tfibsegs)) md') Q.
Proof.
intros i Dfr Dky Rest' lyc Sc Uc Wc memc mdc regsC memC mdC FP1 kc ly' S' U' W' regs' mem' md' Q Hi HINV SB HJ HARU
  Hfrm1 HLc HJc OK' PO' HP' Ekc HBP' EU' HH' Hglob' HFP1 K.
destruct HINV as (_ & _ & HHD & _ & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HLc as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HSS as [Hgot Hcell].
set (Rem := Ds ++ Dk ++ Dy ++ Dky ++ Rest') in *.
set (Rem' := Ds ++ Dk ++ Dy ++ Rest').
pose proof (proj1 HARU) as HARC.
assert (HRBC : rd_blocks_ok tfibsegs B lyc Sc Wc memC Rem) by exact (rd_blocks_ok_below B lyc Sc Wc _ mdC memc memC Rem HARC SB HRB).
assert (HPOC : pobj tfibsegs B lyc Sc Wc memC v) by exact (pobj_below B lyc Sc Wc _ mdC memc memC v HARC SB HPOc).
assert (HROC : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC)) by exact (arodata_below B Wc memc memC SB HRO).
assert (HNDR : List.NoDup (Dfr ++ Rem))
  by (apply (Permutation_NoDup HPD); first [exact HND | apply NoDup_ListNoDup; exact HND]).
assert (HNDRem : List.NoDup Rem) by exact (List.NoDup_app_remove_l _ _ HNDR).
assert (HposR : forall a1 k1, In (a1, k1) Rem -> 0 < k1) by (intros a1 k1 H; exact (proj1 (proj2 (proj2 (HRB a1 k1 H))))).
assert (HR'R : forall b, In b Rem' -> In b Rem) by (intros b H; subst Rem Rem'; rewrite !in_app_iff in *; tauto).
assert (HDkyR : forall b, In b Dky -> In b Rem) by (intros b H; subst Rem; rewrite !in_app_iff; tauto).
assert (HRD : forall b, In b Rem -> In b D)
  by (intros b H; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact H).
assert (HneDky : forall b, In b Rem' -> In b Dky -> False).
{ intros b H1 H2. apply (pjf_nodup_mid (Ds ++ Dk ++ Dy) Dky Rest' b).
  - subst Rem. rewrite <- !app_assoc. exact HNDRem.
  - subst Rem'. rewrite !in_app_iff in *. tauto.
  - exact H2. }
assert (HSEP : forall a1 k1 a2 k2, In (a1, k1) Rem -> In (a2, k2) Rem -> (a1, k1) <> (a2, k2) ->
  a1 + k1 <= a2 - HEAD \/ a2 + k2 <= a1 - HEAD)
  by (intros a1 k1 a2 k2 H1 H2 Hne; exact (pjf_blk_sep lyc Sc Wc _ mdC memC a1 k1 a2 k2 HARC
        (HRBC a1 k1 H1) (HRBC a2 k2 H2) Hne)).
assert (Hreq : forall k1, 0 < k1 -> req_size (k1 + HEAD) = k1 + HEAD) by (intros k1 H; apply pjf_req; unfold HEAD; lia).
(* off the callee's footprint *)
assert (HOFF : forall a1 k1 x, In (a1, k1) Rem' -> a1 - HEAD <= x < a1 + k1 -> ~ inFP FP1 x).
{ intros a1 k1 x Hin1 Hx Hfp. pose proof (HR'R _ Hin1) as HinR. pose proof (HposR a1 k1 HinR) as Hk1.
  destruct (HFP1 x Hfp) as [Hs | (a2 & k2 & Hin2 & Hr)].
  - apply (blk_img tfibsegs B LAWS lyc Sc Wc _ mdC (a1 - HEAD) (k1 + HEAD) x HARC (proj1 (HRBC a1 k1 HinR)));
      [rewrite (Hreq k1 Hk1); unfold HEAD in *; lia | exact (pjf_pstat_img x Hs)].
  - assert (Hne : (a1, k1) <> (a2, k2)) by (intros E; rewrite E in Hin1; exact (HneDky _ Hin1 Hin2)).
    destruct (HSEP a1 k1 a2 k2 HinR (HDkyR _ Hin2) Hne); unfold HEAD in *; lia. }
destruct (pjf_place B lyc Sc Wc (unpoison Uc memC) mdC memC v HARC HPOC) as (HPLm & _ & _).
assert (HvOFF : forall x, v <= x < v + 56 -> ~ inFP FP1 x).
{ intros x Hx Hfp. destruct (HFP1 x Hfp) as [Hs | (a2 & k2 & Hin2 & Hr)].
  - exact (proj1 (proj2 (proj2 (HPLm x Hx))) (pjf_pstat_img x Hs)).
  - destruct (pjf_v_apart lyc Sc Wc _ mdC memC a2 k2 HARC HPOC (HRD _ (HDkyR _ Hin2)) (HRBC a2 k2 (HDkyR _ Hin2)));
      unfold HEAD in *; lia. }
assert (HFP1sh : forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
{ intros a Hfp. destruct (HFP1 a Hfp) as [(r & Hr & Har) | (a2 & k2 & Hin2 & Hr)].
  - unfold FS_PSTAT_FP in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Har; unfold SHADOW_OFF; lia.
  - pose proof (HposR a2 k2 (HDkyR _ Hin2)) as Hk2.
    apply (fsw_ablock_off_shadow B lyc Sc Wc _ mdC (a2 - HEAD) (k2 + HEAD) HARC (proj1 (HRBC a2 k2 (HDkyR _ Hin2)))).
    rewrite (Hreq k2 Hk2). unfold HEAD in *. lia. }
(* the caller's journal across the call *)
assert (HFPS : fsw_fp_sub B ly S0 lyc Sc [] FP FP1).
{ intros a Ha. destruct (HFP1 a Ha) as [Hs | (a1 & k1 & Hin1 & Hr)].
  - right. right. left. split; [apply pjf_inFP_cons; right; apply pjf_inFP_app; right; exact Hs|].
    exact (pjf_pstat_img a Hs).
  - pose proof (HposR a1 k1 (HDkyR _ Hin1)) as Hk1. left. split.
    + apply pjf_inFP_cons. right. apply pjf_inFP_app. left. apply pjf_inFP_hblocks.
      exists a1, k1. split; [exact (HRD _ (HDkyR _ Hin1)) | rewrite (Hreq k1 Hk1); unfold HEAD in *; lia].
    + exists (a1 - HEAD), (k1 + HEAD). split; [exact (proj1 (HRB a1 k1 (HDkyR _ Hin1))) | rewrite (Hreq k1 Hk1); lia]. }
assert (HP'sp : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (fsw_pres _ _ 2%bv HP' ltac:(pjf_cs_reg)).
assert (Hsp' : spZ regs' = sp0 - 128) by (unfold spZ at 1; rewrite HP'sp; exact Hsp).
assert (Ef : STK_fuzz_free = ltac:(let v := eval vm_compute in (STK_fuzz_free) in exact v)) by (vm_compute; reflexivity).
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc memC mdC (EV_pj_free Dfr)
  STK_fuzz_free FP1 128 regsC ly' S' U' W' regs' mem' md' kc (pjf_saved regs ++ []) pjf_cs [] [] 0x837a4
  Hgot Hcell HJ HARU HJc HFPS OK' PO' HP') as (HJ4 & HARU4 & HS4).
- exact Hsp.
- lia.
- lia.
- lia.
- reflexivity.
- vm_compute. reflexivity.
- unfold pjf_cs. repeat constructor; cbn; lia.
- assert (Q19 : YK11.getr regs' 19 = YK11.getr regsC 19) by exact (fsw_pres _ _ 19%bv HP' ltac:(pjf_cs_reg)).
  assert (Q9 : YK11.getr regs' 9 = YK11.getr regsC 9) by exact (fsw_pres _ _ 9%bv HP' ltac:(pjf_cs_reg)).
  pose proof Hfrm1 as (Hfj1 & Hfs1 & Hfs2).
  apply (pjf_cs_ok (Ereg regs' (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H Wc) memC));
    [rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp' | exact (pjf_ew_saved regs' [])
     | rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), Q19, H19; unfold w64; apply wz; lia
     | rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), Q9, H9; unfold w64; apply wz; lia
     | exact Hfj1 | exact Hfs1 | exact Hfs2].
- constructor.
- apply pairwise_disjoint_of_extents. unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region,
    extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl).
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold spZ in Hsp'; unfold sp0, STK in *;
  first [left; lia | right; lia].
- exact I.
- apply (K ly' S' U' W' regs' mem' md').
  + split; [rewrite Ekc, <- pjf_EV_app in HJ4; exact HJ4|].
    split; [exact HARU4|]. split; [exact HH'|].
    split.
    { pose proof (fsw_region_nth _ _ _ 0 _ HS4 eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
      assert (Q19 : YK11.getr regs' 19 = YK11.getr regsC 19) by exact (fsw_pres _ _ 19%bv HP' ltac:(pjf_cs_reg)).
      assert (Q9 : YK11.getr regs' 9 = YK11.getr regsC 9) by exact (fsw_pres _ _ 9%bv HP' ltac:(pjf_cs_reg)).
      refine (pjf_frm_of_region (Ereg regs' (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H W') mem') HR0 _ _ _ _).
      - rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl). exact Hsp'.
      - intros i0 Hi0. exact (pjf_ew_saved regs' [] i0 Hi0).
      - rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), Q19, H19. unfold w64. apply wz. lia.
      - rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), Q9, H9. unfold w64. apply wz. lia. }
    split.
    { rewrite pjf_rd_hblocks_app, <- app_assoc. etransitivity; [exact HBP|]. apply Permutation_app_head. exact HBP'. }
    split; [rewrite EU', pjf_rd_heads_app, <- pjf_udrop_app, <- HUc; reflexivity|].
    split.
    { rewrite pjf_rd_sum_app. replace (live - (rd_sum Dfr + rd_sum Dky)) with (live - rd_sum Dfr - rd_sum Dky) by lia.
      exact Hglob'. }
    split.
    { etransitivity; [exact HPD|]. subst Rem Rem'. rewrite <- app_assoc. apply Permutation_app_head.
      rewrite !app_assoc. apply Permutation_app_tail.
      etransitivity; [apply Permutation_app_comm|]. rewrite !app_assoc. reflexivity. }
    split.
    { exact (rd_blocks_ok_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdC ly' S' U' W' mem' md' kc Rem'
        HJc HARU OK' PO' HOFF (fun a1 k1 H => HRBC a1 k1 (HR'R _ H))). }
    split.
    { exact (pobj_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdC ly' S' U' W' mem' md' kc v
        HJc HARU OK' PO' HvOFF HFP1sh HH' HPOC). }
    split.
    { apply (pjf_keep_call (pjf_FPS (S i) i (Dky ++ Rest')) (pjf_FPS (S i) (S i) Rest')
        STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memc mdC memC ly' S' U' W' mem' md' kc HJc HARU OK' PO' HKEEP SB).
      intros x Hx. unfold pjf_FPS in Hx |- *.
      destruct Hx as [Hx | [(Hks & Hx) | [Hx | ((ba, bk) & Hb & Hx)]]].
      - split; [left; exact Hx|]. split; [exact (HvOFF x Hx)|]. split; [lia|].
        destruct HPOC as [[((cid & pos & Hin & _ & _ & H1 & H2) & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
        + right. exists cid, pos. split; [exact Hin | lia].
        + left. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
      - destruct HKEYS as [(_ & Hksf & _) | (_ & ky & HkyD & Hkyn & EDy)]; [congruence|].
        assert (HyR : In (keys, ky) Rem') by (subst Rem'; rewrite EDy, !in_app_iff; cbn [In]; tauto).
        pose proof (HR'R _ HyR) as HyRR. pose proof (HposR _ _ HyRR) as Hky0.
        destruct (fsw_rblock_low B lyc Sc Wc _ mdC memC keys ky HARC (HRBC _ _ HyRR)) as (Hy1 & Hy2).
        split; [right; left; split; [exact Hks | lia]|].
        split; [apply (HOFF keys ky x HyR); unfold HEAD in *; lia|].
        split; [lia|]. left. exists (keys - HEAD), (ky + HEAD).
        split; [exact (proj1 (HRBC _ _ HyRR)) | rewrite (Hreq ky Hky0); unfold HEAD in *; lia].
      - destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & EDk)]; [lia|].
        assert (HkR' : In (kids, k0) Rem') by (subst Rem'; rewrite EDk, !in_app_iff; cbn [In]; tauto).
        pose proof (HR'R _ HkR') as HkRR. pose proof (HposR _ _ HkRR) as Hk0'.
        destruct (fsw_rblock_low B lyc Sc Wc _ mdC memC kids k0 HARC (HRBC _ _ HkRR)) as (Hk1 & Hk2).
        split; [right; right; left; lia|].
        split; [apply (HOFF kids k0 x HkR'); unfold HEAD in *; lia|].
        split; [lia|]. left. exists (kids - HEAD), (k0 + HEAD).
        split; [exact (proj1 (HRBC _ _ HkRR)) | rewrite (Hreq k0 Hk0'); unfold HEAD in *; lia].
      - unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
        assert (HbR' : In (ba, bk) Rem') by (subst Rem'; rewrite !in_app_iff in *; tauto).
        pose proof (HR'R _ HbR') as HbR. pose proof (HposR _ _ HbR) as Hbk.
        destruct (fsw_rblock_low B lyc Sc Wc _ mdC memC ba bk HARC (HRBC _ _ HbR)) as (Hb1 & Hb2).
        split; [right; right; right; exists (ba, bk); split; [rewrite !in_app_iff; tauto | unfold PjStruct.pj_holds; cbn [fst snd]; lia]|].
        split; [apply (HOFF ba bk x HbR'); unfold HEAD in *; lia|].
        split; [lia|]. left. exists (ba - HEAD), (bk + HEAD).
        split; [exact (proj1 (HRBC _ _ HbR)) | rewrite (Hreq bk Hbk); unfold HEAD in *; lia]. }
    { apply (arodata_kept B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdC ly' S' U' W' mem' md' kc HJc HARU
        OK' PO'); [| |exact HROC].
      - intros Hfp. destruct (HFP1 0 Hfp) as [(r & Hr & Har) | (a2 & k2 & Hin2 & Hr)].
        + unfold FS_PSTAT_FP in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Har; lia.
        + destruct (fsw_rblock_low B lyc Sc Wc _ mdC memC a2 k2 HARC (HRBC _ _ (HDkyR _ Hin2))).
          unfold HEAD in *. lia.
      - intros a Ha Hfp. destruct (HFP1 a Hfp) as [Hs | (a2 & k2 & Hin2 & Hr)]; [exact (pjf_pstat_not_roP a Ha Hs)|].
        pose proof (HposR a2 k2 (HDkyR _ Hin2)) as Hk2.
        apply (blk_img tfibsegs B LAWS lyc Sc Wc _ mdC (a2 - HEAD) (k2 + HEAD) a HARC (proj1 (HRBC a2 k2 (HDkyR _ Hin2))));
          [rewrite (Hreq k2 Hk2); unfold HEAD in *; lia | exact (fsw_roP_img a Ha)]. }
  + apply (pjf_lregs_of i regsC regs' HLc); (apply (fsw_pres _ _ _ HP'); pjf_cs_reg).
Qed.

(* ---- 0x83764 .. 0x837a4: the keys test and fuzz_free (keys[i]) ---- *)
Lemma pjf_seg_key : forall i Dfr Dky Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (i < Z.to_nat n)%nat ->
  pjf_inv (pjf_FPS (S i) i (Dky ++ Rest')) Dfr (Ds ++ Dk ++ Dy ++ Dky ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  PjStruct.pj_key tfibsegs m0 (fun a n0 => In (a, n0) D) ks (keys + 8 * Z.of_nat i) Dky ->
  (forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') (Dfr ++ Dky) (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs i regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x837a4) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x83764) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Dky Rest' lyc Sc Uc Wc regsc memc mdc Q Hi HINV HL Hkey K.
pose proof HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
assert (Hn1 : 1 <= n) by lia.
pose proof (pjf_n_bound Hn1) as (Hn54 & Hnb).
assert (Hi54 : Z.of_nat i <= 2 ^ 54) by lia.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 HARU) as HARc.
set (Rem := Ds ++ Dk ++ Dy ++ Dky ++ Rest') in *.
assert (HposR : forall a1 k1, In (a1, k1) Rem -> 0 < k1) by (intros a1 k1 H; exact (proj1 (proj2 (proj2 (HRB a1 k1 H))))).
assert (HDkyR : forall b, In b Dky -> In b Rem) by (intros b H; subst Rem; rewrite !in_app_iff; tauto).
assert (HRD : forall b, In b Rem -> In b D)
  by (intros b H; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact H).
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
assert (Vkf : val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 32) 8 keys).
{ intros j0 Hj0. unfold mbyte. rewrite (HKEEP (Z_to_bv 64 (v + 32 + Z.of_nat j0))).
  - exact (fsw_pj_u64_val tfibsegs _ _ _ Hkeys j0 Hj0).
  - rewrite wz by lia. unfold pjf_FPS. left. lia. }
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v HARc HPOc) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct HPOc as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
assert (HAPP : app_addr (v + 32)) by exact (proj2 (proj2 (proj2 (HPL (v + 32) ltac:(lia))))).
destruct (pjf_shadow_apart (v + 32) HAPP) as (HS1 & HS2).
pose proof (pjf_disj_img v 32 40 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_got_img) as HdG.
pose proof (pjf_disj_img v 32 40 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_cell_img) as HdC.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (Hpres : forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
destruct HKEYS as [(Ek0 & Eks & EDy) | (Eks & ky & HkyD & Hkyn & EDy)].
- (* ---- keys = 0: the `beqz` at 0x83770 goes to 0x837a4, no call ---- *)
  rewrite Eks in Hkey. cbn [PjStruct.pj_key] in Hkey. subst Dky. rewrite Ek0 in Vkf.
  set (xs := @nil word).
  assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 128)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
  assert (E9 : bv_unsigned (ew (pjf_env regsc xs) 9) = v + 32)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
  assert (E20 : bv_unsigned (ew (pjf_env regsc xs) 20) = shadow_of_addr SHADOW_OFF (v + 32))
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl), H20; unfold w64; apply wz;
        unfold shadow_of_addr, SHADOW_OFF in *; lia).
  unfold pjf_env in E2, E9, E20.
  assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_Lz
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83764) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x83764 [shr 20; fld0 9 0] [] [] xs HARU (proj1 HL) Hpres Hfrm
      ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor; [|constructor]].
      + apply (pjf_shr_ok regsc xs 20%bv 20 Wc memc (v + 32));
          [reflexivity | exact H20 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
        intros x Hx. apply HRA. lia.
      + apply (pjf_fld0_ok regsc xs 9%bv 9 0 Wc memc (v + 32)); [reflexivity | exact H9 | lia | lia | lia |].
        rewrite Z.add_0_r. exact Vkf.
    - unfold pjf_env. apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld0, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - exact I.
    - exact I. }
  assert (E2' : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-128)) by (unfold pjf_env; lia).
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x837a4.
  { cbn [ss_mem ss_Lz pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_Lz) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [shr 20; fld0 9 0] a (sp0 - 128)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
      ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
    unfold sp0, STK in *. lia. }
  assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regsc 2)
    by exact (fsw_reg_atom _ _ _ _ ms 2%bv 2%bv 2 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regsc 3)
    by exact (fsw_reg_atom _ _ _ _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regsc 4)
    by exact (fsw_reg_atom _ _ _ _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regsc 8)
    by exact (fsw_reg_atom _ _ _ _ ms 8%bv 8%bv 8 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regsc 9)
    by exact (fsw_reg_atom _ _ _ _ ms 9%bv 9%bv 9 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P18 : YK11.getr (ms_regs ms) 18 = YK11.getr regsc 18)
    by exact (fsw_reg_atom _ _ _ _ ms 18%bv 18%bv 18 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P19 : YK11.getr (ms_regs ms) 19 = YK11.getr regsc 19)
    by exact (fsw_reg_atom _ _ _ _ ms 19%bv 19%bv 19 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P20 : YK11.getr (ms_regs ms) 20 = YK11.getr regsc 20)
    by exact (fsw_reg_atom _ _ _ _ ms 20%bv 20%bv 20 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P21 : YK11.getr (ms_regs ms) 21 = YK11.getr regsc 21)
    by exact (fsw_reg_atom _ _ _ _ ms 21%bv 21%bv 21 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P22 : YK11.getr (ms_regs ms) 22 = YK11.getr regsc 22)
    by exact (fsw_reg_atom _ _ _ _ ms 22%bv 22%bv 22 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P23 : YK11.getr (ms_regs ms) 23 = YK11.getr regsc 23)
    by exact (fsw_reg_atom _ _ _ _ ms 23%bv 23%bv 23 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P24 : YK11.getr (ms_regs ms) 24 = YK11.getr regsc 24)
    by exact (fsw_reg_atom _ _ _ _ ms 24%bv 24%bv 24 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P25 : YK11.getr (ms_regs ms) 25 = YK11.getr regsc 25)
    by exact (fsw_reg_atom _ _ _ _ ms 25%bv 25%bv 25 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P26 : YK11.getr (ms_regs ms) 26 = YK11.getr regsc 26)
    by exact (fsw_reg_atom _ _ _ _ ms 26%bv 26%bv 26 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  apply (K lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + rewrite app_nil_r. cbn [app] in *.
    split; [exact HJ|]. split; [exact HARU|]. split; [exact HHD|].
    split.
    { pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
      refine (pjf_frm_of_region (pjf_env regsc xs) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
      - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
      - intros i0 Hi0. exact (pjf_ew_sav regsc xs (33 + i0) i0 eq_refl Hi0).
      - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
      - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
    split; [exact HBP|]. split; [exact HUc|].
    split; [exact (fs_glob_below Wc memc (ms_mem ms) _ peak cnt fail SB Hglob)|].
    split; [exact HPD|].
    split; [exact (rd_blocks_ok_below B lyc Sc Wc _ mdc memc (ms_mem ms) _ HARc SB HRB)|].
    split; [exact (pobj_below B lyc Sc Wc _ mdc memc (ms_mem ms) v HARc SB HPOc)|].
    split; [|exact (arodata_below B Wc memc (ms_mem ms) SB HRO)].
    intros x Hx. pose proof (u64_range x) as Rx.
    assert (Hx' : pjf_FPS (S i) i Rest' (bv_unsigned x)).
    { unfold pjf_FPS in Hx |- *. destruct Hx as [Hx | [(Hks & _) | Hx]]; [left; exact Hx | congruence | right; right; exact Hx]. }
    rewrite <- (HKEEP x Hx'). rewrite <- (Z_to_bv_bv_unsigned 64 x).
    apply (fsw_mrestrict_belowZ (w_H Wc) memc (ms_mem ms) _ SB). split; [lia|].
    unfold pjf_FPS in Hx'. destruct Hx' as [Hx' | [(Hks & _) | [Hx' | ((ba, bk) & Hb & Hx')]]]; [lia | congruence | |].
    * destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & EDk)]; [lia|].
      destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 pjf_HAR0 (HBK kids k0 Hk0D)). lia.
    * unfold PjStruct.pj_holds in Hx'. cbn [fst snd] in Hx'.
      assert (HbR : In (ba, bk) Rem) by (subst Rem; rewrite !in_app_iff; tauto).
      destruct (fsw_rblock_low B lyc Sc Wc _ mdc memc ba bk HARc (HRB ba bk HbR)). lia.
  + apply (pjf_lregs_of i regsc (ms_regs ms) HL); assumption.
- (* ---- keys <> 0: keys[i] (atom 47) at ka = keys + 8 i (atom 46 = keys + s7), the shadow check of ka (token run),
     fuzz_free (keys[i]) ---- *)
  rewrite Eks in Hkey. cbn [PjStruct.pj_key] in Hkey. destruct Hkey as (x & Hxu & Hxc).
  assert (HyR : In (keys, ky) Rem) by (subst Rem; rewrite EDy, !in_app_iff; cbn [In]; tauto).
  pose proof (HRB keys ky HyR) as Hyblk. pose proof Hyblk as (Hyin & Hy16 & Hy0 & _).
  destruct (fsw_rblock_low B lyc Sc Wc _ mdc memc keys ky HARc Hyblk) as (Hyl & Hyh).
  set (ka := keys + 8 * Z.of_nat i) in *.
  assert (Vks : val_mem tfibsegs (mrestrict (w_H Wc) memc) ka 8 x).
  { intros j0 Hj0. unfold mbyte. rewrite (HKEEP (Z_to_bv 64 (ka + Z.of_nat j0))).
    - exact (fsw_pj_u64_val tfibsegs _ _ _ Hxu j0 Hj0).
    - rewrite wz by (subst ka; unfold HEAD in *; lia). unfold pjf_FPS. right. left. split; [exact Eks | subst ka; unfold HEAD in *; lia]. }
  destruct Hxu as (Hx64 & _).
  assert (Rky : req_size (ky + HEAD) = ky + HEAD) by (apply pjf_req; unfold HEAD; lia).
  destruct (al_blocks _ _ LAWS lyc Sc Wc _ mdc (keys - HEAD) (ky + HEAD) HARc Hyin) as (_ & _ & _ & HappY & _).
  assert (HkaA0 : app_addr ka) by (apply (in_app_addr _ _ ka HappY); rewrite ?Rky; subst ka; unfold HEAD in *; lia).
  assert (HkaA7 : app_addr (ka + 7)) by (apply (in_app_addr _ _ (ka + 7) HappY); rewrite ?Rky; subst ka; unfold HEAD in *; lia).
  assert (HkaNI : forall y, ka <= y < ka + 8 -> ~ in_img tfibsegs y).
  { intros y Hy. apply (blk_img tfibsegs B LAWS lyc Sc Wc _ mdc (keys - HEAD) (ky + HEAD) y HARc Hyin).
    rewrite Rky. subst ka. unfold HEAD in *. lia. }
  pose proof (pjf_disj_img_blk ka tfib_D_GOT_asan_shadow_memory_dynamic_address HkaNI pjf_got_img) as HkaG.
  pose proof (pjf_disj_img_blk ka tfib_D_asan_shadow_memory_dynamic_address HkaNI pjf_cell_img) as HkaC.
  assert (Hkav : ka + 8 <= v \/ v + 56 <= ka).
  { destruct (pjf_v_apart lyc Sc Wc _ mdc memc keys ky HARc HPOc HkyD Hyblk); subst ka; unfold HEAD in *; lia. }
  set (xs := [w64 keys; w64 ka; w64 x]).
  assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 128)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
  assert (E9 : bv_unsigned (ew (pjf_env regsc xs) 9) = v + 32)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
  assert (E25 : ew (pjf_env regsc xs) 25 = Z_to_bv 64 (8 * Z.of_nat i))
    by exact (eq_trans (ew_Ereg_nat regsc _ 25 25%bv eq_refl) H25).
  assert (E20 : bv_unsigned (ew (pjf_env regsc xs) 20) = shadow_of_addr SHADOW_OFF (v + 32))
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl), H20; unfold w64; apply wz;
        unfold shadow_of_addr, SHADOW_OFF in *; lia).
  assert (E46 : ew (pjf_env regsc xs) 46 = Z_to_bv 64 keys) by (rewrite (pjf_ew_x regsc xs 46 0 eq_refl); reflexivity).
  assert (E47 : ew (pjf_env regsc xs) 47 = Z_to_bv 64 ka) by (rewrite (pjf_ew_x regsc xs 47 1 eq_refl); reflexivity).
  assert (E48 : ew (pjf_env regsc xs) 48 = Z_to_bv 64 x) by (rewrite (pjf_ew_x regsc xs 48 2 eq_refl); reflexivity).
  assert (E47u : bv_unsigned (ew (pjf_env regsc xs) 47) = ka) by (rewrite E47; apply wz; subst ka; unfold HEAD in *; lia).
  assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_R1a
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83764) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_reseatC lyc Sc Uc Wc regsc memc mdc 0x83764 [shr 20; fld 9 0 46; fld 47 0 48]
      [(46%nat, mkAF 4112 PJF_CEIL 4); (47%nat, mkAF 4096 PJF_CEIL 3); (25%nat, mkAF 0 (2 ^ 57) 3)]
      [pjf_Ckey] [(SAlu ALU_ADD (SOff 46 0) (SOff 25 0), SOff 47 0)]
      xs HARU (proj1 HL) Hpres Hfrm ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + apply (pjf_shr_ok regsc xs 20%bv 20 Wc memc (v + 32));
          [reflexivity | exact H20 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
        intros y Hy. apply HRA. lia.
      + apply (pjf_fld_ok regsc xs 9%bv 9 0 46 Wc memc (v + 32) keys);
          [reflexivity | exact H9 | lia | lia | lia | rewrite fsw_SOff0, E46; reflexivity
           | unfold HEAD in *; lia | rewrite Z.add_0_r; exact Vkf].
      + unfold region_ok, fld. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E47u.
        split; [subst ka; unfold HEAD in *; lia|]. split; [subst ka; unfold HEAD in *; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val tfibsegs (pjf_env regsc xs) _ ka 0 8 (SOff 48 0) x);
          [rewrite fsw_SOff0, E48; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vks].
    - destruct (pjf_shadow_apart (v + 32) HAPP) as (HS1' & _).
      apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E2, E9, E20, E47u.
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkaA0, HkaA7.
      unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E46, E47, (wz keys), (wz ka) by (subst ka; unfold HEAD in *; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8.
      unfold HEAD in *.
      rewrite E25, (wz (8 * Z.of_nat i)) by lia.
      split; [split; [unfold PJF_CEIL; lia | split; [exact Hy16 | lia]]|].
      split; [split; [subst ka; unfold PJF_CEIL; lia | split; [subst ka; Z.div_mod_to_equations; lia | lia]]|].
      split; [split; [lia | split; [Z.div_mod_to_equations; lia | lia]] | exact I].
    - cbn [alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite E46, E25, E47.
      rewrite !(wz keys), (wz (8 * Z.of_nat i)), (wz ka) by (subst ka; unfold HEAD in *; lia). rewrite !Z.add_0_r.
      rewrite alu64_add_lit. reflexivity.
    - cbn [conds_ok]. split; [|exact I].
      exact (pjf_acond_key (pjf_env regsc xs) keys (8 * Z.of_nat i) E46
        ltac:(rewrite E25; apply wz; lia) ltac:(unfold PJF_CEIL in *; unfold HEAD in *; lia) ltac:(lia)). }
  assert (SHOK : sh_ok tfibsegs pBx SH_R1a (pjf_env regsc xs) (mrestrict (w_H Wc) memc)).
  { constructor; [|constructor].
    apply (pjf_shent (pjf_env regsc xs) (mrestrict (w_H Wc) memc) 47 ka 0 8).
    - exact (pjf_U_bx regsc _ H23).
    - unfold YP0e.U. rewrite fsw_SOff0. rewrite E47u. reflexivity.
    - lia.
    - rewrite Z.add_0_r. change (rd_of tfibsegs (mrestrict (w_H Wc) memc)) with (aview tfibsegs (w_H Wc) memc).
      apply (fsw_block_body_addressable B lyc Sc Uc Wc memc mdc (keys - HEAD) (ky + HEAD) ka 8 HARU HHD Hyin);
        [subst ka; unfold HEAD in *; lia | lia | rewrite Rky; subst ka; unfold HEAD in *; lia].
    - rewrite Z.add_0_r. apply (in_app_sub _ _ ka 8 HappY); rewrite ?Rky; subst ka; unfold HEAD in *; lia. }
  assert (E2' : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-128)) by lia.
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 0x82dbc.
  { cbn [ss_mem ss_R1a pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  set (mdC := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_R1a) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [shr 20; fld 9 0 46; fld 47 0 48] a (sp0 - 128)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
      ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
    unfold sp0, STK in *. lia. }
  pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x837a4 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  assert (R10 : YK11.getr (ms_regs ms) 10 = w64 x).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms 10%bv HSc).
    lazymatch type of HSc with st_ok _ _ ?ssf _ =>
      replace (sr_get (ss_regs ssf) 10%bv) with (SOff 48 0) by (vm_compute; reflexivity) end.
    rewrite fsw_SOff0, E48. reflexivity. }
  assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regsc 2)
    by exact (fsw_reg_atom _ _ _ _ ms 2%bv 2%bv 2 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regsc 3)
    by exact (fsw_reg_atom _ _ _ _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regsc 4)
    by exact (fsw_reg_atom _ _ _ _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regsc 8)
    by exact (fsw_reg_atom _ _ _ _ ms 8%bv 8%bv 8 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regsc 9)
    by exact (fsw_reg_atom _ _ _ _ ms 9%bv 9%bv 9 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P18 : YK11.getr (ms_regs ms) 18 = YK11.getr regsc 18)
    by exact (fsw_reg_atom _ _ _ _ ms 18%bv 18%bv 18 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P19 : YK11.getr (ms_regs ms) 19 = YK11.getr regsc 19)
    by exact (fsw_reg_atom _ _ _ _ ms 19%bv 19%bv 19 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P20 : YK11.getr (ms_regs ms) 20 = YK11.getr regsc 20)
    by exact (fsw_reg_atom _ _ _ _ ms 20%bv 20%bv 20 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P21 : YK11.getr (ms_regs ms) 21 = YK11.getr regsc 21)
    by exact (fsw_reg_atom _ _ _ _ ms 21%bv 21%bv 21 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P22 : YK11.getr (ms_regs ms) 22 = YK11.getr regsc 22)
    by exact (fsw_reg_atom _ _ _ _ ms 22%bv 22%bv 22 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P23 : YK11.getr (ms_regs ms) 23 = YK11.getr regsc 23)
    by exact (fsw_reg_atom _ _ _ _ ms 23%bv 23%bv 23 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P24 : YK11.getr (ms_regs ms) 24 = YK11.getr regsc 24)
    by exact (fsw_reg_atom _ _ _ _ ms 24%bv 24%bv 24 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P25 : YK11.getr (ms_regs ms) 25 = YK11.getr regsc 25)
    by exact (fsw_reg_atom _ _ _ _ ms 25%bv 25%bv 25 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P26 : YK11.getr (ms_regs ms) 26 = YK11.getr regsc 26)
    by exact (fsw_reg_atom _ _ _ _ ms 26%bv 26%bv 26 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (HspC : spZ (ms_regs ms) = sp0 + (-128)) by (unfold spZ at 1; rewrite P2; unfold spZ in Hsp; lia).
  assert (HLc : pjf_lregs i (ms_regs ms))
    by (apply (pjf_lregs_of i regsc (ms_regs ms) HL); assumption).
  assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
  { pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    refine (pjf_frm_of_region (pjf_env regsc xs) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
    - exact E2.
    - intros i0 Hi0. exact (pjf_ew_sav regsc xs (33 + i0) i0 eq_refl Hi0).
    - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
    - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
  assert (HRBc : rd_blocks_ok tfibsegs B lyc Sc Wc (ms_mem ms) Rem)
    by exact (rd_blocks_ok_below B lyc Sc Wc _ mdc memc (ms_mem ms) Rem HARc SB HRB).
  assert (HROm : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) (ms_mem ms)))
    by exact (arodata_below B Wc memc (ms_mem ms) SB HRO).
  assert (Hglobm : fs_glob tfibsegs Wc (ms_mem ms) (live - rd_sum Dfr) peak cnt fail)
    by exact (fs_glob_below Wc memc (ms_mem ms) _ peak cnt fail SB Hglob).
  assert (Hra1 : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
    by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
  assert (Hgpc : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)).
  { rewrite P3, H3. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 HPRE)))))). }
  assert (Htpc : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)).
  { rewrite P4, H4. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HPRE))))))). }
  assert (Ef : STK_fuzz_free = ltac:(let v := eval vm_compute in (STK_fuzz_free) in exact v)) by (vm_compute; reflexivity).
  assert (HPREc : fpreU tfibsegs B STK_fuzz_free lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) mdC []).
  { apply (fsw_fpreU_atFP B STK sp0 FP ly S0 Uc W (unpoison U mem) md [] lyc Sc Wc (ms_mem ms) _ (EV_pj_free Dfr)
      (ms_regs ms) STK_fuzz_free (-128) [] HJ HARU HROm HspC ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Hra1
      ltac:(unfold raZ; rewrite R1, unsigned_lit_small by lia; lia) Hgpc Htpc).
    apply achain_low. unfold s0Z. rewrite P8, H8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  + (* fuzz_free (NULL): no event, no block *)
    assert (EDky : Dky = []).
    { destruct Hxc as [(_ & E) | (kx & Hin & _)]; [exact E|]. exfalso. rewrite Hx0 in Hin.
      destruct (fsw_rblock_low B ly S0 W _ md mem 0 kx pjf_HAR0 (HBK 0 kx Hin)). unfold HEAD in *. lia. }
    subst Dky.
    eapply SRr_bind.
    { exact (fs_fuzz_free_spec lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) mdC [] x 0 (live - rd_sum Dfr) peak cnt fail
        R10 Hglobm HHD (or_introl (conj Hx0 HPREc)) (fun H => False_ind _ (H Hx0))). }
    intros W4 c4 Hwle4 [(_ & Hpost) | (Hxn & _)]; [|congruence].
    unfold apost_baseU, fpostU in Hpost. cbv beta in Hpost.
    destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJc & OK4 & PO4 & HP4 & Eab & HH4 & Hglob4).
    subst c4. rewrite R1.
    apply (pjf_key_resume i Dfr [] Rest' lyc Sc Uc Wc memc mdc (ms_regs ms) (ms_mem ms) mdC [] 0 ly4 S4 Uc W4 regs4 mem4
      md4 Q Hi HINV SB HJ HARU Hfrm1 HLc HJc OK4 PO4 HP4).
    * reflexivity.
    * cbn [rd_hblocks map app]. rewrite Eab. reflexivity.
    * cbn [rd_heads map]. symmetry. apply pjf_udrop_nil.
    * exact HH4.
    * cbn [rd_sum fold_right]. rewrite Z.sub_0_r. exact Hglob4.
    * intros a (r & Hr & _). destruct Hr.
    * exact K.
  + (* fuzz_free (keys[i]) frees its string block *)
    destruct Hxc as [(E0 & _) | (kx & HxD & EDky)]; [congruence|]. subst Dky.
    assert (HxR : In (x, kx) Rem) by (subst Rem; rewrite !in_app_iff; cbn [In]; tauto).
    pose proof (HRBc x kx HxR) as Hxblk. pose proof (HposR x kx HxR) as Hkx0.
    assert (HNDR : List.NoDup (Dfr ++ Rem))
      by (apply (Permutation_NoDup HPD); first [exact HND | apply NoDup_ListNoDup; exact HND]).
    assert (HhU : In (x - HEAD, HEAD) Uc).
    { rewrite HUc, pjf_udrop_eq. apply List.filter_In. split.
      - apply HUI. unfold rd_heads. apply in_map_iff. exists (x, kx). split; [reflexivity | exact HxD].
      - destruct (hd_in (rd_heads Dfr) (x - HEAD, HEAD)) eqn:E; [|reflexivity]. exfalso.
        apply pjf_hd_in_iff in E. unfold rd_heads in E. apply in_map_iff in E as ([a2 k2] & Ea2 & Hin2).
        cbn [fst] in Ea2. injection Ea2 as Ea2'. assert (a2 = x) by lia. subst a2.
        assert (k2 = kx).
        { apply (pjf_D_uniq x); [|exact HxD].
          apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. left. exact Hin2. }
        subst k2. exact (pjf_nodup_disj Dfr Rem (x, kx) HNDR Hin2 HxR). }
    destruct (in_split _ _ HhU) as (U1 & U2 & EU).
    assert (HsumR : rd_sum Rem = rd_sum Ds + rd_sum Dk + rd_sum Dy + kx + rd_sum Rest')
      by (subst Rem; rewrite !pjf_rd_sum_app; cbn [rd_sum fold_right snd]; lia).
    assert (Hnng : forall L, (forall b, In b L -> In b Rem) -> 0 <= rd_sum L)
      by (intros L HLl; apply pjf_rd_sum_nonneg; intros a1 k1 H; exact (HposR a1 k1 (HLl _ H))).
    assert (Hsum1 : kx <= live - rd_sum Dfr).
    { rewrite (pjf_rd_sum_perm _ _ HPD), pjf_rd_sum_app, HsumR in HSUM.
      pose proof (Hnng Ds ltac:(intros b Hb0; subst Rem; rewrite !in_app_iff; tauto)) as N1.
      pose proof (Hnng Dk ltac:(intros b Hb0; subst Rem; rewrite !in_app_iff; tauto)) as N2.
      pose proof (Hnng Dy ltac:(intros b Hb0; subst Rem; rewrite !in_app_iff; tauto)) as N3.
      pose proof (Hnng Rest' ltac:(intros b Hb0; subst Rem; rewrite !in_app_iff; tauto)) as N4. lia. }
    pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
    assert (Hev1 : st_nev Sc + 1 <= EV_MAX).
    { rewrite (pjf_EV_perm _ _ HPD), pjf_EV_app in HEV. subst Rem. rewrite !pjf_EV_app in HEV.
      pose proof (pjf_EV_nonneg Ds). pose proof (pjf_EV_nonneg Dk). pose proof (pjf_EV_nonneg Dy).
      pose proof (pjf_EV_nonneg Rest'). unfold EV_pj_free at 5 in HEV. unfold EV_fuzz_free in *. cbn [length] in HEV. lia. }
    eapply SRr_bind.
    { exact (fs_fuzz_free_spec lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) mdC [] x kx (live - rd_sum Dfr) peak cnt fail
        R10 Hglobm HHD (or_intror (conj Hx0 (ex_intro _ U1 (ex_intro _ U2 (conj EU (conj HPREc (conj Hxblk Hsum1)))))))
        (fun _ => Hev1)). }
    intros W4 c4 Hwle4 [(Hxz & _) | (_ & U1' & U2' & EU' & Hpost)]; [congruence|].
    unfold apost_baseU, fpostU in Hpost. cbv beta in Hpost.
    destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJc & OK4 & PO4 & HP4 & (l1 & l2 & Eab1 & Eab2) & HH4 &
      Hglob4).
    subst c4. rewrite R1.
    assert (EU4 : U1' ++ U2' = udrop Uc (rd_heads [(x, kx)])).
    { cbn [rd_heads map fst]. rewrite EU'. symmetry. apply pjf_udrop_one.
      apply (pjf_head_once B lyc Sc U1' (x - HEAD, HEAD) U2'); [rewrite <- EU'; exact (proj1 (proj2 HARU)) | cbn; unfold HEAD; lia]. }
    apply (pjf_key_resume i Dfr [(x, kx)] Rest' lyc Sc Uc Wc memc mdc (ms_regs ms) (ms_mem ms) mdC
      (FS_PSTAT_FP ++ ablocks_fp [(x - HEAD, kx + HEAD)]) 1 ly4 S4 (U1' ++ U2') W4 regs4 mem4 md4 Q Hi HINV SB HJ HARU
      Hfrm1 HLc HJc OK4 PO4 HP4).
    * unfold EV_pj_free, EV_fuzz_free. cbn [length]. lia.
    * rewrite Eab1, Eab2. cbn [rd_hblocks map fst snd app]. symmetry. apply Permutation_middle.
    * exact EU4.
    * exact HH4.
    * cbn [rd_sum fold_right snd]. rewrite Z.add_0_r. exact Hglob4.
    * intros a Ha. apply pjf_inFP_app in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha | right].
      apply pjf_inFP_ablocks in Ha. destruct Ha as (p & n0 & Hin & Hr). destruct Hin as [E|[]].
      injection E as <- <-. exists x, kx. split; [left; reflexivity|].
      rewrite pjf_req in Hr by (unfold HEAD; lia). unfold HEAD in *. lia.
    * exact K.
Qed.


(* the loop tail 0x837a4: the resumed state ss_T c, the taken side c of `bltu s10, n` (0x837bc) assumed *)
Lemma pjf_tl_st : forall c lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc i,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc -> pjf_frm Wc memc ->
  (forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 40) 8 n -> 0 <= n < 2 ^ 64 ->
  acond_ok (pjf_env regsc [w64 n]) (mkAC c (SOff 26 1) (SOff 46 0)) ->
  st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T c)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837a4) memc (YK11.seg_rom tfibsegs))).
Proof.
intros c lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64 Hcond.
pose proof HL as HL0.
destruct HL0 as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) HPOc) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct HPOc as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
assert (HAPP : app_addr (v + 40)) by exact (proj2 (proj2 (proj2 (HPL (v + 40) ltac:(lia))))).
destruct (pjf_shadow_apart (v + 40) HAPP) as (HS1 & HS2).
pose proof (pjf_disj_img v 40 48 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_got_img) as HdG.
pose proof (pjf_disj_img v 40 48 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_cell_img) as HdC.
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 n]) 2) = sp0 - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E18 : bv_unsigned (ew (pjf_env regsc [w64 n]) 18) = v + 40)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl), H18; unfold w64; apply wz; lia).
assert (E22 : bv_unsigned (ew (pjf_env regsc [w64 n]) 22) = shadow_of_addr SHADOW_OFF (v + 40))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl), H22; unfold w64; apply wz;
      unfold shadow_of_addr, SHADOW_OFF in *; lia).
assert (E8 : ew (pjf_env regsc [w64 n]) 8 = Z_to_bv 64 v) by exact (eq_trans (ew_Ereg_nat regsc _ 8 8%bv eq_refl) H8).
assert (E19 : ew (pjf_env regsc [w64 n]) 19 = Z_to_bv 64 (v + 24))
  by exact (eq_trans (ew_Ereg_nat regsc _ 19 19%bv eq_refl) H19).
assert (E46 : ew (pjf_env regsc [w64 n]) 46 = Z_to_bv 64 n) by (rewrite (pjf_ew_x regsc [w64 n] 46 0 eq_refl); reflexivity).
apply (pjf_reseatC lyc Sc Uc Wc regsc memc mdc 0x837a4 [shr 22; fld 18 0 46] [] [mkAC c (SOff 26 1) (SOff 46 0)]
  [] [w64 n] HARU (proj1 HL) Hpres Hfrm ltac:(vm_compute; reflexivity)).
- constructor; [|constructor; [|constructor]].
  + apply (pjf_shr_ok regsc [w64 n] 22%bv 22 Wc memc (v + 40));
      [reflexivity | exact H22 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
    intros y Hy. apply HRA. lia.
  + apply (pjf_fld_ok regsc [w64 n] 18%bv 18 0 46 Wc memc (v + 40) n);
      [reflexivity | exact H18 | lia | lia | lia | rewrite fsw_SOff0, E46; reflexivity | exact Hn64
       | rewrite Z.add_0_r; exact Vn].
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E18, E22.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- exact I.
- exact I.
- cbn [conds_ok]. split; [exact Hcond | exact I].
Qed.

(* ---- 0x837a4 .. 0x837bc: the v + 40 shadow check (s6), n reloaded, i + 1, and `bltu s10, n` back to the head
   0x8371c (i + 1 < n) or out to the exit 0x837c0 (i + 1 = n) ---- *)
Lemma pjf_seg_tl : forall i Dfr Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (i < Z.to_nat n)%nat -> (forall b, In b Rest' -> In b D) ->
  pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  ((S i < Z.to_nat n)%nat -> forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs (S i) regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x8371c) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  (S i = Z.to_nat n -> forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_regs regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x837c0) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x837a4) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Rest' lyc Sc Uc Wc regsc memc mdc Q Hi HRD HINV HL Kb Ke.
pose proof HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23) & H20 & H27 & H21 & H24 & H25 & H26).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
assert (Vn : val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 40) 8 n).
{ intros j0 Hj0. unfold mbyte. rewrite (HKEEP (Z_to_bv 64 (v + 40 + Z.of_nat j0))).
  - exact (fsw_pj_u64_val tfibsegs _ _ _ Hnn j0 Hj0).
  - rewrite wz by lia. unfold pjf_FPS. left. lia. }
destruct Hnn as (Hn64 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (Hpres : forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
assert (HFl : forall x, pjf_FPS (S i) (S i) Rest' x -> 0 <= x < alloc_ceiling)
  by (intros x Hx; exact (pjf_FPS_low (S i) (S i) Rest' x HRD Hx)).
assert (E26 : ew (pjf_env regsc [w64 n]) 26 = Z_to_bv 64 (Z.of_nat i))
  by exact (eq_trans (ew_Ereg_nat regsc _ 26 26%bv eq_refl) H26).
assert (E46 : ew (pjf_env regsc [w64 n]) 46 = Z_to_bv 64 n) by (rewrite (pjf_ew_x regsc [w64 n] 46 0 eq_refl); reflexivity).
assert (Hin64 : 0 <= Z.of_nat i + 1 < 2 ^ 64) by lia.
assert (Hnb : 56 * n <= alloc_ceiling).
{ destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & _)]; [lia|].
  destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 pjf_HAR0 (HBK kids k0 Hk0D)). unfold HEAD in *. lia. }
assert (E2' : bv_unsigned (ew (pjf_env regsc [w64 n]) 2) = sp0 + (-128))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
destruct (Nat.lt_ge_cases (S i) (Z.to_nat n)) as [Hlt | Hge].
- (* ---- the back edge ---- *)
  assert (HS : st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T BC_LTU)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837a4) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_tl_st BC_LTU lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64).
    unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot]. rewrite E26, E46.
    unfold bv_ltu. rewrite (wz (Z.of_nat i)), (wz n) by lia. rewrite Z.add_0_r.
    rewrite (wz (Z.of_nat i + 1)), (wz n) by lia. apply Z.ltb_lt. lia. }
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x8371c.
  { cbn [ss_mem ss_T pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc [w64 n]) (ss_mem (ss_T BC_LTU)) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 n]) pjf_cs [shr 22; fld 18 0 46] a (sp0 - 128)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
      ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
    unfold sp0, STK in *. lia. }
  assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regsc 2)
    by exact (fsw_reg_atom _ _ _ _ ms 2%bv 2%bv 2 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regsc 3)
    by exact (fsw_reg_atom _ _ _ _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regsc 4)
    by exact (fsw_reg_atom _ _ _ _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regsc 8)
    by exact (fsw_reg_atom _ _ _ _ ms 8%bv 8%bv 8 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regsc 9)
    by exact (fsw_reg_atom _ _ _ _ ms 9%bv 9%bv 9 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P18 : YK11.getr (ms_regs ms) 18 = YK11.getr regsc 18)
    by exact (fsw_reg_atom _ _ _ _ ms 18%bv 18%bv 18 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P19 : YK11.getr (ms_regs ms) 19 = YK11.getr regsc 19)
    by exact (fsw_reg_atom _ _ _ _ ms 19%bv 19%bv 19 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P20 : YK11.getr (ms_regs ms) 20 = YK11.getr regsc 20)
    by exact (fsw_reg_atom _ _ _ _ ms 20%bv 20%bv 20 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P21 : YK11.getr (ms_regs ms) 21 = YK11.getr regsc 21)
    by exact (fsw_reg_atom _ _ _ _ ms 21%bv 21%bv 21 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P22 : YK11.getr (ms_regs ms) 22 = YK11.getr regsc 22)
    by exact (fsw_reg_atom _ _ _ _ ms 22%bv 22%bv 22 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P23 : YK11.getr (ms_regs ms) 23 = YK11.getr regsc 23)
    by exact (fsw_reg_atom _ _ _ _ ms 23%bv 23%bv 23 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (O24 : bv_unsigned (YK11.getr (ms_regs ms) 24) = 56 * Z.of_nat i + 56).
  { apply (fsw_reg_off _ _ _ ms 24%bv 24 56 (56 * Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 24 24%bv eq_refl), H24. unfold w64. apply wz. lia. }
  assert (O25 : bv_unsigned (YK11.getr (ms_regs ms) 25) = 8 * Z.of_nat i + 8).
  { apply (fsw_reg_off _ _ _ ms 25%bv 25 8 (8 * Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 25 25%bv eq_refl), H25. unfold w64. apply wz. lia. }
  assert (O26 : bv_unsigned (YK11.getr (ms_regs ms) 26) = Z.of_nat i + 1).
  { apply (fsw_reg_off _ _ _ ms 26%bv 26 1 (Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 26 26%bv eq_refl), H26. unfold w64. apply wz. lia. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  apply (Kb Hlt lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + apply (pjf_inv_below _ _ _ lyc Sc Uc Wc memc mdc _ _ HINV HJ HARU); [|exact SB | exact HFl].
    pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    refine (pjf_frm_of_region (pjf_env regsc [w64 n]) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
    * intros i0 Hi0. exact (pjf_ew_sav regsc [w64 n] (33 + i0) i0 eq_refl Hi0).
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia.
  + assert (HR' : pjf_regs (ms_regs ms))
      by (apply (pjf_regs_of regsc (ms_regs ms) (proj1 HL)); assumption).
    unfold pjf_lregs. split; [exact HR'|].
    rewrite P20, P27, P21.
    rewrite <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 24)), <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 25)),
      <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 26)), O24, O25, O26.
    unfold w64. rewrite !Nat2Z.inj_succ.
    split; [exact H20|]. split; [exact H27|]. split; [exact H21|].
    split; [f_equal; lia|]. split; [f_equal; lia | f_equal; lia].
- (* ---- the exit ---- *)
  assert (Heq : S i = Z.to_nat n) by lia.
  assert (HS : st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T BC_GEU)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837a4) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_tl_st BC_GEU lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64).
    unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot]. rewrite E26, E46.
    unfold bv_ltu. rewrite (wz (Z.of_nat i)), (wz n) by lia. rewrite Z.add_0_r.
    rewrite (wz (Z.of_nat i + 1)), (wz n) by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x837c0.
  { cbn [ss_mem ss_T pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc [w64 n]) (ss_mem (ss_T BC_GEU)) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 n]) pjf_cs [shr 22; fld 18 0 46] a (sp0 - 128)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
      ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
    unfold sp0, STK in *. lia. }
  assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regsc 2)
    by exact (fsw_reg_atom _ _ _ _ ms 2%bv 2%bv 2 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regsc 3)
    by exact (fsw_reg_atom _ _ _ _ ms 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regsc 4)
    by exact (fsw_reg_atom _ _ _ _ ms 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regsc 8)
    by exact (fsw_reg_atom _ _ _ _ ms 8%bv 8%bv 8 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regsc 9)
    by exact (fsw_reg_atom _ _ _ _ ms 9%bv 9%bv 9 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P18 : YK11.getr (ms_regs ms) 18 = YK11.getr regsc 18)
    by exact (fsw_reg_atom _ _ _ _ ms 18%bv 18%bv 18 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P19 : YK11.getr (ms_regs ms) 19 = YK11.getr regsc 19)
    by exact (fsw_reg_atom _ _ _ _ ms 19%bv 19%bv 19 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P20 : YK11.getr (ms_regs ms) 20 = YK11.getr regsc 20)
    by exact (fsw_reg_atom _ _ _ _ ms 20%bv 20%bv 20 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P21 : YK11.getr (ms_regs ms) 21 = YK11.getr regsc 21)
    by exact (fsw_reg_atom _ _ _ _ ms 21%bv 21%bv 21 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P22 : YK11.getr (ms_regs ms) 22 = YK11.getr regsc 22)
    by exact (fsw_reg_atom _ _ _ _ ms 22%bv 22%bv 22 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P23 : YK11.getr (ms_regs ms) 23 = YK11.getr regsc 23)
    by exact (fsw_reg_atom _ _ _ _ ms 23%bv 23%bv 23 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  apply (Ke Heq lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + apply (pjf_inv_below _ _ _ lyc Sc Uc Wc memc mdc _ _ HINV HJ HARU); [|exact SB | exact HFl].
    pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    refine (pjf_frm_of_region (pjf_env regsc [w64 n]) (mrestrict (w_H Wc) (ms_mem ms)) HR0 _ _ _ _).
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
    * intros i0 Hi0. exact (pjf_ew_sav regsc [w64 n] (33 + i0) i0 eq_refl Hi0).
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia.
  + apply (pjf_regs_of regsc (ms_regs ms) (proj1 HL)); assumption.
Qed.

(* ---- the loop: induction on the kids not yet visited; the exit goes to the tail at 0x837c0 ---- *)
Lemma pjf_loop : forall j i Dfr Rest lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  (k < 2)%nat -> (Z.to_nat n = i + S j)%nat ->
  pjf_inv (pjf_FPS i i Rest) Dfr (Ds ++ Dk ++ Dy ++ Rest) lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  PjStruct.pf_items tfibsegs m0 (fun a n0 => In (a, n0) D) (pjf_Pd tfibsegs m0 (fun a n0 => In (a, n0) D) (2 - k)) ks
    (kids + 56 * Z.of_nat i) (keys + 8 * Z.of_nat i) (S j) Rest ->
  (forall b, In b Rest -> In b D) ->
  (forall F Dfr' lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     (forall x, v <= x < v + 56 -> F x) ->
     pjf_inv F Dfr' (Ds ++ Dk ++ Dy) lyc' Sc' Uc' Wc' memc' mdc' -> pjf_regs regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x837c0) memc' (YK11.seg_rom tfibsegs)) mdc') GOAL) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8371c) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
induction j as [|j IH]; intros i Dfr Rest lyc Sc Uc Wc regsc memc mdc Hk2 Hn HINV HL HIT HRD TAIL;
  cbn [PjStruct.pf_items] in HIT; destruct HIT as (Dky & D1 & Rest' & -> & Hkey & (d' & Ed' & Hfd1) & HIT');
  (assert (Ed1 : d' = (1 - k)%nat) by lia); subst d';
  (assert (HRD' : forall b, In b Rest' -> In b D) by (intros b Hb; apply HRD; rewrite !in_app_iff; tauto));
  apply (pjf_seg_kid i Dfr Dky D1 Rest' lyc Sc Uc Wc regsc memc mdc GOAL Hk2 ltac:(lia) HINV HL Hfd1);
  intros lyc1 Sc1 Uc1 Wc1 regs1 mem1 md1 HINV1 HL1;
  apply (pjf_seg_key i (Dfr ++ D1) Dky Rest' lyc1 Sc1 Uc1 Wc1 regs1 mem1 md1 GOAL ltac:(lia) HINV1 HL1 Hkey);
  intros lyc2 Sc2 Uc2 Wc2 regs2 mem2 md2 HINV2 HL2;
  apply (pjf_seg_tl i ((Dfr ++ D1) ++ Dky) Rest' lyc2 Sc2 Uc2 Wc2 regs2 mem2 md2 GOAL ltac:(lia) HRD' HINV2 HL2).
- intros Hlt. lia.
- intros Heq lyc3 Sc3 Uc3 Wc3 regs3 mem3 md3 HINV3 HR3. cbn [PjStruct.pf_items] in HIT'. subst Rest'.
  rewrite app_nil_r in HINV3.
  exact (TAIL _ _ lyc3 Sc3 Uc3 Wc3 regs3 mem3 md3 (fun x Hx => or_introl Hx) HINV3 HR3).
- intros Hlt lyc3 Sc3 Uc3 Wc3 regs3 mem3 md3 HINV3 HL3.
  apply (IH (S i) ((Dfr ++ D1) ++ Dky) Rest' lyc3 Sc3 Uc3 Wc3 regs3 mem3 md3 Hk2 ltac:(lia) HINV3 HL3); [|exact HRD' | exact TAIL].
  replace (kids + 56 * Z.of_nat (S i)) with (kids + 56 * Z.of_nat i + 56) by lia.
  replace (keys + 8 * Z.of_nat (S i)) with (keys + 8 * Z.of_nat i + 8) by lia.
  exact HIT'.
- intros Heq. lia.
Qed.


(* ================= the entry ================= *)
(* the frame the prologue wrote: the thirteen saved registers and the two spilled shadow words *)
Lemma pjf_entry_frm : forall xs (Wc : world tfibsegs) memc,
  YP09.region_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) (mrestrict (w_H Wc) memc) pjf_ent_frame ->
  pjf_frm Wc memc.
Proof.
intros xs Wc memc HR.
pose proof pjf_entry_facts as (_ & _ & _ & Hv0 & Hv1 & _). pose proof asan_consts as (C1 & _).
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 2) = sp0)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10u : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 10) = v)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply wz; lia).
assert (Dsp : forall c, 0 <= v + c < 2 ^ 64 ->
  sv_denot (Ereg regs (fs_extraT ++ xs)) (SAlu ALU_SRL (SOff 10 c) (SLit 3)) = Z_to_bv 64 ((v + c) / 8)).
{ intros c Hc. rewrite denot_lit_U, U_srl3. f_equal. f_equal.
  rewrite U_SOff, E10u. apply zcanon_id. unfold M64. lia. }
assert (SAV : forall j nn (r : bv 5) off, (j < 13)%nat -> Z.of_nat nn = bv_unsigned r ->
  nth j (pjf_saved regs) (Z_to_bv 64 0) = YK11.getr regs r -> off = - 8 - 8 * Z.of_nat j ->
  In (YP09.mkChunk off (CVal 8 (SOff nn 0))) (YP09.r_chunks pjf_ent_frame) ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (sp0 - 8 - 8 * Z.of_nat j) 8
    (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))).
{ intros j nn r off Hj Hnn Hnth -> Hin.
  replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
  apply (fsw_field (Ereg regs (fs_extraT ++ xs)) _ 2 sp0 (YP09.r_chunks pjf_ent_frame) (-128) 0 (-128) 0
    (- 8 - 8 * Z.of_nat j) 8%N (SOff nn 0)); [exact HR | exact E2 | exact Hin | | apply u64_range | cbn; lia].
  rewrite Hnth, fsw_SOff0, (ew_Ereg_nat regs _ nn r Hnn), <- Hnth. symmetry. apply Z_to_bv_bv_unsigned. }
split; [|split].
- intros j Hj.
  assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10
                \/ j = 11 \/ j = 12)%nat) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]].
  + exact (SAV 0%nat 1%nat 1%bv (-8) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 1%nat 8%nat 8%bv (-16) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 2%nat 9%nat 9%bv (-24) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 3%nat 18%nat 18%bv (-32) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 4%nat 19%nat 19%bv (-40) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 5%nat 20%nat 20%bv (-48) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 6%nat 21%nat 21%bv (-56) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 7%nat 22%nat 22%bv (-64) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 8%nat 23%nat 23%bv (-72) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 9%nat 24%nat 24%bv (-80) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 10%nat 25%nat 25%bv (-88) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 11%nat 26%nat 26%bv (-96) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
  + exact (SAV 12%nat 27%nat 27%bv (-104) ltac:(lia) eq_refl eq_refl eq_refl ltac:(cbn; tauto)).
- replace (sp0 - 120) with (sp0 + (-120)) by lia.
  apply (fsw_field (Ereg regs (fs_extraT ++ xs)) _ 2 sp0 (YP09.r_chunks pjf_ent_frame) (-128) 0 (-128) 0
    (-120) 8%N (SAlu ALU_SRL (SOff 10 24) (SLit 3)) ((v + 24) / 8));
    [exact HR | exact E2 | cbn; tauto | exact (Dsp 24 ltac:(lia))
     | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia].
- replace (sp0 - 112) with (sp0 + (-112)) by lia.
  apply (fsw_field (Ereg regs (fs_extraT ++ xs)) _ 2 sp0 (YP09.r_chunks pjf_ent_frame) (-128) 0 (-128) 0
    (-112) 8%N (SAlu ALU_SRL (SOff 10 32) (SLit 3)) ((v + 32) / 8));
    [exact HR | exact E2 | cbn; tauto | exact (Dsp 32 ltac:(lia))
     | cbn [Z.of_N]; Z.div_mod_to_equations; lia | cbn; lia].
Qed.

(* the shadow register the entry run computes from v + c *)
Lemma pjf_sh_reg : forall xs c, 0 <= v + c -> v + c < 2 ^ 64 ->
  sv_denot (Ereg regs (fs_extraT ++ xs)) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 c) (SLit 3)) (SOff 32 0))
  = w64 (shadow_of_addr SHADOW_OFF (v + c)).
Proof.
intros xs c Hc0 Hc1. pose proof asan_consts as (C1 & _).
assert (E10 : ew (Ereg regs (fs_extraT ++ xs)) 10 = Z_to_bv 64 v)
  by exact (eq_trans (ew_Ereg_nat regs _ 10 10%bv eq_refl) H10).
assert (U10 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 10) = v) by (rewrite E10; apply wz;
  pose proof pjf_entry_facts as (_ & _ & _ & Hv0 & Hv1 & _); lia).
assert (G32 : ew (Ereg regs (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
apply bv_eq. change (bv_unsigned (sv_denot ?E ?s)) with (YP0e.U E s).
rewrite pjf_U_shaddr.
- rewrite !U_SOff, U10, G32, (wz SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF in *; lia). unfold w64. rewrite wz.
  + unfold shadow_of_addr. lia.
  + unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
- rewrite !U_SOff, U10, G32, (wz SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF in *; lia). unfold SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
(* the state the entry run leaves (at the loop head or at the tail): the invariant with nothing freed *)
Lemma pjf_entry_post : forall xs ss ms md' Rest,
  st_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) ss (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] ly S0 W (unpoison U (ms_mem ms)) md' 0 ->
  ARU tfibsegs B ly S0 U W (ms_mem ms) md' ->
  same_below mem (ms_mem ms) alloc_ceiling ->
  nth_error (ss_mem ss) 0 = Some pjf_ent_frame ->
  sr_get (ss_regs ss) 2%bv = SOff 2 (-128) -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 8%bv = SOff 10 0 -> sr_get (ss_regs ss) 9%bv = SOff 10 32 ->
  sr_get (ss_regs ss) 18%bv = SOff 10 40 -> sr_get (ss_regs ss) 19%bv = SOff 10 24 ->
  sr_get (ss_regs ss) 22%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 32 0) ->
  sr_get (ss_regs ss) 23%bv = SOff 32 0 ->
  Permutation D (Ds ++ Dk ++ Dy ++ Rest) -> (forall b, In b Rest -> In b D) ->
  pjf_inv (pjf_FPS 0 0 Rest) [] (Ds ++ Dk ++ Dy ++ Rest) ly S0 U W (ms_mem ms) md' /\ pjf_regs (ms_regs ms).
Proof.
intros xs ss ms md' Rest HS HJ HARU SB HF0 R2 R3 R4 R8 R9 R18 R19 R22 R23 HPR HRD.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pjf_HAR0 as HAR0.
set (E := Ereg regs (fs_extraT ++ xs)) in *.
assert (G : forall r : bv 5, YK11.getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (subst E; exact (eq_trans (ew_Ereg_nat regs _ 10 10%bv eq_refl) H10)).
assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; apply wz; lia).
assert (W10 : forall c, 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff 10 c) = w64 (v + c)).
{ intros c Hc. cbn [sv_denot]. rewrite U10. reflexivity. }
split.
- split; [exact HJ|]. split; [exact HARU|]. split; [exact HHD0|].
  split.
  { apply (pjf_entry_frm xs W (ms_mem ms)).
    pose proof (fsw_region_nth _ _ _ 0 _ HS HF0) as HR0. cbn [ms_mem restrict] in HR0. exact HR0. }
  split; [cbn [rd_hblocks map app]; reflexivity|].
  split; [cbn [rd_heads map]; symmetry; apply pjf_udrop_nil|].
  split; [cbn [rd_sum fold_right]; rewrite Z.sub_0_r; exact (fs_glob_below W mem (ms_mem ms) _ peak cnt fail SB HG)|].
  split; [exact HPR|].
  split.
  { apply (rd_blocks_ok_below B ly S0 W _ md mem (ms_mem ms) _ HAR0 SB). intros a k0 Hin.
    apply HBK. apply (Permutation_in _ (Permutation_sym HPR)). exact Hin. }
  split; [exact (pobj_below B ly S0 W _ md mem (ms_mem ms) v HAR0 SB HPO)|].
  split; [|exact (arodata_below B W mem (ms_mem ms) SB (proj2 HPRE))].
  intros x Hx. pose proof (u64_range x) as Rx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  apply (fsw_mrestrict_belowZ (w_H W) mem (ms_mem ms) _ SB). exact (pjf_FPS_low 0 0 Rest _ HRD Hx).
- unfold pjf_regs, spZ. rewrite !G, R2, R3, R4, R8, R9, R18, R19, R22, R23.
  assert (G32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E2u : bv_unsigned (ew E 2) = sp0)
    by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  split; [cbn [sv_denot]; rewrite E2u, (wz (sp0 + -128)) by (unfold sp0, STK in *; lia); try lia|].
  split; [rewrite fsw_SOff0; subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)|].
  split; [rewrite fsw_SOff0; subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)|].
  split; [rewrite fsw_SOff0, E10; reflexivity|].
  split; [apply W10; lia|]. split; [apply W10; lia|]. split; [apply W10; lia|].
  split; [subst E; exact (pjf_sh_reg xs 40 ltac:(lia) ltac:(lia))|].
  rewrite fsw_SOff0, G32. reflexivity.
Qed.

(* ---- the entry 0x83674 .. the loop head 0x8371c (n >= 1) or the exit 0x837c0 (n = 0) ---- *)
Lemma pjf_entry :
  (forall F Dfr' lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     (forall x, v <= x < v + 56 -> F x) ->
     pjf_inv F Dfr' (Ds ++ Dk ++ Dy) lyc' Sc' Uc' Wc' memc' mdc' -> pjf_regs regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x837c0) memc' (YK11.seg_rom tfibsegs)) mdc') GOAL) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_free regs mem md) GOAL.
Proof.
intros TAIL.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & HSTK3 & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pjf_HAR0 as HAR0. pose proof HSS as [Hgot Hcell].
pose proof (proj1 HPRE) as HAPU.
pose proof HHDR as (Hrw & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
pose proof (proj1 Hstr) as Hstr64. pose proof (proj1 Hkids) as Hkids64.
pose proof (proj1 Hkeys) as Hkeys64. pose proof (proj1 Hnn) as Hn64.
destruct (pjf_place B ly S0 W (unpoison U mem) md mem v HAR0 HPO) as (HPL & HAMR & HHULL).
assert (HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56)
  by (destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
pose proof (pjf_disj_img v 0 56 tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_got_img) as HdG.
pose proof (pjf_disj_img v 0 56 tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HNI pjf_cell_img) as HdC.
assert (HJ0 : ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] ly S0 W (unpoison U mem) md 0)
  by exact (ajournal_init tfibsegs B STK FP ly S0 W regs (unpoison U mem) md ch (proj1 HAPU)).
assert (HARU0 : ARU tfibsegs B ly S0 U W mem md) by exact (fsw_ARU B STK ly S0 U W regs mem md ch HAPU).
set (xs := [w64 str; w64 kids; w64 keys; w64 n]).
assert (Ex : forall j w, nth j xs (Z_to_bv 64 0) = w -> ew (Ereg regs (fs_extraT ++ xs)) (33 + j) = w)
  by (intros j w <-; replace (33 + j)%nat with (32 + S j)%nat by lia; rewrite ew_Ereg_extra;
      cbn [fs_extraT app nth]; reflexivity).
assert (E33 : ew (Ereg regs (fs_extraT ++ xs)) 33 = Z_to_bv 64 str) by exact (Ex 0%nat _ eq_refl).
assert (E34 : ew (Ereg regs (fs_extraT ++ xs)) 34 = Z_to_bv 64 kids) by exact (Ex 1%nat _ eq_refl).
assert (E35 : ew (Ereg regs (fs_extraT ++ xs)) 35 = Z_to_bv 64 keys) by exact (Ex 2%nat _ eq_refl).
assert (E36 : ew (Ereg regs (fs_extraT ++ xs)) 36 = Z_to_bv 64 n) by exact (Ex 3%nat _ eq_refl).
assert (E10 : ew (Ereg regs (fs_extraT ++ xs)) 10 = Z_to_bv 64 v)
  by exact (eq_trans (ew_Ereg_nat regs _ 10 10%bv eq_refl) H10).
assert (U10 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 10) = v) by (rewrite E10; apply wz; lia).
assert (HSH : sh_ok tfibsegs fs_Bx pjf_SH0 (Ereg regs (fs_extraT ++ xs)) (mrestrict (w_H W) mem)).
{ constructor; [|constructor].
  apply (pjf_shent0 _ _ 10 v 0 56); [apply pjf_U_fsbx | unfold YP0e.U; rewrite fsw_SOff0; exact U10 | lia | |].
  - rewrite Z.add_0_r. exact HRA.
  - rewrite Z.add_0_r. destruct (HPL v ltac:(lia)) as (_ & _ & _ & Ha0).
    destruct (HPL (v + 55) ltac:(lia)) as (_ & _ & _ & Ha1).
    unfold app_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- (* ---- n = 0: straight to the tail ---- *)
  assert (EDi : Di = []) by (rewrite Hn0 in HITEMS; cbn in HITEMS; exact HITEMS).
  assert (HPR : Permutation D (Ds ++ Dk ++ Dy)) by (rewrite EDi, app_nil_r in HPERM; exact HPERM).
  assert (HS : st_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) pjf_ss0z
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_pj_free) mem (YK11.seg_rom tfibsegs)))).
  { apply (fsw_entryT_argsX B STK 128 ly S0 U W regs mem md ch A_pj_free [pjf_v0z]
      [(10%nat, mkAF 4096 PJF_CEIL 3)] xs Hgot Hcell HAPU ltac:(unfold STK in *; lia)
      ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor]. unfold pjf_v0z.
      apply (fsw_pj_part_okR tfibsegs _ _ 10%nat v v 16 48); [lia | lia | exact U10 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 16 (SOff 33 0) str); [exact Hstr | rewrite fsw_SOff0; exact E33].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff 34 0) kids); [exact Hkids | rewrite fsw_SOff0; exact E34].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff 35 0) keys); [exact Hkeys | rewrite fsw_SOff0; exact E35].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SLit 0) 0); [rewrite <- Hn0; exact Hnn | reflexivity].
    - apply (fsw_pj_parts_disjX regs (fs_extraT ++ xs) 128 v); [lia | unfold STK in *; lia | unfold STK in *; lia
        | lia | lia | | cbn [YP09.pairwise_disjoint YP09.all_disjoint]; tauto].
      repeat apply Forall_cons; try apply Forall_nil.
      unfold pj_in_obj, pjf_v0z. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10. lia.
    - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, (wz v) by lia.
      change (2 ^ 3) with 8. split; [split; [unfold PJF_CEIL; lia | split; [exact Hv8 | lia]] | exact I]. }
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ0 HARU0 HSH fs_Bspan 0x837c0.
  { cbn [ss_mem pjf_ss0z fss0T_args fsT_regions_args fsT_regions app].
    eapply awr_ok_cons_stack with (n := 2%nat);
      [reflexivity | rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity | cbn; unfold STK in *; lia
       | cbn; lia |]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  rename HS into HSc.
  assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (Ereg regs (fs_extraT ++ xs)) (ss_mem pjf_ss0z) mem (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a (r & Hin & Hr). cbn [ss_mem pjf_ss0z fss0T_args fsT_regions_args fsT_regions app] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [fstk fs_got_region fs_bcell_region pjf_v0z YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr; unfold STK, spZ in *; lia. }
  destruct (pjf_entry_post xs _ ms _ [] HSc HJ0 HARU0 SB eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(rewrite app_nil_r; exact HPR) ltac:(intros b []))
    as (HINV & HREGS).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl). cbn [ss_pc].
  rewrite app_nil_r in HINV.
  exact (TAIL _ [] ly S0 U W (ms_regs ms) (ms_mem ms) _ (fun x Hx => or_introl Hx) HINV HREGS).
- (* ---- n >= 1: the loop ---- *)
  assert (Hn1 : 1 <= n) by lia.
  assert (Hk2 : (k < 2)%nat).
  { destruct (Nat.lt_ge_cases k 2) as [Hlt | Hge]; [exact Hlt|exfalso].
    assert (Ek : (2 - k = 0)%nat) by lia. rewrite Ek in HITEMS.
    assert (Hpos : (0 < Z.to_nat n)%nat) by lia.
    destruct (Z.to_nat n) as [|m] eqn:Em; [lia|].
    cbn [PjStruct.pf_items] in HITEMS. destruct HITEMS as (Dk1 & D1 & D2 & _ & _ & (d' & Ed' & _) & _). lia. }
  assert (HS : st_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) pjf_ss0n
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_pj_free) mem (YK11.seg_rom tfibsegs)))).
  { apply (fsw_entryT_argsX B STK 128 ly S0 U W regs mem md ch A_pj_free [pjf_v0]
      [(10%nat, mkAF 4096 PJF_CEIL 3); (36%nat, mkAF 1 (2 ^ 54) 0)] xs Hgot Hcell HAPU
      ltac:(unfold STK in *; lia) ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor]. unfold pjf_v0.
      apply (fsw_pj_part_okR tfibsegs _ _ 10%nat v v 16 48); [lia | lia | exact U10 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 16 (SOff 33 0) str); [exact Hstr | rewrite fsw_SOff0; exact E33].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff 34 0) kids); [exact Hkids | rewrite fsw_SOff0; exact E34].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff 35 0) keys); [exact Hkeys | rewrite fsw_SOff0; exact E35].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SOff 36 0) n); [exact Hnn | rewrite fsw_SOff0; exact E36].
    - apply (fsw_pj_parts_disjX regs (fs_extraT ++ xs) 128 v); [lia | unfold STK in *; lia | unfold STK in *; lia
        | lia | lia | | cbn [YP09.pairwise_disjoint YP09.all_disjoint]; tauto].
      repeat apply Forall_cons; try apply Forall_nil.
      unfold pj_in_obj, pjf_v0. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10. lia.
    - assert (Hnb : n <= 2 ^ 54).
      { destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & _)]; [lia|].
        destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 HAR0 (HBK kids k0 Hk0D)). unfold HEAD in *. lia. }
      cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, E36, (wz v), (wz n) by lia.
      change (2 ^ 3) with 8. rewrite Z.pow_0_r.
      split; [split; [unfold PJF_CEIL; lia | split; [exact Hv8 | lia]]|].
      split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I]. }
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ0 HARU0 HSH fs_Bspan 0x8371c.
  { cbn [ss_mem pjf_ss0n fss0T_args fsT_regions_args fsT_regions app].
    eapply awr_ok_cons_stack with (n := 2%nat);
      [reflexivity | rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity | cbn; unfold STK in *; lia
       | cbn; lia |]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  rename HS into HSc.
  assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (Ereg regs (fs_extraT ++ xs)) (ss_mem pjf_ss0n) mem (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a (r & Hin & Hr). cbn [ss_mem pjf_ss0n fss0T_args fsT_regions_args fsT_regions app] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [fstk fs_got_region fs_bcell_region pjf_v0 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?(ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr; unfold STK, spZ in *; lia. }
  assert (HDiD : forall b, In b Di -> In b D)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); rewrite !in_app_iff; tauto).
  destruct (pjf_entry_post xs _ ms _ Di HSc HJ0 HARU0 SB eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    HPERM HDiD) as (HINV & HREGS).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl). cbn [ss_pc].
  assert (HL0 : pjf_lregs 0 (ms_regs ms)).
  { assert (G : forall r : bv 5, YK11.getr (ms_regs ms) r = sv_denot (Ereg regs (fs_extraT ++ xs)) (sr_get (ss_regs _) r))
      by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) _ _ ms r HSc)).
    unfold pjf_lregs. split; [exact HREGS|].
    split; [rewrite (G 20%bv); exact (pjf_sh_reg xs 32 ltac:(lia) ltac:(lia))|].
    split; [rewrite (G 27%bv); exact (pjf_sh_reg xs 24 ltac:(lia) ltac:(lia))|].
    split; [rewrite (G 21%bv); reflexivity|].
    split; [rewrite (G 24%bv); reflexivity|].
    split; [rewrite (G 25%bv); reflexivity | rewrite (G 26%bv); reflexivity]. }
  apply (pjf_loop (Z.to_nat n - 1) 0 [] Di ly S0 U W (ms_regs ms) (ms_mem ms) _ Hk2 ltac:(lia) HINV HL0).
  + replace (S (Z.to_nat n - 1)) with (Z.to_nat n) by lia.
    replace (kids + 56 * Z.of_nat 0) with kids by (cbn [Z.of_nat]; lia).
    replace (keys + 8 * Z.of_nat 0) with keys by (cbn [Z.of_nat]; lia).
    exact HITEMS.
  + exact HDiD.
  + exact TAIL.
Qed.

(* the tail reads only v's 56 bytes of the entry memory *)
Let Fv : Z -> Prop := fun x => v <= x < v + 56.
Let TINV (Dfr Rem : list (Z * Z)) lyc Sc Uc (Wc : world tfibsegs) memc mdc : Prop :=
  pjf_inv Fv Dfr Rem lyc Sc Uc Wc memc mdc.

(* ---- D is a function of the block address (the entry blocks are pairwise disjoint) ---- *)
Lemma pjt_D_fun : forall a k1 k2, In (a, k1) D -> In (a, k2) D -> k1 = k2.
Proof.
intros a k1 k2 H1 H2.
pose proof (proj1 (proj1 HPRE)) as HAPf. destruct HAPf as (HARe & _).
destruct (HBK a k1 H1) as (Hin1 & _ & Hn1 & _).
destruct (HBK a k2 H2) as (Hin2 & _ & Hn2 & _).
destruct (Z.eq_dec k1 k2) as [E|NE]; [exact E|exfalso].
apply (pjt_blocks_disj B ly S0 W (unpoison U mem) md (a - HEAD) (k1 + HEAD) (a - HEAD) (k2 + HEAD) (a - HEAD)
  HARe Hin1 Hin2 (pjt_rq_ne (a - HEAD) (k1 + HEAD) (a - HEAD) (k2 + HEAD) ltac:(cbv [HEAD]; lia)
    ltac:(intros (_ & Eq); apply NE; cbv [HEAD] in Eq; lia))).
assert (R1 : req_size (k1 + HEAD) = k1 + HEAD) by (unfold req_size; destruct (Z.eqb_spec (k1 + HEAD) 0); cbv [HEAD] in *; lia).
assert (R2 : req_size (k2 + HEAD) = k2 + HEAD) by (unfold req_size; destruct (Z.eqb_spec (k2 + HEAD) 0); cbv [HEAD] in *; lia).
rewrite R1, R2. cbv [HEAD]. lia.
Qed.
(* no block already freed shares its head with a block still to free *)
Lemma pjt_head_fresh : forall Dfr Rem p kk, Permutation D (Dfr ++ Rem) -> In (p, kk) Rem ->
  hd_in (rd_heads Dfr) (p - HEAD, HEAD) = false.
Proof.
intros Dfr Rem p kk HP Hin.
destruct (hd_in (rd_heads Dfr) (p - HEAD, HEAD)) eqn:E; [exfalso|reflexivity].
apply pjf_hd_in_iff in E. unfold rd_heads in E. apply in_map_iff in E as (b & Eb & Hb).
destruct b as (q, m). cbn [fst] in Eb. injection Eb as Eb1.
assert (Hqp : q = p) by lia. subst q.
assert (HinD1 : In (p, m) D) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb).
assert (HinD2 : In (p, kk) D) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
pose proof (pjt_D_fun p m kk HinD1 HinD2) as Em. subst m.
assert (HNDl : List.NoDup D) by (apply NoDup_ListNoDup; exact HND).
exact (pjf_nodup_disj Dfr Rem (p, kk) (Permutation_NoDup HP HNDl) Hb Hin).
Qed.

(* ---- the resumed states' disjointness goal, with no extra region and with one field region ---- *)
Lemma pjt_pd0 : forall E, bv_unsigned (ew E 2) = sp0 - 128 ->
  pairwise_disjoint E (fsT_ret_regions 128 pjf_cs []).
Proof.
intros E E2.
pose proof pjf_entry_facts as (_ & Hceil & _).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold STK, sp0 in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma pjt_pd1 : forall E nn b o lo, bv_unsigned (ew E 2) = sp0 - 128 -> bv_unsigned (ew E nn) = b -> b + o = v + lo ->
  0 <= lo -> lo + 8 <= 56 ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) ->
  pairwise_disjoint E (fsT_ret_regions 128 pjf_cs [fld nn o 46]).
Proof.
intros E nn b o lo E2 En Ebo Hlo Hhi HNI.
pose proof pjf_entry_facts as (_ & Hceil & _ & Hv0 & Hv1 & _).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
pose proof (pjf_disj_img v lo (lo + 8) tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) HNI pjf_got_img) as HdG.
pose proof (pjf_disj_img v lo (lo + 8) tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) HNI pjf_cell_img) as HdC.
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, fld, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, En.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold STK, sp0 in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ================= one fuzz_free call: the journal, the data and the registers across it ================= *)
Lemma pjt_cross : forall (FP1 : list (Z * Z)) (kc : Z) (Dfr UL : list (Z * Z))
    lyc Sc Uc (Wc : world tfibsegs) regsC memC mdc ly' S' U' (Wr : world tfibsegs) regs' mem' md',
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memC) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdc ->
  pjf_frm Wc memC ->
  rd_blocks_ok tfibsegs B lyc Sc Wc memC UL ->
  pobj tfibsegs B lyc Sc Wc memC v ->
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wc) memC x = m0 x) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC) ->
  pjf_regs regsC ->
  ajournal tfibsegs B STK_fuzz_free (spZ regsC) FP1 lyc Sc Wc (unpoison Uc memC) mdc []
    ly' S' Wr (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs Wr mem' U' ->
  aregs_preserved regsC regs' ->
  FSupoisonU.fs_heads B ly' S' U' ->
  fsw_fp_sub B ly S0 lyc Sc [] FP FP1 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (forall a kb x, In (a, kb) UL -> a - HEAD <= x < a + kb -> ~ inFP FP1 x) ->
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] ly' S' Wr (unpoison U' mem') md'
    (EV_pj_free Dfr + kc) /\
  ARU tfibsegs B ly' S' U' Wr mem' md' /\
  pjf_frm Wr mem' /\
  rd_blocks_ok tfibsegs B ly' S' Wr mem' UL /\
  pobj tfibsegs B ly' S' Wr mem' v /\
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wr) mem' x = m0 x) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wr) mem') /\
  pjf_regs regs'.
Proof.
intros FP1 kc Dfr UL lyc Sc Uc Wc regsC memC mdc ly' S' U' Wr regs' mem' md'
  HJ HARU Hfrm HBKc Hpo HKEEP HRO HR HJc OK' PO' HP HH' HFsub HFv HFul HFsh HFcl HFro.
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof HSS as [Hgot Hcell].
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
assert (Hsp' : spZ regs' = sp0 - 128)
  by (unfold spZ in *; rewrite (fsw_pres regsC regs' 2%bv HP ltac:(pjf_cs_reg)); exact Hsp).
assert (E2' : bv_unsigned (ew (pjf_env regs' []) 2) = spZ regs - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); unfold spZ in Hsp'; unfold sp0 in Hsp'; exact Hsp').
assert (He' : forall j, (j < 13)%nat ->
  sv_denot (pjf_env regs' []) (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0))
  by (intros j Hj; exact (pjf_ew_sav regs' [] (33 + j) j eq_refl Hj)).
assert (E19' : bv_unsigned (ew (pjf_env regs' []) 19) = v + 24).
{ unfold pjf_env. rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl),
    (fsw_pres regsC regs' 19%bv HP ltac:(pjf_cs_reg)), H19. unfold w64. apply wz.
  pose proof pjf_entry_facts as (_ & _ & _ & Hv0' & Hv1' & _). pose proof asan_consts as (C1' & _). lia. }
assert (E9' : bv_unsigned (ew (pjf_env regs' []) 9) = v + 32).
{ unfold pjf_env. rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl),
    (fsw_pres regsC regs' 9%bv HP ltac:(pjf_cs_reg)), H9. unfold w64. apply wz.
  pose proof pjf_entry_facts as (_ & _ & _ & Hv0' & Hv1' & _). pose proof asan_consts as (C1' & _). lia. }
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc memC mdc (EV_pj_free Dfr)
   STK_fuzz_free FP1 128 regsC ly' S' U' Wr regs' mem' md' kc (pjf_saved regs ++ []) pjf_cs [] [] 0
   Hgot Hcell HJ HARU HJc HFsub OK' PO' HP Hsp ltac:(lia)
   ltac:(vm_compute; intros Hc; discriminate Hc) ltac:(unfold STK in *; lia) ltac:(reflexivity)
   ltac:(vm_compute; reflexivity) ltac:(unfold pjf_cs; repeat constructor; cbn; lia)
   ltac:(exact (pjf_cs_ok (pjf_env regs' []) (mrestrict (w_H Wc) memC) E2' He' E19' E9'
     (proj1 Hfrm) (proj1 (proj2 Hfrm)) (proj2 (proj2 Hfrm))))
   (Forall_nil _) ltac:(apply pjt_pd0; exact E2') I) as (HJ2 & HARU2 & HS2).
(* the frame's twelve saved words, read back from the resumed state's frame region *)
assert (Hfrm2 : pjf_frm Wr mem').
{ pose proof (fsw_region_nth _ _ _ 0 _ HS2 ltac:(reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
  exact (pjf_frm_of_region (pjf_env regs' []) (mrestrict (w_H Wr) mem') HR0 E2' He' E19' E9'). }
assert (HBK2 : rd_blocks_ok tfibsegs B ly' S' Wr mem' UL)
  by exact (rd_blocks_ok_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc UL
       HJc HARU OK' PO' HFul HBKc).
assert (Hpo2 : pobj tfibsegs B ly' S' Wr mem' v)
  by exact (pobj_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc v
       HJc HARU OK' PO' HFv HFsh HH' Hpo).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wr) mem'))
  by exact (arodata_kept B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc
       HJc HARU OK' PO' HFcl HFro HRO).
assert (KB : forall a, v <= a < v + 56 ->
  mrestrict (w_H Wr) mem' (Z_to_bv 64 a) = mrestrict (w_H Wc) memC (Z_to_bv 64 a)).
{ intros a Ha.
  refine (proj2 (fsw_journal_kept_byte B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc
    a HJc HARU OK' PO' _ (HFv a Ha))).
  destruct Hpo as [[((cid & pos & Hin & _ & _ & Hf1 & Hf2) & _)|((bb & nn & Hin & Hb1 & Hb2) & _)] _].
  - right. exists cid, pos. split; [exact Hin | lia].
  - left. exists bb, nn. split; [exact Hin | cbv [HEAD] in Hb1; lia]. }
assert (HKEEP2 : forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wr) mem' x = m0 x).
{ intros x Hx. pose proof (KB (bv_unsigned x) Hx) as E. rewrite Z_to_bv_bv_unsigned in E.
  rewrite E. exact (HKEEP x Hx). }
assert (HR2 : pjf_regs regs').
{ unfold pjf_regs. split; [unfold sp0 in Hsp'; exact Hsp'|].
  split; [rewrite (fsw_pres regsC regs' 3%bv HP ltac:(pjf_cs_reg)); exact H3|].
  split; [rewrite (fsw_pres regsC regs' 4%bv HP ltac:(pjf_cs_reg)); exact H4|].
  split; [rewrite (fsw_pres regsC regs' 8%bv HP ltac:(pjf_cs_reg)); exact H8|].
  split; [rewrite (fsw_pres regsC regs' 9%bv HP ltac:(pjf_cs_reg)); exact H9|].
  split; [rewrite (fsw_pres regsC regs' 18%bv HP ltac:(pjf_cs_reg)); exact H18|].
  split; [rewrite (fsw_pres regsC regs' 19%bv HP ltac:(pjf_cs_reg)); exact H19|].
  split; [rewrite (fsw_pres regsC regs' 22%bv HP ltac:(pjf_cs_reg)); exact H22|].
  rewrite (fsw_pres regsC regs' 23%bv HP ltac:(pjf_cs_reg)); exact H23. }
split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Hfrm2|]. split; [exact HBK2|].
split; [exact Hpo2|]. split; [exact HKEEP2|]. split; [exact HRO2 | exact HR2].
Qed.

(* ================= one exit call of fuzz_free, entry to resume ================= *)
Lemma pjt_call : forall (Dfr Dx Rem' : list (Z * Z)) (p pcr : Z)
    lyc Sc Uc (Wc : world tfibsegs) regsC memC mdc,
  ((Dx = [] /\ p = 0) \/ (exists kk, Dx = [(p, kk)])) ->
  TINV Dfr (Dx ++ Rem') lyc Sc Uc Wc memC mdc ->
  pjf_regs regsC ->
  YK11.getr regsC 1 = Z_to_bv 64 pcr ->
  YK11.getr regsC 10 = w64 p ->
  4096 <= pcr -> pcr < 2 ^ 64 -> pcr mod 2 = 0 ->
  (forall lyr Sr Ur (Wr : world tfibsegs) regsr memr mdr,
     TINV (Dfr ++ Dx) Rem' lyr Sr Ur Wr memr mdr -> pjf_regs regsr ->
     SRr tfibsegs Wr (mkCfg (YK11.mkst regsr (Z_to_bv 64 pcr) memr (YK11.seg_rom tfibsegs)) mdr) GOAL) ->
  SRr tfibsegs Wc (cfg_at tfibsegs A_fuzz_free regsC memC mdc) GOAL.
Proof.
intros Dfr Dx Rem' p pcr lyc Sc Uc Wc regsC memC mdc HDx HINV HR R1 R10 Hpc0 Hpc1 Hpc2 HK.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof (proj1 (proj1 HPRE)) as HAPf.
destruct HAPf as (HARe & _ & _ & Hgpe & Htpe & _).
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
assert (HPREc : fpreU tfibsegs B STK_fuzz_free lyc Sc Uc Wc regsC memC mdc []).
{ apply (fsw_fpreU_atFP B STK sp0 FP ly S0 Uc W (unpoison U mem) md [] lyc Sc Wc memC mdc (EV_pj_free Dfr)
    regsC STK_fuzz_free (-128) [] HJ HARU HRO).
  - unfold sp0 in *; lia.
  - reflexivity.
  - lia.
  - vm_compute; intros Hc; discriminate Hc.
  - unfold STK in *; lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hpc2.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite H3. exact Hgpe.
  - rewrite H4. exact Htpe.
  - apply achain_low. unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HBKr : rd_blocks_ok tfibsegs B lyc Sc Wc memC Rem')
  by (intros a kb Hin; apply HBKc; apply in_or_app; right; exact Hin).
destruct HDx as [(-> & ->) | (kk & ->)].
- (* the field is NULL: fuzz_free returns at once, no event, no block leaves *)
  cbn [app] in HPD, HBKc.
  eapply SRr_bind.
  { apply (fs_fuzz_free_spec lyc Sc Uc Wc regsC memC mdc [] 0 0 (live - rd_sum Dfr) peak cnt fail);
      [ exact R10 | exact Hglob | exact HH
      | left; split; [reflexivity | exact HPREc]
      | intros Hc; exfalso; exact (Hc eq_refl) ]. }
  intros Wr cr Hwle [(_ & Hpost) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  unfold apost_baseU, fpostU in Hpost.
  destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' & Eab & HH2 & HG2).
  subst cr. rewrite R1.
  destruct (pjt_cross [] 0 Dfr Rem' lyc Sc Uc Wc regsC memC mdc ly' S' Uc Wr regs' mem' md'
      HJ HARU Hfrm HBKr Hpo HKEEP HRO HR HJc OK' PO' HP' HH2
      ltac:(intros a Ha; destruct (pjt_inFP_nil a Ha))
      ltac:(intros a _ Ha; exact (pjt_inFP_nil a Ha))
      ltac:(intros a kb x _ _ Hf; exact (pjt_inFP_nil x Hf))
      ltac:(intros a Ha; destruct (pjt_inFP_nil a Ha))
      sink_closed_nil
      ltac:(intros a _ Hf; exact (pjt_inFP_nil a Hf)))
    as (HJ2 & HARU2 & Hfrm2 & HBK2 & Hpo2 & HKEEP2 & HRO2 & HR2).
  apply (HK ly' S' Uc Wr regs' mem' md'); [|exact HR2].
  unfold TINV, pjf_inv. rewrite app_nil_r.
  replace (EV_pj_free Dfr + 0) with (EV_pj_free Dfr) in HJ2 by lia.
  split; [exact HJ2|]. split; [exact HARU2|]. split; [exact HH2|]. split; [exact Hfrm2|].
  split; [rewrite Eab; exact HBP|]. split; [exact HUc|]. split; [exact HG2|].
  split; [exact HPD|]. split; [exact HBK2|]. split; [exact Hpo2|].
  split; [exact HKEEP2 | exact HRO2].
- (* the field is a live block: one event, the block and its head leave *)
  assert (HinRem : In (p, kk) ([(p, kk)] ++ Rem')) by (left; reflexivity).
  pose proof (HBKc p kk HinRem) as HRB.
  pose proof HRB as (Hinb & Hp16 & Hkk & Hvm).
  destruct (fsw_rblock_low B lyc Sc Wc (unpoison Uc memC) mdc memC p kk (proj1 HARU) HRB) as (Hp0 & Hp1).
  assert (Hpne : p <> 0) by (cbv [HEAD] in Hp0; lia).
  assert (HinD : In (p, kk) D)
    by (apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact HinRem).
  assert (HinU : In (p - HEAD, HEAD) U).
  { apply HUI. unfold rd_heads.
    change (p - HEAD, HEAD) with ((fun b : Z * Z => (fst b - HEAD, HEAD)) (p, kk)). apply in_map. exact HinD. }
  assert (HinUc : In (p - HEAD, HEAD) Uc).
  { rewrite HUc, pjf_udrop_eq. apply filter_In. split; [exact HinU|].
    rewrite (pjt_head_fresh Dfr ([(p, kk)] ++ Rem') p kk HPD HinRem). reflexivity. }
  destruct (in_split _ _ HinUc) as (U1 & U2 & EUc).
  assert (Hlive : kk <= live - rd_sum Dfr).
  { pose proof (pjf_rd_sum_perm D (Dfr ++ ([(p, kk)] ++ Rem')) HPD) as ES.
    rewrite !pjf_rd_sum_app, pjt_rd_sum_one in ES.
    assert (HR' : 0 <= rd_sum Rem')
      by (apply pjt_rd_sum_nonneg; intros a0 k0 Hin0;
          destruct (HBKr a0 k0 Hin0) as (_ & _ & Hk0 & _); lia).
    lia. }
  assert (HEVc : st_nev Sc + 1 <= EV_MAX).
  { pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
    pose proof (pjf_EV_perm D (Dfr ++ ([(p, kk)] ++ Rem')) HPD) as EE.
    rewrite !pjf_EV_app in EE.
    assert (E1 : EV_pj_free [(p, kk)] = 1) by (unfold EV_pj_free, EV_fuzz_free; cbn [length]; lia).
    assert (E2 : 0 <= EV_pj_free Rem') by (unfold EV_pj_free, EV_fuzz_free; lia).
    lia. }
  eapply SRr_bind.
  { apply (fs_fuzz_free_spec lyc Sc Uc Wc regsC memC mdc [] p kk (live - rd_sum Dfr) peak cnt fail);
      [ exact R10 | exact Hglob | exact HH
      | right; split; [exact Hpne|]; exists U1, U2;
        split; [exact EUc|]; split; [exact HPREc|]; split; [exact HRB | exact Hlive]
      | intros _; exact HEVc ]. }
  intros Wr cr Hwle [(Hc0 & _) | (_ & U1' & U2' & EUc' & Hpost)]; [exfalso; exact (Hpne Hc0)|].
  unfold apost_baseU, fpostU in Hpost.
  destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' &
    (l1 & l2 & Eab1 & Eab2) & HH2 & HG2).
  subst cr. rewrite R1.
  (* the freed block's footprint avoids v, the surviving blocks, the shadow and the read-only image *)
  destruct (pjf_place B lyc Sc Wc (unpoison Uc memC) mdc memC v (proj1 HARU) Hpo) as (HPL & HAMR & HHULL).
  assert (HFPb : forall a, inFP (ablocks_fp [(p - HEAD, kk + HEAD)]) a <->
    p - HEAD <= a < p - HEAD + req_size (kk + HEAD)).
  { intros a. rewrite pjf_inFP_ablocks. split.
    - intros (q & m & [E|[]] & Hr). injection E as E1 E2. rewrite <- E1, <- E2 in Hr. exact Hr.
    - intros Hr. exists (p - HEAD), (kk + HEAD). split; [left; reflexivity | exact Hr]. }
  assert (Hrq : req_size (kk + HEAD) = kk + HEAD)
    by (unfold req_size; destruct (Z.eqb_spec (kk + HEAD) 0); cbv [HEAD] in *; lia).
  assert (HFv : forall a, v <= a < v + 56 -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a).
  { intros a Ha Hf. apply pjf_inFP_app in Hf as [Hf|Hf].
    - exact (proj1 (proj2 (proj2 (HPL a Ha))) (pjf_pstat_img a Hf)).
    - apply HFPb in Hf.
      destruct Hpo as [[((cid & pos & Hinf & _ & _ & Hf1 & Hf2) & _)|((bb & nn & Hinbb & Hb1 & Hb2) & _)] _].
      + apply (pjt_block_frame_disj B lyc Sc Wc (unpoison Uc memC) mdc (p - HEAD) (kk + HEAD) cid pos a
          (proj1 HARU) Hinb Hinf). split; [exact Hf | lia].
      + destruct (Z.eq_dec bb (p - HEAD)) as [Eb|Nb].
        * destruct (Z.eq_dec nn (kk + HEAD)) as [En|Nn].
          -- apply (HAP (p, kk) v HinD); [unfold PjStruct.pj_holds; cbn [fst snd]; cbv [HEAD] in *; lia | lia].
          -- apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc bb nn (p - HEAD) (kk + HEAD) a
               (proj1 HARU) Hinbb Hinb
               (pjt_rq_ne bb nn (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia)
                  ltac:(intros (_ & Hc); exact (Nn Hc)))).
             cbv [HEAD] in *. split; [lia | lia].
        * apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc bb nn (p - HEAD) (kk + HEAD) a
            (proj1 HARU) Hinbb Hinb
            (pjt_rq_ne bb nn (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia)
               ltac:(intros (Hc & _); exact (Nb Hc)))).
          cbv [HEAD] in *. split; [lia | lia]. }
  assert (HFul : forall a kb x, In (a, kb) Rem' -> a - HEAD <= x < a + kb ->
    ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) x).
  { intros a kb x Hin Hx Hf.
    pose proof (HBKr a kb Hin) as HRBa. pose proof HRBa as (Hina & _ & Hka & _).
    assert (Hrqa : req_size (kb + HEAD) = kb + HEAD)
      by (unfold req_size; destruct (Z.eqb_spec (kb + HEAD) 0); cbv [HEAD] in *; lia).
    apply pjf_inFP_app in Hf as [Hf|Hf].
    - refine (proj2 (al_client_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc x (proj1 HARU) _)
        (pjf_pstat_img x Hf)).
      left. exists (a - HEAD), (kb + HEAD). split; [exact Hina | cbv [HEAD] in *; lia].
    - apply HFPb in Hf.
      assert (HNE : ~ (a - HEAD = p - HEAD /\ kb + HEAD = kk + HEAD)).
      { intros (E1 & E2).
        assert (Ea : a = p) by lia. assert (Ek : kb = kk) by lia. subst a kb.
        assert (HNDl : List.NoDup D) by (apply NoDup_ListNoDup; exact HND).
        assert (HNDr : List.NoDup (Dfr ++ ([(p, kk)] ++ Rem')))
          by exact (Permutation_NoDup HPD HNDl).
        rewrite app_assoc in HNDr.
        exact (pjf_nodup_disj (Dfr ++ [(p, kk)]) Rem' (p, kk) HNDr
          ltac:(apply in_or_app; right; left; reflexivity) Hin). }
      apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc (a - HEAD) (kb + HEAD) (p - HEAD) (kk + HEAD) x
        (proj1 HARU) Hina Hinb
        (pjt_rq_ne (a - HEAD) (kb + HEAD) (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia) HNE)).
      cbv [HEAD] in *. split; [lia | lia]. }
  assert (HFsh : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a ->
    ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Hf. apply pjf_inFP_app in Hf as [Hf|Hf]; [exact (pjt_pstat_low a Hf)|].
    apply HFPb in Hf.
    destruct (al_blocks tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc (p - HEAD) (kk + HEAD)
      (proj1 HARU) Hinb) as (_ & _ & _ & Happ & _).
    pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Haa.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  assert (HFcl : ~ YI16.sink_open_fp (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)])).
  { apply sink_closed_app; [exact pjt_pstat_closed|].
    apply sink_closed_ablocks_fp. repeat constructor. cbn [fst]. cbv [HEAD] in *. lia. }
  assert (HFro : forall a, in_roP tfibsegs FS_RLO FS_RHI a ->
    ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a).
  { intros a Hro Hf. apply pjf_inFP_app in Hf as [Hf|Hf]; [exact (pjt_pstat_notro a Hf Hro)|].
    apply HFPb in Hf.
    refine (proj2 (al_client_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc a (proj1 HARU) _)
      (fsw_roP_img a Hro)).
    left. exists (p - HEAD), (kk + HEAD). split; [exact Hinb | lia]. }
  assert (HFsub : fsw_fp_sub B ly S0 lyc Sc [] FP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)])).
  { intros a Hf. apply pjf_inFP_app in Hf as [Hf|Hf].
    - right. right. left. split; [|exact (pjf_pstat_img a Hf)].
      unfold FP. apply pjf_inFP_cons. right. apply pjf_inFP_app. right. exact Hf.
    - apply HFPb in Hf. left. split.
      + unfold FP. apply pjf_inFP_cons. right. apply pjf_inFP_app. left.
        apply pjf_inFP_hblocks. exists p, kk. split; [exact HinD | exact Hf].
      + exists (p - HEAD), (kk + HEAD). split; [exact Hinb | exact Hf]. }
  destruct (pjt_cross (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) 1 Dfr Rem'
      lyc Sc Uc Wc regsC memC mdc ly' S' (U1' ++ U2') Wr regs' mem' md'
      HJ HARU Hfrm HBKr Hpo HKEEP HRO HR HJc OK' PO' HP' HH2 HFsub HFv HFul HFsh HFcl HFro)
    as (HJ2 & HARU2 & Hfrm2 & HBK2 & Hpo2 & HKEEP2 & HRO2 & HR2).
  apply (HK ly' S' (U1' ++ U2') Wr regs' mem' md'); [|exact HR2].
  unfold TINV, pjf_inv.
  assert (EEV : EV_pj_free (Dfr ++ [(p, kk)]) = EV_pj_free Dfr + 1)
    by (rewrite pjf_EV_app; unfold EV_pj_free, EV_fuzz_free; cbn [length]; lia).
  assert (EHB : rd_hblocks (Dfr ++ [(p, kk)]) = rd_hblocks Dfr ++ [(p - HEAD, kk + HEAD)])
    by (rewrite pjf_rd_hblocks_app; cbn [rd_hblocks map fst snd]; reflexivity).
  assert (EHD : rd_heads (Dfr ++ [(p, kk)]) = rd_heads Dfr ++ [(p - HEAD, HEAD)])
    by (rewrite pjf_rd_heads_app; cbn [rd_heads map fst snd]; reflexivity).
  assert (ESM : rd_sum (Dfr ++ [(p, kk)]) = rd_sum Dfr + kk)
    by (rewrite pjf_rd_sum_app, pjt_rd_sum_one; reflexivity).
  rewrite EEV. split; [exact HJ2|]. split; [exact HARU2|]. split; [exact HH2|]. split; [exact Hfrm2|].
  split.
  { rewrite EHB, Eab2. apply pjf_perm_free1. rewrite <- Eab1. exact HBP. }
  split.
  { rewrite EHD, <- pjf_udrop_app, <- HUc, EUc'.
    symmetry. apply pjf_udrop_one.
    exact (pjf_head_once B lyc Sc U1' (p - HEAD, HEAD) U2' ltac:(rewrite <- EUc'; exact (proj1 (proj2 HARU)))
      ltac:(cbn [snd]; cbv [HEAD]; lia)). }
  split; [rewrite ESM; replace (live - (rd_sum Dfr + kk)) with (live - rd_sum Dfr - kk) by lia; exact HG2|].
  split; [rewrite <- app_assoc; exact HPD|].
  split; [exact HBK2|]. split; [exact Hpo2|]. split; [exact HKEEP2 | exact HRO2].
Qed.

(* ================= the three segments ================= *)
Lemma pjt_inv_perm : forall Dfr Rem Rem2 lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  Permutation Rem Rem2 -> TINV Dfr Rem lyc Sc Uc Wc memc mdc -> TINV Dfr Rem2 lyc Sc Uc Wc memc mdc.
Proof.
intros Dfr Rem Rem2 lyc Sc Uc Wc memc mdc HPm HINV.
unfold TINV, pjf_inv in HINV |- *.
destruct HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & HPD & HBKc & I10 & I11 & I12).
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact I6|]. split; [exact I7|].
split; [exact (Permutation_trans HPD (Permutation_app_head Dfr HPm))|].
split; [intros a kb Hin; apply HBKc; exact (Permutation_in _ (Permutation_sym HPm) Hin)|].
split; [exact I10|]. split; [exact I11 | exact I12].
Qed.
(* a run that writes only the frame keeps every invariant fact; the journal, ARU and the frame come back from the run *)
Lemma pjt_inv_below : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc memR mdc mdR,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memR) mdR (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memR mdR ->
  pjf_frm Wc memR ->
  same_below memc memR alloc_ceiling ->
  TINV Dfr Rem lyc Sc Uc Wc memR mdR.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc memR mdc mdR HINV HJ' HARU' Hfrm' SB.
pose proof pjf_entry_facts as (_ & _ & _ & _ & Hv1 & _).
unfold TINV, pjf_inv in HINV |- *.
destruct HINV as (_ & _ & HH & _ & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HH|]. split; [exact Hfrm'|].
split; [exact HBP|]. split; [exact HUc|].
split; [exact (fs_glob_below Wc memc memR _ peak cnt fail SB Hglob)|].
split; [exact HPD|].
split; [exact (rd_blocks_ok_below B lyc Sc Wc (unpoison Uc memR) mdR memc memR Rem (proj1 HARU') SB HBKc)|].
split; [exact (pobj_below B lyc Sc Wc (unpoison Uc memR) mdR memc memR v (proj1 HARU') SB Hpo)|].
split.
- intros x Hx. rewrite (fsw_mrestrict_below (w_H Wc) memc memR x SB); [exact (HKEEP x Hx)|].
  unfold Fv in Hx. lia.
- exact (arodata_below B Wc memc memR SB HRO).
Qed.
(* the frame's presence, from the journal *)
Lemma pjt_pres : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc -> forall a, sp0 - 128 <= a < sp0 -> apresent (w_H Wc) memc a.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc mdc HINV a Ha.
pose proof pjf_entry_facts as (_ & Hceil & H47 & _).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TINV, pjf_inv in HINV. destruct HINV as (HJ & HARU & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
apply Hpres0. unfold STK in *. lia.
Qed.
(* the header of v, read at the current memory *)
Lemma pjt_hdr : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H Wc) memc) v ty num str kids keys n cap.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc mdc HINV.
unfold TINV, pjf_inv in HINV. destruct HINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKEEP & _).
apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) mem)); [exact HHDR|].
intros x Hx. exact (HKEEP x Hx).
Qed.

(* ---- 0x837f0 .. fuzz_free (str) 0x83808, back at 0x8380c, then pjf_end_memset ---- *)
Lemma pjt_seg_str : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr Ds lyc Sc Uc Wc memc mdc -> pjf_regs regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x837f0) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & Hstr & _ & _ & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 str]).
assert (E2m : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-128)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E46 : ew (pjf_env regsc xs) 46 = Z_to_bv 64 str)
  by exact (pjf_ew_x regsc xs 46 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_X2
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837f0) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. unfold ss_X2.
  apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x837f0
    [fld 8 16 46] [(8%nat, mkAF 4096 PJF_CEIL 3)] [] xs HARU HR Hpres Hfrm ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok regsc xs 8%bv 8 16 46 Wc memc v str ltac:(reflexivity) H8 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(rewrite fsw_SOff0; exact E46) (proj1 Hstr) (fsw_pj_u64_val tfibsegs _ _ _ Hstr)).
  - exact (pjt_pd1 _ 8 v 16 16 E2u E8u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8u.
    change (2 ^ 3) with 8. split; [|exact I]. split; [unfold PJF_CEIL in *; lia|]. split; [exact Hv8 | lia].
  - exact I. }
assert (SHOK : sh_ok tfibsegs pBx SH_X2 (pjf_env regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regsc xs) (mrestrict (w_H Wc) memc) 8 v 16 24).
  - unfold pjf_env. apply pjf_U_bx. exact H23.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 8%bv 8 v); [reflexivity | exact H8 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (24 - 16) with 8 by lia. apply pjf_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 16) ltac:(lia))))).
    + replace (v + 16 + 7) with (v + 23) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 23) ltac:(lia))))). }
(* run 0x837f0 .. the `jal fuzz_free` 0x83808, stopping at the callee's entry 0x82dbc *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535996.
{ cbn [ss_mem ss_X2 pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x8380c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 str) by (pjt_rd HS (10%bv : bv 5); exact E46).
assert (HRm : pjf_regs (ms_regs msC)).
{ apply (pjf_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (22%bv : bv 5). exact (ew_Ereg_nat regsc _ 22 22%bv eq_refl).
  - pjt_rd HS (23%bv : bv 5). exact (ew_Ereg_nat regsc _ 23 23%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_X2) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [fld 8 16 46] a (sp0 - 128)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm Wc (ms_mem msC)).
{ pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  refine (pjf_frm_of_region _ _ HR0 _ _ _ _).
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav regsc xs (33 + i) i eq_refl Hi).
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr Ds lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB) as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Ds [] str 0x8380c lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HSTR as HSTR'.
  destruct HSTR' as [(E1 & E3)|(k0 & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- rewrite app_nil_r. exact HINVm.
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  pose proof HRr as (Hspr & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (pjt_pres _ _ _ _ _ _ _ _ HINVr) as Hpresr.
  unfold TINV, pjf_inv in HINVr.
  destruct HINVr as (HJr & HARUr & HHr & Hfrmr & HBPr & HUcr & Hglobr & HPDr & _ & Hpor & _ & _).
  assert (HS3 : st_ok tfibsegs (pjf_env regsr []) ss_X3
    (restrict (w_H Wr) (YK11.mkst regsr (Z_to_bv 64 0x8380c) memr (YK11.seg_rom tfibsegs)))).
  { unfold ss_X3.
    apply (pjf_reseat lyr Sr Ur Wr regsr memr mdr 0x8380c
      [] [] [] [] HARUr HRr Hpresr Hfrmr ltac:(vm_compute; reflexivity) (Forall_nil _)).
    - apply pjt_pd0. unfold pjf_env. rewrite (ew_Ereg_nat regsr _ 2 2%bv eq_refl). exact Hspr.
    - exact I.
    - exact I. }
  rewrite app_nil_r in HPDr.
  exact (pjf_end_memset lyr Sr Ur Wr regsr memr mdr (Dfr ++ Ds) HS3 HJr HARUr HRr Hfrmr HPDr HBPr HUcr Hglobr Hpor).
Qed.

(* ---- 0x837d8 .. fuzz_free (keys) 0x837ec, back at 0x837f0 ---- *)
Lemma pjt_seg_keys : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr (Ds ++ Dy) lyc Sc Uc Wc memc mdc -> pjf_regs regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x837d8) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & _ & _ & Hkeys & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 keys]).
assert (E2m : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-128)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E9 : bv_unsigned (ew (pjf_env regsc xs) 9) = v + 32)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
assert (E46 : ew (pjf_env regsc xs) 46 = Z_to_bv 64 keys)
  by exact (pjf_ew_x regsc xs 46 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_X1
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837d8) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. pose proof E9 as E9u.
  unfold ss_X1.
  apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x837d8
    [fld 8 32 46] [(8%nat, mkAF 4096 PJF_CEIL 3); (9%nat, mkAF 4096 PJF_CEIL 3)] [] xs HARU HR Hpres Hfrm
    ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok regsc xs 8%bv 8 32 46 Wc memc v keys ltac:(reflexivity) H8 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(rewrite fsw_SOff0; exact E46) (proj1 Hkeys) (fsw_pj_u64_val tfibsegs _ _ _ Hkeys)).
  - exact (pjt_pd1 _ 8 v 32 32 E2u E8u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8u, E9u.
    change (2 ^ 3) with 8.
    split; [split; [unfold PJF_CEIL in *; lia | split; [exact Hv8 | lia]]|].
    split; [split; [unfold PJF_CEIL in *; lia | split; [rewrite Zplus_mod, Hv8; reflexivity | lia]] | exact I].
  - exact I. }
assert (SHOK : sh_ok tfibsegs pBx SH_X1 (pjf_env regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regsc xs) (mrestrict (w_H Wc) memc) 9 (v + 32) 0 8).
  - unfold pjf_env. apply pjf_U_bx. exact H23.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 9%bv 9 (v + 32)); [reflexivity | exact H9 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (v + 32 + 0) with (v + 32) by lia. replace (8 - 0) with 8 by lia. apply pjf_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 32) ltac:(lia))))).
    + replace (v + 32 + 7) with (v + 39) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 39) ltac:(lia))))). }
(* run 0x837d8 .. the `jal fuzz_free` 0x837ec, stopping at the callee's entry 0x82dbc *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535996.
{ cbn [ss_mem ss_X1 pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x837f0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 keys) by (pjt_rd HS (10%bv : bv 5); exact E46).
assert (HRm : pjf_regs (ms_regs msC)).
{ apply (pjf_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (22%bv : bv 5). exact (ew_Ereg_nat regsc _ 22 22%bv eq_refl).
  - pjt_rd HS (23%bv : bv 5). exact (ew_Ereg_nat regsc _ 23 23%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_X1) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [fld 8 32 46] a (sp0 - 128)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm Wc (ms_mem msC)).
{ pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  refine (pjf_frm_of_region _ _ HR0 _ _ _ _).
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav regsc xs (33 + i) i eq_refl Hi).
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr (Ds ++ Dy) lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB) as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Dy Ds keys 0x837f0 lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HKEYS as HKEYS'.
  destruct HKEYS' as [(E1 & _ & E3)|(_ & k0 & _ & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- exact (pjt_inv_perm _ _ _ _ _ _ _ _ _ (Permutation_app_comm Ds Dy) HINVm).
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  exact (pjt_seg_str (Dfr ++ Dy) lyr Sr Ur Wr regsr memr mdr HINVr HRr).
Qed.

(* ---- 0x837c0 .. fuzz_free (kids) 0x837d4, back at 0x837d8 ---- *)
Lemma pjt_seg_kids : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc mdc -> pjf_regs regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x837c0) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H8 & H9 & H18 & H19 & H22 & H23).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & _ & Hkids & _ & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 kids]).
assert (E2m : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 128)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-128)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E19 : bv_unsigned (ew (pjf_env regsc xs) 19) = v + 24)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19; unfold w64; apply wz; lia).
assert (E46 : ew (pjf_env regsc xs) 46 = Z_to_bv 64 kids)
  by exact (pjf_ew_x regsc xs 46 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_T0
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x837c0) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. pose proof E19 as E19u.
  unfold ss_T0.
  apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x837c0
    [fld 19 0 46] [(19%nat, mkAF 4096 PJF_CEIL 3)] [] xs HARU HR Hpres Hfrm
    ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok regsc xs 19%bv 19 0 46 Wc memc (v + 24) kids ltac:(reflexivity) H19 ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(rewrite fsw_SOff0; exact E46) (proj1 Hkids)
      ltac:(rewrite Z.add_0_r; exact (fsw_pj_u64_val tfibsegs _ _ _ Hkids))).
  - exact (pjt_pd1 _ 19 (v + 24) 0 24 E2u E19u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E19u.
    change (2 ^ 3) with 8. split; [|exact I]. split; [unfold PJF_CEIL in *; lia|].
    split; [rewrite Zplus_mod, Hv8; reflexivity | lia].
  - exact I. }
assert (SHOK : sh_ok tfibsegs pBx SH_T0 (pjf_env regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regsc xs) (mrestrict (w_H Wc) memc) 19 (v + 24) 0 8).
  - unfold pjf_env. apply pjf_U_bx. exact H23.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 19%bv 19 (v + 24)); [reflexivity | exact H19 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (v + 24 + 0) with (v + 24) by lia. replace (8 - 0) with 8 by lia. apply pjf_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 24) ltac:(lia))))).
    + replace (v + 24 + 7) with (v + 31) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 31) ltac:(lia))))). }
(* run 0x837c0 .. the `jal fuzz_free` 0x837d4, stopping at the callee's entry 0x82dbc *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535996.
{ cbn [ss_mem ss_T0 pjssc fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x837d8 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 kids) by (pjt_rd HS (10%bv : bv 5); exact E46).
assert (HRm : pjf_regs (ms_regs msC)).
{ apply (pjf_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (22%bv : bv 5). exact (ew_Ereg_nat regsc _ 22 22%bv eq_refl).
  - pjt_rd HS (23%bv : bv 5). exact (ew_Ereg_nat regsc _ 23 23%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_T0) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [fld 19 0 46] a (sp0 - 128)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm Wc (ms_mem msC)).
{ pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  refine (pjf_frm_of_region _ _ HR0 _ _ _ _).
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav regsc xs (33 + i) i eq_refl Hi).
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19. unfold w64. apply wz. lia.
  - repeat (rewrite ew_ewset_other by lia). unfold pjf_env.
    rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9. unfold w64. apply wz. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB)
    as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Dk (Ds ++ Dy) kids 0x837d8 lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HKIDS as HKIDS'.
  destruct HKIDS' as [(E1 & _ & E3)|(k0 & _ & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- assert (HPm : Permutation (Ds ++ Dk ++ Dy) (Dk ++ Ds ++ Dy))
    by (rewrite !app_assoc; apply Permutation_app_tail; apply Permutation_app_comm).
  exact (pjt_inv_perm _ _ _ _ _ _ _ _ _ HPm HINVm).
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  exact (pjt_seg_keys (Dfr ++ Dk) lyr Sr Ur Wr regsr memr mdr HINVr HRr).
Qed.

(* ================= the tail: 0x837c0 .. the ret, the goal pjf_end_memset closes ================= *)
(* statement agreed with the pj_free walk lane (internal path): reached from the loop exit
   (bltu 0x837bc) and from the entry's n = 0 arm (beqz 0x836f8); Rem is Ds ++ Dk ++ Dy, the kids' subtree blocks are
   in Dfr; F keeps v's 56 bytes *)
Lemma pjf_tail : forall F Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  (forall x : Z, v <= x < v + 56 -> F x) ->
  pjf_inv F Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc mdc ->
  pjf_regs regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x837c0) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros F Dfr lyc Sc Uc Wc regsc memc mdc HF HINV HR.
apply (pjt_seg_kids Dfr lyc Sc Uc Wc regsc memc mdc); [|exact HR].
unfold TINV. unfold pjf_inv in HINV |- *.
destruct HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact I6|]. split; [exact I7|]. split; [exact I8|]. split; [exact I9|]. split; [exact I10|].
split; [intros x Hx; apply I11; apply HF; exact Hx | exact I12].
Qed.

End N.
(* ---- v = 0: the prologue, `beqz a0` (0x836ac) to the epilogue, the ret. No call, no event, nothing freed. ---- *)
Definition pjf_ssz0 : sstate := fss0T_args A_pj_free 128 [] [(10%nat, mkAF 0 0 0)].
Definition pjf_expect0 (r : bv 5) : sv := SOff (Z.to_nat (bv_unsigned r)) 0.
Lemma pjf_null : forall kk, (kk <= 2)%nat -> forall ly S0 U (W : world tfibsegs) regs mem md ch live peak cnt fail,
  fpreU tfibsegs B (STK_pj_free kk) ly S0 U W regs mem md ch ->
  YK11.getr regs 10 = w64 0 ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_free regs mem md)
    (fpostU tfibsegs B (STK_pj_free kk) (spZ regs) ((0, 0 + 56) :: ablocks_fp (rd_hblocks []) ++ FS_PSTAT_FP)
       regs ly S0 U W mem md (EV_pj_free []) (udrop U (rd_heads []))
       (fun ly' S' W' _ mem' _ =>
          Permutation (ablocks B ly S0) (rd_hblocks [] ++ ablocks B ly' S') /\
          (0 <> 0 -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W') mem') 0 /\ pobj tfibsegs B ly' S' W' mem' 0) /\
          fs_glob tfibsegs W' mem' (live - rd_sum []) peak cnt fail)).
Proof.
intros kk Hkk.
assert (HSTKk : 128 <= STK_pj_free kk).
{ assert (Hc : (kk = 0 \/ kk = 1 \/ kk = 2)%nat) by lia.
  destruct Hc as [-> | [-> | ->]]; apply Z.leb_le; vm_compute; reflexivity. }
remember (STK_pj_free kk) as SKk eqn:ESKk.
intros ly S0 U W regs mem md ch live peak cnt fail HPRE H10 HG.
pose proof HSS as [Hgot Hcell]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HPRE) as HAPU.
pose proof (fsw_sp B _ ly S0 U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0').
assert (HJ0 : ajournal tfibsegs B SKk (spZ regs) ((0, 0 + 56) :: ablocks_fp (rd_hblocks []) ++ FS_PSTAT_FP)
  ly S0 W (unpoison U mem) md [] ly S0 W (unpoison U mem) md 0)
  by exact (ajournal_init tfibsegs B SKk _ ly S0 W regs (unpoison U mem) md ch (proj1 HAPU)).
assert (HARU : ARU tfibsegs B ly S0 U W mem md) by exact (fsw_ARU B _ ly S0 U W regs mem md ch HAPU).
assert (E10 : ew (Ereg regs (fs_extraT ++ [])) 10 = Z_to_bv 64 0)
  by exact (eq_trans (ew_Ereg_nat regs _ 10 10%bv eq_refl) H10).
assert (HS0 : st_ok tfibsegs (Ereg regs (fs_extraT ++ [])) pjf_ssz0
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_pj_free) mem (YK11.seg_rom tfibsegs)))).
{ apply (fsw_entryT_argsX B SKk 128 ly S0 U W regs mem md ch A_pj_free [] [(10%nat, mkAF 0 0 0)] []
    Hgot Hcell HAPU ltac:(lia) ltac:(vm_compute; reflexivity)).
  - constructor.
  - apply (fsw_pj_parts_disjX regs (fs_extraT ++ []) 128 0);
      [lia | lia | lia
       | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
       | unfold tfib_D_asan_shadow_memory_dynamic_address; lia
       | constructor | cbn [YP09.pairwise_disjoint]; exact I].
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, (wz 0) by lia.
    rewrite Z.pow_0_r. split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I]. }
(* a0 pinned to the literal 0, so the run decides the `beqz a0` at 0x836ac (taken, to the epilogue) *)
assert (HS : st_ok tfibsegs (Ereg regs (fs_extraT ++ []))
  (mkSS (ss_pc pjf_ssz0) (sr_set (ss_regs pjf_ssz0) 10%bv (SLit 0)) (ss_mem pjf_ssz0) (ss_resv pjf_ssz0)
     (ss_facts pjf_ssz0))
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_pj_free) mem (YK11.seg_rom tfibsegs)))).
{ apply YI08.st_ok_set_reg; [exact HS0 | intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc |].
  transitivity (YK11.getr regs 10); [reflexivity | rewrite H10; reflexivity]. }
fsw_aj_runU pj_free_tbl_ok HS HJ0 HARU.
{ cbn [ss_mem pjf_ssz0 fss0T_args fsT_regions_args fsT_regions app].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity | cbn; lia
     | cbn; lia |]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
rename HS into HSc.
assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (Ereg regs (fs_extraT ++ [])) (ss_mem pjf_ssz0) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a (r & Hin & Hr). cbn [ss_mem pjf_ssz0 fss0T_args fsT_regions_args fsT_regions app] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
    cbn [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?(ew_Ereg_nat regs _ 2 2%bv eq_refl) in Hr; unfold spZ in *; lia. }
pose proof (fsw_reg_atom _ regs (fs_extraT ++ []) _ ms 1%bv 1%bv 1 HSc ltac:(vm_compute; reflexivity) eq_refl) as R1.
pose proof HAPU as (HAP0 & _ & _). pose proof HAP0 as (_ & Hra0 & _).
cbn [rd_heads map]. rewrite pjf_udrop_nil.
replace (EV_pj_free []) with 0 by (unfold EV_pj_free, EV_fuzz_free; cbn [length]; lia).
eapply (fsw_retU B pj_free_tbl pj_free_tbl_ok W (Ereg regs (fs_extraT ++ [])) _ ms _ SKk (spZ regs) _ regs
  ly S0 U W mem md ly S0 U 0 _ HSc eq_refl ltac:(vm_compute; reflexivity) ltac:(rewrite R1; exact Hra0) HJ0 HARU).
- apply (fsw_preserved _ (Ereg regs (fs_extraT ++ [])) _ ms regs pjf_expect0 HSc); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
    (lazymatch goal with |- sv_denot _ (pjf_expect0 ?q) = _ =>
       let e := eval vm_compute in (pjf_expect0 q) in change (pjf_expect0 q) with e end);
    rewrite fsw_SOff0; apply ew_Ereg_nat; vm_compute; reflexivity.
- intros mt. cbn [rd_hblocks map app rd_sum fold_right].
  split; [reflexivity|]. split; [intros Hc; congruence|].
  rewrite Z.sub_0_r. exact (fs_glob_below W mem (ms_mem ms) _ peak cnt fail SB HG).
Qed.

End W.
