(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v; 2571 of its 2712 lines of code are new or changed and 1460 lines of the source are left out. *)
(* pj_free 0x83570 (pf.c:334-350) on fs.asan (sha256 64b53ff86172...), 108 instructions: the symbolic walk of
   FSH_Fn_reader.v pj_free_spec k, level-indexed k = 0..2 (statement FIXED, not edited here).
   rule 24: the function's released plain proof exists (lib/Prog/pj_free.v @ c8557374ad2e); no released ASan-image proof
   of any fs function exists: a Theorem Labs lane, (internal path) (a Theorem Labs lane), ossv proof index v5 built
   2026-10-28T21:58:24Z, ossv/recipes@566eb6ffa5df: every fs function CONFIRMED.
   The code (listing 0x83570 .. 0x8371c): prologue (12 saves), `beqz a0` to the epilogue; s0 := v, s4 := the shadow base,
   s2 / s3 / s1 := v + 40 / v + 24 / v + 32, s5 / s9 / s10 their shadow bytes; when n = v->n > 0 the loop i = s8 (s6 = 56 i,
   s7 = 8 i): pj_free (&kids[i]) (0x83608, level k + 1), then fuzz_free (keys[i]) when keys (0x83634); then
   fuzz_free (kids) 0x83668, fuzz_free (keys) 0x83680, fuzz_free (str) 0x8369c, __asan_memset (v, 0, 56) 0x836ac and the
   epilogue. Every inline ASan check (`lbu` of a shadow byte, `bnez` to __asan_report_load8) is decided UNTAKEN by the
   walk: the checked bytes are v's fields (v is a pobj, addressable) and keys[i] (the live keys block).
   Port-from: the released plain proof lib/Prog/pj_free.v (control flow, the loop invariant: freed / remaining blocks and
   the footprint of the not-yet-freed kids kept since entry), a Theorem Labs lane's call walks (FMW_check_reject_clean.v,
   a working branch) and the fs walks FSH_check_reject_clean.v (bab265ebece), FSW_caw_tail.v (token run),
   FSW_pj_object.v (a working branch: the __asan_memset step and the resume after it).
   The data lemmas are lib/A/FSW_pj_free_dat.v. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_reader
FSW_K FSW_ret FSW_rd FSW_pj FSW_K3 FSW_pj_free_tbl FSW_pj_free_dat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Open Scope Z_scope.

(* ================= the canonical symbolic states ================= *)
(* every client pointer lies below alloc_ceiling <= 0x7fffff800000 (YCbq.v asan_consts) *)
Definition PJF_CEIL : Z := 140737479966720.
(* entry, v <> 0: v's fields str / kids / keys / n (atoms 33..36) read through a0 (atom 10) *)
Definition pjf_v0 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 16 48 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
     YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
Definition pjf_ss0 : sstate := fss0T_args A_pj_free 96 [pjf_v0] [(10%nat, mkAF 4096 PJF_CEIL 3)].
Definition pjf_SH0 : list shent := [mkSHE 10 0 56].
(* entry, v = 0 *)
Definition pjf_ssz : sstate := fss0T_args A_pj_free 96 [] [].
(* the twelve saved registers in the frame [sp - 96, sp) after the prologue, as extra atoms xatom 0..11 (atoms 33..44:
   ra, s0, s1, s2 .. s10) *)
Definition pjf_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 44 0)); YP09.mkChunk 8 (CVal 8 (SOff 43 0)); YP09.mkChunk 16 (CVal 8 (SOff 42 0));
   YP09.mkChunk 24 (CVal 8 (SOff 41 0)); YP09.mkChunk 32 (CVal 8 (SOff 40 0)); YP09.mkChunk 40 (CVal 8 (SOff 39 0));
   YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 37 0)); YP09.mkChunk 64 (CVal 8 (SOff 36 0));
   YP09.mkChunk 72 (CVal 8 (SOff 35 0)); YP09.mkChunk 80 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 8 (SOff 33 0))].
Definition pjf_sregs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
Definition pjf_saved (regs : bvmap 5 word) : list word := map (YK11.getr regs) pjf_sregs.
(* a shadow byte holding 0, based at atom n; an 8-byte field at offset o of the object at atom n, holding atom x *)
Definition shr (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition fld (n : nat) (o : Z) (x : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SOff x 0))].
(* the resumed states: registers are the machine's (atoms), the frame, the two shadow-base cells, rs; atom 20 (s4) is
   the shadow base, so the token runs take Bx := SOff 20 0 *)
Definition pjf_G (at_ : list (nat * afact)) (al : list (sv * sv)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ::
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: at_) [] al.
Definition pjss (pc : Z) (rs : list YP09.region) (at_ : list (nat * afact)) (al : list (sv * sv)) : sstate :=
  mkSS pc sr_atoms (fsT_ret_regions 96 pjf_cs rs) None (pjf_G at_ al).
Definition pBx : sv := SOff 20 0.
(* the same with assumed branch conditions: the loop's `bltu s8, n` (0x83650) and the keys test (0x83618) compare two
   SYMBOLIC values, which no atom range decides, so the state carries the taken side as an acond (a closed term; the
   index i and the count n live only in the conds_ok proof). pjss is the cs = [] case, kept as it was. *)
Definition pjf_Gc (at_ : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ::
           (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: at_) cs al.
Definition pjssc (pc : Z) (rs : list YP09.region) (at_ : list (nat * afact)) (cs : list acond)
  (al : list (sv * sv)) : sstate :=
  mkSS pc sr_atoms (fsT_ret_regions 96 pjf_cs rs) None (pjf_Gc at_ cs al).
(* an 8-byte field at offset o of the object at atom n holding the literal 0 (the null kids / keys pointer) *)
Definition fld0 (n : nat) (o : Z) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SLit 0))].
(* after pj_free (&kids[i]) 0x8360c, keys <> 0: keys (atom 45, read through s1), keys + 8 i (atom 46 = keys + s7, an
   alias), keys[i] (atom 47) *)
Definition ss_R1a : sstate :=
  pjss 0x8360c [shr 26; fld 9 0 45; fld 46 0 47] [(45%nat, mkAF 4112 PJF_CEIL 4); (46%nat, mkAF 4096 PJF_CEIL 3)]
    [(SAlu ALU_ADD (SOff 45 0) (SOff 23 0), SOff 46 0)].
Definition SH_R1a : list shent := [mkSHE 46 0 8].
(* ... keys = 0: keys (45), n (46, through s2), kids (47, through s3; 24(s0) is the same cell, an alias) *)
Definition ss_R1b : sstate :=
  pjss 0x8360c [shr 26; fld 9 0 45; shr 21; fld 18 0 46; shr 25; fld 19 0 47] [(19%nat, mkAF 4096 PJF_CEIL 3)]
    [(SOff 8 24, SOff 19 0)].
Definition SH_R : list shent := [mkSHE 19 0 8].
(* after fuzz_free (keys[i]) 0x83638: n (45), kids (46) *)
Definition ss_R2 : sstate :=
  pjss 0x83638 [shr 21; fld 18 0 45; shr 25; fld 19 0 46] [(19%nat, mkAF 4096 PJF_CEIL 3)] [(SOff 8 24, SOff 19 0)].
(* after fuzz_free (kids) 0x8366c: keys (45) *)
Definition ss_X1 : sstate := pjss 0x8366c [fld 9 0 45] [(9%nat, mkAF 4096 PJF_CEIL 3)] [(SOff 8 32, SOff 9 0)].
Definition SH_X1 : list shent := [mkSHE 9 0 8].
(* after fuzz_free (keys) 0x83684: str (45) *)
Definition ss_X2 : sstate := pjss 0x83684 [fld 8 16 45] [(8%nat, mkAF 4096 PJF_CEIL 3)] [].
Definition SH_X2 : list shent := [mkSHE 8 16 24].
(* after fuzz_free (str) 0x836a0, after __asan_memset 0x836b0 *)
Definition ss_X3 : sstate := pjss 0x836a0 [] [] [].
Definition ss_X4 : sstate := pjss 0x836b0 [] [] [].
(* ---- the loop's states (MEASURED on fs.asan with the engine; the runs reach the pcs below) ----
   the loop head 0x835f8 at kid i: the shadow cell of v + 24 (precomputed in s9, atom 25) reads 0, and kids (atom 45,
   the first entry of xs) sits at v + 24 through s3 (atom 19). The run reaches the self call 0x83570 with
   a0 = s6 + kids and ra = 0x8360c. *)
Definition ss_L : sstate := pjss 0x835f8 [shr 25; fld 19 0 45] [(45%nat, mkAF 4112 PJF_CEIL 4)] [].
(* after the self call 0x8360c with keys = 0 (the field holds the literal): the run reaches 0x83638 *)
Definition ss_Lz : sstate := pjss 0x8360c [shr 26; fld0 9 0] [] [].
(* the loop tail 0x83638: the shadow cell of v + 40 (s5, atom 21) and n (atom 45) at v + 40 through s2 (atom 18);
   24(s0) is s3's cell, an alias, for the loop-exit read at 0x83664. The assumed condition is the `bltu s8, n` of
   0x83650: BC_LTU for the back edge to 0x835f8, BC_GEU for the exit to 0x83654. *)
Definition ss_T (c : branch_cond) : sstate :=
  pjssc 0x83638 [shr 21; fld 18 0 45] [] [mkAC c (SOff 24 1) (SOff 45 0)] [(SOff 8 24, SOff 19 0)].
(* ---- the entry's states (MEASURED): v's fields read through a0 (atom 10); n >= 1 (atom 36 at least 1) runs to the
   loop head 0x835f8, n = 0 (the field holds the literal) to the tail 0x83654; both leave the twelve saved registers in
   the frame region pjf_ent_frame (base: the entry sp, atom 2) ---- *)
Definition pjf_ss0n : sstate :=
  fss0T_args A_pj_free 96 [pjf_v0] [(10%nat, mkAF 4096 PJF_CEIL 3); (36%nat, mkAF 1 (2 ^ 54) 0)].
Definition pjf_v0z : YP09.region :=
  YP09.mkRegion (Some 10%nat) 16 48 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
     YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SLit 0))].
Definition pjf_ss0z : sstate := fss0T_args A_pj_free 96 [pjf_v0z] [(10%nat, mkAF 4096 PJF_CEIL 3)].
Definition pjf_ent_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
    [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
     YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the callee-saved registers at the final ret (the epilogue reloads s0 .. s10 from the frame) *)
Definition pjf_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 96 | 8 => SOff 34 0 | 9 => SOff 35 0 | 18 => SOff 36 0 | 19 => SOff 37 0 | 20 => SOff 38 0
  | 21 => SOff 39 0 | 22 => SOff 40 0 | 23 => SOff 41 0 | 24 => SOff 42 0 | 25 => SOff 43 0 | 26 => SOff 44 0
  | z => SOff (Z.to_nat z) 0
  end.

(* ---- generic helpers of the walk (a Theorem Labs lane's FSW_pj_object.v shapes: pjo_same_below_wr, pjo_frame_aview,
   pjo_val_keep, pjo_mbyte_of_aview, pjo_apresent_unpoison, pjo_place, pjo_hull_raw, pjo_glob_keep) ---- *)
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
- apply List.NoDup_app_remove_l in Hnd. exact (pjf_nodup_disj M R x Hnd HM Hx).
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
  in_wrange E (fsT_ret_regions 96 cs rs) a -> sp <= a < sp + 96.
Proof.
intros E cs rs a sp HF E2 (r & Hin & Hr). unfold fsT_ret_regions in Hin. cbn [app In] in Hin.
destruct Hin as [<- | [<- | [<- | Hin]]].
- cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- rewrite Forall_forall in HF. pose proof (HF r Hin). lia.
Qed.
Lemma pjf_frame_aview : forall E rs (H : word -> bool) m m' a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of tfibsegs). apply HF. rewrite (wz a Ha). exact Hn.
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
(* the shadow cell of an 8-aligned, fully addressable 8-byte word reads 0: its last byte's saddr_ok leaves only s = 0.
   The inline checks of the walk whose shadow register was computed BEFORE the resumed point (s5 / s9 / s10) read this
   cell as an ordinary memory byte (the `shr` regions), so the run decides their `bnez` untaken. *)
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
(* one shadow entry of the token run, from addressability and an application home, at this walk's Bx = pBx (s4's atom
   in a resumed state; pj_get's pg_shent at fs_Bx has the same proof) *)
Lemma pjf_shent : forall E m nn base lo hi, U E pBx = SHADOW_OFF -> U E (SOff nn 0) = base -> lo <= hi ->
  range_addressable (rd_of tfibsegs m) SHADOW_OFF (base + lo) (hi - lo) -> in_app (base + lo) (hi - lo) ->
  shent_ok tfibsegs pBx E m (mkSHE nn lo hi).
Proof.
intros E m nn base lo hi HB Hn Hlh Hra Happ. unfold shent_ok. cbn [she_m she_lo she_hi]. rewrite HB, Hn.
split; [exact Hra|]. unfold app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hn. intros a Ha.
rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
(* U of a register's own atom, and of the walk's shadow base pBx = SOff 20 0 (s4), in any Ereg env *)
Lemma pjf_U_atom : forall regsc extra (r : bv 5) nn z, Z.of_nat nn = bv_unsigned r ->
  YK11.getr regsc r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U (Ereg regsc extra) (SOff nn 0) = z.
Proof.
intros regsc extra r nn z Hnn Hr Hz. unfold U. rewrite fsw_SOff0, (ew_Ereg_nat regsc extra nn r Hnn), Hr.
apply wz. exact Hz.
Qed.
Lemma pjf_U_bx : forall regsc extra, YK11.getr regsc 20 = w64 SHADOW_OFF ->
  U (Ereg regsc extra) pBx = SHADOW_OFF.
Proof.
intros regsc extra H20. unfold pBx. apply (pjf_U_atom regsc extra 20%bv); [reflexivity | exact H20|].
unfold SHADOW_OFF. lia.
Qed.
(* one shadow entry at the entry state's Bx = fs_Bx (atom 32; pj_get's pg_shent) *)
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
(* the shadow address the entry run leaves in s5 / s9 / s10 *)
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
assert (Hlo : 0xa3ca0 <= a) by (destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia).
destruct Hro as [(s & Hs & Hw & Hsr) | Hr2]; [|unfold FS_RLO, FS_RHI in Hr2; lia].
assert (Hall : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa3ca0)) tfibsegs
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall s Hs). rewrite Hw in Hall. cbn [orb] in Hall.
apply Z.leb_le in Hall. lia.
Qed.
End H.

(* the callee-saved test of a concrete register (FSW_K's fsw_cs_cases shape) *)
Ltac pjf_cs_reg :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0 lib/A/FSH_Base.v FsShadowSyms; owner RELOC: TfibLib tl_got_shadow / tl_shadow_cell (donor A/ACeg.v:28-29) *)
Hypothesis HSS : FsShadowSyms B.
(* owner ALLOC (a Theorem Labs lane, lib/A/FSH_Fn_alloc.v, S0 CTX drop a working branch faa7e2570e5): the room premise
   is on p <> 0 only (a null free has no event), no CTX binder *)
Hypothesis fs_fuzz_free_spec : @fuzz_free_spec fx rc SK tfibsegs B.
(* owner POISON-U (a Theorem Labs lane, lib/A/FSupoisonU.v:244, the ARU form of the donor's __asan_memset contract; named in
   FSH_Fn_reader.v:54-56) *)
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.
(* a reader block whose HEAD word lies off a callee's footprint survives the call (FSW_rd.fs_rblock_kept_call asks the
   whole block off FP1; a kid call writes INSIDE the kids block, below which its head stays): the same proof, the
   premise narrowed to the 8 head bytes that fs_rblock reads and the head byte fsw_journal_block_live takes *)
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

(* the frame's twelve saved words, at the current memory *)
Definition pjf_frm (Wc : world tfibsegs) (memc : word -> option byte) : Prop :=
  forall j, (j < 12)%nat ->
    val_mem tfibsegs (mrestrict (w_H Wc) memc) (sp0 - 8 - 8 * Z.of_nat j) 8
      (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0))).
(* the registers every resumed point has (callee-saved, set at entry): sp, gp, tp, s11 as at entry, s0 .. s5 *)
Definition pjf_regs (r : bvmap 5 word) : Prop :=
  spZ r = sp0 - 96 /\ YK11.getr r 3 = YK11.getr regs 3 /\ YK11.getr r 4 = YK11.getr regs 4 /\
  YK11.getr r 27 = YK11.getr regs 27 /\ YK11.getr r 8 = w64 v /\ YK11.getr r 9 = w64 (v + 32) /\
  YK11.getr r 18 = w64 (v + 40) /\ YK11.getr r 19 = w64 (v + 24) /\ YK11.getr r 20 = w64 SHADOW_OFF /\
  YK11.getr r 21 = w64 (shadow_of_addr SHADOW_OFF (v + 40)).
(* ... in the loop at kid i: s6 = 56 i, s7 = 8 i, s8 = i, s9 / s10 the shadow bytes of v + 24 / v + 32 *)
Definition pjf_lregs (i : nat) (r : bvmap 5 word) : Prop :=
  pjf_regs r /\ YK11.getr r 22 = w64 (56 * Z.of_nat i) /\ YK11.getr r 23 = w64 (8 * Z.of_nat i) /\
  YK11.getr r 24 = w64 (Z.of_nat i) /\ YK11.getr r 25 = w64 (shadow_of_addr SHADOW_OFF (v + 24)) /\
  YK11.getr r 26 = w64 (shadow_of_addr SHADOW_OFF (v + 32)).
(* the bytes kept since entry while kid ik and key iy are next (lib/Prog/pj_free.v:1161 FP): v, the kids and keys slots
   not yet passed, and the blocks Dr of the items not yet freed *)
Definition pjf_FPS (ik iy : nat) (Dr : list (Z * Z)) (x : Z) : Prop :=
  (v <= x < v + 56) \/ (ks = true /\ keys + 8 * Z.of_nat iy <= x < keys + 8 * n) \/
  (kids + 56 * Z.of_nat ik <= x < kids + 56 * n) \/ (exists b, In b Dr /\ PjStruct.pj_holds b x).
(* the invariant of a resumed point: Dfr freed, Rem not yet (Permutation D (Dfr ++ Rem)), the bytes F kept.
   arodata_okP is the last conjunct: every call site needs it for the callee's fpreU (FSW_ret.fsw_fpreU_atFP), and
   FSW_rd.arodata_kept carries it across a call. *)
Definition pjf_inv (F : Z -> Prop) (Dfr Rem : list (Z * Z)) lyc Sc Uc (Wc : world tfibsegs) memc mdc : Prop :=
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) /\
  ARU tfibsegs B lyc Sc Uc Wc memc mdc /\ FSupoisonU.fs_heads B lyc Sc Uc /\ pjf_frm Wc memc /\
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) /\ Uc = udrop U (rd_heads Dfr) /\
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail /\ Permutation D (Dfr ++ Rem) /\
  rd_blocks_ok tfibsegs B lyc Sc Wc memc Rem /\ pobj tfibsegs B lyc Sc Wc memc v /\
  (forall x : word, F (bv_unsigned x) -> mrestrict (w_H Wc) memc x = m0 x) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).

(* ---- the entry's numerals and bounds ---- *)
Lemma pjf_STK : 96 + 4096 <= STK /\ STK_fuzz_free + 96 <= STK /\
  ((k < 2)%nat -> STK_pj_free (2 - S k) + 96 <= STK) /\ STK <= 2 ^ 20.
Proof.
assert (E0 : STK_pj_free 0 = ltac:(let v := eval vm_compute in (STK_pj_free 0) in exact v)) by (vm_compute; reflexivity).
assert (E1 : STK_pj_free 1 = ltac:(let v := eval vm_compute in (STK_pj_free 1) in exact v)) by (vm_compute; reflexivity).
assert (E2 : STK_pj_free 2 = ltac:(let v := eval vm_compute in (STK_pj_free 2) in exact v)) by (vm_compute; reflexivity).
assert (Ef : STK_fuzz_free = ltac:(let v := eval vm_compute in (STK_fuzz_free) in exact v)) by (vm_compute; reflexivity).
unfold STK. assert (Hc : (k = 0 \/ k = 1 \/ k = 2)%nat) by lia.
destruct Hc as [Hk0 | [Hk0 | Hk0]]; rewrite Hk0; cbn [Nat.sub]; rewrite ?E0, ?E1, ?E2, Ef; (split; [lia|]);
  (split; [lia|]); (split; [intros Hlt; cbn [Nat.sub]; rewrite ?E0, ?E1, ?E2; lia | lia]).
Qed.
(* the kid call's window, at level k + 1 *)
Lemma pjf_STK1 : (k < 2)%nat -> 0 <= STK_pj_free (2 - S k) /\ STK_pj_free (2 - S k) + 96 <= STK.
Proof.
intros Hk2. assert (E0 : STK_pj_free 0 = ltac:(let v := eval vm_compute in (STK_pj_free 0) in exact v)) by (vm_compute; reflexivity).
assert (E1 : STK_pj_free 1 = ltac:(let v := eval vm_compute in (STK_pj_free 1) in exact v)) by (vm_compute; reflexivity).
assert (E2 : STK_pj_free 2 = ltac:(let v := eval vm_compute in (STK_pj_free 2) in exact v)) by (vm_compute; reflexivity).
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
(* two entries of D with one start are one entry: their heads sit on one byte, so as live blocks at entry they are
   the same block (sep_blocks) *)
Lemma pjf_D_uniq : forall a k1 k2, In (a, k1) D -> In (a, k2) D -> k1 = k2.
Proof.
intros a k1 k2 H1 H2. destruct (Z.eq_dec k1 k2) as [E|NE]; [exact E|exfalso].
destruct (HBK a k1 H1) as (B1 & _ & P1 & _). destruct (HBK a k2 H2) as (B2 & _ & P2 & _).
pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S0 W (unpoison U mem) md _ _ _ _ pjf_HAR0 B1 B2
  ltac:(intros E; injection E; intros; lia)) as Hd.
rewrite !pjf_req in Hd by (unfold HEAD; lia). unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia.
Qed.
(* two distinct live reader blocks: their whole blocks (head included) are apart *)
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
(* v (a pobj) lies off every live block of D: a fake frame is apart from every block, and a block holding v is no
   block of D (pj_apart D v) *)
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
(* sums and event counts of block lists *)
Lemma pjf_rd_sum_nonneg : forall L, (forall a ka, In (a, ka) L -> 0 < ka) -> 0 <= rd_sum L.
Proof.
induction L as [|[a ka] L IH]; intros H; [cbn; lia|]. rewrite pjf_rd_sum_cons. cbn [snd].
pose proof (H a ka (or_introl eq_refl)). pose proof (IH (fun a' k' Hin => H a' k' (or_intror Hin))). lia.
Qed.
Lemma pjf_EV_nonneg : forall L, 0 <= EV_pj_free L.
Proof. intros L. unfold EV_pj_free, EV_fuzz_free. lia. Qed.

(* ---- reading the frame's twelve saved words, and re-seating a resumed state ---- *)
Lemma pjf_saved_nth : forall j, (j < 12)%nat ->
  bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)) = bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)).
Proof. reflexivity. Qed.
Lemma pjf_ew_saved : forall regsc xs j, (j < 12)%nat ->
  sv_denot (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0).
Proof.
intros regsc xs j Hj. rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
cbn [fs_extraT app nth]. apply app_nth1. unfold pjf_saved. rewrite length_map. cbn. lia.
Qed.
Lemma pjf_cs_ok : forall E m, bv_unsigned (ew E 2) = sp0 - 96 ->
  (forall j, (j < 12)%nat -> sv_denot E (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0)) ->
  (forall j, (j < 12)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))) ->
  Forall (YP09.chunk_ok tfibsegs E m (sp0 - 96)) pjf_cs.
Proof.
intros E m E2 He Hv.
assert (C : forall j off, (j < 12)%nat -> off = 88 - 8 * Z.of_nat j ->
  YP09.chunk_ok tfibsegs E m (sp0 - 96) (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0)))).
{ intros j off Hj ->. apply (chunk_ok_val tfibsegs E m (sp0 - 96) _ 8%N (SOff (33 + j) 0)
    (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0)))).
  - rewrite (He j Hj). symmetry. apply Z_to_bv_bv_unsigned.
  - apply u64_range.
  - cbn; lia.
  - change (N.to_nat 8) with 8%nat. replace (sp0 - 96 + (88 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
    exact (Hv j Hj). }
unfold pjf_cs.
repeat (apply Forall_cons; [first
  [ apply (C 11%nat); [lia | reflexivity] | apply (C 10%nat); [lia | reflexivity] | apply (C 9%nat); [lia | reflexivity]
  | apply (C 8%nat); [lia | reflexivity] | apply (C 7%nat); [lia | reflexivity] | apply (C 6%nat); [lia | reflexivity]
  | apply (C 5%nat); [lia | reflexivity] | apply (C 4%nat); [lia | reflexivity] | apply (C 3%nat); [lia | reflexivity]
  | apply (C 2%nat); [lia | reflexivity] | apply (C 1%nat); [lia | reflexivity] | apply (C 0%nat); [lia | reflexivity]]|]).
apply Forall_nil.
Qed.
(* the saved words from a frame region of the walk's states *)
Lemma pjf_frm_of_region : forall E (m : word -> option byte),
  YP09.region_ok tfibsegs E m (fstk_ret 96 pjf_cs) -> bv_unsigned (ew E 2) = sp0 - 96 ->
  (forall j, (j < 12)%nat -> sv_denot E (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0)) ->
  forall j, (j < 12)%nat -> val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8
    (bv_unsigned (nth j (pjf_saved regs) (Z_to_bv 64 0))).
Proof.
intros E m HR E2 He j Hj.
replace (sp0 - 8 - 8 * Z.of_nat j) with ((sp0 - 96) + (88 - 8 * Z.of_nat j)) by lia.
apply (fsw_field E m 2 (sp0 - 96) pjf_cs 0 96 0 96 (88 - 8 * Z.of_nat j) 8%N (SOff (33 + j) 0)); [exact HR | exact E2 | | | |].
- unfold pjf_cs.
  assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11)%nat)
    by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]; cbn; tauto.
- rewrite (He j Hj). symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- cbn; lia.
Qed.
(* a resumed state, built from the machine's registers and memory (FSW_ret.fsw_after_callU_args' second half, without
   the call; a Theorem Labs lane's pjo_resume_ok): the frame from pjf_frm, the two shadow-base cells from AR (HSS), rs as given *)
Lemma pjf_reseatC : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc pc rs at_ cs al xs,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = sp0 - 96 -> YK11.getr regsc 20 = w64 SHADOW_OFF ->
  (forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pjf_frm Wc memc ->
  regions_wf (fsT_ret_regions 96 pjf_cs rs) = true ->
  Forall (YP09.region_ok tfibsegs (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (fsT_ret_regions 96 pjf_cs rs) ->
  atoms_ok (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) at_ ->
  alias_ok (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) al ->
  conds_ok (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) cs ->
  st_ok tfibsegs (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (pjssc pc rs at_ cs al)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc pc rs at_ cs al xs HARU Hsp H20 Hpres Hfrm Hwf Hrs Hpd Hat Hal Hcs.
pose proof HSS as [Hgot Hcell].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HARU as (HAR & _ & _).
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & _).
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
set (E := Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) in *.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 96) by (subst E; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl), H20; unfold w64; apply wz; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold pjssc. apply (entry_st_ok_full tfibsegs); try fold E.
- apply regs_ok_Ereg.
- exact Hwf.
- unfold fsT_ret_regions. cbn [app]. constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    * apply (pjf_cs_ok E _ E2); [intros j Hj; subst E; exact (pjf_ew_saved regsc xs j Hj) | exact Hfrm].
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
  cbn [af_lo af_hi af_al2]. rewrite E2, U32, U20. change (2 ^ 4) with 16. rewrite Z.pow_0_r.
  split; [split; [lia | split; [unfold sp0; rewrite Zminus_mod, Hal16; reflexivity | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact Hat].
Qed.
(* the cs = [] instance, the shape every resumed point outside the loop takes *)
Lemma pjf_reseat : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc pc rs at_ al xs,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = sp0 - 96 -> YK11.getr regsc 20 = w64 SHADOW_OFF ->
  (forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pjf_frm Wc memc ->
  regions_wf (fsT_ret_regions 96 pjf_cs rs) = true ->
  Forall (YP09.region_ok tfibsegs (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (fsT_ret_regions 96 pjf_cs rs) ->
  atoms_ok (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) at_ ->
  alias_ok (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) al ->
  st_ok tfibsegs (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) (pjss pc rs at_ al)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc pc rs at_ al xs HARU Hsp H20 Hpres Hfrm Hwf Hrs Hpd Hat Hal.
exact (pjf_reseatC lyc Sc Uc Wc regsc memc mdc pc rs at_ [] al xs HARU Hsp H20 Hpres Hfrm Hwf Hrs Hpd Hat Hal I).
Qed.


(* ---- the resumed env: the shadow base (fs_extraT) then the twelve saved registers, then the walk's own atoms ---- *)
Definition pjf_env (regsc : bvmap 5 word) (xs : list word) : env := Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs).
Lemma pjf_ew_sav : forall regsc xs nn j, nn = (33 + j)%nat -> (j < 12)%nat ->
  sv_denot (pjf_env regsc xs) (SOff nn 0) = nth j (pjf_saved regs) (Z_to_bv 64 0).
Proof. intros regsc xs nn j -> Hj. unfold pjf_env. exact (pjf_ew_saved regsc xs j Hj). Qed.
(* ... and the walk's own atoms, from 45 (fs_extraT is one word, pjf_saved twelve) *)
Lemma pjf_ew_x : forall regsc xs nn j, nn = (45 + j)%nat ->
  ew (pjf_env regsc xs) nn = nth j xs (Z_to_bv 64 0).
Proof.
intros regsc xs nn j ->. unfold pjf_env. replace (45 + j)%nat with (32 + S (12 + j))%nat by lia.
rewrite ew_Ereg_extra. cbn [fs_extraT app nth].
rewrite app_nth2 by (unfold pjf_saved, pjf_sregs; rewrite length_map; cbn [length]; lia).
unfold pjf_saved, pjf_sregs. rewrite length_map. cbn [length map].
replace (12 + j - 12)%nat with j by lia. reflexivity.
Qed.
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
(* an 8-byte field at offset o of the object based at a register, holding the value of an atom of xs *)
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
(* ... holding the literal 0 (the null keys pointer) *)
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
(* a byte window of v next to an image byte range (pj_string's pjs_disj_img) *)
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
(* the GOT word and the shadow-base cell are image bytes (FSW_pj_free_dat.pjf_img_cover on the pinned image) *)
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
   frame: the low half's cells sit at or above SHADOW_OFF (above every low application byte) and the high half's at
   most at SHADOW_OFF + ASAN_CEIL / 8, far below kHighMemBeg *)
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
(* ---- the loop head 0x835f8 at kid i: the resumed state ss_L ---- *)
Lemma pjf_lp_st : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc i kidsv,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc -> pjf_frm Wc memc ->
  (forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 24) 8 kidsv ->
  4112 <= kidsv -> kidsv mod 16 = 0 -> kidsv <= PJF_CEIL ->
  st_ok tfibsegs (pjf_env regsc [w64 kidsv]) ss_L
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x835f8) memc (YK11.seg_rom tfibsegs))).
Proof.
intros lyc Sc Uc Wc regsc memc mdc i kidsv HARU HL Hfrm Hpres HPOc Hkv Hk1 Hk2 Hk3.
destruct HL as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 2) = sp0 - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E19 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 19) = v + 24)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19; unfold w64; apply wz; lia).
assert (E25 : bv_unsigned (ew (pjf_env regsc [w64 kidsv]) 25) = shadow_of_addr SHADOW_OFF (v + 24))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 25 25%bv eq_refl), H25; unfold w64; apply wz;
      unfold shadow_of_addr, SHADOW_OFF in *; lia).
assert (E45 : ew (pjf_env regsc [w64 kidsv]) 45 = Z_to_bv 64 kidsv)
  by (rewrite (pjf_ew_x regsc [w64 kidsv] 45 0 eq_refl); reflexivity).
unfold pjf_env in E2, E19, E25, E45.
apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x835f8 [shr 25; fld 19 0 45] [(45%nat, mkAF 4112 PJF_CEIL 4)] []
  [w64 kidsv] HARU Hsp H20 Hpres Hfrm ltac:(vm_compute; reflexivity)).
- constructor; [|constructor; [|constructor]].
  + apply (pjf_shr_ok regsc [w64 kidsv] 25%bv 25 Wc memc (v + 24));
      [reflexivity | exact H25 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
    intros x Hx. apply HRA. lia.
  + apply (pjf_fld_ok regsc [w64 kidsv] 19%bv 19 0 45 Wc memc (v + 24) kidsv);
      [reflexivity | exact H19 | lia | lia | lia | rewrite fsw_SOff0; unfold pjf_env; exact E45
       | unfold PJF_CEIL in *; lia | rewrite Z.add_0_r; exact Hkv].
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E45, (wz kidsv) by (unfold PJF_CEIL in *; lia).
  change (2 ^ 4) with 16. split; [split; [lia | split; [exact Hk2 | lia]] | exact I].
- exact I.
Qed.
(* the callee-saved registers the epilogue restores: sp + 96 and the eleven saved atoms; gp / tp / s11 are kept *)
Lemma pjf_expect_ok : forall regsc xs,
  bv_unsigned (ew (pjf_env regsc xs) 2) = spZ regs - 96 ->
  YK11.getr regsc 3 = YK11.getr regs 3 -> YK11.getr regsc 4 = YK11.getr regs 4 ->
  YK11.getr regsc 27 = YK11.getr regs 27 ->
  forall r, In r CALLEE_SAVED -> sv_denot (pjf_env regsc xs) (pjf_expect r) = YK11.getr regs r.
Proof.
intros regsc xs E2 H3 H4 H27 r Hr. cbv [CALLEE_SAVED In] in Hr.
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
- rewrite fsw_SOff0. unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 27 27%bv eq_refl). exact H27.
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

(* ---- the last segment: from 0x836b0 (after __asan_memset) to the `ret`, giving the spec's post ---- *)
Lemma pjf_end_ret : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc Dfr,
  st_ok tfibsegs (pjf_env regsc []) ss_X4
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x836b0) memc (YK11.seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = sp0 - 96 ->
  YK11.getr regsc 3 = YK11.getr regs 3 -> YK11.getr regsc 4 = YK11.getr regs 4 ->
  YK11.getr regsc 27 = YK11.getr regs 27 ->
  Permutation D Dfr ->
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) ->
  Uc = udrop U (rd_heads Dfr) ->
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H Wc) memc) v ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x836b0) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros lyc Sc Uc Wc regsc memc mdc Dfr HS HJ HARU Hsp H3 H4 H27 HPD HBP HUc Hglob Hzero Hpo.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
assert (E2 : bv_unsigned (ew (pjf_env regsc []) 2) = sp0 + (-96))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
fsw_aj_runU pj_free_tbl_ok HS HJ HARU.
{ cbn [ss_mem pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil] ]. }
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc []) (ss_mem ss_X4) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc []) pjf_cs [] a (sp0 - 96) (Forall_nil _)
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
  apply (pjf_expect_ok regsc []); [unfold sp0 in E2 |- *; lia | exact H3 | exact H4 | exact H27].
- intros matq. unfold Qf. split; [|split].
  + etransitivity; [exact HBP|]. apply Permutation_app_tail. unfold rd_hblocks. apply Permutation_map.
    symmetry. exact HPD.
  + intros _. split.
    * exact (pjf_zero_below Wc memc (ms_mem ms) SB Hv1 Hzero).
    * exact (pobj_below B lyc Sc Wc _ _ memc (ms_mem ms) v (proj1 HARU) SB Hpo).
  + rewrite ESUM. exact (fs_glob_below Wc memc (ms_mem ms) _ peak cnt fail SB Hglob).
Qed.

(* ---- the __asan_memset (v, 0, 56) segment: 0x836a0 .. the call, the call, and the resume at 0x836b0 ---- *)
Lemma pjf_end_memset : forall lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc Dfr,
  st_ok tfibsegs (pjf_env regsc []) ss_X3
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x836a0) memc (YK11.seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_regs regsc ->
  Permutation D Dfr ->
  Permutation (ablocks B ly S0) (rd_hblocks Dfr ++ ablocks B lyc Sc) ->
  Uc = udrop U (rd_heads Dfr) ->
  fs_glob tfibsegs Wc memc (live - rd_sum Dfr) peak cnt fail ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x836a0) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros lyc Sc Uc Wc regsc memc mdc Dfr HS HJ HARU HR HPD HBP HUc Hglob Hpo.
pose proof pjf_entry_facts as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & Hra & Hra4).
pose proof pjf_STK as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 (proj1 HPRE)) as HAPf.
destruct HAPf as (HARe & Hrae & Hra4e & Hgpe & Htpe & Hstke & Hprese & Hche & HQTe).
destruct (al_layout _ _ LAWS ly S0 W (unpoison U mem) md lyc HARe Hly) as (Eab & Efa & Eown).
assert (E2 : bv_unsigned (ew (pjf_env regsc []) 2) = sp0 + (-96))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
assert (PLACE : forall mx md', AR tfibsegs B lyc Sc Wc mx md' ->
  (forall a, v <= a < v + 56 -> apresent (w_H Wc) mx a /\ ~ aowned B lyc Sc a /\ ~ in_img tfibsegs a /\ app_addr a) /\
  amem_range v 56 /\ shadow_hull_vis (aview tfibsegs (w_H Wc) mx) v 56)
  by (intros mx md' HARx; exact (pjf_place B lyc Sc Wc mx md' memc v HARx Hpo)).
destruct (PLACE (unpoison Uc memc) mdc (proj1 HARU)) as (HPL & HAMR & HHULL0).
assert (HRA0 : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HPOI : upoisoned tfibsegs Wc memc Uc) by exact (proj2 (proj2 HARU)).
(* ---- run 0x836a0 .. the call of __asan_memset ---- *)
fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU PC_memset.
{ cbn [ss_mem pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil] ]. }
rename HS into HSc.
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc []) (ss_mem ss_X3) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc []) pjf_cs [] a (sp0 - 96) (Forall_nil _)
    ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; exact Hsp) Ha).
  unfold STK in *. lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x836b0 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 2%bv 2%bv 2 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 3%bv 3%bv 3 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 4%bv 4%bv 4 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 10%bv 8%bv 8 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_lit _ _ _ ms 11%bv 0 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fsw_reg_lit _ _ _ ms 12%bv 56 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R12.
rewrite H8 in R10.
assert (HspC : spZ (ms_regs ms) = sp0 + (-96)) by (unfold spZ at 1; rewrite R2; unfold spZ in Hsp; lia).
assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
{ intros j Hj.
  apply (pjf_frm_of_region (pjf_env regsc []) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
  - pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). unfold spZ in Hsp. exact Hsp.
  - intros i Hi. exact (pjf_ew_sav regsc [] (33 + i) i eq_refl Hi). }
assert (Ho16 : (-96) mod 16 = 0) by reflexivity.
assert (Ho0 : (-96) <= 0) by lia.
assert (HoS : ESTACK - (-96) <= STK) by (unfold ESTACK; lia).
assert (Hrok : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hgpc : YK11.getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite R3, H3; exact Hgpe).
assert (Htpc : YK11.getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite R4, H4; exact Htpe).
pose proof (fsw_ecall_preU_at B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Uc Wc (ms_mem ms) _ (EV_pj_free Dfr)
  (ms_regs ms) (-96) HJ HARU HspC Ho16 Ho0 HoS Hrok Hgpc Htpc) as HPREc.
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
set (Wr := fun a => v <= a < v + 56 \/ sp0 - 96 - 4096 <= a < sp0 - 96).
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Uc Wc (ms_mem ms) _ (EV_pj_free Dfr) Uc
    Wr (Z_to_bv 64 0x836b0) _
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
(* ---- back at 0x836b0 ---- *)
assert (P2 : YK11.getr regs2 2 = YK11.getr (ms_regs ms) 2)
  by exact (fsw_pres _ _ 2%bv HP2 ltac:(pjf_cs_reg)).
assert (P3 : YK11.getr regs2 3 = YK11.getr (ms_regs ms) 3)
  by exact (fsw_pres _ _ 3%bv HP2 ltac:(pjf_cs_reg)).
assert (P4 : YK11.getr regs2 4 = YK11.getr (ms_regs ms) 4)
  by exact (fsw_pres _ _ 4%bv HP2 ltac:(pjf_cs_reg)).
assert (P20 : YK11.getr regs2 20 = YK11.getr (ms_regs ms) 20)
  by exact (fsw_pres _ _ 20%bv HP2 ltac:(pjf_cs_reg)).
assert (P27 : YK11.getr regs2 27 = YK11.getr (ms_regs ms) 27)
  by exact (fsw_pres _ _ 27%bv HP2 ltac:(pjf_cs_reg)).
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 20%bv 20%bv 20 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof (fsw_reg_atom _ regsc (fs_extraT ++ pjf_saved regs ++ []) _ ms 27%bv 27%bv 27 HSc
  ltac:(vm_compute; reflexivity) eq_refl) as R27.
assert (Hsp2 : spZ regs2 = sp0 - 96) by (unfold spZ at 1; rewrite P2; unfold spZ in HspC; lia).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
  mbyte tfibsegs (mrestrict (w_H Wc) mem2) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a)
  by (intros a Ha HW; apply (mbyte_of_aview tfibsegs); exact (Hfr2 a Ha HW)).
assert (Hfrm2 : pjf_frm Wc mem2).
{ intros j Hj. apply (pjf_val_keep (mrestrict (w_H Wc) (ms_mem ms))); [|exact (Hfrm1 j Hj)].
  intros i Hi. apply KEEP; [unfold STK in *; lia|]. unfold Wr. unfold STK in *. lia. }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HP2s : forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) mem2 a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc mem2 md2 a HARU2); [lia|]. apply Hpres2.
  unfold STK in *. lia. }
pose proof (pjf_reseat lyc Sc Uc Wc regs2 mem2 md2 0x836b0 [] [] [] [] HARU2 Hsp2
  ltac:(rewrite P20, R20; exact H20) HP2s Hfrm2 ltac:(vm_compute; reflexivity) (Forall_nil _)
  ltac:(apply pairwise_disjoint_of_extents; unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region,
          extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl);
        unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        repeat match goal with |- _ /\ _ => split end; try exact I; unfold spZ in Hsp2;
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
exact (pjf_end_ret lyc Sc Uc Wc regs2 mem2 md2 Dfr HS2 HJ2 HARU2 Hsp2
  ltac:(rewrite P3, R3; exact H3) ltac:(rewrite P4, R4; exact H4) ltac:(rewrite P27, R27; exact H27)
  HPD HBP HUc Hglob2 Hzero2 Hpo2).
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
(* the keep chain across a call: a byte of F off the callee's footprint that lies in a live block or a live frame keeps
   its entry value *)
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

(* ---- the self call 0x83608: the loop head 0x835f8 at kid i, the run to the call, pj_free (&kids[i]) at level k + 1
   (REC), and the resume at 0x8360c with kid i's blocks freed ---- *)
Lemma pjf_seg_kid : forall i Dfr Dky D1 Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (k < 2)%nat -> (i < Z.to_nat n)%nat ->
  pjf_inv (pjf_FPS i i (Dky ++ D1 ++ Rest')) Dfr (Ds ++ Dk ++ Dy ++ Dky ++ D1 ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  PjStruct.pj_fd tfibsegs m0 (fun a n0 => In (a, n0) D) (1 - k) (kids + 56 * Z.of_nat i) D1 ->
  (forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) i (Dky ++ Rest')) (Dfr ++ D1) (Ds ++ Dk ++ Dy ++ Dky ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs i regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x8360c) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x835f8) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Dky D1 Rest' lyc Sc Uc Wc regsc memc mdc Q Hk2 Hi HINV HL Hfd1 K.
destruct HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (Hpres : forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
pose proof (pjf_lp_st lyc Sc Uc Wc regsc memc mdc i kids HARU HL Hfrm Hpres HPOc Vk
  ltac:(unfold HEAD in *; lia) Hk16 ltac:(unfold PJF_CEIL; lia)) as HS.
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 kids]) 2) = sp0 + (-96))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
(* ---- run 0x835f8 .. the self call ---- *)
fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x83570.
{ cbn [ss_mem ss_L pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
rename HS into HSc.
assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regsc [w64 kids]) (ss_mem ss_L) memc (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 kids]) pjf_cs [shr 25; fld 19 0 45] a (sp0 - 96)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
    ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
  unfold sp0, STK in *. lia. }
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x8360c HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs ms) 10 = w64 (kids + 56 * Z.of_nat i)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms 10%bv HSc).
  lazymatch type of HSc with st_ok _ _ ?ssf _ =>
    replace (sr_get (ss_regs ssf) 10%bv) with (SAlu ALU_ADD (SOff 22 0) (SOff 45 0)) by (vm_compute; reflexivity) end.
  cbn [sv_denot]. rewrite (pjf_ew_x regsc [w64 kids] 45 0 eq_refl). cbn [nth].
  assert (E22 : ew (pjf_env regsc [w64 kids]) 22 = YK11.getr regsc 22) by exact (ew_Ereg_nat regsc _ 22 22%bv eq_refl).
  rewrite E22, H22. unfold w64. rewrite !Z.add_0_r.
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
assert (HspC : spZ (ms_regs ms) = sp0 + (-96)) by (unfold spZ at 1; rewrite P2; unfold spZ in Hsp; lia).
assert (HLc : pjf_lregs i (ms_regs ms)).
{ unfold pjf_lregs, pjf_regs. rewrite P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27.
  repeat split; try assumption; unfold spZ at 1; rewrite P2; exact Hsp. }
assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
{ intros j Hj.
  apply (pjf_frm_of_region (pjf_env regsc [w64 kids]) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
  - pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
  - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). unfold spZ in Hsp. exact Hsp.
  - intros i0 Hi0. exact (pjf_ew_sav regsc [w64 kids] (33 + i0) i0 eq_refl Hi0). }
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
    (ms_regs ms) (STK_pj_free (2 - S k)) (-96) [] HJ HARU HROm HspC ltac:(reflexivity) ltac:(lia)
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
assert (Hsp4 : spZ regs4 = sp0 - 96) by (unfold spZ at 1; rewrite HP4sp; unfold spZ in HspC; lia).
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc (ms_mem ms) mdC (EV_pj_free Dfr)
  (STK_pj_free (2 - S k)) FP1 96 (ms_regs ms) ly4 S4 U4 W4 regs4 mem4 md4 (EV_pj_free D1) (pjf_saved regs ++ [])
  pjf_cs [] [] 0x8360c Hgot Hcell HJ HARU HJc HFPS OK4 PO4 HP4) as (HJ4 & HARU4 & HS4).
- lia.
- lia.
- exact (proj1 (pjf_STK1 Hk2)).
- pose proof (proj2 (pjf_STK1 Hk2)). lia.
- reflexivity.
- vm_compute. reflexivity.
- unfold pjf_cs. repeat constructor; cbn; lia.
- apply (pjf_cs_ok (Ereg regs4 (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H Wc) (ms_mem ms)));
    [rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Hsp4 | exact (pjf_ew_saved regs4 []) | exact Hfrm1].
- constructor.
- apply pairwise_disjoint_of_extents. unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region,
    extent_of_region; cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl).
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold spZ in Hsp4; unfold sp0, STK in *;
  first [left; lia | right; lia].
- exact I.
- (* ---- back at 0x8360c: the invariant with kid i's blocks freed ---- *)
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
    { intros j Hj.
      apply (pjf_frm_of_region (Ereg regs4 (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H W4) mem4));
        [| | | exact Hj].
      - pose proof (fsw_region_nth _ _ _ 0 _ HS4 eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
      - rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl). exact Hsp4.
      - intros i0 Hi0. exact (pjf_ew_saved regs4 [] i0 Hi0). }
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
  + unfold pjf_lregs, pjf_regs in HLc |- *.
    destruct HLc as ((Q2 & Q3 & Q4 & Q27 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21) & Q22 & Q23 & Q24 & Q25 & Q26).
    rewrite !(fsw_pres _ _ _ HP4) by pjf_cs_reg.
    repeat split; try assumption.
Qed.

(* ---- the resume at 0x83638 after fuzz_free (keys[i]): the invariant with keys[i]'s string block (if any) freed.
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
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83638) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x83638) mem' (YK11.seg_rom tfibsegs)) md') Q.
Proof.
intros i Dfr Dky Rest' lyc Sc Uc Wc memc mdc regsC memC mdC FP1 kc ly' S' U' W' regs' mem' md' Q Hi HINV SB HJ HARU
  Hfrm1 HLc HJc OK' PO' HP' Ekc HBP' EU' HH' Hglob' HFP1 K.
destruct HINV as (_ & _ & HHD & _ & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HLc as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (Hsp' : spZ regs' = sp0 - 96) by (unfold spZ at 1; rewrite HP'sp; exact Hsp).
assert (Ef : STK_fuzz_free = ltac:(let v := eval vm_compute in (STK_fuzz_free) in exact v)) by (vm_compute; reflexivity).
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc memC mdC (EV_pj_free Dfr)
  STK_fuzz_free FP1 96 regsC ly' S' U' W' regs' mem' md' kc (pjf_saved regs ++ []) pjf_cs [] [] 0x83638
  Hgot Hcell HJ HARU HJc HFPS OK' PO' HP') as (HJ4 & HARU4 & HS4).
- exact Hsp.
- lia.
- lia.
- lia.
- reflexivity.
- vm_compute. reflexivity.
- unfold pjf_cs. repeat constructor; cbn; lia.
- apply (pjf_cs_ok (Ereg regs' (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H Wc) memC));
    [rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp' | exact (pjf_ew_saved regs' []) | exact Hfrm1].
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
    { intros j Hj.
      apply (pjf_frm_of_region (Ereg regs' (fs_extraT ++ pjf_saved regs ++ [])) (mrestrict (w_H W') mem'));
        [| | | exact Hj].
      - pose proof (fsw_region_nth _ _ _ 0 _ HS4 eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
      - rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl). exact Hsp'.
      - intros i0 Hi0. exact (pjf_ew_saved regs' [] i0 Hi0). }
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
  + unfold pjf_lregs, pjf_regs in HLc |- *.
    destruct HLc as ((Q2 & Q3 & Q4 & Q27 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21) & Q22 & Q23 & Q24 & Q25 & Q26).
    rewrite !(fsw_pres _ _ _ HP') by pjf_cs_reg.
    repeat split; try assumption.
Qed.

(* ---- 0x8360c .. 0x83638: the keys test and fuzz_free (keys[i]) ---- *)
Lemma pjf_seg_key : forall i Dfr Dky Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (i < Z.to_nat n)%nat ->
  pjf_inv (pjf_FPS (S i) i (Dky ++ Rest')) Dfr (Ds ++ Dk ++ Dy ++ Dky ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  PjStruct.pj_key tfibsegs m0 (fun a n0 => In (a, n0) D) ks (keys + 8 * Z.of_nat i) Dky ->
  (forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') (Dfr ++ Dky) (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs i regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83638) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8360c) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Dky Rest' lyc Sc Uc Wc regsc memc mdc Q Hi HINV HL Hkey K.
pose proof HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (Hpres : forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
destruct HKEYS as [(Ek0 & Eks & EDy) | (Eks & ky & HkyD & Hkyn & EDy)].
- (* ---- keys = 0: the `beqz` at 0x83618 goes to 0x83638, no call ---- *)
  rewrite Eks in Hkey. cbn [PjStruct.pj_key] in Hkey. subst Dky. rewrite Ek0 in Vkf.
  set (xs := @nil word).
  assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 96)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
  assert (E9 : bv_unsigned (ew (pjf_env regsc xs) 9) = v + 32)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
  assert (E26 : bv_unsigned (ew (pjf_env regsc xs) 26) = shadow_of_addr SHADOW_OFF (v + 32))
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 26 26%bv eq_refl), H26; unfold w64; apply wz;
        unfold shadow_of_addr, SHADOW_OFF in *; lia).
  unfold pjf_env in E2, E9, E26.
  assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_Lz
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8360c) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x8360c [shr 26; fld0 9 0] [] [] xs HARU Hsp H20 Hpres Hfrm
      ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor; [|constructor]].
      + apply (pjf_shr_ok regsc xs 26%bv 26 Wc memc (v + 32));
          [reflexivity | exact H26 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
        intros x Hx. apply HRA. lia.
      + apply (pjf_fld0_ok regsc xs 9%bv 9 0 Wc memc (v + 32)); [reflexivity | exact H9 | lia | lia | lia |].
        rewrite Z.add_0_r. exact Vkf.
    - apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld0, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - exact I.
    - exact I. }
  assert (E2' : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-96)) by (unfold pjf_env; lia).
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x83638.
  { cbn [ss_mem ss_Lz pjss fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_Lz) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [shr 26; fld0 9 0] a (sp0 - 96)
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
    { intros j Hj. apply (pjf_frm_of_region (pjf_env regsc xs) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
      - pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
      - unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
      - intros i0 Hi0. exact (pjf_ew_sav regsc xs (33 + i0) i0 eq_refl Hi0). }
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
  + unfold pjf_lregs, pjf_regs.
    rewrite P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27.
    repeat split; try assumption; unfold spZ at 1; rewrite P2; exact Hsp.
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
  assert (E2 : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 - 96)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
  assert (E9 : bv_unsigned (ew (pjf_env regsc xs) 9) = v + 32)
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
  assert (E23 : ew (pjf_env regsc xs) 23 = Z_to_bv 64 (8 * Z.of_nat i))
    by exact (eq_trans (ew_Ereg_nat regsc _ 23 23%bv eq_refl) H23).
  assert (E26 : bv_unsigned (ew (pjf_env regsc xs) 26) = shadow_of_addr SHADOW_OFF (v + 32))
    by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 26 26%bv eq_refl), H26; unfold w64; apply wz;
        unfold shadow_of_addr, SHADOW_OFF in *; lia).
  assert (E45 : ew (pjf_env regsc xs) 45 = Z_to_bv 64 keys) by (rewrite (pjf_ew_x regsc xs 45 0 eq_refl); reflexivity).
  assert (E46 : ew (pjf_env regsc xs) 46 = Z_to_bv 64 ka) by (rewrite (pjf_ew_x regsc xs 46 1 eq_refl); reflexivity).
  assert (E47 : ew (pjf_env regsc xs) 47 = Z_to_bv 64 x) by (rewrite (pjf_ew_x regsc xs 47 2 eq_refl); reflexivity).
  assert (E46u : bv_unsigned (ew (pjf_env regsc xs) 46) = ka) by (rewrite E46; apply wz; subst ka; unfold HEAD in *; lia).
  assert (HS : st_ok tfibsegs (pjf_env regsc xs) ss_R1a
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8360c) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_reseat lyc Sc Uc Wc regsc memc mdc 0x8360c [shr 26; fld 9 0 45; fld 46 0 47]
      [(45%nat, mkAF 4112 PJF_CEIL 4); (46%nat, mkAF 4096 PJF_CEIL 3)] [(SAlu ALU_ADD (SOff 45 0) (SOff 23 0), SOff 46 0)]
      xs HARU Hsp H20 Hpres Hfrm ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + apply (pjf_shr_ok regsc xs 26%bv 26 Wc memc (v + 32));
          [reflexivity | exact H26 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
        intros y Hy. apply HRA. lia.
      + apply (pjf_fld_ok regsc xs 9%bv 9 0 45 Wc memc (v + 32) keys);
          [reflexivity | exact H9 | lia | lia | lia | rewrite fsw_SOff0, E45; reflexivity
           | unfold HEAD in *; lia | rewrite Z.add_0_r; exact Vkf].
      + unfold region_ok, fld. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) with (pjf_env regsc xs). rewrite E46u.
        split; [subst ka; unfold HEAD in *; lia|]. split; [subst ka; unfold HEAD in *; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val tfibsegs (pjf_env regsc xs) _ ka 0 8 (SOff 47 0) x);
          [rewrite fsw_SOff0, E47; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vks].
    - destruct (pjf_shadow_apart (v + 32) HAPP) as (HS1' & _).
      apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) with (pjf_env regsc xs).
      rewrite E2, E9, E26, E46u.
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkaA0, HkaA7.
      unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) with (pjf_env regsc xs).
      cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E45, E46, (wz keys), (wz ka) by (subst ka; unfold HEAD in *; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8.
      unfold HEAD in *.
      split; [split; [unfold PJF_CEIL; lia | split; [exact Hy16 | lia]]|].
      split; [split; [subst ka; unfold PJF_CEIL; lia | split; [subst ka; Z.div_mod_to_equations; lia | lia]] | exact I].
    - change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ xs)) with (pjf_env regsc xs).
      cbn [alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite E45, E23, E46.
      rewrite !(wz keys), (wz (8 * Z.of_nat i)), (wz ka) by (subst ka; unfold HEAD in *; lia). rewrite !Z.add_0_r.
      rewrite alu64_add_lit. reflexivity. }
  assert (SHOK : sh_ok tfibsegs pBx SH_R1a (pjf_env regsc xs) (mrestrict (w_H Wc) memc)).
  { constructor; [|constructor].
    apply (pjf_shent (pjf_env regsc xs) (mrestrict (w_H Wc) memc) 46 ka 0 8).
    - exact (pjf_U_bx regsc _ H20).
    - unfold YP0e.U. rewrite fsw_SOff0. rewrite E46u. reflexivity.
    - lia.
    - rewrite Z.add_0_r. change (rd_of tfibsegs (mrestrict (w_H Wc) memc)) with (aview tfibsegs (w_H Wc) memc).
      apply (fsw_block_body_addressable B lyc Sc Uc Wc memc mdc (keys - HEAD) (ky + HEAD) ka 8 HARU HHD Hyin);
        [subst ka; unfold HEAD in *; lia | lia | rewrite Rky; subst ka; unfold HEAD in *; lia].
    - rewrite Z.add_0_r. apply (in_app_sub _ _ ka 8 HappY); rewrite ?Rky; subst ka; unfold HEAD in *; lia. }
  assert (E2' : bv_unsigned (ew (pjf_env regsc xs) 2) = sp0 + (-96)) by lia.
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 0x82d40.
  { cbn [ss_mem ss_R1a pjss fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  set (mdC := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc xs) (ss_mem ss_R1a) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc xs) pjf_cs [shr 26; fld 9 0 45; fld 46 0 47] a (sp0 - 96)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
      ltac:(unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp) Ha).
    unfold sp0, STK in *. lia. }
  pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x83638 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
  assert (R10 : YK11.getr (ms_regs ms) 10 = w64 x).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms 10%bv HSc).
    lazymatch type of HSc with st_ok _ _ ?ssf _ =>
      replace (sr_get (ss_regs ssf) 10%bv) with (SOff 47 0) by (vm_compute; reflexivity) end.
    rewrite fsw_SOff0, E47. reflexivity. }
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
  assert (HspC : spZ (ms_regs ms) = sp0 + (-96)) by (unfold spZ at 1; rewrite P2; unfold spZ in Hsp; lia).
  assert (HLc : pjf_lregs i (ms_regs ms)).
  { unfold pjf_lregs, pjf_regs. rewrite P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27.
    repeat split; try assumption; unfold spZ at 1; rewrite P2; exact Hsp. }
  assert (Hfrm1 : pjf_frm Wc (ms_mem ms)).
  { intros j Hj. apply (pjf_frm_of_region (pjf_env regsc xs) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
    - pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
    - exact E2.
    - intros i0 Hi0. exact (pjf_ew_sav regsc xs (33 + i0) i0 eq_refl Hi0). }
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
      (ms_regs ms) STK_fuzz_free (-96) [] HJ HARU HROm HspC ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Hra1
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

(* ---- the kept bytes all lie below alloc_ceiling (the entry's blocks of D) ---- *)
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
(* the loop tail 0x83638: the resumed state ss_T c, the taken side c of `bltu s8, n` assumed *)
Lemma pjf_tl_st : forall c lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc i,
  ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc -> pjf_frm Wc memc ->
  (forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  pobj tfibsegs B lyc Sc Wc memc v ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (v + 40) 8 n -> 0 <= n < 2 ^ 64 ->
  acond_ok (pjf_env regsc [w64 n]) (mkAC c (SOff 24 1) (SOff 45 0)) ->
  st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T c)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83638) memc (YK11.seg_rom tfibsegs))).
Proof.
intros c lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64 Hcond.
destruct HL as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (E2 : bv_unsigned (ew (pjf_env regsc [w64 n]) 2) = sp0 - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E18 : bv_unsigned (ew (pjf_env regsc [w64 n]) 18) = v + 40)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl), H18; unfold w64; apply wz; lia).
assert (E21 : bv_unsigned (ew (pjf_env regsc [w64 n]) 21) = shadow_of_addr SHADOW_OFF (v + 40))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl), H21; unfold w64; apply wz;
      unfold shadow_of_addr, SHADOW_OFF in *; lia).
assert (E8 : ew (pjf_env regsc [w64 n]) 8 = Z_to_bv 64 v) by exact (eq_trans (ew_Ereg_nat regsc _ 8 8%bv eq_refl) H8).
assert (E19 : ew (pjf_env regsc [w64 n]) 19 = Z_to_bv 64 (v + 24))
  by exact (eq_trans (ew_Ereg_nat regsc _ 19 19%bv eq_refl) H19).
assert (E45 : ew (pjf_env regsc [w64 n]) 45 = Z_to_bv 64 n) by (rewrite (pjf_ew_x regsc [w64 n] 45 0 eq_refl); reflexivity).
apply (pjf_reseatC lyc Sc Uc Wc regsc memc mdc 0x83638 [shr 21; fld 18 0 45] [] [mkAC c (SOff 24 1) (SOff 45 0)]
  [(SOff 8 24, SOff 19 0)] [w64 n] HARU Hsp H20 Hpres Hfrm ltac:(vm_compute; reflexivity)).
- constructor; [|constructor; [|constructor]].
  + apply (pjf_shr_ok regsc [w64 n] 21%bv 21 Wc memc (v + 40));
      [reflexivity | exact H21 | lia | lia | rewrite Zplus_mod, Hv8; reflexivity |].
    intros y Hy. apply HRA. lia.
  + apply (pjf_fld_ok regsc [w64 n] 18%bv 18 0 45 Wc memc (v + 40) n);
      [reflexivity | exact H18 | lia | lia | lia | rewrite fsw_SOff0, E45; reflexivity | exact Hn64
       | rewrite Z.add_0_r; exact Vn].
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, shr, fld, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ [w64 n])) with (pjf_env regsc [w64 n]).
  rewrite E2, E18, E21.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_of_addr, SHADOW_OFF, STK, sp0, PJF_CEIL in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- exact I.
- change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ [w64 n])) with (pjf_env regsc [w64 n]).
  cbn [alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite E8, E19.
  rewrite (wz v), (wz (v + 24)) by lia. f_equal. lia.
- change (Ereg regsc (fs_extraT ++ pjf_saved regs ++ [w64 n])) with (pjf_env regsc [w64 n]).
  cbn [conds_ok]. split; [exact Hcond | exact I].
Qed.

(* ---- 0x83638 .. 0x83650: the v + 40 shadow check (s5), n reloaded, i + 1, and `bltu s8, n` back to the head 0x835f8
   (i + 1 < n) or out to the tail 0x83654 (i + 1 = n) ---- *)
Lemma pjf_seg_tl : forall i Dfr Rest' lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc
    (Q : world tfibsegs -> config -> Prop),
  (i < Z.to_nat n)%nat -> (forall b, In b Rest' -> In b D) ->
  pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc Sc Uc Wc memc mdc ->
  pjf_lregs i regsc ->
  ((S i < Z.to_nat n)%nat -> forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_lregs (S i) regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x835f8) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  (S i = Z.to_nat n -> forall lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     pjf_inv (pjf_FPS (S i) (S i) Rest') Dfr (Ds ++ Dk ++ Dy ++ Rest') lyc' Sc' Uc' Wc' memc' mdc' ->
     pjf_regs regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83654) memc' (YK11.seg_rom tfibsegs)) mdc') Q) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x83638) memc (YK11.seg_rom tfibsegs)) mdc) Q.
Proof.
intros i Dfr Rest' lyc Sc Uc Wc regsc memc mdc Q Hi HRD HINV HL Kb Ke.
pose proof HINV as (HJ & HARU & HHD & Hfrm & HBP & HUc & Hglob & HPD & HRB & HPOc & HKEEP & HRO).
pose proof HL as ((Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) & H22 & H23 & H24 & H25 & H26).
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
assert (Hpres : forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a).
{ intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
  apply HpresJ. unfold sp0, STK in *. lia. }
assert (HFl : forall x, pjf_FPS (S i) (S i) Rest' x -> 0 <= x < alloc_ceiling)
  by (intros x Hx; exact (pjf_FPS_low (S i) (S i) Rest' x HRD Hx)).
assert (E24 : ew (pjf_env regsc [w64 n]) 24 = Z_to_bv 64 (Z.of_nat i))
  by exact (eq_trans (ew_Ereg_nat regsc _ 24 24%bv eq_refl) H24).
assert (E45 : ew (pjf_env regsc [w64 n]) 45 = Z_to_bv 64 n) by (rewrite (pjf_ew_x regsc [w64 n] 45 0 eq_refl); reflexivity).
assert (Hin64 : 0 <= Z.of_nat i + 1 < 2 ^ 64) by lia.
assert (Hnb : 56 * n <= alloc_ceiling).
{ destruct HKIDS as [(_ & En0 & _) | (k0 & Hk0D & Hk0n & _)]; [lia|].
  destruct (fsw_rblock_low B ly S0 W _ md mem kids k0 pjf_HAR0 (HBK kids k0 Hk0D)). unfold HEAD in *. lia. }
assert (E2' : bv_unsigned (ew (pjf_env regsc [w64 n]) 2) = sp0 + (-96))
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); unfold spZ in Hsp; rewrite Hsp; lia).
destruct (Nat.lt_ge_cases (S i) (Z.to_nat n)) as [Hlt | Hge].
- (* ---- the back edge ---- *)
  assert (HS : st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T BC_LTU)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83638) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_tl_st BC_LTU lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64).
    unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot]. rewrite E24, E45.
    unfold bv_ltu. rewrite (wz (Z.of_nat i)), (wz n) by lia. rewrite Z.add_0_r.
    rewrite (wz (Z.of_nat i + 1)), (wz n) by lia. apply Z.ltb_lt. lia. }
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x835f8.
  { cbn [ss_mem ss_T pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc [w64 n]) (ss_mem (ss_T BC_LTU)) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 n]) pjf_cs [shr 21; fld 18 0 45] a (sp0 - 96)
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
  assert (P25 : YK11.getr (ms_regs ms) 25 = YK11.getr regsc 25)
    by exact (fsw_reg_atom _ _ _ _ ms 25%bv 25%bv 25 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P26 : YK11.getr (ms_regs ms) 26 = YK11.getr regsc 26)
    by exact (fsw_reg_atom _ _ _ _ ms 26%bv 26%bv 26 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (O22 : bv_unsigned (YK11.getr (ms_regs ms) 22) = 56 * Z.of_nat i + 56).
  { apply (fsw_reg_off _ _ _ ms 22%bv 22 56 (56 * Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl), H22. unfold w64. apply wz. lia. }
  assert (O23 : bv_unsigned (YK11.getr (ms_regs ms) 23) = 8 * Z.of_nat i + 8).
  { apply (fsw_reg_off _ _ _ ms 23%bv 23 8 (8 * Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 23 23%bv eq_refl), H23. unfold w64. apply wz. lia. }
  assert (O24 : bv_unsigned (YK11.getr (ms_regs ms) 24) = Z.of_nat i + 1).
  { apply (fsw_reg_off _ _ _ ms 24%bv 24 1 (Z.of_nat i) HSc ltac:(vm_compute; reflexivity)); [|lia].
    unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 24 24%bv eq_refl), H24. unfold w64. apply wz. lia. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  apply (Kb Hlt lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + apply (pjf_inv_below _ _ _ lyc Sc Uc Wc memc mdc _ _ HINV HJ HARU); [|exact SB | exact HFl].
    intros j Hj. apply (pjf_frm_of_region (pjf_env regsc [w64 n]) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
    * pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
    * intros i0 Hi0. exact (pjf_ew_sav regsc [w64 n] (33 + i0) i0 eq_refl Hi0).
  + unfold pjf_lregs, pjf_regs. rewrite P3, P4, P8, P9, P18, P19, P20, P21, P25, P26, P27.
    rewrite <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 22)), <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 23)),
      <- (Z_to_bv_bv_unsigned 64 (YK11.getr (ms_regs ms) 24)), O22, O23, O24.
    unfold w64. rewrite !Nat2Z.inj_succ.
    repeat split; try assumption; try (f_equal; lia); unfold spZ at 1; rewrite P2; exact Hsp.
- (* ---- the exit ---- *)
  assert (Heq : S i = Z.to_nat n) by lia.
  assert (HS : st_ok tfibsegs (pjf_env regsc [w64 n]) (ss_T BC_GEU)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83638) memc (YK11.seg_rom tfibsegs)))).
  { apply (pjf_tl_st BC_GEU lyc Sc Uc Wc regsc memc mdc i HARU HL Hfrm Hpres HPOc Vn Hn64).
    unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot]. rewrite E24, E45.
    unfold bv_ltu. rewrite (wz (Z.of_nat i)), (wz n) by lia. rewrite Z.add_0_r.
    rewrite (wz (Z.of_nat i + 1)), (wz n) by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
  fsw_aj_run_toU pj_free_tbl_ok HS HJ HARU 0x83654.
  { cbn [ss_mem ss_T pjssc fsT_ret_regions app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
      first [ reflexivity | exact E2' | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
            | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
  rename HS into HSc.
  assert (SB : same_below memc (ms_mem ms) alloc_ceiling).
  { apply (pjf_same_below_wr (pjf_env regsc [w64 n]) (ss_mem (ss_T BC_GEU)) memc (ms_mem ms) alloc_ceiling HF); [|lia].
    intros a Ha. pose proof (pjf_wrange_ret (pjf_env regsc [w64 n]) pjf_cs [shr 21; fld 18 0 45] a (sp0 - 96)
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
  assert (P25 : YK11.getr (ms_regs ms) 25 = YK11.getr regsc 25)
    by exact (fsw_reg_atom _ _ _ _ ms 25%bv 25%bv 25 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P26 : YK11.getr (ms_regs ms) 26 = YK11.getr regsc 26)
    by exact (fsw_reg_atom _ _ _ _ ms 26%bv 26%bv 26 HSc ltac:(vm_compute; reflexivity) eq_refl).
  assert (P27 : YK11.getr (ms_regs ms) 27 = YK11.getr regsc 27)
    by exact (fsw_reg_atom _ _ _ _ ms 27%bv 27%bv 27 HSc ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HSc eq_refl). cbn [ss_pc].
  apply (Ke Heq lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + apply (pjf_inv_below _ _ _ lyc Sc Uc Wc memc mdc _ _ HINV HJ HARU); [|exact SB | exact HFl].
    intros j Hj. apply (pjf_frm_of_region (pjf_env regsc [w64 n]) (mrestrict (w_H Wc) (ms_mem ms))); [| | | exact Hj].
    * pose proof (fsw_region_nth _ _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0. exact HR0.
    * unfold pjf_env. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp.
    * intros i0 Hi0. exact (pjf_ew_sav regsc [w64 n] (33 + i0) i0 eq_refl Hi0).
  + unfold pjf_regs. rewrite P3, P4, P8, P9, P18, P19, P20, P21, P27.
    repeat split; try assumption; unfold spZ at 1; rewrite P2; exact Hsp.
Qed.

(* ---- the loop: induction on the kids not yet visited; the exit goes to the tail at 0x83654 ---- *)
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
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83654) memc' (YK11.seg_rom tfibsegs)) mdc') GOAL) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x835f8) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
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
(* the frame the prologue wrote: the twelve saved registers *)
Lemma pjf_entry_frm : forall xs (Wc : world tfibsegs) memc,
  YP09.region_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) (mrestrict (w_H Wc) memc) pjf_ent_frame ->
  pjf_frm Wc memc.
Proof.
intros xs Wc memc HR j Hj.
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 2) = sp0)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (Hc : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11)%nat)
  by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
- replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 + (-8)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-8) 8%N (SOff 1 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 1 1%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 + (-16)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-16) 8%N (SOff 8 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 8 8%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 + (-24)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-24) 8%N (SOff 9 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 9 9%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 + (-32)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-32) 8%N (SOff 18 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 18 18%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 + (-40)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-40) 8%N (SOff 19 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 19 19%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 + (-48)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-48) 8%N (SOff 20 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 20 20%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 + (-56)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-56) 8%N (SOff 21 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 21 21%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 7) with (sp0 + (-64)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-64) 8%N (SOff 22 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 22 22%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 8) with (sp0 + (-72)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-72) 8%N (SOff 23 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 23 23%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 9) with (sp0 + (-80)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-80) 8%N (SOff 24 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 24 24%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 10) with (sp0 + (-88)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-88) 8%N (SOff 25 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 25 25%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
- replace (sp0 - 8 - 8 * Z.of_nat 11) with (sp0 + (-96)) by lia.
  apply (fsw_field _ _ 2 sp0 _ (-96) 0 (-96) 0 (-96) 8%N (SOff 26 0) _ HR E2); [cbn; tauto | | apply u64_range | cbn; lia].
  rewrite fsw_SOff0, (ew_Ereg_nat regs _ 26 26%bv eq_refl). cbn [pjf_saved pjf_sregs map nth].
  symmetry. apply Z_to_bv_bv_unsigned.
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
  sr_get (ss_regs ss) 2%bv = SOff 2 (-96) -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  sr_get (ss_regs ss) 27%bv = SOff 27 0 -> sr_get (ss_regs ss) 8%bv = SOff 10 0 ->
  sr_get (ss_regs ss) 9%bv = SOff 10 32 -> sr_get (ss_regs ss) 18%bv = SOff 10 40 ->
  sr_get (ss_regs ss) 19%bv = SOff 10 24 -> sr_get (ss_regs ss) 20%bv = SOff 32 0 ->
  sr_get (ss_regs ss) 21%bv = SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 32 0) ->
  Permutation D (Ds ++ Dk ++ Dy ++ Rest) -> (forall b, In b Rest -> In b D) ->
  pjf_inv (pjf_FPS 0 0 Rest) [] (Ds ++ Dk ++ Dy ++ Rest) ly S0 U W (ms_mem ms) md' /\ pjf_regs (ms_regs ms).
Proof.
intros xs ss ms md' Rest HS HJ HARU SB HF0 R2 R3 R4 R27 R8 R9 R18 R19 R20 R21 HPR HRD.
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
- unfold pjf_regs, spZ. rewrite !G, R2, R3, R4, R27, R8, R9, R18, R19, R20, R21.
  assert (G32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E2u : bv_unsigned (ew E 2) = sp0)
    by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  split; [cbn [sv_denot]; rewrite E2u, (wz (sp0 + -96)) by (unfold sp0, STK in *; lia); try lia|].
  split; [rewrite fsw_SOff0; subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)|].
  split; [rewrite fsw_SOff0; subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)|].
  split; [rewrite fsw_SOff0; subst E; exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)|].
  split; [rewrite fsw_SOff0, E10; reflexivity|].
  split; [apply W10; lia|]. split; [apply W10; lia|]. split; [apply W10; lia|].
  split; [rewrite fsw_SOff0, G32; reflexivity|].
  subst E. exact (pjf_sh_reg xs 40 ltac:(lia) ltac:(lia)).
Qed.

(* ---- the entry 0x83570 .. the loop head 0x835f8 (n >= 1) or the tail 0x83654 (n = 0) ---- *)
Lemma pjf_entry :
  (forall F Dfr' lyc' Sc' Uc' (Wc' : world tfibsegs) regsc' memc' mdc',
     (forall x, v <= x < v + 56 -> F x) ->
     pjf_inv F Dfr' (Ds ++ Dk ++ Dy) lyc' Sc' Uc' Wc' memc' mdc' -> pjf_regs regsc' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 0x83654) memc' (YK11.seg_rom tfibsegs)) mdc') GOAL) ->
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
  { apply (fsw_entryT_argsX B STK 96 ly S0 U W regs mem md ch A_pj_free [pjf_v0z]
      [(10%nat, mkAF 4096 PJF_CEIL 3)] xs Hgot Hcell HAPU ltac:(unfold STK in *; lia)
      ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor]. unfold pjf_v0z.
      apply (fsw_pj_part_okR tfibsegs _ _ 10%nat v v 16 48); [lia | lia | exact U10 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 16 (SOff 33 0) str); [exact Hstr | rewrite fsw_SOff0; exact E33].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff 34 0) kids); [exact Hkids | rewrite fsw_SOff0; exact E34].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff 35 0) keys); [exact Hkeys | rewrite fsw_SOff0; exact E35].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SLit 0) 0); [rewrite <- Hn0; exact Hnn | reflexivity].
    - apply (fsw_pj_parts_disjX regs (fs_extraT ++ xs) 96 v); [lia | unfold STK in *; lia | unfold STK in *; lia
        | lia | lia | | cbn [YP09.pairwise_disjoint YP09.all_disjoint]; tauto].
      repeat apply Forall_cons; try apply Forall_nil.
      unfold pj_in_obj, pjf_v0z. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10. lia.
    - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, (wz v) by lia.
      change (2 ^ 3) with 8. split; [split; [unfold PJF_CEIL; lia | split; [exact Hv8 | lia]] | exact I]. }
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ0 HARU0 HSH fs_Bspan 0x83654.
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
    ltac:(vm_compute; reflexivity) ltac:(rewrite app_nil_r; exact HPR) ltac:(intros b []))
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
  { apply (fsw_entryT_argsX B STK 96 ly S0 U W regs mem md ch A_pj_free [pjf_v0]
      [(10%nat, mkAF 4096 PJF_CEIL 3); (36%nat, mkAF 1 (2 ^ 54) 0)] xs Hgot Hcell HAPU
      ltac:(unfold STK in *; lia) ltac:(vm_compute; reflexivity)).
    - constructor; [|constructor]. unfold pjf_v0.
      apply (fsw_pj_part_okR tfibsegs _ _ 10%nat v v 16 48); [lia | lia | exact U10 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 16 (SOff 33 0) str); [exact Hstr | rewrite fsw_SOff0; exact E33].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 24 (SOff 34 0) kids); [exact Hkids | rewrite fsw_SOff0; exact E34].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 32 (SOff 35 0) keys); [exact Hkeys | rewrite fsw_SOff0; exact E35].
      + apply (fsw_pj_chunk8 tfibsegs _ _ v 40 (SOff 36 0) n); [exact Hnn | rewrite fsw_SOff0; exact E36].
    - apply (fsw_pj_parts_disjX regs (fs_extraT ++ xs) 96 v); [lia | unfold STK in *; lia | unfold STK in *; lia
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
  fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ0 HARU0 HSH fs_Bspan 0x835f8.
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
    ltac:(vm_compute; reflexivity) HPERM HDiD) as (HINV & HREGS).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HSc eq_refl). cbn [ss_pc].
  assert (HL0 : pjf_lregs 0 (ms_regs ms)).
  { assert (G : forall r : bv 5, YK11.getr (ms_regs ms) r = sv_denot (Ereg regs (fs_extraT ++ xs)) (sr_get (ss_regs _) r))
      by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) _ _ ms r HSc)).
    unfold pjf_lregs. split; [exact HREGS|].
    split; [rewrite (G 22%bv); reflexivity|].
    split; [rewrite (G 23%bv); reflexivity|].
    split; [rewrite (G 24%bv); reflexivity|].
    split; [rewrite (G 25%bv); exact (pjf_sh_reg xs 24 ltac:(lia) ltac:(lia))
           | rewrite (G 26%bv); exact (pjf_sh_reg xs 32 ltac:(lia) ltac:(lia))]. }
  apply (pjf_loop (Z.to_nat n - 1) 0 [] Di ly S0 U W (ms_regs ms) (ms_mem ms) _ Hk2 ltac:(lia) HINV HL0).
  + replace (S (Z.to_nat n - 1)) with (Z.to_nat n) by lia.
    replace (kids + 56 * Z.of_nat 0) with kids by (cbn [Z.of_nat]; lia).
    replace (keys + 8 * Z.of_nat 0) with keys by (cbn [Z.of_nat]; lia).
    exact HITEMS.
  + exact HDiD.
  + exact TAIL.
Qed.
End N.

(* ---- v = 0: the prologue, `beqz a0` to the epilogue, the ret. No call, no event, nothing freed. ---- *)
Definition pjf_ssz0 : sstate := fss0T_args A_pj_free 96 [] [(10%nat, mkAF 0 0 0)].
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
assert (HSTKk : 96 <= STK_pj_free kk).
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
{ apply (fsw_entryT_argsX B SKk 96 ly S0 U W regs mem md ch A_pj_free [] [(10%nat, mkAF 0 0 0)] []
    Hgot Hcell HAPU ltac:(lia) ltac:(vm_compute; reflexivity)).
  - constructor.
  - apply (fsw_pj_parts_disjX regs (fs_extraT ++ []) 96 0);
      [lia | lia | lia
       | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
       | unfold tfib_D_asan_shadow_memory_dynamic_address; lia
       | constructor | cbn [YP09.pairwise_disjoint]; exact I].
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, (wz 0) by lia.
    rewrite Z.pow_0_r. split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I]. }
(* a0 pinned to the literal 0, so the run decides the `beqz a0` at 0x835a4 (taken, to the epilogue) *)
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
