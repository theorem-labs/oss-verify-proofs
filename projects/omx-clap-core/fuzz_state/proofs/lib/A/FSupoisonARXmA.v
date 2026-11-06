(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/AGif0n.v, with its module paths changed; 632 of its 664 lines of code are new or changed and 315 lines of the source are left out. *)
(* The AR -> ARU transfer of a Theorem Labs lane's FROZEN primary Allocate interface records (a Theorem Labs lane):
   lib/Reusable/AGif0n.v's [AIface], [AIfaceK] and [AIfaceM], at the record level (rule 24: no function proved; kind:
   statement transfer of an interface record).

   For each record R, with ARX abstract: "R holds of cgif's instance [ARX_AR im_segs B I] => R holds of fuzz_state's
   instance [ARX_ARU im_segs B I Up]", the owned set [aowned B] on both sides, every other parameter the same variable
   (FSupoisonARXm.v's method, section 3 toolkit):
     - [aiface_U]  : AIface  (if_inst, if_view, if_shape, if_depot, if_dpost_aok, if_post, if_owned, if_uninit);
     - [aifaceK_U] : AIfaceK (if_post_k, if_owned_k), reading the pre-state's view off the AR side's AIface.if_view;
     - [ifaceM_U]  : AIfaceM; its callee contract [if_refill] is NOT transferred (the refill runs on the poisoned
       memory, decision a Theorem Labs lane 12:13Z): the ARU record takes it as the premise [if_refill_t ..],
       whose text is the field's text, so the record constructor takes it by conversion.

   Shared work: [hview_back] (the hit view's read set is off Up; if_view, if_view_m), [mview_back] (the miss view's;
   if_mview), [post_g_core] / [post_k_core] (the machine post of the g / k path moved to the unpoisoned memories, and
   Up's shadow bytes unchanged by it; if_post + if_post_miss / if_post_k + if_post_miss_k), [rebuild_view] (ARU at
   the post state; all four post fields), [zone_off] (the zones are off Up; if_depot, if_depot_miss, the posts).

   Premises (image facts only; each is what a real fs instance satisfies):
     premise                                 | discharged for fs by
     ----------------------------------------+----------------------------------------------------------------------
     inst_low ag_inst_ok                     | lib/A|B/FSupoisonARX.fs_inst_low (ag_inst_ok := fs_inst_ok,
                                             |   inst = TFIB_INST, below SHADOW_OFF)
     zones_free im_segs B ag_dzone ag_czone  | lib/A|B/FSupoisonARX.fs_zones_free / zones_free_shape
     img_low                       (M only)  | AF0m.TFIB_OOM 0x12a1a0, TFIB_ERRNO 0x5dae8c (A); B's YF0m likewise
     ag_inst_ok I                  (M only)  | ADDED: AIfaceM has no if_inst, and the view fields (if_mview,
                                             |   if_view_m) fix the instance cells inst + 0x20 / 0xe20 / 0xe28, which
                                             |   must be off Up.  fs: I = TFIB_INST and ag_inst_ok := fs_inst_ok
                                             |   (inst = TFIB_INST), so eq_refl; for any image, the AR side's
                                             |   AIface.if_inst at an AR state gives it.
   No premise fixes the shadow offset ag_shadow (SHBv): every shadow cell a transfer moves is placed off Up by the
   view's 250 bytes, or by lying inside that window, whatever SHBv is.

   Requires only lib/Reusable, lib/A/FSupoison and lib/A/FSupoisonARXm (image-free).  No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG ImgBase ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Arithmetic of the hit paths (ImgBaseAG's g and k geometry).                                                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* The cached chunk sits in the primary space, above kHighMemBeg and below the ceiling.  The bound on v is hview.hv_v's
   (c5 F1 form, a working branch 86aa4177b94); the class size is at most kMaxSize (YG0a.class_ok). *)
Lemma Kv_bounds : forall ly cl v, layout_ok ly -> 1 <= cl <= 30 -> 0 <= v -> 16 * v + 2 ^ 16 <= 2 ^ 32 ->
0 < class_size cl -> kHighMemBeg <= Kv ly cl v /\ Kv ly cl v + class_size cl <= ASAN_CEIL /\ Kv ly cl v mod 8 = 0.
Proof.
intros ly cl v LO Hcl Hv Hvs Hcs.
pose proof (lo_high ly LO) as [H1 H2].
pose proof (lo_space_in ly LO) as [S1 S2].
pose proof (lo_space_al ly LO) as SA.
pose proof (class_ok cl ltac:(lia)) as (_ & _ & KM & _). unfold kMaxSize in KM.
assert (E32 : 2 ^ 32 = 4294967296) by reflexivity.
assert (E16 : 2 ^ 16 = 65536) by reflexivity.
assert (E37 : kSpaceSize = 137438953472) by reflexivity.
assert (CL : 0 <= cl * 2 ^ 32 <= 30 * 2 ^ 32) by (rewrite E32; nia).
unfold Kv, kHighMemBeg, kPrimResvSize in *. rewrite E32 in *. rewrite E16 in *. rewrite E37 in *.
split; [lia|]. split; [lia|].
apply Z.mod_divide in SA as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. rewrite Hq.
exists (q * 8192 + cl * 536870912 + 2 * v). lia.
Qed.

Lemma Kv_split : forall ly cl v x, Kv ly cl v mod 8 = 0 -> x mod 8 = 0 -> (Kv ly cl v + x) / 8 = Kv ly cl v / 8 + x / 8.
Proof.
intros ly cl v x K8 Hx. apply Z.mod_divide in Hx as [a Ha]; [|lia]. apply Z.mod_divide in K8 as [b Hb]; [|lia].
rewrite Ha, Hb. replace (b * 8 + a * 8) with ((b + a) * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.

(* A byte [base + x/8] of a shadow window [base, base + c/8) whose granule x is followed by a whole granule. *)
Lemma pb_in : forall base x c, x mod 8 = 0 -> 0 <= x -> x + 8 <= c -> base <= base + x / 8 < base + c / 8.
Proof.
intros base x c H8 H0 Hc. apply Z.mod_divide in H8 as [a Ha]; [|lia]. subst x. rewrite Z.div_mul by lia.
assert (a + 1 <= c / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* A sub-window [base + r/8, base + r/8 + q/8) of a shadow window [base, base + c/8). *)
Lemma win_sub : forall base r q c, r mod 8 = 0 -> q mod 8 = 0 -> 0 <= r -> 0 <= q -> r + q <= c ->
forall s, base + r / 8 <= s < base + r / 8 + q / 8 -> base <= s < base + c / 8.
Proof.
intros base r q c Hr Hq R0 Q0 Hc s Hs.
apply Z.mod_divide in Hr as [a Ha]; [|lia]. apply Z.mod_divide in Hq as [b Hb]; [|lia]. subst r q.
rewrite !Z.div_mul in Hs by lia.
assert (a + b <= c / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* The g path (49 <= n <= 64512, redzone RZ (rz_log n)): the new block's shadow window [SKv, SKv + class_size/8)
   holds the user shadow [SUv, SUv + N8D/8) and, for an odd size, the partial byte PBv. *)
Lemma shadow_window : forall ly n cl v, layout_ok ly -> 49 <= n <= 64512 -> cl = chunk_class n ->
0 <= v -> 16 * v + 2 ^ 16 <= 2 ^ 32 ->
SKv ly cl v + (RZ (rz_log n) + N8D n) / 8 = PBv ly n cl v (rz_log n) /\
SKv ly cl v + RZ (rz_log n) / 8 = SUv ly cl v (rz_log n) /\
(n mod 8 <> 0 -> RZ (rz_log n) + N8D n + 8 <= class_size cl) /\
RZ (rz_log n) + N8D n <= class_size cl /\
RZ (rz_log n) + n <= class_size cl /\ 16 <= RZ (rz_log n) <= 2048 /\
RZ (rz_log n) mod 8 = 0 /\ N8D n mod 8 = 0 /\ 0 <= N8D n.
Proof.
intros ly n cl v LO Hn Hcl Hv Hvs.
pose proof (from_primary_64512 n ltac:(lia)) as FP.
pose proof (primary_geometry n ltac:(lia) FP) as (PG1 & PG2 & PG3 & PG4 & PG5).
pose proof (req_size_bounds n ltac:(lia)) as (_ & _ & RQ).
pose proof (rz_size_bounds n) as [[RZ1 RZ2] RZM].
assert (RZ8 : RZ (rz_log n) = rz_size n) by (unfold RZ, rz_of; rewrite rz_size_eq; reflexivity).
rewrite <- Hcl in PG1, PG2, PG3, PG4, PG5.
pose proof (Kv_bounds ly cl v LO ltac:(lia) Hv Hvs ltac:(lia)) as (_ & _ & K8).
assert (N8 : N8D n <= n /\ N8D n mod 8 = 0 /\ 0 <= N8D n).
{ unfold N8D. pose proof (Z.mul_div_le n 8 ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia | lia]. }
assert (RZD8 : RZ (rz_log n) mod 8 = 0).
{ rewrite RZ8. apply Z.mod_divide; [lia|]. apply Z.mod_divide in RZM as [a Ha]; [|lia]. exists (a * 2). lia. }
assert (SUM8 : (RZ (rz_log n) + N8D n) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in RZD8 as [a Ha]; [|lia].
  destruct N8 as (_ & NM & _). apply Z.mod_divide in NM as [b Hb]; [|lia]. exists (a + b). lia. }
split.
{ unfold PBv, SKv.
  replace (Kv ly cl v + RZ (rz_log n) + N8D n) with (Kv ly cl v + (RZ (rz_log n) + N8D n)) by lia.
  rewrite (Kv_split ly cl v _ K8 SUM8). lia. }
split; [unfold SUv, Uv, SKv; rewrite (Kv_split ly cl v _ K8 RZD8); lia|].
assert (N8L : n mod 8 <> 0 -> N8D n <= n - 1).
{ intros HO. unfold N8D. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
rewrite RZ8 in RZD8, SUM8 |- *.
split; [intros HO; pose proof (N8L HO); lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact RZD8 | exact (proj2 N8)].
Qed.

(* The k path (0 <= n <= 48, redzone K6.RZ = 16, header size K6.NPv n): the same window facts. *)
Lemma shadow_window_k : forall ly n cl v, layout_ok ly -> 0 <= n <= 48 -> cl = chunk_class n ->
0 <= v -> 16 * v + 2 ^ 16 <= 2 ^ 32 ->
SKv ly cl v + (K6.RZ + K6.N8D n) / 8 = K6.PBv ly n cl v /\
SKv ly cl v + K6.RZ / 8 = K6.SUv ly cl v /\
(K6.NPv n mod 8 <> 0 -> K6.RZ + K6.N8D n + 8 <= class_size cl) /\
K6.RZ + K6.N8D n <= class_size cl /\
K6.RZ + K6.NPv n <= class_size cl /\
K6.N8D n mod 8 = 0 /\ 0 <= K6.N8D n /\ 1 <= K6.NPv n.
Proof.
intros ly n cl v LO Hn Hcl Hv Hvs.
pose proof (from_primary_64512 n ltac:(lia)) as FP.
pose proof (primary_geometry n ltac:(lia) FP) as (PG1 & PG2 & PG3 & PG4 & PG5).
pose proof (req_size_bounds n ltac:(lia)) as (RQ0 & _ & _).
assert (RZ0 : rz_size n = 16).
{ unfold rz_size, rz_log. replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
rewrite <- Hcl in PG1, PG2, PG3, PG4, PG5.
pose proof (Kv_bounds ly cl v LO ltac:(lia) Hv Hvs ltac:(lia)) as (_ & _ & K8).
assert (NP : K6.NPv n = req_size n) by (unfold K6.NPv; exact RQ0).
assert (NP1 : 1 <= K6.NPv n) by (unfold K6.NPv; lia).
assert (N8 : K6.N8D n <= K6.NPv n /\ K6.N8D n mod 8 = 0 /\ 0 <= K6.N8D n).
{ unfold K6.N8D. pose proof (Z.mul_div_le (K6.NPv n) 8 ltac:(lia)).
  pose proof (Z.div_pos (K6.NPv n) 8 ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia | lia]. }
destruct N8 as (N8a & N8b & N8c).
assert (SUM8 : (16 + K6.N8D n) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in N8b as [b Hb]; [|lia]. exists (2 + b). lia. }
assert (CS : 16 + K6.NPv n <= class_size cl) by lia.
unfold K6.RZ.
split.
{ unfold K6.PBv, SKv, K6.RZ. change (K6.Kv ly cl v) with (Kv ly cl v).
  replace (Kv ly cl v + 16 + K6.N8D n) with (Kv ly cl v + (16 + K6.N8D n)) by lia.
  rewrite (Kv_split ly cl v _ K8 SUM8). lia. }
split.
{ unfold K6.SUv, K6.Uv, SKv, K6.RZ. change (K6.Kv ly cl v) with (Kv ly cl v).
  rewrite (Kv_split ly cl v 16 K8 eq_refl). lia. }
assert (N8L : K6.NPv n mod 8 <> 0 -> K6.N8D n <= K6.NPv n - 1).
{ intros HO. unfold K6.N8D. pose proof (Z.div_mod (K6.NPv n) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (K6.NPv n) 8 ltac:(lia)). lia. }
split; [intros HO; pose proof (N8L HO); lia|].
split; [lia|]. split; [lia|]. split; [exact N8b|]. split; [exact N8c | exact NP1].
Qed.

(* The hit path's chunk offset, read off the view's bounds. *)
Lemma off_range : forall off, off mod 32 = 0 -> 0 <= off / 16 -> 16 * (off / 16) + 2 ^ 16 <= 2 ^ 32 ->
0 <= off < 2 ^ 32.
Proof.
intros off H32 H0 H1.
assert (EOFF : off = 16 * (off / 16)).
{ apply Z.mod_divide in H32 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 32) with (q * 2 * 16) by lia. rewrite Z.div_mul by lia. lia. }
assert (E32 : 2 ^ 32 = 4294967296) by reflexivity. assert (E16 : 2 ^ 16 = 65536) by reflexivity.
rewrite E16, E32 in H1. rewrite E32. lia.
Qed.

Lemma st_final_chunks : forall S cl l off n tr z,
st_chunks (st_final S cl l off n tr z) = upd_chunk (st_chunks S) (new_chunk cl off n).
Proof. intros S cl l off n tr z. unfold st_final, st_popped, depot_after. destruct (z =? 0); reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Off-Up facts shared by the fields.                                                                             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma ush_not_off : forall Up s, FSP.in_ush Up s = true -> 0 <= s < 2 ^ 64 -> ~ off_ush Up s.
Proof. intros Up s H R O. unfold off_ush in O. rewrite (Z.mod_small s _ R) in O. rewrite O in H. discriminate. Qed.

(* The two zones of a callee hold no user-poisoned byte. *)
Lemma zone_off : forall B Up ly S W mem md a, zones_free im_segs B ag_dzone ag_czone ->
FSP.ARU im_segs B ly S Up W mem md -> ag_dzone ly a \/ ag_czone ly a -> off_ush Up a.
Proof.
intros B Up ly S W mem md a ZON HARU Ha.
destruct (ZON ly S W (FSP.unpoison Up mem) md a (FSP.ARU_AR im_segs B ly S Up W mem md HARU) Ha) as [HR HF].
exact (ush_free_off im_segs B ly S Up W mem md a HARU HR HF).
Qed.

Lemma wframe_unpoison : forall W ly regs0 mem0 tr Up, wframe W ly regs0 mem0 tr ->
wframe W ly regs0 (FSP.unpoison Up mem0) tr.
Proof.
intros W ly regs0 mem0 tr Up (F1 & F2 & F3 & F4 & F5).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem0 a (F5 a Ha)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The views (kind 2): each cell the view fixes is off Up, so the AR side's view over [unpoison Up mem] is the    *)
(*    view over [mem].                                                                                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* The hit view's read set: the constant cells (owned core), the instance cells (below the shadow, inst_low), the
   thread's cache / unwinding / junk cells (thread object), the cached chunk (primary space, >= kHighMemBeg) and its
   shadow (each byte reads 250 through ARU's view, so it is not a poisoned byte: val250_off_ush). *)
Lemma hview_back : forall B Up ly S W mem md inst cl cnt v,
inst_low ag_inst_ok -> ag_inst_ok inst ->
FSP.ARU im_segs B ly S Up W mem md -> 1 <= cl <= 30 -> 0 < class_size cl ->
hview B W ly inst (FSP.unpoison Up mem) cl cnt v -> hview B W ly inst mem cl cnt v.
Proof.
intros B Up ly S W mem md inst cl cnt v ILOW IOK HARU Hcl Hcs HV.
pose proof (ILOW inst IOK) as [IL1 IL2].
destruct HV as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12].
pose proof L5 as (HV0 & HV2 & HVS).
pose proof (Kv_bounds ly cl v L1 Hcl HV0 HVS Hcs) as (KB1 & KB2 & KB8).
pose proof ASAN_CEIL_range as [CR _].
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem md a HARU Ha)).
assert (OL : forall a, 0 <= a < SHADOW_OFF -> off_ush Up a)
  by (intros a Ha; exact (low_off_ush im_segs B ly S Up W mem md a HARU Ha)).
assert (OH : forall a, Kv ly cl v <= a < Kv ly cl v + class_size cl -> off_ush Up a).
{ intros a Ha. apply (high_off_ush im_segs B ly S Up W mem md a HARU). unfold kHighMemBeg, ASAN_CEIL in *. lia. }
constructor; try assumption.
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison im_segs B ly (w_H W) Up mem c).
  + intros k Hk. exact (const_cell_off_ush im_segs B ly S Up W mem md c HARU Hc k Hk).
  + exact (proj1 (Forall_forall _ _) L6 c Hc).
- destruct L7 as (V1 & V2 & V3). split; [|split].
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0x20) 8 _
            ltac:(intros k Hk; apply OL; lia)) V1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0xe20) 8 _
            ltac:(intros k Hk; apply OL; lia)) V2).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0xe28) 8 _
            ltac:(intros k Hk; apply OL; lia)) V3).
- destruct L8 as (V1 & V2 & V3). split; [|split].
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (Pv ly cl) 4 _
            ltac:(intros k Hk; apply OT; unfold Pv, t_cache, kThreadObjSize in *; lia)) V1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (Pv ly cl + 8) 8 _
            ltac:(intros k Hk; apply OT; unfold Pv, t_cache, kThreadObjSize in *; lia)) V2).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (PVv ly cl cnt) 4 _
            ltac:(intros k Hk; apply OT; unfold PVv, Pv, t_cache, kThreadObjSize in *; lia)) V3).
- exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (ly_T ly + t_unwinding) 1 0
          ltac:(intros k Hk; apply OT; unfold t_unwinding, kThreadObjSize in *; lia)) L9).
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a);
  [apply OT; unfold t_cache_stats, t_unwinding, kThreadObjSize in *; lia | exact (L10 a Ha)].
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [apply OH; exact Ha | exact (L11 a Ha)].
- intros s Hs. destruct (L12 s Hs) as [P1 P2].
  pose proof (val250_off_ush im_segs Up W mem s (proj1 P1) P2) as OS.
  split; [exact (apresent_unpoison_bwd (w_H W) Up mem s OS P1)|].
  exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem s 1 250
          ltac:(intros k Hk; replace (s + k) with s by lia; exact OS)) P2).
Qed.

(* The miss view's read set: the constant cells, the instance cells, the class's cache count, the unwinding byte. *)
Lemma mview_back : forall B Up ly S W mem md inst cl,
inst_low ag_inst_ok -> ag_inst_ok inst ->
FSP.ARU im_segs B ly S Up W mem md -> 1 <= cl <= 30 ->
mview B W ly inst (FSP.unpoison Up mem) cl -> mview B W ly inst mem cl.
Proof.
intros B Up ly S W mem md inst cl ILOW IOK HARU Hcl MV.
pose proof (ILOW inst IOK) as [IL1 IL2].
destruct MV as [M1 M2 M3 M4 M5 M6 M7].
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem md a HARU Ha)).
assert (OL : forall a, 0 <= a < SHADOW_OFF -> off_ush Up a)
  by (intros a Ha; exact (low_off_ush im_segs B ly S Up W mem md a HARU Ha)).
constructor; try assumption.
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison im_segs B ly (w_H W) Up mem c).
  + intros k Hk. exact (const_cell_off_ush im_segs B ly S Up W mem md c HARU Hc k Hk).
  + exact (proj1 (Forall_forall _ _) M4 c Hc).
- destruct M5 as (V1 & V2 & V3). split; [|split].
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0x20) 8 _
            ltac:(intros k Hk; apply OL; lia)) V1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0xe20) 8 _
            ltac:(intros k Hk; apply OL; lia)) V2).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0xe28) 8 _
            ltac:(intros k Hk; apply OL; lia)) V3).
- exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (Pv ly cl) 4 0
          ltac:(intros k Hk; apply OT; unfold Pv, t_cache, kThreadObjSize in *; lia)) M6).
- exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (ly_T ly + t_unwinding) 1 0
          ltac:(intros k Hk; apply OT; unfold t_unwinding, kThreadObjSize in *; lia)) M7).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The posts (kind 4): the machine post moved to the unpoisoned memories, Up's shadow bytes unchanged by it, and  *)
(*    ARU rebuilt at the post state.                                                                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* The g path: at_RETw over (mem0, mem') gives at_RETw over (unpoison Up mem0, unpoison Up mem'), with the entry
   frame and the header byte jb; and no window the post writes holds a byte of Up. *)
Lemma post_g_core : forall B Up ly S W mem0 md0 inst n cnt v regs0 jb odd z tr
(DP : Z -> (word -> option byte) -> Prop) regs' mem' mat,
zones_free im_segs B ag_dzone ag_czone ->
FSP.ARU im_segs B ly S Up W mem0 md0 ->
49 <= n <= 64512 ->
hview B W ly inst (FSP.unpoison Up mem0) (chunk_class n) cnt v ->
wframe W ly regs0 mem0 tr ->
val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) v + RZ (rz_log n) - 15) 1 jb ->
at_RETw W ly regs0 mem0 md0 n (chunk_class n) cnt v jb (rz_log n) DP odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> n mod 8 <> 0) ->
wframe W ly regs0 (FSP.unpoison Up mem0) tr /\
val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem0)) (Kv ly (chunk_class n) v + RZ (rz_log n) - 15) 1 jb /\
at_RETw W ly regs0 (FSP.unpoison Up mem0) md0 n (chunk_class n) cnt v jb (rz_log n) DP odd z W
  (mkCfg (mkst regs' (getr regs0 1) (FSP.unpoison Up mem') (seg_rom im_segs))
         (with_vm_backing (m_vm_lazy md0) mat md0)) /\
(forall s, FSP.in_ush Up s = true -> mem' (Z_to_bv 64 s) = mem0 (Z_to_bv 64 s)).
Proof.
intros B Up ly S W mem0 md0 inst n cnt v regs0 jb odd z tr DP regs' mem' mat ZON HARU Hn HVIEW Hwf Hjbv HRET Hodd.
pose proof (FSP.ARU_ARm im_segs B ly S Up W mem0 md0 HARU) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (from_primary_64512 n ltac:(lia)) as FP.
pose proof (primary_geometry n ltac:(lia) FP) as (PG1 & PG2 & PG3 & PG4 & PG5).
pose proof HVIEW as [_ _ _ HCNT [HV0 [HV2 HVS]] _ _ _ _ _ _ HSH].
pose proof ASAN_CEIL_range as [CR _].
pose proof (Kv_bounds ly (chunk_class n) v LO PG1 HV0 HVS PG5) as (KB1 & KB2 & KB8).
pose proof (shadow_window ly n (chunk_class n) v LO Hn eq_refl HV0 HVS)
  as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6 & SW7 & SW8 & SW9).
pose proof (lo_stk_ceil ly LO) as STKC.
assert (SHOFF : forall s, SKv ly (chunk_class n) v <= s < SKv ly (chunk_class n) v + class_size (chunk_class n) / 8 ->
  off_ush Up s).
{ intros s Hs. destruct (HSH s Hs) as [P1 P2]. exact (val250_off_ush im_segs Up W mem0 s (proj1 P1) P2). }
assert (OFFHIGH : forall a, Kv ly (chunk_class n) v <= a < Kv ly (chunk_class n) v + class_size (chunk_class n) ->
  off_ush Up a).
{ intros a Ha. apply (high_off_ush im_segs B ly S Up W mem0 md0 a HARU). unfold kHighMemBeg, ASAN_CEIL in *. lia. }
assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem0 md0 a HARU Ha)).
assert (OFFZ : forall a, ag_dzone ly a -> off_ush Up a)
  by (intros a Ha; exact (zone_off B Up ly S W mem0 md0 a ZON HARU (or_introl Ha))).
assert (PBOFF : n mod 8 <> 0 -> off_ush Up (PBv ly n (chunk_class n) v (rz_log n))).
{ intros HO. apply SHOFF. rewrite <- SW1. apply pb_in; [|lia | exact (SW3 HO)].
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in SW7 as [a Ha]; [|lia].
  apply Z.mod_divide in SW8 as [b Hb]; [|lia]. exists (a + b). lia. }
assert (SUOFF : forall s, SUv ly (chunk_class n) v (rz_log n) <= s <
   SUv ly (chunk_class n) v (rz_log n) + N8D n / 8 -> off_ush Up s).
{ intros s Hs. apply SHOFF. rewrite <- SW2 in Hs.
  exact (win_sub _ _ _ _ SW7 SW8 ltac:(lia) SW9 SW4 s Hs). }
destruct HRET as (EW & regs'' & mem'' & mat'' & Ecfg & R10 & RREGS & RDEP & RFRAME & RSTK & RPRES & RVALS).
assert (Emem : mem' = mem'')
  by (apply (f_equal (fun c => ms_mem (cfg_ms c))) in Ecfg; cbn in Ecfg; exact Ecfg).
assert (Eregs : regs' = regs'')
  by (apply (f_equal (fun c => ms_regs (cfg_ms c))) in Ecfg; cbn in Ecfg; exact Ecfg).
subst mem'' regs''.
cbv zeta in RVALS.
destruct RVALS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
split; [exact (wframe_unpoison W ly regs0 mem0 tr Up Hwf)|].
split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem0 _ _ _ _) Hjbv); intros k Hk; apply OFFHIGH; lia|].
split.
{ split; [exact EW|]. exists regs', (FSP.unpoison Up mem'), mat. split; [reflexivity|].
  split; [exact R10|]. split; [exact RREGS|].
  split.
  { destruct RDEP as (memD & D1 & D2 & D3). exists memD. split; [exact D1|]. split.
    - intros a Ha HP0. exact (D2 a Ha (apresent_unpoison_bwd (w_H W) Up mem0 a (OFFZ a Ha) HP0)).
    - intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFZ _ Hx))). exact (D3 x Hx). }
  split; [intros x H1 H2 H3 H4; exact (unpoison_eq Up mem0 mem' x (RFRAME x H1 H2 H3 H4))|].
  split; [intros a Ha; exact (apresent_unpoison_fwd (w_H W) Up mem' a (RSTK a Ha))|].
  split; [intros a Ha; exact (apresent_unpoison_fwd (w_H W) Up mem' a (RPRES a Ha))|].
  cbv zeta.
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A1); intros k Hk; apply OFFHIGH; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A2); intros k Hk; apply OFFHIGH; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A3); intros k Hk; apply OFFHIGH; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A4); intros k Hk; apply OFFHIGH; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A5); intros k Hk; apply OFFHIGH; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A6); intros k Hk; apply OFFHIGH; lia|].
  split; [exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (Pv ly (chunk_class n)) 4 _
            ltac:(intros k Hk; apply OFFT; unfold Pv, t_cache, kThreadObjSize in *; lia)) A7)|].
  split; [exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (ly_T ly + t_unwinding) 1 _
            ltac:(intros k Hk; apply OFFT; unfold t_unwinding, kThreadObjSize in *; lia)) A8)|].
  split.
  { intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush Up (bv_unsigned x)); [reflexivity | exact (A9 x Hx)]. }
  intros Eodd. exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (PBv ly n (chunk_class n) v (rz_log n)) 1 _
    ltac:(intros k Hk; replace (PBv ly n (chunk_class n) v (rz_log n) + k)
            with (PBv ly n (chunk_class n) v (rz_log n)) by lia;
          exact (PBOFF (proj1 Hodd Eodd)))) (A10 Eodd)). }
(* Up's shadow bytes lie outside every window the post writes. *)
intros s Hs.
pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (UB1 & UB2 & SR).
pose proof (ush_not_off Up s Hs SR) as NO.
apply (RFRAME (Z_to_bv 64 s)); rewrite (wz64 s SR).
- intros HW. unfold WIN in HW. destruct HW as [HW|[HW|[HW|HW]]].
  + destruct Hwf as ((Fsp & _) & _). unfold AFSTACK, ASAN_CEIL, kHighMemBeg in *. lia.
  + apply NO, OFFT. unfold WINT, Pv, SSLOTv in HW. unfold t_cache, t_stats, t_unwinding, kThreadObjSize in *.
    destruct HW as [HW|[HW|[HW|HW]]]; lia.
  + unfold Uv in HW. unfold kHighMemBeg in *. lia.
  + destruct HW as [Eodd HW]. apply NO.
    replace s with (PBv ly n (chunk_class n) v (rz_log n)) by lia. exact (PBOFF (proj1 Hodd Eodd)).
- intros HD. exact (NO (OFFZ s HD)).
- unfold kHighMemBeg in *. lia.
- intros HU. exact (NO (SUOFF s HU)).
Qed.

(* The k path's twin, over K6's geometry (redzone 16, header size K6.NPv n). *)
Lemma post_k_core : forall B Up ly S W mem0 md0 inst n cnt v regs0 jb odd z tr
(DP : Z -> (word -> option byte) -> Prop) regs' mem' mat,
zones_free im_segs B ag_dzone ag_czone ->
FSP.ARU im_segs B ly S Up W mem0 md0 ->
0 <= n <= 48 ->
hview B W ly inst (FSP.unpoison Up mem0) (chunk_class n) cnt v ->
wframe W ly regs0 mem0 tr ->
val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) v + K6.RZ - 15) 1 jb ->
at_RETkw W ly regs0 mem0 md0 n (chunk_class n) cnt v jb DP odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> K6.NPv n mod 8 <> 0) ->
wframe W ly regs0 (FSP.unpoison Up mem0) tr /\
val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem0)) (K6.Kv ly (chunk_class n) v + K6.RZ - 15) 1 jb /\
at_RETkw W ly regs0 (FSP.unpoison Up mem0) md0 n (chunk_class n) cnt v jb DP odd z W
  (mkCfg (mkst regs' (getr regs0 1) (FSP.unpoison Up mem') (seg_rom im_segs))
         (with_vm_backing (m_vm_lazy md0) mat md0)) /\
(forall s, FSP.in_ush Up s = true -> mem' (Z_to_bv 64 s) = mem0 (Z_to_bv 64 s)).
Proof.
intros B Up ly S W mem0 md0 inst n cnt v regs0 jb odd z tr DP regs' mem' mat ZON HARU Hn HVIEW Hwf Hjbv HRET Hodd.
pose proof (FSP.ARU_ARm im_segs B ly S Up W mem0 md0 HARU) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (from_primary_64512 n ltac:(lia)) as FP.
pose proof (primary_geometry n ltac:(lia) FP) as (PG1 & PG2 & PG3 & PG4 & PG5).
pose proof HVIEW as [_ _ _ HCNT [HV0 [HV2 HVS]] _ _ _ _ _ _ HSH].
pose proof ASAN_CEIL_range as [CR _].
pose proof (Kv_bounds ly (chunk_class n) v LO PG1 HV0 HVS PG5) as (KB1 & KB2 & KB8).
pose proof (shadow_window_k ly n (chunk_class n) v LO Hn eq_refl HV0 HVS)
  as (SW1 & SW2 & SW3 & SW4 & SW5 & SW8 & SW9 & NP1).
pose proof (lo_stk_ceil ly LO) as STKC.
assert (EK : K6.Kv ly (chunk_class n) v = Kv ly (chunk_class n) v) by reflexivity.
assert (SHOFF : forall s, SKv ly (chunk_class n) v <= s < SKv ly (chunk_class n) v + class_size (chunk_class n) / 8 ->
  off_ush Up s).
{ intros s Hs. destruct (HSH s Hs) as [P1 P2]. exact (val250_off_ush im_segs Up W mem0 s (proj1 P1) P2). }
assert (OFFHIGH : forall a, K6.Kv ly (chunk_class n) v <= a < K6.Kv ly (chunk_class n) v + class_size (chunk_class n) ->
  off_ush Up a).
{ intros a Ha. rewrite EK in Ha. apply (high_off_ush im_segs B ly S Up W mem0 md0 a HARU).
  unfold kHighMemBeg, ASAN_CEIL in *. lia. }
assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem0 md0 a HARU Ha)).
assert (OFFZ : forall a, ag_dzone ly a -> off_ush Up a)
  by (intros a Ha; exact (zone_off B Up ly S W mem0 md0 a ZON HARU (or_introl Ha))).
assert (PBOFF : K6.NPv n mod 8 <> 0 -> off_ush Up (K6.PBv ly n (chunk_class n) v)).
{ intros HO. apply SHOFF. rewrite <- SW1. apply pb_in; [|unfold K6.RZ; lia | exact (SW3 HO)].
  unfold K6.RZ. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SW8 as [b Hb]; [|lia]. exists (2 + b). lia. }
assert (SUOFF : forall s, K6.SUv ly (chunk_class n) v <= s < K6.SUv ly (chunk_class n) v + K6.N8D n / 8 ->
  off_ush Up s).
{ intros s Hs. apply SHOFF. rewrite <- SW2 in Hs.
  exact (win_sub (SKv ly (chunk_class n) v) K6.RZ (K6.N8D n) (class_size (chunk_class n)) eq_refl SW8
    ltac:(unfold K6.RZ; lia) SW9 SW4 s Hs). }
destruct HRET as (EW & regs'' & mem'' & mat'' & Ecfg & R10 & RREGS & RDEP & RFRAME & RSTK & RPRES & RVALS).
assert (Emem : mem' = mem'')
  by (apply (f_equal (fun c => ms_mem (cfg_ms c))) in Ecfg; cbn in Ecfg; exact Ecfg).
assert (Eregs : regs' = regs'')
  by (apply (f_equal (fun c => ms_regs (cfg_ms c))) in Ecfg; cbn in Ecfg; exact Ecfg).
subst mem'' regs''.
cbv zeta in RVALS.
destruct RVALS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
split; [exact (wframe_unpoison W ly regs0 mem0 tr Up Hwf)|].
split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem0 _ _ _ _) Hjbv); intros k Hk; apply OFFHIGH;
        unfold K6.RZ in *; lia|].
split.
{ split; [exact EW|]. exists regs', (FSP.unpoison Up mem'), mat. split; [reflexivity|].
  split; [exact R10|]. split; [exact RREGS|].
  split.
  { destruct RDEP as (memD & D1 & D2 & D3). exists memD. split; [exact D1|]. split.
    - intros a Ha HP0. exact (D2 a Ha (apresent_unpoison_bwd (w_H W) Up mem0 a (OFFZ a Ha) HP0)).
    - intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFZ _ Hx))). exact (D3 x Hx). }
  split; [intros x H1 H2 H3 H4; exact (unpoison_eq Up mem0 mem' x (RFRAME x H1 H2 H3 H4))|].
  split; [intros a Ha; exact (apresent_unpoison_fwd (w_H W) Up mem' a (RSTK a Ha))|].
  split; [intros a Ha; exact (apresent_unpoison_fwd (w_H W) Up mem' a (RPRES a Ha))|].
  cbv zeta.
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A1); intros k Hk; apply OFFHIGH;
          unfold K6.RZ in *; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A2); intros k Hk; apply OFFHIGH;
          unfold K6.RZ in *; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A3); intros k Hk; apply OFFHIGH;
          unfold K6.RZ in *; lia|].
  split; [refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ _ _ _) A4); intros k Hk; apply OFFHIGH;
          unfold K6.RZ in *; lia|].
  split; [exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (K6.Pv ly (chunk_class n)) 4 _
            ltac:(intros k Hk; apply OFFT; unfold K6.Pv, t_cache, kThreadObjSize in *; lia)) A5)|].
  split; [exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (ly_T ly + t_unwinding) 1 _
            ltac:(intros k Hk; apply OFFT; unfold t_unwinding, kThreadObjSize in *; lia)) A6)|].
  split.
  { intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush Up (bv_unsigned x)); [reflexivity | exact (A7 x Hx)]. }
  intros Eodd. exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (K6.PBv ly n (chunk_class n) v) 1 _
    ltac:(intros k Hk; replace (K6.PBv ly n (chunk_class n) v + k) with (K6.PBv ly n (chunk_class n) v) by lia;
          exact (PBOFF (proj1 Hodd Eodd)))) (A8 Eodd)). }
intros s Hs.
pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (UB1 & UB2 & SR).
pose proof (ush_not_off Up s Hs SR) as NO.
apply (RFRAME (Z_to_bv 64 s)); rewrite (wz64 s SR).
- intros HW. unfold K6.WIN in HW. destruct HW as [HW|[HW|[HW|HW]]].
  + destruct Hwf as ((Fsp & _) & _). unfold AFSTACK, ASAN_CEIL, kHighMemBeg in *. lia.
  + apply NO, OFFT. unfold K6.WINT, K6.Pv, K6.SSLOTv in HW. unfold t_cache, t_stats, t_unwinding, kThreadObjSize in *.
    destruct HW as [HW|[HW|[HW|HW]]]; lia.
  + unfold K6.Uv, K6.RZ in HW. rewrite EK in HW. unfold kHighMemBeg in *. lia.
  + destruct HW as [Eodd HW]. apply NO.
    replace s with (K6.PBv ly n (chunk_class n) v) by lia. exact (PBOFF (proj1 Hodd Eodd)).
- intros HD. exact (NO (OFFZ s HD)).
- rewrite EK. unfold K6.RZ. unfold kHighMemBeg in *. lia.
- intros HU. exact (NO (SUOFF s HU)).
Qed.

(* ARU at the post state Xf of a cache pop of X: AR there over the unpoisoned post memory (the AR side's post
   field), every live block of X still live (the popped chunk is not one of them: its offset is a cache entry, so no
   chunk of X begins there), and Up's shadow bytes unchanged. *)
Lemma rebuild_view : forall B Up ly X W mem0 md0 Xf mem' md' n l off inst cnt,
FSP.ARU im_segs B ly X Up W mem0 md0 ->
AR im_segs B ly Xf W (FSP.unpoison Up mem') md' ->
0 <= n -> from_primary n = true ->
pc_chunks (cache X (chunk_class n)) = l ++ [off] ->
off mod 32 = 0 -> hview B W ly inst (FSP.unpoison Up mem0) (chunk_class n) cnt (off / 16) ->
st_chunks Xf = upd_chunk (st_chunks X) (new_chunk (chunk_class n) off n) ->
(forall s, FSP.in_ush Up s = true -> mem' (Z_to_bv 64 s) = mem0 (Z_to_bv 64 s)) ->
FSP.ARU im_segs B ly Xf Up W mem' md'.
Proof.
intros B Up ly X W mem0 md0 Xf mem' md' n l off inst cnt HARU HAR Hn Hfp Hcache Hoff32 HVIEW ECH RAW.
pose proof (FSP.ARU_ARm im_segs B ly X Up W mem0 md0 HARU) as M.
pose proof (primary_geometry n Hn Hfp) as (PG1 & _ & _ & _ & PG5).
pose proof HVIEW as [_ _ _ _ [HV0 [_ HVS]] _ _ _ _ _ _ _].
pose proof (off_range off Hoff32 HV0 HVS) as OFFR.
assert (NOBEG : forall k, In k (st_chunks X) -> ck_beg k <> PPrim (region_off (chunk_class n) + off)).
{ intros k Hk Ebeg.
  pose proof (wf_classes (as_universe B) 0 0 0 X (am_wf B ly X _ M) (chunk_class n) ltac:(lia)) as WC.
  unfold wf_class in WC. pose proof (wr_nodup _ _ _ _ _ _ WC) as ND.
  assert (INP : In off (pc_chunks (cache X (chunk_class n))))
    by (rewrite Hcache; apply in_or_app; right; left; reflexivity).
  assert (INC : In off (chunk_offs X (chunk_class n))).
  { unfold chunk_offs. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Ebeg.
    rewrite (prim_class_region (chunk_class n) off OFFR), Z.eqb_refl. cbn [In]. left. lia. }
  exact (nodup_app_notin _ _ off (NoDup_app_remove_l _ _ ND) INP
    (in_or_app (chunk_offs X (chunk_class n)) (batch_offs X (chunk_class n)) off (or_introl INC))). }
apply (ARU_rebuild_raw im_segs B ly X Up W mem0 md0 ly Xf mem' md' HARU HAR); [|exact RAW].
intros r p m _ Hin _ _. unfold ablocks in *. apply in_map_iff in Hin as ([q mm] & Eq & Hin2).
unfold blocks in Hin2. apply in_map_iff in Hin2 as (k & Ek & Hk). apply filter_In in Hk as [Hk Hal].
apply in_map_iff. exists (q, mm). split; [exact Eq|]. unfold blocks. apply in_map_iff. exists k.
split; [exact Ek|]. apply filter_In. split; [|exact Hal]. rewrite ECH.
apply upd_chunk_keeps; [exact Hk|]. cbn [new_chunk ck_beg]. exact (NOBEG k Hk).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The callee contract of AIfaceM (kind 5): AGif0n.v:284-299's if_refill, text unchanged, as a premise.          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition if_refill_t (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (lpost : astate -> Prop) (rtree : Z -> M unit) : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
    ARX inst ly S0 W mem0 md0 -> rpre S0 n -> 0 <= n -> from_primary n = true ->
    pc_chunks (cache S0 (chunk_class n)) = [] ->
    ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
    (* the raw frame: ARX reads raw memory at hidden in-band bytes, which aview does not see; the seed writes the
       thread's unwinding byte outside the scratch window *)
    (forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
       mem x = mem0 x) ->
    (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
    spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
    getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
    getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
    amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
      (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (rleaf ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The records.                                                                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Theorem aiface_U : forall B U mt rpre nmax lmax lpost dpost mtag stag I Up,
inst_low ag_inst_ok -> zones_free im_segs B ag_dzone ag_czone ->
AIface B U mt (ARX_AR im_segs B I) (aowned B) rpre nmax lmax lpost dpost mtag stag ->
AIface B U mt (ARX_ARU im_segs B I Up) (aowned B) rpre nmax lmax lpost dpost mtag stag.
Proof.
intros B U mt rpre nmax lmax lpost dpost mtag stag I Up ILOW ZON [HI HV HSh HDe HDa HPo HOw HUn].
constructor.
- (* if_inst (kind 1) *)
  intros inst ly S W mem md H. exact (HI inst ly S W _ md (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* if_view (kind 2) *)
  intros inst ly S W mem md n l off H Hr Hn Hfp Hinit Hc.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly S W mem md H) as HA.
  destruct (HV inst ly S W _ md n l off HA Hr Hn Hfp Hinit Hc) as [Ho Hv].
  split; [exact Ho|].
  pose proof (primary_geometry n Hn Hfp) as (PG1 & _ & _ & _ & PG5).
  exact (hview_back B Up ly S W mem md inst _ _ _ ILOW (HI _ _ _ _ _ _ HA) (proj2 H) PG1 PG5 Hv).
- (* if_shape (no ARX) *)
  exact HSh.
- (* if_depot (kind 3) *)
  intros inst ly S W mem0 md0 tr regs mem md buf H HU HZ.
  refine (HDe inst ly S W _ md0 tr regs mem md buf (ARX_ARU_AR im_segs B I Up inst ly S W mem0 md0 H) HU _).
  intros x Hx.
  rewrite (FSP.unpoison_out Up mem0 x (off_ush_w Up x (zone_off B Up ly S W mem0 md0 _ ZON (proj2 H) Hx))).
  exact (HZ x Hx).
- (* if_dpost_aok (no ARX) *)
  exact HDa.
- (* if_post (kind 4) *)
  intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat H Hrpre Hnmax Hlmax HU Hn Hinit Hcache
    Hwf Hjb Hjbv HRET Hodd Hpath.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly S W mem0 md0 H) as HA.
  pose proof (from_primary_64512 n ltac:(lia)) as FP.
  destruct (HV inst ly S W _ md0 n l off HA Hrpre ltac:(lia) FP Hinit Hcache) as [Hoff32 HVIEW].
  destruct (post_g_core B Up ly S W mem0 md0 inst n _ _ regs0 jb odd z tr _ regs' mem' mat ZON (proj2 H) Hn
    HVIEW Hwf Hjbv HRET Hodd) as (HWF' & HJB' & HRET' & RAW).
  destruct (HPo inst ly S W _ md0 n tr l off regs0 jb odd z regs' _ mat HA Hrpre Hnmax Hlmax HU Hn Hinit Hcache
    HWF' Hjb HJB' HRET' Hodd Hpath) as [[E HARp] Hlp].
  split; [|exact Hlp]. split; [exact E|].
  exact (rebuild_view B Up ly S W mem0 md0 _ mem' _ n l off inst _ (proj2 H) HARp ltac:(lia) FP Hcache Hoff32
    HVIEW (st_final_chunks _ _ _ _ _ _ _) RAW).
- (* if_owned (kind 1) *)
  intros inst ly S W mem md n l off odd a H.
  exact (HOw inst ly S W _ md n l off odd a (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* if_uninit (kind 1) *)
  intros inst ly S W mem md c H. exact (HUn inst ly S W _ md c (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
Qed.

Theorem aifaceK_U : forall B U mt rpre nmax lmax lpost dpost mtag stag I Up,
inst_low ag_inst_ok -> zones_free im_segs B ag_dzone ag_czone ->
AIface B U mt (ARX_AR im_segs B I) (aowned B) rpre nmax lmax lpost dpost mtag stag ->
AIfaceK B U mt (ARX_AR im_segs B I) (aowned B) rpre nmax lmax lpost dpost mtag stag ->
AIfaceK B U mt (ARX_ARU im_segs B I Up) (aowned B) rpre nmax lmax lpost dpost mtag stag.
Proof.
intros B U mt rpre nmax lmax lpost dpost mtag stag I Up ILOW ZON HA0 [HPk HOk].
destruct HA0 as [_ HV _ _ _ _ _ _].
constructor.
- (* if_post_k (kind 4; the pre-state's view from AIface.if_view) *)
  intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat H Hrpre Hnmax Hlmax HU Hn Hinit Hcache
    Hwf Hjb Hjbv HRET Hodd Hpath.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly S W mem0 md0 H) as HA.
  pose proof (from_primary_64512 n ltac:(lia)) as FP.
  destruct (HV inst ly S W _ md0 n l off HA Hrpre ltac:(lia) FP Hinit Hcache) as [Hoff32 HVIEW].
  destruct (post_k_core B Up ly S W mem0 md0 inst n _ _ regs0 jb odd z tr _ regs' mem' mat ZON (proj2 H) Hn
    HVIEW Hwf Hjbv HRET Hodd) as (HWF' & HJB' & HRET' & RAW).
  destruct (HPk inst ly S W _ md0 n tr l off regs0 jb odd z regs' _ mat HA Hrpre Hnmax Hlmax HU Hn Hinit Hcache
    HWF' Hjb HJB' HRET' Hodd Hpath) as [[E HARp] Hlp].
  split; [|exact Hlp]. split; [exact E|].
  exact (rebuild_view B Up ly S W mem0 md0 _ mem' _ n l off inst _ (proj2 H) HARp ltac:(lia) FP Hcache Hoff32
    HVIEW (st_final_chunks _ _ _ _ _ _ _) RAW).
- (* if_owned_k (kind 1) *)
  intros inst ly S W mem md n l off odd a H.
  exact (HOk inst ly S W _ md n l off odd a (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
Qed.

Theorem ifaceM_U : forall B U mt rpre nmax lmax lpost dpost mtag stag rtree I Up,
inst_low ag_inst_ok -> zones_free im_segs B ag_dzone ag_czone -> img_low ->
ag_inst_ok I ->
AIfaceM B U mt (ARX_AR im_segs B I) (aowned B) rpre nmax lmax lpost dpost mtag stag rtree ->
if_refill_t B (ARX_ARU im_segs B I Up) (aowned B) rpre lpost rtree ->
AIfaceM B U mt (ARX_ARU im_segs B I Up) (aowned B) rpre nmax lmax lpost dpost mtag stag rtree.
Proof.
intros B U mt rpre nmax lmax lpost dpost mtag stag rtree I Up ILOW ZON IMGL IOK
  [HMv HShm _ HPm HPmk HDm HOo HSt HVm HOm HOmk HMj] HREF.
constructor.
- (* if_mview (kind 2) *)
  intros inst ly S W mem md n H Hn Hfp Hc.
  pose proof (HMv inst ly S W _ md n (ARX_ARU_AR im_segs B I Up inst ly S W mem md H) Hn Hfp Hc) as MV.
  pose proof (primary_geometry n Hn Hfp) as (PG1 & _).
  assert (Hok : ag_inst_ok inst) by (rewrite (proj1 H); exact IOK).
  exact (mview_back B Up ly S W mem md inst _ ILOW Hok (proj2 H) PG1 MV).
- (* if_shape_miss (no ARX) *)
  exact HShm.
- (* if_refill (kind 5: the premise) *)
  exact HREF.
- (* if_post_miss (kind 4 at the pop state Sp; the entry state S0 is only taken) *)
  intros inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat H0 Hrpre Hlmax0 H
    Hnmax Hlmax HU Hn Hinit Hcache Hwf Hjb Hjbv HRET Hodd Hpath.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly0 S0 W0 mem00 md00 H0) as HA0.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly Sp W mem0 md0 H) as HA.
  pose proof (from_primary_64512 n ltac:(lia)) as FP.
  destruct (HVm inst ly Sp W _ md0 n l off HA ltac:(lia) FP Hinit Hcache) as [Hoff32 HVIEW].
  destruct (post_g_core B Up ly Sp W mem0 md0 inst n _ _ regs0 jb odd z tr _ regs' mem' mat ZON (proj2 H) Hn
    HVIEW Hwf Hjbv HRET Hodd) as (HWF' & HJB' & HRET' & RAW).
  destruct (HPm inst ly ly0 S0 Sp W0 _ md00 W _ md0 n tr l off regs0 jb odd z regs' _ mat HA0 Hrpre Hlmax0 HA
    Hnmax Hlmax HU Hn Hinit Hcache HWF' Hjb HJB' HRET' Hodd Hpath) as [[E HARp] Hlp].
  split; [|exact Hlp]. split; [exact E|].
  exact (rebuild_view B Up ly Sp W mem0 md0 _ mem' _ n l off inst _ (proj2 H) HARp ltac:(lia) FP Hcache Hoff32
    HVIEW (st_final_chunks _ _ _ _ _ _ _) RAW).
- (* if_post_miss_k (kind 4, k geometry, at Sp) *)
  intros inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat H0 Hrpre Hlmax0 H
    Hnmax Hlmax HU Hn Hinit Hcache Hwf Hjb Hjbv HRET Hodd Hpath.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly0 S0 W0 mem00 md00 H0) as HA0.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly Sp W mem0 md0 H) as HA.
  pose proof (from_primary_64512 n ltac:(lia)) as FP.
  destruct (HVm inst ly Sp W _ md0 n l off HA ltac:(lia) FP Hinit Hcache) as [Hoff32 HVIEW].
  destruct (post_k_core B Up ly Sp W mem0 md0 inst n _ _ regs0 jb odd z tr _ regs' mem' mat ZON (proj2 H) Hn
    HVIEW Hwf Hjbv HRET Hodd) as (HWF' & HJB' & HRET' & RAW).
  destruct (HPmk inst ly ly0 S0 Sp W0 _ md00 W _ md0 n tr l off regs0 jb odd z regs' _ mat HA0 Hrpre Hlmax0 HA
    Hnmax Hlmax HU Hn Hinit Hcache HWF' Hjb HJB' HRET' Hodd Hpath) as [[E HARp] Hlp].
  split; [|exact Hlp]. split; [exact E|].
  exact (rebuild_view B Up ly Sp W mem0 md0 _ mem' _ n l off inst _ (proj2 H) HARp ltac:(lia) FP Hcache Hoff32
    HVIEW (st_final_chunks _ _ _ _ _ _ _) RAW).
- (* if_depot_miss (kind 3, zones at Sp) *)
  intros inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr regs mem md buf H0 HU H HZ.
  refine (HDm inst ly ly0 S0 Sp W0 _ md00 W _ md0 tr regs mem md buf
    (ARX_ARU_AR im_segs B I Up inst ly0 S0 W0 mem00 md00 H0) HU
    (ARX_ARU_AR im_segs B I Up inst ly Sp W mem0 md0 H) _).
  intros x Hx.
  rewrite (FSP.unpoison_out Up mem0 x (off_ush_w Up x (zone_off B Up ly Sp W mem0 md0 _ ZON (proj2 H) Hx))).
  exact (HZ x Hx).
- (* if_oom (frames move pointwise; im_oom / errno off Up by img_low; Up's bytes outside every written cell) *)
  intros inst ly S0 Sp W mem md n tr sp0 mem' md' H Hl Hc HV HR HP HP' Hlo Hhi Hoom Hio Hvm Hlz Hpath.
  pose proof (ARX_ARU_AR im_segs B I Up inst ly Sp W mem md H) as HA.
  destruct H as [E HARU].
  destruct IMGL as [[O1 O2] [E1 E2]].
  pose proof (low_off_ush im_segs B ly Sp Up W mem md im_oom HARU (conj O1 O2)) as OOMOFF.
  assert (Hoom' : val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem')) im_oom 1 1).
  { apply (val_mem_unpoison im_segs (w_H W) Up mem' im_oom 1 1); [|exact Hoom].
    intros k Hk. replace (im_oom + k) with im_oom by lia. exact OOMOFF. }
  destruct (HOo inst ly S0 Sp W _ md n tr sp0 (FSP.unpoison Up mem') md' HA Hl Hc
    (fun a Ha H1 H2 H3 => aview_unpoison_eq im_segs (w_H W) Up mem mem' a (HV a Ha H1 H2 H3))
    (fun x H1 H2 H3 => unpoison_eq Up mem mem' x (HR x H1 H2 H3))
    (fun a Ha => apresent_unpoison_fwd (w_H W) Up mem a (HP a Ha))
    (fun a Ha => apresent_unpoison_fwd (w_H W) Up mem' a (HP' a Ha))
    Hlo Hhi Hoom' Hio Hvm Hlz Hpath) as ([_ HARp] & Hlp & Ho1 & Ho2).
  split; [|split; [exact Hlp | split; [exact Ho1 | exact Ho2]]].
  split; [exact E|].
  apply (ARU_rebuild_raw im_segs B ly Sp Up W mem md ly Sp mem' md' HARU HARp).
  + intros r p m _ Hb _ _. exact Hb.
  + intros s Hs.
    pose proof (ush_band im_segs B ly Sp Up W mem md s HARU Hs) as (UB1 & UB2 & SR).
    pose proof (FSP.stk_kHighMemBeg B ly Sp _ (FSP.ARU_ARm im_segs B ly Sp Up W mem md HARU)) as [K1 K2].
    apply HR; rewrite (wz64 s SR); [unfold AFSTACK, kHighMemBeg in *; lia | lia | lia].
- (* if_stack (kind 1) *)
  intros inst ly S W mem md a H. exact (HSt inst ly S W _ md a (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* if_view_m (kind 2) *)
  intros inst ly S W mem md n l off H Hn Hfp Hinit Hc.
  destruct (HVm inst ly S W _ md n l off (ARX_ARU_AR im_segs B I Up inst ly S W mem md H) Hn Hfp Hinit Hc)
    as [Ho Hv].
  split; [exact Ho|].
  pose proof (primary_geometry n Hn Hfp) as (PG1 & _ & _ & _ & PG5).
  assert (Hok : ag_inst_ok inst) by (rewrite (proj1 H); exact IOK).
  exact (hview_back B Up ly S W mem md inst _ _ _ ILOW Hok (proj2 H) PG1 PG5 Hv).
- (* if_owned_m (kind 1) *)
  intros inst ly S W mem md n l off odd a H.
  exact (HOm inst ly S W _ md n l off odd a (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* if_owned_m_k (kind 1) *)
  intros inst ly S W mem md n l off odd a H.
  exact (HOmk inst ly S W _ md n l off odd a (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* if_mono_join (kind 1) *)
  intros inst ly Sp W mem md n l off tr z a H.
  exact (HMj inst ly Sp W _ md n l off tr z a (ARX_ARU_AR im_segs B I Up inst ly Sp W mem md H)).
Qed.

End a.
