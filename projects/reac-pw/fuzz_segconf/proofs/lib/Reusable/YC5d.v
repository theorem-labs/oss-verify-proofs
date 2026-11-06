(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC5d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: amalloc04_rule, afree04_rule and afree_null04_rule no longer take In (call_trace0 ...) (as_universe B); st_nev Sc < EV_MAX admits any trace. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Record ameter_ops : Type := mkAMeter {
mo_ok : astate -> Z -> Prop;
mo_le : astate -> astate -> Z -> Prop;
mo_malloc : Z -> Z;
mo_free : Z }.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Record ameter_laws (MT : ameter_ops) : Prop := mkAMeterLaws {
mo_le_refl : forall s, mo_le MT s s 0;
mo_le_trans : forall s1 s2 s3 m1 m2, mo_le MT s1 s2 m1 -> mo_le MT s2 s3 m2 -> mo_le MT s1 s3 (m1 + m2);
mo_le_mono : forall s s' m m', mo_le MT s s' m -> m <= m' -> mo_le MT s s' m';
mo_ok_le : forall s m m', mo_ok MT s m' -> m <= m' -> mo_ok MT s m;
mo_ok_step : forall s s' m1 m2, mo_ok MT s (m1 + m2) -> mo_le MT s s' m1 -> mo_ok MT s' m2;
mo_malloc_nonneg : forall n, 0 <= n -> 0 <= mo_malloc MT n;
mo_malloc_mono : forall n n', 0 <= n <= n' -> mo_malloc MT n <= mo_malloc MT n';
mo_free_nonneg : 0 <= mo_free MT }.
Lemma mok_station : forall MT (Sc Sk : astate) (T acc c : Z),
ameter_laws MT -> mo_ok MT Sc T -> mo_le MT Sc Sk acc -> 0 <= c -> acc + c <= T -> mo_ok MT Sk c.
Proof.
intros MT Sc Sk T acc c ML HT HLE Hc Hle.
apply (mo_ok_step MT ML Sc Sk acc c); [|exact HLE]. apply (mo_ok_le MT ML Sc (acc + c) T HT Hle).
Qed.
Lemma mle_station : forall MT (Sc Sk Sk' : astate) (acc c : Z),
ameter_laws MT -> mo_le MT Sc Sk acc -> mo_le MT Sk Sk' c -> mo_le MT Sc Sk' (acc + c).
Proof. intros MT Sc Sk Sk' acc c ML H1 H2. exact (mo_le_trans MT ML _ _ _ _ _ H1 H2). Qed.
Lemma mle_weaken : forall MT (Sc Sk : astate) (acc acc' : Z),
ameter_laws MT -> mo_le MT Sc Sk acc -> acc <= acc' -> mo_le MT Sc Sk acc'.
Proof. intros MT Sc Sk acc acc' ML H Hle. exact (mo_le_mono MT ML _ _ _ _ H Hle). Qed.
Lemma mle_start : forall MT (Sc : astate), ameter_laws MT -> mo_le MT Sc Sc 0.
Proof. intros MT Sc ML. exact (mo_le_refl MT ML Sc). Qed.
Record ameter_fs_laws (MT : ameter_ops) : Prop := mkAMeterFsLaws {
mo_ok_set_fs : forall s f m, mo_ok MT s m -> mo_ok MT (set_fs f s) m;
mo_le_set_fs_r : forall s s' f m, mo_le MT s s' m -> mo_le MT s (set_fs f s') m;
mo_le_set_fs_l : forall s s' f m, mo_le MT (set_fs f s) s' m -> mo_le MT s s' m }.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation code := (as_code B).
Definition amalloc04_rule : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n)).
Definition afree04_rule : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT)).
Definition afree_null04_rule : Prop :=
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
frames S2 = frames Sc /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
mo_le MT Sc S2 (mo_free MT)).
End e.
End d.
End b.
