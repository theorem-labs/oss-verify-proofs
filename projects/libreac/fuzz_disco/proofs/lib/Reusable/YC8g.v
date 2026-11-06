(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC8g.v for libreac/fuzz_disco's asan-ubsan program walks, with its module paths changed; cgif_file's own program part (its stack, event and live constants, its object layouts tcgif_vals / traw_vals / tcgif_at, its function specs in Section o) and the Require of YI5w YI5z that only that part uses are dropped. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Variable segs : list Segment.
Definition afobj (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
p mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
Definition apost_base (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
(@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Lemma apost_base_same_fx : forall B STK FP regs ly S W mem md k Q W' c',
(exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md') ->
apost_base B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros B STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & H).
destruct H as (Hc & H). exists fx, ly', S', regs', mem', md'.
split; [exact Hc|]. split; [intros; reflexivity|]. split; [left; reflexivity | exact H].
Qed.
End l.
End j.
