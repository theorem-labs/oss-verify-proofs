(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, as fuzz_grant's lib/A/Prog/GrantBase.v (origin/cold/pg-prog 4a980cd5011) and fuzz_identity's lib/A/Prog/IdentBase.v (origin/cold/port-libreac-identity ea5560a967b) carry it, with only the unit's module prefix changed, for libreac/fuzz_boxreg: the read-only range, the frame object and the shape of a call's post-condition. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxBase.v at origin/ossv/recipes ee71d1fd3fc
   for reac-pw/fuzz_role (image A and image B): module paths changed; its lines 17-45 (in_roP, arodata_okP,
   ro_below_ofl, ro_spares, arodata_ok_journalP) are taken as they stand; its lines 46-107 (afobj, apost_base,
   apost_baseF, fxr, apost_baseF_continue) are left out and replaced by the role definitions below (rl_fxk in place of
   fxr, for role's float registers; rl_wcell in place of afobj, for a cell that lies on the stack or in a side-stack
   frame); the role constants, the string predicate rl_cstr and the read-only cell predicate rl_ro_cells are new. *)
(* The image-independent definitions that the ASan-level contracts of reac-pw/fuzz_role's program functions
   (lib/A/RPgCSpec.v) are stated over. No image module is Required: every address is an argument.

   Why the float state appears here: role's program changes float registers. LLVMFuzzerTestOneInput loads fa0
   (flw, before the pod_nearest call); reac_role_prop_parse writes fa3, fa4 and fa5 (fld, fcvt.d.s, fadd.d) and
   accrues fflags; pod_nearest writes fa5 (fmv.w.x) and accrues fflags (feq.s, flt.s, fcvt.l.s, and the inexact flag
   of the soft-float addition it calls). A configuration of this semantics carries the float state in mkst, so a
   function that changes it returns at some other float state fx'. rl_fxk names what such a function keeps: every
   float register outside a given list, and a zero rounding mode (each of these functions runs with a zero rounding
   mode and writes no rounding mode). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model.
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

(* ======================================== role's shared quantities ======================================== *)
(* pp->len after pod_build of the bytes after the flags byte: the plain contract's role_len
   (lib/Prog/LLVMFuzzerTestOneInput_c.v), the length of the pod that LLVMFuzzerTestOneInput allocates. *)
Definition rl_len (rest : list byte) : Z := Z.of_nat (length (Model.buf (fst (Model.pod_build rest)))).

(* The texts the checks compare (fuzz_role.c, reac_role_cfg.c), as byte values without the NUL:
   "applied" (REAC_ROLE_STATE_APPLIED), "role_reestablish_pending" (REAC_ROLE_STATE_REESTABLISH_PENDING),
   "none" and "malformed" (codes[0] and codes[1] of reac_role_refuse_code). *)
Definition STR_APPLIED : list Z := [97; 112; 112; 108; 105; 101; 100].
Definition STR_PENDING : list Z :=
  [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110; 100; 105; 110; 103].
Definition STR_NONE : list Z := [110; 111; 110; 101].
Definition STR_MALFORMED : list Z := [109; 97; 108; 102; 111; 114; 109; 101; 100].

(* The float state a function returns at: every float register outside ks as at entry (Sem.reg_get, so f0 is
   covered too), and a zero rounding mode. *)
Definition rl_fxk (ks : list Z) (fx fx' : YK11.FPState) : Prop :=
(forall k : bv 5, ~ In (bv_unsigned k) ks -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
YK0o.frm_zero (@fp_csr fx').

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A NUL-terminated string s at a, as the strcmp wrapper's contract reads it: its bytes and the NUL, each nonzero
   before the NUL; it lies in the image, low enough for the shadow map, with its len + 1 bytes marked usable and
   their shadow bytes readable. *)
Definition rl_cstr (H : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs H mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s /\
0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> in_img segs (a + i)) /\
amem_range a (Z.of_nat (length s) + 1) /\
range_addressable (aview segs H mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview segs H mem) a (Z.of_nat (length s) + 1).
(* 8-byte cells of read-only data with their values (constants the code loads without a shadow check). *)
Definition rl_ro_cells (H : word -> bool) (mem : word -> option byte) (cs : list (Z * Z)) : Prop :=
Forall (fun c => val_mem segs (mrestrict H mem) (fst c) 8 (snd c)) cs.
End s.

(* A cell [q, q + n) that a callee with stack use T at sp may write for its caller: in the caller's stack window
   [sp0 - STK, sp0), or in one of the side-stack frames own the caller holds; and outside the callee's own stack
   [sp - T, sp). Both places are writable under the caller's journal (YCbq.v awr_byte). *)
Definition rl_wcell (STK sp0 : Z) (ly : alayout) (own : list (Z * Z)) (sp T q n : Z) : Prop :=
((sp0 - STK <= q /\ q + n <= sp0) \/
 (exists cid pos, In (cid, pos) own /\ 0 <= cid /\
  frame_addr ly cid pos <= q /\ q + n <= frame_addr ly cid pos + fs_frame_bytes cid)) /\
(sp <= q \/ q + n <= sp - T).

(* The bridge from a block made since the journal's start (in the current blocks blc, not in the start blocks bl0)
   to the journal's write right on each of its bytes (YCbq.v awr_byte, its in_tmp_block case): what the segment
   walks use for their writes to pp and pod, from rl_seg_pre's last conjunct and role_check_contract's pod premise. *)
Lemma rl_fresh_awr : forall STK sp0 FP bl0 blc ly own p n i,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 <= i < req_size n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n i Hin Hout Hi. right. right. left.
exists p, n. split; [exact Hin|]. split; [exact Hout|]. lia.
Qed.
Lemma rl_fresh_awr_n : forall STK sp0 FP bl0 blc ly own p n,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 < n ->
forall i, 0 <= i < n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n Hin Hout Hn i Hi. apply (rl_fresh_awr STK sp0 FP bl0 blc ly own p n i Hin Hout).
unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.

(* ================ the cut states of LLVMFuzzerTestOneInput, as data each image fills ================
   The two ASan images keep the harness's values in different registers and real-frame cells (image A keeps the
   input cursor at R+0xc8, image B in s4, ...), so a cut state is a list of (location, value) facts over the run's
   quantities rl_env. A location is a register or an 8-byte cell at a base plus an offset; a value is one of the
   quantities, an address made from pp, or a constant. The image's lists are measured from its code. *)
(* The run's quantities: S the entry sp; R the 32-aligned base of the real frame (R + its size <= S); F the frame
   for locals (a side-stack frame); pp and pod the two blocks; len = pp->len after the build (rl_len of the input
   after the flags byte); fl the flags byte; src and left the input cursor and the bytes left after the flags
   byte. *)
Record rl_env := RLEnv {
e_S : Z; e_R : Z; e_F : Z; e_pp : Z; e_pod : Z; e_len : Z; e_fl : Z; e_src : Z; e_left : Z }.
(* XShF is the shadow address of F, (F >> 3) + K with K the runtime's shadow offset (SHADOW_OFF); XPpShr c is
   (pp + c) >> 3, a shadow index before K is added; XLenNZ is the malloc request len + (len == 0). *)
Inductive rl_x :=
| XS | XR | XF | XShF | XPp (c : Z) | XPpShr (c : Z) | XPod | XLen | XLenNZ | XFl | XSrc | XLeft | XC (c : Z).
Definition rl_xv (e : rl_env) (x : rl_x) : Z :=
match x with
| XS => e_S e | XR => e_R e | XF => e_F e | XShF => shadow_addr (e_F e)
| XPp c => e_pp e + c | XPpShr c => Z.shiftr (e_pp e + c) 3 | XPod => e_pod e
| XLen => e_len e | XLenNZ => e_len e + (if e_len e =? 0 then 1 else 0)
| XFl => e_fl e | XSrc => e_src e | XLeft => e_left e | XC c => c
end.
Inductive rl_loc := LReg (r : Z) | LCell (b : rl_x) (off : Z).
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A register holds the 64-bit word of v; a cell holds its 8 little-endian bytes. *)
Definition rl_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rl_env)
(l : rl_loc) (v : Z) : Prop :=
match l with
| LReg r => getr regs (Z_to_bv 5 r) = w64 v
| LCell b o => val_mem segs (mrestrict H mem) (rl_xv e b + o) 8 (v mod 2 ^ 64)
end.
Definition rl_cut (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : rl_env)
(L : list (rl_loc * rl_x)) : Prop :=
Forall (fun f => rl_at H mem regs e (fst f) (rl_xv e (snd f))) L.
(* The shadow bytes of the frame for locals, from shadow_addr F on (one byte per 8-byte granule of F). *)
Definition rl_fsh (H : word -> bool) (mem : word -> option byte) (F : Z) (pat : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length pat) -> aview segs H mem (shadow_addr F + i) = Some (nth (Z.to_nat i) pat 0).
End u.
(* a lies in one of the ranges ws: (base, offset, length) -> [base + offset, base + offset + length). *)
Definition rl_inw (e : rl_env) (ws : list (rl_x * Z * Z)) (a : Z) : Prop :=
Exists (fun w => rl_xv e (fst (fst w)) + snd (fst w) <= a < rl_xv e (fst (fst w)) + snd (fst w) + snd w) ws.
