(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, as fuzz_grant's lib/A/Prog/GrantBase.v (a working branch 4a980cd5011) and fuzz_identity's lib/A/Prog/IdentBase.v (a working branch ea5560a967b) carry it, with only the unit's module prefix changed, for libreac/fuzz_boxreg: the read-only range, the frame object and the shape of a call's post-condition. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxBase.v at origin/ossv/recipes ee71d1fd3fc
   for reac-pw/fuzz_role (image A and image B): module paths changed; its lines 17-45 (in_roP, arodata_okP,
   ro_below_ofl, ro_spares, arodata_ok_journalP) are taken as they stand; its lines 46-107 (afobj, apost_base,
   apost_baseF, fxr, apost_baseF_continue) are left out and replaced by the role definitions below (rl_fxk in place of
   fxr, for role's float registers; rl_wcell in place of afobj, for a cell that lies on the stack or in a side-stack
   frame); the role constants, the string predicate rl_cstr and the read-only cell predicate rl_ro_cells are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgBase.v at
   0de5d668c87 for reac-pw/fuzz_headamp (image A and image B): module paths changed and the rl_ prefix renamed to
   hd_. Lines 36-64 (in_roP, arodata_okP, ro_below_ofl, ro_spares, arodata_ok_journalP), the float predicate, the
   cell predicate, the two fresh-block bridges and the cut-state machinery are taken as they stand, renamed. What
   differs, because headamp's binary differs from role's:
   - role's four text constants (STR_APPLIED, STR_PENDING, STR_NONE, STR_MALFORMED) are left out: headamp's texts
     are already in the shared Pod model (Pod/Headamp.v HA_PREFIX, NAME_PHANTOM, NAME_PAD, NAME_SENS), and no second
     copy of them is made here; hd_zbytes turns such a list of bytes into the list of Z that hd_cstr reads.
   - hd_cstr asks `amem_range a (len + 8)` where role's rl_cstr asks `len + 1`, and adds the tail clause
     `hd_str_tail` (every byte after the NUL up to the end of its 8-byte word is readable). Headamp's parse calls
     the strncmp wrapper and the strtol wrapper, which role's program does not: both ask for the longer range and
     for the tail (reac-pw/fuzz_pin lib/A/PPgWrap.v awrap_str at ee62985a892;
     plugin-hostd/fuzz_command lib/A/Rt/RtNumber.v astrtol_realizes and lib/A/Rt/RtDefs.v atail_vis at
     2d2ff01bb6f2). `amem_range a (len + 8)` implies role's `amem_range a (len + 1)`
     (hd_amem_range_le), so every consumer of the role form is served.
   - the run's quantities (hd_env) are headamp's: four live blocks (pp, pod, out, first), the parse's answer rc, the
     cap and the null flag, in place of role's two blocks and its flags byte.
   - hd_x gains the constructors headamp's cut lists need (XF c for a cell of the frame for locals, XOut, XFirst,
     XCap, XCap3, XCap33, XNull, XNotNull, XProps, XRc, XRc3, XRc3NZ). *)
(* The image-independent definitions that the ASan-level contracts of reac-pw/fuzz_headamp's program functions
   (lib/A/HPgCSpec.v) are stated over. No image module is Required: every address is an argument.

   Why the float state appears here: headamp's program changes float registers. LLVMFuzzerTestOneInput sets fs1 and
   fs2 (fmv.w.x, the two binary32 bounds of the inlined pod_nearest; image B also fs3, fmv.w.x at B 0x830e0, the
   2^63 bound of its float-cast check), loads fs0 (flw, the cell value) and moves it to fa0 (fmv.s) for the
   soft-float call; reac_headamp_prop_parse_result writes fa4 and fa5 (fld, fcvt.d.s, fadd.d,
   fcvt.d.l) and saves and restores fs0; both accrue fflags and write no rounding mode. A configuration of this
   semantics carries the float state in mkst, so a function that changes it returns at some other float state fx'.
   hd_fxk names what such a function keeps: every float register outside a given list, and a zero rounding mode
   (each of these functions runs with a zero rounding mode and writes no rounding mode).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model.
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

(* ======================================== headamp's shared quantities ======================================== *)
(* pp->len after pod_build of the bytes after the two harness bytes: the plain contract's length of the pod the
   harness allocates (Pod/Model.v buf of the record pod_build makes). *)
Definition hd_len (rest : list byte) : Z := Z.of_nat (length (Model.buf (fst (Model.pod_build rest)))).

(* A list of bytes as the list of Z that hd_cstr reads (the texts are Pod/Headamp.v's: HA_PREFIX, NAME_PHANTOM,
   NAME_PAD, NAME_SENS). *)
Definition hd_zbytes (l : list byte) : list Z := map (fun b : byte => bv_unsigned b) l.

(* The float state a function returns at: every float register outside ks as at entry (Sem.reg_get, so f0 is
   covered too), and a zero rounding mode. *)
Definition hd_fxk (ks : list Z) (fx fx' : YK11.FPState) : Prop :=
(forall k : bv 5, ~ In (bv_unsigned k) ks -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
YK0o.frm_zero (@fp_csr fx').

(* amem_range is monotone in the length (fuzz_pin lib/A/PPgCSpec.v pin_amem_range_le): the longer range the
   strncmp and strtol wrappers ask for gives the shorter one the strlen and strcmp wrappers ask for. *)
Lemma hd_amem_range_le : forall p n m, n <= m -> amem_range p m -> amem_range p n.
Proof. intros p n m Hnm [H|[H1 H2]]; [left; lia | right; split; [exact H1 | lia]]. Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* Every byte after e up to the end of e's 8-byte word is readable: musl's word loops inside the strncmp, strtol
   and strcmp wrappers read the whole word that holds the byte they stop at (fuzz_command lib/A/Rt/RtDefs.v
   atail_vis). *)
Definition hd_str_tail (rd : reader) (e : Z) : Prop := forall a, e < a < e - e mod 8 + 8 -> rd a <> None.
(* A NUL-terminated string s at a, as the string wrappers' contracts read it: its bytes and the NUL, each nonzero
   before the NUL; it lies in the image, low enough for the shadow map, with its len + 1 bytes marked usable, their
   shadow bytes readable, the tail of the NUL's word readable, and len + 8 bytes of application memory range. *)
Definition hd_cstr (H : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs H mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s /\
0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> in_img segs (a + i)) /\
amem_range a (Z.of_nat (length s) + 8) /\
range_addressable (aview segs H mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview segs H mem) a (Z.of_nat (length s) + 1) /\
hd_str_tail (aview segs H mem) (a + Z.of_nat (length s)).
(* 8-byte cells of read-only data with their values (constants the code loads without a shadow check). *)
Definition hd_ro_cells (H : word -> bool) (mem : word -> option byte) (cs : list (Z * Z)) : Prop :=
Forall (fun c => val_mem segs (mrestrict H mem) (fst c) 8 (snd c)) cs.
End s.

(* A cell [q, q + n) that a callee with stack use T at sp may write for its caller: in the caller's stack window
   [sp0 - STK, sp0), or in one of the side-stack frames own the caller holds; and outside the callee's own stack
   [sp - T, sp). Both places are writable under the caller's journal (YCbq.v awr_byte). *)
Definition hd_wcell (STK sp0 : Z) (ly : alayout) (own : list (Z * Z)) (sp T q n : Z) : Prop :=
((sp0 - STK <= q /\ q + n <= sp0) \/
 (exists cid pos, In (cid, pos) own /\ 0 <= cid /\
  frame_addr ly cid pos <= q /\ q + n <= frame_addr ly cid pos + fs_frame_bytes cid)) /\
(sp <= q \/ q + n <= sp - T).

(* The bridge from a block made since the journal's start (in the current blocks blc, not in the start blocks bl0)
   to the journal's write right on each of its bytes (YCbq.v awr_byte, its in_tmp_block case): what the segment
   walks use for their writes to pp, pod, out and first, from hd_seg_pre's last conjuncts. *)
Lemma hd_fresh_awr : forall STK sp0 FP bl0 blc ly own p n i,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 <= i < req_size n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n i Hin Hout Hi. right. right. left.
exists p, n. split; [exact Hin|]. split; [exact Hout|]. lia.
Qed.
Lemma hd_fresh_awr_n : forall STK sp0 FP bl0 blc ly own p n,
In (p, n) blc -> ~ In (p, n) bl0 -> 0 < n ->
forall i, 0 <= i < n -> awr_byte STK sp0 FP bl0 blc ly own (p + i).
Proof.
intros STK sp0 FP bl0 blc ly own p n Hin Hout Hn i Hi. apply (hd_fresh_awr STK sp0 FP bl0 blc ly own p n i Hin Hout).
unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.

(* ================ the cut states of LLVMFuzzerTestOneInput, as data each image fills ================
   The two ASan images keep the harness's values in different registers and real-frame cells (image A keeps the
   null flag at R+0x40 and the frame for locals in s6 and s10; image B keeps 1 - null at R+0x38 and in s7, and the
   frame for locals in s7, s5, R+0x18 and R+0x48), so a cut state is a list
   of (location, value) facts over the run's quantities hd_env. A location is a register or an 8-byte cell at a
   base plus an offset; a value is one of the quantities, an address made from a block, or a constant. The image's
   lists are measured from its code. *)
(* The run's quantities: S the entry sp; R the 32-aligned base of the real frame (R + its size <= S); F the frame
   for locals (a side-stack frame of the image's class); pp, pod, out and first the four blocks; len = pp->len
   after the build (hd_len of the input after the two harness bytes); cap the harness's cap (the second input byte
   mod 10); null the harness's null flag (the first input byte and 1); rc the parse's answer; src and left the
   input cursor and the bytes left after the two harness bytes. *)
Record hd_env := HDEnv {
e_S : Z; e_R : Z; e_F : Z;
e_pp : Z; e_pod : Z; e_out : Z; e_first : Z;
e_len : Z; e_cap : Z; e_null : Z; e_rc : Z; e_src : Z; e_left : Z }.
(* XShF is the shadow address of F, (F >> 3) + K with K the runtime's shadow offset (SHADOW_OFF); XPpShr c is
   (pp + c) >> 3, a shadow index before K is added; XLenNZ is the malloc request len + (len == 0); XCap3 and
   XCap33 are 3 cap and 3 cap + 3 (the out block's size); XNotNull is 1 minus the null flag (image B keeps it at
   R+0x38 and in s7, and forms the parse's argument as neg(s7) & pod); XProps is the parse's first argument, pod
   when the null flag is 0 and 0 when it is 1; XRc3 is 3 max(rc, 0) and XRc3NZ the first block's malloc request. *)
Inductive hd_x :=
| XS | XR | XF (c : Z) | XShF
| XPp (c : Z) | XPpShr (c : Z) | XPod | XOut | XFirst
| XLen | XLenNZ | XCap | XCap3 | XCap33 | XNull | XNotNull | XProps | XRc | XRc3 | XRc3NZ
| XSrc | XLeft | XC (c : Z).
Definition hd_xv (e : hd_env) (x : hd_x) : Z :=
match x with
| XS => e_S e | XR => e_R e | XF c => e_F e + c | XShF => shadow_addr (e_F e)
| XPp c => e_pp e + c | XPpShr c => Z.shiftr (e_pp e + c) 3
| XPod => e_pod e | XOut => e_out e | XFirst => e_first e
| XLen => e_len e | XLenNZ => e_len e + (if e_len e =? 0 then 1 else 0)
| XCap => e_cap e | XCap3 => 3 * e_cap e | XCap33 => 3 * e_cap e + 3
| XNull => e_null e | XNotNull => 1 - e_null e | XProps => (if e_null e =? 0 then e_pod e else 0)
| XRc => e_rc e | XRc3 => 3 * Z.max (e_rc e) 0
| XRc3NZ => 3 * Z.max (e_rc e) 0 + (if 3 * Z.max (e_rc e) 0 =? 0 then 1 else 0)
| XSrc => e_src e | XLeft => e_left e | XC c => c
end.
Inductive hd_loc := LReg (r : Z) | LCell (b : hd_x) (off : Z).
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A register holds the 64-bit word of v; a cell holds its 8 little-endian bytes. *)
Definition hd_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
(l : hd_loc) (v : Z) : Prop :=
match l with
| LReg r => getr regs (Z_to_bv 5 r) = w64 v
| LCell b o => val_mem segs (mrestrict H mem) (hd_xv e b + o) 8 (v mod 2 ^ 64)
end.
Definition hd_cut (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
(L : list (hd_loc * hd_x)) : Prop :=
Forall (fun f => hd_at H mem regs e (fst f) (hd_xv e (snd f))) L.
(* The shadow bytes of the frame for locals, from shadow_addr F on (one byte per 8-byte granule of F). *)
Definition hd_fsh (H : word -> bool) (mem : word -> option byte) (F : Z) (pat : list Z) : Prop :=
forall i, 0 <= i < Z.of_nat (length pat) -> aview segs H mem (shadow_addr F + i) = Some (nth (Z.to_nat i) pat 0).
End u.
(* a lies in one of the ranges ws: (base, offset, length) -> [base + offset, base + offset + length). *)
Definition hd_inw (e : hd_env) (ws : list (hd_x * Z * Z)) (a : Z) : Prop :=
Exists (fun w => hd_xv e (fst (fst w)) + snd (fst w) <= a < hd_xv e (fst (fst w)) + snd (fst w) + snd w) ws.
