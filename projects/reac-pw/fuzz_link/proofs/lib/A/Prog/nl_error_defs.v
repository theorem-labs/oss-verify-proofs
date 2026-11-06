(* nl_error (fuzz_link.asan 0x86e4c, listing offset AF_nl_error = 0x4c80; listing
   (internal path) (internal record, sha256 7ca564e0b716)): the data the phases of the walk of
   lib/A/Prog/nl_error_c.v `nl_error_acontract` share.

   THE PHASES. The code joins after every nl_put: each put's no-room arm stores full := 1 and jumps to the
   instruction after the put (+0x1b0, +0x238, +0x2bc, +0x348, +0x3e0), then +0x484 (after the cut put), +0x4e0
   (after nl_end) and +0x550 (after nl_pad); +0x414 joins the two arms of the cut's `bgez`. The walk cuts at each
   of them (J1 .. J8, J5b), as pcap's PcapSourceNext*.v do: a phase lemma has the shape
   `ne_from POST J_next -> ne_from POST J_self`, so no path is walked twice.

   A join is a CONCRETE invariant (`ne_jg`): the pc, the registers the code still reads, the 13 words the prologue
   saved, the cut's spill slot, the two fields of the struct nl_w (LinkWalkNlw.v nlw_fields) and n0 <= n, the
   shadow of w (addressable, visible), the side frame F's flag word, presence and 16 shadow bytes, the caller's
   journal with F on top of `own`, and what the walk kept: every byte outside the call's window, w, F and F's
   shadow is as it was right after frame_alloc_1 returned (memA). Each phase seats a symbolic state on it
   (`ne_ss`, nl_error_kit.v ne_seat), runs, and reads the next join back.

   The atoms of a seated state (`ne_E`): 0..31 the registers of the join, 32 the shadow base, 33 n, 34 full,
   35 w, 36 F, 37 F's flag address, 38 F's shadow address, 39 the entry sp, 40 the realigned sp1, 41 n0 (s6),
   42 the code (a1 at entry), 43 cut' (the cut after +0x40c), 44..56 the 13 saved words (ne_saves), 57 the cut.
   The calls after a join havoc atoms 100..115 (jafter_call_keep_pi with k = 100); the runs' fresh atoms start
   at 512.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlw PcapRelro nl_error_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Image-free constants of the walk
   ========================================================================== *)

(* The listing offsets of the cuts. *)
Definition NE_JE : Z := 0x7c.    (* frame_alloc_1 returned *)
Definition NE_J0 : Z := 0x120.   (* before the check C1 of n and the load of n *)
Definition NE_J1 : Z := 0x1b0.   (* after nl_put32(w, 0)  (+0x130..+0x1ac) *)
Definition NE_J2 : Z := 0x238.   (* after nl_put16(w, 2)  (+0x1b0..+0x234) *)
Definition NE_J3 : Z := 0x2bc.   (* after nl_put16(w, 0)  (+0x238..+0x2b8) *)
Definition NE_J4 : Z := 0x348.   (* after nl_put32(w, 1)  (+0x2bc..+0x344) *)
Definition NE_J5 : Z := 0x3e0.   (* after nl_put32(w, 0)  (+0x348..+0x3dc) *)
Definition NE_J5c : Z := 0x404.  (* checked_memset(F + 36, 0, 16) returned (+0x400) *)
Definition NE_J5b : Z := 0x414.  (* after the cut's `bgez` (+0x40c, +0x410) *)
Definition NE_J6c : Z := 0x46c.  (* checked_memcpy(w + n, F + 32, cut') returned (+0x468) *)
Definition NE_J6 : Z := 0x484.   (* after the cut put      (+0x414..+0x480) *)
Definition NE_J7 : Z := 0x4e0.   (* after nl_end            (+0x484..+0x4dc) *)
Definition NE_J8c : Z := 0x53c.  (* nl_pad's checked_memset(w + n, 0, p - n) returned (+0x538) *)
Definition NE_J8 : Z := 0x550.   (* after nl_pad            (+0x4e0..+0x54c) *)

(* The words the prologue saves (+0x08..+0x38), as offsets from the entry sp, and the register saved there. *)
Definition ne_saves : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* F's 16 shadow bytes (fs_frame_bytes 1 = 128): as +0xe8..+0x118 leave them (left redzone f1, the 20-byte body
   marked unusable f8, right redzone f3, then frame_alloc_1's zeroes), and after +0x3e8..+0x3f0 make the body's
   20 bytes usable (granules 0, 0, 4). *)
Definition ne_shA : list Z := [241; 241; 241; 241; 248; 248; 248; 243; 243; 243; 243; 243; 0; 0; 0; 0].
Definition ne_shB : list Z := [241; 241; 241; 241; 0; 0; 4; 243; 243; 243; 243; 243; 0; 0; 0; 0].

(* the cut after +0x40c / +0x410: a cut with bit 63 set becomes 20 *)
Definition ne_cutv (c : Z) : Z := if c <? 2 ^ 63 then c else 20.
(* nl_pad's p (+0x4ec..+0x4f8): NL_ALIGN(n) *)
Definition ne_pad (n : Z) : Z := 4 * ((n + 3) / 4).

(* ---- the seated symbolic state ---- *)
Definition NE_SB : Z := 0x7fff8000.
(* s11 as +0xf8 / +0x11c compute it: the shadow cell of w + 4096 *)
Definition ne_s11sv : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 35 4096) (SLit 3)) (SOff 32 0).
(* the registers every join carries (beside gp, tp, which keep their own atoms) *)
Definition ne_upd_common : list (bv 5 * sv) :=
  [(2%bv, SOff 40 0); (8%bv, SOff 39 0); (9%bv, SOff 40 0); (26%bv, SOff 32 0)].
Definition ne_save_chunks : list YP09.chunk :=
  map (fun '(o, k) => YP09.mkChunk o (CVal 8 (SOff k 0)))
    (combine (map fst ne_saves) (seq 44 13)).
(* F's 16 shadow bytes sh, as the chunks of its region *)
Definition ne_sh_chunks (sh : list Z) : list YP09.chunk :=
  map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (seq 0 16).
(* the regions: w's two fields, F (its flag word), F's shadow sh (writable iff wsh), the cut's slot, the saves *)
Definition ne_regions (wsh : bool) (sh : list Z) : smem :=
  [YP09.mkRegion (Some 35%nat) 4096 4112 4096 4112
     [YP09.mkChunk 4096 (CVal 8 (SOff 33 0)); YP09.mkChunk 4104 (CVal 4 (SOff 34 0))];
   YP09.mkRegion (Some 36%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 37 0))];
   YP09.mkRegion (Some 38%nat) 0 16 0 (if wsh then 16 else 0) (ne_sh_chunks sh);
   YP09.mkRegion (Some 40%nat) 24 56 48 56 [YP09.mkChunk 24 (CVal 8 (SOff 57 0))];
   YP09.mkRegion (Some 39%nat) (-104) 0 (-104) (-104) ne_save_chunks].
(* The facts: the atoms' ranges, the conditions xc a phase knows (the room test it has decided), and the two
   aliases by which a store at w + n (a put's bytes) and at w + n0 (nl_end's length) resolves to the atoms 58 and
   59, whose regions (ne_put_region, ne_end_region) a phase that makes that store adds. *)
Definition ne_facts (xc : list acond) : facts :=
  mkFacts [(32%nat, mkAF NE_SB NE_SB 0); (33%nat, mkAF 0 4096 0); (34%nat, mkAF 0 1 0);
           (35%nat, mkAF 0 (2 ^ 47 - 4113) 0); (36%nat, mkAF 4096 140737479966720 6);
           (37%nat, mkAF 4096 140737479966720 0); (38%nat, mkAF (NE_SB + 512) (NE_SB + 2 ^ 44) 3);
           (39%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (40%nat, mkAF (2 ^ 46 - 176) (2 ^ 47) 5);
           (41%nat, mkAF 0 4096 0); (43%nat, mkAF 0 20 0);
           (58%nat, mkAF 0 (2 ^ 47 - 17) 0); (59%nat, mkAF 0 (2 ^ 47 - 17) 0)] xc
    [shadow_decl 36 32 38;
     (SAlu ALU_ADD (SOff 35 0) (SOff 33 0), SOff 58 0); (SAlu ALU_ADD (SOff 35 0) (SOff 41 0), SOff 59 0)].
Definition ne_put_region (k : Z) : YP09.region := YP09.mkRegion (Some 58%nat) 0 k 0 k [].
Definition ne_end_region : YP09.region := YP09.mkRegion (Some 59%nat) 0 4 0 4 [].
Definition ne_ss (o : Z) (upd : list (bv 5 * sv)) (wsh : bool) (sh : list Z) (xr : list YP09.region) (xc : list acond)
    : sstate :=
  mkSS (AF_nl_error + o) (sr_sets sr_atoms (ne_upd_common ++ upd)) (ne_regions wsh sh ++ xr) None (ne_facts xc).
(* the check that a run's end state holds F's shadow bytes sh' as its region 38 chunks *)
Definition ne_sh_check (rs : smem) (sh' : list Z) : bool :=
  Nat.eqb (length sh') 16 && forallb (fun v => (0 <=? v) && (v <? 256)) sh' &&
  forallb (fun i => match find (fun r => match YP09.r_base r with Some q => Nat.eqb q 38 | None => false end) rs with
                    | Some r => match find (fun c => Z.eqb (YP09.c_off c) (Z.of_nat i)) (YP09.r_chunks r) with
                                | Some (YP09.mkChunk _ (CVal 1 (SLit v))) => Z.eqb (v mod 256) (nth i sh' 0)
                                | _ => false end
                    | None => false end) (seq 0 16).
(* the shadow entries of a run with instrumented checks: w's two fields, F (reversed: no byte of it is claimed
   addressable, only that it is application memory; YCbq.v shent_app_of_frame), and the 16 bytes from w + n and
   from w + n0 (the engine's tok_load asks `covered x 8` of a check at x) *)
Definition ne_SH : list shent := [mkSHE 35 4096 4112; mkSHE 36 128 0; mkSHE 58 0 16; mkSHE 59 0 16].
Definition ne_Bx : sv := SOff 32 0.
Definition ne_span : Z * Z := (NE_SB, NE_SB + 2 ^ 44 - 1).
(* a run with no check (F's shadow writable): no shadow entry, an empty band below every window *)
Definition ne_span0 : Z * Z := (0, 0).
Definition ne_updE : list (bv 5 * sv) :=      (* JE: a0 = F, s2 = w, s3 = 4096, s7 = code, s6 the caller's *)
  [(10%bv, SOff 36 0); (18%bv, SOff 35 0); (19%bv, SLit 4096); (23%bv, SOff 42 0); (22%bv, SOff 51 0)].
Definition ne_upd0 : list (bv 5 * sv) :=      (* J0: s2 = w, s4 = F, s7 = code, s6 the caller's *)
  [(18%bv, SOff 35 0); (20%bv, SOff 36 0); (23%bv, SOff 42 0); (22%bv, SOff 51 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
(* the per-join registers of a seated state (the symbolic side of ne_rvA .. ne_rv6 below) *)
Definition ne_updA : list (bv 5 * sv) :=      (* J1 .. J4: a1 = -4093, s2 = w, s4 = F, s7 = code *)
  [(11%bv, SLit (2 ^ 64 - 4093)); (18%bv, SOff 35 0); (20%bv, SOff 36 0); (23%bv, SOff 42 0); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
Definition ne_upd5 : list (bv 5 * sv) :=      (* J5: s2 = code, s4 = F, s5 = w, s7 = code *)
  [(18%bv, SOff 42 0); (20%bv, SOff 36 0); (21%bv, SOff 35 0); (23%bv, SOff 42 0); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
Definition ne_upd5b : list (bv 5 * sv) :=     (* J5b: a2 = cut', s4 = F, s5 = w, s7 = F + 32 *)
  [(12%bv, SOff 43 0); (20%bv, SOff 36 0); (21%bv, SOff 35 0); (23%bv, SOff 36 32); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
Definition ne_upd6 : list (bv 5 * sv) :=      (* J6 .. J8: s2 = F, s4 = w *)
  [(18%bv, SOff 36 0); (20%bv, SOff 35 0); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
Definition ne_upd5c : list (bv 5 * sv) :=     (* J5c: s2 = code, s4 = F, s5 = w, s7 = F + 32 *)
  [(18%bv, SOff 42 0); (20%bv, SOff 36 0); (21%bv, SOff 35 0); (23%bv, SOff 36 32); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].
Definition ne_upd6c : list (bv 5 * sv) :=     (* J6c: s2 = F, s4 = w, s5 = cut' *)
  [(18%bv, SOff 36 0); (20%bv, SOff 35 0); (21%bv, SOff 43 0); (22%bv, SOff 41 0);
   (19%bv, SOff 35 4096); (24%bv, SOff 38 0); (25%bv, SOff 36 0); (27%bv, ne_s11sv)].

(* ==========================================================================
   2. The call's context and the phase predicate
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* Everything the contract quantifies, and the Pre's byte list of the struct. *)
Record necx := mkNECX {
  n_G : list (Z * Z); n_XO : Z; n_OUT : list (Z * Z); n_STK : Z; n_sp0 : Z; n_FP : list (Z * Z);
  n_ly : alayout; n_S : astate; n_W0 : world SEGS; n_mem0 : word -> option byte; n_md0 : Model;
  n_own : list (Z * Z);
  n_lyc : alayout; n_Sc : astate; n_W : world SEGS; n_memc : word -> option byte; n_mdc : Model; n_k : Z;
  n_regs : bvmap 5 word;
  n_bs : list byte
}.

Definition ne_w (cx : necx) : Z := aarg (n_regs cx) 0.
Definition ne_cut (cx : necx) : Z := aarg (n_regs cx) 2.
Definition ne_sp (cx : necx) : Z := spZ (n_regs cx).
Definition ne_sp1 (cx : necx) : Z := 32 * ((ne_sp cx - 160) / 32).
Definition ne_n0 (cx : necx) : Z := nw_n (n_bs cx).
(* the extra regions a seated state may carry: a put's 2 or 4 bytes at w + n (room decided), nl_end's 4 bytes
   at w + n0 (nl_end's test decided) *)
Definition ne_xr_ok (cx : necx) (n : Z) (xr : list YP09.region) : Prop :=
  xr = [] \/ (xr = [ne_put_region 2] /\ n + 2 <= 4096) \/ (xr = [ne_put_region 4] /\ n + 4 <= 4096) \/
  (xr = [ne_end_region] /\ ne_n0 cx + 4 <= n).
Definition ne_F (cx : necx) (pos : Z) : Z := frame_addr (n_lyc cx) 1 pos.
Definition ne_FL (cx : necx) (pos : Z) : Z := flag_addr (n_lyc cx) 1 pos.
Definition ne_Fsh (cx : necx) (pos : Z) : Z := shadow_addr (ne_F cx pos).
Definition ne_Wr (cx : necx) : list (Z * Z) := nl_error_awr (n_regs cx) (rdW (n_W cx) (n_memc cx)).

(* The contract's premises, at the context. *)
Definition ne_base (cx : necx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B NL_ERROR_AK 0 [(1, 1)] (ne_Wr cx)
    (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
    (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx) /\
  anlw_at SEGS (rdW (n_W cx) (n_memc cx)) (ne_w cx) (n_bs cx) /\ nlw_wf (n_bs cx) /\
  apart_frame (n_regs cx) NL_ERROR_AK (ne_w cx) NW_SIZE /\
  (ne_cut cx <= NL_ERR_BODY \/ 2 ^ 63 <= ne_cut cx) /\
  amem_range (ne_w cx) NW_SIZE /\
  range_addressable (ard SEGS (rdW (n_W cx) (n_memc cx))) SHADOW_OFF (ne_w cx) NW_SIZE /\
  shadow_hull_vis (ard SEGS (rdW (n_W cx) (n_memc cx))) (ne_w cx) NW_SIZE.

(* The contract's Post, at the context. *)
Definition ne_post (cx : necx) : world SEGS -> config -> Prop :=
  apost SK SEGS B NL_ERROR_AK 0 (fun a => inFP (ne_Wr cx) a)
    (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
    (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) (n_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (n_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (n_lyc cx) (n_Sc cx)) /\
       nl_error_apost SEGS (n_regs cx) (rdW (n_W cx) (n_memc cx)) regs2 (rdW W2 mem2)).

(* What frame_alloc_1 (+0x78) leaves, fixed from its return on: the class-1 frame at slot pos was free at the
   call; F, its flag and w are where AR's frame facts and the journal put them (F 64-aligned, application memory,
   below the allocator's ceiling, apart from w); and memA (the memory right after the call) keeps, relative to
   the call's entry memory, what the Post's kept clause asks, with the call's window [sp - K, sp)
   (LinkWalkSide.v akept_of_acall_kept on frame_alloc_1's acall_kept, after the prologue's akept_step). The
   heap-block shadow clause of the Post needs nothing here: LinkWalkSide.v ashadow_kept_AR gives it from the two
   journals' AR. *)
Definition ne_fctx (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte) : Prop :=
  ~ In (1, pos) (frames (n_Sc cx)) /\
  frames S3 = (1, pos) :: frames (n_Sc cx) /\ (exists f0, S3 = set_fs f0 (n_Sc cx)) /\
  4096 <= ne_F cx pos /\ ne_F cx pos mod 64 = 0 /\ ne_F cx pos + 128 <= alloc_ceiling /\
  (ne_F cx pos + 128 <= kLowShadowBeg \/ kHighMemBeg <= ne_F cx pos) /\
  4096 <= ne_FL cx pos < alloc_ceiling /\
  (ne_w cx + NW_SIZE <= ne_F cx pos \/ ne_F cx pos + 128 <= ne_w cx) /\
  akept SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_W cx) memA (ne_sp cx - NL_ERROR_AK) (ne_sp cx)
    (fun _ => False).

(* The bytes a phase may write: the call's window, w, F and F's shadow. *)
Definition ne_Z (cx : necx) (pos : Z) (a : Z) : Prop :=
  (ne_sp cx - NL_ERROR_AK <= a < ne_sp cx) \/ (ne_w cx <= a < ne_w cx + NW_SIZE) \/
  (ne_F cx pos <= a < ne_F cx pos + 128) \/ (ne_Fsh cx pos <= a < ne_Fsh cx pos + 16).

(* The bytes one step of a phase may write (a run's writable windows, a checked call's destination and window):
   the checked calls' window [sp1 - ESTACK, sp1), the spill slot of F at sp1 + 48 (+0x124), w, F and F's shadow.
   It misses the 13 saved words and the cut's slot. *)
Definition ne_X (cx : necx) (pos : Z) (a : Z) : Prop :=
  (ne_sp1 cx - ESTACK <= a < ne_sp1 cx) \/ (ne_sp1 cx + 48 <= a < ne_sp1 cx + 56) \/
  (ne_w cx <= a < ne_w cx + NW_SIZE) \/
  (ne_F cx pos <= a < ne_F cx pos + 128) \/ (ne_Fsh cx pos <= a < ne_Fsh cx pos + 16).

(* THE JOIN, common part: n and f are the struct's fields now, sh F's shadow bytes now. *)
Definition ne_j (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (n f : Z) (sh : list Z) : Prop :=
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((1, pos) :: n_own cx) (n_lyc cx) S3 (n_W cx) mem3 md3 (n_k cx) /\
  m_fds md3 = m_fds (n_mdc cx) /\ m_fs md3 = m_fs (n_mdc cx) /\
  getr regs3 2 = w64 (ne_sp1 cx) /\ getr regs3 3 = getr (n_regs cx) 3 /\ getr regs3 4 = getr (n_regs cx) 4 /\
  getr regs3 8 = w64 (ne_sp cx) /\ getr regs3 9 = w64 (ne_sp1 cx) /\
  getr regs3 26 = w64 SHADOW_OFF /\
  Forall (fun ok : Z * bv 5 => val_mem SEGS (rdW (n_W cx) mem3) (ne_sp cx + fst ok) 8
                                (bv_unsigned (getr (n_regs cx) (snd ok)))) ne_saves /\
  val_mem SEGS (rdW (n_W cx) mem3) (ne_sp1 cx + 24) 8 (ne_cut cx) /\
  nlw_fields SEGS (rdW (n_W cx) mem3) (ne_w cx) n f /\ ne_n0 cx <= n /\
  range_addressable (aview SEGS (w_H (n_W cx)) mem3) SHADOW_OFF (ne_w cx) NW_SIZE /\
  shadow_hull_vis (aview SEGS (w_H (n_W cx)) mem3) (ne_w cx) NW_SIZE /\
  val_mem SEGS (rdW (n_W cx) mem3) (ne_F cx pos + 120) 8 (ne_FL cx pos) /\
  (forall i, 0 <= i < 128 -> apresent (w_H (n_W cx)) mem3 (ne_F cx pos + i)) /\
  length sh = 16%nat /\
  (forall i, (i < 16)%nat -> aview SEGS (w_H (n_W cx)) mem3 (ne_Fsh cx pos + Z.of_nat i) = Some (nth i sh 0)) /\
  (forall i, 0 <= i < 16 -> apresent (w_H (n_W cx)) mem3 (ne_Fsh cx pos + i)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ ne_Z cx pos a ->
     aview SEGS (w_H (n_W cx)) mem3 a = aview SEGS (w_H (n_W cx)) memA a) /\
  (forall a, apresent (w_H (n_W cx)) memA a -> apresent (w_H (n_W cx)) mem3 a).

(* A join: the common part at some n, f, and the registers rv (a function of the context and F's slot) the
   phase reads. *)
Definition ne_jg (sh : list Z) (rv : necx -> Z -> list (bv 5 * word)) (cx : necx) (pos : Z) (S3 : astate)
    (memA : word -> option byte) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  exists n f, ne_j cx pos S3 memA regs3 mem3 md3 n f sh /\
    Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (rv cx pos).

(* the per-join registers *)
Definition ne_rvA (cx : necx) (pos : Z) : list (bv 5 * word) :=     (* J1 .. J4 *)
  [(11%bv, w64 (2 ^ 64 - 4093)); (18%bv, w64 (ne_w cx)); (20%bv, w64 (ne_F cx pos)); (23%bv, getr (n_regs cx) 11);
   (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].
Definition ne_rv5 (cx : necx) (pos : Z) : list (bv 5 * word) :=     (* J5 *)
  [(18%bv, getr (n_regs cx) 11); (20%bv, w64 (ne_F cx pos)); (21%bv, w64 (ne_w cx)); (23%bv, getr (n_regs cx) 11);
   (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].
Definition ne_rv5b (cx : necx) (pos : Z) : list (bv 5 * word) :=    (* J5b *)
  [(12%bv, w64 (ne_cutv (ne_cut cx))); (20%bv, w64 (ne_F cx pos)); (21%bv, w64 (ne_w cx));
   (23%bv, w64 (ne_F cx pos + 32)); (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].
Definition ne_rv6 (cx : necx) (pos : Z) : list (bv 5 * word) :=     (* J6, J7, J8 *)
  [(18%bv, w64 (ne_F cx pos)); (20%bv, w64 (ne_w cx)); (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].

Definition ne_rv5c (cx : necx) (pos : Z) : list (bv 5 * word) :=    (* J5c *)
  [(18%bv, getr (n_regs cx) 11); (20%bv, w64 (ne_F cx pos)); (21%bv, w64 (ne_w cx)); (23%bv, w64 (ne_F cx pos + 32));
   (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].
Definition ne_rv6c (cx : necx) (pos : Z) : list (bv 5 * word) :=    (* J6c *)
  [(18%bv, w64 (ne_F cx pos)); (20%bv, w64 (ne_w cx)); (21%bv, w64 (ne_cutv (ne_cut cx))); (22%bv, w64 (ne_n0 cx));
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].

(* the joins of the head: JE right after frame_alloc_1 returned (+0x7c; F's shadow still all 0, s3 = 4096, s6 the
   caller's), J0 at +0x120 (F's header and shadow written, before the check C1 and the load of n) *)
Definition ne_shZ : list Z := repeat 0 16.
Definition ne_rvE (cx : necx) (pos : Z) : list (bv 5 * word) :=
  [(10%bv, w64 (ne_F cx pos)); (18%bv, w64 (ne_w cx)); (19%bv, w64 4096); (23%bv, getr (n_regs cx) 11);
   (22%bv, getr (n_regs cx) 22)].
Definition ne_rv0 (cx : necx) (pos : Z) : list (bv 5 * word) :=
  [(18%bv, w64 (ne_w cx)); (20%bv, w64 (ne_F cx pos)); (23%bv, getr (n_regs cx) 11); (22%bv, getr (n_regs cx) 22);
   (19%bv, w64 (ne_w cx + 4096)); (24%bv, w64 (ne_Fsh cx pos)); (25%bv, w64 (ne_F cx pos));
   (27%bv, w64 (SHADOW_OFF + (ne_w cx + 4096) / 8))].
Definition ne_JEi (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ne_j cx pos S3 memA regs3 mem3 md3 (ne_n0 cx) (nw_full (n_bs cx)) ne_shZ /\
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rvE cx pos).
Definition ne_J0i (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ne_j cx pos S3 memA regs3 mem3 md3 (ne_n0 cx) (nw_full (n_bs cx)) ne_shA /\
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv0 cx pos).

Definition ne_JA : necx -> Z -> astate -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  ne_jg ne_shA ne_rvA.
Definition ne_J5i := ne_jg ne_shA ne_rv5.
Definition ne_J5bi := ne_jg ne_shB ne_rv5b.
Definition ne_J6i := ne_jg ne_shB ne_rv6.
Definition ne_J5ci := ne_jg ne_shB ne_rv5c.
(* J6c: the copy is done, the room test it passed is kept *)
Definition ne_J6ci (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model) : Prop :=
  exists n f, ne_j cx pos S3 memA regs3 mem3 md3 n f ne_shB /\
    Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv6c cx pos) /\
    n + ne_cutv (ne_cut cx) <= 4096.
(* J8c: nl_pad's fill is done; s5 = p - n *)
Definition ne_J8ci (cx : necx) (pos : Z) (S3 : astate) (memA : word -> option byte) (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) (md3 : Model) : Prop :=
  exists n f, ne_j cx pos S3 memA regs3 mem3 md3 n f ne_shB /\
    Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv6 cx pos) /\
    getr regs3 21 = w64 (ne_pad n - n) /\ ne_pad n <= 4096.

(* THE PHASE PREDICATE: from every state GI describes at listing offset AF_nl_error + o, the run reaches POST. *)
Definition ne_from (POST : necx -> world SEGS -> config -> Prop) (o : Z)
    (GI : necx -> Z -> astate -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : Prop :=
  forall cx pos S3 memA regs3 mem3 md3,
    ne_base cx -> ne_fctx cx pos S3 memA -> GI cx pos S3 memA regs3 mem3 md3 ->
    SRr SEGS (n_W cx) (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (AF_nl_error + o))) mem3 (seg_rom SEGS)) md3) (POST cx).

(* The environment of a seated state. *)
Definition ne_extra (cx : necx) (pos n f : Z) : list word :=
  map w64 [SHADOW_OFF; n; f; ne_w cx; ne_F cx pos; ne_FL cx pos; ne_Fsh cx pos; ne_sp cx; ne_sp1 cx;
           ne_n0 cx; bv_unsigned (getr (n_regs cx) 11); ne_cutv (ne_cut cx)] ++
  map (fun ok : Z * bv 5 => getr (n_regs cx) (snd ok)) ne_saves ++
  [w64 (ne_cut cx); w64 (ne_w cx + n); w64 (ne_w cx + ne_n0 cx)].
Definition ne_E (cx : necx) (pos : Z) (regs3 : bvmap 5 word) (n f : Z) : env :=
  Eimg (Ereg regs3 (ne_extra cx pos n f)).
End b.
End a.

