(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 133 of its 156 lines of code are new or changed and 495 lines of the source are left out. *)
(* The shared vocabulary of the walk of cross_check on IMAGE B (reac-pw/fuzz_segconf, fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3; 0x897cc, 696 bytes, 174 instructions, real frame 128 bytes, no side-stack frame of its own).
   ADAPTED from the image-A G3 walk owner's image-A lib/A/Prog/cross_check_d.v (commit 130284ff40f1): the
   same records, cut predicates and segment statements, re-derived on image B's machine code -- the cut offsets,
   the register map of INV_LOOP and the spill slots are image B's and differ from image A's. Requires are the
   image-B kit copies (lib.B) and lib.B.Prog, as every B file does.

   The cut points, as offsets from cross_check's entry (BASE + CC_* is the address):
     CC_LOOP 0xa8  (0x89874)  the head of the segment loop, pass i; `li a0,33` then the two UBSan trap tests
     CC_EPI  0x230 (0x899fc)  the epilogue: the 13 reloads, `addi sp,sp,128`, `ret`
   The entry (0x897cc-0x89870) runs the prologue, the two entry UBSan trap tests (0x89804 c = 0, 0x89810
   c & 7 <> 0), the inline check of c->n (0x89834) and the preheader; one pass of the body
   (0x89874-0x89980, with the check stubs 0x89984-0x899f4 and the error calls 0x89a3c-0x89a80) ends at the loop
   head again or at CC_EPI.

   cross_check calls one program function, refuse (image B 0x892f8, PCall SS_refuse), at 0x89900 (the BOX arm:
   role = box with no model, format F_xbox with s->name) and at 0x89944 (the MODEL arm: a model under a role
   that is not box, F_xmodel with s->name and s->model); the two call sites are on exclusive arms, so one pass
   makes at most one call. NOTE the order is the other way round from image A, whose model arm came first.
   refuse reaches the snprintf and vsnprintf wrappers, so its post is apost_baseF: it returns at some FP state
   fx1 with fxrel fx fx1 (lib/B/Prog/PaFx.v). Both calls are inside the loop, so EVERY cut after a pass is
   stated at every FP state: the loop segment takes `forall fx0, from_LOOP (fx := fx0) ... (i + 1)` and
   `forall fx0, from_EPI (fx := fx0)`, and lifts their apost_baseF at fx1 to the entry's fx with
   PaFx.srr_apost_baseF_lift. The rounding-mode premise frm0 is a premise of the loop segment only.

   cross_check takes NO side-stack frame: the objdump has no frame_alloc call and no 0x41b58ab3 / 0x45e0360e
   frame magic. Its journal therefore carries the empty own-frame list at every cut, and refuse's own class-0
   frame is taken and freed inside refuse (its post's sa_noalloc). s0 holds c, not a frame pointer, so the frame
   chain at a call site is the empty chain (YCbq.v achain_low: a live heap block lies below alloc_ceiling, and
   astk_ok gives alloc_ceiling <= ly_stk_lo).

   The four UBSan trap branches of image B (all to the one `unimp` at 0x89a38) are discharged where they stand:
     0x89804 `beqz a0`      c = 0                 -- cc_pre's cp_c0, sharpened to 4096 <= c by cp_heap
     0x89810 `bnez a0`      (c & 7) <> 0          -- cc_pre's cp_c16 (c mod 16 = 0)
     0x89878 `beq s10,33`   i = 33                -- INV_LOOP's 0 <= i < cc_n v with cc_n v <= 32
     0x8987c `bltu s11,s9`  ~c < 356 i            -- INV_LOOP's regs 27 = ~c with cp_addr's c + 16616 <= 2^63,
                                                     and regs 25 = 356 i with i <= 31
   The first two are the entry segment's, the last two the loop segment's.

   EVERY definition below takes B, lit, gotw, guard and STK_REF as EXPLICIT parameters, in that order, even
   where the body does not use one of them: a Section Variable is discharged only into the definitions that
   mention it, which gives the same name different arities in different files.

   Statement text and predicates only: no instruction of the binary is walked here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import cross_check_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the cut points, as offsets from the listing's start (image B: entry 0x897cc = BASE + AF_cross_check) *)
Definition CC_LOOP : Z := AF_cross_check + 0xa8.
Definition CC_EPI : Z := AF_cross_check + 0x230.
(* the return point of the refuse call of the BOX arm (0x89904) and of the MODEL arm (0x89948) *)
Definition CC_RET1 : Z := AF_cross_check + 0x138.
Definition CC_RET2 : Z := AF_cross_check + 0x17c.
(* the registers the prologue saves, in the order of their slots: slot j at sp0 - 8 - 8 j (ra at 120(sp),
   s0 at 112(sp), ..., s11 at 24(sp), with sp = sp0 - 128) *)
Definition cc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the values the walk keeps from cross_check's entry: the statement's binders *)
Record ccx : Type := mkCCX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte;
  x_md : Model; x_ch : list (Z * Z * Z); x_c : Z; x_rcs : rconf }.
Definition cc_sp0 (v : ccx) : Z := spZ (x_regs v).
(* the number of segment entries the loop runs over, and the record after i passes *)
Definition cc_n (v : ccx) : Z := Z.of_nat (length (rc_seg (x_rcs v))).
Definition cc_at (v : ccx) (i : Z) : rconf := cc_fold (x_rcs v) i.
(* cross_check's own stack number (cross_check_c.v: 128 + STK_refuse) and footprint *)
Definition cc_STK (STK_REF : Z) : Z := 128 + STK_REF.
Definition cc_FP (v : ccx) : list (Z * Z) := cross_check_W (x_c v).
(* cross_check_contract's premises over the context. cross_check_pre's conjuncts are spelled out and its ONE
   rounding-mode conjunct (sa_frm0, which is PaFx's frm0 at the ambient FP state) is LEFT OUT: the loop crosses
   a refuse call, which changes the FP state, so a cut predicate that mentioned the FP state could not be
   carried from one pass to the next. Rounding mode 0 travels on its own, as the `frm0 fx` premise of cc_S2P,
   and PaFx.fxrel_frm0 carries it across each call. cc_pre is therefore the same Prop at every FP state. *)
Record cc_pre (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) : Prop := mkCCPre {
  cp_afn : afn_pre SEGS B (cc_STK STK_REF) (x_ly v) (x_S v) (x_W v) (x_regs v) (x_mem v) (x_md v) (x_ch v);
  cp_rod : arodata_okP SEGS SEG_RLO SEG_RHI B (rdW (x_W v) (x_mem v));
  cp_a0 : getr (x_regs v) 10 = w64 (x_c v);
  cp_c64 : 0 <= x_c v < 2 ^ 64;
  cp_c0 : x_c v <> 0;
  cp_c16 : x_c v mod 16 = 0;
  cp_rconf : sa_rconf (rdW (x_W v) (x_mem v)) (x_c v) (x_rcs v);
  cp_heap : sa_heap B (x_ly v) (x_S v) (x_c v) seg_spec.SEG_C_SIZE;
  cp_addr : sa_addr (rdW (x_W v) (x_mem v)) (x_c v) seg_spec.SEG_C_SIZE;
  cp_ref64 : rc_refused (x_rcs v) + 64 < 2 ^ 32;
  cp_ssp : sa_ssp (rdW (x_W v) (x_mem v)) gotw guard;
  cp_lits : forall x, In x CROSS_CHECK_LITS -> sa_lit SEGS B (rdW (x_W v) (x_mem v)) (lit x) x;
  cp_room : sa_room (x_S v);
  cp_nev : st_nev (x_S v) + EV_cross_check <= EV_MAX }.
(* cc_pre from the statement's premises, and back to cross_check_pre at any FP state with rounding mode 0 *)
Lemma cc_pre_of : forall B lit gotw guard STK_REF v,
  afn_pre SEGS B (cc_STK STK_REF) (x_ly v) (x_S v) (x_W v) (x_regs v) (x_mem v) (x_md v) (x_ch v) ->
  arodata_okP SEGS SEG_RLO SEG_RHI B (rdW (x_W v) (x_mem v)) ->
  getr (x_regs v) 10 = w64 (x_c v) -> 0 <= x_c v < 2 ^ 64 ->
  cross_check_pre SEGS B lit gotw guard (x_ly v) (x_S v) (rdW (x_W v) (x_mem v)) (x_c v) (x_rcs v) ->
  sa_room (x_S v) -> st_nev (x_S v) + EV_cross_check <= EV_MAX ->
  cc_pre B lit gotw guard STK_REF v.
Proof.
intros B lit gotw guard STK_REF v HA HR H10 H64
  (Hc0 & Hc16 & Hrc & Hheap & Haddr & Href & Hfrm & Hssp & Hlits) HRoom HNev.
constructor; assumption.
Qed.
Lemma cc_pre_frm0 : forall B lit gotw guard STK_REF v,
  cc_pre B lit gotw guard STK_REF v -> sa_frm0 ->
  cross_check_pre SEGS B lit gotw guard (x_ly v) (x_S v) (rdW (x_W v) (x_mem v)) (x_c v) (x_rcs v).
Proof.
intros B lit gotw guard STK_REF v
  [Hafn Hrod Ha0 Hc64 Hc0 Hc16 Hrc Hheap Haddr Href Hssp Hlits Hroom Hnev] Hfrm.
(* sa_ssp is itself a conjunction, so `repeat split` would split past it *)
exact (conj Hc0 (conj Hc16 (conj Hrc (conj Hheap (conj Haddr (conj Href (conj Hfrm (conj Hssp Hlits)))))))).
Qed.
(* what the walk gives at the return: cross_check_contract's post *)
Definition cc_Q (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
  sa_rconf (rdW W' mem') (x_c v) (SegModel.cross_check (x_rcs v)) /\ sa_noalloc B (x_ly v) (x_S v) ly' S'.
(* the statement's post (FP-existential, apost_baseF: refuse reaches the printf wrappers) and the post at the
   FP state a refuse call returned (apost_base, what the rest of the pass proves) *)
Definition cc_post (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  : world SEGS -> config -> Prop :=
  apost_baseF SEGS B (cc_STK STK_REF) (cc_FP v) (x_regs v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v)
    EV_cross_check (cc_Q B lit gotw guard STK_REF v).
Definition cc_postB (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B (cc_STK STK_REF) (cc_FP v) (x_regs v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v)
    EV_cross_check (cc_Q B lit gotw guard STK_REF v).
(* the frame part of every cut: the walk's journal from the entry with NO own side-stack frame, the registers
   the ABI keeps, the 13 saved registers in their slots, and "nothing was allocated" (each refuse call takes
   and frees its own class-0 frame, so the frame list comes back and the layout is kept) *)
Record cc_fi (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop := mkCCFi {
  fi_j : ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
           ly3 S3 W3 mem3 md3 0;
  fi_sp : getr regs3 2 = w64 (cc_sp0 v - 128);
  fi_gp : getr regs3 3 = w64 (as_gp B);
  fi_tp : getr regs3 4 = w64 (as_tp B);
  fi_saved : forall j r, nth_error cc_saved j = Some r ->
    rdword (rdW W3 mem3) (cc_sp0 v - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs v) (Z_to_bv 5 r)));
  fi_noal : sa_noalloc B (x_ly v) (x_S v) ly3 S3 }.
(* the facts of the entry that every cut still has, and that both refuse call sites and the post need: the
   read-only bytes, the literals cross_check and refuse pass, printf's stack-protector cells, and the reader's
   block still live. refuse writes only inside that block (refuse_W) and inside its own frames, so each of
   these survives a pass. The block's shadow facts (sa_addr) are NOT carried here: they are read off AR at the
   current state (YCbq.v range_addressable_of_block over YG0d.v AR_blocks_law). *)
Record cc_un (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop := mkCCUn {
  un_rod : arodata_okP SEGS SEG_RLO SEG_RHI B (rdW W3 mem3);
  un_lit : forall x, In x CROSS_CHECK_LITS -> sa_lit SEGS B (rdW W3 mem3) (lit x) x;
  un_ssp : sa_ssp (rdW W3 mem3) gotw guard;
  un_heap : sa_heap B ly3 S3 (x_c v) seg_spec.SEG_C_SIZE }.
(* pass i of the loop, at its head 0x89874. The loop is rotated: the head is reached only with i < n, and n is
   reloaded from c->n at the latch (0x89970), so the invariant carries the record after i passes.
   Registers (image B, cc.md section 1.1): s0 = c, s1 = &c->n, s2 = the shadow base, s3 = the shadow
   byte address of &c->n, s9 = 356 i, s10 = i, s11 = ~c (image A's map is a different one: there s2 was
   F_xmodel, s3 the shadow base and s11 the shadow byte address, and there was no ~c). The three spills are
   sp+0 = ((c + RC_N) & 7) + 3 = 3 (c is 16-aligned and RC_N is a multiple of 8), sp+8 = F_xbox and
   sp+16 = F_xmodel; image A spilled only two of them and in the other order. *)
Definition INV_LOOP (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 /\
  0 <= i < cc_n v /\
  sa_rconf (rdW W3 mem3) (x_c v) (cc_at v i) /\
  getr regs3 8 = w64 (x_c v) /\
  getr regs3 9 = w64 (x_c v + seg_spec.RC_N) /\
  getr regs3 18 = w64 SHADOW_OFF /\
  getr regs3 19 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) /\
  getr regs3 25 = w64 (356 * i) /\
  getr regs3 26 = w64 i /\
  getr regs3 27 = w64 (2 ^ 64 - 1 - x_c v) /\
  rdword (rdW W3 mem3) (cc_sp0 v - 128) = Some 3 /\
  rdword (rdW W3 mem3) (cc_sp0 v - 120) = Some (lit F_xbox) /\
  rdword (rdW W3 mem3) (cc_sp0 v - 112) = Some (lit F_xmodel).
(* the epilogue 0x899fc: every pass is done, the record holds SegModel.cross_check rcs *)
Definition INV_EPI (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  sa_rconf (rdW W3 mem3) (x_c v) (SegModel.cross_check (x_rcs v)).
(* "from this cut point the walk reaches the statement's post" *)
Definition cc_from (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (pc : Z)
  (INV : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (v : ccx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, INV ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Definition from_LOOP (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z) : Prop :=
  cc_from B lit gotw guard STK_REF CC_LOOP (INV_LOOP B lit gotw guard STK_REF v i) v.
Definition from_EPI (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) : Prop :=
  cc_from B lit gotw guard STK_REF CC_EPI (INV_EPI B lit gotw guard STK_REF v) v.
End f.
End d.

(* the segments of the walk (one file each); cross_check.v chains them. Each is a lemma of a closed section, so
   it holds at every ambient FP state fx: that is why these statements live OUTSIDE Section d, where fx is an
   implicit argument a use can give with (fx := fx0). The refuse call of a pass returns at some fx1 with
   fxrel fx fx1, so the loop segment takes the next cuts at every FP state and lifts their post to the entry's
   FP state with PaFx.srr_apost_baseF_lift. *)
Section sp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
(* S1: the entry 0x897cc to the loop head (n > 0) or to the epilogue (n <= 0). No call, so the FP state is the
   entry's and the two cuts are taken at it. It discharges the two entry trap sites 0x89804 and 0x89810 and
   inline check 1 (0x89834, the load of c->n). *)
Definition cc_S1P (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) : Prop :=
  forall v, cc_pre B lit gotw guard STK_REF v ->
  from_EPI B lit gotw guard STK_REF v -> from_LOOP B lit gotw guard STK_REF v 0 ->
  SRr SEGS (x_W v) (cfg_at SEGS (BASE + AF_cross_check) (x_regs v) (x_mem v) (x_md v))
    (cc_post B lit gotw guard STK_REF v).
(* S2: one pass, from the loop head at i to the loop head at i + 1 or to the epilogue. It is the only segment
   that calls refuse, so it takes rounding mode 0 and the two next cuts at every FP state. The next pass needs
   rounding mode 0 at ITS own FP state: the refuse call of this pass returns at some fx1 with fxrel fx fx1, and
   PaFx.fxrel_frm0 carries frm0 from fx to fx1, so the premise for pass i + 1 is given only at the FP states
   that have it. The epilogue needs none. It discharges the two loop-head trap sites 0x89878 and 0x8987c and
   inline checks 2-9. *)
Definition cc_S2P (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) : Prop :=
  forall v i, frm0 fx -> cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  from_LOOP B lit gotw guard STK_REF v i.
(* S3: the epilogue, the 13 reloads and the return. *)
Definition cc_S3P (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) : Prop :=
  forall v, cc_pre B lit gotw guard STK_REF v -> from_EPI B lit gotw guard STK_REF v.
End sp.
