(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the cgif caller-journal contract,
   STATEMENT ONLY. No proof of the walk is in this file; `pb_reac_box_model_block_stmt` states what the walk
   proves. (rule 24: no function is proved here.)

   Guide of record: a working branch d69f7c708f6 (the v1.9.0 listing, 12 files, tool
   bfeab2e7364, PA 13 primitives). a Theorem Labs lane's working branch d385ad485f1 stays a record of the plain contract. Every
   numeral below is from that listing or from the PIN binary; none from lib/A/Prog/SlotModel.v.

   The call. Both callers hand it 32 bytes `o` inside their own side-stack frame (reac_box_catalogue_match
   0x846c8: class-2 frame + 112; ctrl_lay_block 0x85824: class-1 frame + 32), so the contract is in cgif's
   caller-journal form (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v:311-365), with CtrlCallerJ's shapes tcj_kept /
   twr_ok / tsrc_ok. Model: RcSynth.synth and RcSynth.rc (the plain contract lib/Prog/reac_box_model_block_c.v).

   Segments and the read-only premise (two Theorem Labs lanes, 23:37Z). The contract is stated over the walk's
   segment list SEGS := AB1v.tfibsegs, not over an abstract PA image's pa_segs: the PA values (VAL, BASE,
   pa_relro_lo, pa_relro_hi) are those of the CONCRETE image instance CtrlImg.PI_ctrl (CtrlImg.v:82), whose
   pa_segs is tfibsegs, so CtrlCallerJ's shapes, stated over pa_segs PI, apply by conversion. The read-only
   premise is YE01.arodata_okS (core), as in a Theorem Labs lane's ctl_base, not arodata_okP SEGS pa_relro_lo
   pa_relro_hi; the glue reaches arodata_okP from it by a Theorem Labs lane's ProgWorld lemma arodata_okP_of_S.

   build_dt1_single (0x86a94) is a LEAF inside the lifted stretch: this spec takes no build_dt1_single
   hypothesis. BUILD_DT1_SINGLE_STK stays here only as the stack constant the callers name. The runtime
   hypotheses the PROOF needs (astack_malloc_realizes SEGS B 0, astack_free_law, frame_flag_lawP, the memcpy /
   memset rules) are hypotheses of the later proof section, not of the spec.

   Why a Definition and not a Theorem. A committed file holds no Admitted, so the walk's premises are named
   binders of `pb_reac_box_model_block_stmt`. The walk file states `Theorem pb_reac_box_model_block :
   treac_box_model_block_spec ...` under the same hypotheses, and the stmt follows from it by `intros`. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* a Theorem Labs lane 21:42Z: the cgif core lands in ctrl's TOP-LEVEL lib/Reusable. Anything whose name collides with a ctrl
   module of the same name is used QUALIFIED; the collided ctrl module is never Imported here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
(* the ctrl PA layer: the position-abstract listing engine and its ctrl instance. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
(* the caller-journal shapes tcj_kept / twr_ok / tsrc_ok (grant's lib/A/Prog/CtrlFinish.v:111-143, ported by a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
(* qualified only (closure rule, a Theorem Labs lane 23:38Z): the walk's segments, the concrete PA instance and
   a Theorem Labs lane's read-only shape. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 APostBase.
(* ctrl's address-free model. Required without Import (glue closure rule; RcSynth's `rc` would also shadow the
   RunCeil instance), so every name of it is written qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
(* the concrete instance is the one every PA shape here is resolved with; activated locally so that no name of
   CtrlImg is Imported (closure rule). *)
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Section d.
(* The PA layer is instantiated with the CONCRETE instance CtrlImg.PI_ctrl (CtrlImg.v:82, whose pa_segs is
   AB1v.tfibsegs), not with an abstract `Context {PI : PAImg ctrl_listing}` (a Theorem Labs lane 23:49Z). *)
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing CtrlImg.PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing CtrlImg.PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing CtrlImg.PI_ctrl A_TEXT).
Definition A_reac_box_model_blockP : Z := BASE + AF_reac_box_model_block.
(* The image objects this call names (CtrlAddr.v ctrl_obj of the v1.9.0 listing). The function itself is object
   26 (0x85b44), which the prologue stores into its side-stack frame at +16. *)
Definition A_BMB_JT : nat := 27%nat.       (* the switch's jump table, 0x219f4, 7 words; PAddHi at slot 4966 *)
Definition A_JOIN_0013 : nat := 28%nat.    (* 0x21a20, 32 bytes, copied to o for b = 2; PAddHi at slot 5109 *)
Definition A_JOIN_0014 : nat := 29%nat.    (* 0x21a60, 32 bytes, copied to o for b = 1; PAddHi at slot 5125 *)
Definition A_BMB_PC : nat := 26%nat.       (* 0x85b44, the pc word of the frame descriptor *)
Definition A_BOX_CATALOGUE : nat := 17%nat. (* 0x9e800, the table the row p comes from *)
(* The offsets from the function's start of the seven cases the jump table selects (targets 0x85c88 0x85eec
   0x85eac 0x85eb8 0x85e20 0x85f04 0x85f98). *)
Definition BMB_JOFF (k : Z) : Z :=
if k =? 0 then 0x144 else if k =? 1 then 0x3a8 else if k =? 2 then 0x368 else if k =? 3 then 0x374
else if k =? 4 then 0x2dc else if k =? 5 then 0x3c0 else 0x454.
(* the byte lists of the model, as the image holds them *)
Definition bmb_z (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.
(* The stack each call needs. build_dt1_single's own frame is 48 (`addi sp,sp,-48` at 0x86a94) and below it its
   __asan_memcpy (0x86cd8) needs the runtime window ESTACK = 4096. This function's own frame is 160
   (`addi sp,sp,-160` at 0x85b44) plus the 16 bytes the `andi sp,sp,-32` at 0x85b84 may drop, and
   build_dt1_single is its deepest callee. Names: a Theorem Labs lane's ruling (catalogue_match-spec-draft.md section 5 Q3 (a working note, not in this delivery)).
   The value is 4320, not ctrl's K = 4272, because in cgif form every runtime callee needs ESTACK and the
   real-stack probe arm (sp1 - 4096) is dead. *)
Definition BUILD_DT1_SINGLE_STK : Z := 48 + ESTACK.              (* = 4144 *)
Definition REAC_BOX_MODEL_BLOCK_STK : Z := 176 + BUILD_DT1_SINGLE_STK.   (* = 4320 *)
(* The journal events this call adds. It takes one class-0 side-stack frame (__asan_stack_malloc_0 at 0x85bb8)
   and releases it (the flag store `ld a0,56(s2)` / `sb zero,0(a0)` at 0x864f4 / 0x864f8); neither is an
   allocator event: aj_stack_malloc_atS keeps the journal index k and gives st_nev S2 = st_nev Sc and
   blocks_bytes S2 = blocks_bytes Sc (YC85.v:301, :304), and the flag store is a plain store. No callee on the
   path allocates (memset, memcpy, build_dt1_single). So the count is 0, as in a Theorem Labs lane's EV_REPLY. *)
Definition EV_BMB : Z := 0.
Section e.
Variable B : asyms.
(* the registered globals, as the callers' specs carry them (the row's table and the name strings) *)
Variable GLOBS : list (Z * Z).
(* o lies in a side-stack frame of the caller's, or on the machine stack. Either way its shadow survives this
   call's own frame: a frame's shadow bytes are client bytes (cgif lib/YG0n.v:229-233), and AR keeps the machine
   stack's shadow zero. *)
Definition tbmb_o_home (lyc : alayout) (Sc : astate) (o : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\ cid <> 0 /\ forall x, o <= x < o + 32 -> in_zr x (frame_rng lyc (cid, pos)))
\/ (ly_stk_lo lyc <= o /\ o + 32 < ly_stk_hi lyc).
Definition treac_box_model_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (p b o : Z) (row nb : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr regs 1) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_BMB) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(if (p =? 0) || (o =? 0)
 then lib.Reusable.YK11.getr regs2 10 = w64 (-1) /\
      tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc Sc W memc W2 mem2 (spZ regs) (fun _ => False)
 else lib.Reusable.YK11.getr regs2 10 = w64 (RcSynth.rc row b) /\
      garr8 SEGS (mrestrict (w_H W2) mem2) o (bmb_z (RcSynth.synth row b nb)) /\
      tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + 32)).
(* The contract. `a` is the entry pc, `rlo` / `rhi` the read-only window of the RO premise, as a Theorem Labs lane's
   ctl_base takes them. There is no `achain` premise (a Theorem Labs lane 00:04Z): the walk cannot supply a chain at the
   callee call sites, and cgif's astack_malloc_realizes does not need one. *)
Definition treac_box_model_block_spec (a : Z) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p b o : Z) (row nb : list byte),
ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YE01.arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= raZ regs ->
lib.Reusable.YK11.getr regs 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
lib.Reusable.YK11.getr regs 10 = w64 p -> lib.Reusable.YK11.getr regs 11 = w64 b -> lib.Reusable.YK11.getr regs 12 = w64 o ->   (* a0 = p, a1 = b, a2 = o *)
0 <= p < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_BOX_MODEL_BLOCK_STK -> spZ regs <= sp0 ->
(* room for the class-0 frame __asan_stack_malloc_0 takes at 0x85bb8 *)
count_cid 0 (frames Sc) < fs_frames 0 ->
(* the 296-byte row at p: a row of a registered, read-only image table (BOX_CATALOGUE, object 17, in
   PT_GNU_RELRO); arodata_okS carries its bytes *)
(p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
           garr8 SEGS (mrestrict (w_H W) memc) p (bmb_z row) /\
           (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
           IMG_LO + 64 <= p /\ p + 296 + 64 <= IMG_HI /\
           (forall x, p <= x < p + 296 -> in_roP SEGS rlo rhi x /\
              ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
           (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
(* the name the row points to (a read-only image string), read byte by byte for b = 5 and b = 6 *)
(p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
           RcBox.name_ok nb /\
           garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname row) (bmb_z nb) /\
           (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\
              RcSynth.rname row + Z.of_nat (length nb) <= q + sz) /\
           (forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) ->
              in_roP SEGS rlo rhi x /\
              ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
           (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o)) ->
(* the 32 bytes at o: the caller's, which it lets this call write *)
(o <> 0 -> tbmb_o_home lyc Sc o /\
           (forall x, o <= x < o + 32 -> ~ in_img SEGS x) /\
           twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32 /\
           tsrc_ok W memc (spZ regs) o 32 /\
           (spZ regs <= o \/ o + 32 <= spZ regs - REAC_BOX_MODEL_BLOCK_STK)) ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(treac_box_model_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p b o row nb).
(* What the walk proves, with the walk's premises as named binders. RLO / RHI are the read-only range of the RO
   premise. JE k is the jump table's word k (0x64294 0x644f8 0x644b8 0x644c4 0x6442c 0x64510 0x645a4 in
   fuzz_ctrl.asan), so the `jr` at 0x85c84 goes to VAL (A_OBJ A_BMB_JT) + JE k = the case's pc. Each image fact
   is a fact of the image alone; a Theorem Labs lane discharges it from the ctrl instance by vm_compute over the image's
   read-only bytes. *)
Variables RLO RHI : Z.
(* RELRO: the relro window of the RO premise lies in the image (cgif lib/YC20.v:56); ROFL: it lies below the sink's
   overflow head (APostBase.ro_below_ofl). With them the RO premise carries from the entry memory to every later
   memory of the journal (APostBase.arodata_ok_journalP), which the proof needs at the allocator's return. The
   composer discharges both from PI_ctrl's pa_relro range. *)
Definition pb_reac_box_model_block_stmt : Prop :=
forall (RELRO : forall a, RLO <= a < RHI -> in_img SEGS a)
  (ROFL : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.ro_below_ofl SEGS RLO RHI)
  (TL : PALib B) (LAWS : AR_laws SEGS B) (ML : model_laws (as_universe B))
  (* the runtime rules the walk applies: the two intrinsics, the class-0 fake stack and the flag release *)
  (AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset))
  (AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy))
  (ASM0 : astack_malloc_realizes SEGS B 0)
  (SMP : stack_malloc_progressP B)
  (ASF : astack_free_law SEGS B)
  (FFL : frame_flag_lawP SEGS B)
  (TLF : PALibF B)
  (* what the image holds *)
  (JE : Z -> Z)
  (HJT_rng : IMG_LO + 64 <= VAL (A_OBJ A_BMB_JT) /\ VAL (A_OBJ A_BMB_JT) + 28 + 64 <= IMG_HI)
  (HJT_pos : forall k, 0 <= k <= 6 -> 0 <= JE k < 2 ^ 31)
  (HJT_eq : forall k, 0 <= k <= 6 ->
     VAL (A_OBJ A_BMB_JT) + JE k = A_reac_box_model_blockP + BMB_JOFF k)
  (HJT_e : forall (H : word -> bool) mem k, 0 <= k <= 6 ->
     YE01.arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
     lib.Reusable.YI04.val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_BMB_JT) + 4 * k) 4 (JE k))
  (HJ13_rng : IMG_LO + 64 <= VAL (A_OBJ A_JOIN_0013) /\ VAL (A_OBJ A_JOIN_0013) + 32 + 64 <= IMG_HI)
  (HJ14_rng : IMG_LO + 64 <= VAL (A_OBJ A_JOIN_0014) /\ VAL (A_OBJ A_JOIN_0014) + 32 + 64 <= IMG_HI)
  (HJ13 : forall (H : word -> bool) mem,
     YE01.arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_JOIN_0013)) (bmb_z RcSynth.J13))
  (HJ14 : forall (H : word -> bool) mem,
     YE01.arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_JOIN_0014)) (bmb_z RcSynth.J14))
  (* The bytes of the image's constants are marked usable, and the shadow of the image's read range is mapped
     (CtrlRo.v). The two JOIN blocks are 32-byte registered globals (asan_globals entries 53 and 54: size 0x20,
     size with red zone 0x40), so in_zs; the row names are registered globals of 7 to 9 bytes, so only
     globs_marked. *)
  (HGM : globs_marked SEGS B GLOBS)
  (HIMGSH : img_shadow_vis SEGS B)
  (HZS_J13 : in_zs B (VAL (A_OBJ A_JOIN_0013)) 32)
  (HZS_J14 : in_zs B (VAL (A_OBJ A_JOIN_0014)) 32),
treac_box_model_block_spec A_reac_box_model_blockP RLO RHI.
End e.
End d.
End b.
