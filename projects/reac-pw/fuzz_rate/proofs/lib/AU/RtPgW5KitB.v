(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the
   save-slot region, regs_ok_override / ck_regs_ok / ck_lit / ck_atom, ck_kept_run, awr_stk / kwr_stk, the run /
   keep / leaf chain, ck_wx / ck_segs_low) and proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v at 77f59d02b01 (the .got
   word and shadow-offset cell regions with base None and their al_const proofs) for reac-pw/fuzz_headamp's image A
   (fuzz_headamp.asan): the common plumbing of the walks of headamp's check functions against lib/A/HPgCSpec.v's
   hd_check_*_specX. What is new against role's files: the .got word 0x9c370 and the cell 0xa4db8 of this image;
   the entry state takes data regions and pointer facts as arguments (role's check functions read no memory); the
   shadow entries of the token engine (YCbn.v) for the checked pointer ranges, proved from the contracts'
   range_addressable and hd_app_rng premises (hc_shent); the leaf closes HPgCSpec's hd_post (its ra clause and its
   stack window T_check_STK = 32 around the 16-byte save slot); AR's laws come from the kernel theorem
   YG0q.AR_laws_ok, not a Section hypothesis. Everything here is generic over the segments and over the .got word
   and the cell (hc_entry_at, hc_app_apart_at, hc_prelude_with); the last block is image A's instance, and
   lib/AU/HPgChkBaseU.v is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgChkBase.v, with its module paths changed; 117 of its 167 lines of code are new or changed and 313 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Kit.v at dc0c32440025 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; the table
   holds rate's code ranges of the three pieces (SELS 0x81150, SELI 0x82280, CL 0x82484), their slow blocks and the
   error-path entries; the role vocabulary rm_ / rl_ becomes rate's rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Kit.v at a66696a9b1d1 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the table holds image B's code ranges of the three
   pieces (SELS 0x81210 -> C 0x813a0; SELI 0x82398 -> LATCH7 0x8257c with CL 0x824c0 -> LATCH 0x82578), their slow
   blocks and the error-path entries; the image facts come from lib/AU/RtPgStepsB.v; the prefix w5_ becomes w5b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the shared part of three
   pieces of the walk of LLVMFuzzerTestOneInput (0x8076c): the Int-7 value pod (SELI 0x82398 -> LATCH7 0x8257c), the
   params Struct's header and its pod count (SELS 0x81210 -> C 0x813a0 / CL 0x824c0) and the Struct's close (CL
   0x824c0 -> LATCH 0x82578). Proves no function (kind: segment lemma).

   HOW A PIECE IS WALKED. A piece starts at a pc with semantic facts: the harness's journal, the registers it reads,
   the 8-byte real-frame cells at R + off it reads (val_mem), pp->len at pp + 0x4000, and bounds. It builds the
   kit engine's symbolic state there (lib/Reusable YI04 entry_st_ok_full): the registers as atoms of
   Ereg regs extra (atom n < 32 is register n, atom 32 the runtime's shadow offset K = 0x7fff8000, atoms 33.. the
   piece's own quantities), regions over the cells it reads or writes, and an alias that names an address the code
   forms by `add` from pp and a length (pp + at as one atom, so that its stores resolve to a region). Every atom
   bound (mkAF lo hi ..) is a closed numeral, so that the engine decides each branch by computation. The
   instrumented checks run through the engine's shadow tokens (YCbn); every check on pp is COVERED by a shadow
   entry over pp's bytes (shent_ok: the bytes are marked usable, pp's block_shadow, and lie outside the shadow
   band, pp's in_app), so its shadow byte reads as 0 and it costs no obligation, whatever its branch form. The run
   (YCbq SRr_run_to_tok_AJ) ends at the piece's last pc; the post (w5b_post) is read off the final symbolic state:
   the journal, every register outside a clobber list as at the start, the bytes the piece writes, and every other
   byte outside the callees' stack as at the start.

   THE CODE (this file needs only the table): w5b_tbl holds the words of [0x81210, 0x813a4) (SELS to C),
   [0x82398, 0x82580) (SELI, the Struct's two early exits to CL, CL and the latch's two entries), [0x825c4, 0x82684)
   (their slow blocks and the inline report of 0x8266c) and [0x83300, 0x83558) (the error-path entries the engine
   decodes to tell an out-of-line report from a slow block). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the code and the context ======================================== *)
Definition w5b_tbl : ctable :=
  build_table rsegs 0x81210 101 (build_table rsegs 0x82398 122 (build_table rsegs 0x825c4 48
    (build_table rsegs 0x83300 150 TEmpty))).
Lemma w5b_tbl_ok : table_ok rsegs w5b_tbl.
Proof.
unfold w5b_tbl. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
Lemma w5b_wx : wx_segs_nowrap rsegs.
Proof. exact RtPgStepsB.rtsb_wx. Qed.
Lemma w5b_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact RtPgStepsB.rtsb_segs_low. Qed.
(* env slot 32 is the runtime's shadow offset K; the band of shadow addresses the tokens may name *)
Definition W5B_SB : Z := 0x7fff8000.
Definition w5b_Bx : sv := SOff 32 0.
Definition w5b_Bspan : Z * Z := (W5B_SB, W5B_SB + 2 ^ 44 - 1).
Lemma w5b_SB_K : W5B_SB = SHADOW_OFF.
Proof. reflexivity. Qed.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s4` *)
Definition w5b_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) w5b_Bx.
(* the entry registers: the atoms of Ereg with the overrides ov (register, the value the start state gives it) *)
Definition w5b_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* ======================================== engine helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
Lemma w5b_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma w5b_regs_ok : forall E regs extra (ov : list (bv 5 * sv)), E = Ereg regs extra ->
Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) ov ->
regs_ok E (w5b_sr ov) regs.
Proof.
intros E regs extra ov -> Hov. unfold w5b_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply w5b_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
(* the engine's entry state, over an environment named by its equation *)
Lemma w5b_entry : forall segs pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof. intros segs pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
Lemma w5b_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. subst r. apply H. reflexivity. Qed.
(* a value the start state names: an atom plus an offset, read as an unsigned word *)
Lemma w5b_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. apply (U_atom_off E n v c Hn Hv Hc).
Qed.
Lemma w5b_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 W5B_SB ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
sv_denot E (w5b_sh n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn HK Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold w5b_sh, w5b_Bx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn) by lia. rewrite (U_atom E 32 W5B_SB HK) by (unfold W5B_SB; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite <- w5b_SB_K. rewrite zcanon_id by (unfold M64, W5B_SB; lia). lia.
Qed.
(* the byte a one-byte chunk holds *)
Lemma w5b_mbyte_chunk1 : forall segs E (m : word -> option byte) base off e,
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 e)) ->
mbyte segs m (base + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros segs E m base off e H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.
(* a register outside clob whose final symbolic value is its start value (over atoms below K, which the run's
   environment keeps) holds its start value *)
Lemma w5b_regs_kept : forall E E' K sr0 srf (regs regs2 : bvmap 5 word) (clob : list (bv 5)),
regs_ok E sr0 regs -> regs_ok E' srf regs2 -> env_agree K E E' ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob ||
  (sv_eqb (sr_get srf r) (sr_get sr0 r) && sv_atoms_lt K (sr_get sr0 r))) RtPgStepsB.nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.
Proof.
intros E E' K sr0 srf regs regs2 clob H0 Hf HA Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (RtPgStepsB.in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply andb_prop in Hq as [Hq Hat]. apply sv_eqb_eq in Hq.
  rewrite (Hf r), Hq, (H0 r). apply (sv_denot_agree K E E' _ HA Hat).
Qed.
(* the bytes a run keeps: every address outside the write windows of its start regions *)
Lemma w5b_kept_run : forall segs E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview segs H m' a = aview segs H m a.
Proof.
intros segs E rs H m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
End h.

(* ======================================== the post of a piece ========================================
   A piece ends at a fixed pc, like a segment, inside the harness's journal (no event: the pieces allocate
   nothing). It keeps sp / gp / tp and every register outside clob, the frames, blocks, I/O state and meter as at
   its start, and every byte outside the callees' stack [sp - T_SEG_STK, sp) and outside E (the bytes it writes)
   as at its start; R says what it wrote and computed. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Definition w5b_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (E : Z -> Prop) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.
End b.

(* ======================================== facts every piece re-derives ======================================== *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma w5b_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. exact RtPgStepsB.same_io_wvb. Qed.
(* a shadow entry over bytes of a live block: they are marked usable, and they lie outside the shadow band *)
Lemma w5b_shent_blk : forall ly S W mem md p m E n lo hi a0,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
ew E n = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> ew E 32 = Z_to_bv 64 W5B_SB ->
0 <= lo <= hi -> p <= a0 + lo -> a0 + hi <= p + req_size m ->
shent_ok rsegs w5b_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md p m E n lo hi a0 HAR Hin Hn Ha0 HK Hlh Hlo Hhi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E w5b_Bx = SHADOW_OFF) by (unfold w5b_Bx; rewrite (U_atom E 32 W5B_SB HK) by (unfold W5B_SB; lia); reflexivity).
assert (UN : U E (SOff n 0) = a0) by (apply U_atom; assumption).
split; cbn [she_m she_lo she_hi].
- rewrite UB, UN. rewrite <- aview_rd_of.
  apply (range_addressable_of_block rsegs B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End f.
