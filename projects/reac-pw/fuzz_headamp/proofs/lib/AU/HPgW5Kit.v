(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths changed; 428 of its 479 lines of code are new or changed and 539 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Kit.v and RPgW5Seg.v at 164759458cd (one
   file); module paths changed, the w5_ prefix renamed to hw5_, rm_ -> hm_, rl_ -> hd_, rs_ -> hsu_ (the cut states of
   lib/AU/HPgSeg.v), the code table moved to image B of fuzz_headamp, the AR_laws Section hypothesis replaced by the
   kernel theorem YG0q.AR_laws_ok, and the segment's start facts read at image B's record (class-4 frame, real frame
   of 0x220 bytes). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the shared part of three
   pieces of the walk of LLVMFuzzerTestOneInput (0x80c40): the Int-7 value pod (SELI 0x828ec -> LATCH 0x82ae4), the
   params Struct's header and its pod count (SELS 0x816fc -> C 0x81888 / CL 0x82a18) and the Struct's close
   (CL 0x82a18 -> LATCH 0x82ae4). Proves no function (kind: segment lemma).

   HOW A PIECE IS WALKED. A piece starts at a pc with semantic facts: the harness's journal, the registers it reads,
   the 8-byte real-frame cells at R + off it reads (val_mem), pp->len at pp + 0x4000, and bounds. It builds the
   kit engine's symbolic state there (lib/Reusable YI04 entry_st_ok_full): the registers as atoms of
   Ereg regs extra (atom n < 32 is register n, atom 32 the runtime's shadow offset K = 0x7fff8000, atoms 33.. the
   piece's own quantities), regions over the cells it reads or writes, and aliases that name an address the code
   forms by `add` from pp and a length. The instrumented checks run through the engine's shadow tokens (YCbn);
   every check on pp is COVERED by a shadow entry over pp's bytes (hw5_shent_blk), so it costs no obligation. The
   UBSan tests (a branch to the trap `unimp` at 0x83a14) are decided by the atoms' range facts and the start
   state's conditions. The run (YCbq SRr_run_to_tok_AJ) ends at the piece's last pc or at a callee's entry; the
   post (hw5_post) is read off the final symbolic state.

   THE CODE (hw5_tbl): the words of [0x816fc, 0x8188c) (the open piece), [0x828ec, 0x82bec) (the Int-7 piece, the
   open piece's no-input arm 0x829d0 .. 0x829d8, the close piece and the slow blocks of all three, 0x82b2c ..
   0x82be8), [0x83a10, 0x83a18) (the two `unimp` traps) and [0x83c00, 0x83dc0) (the report entries the engine
   decodes to tell an out-of-line report from a slow block: 0x83c24 .. 0x83d98). Measured by following every branch
   of the three pieces over the listing of the unstripped twin.

   THE BRIDGE (second half): the cut states of lib/AU/HPgSeg.v read back as the core walks' explicit facts
   (hw5_at_reg, hw5_at_cell, hw5_pre_facts), a cut's segment frame carried across a piece's hw5_post
   (hw5_core_post), and the first block's image rebuilt from its parts (hw5_img_buf, hw5_img_flags, hw5_img_gen,
   hw5_img_close_eq). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the code and the context ======================================== *)
Definition hw5_tbl : ctable :=
  build_table rsegs 0x816fc 100 (build_table rsegs 0x828ec 192
    (build_table rsegs 0x83a10 2 (build_table rsegs 0x83c00 112 TEmpty))).
Lemma hw5_tbl_ok : table_ok rsegs hw5_tbl.
Proof.
unfold hw5_tbl. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
Lemma hw5_wx : wx_segs_nowrap rsegs.
Proof. exact HPgSteps.img_wx. Qed.
Lemma hw5_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact HPgSteps.img_segs_low. Qed.
(* env slot 32 is the runtime's shadow offset K; the band of shadow addresses the tokens may name *)
Definition HW5_SB : Z := 0x7fff8000.
Definition hw5_Bx : sv := SOff 32 0.
Definition hw5_Bspan : Z * Z := (HW5_SB, HW5_SB + 2 ^ 44 - 1).
Lemma hw5_SB_K : HW5_SB = SHADOW_OFF.
Proof. reflexivity. Qed.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s11` *)
Definition hw5_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) hw5_Bx.
(* the entry registers: the atoms of Ereg with the overrides ov (register, the value the start state gives it) *)
Definition hw5_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* ======================================== engine helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
Lemma hw5_regs_ok_override : forall E sr regs (r : bv 5) e,
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
Lemma hw5_regs_ok : forall E regs extra (ov : list (bv 5 * sv)), E = Ereg regs extra ->
Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) ov ->
regs_ok E (hw5_sr ov) regs.
Proof.
intros E regs extra ov -> Hov. unfold hw5_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply hw5_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
(* the engine's entry state, over an environment named by its equation *)
Lemma hw5_entry : forall segs pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof. intros segs pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
Lemma hw5_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. subst r. apply H. reflexivity. Qed.
(* a value the start state names: an atom plus an offset, read as an unsigned word *)
Lemma hw5_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. apply (U_atom_off E n v c Hn Hv Hc).
Qed.
Lemma hw5_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 HW5_SB ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
sv_denot E (hw5_sh n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn HK Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold hw5_sh, hw5_Bx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn) by lia. rewrite (U_atom E 32 HW5_SB HK) by (unfold HW5_SB; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite <- hw5_SB_K. rewrite zcanon_id by (unfold M64, HW5_SB; lia). lia.
Qed.
(* the byte a one-byte chunk holds *)
Lemma hw5_mbyte_chunk1 : forall segs E (m : word -> option byte) base off e,
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
Lemma hw5_regs_kept : forall E E' K sr0 srf (regs regs2 : bvmap 5 word) (clob : list (bv 5)),
regs_ok E sr0 regs -> regs_ok E' srf regs2 -> env_agree K E E' ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob ||
  (sv_eqb (sr_get srf r) (sr_get sr0 r) && sv_atoms_lt K (sr_get sr0 r))) HPgSteps.nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.
Proof.
intros E E' K sr0 srf regs regs2 clob H0 Hf HA Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (HPgSteps.in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply andb_prop in Hq as [Hq Hat]. apply sv_eqb_eq in Hq.
  rewrite (Hf r), Hq, (H0 r). apply (sv_denot_agree K E E' _ HA Hat).
Qed.
(* the bytes a run keeps: every address outside the write windows of its start regions *)
Lemma hw5_kept_run : forall segs E rs (H : word -> bool) (m m' : word -> option byte) a,
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
Definition hw5_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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
Lemma hw5_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a shadow entry over bytes of a live block: they are marked usable, and they lie outside the shadow band *)
Lemma hw5_shent_blk : forall ly S W mem md p m E n lo hi a0,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
ew E n = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> ew E 32 = Z_to_bv 64 HW5_SB ->
0 <= lo <= hi -> p <= a0 + lo -> a0 + hi <= p + req_size m ->
shent_ok rsegs hw5_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md p m E n lo hi a0 HAR Hin Hn Ha0 HK Hlh Hlo Hhi.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E hw5_Bx = SHADOW_OFF) by (unfold hw5_Bx; rewrite (U_atom E 32 HW5_SB HK) by (unfold HW5_SB; lia); reflexivity).
assert (UN : U E (SOff n 0) = a0) by (apply U_atom; assumption).
split; cbn [she_m she_lo she_hi].
- rewrite UB, UN. rewrite <- aview_rd_of.
  apply (range_addressable_of_block rsegs B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End f.

(* ==================================================================================================
   THE BRIDGE between the cut states of lib/AU/HPgSeg.v and the core walks
   ================================================================================================== *)
Section a. Context {fx : YK11.FPState}.
(* a register named by Z_to_bv 5 r (hd_at's form) is the register named by the literal *)
Lemma hw5_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.
End a.

(* ---- byte lists ---- *)
Lemma hw5_nth_ow : forall (l bs : list byte) off j d, (off + length bs <= length l)%nat ->
nth j (overwrite l off bs) d = if ((off <=? j) && (j <? off + length bs))%nat then nth (j - off) bs d else nth j l d.
Proof.
intros l bs off j d Hl. unfold overwrite.
assert (Hf : length (firstn off l) = off) by (apply firstn_length_le; lia).
destruct (Nat.leb_spec off j) as [H1|H1]; cbn [andb].
- rewrite app_nth2 by lia. rewrite Hf.
  destruct (Nat.ltb_spec j (off + length bs)) as [H2|H2].
  + rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
- rewrite app_nth1 by lia. rewrite nth_firstn. destruct (Nat.ltb_spec j off); [reflexivity | lia].
Qed.
Lemma hw5_len_ow : forall (l bs : list byte) off, (off + length bs <= length l)%nat ->
length (overwrite l off bs) = length l.
Proof. intros l bs off H. apply length_overwrite. exact H. Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* bytes rebuilt pointwise: the ones Pb marks are read off the new state, the others are the old list's and
   unchanged in memory *)
Lemma hw5_bytes_merge : forall H mem H' mem' a (l l' : list byte) (Pb : Z -> bool),
hm_bytes rsegs H mem a l -> length l' = length l ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = false ->
  aview rsegs H' mem' (a + Z.of_nat j) = aview rsegs H mem (a + Z.of_nat j) /\
  nth j l' (Z_to_bv 8 0) = nth j l (Z_to_bv 8 0)) ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = true ->
  aview rsegs H' mem' (a + Z.of_nat j) = Some (bv_unsigned (nth j l' (Z_to_bv 8 0)))) ->
hm_bytes rsegs H' mem' a l'.
Proof.
intros H mem H' mem' a l l' Pb Hb Hlen Hout Hin. apply hm_bytes_aview. intros j Hj. rewrite Hlen in Hj.
destruct (Pb (a + Z.of_nat j)) eqn:E; [exact (Hin j Hj E)|].
destruct (Hout j Hj E) as [A N]. rewrite A, N. exact (proj1 (hm_bytes_aview rsegs H mem a l) Hb j Hj).
Qed.
End m.

(* ---- the record ---- *)
Lemma hw5_find_none : forall (f : Z * pval -> bool) ps, existsb f ps = false -> find f ps = None.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [reflexivity|].
intros H. apply orb_false_iff in H as [H1 H2]. rewrite H1. exact (IH H2).
Qed.
Lemma hw5_find_some : forall (f : Z * pval -> bool) ps, existsb f ps = true -> exists x, find f ps = Some x.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [discriminate|].
intros H. destruct (f x) eqn:E; [exists x; reflexivity|]. apply IH. exact H.
Qed.
Lemma hw5_first1 : forall ps, hsu_first ps = 1 -> first_params ps = None.
Proof.
intros ps H. unfold hsu_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [discriminate|].
rewrite (hw5_find_none _ ps E). reflexivity.
Qed.
Lemma hw5_first0 : forall ps, hsu_first ps <> 1 -> exists v, first_params ps = Some v.
Proof.
intros ps H. unfold hsu_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [|lia].
destruct (hw5_find_some _ ps E) as (x & Hx). rewrite Hx. exists (snd x). reflexivity.
Qed.
Lemma hw5_first_range : forall ps, hsu_first ps = 0 \/ hsu_first ps = 1.
Proof. intros ps. unfold hsu_first. destruct (negb _); cbn; lia. Qed.
Lemma hw5_plen_lo : forall sh ps, sh <> 7 -> 16 <= hsu_plen sh ps.
Proof.
intros sh ps Hsh. unfold hsu_plen, pc_buf, body_bytes, hdr_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
rewrite !app_nil_r, !zlen_app, !zlen_le32. pose proof (Zle_0_nat (length (flat_map (prop_bytes sh) ps))). lia.
Qed.
Lemma hw5_buf_open_len : forall sh ps es,
Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) =
hsu_plen sh ps + 16 + Z.of_nat (length (flat_map enc_pod es)).
Proof.
intros sh ps es. unfold hsu_plen, pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
rewrite app_nil_r, !zlen_app, !zlen_le32. lia.
Qed.

Section bb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* a fact of a cut's (location, value) list, read back *)
Lemma hw5_at_reg : forall H mem regs e (L : list (hd_loc * Z)) r v,
hsu_at rsegs H mem regs e L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma hw5_at_cell : forall H mem regs e (L : list (hd_loc * Z)) o v,
hsu_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.

(* the cut's segment frame across a piece *)
Lemma hw5_core_post : forall cx (E1 Ep : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 pc clob
  (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
  hsu_core rsegs B MT cx E1 ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, Ep a -> E1 a) ->
  (forall r, (r = 2 \/ r = 3 \/ r = 4) -> ~ In (Z_to_bv 5 r) clob) ->
  hw5_post B MT (x_STK _ cx) (x_sp0 _ cx) (x_FP _ cx) (x_ly _ cx) (x_S _ cx) (x_W0 _ cx) (x_mem0 _ cx) (x_md0 _ cx)
    (x_own _ cx) (x_k _ cx) regs2 ly2 S2 W2 mem2 md2 pc clob Ep R W3 c3 ->
  exists ly3 S3 regs3 mem3 md3, c3 = cfg_at rsegs pc regs3 mem3 md3 /\
    hsu_core rsegs B MT cx E1 ly3 S3 W3 regs3 mem3 md3 /\
    (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - T_SEG_STK <= a < spZ regs2) -> ~ Ep a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) /\
    R W3 regs3 mem3.
Proof using MTL.
intros cx E1 Ep ly2 S2 W2 regs2 mem2 md2 pc clob R W3 c3 Hcore HE Hc
  (ly3 & S3 & regs3 & mem3 & md3 & Hcfg & HJ3 & Hregs & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct Hcore as (HJ2 & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
assert (Hsp : spZ regs2 = spZ (x_regs _ cx)).
{ unfold spZ. rewrite <- !(hw5_getr5 _ 2%bv 2) by reflexivity. rewrite (Hr234 2); [reflexivity | lia]. }
exists ly3, S3, regs3, mem3, md3. split; [exact Hcfg|].
split.
{ split; [exact HJ3|]. split.
  { intros r Hr. rewrite Hregs; [apply Hr234; exact Hr| |apply Hc; exact Hr].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. destruct Hr as [-> | [-> | ->]]; vm_compute; discriminate. }
  split; [rewrite Hfr; exact Hfr2|].
  split; [eapply Permutation_trans; [exact Hperm | exact Hperm2]|].
  split; [eapply same_io_trans; [exact Hio2 | exact Hio]|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo)|].
  intros a Ha Hst HnE. rewrite (Hmem a Ha); [apply Hmem2; assumption | rewrite Hsp; exact Hst |].
  intros HEp. exact (HnE (HE a HEp)). }
split; [exact Hregs|]. split; [exact Hmem | exact HR].
Qed.
End bb.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* membership in a cut's (location, value) list, and a register outside a clobber list *)
Ltac hw5_in := cbn [hsu_L_KEY hsu_L_pod hsu_L_Dc hsu_L_SEL hsu_L_N hsu_L_P hsu_L_post hsu_Rc1 hsu_Rc0 hsu_Kc
  hsu_cur2 app In fst snd]; repeat (first [left; reflexivity | right]).
Ltac hw5_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a location of the end cut that the piece kept: from the start cut's list Hat, its register outside the clobber
   list (Hkeep) or its 8 bytes in a range the piece did not write (Kc) *)
Ltac hw5_kept Hat Hkeep Kc := lazymatch goal with |- hd_at _ _ _ _ _ ?l ?v =>
  apply (hm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(hw5_in)));
  cbn [hm_keeps hd_xv];
  first [ apply Hkeep; [vm_compute; discriminate | hw5_notin]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.

(* ======================================== the segment's start ======================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* the real frame, the frame for locals and the first block, as the segment's start fixes them (image B: the real
   frame is 0x220 bytes below S, the frame for locals a class-4 side-stack frame of 1024 bytes) *)
Lemma hw5_pre_facts : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\
  e_R (x_e cx) mod 32 = 0 /\ getr (x_regs cx) 2 = w64 (e_R (x_e cx)) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  ~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE /\
  in_app (e_F (x_e cx)) 1024.
Proof.
intros cx sh Hpre. unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR32 & HRs & HRstk & Hown & HF & Hfsh & Hcap & Hnull & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hguard & Hrom & (Hpp0 & Hpp & Hout)).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
assert (Hin : In (hi_cid headamp_himg_B, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3).
rewrite <- HF in F1, F2, F3. cbn [hi_cid headamp_himg_B] in F2, F3. change (fs_frame_bytes 4) with 1024 in F2, F3.
pose proof asan_consts as (C1 & _). cbn [hi_rsz headamp_himg_B] in HRs.
unfold T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|]. split; [exact HR32|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact Hpp|]. split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Happ | exact F3].
Qed.
End s.

(* ======================================== the first block's image ======================================== *)
Section i. Context {fx : YK11.FPState}.
(* buf[0..len) of an image *)
Lemma hw5_img_buf : forall H mem pp b isp hp pst es corr,
hm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) -> hm_bytes rsegs H mem pp b.
Proof. intros H mem pp b isp hp pst es corr Hb. rewrite pp_image_tail in Hb. apply hm_bytes_app in Hb as [Hb _]. exact Hb. Qed.
(* the two flag words of an image, carried to a state that keeps them *)
Lemma hw5_img_flags : forall H mem H' mem' pp b isp hp pst es corr,
Z.of_nat (length b) <= POD_BUF_MAX -> (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
hm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
(forall y, pp + OFF_HAS_PARAMS <= y < pp + OFF_ENT -> aview rsegs H' mem' y = aview rsegs H mem y) ->
hm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp)) /\
hm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst)).
Proof.
intros H mem H' mem' pp b isp hp pst es corr Hb He Hs Old K.
pose proof (hm_pp_has_params rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V1.
pose proof (hm_pp_params_struct rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V2.
split; (eapply hm_bytes_kept; [apply hm_bytes_of_val; eassumption|]);
  intros y Hy; rewrite ?length_le32, ?length_Z_to_le_bytes in Hy; apply K; unfold OFF_HAS_PARAMS, OFF_PARAMS_STRUCT, OFF_ENT in *; lia.
Qed.
(* an image rebuilt from its parts: buf[0..len) grown or patched (b'), len, the two flag words, every other byte
   kept from the old image (the zeros after b', is_props, the entries and what follows them) *)
Lemma hw5_img_gen : forall H mem H' mem' pp b b' isp hp pst hp' pst' es corr,
(length b <= length b')%nat -> Z.of_nat (length b') <= POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
hm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
hm_bytes rsegs H' mem' pp b' ->
val_mem rsegs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b')) ->
hm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp')) ->
hm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst')) ->
(forall y, pp + Z.of_nat (length b') <= y < pp + OFF_LEN \/ pp + OFF_IS_PROPS <= y < pp + OFF_HAS_PARAMS \/
  pp + OFF_ENT <= y < pp + PP_SIZE -> aview rsegs H' mem' y = aview rsegs H mem y) ->
hm_bytes rsegs H' mem' pp (pp_image b' isp hp' pst' es corr).
Proof.
intros H mem H' mem' pp b b' isp hp pst hp' pst' es corr Hbb Hb' He Hs Old Nb Nlen Nh Np K.
assert (Hb : Z.of_nat (length b) <= POD_BUF_MAX) by lia.
pose proof (length_pp_image b isp hp pst es corr Hb He Hs) as LI.
rewrite pp_image_tail in LI, Old |- *. unfold pp_tail in LI, Old |- *.
remember (flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
  ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4) as T eqn:ET.
clear ET.
assert (Ez : zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)))
  = zeros (length b' - length b) ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b')))).
{ rewrite <- zeros_app. f_equal. unfold POD_BUF_MAX in *. lia. }
rewrite Ez in Old, LI. rewrite <- app_assoc in Old.
rewrite !length_app, !length_zeros, length_le64, !length_le32 in LI.
unfold PP_SIZE, POD_BUF_MAX in *.
apply hm_bytes_app in Old as [_ Old]. apply hm_bytes_app in Old as [_ Old].
apply hm_bytes_app in Old as [Ozk Old]. apply hm_bytes_app in Old as [_ Old].
apply hm_bytes_app in Old as [Oi Old]. apply hm_bytes_app in Old as [_ Old].
apply hm_bytes_app in Old as [_ OT].
repeat (first [rewrite length_zeros in Ozk | rewrite length_zeros in Oi | rewrite length_zeros in OT |
  rewrite length_le64 in Oi | rewrite length_le64 in OT | rewrite length_le32 in OT]).
apply hm_bytes_app. split; [exact Nb|].
apply hm_bytes_app. split.
{ eapply hm_bytes_kept.
  - replace (pp + Z.of_nat (length b')) with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b)) by lia.
    exact Ozk.
  - intros y Hy. rewrite length_zeros in Hy. apply K. left. unfold OFF_LEN. lia. }
rewrite length_zeros.
apply hm_bytes_app. split.
{ unfold le64. apply hm_bytes_of_val.
  replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b')))) with (pp + OFF_LEN)
    by (unfold OFF_LEN; lia). exact Nlen. }
rewrite length_le64.
apply hm_bytes_app. split.
{ eapply hm_bytes_kept.
  - replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8)
      with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
            Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8) by lia.
    exact Oi.
  - intros y Hy. rewrite length_le32 in Hy. apply K. right. left. unfold OFF_IS_PROPS, OFF_HAS_PARAMS. lia. }
rewrite length_le32.
apply hm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4)
    with (pp + OFF_HAS_PARAMS) by (unfold OFF_HAS_PARAMS; lia). exact Nh. }
rewrite length_le32.
apply hm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4) with (pp + OFF_PARAMS_STRUCT) by (unfold OFF_PARAMS_STRUCT; lia). exact Np. }
rewrite length_le32.
eapply hm_bytes_kept.
- replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4 + Z.of_nat 4)
    with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
          Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) by lia.
  exact OT.
- intros y Hy. apply K. right. right. unfold OFF_ENT. lia.
Qed.

(* the recorded pods of a cut: at most 32, each body at most 96 bytes *)
Lemma hw5_ents_bounds : forall sh ps o, hsu_wf sh ps ->
(match o with Some es => Forall ent_wf es /\ (length es <= 32)%nat | None => True end) ->
(length (pc_ents (PbCut sh ps o)) <= 32)%nat /\ Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps o)).
Proof.
intros sh ps o (Hs & Hk & He & Hl) Ho.
assert (Hbody : forall l, Forall ent_wf l -> Forall (fun e => (length (e_body e) <= 96)%nat) l).
{ intros l Hl'. eapply Forall_impl; [|exact Hl']. intros e (_ & Hb & Hz). rewrite Hb. lia. }
unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _].
  rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv']. rewrite E in Hv'. cbn in Hv'.
  split; [exact Hv'|]. apply Hbody.
  apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- destruct o as [es|]; [destruct Ho as [Ho1 Ho2]; split; [exact Ho2 | apply Hbody; exact Ho1] |
  split; [cbn; lia | constructor]].
Qed.
(* the image at the Struct's close (Model.pc_buf_close; pod.h:434-438): the size word patched, and the two flag
   words set when this Struct is the first params property *)
Lemma hw5_img_close_eq : forall sh ps es, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) =
pp_image (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (hsu_at_of sh ps))
           (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - hsu_at_of sh ps - 8)))
  (is_props (PodRec sh ps None))
  (has_params (PodRec sh ps None) || (hsu_first ps =? 1))
  (params_struct (PodRec sh ps None) || (hsu_first ps =? 1))
  (pc_ents (PbCut sh ps (Some es))) false.
Proof.
intros sh ps es Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
change (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
  with (pc_buf (pc_close (PbCut sh ps (Some es)))).
rewrite <- (pc_buf_close sh ps es Hsh).
replace (Z.to_nat (hsu_at_of sh ps)) with (length (pc_buf (PbCut sh ps None)) + 8)%nat
  by (unfold hsu_at_of, hsu_plen; lia).
replace (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - hsu_at_of sh ps - 8)
  with (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16)
  by (unfold hsu_at_of, hsu_plen; lia).
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (Z.eqb_spec (hsu_first ps) 1) as [E|E].
- rewrite (hw5_first1 ps E). cbn [fst snd]. rewrite Z.eqb_refl. reflexivity.
- destruct (hw5_first0 ps E) as [v Hv]. rewrite Hv.
  destruct v; reflexivity.
Qed.
End i.

Print Assumptions hw5_tbl_ok.
Print Assumptions hw5_shent_blk.
Print Assumptions hw5_core_post.
Print Assumptions hw5_pre_facts.
Print Assumptions hw5_img_gen.
Print Assumptions hw5_img_close_eq.
