(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths changed; 110 of its 165 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Kit.v at 164759458cd; module paths changed, rm_ -> hm_, rl_ -> hd_, the code table moved to image A of fuzz_headamp (the three pieces' words, their slow blocks and their report entries at headamp's addresses), the AR_laws Section hypothesis replaced by the kernel theorem YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the shared part of three
   pieces of the walk of LLVMFuzzerTestOneInput (0x80bc0): the Int-7 value pod (0x82808 -> 0x82ac0), the params
   Struct's header and its pod count (0x8165c -> 0x817a0 / 0x82a14) and the Struct's close (0x82a14 -> 0x82ac0).
   Proves no function (kind: segment lemma).

   HOW A PIECE IS WALKED. A piece starts at a pc with semantic facts: the harness's journal, the registers it reads,
   the 8-byte real-frame cells at R + off it reads (val_mem), pp->len at pp + 0x4000, and bounds. It builds the
   kit engine's symbolic state there (lib/Reusable YI04 entry_st_ok_full): the registers as atoms of
   Ereg regs extra (atom n < 32 is register n, atom 32 the runtime's shadow offset K = 0x7fff8000, atoms 33.. the
   piece's own quantities), regions over the cells it reads or writes, and an alias that names an address the code
   forms by `add` from pp and a length (pp + at as one atom, so that its stores resolve to a region). The
   instrumented checks run through the engine's shadow tokens (YCbn); every check on pp is COVERED by a shadow
   entry over pp's bytes (shent_ok: the bytes are marked usable, pp's block_shadow, and lie outside the shadow
   band, pp's in_app), so it costs no obligation. The run (YCbq SRr_run_to_tok_AJ) ends at the piece's last pc;
   the post (w5_post) is read off the final symbolic state: the journal, every register outside a clobber list as
   at the start, the bytes the piece writes, and every other byte outside the callees' stack as at the start.

   THE CODE (this file needs only the table): w5_tbl holds the words of [0x8165c, 0x817a4) (the open piece),
   [0x82808, 0x82c68) (the Int-7 piece, the open piece's no-input arm 0x829d4 .. 0x829d8, the close piece and the
   slow blocks of all three, 0x82b88 .. 0x82c64) and [0x83b00, 0x83d4c) (the report entries the engine decodes to
   tell an out-of-line report from a slow block). Measured by following every branch of the three pieces over the
   listing of the unstripped twin: the reached words are [0x8165c, 0x817a0), [0x82808, 0x829dc), [0x82a14,
   0x82ac0), [0x82b88, 0x82c68), and the report entries [0x83b00, 0x83b38), [0x83c34, 0x83c54), [0x83cc0,
   0x83d4c). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the code and the context ======================================== *)
Definition w5_tbl : ctable :=
  build_table rsegs 0x8165c 82 (build_table rsegs 0x82808 280 (build_table rsegs 0x83b00 147 TEmpty)).
Lemma w5_tbl_ok : table_ok rsegs w5_tbl.
Proof.
unfold w5_tbl. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.
Lemma w5_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma w5_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
(* env slot 32 is the runtime's shadow offset K; the band of shadow addresses the tokens may name *)
Definition W5_SB : Z := 0x7fff8000.
Definition w5_Bx : sv := SOff 32 0.
Definition w5_Bspan : Z * Z := (W5_SB, W5_SB + 2 ^ 44 - 1).
Lemma w5_SB_K : W5_SB = SHADOW_OFF.
Proof. reflexivity. Qed.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s7` *)
Definition w5_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) w5_Bx.
(* the entry registers: the atoms of Ereg with the overrides ov (register, the value the start state gives it) *)
Definition w5_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* ======================================== engine helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
Lemma w5_regs_ok_override : forall E sr regs (r : bv 5) e,
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
Lemma w5_regs_ok : forall E regs extra (ov : list (bv 5 * sv)), E = Ereg regs extra ->
Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) ov ->
regs_ok E (w5_sr ov) regs.
Proof.
intros E regs extra ov -> Hov. unfold w5_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply w5_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
(* the engine's entry state, over an environment named by its equation *)
Lemma w5_entry : forall segs pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof. intros segs pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
Lemma w5_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. subst r. apply H. reflexivity. Qed.
(* a value the start state names: an atom plus an offset, read as an unsigned word *)
Lemma w5_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. apply (U_atom_off E n v c Hn Hv Hc).
Qed.
Lemma w5_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 W5_SB ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
sv_denot E (w5_sh n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn HK Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold w5_sh, w5_Bx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn) by lia. rewrite (U_atom E 32 W5_SB HK) by (unfold W5_SB; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite <- w5_SB_K. rewrite zcanon_id by (unfold M64, W5_SB; lia). lia.
Qed.
(* the byte a one-byte chunk holds *)
Lemma w5_mbyte_chunk1 : forall segs E (m : word -> option byte) base off e,
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
Lemma w5_regs_kept : forall E E' K sr0 srf (regs regs2 : bvmap 5 word) (clob : list (bv 5)),
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
Lemma w5_kept_run : forall segs E rs (H : word -> bool) (m m' : word -> option byte) a,
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
Definition w5_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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
Lemma w5_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a shadow entry over bytes of a live block: they are marked usable, and they lie outside the shadow band *)
Lemma w5_shent_blk : forall ly S W mem md p m E n lo hi a0,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
ew E n = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> ew E 32 = Z_to_bv 64 W5_SB ->
0 <= lo <= hi -> p <= a0 + lo -> a0 + hi <= p + req_size m ->
shent_ok rsegs w5_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md p m E n lo hi a0 HAR Hin Hn Ha0 HK Hlh Hlo Hhi.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E w5_Bx = SHADOW_OFF) by (unfold w5_Bx; rewrite (U_atom E 32 W5_SB HK) by (unfold W5_SB; lia); reflexivity).
assert (UN : U E (SOff n 0) = a0) by (apply U_atom; assumption).
split; cbn [she_m she_lo she_hi].
- rewrite UB, UN. rewrite <- aview_rd_of.
  apply (range_addressable_of_block rsegs B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End f.
