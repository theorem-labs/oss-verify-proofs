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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 293 of its 351 lines of code are new or changed and 232 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Kit.v and
   proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at ada533759b23 for reac-pw/fuzz_rate image A: the code table, the
   shadow band and the engine helpers are rate's (the prefix w5_ becomes rw8_, the image is images.Asan instead of
   a lib/A/Img0 module, RPgMem's rm_ lemmas become RtPgMem's rtm_); the post of a block is RtPgSteps.rts_post
   instead of a local copy; the five run statements of the piece are new. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the shared part of the
   walk piece "write + record" of LLVMFuzzerTestOneInput (0x80714), J 0x81e00 -> C 0x8127c / CL 0x82484
   (pod.h:200-206 pod_write_ent inlined, pod.h:428-433 the record copy and the pod loop's latch). Proves no
   function (kind: segment lemma): statement text and engine helpers only.

   WHAT THE PIECE DOES (listing of image A; the model is Pod/Model.enc_pod and Pod/Layout.pp_image_ent).
     0x81e00 .. 0x81f40  pod_put32(pp, e->size) at pp + len, pod_put32(pp, e->type) at pp + len + 4, then
                         __asan_memcpy(pp + len + 8, e->body, e->size) with ra = 0x81f44
     0x81f44 .. 0x81f8c  len += e->size, the pad count s8 = (8 - len % 8) % 8, then
                         __asan_memset(pp + len, 0, s8) with ra = 0x81f90
     0x81f90 .. 0x81ff4  len += s8; s8 and s10 are swapped back; if `first` (R+0x110) is set, the check of
                         pp->n_ent, n_ent += 1 and __asan_memcpy(&pp->ent[n_ent], e, 104) with ra = 0x81ff8
     0x81ff8 .. 0x82040  e goes out of scope (13 shadow bytes := 0xf8), k += 1, and `bne a1,a0` leaves to the pod
                         loop's head C 0x8127c (k + 1 <> cnt) or to the Struct's close CL 0x82484 (k + 1 = cnt).
   FIVE RUNS. The three calls cut the piece into four engine runs; the first three carry instrumented checks and
   run on the token engine (lib/Reusable/YCbn.v), the last writes the frame's shadow and runs on the plain engine
   (a shadow write is not a cell the token engine may name, so its region would fail cells_safe_b):
     rw8_runA_stmt  J 0x81e00 -> __asan_memcpy 0x51860      9 checks (pp->len x6, the 4 store_n of the two put32)
     rw8_runB_stmt  0x81f44   -> __asan_memset 0x51cfc      2 checks (pp->len)
     rw8_runC1_stmt 0x81f90   -> __asan_memcpy 0x51860      2 checks (pp->len, pp->n_ent), `first` set
     rw8_runC0_stmt 0x81f90   -> 0x81ffc                    1 check  (pp->len), `first` clear
     rw8_runD_stmt  0x81ff8 / 0x81ffc -> C 0x8127c / CL 0x82484   no check
   Every check is on the first block's bytes and is covered by the shadow entries (27, 0x4000, 0x4d18) and
   (33, 0, 16) of rw8_shent_blk, so no error path is reached and the runs leave no shadow obligation. The three
   capacity tests of pod_put / pod_pad (pod.h:177) are not taken: the two on pp->len alone are start-state
   conditions (the engine reads len - 0x3ffd as an atom with a negative offset, whose unsigned range it does not
   know), the three others follow from the atoms' ranges. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition RW8_J : Z := 0x81e00.       (* the piece's start: the inlined pod_write_ent begins *)
Definition RW8_CPY : Z := 0x51860.     (* __asan_memcpy *)
Definition RW8_SET : Z := 0x51cfc.     (* __asan_memset *)
Definition RW8_RA1 : Z := 0x81f44.     (* after the body copy *)
Definition RW8_RA2 : Z := 0x81f90.     (* after the pad fill *)
Definition RW8_RA3 : Z := 0x81ff8.     (* after the record copy *)
Definition RW8_T0 : Z := 0x81ffc.      (* the scope stores, entered directly when `first` is clear *)
Definition RW8_C : Z := 0x8127c.       (* the pod loop's head *)
Definition RW8_CL : Z := 0x82484.      (* the params Struct's close *)

(* ======================================== the code ========================================
   [0x81e00, 0x82048) is the piece and the branch that leaves it; [0x820e8, 0x82138) and [0x83280, 0x832a8) /
   [0x833a4, 0x833d8) are the slow blocks and the out-of-line report entries of its checks, which the token
   engine decodes to tell one from the other. *)
Definition rw8_tbl : ctable :=
  build_table rsegs 0x81e00 146 (build_table rsegs 0x820e8 20 (build_table rsegs 0x83280 10
  (build_table rsegs 0x833a4 13 TEmpty))).
Lemma rw8_tbl_ok : table_ok rsegs rw8_tbl.
Proof.
unfold rw8_tbl. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
(* the plain-engine table of the last run (the scope stores and the latch) *)
Definition rw8_tblD : ctable := build_table rsegs 0x81ff8 19 TEmpty.
Lemma rw8_tblD_ok : table_ok rsegs rw8_tblD.
Proof. apply build_table_ok0. lia. Qed.
Lemma rw8_wx : wx_segs_nowrap rsegs.
Proof. exact rts_wx. Qed.
Lemma rw8_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact rts_segs_low. Qed.
Lemma rw8_ret1 : YK0s.ret_ok (Z_to_bv 64 RW8_RA1).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rw8_ret2 : YK0s.ret_ok (Z_to_bv 64 RW8_RA2).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rw8_ret3 : YK0s.ret_ok (Z_to_bv 64 RW8_RA3).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* ======================================== the engine's vocabulary ======================================== *)
(* env slot 32 is the runtime's shadow offset K; the band of shadow addresses the tokens may name *)
Definition RW8_SB : Z := 0x7fff8000.
Definition rw8_Bx : sv := SOff 32 0.
Definition rw8_Bspan : Z * Z := (RW8_SB, RW8_SB + 2 ^ 44 - 1).
Lemma rw8_SB_K : RW8_SB = SHADOW_OFF.
Proof. reflexivity. Qed.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s2` *)
Definition rw8_shr (n : nat) (c : Z) : sv := SAlu ALU_SRL (SOff n c) (SLit 3).
Definition rw8_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (rw8_shr n c) rw8_Bx.
(* the entry registers: the atoms of Ereg with the overrides ov (register, the value the start state gives it) *)
Definition rw8_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* ======================================== engine helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
Lemma rw8_regs_ok_override : forall E sr regs (r : bv 5) e,
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
Lemma rw8_regs_ok : forall E regs extra (ov : list (bv 5 * sv)), E = Ereg regs extra ->
Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) ov ->
regs_ok E (rw8_sr ov) regs.
Proof.
intros E regs extra ov -> Hov. unfold rw8_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply rw8_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
(* the engine's entry state, over an environment named by its equation *)
Lemma rw8_entry : forall pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok rsegs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok rsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)).
Proof. intros pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
Lemma rw8_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. subst r. apply H. reflexivity. Qed.
(* a value the start state names: an atom plus an offset, read as an unsigned word *)
Lemma rw8_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. apply (U_atom_off E n v c Hn Hv Hc).
Qed.
Lemma rw8_den_shr : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
sv_denot E (rw8_shr n c) = w64 (Z.shiftr (v + c) 3).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold rw8_shr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n v c Hn) by lia. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). reflexivity.
Qed.
Lemma rw8_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 RW8_SB ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 -> sv_denot E (rw8_sh n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn HK Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold rw8_sh, rw8_shr, rw8_Bx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn) by lia. rewrite (U_atom E 32 RW8_SB HK) by (unfold RW8_SB; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite <- rw8_SB_K. rewrite zcanon_id by (unfold M64, RW8_SB; lia). lia.
Qed.
(* the byte a one-byte chunk holds *)
Lemma rw8_mbyte_chunk1 : forall E (m : word -> option byte) base off e,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 1 e)) ->
mbyte rsegs m (base + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E m base off e H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.
(* a register outside clob whose final symbolic value is its start value holds its start value *)
Lemma rw8_regs_kept : forall E E' K sr0 srf (regs regs2 : bvmap 5 word) (clob : list (bv 5)),
regs_ok E sr0 regs -> regs_ok E' srf regs2 -> env_agree K E E' ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob ||
  (sv_eqb (sr_get srf r) (sr_get sr0 r) && sv_atoms_lt K (sr_get sr0 r))) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.
Proof.
intros E E' K sr0 srf regs regs2 clob H0 Hf HA Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply andb_prop in Hq as [Hq Hat]. apply sv_eqb_eq in Hq.
  rewrite (Hf r), Hq, (H0 r). apply (sv_denot_agree K E E' _ HA Hat).
Qed.
(* the value of a register in a final symbolic state, over atoms the run's environment keeps *)
Lemma rw8_reg_val : forall E Ef K sr (regs : bvmap 5 word) (r : bv 5) v,
regs_ok Ef sr regs -> env_agree K E Ef -> sr_get sr r = v -> sv_atoms_lt K v = true ->
getr regs r = sv_denot E v.
Proof. intros E Ef K sr regs r v HR HA Hv Hl. rewrite (HR r), Hv. apply (sv_denot_agree K E Ef v HA Hl). Qed.
(* the bytes a run keeps: every address outside the write windows of its start regions *)
Lemma rw8_kept_run : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
(* bytes held by one-byte chunks of a final region *)
Lemma rw8_bytes_chunks : forall E H mem base (l : list byte) cs,
Forall (YP09.chunk_ok rsegs E (mrestrict H mem) base) cs ->
(forall i, (i < length l)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (bv_unsigned (nth i l (Z_to_bv 8 0)))))) cs) ->
rtm_bytes rsegs H mem base l.
Proof.
intros E H mem base l cs C Hin. rewrite Forall_forall in C. apply rtm_bytes_aview. intros i Hi.
unfold aview. rewrite (rw8_mbyte_chunk1 E (mrestrict H mem) base (Z.of_nat i) _ (C _ (Hin i Hi))).
cbn [option_map]. f_equal. rewrite U_SLit, rtm_unsigned_byte.
pose proof (rtm_byte_range (nth i l (Z_to_bv 8 0))) as Rb.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. exact Rb.
Qed.
Lemma rw8_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma rw8_val_kept : forall H mem H' mem' a n v,
val_mem rsegs (mrestrict H mem) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' mem' x = aview rsegs H mem x) ->
val_mem rsegs (mrestrict H' mem') a n v.
Proof.
intros H mem H' mem' a n v V K. apply rtm_val_of_bytes. eapply rtm_bytes_kept; [apply rtm_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.
Lemma rw8_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) -> val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
Lemma rw8_pres : forall (regsT regs2 : bvmap 5 word) (r : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r.
Proof. intros regsT regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma rw8_frame_nil : forall E (H : word -> bool) m m', frame_of E [] m m' ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. apply (aview_eq_of rsegs). unfold mrestrict. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & _). destruct Hin.
Qed.
End h.

(* ======================================== facts the runs re-derive ======================================== *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma rw8_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a shadow entry over bytes of a live block: they are marked usable, and they lie outside the shadow band *)
Lemma rw8_shent_blk : forall ly S W mem md p m E n lo hi a0,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
ew E n = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> ew E 32 = Z_to_bv 64 RW8_SB ->
0 <= lo <= hi -> p <= a0 + lo -> a0 + hi <= p + req_size m ->
shent_ok rsegs rw8_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md p m E n lo hi a0 HAR Hin Hn Ha0 HK Hlh Hlo Hhi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E rw8_Bx = SHADOW_OFF)
  by (unfold rw8_Bx; rewrite (U_atom E 32 RW8_SB HK) by (unfold RW8_SB; lia); reflexivity).
assert (UN : U E (SOff n 0) = a0) by (apply U_atom; assumption).
split; cbn [she_m she_lo she_hi].
- rewrite UB, UN. rewrite <- aview_rd_of.
  apply (range_addressable_of_block rsegs B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End f.

(* ======================================== the geometry of a run ========================================
   The real frame R, the frame for locals F (the class-3 side-stack frame at pos) and the callers' window, as
   RtPgSeg's rs_pre fixes them. *)

(* The bounds of the piece's quantities: len is the first block's length at J, sz and ty the pod's size and type,
   cnt the Struct's pod count, kk the pods written so far. Model.pc_buf_len_open and Model.ent_wf give them. *)
Definition rw8_bounds (len sz ty cnt kk : Z) : Prop :=
32 <= len /\ len + 56 <= 5440 /\ len mod 8 = 0 /\ 0 <= sz <= 45 /\ 0 <= ty < 2 ^ 32 /\
1 <= cnt <= 32 /\ 0 <= kk <= 31.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Definition rw8_geo (STK sp0 : Z) (own : list (Z * Z)) (lyc : alayout) (R F pos : Z) : Prop :=
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R + 0x1e0 <= sp0 /\ kHighMemBeg <= R - T_SEG_STK /\
In (3, pos) own /\ F = frame_addr lyc 3 pos /\ in_app F 512 /\ F mod 32 = 0.

(* the registers each run may change *)
Definition rw8_clobA : list (bv 5) := [1; 10; 11; 12; 13; 14; 24; 26]%bv.
Definition rw8_clobB : list (bv 5) := [1; 10; 11; 12; 24]%bv.
Definition rw8_clobC : list (bv 5) := [1; 10; 11; 12; 13; 24; 26]%bv.
Definition rw8_clobD : list (bv 5) := [10; 11]%bv.

(* ---------------- run A: J 0x81e00 -> __asan_memcpy, the two put32 and the body copy's arguments ---------- *)
Definition rw8_runA_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos len sz ty rl : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 19 = w64 (F + 0xe0) -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 rl ->
getr regs 26 = w64 ((- 0x4001) mod 2 ^ 64) -> getr regs 27 = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((- 0x3ffd) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 ty ->
val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 sz ->
0 <= rl < 2 ^ 64 ->
32 <= len -> len + 56 <= 5440 -> len mod 8 = 0 -> 0 <= sz <= 45 -> 0 <= ty < 2 ^ 32 ->
SRr rsegs W (cfg_at rsegs RW8_J regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RW8_CPY rw8_clobA
  (fun a => (pp + len <= a < pp + len + 8) \/ (pp + 0x4000 <= a < pp + 0x4008))
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 RW8_RA1 /\ getr regs2 10 = w64 (pp + len + 8) /\
     getr regs2 11 = w64 (F + 0xf8) /\ getr regs2 12 = w64 sz /\
     getr regs2 24 = w64 sz /\ getr regs2 26 = w64 rl /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (len + 8) /\
     rtm_bytes rsegs (w_H W2) mem2 (pp + len) (Z_to_le_bytes 4 sz ++ Z_to_le_bytes 4 ty))).

(* ---------------- run B: 0x81f44 -> __asan_memset, len += sz and the pad count ---------------- *)
Definition rw8_runB_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos L1 sz : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 24 = w64 sz -> getr regs 27 = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 L1 ->
40 <= L1 + sz -> L1 + sz + 7 <= 16000 -> 0 <= sz <= 45 ->
SRr rsegs W (cfg_at rsegs RW8_RA1 regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RW8_SET rw8_clobB
  (fun a => pp + 0x4000 <= a < pp + 0x4008)
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 RW8_RA2 /\ getr regs2 10 = w64 (pp + (L1 + sz)) /\
     getr regs2 11 = w64 0 /\ getr regs2 12 = w64 (pad8 (L1 + sz)) /\
     getr regs2 24 = w64 (pad8 (L1 + sz)) /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (L1 + sz))).

(* ---------------- run C: 0x81f90 -> the record copy (first set) or the scope stores (first clear) ---------- *)
Definition rw8_runC1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos L0 p kk rl : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 19 = w64 (F + 0xe0) -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 p -> getr regs 26 = w64 rl ->
getr regs 27 = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 (pp + 0x4014) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 ((- 0x4001) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 L0 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk ->
40 <= L0 -> L0 + p <= 5440 -> 0 <= p <= 7 -> 0 <= kk <= 31 -> 0 <= rl < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs RW8_RA2 regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RW8_CPY rw8_clobC
  (fun a => (pp + 0x4000 <= a < pp + 0x4008) \/ (pp + 0x4d14 <= a < pp + 0x4d18))
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 RW8_RA3 /\ getr regs2 10 = w64 (pp + 0x4014 + 104 * kk) /\
     getr regs2 11 = w64 (F + 0xf0) /\ getr regs2 12 = w64 104 /\
     getr regs2 24 = w64 rl /\ getr regs2 26 = w64 ((- 0x4001) mod 2 ^ 64) /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (L0 + p) /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 (kk + 1))).
Definition rw8_runC0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos L0 p kk rl : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 18 = w64 SHADOW_OFF ->
getr regs 22 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 (pp + 0x4000) ->
getr regs 24 = w64 p -> getr regs 26 = w64 rl -> getr regs 27 = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 ((- 0x4001) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 L0 ->
40 <= L0 -> L0 + p <= 5440 -> 0 <= p <= 7 -> 0 <= kk <= 31 -> 0 <= rl < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs RW8_RA2 regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RW8_T0 rw8_clobC
  (fun a => pp + 0x4000 <= a < pp + 0x4008)
  (fun W2 regs2 mem2 =>
     getr regs2 11 = w64 kk /\ getr regs2 24 = w64 rl /\
     getr regs2 26 = w64 ((- 0x4001) mod 2 ^ 64) /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (L0 + p))).

(* ---------------- run D: the scope stores and the latch, to C or to CL ---------------- *)
Definition rw8_runD_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pos cnt kk pc0 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rw8_geo STK sp0 own lyc R F pos ->
(pc0 = RW8_RA3 \/ pc0 = RW8_T0) -> (pc0 = RW8_T0 -> getr regs 11 = w64 kk) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 20 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 cnt ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 kk ->
1 <= cnt <= 32 -> 0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (if kk + 1 =? cnt then RW8_CL else RW8_C) rw8_clobD
  (fun a => shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b)
  (fun W2 regs2 mem2 =>
     getr regs2 11 = w64 (kk + 1) /\
     (forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 0x1e + i) = Some 0xf8))).
End st.
