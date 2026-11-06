(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheck.v (ck_entry, the code table ck_tbl / ck_wx / ck_segs_low) and
   lib/A/RPgCheckStr.v (rl_cstr_kept) at 77f59d02b01 for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02:
   the half's code table, the entry state of a run that starts at one of its cuts (the registers, the real frame at
   s1 and the role cell as regions), the stack facts of lib/A/RPgSeg.v's rs_pre, the seam between RPgSeg's rs_core and
   lib/A/RPgCSpec.v's callee contracts (rl_pre before a call, rl_post after it), and the strings and cells the callees
   read, carried from the segment's start to a cut (rl_cstr_kept with two worlds and the half's write set). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the entry-state
   helpers ck_sr / regs_ok_override / ck_regs_ok / ck_entry, the run and keep tactics and ck_kept_run) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v and RPgM02KeyBase.v at 7e8cf15c304 (the half's code table and
   engine base, the real-frame and entry regions with their region_ok lemmas, the shadow entry of a value
   dispatch, the address arithmetic of &ent[v] and the sign-extension language) for reac-pw/fuzz_headamp image A:
   the ck_ / m2_ / m2k_ prefixes are renamed hv_, every address is headamp's own, role's role cell and strcmp
   wrapper are dropped, and headamp's three value arms (Bool, Int, Float) with its frame cells R+0x88, R+0x90 and
   R+0x98 take the place of role's two arms. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dBase.v; 1142 of its 1195 lines of code are new or changed and 464 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): PART 1 of the piece "the key and the channel" of M03 (lib/A/HPgKcCut.v hk_P1_stmt):
   KEY 0x83168 -> LATCH 0x83474 (no prefix) / BL 0x831c0 (the prefix). Proves no function (kind: segment lemma).

   THE CODE (0x83168 .. 0x831bc, 22 words; the table kp_tbl)
     0x83168 addi a0,s4,-1            a0 := m  (s4 = m + 1)
     0x8316c blt a0,t5,0x83694        t5 = -1 and m >= 0: never taken
     0x83170 sd ra,200(s1)            R+0xc8 := &ent[0]
     0x83174 sd t3,208(s1)            R+0xd0 := n_ent - 1
     0x83178 auipc a0 / 0x8317c addi a1,a0,-632    a1 := 0x20f00, the harness's "reac.headamp."
     0x83180 li a2,13 / 0x83184 mv a0,s2           a2 := 13, a0 := the key
     0x83188 sd t2,224(s1)            R+0xe0 := n_ent
     0x8318c sd t6,216(s1)            R+0xd8 := &ent[0]
     0x83190 jal 0x41ba4              the strncmp wrapper (lib/A/HPgCallsStr.v hc_strncmp_key_call), ra = 0x83194
     0x83194 ld t6,216(s1) / 0x83198 ld t2,224(s1)   t6 and t2 back
     0x8319c bnez a0,0x83474          no prefix: the pair loop's latch with the next index m + 2
     0x831a0 li a1,0 / 0x831a4 ld a2,264(s1)          a1 := 0, a2 := x (R+0x108)
     0x831a8 lw a0,128(a2) / 0x831ac addi a0,a0,1 / 0x831b0 sw a0,128(a2)    x->keys++
     0x831b4 addi a0,s2,13 / 0x831b8 li a5,5 / 0x831bc li a6,32              rest, the isspace bounds
   and falls through to BL 0x831c0. No instrumented check is in this range (x's granules are 0x00 in hq_shX and
   the real frame is not instrumented), so the plain token runner with an empty shadow-entry list decides every
   step; the two branches above are split by hand.

   THE WRITES: the four real-frame cells [R+0xc8, R+0xe8), the wrapper's own stack [R - 2 ESTACK, R) and, on the
   prefix arm, the four bytes of x->keys. hq_base3 crosses all three by lib/A/HPgKcLib.v hk_base3_kept (its write
   set hk_wr is [R, R+0x120) together with x->keys). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c YP08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgSteps HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgKcCut HPgKcLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================== the code table and the three entry states ======================== *)
Definition kp_tbl : ctable := build_table rsegs HQ_KEY 22 TEmpty.
Lemma kp_tbl_ok : table_ok rsegs kp_tbl.
Proof. apply build_table_ok0. unfold HQ_KEY. lia. Qed.

Definition KP_KEYS : Z := 0x831a0.   (* the pc after the `bnez a0` *)

(* block 1: the four saves into [R+0xc8, R+0xe8) of the real frame (s1 = R is atom 9) *)
Definition kp_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xc8 0xe8 0xc8 0xe8 [].
Definition kp_F1 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition kp_S1 : sstate := mkSS HQ_KEY sr_atoms [kp_R1] None kp_F1.

(* block 2a: the two reloads of t6 and t2 (atoms 33 = &ent[0], 34 = n_ent) and the `bnez` *)
Definition kp_R2 : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xe8 0 0
  [YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 34 0))].
Definition kp_F2 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition kp_S2 : sstate := mkSS RA_STRNCMP sr_atoms [kp_R2] None kp_F2.

(* block 2b: x from R+0x108 (atom 33) and x->keys (atom 34) *)
Definition kp_R3 : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0
  [YP09.mkChunk 0x108 (CVal 8 (SOff 33 0))].
Definition kp_RX : YP09.region := YP09.mkRegion (Some 33%nat) 0x80 0x84 0x80 0x84
  [YP09.mkChunk 0x80 (CVal 4 (SOff 34 0))].
(* x lies in application memory, so its write window is apart from the shadow band; the engine's static check
   asks that as ONE interval, so the two halves of application memory are two entry states. *)
Definition kp_F3a : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 4096 (0x7fff7000 - 132) 5);
           (34%nat, mkAF 0 (2 ^ 31 - 2) 0)] [] [].
Definition kp_F3b : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 0x10007fff8000 (2 ^ 47) 5);
           (34%nat, mkAF 0 (2 ^ 31 - 2) 0)] [] [].
Definition kp_S3a : sstate := mkSS KP_KEYS sr_atoms [kp_R3; kp_RX] None kp_F3a.
Definition kp_S3b : sstate := mkSS KP_KEYS sr_atoms [kp_R3; kp_RX] None kp_F3b.

(* ======================== the model: how many keys the fold counts ======================== *)
Lemma kp_pairs_len : forall kf es k, (length (Accessors.pairs_by kf es k) <= length es)%nat.
Proof.
intros kf es. induction es as [|e es IH]; intros k; [cbn; lia|].
cbn [Accessors.pairs_by length]. destruct k as [k'|].
- cbn [length]. pose proof (IH None). lia.
- pose proof (IH (kf e)). lia.
Qed.

Lemma kp_fold_keys : forall cellf cap ps cs keys rf,
keys <= snd (fst (Headamp.ha_fold cellf cap ps cs keys rf)) <= keys + Z.of_nat (length ps).
Proof.
intros cellf cap ps. induction ps as [|[k v] ps IH]; intros cs keys rf; [cbn; lia|].
cbn [Headamp.ha_fold length].
destruct (negb (Headamp.ha_prefix k)).
- pose proof (IH cs keys rf). lia.
- destruct (cellf k v) as [bad|c].
  + pose proof (IH cs (keys + 1) (if rf =? Headamp.REFUSE_NONE then bad else rf)). lia.
  + destruct (cap <=? Z.of_nat (length cs)); [cbn [fst snd]; lia|].
    pose proof (IH (cs ++ [c]) (keys + 1) rf). lia.
Qed.

Lemma kp_fold_pref : forall cellf cap k v ps cs keys rf,
Headamp.ha_prefix k = true ->
keys + 1 <= snd (fst (Headamp.ha_fold cellf cap ((k, v) :: ps) cs keys rf)).
Proof.
intros cellf cap k v ps cs keys rf Hp. cbn [Headamp.ha_fold]. rewrite Hp. cbn [negb].
destruct (cellf k v) as [bad|c].
- pose proof (kp_fold_keys cellf cap ps cs (keys + 1) (if rf =? Headamp.REFUSE_NONE then bad else rf)). lia.
- destruct (cap <=? Z.of_nat (length cs)); [cbn [fst snd]; lia|].
  pose proof (kp_fold_keys cellf cap ps (cs ++ [c]) (keys + 1) rf). lia.
Qed.

Lemma kp_exp_keys_le : forall cx r, Model.pod_rec_wf r -> hq_live rsegs cx r ->
ans_keys (hq_exp rsegs cx r) <= 32.
Proof.
intros cx r Hw (Hnull & _ & Hprops & Hpst).
assert (E1 : (e_null (x_e rsegs cx) =? 1) = false) by (rewrite Hnull; reflexivity).
unfold hq_exp, Headamp.expect_model. rewrite E1, Hprops, Hpst. cbn [orb negb]. cbv iota.
pose proof (kp_fold_keys Headamp.expect_cell (e_cap (x_e rsegs cx))
  (Accessors.pairs (Model.ents r)) [] 0 Headamp.REFUSE_NONE) as Hb.
destruct (Headamp.ha_fold Headamp.expect_cell (e_cap (x_e rsegs cx))
  (Accessors.pairs (Model.ents r)) [] 0 Headamp.REFUSE_NONE) as [[cells kk] rf0].
cbn [fst snd] in Hb. unfold Accessors.pairs in Hb.
unfold Headamp.ha_result, ans_keys. cbn [fst snd].
pose proof (kp_pairs_len Accessors.key_of (Model.ents r) None) as Hl.
destruct (Model.ents_wf r Hw) as [Hle _]. lia.
Qed.

Lemma kp_keys_bound : forall cx r m k v cs keys rf,
Model.pod_rec_wf r -> hq_live rsegs cx r -> hq_pair_inv rsegs cx r m k v cs keys rf ->
keys + 1 <= 32.
Proof.
intros cx r m k v cs keys rf Hw Hlive (Hv & Hpref & Hm & Hfold).
pose proof (kp_fold_pref Headamp.expect_cell (e_cap (x_e rsegs cx)) k v
  (Accessors.pairs_by Accessors.key_of (skipn (S (S m)) (Model.ents r)) None) cs keys rf Hpref) as H1.
rewrite Hfold in H1. unfold hq_fin in H1. cbn [fst snd] in H1.
pose proof (kp_exp_keys_le cx r Hw Hlive). lia.
Qed.

(* ======================== engine helpers ======================== *)
Lemma kp_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma kp_soff : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.

(* a chunk of a region, read back as a value of memory *)
Lemma kp_chunk : forall E (mem : word -> option byte) (n : nat) (b lo hi wlo whi : Z)
(cs : list YP09.chunk) (off : Z) (j : nat) (c v : Z) (w : N),
region_ok rsegs E mem (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b ->
In (YP09.mkChunk off (CVal w (SOff j c))) cs ->
ew E j = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
0 <= v + c < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
val_mem rsegs mem (b + off) (N.to_nat w) (v + c).
Proof.
intros E mem n b lo hi wlo whi cs off j c v w (_ & _ & _ & Hcs) Hn Hin Hj Hv Hvc Hw8 Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E mem b off w (SOff j c) (v + c) Hck (kp_soff E j v c Hj Hv Hvc) Hw8 Hw).
Qed.

(* every byte outside the zone the run's write windows lie in is kept (role's ck_kept_run) *)
Lemma kp_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
intros X. exact (Hz (HW a X)).
Qed.

(* the four bytes of x->keys inside the 136 bytes of the frame object x *)
Lemma kp_x_keys_val : forall cs keys rf (H : word -> bool) mem x,
(length cs <= X_CELLS)%nat -> 0 <= keys < 2 ^ 64 ->
garr8 rsegs (mrestrict H mem) x (hd_zbytes (hq_x_open cs keys rf)) ->
val_mem rsegs (mrestrict H mem) (x + 128) 4 keys.
Proof.
intros cs keys rf H mem x Hcs Hk Hg.
apply (hm_bytes_zbytes rsegs) in Hg. unfold hq_x_open in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite repeat_length in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite length_x_cells_bytes in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite repeat_length in Hg.
unfold ha_res_bytes in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite length_le4 in Hg.
apply (hm_bytes_app rsegs) in Hg as [Hg _].
replace (x + Z.of_nat 4 + Z.of_nat (12 * length cs) + Z.of_nat (12 * (X_CELLS - length cs)) + Z.of_nat 4)
  with (x + 128) in Hg by (unfold X_CELLS in *; lia).
unfold le4 in Hg. rewrite unsigned_lit_small in Hg by lia.
exact (hm_val_of_bytes rsegs _ _ _ _ _ Hg).
Qed.

(* the 136 bytes of x with x->keys one more *)
Lemma kp_x_store : forall cs keys rf (H : word -> bool) mem (H' : word -> bool) mem' x,
(length cs <= X_CELLS)%nat -> 0 <= keys < 2 ^ 31 - 1 ->
garr8 rsegs (mrestrict H mem) x (hd_zbytes (hq_x_open cs keys rf)) ->
val_mem rsegs (mrestrict H' mem') (x + 128) 4 (keys + 1) ->
(forall y, x <= y < x + 136 -> ~ (x + 128 <= y < x + 132) -> aview rsegs H' mem' y = aview rsegs H mem y) ->
garr8 rsegs (mrestrict H' mem') x (hd_zbytes (hq_x_open cs (keys + 1) rf)).
Proof.
intros cs keys rf H mem H' mem' x Hcs Hk Hg Hv Hkeep.
rewrite <- (hk_x_open_keys cs keys rf Hcs Hk).
apply (hm_bytes_zbytes rsegs).
apply (hm_bytes_store rsegs H mem H' mem' x (hq_x_open cs keys rf) 128 4 (keys + 1)).
- apply (hm_bytes_zbytes rsegs). exact Hg.
- change (Z.of_nat 128) with 128. exact Hv.
- rewrite (hq_x_open_len cs keys rf Hcs). lia.
- rewrite (hq_x_open_len cs keys rf Hcs). intros y Hy Hn. apply Hkeep; [lia|].
  change (Z.of_nat 128) with 128 in Hn. change (Z.of_nat (128 + 4)) with 132 in Hn. lia.
Qed.

(* membership in a computed chunk list *)
Ltac kp_in := cbn [In]; repeat (first [left; reflexivity | right]); fail.
(* the symbolic value of a register of the engine's state, as a closed term *)
Ltac kp_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
Ltac kp_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* the write-window goal of a run, with its region list computed *)
Ltac kp_awr_norm :=
lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end.
(* the region of index i of the engine's state, read back *)
Ltac kp_region HS i Hname :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict ?H ?ms) =>
  let rr := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch rr with
  | Some ?rg =>
    let Hr := fresh "Hnth" in
    assert (Hr : nth_error (ss_mem ss) i = Some rg) by (vm_compute; reflexivity);
    pose proof (st_ok_region_at E ss (restrict H ms) i rg HS Hr) as Hname;
    cbn [ms_mem restrict] in Hname; clear Hr
  end
end.

(* a register / an 8-byte cell of a cut's list *)
Lemma kp_at_get : forall (W2 : world rsegs) mem2 (regs2 : bvmap 5 word) e L rr v,
hs_at rsegs (w_H W2) mem2 regs2 e L -> In (LReg rr, v) L -> getr regs2 (Z_to_bv 5 rr) = w64 v.
Proof. intros W2 mem2 regs2 e L rr v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.

Lemma kp_at_cell : forall (W2 : world rsegs) mem2 (regs2 : bvmap 5 word) e L b off v,
hs_at rsegs (w_H W2) mem2 regs2 e L -> In (LCell b off, v) L ->
val_mem rsegs (mrestrict (w_H W2) mem2) (hd_xv e b + off) 8 (v mod 2 ^ 64).
Proof. intros W2 mem2 regs2 e L b off v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.

(* membership in a cut's list *)
Ltac kp_lin := unfold hk_L, hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body;
cbn [In app]; repeat (first [left; reflexivity | right]).

Lemma kp_bvq : forall q : Z, 0 <= q < 32 -> bv_unsigned (Z_to_bv 5 q) = q.
Proof.
intros q Hq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

(* a run that keeps every register outside a list of caller-saved ones keeps the callee-saved set *)
Lemma kp_keep_cs : forall (regs regs' : bvmap 5 word) (l : list (bv 5)),
(forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr l -> getr regs' rr = getr regs rr) ->
(forall c, In c l -> ~ acallee_saved (bv_unsigned c)) ->
aregs_preserved regs regs'.
Proof.
intros regs regs' l HK Hl q Hq.
assert (Hq32 : 0 <= q < 32) by (unfold acallee_saved in Hq; lia).
apply HK.
- rewrite kp_bvq by lia. unfold acallee_saved in Hq. lia.
- intros Hin. pose proof (Hl _ Hin) as Hn. rewrite kp_bvq in Hn by lia. exact (Hn Hq).
Qed.

Ltac kp_csnot :=
lazymatch goal with |- ~ acallee_saved (bv_unsigned ?X) =>
let v := eval vm_compute in (bv_unsigned X) in
replace (bv_unsigned X) with v by (vm_compute; reflexivity) end;
unfold acallee_saved; lia.

Lemma kp_cs1 : forall c : bv 5, In c [1; 10; 11; 12]%bv -> ~ acallee_saved (bv_unsigned c).
Proof.
intros c Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; kp_csnot.
Qed.
Lemma kp_cs2 : forall c : bv 5, In c [7; 31]%bv -> ~ acallee_saved (bv_unsigned c).
Proof.
intros c Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[]]]; kp_csnot.
Qed.
Lemma kp_cs3 : forall c : bv 5, In c [10; 11; 12; 15; 16]%bv -> ~ acallee_saved (bv_unsigned c).
Proof.
intros c Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; kp_csnot.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
(* the strncmp wrapper's contract at image A's trampoline 0x41ba4, as lib/A/HPgCallsStr.v's Section hypothesis
   STRNCMP states it at segs = Img0.rsegs, for EVERY float state: the cut this part starts from is at the walk's
   own float state fx2, not at the Section's fx, and only `cfg_at` in that text names a float state. *)
Hypothesis STRNCMP : forall fx' : YK11.FPState,
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre rsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok rsegs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok rsegs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))) ->
SRr rsegs W (@cfg_at fx' rsegs A_STRNCMP regs mem md)
(fun (W' : world rsegs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
 AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ======================== what the segment's start gives about the frame ======================== *)
Lemma kp_start : forall cx r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
  Model.pod_rec_wf r /\
  In (HQ_CID, x_pos rsegs cx) (x_own rsegs cx) /\
  e_F (x_e rsegs cx) = frame_addr (x_ly rsegs cx) HQ_CID (x_pos rsegs cx) /\
  e_R (x_e rsegs cx) mod 32 = 0 /\
  e_R (x_e rsegs cx) + HQ_RSZ <= e_S (x_e rsegs cx) /\
  e_S (x_e rsegs cx) = x_sp0 rsegs cx /\
  x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
  st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
  getr (x_regs rsegs cx) 2 = w64 (e_R (x_e rsegs cx)) /\
  getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\
  getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof.
intros cx r ev HS.
destruct HS as (Hpre & _ & Hwf & _).
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HeS & HRal & HRsz & Hwin & Hown & HFeq & _).
cbn [hi_cid hi_rsz headamp_himg_A] in Hown, HFeq, HRsz.
assert (HFl : frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) = frame_addr (x_ly rsegs cx) 4 (x_pos rsegs cx))
  by (eapply hc_frame_addr_j; exact HJ).
rewrite HFl in HFeq.
unfold HQ_CID, HQ_RSZ.
split; [exact Hwf|]. split; [exact Hown|]. split; [exact HFeq|]. split; [exact HRal|].
split; [exact HRsz|]. split; [exact HeS|]. split; [exact Hwin|]. split; [exact Hev|].
split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma kp_core : forall cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ev,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
@hc_core rc SK rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ev HS Hb.
destruct (kp_start cx r ev HS) as (Hwf & Hown & HFeq & HRal & HRsz & HeS & Hwin & Hev & H2 & H3 & H4).
destruct Hb as (Hcore & _). destruct Hcore as (HJ & Hregs & _).
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 16 32); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact HRal]. }
split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hregs 2 ltac:(tauto))|].
split; [rewrite <- H3; exact (Hregs 3 ltac:(tauto))|].
split; [rewrite <- H4; exact (Hregs 4 ltac:(tauto))|].
split; [exact HR16|]. split; [exact Hwin|]. unfold HQ_RSZ in HRsz. lia.
Qed.

(* ======================== block 1: KEY 0x83168 .. the `jal` of the wrapper ======================== *)
Lemma kp_blk1 : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R key nent ppe : Z) (m : nat),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
getr regs 9 = w64 R -> getr regs 18 = w64 key ->
getr regs 20 = w64 (Z.of_nat m + 1) -> getr regs 30 = w64 (-1) ->
getr regs 1 = w64 ppe -> getr regs 31 = w64 ppe ->
getr regs 7 = w64 nent -> getr regs 28 = w64 (nent - 1) ->
(m < 32)%nat -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
sp0 - STK <= R - T_SEG_STK -> R + HQ_RSZ <= sp0 ->
0 <= ppe < 2 ^ 64 -> 1 <= nent <= 32 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' 1 = w64 RA_STRNCMP -> getr regs' 10 = w64 key ->
 getr regs' 11 = w64 A_HKEY -> getr regs' 12 = w64 13 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 200) 8 ppe ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 208) 8 (nent - 1) ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 216) 8 ppe ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 224) 8 nent ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (R + 200 <= a < R + 232) ->
    aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 SRr rsegs W (@cfg_at fx2 rsegs A_STRNCMP regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs HQ_KEY regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W memc mdc regs R key nent ppe m
  HJ H9 H18 H20 H30 H1 H31 H7 H28 Hm HR HRal Hwin Hrsz Hppe Hnent Hpres K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hts : T_SEG_STK = 16384) by reflexivity. rewrite Hts in Hwin.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold HQ_RSZ in Hrsz.
assert (HS : st_ok rsegs (Ereg regs rt_extra) kp_S1
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 HQ_KEY) memc (seg_rom rsegs)))).
{ assert (B9' : bv_unsigned (ew (Ereg regs rt_extra) 9) = R)
    by (rewrite (ew_Ereg_nat regs rt_extra 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold kp_S1. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold kp_R1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kp_F1 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9'. change (2 ^ 5) with 32. repeat split; lia. }
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (B9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = Z_to_bv 64 key)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 18 18%bv eq_refl); exact H18).
assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat m + 1))
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 20 20%bv eq_refl); exact H20).
assert (E30 : ew E 30 = Z_to_bv 64 (2 ^ 64 - 1)).
{ subst E. rewrite (ew_Ereg_nat regs rt_extra 30 30%bv eq_refl), H30. apply bv_eq. vm_compute. reflexivity. }
assert (E1 : ew E 1 = Z_to_bv 64 ppe)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 1 1%bv eq_refl); exact H1).
assert (E31 : ew E 31 = Z_to_bv 64 ppe)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 31 31%bv eq_refl); exact H31).
assert (E7 : ew E 7 = Z_to_bv 64 nent)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 7 7%bv eq_refl); exact H7).
assert (E28 : ew E 28 = Z_to_bv 64 (nent - 1))
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 28 28%bv eq_refl); exact H28).
assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
clear HE.
unfold cfg_at. change (w64 HQ_KEY) with (Z_to_bv 64 HQ_KEY).
(* 0x83168 addi a0,s4,-1; stop at the `blt` *)
aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan 0x8316c.
{ lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [ reflexivity | rewrite B9; ring | cbn [YP09.r_wlo YP09.r_whi]; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil ]. }
rename ms into ms1.
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 200 <= a < R + 232) ->
  aview rsegs (w_H W) (ms_mem ms1) a = aview rsegs (w_H W) memc a).
{ eapply (kp_kept_run (fun a => R + 200 <= a < R + 232) _ _ (w_H W) memc memc (ms_mem ms1)).
  - intros a Ha Hz. reflexivity.
  - exact HFr.
  - intros a (rr & Hin & Hb).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
    destruct Hin as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B9 in Hb. exact Hb. }
clear HF HFr HG.
srr_branch_tok kp_tbl_ok HS SHOK RTBspan.
- (* taken: m < -1, which m >= 0 refutes *)
  exfalso.
  assert (HU20 : U E (SOff 20 (-1)) = Z.of_nat m).
  { rewrite (U_atom_off E 20 (Z.of_nat m + 1) (-1) E20 ltac:(lia) ltac:(lia)). lia. }
  assert (HU30 : U E (SOff 30 0) = 2 ^ 64 - 1) by (apply (U_atom E 30 _ E30); lia).
  rewrite !denot_lit_U, YO0c.branch_lt, HU20, HU30 in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  rewrite (YO0b.s64_small (Z.of_nat m)) in Hc by lia.
  replace (YO0b.s64 (2 ^ 64 - 1)) with (-1) in Hc by (vm_compute; reflexivity).
  apply Z.ltb_lt in Hc. lia.
- (* not taken: the four saves and the `jal` *)
  aj_run_tok kp_tbl_ok HS HJ SHOK RTBspan.
  + lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)).
    * reflexivity.
    * rewrite B9. ring.
    * cbn [YP09.r_wlo YP09.r_whi]. lia.
    * cbn [YP09.r_wlo YP09.r_whi]. lia.
    * apply awr_ok_nil.
  + assert (R1' : getr (ms_regs ms) (1%bv : bv 5) = w64 RA_STRNCMP).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (1%bv : bv 5) HS). kp_sv. reflexivity. }
    assert (R10' : getr (ms_regs ms) (10%bv : bv 5) = w64 key).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (10%bv : bv 5) HS). kp_sv.
      rewrite kp_denot0, E18. reflexivity. }
    assert (R11' : getr (ms_regs ms) (11%bv : bv 5) = w64 A_HKEY).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS). kp_sv. reflexivity. }
    assert (R12' : getr (ms_regs ms) (12%bv : bv 5) = w64 13).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (12%bv : bv 5) HS). kp_sv. reflexivity. }
    assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12]%bv ->
      getr (ms_regs ms) rr = getr regs rr).
    { intros rr Hr0 Hn.
      exact (regs_kept_of_st_ok rsegs _ _ ms regs rt_extra (w_H W) [1; 10; 11; 12]%bv
        HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
    kp_region HS 0%nat HRok.
    assert (V_c8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 200) 8 ppe).
    { replace ppe with (ppe + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kp_chunk _ _ 9%nat R); [exact HRok | exact B9 | kp_in | exact E1 | lia | lia | cbn; lia | cbn; lia]. }
    assert (V_d0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 208) 8 (nent - 1)).
    { replace (nent - 1) with (nent - 1 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kp_chunk _ _ 9%nat R); [exact HRok | exact B9 | kp_in | exact E28 | lia | lia | cbn; lia | cbn; lia]. }
    assert (V_d8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 216) 8 ppe).
    { replace ppe with (ppe + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kp_chunk _ _ 9%nat R); [exact HRok | exact B9 | kp_in | exact E31 | lia | lia | cbn; lia | cbn; lia]. }
    assert (V_e0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 224) 8 nent).
    { replace nent with (nent + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kp_chunk _ _ 9%nat R); [exact HRok | exact B9 | kp_in | exact E7 | lia | lia | cbn; lia | cbn; lia]. }
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 200 <= a < R + 232) ->
      aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
    { eapply (kp_kept_run (fun a => R + 200 <= a < R + 232) _ _ (w_H W) memc _ (ms_mem ms)).
      - exact KE1.
      - exact HFr.
      - intros a (rr & Hin & Hb).
        lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
        destruct Hin as [<-|[]].
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B9 in Hb. exact Hb. }
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
      replace (ss_pc ss) with A_STRNCMP by (vm_compute; reflexivity) end.
    eapply K;
    [ exact HJ | kp_io | exact RK | exact R1' | exact R10' | exact R11' | exact R12'
    | exact V_c8 | exact V_d0 | exact V_d8 | exact V_e0 | exact KE ].
Qed.

(* ======================== block 2a: 0x83194 .. LATCH 0x83474 / 0x831a0 ======================== *)
Definition kp_ex2 (ppe nent : Z) : list word := [Z_to_bv 64 SBr; w64 ppe; w64 nent].

Lemma kp_blk2a : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R nent ppe : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
getr regs 9 = w64 R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
0 <= ppe < 2 ^ 64 -> 1 <= nent <= 32 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 216) 8 ppe ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 224) 8 nent ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 31]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' 7 = w64 nent -> getr regs' 31 = w64 ppe ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 getr regs 10 <> w64 0 ->
 SRr rsegs W (@cfg_at fx2 rsegs HQ_LATCH regs' mem' md') Q) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 31]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' 7 = w64 nent -> getr regs' 31 = w64 ppe ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 getr regs 10 = w64 0 ->
 SRr rsegs W (@cfg_at fx2 rsegs KP_KEYS regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs RA_STRNCMP regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W memc mdc regs R nent ppe
  HJ H9 HR HRal Hppe Hnent Vd8 Ve0 KL KN.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (HS : st_ok rsegs (Ereg regs (kp_ex2 ppe nent)) kp_S2
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 RA_STRNCMP) memc (seg_rom rsegs)))).
{ assert (B9' : bv_unsigned (ew (Ereg regs (kp_ex2 ppe nent)) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (A33 : ew (Ereg regs (kp_ex2 ppe nent)) 33 = Z_to_bv 64 ppe)
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (A34 : ew (Ereg regs (kp_ex2 ppe nent)) 34 = Z_to_bv 64 nent)
    by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite restrict_mkst_fx. unfold kp_S2. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold kp_R2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs _ _ R 216 8 (SOff 33 0) ppe);
      [rewrite kp_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Vd8].
    + apply (chunk_ok_val rsegs _ _ R 224 8 (SOff 34 0) nent);
      [rewrite kp_denot0; exact A34 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Ve0].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kp_F2 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9'. change (2 ^ 5) with 32. repeat split; lia. }
remember (Ereg regs (kp_ex2 ppe nent)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (kp_ex2 ppe nent)) E) by (subst E; apply env_agree_refl).
assert (B9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (A33 : ew E 33 = Z_to_bv 64 ppe)
  by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 nent)
  by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
clear HE.
unfold cfg_at. change (w64 RA_STRNCMP) with (Z_to_bv 64 RA_STRNCMP).
(* 0x83194 / 0x83198 the two reloads; stop at the `bnez` *)
aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan 0x8319c.
{ kp_awr_norm. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
rename ms into ms1.
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms1) a = aview rsegs (w_H W) memc a).
{ intros a Ha.
  exact (kp_kept_run (fun _ => False) E (ss_mem kp_S2) (w_H W) memc memc (ms_mem ms1)
    ltac:(intros b Hb Hz; reflexivity) HFr
    ltac:(intros b (rr & Hin & Hb);
          lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
          destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
    a Ha ltac:(intros HF0; exact HF0)). }
clear HF HFr HG.
assert (HU10 : U E (SOff 10 0) = bv_unsigned (getr regs 10))
  by (unfold U; rewrite kp_denot0, E10; reflexivity).
srr_branch_tok kp_tbl_ok HS SHOK RTBspan.
- (* taken: a0 <> 0, to LATCH *)
  rewrite branch_ne_U, HU10, (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan HQ_LATCH.
  { kp_awr_norm. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  assert (R7' : getr (ms_regs ms) (7%bv : bv 5) = w64 nent).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (7%bv : bv 5) HS). kp_sv.
    rewrite kp_denot0, A34. reflexivity. }
  assert (R31' : getr (ms_regs ms) (31%bv : bv 5) = w64 ppe).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (31%bv : bv 5) HS). kp_sv.
    rewrite kp_denot0, A33. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 31]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kp_ex2 ppe nent) (w_H W) [7; 31]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { intros a Ha.
    exact (kp_kept_run (fun _ => False) E (ss_mem kp_S2) (w_H W) memc _ (ms_mem ms)
      ltac:(intros b Hb Hz; apply KE1; exact Hb) HFr
      ltac:(intros b (rr & Hin & Hb);
            lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
            destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
      a Ha ltac:(intros HF0; exact HF0)). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with HQ_LATCH by (vm_compute; reflexivity) end.
  eapply KL; [exact HJ | kp_io | exact RK | exact R7' | exact R31' | exact KE |].
  intros Hz. apply Hc. rewrite Hz. reflexivity.
- (* not taken: a0 = 0, to 0x831a0 *)
  rewrite branch_ne_U, HU10, (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan KP_KEYS.
  { kp_awr_norm. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  assert (R7' : getr (ms_regs ms) (7%bv : bv 5) = w64 nent).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (7%bv : bv 5) HS). kp_sv.
    rewrite kp_denot0, A34. reflexivity. }
  assert (R31' : getr (ms_regs ms) (31%bv : bv 5) = w64 ppe).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (31%bv : bv 5) HS). kp_sv.
    rewrite kp_denot0, A33. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 31]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kp_ex2 ppe nent) (w_H W) [7; 31]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { intros a Ha.
    exact (kp_kept_run (fun _ => False) E (ss_mem kp_S2) (w_H W) memc _ (ms_mem ms)
      ltac:(intros b Hb Hz; apply KE1; exact Hb) HFr
      ltac:(intros b (rr & Hin & Hb);
            lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
            destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
      a Ha ltac:(intros HF0; exact HF0)). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with KP_KEYS by (vm_compute; reflexivity) end.
  eapply KN; [exact HJ | kp_io | exact RK | exact R7' | exact R31' | exact KE |].
  apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* ======================== block 2b: 0x831a0 .. BL 0x831c0 (x->keys++) ======================== *)
Definition kp_ex3 (x keys : Z) : list word := [Z_to_bv 64 SBr; w64 x; w64 keys].

Lemma kp_blk2b : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R x keys key cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
getr regs 9 = w64 R -> getr regs 18 = w64 key ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
in_app x 132 -> x + 132 <= R -> x mod 32 = 0 ->
0 <= keys <= 2 ^ 31 - 2 -> 0 <= key -> key + 13 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 264) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 128) 4 keys ->
In (cid, pos) own ->
frame_addr ly2 cid pos <= x -> x + 132 <= frame_addr ly2 cid pos + fs_frame_bytes cid ->
(forall o, 0 <= o < 4 -> apresent (w_H W) memc (x + 128 + o)) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12; 15; 16]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' 10 = w64 (key + 13) -> getr regs' 11 = w64 0 ->
 getr regs' 15 = w64 5 -> getr regs' 16 = w64 32 ->
 val_mem rsegs (mrestrict (w_H W) mem') (x + 128) 4 (keys + 1) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 SRr rsegs W (@cfg_at fx2 rsegs HK_BL regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs KP_KEYS regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W memc mdc regs R x keys key cid pos
  HJ H9 H18 HR HRal Hinapp Hx1 Hxal Hkeys Hkey0 Hkey1 Vx108 Vxk Hown Hfr0 Hfr1 Hap K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (@ASAN_CEIL_range rc) as [[Hac1 Hac2] _]. unfold ASAN_CEIL in Hac1, Hac2.
destruct Hinapp as (Hx0 & [Hlow | (Hhi1 & Hhi2)]).
- unfold kLowShadowBeg in Hlow.
  assert (HS : st_ok rsegs (Ereg regs (kp_ex3 x keys)) kp_S3a
    (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KP_KEYS) memc (seg_rom rsegs)))).
  { unfold kp_S3a, kp_F3a.
    assert (B9' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 9) = R)
      by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
    assert (A33 : ew (Ereg regs (kp_ex3 x keys)) 33 = Z_to_bv 64 x)
      by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
    assert (A34 : ew (Ereg regs (kp_ex3 x keys)) 34 = Z_to_bv 64 keys)
      by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
    assert (B33' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 33) = x)
      by (rewrite A33; apply unsigned_lit_small; lia).
    assert (B34' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 34) = keys)
      by (rewrite A34; apply unsigned_lit_small; lia).
    rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold kp_R3, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 264 8 (SOff 33 0) x);
        [rewrite kp_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Vx108].
      + unfold kp_RX, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33'.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable rsegs);
                replace (x + o) with (x + 128 + (o - 128)) by lia; apply Hap; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ x 128 4 (SOff 34 0) keys);
        [rewrite kp_denot0; exact A34 | cbn; lia | cbn; lia | change (N.to_nat 4) with 4%nat; exact Vxk].
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
      unfold extent_disjoint, kp_R3, kp_RX.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9', B33'. right. lia.
    - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite B9', B33', B34'.
      change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
  }
  remember (Ereg regs (kp_ex3 x keys)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (kp_ex3 x keys)) E) by (subst E; apply env_agree_refl).
  assert (A33 : ew E 33 = Z_to_bv 64 x)
    by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (A34 : ew E 34 = Z_to_bv 64 keys)
    by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (B33 : bv_unsigned (ew E 33) = x) by (rewrite A33; apply unsigned_lit_small; lia).
  assert (E18 : ew E 18 = Z_to_bv 64 key)
    by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
  clear HE.
  unfold cfg_at. change (w64 KP_KEYS) with (Z_to_bv 64 KP_KEYS).
  aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan HK_BL.
  { kp_awr_norm.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat x);
    [ reflexivity | exact B33 | | apply awr_ok_nil ].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right. right. right. exists cid, pos. split; [exact Hown|]. left.
    unfold in_zr. cbn [fst snd]. lia. }
  assert (R10' : getr (ms_regs ms) (10%bv : bv 5) = w64 (key + 13)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (10%bv : bv 5) HS). kp_sv.
    rewrite (kp_soff E 18 key 13 E18 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (R11' : getr (ms_regs ms) (11%bv : bv 5) = w64 0).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (R15' : getr (ms_regs ms) (15%bv : bv 5) = w64 5).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (15%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (R16' : getr (ms_regs ms) (16%bv : bv 5) = w64 32).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (16%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12; 15; 16]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kp_ex3 x keys) (w_H W) [10; 11; 12; 15; 16]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  kp_region HS 1%nat HRokX.
  assert (Vx : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (x + 128) 4 (keys + 1)).
  { change 4%nat with (N.to_nat 4).
    eapply (kp_chunk _ _ 33%nat x);
    [exact HRokX | exact B33 | kp_in | exact A34 | lia | lia | cbn; lia | cbn; lia]. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { eapply (kp_kept_run (fun a => x + 128 <= a < x + 132) _ _ (w_H W) memc memc (ms_mem ms)).
    - intros a Ha Hz. reflexivity.
    - exact HFr.
    - intros a (rr & Hin & Hb).
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
      destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite B33 in Hb. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with HK_BL by (vm_compute; reflexivity) end.
  eapply K;
  [ exact HJ | kp_io | exact RK | exact R10' | exact R11' | exact R15' | exact R16' | exact Vx | exact KE ].
- unfold kHighMemBeg in Hhi1.
  assert (HS : st_ok rsegs (Ereg regs (kp_ex3 x keys)) kp_S3b
    (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KP_KEYS) memc (seg_rom rsegs)))).
  { unfold kp_S3b, kp_F3b.
    assert (B9' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 9) = R)
      by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
    assert (A33 : ew (Ereg regs (kp_ex3 x keys)) 33 = Z_to_bv 64 x)
      by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
    assert (A34 : ew (Ereg regs (kp_ex3 x keys)) 34 = Z_to_bv 64 keys)
      by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
    assert (B33' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 33) = x)
      by (rewrite A33; apply unsigned_lit_small; lia).
    assert (B34' : bv_unsigned (ew (Ereg regs (kp_ex3 x keys)) 34) = keys)
      by (rewrite A34; apply unsigned_lit_small; lia).
    rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold kp_R3, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 264 8 (SOff 33 0) x);
        [rewrite kp_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Vx108].
      + unfold kp_RX, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33'.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable rsegs);
                replace (x + o) with (x + 128 + (o - 128)) by lia; apply Hap; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ x 128 4 (SOff 34 0) keys);
        [rewrite kp_denot0; exact A34 | cbn; lia | cbn; lia | change (N.to_nat 4) with 4%nat; exact Vxk].
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
      unfold extent_disjoint, kp_R3, kp_RX.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9', B33'. right. lia.
    - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite B9', B33', B34'.
      change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
  }
  remember (Ereg regs (kp_ex3 x keys)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (kp_ex3 x keys)) E) by (subst E; apply env_agree_refl).
  assert (A33 : ew E 33 = Z_to_bv 64 x)
    by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (A34 : ew E 34 = Z_to_bv 64 keys)
    by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (B33 : bv_unsigned (ew E 33) = x) by (rewrite A33; apply unsigned_lit_small; lia).
  assert (E18 : ew E 18 = Z_to_bv 64 key)
    by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
  clear HE.
  unfold cfg_at. change (w64 KP_KEYS) with (Z_to_bv 64 KP_KEYS).
  aj_run_to_tok kp_tbl_ok HS HJ SHOK RTBspan HK_BL.
  { kp_awr_norm.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat x);
    [ reflexivity | exact B33 | | apply awr_ok_nil ].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right. right. right. exists cid, pos. split; [exact Hown|]. left.
    unfold in_zr. cbn [fst snd]. lia. }
  assert (R10' : getr (ms_regs ms) (10%bv : bv 5) = w64 (key + 13)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (10%bv : bv 5) HS). kp_sv.
    rewrite (kp_soff E 18 key 13 E18 ltac:(lia) ltac:(lia)). reflexivity. }
  assert (R11' : getr (ms_regs ms) (11%bv : bv 5) = w64 0).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (R15' : getr (ms_regs ms) (15%bv : bv 5) = w64 5).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (15%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (R16' : getr (ms_regs ms) (16%bv : bv 5) = w64 32).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (16%bv : bv 5) HS). kp_sv. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12; 15; 16]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kp_ex3 x keys) (w_H W) [10; 11; 12; 15; 16]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  kp_region HS 1%nat HRokX.
  assert (Vx : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (x + 128) 4 (keys + 1)).
  { change 4%nat with (N.to_nat 4).
    eapply (kp_chunk _ _ 33%nat x);
    [exact HRokX | exact B33 | kp_in | exact A34 | lia | lia | cbn; lia | cbn; lia]. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { eapply (kp_kept_run (fun a => x + 128 <= a < x + 132) _ _ (w_H W) memc memc (ms_mem ms)).
    - intros a Ha Hz. reflexivity.
    - exact HFr.
    - intros a (rr & Hin & Hb).
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
      destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite B33 in Hb. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with HK_BL by (vm_compute; reflexivity) end.
  eapply K;
  [ exact HJ | kp_io | exact RK | exact R10' | exact R11' | exact R15' | exact R16' | exact Vx | exact KE ].
Qed.



(* ======================== the piece ======================== *)
Theorem hk_P1 : @hk_P1_stmt fx rc SK rsegs B MT.
Proof using errno_low STRNCMP.
unfold hk_P1_stmt. intros cx POST r ev at0 m HS HLATCH HBL.
unfold hq_from_KEY. intros fx2 ly2 S2 W2 regs2 mem2 md2 kk cs keys rf HKEY.
pose proof HKEY as (Hbase & Hat & Hfs9 & Hfs18 & Hlive & Hat0m & HSm & Hnone & Hkey & Hxat & Hfold).
destruct (kp_start cx r ev HS) as (Hwf & Hown & HFeq & HRal & HRsz & HeS & Hwin & Hev & P2 & P3 & P4).
pose proof (kp_core cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 ev HS Hbase) as HC.
pose proof HC as HCc. apply hc_core_R in HCc. destruct HCc as (Hceil & H47 & Hsp).
pose proof (@ASAN_CEIL_range rc) as [[Hac1 Hac2] _]. unfold ASAN_CEIL in Hac1, Hac2.
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hps : Layout.PP_SIZE = 19744) by (vm_compute; reflexivity).
assert (Hrq : req_size Layout.PP_SIZE = 19744) by (vm_compute; reflexivity).
assert (Hfb : fs_frame_bytes HQ_CID = 1024) by (vm_compute; reflexivity).
rewrite Hts in Hceil.
destruct (Model.ents_wf r Hwf) as [Hlen32 _].
pose proof Hbase as (Hcore & _).
pose proof Hcore as (HJ2 & Hregs234 & Hfrs2 & Hperm2 & Hio2 & Hmo2 & Hkeep2).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _).
rewrite HeS in HRsz.
(* the frame for locals *)
assert (HFl2 : frame_addr ly2 HQ_CID (x_pos rsegs cx) = e_F (x_e rsegs cx))
  by (rewrite HFeq; eapply hc_frame_addr_j; exact HJ2).
assert (Hfin : In (HQ_CID, x_pos rsegs cx) (frames S2))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 HQ_CID (x_pos rsegs cx) HAR2 Hfin)
  as (HF32 & HFapp & HFpres & _).
rewrite HFl2 in HF32, HFapp, HFpres.
assert (HFlow : 4096 <= frame_addr ly2 HQ_CID (x_pos rsegs cx) /\
  frame_addr ly2 HQ_CID (x_pos rsegs cx) + fs_frame_bytes HQ_CID <= alloc_ceiling)
  by (eapply hc_frm_low; [exact HJ2 | exact Hown]).
destruct HFlow as (HF4k & HFceil).
rewrite HFl2 in HF4k. rewrite HFl2, Hfb in HFceil.
(* the key *)
destruct (hk_keymem B MT cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 m kk HS Hbase ltac:(lia) Hkey)
  as (Hklen & Hknul & _ & _ & _ & Hppin & Hpp4k & Hppceil & _ & _ & _).
destruct (hk_strncmp_prefix kk Hknul) as (d & Hmodel & Hdiff).
(* the registers and cells of the cut *)
unfold hs_at_cx in Hat.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 9 (e_R (x_e rsegs cx)) Hat ltac:(kp_lin)) as G9.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 18
  (e_pp (x_e rsegs cx) + HQ_ENT_BODY + 104 * Z.of_nat m) Hat ltac:(kp_lin)) as G18.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 20 (Z.of_nat m + 1) Hat ltac:(kp_lin)) as G20.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 30 (-1) Hat ltac:(kp_lin)) as G30.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 1
  (e_pp (x_e rsegs cx) + HQ_ENT0) Hat ltac:(kp_lin)) as G1.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 31
  (e_pp (x_e rsegs cx) + HQ_ENT0) Hat ltac:(kp_lin)) as G31.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 7 (hq_nent r) Hat ltac:(kp_lin)) as G7.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 28 (hq_nent r - 1) Hat ltac:(kp_lin)) as G28.
pose proof (kp_at_get W2 mem2 regs2 (x_e rsegs cx) _ 21 (Z.of_nat m + 2) Hat ltac:(kp_lin)) as G21.
pose proof (kp_at_cell W2 mem2 regs2 (x_e rsegs cx) _ XR 0x108
  (e_F (x_e rsegs cx) + HQ_XO) Hat ltac:(kp_lin)) as C108.
cbn [hd_xv] in C108.
assert (Hnent1 : 1 <= hq_nent r <= 32) by (unfold hq_nent; lia).
assert (Hppe : 0 <= e_pp (x_e rsegs cx) + HQ_ENT0 < 2 ^ 64) by (unfold HQ_ENT0; lia).
assert (Hkad : 0 <= hk_kaddr rsegs cx m /\ hk_kaddr rsegs cx m + 13 < 2 ^ 64)
  by (unfold hk_kaddr, HQ_ENT_BODY; lia).
(* ---------------- block 1: the four saves and the `jal` ---------------- *)
apply (kp_blk1 fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  regs2 (e_R (x_e rsegs cx)) (hk_kaddr rsegs cx m) (hq_nent r) (e_pp (x_e rsegs cx) + HQ_ENT0) m
  HJ2 G9 G18 G20 G30 G1 G31 G7 G28
  ltac:(lia) ltac:(lia) HRal Hwin HRsz Hppe Hnent1 Hpres).
intros regsA memA mdA HJA HioA RKA A1 A10 A11 A12 Vc8 Vd0 Vd8 Ve0 KEA.
assert (RPA : aregs_preserved regs2 regsA) by (apply (kp_keep_cs regs2 regsA [1; 10; 11; 12]%bv RKA kp_cs1)).
assert (HbaseA : @hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regsA memA mdA).
{ apply (hk_base3_kept B MT errno_low cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regsA memA mdA
    HS Hbase hq_shX_len HJA ltac:(intros q Hq; apply RPA; unfold acallee_saved; lia) HioA).
  intros a Ha Hns Hnw. apply KEA; [exact Ha|]. intros Hin. apply Hnw. unfold hk_wr. left. lia. }
pose proof (kp_core cx fx2 r hq_shX ly2 S2 W2 regsA memA mdA ev HS HbaseA) as HCA.
destruct (hk_keymem B MT cx ev fx2 r hq_shX ly2 S2 W2 regsA memA mdA m kk HS HbaseA ltac:(lia) Hkey)
  as (_ & _ & _ & HkgarrA & HktailA & HppinA & _ & _ & _ & _ & _).
assert (HlitA : hd_cstr rsegs (w_H W2) memA A_HKEY (hd_zbytes Headamp.HA_PREFIX)).
{ apply (hk_cstr_now B MT errno_low cx ev fx2 r hq_shX ly2 S2 W2 regsA memA mdA
    A_HKEY (hd_zbytes Headamp.HA_PREFIX) HS HbaseA).
  replace (hd_zbytes Headamp.HA_PREFIX)
    with [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46] by (vm_compute; reflexivity).
  cbn [hi_strs headamp_himg_A]. unfold headamp_A_strs. cbn [In].
  right. right. left. reflexivity. }
assert (HroA : arodata_okP rsegs 0 0 B (aview rsegs (w_H W2) memA))
  by exact (hk_arodata_now B MT cx ev fx2 r hq_shX ly2 S2 W2 regsA memA mdA HS HbaseA).
(* ---------------- the strncmp wrapper ---------------- *)
apply (@hc_strncmp_key_call fx2 rc SK rsegs B img_segs_low (STRNCMP fx2) 0 0 POST
  (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 memA mdA regsA (e_R (x_e rsegs cx)) (hk_kaddr rsegs cx m)
  (e_pp (x_e rsegs cx)) Layout.PP_SIZE d kk
  HCA A1 A10 A11 A12 HppinA ltac:(unfold hk_kaddr, HQ_ENT_BODY; lia)
  ltac:(rewrite Hrq; unfold hk_kaddr, HQ_ENT_BODY; lia)
  HkgarrA Hknul HktailA HlitA HroA Hmodel).
intros regsB memB mdB HCB RPB HioB KEB Hv. destruct Hv as (vv & Hvv & Hviff).
assert (HJB : ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
  (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
  ly2 S2 W2 memB mdB (x_k rsegs cx)) by (destruct HCB as (HJB & _); exact HJB).
assert (RP2B : aregs_preserved regs2 regsB) by (eapply aregs_preserved_trans; [exact RPA | exact RPB]).
assert (GB9 : getr regsB (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite (RPB 9 ltac:(unfold acallee_saved; lia)), (RPA 9 ltac:(unfold acallee_saved; lia)); exact G9).
assert (VB_d8 : val_mem rsegs (mrestrict (w_H W2) memB) (e_R (x_e rsegs cx) + 216) 8
  (e_pp (x_e rsegs cx) + HQ_ENT0)).
{ apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memB); [|exact Vd8].
  intros kq Hkq. apply KEB; lia. }
assert (VB_e0 : val_mem rsegs (mrestrict (w_H W2) memB) (e_R (x_e rsegs cx) + 224) 8 (hq_nent r)).
{ apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memB); [|exact Ve0].
  intros kq Hkq. apply KEB; lia. }
(* ---------------- block 2a: the reloads and the `bnez` ---------------- *)
apply (kp_blk2a fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 memB mdB
  regsB (e_R (x_e rsegs cx)) (hq_nent r) (e_pp (x_e rsegs cx) + HQ_ENT0)
  HJB GB9 ltac:(lia) HRal Hppe Hnent1 VB_d8 VB_e0).
- (* ================= no prefix: the pair loop's latch at m + 2 ================= *)
  intros regsC memC mdC HJC HioC RKC C7 C31 KEC Hne.
  assert (RPC : aregs_preserved regsB regsC) by (apply (kp_keep_cs regsB regsC [7; 31]%bv RKC kp_cs2)).
  assert (RP2C : aregs_preserved regs2 regsC) by (eapply aregs_preserved_trans; [exact RP2B | exact RPC]).
  assert (KE2C : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha H1 H2. rewrite (KEC a Ha). rewrite (KEB a Ha H1). apply KEA; assumption. }
  assert (KEAC : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1. rewrite (KEC a Ha). apply KEB; assumption. }
  assert (Hpf : Headamp.ha_prefix kk = false).
  { destruct (Bool.bool_dec (Headamp.ha_prefix kk) true) as [Hp|Hp].
    - exfalso. apply Hne. rewrite Hvv. apply Hviff. apply Hdiff. exact Hp.
    - apply Bool.not_true_is_false. exact Hp. }
  apply (HLATCH fx2 ly2 S2 W2 regsC memC mdC cs keys rf).
  assert (Hio2C : same_io md2 mdC).
  { eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB | exact HioC]. }
  assert (HbaseC : @hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regsC memC mdC).
  { apply (hk_base3_kept B MT errno_low cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regsC memC mdC
      HS Hbase hq_shX_len HJC ltac:(intros q Hq; apply RP2C; unfold acallee_saved; lia) Hio2C).
    intros a Ha Hns Hnw. apply KE2C;
    [ exact Ha | intros HX; apply Hns; lia | intros HX; apply Hnw; unfold hk_wr; left; lia ]. }
  assert (KEW : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. apply KE2C; lia. }
  pose proof Hat as HatS. apply Forall_app in HatS. destruct HatS as [HsegS HrestS].
  apply Forall_app in HrestS. destruct HrestS as [HloopcS _].
  assert (HsegC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hq_L_seg rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memC regs2 regsC (x_e rsegs cx)
      (hq_L_seg rsegs cx) HsegS).
    intros f Hf. apply (hm_keeps_of rsegs (fun _ : Z => True)).
    - intros xq HX. exfalso. exact (HX I).
    - unfold hq_L_seg, hq_L_frame in Hf. cbn [In app] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst]; apply RP2C; unfold acallee_saved; lia|]). destruct Hf. }
  assert (HloopcC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hq_L_loopc rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memC regs2 regsC (x_e rsegs cx)
      (hq_L_loopc rsegs cx) HloopcS).
    intros f Hf.
    apply (hm_keeps_of rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232))); [exact KEW|].
    unfold hq_L_loopc in Hf. cbn [In] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hd_xv]; intros i Hi; lia|]). destruct Hf. }
  assert (BodyC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hq_L_body rsegs cx r)).
  { unfold hq_L_body.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    cbn [fst snd hd_at hd_xv].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + HQ_ENT0)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vc8].
    - rewrite (Z.mod_small (hq_nent r - 1)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vd0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + HQ_ENT0)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vd8].
    - rewrite (Z.mod_small (hq_nent r)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Ve0]. }
  assert (ExtraC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    [(LReg 31, e_pp (x_e rsegs cx) + HQ_ENT0); (LReg 7, hq_nent r); (LReg 21, Z.of_nat (S (S m)))]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    cbn [fst snd hd_at].
    - exact C31.
    - exact C7.
    - replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia.
      rewrite (RP2C 21 ltac:(unfold acallee_saved; lia)). exact G21. }
  pose proof Hxat as (Hxg & Hcl & Hccap & Hckeys & Hkeysb & Hrfv).
  split; [exact HbaseC|].
  split.
  { unfold hs_at_cx, hs_at. rewrite !Forall_app.
    split; [exact HsegC|]. split; [exact HloopcC|]. split; [exact BodyC | exact ExtraC]. }
  split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hlive|].
  split; [unfold hq_nent; lia|]. split; [lia|].
  split.
  { split; [|split; [exact Hcl | split; [exact Hccap | split; [exact Hckeys |
      split; [exact Hkeysb | exact Hrfv]]]]].
    apply (hm_bytes_zbytes rsegs).
    apply (hm_bytes_kept_wr rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232))
      (w_H W2) mem2 (w_H W2) memC (e_F (x_e rsegs cx) + HQ_XO) (hq_x_open cs keys rf)).
    - apply (hm_bytes_zbytes rsegs). exact Hxg.
    - exact KEW.
    - intros xq Hxq. rewrite (hq_x_open_len cs keys rf Hcl) in Hxq. unfold HQ_XO in *. lia. }
  exact (hk_fold_skip cx r at0 m kk cs keys rf Hat0m HSm Hnone Hkey Hfold Hpf).
- (* ================= the prefix: x->keys++ and the blanks loop ================= *)
  intros regsC memC mdC HJC HioC RKC C7 C31 KEC Heq.
  assert (RPC : aregs_preserved regsB regsC) by (apply (kp_keep_cs regsB regsC [7; 31]%bv RKC kp_cs2)).
  assert (RP2C : aregs_preserved regs2 regsC) by (eapply aregs_preserved_trans; [exact RP2B | exact RPC]).
  assert (KE2C : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha H1 H2. rewrite (KEC a Ha). rewrite (KEB a Ha H1). apply KEA; assumption. }
  assert (KEAC : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1. rewrite (KEC a Ha). apply KEB; assumption. }
  assert (Hpt : Headamp.ha_prefix kk = true).
  { apply Hdiff. apply Hviff. rewrite <- Hvv. exact Heq. }
  assert (Hpair : hq_pair_inv rsegs cx r m kk (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf)
    by exact (hk_pair_of_fold cx r at0 m kk cs keys rf Hat0m HSm Hnone Hkey Hfold Hpt).
  assert (Hkb : keys + 1 <= 32) by exact (kp_keys_bound cx r m kk (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf Hwf Hlive Hpair).
  (* the frame object x *)
  assert (HARC : AR rsegs B ly2 S2 W2 memC mdC) by (destruct HJC as (HARC & _); exact HARC).
  destruct (al_frames rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 memC mdC HQ_CID (x_pos rsegs cx) HARC Hfin)
    as (_ & _ & HFpresC & _).
  rewrite HFl2, Hfb in HFpresC.
  assert (KEW : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. apply KE2C; lia. }
  pose proof Hxat as (Hxg & Hcl & Hccap & Hckeys & Hkeysb & Hrfv).
  assert (HxgC : garr8 rsegs (mrestrict (w_H W2) memC) (e_F (x_e rsegs cx) + HQ_XO)
    (hd_zbytes (hq_x_open cs keys rf))).
  { apply (hm_bytes_zbytes rsegs).
    apply (hm_bytes_kept_wr rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232))
      (w_H W2) mem2 (w_H W2) memC (e_F (x_e rsegs cx) + HQ_XO) (hq_x_open cs keys rf)).
    - apply (hm_bytes_zbytes rsegs). exact Hxg.
    - exact KEW.
    - intros xq Hxq. rewrite (hq_x_open_len cs keys rf Hcl) in Hxq. unfold HQ_XO in *. lia. }
  assert (GC9 : getr regsC (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
    by (rewrite (RP2C 9 ltac:(unfold acallee_saved; lia)); exact G9).
  assert (GC18 : getr regsC (Z_to_bv 5 18) = w64 (hk_kaddr rsegs cx m))
    by (rewrite (RP2C 18 ltac:(unfold acallee_saved; lia)); exact G18).
  assert (VC_108 : val_mem rsegs (mrestrict (w_H W2) memC) (e_R (x_e rsegs cx) + 264) 8
    (e_F (x_e rsegs cx) + HQ_XO)).
  { rewrite <- (Z.mod_small (e_F (x_e rsegs cx) + HQ_XO) (2 ^ 64)) by (unfold HQ_XO; lia).
    apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 memC); [|exact C108].
    intros kq Hkq. apply KE2C; lia. }
  assert (VC_xk : val_mem rsegs (mrestrict (w_H W2) memC) (e_F (x_e rsegs cx) + HQ_XO + 128) 4 keys)
    by (apply (kp_x_keys_val cs keys rf (w_H W2) memC (e_F (x_e rsegs cx) + HQ_XO) Hcl ltac:(lia) HxgC)).
  apply (kp_blk2b fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
    (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 memC mdC
    regsC (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx) + HQ_XO) keys (hk_kaddr rsegs cx m)
    HQ_CID (x_pos rsegs cx)
    HJC GC9 GC18 ltac:(lia) HRal
    ltac:(apply (in_app_sub (e_F (x_e rsegs cx)) (fs_frame_bytes HQ_CID));
          [exact HFapp | unfold HQ_XO; lia | lia | rewrite Hfb; unfold HQ_XO; lia])
    ltac:(unfold HQ_XO; lia)
    ltac:(rewrite Z.add_mod by lia; rewrite HF32; unfold HQ_XO; vm_compute; reflexivity)
    ltac:(lia) ltac:(unfold hk_kaddr, HQ_ENT_BODY; lia) ltac:(unfold hk_kaddr, HQ_ENT_BODY; lia)
    VC_108 VC_xk Hown
    ltac:(rewrite HFl2; unfold HQ_XO; lia) ltac:(rewrite HFl2, Hfb; unfold HQ_XO; lia)
    ltac:(intros o Ho; apply (HFpresC (e_F (x_e rsegs cx) + HQ_XO + 128 + o)); unfold HQ_XO; lia)).
  intros regsD memD mdD HJD HioD RKD D10 D11 D15 D16 Vxk1 KED.
  assert (RPD : aregs_preserved regsC regsD)
    by (apply (kp_keep_cs regsC regsD [10; 11; 12; 15; 16]%bv RKD kp_cs3)).
  assert (RP2D : aregs_preserved regs2 regsD) by (eapply aregs_preserved_trans; [exact RP2C | exact RPD]).
  assert (Hio2D : same_io md2 mdD).
  { eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB|].
    eapply same_io_trans; [exact HioC | exact HioD]. }
  assert (KEWD : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232) \/
       (e_F (x_e rsegs cx) + HQ_XO + 128 <= a < e_F (x_e rsegs cx) + HQ_XO + 132)) ->
    aview rsegs (w_H W2) memD a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. rewrite (KED a ltac:(lia) ltac:(lia)). apply KE2C; lia. }
  assert (HbaseD : @hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regsD memD mdD).
  { apply (hk_base3_kept B MT errno_low cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regsD memD mdD
      HS Hbase hq_shX_len HJD ltac:(intros q Hq; apply RP2D; unfold acallee_saved; lia) Hio2D).
    intros a Ha Hns Hnw. apply KEWD. intros HX.
    destruct HX as [HX|[HX|[HX|[HX|HX]]]]; [lia | lia | apply Hns; lia
      | apply Hnw; unfold hk_wr; left; lia | apply Hnw; unfold hk_wr; right; unfold HQ_XO in *; lia]. }
  (* the cut's lists at memD *)
  pose proof Hat as HatS. apply Forall_app in HatS. destruct HatS as [HsegS HrestS].
  apply Forall_app in HrestS. destruct HrestS as [HloopcS _].
  assert (HsegD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hq_L_seg rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memD regs2 regsD (x_e rsegs cx)
      (hq_L_seg rsegs cx) HsegS).
    intros f Hf. apply (hm_keeps_of rsegs (fun _ : Z => True)).
    - intros xq HX. exfalso. exact (HX I).
    - unfold hq_L_seg, hq_L_frame in Hf. cbn [In app] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst]; apply RP2D; unfold acallee_saved; lia|]). destruct Hf. }
  assert (HloopcD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hq_L_loopc rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memD regs2 regsD (x_e rsegs cx)
      (hq_L_loopc rsegs cx) HloopcS).
    intros f Hf.
    apply (hm_keeps_of rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 200 <= a < e_R (x_e rsegs cx) + 232) \/
      (e_F (x_e rsegs cx) + HQ_XO + 128 <= a < e_F (x_e rsegs cx) + HQ_XO + 132))); [exact KEWD|].
    unfold hq_L_loopc in Hf. cbn [In] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hd_xv]; intros i Hi; unfold HQ_XO in *; lia|]). destruct Hf. }
  assert (KEAD : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_F (x_e rsegs cx) + HQ_XO + 128 <= a < e_F (x_e rsegs cx) + HQ_XO + 132) ->
    aview rsegs (w_H W2) memD a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1 H2. rewrite (KED a Ha H2). apply KEAC; assumption. }
  assert (BodyD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hq_L_body rsegs cx r)).
  { unfold hq_L_body.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    cbn [fst snd hd_at hd_xv].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + HQ_ENT0)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQ_XO in *; lia | exact Vc8].
    - rewrite (Z.mod_small (hq_nent r - 1)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQ_XO in *; lia | exact Vd0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + HQ_ENT0)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQ_XO in *; lia | exact Vd8].
    - rewrite (Z.mod_small (hq_nent r)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQ_XO in *; lia | exact Ve0]. }
  assert (ExtraD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    [(LReg 31, e_pp (x_e rsegs cx) + HQ_ENT0); (LReg 7, hq_nent r);
     (LReg 20, Z.of_nat m + 1); (LReg 21, Z.of_nat m + 2)]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    cbn [fst snd hd_at].
    - exact (eq_trans (RKD (31%bv) ltac:(vm_compute; discriminate) ltac:(cbn [In]; intros HX; repeat (destruct HX as [HX|HX]; [apply (f_equal (@bv_unsigned 5)) in HX; vm_compute in HX; discriminate HX|]); exact HX)) C31).
    - exact (eq_trans (RKD (7%bv) ltac:(vm_compute; discriminate) ltac:(cbn [In]; intros HX; repeat (destruct HX as [HX|HX]; [apply (f_equal (@bv_unsigned 5)) in HX; vm_compute in HX; discriminate HX|]); exact HX)) C7).
    - rewrite (RP2D 20 ltac:(unfold acallee_saved; lia)). exact G20.
    - rewrite (RP2D 21 ltac:(unfold acallee_saved; lia)). exact G21. }
  assert (HxatD : hq_x_at rsegs cx W2 memD cs (keys + 1) rf).
  { split; [|split; [exact Hcl | split; [lia | split; [lia | split; [lia | exact Hrfv]]]]].
    apply (kp_x_store cs keys rf (w_H W2) mem2 (w_H W2) memD (e_F (x_e rsegs cx) + HQ_XO) Hcl Hkeysb Hxg).
    - exact Vxk1.
    - intros y Hy Hny. apply KEWD. unfold HQ_XO in *. lia. }
  apply (HBL fx2 ly2 S2 W2 regsD memD mdD kk cs keys rf).
  split.
  { split; [exact HbaseD|].
    split.
    { unfold hs_at_cx, hs_at, hk_L. rewrite !Forall_app.
      split; [exact HsegD|]. split; [exact HloopcD|]. split; [exact BodyD | exact ExtraD]. }
    split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hlive|]. split; [exact Hat0m|].
    split; [exact Hkey|]. split; [exact Hpair|]. split; [exact HxatD | exact Hckeys]. }
  split.
  { unfold hs_at_cx, hs_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]]; cbn [fst snd hd_at].
    - rewrite (RP2D 18 ltac:(unfold acallee_saved; lia)). exact G18.
    - exact D10.
    - cbn [Z.of_nat]. exact D11.
    - exact D15.
    - exact D16. }
  lia.
Qed.

Print Assumptions hk_P1.

End d.
End b.
