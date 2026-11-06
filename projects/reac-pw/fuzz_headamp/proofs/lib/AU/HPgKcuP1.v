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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgKcP1.v, with its module names, addresses and numbers changed; 818 of its 1352 lines of code are new or changed and 661 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): PART 1 of the piece "the key and the channel" of the walk of
   LLVMFuzzerTestOneInput (lib/AU/HPgKcuCut.v hku_P1_stmt): KEY 0x83260 -> LATCH 0x836b4 (the key has no
   prefix) / BL 0x832e8 (it has). Proves no function (kind: segment lemma).

   THE CODE (0x83260 .. 0x832e4, 34 words; the table kpu_tbl)
     0x83260 addiw a0,a2,1          a0 := m + 2   (a2 = m + 1)
     0x83264 blt  a0,a2 -> unimp    never: the increment of m + 1 does not overflow 32 bits
     0x83268 bltz a2    -> RC       never: a2 = m + 1 >= 1
     0x8326c sd a0,216(s1)          R+0xd8  := m + 2
     0x83270 sd t3,224(s1)          R+0xe0  := t3
     0x83274 sd t2,240(s1)          R+0xf0  := t2
     0x83278 sd t4,232(s1)          R+0xe8  := t4
     0x8327c sd t0,248(s1)          R+0xf8  := t0
     0x83280 sd t1,256(s1)          R+0x100 := t1
     0x83284 auipc a0 / 0x83288 addi a1,a0,-836   a1 := 0x20f40, the harness's "reac.headamp."
     0x8328c li a2,13 / 0x83290 mv a0,s7         a2 := 13, a0 := the key
     0x83294 sd t5,272(s1)          R+0x110 := t5
     0x83298 sd t6,264(s1)          R+0x108 := t6
     0x8329c jal 0x41c24            the strncmp wrapper (lib/AU/HPgKcuNcmp.v hkn_strncmp_key_call), ra = 0x832a0
     0x832a0 ld t6,264(s1) / 0x832a4 ld t5,272(s1)    t6 and t5 back
     0x832a8 bnez a0 -> 0x836b4     no prefix: the pair loop's latch with the next index m + 2
     0x832ac ld a2,312(s1)          a2 := x (the frame object at F + 0x2c0)
     0x832b0 lw a1,128(a2) / 0x832b4 addiw a0,a1,1 / 0x832b8 blt a0,a1 -> unimp / 0x832bc sw a0,128(a2)
                                    x->keys++ with its UBSan test (never: x->keys < 2 ^ 31 - 2)
     0x832c0 li a0,-13 / 0x832c4 li a6,5 / 0x832c8 li a7,32 / 0x832cc li t2,9 / 0x832d0 li t3,10
     0x832d4 ld t4,208(s1)          t4 := R+0xd0 = 1000000, read_channel's bound
     0x832d8 bgeu s7,a0 -> unimp    never: the key lies below 2 ^ 64 - 13
     0x832dc li a1,0 / 0x832e0 addi a0,s7,13 / 0x832e4 not a2,a0
   and falls through to BL 0x832e8.  The eight saves are exactly the cells lib/AU/HPgSegM.v hqu_L_body (m + 2)
   names, and their values are the KEY cut's own registers (hqu_L_loopr t0 t1 t2 t3 t4, hqu_L_t56 t5 t6).

   THE WRITES: the real-frame cells [R+0xd8, R+0x118), the wrapper's own stack [R - 2 ESTACK, R) and, on the
   prefix arm, the four bytes of x->keys; all three lie in lib/AU/HPgKcuLib.v hku_wr, so hqu_base3 crosses them
   by hku_base3_kept.  No instrumented check is in this range (x's granules are 0x00 in hqu_shX and the real
   frame is not instrumented), so the token runner with an empty shadow-entry list decides every step; the four
   branches above are split by hand.

   Section hypotheses: errno_low (lib/AU/HPgKcuLib.v's) and STRNCMP (lib/AU/HPgKcuNcmp.v's, the wrapper's
   contract at 0x41c24 at every float state), both passed through unchanged. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require KeyFacts PairFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuCut HPgKcuLib HPgKcuLoop HPgKcuNcmp HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================== the code table and the entry states ======================== *)
(* the 34 words 0x83260 .. 0x832e4; BL 0x832e8 lies outside it *)
Definition kpu_tbl : ctable := build_table rsegs HQU_KEY 34 TEmpty.
Lemma kpu_tbl_ok : table_ok rsegs kpu_tbl.
Proof. apply build_table_ok0. unfold HQU_KEY. lia. Qed.

Definition KPU_KEYS : Z := 0x832ac.   (* the pc after the `bnez a0` of 0x832a8 *)
Definition KPU_CST : Z := 0x832c0.    (* x->keys is stored; the six constants follow *)

(* block 1: the eight saves into [R+0xd8, R+0x118) of the real frame (s1 = R is atom 9; a2 = m + 1 is atom 12,
   whose range lets the engine fold the `addiw` into the atom's offset) *)
Definition kpu_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0x118 0xd8 0x118 [].
Definition kpu_F1 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (12%nat, mkAF 0 33 0)] [] [].
Definition kpu_S1 : sstate := mkSS HQU_KEY sr_atoms [kpu_R1] None kpu_F1.

(* block 2a: the two reloads of t6 and t5 (atoms 33 and 34) and the `bnez` *)
Definition kpu_R2 : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x118 0 0
  [YP09.mkChunk 0x108 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 34 0))].
Definition kpu_F2 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition kpu_S2 : sstate := mkSS RB_STRNCMP sr_atoms [kpu_R2] None kpu_F2.

(* block 2b: x from R+0x138 (atom 33) and x->keys (atom 34).  The entry state is image A's twin: two
   regions and three atom facts.  A state that carries more than that (a third region, a wide span whose
   middle bytes no chunk covers) makes one step of the run grow to several GB, so the part of the walk
   that reads R+0xd0 is block 2c, with its own small state. *)
Definition kpu_R3 : YP09.region := YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0
  [YP09.mkChunk 0x138 (CVal 8 (SOff 33 0))].
Definition kpu_RX : YP09.region := YP09.mkRegion (Some 33%nat) 0x80 0x84 0x80 0x84
  [YP09.mkChunk 0x80 (CVal 4 (SOff 34 0))].
(* x lies in application memory, so its write window is apart from the shadow band; the engine's static check
   asks that as ONE interval, so the two halves of application memory are two entry states. *)
Definition kpu_F3a : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 4096 (0x7fff7000 - 132) 5);
           (34%nat, mkAF 0 (2 ^ 31 - 2) 0)] [] [].
Definition kpu_F3b : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 0x10007fff8000 (2 ^ 47) 5);
           (34%nat, mkAF 0 (2 ^ 31 - 2) 0)] [] [].
Definition kpu_S3a : sstate := mkSS KPU_KEYS sr_atoms [kpu_R3; kpu_RX] None kpu_F3a.
Definition kpu_S3b : sstate := mkSS KPU_KEYS sr_atoms [kpu_R3; kpu_RX] None kpu_F3b.

(* block 2c: read_channel's bound from R+0xd0 (atom 33) and the key in s7 (atom 23), whose range decides
   the pointer trap test of 0x832d8 *)
Definition kpu_R4 : YP09.region := YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0 0
  [YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0))].
Definition kpu_F4 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF 0x4000 (2 ^ 47) 0)] [] [].
Definition kpu_S4 : sstate := mkSS KPU_CST sr_atoms [kpu_R4] None kpu_F4.

(* ======================== the model: how many keys the fold counts ======================== *)
Lemma kpu_pairs_len : forall kf es k, (length (Accessors.pairs_by kf es k) <= length es)%nat.
Proof.
intros kf es. induction es as [|e es IH]; intros k; [cbn; lia|].
cbn [Accessors.pairs_by length]. destruct k as [k'|].
- cbn [length]. pose proof (IH None). lia.
- pose proof (IH (kf e)). lia.
Qed.

(* ha_fold never lowers the key counter, and raises it past a pair whose key has the prefix *)
Lemma kpu_fold_keys : forall cellf cap ps cs keys rf,
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

Lemma kpu_fold_pref : forall cellf cap k v ps cs keys rf,
Headamp.ha_prefix k = true ->
keys + 1 <= snd (fst (Headamp.ha_fold cellf cap ((k, v) :: ps) cs keys rf)).
Proof.
intros cellf cap k v ps cs keys rf Hp. cbn [Headamp.ha_fold]. rewrite Hp. cbn [negb].
destruct (cellf k v) as [bad|c].
- pose proof (kpu_fold_keys cellf cap ps cs (keys + 1) (if rf =? Headamp.REFUSE_NONE then bad else rf)). lia.
- destruct (cap <=? Z.of_nat (length cs)); [cbn [fst snd]; lia|].
  pose proof (kpu_fold_keys cellf cap ps (cs ++ [c]) (keys + 1) rf). lia.
Qed.

Section mdl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma kpu_exp_keys_le : forall cx r, Model.pod_rec_wf r -> hqu_live rsegs cx r ->
ans_keys (hqu_exp rsegs cx r) <= 32.
Proof.
intros cx r Hw (Hnull & _ & Hprops & Hpst).
assert (E1 : (e_null (x_e rsegs cx) =? 1) = false) by (rewrite Hnull; reflexivity).
unfold hqu_exp, Headamp.expect_model. rewrite E1, Hprops, Hpst. cbn [orb negb]. cbv iota.
pose proof (kpu_fold_keys Headamp.expect_cell (e_cap (x_e rsegs cx))
  (Accessors.pairs (Model.ents r)) [] 0 Headamp.REFUSE_NONE) as Hb.
destruct (Headamp.ha_fold Headamp.expect_cell (e_cap (x_e rsegs cx))
  (Accessors.pairs (Model.ents r)) [] 0 Headamp.REFUSE_NONE) as [[cells kk] rf0].
cbn [fst snd] in Hb. unfold Accessors.pairs in Hb.
unfold Headamp.ha_result, ans_keys. cbn [fst snd].
pose proof (kpu_pairs_len Accessors.key_of (Model.ents r) None) as Hl.
destruct (Model.ents_wf r Hw) as [Hle _]. lia.
Qed.

(* the key counter of a pair cut: the fold has yet to count this key, so one more is still at most 32 *)
Lemma kpu_keys_bound : forall cx r m k v cs keys rf,
Model.pod_rec_wf r -> hqu_live rsegs cx r -> hqu_pair_inv rsegs cx r m k v cs keys rf ->
keys + 1 <= 32.
Proof.
intros cx r m k v cs keys rf Hw Hlive (Hv & Hpref & Hm & Hfold).
pose proof (kpu_fold_pref Headamp.expect_cell (e_cap (x_e rsegs cx)) k v
  (Accessors.pairs_by Accessors.key_of (skipn (S (S m)) (Model.ents r)) None) cs keys rf Hpref) as H1.
rewrite Hfold in H1. unfold hqu_fin in H1. cbn [fst snd] in H1.
pose proof (kpu_exp_keys_le cx r Hw Hlive). lia.
Qed.
End mdl.

(* ======================== engine helpers ======================== *)
(* a chunk of a region of the engine's state, read back as a value of memory *)
Lemma kpu_chunk : forall E (mem : word -> option byte) (n : nat) (b lo hi wlo whi : Z)
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
exact (val_of_chunk_ok rsegs E mem b off w (SOff j c) (v + c) Hck
  (ku_soff E j v c Hj Hv Hvc) Hw8 Hw).
Qed.

(* the four bytes of x->keys inside the 136 bytes of the frame object x *)
Lemma kpu_x_keys_val : forall cs keys rf (H : word -> bool) mem x,
(length cs <= X_CELLS)%nat -> 0 <= keys < 2 ^ 64 ->
garr8 rsegs (mrestrict H mem) x (hd_zbytes (hqu_x_open cs keys rf)) ->
val_mem rsegs (mrestrict H mem) (x + 128) 4 keys.
Proof.
intros cs keys rf H mem x Hcs Hk Hg.
apply (hm_bytes_zbytes rsegs) in Hg. unfold hqu_x_open in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite repeat_length in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite length_x_cells_bytes in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite repeat_length in Hg.
unfold ha_res_bytes in Hg.
apply (hm_bytes_app rsegs) in Hg as [_ Hg]. rewrite Mem.length_le4 in Hg.
apply (hm_bytes_app rsegs) in Hg as [Hg _].
replace (x + Z.of_nat 4 + Z.of_nat (12 * length cs) + Z.of_nat (12 * (X_CELLS - length cs)) + Z.of_nat 4)
  with (x + 128) in Hg by (unfold X_CELLS in *; lia).
unfold Mem.le4 in Hg. rewrite unsigned_lit_small in Hg by lia.
exact (hm_val_of_bytes rsegs _ _ _ _ _ Hg).
Qed.

(* the 136 bytes of x with x->keys one more *)
Lemma kpu_x_store : forall cs keys rf (H : word -> bool) mem (H' : word -> bool) mem' x,
(length cs <= X_CELLS)%nat -> 0 <= keys < 2 ^ 31 - 1 ->
garr8 rsegs (mrestrict H mem) x (hd_zbytes (hqu_x_open cs keys rf)) ->
val_mem rsegs (mrestrict H' mem') (x + 128) 4 (keys + 1) ->
(forall y, x <= y < x + 136 -> ~ (x + 128 <= y < x + 132) -> aview rsegs H' mem' y = aview rsegs H mem y) ->
garr8 rsegs (mrestrict H' mem') x (hd_zbytes (hqu_x_open cs (keys + 1) rf)).
Proof.
intros cs keys rf H mem H' mem' x Hcs Hk Hg Hv Hkeep.
rewrite <- (hku_x_open_keys cs keys rf Hcs Hk).
apply (hm_bytes_zbytes rsegs).
apply (hm_bytes_store rsegs H mem H' mem' x (hqu_x_open cs keys rf) 128 4 (keys + 1)).
- apply (hm_bytes_zbytes rsegs). exact Hg.
- change (Z.of_nat 128) with 128. exact Hv.
- rewrite (hqu_x_open_len cs keys rf Hcs). lia.
- rewrite (hqu_x_open_len cs keys rf Hcs). intros y Hy Hn. apply Hkeep; [lia|].
  change (Z.of_nat 128) with 128 in Hn. change (Z.of_nat (128 + 4)) with 132 in Hn. lia.
Qed.

(* membership in a computed chunk list *)
Ltac kpu_chin := cbn [In]; repeat (first [left; reflexivity | right]); fail.
(* the write-window goal of a run over the real frame only *)
Ltac kpu_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with B9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.
(* the region of index i of the engine's state, read back *)
Ltac kpu_region HS i Hname :=
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
(* membership in a cut's list *)
Ltac kpu_lin := unfold hku_L, hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_loopr, hqu_L_t56, hqu_L_body;
cbv zeta; cbn [In app]; repeat (first [left; reflexivity | right]).

Lemma kpu_bvq : forall q : Z, 0 <= q < 32 -> bv_unsigned (Z_to_bv 5 q) = q.
Proof.
intros q Hq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

(* a run that keeps every register outside a list of caller-saved ones keeps the callee-saved set *)
Lemma kpu_keep_cs : forall (regs regs' : bvmap 5 word) (l : list (bv 5)),
(forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr l -> getr regs' rr = getr regs rr) ->
(forall c, In c l -> ~ acallee_saved (bv_unsigned c)) ->
aregs_preserved regs regs'.
Proof.
intros regs regs' l HK Hl q Hq.
assert (Hq32 : 0 <= q < 32) by (unfold acallee_saved in Hq; lia).
apply HK.
- rewrite kpu_bvq by lia. unfold acallee_saved in Hq. lia.
- intros Hin. pose proof (Hl _ Hin) as Hn. rewrite kpu_bvq in Hn by lia. exact (Hn Hq).
Qed.

Ltac kpu_csnot :=
lazymatch goal with |- ~ acallee_saved (bv_unsigned ?X) =>
let v := eval vm_compute in (bv_unsigned X) in
replace (bv_unsigned X) with v by (vm_compute; reflexivity) end;
unfold acallee_saved; lia.

Lemma kpu_cs1 : forall c : bv 5, In c [1; 10; 11; 12]%bv -> ~ acallee_saved (bv_unsigned c).
Proof. intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; kpu_csnot. Qed.
Lemma kpu_cs2 : forall c : bv 5, In c [30; 31]%bv -> ~ acallee_saved (bv_unsigned c).
Proof. intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; kpu_csnot. Qed.
Lemma kpu_cs3 : forall c : bv 5, In c [7; 10; 11; 12; 16; 17; 28; 29]%bv ->
~ acallee_saved (bv_unsigned c).
Proof.
intros c Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kpu_csnot.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
(* the strncmp wrapper's contract at image B's trampoline 0x41c24, as lib/AU/HPgKcuNcmp.v states it at
   segs = Img0U.rsegs, for EVERY float state: the cut this part starts from is at the walk's own float state
   fx2, not at the Section's fx, and only `cfg_at` in that text names a float state. *)
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
SRr rsegs W (@cfg_at fx' rsegs B_STRNCMP regs mem md)
(fun (W' : world rsegs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
 AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the lemmas of lib/AU/HPgKcuLib.v, with or without the Section hypothesis errno_low *)
Ltac kpu_lib L H := first [pose proof (L errno_low) as H | pose proof L as H].

(* ======================== what the segment's start gives about the frame ======================== *)
Lemma kpu_start : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
  Model.pod_rec_wf r /\
  In (HQU_CID, x_pos rsegs cx) (x_own rsegs cx) /\
  e_F (x_e rsegs cx) = frame_addr (x_ly rsegs cx) HQU_CID (x_pos rsegs cx) /\
  e_R (x_e rsegs cx) mod 32 = 0 /\
  e_R (x_e rsegs cx) + HQU_RSZ <= e_S (x_e rsegs cx) /\
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
cbn [hi_cid hi_rsz headamp_himg_B] in Hown, HFeq, HRsz.
(* the frame's address is the same under every layout of the journal, so state it at its start *)
assert (HFl : frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) = frame_addr (x_ly rsegs cx) 4 (x_pos rsegs cx))
  by (eapply hc_frame_addr_j; exact HJ).
rewrite HFl in HFeq.
unfold HQU_CID, HQU_RSZ.
split; [exact Hwf|]. split; [exact Hown|]. split; [exact HFeq|]. split; [exact HRal|].
split; [exact HRsz|]. split; [exact HeS|]. split; [exact Hwin|]. split; [exact Hev|].
split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma kpu_core : forall cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ev,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
@hc_core rc SK rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ev HS Hb.
destruct (kpu_start cx r ev HS) as (Hwf & Hown & HFeq & HRal & HRsz & HeS & Hwin & Hev & H2 & H3 & H4).
destruct Hb as (Hcore & _). destruct Hcore as (HJ & Hregs & _).
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 16 32); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact HRal]. }
split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hregs 2 ltac:(tauto))|].
split; [rewrite <- H3; exact (Hregs 3 ltac:(tauto))|].
split; [rewrite <- H4; exact (Hregs 4 ltac:(tauto))|].
split; [exact HR16|]. split; [exact Hwin|]. unfold HQU_RSZ in HRsz. lia.
Qed.

(* ======================== block 1: KEY 0x83260 .. the `jal` of the wrapper ======================== *)
Lemma kpu_blk1 : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R key mm w5 w6 w7 w28 w29 w30 w31 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R ->
getr regs (Z_to_bv 5 23) = w64 key ->
getr regs (Z_to_bv 5 12) = w64 (mm + 1) ->
getr regs (Z_to_bv 5 5) = w64 w5 -> getr regs (Z_to_bv 5 6) = w64 w6 ->
getr regs (Z_to_bv 5 7) = w64 w7 -> getr regs (Z_to_bv 5 28) = w64 w28 ->
getr regs (Z_to_bv 5 29) = w64 w29 -> getr regs (Z_to_bv 5 30) = w64 w30 ->
getr regs (Z_to_bv 5 31) = w64 w31 ->
0 <= mm <= 32 -> 0 <= key < 2 ^ 64 ->
0 <= w5 < 2 ^ 64 -> 0 <= w6 < 2 ^ 64 -> 0 <= w7 < 2 ^ 64 -> 0 <= w28 < 2 ^ 64 ->
0 <= w29 < 2 ^ 64 -> 0 <= w30 < 2 ^ 64 -> 0 <= w31 < 2 ^ 64 ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' (Z_to_bv 5 1) = w64 RB_STRNCMP ->
 getr regs' (Z_to_bv 5 10) = w64 key ->
 getr regs' (Z_to_bv 5 11) = w64 B_HKEY ->
 getr regs' (Z_to_bv 5 12) = w64 13 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0xd8) 8 (mm + 2) ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0xe0) 8 w28 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0xe8) 8 w29 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0xf0) 8 w7 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0xf8) 8 w5 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0x100) 8 w6 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0x108) 8 w31 ->
 val_mem rsegs (mrestrict (w_H W) mem') (R + 0x110) 8 w30 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xd8 <= a < R + 0x118) ->
    aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 SRr rsegs W (@cfg_at fx2 rsegs B_STRNCMP regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs HQU_KEY regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R key mm w5 w6 w7 w28 w29 w30 w31
  HJ H9 H23 H12 H5 H6 H7 H28 H29 H30 H31 Hmm Hkey Hb5 Hb6 Hb7 Hb28 Hb29 Hb30 Hb31
  HR HRal Hwin Hrsz Hpres K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hts : T_SEG_STK = 16384) by reflexivity. rewrite Hts in Hwin.
assert (HS : st_ok rsegs (Ereg regs rt_extra) kpu_S1
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 HQU_KEY) memc (seg_rom rsegs)))).
{ assert (B9' : bv_unsigned (ew (Ereg regs rt_extra) 9) = R)
    by (rewrite (ew_Ereg_nat regs rt_extra 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
  assert (B12' : bv_unsigned (ew (Ereg regs rt_extra) 12) = mm + 1)
    by (rewrite (ew_Ereg_nat regs rt_extra 12 (Z_to_bv 5 12) eq_refl), H12; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold kpu_S1. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold kpu_R1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kpu_F1 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9', B12'.
    change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (B9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 9 (Z_to_bv 5 9) eq_refl), H9;
      apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = Z_to_bv 64 (mm + 1))
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 12 (Z_to_bv 5 12) eq_refl); exact H12).
assert (E23 : ew E 23 = Z_to_bv 64 key)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 23 (Z_to_bv 5 23) eq_refl); exact H23).
assert (E5 : ew E 5 = Z_to_bv 64 w5)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 5 (Z_to_bv 5 5) eq_refl); exact H5).
assert (E6 : ew E 6 = Z_to_bv 64 w6)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 6 (Z_to_bv 5 6) eq_refl); exact H6).
assert (E7 : ew E 7 = Z_to_bv 64 w7)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 7 (Z_to_bv 5 7) eq_refl); exact H7).
assert (E28 : ew E 28 = Z_to_bv 64 w28)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 28 (Z_to_bv 5 28) eq_refl); exact H28).
assert (E29 : ew E 29 = Z_to_bv 64 w29)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 29 (Z_to_bv 5 29) eq_refl); exact H29).
assert (E30 : ew E 30 = Z_to_bv 64 w30)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 30 (Z_to_bv 5 30) eq_refl); exact H30).
assert (E31 : ew E 31 = Z_to_bv 64 w31)
  by (subst E; rewrite (ew_Ereg_nat regs rt_extra 31 (Z_to_bv 5 31) eq_refl); exact H31).
assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
clear HE.
unfold cfg_at. change (w64 HQU_KEY) with (Z_to_bv 64 HQU_KEY).
(* 0x83260 .. 0x8329c: the increment, its two trap tests (the engine decides both from the atom facts:
   a2 = m + 1 lies in [0, 33], so m + 2 is above it and a2 is not negative), the eight saves and the
   `jal`, which leaves the table *)
aj_run_tok kpu_tbl_ok HS HJ SHOK RTBspan; [kpu_awr|].
    assert (R1' : getr (ms_regs ms) (Z_to_bv 5 1) = w64 RB_STRNCMP).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 1) HS). ku_sv. reflexivity. }
    assert (R10' : getr (ms_regs ms) (Z_to_bv 5 10) = w64 key).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 10) HS). ku_sv.
      rewrite ku_denot0, E23. reflexivity. }
    assert (R11' : getr (ms_regs ms) (Z_to_bv 5 11) = w64 B_HKEY).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 11) HS). ku_sv. reflexivity. }
    assert (R12' : getr (ms_regs ms) (Z_to_bv 5 12) = w64 13).
    { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 12) HS). ku_sv. reflexivity. }
    assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12]%bv ->
      getr (ms_regs ms) rr = getr regs rr).
    { intros rr Hr0 Hn.
      exact (regs_kept_of_st_ok rsegs _ _ ms regs rt_extra (w_H W) [1; 10; 11; 12]%bv
        HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
    kpu_region HS 0%nat HRok.
    assert (V_d8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xd8) 8 (mm + 2)).
    { replace (mm + 2) with (mm + 1 + 1) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E12 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_e0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xe0) 8 w28).
    { replace w28 with (w28 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E28 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_e8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xe8) 8 w29).
    { replace w29 with (w29 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E29 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_f0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xf0) 8 w7).
    { replace w7 with (w7 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E7 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_f8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xf8) 8 w5).
    { replace w5 with (w5 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E5 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_100 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x100) 8 w6).
    { replace w6 with (w6 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E6 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_108 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x108) 8 w31).
    { replace w31 with (w31 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E31 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (V_110 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x110) 8 w30).
    { replace w30 with (w30 + 0) by lia. change 8%nat with (N.to_nat 8).
      eapply (kpu_chunk _ _ 9%nat R); [exact HRok | exact B9 | kpu_chin | exact E30 | lia | lia
        | cbn; lia | cbn; lia]. }
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xd8 <= a < R + 0x118) ->
      aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
    { eapply (cb_kept_run (fun a => R + 0xd8 <= a < R + 0x118) _ _ (w_H W) memc _ (ms_mem ms)).
      - intros a Ha Hz. reflexivity.
      - exact HFr.
      - intros a (rr & Hin & Hb).
        lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
        destruct Hin as [<-|[]].
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite B9 in Hb. exact Hb. }
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
      replace (ss_pc ss) with B_STRNCMP by (vm_compute; reflexivity) end.
    eapply K;
    [ exact HJ | ku_io | exact RK | exact R1' | exact R10' | exact R11' | exact R12'
    | exact V_d8 | exact V_e0 | exact V_e8 | exact V_f0 | exact V_f8 | exact V_100 | exact V_108
    | exact V_110 | exact KE ].
Qed.

(* ======================== block 2a: 0x832a0 .. LATCH 0x836b4 / 0x832ac ======================== *)
Definition kpu_ex2 (w31 w30 : Z) : list word := [Z_to_bv 64 SBr; w64 w31; w64 w30].

Lemma kpu_blk2a : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R w30 w31 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
0 <= w30 < 2 ^ 64 -> 0 <= w31 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 w31 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 w30 ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [30; 31]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' (Z_to_bv 5 30) = w64 w30 -> getr regs' (Z_to_bv 5 31) = w64 w31 ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 getr regs (Z_to_bv 5 10) <> w64 0 ->
 SRr rsegs W (@cfg_at fx2 rsegs HQU_LATCH regs' mem' md') Q) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [30; 31]%bv -> getr regs' rr = getr regs rr) ->
 getr regs' (Z_to_bv 5 30) = w64 w30 -> getr regs' (Z_to_bv 5 31) = w64 w31 ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 getr regs (Z_to_bv 5 10) = w64 0 ->
 SRr rsegs W (@cfg_at fx2 rsegs KPU_KEYS regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs RB_STRNCMP regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R w30 w31
  HJ H9 HR HRal Hb30 Hb31 V108 V110 KL KN.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (HS : st_ok rsegs (Ereg regs (kpu_ex2 w31 w30)) kpu_S2
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 RB_STRNCMP) memc (seg_rom rsegs)))).
{ assert (B9' : bv_unsigned (ew (Ereg regs (kpu_ex2 w31 w30)) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
  assert (A33 : ew (Ereg regs (kpu_ex2 w31 w30)) 33 = Z_to_bv 64 w31)
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (A34 : ew (Ereg regs (kpu_ex2 w31 w30)) 34 = Z_to_bv 64 w30)
    by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite restrict_mkst_fx. unfold kpu_S2. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold kpu_R2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 33 0) w31);
      [rewrite ku_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact V108].
    + apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 34 0) w30);
      [rewrite ku_denot0; exact A34 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact V110].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kpu_F2 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9'. change (2 ^ 5) with 32. repeat split; lia. }
remember (Ereg regs (kpu_ex2 w31 w30)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (kpu_ex2 w31 w30)) E) by (subst E; apply env_agree_refl).
assert (B9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
assert (A33 : ew E 33 = Z_to_bv 64 w31)
  by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A34 : ew E 34 = Z_to_bv 64 w30)
  by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10 : ew E 10 = getr regs (Z_to_bv 5 10))
  by (subst E; exact (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl)).
assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
clear HE.
unfold cfg_at. change (w64 RB_STRNCMP) with (Z_to_bv 64 RB_STRNCMP).
(* 0x832a0 / 0x832a4: the two reloads; stop at the `bnez` *)
aj_run_to_tok kpu_tbl_ok HS HJ SHOK RTBspan 0x832a8; [kpu_awr|].
rename ms into ms1.
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms1) a = aview rsegs (w_H W) memc a).
{ intros a Ha.
  exact (cb_kept_run (fun _ => False) E (ss_mem kpu_S2) (w_H W) memc memc (ms_mem ms1)
    ltac:(intros b Hb Hz; reflexivity) HFr
    ltac:(intros b (rr & Hin & Hb);
          lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
          destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
    a Ha ltac:(intros HF0; exact HF0)). }
clear HF HFr HG.
assert (HU10 : U E (SOff 10 0) = bv_unsigned (getr regs (Z_to_bv 5 10)))
  by (unfold U; rewrite ku_denot0, E10; reflexivity).
srr_branch_tok kpu_tbl_ok HS SHOK RTBspan.
- (* taken: a0 <> 0, to LATCH *)
  rewrite branch_ne_U, HU10, (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_tok kpu_tbl_ok HS HJ SHOK RTBspan; [kpu_awr|].
  assert (R30' : getr (ms_regs ms) (Z_to_bv 5 30) = w64 w30).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 30) HS). ku_sv.
    rewrite ku_denot0, A34. reflexivity. }
  assert (R31' : getr (ms_regs ms) (Z_to_bv 5 31) = w64 w31).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 31) HS). ku_sv.
    rewrite ku_denot0, A33. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [30; 31]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kpu_ex2 w31 w30) (w_H W) [30; 31]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { intros a Ha.
    exact (cb_kept_run (fun _ => False) E (ss_mem kpu_S2) (w_H W) memc _ (ms_mem ms)
      ltac:(intros b Hb Hz; apply KE1; exact Hb) HFr
      ltac:(intros b (rr & Hin & Hb);
            lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
            destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
      a Ha ltac:(intros HF0; exact HF0)). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with HQU_LATCH by (vm_compute; reflexivity) end.
  eapply KL; [exact HJ | ku_io | exact RK | exact R30' | exact R31' | exact KE |].
  intros Hz. apply Hc. rewrite Hz. reflexivity.
- (* not taken: a0 = 0, to 0x832ac *)
  rewrite branch_ne_U, HU10, (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_tok kpu_tbl_ok HS HJ SHOK RTBspan; [kpu_awr|].
  assert (R30' : getr (ms_regs ms) (Z_to_bv 5 30) = w64 w30).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 30) HS). ku_sv.
    rewrite ku_denot0, A34. reflexivity. }
  assert (R31' : getr (ms_regs ms) (Z_to_bv 5 31) = w64 w31).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 31) HS). ku_sv.
    rewrite ku_denot0, A33. reflexivity. }
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [30; 31]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kpu_ex2 w31 w30) (w_H W) [30; 31]%bv
      HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { intros a Ha.
    exact (cb_kept_run (fun _ => False) E (ss_mem kpu_S2) (w_H W) memc _ (ms_mem ms)
      ltac:(intros b Hb Hz; apply KE1; exact Hb) HFr
      ltac:(intros b (rr & Hin & Hb);
            lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
            destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
      a Ha ltac:(intros HF0; exact HF0)). }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with KPU_KEYS by (vm_compute; reflexivity) end.
  eapply KN; [exact HJ | ku_io | exact RK | exact R30' | exact R31' | exact KE |].
  apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* ======================== block 2b: 0x832ac .. 0x832c0 (x->keys++) ======================== *)
Definition kpu_ex3 (x keys : Z) : list word := [Z_to_bv 64 SBr; w64 x; w64 keys].

Lemma kpu_blk2b : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R x keys cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
in_app x 132 -> x + 132 <= R -> x mod 32 = 0 ->
0 <= keys <= 2 ^ 31 - 2 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 x ->
val_mem rsegs (mrestrict (w_H W) memc) (x + 128) 4 keys ->
In (cid, pos) own ->
frame_addr ly2 cid pos <= x -> x + 132 <= frame_addr ly2 cid pos + fs_frame_bytes cid ->
(forall o, 0 <= o < 4 -> apresent (w_H W) memc (x + 128 + o)) ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12]%bv -> getr regs' rr = getr regs rr) ->
 val_mem rsegs (mrestrict (w_H W) mem') (x + 128) 4 (keys + 1) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 SRr rsegs W (@cfg_at fx2 rsegs KPU_CST regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs KPU_KEYS regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W memc mdc regs R x keys cid pos
  HJ H9 HR HRal Hinapp Hx1 Hxal Hkeys V138 Vxk Hown Hfr0 Hfr1 Hap K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (@ASAN_CEIL_range rc) as [[Hac1 Hac2] _]. unfold ASAN_CEIL in Hac1, Hac2.
assert (HSS : forall (G : facts),
  (bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 9) = R ->
   bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 33) = x ->
   bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 34) = keys ->
   facts_ok (Ereg regs (kpu_ex3 x keys)) G) ->
  st_ok rsegs (Ereg regs (kpu_ex3 x keys)) (mkSS KPU_KEYS sr_atoms [kpu_R3; kpu_RX] None G)
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KPU_KEYS) memc (seg_rom rsegs)))).
{ intros G HG.
  assert (B9' : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
  assert (A33 : ew (Ereg regs (kpu_ex3 x keys)) 33 = Z_to_bv 64 x)
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (A34 : ew (Ereg regs (kpu_ex3 x keys)) 34 = Z_to_bv 64 keys)
    by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  destruct Hinapp as (Hx0 & _).
  assert (B33' : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 33) = x)
    by (rewrite A33; apply unsigned_lit_small; lia).
  assert (B34' : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 34) = keys)
    by (rewrite A34; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold kpu_R3, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 33 0) x);
      [rewrite ku_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact V138].
    + unfold kpu_RX, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B33'.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs);
              replace (x + o) with (x + 128 + (o - 128)) by lia; apply Hap; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ x 128 4 (SOff 34 0) keys);
      [rewrite ku_denot0; exact A34 | cbn; lia | cbn; lia | change (N.to_nat 4) with 4%nat; exact Vxk].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
    unfold extent_disjoint, kpu_R3, kpu_RX.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9', B33'. right. lia.
  - exact (HG B9' B33' B34'). }
assert (A33g : ew (Ereg regs (kpu_ex3 x keys)) 33 = Z_to_bv 64 x)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A34g : ew (Ereg regs (kpu_ex3 x keys)) 34 = Z_to_bv 64 keys)
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B9g : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
destruct Hinapp as (Hx0 & Hhalf).
assert (B33g : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 33) = x)
  by (rewrite A33g; apply unsigned_lit_small; lia).
assert (B34g : bv_unsigned (ew (Ereg regs (kpu_ex3 x keys)) 34) = keys)
  by (rewrite A34g; apply unsigned_lit_small; lia).
(* The run is made at a CONCRETE entry state in each half of application memory: under a facts list that
   is a variable, the run's vm_compute does not reduce and one step of it grows to several GB. *)
destruct Hhalf as [Hlow | (Hhi1 & Hhi2)].
- unfold kLowShadowBeg in Hlow.
  assert (HS : st_ok rsegs (Ereg regs (kpu_ex3 x keys)) kpu_S3a
    (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KPU_KEYS) memc (seg_rom rsegs)))).
  { unfold kpu_S3a. apply HSS. intros B9' B33' B34'.
    split; [|split; [exact I | exact I]]. cbn [kpu_F3a f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9', B33', B34'.
    change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
  remember (Ereg regs (kpu_ex3 x keys)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (kpu_ex3 x keys)) E) by (subst E; apply env_agree_refl).
  assert (B33 : bv_unsigned (ew E 33) = x) by (subst E; exact B33g).
  assert (A34 : ew E 34 = Z_to_bv 64 keys) by (subst E; exact A34g).
  assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
  clear HE.
  unfold cfg_at. change (w64 KPU_KEYS) with (Z_to_bv 64 KPU_KEYS).
  aj_run_to_tok kpu_tbl_ok HS HJ SHOK RTBspan KPU_CST;
  [ lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat x);
    [ reflexivity | exact B33 | | apply awr_ok_nil ];
    cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    right; right; right; exists cid, pos; split; [exact Hown|]; left;
    unfold in_zr; cbn [fst snd]; lia |].
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kpu_ex3 x keys) (w_H W)
      [10; 11; 12]%bv HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  kpu_region HS 1%nat HRokX.
  assert (Vx : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (x + 128) 4 (keys + 1)).
  { change 4%nat with (N.to_nat 4).
    eapply (kpu_chunk _ _ 33%nat x);
    [exact HRokX | exact B33 | kpu_chin | exact A34 | lia | lia | cbn; lia | cbn; lia]. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { eapply (cb_kept_run (fun a => x + 128 <= a < x + 132) _ _ (w_H W) memc memc (ms_mem ms)).
    - intros a Ha Hz. reflexivity.
    - exact HFr.
    - intros a (rr & Hin & Hb).
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
      destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite B33 in Hb. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with KPU_CST by (vm_compute; reflexivity) end.
  eapply K; [ exact HJ | ku_io | exact RK | exact Vx | exact KE ].
- unfold kHighMemBeg in Hhi1.
  assert (HS : st_ok rsegs (Ereg regs (kpu_ex3 x keys)) kpu_S3b
    (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KPU_KEYS) memc (seg_rom rsegs)))).
  { unfold kpu_S3b. apply HSS. intros B9' B33' B34'.
    split; [|split; [exact I | exact I]]. cbn [kpu_F3b f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9', B33', B34'.
    change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
  remember (Ereg regs (kpu_ex3 x keys)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (kpu_ex3 x keys)) E) by (subst E; apply env_agree_refl).
  assert (B33 : bv_unsigned (ew E 33) = x) by (subst E; exact B33g).
  assert (A34 : ew E 34 = Z_to_bv 64 keys) by (subst E; exact A34g).
  assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
  clear HE.
  unfold cfg_at. change (w64 KPU_KEYS) with (Z_to_bv 64 KPU_KEYS).
  aj_run_to_tok kpu_tbl_ok HS HJ SHOK RTBspan KPU_CST;
  [ lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat x);
    [ reflexivity | exact B33 | | apply awr_ok_nil ];
    cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    right; right; right; exists cid, pos; split; [exact Hown|]; left;
    unfold in_zr; cbn [fst snd]; lia |].
  assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [10; 11; 12]%bv ->
    getr (ms_regs ms) rr = getr regs rr).
  { intros rr Hr0 Hn.
    exact (regs_kept_of_st_ok rsegs _ _ ms regs (kpu_ex3 x keys) (w_H W)
      [10; 11; 12]%bv HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
  kpu_region HS 1%nat HRokX.
  assert (Vx : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (x + 128) 4 (keys + 1)).
  { change 4%nat with (N.to_nat 4).
    eapply (kpu_chunk _ _ 33%nat x);
    [exact HRokX | exact B33 | kpu_chin | exact A34 | lia | lia | cbn; lia | cbn; lia]. }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (x + 128 <= a < x + 132) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
  { eapply (cb_kept_run (fun a => x + 128 <= a < x + 132) _ _ (w_H W) memc memc (ms_mem ms)).
    - intros a Ha Hz. reflexivity.
    - exact HFr.
    - intros a (rr & Hin & Hb).
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
      destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite B33 in Hb. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
    replace (ss_pc ss) with KPU_CST by (vm_compute; reflexivity) end.
  eapply K; [ exact HJ | ku_io | exact RK | exact Vx | exact KE ].
Qed.

(* ======================== block 2c: 0x832c0 .. BL 0x832e8 ======================== *)
Definition kpu_ex4 (big : Z) : list word := [Z_to_bv 64 SBr; w64 big].

Lemma kpu_blk2c : forall (fx2 : YK11.FPState) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc (W : world rsegs) memc mdc (regs : bvmap 5 word)
(R key big : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 23) = w64 key ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 32 = 0 ->
0x4000 <= key -> key + 13 <= 2 ^ 47 -> 0 <= big < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 big ->
(forall (regs' : bvmap 5 word) mem' md',
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
 same_io mdc md' ->
 (forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 10; 11; 12; 16; 17; 28; 29]%bv ->
  getr regs' rr = getr regs rr) ->
 getr regs' (Z_to_bv 5 10) = w64 (key + 13) -> getr regs' (Z_to_bv 5 11) = w64 0 ->
 getr regs' (Z_to_bv 5 12) = w64 (hqu_not (key + 13)) ->
 getr regs' (Z_to_bv 5 16) = w64 5 -> getr regs' (Z_to_bv 5 17) = w64 32 ->
 getr regs' (Z_to_bv 5 7) = w64 9 -> getr regs' (Z_to_bv 5 28) = w64 10 ->
 getr regs' (Z_to_bv 5 29) = w64 big ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) memc a) ->
 SRr rsegs W (@cfg_at fx2 rsegs HKU_BL regs' mem' md') Q) ->
SRr rsegs W (@cfg_at fx2 rsegs KPU_CST regs memc mdc) Q.
Proof.
intros fx2 Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R key big
  HJ H9 H23 HR HRal Hkey0 Hkey1 Hbig Vd0 K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (HS : st_ok rsegs (Ereg regs (kpu_ex4 big)) kpu_S4
  (restrict (w_H W) (@YK11.mkst fx2 regs (Z_to_bv 64 KPU_CST) memc (seg_rom rsegs)))).
{ assert (B9' : bv_unsigned (ew (Ereg regs (kpu_ex4 big)) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9; apply unsigned_lit_small; lia).
  assert (B23' : bv_unsigned (ew (Ereg regs (kpu_ex4 big)) 23) = key)
    by (rewrite (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl), H23; apply unsigned_lit_small; lia).
  assert (A33 : ew (Ereg regs (kpu_ex4 big)) 33 = Z_to_bv 64 big)
    by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite restrict_mkst_fx. unfold kpu_S4. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold kpu_R4, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9'.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ R 0xd0 8 (SOff 33 0) big);
    [rewrite ku_denot0; exact A33 | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Vd0].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kpu_F4 f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite B9', B23'.
    change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
remember (Ereg regs (kpu_ex4 big)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (kpu_ex4 big)) E) by (subst E; apply env_agree_refl).
assert (E23 : ew E 23 = Z_to_bv 64 key)
  by (subst E; rewrite (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl); exact H23).
assert (A33 : ew E 33 = Z_to_bv 64 big)
  by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (SHOK : sh_ok rsegs RTBx (@nil shent) E (mrestrict (w_H W) memc)) by constructor.
clear HE.
unfold cfg_at. change (w64 KPU_CST) with (Z_to_bv 64 KPU_CST).
(* 0x832c0 .. 0x832e4: the six constants, the pointer trap test (never: the key lies below 2 ^ 47, which
   the atom's range gives the engine) and the cursor's one's complement; BL 0x832e8 leaves the table *)
aj_run_tok kpu_tbl_ok HS HJ SHOK RTBspan;
[ lazymatch goal with |- awr_ok ?Ee ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ee rs' stk sp fp b0 bc lyy ow) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] |].
assert (R10' : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (key + 13)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 10) HS). ku_sv.
  apply (ku_soff E 23 key 13 E23); lia. }
assert (R11' : getr (ms_regs ms) (Z_to_bv 5 11) = w64 0).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 11) HS). ku_sv. reflexivity. }
assert (R12' : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (hqu_not (key + 13))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 12) HS). ku_sv.
  rewrite denot_lit_U, (U_not_off E 23 key 13 E23 ltac:(lia) ltac:(lia)).
  unfold w64. rewrite <- (Z_to_bv_mod64 (hqu_not (key + 13))).
  rewrite (hqu_not_mod (key + 13) ltac:(lia)). reflexivity. }
assert (R16' : getr (ms_regs ms) (Z_to_bv 5 16) = w64 5).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 16) HS). ku_sv. reflexivity. }
assert (R17' : getr (ms_regs ms) (Z_to_bv 5 17) = w64 32).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 17) HS). ku_sv. reflexivity. }
assert (R7' : getr (ms_regs ms) (Z_to_bv 5 7) = w64 9).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 7) HS). ku_sv. reflexivity. }
assert (R28' : getr (ms_regs ms) (Z_to_bv 5 28) = w64 10).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 28) HS). ku_sv. reflexivity. }
assert (R29' : getr (ms_regs ms) (Z_to_bv 5 29) = w64 big).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (Z_to_bv 5 29) HS). ku_sv.
  rewrite ku_denot0, A33. reflexivity. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 ->
  ~ In rr [7; 10; 11; 12; 16; 17; 28; 29]%bv -> getr (ms_regs ms) rr = getr regs rr).
{ intros rr Hr0 Hn.
  exact (regs_kept_of_st_ok rsegs _ _ ms regs (kpu_ex4 big) (w_H W)
    [7; 10; 11; 12; 16; 17; 28; 29]%bv HS HAE ltac:(vm_compute; reflexivity) rr Hr0 Hn). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha.
  exact (cb_kept_run (fun _ => False) E (ss_mem kpu_S4) (w_H W) memc memc (ms_mem ms)
    ltac:(intros b Hb Hz; reflexivity) HFr
    ltac:(intros b (rr & Hin & Hb);
          lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
          destruct Hin as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia)
    a Ha ltac:(intros HF0; exact HF0)). }
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?ss)] =>
  replace (ss_pc ss) with HKU_BL by (vm_compute; reflexivity) end.
eapply K;
[ exact HJ | ku_io | exact RK | exact R10' | exact R11' | exact R12' | exact R16' | exact R17'
| exact R7' | exact R28' | exact R29' | exact KE ].
Qed.

(* ======================== the piece ======================== *)
Theorem hku_P1 : hku_P1_stmt rsegs B MT.
Proof.
unfold hku_P1_stmt. intros cx POST r ev at0 m HS HLATCH HBL.
unfold hqu_from_KEY. intros fx2 ly2 S2 W2 regs2 mem2 md2 kk cs keys rf HKEY.
pose proof HKEY as (Hbase & Hat & Hfs9 & Hfs18 & Hfs19 & Hlive & Hat0m & HSm & Hkpos & Hnone & Hkey
  & Hxat & Hfold).
destruct (kpu_start cx r ev HS) as (Hwf & Hown & HFeq & HRal & HRsz & HeS & Hwin & Hev & P2 & P3 & P4).
pose proof (kpu_core cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 ev HS Hbase) as HC.
pose proof HC as HCc. apply hc_core_R in HCc. destruct HCc as (Hceil & H47 & Hsp).
pose proof (@alloc_ceiling_value rc) as [[Hac0 Hac2] _].
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hps : Layout.PP_SIZE = 19744) by (vm_compute; reflexivity).
assert (Hrq : req_size Layout.PP_SIZE = 19744) by (vm_compute; reflexivity).
assert (Hfb : fs_frame_bytes HQU_CID = 1024) by (vm_compute; reflexivity).
rewrite Hts in Hceil.
destruct (Model.ents_wf r Hwf) as [Hlen32 _].
pose proof Hbase as (Hcore & _).
pose proof Hcore as (HJ2 & Hregs234 & Hfrs2 & Hperm2 & Hio2 & Hmo2 & Hkeep2).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _).
rewrite HeS in HRsz.
(* the frame for locals *)
assert (HFl2 : frame_addr ly2 HQU_CID (x_pos rsegs cx) = e_F (x_e rsegs cx))
  by (rewrite HFeq; eapply hc_frame_addr_j; exact HJ2).
assert (Hfin : In (HQU_CID, x_pos rsegs cx) (frames S2))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 HQU_CID (x_pos rsegs cx) HAR2 Hfin)
  as (HF32 & HFapp & HFpres & _).
rewrite HFl2 in HF32, HFapp, HFpres.
assert (HFlow : 4096 <= frame_addr ly2 HQU_CID (x_pos rsegs cx) /\
  frame_addr ly2 HQU_CID (x_pos rsegs cx) + fs_frame_bytes HQU_CID <= alloc_ceiling)
  by (eapply hc_frm_low; [exact HJ2 | exact Hown]).
destruct HFlow as (HF4k & HFceil).
rewrite HFl2 in HF4k. rewrite HFl2, Hfb in HFceil.
(* the key's bytes *)
kpu_lib (@hku_keymem fx rc SK B MT) KM.
destruct (KM cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 m kk HS Hbase ltac:(lia) Hkey)
  as (Hklen & Hknul & Vk & Hkgarr & Hktail & Hppin & Hpp4k & Hppceil & Hppal & HRA & Happ). clear KM.
destruct (PairFacts.strncmp_prefix kk Hknul) as (d & Hmodel & Hdrange & Hdiff).
rewrite Hps in Hppceil.
set (K := hku_kaddr rsegs cx m) in *.
destruct (ku_kaddr_bounds cx m Hpp4k Hppceil Hac2 ltac:(clear - Hlen32 HSm; lia)) as [HK0 HK1].
assert (HKdef : K = e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m)
  by reflexivity.
(* the registers and cells of the KEY cut *)
unfold hsu_at_cx in Hat.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 9 (e_R (x_e rsegs cx)) Hat ltac:(kpu_lin)) as G9.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 23 K Hat ltac:(kpu_lin)) as G23.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 12 (Z.of_nat m + 1) Hat ltac:(kpu_lin)) as G12.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 5 (e_pp (x_e rsegs cx) + Layout.OFF_ENT) Hat ltac:(kpu_lin)) as G5.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 6 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4) Hat ltac:(kpu_lin)) as G6.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 7 (hqu_not (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) Hat
  ltac:(kpu_lin)) as G7.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 28 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) Hat ltac:(kpu_lin)) as G28.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 29 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) Hat ltac:(kpu_lin)) as G29.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 30 (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) Hat
  ltac:(kpu_lin)) as G30.
pose proof (ku_at_reg cx W2 mem2 regs2 _ 31 (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)) Hat
  ltac:(kpu_lin)) as G31.
(* the two real-frame cells block 2b reads *)
assert (Hatc : forall b off v, In (LCell b off, v) (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++
  hqu_L_loopr rsegs cx ++ hqu_L_t56 rsegs cx ++
  [(LReg 23, e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8 + Layout.ENT_SIZE * Z.of_nat m);
   (LReg 12, Z.of_nat m + 1); (LReg 18, Z.of_nat m + 1);
   (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1))]) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (hd_xv (x_e rsegs cx) b + off) 8 (v mod 2 ^ 64)).
{ intros b off v Hin. unfold hsu_at in Hat. rewrite Forall_forall in Hat. exact (Hat _ Hin). }
pose proof (Hatc XR 0xd0 HQU_RC_BIG ltac:(kpu_lin)) as C_d0.
pose proof (Hatc XR 0x138 (e_F (x_e rsegs cx) + HQU_XO) ltac:(kpu_lin)) as C_138.
cbn [hd_xv] in C_d0, C_138.
rewrite (Z.mod_small HQU_RC_BIG) in C_d0 by (unfold HQU_RC_BIG; lia).
rewrite (Z.mod_small (e_F (x_e rsegs cx) + HQU_XO)) in C_138 by (unfold HQU_XO; lia).
(* the shapes the blocks need *)
assert (Hppe : 0 <= e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8 < 2 ^ 64)
  by (unfold Layout.OFF_ENT; lia).
assert (Hnot7 : getr regs2 (Z_to_bv 5 7) = w64 ((hqu_not (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) mod 2 ^ 64)).
{ rewrite G7. unfold w64. rewrite Z_to_bv_mod64. reflexivity. }
assert (Hnot7b : 0 <= hqu_not (e_pp (x_e rsegs cx) + Layout.OFF_ENT) mod 2 ^ 64 < 2 ^ 64)
  by (apply Z.mod_pos_bound; lia).
(* ---------------- block 1: the eight saves and the `jal` ---------------- *)
apply (kpu_blk1 fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  regs2 (e_R (x_e rsegs cx)) K (Z.of_nat m)
  (e_pp (x_e rsegs cx) + Layout.OFF_ENT) (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4)
  ((hqu_not (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) mod 2 ^ 64)
  (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)
  (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)
  (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT))
  HJ2 G9 G23 G12 G5 G6 Hnot7 G28 G29 G30 G31
  ltac:(lia) ltac:(unfold KU_PHI in *; lia)
  ltac:(unfold Layout.OFF_ENT; lia) ltac:(unfold Layout.OFF_ENT; lia) Hnot7b
  ltac:(unfold Layout.OFF_ENT; lia) ltac:(unfold Layout.OFF_ENT; lia)
  ltac:(unfold Layout.OFF_PARAMS_STRUCT; lia)
  ltac:(unfold shadow_addr, SHADOW_OFF, Layout.OFF_PARAMS_STRUCT;
        pose proof (Z.div_mod (e_pp (x_e rsegs cx) + 0x4010) 8 ltac:(lia)); lia)
  ltac:(lia) HRal Hwin ltac:(unfold HQU_RSZ in *; lia) Hpres).
intros regsA memA mdA HJA HioA RKA A1 A10 A11 A12 Vd8 Ve0 Ve8 Vf0 Vf8 V100 V108 V110 KEA.
assert (RPA : aregs_preserved regs2 regsA) by (apply (kpu_keep_cs regs2 regsA [1; 10; 11; 12]%bv RKA kpu_cs1)).
assert (HbaseA : @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regsA memA mdA).
{ apply (hku_base3_kept B MT errno_low cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regsA memA mdA
    HS Hbase hqu_shX_len HJA ltac:(intros q Hq; apply RPA; unfold acallee_saved; lia) HioA).
  intros a Ha Hns Hnw. apply KEA; [exact Ha|]. intros Hin. apply Hnw. unfold hku_wr. left. lia. }
pose proof (kpu_core cx fx2 r hqu_shX ly2 S2 W2 regsA memA mdA ev HS HbaseA) as HCA.
kpu_lib (@hku_keymem fx rc SK B MT) KM2.
destruct (KM2 cx ev fx2 r hqu_shX ly2 S2 W2 regsA memA mdA m kk HS HbaseA ltac:(lia) Hkey)
  as (_ & _ & _ & HkgarrA & HktailA & HppinA & _). clear KM2.
assert (HlitA : hd_cstr rsegs (w_H W2) memA B_HKEY (hd_zbytes Headamp.HA_PREFIX)).
{ kpu_lib (@hku_cstr_now fx rc SK B MT) KC.
  apply (KC cx ev fx2 r hqu_shX ly2 S2 W2 regsA memA mdA B_HKEY (hd_zbytes Headamp.HA_PREFIX) HS HbaseA).
  replace (hd_zbytes Headamp.HA_PREFIX)
    with [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46] by (vm_compute; reflexivity).
  cbn [hi_strs headamp_himg_B]. unfold headamp_B_strs. cbn [In].
  right. right. left. reflexivity. }
assert (HroA : arodata_okP rsegs 0 0 B (aview rsegs (w_H W2) memA)).
{ kpu_lib (@hku_arodata_now fx rc SK B MT) KA.
  exact (KA cx ev fx2 r hqu_shX ly2 S2 W2 regsA memA mdA HS HbaseA). }
(* ---------------- the strncmp wrapper ---------------- *)
apply (@hkn_strncmp_key_call fx2 rc SK rsegs B img_segs_low STRNCMP 0 0 POST
  (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 memA mdA regsA (e_R (x_e rsegs cx)) K
  (e_pp (x_e rsegs cx)) Layout.PP_SIZE d kk
  HCA A1 A10 A11 A12 HppinA ltac:(rewrite HKdef; unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia)
  ltac:(rewrite Hrq, HKdef; unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia)
  HkgarrA Hknul HktailA HlitA HroA Hmodel).
intros regsB memB mdB HCB RPB HioB KEB Hv. destruct Hv as (vv & Hvv & Hviff).
assert (HJB : ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
  (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
  ly2 S2 W2 memB mdB (x_k rsegs cx)) by (destruct HCB as (HJB & _); exact HJB).
assert (RP2B : aregs_preserved regs2 regsB) by (eapply aregs_preserved_trans; [exact RPA | exact RPB]).
assert (GB9 : getr regsB (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite (RP2B 9 ltac:(unfold acallee_saved; lia)); exact G9).
assert (VB_108 : val_mem rsegs (mrestrict (w_H W2) memB) (e_R (x_e rsegs cx) + 0x108) 8
  (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT))).
{ apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memB); [|exact V108].
  intros kq Hkq. apply KEB; lia. }
assert (VB_110 : val_mem rsegs (mrestrict (w_H W2) memB) (e_R (x_e rsegs cx) + 0x110) 8
  (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)).
{ apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memB); [|exact V110].
  intros kq Hkq. apply KEB; lia. }
(* ---------------- block 2a: the reloads and the `bnez` ---------------- *)
apply (kpu_blk2a fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 memB mdB
  regsB (e_R (x_e rsegs cx)) (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)
  (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT))
  HJB GB9 ltac:(lia) HRal
  ltac:(unfold Layout.OFF_PARAMS_STRUCT; lia)
  ltac:(unfold shadow_addr, SHADOW_OFF, Layout.OFF_PARAMS_STRUCT;
        pose proof (Z.div_mod (e_pp (x_e rsegs cx) + 0x4010) 8 ltac:(lia)); lia)
  VB_108 VB_110).
- (* ================= no prefix: the pair loop's latch at m + 2 ================= *)
  intros regsC memC mdC HJC HioC RKC C30 C31 KEC Hne.
  assert (RPC : aregs_preserved regsB regsC) by (apply (kpu_keep_cs regsB regsC [30; 31]%bv RKC kpu_cs2)).
  assert (RP2C : aregs_preserved regs2 regsC) by (eapply aregs_preserved_trans; [exact RP2B | exact RPC]).
  assert (KE2C : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha H1 H2. rewrite (KEC a Ha). rewrite (KEB a Ha H1). apply KEA; assumption. }
  assert (KEAC : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1. rewrite (KEC a Ha). apply KEB; assumption. }
  assert (Hpf : Headamp.ha_prefix kk = false).
  { destruct (Bool.bool_dec (Headamp.ha_prefix kk) true) as [Hp|Hp].
    - exfalso. apply Hne. rewrite (Hvv : getr regsB (Z_to_bv 5 10) = vv).
      apply Hviff. apply Hdiff. exact Hp.
    - apply Bool.not_true_is_false. exact Hp. }
  assert (Hio2C : same_io md2 mdC).
  { eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB | exact HioC]. }
  assert (HbaseC : @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regsC memC mdC).
  { apply (hku_base3_kept B MT errno_low cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regsC memC mdC
      HS Hbase hqu_shX_len HJC ltac:(intros q Hq; apply RP2C; unfold acallee_saved; lia) Hio2C).
    intros a Ha Hns Hnw. apply KE2C;
    [ exact Ha | intros HX; apply Hns; lia | intros HX; apply Hnw; unfold hku_wr; left; lia ]. }
  assert (KEW : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. apply KE2C; lia. }
  pose proof Hat as HatS. apply Forall_app in HatS. destruct HatS as [HsegS HrestS].
  apply Forall_app in HrestS. destruct HrestS as [HloopcS _].
  assert (HsegC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_seg rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memC regs2 regsC (x_e rsegs cx)
      (hqu_L_seg rsegs cx) HsegS).
    intros f Hf. apply (hm_keeps_of rsegs (fun _ : Z => True)).
    - intros xq HX. exfalso. exact (HX I).
    - unfold hqu_L_seg, hqu_L_frame in Hf. cbn [In app] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst]; apply RP2C; unfold acallee_saved; lia|]). destruct Hf. }
  assert (HloopcC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_loopc rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memC regs2 regsC (x_e rsegs cx)
      (hqu_L_loopc rsegs cx) HloopcS).
    intros f Hf.
    apply (hm_keeps_of rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118))); [exact KEW|].
    unfold hqu_L_loopc in Hf. cbv zeta in Hf. cbn [In] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hd_xv]; intros i Hi; lia|]). destruct Hf. }
  assert (Ht56C : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_t56 rsegs cx)).
  { unfold hqu_L_t56. cbv zeta.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd hd_at].
    - exact C30.
    - exact C31. }
  assert (BodyC : Forall (fun f => hd_at rsegs (w_H W2) memC regsC (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_body rsegs cx (Z.of_nat m + 2))).
  { unfold hqu_L_body. cbv zeta.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_nil]]]]]]]]; cbn [fst snd hd_at hd_xv].
    - rewrite (Z.mod_small (Z.of_nat m + 2)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vd8].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Ve0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Ve8].
    - apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vf0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) by (unfold Layout.OFF_ENT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact Vf8].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4)) by (unfold Layout.OFF_ENT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact V100].
    - rewrite (Z.mod_small (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)))
        by (unfold shadow_addr, SHADOW_OFF, Layout.OFF_PARAMS_STRUCT;
            pose proof (Z.div_mod (e_pp (x_e rsegs cx) + 0x4010) 8 ltac:(lia)); lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact V108].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT))
        by (unfold Layout.OFF_PARAMS_STRUCT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memC);
      [intros kq Hkq; apply KEAC; lia | exact V110]. }
  apply (HLATCH fx2 ly2 S2 W2 regsC memC mdC cs keys rf).
  pose proof Hxat as (Hxg & Hcl & Hccap & Hckeys & Hkeysb & Hrfv).
  split; [exact HbaseC|].
  split.
  { unfold hsu_at_cx, hsu_at. rewrite !Forall_app.
    split; [exact HsegC|]. split; [exact HloopcC|]. split; [exact Ht56C|].
    replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia. exact BodyC. }
  split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hfs19|]. split; [exact Hlive|].
  split; [unfold hqu_nent; lia|]. split; [lia|].
  split.
  { split; [|split; [exact Hcl | split; [exact Hccap | split; [exact Hckeys |
      split; [exact Hkeysb | exact Hrfv]]]]].
    apply (hm_bytes_zbytes rsegs).
    apply (hm_bytes_kept_wr rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118))
      (w_H W2) mem2 (w_H W2) memC (e_F (x_e rsegs cx) + HQU_XO) (hqu_x_open cs keys rf)).
    - apply (hm_bytes_zbytes rsegs). exact Hxg.
    - exact KEW.
    - intros xq Hxq. rewrite (hqu_x_open_len cs keys rf Hcl) in Hxq. unfold HQU_XO in *. lia. }
  exact (hku_fold_skip cx r at0 m kk cs keys rf Hat0m HSm Hnone Hkey Hfold Hpf).
- (* ================= the prefix: x->keys++ and the blanks loop ================= *)
  intros regsC memC mdC HJC HioC RKC C30 C31 KEC Heq.
  assert (RPC : aregs_preserved regsB regsC) by (apply (kpu_keep_cs regsB regsC [30; 31]%bv RKC kpu_cs2)).
  assert (RP2C : aregs_preserved regs2 regsC) by (eapply aregs_preserved_trans; [exact RP2B | exact RPC]).
  assert (KE2C : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha H1 H2. rewrite (KEC a Ha). rewrite (KEB a Ha H1). apply KEA; assumption. }
  assert (KEAC : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1. rewrite (KEC a Ha). apply KEB; assumption. }
  assert (Hpt : Headamp.ha_prefix kk = true).
  { apply Hdiff. apply Hviff. rewrite <- Hvv. exact Heq. }
  assert (Hpair : hqu_pair_inv rsegs cx r m kk (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf)
    by exact (hku_pair_of_fold cx r at0 m kk cs keys rf Hat0m HSm Hnone Hkey Hfold Hpt).
  assert (Hkb : keys + 1 <= 32)
    by exact (kpu_keys_bound cx r m kk (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf Hwf Hlive Hpair).
  assert (Hio2C : same_io md2 mdC).
  { eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB | exact HioC]. }
  (* the frame object x *)
  assert (HARC : AR rsegs B ly2 S2 W2 memC mdC) by (destruct HJC as (HARC & _); exact HARC).
  destruct (al_frames rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 memC mdC HQU_CID (x_pos rsegs cx) HARC Hfin)
    as (_ & _ & HFpresC & _).
  rewrite HFl2, Hfb in HFpresC.
  assert (KEW : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118)) ->
    aview rsegs (w_H W2) memC a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. apply KE2C; lia. }
  pose proof Hxat as (Hxg & Hcl & Hccap & Hckeys & Hkeysb & Hrfv).
  assert (HxgC : garr8 rsegs (mrestrict (w_H W2) memC) (e_F (x_e rsegs cx) + HQU_XO)
    (hd_zbytes (hqu_x_open cs keys rf))).
  { apply (hm_bytes_zbytes rsegs).
    apply (hm_bytes_kept_wr rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118))
      (w_H W2) mem2 (w_H W2) memC (e_F (x_e rsegs cx) + HQU_XO) (hqu_x_open cs keys rf)).
    - apply (hm_bytes_zbytes rsegs). exact Hxg.
    - exact KEW.
    - intros xq Hxq. rewrite (hqu_x_open_len cs keys rf Hcl) in Hxq. unfold HQU_XO in *. lia. }
  assert (GC9 : getr regsC (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
    by (rewrite (RP2C 9 ltac:(unfold acallee_saved; lia)); exact G9).
  assert (GC23 : getr regsC (Z_to_bv 5 23) = w64 K)
    by (rewrite (RP2C 23 ltac:(unfold acallee_saved; lia)); exact G23).
  assert (VC_138 : val_mem rsegs (mrestrict (w_H W2) memC) (e_R (x_e rsegs cx) + 0x138) 8
    (e_F (x_e rsegs cx) + HQU_XO)).
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 memC); [|exact C_138].
    intros kq Hkq. apply KE2C; lia. }
  assert (VC_d0 : val_mem rsegs (mrestrict (w_H W2) memC) (e_R (x_e rsegs cx) + 0xd0) 8 HQU_RC_BIG).
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 memC); [|exact C_d0].
    intros kq Hkq. apply KE2C; lia. }
  assert (VC_xk : val_mem rsegs (mrestrict (w_H W2) memC) (e_F (x_e rsegs cx) + HQU_XO + 128) 4 keys)
    by (apply (kpu_x_keys_val cs keys rf (w_H W2) memC (e_F (x_e rsegs cx) + HQU_XO) Hcl ltac:(lia) HxgC)).
  apply (kpu_blk2b fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
    (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 memC mdC
    regsC (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx) + HQU_XO) keys
    HQU_CID (x_pos rsegs cx)
    HJC GC9 ltac:(lia) HRal
    ltac:(apply (in_app_sub (e_F (x_e rsegs cx)) (fs_frame_bytes HQU_CID));
          [exact HFapp | unfold HQU_XO; lia | lia | rewrite Hfb; unfold HQU_XO; lia])
    ltac:(unfold HQU_XO; lia)
    ltac:(rewrite Z.add_mod by lia; rewrite HF32; unfold HQU_XO; vm_compute; reflexivity)
    ltac:(lia)
    VC_138 VC_xk Hown
    ltac:(rewrite HFl2; unfold HQU_XO; lia) ltac:(rewrite HFl2, Hfb; unfold HQU_XO; lia)
    ltac:(intros o Ho; apply (HFpresC (e_F (x_e rsegs cx) + HQU_XO + 128 + o)); unfold HQU_XO; lia)).
  intros regsD1 memD1 mdD1 HJD1 HioD1 RKD1 Vxk1' KED1.
  assert (GD9 : getr regsD1 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))).
  { rewrite (ku_keep _ _ _ [9] RKD1 ltac:(vm_compute; reflexivity) 9 (or_introl eq_refl)). exact GC9. }
  assert (GD23 : getr regsD1 (Z_to_bv 5 23) = w64 K).
  { rewrite (ku_keep _ _ _ [23] RKD1 ltac:(vm_compute; reflexivity) 23 (or_introl eq_refl)). exact GC23. }
  assert (VD_d0 : val_mem rsegs (mrestrict (w_H W2) memD1) (e_R (x_e rsegs cx) + 0xd0) 8 HQU_RC_BIG).
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) memC memD1); [|exact VC_d0].
    intros kq Hkq. apply KED1; unfold HQU_XO in *; lia. }
  apply (kpu_blk2c fx2 POST (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
    (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 memD1 mdD1
    regsD1 (e_R (x_e rsegs cx)) K HQU_RC_BIG
    HJD1 GD9 GD23 ltac:(lia) HRal ltac:(lia) ltac:(unfold KU_PHI in *; lia) ltac:(unfold HQU_RC_BIG; lia)
    VD_d0).
  intros regsD memD mdD HJD HioD2 RKD2 D10 D11 D12 D16 D17 D7 D28 D29 KED2.
  assert (HioD : same_io mdC mdD) by (eapply same_io_trans; [exact HioD1 | exact HioD2]).
  assert (RKD : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [7; 10; 11; 12; 16; 17; 28; 29]%bv ->
    getr regsD rr = getr regsC rr).
  { intros rr Hr0 Hn. rewrite (RKD2 rr Hr0 Hn). apply RKD1; [exact Hr0|].
    intros Hin. apply Hn. cbn [In] in Hin |- *. tauto. }
  assert (KED : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_F (x_e rsegs cx) + HQU_XO + 128 <= a < e_F (x_e rsegs cx) + HQU_XO + 132) ->
    aview rsegs (w_H W2) memD a = aview rsegs (w_H W2) memC a).
  { intros a Ha Hn. rewrite (KED2 a Ha). apply KED1; [exact Ha | lia]. }
  assert (Vxk1 : val_mem rsegs (mrestrict (w_H W2) memD) (e_F (x_e rsegs cx) + HQU_XO + 128) 4 (keys + 1)).
  { apply (val_mem_kept rsegs (w_H W2) (w_H W2) memD1 memD); [|exact Vxk1'].
    intros kq Hkq. apply KED2. unfold HQU_XO in *; lia. }
  assert (RPD : aregs_preserved regsC regsD)
    by (apply (kpu_keep_cs regsC regsD [7; 10; 11; 12; 16; 17; 28; 29]%bv RKD kpu_cs3)).
  assert (RP2D : aregs_preserved regs2 regsD) by (eapply aregs_preserved_trans; [exact RP2C | exact RPD]).
  assert (Hio2D : same_io md2 mdD) by (eapply same_io_trans; [exact Hio2C | exact HioD]).
  assert (KEWD : forall a : Z,
    ~ ((a < 0) \/ (2 ^ 64 <= a) \/
       (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
       (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118) \/
       (e_F (x_e rsegs cx) + HQU_XO + 128 <= a < e_F (x_e rsegs cx) + HQU_XO + 132)) ->
    aview rsegs (w_H W2) memD a = aview rsegs (w_H W2) mem2 a).
  { intros a Hn. rewrite (KED a ltac:(lia) ltac:(lia)). apply KE2C; lia. }
  assert (HbaseD : @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regsD memD mdD).
  { apply (hku_base3_kept B MT errno_low cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regsD memD mdD
      HS Hbase hqu_shX_len HJD ltac:(intros q Hq; apply RP2D; unfold acallee_saved; lia) Hio2D).
    intros a Ha Hns Hnw. apply KEWD. intros HX.
    destruct HX as [HX|[HX|[HX|[HX|HX]]]]; [lia | lia | apply Hns; lia
      | apply Hnw; unfold hku_wr; left; lia | apply Hnw; unfold hku_wr; right; unfold HQU_XO in *; lia]. }
  (* the cut's lists at memD *)
  pose proof Hat as HatS. apply Forall_app in HatS. destruct HatS as [HsegS HrestS].
  apply Forall_app in HrestS. destruct HrestS as [HloopcS _].
  assert (HsegD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_seg rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memD regs2 regsD (x_e rsegs cx)
      (hqu_L_seg rsegs cx) HsegS).
    intros f Hf. apply (hm_keeps_of rsegs (fun _ : Z => True)).
    - intros xq HX. exfalso. exact (HX I).
    - unfold hqu_L_seg, hqu_L_frame in Hf. cbn [In app] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst]; apply RP2D; unfold acallee_saved; lia|]). destruct Hf. }
  assert (HloopcD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_loopc rsegs cx)).
  { apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memD regs2 regsD (x_e rsegs cx)
      (hqu_L_loopc rsegs cx) HloopcS).
    intros f Hf.
    apply (hm_keeps_of rsegs (fun a : Z => (a < 0) \/ (2 ^ 64 <= a) \/
      (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) \/
      (e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x118) \/
      (e_F (x_e rsegs cx) + HQU_XO + 128 <= a < e_F (x_e rsegs cx) + HQU_XO + 132))); [exact KEWD|].
    unfold hqu_L_loopc in Hf. cbv zeta in Hf. cbn [In] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hd_xv]; intros i Hi; unfold HQU_XO in *; lia|]). destruct Hf. }
  assert (Ht56D : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_t56 rsegs cx)).
  { unfold hqu_L_t56. cbv zeta.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd hd_at].
    - rewrite (ku_keep _ _ _ [30] RKD ltac:(vm_compute; reflexivity) 30 (or_introl eq_refl)). exact C30.
    - rewrite (ku_keep _ _ _ [31] RKD ltac:(vm_compute; reflexivity) 31 (or_introl eq_refl)). exact C31. }
  assert (KEAD : forall a, 0 <= a < 2 ^ 64 ->
    ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
    ~ (e_F (x_e rsegs cx) + HQU_XO + 128 <= a < e_F (x_e rsegs cx) + HQU_XO + 132) ->
    aview rsegs (w_H W2) memD a = aview rsegs (w_H W2) memA a).
  { intros a Ha H1 H2. rewrite (KED a Ha H2). apply KEAC; assumption. }
  assert (BodyD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_body rsegs cx (Z.of_nat m + 2))).
  { unfold hqu_L_body. cbv zeta.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_nil]]]]]]]]; cbn [fst snd hd_at hd_xv].
    - rewrite (Z.mod_small (Z.of_nat m + 2)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact Vd8].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact Ve0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8)) by lia.
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact Ve8].
    - apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact Vf0].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) by (unfold Layout.OFF_ENT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact Vf8].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4)) by (unfold Layout.OFF_ENT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact V100].
    - rewrite (Z.mod_small (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT)))
        by (unfold shadow_addr, SHADOW_OFF, Layout.OFF_PARAMS_STRUCT;
            pose proof (Z.div_mod (e_pp (x_e rsegs cx) + 0x4010) 8 ltac:(lia)); lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact V108].
    - rewrite (Z.mod_small (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT))
        by (unfold Layout.OFF_PARAMS_STRUCT; lia).
      apply (val_mem_kept rsegs (w_H W2) (w_H W2) memA memD);
      [intros kq Hkq; apply KEAD; unfold HQU_XO in *; lia | exact V110]. }
  assert (ExtraD : Forall (fun f => hd_at rsegs (w_H W2) memD regsD (x_e rsegs cx) (fst f) (snd f))
    [(LReg 18, Z.of_nat m + 1); (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1))]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd hd_at].
    - rewrite (RP2D 18 ltac:(unfold acallee_saved; lia)).
      exact (ku_at_reg cx W2 mem2 regs2 _ 18 (Z.of_nat m + 1) Hat ltac:(kpu_lin)).
    - rewrite (RP2D 24 ltac:(unfold acallee_saved; lia)).
      exact (ku_at_reg cx W2 mem2 regs2 _ 24 (Layout.ENT_SIZE * (Z.of_nat m + 1)) Hat ltac:(kpu_lin)). }
  assert (HxatD : hqu_x_at rsegs cx W2 memD cs (keys + 1) rf).
  { split; [|split; [exact Hcl | split; [lia | split; [lia | split; [lia | exact Hrfv]]]]].
    apply (kpu_x_store cs keys rf (w_H W2) mem2 (w_H W2) memD (e_F (x_e rsegs cx) + HQU_XO) Hcl Hkeysb Hxg).
    - exact Vxk1.
    - intros y Hy Hny. apply KEWD. unfold HQU_XO in *. lia. }
  apply (HBL fx2 ly2 S2 W2 regsD memD mdD kk cs keys rf).
  split.
  { split; [exact HbaseD|].
    split.
    { unfold hsu_at_cx, hsu_at, hku_L. rewrite !Forall_app.
      split; [exact HsegD|]. split; [exact HloopcD|]. split; [exact Ht56D|].
      split; [exact BodyD | exact ExtraD]. }
    split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hfs19|]. split; [exact Hlive|].
    split; [exact Hat0m|]. split; [exact Hkey|]. split; [exact Hpair|].
    split; [exact HxatD | exact Hckeys]. }
  split.
  { unfold hsu_at_cx, hsu_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]]]]]]; cbn [fst snd hd_at].
    - rewrite (RP2D 23 ltac:(unfold acallee_saved; lia)). exact G23.
    - exact D10.
    - cbn [Z.of_nat]. exact D11.
    - exact D12.
    - exact D16.
    - exact D17.
    - exact D7.
    - exact D28.
    - exact D29. }
  lia.
Qed.

Print Assumptions hku_P1.

End d.
End b.
