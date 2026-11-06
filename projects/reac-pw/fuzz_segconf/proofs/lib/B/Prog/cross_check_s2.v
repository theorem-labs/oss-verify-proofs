(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_info (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8bb70, 122 instructions), after lib/A/Prog/answer_code.v (a working branch
   2ba4488ce71: a side-stack frame taken by __asan_stack_malloc_N, its header and shadow, the snprintf call and the
   release by the flag store) and lib/A/Prog/sup_instance_info.v (a working branch 0de7ca03d26: the
   recorder's chain through record, arg_s, rec_shape_of and answer and the post), re-derived on B's code, against
   a Theorem Labs lane's statement (a working branch f490061c104). The snprintf step through the shared contract and the change of FP
   state after it follow a working branch 07b554c4785 (lib/B/Prog/answer_code.v:943-1070), the release
   by the flag store answer_code.v's end, the post's block algebra a working branch b5e1a22725a
   (descriptors_panel_get_aux.v dpgb_post_of), the calls after record a working branch c79a9f2daf7. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_info.v, with its module paths and module names changed; 369 of its 434 lines of code are new or changed and 1757 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/cross_check_s1.v, with its module paths, module names and numbers changed; 1498 of its 1574 lines of code are new or changed and 358 lines of the source are left out. *)
(* Segment 2 of the walk of cross_check on reac-pw/fuzz_segconf's ASan+UBSan IMAGE B
   (fuzz_segconf.asan-ubsan, pin c3796c0b38f3; cross_check 0x897cc): ONE PASS of the segment loop, from the loop
   head 0x89874 (CC_LOOP = AF_cross_check + 0xa8) to the loop head of pass i + 1 or to the epilogue 0x899fc
   (CC_EPI). It is the only segment that calls refuse, and the only one that walks an inline store.

   The instructions (cross_check.fuzz_segconf.asan-ubsan.s lines 44-141):
     0x89874 li a0,33 ; 0x89878 beq s10,a0,89a38     UBSan TRAP 3 (i = 33), excluded by i <= 31
     0x8987c bltu s11,s9,89a38                       UBSan TRAP 4 (~c < 356 i), excluded by c + 16616 <= 2^63
     0x89880 add s4,s0,s9                            s4 = c + 356 i   (the alias below)
     0x89884 addi s5,s4,20 .. 0x89894                check 2 (load4 of s->role_set)
     0x89898 lw a0,20(s4) ; 0x8989c beqz a0,898c0    role_set
     0x898a0 .. 0x898b0                              check 3 (load4 of s->role)
     0x898b4 lw a0,16(s4) ; 0x898b8 addi a0,a0,-4 ; 0x898bc seqz a0,a0    a0 = is_box
     0x898c0 addi s6,s4,60 .. 0x898d0                check 4 (load4 of s->model_set)
     0x898d4 lw a1,60(s4) ; 0x898d8 seqz a1,a1       a1 = not model_set
     0x898dc or a2,a1,a0 ; 0x898e0 andi a2,a2,1 ; 0x898e4 beqz a2,8992c  -> the MODEL arm
     0x898e8 and a0,a1,a0 ; 0x898ec beqz a0,89968                        -> the latch (neither arm)
     0x898f0 .. 0x89928  the BOX arm: refuse(c, 0, F_xbox, s->name) at 0x89900, then
                         check 5 + `sw zero,20(s4)` (role_set = 0) and check 6 + `sw zero,16(s4)` (role = AUTO)
     0x8992c .. 0x89964  the MODEL arm: refuse(c, 0, F_xmodel, s->name, s->model) at 0x89944, then
                         check 7 + `sw zero,60(s4)` (model_set = 0) and check 8 + `sb zero,0(s5)` (model[0] = 0)
     0x89968 .. 0x89980  the latch: check 9, `lw a0,0(s1)` (n re-loaded), `addi s10,s10,1`,
                         `addi s9,s9,356`, `blt s10,a0,89874` (back to the head) else `j 899fc`

   WHAT THE SYMBOLIC STATE AT THE HEAD LOOKS LIKE (ss_cc2 below), and why each piece is there:
   - the registers are the atoms 0..31 of sr_atoms, so atom r is the cut's value of register r: atom 8 = c,
     atom 9 = c + RC_N, atom 18 = the shadow base, atom 19 = the shadow byte address of &c->n, atom 25 = 356 i,
     atom 26 = i, atom 27 = ~c, atom 2 = sp0 - 128. INV_LOOP (cross_check_d.v) is exactly that list.
   - atoms 32..36 are the values the pass reads out of the block: 32 = c + 356 i (the entry's address),
     33 = s->role, 34 = s->role_set as 0/1, 35 = s->model_set as 0/1, 36 = c->n. cross_check_f.v's
     sa_rconf_fields and sa_rconf_n give each of them from INV_LOOP's sa_rconf.
   - TWO ALIASES. (a) `add s4,s0,s9` builds SAlu ALU_ADD (SOff 8 0) (SOff 25 0), which is not a base+offset form,
     so no region could be found on it; the alias sends it to SOff 32 0, the atom for c + 356 i. YP0e.v's
     s_alu2 applies aliased2 to the result of every two-register ALU op, so the run rewrites it by itself.
     (b) the shadow byte address of &c->n is carried in s3 from the ENTRY segment, so at the latch's
     `lb a0,0(s3)` the address is the opaque atom SOff 19 0 and YCbn.v's match_x would not see a shadow load;
     the alias sends SOff 19 0 to (SOff 9 0 >> 3) + SOff 18 0, which match_x_core does match. Both aliases are
     discharged in cc2_seed by alias_ok, from INV_LOOP's register equations.
   - the three spill slots [sp, sp + 24) are a READ-ONLY region on atom 2 holding 3, lit F_xbox and lit F_xmodel
     (INV_LOOP's three rdword conjuncts); the pass reads two of them for the refuse calls. The 13 saved slots
     [sp + 24, sp + 128) are NOT a region: the pass writes no stack byte and refuse's window is below sp, so
     cross_check_r.v's cc_own_frame_kept carries INV_LOOP's fi_saved across the call untouched.
   - the fields of seg[i] are a READ-ONLY region on atom 32 over [16, 64) (role, role_set, model_set as chunks),
     and c->n is a read-only region on atom 9. The head runs write no byte at all (every store of the pass
     comes after a refuse call, below), so the memory at every stop of the head is the cut's (cc2_frame_ro).
     (CHANGED from this file's first design, which gave the seg[i] region the write window [16, 64): the stores
     are walked from a fresh seed over refuse's post state, so the window is never used at the head and only
     added an awr_ok and an app-shadow entry to prove.)

   HOW THE PASS IS WALKED (the form of plugin-hostd/fuzz_command's chain_words_s4.v at origin/ossv/recipes
   501c0d516c69: a token run to the call, PaFx.cl_callSF + PaFx.srr_after_callF, the rest a lemma of a closed
   section taken at the FP state the callee returned):
   - cc_s2 seeds ss_cc2 (cc2_seed) and token-runs the tests. The executor decides the two trap branches itself:
     0x89878 `beq s10,33` from the atom fact (26, mkAF 0 31 0) (ranges [0, 31] and [33, 33] are apart), and
     0x8987c `bltu s11,s9` from (27, mkAF 2^63 (2^64-1) 0) against (25, mkAF 0 11036 2) (ranges_ltu). The three
     undecided branches 0x8989c, 0x898e4, 0x898ec are split with psrr_branch_tok and each side is tied to the
     flags of seg[i] by cc2_br1 / cc2_br2A / cc2_br2B / cc2_br3A / cc2_br3B (cc2_seqz is the is_box bit);
     the side the flags exclude ends in a contradiction. The six leaves: MODEL arm (role_set = 0 or 1),
     BOX arm, latch (role_set = 0 or 1).
   - a leaf at `jal refuse` goes to cc2_call_model / cc2_call_box: refuse_site_ok_89944 / _89900 give
     refuse_pre, cc_call_room / cc_call_chain / cc_refuse_FP_sub the side conditions of cl_callSF, and
     cc2_after_call rebuilds the cut facts at the return (cc_own_frame_kept, cc_un_after, refuse's post).
   - the arm after the return is cc2_box_after / cc2_model_after, each from its own seed (ss_cc2b at 0x89904:
     s4 = atom 20, s5 = atom 21, the alias of s7; ss_cc2m at 0x89948: s4, s5, s6 = atoms 20, 21, 22, the alias
     of s8), whose regions are exactly the bytes the arm zeroes; sa_rconf_drop_role / sa_rconf_drop_model and
     r_cross_seg_box / r_cross_seg_model give the record cc_at v (i + 1).
   - the latch is cc2_latch, from its own seed ss_cc2l (c->n as atom 32, the alias of s3); `blt s10,a0` is split
     and cc2_lt_atoms ties it to i + 1 < n: taken to INV_LOOP (i + 1), not taken (i + 1 = n, cc_fold_all) to
     INV_EPI. The path that calls nothing reaches it with the record unchanged (cc2_keep_inv,
     r_cross_seg_keep).

   THE EIGHT INLINE CHECKS of this segment are left to the token runs as OBLIGATIONS and discharged with
   YCbq.v's obl_of_range over cross_check_r.v's cc_block_addr (every address is a field of the live block):
   check 2 (s4 + 20, 4 bytes), 3 (s4 + 16, 4), 4 (s4 + 60, 4) in the head runs; 5 (s5 = s4 + 20, 4) and
   6 (s4 + 16, 4) in cc2_box_after; 7 (s6 = s4 + 60, 4) and 8 (s5 = s4 + 36, 1) in cc2_model_after; 9 in
   cc2_latch, whose slow path 0x899a4 begins with `ld a1,0(sp)` and no andi, so the executor asks the whole
   8-byte granule of &c->n. The arms' seeds carry the app-shadow entries app_entries makes for their write
   regions (shent_app_of_block: the block is application memory).

   cc_s2's hypotheses are cc_s3's list, unchanged.

   ADAPTED from the image-A G3 walk owner's image-A cross_check lane (a working branch), the released engine models
   being plugin-hostd/fuzz_command's numberA.v / numberE.v / check_reply_s1.v / check_reply_s2.v /
   chain_words_s4.v at origin/ossv/recipes 501c0d516c69. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep SegSyms
  SegList SegPa PaJournal SegPaLib PaLibG PaLibF PaSB PaDenot PaCall PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegObj SegPgBase SegABase PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c cross_check_f
  cross_check_d cross_check_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* the atoms above the registers *)
Notation N_SI := 32%nat (only parsing).    (* c + 356 i, the address of seg[i] *)
Notation N_ROLE := 33%nat (only parsing).  (* s->role *)
Notation N_RSET := 34%nat (only parsing).  (* s->role_set, as the 0/1 the field holds *)
Notation N_MSET := 35%nat (only parsing).  (* s->model_set, as the 0/1 the field holds *)
Notation N_N := 36%nat (only parsing).     (* c->n *)

(* the shadow byte address of &c->n, as the ENTRY segment built it: (s1 >> 3) + the shadow base *)
Definition cc2_shn : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 18 0).
(* the two aliases (head comment) *)
Definition cc2_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 8 0) (SOff 25 0), SOff N_SI 0); (SOff 19 0, cc2_shn) ].
(* the three spill slots, read-only *)
Definition cc2_spill : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SLit 3));
     YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 73) 0));
     YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 74) 0))].
(* the fields of seg[i] the pass reads and writes *)
Definition cc2_seg : YP09.region :=
  YP09.mkRegion (Some N_SI) 16 64 16 16
    [YP09.mkChunk 16 (CVal 4 (SOff N_ROLE 0));
     YP09.mkChunk 20 (CVal 4 (SOff N_RSET 0));
     YP09.mkChunk 60 (CVal 4 (SOff N_MSET 0))].
(* c->n, read-only (the latch re-loads it) *)
Definition cc2_n : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff N_N 0))].
Definition cc2_regions : smem := [cc2_spill; cc2_seg; cc2_n].
Definition cc2_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
    (8%nat, HPTR 4);
    (9%nat, mkAF 4096 140737479966720 3);
    (18%nat, mkAF SB SB 0);
    (25%nat, mkAF 0 11036 2);
    (26%nat, mkAF 0 31 0);
    (27%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0);
    (N_SI, HPTR 2);
    (N_ROLE, mkAF 0 (2 ^ 31 - 1) 0);
    (N_RSET, mkAF 0 1 0);
    (N_MSET, mkAF 0 1 0);
    (N_N, mkAF 0 32 0) ].
Definition ss_cc2 : sstate := mkSS CC_LOOP sr_atoms cc2_regions None (mkFacts cc2_atoms [] cc2_alias).
(* atoms 32..36 of the seeded environment *)
Definition cc2_extra (c i : Z) (s : rseg) (n : Z) : list word :=
  map (Z_to_bv 64)
    [c + 356 * i; rs_role s; (if rs_role_set s then 1 else 0); (if rs_model_set s then 1 else 0); n].

(* the latch 0x89968 (check 9, the reload of n, i + 1, 356 (i + 1), `blt s10,a0`): its own seed, the registers
   of the cut as atoms 0..31, atom 32 = c->n, the one read-only region c->n on atom 9, and the alias of s3 *)
Definition CC_LATCH : Z := AF_cross_check + 0x19c.
Definition cc2l_n : YP09.region := YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition ss_cc2l : sstate := mkSS CC_LATCH sr_atoms [cc2l_n] None
  (mkFacts [(9%nat, mkAF 4096 140737479966720 3); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 32 0)] []
     [(SOff 19 0, cc2_shn)]).
(* the shadow byte address of the address in atom n, as `srli; add s2` builds it *)
Definition cc2_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 18 0).
(* the return point of the BOX arm's call 0x89904: s4 = atom 20 = &seg[i], s5 = atom 21 = s4 + 20, s7 = atom 23
   = the shadow byte address of s5 (the alias); the one region is the 8 bytes role, role_set the arm zeroes *)
Definition ss_cc2b : sstate := mkSS CC_RET1 sr_atoms [YP09.mkRegion (Some 20%nat) 16 24 16 24 []] None
  (mkFacts [(18%nat, mkAF SB SB 0); (20%nat, HPTR 2); (21%nat, HPTR 2)] [] [(SOff 23 0, cc2_shx 21)]).
(* the return point of the MODEL arm's call 0x89948: s4 = atom 20, s5 = atom 21 = s4 + 36 = &model[0],
   s6 = atom 22 = s4 + 60, s8 = atom 24 = the shadow byte address of s6 (the alias); the two regions are
   model_set (on s4) and model[0] (on s5), the bytes the arm zeroes *)
Definition ss_cc2m : sstate := mkSS CC_RET2 sr_atoms
  [YP09.mkRegion (Some 20%nat) 60 64 60 64 []; YP09.mkRegion (Some 21%nat) 0 1 0 1 []] None
  (mkFacts [(18%nat, mkAF SB SB 0); (20%nat, HPTR 2); (21%nat, HPTR 2); (22%nat, HPTR 2)] []
     [(SOff 24 0, cc2_shx 22)]).

(* `blt s10,a0` at the latch, with s10 = i + 1 (atom a plus 1) and a0 = n (atom b) *)
Lemma cc2_lt_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> x + 1 < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff a 1)) (sv_denot E (SOff b 0)) = (x + 1 <? y).
Proof.
intros E a b x y Ha Hb Hx Hx1 Hy. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff a 1))) with (Sg E (SOff a 1)).
change (bv_signed (sv_denot E (SOff b 0))) with (Sg E (SOff b 0)).
rewrite !S_SOff, Ha, Hb, !unsigned_lit_small by lia.
rewrite !swrap64_id by (unfold half64; lia). rewrite Z.add_0_r. reflexivity.
Qed.
(* a run whose regions are all read-only writes no byte *)
Lemma cc2_frame_ro : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. apply functional_extensionality. intros x. apply HF.
intros (r & Hr & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hr). apply Z.leb_le in Hro. lia.
Qed.
(* every region of a run is read-only: its write obligation is vacuous *)
Ltac cc2_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

(* the branches of the tests, decided by the three flags of seg[i]: atom 34 = role_set as 0/1, atom 35 =
   model_set as 0/1, atom 33 = role. Each is the stop reason the token run reports (see the head comment). *)
(* 0x8989c `beqz a0` with a0 = role_set *)
Lemma cc2_br1 : forall E (b : bool), ew E 34 = Z_to_bv 64 (if b then 1 else 0) ->
  branch_taken BC_EQ (sv_denot E (SOff 34 0)) (sv_denot E (SLit 0)) = negb b.
Proof. intros E b H. cbn [sv_denot]. rewrite H. destruct b; vm_compute; reflexivity. Qed.
(* `seqz` of role - 4, the is_box bit *)
Lemma cc2_seqz : forall E r, ew E 33 = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
  alu64 ALU_SLTU (sv_denot E (SOff 33 (-4))) (sv_denot E (SLit 1)) = Z_to_bv 64 (if r =? 4 then 1 else 0).
Proof.
intros E r H33 Hr. apply bv_eq.
change (U E (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1)) = bv_unsigned (Z_to_bv 64 (if r =? 4 then 1 else 0))).
rewrite U_SAlu, U_SOff, U_SLit, H33, unsigned_lit_small by lia. cbn [zalu_raw].
destruct (Z.eqb_spec r 4) as [-> | Hne]; [vm_compute; reflexivity|].
assert (Hz : zcanon 1 <= zcanon (r + -4)).
{ unfold zcanon, M64. rewrite (Z.mod_small 1) by lia. destruct (Z_lt_le_dec r 4) as [Hlt | Hge].
  - replace (r + -4) with ((r + -4 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
rewrite (proj2 (Z.ltb_ge _ _) Hz). vm_compute. reflexivity.
Qed.
(* 0x898e4 `beqz a2`, a2 = (not model_set | a0) & 1, on the path role_set = 0 (a0 = role_set) *)
Lemma cc2_br2A : forall E (rs ms : bool), ew E 34 = Z_to_bv 64 (if rs then 1 else 0) ->
  ew E 35 = Z_to_bv 64 (if ms then 1 else 0) ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SOff 34 0)) (SLit 1)))
    (sv_denot E (SLit 0)) = negb (negb ms || rs).
Proof. intros E rs ms H34 H35. cbn [sv_denot]. rewrite H34, H35. destruct rs, ms; vm_compute; reflexivity. Qed.
(* the same on the path role_set = 1 (a0 = is_box) *)
Lemma cc2_br2B : forall E (ms : bool) r, ew E 33 = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
  ew E 35 = Z_to_bv 64 (if ms then 1 else 0) ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 35 0) (SLit 1))
       (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))) (SLit 1)))
    (sv_denot E (SLit 0)) = negb (negb ms || (r =? 4)).
Proof.
intros E ms r H33 Hr H35.
change (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 35 0) (SLit 1))
       (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))) (SLit 1)))
  with (alu64 ALU_AND (alu64 ALU_OR (alu64 ALU_SLTU (sv_denot E (SOff 35 0)) (sv_denot E (SLit 1)))
       (alu64 ALU_SLTU (sv_denot E (SOff 33 (-4))) (sv_denot E (SLit 1)))) (sv_denot E (SLit 1))).
rewrite (cc2_seqz E r H33 Hr). cbn [sv_denot]. rewrite H35.
destruct ms, (r =? 4); vm_compute; reflexivity.
Qed.
(* 0x898ec `beqz a0`, a0 = not model_set & (role_set, resp. is_box) *)
Lemma cc2_br3A : forall E (rs ms : bool), ew E 34 = Z_to_bv 64 (if rs then 1 else 0) ->
  ew E 35 = Z_to_bv 64 (if ms then 1 else 0) ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SOff 34 0)))
    (sv_denot E (SLit 0)) = negb (negb ms && rs).
Proof. intros E rs ms H34 H35. cbn [sv_denot]. rewrite H34, H35. destruct rs, ms; vm_compute; reflexivity. Qed.
Lemma cc2_br3B : forall E (ms : bool) r, ew E 33 = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
  ew E 35 = Z_to_bv 64 (if ms then 1 else 0) ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))))
    (sv_denot E (SLit 0)) = negb (negb ms && (r =? 4)).
Proof.
intros E ms r H33 Hr H35.
change (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))))
  with (alu64 ALU_AND (alu64 ALU_SLTU (sv_denot E (SOff 35 0)) (sv_denot E (SLit 1)))
       (alu64 ALU_SLTU (sv_denot E (SOff 33 (-4))) (sv_denot E (SLit 1)))).
rewrite (cc2_seqz E r H33 Hr). cbn [sv_denot]. rewrite H35.
destruct ms, (r =? 4); vm_compute; reflexivity.
Qed.

(* a 4-byte field read through the ASan reader is a val_mem of the restricted memory *)
Lemma cc2_val_mem_of_sa_val : forall segs H mem a (n : nat) (val : Z),
  sa_val (aview segs H mem) a n val -> val_mem segs (mrestrict H mem) a n val.
Proof.
intros segs H mem a n val Hv k Hk.
pose proof (Hv k Hk) as E. unfold aview, option_map in E.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
(* two modules define le_byte (YO0f's, which val_mem uses, and the kit's, which sa_val uses); they are the
   same function, so the bridge is by reflexivity *)
injection E as E.
assert (LB : Z_to_bv 8 (YO0f.le_byte val n k) = Z_to_bv 8 (le_byte val n k)) by reflexivity.
rewrite LB. f_equal. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* INV_LOOP with the record left open: the cut facts of pass i at the loop head (R = cc_at v i, which is INV_LOOP
   itself), at the latch (R = cc_at v (i + 1)), and at the two returns of refuse (R = SegModel.refuse ..) *)
Definition cc2_inv (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z) (R : rconf)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 /\
  0 <= i < cc_n v /\
  sa_rconf (rdW W3 mem3) (x_c v) R /\
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

(* a word whose 8 bytes the reader keeps reads the same *)
Lemma cc2_rdword_same : forall (rd rd' : reader) a, (forall x, a <= x < a + 8 -> rd' x = rd x) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
rewrite (H a), (H (a + 1)), (H (a + 2)), (H (a + 3)), (H (a + 4)), (H (a + 5)), (H (a + 6)), (H (a + 7))
  by lia.
reflexivity.
Qed.
(* the bytes of a chunk the run stored as 0, through the reader *)
Lemma cc2_aview0 : forall H (m : word -> option byte) a (n : nat),
  val_mem SEGS (mrestrict H m) a n 0 -> forall k, 0 <= k < Z.of_nat n -> aview SEGS H m (a + k) = Some 0.
Proof.
intros H m a n Hv k Hk. unfold aview.
pose proof (Hv (Z.to_nat k) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite E. cbn [option_map].
assert (L0 : forall w j, YO0f.le_byte 0 w j = 0).
{ intros w j. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity. }
rewrite L0. reflexivity.
Qed.
(* cc_un survives a run that writes only inside the reader's block: the read-only window, the literals and the
   stack-protector cells are image bytes or AR facts, and no image byte lies in a live block *)
Lemma cc2_un_keep : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  ly S (W : world SEGS) mem mem' md',
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotw guard) ->
  cc_un B lit gotw guard STK_REF v ly S W mem ->
  AR SEGS B ly S W mem' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_c v <= a < x_c v + seg_spec.SEG_C_SIZE) -> rdW W mem' a = rdW W mem a) ->
  cc_un B lit gotw guard STK_REF v ly S W mem'.
Proof.
intros B lit gotw guard STK_REF v ly S W mem mem' md' HRO HSSP Hun HAR' HK.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof Hun as [Hrod Hlit _ Hheap].
pose proof Hheap as (b & m & Hin & Hb & Hm).
pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hreq].
assert (KI : forall y, in_img SEGS y -> rdW W mem' y = rdW W mem y).
{ intros y Hi. pose proof (pa_img_range y Hi) as Hy. unfold kImgEnd in Hy.
  apply HK; [lia|]. intros Hy2.
  exact (blk_img SEGS B LAWS ly S W mem' md' b m y HAR' Hin ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) Hi). }
constructor.
- intros a Hro Ho He.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (HRO a Hr)]. }
  rewrite (KI a Hi). exact (Hrod a Hro Ho He).
- intros x Hx. destruct (Hlit x Hx) as (Hpos & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
  split; [exact Hpos|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
  split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W) mem' _ Hrom)].
  intros j Hj. rewrite <- (Hzs j Hj).
  rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Himg (lit x + Z.of_nat j) ltac:(lia)) as (Hi & _ & _).
  exact (KI _ Hi).
- exact (HSSP ly S W mem' md' HAR').
- exact Hheap.
Qed.

(* every byte of the reader's block is present, so the fields the pass stores into are writable *)
Lemma cc2_block_wr : forall (B : asyms) ly S (W : world SEGS) mem md (q n a : Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> q <= a < q + n ->
  writable_at SEGS (mrestrict (w_H W) mem) a.
Proof.
intros B ly S W mem md q n a HAR (b & m & Hin & Hb & Hq) Ha.
destruct (al_blocks _ _ (YG0q.AR_laws_ok SEGS B) ly S W mem md b m HAR Hin)
  as (_ & _ & _ & _ & Hp & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
assert (Hab : b <= a < b + req_size m) by lia.
destruct (Hp a Hab) as [Hpr _].
apply apresent_writable. exact Hpr.
Qed.

(* the symbolic state of ss_cc2 holds at the loop head of pass i *)
Lemma cc2_seed : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3,
  lit F_xmodel = VAL (A_OBJ 74) -> lit F_xbox = VAL (A_OBJ 73) ->
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  st_ok_pi SEGS VAL
    (Eimg (Ereg regs3 (cc2_extra (x_c v) i (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) (cc_n v))))
    ss_cc2
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_LOOP)) mem3 (seg_rom SEGS))).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HLM HLB HP HI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi32 & Hlen & H4096 & Hceil & Hstk).
pose proof HP as [HA _ _ Hc64 _ Hc16 _ _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _ & Htop & _).
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof HNA as (_ & Hly & _).
unfold cc_STK in Hslo, Hstk1.
assert (Hsp : 2 ^ 46 <= cc_sp0 v - 128 /\ cc_sp0 v <= 2 ^ 47) by (unfold cc_sp0; lia).
(* the fields of seg[i] *)
destruct (sa_rconf_fields _ _ _ _ Hrci Hlen)
  as (Hname & Hnl & Hmodel & Hml & Hrole & Hrole31 & Hrset & Hmset).
rewrite Z2Nat.id in Hname, Hmodel, Hrole, Hrset, Hmset by lia.
destruct (sa_rconf_n _ _ _ Hrc) as (Hn & Hn32 & _).
unfold cc_at in Hn. rewrite cc_fold_len in Hn by lia. change (Z.of_nat (length (rc_seg (x_rcs v)))) with (cc_n v) in Hn.
unfold cc_at in Hn32. rewrite cc_fold_len in Hn32 by lia.
assert (Hnv : 0 <= cc_n v <= 32) by (unfold cc_n; lia).
set (s := nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) in *.
unfold seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_MODEL_SET in Hrole, Hrset, Hmset.
unfold seg_spec.RC_N in *. unfold seg_spec.SEG_C_SIZE in *.
set (c := x_c v) in *. set (sp0 := cc_sp0 v) in *.
assert (Hc47 : c + 16616 <= 140737479966720) by lia.
set (E := Eimg (Ereg regs3 (cc2_extra c i s (cc_n v)))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (cc2_extra c i s (cc_n v)) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth cc2_extra map] in E32, E33, E34, E35, E36. clear EX.
assert (E73 : ew E (A_OBJ 73) = Z_to_bv 64 (VAL (A_OBJ 73)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E74 : ew E (A_OBJ 74) = Z_to_bv 64 (VAL (A_OBJ 74)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 73)) as V73. pose proof (pa_val_range (A_OBJ 74)) as V74.
assert (Hb34 : 0 <= (if rs_role_set s then 1 else 0) <= 1) by (destruct (rs_role_set s); lia).
assert (Hb35 : 0 <= (if rs_model_set s then 1 else 0) <= 1) by (destruct (rs_model_set s); lia).
assert (U2 : bv_unsigned (ew E 2) = sp0 - 128)
  by (rewrite (EE 2%nat 2%bv eq_refl), HSP; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (EE 8%nat 8%bv eq_refl), H8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = c + 0x2c80)
  by (rewrite (EE 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SB)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; unfold w64, SB, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (D9 : 0 <= (c + 0x2c80) / 8 <= c + 0x2c80)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U25 : bv_unsigned (ew E 25) = 356 * i)
  by (rewrite (EE 25%nat 25%bv eq_refl), H25; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = i)
  by (rewrite (EE 26%nat 26%bv eq_refl), H26; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = 2 ^ 64 - 1 - c)
  by (rewrite (EE 27%nat 27%bv eq_refl), H27; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = c + 356 * i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = rs_role s) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = (if rs_role_set s then 1 else 0))
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = (if rs_model_set s then 1 else 0))
  by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = cc_n v) by (rewrite E36; apply unsigned_lit_small; lia).
(* the alignments the atom facts carry, through Z.div_mod (the division flag is off in this file) *)
pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. rewrite Hc16, Z.add_0_r in Dc.
assert (Esp : sp0 = spZ (x_regs v)) by reflexivity.
assert (Hal16' : sp0 mod 16 = 0) by exact Hal16.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Dsp. rewrite Hal16', Z.add_0_r in Dsp.
assert (M2 : (sp0 - 128) mod 16 = 0)
  by (replace (sp0 - 128) with ((sp0 / 16 - 8) * 16) by lia; apply Z_mod_mult).
assert (M9 : (c + 0x2c80) mod 8 = 0)
  by (replace (c + 0x2c80) with ((2 * (c / 16) + 1424) * 8) by lia; apply Z_mod_mult).
assert (M25 : (356 * i) mod 4 = 0) by (replace (356 * i) with ((89 * i) * 4) by lia; apply Z_mod_mult).
assert (M32 : (c + 356 * i) mod 4 = 0)
  by (replace (c + 356 * i) with ((4 * (c / 16) + 89 * i) * 4) by lia; apply Z_mod_mult).
rewrite restrict_mkst_fx. unfold ss_cc2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cc2_regions, cc2_spill, cc2_seg, cc2_n.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 0 8 (SLit 3) 3); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hs0).
    * apply (chunk_ok_val SEGS E _ _ 8 8 (SOff (A_OBJ 73) 0) (VAL (A_OBJ 73)));
        [cbn [sv_denot]; rewrite E73, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      replace (sp0 - 128 + 8) with (sp0 - 120) by lia. rewrite <- HLB.
      exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hs8).
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff (A_OBJ 74) 0) (VAL (A_OBJ 74)));
        [cbn [sv_denot]; rewrite E74, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      replace (sp0 - 128 + 16) with (sp0 - 112) by lia. rewrite <- HLM.
      exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hs16).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 16 4 (SOff N_ROLE 0) (rs_role s));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (cc2_val_mem_of_sa_val _ _ _ _ _ _ Hrole).
    * apply (chunk_ok_val SEGS E _ _ 20 4 (SOff N_RSET 0) (if rs_role_set s then 1 else 0));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (cc2_val_mem_of_sa_val _ _ _ _ _ _ Hrset).
    * apply (chunk_ok_val SEGS E _ _ 60 4 (SOff N_MSET 0) (if rs_model_set s then 1 else 0));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (cc2_val_mem_of_sa_val _ _ _ _ _ _ Hmset).
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ _ 0 4 (SOff N_N 0) (cc_n v));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (cc2_val_mem_of_sa_val _ _ _ _ _ _ Hn).
- apply pairwise_disjoint_of_extents.
  unfold cc2_regions, cc2_spill, cc2_seg, cc2_n, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- split; [|split; [exact I|]].
  + unfold cc2_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U9, U18, U25, U26, U27, U32, U33, U34, U35, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
  + unfold cc2_alias. cbn [alias_ok]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 8 0) (SOff 25 0)) = U E (SOff N_SI 0)).
      rewrite U_SAlu, !U_SOff, U8, U25, U32. cbn [zalu_raw]. rewrite !Z.add_0_r.
      rewrite (zcanon_id c) by (unfold M64; lia). rewrite (zcanon_id (356 * i)) by (unfold M64; lia).
      reflexivity.
    * unfold cc2_shn. rewrite (denot_shx E 9 18 0 (c + 0x2c80) SB);
        [| rewrite <- U9; symmetry; apply Z_to_bv_bv_unsigned
         | rewrite <- U18; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia | unfold SB; lia].
      cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), H19. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      rewrite !Z.add_0_r. reflexivity.
Qed.

(* the symbolic state of ss_cc2l holds at the latch *)
Lemma cc2l_seed : forall (c : Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (n : Z),
  getr regs3 9 = w64 (c + seg_spec.RC_N) -> getr regs3 18 = w64 SHADOW_OFF ->
  getr regs3 19 = w64 (SHADOW_OFF + (c + seg_spec.RC_N) / 8) ->
  4096 <= c -> c + 16616 <= 140737479966720 -> c mod 16 = 0 -> 0 <= n <= 32 ->
  sa_val (rdW W3 mem3) (c + seg_spec.RC_N) 4 n ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs3 [Z_to_bv 64 n])) ss_cc2l
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_LATCH)) mem3 (seg_rom SEGS))).
Proof.
intros c W3 regs3 mem3 n H9 H18 H19 Hc1 Hc2 Hc16 Hn Hnv.
unfold seg_spec.RC_N in *.
set (E := Eimg (Ereg regs3 [Z_to_bv 64 n])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c + 0x2c80)
  by (rewrite (EE 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SB)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; unfold w64, SB, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (D9 : 0 <= (c + 0x2c80) / 8 <= c + 0x2c80)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. rewrite Hc16, Z.add_0_r in Dc.
assert (M9 : (c + 0x2c80) mod 8 = 0)
  by (replace (c + 0x2c80) with ((2 * (c / 16) + 1424) * 8) by lia; apply Z_mod_mult).
rewrite restrict_mkst_fx. unfold ss_cc2l. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cc2l_n. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) n);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (cc2_val_mem_of_sa_val _ _ _ _ _ _ Hnv).
- cbn. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, U32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
  + cbn [f_alias alias_ok]. split; [|exact I].
    unfold cc2_shn. rewrite (denot_shx E 9 18 0 (c + 0x2c80) SB);
      [| rewrite <- U9; symmetry; apply Z_to_bv_bv_unsigned
       | rewrite <- U18; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia | unfold SB; lia].
    cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), H19. unfold w64.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.add_0_r. reflexivity.
Qed.

(* the latch 0x89968 .. 0x89980 of pass i, the record already cc_at v (i + 1): check 9 (inline, load4 of c->n;
   its slow path 0x899a4 starts with `ld a1,0(sp)`, no andi, so the executor asks the whole 8-byte granule of
   &c->n, which the block's shadow gives), n re-loaded, s10 = i + 1, s9 = 356 (i + 1), and `blt s10,a0` split:
   taken to the head of pass i + 1, not taken (i + 1 = n) through `j 0x899fc` to the epilogue. No byte is
   written, so every fact of the memory carries over unchanged. *)
Lemma cc2_latch : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  from_EPI B lit gotw guard STK_REF v -> from_LOOP B lit gotw guard STK_REF v (i + 1) ->
  cc2_inv B lit gotw guard STK_REF v i (cc_at v (i + 1)) ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HEPI HLOOP HI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof Hun as [_ _ _ Hheap3].
pose proof HJ as (HAR3 & _).
pose proof HP as [_ _ _ Hc64 _ Hc16 _ _ _ _ _ _ _ _].
destruct (cc_block_low B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [H4096 Hceil].
pose proof (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (_ & _ & _ & HRA & _).
destruct (sa_rconf_n _ _ _ Hrc) as (Hn & Hn32 & _).
unfold cc_at in Hn, Hn32. rewrite cc_fold_len in Hn, Hn32 by lia.
change (Z.of_nat (length (rc_seg (x_rcs v)))) with (cc_n v) in Hn.
assert (Hnv : 0 <= cc_n v <= 32) by (unfold cc_n; lia).
unfold seg_spec.SEG_C_SIZE in Hceil, HRA.
pose proof (cc2l_seed (x_c v) W3 regs3 mem3 (cc_n v) H9 H18 H19 H4096 ltac:(lia) Hc16 Hnv Hn) as HS.
unfold seg_spec.RC_N in *.
remember (Eimg (Ereg regs3 [Z_to_bv 64 (cc_n v)])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (cc_n v))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (UB : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia]).
assert (U9 : U E (SOff 9 0) = x_c v + 0x2c80)
  by (apply U_atom; [rewrite (EE 9%nat 9%bv eq_refl); exact H9 | lia]).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) mem3)) by constructor.
unfold cfg_at. change (w64 (BASE + CC_LATCH)) with (Z_to_bv 64 (BASE + CC_LATCH)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U9.
  apply (obl_of_range SEGS (w_H W3) mem3 E (SOff 18 0) (x_c v + 0x2c80) 8 (x_c v) 16616 HRA UB); lia. }
{ cc2_awr_ro. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
assert (M1 : ms_mem ms1 = mem3) by (eapply cc2_frame_ro; [| exact HF1]; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (E1E : forall k, (k < 1024)%nat -> ew E1 k = ew E k)
  by (intros k Hk; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
clearbody E1.
assert (LT : branch_taken BC_LT (sv_denot E1 (SOff 26 1)) (sv_denot E1 (SOff 32 0)) = (i + 1 <? cc_n v)).
{ apply cc2_lt_atoms; [rewrite E1E, (EE 26%nat 26%bv eq_refl) by lia; exact H26
                      | rewrite E1E by lia; exact E32 | lia | lia | lia]. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: i + 1 < n, the head of pass i + 1 *)
  rewrite LT in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LOOP.
  { cc2_awr_ro. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (M2 : ms_mem ms2 = ms_mem ms1) by (eapply cc2_frame_ro; [| exact HF2]; vm_compute; reflexivity).
  rewrite M1 in M2.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
  prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
  prreg HS (27%bv : bv 5) R27.
  pmkst HS.
  change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_LOOP) (ms_regs ms2) (ms_mem ms2) md2)
    (cc_post B lit gotw guard STK_REF v)).
  apply (HLOOP ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) md2).
  unfold INV_LOOP.
  split.
  { constructor.
    - exact HJ.
    - rewrite R2, E1E, (EE 2%nat 2%bv eq_refl) by lia. exact HSP.
    - rewrite R3, E1E, (EE 3%nat 3%bv eq_refl) by lia. exact HGP.
    - rewrite R4, E1E, (EE 4%nat 4%bv eq_refl) by lia. exact HTP.
    - rewrite M2. exact HSV.
    - exact HNA. }
  split; [rewrite M2; exact Hun|].
  split; [lia|].
  split; [rewrite M2; exact Hrc|].
  split; [rewrite R8, E1E, (EE 8%nat 8%bv eq_refl) by lia; exact H8|].
  split; [rewrite R9, E1E, (EE 9%nat 9%bv eq_refl) by lia; exact H9|].
  split; [rewrite R18, E1E, (EE 18%nat 18%bv eq_refl) by lia; exact H18|].
  split; [rewrite R19, E1E, (EE 19%nat 19%bv eq_refl) by lia; exact H19|].
  split.
  { rewrite R25, E1E, (EE 25%nat 25%bv eq_refl), H25 by lia. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal. lia. }
  split.
  { rewrite R26, E1E, (EE 26%nat 26%bv eq_refl), H26 by lia. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity. }
  split; [rewrite R27, E1E, (EE 27%nat 27%bv eq_refl) by lia; exact H27|].
  rewrite M2. split; [exact Hs0|]. split; [exact Hs8 | exact Hs16].
- (* not taken: i + 1 = n, through `j 0x899fc` to the epilogue; the fold is complete *)
  rewrite LT in Hc. apply Z.ltb_ge in Hc.
  assert (Hin : i + 1 = cc_n v) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_EPI.
  { cc2_awr_ro. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (M2 : ms_mem ms2 = ms_mem ms1) by (eapply cc2_frame_ro; [| exact HF2]; vm_compute; reflexivity).
  rewrite M1 in M2.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  pmkst HS.
  change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_EPI) (ms_regs ms2) (ms_mem ms2) md2)
    (cc_post B lit gotw guard STK_REF v)).
  apply (HEPI ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) md2).
  split.
  { constructor.
    - exact HJ.
    - rewrite R2, E1E, (EE 2%nat 2%bv eq_refl) by lia. exact HSP.
    - rewrite R3, E1E, (EE 3%nat 3%bv eq_refl) by lia. exact HGP.
    - rewrite R4, E1E, (EE 4%nat 4%bv eq_refl) by lia. exact HTP.
    - rewrite M2. exact HSV.
    - exact HNA. }
  rewrite M2. replace (SegModel.cross_check (x_rcs v)) with (cc_at v (i + 1)); [exact Hrc|].
  unfold cc_at. rewrite Hin. unfold cc_n. apply cc_fold_all.
Qed.

(* the symbolic state of ss_cc2b holds at the return 0x89904 of the BOX arm's call *)
Lemma cc2b_seed : forall (B : asyms) ly S (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md (c i : Z),
  AR SEGS B ly S W3 mem3 md -> sa_heap B ly S c seg_spec.SEG_C_SIZE ->
  4096 <= c -> c + 16616 <= 140737479966720 -> c mod 16 = 0 -> 0 <= i <= 31 ->
  getr regs3 18 = w64 SHADOW_OFF -> getr regs3 20 = w64 (c + 356 * i) ->
  getr regs3 21 = w64 (c + 356 * i + 20) -> getr regs3 23 = w64 (SHADOW_OFF + (c + 356 * i + 20) / 8) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) ss_cc2b
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_RET1)) mem3 (seg_rom SEGS))).
Proof.
intros B ly S W3 regs3 mem3 md c i HAR Hheap Hc1 Hc2 Hc16 Hi H18 H20 H21 H23.
set (E := Eimg (Ereg regs3 [])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U18 : bv_unsigned (ew E 18) = SB)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; unfold w64, SB, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = c + 356 * i)
  by (rewrite (EE 20%nat 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = c + 356 * i + 20)
  by (rewrite (EE 21%nat 21%bv eq_refl), H21; unfold w64; apply unsigned_lit_small; lia).
assert (D : 0 <= (c + 356 * i + 20) / 8 <= c + 356 * i + 20)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. rewrite Hc16, Z.add_0_r in Dc.
assert (M20 : (c + 356 * i) mod 4 = 0)
  by (replace (c + 356 * i) with ((4 * (c / 16) + 89 * i) * 4) by lia; apply Z_mod_mult).
assert (M21 : (c + 356 * i + 20) mod 4 = 0)
  by (replace (c + 356 * i + 20) with ((4 * (c / 16) + 89 * i + 5) * 4) by lia; apply Z_mod_mult).
rewrite restrict_mkst_fx. unfold ss_cc2b. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U20. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (cc2_block_wr B ly S W3 mem3 md c seg_spec.SEG_C_SIZE); [exact HAR | exact Hheap |].
  unfold seg_spec.SEG_C_SIZE. lia.
- cbn. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U20, U21. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
  + cbn [f_alias alias_ok]. split; [|exact I].
    unfold cc2_shx. rewrite (denot_shx E 21 18 0 (c + 356 * i + 20) SB);
      [| rewrite <- U21; symmetry; apply Z_to_bv_bv_unsigned
       | rewrite <- U18; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia | unfold SB; lia].
    cbn [sv_denot]. rewrite (EE 23%nat 23%bv eq_refl), H23. unfold w64.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.add_0_r. reflexivity.
Qed.

(* the BOX arm after refuse returned (0x89904 .. 0x89928): check 5 (inline, store4 of s->role_set at s5 = s4 + 20;
   s7 is the alias of its shadow byte) and `sw zero,20(s4)`, check 6 (inline, store4 of s->role at s4 + 16) and
   `sw zero,16(s4)`, then `j 0x89968` to the latch. The record refuse left becomes its r_upd rs_drop_role, which
   is the fold's next record on this arm (r_cross_seg_box). Only those 8 bytes are written. *)
Lemma cc2_box_after : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3,
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  cc_pre B lit gotw guard STK_REF v ->
  from_EPI B lit gotw guard STK_REF v -> from_LOOP B lit gotw guard STK_REF v (i + 1) ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = false ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = true ->
  cc2_inv B lit gotw guard STK_REF v i
    (SegModel.refuse (cc_at v i) 0 F_xbox [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))])
    ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 20 = w64 (x_c v + 356 * i) ->
  getr regs3 21 = w64 (x_c v + 356 * i + 20) ->
  getr regs3 23 = w64 (SHADOW_OFF + (x_c v + 356 * i + 20) / 8) ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_RET1) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HRO HSSP HP HEPI HLOOP Hms Hbox HI H20 H21 H23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof Hun as [_ _ _ Hheap3].
pose proof HJ as (HAR3 & _).
pose proof HP as [HA _ _ Hc64 _ Hc16 Hrc0 _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _).
unfold cc_STK in Hslo, Hstk1.
destruct (cc_block_low B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [H4096 Hceil].
pose proof (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (_ & _ & _ & HRA & _).
destruct (sa_rconf_n _ _ _ Hrc0) as (_ & Hn32 & _).
assert (Hi31 : 0 <= i <= 31) by (unfold cc_n in Hib; lia).
pose proof Hheap3 as (bq & mq & Hinq & Hbq & Hmq).
unfold seg_spec.SEG_C_SIZE in *.
pose proof (req_size_pos mq ltac:(lia)) as [_ Hreq].
pose proof (cc2b_seed B ly3 S3 W3 regs3 mem3 md3 (x_c v) i HAR3 Hheap3 H4096 ltac:(lia) Hc16 Hi31
  H18 H20 H21 H23) as HS.
remember (Eimg (Ereg regs3 [])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (UB : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia]).
assert (U20 : bv_unsigned (ew E 20) = x_c v + 356 * i)
  by (rewrite (EE 20%nat 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (U200 : U E (SOff 20 0) = x_c v + 356 * i)
  by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact H20 | lia]).
assert (U2016 : U E (SOff 20 16) = x_c v + 356 * i + 16)
  by (rewrite U_SOff, U20; apply zcanon_id; unfold M64; lia).
assert (U21 : U E (SOff 21 0) = x_c v + 356 * i + 20)
  by (apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl); exact H21 | lia]).
assert (SHOK : sh_ok SEGS (SOff 18 0) [mkSHE 20 24 16] E (mrestrict (w_H W3) mem3)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 E (SOff 18 0) 20 (x_c v + 356 * i) bq mq 16 24
    _ HAR3 Hinq UB U200); lia. }
unfold cfg_at. change (w64 (BASE + CC_RET1)) with (Z_to_bv 64 (BASE + CC_RET1)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LATCH.
{ rewrite ?U2016, ?U21.
  apply (obl_of_range SEGS (w_H W3) mem3 E (SOff 18 0) _ 4 (x_c v) 16616 HRA UB); lia. }
{ rewrite ?U2016, ?U21.
  apply (obl_of_range SEGS (w_H W3) mem3 E (SOff 18 0) _ 4 (x_c v) 16616 HRA UB); lia. }
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U20 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
  - exists (x_c v, x_c v + seg_spec.RSEG_SIZE * 32). unfold cc_FP, cross_check_W.
    split; [left; reflexivity | cbn [fst snd]; unfold seg_spec.RSEG_SIZE; lia].
  - exists bq, mq. split; [exact Hinq | lia]. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (E1E : forall k, (k < 1024)%nat -> ew E1 k = ew E k)
  by (intros k Hk; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
clearbody E1.
(* the run wrote only s->role and s->role_set *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_c v + 356 * i + 16 <= a < x_c v + 356 * i + 24) ->
  rdW W3 (ms_mem ms1) a = rdW W3 mem3 a).
{ intros a Ha Hn.
  apply (kept_of_frame E _ (w_H W3) mem3 (ms_mem ms1)
    (fun x => x_c v + 356 * i + 16 <= x < x_c v + 356 * i + 24) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. vm_compute in Hin. destruct Hin as [Hq | []].
  injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U20 in Hx. lia. }
(* the 8 bytes it wrote are 0: the region's two chunks *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss1) cc2l_n) in
  pose proof (st_ok_pi_region_nth E1 ss1 _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as RG end.
cbn [ms_mem restrict] in RG.
assert (U20' : bv_unsigned (ew E1 20) = x_c v + 356 * i) by (rewrite E1E by lia; exact U20).
pose proof (field_of_region E1 _ 20 (x_c v + 356 * i) _ 16 24 16 24 16 4 (SLit 0) 0 RG U20'
  ltac:(left; reflexivity) eq_refl ltac:(zside) ltac:(zside)) as Z16.
pose proof (field_of_region E1 _ 20 (x_c v + 356 * i) _ 16 24 16 24 20 4 (SLit 0) 0 RG U20'
  ltac:(right; left; reflexivity) eq_refl ltac:(zside) ltac:(zside)) as Z20.
(* the record: refuse's, with role and role_set zeroed, is the fold at i + 1 *)
assert (Hlen : (Z.to_nat i < length (rc_seg (SegModel.refuse (cc_at v i) 0 F_xbox
    [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))])))%nat).
{ rewrite refuse_seg. unfold cc_at. rewrite cc_fold_len by lia. unfold cc_n in Hib. lia. }
assert (HR1 : sa_rconf (rdW W3 (ms_mem ms1)) (x_c v) (cc_at v (i + 1))).
{ unfold cc_at at 1. rewrite cc_fold_S by lia. fold (cc_at v i). rewrite r_cross_seg_box by assumption.
  apply (sa_rconf_drop_role (rdW W3 mem3) (rdW W3 (ms_mem ms1)) (x_c v) _ (Z.to_nat i) Hrc Hlen).
  - intros k Hk. rewrite Z2Nat.id by lia. unfold seg_spec.RS_ROLE.
    destruct (Z_lt_le_dec k 4) as [Hk4 | Hk4].
    + replace (x_c v + 356 * i + 16 + k) with (x_c v + 356 * i + 16 + k) by lia.
      exact (cc2_aview0 (w_H W3) (ms_mem ms1) _ 4 Z16 k ltac:(lia)).
    + replace (x_c v + 356 * i + 16 + k) with (x_c v + 356 * i + 20 + (k - 4)) by lia.
      exact (cc2_aview0 (w_H W3) (ms_mem ms1) _ 4 Z20 (k - 4) ltac:(lia)).
  - intros a Ha Hn. rewrite Z2Nat.id in Hn by lia. unfold seg_spec.RS_ROLE in Hn.
    unfold seg_spec.SEG_C_SIZE in Ha. apply K1; lia. }
(* the cut facts at the latch *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
prreg HS (27%bv : bv 5) R27.
pose proof HJ as (HAR1 & _).
assert (Hsp : alloc_ceiling <= cc_sp0 v <= 2 ^ 47) by (unfold cc_sp0; lia).
assert (KS : forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W3 (ms_mem ms1) a = rdW W3 mem3 a)
  by (intros a Ha; apply K1; lia).
pmkst HS.
change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) (ms_regs ms1) (ms_mem ms1) md1)
  (cc_post B lit gotw guard STK_REF v)).
apply (cc2_latch B lit gotw guard STK_REF v i ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) md1 HP HEPI HLOOP).
split.
{ constructor.
  - exact HJ.
  - rewrite R2, E1E, (EE 2%nat 2%bv eq_refl) by lia. exact HSP.
  - rewrite R3, E1E, (EE 3%nat 3%bv eq_refl) by lia. exact HGP.
  - rewrite R4, E1E, (EE 4%nat 4%bv eq_refl) by lia. exact HTP.
  - intros j r Hj. assert (Hjl : (j < length cc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cc_saved] in Hjl.
    rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia). exact (HSV j r Hj).
  - exact HNA. }
split.
{ apply (cc2_un_keep B lit gotw guard STK_REF v ly3 S3 W3 mem3 (ms_mem ms1) md1 HRO HSSP Hun HAR1).
  intros a Ha Hn. apply K1; [exact Ha|]. unfold seg_spec.SEG_C_SIZE in Hn. lia. }
split; [exact Hib|].
split; [exact HR1|].
split; [rewrite R8, E1E, (EE 8%nat 8%bv eq_refl) by lia; exact H8|].
split; [rewrite R9, E1E, (EE 9%nat 9%bv eq_refl) by lia; exact H9|].
split; [rewrite R18, E1E, (EE 18%nat 18%bv eq_refl) by lia; exact H18|].
split; [rewrite R19, E1E, (EE 19%nat 19%bv eq_refl) by lia; exact H19|].
split; [rewrite R25, E1E, (EE 25%nat 25%bv eq_refl) by lia; exact H25|].
split; [rewrite R26, E1E, (EE 26%nat 26%bv eq_refl) by lia; exact H26|].
split; [rewrite R27, E1E, (EE 27%nat 27%bv eq_refl) by lia; exact H27|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs0|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs8|].
rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs16.
Qed.

(* the symbolic state of ss_cc2m holds at the return 0x89948 of the MODEL arm's call *)
Lemma cc2m_seed : forall (B : asyms) ly S (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md (c i : Z),
  AR SEGS B ly S W3 mem3 md -> sa_heap B ly S c seg_spec.SEG_C_SIZE ->
  4096 <= c -> c + 16616 <= 140737479966720 -> c mod 16 = 0 -> 0 <= i <= 31 ->
  getr regs3 18 = w64 SHADOW_OFF -> getr regs3 20 = w64 (c + 356 * i) ->
  getr regs3 21 = w64 (c + 356 * i + 36) -> getr regs3 22 = w64 (c + 356 * i + 60) ->
  getr regs3 24 = w64 (SHADOW_OFF + (c + 356 * i + 60) / 8) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) ss_cc2m
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_RET2)) mem3 (seg_rom SEGS))).
Proof.
intros B ly S W3 regs3 mem3 md c i HAR Hheap Hc1 Hc2 Hc16 Hi H18 H20 H21 H22 H24.
set (E := Eimg (Ereg regs3 [])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U18 : bv_unsigned (ew E 18) = SB)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; unfold w64, SB, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = c + 356 * i)
  by (rewrite (EE 20%nat 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = c + 356 * i + 36)
  by (rewrite (EE 21%nat 21%bv eq_refl), H21; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = c + 356 * i + 60)
  by (rewrite (EE 22%nat 22%bv eq_refl), H22; unfold w64; apply unsigned_lit_small; lia).
assert (D : 0 <= (c + 356 * i + 60) / 8 <= c + 356 * i + 60)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. rewrite Hc16, Z.add_0_r in Dc.
assert (M20 : (c + 356 * i) mod 4 = 0)
  by (replace (c + 356 * i) with ((4 * (c / 16) + 89 * i) * 4) by lia; apply Z_mod_mult).
assert (M21 : (c + 356 * i + 36) mod 4 = 0)
  by (replace (c + 356 * i + 36) with ((4 * (c / 16) + 89 * i + 9) * 4) by lia; apply Z_mod_mult).
assert (M22 : (c + 356 * i + 60) mod 4 = 0)
  by (replace (c + 356 * i + 60) with ((4 * (c / 16) + 89 * i + 15) * 4) by lia; apply Z_mod_mult).
rewrite restrict_mkst_fx. unfold ss_cc2m. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U20. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (cc2_block_wr B ly S W3 mem3 md c seg_spec.SEG_C_SIZE); [exact HAR | exact Hheap |].
    unfold seg_spec.SEG_C_SIZE. lia.
  + rewrite U21. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (cc2_block_wr B ly S W3 mem3 md c seg_spec.SEG_C_SIZE); [exact HAR | exact Hheap |].
    unfold seg_spec.SEG_C_SIZE. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U21.
  split; [split; [right; lia | exact I] | split; exact I].
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U20, U21, U22. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
  + cbn [f_alias alias_ok]. split; [|exact I].
    unfold cc2_shx. rewrite (denot_shx E 22 18 0 (c + 356 * i + 60) SB);
      [| rewrite <- U22; symmetry; apply Z_to_bv_bv_unsigned
       | rewrite <- U18; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia | unfold SB; lia].
    cbn [sv_denot]. rewrite (EE 24%nat 24%bv eq_refl), H24. unfold w64.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.add_0_r. reflexivity.
Qed.

(* the MODEL arm after refuse returned (0x89948 .. 0x89964): check 7 (inline, store4 of s->model_set at
   s6 = s4 + 60; s8 is the alias of its shadow byte) and `sw zero,60(s4)`, check 8 (inline, store1 of
   s->model[0] at s5 = s4 + 36) and `sb zero,0(s5)`, falling through to the latch. The record refuse left becomes
   its r_upd rs_drop_model, the fold's next record on this arm (r_cross_seg_model). Only those 5 bytes are
   written. *)
Lemma cc2_model_after : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3,
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  cc_pre B lit gotw guard STK_REF v ->
  from_EPI B lit gotw guard STK_REF v -> from_LOOP B lit gotw guard STK_REF v (i + 1) ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = true ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = false ->
  cc2_inv B lit gotw guard STK_REF v i
    (SegModel.refuse (cc_at v i) 0 F_xmodel
       [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d));
        AS (rs_model (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))])
    ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 20 = w64 (x_c v + 356 * i) ->
  getr regs3 21 = w64 (x_c v + 356 * i + 36) ->
  getr regs3 22 = w64 (x_c v + 356 * i + 60) ->
  getr regs3 24 = w64 (SHADOW_OFF + (x_c v + 356 * i + 60) / 8) ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_RET2) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HRO HSSP HP HEPI HLOOP Hms Hbox HI H20 H21 H22 H24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof Hun as [_ _ _ Hheap3].
pose proof HJ as (HAR3 & _).
pose proof HP as [HA _ _ Hc64 _ Hc16 Hrc0 _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _).
unfold cc_STK in Hslo, Hstk1.
destruct (cc_block_low B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [H4096 Hceil].
pose proof (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (_ & _ & _ & HRA & _).
destruct (sa_rconf_n _ _ _ Hrc0) as (_ & Hn32 & _).
assert (Hi31 : 0 <= i <= 31) by (unfold cc_n in Hib; lia).
pose proof Hheap3 as (bq & mq & Hinq & Hbq & Hmq).
unfold seg_spec.SEG_C_SIZE in *.
pose proof (req_size_pos mq ltac:(lia)) as [_ Hreq].
pose proof (cc2m_seed B ly3 S3 W3 regs3 mem3 md3 (x_c v) i HAR3 Hheap3 H4096 ltac:(lia) Hc16 Hi31
  H18 H20 H21 H22 H24) as HS.
remember (Eimg (Ereg regs3 [])) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (UB : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia]).
assert (U20 : bv_unsigned (ew E 20) = x_c v + 356 * i)
  by (rewrite (EE 20%nat 20%bv eq_refl), H20; unfold w64; apply unsigned_lit_small; lia).
assert (U21b : bv_unsigned (ew E 21) = x_c v + 356 * i + 36)
  by (rewrite (EE 21%nat 21%bv eq_refl), H21; unfold w64; apply unsigned_lit_small; lia).
assert (U200 : U E (SOff 20 0) = x_c v + 356 * i)
  by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact H20 | lia]).
assert (U21 : U E (SOff 21 0) = x_c v + 356 * i + 36)
  by (apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl); exact H21 | lia]).
assert (U22 : U E (SOff 22 0) = x_c v + 356 * i + 60)
  by (apply U_atom; [rewrite (EE 22%nat 22%bv eq_refl); exact H22 | lia]).
assert (SHOK : sh_ok SEGS (SOff 18 0) [mkSHE 20 64 60; mkSHE 21 1 0] E (mrestrict (w_H W3) mem3)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_app_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 E (SOff 18 0) 20 (x_c v + 356 * i) bq mq 60 64
      _ HAR3 Hinq UB U200); lia.
  - apply (shent_app_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 E (SOff 18 0) 21 (x_c v + 356 * i + 36) bq mq 0 1
      _ HAR3 Hinq UB U21); lia. }
unfold cfg_at. change (w64 (BASE + CC_RET2)) with (Z_to_bv 64 (BASE + CC_RET2)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LATCH.
{ rewrite ?U21, ?U22.
  apply (obl_of_range SEGS (w_H W3) mem3 E (SOff 18 0) _ _ (x_c v) 16616 HRA UB); lia. }
{ rewrite ?U21, ?U22.
  apply (obl_of_range SEGS (w_H W3) mem3 E (SOff 18 0) _ _ (x_c v) 16616 HRA UB); lia. }
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U20 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
    - exists (x_c v, x_c v + seg_spec.RSEG_SIZE * 32). unfold cc_FP, cross_check_W.
      split; [left; reflexivity | cbn [fst snd]; unfold seg_spec.RSEG_SIZE; lia].
    - exists bq, mq. split; [exact Hinq | lia]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U21b | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
  - exists (x_c v, x_c v + seg_spec.RSEG_SIZE * 32). unfold cc_FP, cross_check_W.
    split; [left; reflexivity | cbn [fst snd]; unfold seg_spec.RSEG_SIZE; lia].
  - exists bq, mq. split; [exact Hinq | lia]. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (E1E : forall k, (k < 1024)%nat -> ew E1 k = ew E k)
  by (intros k Hk; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
clearbody E1.
(* the run wrote only s->model_set and s->model[0] *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_c v + 356 * i + 60 <= a < x_c v + 356 * i + 64 \/ x_c v + 356 * i + 36 <= a < x_c v + 356 * i + 37) ->
  rdW W3 (ms_mem ms1) a = rdW W3 mem3 a).
{ intros a Ha Hn.
  apply (kept_of_frame E _ (w_H W3) mem3 (ms_mem ms1)
    (fun x => x_c v + 356 * i + 60 <= x < x_c v + 356 * i + 64 \/
              x_c v + 356 * i + 36 <= x < x_c v + 356 * i + 37) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. vm_compute in Hin. destruct Hin as [Hq | [Hq | []]].
  - injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U20 in Hx. lia.
  - injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U21b in Hx. lia. }
(* the 5 bytes it wrote are 0: the two regions' chunks *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss1) cc2l_n) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ss1) cc2l_n) in
  pose proof (st_ok_pi_region_nth E1 ss1 _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as RG0;
  pose proof (st_ok_pi_region_nth E1 ss1 _ 1%nat r1 HS ltac:(vm_compute; reflexivity)) as RG1 end.
cbn [ms_mem restrict] in RG0, RG1.
assert (U20' : bv_unsigned (ew E1 20) = x_c v + 356 * i) by (rewrite E1E by lia; exact U20).
assert (U21' : bv_unsigned (ew E1 21) = x_c v + 356 * i + 36) by (rewrite E1E by lia; exact U21b).
pose proof (field_of_region E1 _ 20 (x_c v + 356 * i) _ 60 64 60 64 60 4 (SLit 0) 0 RG0 U20'
  ltac:(left; reflexivity) eq_refl ltac:(zside) ltac:(zside)) as Z60.
pose proof (field_of_region E1 _ 21 (x_c v + 356 * i + 36) _ 0 1 0 1 0 1 (SLit 0) 0 RG1 U21'
  ltac:(left; reflexivity) eq_refl ltac:(zside) ltac:(zside)) as Z36.
(* the record: refuse's, with model_set and model[0] zeroed, is the fold at i + 1 *)
assert (Hlen : (Z.to_nat i < length (rc_seg (SegModel.refuse (cc_at v i) 0 F_xmodel
    [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d));
     AS (rs_model (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))])))%nat).
{ rewrite refuse_seg. unfold cc_at. rewrite cc_fold_len by lia. unfold cc_n in Hib. lia. }
assert (HR1 : sa_rconf (rdW W3 (ms_mem ms1)) (x_c v) (cc_at v (i + 1))).
{ unfold cc_at at 1. rewrite cc_fold_S by lia. fold (cc_at v i). rewrite r_cross_seg_model by assumption.
  apply (sa_rconf_drop_model (rdW W3 mem3) (rdW W3 (ms_mem ms1)) (x_c v) _ (Z.to_nat i) Hrc Hlen).
  - intros k Hk. rewrite Z2Nat.id by lia. unfold seg_spec.RS_MODEL_SET.
    exact (cc2_aview0 (w_H W3) (ms_mem ms1) _ 4 Z60 k ltac:(lia)).
  - rewrite Z2Nat.id by lia. unfold seg_spec.RS_MODEL.
    pose proof (cc2_aview0 (w_H W3) (ms_mem ms1) _ 1 Z36 0 ltac:(lia)) as Z.
    rewrite !Z.add_0_r in Z. exact Z.
  - intros a Ha Hn1 Hn2. rewrite Z2Nat.id in Hn1, Hn2 by lia.
    unfold seg_spec.RS_MODEL, seg_spec.RS_MODEL_SET in Hn1, Hn2.
    unfold seg_spec.SEG_C_SIZE in Ha. apply K1; lia. }
(* the cut facts at the latch *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
prreg HS (27%bv : bv 5) R27.
pose proof HJ as (HAR1 & _).
assert (Hsp : alloc_ceiling <= cc_sp0 v <= 2 ^ 47) by (unfold cc_sp0; lia).
assert (KS : forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W3 (ms_mem ms1) a = rdW W3 mem3 a)
  by (intros a Ha; apply K1; lia).
pmkst HS.
change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) (ms_regs ms1) (ms_mem ms1) md1)
  (cc_post B lit gotw guard STK_REF v)).
apply (cc2_latch B lit gotw guard STK_REF v i ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) md1 HP HEPI HLOOP).
split.
{ constructor.
  - exact HJ.
  - rewrite R2, E1E, (EE 2%nat 2%bv eq_refl) by lia. exact HSP.
  - rewrite R3, E1E, (EE 3%nat 3%bv eq_refl) by lia. exact HGP.
  - rewrite R4, E1E, (EE 4%nat 4%bv eq_refl) by lia. exact HTP.
  - intros j r Hj. assert (Hjl : (j < length cc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cc_saved] in Hjl.
    rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia). exact (HSV j r Hj).
  - exact HNA. }
split.
{ apply (cc2_un_keep B lit gotw guard STK_REF v ly3 S3 W3 mem3 (ms_mem ms1) md1 HRO HSSP Hun HAR1).
  intros a Ha Hn. apply K1; [exact Ha|]. unfold seg_spec.SEG_C_SIZE in Hn. lia. }
split; [exact Hib|].
split; [exact HR1|].
split; [rewrite R8, E1E, (EE 8%nat 8%bv eq_refl) by lia; exact H8|].
split; [rewrite R9, E1E, (EE 9%nat 9%bv eq_refl) by lia; exact H9|].
split; [rewrite R18, E1E, (EE 18%nat 18%bv eq_refl) by lia; exact H18|].
split; [rewrite R19, E1E, (EE 19%nat 19%bv eq_refl) by lia; exact H19|].
split; [rewrite R25, E1E, (EE 25%nat 25%bv eq_refl) by lia; exact H25|].
split; [rewrite R26, E1E, (EE 26%nat 26%bv eq_refl) by lia; exact H26|].
split; [rewrite R27, E1E, (EE 27%nat 27%bv eq_refl) by lia; exact H27|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs0|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs8|].
rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs16.
Qed.

(* the cut facts at the latch on the path that calls nothing: the head run wrote no byte and kept the ten
   registers, and r_cross_seg leaves the record as it was *)
Lemma cc2_keep_inv : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regs' : bvmap 5 word) md',
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 md' 0 ->
  getr regs' 2 = getr regs3 2 -> getr regs' 3 = getr regs3 3 -> getr regs' 4 = getr regs3 4 ->
  getr regs' 8 = getr regs3 8 -> getr regs' 9 = getr regs3 9 -> getr regs' 18 = getr regs3 18 ->
  getr regs' 19 = getr regs3 19 -> getr regs' 25 = getr regs3 25 -> getr regs' 26 = getr regs3 26 ->
  getr regs' 27 = getr regs3 27 ->
  r_cross_seg (cc_at v i) (Z.to_nat i) = cc_at v i ->
  cc2_inv B lit gotw guard STK_REF v i (cc_at v (i + 1)) ly3 S3 W3 regs' mem3 md'.
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs' md' HI HJ' R2 R3 R4 R8 R9 R18 R19 R25 R26 R27 Hk.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
assert (Hat : cc_at v (i + 1) = cc_at v i) by (unfold cc_at at 1; rewrite cc_fold_S by lia; exact Hk).
rewrite Hat.
split; [constructor; [exact HJ' | rewrite R2; exact HSP | rewrite R3; exact HGP | rewrite R4; exact HTP
                     | exact HSV | exact HNA]|].
split; [exact Hun|]. split; [exact Hib|]. split; [exact Hrc|].
rewrite R8, R9, R18, R19, R25, R26, R27.
exact (conj H8 (conj H9 (conj H18 (conj H19 (conj H25 (conj H26 (conj H27 (conj Hs0 (conj Hs8 Hs16))))))))).
Qed.

(* the cut facts at the return of a refuse call of pass i: the journal and the registers refuse keeps,
   cross_check's own frame above refuse's entry sp (cc_own_frame_kept), the facts of cc_un (cc_un_after), and
   the record refuse's post gives *)
Lemma cc2_after_call : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regsc : bvmap 5 word) mdc ly4 S4 W4 regs4 mem4 md4 (R : rconf),
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  0 <= STK_REF ->
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  getr regsc 2 = getr regs3 2 -> getr regsc 3 = getr regs3 3 -> getr regsc 4 = getr regs3 4 ->
  getr regsc 8 = getr regs3 8 -> getr regsc 9 = getr regs3 9 -> getr regsc 18 = getr regs3 18 ->
  getr regsc 19 = getr regs3 19 -> getr regsc 25 = getr regs3 25 -> getr regsc 26 = getr regs3 26 ->
  getr regsc 27 = getr regs3 27 ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly4 S4 W4 mem4 md4 (0 + EV_refuse) ->
  ajournal SEGS B STK_REF (cc_sp0 v + -128) (refuse_W (x_c v) (cc_at v i)) ly3 S3 W3 mem3 mdc []
    ly4 S4 W4 mem4 md4 EV_refuse ->
  aregs_preserved regsc regs4 ->
  sa_rconf (aview SEGS (w_H W4) mem4) (x_c v) R -> sa_noalloc B ly3 S3 ly4 S4 ->
  cc2_inv B lit gotw guard STK_REF v i R ly4 S4 W4 regs4 mem4 md4.
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc mdc ly4 S4 W4 regs4 mem4 md4 R HRO HSSP HSTK HP HI
  R2 R3 R4 R8 R9 R18 R19 R25 R26 R27 HJ4 HJc HP4 HR4 HNA4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi32 & Hlen & H4096 & Hceil & Hstk).
destruct (sa_rconf_n _ _ _ Hrci) as (_ & _ & Hlen8).
pose proof HP as [HA _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _).
unfold cc_STK in Hslo, Hstk1.
replace (cc_sp0 v + -128) with (cc_sp0 v - 128) in HJc by lia.
assert (KS : forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W4 mem4 a = rdW W3 mem3 a).
{ apply (cc_own_frame_kept B STK_REF v ly3 S3 W3 mem3 mdc ly4 S4 W4 mem4 md4 (cc_at v i) EV_refuse HSTK HJc).
  - intros a Ha. pose proof (refuse_W_in_block _ _ _ Ha) as Hab.
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
  - intros a Ha Hb. unfold cc_sp0 in Hb. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (G : forall r, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) by exact HP4.
split.
{ constructor.
  - exact HJ4.
  - transitivity (getr regsc 2); [exact (G 2 ltac:(unfold acallee_saved; lia)) | rewrite R2; exact HSP].
  - transitivity (getr regsc 3); [exact (G 3 ltac:(unfold acallee_saved; lia)) | rewrite R3; exact HGP].
  - transitivity (getr regsc 4); [exact (G 4 ltac:(unfold acallee_saved; lia)) | rewrite R4; exact HTP].
  - intros j r Hj. assert (Hjl : (j < length cc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cc_saved] in Hjl.
    rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia). exact (HSV j r Hj).
  - exact (sa_noalloc_trans B _ _ _ _ _ _ HNA HNA4). }
split; [exact (cc_un_after B lit gotw guard STK_REF v ly3 S3 W3 mem3 mdc ly4 S4 W4 mem4 md4 (cc_at v i) EV_refuse
  HRO HSSP HP Hun Hlen8 HJc)|].
split; [exact Hib|]. split; [exact HR4|].
split; [transitivity (getr regsc 8); [exact (G 8 ltac:(unfold acallee_saved; lia)) | rewrite R8; exact H8]|].
split; [transitivity (getr regsc 9); [exact (G 9 ltac:(unfold acallee_saved; lia)) | rewrite R9; exact H9]|].
split; [transitivity (getr regsc 18); [exact (G 18 ltac:(unfold acallee_saved; lia)) | rewrite R18; exact H18]|].
split; [transitivity (getr regsc 19); [exact (G 19 ltac:(unfold acallee_saved; lia)) | rewrite R19; exact H19]|].
split; [transitivity (getr regsc 25); [exact (G 25 ltac:(unfold acallee_saved; lia)) | rewrite R25; exact H25]|].
split; [transitivity (getr regsc 26); [exact (G 26 ltac:(unfold acallee_saved; lia)) | rewrite R26; exact H26]|].
split; [transitivity (getr regsc 27); [exact (G 27 ltac:(unfold acallee_saved; lia)) | rewrite R27; exact H27]|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs0|].
split; [rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs8|].
rewrite (cc2_rdword_same (rdW W3 mem3)) by (intros x Hx; apply KS; lia); exact Hs16.
Qed.
End f.
End d.

(* The two refuse calls and the pass itself are in a section opened after the lemmas above are closed: refuse
   returns at some FP state fx1 with fxrel fx fx1, and the rest of the pass is cc2_box_after / cc2_model_after
   taken with (fx := fx1) (PaFx.srr_after_callF lifts their apost_baseF back to the entry's FP state). *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* `jal refuse` of the BOX arm, 0x89900: refuse(c, 0, F_xbox, s->name), through PaFx.cl_callSF (refuse's
   post is apost_baseF); refuse_site_ok_89900 gives refuse_pre, cross_check_r.v the side conditions, and the
   rest of the arm is cc2_box_after at the FP state refuse returned *)
Lemma cc2_call_box : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regsc : bvmap 5 word) mdc,
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xbox = VAL (A_OBJ 73) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  frm0 fx -> cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 mdc 0 ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = false ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = true ->
  getr regsc 1 = Z_to_bv 64 (BASE + CC_RET1) ->
  getr regsc 2 = getr regs3 2 -> getr regsc 3 = getr regs3 3 -> getr regsc 4 = getr regs3 4 ->
  getr regsc 8 = getr regs3 8 -> getr regsc 9 = getr regs3 9 -> getr regsc 18 = getr regs3 18 ->
  getr regsc 19 = getr regs3 19 -> getr regsc 25 = getr regs3 25 -> getr regsc 26 = getr regs3 26 ->
  getr regsc 27 = getr regs3 27 ->
  getr regsc 10 = w64 (x_c v) -> getr regsc 11 = w64 0 -> getr regsc 12 = w64 (lit F_xbox) ->
  getr regsc 13 = w64 (x_c v + 356 * i) ->
  getr regsc 20 = w64 (x_c v + 356 * i) -> getr regsc 21 = w64 (x_c v + 356 * i + 20) ->
  getr regsc 23 = w64 (SHADOW_OFF + (x_c v + 356 * i + 20) / 8) ->
  SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_refuse)) mem3 (seg_rom SEGS)) mdc)
    (cc_post B lit gotw guard STK_REF v).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc mdc HRO HSSP HLB HSTK REF Hfrm HP HEPI HLOOP
  HI HJc Hms Hbox Q1 Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26 Q27 Q10 Q11 Q12 Q13 Q20 Q21 Q23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof Hun as [Hrod3 _ _ Hheap3].
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & _ & Hrci & Hi32 & Hlen & H4096 & Hceil & Hstk).
destruct (sa_rconf_n _ _ _ Hrci) as (_ & _ & Hlen8).
destruct (cc_call_room B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 HP Hfi) as (_ & Hroom & Hnev).
pose proof HP as [HA _ _ Hc64 _ _ _ _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _).
unfold cc_STK in Hslo, Hstk1.
pose proof Hheap3 as (bq & mq & Hinq & Hbq & Hmq).
unfold seg_spec.SEG_C_SIZE in *.
pose proof (req_size_pos mq ltac:(lia)) as [_ Hreq].
assert (Hsp' : spZ regsc = cc_sp0 v - 128).
{ unfold spZ. rewrite Q2, HSP. unfold w64. rewrite unsigned_lit_small by (unfold cc_sp0; lia). reflexivity. }
assert (Hsp : spZ regsc = cc_sp0 v + -128) by lia.
pose proof (pa_val_range (A_OBJ 73)) as V73.
unfold cc_post.
eapply srr_after_callF.
{ apply (cl_callSF B LAWS W3 regsc mem3 (Z_to_bv 64 (BASE + AF_refuse)) (cc_STK STK_REF) (cc_sp0 v) (cc_FP v)
    (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) [] ly3 S3 mdc 0 STK_REF (refuse_W (x_c v) (cc_at v i)) EV_refuse
    (-128) (Z_to_bv 64 (BASE + CC_RET1)) []
    (fun ly' S' W' regs' mem' md' =>
       sa_rconf (aview SEGS (w_H W') mem') (x_c v)
         (SegModel.refuse (cc_at v i) 0 F_xbox [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))]) /\
       sa_noalloc B ly3 S3 ly' S')
    HJc Hsp).
  - reflexivity.
  - lia.
  - exact HSTK.
  - unfold cc_STK. lia.
  - rewrite Q3. exact HGP.
  - rewrite Q4. exact HTP.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold CC_RET1, AF_cross_check; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold CC_RET1, AF_cross_check; lia). unfold CC_RET1, AF_cross_check. lia.
  - replace (cc_sp0 v + -128) with (cc_sp0 v - 128) by lia.
    apply (cc_call_chain B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 regsc HP Hfi Hun);
      [rewrite Q8; exact H8 | exact Hc64].
  - intros HPRE1. eapply SRr_mono.
    + apply (REF fx ly3 S3 W3 regsc mem3 mdc [] (x_c v) 0 (lit F_xbox) 0 (cc_at v i) F_xbox
        [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))] HPRE1 Hrod3 Q10 Hc64 Q11 ltac:(lia) Q12
        ltac:(rewrite HLB; lia)).
      * exact (refuse_site_ok_89900 B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc HP HI Hfrm
          Hms Hbox Q10 Q11 Q12 Q13 Hsp').
      * exact Hroom.
      * exact Hnev.
    + cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact Hf1|].
      split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (cc_refuse_FP_sub v (cc_at v i) a Hlen8 Ha)|].
    pose proof (refuse_W_in_block _ _ _ Ha) as Hab. exists bq, mq. split; [exact Hinq|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in Hab. lia. }
cbv beta. intros fx1 ly4 S4 W4 regs4 mem4 md4 _ Hfx (HJ4 & HJc4 & HP4 & HR4 & HNA4).
assert (G : forall r, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) by exact HP4.
apply (cc2_box_after (fx := fx1) B lit gotw guard STK_REF v i ly4 S4 W4 regs4 mem4 md4 HRO HSSP HP
  (HEPI fx1) (HLOOP fx1 (fxrel_frm0 fx fx1 Hfrm Hfx)) Hms Hbox).
- exact (cc2_after_call B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc mdc ly4 S4 W4 regs4 mem4 md4 _
    HRO HSSP HSTK HP HI Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26 Q27 HJ4 HJc4 HP4 HR4 HNA4).
- rewrite <- Q20. exact (G 20 ltac:(unfold acallee_saved; lia)).
- rewrite <- Q21. exact (G 21 ltac:(unfold acallee_saved; lia)).
- rewrite <- Q23. exact (G 23 ltac:(unfold acallee_saved; lia)).
Qed.

(* `jal refuse` of the MODEL arm, 0x89944: refuse(c, 0, F_xmodel, s->name, s->model); the rest of the arm is
   cc2_model_after at the FP state refuse returned *)
Lemma cc2_call_model : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regsc : bvmap 5 word) mdc,
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 74) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  frm0 fx -> cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 mdc 0 ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = true ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = false ->
  getr regsc 1 = Z_to_bv 64 (BASE + CC_RET2) ->
  getr regsc 2 = getr regs3 2 -> getr regsc 3 = getr regs3 3 -> getr regsc 4 = getr regs3 4 ->
  getr regsc 8 = getr regs3 8 -> getr regsc 9 = getr regs3 9 -> getr regsc 18 = getr regs3 18 ->
  getr regsc 19 = getr regs3 19 -> getr regsc 25 = getr regs3 25 -> getr regsc 26 = getr regs3 26 ->
  getr regsc 27 = getr regs3 27 ->
  getr regsc 10 = w64 (x_c v) -> getr regsc 11 = w64 0 -> getr regsc 12 = w64 (lit F_xmodel) ->
  getr regsc 13 = w64 (x_c v + 356 * i) -> getr regsc 14 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL) ->
  getr regsc 20 = w64 (x_c v + 356 * i) -> getr regsc 21 = w64 (x_c v + 356 * i + 36) ->
  getr regsc 22 = w64 (x_c v + 356 * i + 60) ->
  getr regsc 24 = w64 (SHADOW_OFF + (x_c v + 356 * i + 60) / 8) ->
  SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_refuse)) mem3 (seg_rom SEGS)) mdc)
    (cc_post B lit gotw guard STK_REF v).
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc mdc HRO HSSP HLM HSTK REF Hfrm HP HEPI HLOOP
  HI HJc Hms Hbox Q1 Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26 Q27 Q10 Q11 Q12 Q13 Q14 Q20 Q21 Q22 Q24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
pose proof Hun as [Hrod3 _ _ Hheap3].
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & _ & Hrci & Hi32 & Hlen & H4096 & Hceil & Hstk).
destruct (sa_rconf_n _ _ _ Hrci) as (_ & _ & Hlen8).
destruct (cc_call_room B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 HP Hfi) as (_ & Hroom & Hnev).
pose proof HP as [HA _ _ Hc64 _ _ _ _ _ _ _ _ _ _].
pose proof HA as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & Hstk1 & Hceil2 & Hslo & Hshi & H47 & _).
unfold cc_STK in Hslo, Hstk1.
pose proof Hheap3 as (bq & mq & Hinq & Hbq & Hmq).
unfold seg_spec.SEG_C_SIZE in *.
pose proof (req_size_pos mq ltac:(lia)) as [_ Hreq].
assert (Hsp' : spZ regsc = cc_sp0 v - 128).
{ unfold spZ. rewrite Q2, HSP. unfold w64. rewrite unsigned_lit_small by (unfold cc_sp0; lia). reflexivity. }
assert (Hsp : spZ regsc = cc_sp0 v + -128) by lia.
pose proof (pa_val_range (A_OBJ 74)) as V74.
unfold cc_post.
eapply srr_after_callF.
{ apply (cl_callSF B LAWS W3 regsc mem3 (Z_to_bv 64 (BASE + AF_refuse)) (cc_STK STK_REF) (cc_sp0 v) (cc_FP v)
    (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) [] ly3 S3 mdc 0 STK_REF (refuse_W (x_c v) (cc_at v i)) EV_refuse
    (-128) (Z_to_bv 64 (BASE + CC_RET2)) []
    (fun ly' S' W' regs' mem' md' =>
       sa_rconf (aview SEGS (w_H W') mem') (x_c v)
         (SegModel.refuse (cc_at v i) 0 F_xmodel
            [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d));
             AS (rs_model (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))]) /\
       sa_noalloc B ly3 S3 ly' S')
    HJc Hsp).
  - reflexivity.
  - lia.
  - exact HSTK.
  - unfold cc_STK. lia.
  - rewrite Q3. exact HGP.
  - rewrite Q4. exact HTP.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold CC_RET2, AF_cross_check; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold CC_RET2, AF_cross_check; lia). unfold CC_RET2, AF_cross_check. lia.
  - replace (cc_sp0 v + -128) with (cc_sp0 v - 128) by lia.
    apply (cc_call_chain B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 regsc HP Hfi Hun);
      [rewrite Q8; exact H8 | exact Hc64].
  - intros HPRE1. eapply SRr_mono.
    + apply (REF fx ly3 S3 W3 regsc mem3 mdc [] (x_c v) 0 (lit F_xmodel) 0 (cc_at v i) F_xmodel
        [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d));
         AS (rs_model (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))] HPRE1 Hrod3 Q10 Hc64 Q11 ltac:(lia) Q12
        ltac:(rewrite HLM; lia)).
      * exact (refuse_site_ok_89944 B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc HP HI Hfrm
          Hms Hbox Q10 Q11 Q12 Q13 Q14 Hsp').
      * exact Hroom.
      * exact Hnev.
    + cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact Hf1|].
      split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (cc_refuse_FP_sub v (cc_at v i) a Hlen8 Ha)|].
    pose proof (refuse_W_in_block _ _ _ Ha) as Hab. exists bq, mq. split; [exact Hinq|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in Hab. lia. }
cbv beta. intros fx1 ly4 S4 W4 regs4 mem4 md4 _ Hfx (HJ4 & HJc4 & HP4 & HR4 & HNA4).
assert (G : forall r, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) by exact HP4.
apply (cc2_model_after (fx := fx1) B lit gotw guard STK_REF v i ly4 S4 W4 regs4 mem4 md4 HRO HSSP HP
  (HEPI fx1) (HLOOP fx1 (fxrel_frm0 fx fx1 Hfrm Hfx)) Hms Hbox).
- exact (cc2_after_call B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regsc mdc ly4 S4 W4 regs4 mem4 md4 _
    HRO HSSP HSTK HP HI Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q25 Q26 Q27 HJ4 HJc4 HP4 HR4 HNA4).
- rewrite <- Q20. exact (G 20 ltac:(unfold acallee_saved; lia)).
- rewrite <- Q21. exact (G 21 ltac:(unfold acallee_saved; lia)).
- rewrite <- Q22. exact (G 22 ltac:(unfold acallee_saved; lia)).
- rewrite <- Q24. exact (G 24 ltac:(unfold acallee_saved; lia)).
Qed.

(* a register the head run kept: its value at the stop is the cut's (Ek agrees with E below 1024) *)
Ltac cc2_req HS EF EE :=
  lazymatch goal with |- getr _ ?r = getr _ _ =>
    let Q := fresh "Q" in prreg HS r Q;
    lazymatch type of Q with _ = ew _ ?n => rewrite Q, (EF n ltac:(lia)), (EE n r eq_refl); reflexivity end end.
(* a register whose value is SOff 32 k, the address of seg[i] plus k *)
Ltac cc2_sv HS EF E32 U32 :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q, (EF 32%nat ltac:(lia)); rewrite ?U32, ?E32; reflexivity end.
(* the symbolic value of a register at a stop, unreduced *)
Ltac cc2_rawreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

(* S2: one pass of the loop, from the head 0x89874 of pass i *)
Theorem cc_s2 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z),
  PALib B -> PALibF B -> seg_val_objs -> seg_sig_prog ->
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 74) -> lit F_xbox = VAL (A_OBJ 73) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S2P B lit gotw guard STK_REF.
Proof.
intros B lit gotw guard STK_REF TL TLF HVO HSG HRRO HSSP HLM HLB HSTK REF.
intros v i Hfrm HP HEPI HLOOP. unfold from_LOOP, cc_from. intros ly3 S3 W3 regs3 mem3 md3 HI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (cc2_seed B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HLM HLB HP HI) as HS.
pose proof HI as (Hfi & Hun & Hib & Hrc & H8 & H9 & H18 & H19 & H25 & H26 & H27 & Hs0 & Hs8 & Hs16).
pose proof Hfi as [HJ HSP HGP HTP HSV HNA].
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi32 & Hlen & H4096 & Hceil & Hstk).
pose proof (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (_ & _ & _ & HRA & _).
destruct (sa_rconf_fields _ _ _ _ Hrci Hlen) as (_ & _ & _ & _ & _ & Hrole31 & _ & _).
unfold seg_spec.SEG_C_SIZE in Hceil, HRA.
set (s := nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) in *.
remember (Eimg (Ereg regs3 (cc2_extra (x_c v) i s (cc_n v)))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (cc2_extra (x_c v) i s (cc_n v)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth cc2_extra map] in E32, E33, E34, E35. clear EX.
assert (UB : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia]).
assert (U32 : bv_unsigned (ew E 32) = x_c v + 356 * i) by (rewrite E32; apply unsigned_lit_small; lia).
(* every inline check of the tests (2, 3, 4) reads a field of seg[i] inside the live block: its obligation is
   the block's shadow, read off AR at the cut *)
assert (OBL : forall E' (k n : Z), ew E' 32 = ew E 32 -> ew E' 18 = ew E 18 -> 0 <= k -> 0 <= n -> k + n <= 64 ->
  ob_holds SEGS (SOff 18 0) E' (mrestrict (w_H W3) mem3) (mkOB (SOff 32 k) n)).
{ intros E' k n H32' H18' Hk Hn Hkn. unfold ob_holds. cbn [ob_x ob_n].
  assert (UB' : U E' (SOff 18 0) = SHADOW_OFF) by (rewrite <- UB; unfold U; cbn [sv_denot]; rewrite H18'; reflexivity).
  assert (UK : U E' (SOff 32 k) = x_c v + 356 * i + k)
    by (rewrite U_SOff, H32', U32; apply zcanon_id; unfold M64; lia).
  rewrite UK. apply (obl_of_range SEGS (w_H W3) mem3 E' (SOff 18 0) _ n (x_c v) 16616 HRA UB'); lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) mem3)) by constructor.
unfold cfg_at. change (w64 (BASE + CC_LOOP)) with (Z_to_bv 64 (BASE + CC_LOOP)).
(* run 1, 0x89874 .. 0x8989c: the two UBSan trap tests 0x89878 / 0x8987c decided not taken by the executor from
   the atom facts of i, ~c and 356 i; s4 = c + 356 i (the alias); check 2; role_set loaded; stop at `beqz a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply OBL; [reflexivity | reflexivity | lia | lia | lia]. }
{ cc2_awr_ro. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
assert (M1 : ms_mem ms1 = mem3) by (eapply cc2_frame_ro; [| exact HF1]; vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (E1F : forall k, (k < 1024)%nat -> ew E1 k = ew E k)
  by (intros k Hk; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
clearbody E1.
assert (LT1 : branch_taken BC_EQ (sv_denot E1 (SOff 34 0)) (sv_denot E1 (SLit 0)) = negb (rs_role_set s))
  by (apply cc2_br1; rewrite E1F by lia; exact E34).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* role_set = 0: is_box = 0 *)
  rewrite LT1 in Hc. apply negb_true_iff in Hc. rename Hc into Hrs.
  (* run 2A, 0x898c0 .. 0x898e4: check 4, model_set loaded, a2 formed; stop at `beqz a2` *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rewrite M1. apply OBL; [rewrite E1F by lia; reflexivity | rewrite E1F by lia; reflexivity | lia | lia | lia]. }
  { cc2_awr_ro. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (M2 : ms_mem ms2 = mem3) by (rewrite <- M1; eapply cc2_frame_ro; [| exact HF2]; vm_compute; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E2 := Ex) in * end.
  assert (E2F : forall k, (k < 1024)%nat -> ew E2 k = ew E k)
    by (intros k Hk; unfold E2; rewrite ?ew_ewset_other by lia; apply E1F; exact Hk).
  clearbody E2.
  assert (LT2 : branch_taken BC_EQ
      (sv_denot E2 (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SOff 34 0)) (SLit 1)))
      (sv_denot E2 (SLit 0)) = negb (negb (rs_model_set s) || rs_role_set s))
    by (apply cc2_br2A; rewrite E2F by lia; assumption).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a2 = 0: model_set = 1, the MODEL arm *)
    assert (Hms : rs_model_set s = true)
      by (revert Hc; rewrite LT2, Hrs; destruct (rs_model_set s); cbn; intros Hc; [reflexivity | discriminate Hc]).
    clear Hc.
    assert (Hbx : rs_role_set s && (rs_role s =? 4) = false) by (rewrite Hrs; reflexivity).
    (* run 3, 0x8992c .. 0x89944: s5 = s4 + 36, the arguments; stop at `jal refuse` *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { cc2_awr_ro. }
    rename HF into HF3, HFr into HFr3, HG into HG3.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into ms3 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3' := mm) in *; clearbody md3' end.
    assert (M3 : ms_mem ms3 = mem3) by (rewrite <- M2; eapply cc2_frame_ro; [| exact HF3]; vm_compute; reflexivity).
    lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in * end.
    assert (E3F : forall k, (k < 1024)%nat -> ew E3 k = ew E k)
      by (intros k Hk; unfold E3; rewrite ?ew_ewset_other by lia; apply E2F; exact Hk).
    clearbody E3.
    pmkst HS.
    rewrite (HSG SS_refuse ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
    change (seg_af SS_refuse) with AF_refuse. rewrite M3. rewrite M3 in HJ.
    apply (cc2_call_model B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 (ms_regs ms3) md3' HRRO HSSP HLM
      HSTK REF Hfrm HP HEPI HLOOP HI HJ Hms Hbx).
    { prreg HS (1%bv : bv 5) Q. exact Q. }
    1-10: cc2_req HS E3F EE.
    { prreg HS (10%bv : bv 5) Q. rewrite Q, (E3F 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl). exact H8. }
    { prreg HS (11%bv : bv 5) Q. rewrite Q. reflexivity. }
    { prreg HS (12%bv : bv 5) Q. rewrite Q.
      lazymatch goal with HI3 : img_env _ _ E3 |- _ =>
        rewrite <- (Z_to_bv_bv_unsigned 64 (ew E3 315%nat)), (HI3 315%nat ltac:(unfold A_TEXT, A_LIM; lia)) end.
      rewrite HLM. reflexivity. }
    1-5: cc2_sv HS E3F E32 U32.
    { cc2_rawreg HS (24%bv : bv 5) Q.
      rewrite (denot_shx E3 32 18 60 (x_c v + 356 * i) SB) in Q;
        [exact Q | rewrite E3F by lia; exact E32 | rewrite E3F, (EE 18%nat 18%bv eq_refl) by lia; exact H18
        | lia | lia | lia | unfold SB; lia]. }
  + (* a2 <> 0: model_set = 0 *)
    assert (Hms : rs_model_set s = false)
      by (revert Hc; rewrite LT2, Hrs; destruct (rs_model_set s); cbn; intros Hc; [discriminate Hc | reflexivity]).
    clear Hc.
    (* run 3, 0x898e8 .. 0x898ec: a0 = not model_set & role_set; stop at `beqz a0` *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { cc2_awr_ro. }
    rename HF into HF3, HFr into HFr3, HG into HG3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms3 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3' := mm) in *; clearbody md3' end.
    assert (M3 : ms_mem ms3 = mem3) by (rewrite <- M2; eapply cc2_frame_ro; [| exact HF3]; vm_compute; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in * end.
    assert (E3F : forall k, (k < 1024)%nat -> ew E3 k = ew E k)
      by (intros k Hk; unfold E3; rewrite ?ew_ewset_other by lia; apply E2F; exact Hk).
    clearbody E3.
    assert (LT3 : branch_taken BC_EQ (sv_denot E3 (SAlu ALU_AND (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SOff 34 0)))
        (sv_denot E3 (SLit 0)) = negb (negb (rs_model_set s) && rs_role_set s))
      by (apply cc2_br3A; rewrite E3F by lia; assumption).
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* a0 = 0: neither arm, to the latch; the record is unchanged *)
      assert (Hkeep : (rs_model_set s = false /\ rs_role_set s && (rs_role s =? 4) = false) \/
                      (rs_model_set s = true /\ rs_role_set s && (rs_role s =? 4) = true))
        by (left; split; [exact Hms | rewrite Hrs; reflexivity]).
      paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LATCH.
      { cc2_awr_ro. }
      rename HF into HF4, HFr into HFr4, HG into HG4.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms4 end.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
      assert (M4 : ms_mem ms4 = mem3) by (rewrite <- M3; eapply cc2_frame_ro; [| exact HF4]; vm_compute; reflexivity).
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in * end.
      assert (E4F : forall k, (k < 1024)%nat -> ew E4 k = ew E k)
        by (intros k Hk; unfold E4; rewrite ?ew_ewset_other by lia; apply E3F; exact Hk).
      clearbody E4.
      pmkst HS.
      change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) (ms_regs ms4) (ms_mem ms4) md4)
        (cc_post B lit gotw guard STK_REF v)).
      rewrite M4. rewrite M4 in HJ.
      apply (cc2_latch B lit gotw guard STK_REF v i ly3 S3 W3 (ms_regs ms4) mem3 md4 HP (HEPI fx) (HLOOP fx Hfrm)).
      apply (cc2_keep_inv B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 (ms_regs ms4) md4 HI HJ).
      1-10: cc2_req HS E4F EE.
      apply r_cross_seg_keep. exact Hkeep.
    * (* a0 <> 0 would need role_set = 1 *)
      rewrite LT3, Hms, Hrs in Hc. cbn in Hc. discriminate Hc.
- (* role_set = 1: is_box = (role = BOX) *)
  rewrite LT1 in Hc. apply negb_false_iff in Hc. rename Hc into Hrs.
  (* run 2B, 0x898a0 .. 0x898e4: check 3, role loaded, is_box, check 4, model_set, a2; stop at `beqz a2` *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rewrite M1. apply OBL; [rewrite E1F by lia; reflexivity | rewrite E1F by lia; reflexivity | lia | lia | lia]. }
  { rewrite M1. apply OBL; [rewrite E1F by lia; reflexivity | rewrite E1F by lia; reflexivity | lia | lia | lia]. }
  { cc2_awr_ro. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms2 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  assert (M2 : ms_mem ms2 = mem3) by (rewrite <- M1; eapply cc2_frame_ro; [| exact HF2]; vm_compute; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E2 := Ex) in * end.
  assert (E2F : forall k, (k < 1024)%nat -> ew E2 k = ew E k)
    by (intros k Hk; unfold E2; rewrite ?ew_ewset_other by lia; apply E1F; exact Hk).
  clearbody E2.
  assert (LT2 : branch_taken BC_EQ
      (sv_denot E2 (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 35 0) (SLit 1))
         (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))) (SLit 1)))
      (sv_denot E2 (SLit 0)) = negb (negb (rs_model_set s) || (rs_role s =? 4)))
    by (apply cc2_br2B; [rewrite E2F by lia; exact E33 | exact Hrole31 | rewrite E2F by lia; exact E35]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a2 = 0: model_set = 1 and role <> BOX, the MODEL arm *)
    assert (Hms : rs_model_set s = true /\ (rs_role s =? 4) = false)
      by (revert Hc; rewrite LT2; destruct (rs_model_set s), (rs_role s =? 4); cbn; intros Hc;
          first [split; reflexivity | discriminate Hc]).
    destruct Hms as [Hms Hr4]. clear Hc.
    assert (Hbx : rs_role_set s && (rs_role s =? 4) = false) by (rewrite Hrs, Hr4; reflexivity).
    paj_run_tok RUN HS HJ SHOK Bspan.
    { cc2_awr_ro. }
    rename HF into HF3, HFr into HFr3, HG into HG3.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into ms3 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3' := mm) in *; clearbody md3' end.
    assert (M3 : ms_mem ms3 = mem3) by (rewrite <- M2; eapply cc2_frame_ro; [| exact HF3]; vm_compute; reflexivity).
    lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in * end.
    assert (E3F : forall k, (k < 1024)%nat -> ew E3 k = ew E k)
      by (intros k Hk; unfold E3; rewrite ?ew_ewset_other by lia; apply E2F; exact Hk).
    clearbody E3.
    pmkst HS.
    rewrite (HSG SS_refuse ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
    change (seg_af SS_refuse) with AF_refuse. rewrite M3. rewrite M3 in HJ.
    apply (cc2_call_model B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 (ms_regs ms3) md3' HRRO HSSP HLM
      HSTK REF Hfrm HP HEPI HLOOP HI HJ Hms Hbx).
    { prreg HS (1%bv : bv 5) Q. exact Q. }
    1-10: cc2_req HS E3F EE.
    { prreg HS (10%bv : bv 5) Q. rewrite Q, (E3F 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl). exact H8. }
    { prreg HS (11%bv : bv 5) Q. rewrite Q. reflexivity. }
    { prreg HS (12%bv : bv 5) Q. rewrite Q.
      lazymatch goal with HI3 : img_env _ _ E3 |- _ =>
        rewrite <- (Z_to_bv_bv_unsigned 64 (ew E3 315%nat)), (HI3 315%nat ltac:(unfold A_TEXT, A_LIM; lia)) end.
      rewrite HLM. reflexivity. }
    1-5: cc2_sv HS E3F E32 U32.
    { cc2_rawreg HS (24%bv : bv 5) Q.
      rewrite (denot_shx E3 32 18 60 (x_c v + 356 * i) SB) in Q;
        [exact Q | rewrite E3F by lia; exact E32 | rewrite E3F, (EE 18%nat 18%bv eq_refl) by lia; exact H18
        | lia | lia | lia | unfold SB; lia]. }
  + (* a2 <> 0 *)
    assert (H2 : (negb (rs_model_set s) || (rs_role s =? 4)) = true)
      by (revert Hc; rewrite LT2; intros Hc; apply negb_false_iff in Hc; exact Hc).
    clear Hc.
    (* run 3, 0x898e8 .. 0x898ec: a0 = not model_set & is_box; stop at `beqz a0` *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { cc2_awr_ro. }
    rename HF into HF3, HFr into HFr3, HG into HG3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms3 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3' := mm) in *; clearbody md3' end.
    assert (M3 : ms_mem ms3 = mem3) by (rewrite <- M2; eapply cc2_frame_ro; [| exact HF3]; vm_compute; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in * end.
    assert (E3F : forall k, (k < 1024)%nat -> ew E3 k = ew E k)
      by (intros k Hk; unfold E3; rewrite ?ew_ewset_other by lia; apply E2F; exact Hk).
    clearbody E3.
    assert (LT3 : branch_taken BC_EQ
        (sv_denot E3 (SAlu ALU_AND (SAlu ALU_SLTU (SOff 35 0) (SLit 1)) (SAlu ALU_SLTU (SOff 33 (-4)) (SLit 1))))
        (sv_denot E3 (SLit 0)) = negb (negb (rs_model_set s) && (rs_role s =? 4)))
      by (apply cc2_br3B; [rewrite E3F by lia; exact E33 | exact Hrole31 | rewrite E3F by lia; exact E35]).
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* a0 = 0: neither arm, to the latch; the record is unchanged *)
      assert (H3 : (negb (rs_model_set s) && (rs_role s =? 4)) = false)
        by (revert Hc; rewrite LT3; intros Hc; apply negb_true_iff in Hc; exact Hc).
      assert (Hkeep : (rs_model_set s = false /\ rs_role_set s && (rs_role s =? 4) = false) \/
                      (rs_model_set s = true /\ rs_role_set s && (rs_role s =? 4) = true))
        by (rewrite Hrs; revert H2 H3; destruct (rs_model_set s), (rs_role s =? 4); cbn; intros H2 H3;
            first [left; split; reflexivity | right; split; reflexivity | discriminate H2 | discriminate H3]).
      paj_run_to_tok RUNTO HS HJ SHOK Bspan CC_LATCH.
      { cc2_awr_ro. }
      rename HF into HF4, HFr into HFr4, HG into HG4.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) => rename mx into ms4 end.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
      assert (M4 : ms_mem ms4 = mem3) by (rewrite <- M3; eapply cc2_frame_ro; [| exact HF4]; vm_compute; reflexivity).
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in * end.
      assert (E4F : forall k, (k < 1024)%nat -> ew E4 k = ew E k)
        by (intros k Hk; unfold E4; rewrite ?ew_ewset_other by lia; apply E3F; exact Hk).
      clearbody E4.
      pmkst HS.
      change (SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) (ms_regs ms4) (ms_mem ms4) md4)
        (cc_post B lit gotw guard STK_REF v)).
      rewrite M4. rewrite M4 in HJ.
      apply (cc2_latch B lit gotw guard STK_REF v i ly3 S3 W3 (ms_regs ms4) mem3 md4 HP (HEPI fx) (HLOOP fx Hfrm)).
      apply (cc2_keep_inv B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 (ms_regs ms4) md4 HI HJ).
      1-10: cc2_req HS E4F EE.
      apply r_cross_seg_keep. exact Hkeep.
    * (* a0 <> 0: model_set = 0 and role = BOX, the BOX arm *)
      assert (Hb : rs_model_set s = false /\ (rs_role s =? 4) = true)
        by (revert Hc; rewrite LT3; destruct (rs_model_set s), (rs_role s =? 4); cbn; intros Hc;
            first [split; reflexivity | discriminate Hc]).
      destruct Hb as [Hms Hr4].
      assert (Hbx : rs_role_set s && (rs_role s =? 4) = true) by (rewrite Hrs, Hr4; reflexivity).
      (* run 4, 0x898f0 .. 0x89900: the arguments, a2 = [sp + 8] = F_xbox; stop at `jal refuse` *)
      paj_run_tok RUN HS HJ SHOK Bspan.
      { cc2_awr_ro. }
      rename HF into HF4, HFr into HFr4, HG into HG4.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => rename mx into ms4 end.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
      assert (M4 : ms_mem ms4 = mem3) by (rewrite <- M3; eapply cc2_frame_ro; [| exact HF4]; vm_compute; reflexivity).
      lazymatch type of HS with st_ok _ ?Ex _ _ => set (E4 := Ex) in * end.
      assert (E4F : forall k, (k < 1024)%nat -> ew E4 k = ew E k)
        by (intros k Hk; unfold E4; rewrite ?ew_ewset_other by lia; apply E3F; exact Hk).
      clearbody E4.
      pmkst HS.
      rewrite (HSG SS_refuse ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
      change (seg_af SS_refuse) with AF_refuse. rewrite M4. rewrite M4 in HJ.
      apply (cc2_call_box B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 (ms_regs ms4) md4 HRRO HSSP HLB
        HSTK REF Hfrm HP HEPI HLOOP HI HJ Hms Hbx).
      { prreg HS (1%bv : bv 5) Q. exact Q. }
      1-10: cc2_req HS E4F EE.
      { prreg HS (10%bv : bv 5) Q. rewrite Q, (E4F 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl). exact H8. }
      { prreg HS (11%bv : bv 5) Q. rewrite Q. reflexivity. }
      { prreg HS (12%bv : bv 5) Q. rewrite Q.
        lazymatch goal with HI4 : img_env _ _ E4 |- _ =>
          rewrite <- (Z_to_bv_bv_unsigned 64 (ew E4 314%nat)), (HI4 314%nat ltac:(unfold A_TEXT, A_LIM; lia)) end.
        rewrite HLB. reflexivity. }
      1-3: cc2_sv HS E4F E32 U32.
      { cc2_rawreg HS (23%bv : bv 5) Q.
        rewrite (denot_shx E4 32 18 20 (x_c v + 356 * i) SB) in Q;
          [exact Q | rewrite E4F by lia; exact E32 | rewrite E4F, (EE 18%nat 18%bv eq_refl) by lia; exact H18
          | lia | lia | lia | unfold SB; lia]. }
Qed.
End f2.
End d2.
