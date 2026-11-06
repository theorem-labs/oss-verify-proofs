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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 576 of its 618 lines of code are new or changed and 248 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0HdB.v at 49b53fe65a85 for reac-pw/fuzz_rate's image A: module paths changed (images.Asan in place of lib/A/Img0, the RtPg files in place of the RPg files); the pcs, the registers (the shadow base s4 = x20, the cursor s9 = x25, what is left after the kind byte s8 = x24, in.n in the register s10 = x26, &ch in s6 = x22, the `v / 10` multiplier in t2 = x7, the token base s2 = x18) and the code of the six blocks are rate's (rate writes no real-frame cell in the head: the real frame is a read-only region holding [R+0x90] and [R+0x98]; the a5 test of the reads is on the register); the AR laws come from the kernel theorem AR_laws_ok in place of a Section hypothesis; kept_run is RtPgW7bBase.w7_kept_run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0HdB.v, with its module paths, module names, addresses and numbers changed; 390 of its 602 lines of code are new or changed and 406 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0HdB.v at 97ea9c9eafa; restated for
   reac-pw/fuzz_headamp's image B: every block re-walked on image B's code (its UBSan cursor tests `bltu a6,x+1`,
   its registers, R+0x110 for the cursor after c and p, t1 for what is left), image B's class-4 frame (1024 bytes,
   128 shadow bytes), the shadow base atom s11 = x27, and the posts in lib/AU/HPgCaseB.v's cb_post form. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block lemmas of the
   head of ent_build's case 0 in LLVMFuzzerTestOneInput 0x80c40 (pod.h:224-236), from D = 0x8194c and D0E = 0x819c0
   to the two arms DIG = 0x81a1c and ODD = 0x82318 (lib/AU/HPgE0Def.v). Proves no function (kind: segment lemma).

   THE SPLIT. A run that stores a shadow byte (the scope stores of t and ch) is a plain engine run with the frame's
   shadow row writable; a run that passes an instrumented check (the two reads of the input cursor) is a token run
   (lib/Reusable/YCbn.v) with the row absent. So the head is six blocks, each from a fixed pc to a fixed pc in the
   shape HPgCaseB.cb_post (the journal at the block's start state, the I/O state, the registers outside clob, every
   byte outside the write set, presence kept, and a relation of the result):
     eh_T1  0x8194c -> 0x81980  plain: the twelve t stores (shadow F + 4 .. 15 := 0), `beqz s4` not taken (s4 >= 1)
     eh_T0  0x8194c -> 0x81a1c  plain, s4 = 0: the t stores, `beqz s4` taken to 0x82294 (s5 := s2, j 0x819f4),
                                t3 := 9, t1 := 0, s10 := 0, a3 := 0, the three ch stores (F + 20 .. 22),
                                R+0x110 := s5, s2 := [R+0xc8], t0 := 4
     eh_TE  0x819c0 -> 0x81a1c  plain: the t stores, t2 := 10, then as eh_T0 from 0x819f4
     eh_K1  0x81980 -> 0x822fc  token, one byte left: the UBSan test `bltu a6,s2+1` (a6 = 1), the check of the
                                cursor (slow block 0x827c4), a3 := c, a0 := a7 + 2, t3 := 9, `bne t1,2` not taken,
                                R+0x110 := a0, t1 := 0, s10 := 0
     eh_K2  0x81980 -> 0x822fc  token, two bytes or more: the same read, `bne` taken to 0x822d0, the UBSan test of
                                a0 + 1, the check of the second byte (slow block 0x82868), s10 := p,
                                t1 := t1 - 3, R+0x110 := a7 + 3
     eh_C   0x822fc -> 0x81a1c / 0x82318  plain: the three ch stores, s2 := [R+0xc8], t0 := 4, `bgeu 0xc7,a3`:
                                c < 200 to DIG, c >= 200 to ODD
   THE ENGINE STATES (image B's registers). Atom 19 = s3 = shadow_addr F bases the row's two regions, t's twelve
   bytes [4, 16) and ch's three [20, 23), each its own write window; atom 9 = s1 = R bases the real frame's cells:
   R+0xc8 = F + 0xa0 = &ch (env slot 32) and the write window [R+0x110, R+0x118) of the cursor cell; atom 17 = a7,
   the kind byte's address, bases the input bytes c (slot 32) and p (slot 33), read-only, and s2 (x18) is seated as
   a7 + 1, a6 (x16) as 1 and, with one byte left, t1 (x6) as 2. The token runs use the shadow base s11 = K itself
   (HPgE0Base.E0Bx = SOff 27 0), know R in [2^46, 2^47] (so the cursor cell's window is apart from the shadow band)
   and a7 below a closed bound, and leave one obligation per input read: range_addressable of that byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0Def HPgE0Base HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition EH_D : Z := 0x8194c.
Definition EH_D0E : Z := 0x819c0.
Definition EH_K : Z := 0x81980.     (* the first read of the cursor *)
Definition EH_CH : Z := 0x822fc.    (* the ch stores after the reads *)

(* ======================================== the engine states ======================================== *)
Definition eh_rT : YP09.region := YP09.mkRegion (Some 19%nat) 4 16 4 16 [].
Definition eh_rCh : YP09.region := YP09.mkRegion (Some 19%nat) 20 23 20 23 [].
(* the real frame: &ch at R+0xc8 and the cursor cell [R+0x110, R+0x118) *)
Definition eh_rRw : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xc8 0x118 0x110 0x118 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition eh_rRc : YP09.region := YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0 0 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition eh_rRk : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0x110 0x118 [].
(* the input bytes after the kind byte, based at a7 = the kind byte's address *)
Definition eh_rIn1 : YP09.region := YP09.mkRegion (Some 17%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition eh_rIn2 : YP09.region :=
YP09.mkRegion (Some 17%nat) 1 3 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0)); YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
(* the token runs' facts: s11 = K, a7 below a closed bound, R in [2^46, 2^47] and 32-aligned *)
Definition eh_fK (a7hi : Z) : list (nat * afact) :=
[(27%nat, mkAF E0SB E0SB 0); (17%nat, mkAF 0 a7hi 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)].

Definition ss_T1 : sstate :=
mkSS EH_D sr_atoms [eh_rT] None (mkFacts [(20%nat, mkAF 1 (2 ^ 63) 0)] [] []).
Definition ss_T0 : sstate := mkSS EH_D sr_atoms [eh_rT; eh_rCh; eh_rRw] None (mkFacts [] [] []).
Definition ss_TE : sstate := mkSS EH_D0E sr_atoms [eh_rT; eh_rCh; eh_rRw] None (mkFacts [] [] []).
Definition ss_K1 : sstate := mkSS EH_K sr_atoms [eh_rRk; eh_rIn1] None (mkFacts (eh_fK (2 ^ 47 - 3)) [] []).
Definition ss_K2 : sstate :=
mkSS EH_K sr_atoms [eh_rRk; eh_rIn2] None (mkFacts ((6%nat, mkAF 3 (2 ^ 47 + 1) 0) :: eh_fK (2 ^ 47 - 4)) [] []).
Definition ss_C (odd : bool) : sstate :=
mkSS EH_CH sr_atoms [eh_rCh; eh_rRc] None (mkFacts [(13%nat, if odd then mkAF 200 255 0 else mkAF 0 199 0)] [] []).

(* ======================================== the write sets ======================================== *)
Definition eh_wT (F : Z) : Z -> Prop := fun a => shadow_addr F + 4 <= a < shadow_addr F + 16.
Definition eh_wCh (F : Z) : Z -> Prop := fun a => shadow_addr F + 20 <= a < shadow_addr F + 23.
Definition eh_wN (R : Z) : Z -> Prop := fun a => R + 0x110 <= a < R + 0x118.
Definition eh_wTCN (R F : Z) : Z -> Prop := fun a => eh_wT F a \/ eh_wCh F a \/ eh_wN R a.

Lemma eh_sF : forall F, 4096 <= F -> F + 1024 <= 2 ^ 47 ->
0x7fff8000 + 512 <= shadow_addr F /\ shadow_addr F + 128 <= 0x7fff8000 + 2 ^ 44.
Proof.
intros F H0 H1. unfold shadow_addr, SHADOW_OFF.
assert (512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the row's bytes j .. j + n - 1 hold 0 *)
Definition eh_zero (W : world rsegs) (mem : word -> option byte) (F j n : Z) : Prop :=
forall i, j <= i < j + n -> aview rsegs (w_H W) mem (shadow_addr F + i) = Some 0.

(* ======================================== engine helpers ======================================== *)
Lemma eh_val_at : forall E ss H ms i n lo hi wlo whi cs b off (w : N) e v a (wn : nat),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + off -> wn = N.to_nat w ->
val_mem rsegs (mrestrict H (ms_mem ms)) a wn v.
Proof.
intros E ss H ms i n lo hi wlo whi cs b off w e v a wn HS Hi Hb Hc He Hv Hw -> ->.
exact (e0_field E _ n b cs lo hi wlo whi off w e v (st_ok_region_at E ss (restrict H ms) i _ HS Hi) Hb Hc He Hv Hw).
Qed.
Lemma eh_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.
Lemma eh_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma eh_denot_ext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SExt, (U_atom E n v H ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. rewrite Z.mod_small by lia.
reflexivity.
Qed.
Lemma eh_ew_reg : forall regs ex n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
ew (Ereg regs ex) n = Z_to_bv 64 v.
Proof. intros regs ex n r v Hn H. rewrite (ew_Ereg_nat regs ex n r Hn), H. reflexivity. Qed.
Lemma eh_unsigned : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma eh_aview0 : forall H mem x, val_mem rsegs (mrestrict H mem) x (N.to_nat 1) 0 -> aview rsegs H mem x = Some 0.
Proof. intros H mem x V. apply (hm_val1_aview rsegs H mem x 0); [exact V | lia]. Qed.

(* a register of the final state *)
Ltac eh_reg HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  rewrite (st_ok_restrict_reg rsegs _ _ ssf _ r HS);
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* a chunk of region i of the final state at offset off; leaves the base, the value, its range *)
Ltac eh_chunk HS i off :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let r := eval vm_compute in (nth_error (ss_mem ssf) i) in
  lazymatch r with Some (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    eapply (eh_val_at _ ssf _ _ i n lo hi wlo whi cs _ off);
    [exact HS | vm_compute; reflexivity | | cbn [In]; repeat (first [left; reflexivity | right]) | | | cbn; lia | | ] end end.
(* every byte j .. j + n - 1 of region i (based at the row, EB : its base) holds the 0 a scope store wrote *)
Ltac eh_zero_tac HS i EB :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; apply eh_aview0;
lazymatch type of Hk with ?a <= k < ?b =>
  let b' := eval vm_compute in b in
  let Hk0 := fresh "Hk" in assert (Hk0 : a <= k < b') by lia; clear Hk;
  let rec go Hc :=
    first
    [ exfalso; lia
    | lazymatch type of Hc with ?x <= k < ?y =>
        let Hne := fresh "Hne" in
        destruct (Z.eq_dec k x) as [->|Hne];
        [ eh_chunk HS i x; [exact EB | reflexivity | cbn; lia | reflexivity | reflexivity]
        | let x' := eval vm_compute in (x + 1) in
          let Hc' := fresh "Hk" in assert (Hc' : x' <= k < y) by lia; clear Hc Hne; go Hc' ] end ]
  in go Hk0 end.
(* the I/O state of a run's last model *)
Ltac eh_io := let rec kio := first [apply same_io_refl | apply same_io_wvb | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.

Section d.
Variable B : asyms.

(* the context every block runs in: the journal, the real frame R inside its stack window, F = the side-stack frame
   (4, pos) the harness holds *)
Definition eh_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 32 = 0 /\ R + 0x220 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos.

Lemma eh_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ alloc_ceiling + T_SEG_STK <= R /\
2 ^ 46 <= R /\ R + 0x220 <= 2 ^ 47 /\ T_SEG_STK = 16384 /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) /\
(forall a, sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & HR32 & HRhi & HRlo & Hown & EF).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (@asan_consts rc) as (C1 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & _ & _ & HFsh).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- EF in HF32, HFsh, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFsh, HFceil.
change (1024 / 8) with 128 in HFsh.
split; [exact HF32|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Has|].
split; [intros i Hi; exact (proj1 (HFsh i Hi))|].
split; [exact Hpres|].
intros a Ha. left. exact Ha.
Qed.

(* ---- the leaf of a run: the journal, the I/O state and presence from the run ---- *)
Ltac eh_leaf HS HJ :=
eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | eh_io | | | eassumption | ].
(* the frame condition of a run: in_wrange of its start regions lies in Wr; fin closes one region's case *)
Ltac eh_kept HFr Wr fin :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
intros a Ha Hz;
refine (cb_kept_run Wr _ _ _ _ _ _ (fun a _ _ => eq_refl) HFr _ a Ha Hz);
let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros x (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; fin Hr | ]);
destruct Hin.
Ltac eh_fr Hctx :=
destruct (eh_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & HFsh & HRp & AS).
Ltac eh_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
(* the row's write window: the frame (4, pos) the harness owns *)
Ltac eh_awr_row U19 EF Hown :=
eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat 4 _);
[ reflexivity | rewrite <- EF; exact U19 | exact Hown | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; vm_compute; discriminate | ].

(* ======================================== eh_T1: 0x8194c -> 0x81980 ======================================== *)
Definition eh_T1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 20 = w64 n -> 1 <= n < 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs EH_D regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k EH_K regs memc mdc [] (eh_wT F)
 (fun _ mem2 => eh_zero W mem2 F 4 12)).

Lemma eh_T1 : eh_T1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos n Hctx H19 H20 Hn.
pose proof (AR_laws_ok rsegs B) as LAWS.
eh_fr Hctx.
pose proof Hctx as (HJ & HR32 & HRhi & HRlo & Hown & EF).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ apply eh_unsigned; [exact (eh_ew_reg regs [] 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U20 : bv_unsigned (ew (Ereg regs []) 20) = n).
{ apply eh_unsigned; [exact (eh_ew_reg regs [] 20 20%bv _ eq_refl H20) | lia]. }
assert (HS : st_ok rsegs (Ereg regs []) ss_T1 (restrict (w_H W) (mkst regs (Z_to_bv 64 EH_D) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_T1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
unfold cfg_at. change (w64 EH_D) with (Z_to_bv 64 EH_D).
aj_run_to e0_tbl_ok HS HJ EH_K.
- eh_awr. eh_awr_row U19 EF Hown. apply awr_ok_nil.
- eh_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + eh_kept HFr (eh_wT F) ltac:(fun H => rewrite ?U19 in H; cbv [eh_wT]; lia).
  + eh_zero_tac HS 0%nat U19.
Qed.

(* ================================ eh_T0 / eh_TE: to DIG with nothing read ================================ *)
Definition eh_Z_R (F : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 5 = w64 4 /\ getr regs2 6 = w64 0 /\ getr regs2 13 = w64 0 /\ getr regs2 18 = w64 (F + 0xa0) /\
getr regs2 26 = w64 0 /\ getr regs2 28 = w64 9.
Definition eh_Z_mem (W : world rsegs) (mem2 : word -> option byte) (R F cur : Z) : Prop :=
eh_zero W mem2 F 4 12 /\ eh_zero W mem2 F 20 3 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8 cur.

Definition eh_T0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 20 = w64 0 ->
getr regs 18 = w64 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs EH_D regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k E0_DIG regs memc mdc [5; 6; 13; 18; 20; 21; 26; 28]%bv
 (eh_wTCN R F) (fun regs2 mem2 => eh_Z_R F regs2 /\ eh_Z_mem W mem2 R F cur)).
Definition eh_TE_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 21 = w64 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs EH_D0E regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k E0_DIG regs memc mdc [5; 6; 7; 13; 18; 26; 28]%bv
 (eh_wTCN R F) (fun regs2 mem2 => eh_Z_R F regs2 /\ getr regs2 7 = w64 10 /\ eh_Z_mem W mem2 R F cur)).

(* the entry state of both: the row's two regions and the real frame's cells, F + 0xa0 in slot 32 *)
Lemma eh_entry_Z : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos pc,
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (F + 0xa0) ->
st_ok rsegs (Ereg regs [Z_to_bv 64 (F + 0xa0)]) (mkSS pc sr_atoms [eh_rT; eh_rCh; eh_rRw] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pc Hctx H9 H19 Hc8.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & _).
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]).
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  + apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  + apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | |].
    * intros o Ho. apply HRp. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0xc8 8 (SOff 32 0) (F + 0xa0));
        [apply eh_denot_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Hc8].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [eh_rT eh_rCh eh_rRw YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
  repeat split; first [exact I | lia].
- split; [exact I | split; exact I].
Qed.

Lemma eh_T0 : eh_T0_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur Hctx H9 H19 H20 H18 Hcur Hc8.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (eh_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EH_D Hctx H9 H19 Hc8) as HS0.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & Hown & EF).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS0.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X18 : ew (Ereg regs ex) 18 = Z_to_bv 64 cur) by exact (eh_ew_reg regs ex 18 18%bv _ eq_refl H18).
pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 0 HS0 eq_refl H20) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold cfg_at. change (w64 EH_D) with (Z_to_bv 64 EH_D).
aj_run_to e0_tbl_ok HS HJ E0_DIG.
- eh_awr.
  eh_awr_row U19 EF Hown. eh_awr_row U19 EF Hown.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia.
- eh_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + eh_kept HFr (eh_wTCN R F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [eh_wTCN eh_wT eh_wCh eh_wN]; lia).
  + cbv beta. split.
    * unfold eh_Z_R. split; [|split; [|split; [|split; [|split]]]].
      -- eh_reg HS (5%bv : bv 5). reflexivity.
      -- eh_reg HS (6%bv : bv 5). reflexivity.
      -- eh_reg HS (13%bv : bv 5). reflexivity.
      -- eh_reg HS (18%bv : bv 5). apply eh_denot_atom; [exact X32 | lia].
      -- eh_reg HS (26%bv : bv 5). reflexivity.
      -- eh_reg HS (28%bv : bv 5). reflexivity.
    * split; [|split].
      -- eh_zero_tac HS 0%nat U19.
      -- eh_zero_tac HS 1%nat U19.
      -- eh_chunk HS 2%nat 0x110; [exact U9 | apply eh_denot_atom; [exact X18 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

Lemma eh_TE : eh_TE_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur Hctx H9 H19 H21 Hcur Hc8.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (eh_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EH_D0E Hctx H9 H19 Hc8) as HS.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & Hown & EF).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X21 : ew (Ereg regs ex) 21 = Z_to_bv 64 cur) by exact (eh_ew_reg regs ex 21 21%bv _ eq_refl H21).
unfold cfg_at. change (w64 EH_D0E) with (Z_to_bv 64 EH_D0E).
aj_run_to e0_tbl_ok HS HJ E0_DIG.
- eh_awr.
  eh_awr_row U19 EF Hown. eh_awr_row U19 EF Hown.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia.
- eh_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + eh_kept HFr (eh_wTCN R F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [eh_wTCN eh_wT eh_wCh eh_wN]; lia).
  + cbv beta. split; [|split].
    * unfold eh_Z_R. split; [|split; [|split; [|split; [|split]]]].
      -- eh_reg HS (5%bv : bv 5). reflexivity.
      -- eh_reg HS (6%bv : bv 5). reflexivity.
      -- eh_reg HS (13%bv : bv 5). reflexivity.
      -- eh_reg HS (18%bv : bv 5). apply eh_denot_atom; [exact X32 | lia].
      -- eh_reg HS (26%bv : bv 5). reflexivity.
      -- eh_reg HS (28%bv : bv 5). reflexivity.
    * eh_reg HS (7%bv : bv 5). reflexivity.
    * split; [|split].
      -- eh_zero_tac HS 0%nat U19.
      -- eh_zero_tac HS 1%nat U19.
      -- eh_chunk HS 2%nat 0x110; [exact U9 | apply eh_denot_atom; [exact X21 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

(* ================================ eh_C: the ch stores and the arm test ================================ *)
Definition eh_C_stmt : Prop :=
forall (odd : bool) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 13 = w64 c ->
(if odd then 200 <= c < 256 else 0 <= c < 200) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc8) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs EH_CH regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (if odd then E0_ODD else E0_DIG) regs memc mdc [5; 11; 18]%bv
 (eh_wCh F) (fun regs2 mem2 => eh_zero W mem2 F 20 3 /\ getr regs2 18 = w64 (F + 0xa0) /\ getr regs2 5 = w64 4)).

Lemma eh_C : eh_C_stmt.
Proof.
intros odd STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c Hctx H9 H19 H13 Hc Hc8.
pose proof (AR_laws_ok rsegs B) as LAWS.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & Hown & EF).
assert (Hc8b : 0 <= c < 256) by (destruct odd; cbv iota in Hc; lia).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]).
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (U13 : bv_unsigned (ew (Ereg regs ex) 13) = c).
{ apply eh_unsigned; [exact (eh_ew_reg regs ex 13 13%bv _ eq_refl H13) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (HS : st_ok rsegs (Ereg regs ex) (ss_C odd)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 EH_CH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
      intros o Ho. apply HFsh. lia.
    + apply (hm_ro_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0xc8 8 (SOff 32 0) (F + 0xa0));
        [apply eh_denot_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Hc8].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [eh_rCh eh_rRc YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    repeat split; first [exact I | lia].
  - split; [|split; exact I]. cbn [ss_C f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. rewrite U13. destruct odd; cbn [af_lo af_hi af_al2]; cbv iota in Hc; rewrite Z.pow_0_r, Z.mod_1_r;
    repeat split; lia. }
unfold cfg_at. change (w64 EH_CH) with (Z_to_bv 64 EH_CH).
destruct odd; cbv iota.
- aj_run_to e0_tbl_ok HS HJ E0_ODD.
  + eh_awr. eh_awr_row U19 EF Hown. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
  + eh_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * eh_kept HFr (eh_wCh F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [eh_wCh]; lia).
    * cbv beta. split; [eh_zero_tac HS 0%nat U19 | split].
      -- eh_reg HS (18%bv : bv 5). apply eh_denot_atom; [exact X32 | lia].
      -- eh_reg HS (5%bv : bv 5). reflexivity.
- aj_run_to e0_tbl_ok HS HJ E0_DIG.
  + eh_awr. eh_awr_row U19 EF Hown. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
  + eh_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * eh_kept HFr (eh_wCh F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [eh_wCh]; lia).
    * cbv beta. split; [eh_zero_tac HS 0%nat U19 | split].
      -- eh_reg HS (18%bv : bv 5). apply eh_denot_atom; [exact X32 | lia].
      -- eh_reg HS (5%bv : bv 5). reflexivity.
Qed.

(* ================================ eh_K1 / eh_K2: the reads of c and p ================================ *)
Definition eh_K1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur c : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 17 = w64 (cur - 1) -> getr regs 18 = w64 cur ->
getr regs 16 = w64 1 -> getr regs 6 = w64 2 ->
1 <= cur -> cur + 1 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
~ (R <= cur < R + 0x198) ->
SRr rsegs W (cfg_at rsegs EH_K regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k EH_CH regs memc mdc [6; 10; 11; 12; 13; 16; 18; 26; 28]%bv
 (eh_wN R)
 (fun regs2 mem2 => getr regs2 13 = w64 c /\ getr regs2 6 = w64 0 /\ getr regs2 26 = w64 0 /\
   getr regs2 28 = w64 9 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8 (cur + 1))).
Definition eh_K2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur n c p : Z),
eh_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 17 = w64 (cur - 1) -> getr regs 18 = w64 cur ->
getr regs 16 = w64 1 -> getr regs 6 = w64 (n + 1) -> 2 <= n <= 2 ^ 47 ->
1 <= cur -> cur + 2 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (cur + 1) 1 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 2 ->
(forall a, cur <= a < cur + 2 -> ~ (R <= a < R + 0x198)) ->
SRr rsegs W (cfg_at rsegs EH_K regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k EH_CH regs memc mdc [6; 10; 11; 12; 13; 16; 18; 26; 28]%bv
 (eh_wN R)
 (fun regs2 mem2 => getr regs2 13 = w64 c /\ getr regs2 6 = w64 (n - 2) /\ getr regs2 26 = w64 p /\
   getr regs2 28 = w64 9 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8 (cur + 2))).

Lemma eh_K1 : eh_K1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur c Hctx H9 H27 H17 H18 H16 H6 Hc0 Hc1
  Hcv Hc HRA Hdis.
pose proof (AR_laws_ok rsegs B) as LAWS.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & _).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
set (ex := [Z_to_bv 64 c]).
assert (X9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9).
assert (X17 : ew (Ereg regs ex) 17 = Z_to_bv 64 (cur - 1)) by exact (eh_ew_reg regs ex 17 17%bv _ eq_refl H17).
assert (X27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF) by exact (eh_ew_reg regs ex 27 27%bv _ eq_refl H27).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 0).
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R) by (apply eh_unsigned; [exact X9 | lia]).
assert (U17 : bv_unsigned (ew (Ereg regs ex) 17) = cur - 1) by (apply eh_unsigned; [exact X17 | lia]).
assert (U27 : bv_unsigned (ew (Ereg regs ex) 27) = SHADOW_OFF)
  by (apply eh_unsigned; [exact X27 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 EH_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | intros o Ho; apply HRp; lia | constructor].
    + apply (hm_ro_region rsegs _ _ _ 17%nat (cur - 1)); [exact U17 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 32 0) c);
        [apply eh_denot_atom; [exact X32 | lia] | cbn; lia | cbn; lia |].
      replace (cur - 1 + 1) with cur by lia. exact Hcv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [eh_rRk eh_rIn1 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U17.
    repeat split; first [exact I | lia].
  - split; [|split; exact I]. cbn [ss_K1 eh_fK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U27, U17, U9. unfold E0SB, SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32.
    repeat split; lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 17 1) HS0 eq_refl
  ltac:(rewrite (eh_denot_off _ 17 (cur - 1) 1 X17 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        symmetry; exact H18)) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K1] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS1 eq_refl H16) as HS2. clear HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_lit rsegs _ _ _ (6%bv : bv 5) 2 HS2 eq_refl H6) as HS. clear HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA33 : env_agree 33 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 EH_K) with (Z_to_bv 64 EH_K).
aj_run_to_tok e0_tbl_ok HS HJ SHOK E0Bspan EH_CH.
- (* the shadow check of c's byte *)
  cbn [ms_mem mkst]. unfold E0Bx.
  rewrite (U_atom _ 27 SHADOW_OFF X27 ltac:(unfold SHADOW_OFF; lia)),
    (U_atom_off _ 17 (cur - 1) 1 X17 ltac:(lia) ltac:(lia)).
  replace (cur - 1 + 1) with cur by lia. exact HRA.
- eh_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia. }
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 33 (Ereg regs ex) E') by env_agree_chain HA33 end.
  destruct HA as [HA _].
  eh_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + eh_kept HFr (eh_wN R) ltac:(fun H => rewrite ?U9, ?U17 in H; cbv [eh_wN]; lia).
  + cbv beta. split; [|split; [|split; [|split]]].
    * eh_reg HS (13%bv : bv 5). apply eh_denot_ext8; [rewrite HA by lia; exact X32 | lia].
    * eh_reg HS (6%bv : bv 5). reflexivity.
    * eh_reg HS (26%bv : bv 5). reflexivity.
    * eh_reg HS (28%bv : bv 5). reflexivity.
    * eh_chunk HS 0%nat 0x110; [rewrite HA by lia; exact U9 | | cbn; lia | reflexivity | reflexivity].
      rewrite (eh_denot_off _ 17 (cur - 1) 2 ltac:(rewrite HA by lia; exact X17) ltac:(lia) ltac:(lia)).
      f_equal; lia.
Qed.

Lemma eh_K2 : eh_K2_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur n c p Hctx H9 H27 H17 H18 H16 H6 Hn
  Hc0 Hc1 Hcv Hc Hpv Hp HRA Hdis.
pose proof (AR_laws_ok rsegs B) as LAWS.
eh_fr Hctx. pose proof Hctx as (HJ & HR32 & HRhi & HRlo & _).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (@asan_consts rc) as (C1 & _).
pose proof (Hdis cur ltac:(lia)) as Hd0. pose proof (Hdis (cur + 1) ltac:(lia)) as Hd1. clear Hdis.
set (ex := [Z_to_bv 64 c; Z_to_bv 64 p]).
assert (X9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by exact (eh_ew_reg regs ex 9 9%bv _ eq_refl H9).
assert (X17 : ew (Ereg regs ex) 17 = Z_to_bv 64 (cur - 1)) by exact (eh_ew_reg regs ex 17 17%bv _ eq_refl H17).
assert (X27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF) by exact (eh_ew_reg regs ex 27 27%bv _ eq_refl H27).
assert (X6 : ew (Ereg regs ex) 6 = Z_to_bv 64 (n + 1)) by exact (eh_ew_reg regs ex 6 6%bv _ eq_refl H6).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 0).
assert (X33 : ew (Ereg regs ex) 33 = Z_to_bv 64 p) by exact (ew_Ereg_extra regs ex 1).
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R) by (apply eh_unsigned; [exact X9 | lia]).
assert (U17 : bv_unsigned (ew (Ereg regs ex) 17) = cur - 1) by (apply eh_unsigned; [exact X17 | lia]).
assert (U6 : bv_unsigned (ew (Ereg regs ex) 6) = n + 1) by (apply eh_unsigned; [exact X6 | lia]).
assert (U27 : bv_unsigned (ew (Ereg regs ex) 27) = SHADOW_OFF)
  by (apply eh_unsigned; [exact X27 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 EH_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | intros o Ho; apply HRp; lia | constructor].
    + apply (hm_ro_region rsegs _ _ _ 17%nat (cur - 1)); [exact U17 | lia | lia |].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 32 0) c);
          [apply eh_denot_atom; [exact X32 | lia] | cbn; lia | cbn; lia |].
        replace (cur - 1 + 1) with cur by lia. exact Hcv.
      * apply (chunk_ok_val rsegs _ _ (cur - 1) 2 1 (SOff 33 0) p);
          [apply eh_denot_atom; [exact X33 | lia] | cbn; lia | cbn; lia |].
        replace (cur - 1 + 2) with (cur + 1) by lia. exact Hpv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [eh_rRk eh_rIn2 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U17.
    repeat split; first [exact I | lia].
  - split; [|split; exact I]. cbn [ss_K2 eh_fK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U6, U27, U17, U9. unfold E0SB, SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32.
    repeat split; lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 17 1) HS0 eq_refl
  ltac:(rewrite (eh_denot_off _ 17 (cur - 1) 1 X17 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        symmetry; exact H18)) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K2] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS1 eq_refl H16) as HS. clear HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA34 : env_agree 34 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 EH_K) with (Z_to_bv 64 EH_K).
aj_run_to_tok e0_tbl_ok HS HJ SHOK E0Bspan EH_CH.
1-2: (* the shadow checks of the two bytes *)
  cbn [ms_mem mkst]; unfold E0Bx;
  lazymatch goal with |- range_addressable _ _ (U _ (SOff 17 ?j)) _ =>
    rewrite (U_atom _ 27 SHADOW_OFF X27 ltac:(unfold SHADOW_OFF; lia)),
      (U_atom_off _ 17 (cur - 1) j X17 ltac:(lia) ltac:(lia));
    replace (cur - 1 + j) with (cur + (j - 1)) by lia;
    refine (hm_in_ra _ _ cur 2 (j - 1) HRA _); lia end.
- eh_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia. }
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 34 (Ereg regs ex) E') by env_agree_chain HA34 end.
  destruct HA as [HA _].
  eh_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + eh_kept HFr (eh_wN R) ltac:(fun H => rewrite ?U9, ?U17 in H; cbv [eh_wN]; lia).
  + cbv beta. split; [|split; [|split; [|split]]].
    * eh_reg HS (13%bv : bv 5). apply eh_denot_ext8; [rewrite HA by lia; exact X32 | lia].
    * eh_reg HS (6%bv : bv 5).
      rewrite (eh_denot_off _ 6 (n + 1) (-3) ltac:(rewrite HA by lia; exact X6) ltac:(lia) ltac:(lia)).
      unfold w64. f_equal. lia.
    * eh_reg HS (26%bv : bv 5). apply eh_denot_ext8; [rewrite HA by lia; exact X33 | lia].
    * eh_reg HS (28%bv : bv 5). reflexivity.
    * eh_chunk HS 0%nat 0x110; [rewrite HA by lia; exact U9 | | cbn; lia | reflexivity | reflexivity].
      rewrite (eh_denot_off _ 17 (cur - 1) 3 ltac:(rewrite HA by lia; exact X17) ltac:(lia) ltac:(lia)).
      f_equal; lia.
Qed.

End d.
End b.

Print Assumptions eh_T1.
Print Assumptions eh_T0.
Print Assumptions eh_TE.
Print Assumptions eh_C.
Print Assumptions eh_K1.
Print Assumptions eh_K2.
