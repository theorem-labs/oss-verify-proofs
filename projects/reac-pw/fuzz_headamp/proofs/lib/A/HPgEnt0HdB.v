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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0HdB.v, with its module paths, addresses and numbers changed; 201 of its 604 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0HdB.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0); the real frame's cells R+0x58 -> R+0x80 and R+0xf8 -> R+0x118 (engine region [R+0x80, R+0x120)), the real frame of 0x1e0 bytes; the frame for locals of class 4 (1024 bytes, 128 shadow bytes). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemmas of the
   head of ent_build's case 0 (pod.h:224-236), from D = 0x81860 and D0E = 0x818cc to the two arms DIG = 0x81920 and
   ODD = 0x820c8 (lib/A/HPgEnt0Def.v). Proves no function (kind: segment lemma).

   THE SPLIT. A run that stores a shadow byte (the scope stores of t and ch) is a plain engine run with the frame's
   shadow row writable; a run that passes an instrumented check (the two reads of the input cursor) is a token run
   (lib/Reusable/YCbn.v) with the row absent. So the head is six blocks, each from a fixed pc to a fixed pc in the
   shape HPgW7bBase.w7_post (the journal at the block's start state, the I/O state, the registers outside clob, every
   byte outside the write set, presence kept, and a relation of the result):
     hd_T1  0x81860 -> 0x81894  plain: the twelve t stores (shadow F + 4 .. 15 := 0), `beqz s9` not taken (s9 >= 1)
     hd_T0  0x81860 -> 0x81920  plain, s9 = 0: the t stores, `beqz s9` taken to 0x8212c (s9 := s8, s4 := [R+0x80]),
                                0x81904 t0 := 9, [R+0x118] := 0, s11 := 0, a0 := 0, the three ch stores (F + 20 .. 22)
     hd_TE  0x818cc -> 0x81920  plain: the t stores, s4 := [R+0x80], a7 := 10, then as hd_T0 from 0x81904
     hd_K1  0x81894 -> 0x820ac  token, one byte left: the check of the cursor (slow block 0x826d0), a0 := c,
                                s8 := a4 + 2, `bne [R+0x118], 2` not taken, [R+0x118] := 0, s11 := 0
     hd_K2  0x81894 -> 0x820ac  token, two bytes or more: the same read, `bne` taken to 0x82088, the check of the
                                second byte (slow block 0x82784), s11 := p, s8 := a4 + 3, [R+0x118] -= 3
     hd_C   0x820ac -> 0x81920 / 0x820c8  plain: the three ch stores, `bltu 0xc7,a0`: c < 200 to DIG (s9 := s8),
                                c >= 200 to ODD
   THE ENGINE STATES. Atom 19 = s3 = shadow_addr F bases the row's two regions, t's twelve bytes [4, 16) and ch's
   three [20, 23), each its own write window; atom 9 = s1 = R bases the real frame's cells [R+0x80, R+0x120) (the
   8-byte cell R+0x80 = F + 0xa0 as env slot 32, R+0x118 = what is left of the input, write window [R+0x118, R+0x120));
   atom 14 = a4, the kind byte's address, bases the input bytes c (slot 33) and p (slot 34), read-only, and s8 is
   seated as a4 + 1. The token runs use the shadow base s7 itself (HPgW7bBase W7Bx = SOff 23 0) and leave one
   obligation per input read: range_addressable of that byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgMem HPgSteps HPgW7bBase HPgEnt0Def.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition HD_D : Z := 0x81860.
Definition HD_D0E : Z := 0x818cc.
Definition HD_K : Z := 0x81894.     (* the first read of the cursor *)
Definition HD_CH : Z := 0x820ac.    (* the ch stores *)

(* ======================================== the engine states ======================================== *)
Definition hd_rT : YP09.region := YP09.mkRegion (Some 19%nat) 4 16 4 16 [].
Definition hd_rCh : YP09.region := YP09.mkRegion (Some 19%nat) 20 23 20 23 [].
Definition hd_rR (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x80 0x120 0x118 0x120 (YP09.mkChunk 0x80 (CVal 8 (SOff 32 0)) :: cs).
Definition hd_rIn1 : YP09.region := YP09.mkRegion (Some 14%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition hd_rIn2 : YP09.region :=
YP09.mkRegion (Some 14%nat) 1 3 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition hd_fK (a4hi : Z) : list (nat * afact) :=
[(23%nat, mkAF W7SB W7SB 0); (14%nat, mkAF 0 a4hi 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4)].

Definition ss_T1 : sstate :=
mkSS HD_D sr_atoms [hd_rT] None (mkFacts [(25%nat, mkAF 1 (2 ^ 63) 0)] [] []).
Definition ss_T0 : sstate := mkSS HD_D sr_atoms [hd_rT; hd_rCh; hd_rR []] None (mkFacts [] [] []).
Definition ss_TE : sstate := mkSS HD_D0E sr_atoms [hd_rT; hd_rCh; hd_rR []] None (mkFacts [] [] []).
Definition ss_K1 : sstate :=
mkSS HD_K sr_atoms [hd_rR [YP09.mkChunk 0x118 (CVal 8 (SLit 2))]; hd_rIn1] None (mkFacts (hd_fK (2 ^ 47 - 3)) [] []).
Definition ss_K2 : sstate :=
mkSS HD_K sr_atoms [hd_rR [YP09.mkChunk 0x118 (CVal 8 (SOff 25 1))]; hd_rIn2] None
(mkFacts ((25%nat, mkAF 2 (2 ^ 47) 0) :: hd_fK (2 ^ 47 - 4)) [] []).
Definition ss_C (odd : bool) : sstate :=
mkSS HD_CH sr_atoms [hd_rCh] None (mkFacts [(10%nat, if odd then mkAF 200 255 0 else mkAF 0 199 0)] [] []).

(* ======================================== the write sets ======================================== *)
Definition hd_wT (F : Z) : Z -> Prop := fun a => shadow_addr F + 4 <= a < shadow_addr F + 16.
Definition hd_wCh (F : Z) : Z -> Prop := fun a => shadow_addr F + 20 <= a < shadow_addr F + 23.
Definition hd_wN (R : Z) : Z -> Prop := fun a => R + 0x118 <= a < R + 0x120.
Definition hd_wTCN (R F : Z) : Z -> Prop := fun a => hd_wT F a \/ hd_wCh F a \/ hd_wN R a.

Lemma hd_sF : forall F, 4096 <= F -> F + 1024 <= 2 ^ 47 ->
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
Definition hd_zero (W : world rsegs) (mem : word -> option byte) (F j n : Z) : Prop :=
forall i, j <= i < j + n -> aview rsegs (w_H W) mem (shadow_addr F + i) = Some 0.

(* ======================================== engine helpers ======================================== *)
Lemma hd_pin_sv : forall E ss ms (r : bv 5) e,
st_ok rsegs E ss ms -> bv_eqb r 0 = false -> getr (ms_regs ms) r = sv_denot E e ->
st_ok rsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 Hr.
apply (st_ok_regs rsegs E ss ms (sr_set (ss_regs ss) r e) HS).
intros rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite <- (st_ok_reg rsegs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma hd_val_at : forall E ss H ms i n lo hi wlo whi cs b off (w : N) e v a (wn : nat),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + off -> wn = N.to_nat w ->
val_mem rsegs (mrestrict H (ms_mem ms)) a wn v.
Proof.
intros E ss H ms i n lo hi wlo whi cs b off w e v a wn HS Hi Hb Hc He Hv Hw -> ->.
exact (w7_field E _ n b cs lo hi wlo whi off w e v (w7_region_nth E ss (restrict H ms) i _ HS Hi) Hb Hc He Hv Hw).
Qed.
Lemma hd_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.
Lemma hd_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma hd_denot_ext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SExt, (U_atom E n v H ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. rewrite Z.mod_small by lia.
reflexivity.
Qed.
Lemma hd_ew_reg : forall regs ex n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
ew (Ereg regs ex) n = Z_to_bv 64 v.
Proof. intros regs ex n r v Hn H. rewrite (ew_Ereg_nat regs ex n r Hn), H. reflexivity. Qed.
Lemma hd_unsigned : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma hd_aview0 : forall H mem x, val_mem rsegs (mrestrict H mem) x (N.to_nat 1) 0 -> aview rsegs H mem x = Some 0.
Proof. intros H mem x V. apply (hm_val1_aview rsegs H mem x 0); [exact V | lia]. Qed.
Lemma hd_w64_eq : forall a b, a = b -> w64 a = w64 b.
Proof. intros a b ->. reflexivity. Qed.

(* a register of the final state *)
Ltac hd_reg HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  rewrite (st_ok_restrict_reg rsegs _ _ ssf _ r HS);
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* a chunk of region i of the final state at offset off; leaves the base, the value, its range *)
Ltac hd_chunk HS i off :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let r := eval vm_compute in (nth_error (ss_mem ssf) i) in
  lazymatch r with Some (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    eapply (hd_val_at _ ssf _ _ i n lo hi wlo whi cs _ off);
    [exact HS | vm_compute; reflexivity | | cbn [In]; repeat (first [left; reflexivity | right]) | | | cbn; lia | | ] end end.
(* every byte j .. j + n - 1 of region i (based at the row, EB : its base) holds the 0 a scope store wrote *)
Ltac hd_zero_tac HS i EB :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; apply hd_aview0;
lazymatch type of Hk with ?a <= k < ?b =>
  let b' := eval vm_compute in b in
  let Hk0 := fresh "Hk" in assert (Hk0 : a <= k < b') by lia; clear Hk;
  let rec go Hc :=
    first
    [ exfalso; lia
    | lazymatch type of Hc with ?x <= k < ?y =>
        let Hne := fresh "Hne" in
        destruct (Z.eq_dec k x) as [->|Hne];
        [ hd_chunk HS i x; [exact EB | reflexivity | cbn; lia | reflexivity | reflexivity]
        | let x' := eval vm_compute in (x + 1) in
          let Hc' := fresh "Hk" in assert (Hc' : x' <= k < y) by lia; clear Hc Hne; go Hc' ] end ]
  in go Hk0 end.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* the context every block runs in: the journal, the real frame R inside its stack window, F = the side-stack frame
   (4, pos) the harness holds *)
Definition hd_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x1e0 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos.

Lemma hd_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ alloc_ceiling + T_SEG_STK <= R /\
2 ^ 46 <= R /\ R + 0x1e0 <= 2 ^ 47 /\ T_SEG_STK = 16384 /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) /\
(forall a, shadow_addr F <= a < shadow_addr F + 128 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) /\
(forall a, sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & HR16 & HRhi & HRlo & Hown & EF).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF32 & _ & _ & HFsh).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- EF in HF32, HFsh, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFsh, HFceil.
change (1024 / 8) with 128 in HFsh.
split; [exact HF32|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Has|].
split; [intros i Hi; exact (proj1 (HFsh i Hi))|].
split; [exact Hpres|].
split.
- intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. right.
  unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes 4 / 8) with 128. lia.
- intros a Ha. left. exact Ha.
Qed.

(* ---- the leaf of a run: the journal, the I/O state and presence from the run ---- *)
Ltac hd_leaf HS HJ :=
eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | eassumption | ].
(* the frame condition of a run: in_wrange of its start regions lies in Wr; fin closes one region's case *)
Ltac hd_kept HFr Wr fin :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
intros a Ha Hz;
refine (kept_run Wr _ _ _ _ _ _ (fun a _ _ => eq_refl) HFr _ a Ha Hz);
let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros x (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; fin Hr | ]);
destruct Hin.
Ltac hd_fr Hctx :=
destruct (hd_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & HFsh & HRp & AF & AS).
Ltac hd_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.

(* ======================================== hd_T1: 0x81860 -> 0x81894 ======================================== *)
Definition hd_T1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 25 = w64 n -> 1 <= n < 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs HD_D regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HD_K regs memc mdc [] (hd_wT F)
 (fun _ mem2 => hd_zero W mem2 F 4 12)).

Lemma hd_T1 : hd_T1_stmt.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos n Hctx H19 H25 Hn.
hd_fr Hctx.
pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hd_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (E19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ apply hd_unsigned; [exact (hd_ew_reg regs [] 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (E25 : bv_unsigned (ew (Ereg regs []) 25) = n).
{ apply hd_unsigned; [exact (hd_ew_reg regs [] 25 25%bv _ eq_refl H25) | lia]. }
assert (HS : st_ok rsegs (Ereg regs []) ss_T1 (restrict (w_H W) (mkst regs (Z_to_bv 64 HD_D) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact E19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_T1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E25. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
unfold cfg_at. change (w64 HD_D) with (Z_to_bv 64 HD_D).
aj_run_to r7_tbl_ok HS HJ HD_K.
- cbn [ss_mem ss_T1].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact E19 | | apply awr_ok_nil].
  cbn [hd_rT YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia.
- hd_leaf HS HJ.
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (kept_run (hd_wT F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (r & Hin & Hr). cbn [ss_mem ss_T1 In] in Hin. destruct Hin as [<-|[]].
    cbn [hd_rT YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19 in Hr. unfold hd_wT. lia.
  + hd_zero_tac HS 0%nat E19.
Qed.

(* ================================ hd_T0 / hd_TE: to DIG with nothing read ================================ *)
Definition hd_Z_R (F : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 5 = w64 9 /\ getr regs2 10 = w64 0 /\ getr regs2 20 = w64 (F + 0xa0) /\ getr regs2 27 = w64 0.
Definition hd_Z_mem (W : world rsegs) (mem2 : word -> option byte) (R F : Z) : Prop :=
hd_zero W mem2 F 4 12 /\ hd_zero W mem2 F 20 3 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 0.

Definition hd_T0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 25 = w64 0 ->
getr regs 24 = w64 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HD_D regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k R7_DIG regs memc mdc [5; 10; 20; 25; 27]%bv (hd_wTCN R F)
 (fun regs2 mem2 => hd_Z_R F regs2 /\ getr regs2 25 = w64 cur /\ hd_Z_mem W mem2 R F)).
Definition hd_TE_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HD_D0E regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k R7_DIG regs memc mdc [5; 10; 17; 20; 27]%bv (hd_wTCN R F)
 (fun regs2 mem2 => hd_Z_R F regs2 /\ getr regs2 17 = w64 10 /\ hd_Z_mem W mem2 R F)).

(* the entry state of both: the row's two regions and the real frame's cells, F + 0xa0 in slot 32 *)
Lemma hd_entry_Z : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos pc,
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0xa0) ->
st_ok rsegs (Ereg regs [Z_to_bv 64 (F + 0xa0)]) (mkSS pc sr_atoms [hd_rT; hd_rCh; hd_rR []] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pc Hctx H9 H19 H58.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof asan_consts as (C1 & _).
destruct (hd_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]).
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
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
      apply (chunk_ok_val rsegs _ _ R 0x80 8 (SOff 32 0) (F + 0xa0));
        [apply hd_denot_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact H58].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [hd_rT hd_rCh hd_rR YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
  repeat split; first [left; lia | exact I].
- split; [exact I | split; exact I].
Qed.

Lemma hd_T0 : hd_T0_stmt.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur Hctx H9 H19 H25 H24 Hcur H58.
pose proof (hd_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD_D Hctx H9 H19 H58) as HS0.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hd_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS0.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X24 : ew (Ereg regs ex) 24 = Z_to_bv 64 cur) by exact (hd_ew_reg regs ex 24 24%bv _ eq_refl H24).
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS0 eq_refl H25) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold cfg_at. change (w64 HD_D) with (Z_to_bv 64 HD_D).
aj_run_to r7_tbl_ok HS HJ R7_DIG.
- hd_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia.
- hd_leaf HS HJ.
  + eapply (w7_regs_kept _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + hd_kept HFr (hd_wTCN R F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia).
  + cbv beta. split; [|split].
    * unfold hd_Z_R. split; [|split; [|split]].
      -- hd_reg HS (5%bv : bv 5). reflexivity.
      -- hd_reg HS (10%bv : bv 5). reflexivity.
      -- hd_reg HS (20%bv : bv 5). apply hd_denot_atom; [exact X32 | lia].
      -- hd_reg HS (27%bv : bv 5). reflexivity.
    * hd_reg HS (25%bv : bv 5). apply hd_denot_atom; [exact X24 | lia].
    * split; [|split].
      -- hd_zero_tac HS 0%nat U19.
      -- hd_zero_tac HS 1%nat U19.
      -- hd_chunk HS 2%nat 0x118; [exact U9 | reflexivity | cbn; lia | reflexivity | reflexivity].
Qed.

Lemma hd_TE : hd_TE_stmt.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H9 H19 H58.
pose proof (hd_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD_D0E Hctx H9 H19 H58) as HS.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hd_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hd_unsigned; [exact (hd_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
unfold cfg_at. change (w64 HD_D0E) with (Z_to_bv 64 HD_D0E).
aj_run_to r7_tbl_ok HS HJ R7_DIG.
- hd_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia.
- hd_leaf HS HJ.
  + eapply (w7_regs_kept _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + hd_kept HFr (hd_wTCN R F) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hd_wTCN hd_wT hd_wCh hd_wN]; lia).
  + cbv beta. split; [|split].
    * unfold hd_Z_R. split; [|split; [|split]].
      -- hd_reg HS (5%bv : bv 5). reflexivity.
      -- hd_reg HS (10%bv : bv 5). reflexivity.
      -- hd_reg HS (20%bv : bv 5). apply hd_denot_atom; [exact X32 | lia].
      -- hd_reg HS (27%bv : bv 5). reflexivity.
    * hd_reg HS (17%bv : bv 5). reflexivity.
    * split; [|split].
      -- hd_zero_tac HS 0%nat U19.
      -- hd_zero_tac HS 1%nat U19.
      -- hd_chunk HS 2%nat 0x118; [exact U9 | reflexivity | cbn; lia | reflexivity | reflexivity].
Qed.

(* ================================ hd_C: the ch stores and the arm test ================================ *)
Definition hd_C_stmt : Prop :=
forall (odd : bool) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c cur : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 10 = w64 c ->
(if odd then 200 <= c < 256 else 0 <= c < 200) -> getr regs 24 = w64 cur -> 0 <= cur < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs HD_CH regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (if odd then R7_ODD else R7_DIG) regs memc mdc [11; 25]%bv
 (hd_wCh F) (fun regs2 mem2 => hd_zero W mem2 F 20 3 /\ (if odd then True else getr regs2 25 = w64 cur))).

Lemma hd_C : hd_C_stmt.
Proof using LAWS.
intros odd STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c cur Hctx H19 H10 Hc H24 Hcur.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
assert (Hc8 : 0 <= c < 256) by (destruct odd; cbv iota in Hc; lia).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hd_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ apply hd_unsigned; [exact (hd_ew_reg regs [] 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U10 : bv_unsigned (ew (Ereg regs []) 10) = c).
{ apply hd_unsigned; [exact (hd_ew_reg regs [] 10 10%bv _ eq_refl H10) | lia]. }
assert (X24 : ew (Ereg regs []) 24 = Z_to_bv 64 cur) by exact (hd_ew_reg regs [] 24 24%bv _ eq_refl H24).
assert (HS : st_ok rsegs (Ereg regs []) (ss_C odd)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HD_CH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_C f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. rewrite U10. destruct odd; cbn [af_lo af_hi af_al2]; cbv iota in Hc; rewrite Z.pow_0_r, Z.mod_1_r;
    repeat split; lia. }
unfold cfg_at. change (w64 HD_CH) with (Z_to_bv 64 HD_CH).
destruct odd; cbv iota.
- aj_run_to r7_tbl_ok HS HJ R7_ODD.
  + hd_awr.
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia.
  + hd_leaf HS HJ.
    * eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hd_kept HFr (hd_wCh F) ltac:(fun H => rewrite ?U19 in H; cbv [hd_wCh]; lia).
    * cbv beta. split; [hd_zero_tac HS 0%nat U19 | exact I].
- aj_run_to r7_tbl_ok HS HJ R7_DIG.
  + hd_awr.
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia.
  + hd_leaf HS HJ.
    * eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hd_kept HFr (hd_wCh F) ltac:(fun H => rewrite ?U19 in H; cbv [hd_wCh]; lia).
    * cbv beta. split; [hd_zero_tac HS 0%nat U19 |].
      hd_reg HS (25%bv : bv 5). apply hd_denot_atom; [exact X24 | lia].
Qed.

(* ================================ hd_K1 / hd_K2: the reads of c and p ================================ *)
Definition hd_K_R (F cur c p : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 5 = w64 9 /\ getr regs2 10 = w64 c /\ getr regs2 20 = w64 (F + 0xa0) /\
getr regs2 24 = w64 cur /\ getr regs2 27 = w64 p.

Definition hd_K1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur c : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 14 = w64 (cur - 1) -> getr regs 24 = w64 cur ->
1 <= cur -> cur + 1 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0xa0) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 2 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
~ (R <= cur < R + 0x160) ->
SRr rsegs W (cfg_at rsegs HD_K regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HD_CH regs memc mdc [5; 10; 11; 12; 20; 24; 27]%bv (hd_wN R)
 (fun regs2 mem2 => hd_K_R F (cur + 1) c 0 regs2 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 0)).
Definition hd_K2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur n c p : Z),
hd_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 14 = w64 (cur - 1) -> getr regs 24 = w64 cur ->
getr regs 25 = w64 n -> 2 <= n <= 2 ^ 47 ->
1 <= cur -> cur + 2 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0xa0) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (n + 1) ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (cur + 1) 1 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 2 ->
(forall a, cur <= a < cur + 2 -> ~ (R <= a < R + 0x160)) ->
SRr rsegs W (cfg_at rsegs HD_K regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HD_CH regs memc mdc [5; 10; 11; 12; 20; 24; 27]%bv (hd_wN R)
 (fun regs2 mem2 => hd_K_R F (cur + 2) c p regs2 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 (n - 2))).

Lemma hd_K1 : hd_K1_stmt.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur c Hctx H9 H23 H14 H24 Hc0 Hc1
  H58 Hf8 Hcv Hc HRA Hdis.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
set (ex := [Z_to_bv 64 (F + 0xa0); Z_to_bv 64 c]).
assert (X9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by exact (hd_ew_reg regs ex 9 9%bv _ eq_refl H9).
assert (X14 : ew (Ereg regs ex) 14 = Z_to_bv 64 (cur - 1)) by exact (hd_ew_reg regs ex 14 14%bv _ eq_refl H14).
assert (X23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by exact (hd_ew_reg regs ex 23 23%bv _ eq_refl H23).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X33 : ew (Ereg regs ex) 33 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 1).
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R) by (apply hd_unsigned; [exact X9 | lia]).
assert (U14 : bv_unsigned (ew (Ereg regs ex) 14) = cur - 1) by (apply hd_unsigned; [exact X14 | lia]).
assert (U23 : bv_unsigned (ew (Ereg regs ex) 23) = SHADOW_OFF)
  by (apply hd_unsigned; [exact X23 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HD_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | intros o Ho; apply HRp; lia |].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ R 0x80 8 (SOff 32 0) (F + 0xa0));
          [apply hd_denot_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact H58].
      * apply (chunk_ok_val rsegs _ _ R 0x118 8 (SLit 2) 2);
          [reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Hf8].
    + apply (hm_ro_region rsegs _ _ _ 14%nat (cur - 1)); [exact U14 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 33 0) c);
        [apply hd_denot_atom; [exact X33 | lia] | cbn; lia | cbn; lia |].
      replace (cur - 1 + 1) with cur by lia. exact Hcv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [hd_rR hd_rIn1 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U14.
    split; [split; [lia | exact I] | split; exact I].
  - split; [|split; exact I]. cbn [ss_K1 hd_fK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U23, U14, U9. unfold W7SB, SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat split; lia. }
pose proof (hd_pin_sv _ _ _ (24%bv : bv 5) (SOff 14 1) HS0 eq_refl
  ltac:(rewrite (hd_denot_off _ 14 (cur - 1) 1 X14 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        exact H24)) as HS.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K1] in HS.
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA34 : env_agree 34 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 HD_K) with (Z_to_bv 64 HD_K).
aj_run_to_tok r7_tbl_ok HS HJ SHOK W7Bspan HD_CH.
- (* the shadow check of c's byte *)
  cbn [ms_mem mkst]. unfold W7Bx.
  rewrite (U_atom _ 23 SHADOW_OFF X23 ltac:(unfold SHADOW_OFF; lia)), (U_atom_off _ 14 (cur - 1) 1 X14 ltac:(lia) ltac:(lia)).
  replace (cur - 1 + 1) with cur by lia. exact HRA.
- hd_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia. }
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 34 (Ereg regs ex) E') by env_agree_chain HA34 end.
  destruct HA as [HA _].
  hd_leaf HS HJ.
  + eapply (w7_regs_kept _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + hd_kept HFr (hd_wN R) ltac:(fun H => rewrite ?U9, ?U14 in H; cbv [hd_wN]; lia).
  + cbv beta. split.
    * unfold hd_K_R. split; [|split; [|split; [|split]]].
      -- hd_reg HS (5%bv : bv 5). reflexivity.
      -- hd_reg HS (10%bv : bv 5). apply hd_denot_ext8; [rewrite HA by lia; exact X33 | lia].
      -- hd_reg HS (20%bv : bv 5). apply hd_denot_atom; [rewrite HA by lia; exact X32 | lia].
      -- hd_reg HS (24%bv : bv 5).
         rewrite (hd_denot_off _ 14 (cur - 1) 2 ltac:(rewrite HA by lia; exact X14) ltac:(lia) ltac:(lia)).
         unfold w64. f_equal. lia.
      -- hd_reg HS (27%bv : bv 5). reflexivity.
    * hd_chunk HS 0%nat 0x118; [rewrite HA by lia; exact U9 | reflexivity | cbn; lia | reflexivity | reflexivity].
Qed.

Lemma hd_K2 : hd_K2_stmt.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur n c p Hctx H9 H23 H14 H24 H25 Hn
  Hc0 Hc1 H58 Hf8 Hcv Hc Hpv Hp HRA Hdis.
hd_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
pose proof (Hdis cur ltac:(lia)) as Hd0. pose proof (Hdis (cur + 1) ltac:(lia)) as Hd1.
set (ex := [Z_to_bv 64 (F + 0xa0); Z_to_bv 64 c; Z_to_bv 64 p]).
assert (X9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by exact (hd_ew_reg regs ex 9 9%bv _ eq_refl H9).
assert (X14 : ew (Ereg regs ex) 14 = Z_to_bv 64 (cur - 1)) by exact (hd_ew_reg regs ex 14 14%bv _ eq_refl H14).
assert (X23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by exact (hd_ew_reg regs ex 23 23%bv _ eq_refl H23).
assert (X25 : ew (Ereg regs ex) 25 = Z_to_bv 64 n) by exact (hd_ew_reg regs ex 25 25%bv _ eq_refl H25).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X33 : ew (Ereg regs ex) 33 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 1).
assert (X34 : ew (Ereg regs ex) 34 = Z_to_bv 64 p) by exact (ew_Ereg_extra regs ex 2).
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R) by (apply hd_unsigned; [exact X9 | lia]).
assert (U14 : bv_unsigned (ew (Ereg regs ex) 14) = cur - 1) by (apply hd_unsigned; [exact X14 | lia]).
assert (U25 : bv_unsigned (ew (Ereg regs ex) 25) = n) by (apply hd_unsigned; [exact X25 | lia]).
assert (U23 : bv_unsigned (ew (Ereg regs ex) 23) = SHADOW_OFF)
  by (apply hd_unsigned; [exact X23 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HD_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | intros o Ho; apply HRp; lia |].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ R 0x80 8 (SOff 32 0) (F + 0xa0));
          [apply hd_denot_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact H58].
      * apply (chunk_ok_val rsegs _ _ R 0x118 8 (SOff 25 1) (n + 1));
          [apply hd_denot_off; [exact X25 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Hf8].
    + apply (hm_ro_region rsegs _ _ _ 14%nat (cur - 1)); [exact U14 | lia | lia |].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 33 0) c);
          [apply hd_denot_atom; [exact X33 | lia] | cbn; lia | cbn; lia |].
        replace (cur - 1 + 1) with cur by lia. exact Hcv.
      * apply (chunk_ok_val rsegs _ _ (cur - 1) 2 1 (SOff 34 0) p);
          [apply hd_denot_atom; [exact X34 | lia] | cbn; lia | cbn; lia |].
        replace (cur - 1 + 2) with (cur + 1) by lia. exact Hpv.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [hd_rR hd_rIn2 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U14.
    split; [split; [lia | exact I] | split; exact I].
  - split; [|split; exact I]. cbn [ss_K2 hd_fK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U25, U23, U14, U9. unfold W7SB, SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat split; lia. }
pose proof (hd_pin_sv _ _ _ (24%bv : bv 5) (SOff 14 1) HS0 eq_refl
  ltac:(rewrite (hd_denot_off _ 14 (cur - 1) 1 X14 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        exact H24)) as HS.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K2] in HS.
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA35 : env_agree 35 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 HD_K) with (Z_to_bv 64 HD_K).
aj_run_to_tok r7_tbl_ok HS HJ SHOK W7Bspan HD_CH.
1-2: (* the shadow checks of the two bytes *)
  cbn [ms_mem mkst]; unfold W7Bx;
  lazymatch goal with |- range_addressable _ _ (U _ (SOff 14 ?j)) _ =>
    rewrite (U_atom _ 23 SHADOW_OFF X23 ltac:(unfold SHADOW_OFF; lia)),
      (U_atom_off _ 14 (cur - 1) j X14 ltac:(lia) ltac:(lia));
    replace (cur - 1 + j) with (cur + (j - 1)) by lia;
    refine (hm_in_ra _ _ cur 2 (j - 1) HRA _); lia end.
- hd_awr.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact U9 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AS. lia. }
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 35 (Ereg regs ex) E') by env_agree_chain HA35 end.
  destruct HA as [HA _].
  hd_leaf HS HJ.
  + eapply (w7_regs_kept _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + hd_kept HFr (hd_wN R) ltac:(fun H => rewrite ?U9, ?U14 in H; cbv [hd_wN]; lia).
  + cbv beta. split.
    * unfold hd_K_R. split; [|split; [|split; [|split]]].
      -- hd_reg HS (5%bv : bv 5). reflexivity.
      -- hd_reg HS (10%bv : bv 5). apply hd_denot_ext8; [rewrite HA by lia; exact X33 | lia].
      -- hd_reg HS (20%bv : bv 5). apply hd_denot_atom; [rewrite HA by lia; exact X32 | lia].
      -- hd_reg HS (24%bv : bv 5).
         rewrite (hd_denot_off _ 14 (cur - 1) 3 ltac:(rewrite HA by lia; exact X14) ltac:(lia) ltac:(lia)).
         unfold w64. f_equal. lia.
      -- hd_reg HS (27%bv : bv 5). apply hd_denot_ext8; [rewrite HA by lia; exact X34 | lia].
    * hd_chunk HS 0%nat 0x118; [rewrite HA by lia; exact U9 | | cbn; lia | reflexivity | reflexivity].
      rewrite (hd_denot_off _ 25 n (-2) ltac:(rewrite HA by lia; exact X25) ltac:(lia) ltac:(lia)).
      try (f_equal; lia).
Qed.

End d.
End b.
