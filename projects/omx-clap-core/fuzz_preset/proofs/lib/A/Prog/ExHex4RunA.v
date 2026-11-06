(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image A' (#102 pin asan 1be0f53d96cb, facts 8f3e7e1a07f1), ex_hex4
   (fuzz_preset.c :136-155; A_prog_sigma AS_ex_hex4 = A 0x84688, 55 instructions, 220 bytes) in the achain-free RUN
   FORM that ex_string's A' walk takes as its Section hypothesis for ex_hex4:
     ex_hex4_run_A : texhex4_runA SK B PST ARx (A_prog_sigma AS_ex_hex4)        (lib/A/Prog/ExsA_Callee.v)
   over any allocator relation ARx with AR_laws_x (YCbqG.v) and the two image facts of A that PALib states at
   PI_prog_A (pal_got_shadow / pal_cell, YC1fP.v): EXH_HGOT / EXH_HCELL.
   rule 24: proves function ex_hex4 (reuse search: see the brief)
   PORTED from lib/B/Prog/ExHex4RunB.v (image B', asan-ubsan d663f82d7f48, a Theorem Labs lane's proved walk, on the cut
   7cdbb61b5fa0): the same plan (journal-free helpers, the invariant runners exh_run / exh_run_to over YC80x's
   srr_inv_laws, the entry / turn / final / failret segment lemmas, the loop induction exh_loopP, exh_mainP and the
   run form with the memnorm keep), re-pointed at A' code and the whole-range table A_prog_tbl of A_prog_listing /
   PI_prog_A. WHAT CHANGED against the donor:
   - A' has no UBSan instrumentation: B''s `snez a6,a0` (B 0x84a6c), the pointer-overflow / null checks
     `bltu a2,a0 ; seqz ; xor ; beqz ; beqz a0` (B 0x84a80-0x84a90), the out-alignment check `andi a0,a1,3 ; bnez`
     (B 0x84b08-0x84b0c) and the unimp trap (B 0x84b3c) are absent, so exh_turnP lost the bltu refutation, the loop
     state lost the (p != 0) register and the fact on atom 10, and exh_finalP's run has no alignment decision. The
     entry state keeps its fact on atom 10 (p's range, beside exh_SHe's mkSHE 10 0 4): the entry run needs it.
   - registers: A' keeps two cursors, a2 (shadow test) and a0 (byte load `lbu t0,0(a0)`), both p + i at the loop
     head (B': a2 and t1, with a0 = p kept); the byte in t0 (B': t2), the temp t1 (B': t3), a6 = -10 (B': a7),
     a7 = 5 (B': t0). exh_turn_regs states a0 / a2 = p + i, a1 = o, a3 = v, a4 = the shadow offset, a5 = 4 - i,
     a6 = -10, a7 = 5.
   - pcs (EXH_PC + offset): loop head 0x28 (B' 0x30), digit tests `bgeu c - 58, -10` 0x40, `bltu 5, c - 97` 0x48,
     `bltz c - 87` 0x50, `bltu 5, c - 65` 0x64, `bltz c - 55` 0x6c, counter test `bnez a5` 0x84 (B' 0xa0), store
     tail 0x9c (B' 0xb8; its `sw a3,0(a1)` A 0x84738 = EXH_PC + 0xb0), failure return 0xb8 (B' 0xdc).
   THE TWO REPORT SITES (A' has no ubsan trap):
   - A 0x84720 (EXH_PC + 0x98) __asan_report_load1, entry edge 0x846bc bnez -> 0x84714, decider 0x84718 blt: FORM
     A/B, refuted in exh_turnP's run from the loop head by the shadow hint mkSHE 32 0 1 (exh_SHl), whose sh_ok is
     shent_ok_of_range of range_addressable p 4 (premise of texhex4_runA): the cursor byte p + i is addressable.
   - A 0x84760 (EXH_PC + 0xd8) __asan_report_store4, entry edge 0x84730 bnez -> 0x84750, decider 0x84758 blt:
     FORM A/B, refuted in exh_finalP's run by mkSHE 11 0 4 (exh_SHf) from range_addressable o 4.
   Numerals: 0x28, 0x40, 0x48, 0x50, 0x64, 0x6c, 0x84, 0x98, 0x9c, 0xb0, 0xb8, 0xd8 (DERIVED: pc offsets in ex_hex4
   from the A' listing); 16 (LENGTH: ex_hex4's frame); 4 (LENGTH: four digits; out's width); 48, 57, 58, 65, 70, 55,
   87, 97, 102, -10, 5 (WORD: the code's immediates and PjGrammar.hexval's ranges); 32 .. 35 (DERIVED: symbolic atom
   numbers); 0x7fff8000, 0x10007fff8000, 2 ^ 44 (DERIVED: SHADOW_OFF and the shadow span); 4096, 2 ^ 32, 2 ^ 46,
   2 ^ 47, 2 ^ 63, 2 ^ 64, 255, 65535 (LENGTH / DERIVED: address-space and value bounds). No ADDRESS: entry, GOT word
   (A_prog_val (A_OBJ 0) = 0xa2010 at A') and shadow cell (A_prog_val (A_OBJ 12) = 0xaaeb8) are A_prog_sigma /
   A_prog_val terms; the comments' A 0x.. addresses are the A' listing's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP YImgTop YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import ExsA_Callee.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition EXH_PC : Z := A_prog_sigma AS_ex_hex4.
Definition EXH_GOT : Z := A_prog_val (A_OBJ 0).
Definition EXH_CELL : Z := A_prog_val (A_OBJ 12).
Definition EXH_TBL : ctable := A_prog_tbl.
Definition EXH_Bx : sv := SOff 32 0.
Definition EXH_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition EXH_SRC (hi : Z) : afact := mkAF 4096 hi 0.
Definition EXH_OUTF : afact := mkAF (2 ^ 46) (2 ^ 47 - 4) 2.
Definition EXH_SPF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition EXH_SBF : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition exh_gotR : YP09.region :=
YP09.mkRegion None EXH_GOT (EXH_GOT + 8) 0 0 [YP09.mkChunk EXH_GOT (CVal 8 (SLit EXH_CELL))].
Definition exh_cellR : YP09.region :=
YP09.mkRegion None EXH_CELL (EXH_CELL + 8) 0 0 [YP09.mkChunk EXH_CELL (CVal 8 (SOff 32 0))].
Definition exh_stkE : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition exh_SHe : list shent := [mkSHE 10 0 4; mkSHE 11 0 4].
Definition ss_exh_e : sstate :=
mkSS EXH_PC sr_atoms [exh_stkE; exh_gotR; exh_cellR] None
(mkFacts [(2%nat, EXH_SPF); (10%nat, EXH_SRC (2 ^ 47 - 4)); (11%nat, EXH_OUTF); (32%nat, EXH_SBF)] [] []).
Definition EXH_BxL : sv := SOff 14 0.
Definition exh_stkL : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))].
Definition exh_curR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition exh_outR : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 4 [].
Definition exh_SHl : list shent := [mkSHE 32 0 1; mkSHE 11 0 4].
(* the loop head (A EXH_PC + 0x28): a2 = a0 = p + i (atom 32), a5 = 4 - i (atom 35), a6 = -10, a7 = 5, a3 = v
   (atom 34) *)
Definition exh_lregs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
  12%bv (SOff 32 0)) 10%bv (SOff 32 0)) 15%bv (SOff 35 0)) 16%bv (SLit (-10)))
  17%bv (SLit 5)) 13%bv (SOff 34 0).
Definition ss_exh_l : sstate :=
mkSS (EXH_PC + 0x28) exh_lregs [exh_stkL; exh_curR] None
(mkFacts [(2%nat, EXH_SPF); (11%nat, EXH_OUTF); (14%nat, EXH_SBF);
          (32%nat, EXH_SRC (2 ^ 47 - 1)); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 65535 0); (35%nat, mkAF 1 4 0)] [] []).
Definition exh_SHf : list shent := [mkSHE 11 0 4].
Definition exh_fregs : list sv := sr_set sr_atoms 13%bv (SOff 32 0).
Definition ss_exh_f : sstate :=
mkSS (EXH_PC + 0x9c) exh_fregs [exh_stkL; exh_outR] None
(mkFacts [(2%nat, EXH_SPF); (11%nat, EXH_OUTF); (14%nat, EXH_SBF); (32%nat, mkAF 0 65535 0)] [] []).
Definition ss_exh_q : sstate :=
mkSS (EXH_PC + 0xb8) sr_atoms [exh_stkL] None (mkFacts [(2%nat, EXH_SPF)] [] []).

(* ---- journal-free helpers (h-verbs-1's hex4_x.v / hex4_xs.v, d83df2ff2fa4, renamed exh_) ---- *)
Fixpoint exh_hacc (v : Z) (l : list Z) : option Z :=
match l with
| [] => Some v
| c :: r => match PjGrammar.hexval c with Some d => exh_hacc (16 * v + d) r | None => None end
end.
Lemma exh_hacc_hex4 : forall l, Z.of_nat (length l) = 4 -> exh_hacc 0 l = PjGrammar.hex4 l.
Proof.
intros l Hl.
destruct l as [|a [|b [|c [|d [|e l]]]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hl; try lia.
cbn [exh_hacc PjGrammar.hex4].
destruct (PjGrammar.hexval a) as [va|]; [|reflexivity].
destruct (PjGrammar.hexval b) as [vb|]; [|destruct (PjGrammar.hexval c); reflexivity].
destruct (PjGrammar.hexval c) as [vc|]; [|reflexivity].
destruct (PjGrammar.hexval d) as [vd|]; [|reflexivity].
cbn. f_equal. lia.
Qed.
(* the accumulator step `slli a3,a3,4 ; add a3,t0,a3` (A EXH_PC + 0x70, + 0x7c): 16 * v + digit *)
Lemma exh_acc_add : forall (E : env) (n1 n2 : nat) (cc vv delta : Z),
bv_unsigned (ew E n1) = cc -> bv_unsigned (ew E n2) = vv ->
0 <= vv < 4096 -> 0 <= cc + delta < 16 ->
sv_denot E (SAlu ALU_ADD (SOff n1 delta) (SAlu ALU_SLL (SOff n2 0) (SLit 4))) = w64 (16 * vv + (cc + delta)).
Proof.
intros E n1 n2 cc vv delta H1 H2 Hv Hd.
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_SOff E n1 delta), H1, (zcanon_id (cc + delta)) by (unfold M64; lia).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_SOff E n2 0), H2, Z.add_0_r, (zcanon_id vv) by (unfold M64; lia).
rewrite U_SLit, (zcanon_id 4) by (unfold M64; lia).
change (Z.land 4 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (zcanon_id (vv * 16)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* `bltz t0` after t0 := c + d (A EXH_PC + 0x50, + 0x6c): not taken when c + d >= 0 *)
Lemma exh_bltz_off : forall E (n : nat) d c, bv_unsigned (ew E n) = c -> 0 <= c + d < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n d)) (sv_denot E (SLit 0)) = false.
Proof.
intros E n d c Hc Hd. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff n d)). fold (U E (SLit 0)).
rewrite U_SOff, U_SLit, Hc, (zcanon_id (c + d)) by (unfold M64; lia). change (zcanon 0) with 0.
rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_ge. lia.
Qed.
(* a residue mod 2 ^ 64 of a value in (-2 ^ 64, 2 ^ 64) *)
Lemma exh_mod64_cases : forall x, - 2 ^ 64 <= x < 2 ^ 64 ->
(0 <= x /\ x mod 2 ^ 64 = x) \/ (x < 0 /\ x mod 2 ^ 64 = x + 2 ^ 64).
Proof.
intros x Hx. destruct (Z.le_gt_cases 0 x) as [H|H].
- left. split; [exact H|]. apply Z.mod_small. lia.
- right. split; [exact H|]. rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Local Ltac exh_unmod H :=
repeat match type of H with
| context [?x mod 2 ^ 64] =>
  let Hc := fresh "Hc" in let Hm := fresh "Hm" in
  destruct (exh_mod64_cases x ltac:(lia)) as [[Hc Hm]|[Hc Hm]]; rewrite Hm in H; clear Hm
end.
Local Ltac hexval_solve :=
unfold PjGrammar.hexval;
repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
first [ reflexivity | f_equal; lia | exfalso; lia ].
Lemma exh_no_wrange_lc : forall E a, ~ in_wrange E [exh_stkL; exh_curR] a.
Proof.
intros E a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
unfold exh_stkL, exh_curR in Hr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Definition exh_src_ok (p : Z) : Prop := 4096 <= p /\ (p + 4 < 0x7fff8000 \/ (0x10007fff8000 <= p /\ p + 4 < 2 ^ 47)).
Definition exh_out_ok (o : Z) : Prop := 2 ^ 46 <= o /\ o + 4 <= 2 ^ 47.
Lemma exh_obj_bounds : 4096 <= EXH_GOT /\ EXH_GOT + 8 <= EXH_CELL /\ EXH_CELL + 8 <= 2 ^ 32.
Proof.
unfold EXH_GOT, EXH_CELL.
let g := eval vm_compute in (A_prog_val (A_OBJ 0)) in change (A_prog_val (A_OBJ 0)) with g.
let c := eval vm_compute in (A_prog_val (A_OBJ 12)) in change (A_prog_val (A_OBJ 12)) with c.
lia.
Qed.
Lemma exh_ret_ok_mod2 : forall k : word, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
apply (f_equal bv_unsigned) in H. rewrite Z_to_bv_unsigned in H.
assert (Hb : Z.testbit (bv_unsigned k) 0 = false).
{ rewrite <- H at 1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec.
replace (Z.testbit (-2) 0) with false by reflexivity. apply andb_false_r. }
rewrite Z.bit0_odd in Hb. rewrite Zmod_odd, Hb. reflexivity.
Qed.
Definition EXH_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma exh_regs_pres_of_kept : forall (regs regs' : bvmap 5 word),
(forall r, In r EXH_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 ->
aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. cbv [acallee_saved] in Hr.
assert (Hall : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22
\/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat match goal with
| H : _ \/ _ |- _ => destruct H as [->|H];
[ first [exact H2 | apply HK; cbv [EXH_KEPT In];
solve [repeat first [(left; apply bv_eq; vm_compute; reflexivity) | right]]] | ]
| H : r = _ |- _ => rewrite H;
first [exact H2 | apply HK; cbv [EXH_KEPT In];
solve [repeat first [(left; apply bv_eq; vm_compute; reflexivity) | right]]]
end.
Qed.
(* the loop-head registers at the i-th digit (A EXH_PC + 0x28): a0 = a2 = p + i (the load and the shadow cursors),
   a3 = v, a4 = the shadow offset, a5 = 4 - i, a6 = -10, a7 = 5 *)
Definition exh_turn_regs (regs : bvmap 5 word) (p i o v sp : Z) : Prop :=
getr regs 2 = w64 sp /\ getr regs 10 = w64 (p + i) /\
getr regs 11 = w64 o /\ getr regs 12 = w64 (p + i) /\ getr regs 13 = w64 v /\
getr regs 14 = w64 SHADOW_OFF /\ getr regs 15 = w64 (4 - i) /\ getr regs 16 = w64 (-10) /\ getr regs 17 = w64 5.

(* ---- YCbqG's table runners SRr_run_tok_AJx / SRr_run_to_tok_AJx carrying a memory invariant Pinv (YC80x
   srr_inv_laws; the run step is YC80x.SRr_msteps_inv). The shape of h-verbs-1's hex4_mn.v Section tw
   (d83df2ff2fa4, blob a0acac4a3e17), with its msteps_keeps hypothesis replaced by srr_inv_laws. ---- *)
Section tw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs Pinv.
Definition exh_run_post (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
Pinv (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma exh_chain : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exh_run_post W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_inv segs Hwx Pinv PLAW W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec (SK := SK) segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma exh_run : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exh_run_post W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply exh_chain; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
Lemma exh_run_to : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exh_run_post W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply exh_chain; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
End tw.

(* ---- the walk (h-verbs-1's hex4 walk, hex4_x.v / hex4_mn.v at d83df2ff2fa4, re-pointed at ex_hex4: its loop head
   is EXH_PC + 0x28, its digit tests are `bgeu c - 58, -10` / `bltu 5, c - 97` / `bltu 5, c - 65` with a `bltz` after
   the two letter subtractions, its accumulator step is `add`, and a0 / a2 carry the cursor) ---- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
(* PALib's pal_got_shadow / pal_cell (YC1fP.v) at PI_prog_A, as ex_ws_x.v's EXW_HGOT / EXW_HCELL *)
Hypothesis EXH_HGOT : as_got_shadow B = EXH_GOT.
Hypothesis EXH_HCELL : as_shadow_cell B = EXH_CELL.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws rsegs Pinv.
Let RUNP := exh_run SK rsegs B PST ARx LAWS A_prog_segs_low A_prog_wx EXH_TBL A_prog_tbl_ok Pinv PLAW.
Let RUNTOP := exh_run_to SK rsegs B PST ARx LAWS A_prog_segs_low A_prog_wx EXH_TBL A_prog_tbl_ok Pinv PLAW.
Let RET := @SRr_ret_at rsegs fx EXH_TBL A_prog_tbl_ok A_prog_wx.
Lemma exh_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma exh_frame_aview : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs m m' H a HF Ha Hw. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hw). reflexivity.
Qed.
Definition exh_keeps (W : world rsegs) (m m' : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x.
Lemma exh_keeps_val_mem : forall W m m' a (n : nat) val,
exh_keeps W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) m) a n val -> val_mem rsegs (mrestrict (w_H W) m') a n val.
Proof.
intros W m m' a n val HK Ha Han HV j Hj.
assert (Hx : 0 <= a + Z.of_nat j < 2 ^ 64) by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) m m' (a + Z.of_nat j) (HK _ Hx)). exact (HV j Hj).
Qed.
Lemma exh_keeps_garr8 : forall W m m' a (l : list Z),
exh_keeps W m m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
garr8 rsegs (mrestrict (w_H W) m) a l -> garr8 rsegs (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HK Ha Hal HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
assert (H1 : 0 <= a + Z.of_nat j) by lia.
assert (H2 : a + Z.of_nat j + Z.of_nat 1 <= 2 ^ 64) by (cbn; lia).
exact (exh_keeps_val_mem W m m' (a + Z.of_nat j) 1 (nth j l 0) HK H1 H2 HV).
Qed.
Lemma exh_keeps_ra : forall W m m' a n,
exh_keeps W m m' -> 0 <= a -> a + n <= 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. rewrite HK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF in *. lia.
Qed.
Lemma exh_keeps_trans : forall W m1 m2 m3, exh_keeps W m1 m2 -> exh_keeps W m2 m3 -> exh_keeps W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx), (H1 x Hx). reflexivity. Qed.
Lemma exh_keeps_refl : forall W m, exh_keeps W m m.
Proof. intros W m x Hx. reflexivity. Qed.
Lemma exh_keeps_of_frame : forall W E (rs : smem) m m',
(forall a, ~ in_wrange E rs a) -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> exh_keeps W m m'.
Proof. intros W E rs m m' Hn HF x Hx. exact (exh_frame_aview E rs m m' (w_H W) x HF Hx (Hn x)). Qed.
Lemma exh_awr_ok_lc : forall E STK sp0 FP bl0 blc ly own, awr_ok E [exh_stkL; exh_curR] STK sp0 FP bl0 blc ly own.
Proof. intros E STK sp0 FP bl0 blc ly own a Ha. exfalso. exact (exh_no_wrange_lc E a Ha). Qed.
Lemma exh_hexval_range : forall c d, PjGrammar.hexval c = Some d -> 0 <= d < 16.
Proof.
intros c d. unfold PjGrammar.hexval.
repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
intro Hs; try discriminate Hs; injection Hs as E; subst d; lia.
Qed.
Lemma exh_garr8_hd : forall (W : world rsegs) m a c l, garr8 rsegs (mrestrict (w_H W) m) a (c :: l) ->
val_mem rsegs (mrestrict (w_H W) m) a 1 c /\ 0 <= c < 256.
Proof.
intros W m a c l HG. destruct (HG 0%nat ltac:(cbn; lia)) as [HV Hr]. cbn [nth] in HV, Hr.
rewrite Z.add_0_r in HV. split; [exact HV | exact Hr].
Qed.
Lemma exh_garr8_tl : forall (W : world rsegs) m a c l, garr8 rsegs (mrestrict (w_H W) m) a (c :: l) ->
garr8 rsegs (mrestrict (w_H W) m) (a + 1) l.
Proof.
intros W m a c l HG j Hj. destruct (HG (S j) ltac:(cbn; lia)) as [HV Hr]. cbn [nth] in HV, Hr.
replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. split; [exact HV | exact Hr].
Qed.
Definition exh_keeps_out (W : world rsegs) (lo hi : Z) (m m' : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x.
Lemma exh_out_val_mem : forall (W : world rsegs) lo hi m m' a (n : nat) val,
exh_keeps_out W lo hi m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
val_mem rsegs (mrestrict (w_H W) m) a n val -> val_mem rsegs (mrestrict (w_H W) m') a n val.
Proof.
intros W lo hi m m' a n val HK Ha Han Hd HV j Hj.
assert (Hx : 0 <= a + Z.of_nat j < 2 ^ 64) by lia.
assert (Hnx : ~ (lo <= a + Z.of_nat j < hi)) by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) m m' (a + Z.of_nat j) (HK _ Hx Hnx)). exact (HV j Hj).
Qed.
Lemma exh_out_garr8 : forall W lo hi m m' a (l : list Z),
exh_keeps_out W lo hi m m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
(a + Z.of_nat (length l) <= lo \/ hi <= a) ->
garr8 rsegs (mrestrict (w_H W) m) a l -> garr8 rsegs (mrestrict (w_H W) m') a l.
Proof.
intros W lo hi m m' a l HK Ha Hal Hd HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
assert (H1 : 0 <= a + Z.of_nat j) by lia.
assert (H2 : a + Z.of_nat j + Z.of_nat 1 <= 2 ^ 64) by (cbn; lia).
assert (H3 : a + Z.of_nat j + Z.of_nat 1 <= lo \/ hi <= a + Z.of_nat j) by (cbn; lia).
exact (exh_out_val_mem W lo hi m m' (a + Z.of_nat j) 1 (nth j l 0) HK H1 H2 H3 HV).
Qed.
Lemma exh_out_ra : forall W lo hi m m' a n,
exh_keeps_out W lo hi m m' -> 0 <= a -> a + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 44 <= lo ->
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W lo hi m m' a n HK Ha Han Hlo HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
rewrite HK; [exact Hs | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia].
Qed.
Lemma exh_entry_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok rsegs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok rsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Local Ltac xbr cnd a b HS Hc := apply (SRr_sym_branch rsegs _ _ _ _ _ _ cnd a b HS); clear HS; intros Hc HS.
Local Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Local Ltac zcond H :=
rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_ne_U, ?branch_eq_U in H;
rewrite ?U_SOff, ?U_SLit in H;
repeat (rewrite ew_ewset_other in H by lia);
repeat match goal with
| H' : negb _ = true |- _ => apply negb_true_iff in H'
| H' : negb _ = false |- _ => apply negb_false_iff in H'
| H' : (_ <? _) = true |- _ => apply Z.ltb_lt in H'
| H' : (_ <? _) = false |- _ => apply Z.ltb_ge in H'
| H' : (_ =? _) = true |- _ => apply Z.eqb_eq in H'
| H' : (_ =? _) = false |- _ => apply Z.eqb_neq in H'
end;
unfold zcanon, M64 in H.
Local Ltac kept_at regs0 extra0 HS HAE HKK :=
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs0 extra0 EXH_KEPT HS
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKK;
cbn [ms_regs restrict] in HKK.
Local Ltac acc_tac cc vv delta U33 U34 :=
apply (exh_acc_add _ 33 34 cc vv delta);
[ repeat (rewrite ew_ewset_other by lia); exact U33
| repeat (rewrite ew_ewset_other by lia); exact U34
| lia | lia ].
Local Ltac cnt_tac ii Hcnt U35 :=
zcond Hcnt; rewrite U35 in Hcnt;
rewrite (Z.mod_small (4 - ii + -1)) in Hcnt by lia; rewrite (Z.mod_small 0) in Hcnt by lia; lia.
Local Ltac xrunP HS HJ HPM SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_runN_tok rsegs EXH_TBL K Bx EXH_SPAN SH 200000%N ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok rsegs EXH_TBL K Bx EXH_SPAN SH 200000%N ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNP W 200000%N E K Bx EXH_SPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ | exact HPM
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ HPM SHOK ]
end end end.
Local Ltac xruntoP stop HS HJ HPM SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_run_toN_tok rsegs EXH_TBL K Bx EXH_SPAN SH 200000%N stop ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok rsegs EXH_TBL K Bx EXH_SPAN SH 200000%N stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTOP W 200000%N stop E K Bx EXH_SPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ | exact HPM
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ HPM SHOK ]
end end end.
Local Ltac xafterP HS HJ HPM SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM.
Local Ltac xafter2P W HKEEP HGROW HS HJ HPM SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in let Hlen := fresh "Hlen" in
let HFa := fresh "HFa" in let HFb := fresh "HFb" in let HGc := fresh "HGc" in
let HK2 := fresh "HK2" in let HG2 := fresh "HG2" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HFa HFb HGc;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HFa, HFb, HGc, HJ, HPM;
pose proof (exh_keeps_trans W _ _ _ HKEEP (exh_keeps_of_frame W _ _ _ _ (exh_no_wrange_lc _) HFb)) as HK2;
clear HKEEP; rename HK2 into HKEEP;
pose proof (mem_grows_trans _ _ _ HGROW HGc) as HG2;
clear HGROW; rename HG2 into HGROW;
clear HFa HFb HGc.
(* after a digit d = cc + delta: the run to the counter test `bnez a5` (EXH_PC + 0x84), the test, and the next loop
   head (EXH_PC + 0x28) or the store tail (EXH_PC + 0x9c) *)
Local Ltac xtailP W regs0 extra0 pp ii cc vv delta KS KE E2 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK :=
let Hcnt := fresh "Hcnt" in
let Q2 := fresh "Q2" in
let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in
let Q14 := fresh "Q14" in let Q15 := fresh "Q15" in let Q16 := fresh "Q16" in let Q17 := fresh "Q17" in
let HKK := fresh "HKK" in
xruntoP (EXH_PC + 0x84) HS HJ HPM SHOK; [ apply exh_awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
xbr BC_NE (SOff 35 (-1)) (SLit 0) HS Hcnt;
[ xruntoP (EXH_PC + 0x28) HS HJ HPM SHOK; [ apply exh_awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
prreg HS (2%bv : bv 5) Q2;
prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
prreg HS (12%bv : bv 5) Q12; prreg_raw HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14;
prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16; prreg HS (17%bv : bv 5) Q17;
kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KS (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ | exact HPM
| unfold exh_turn_regs; repeat split;
  [ rewrite Q2, E2; reflexivity
  | rewrite Q10, U32; unfold w64; f_equal; lia
  | rewrite Q11, E11; reflexivity
  | rewrite Q12, U32; unfold w64; f_equal; lia
  | rewrite Q13; acc_tac cc vv delta U33 U34
  | rewrite Q14, E14; reflexivity
  | rewrite Q15, U35; unfold w64; f_equal; lia
  | rewrite Q16; reflexivity | rewrite Q17; reflexivity ]
| exact HKK ]
| xruntoP (EXH_PC + 0x9c) HS HJ HPM SHOK; [ apply exh_awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
prreg HS (2%bv : bv 5) Q2; prreg HS (11%bv : bv 5) Q11; prreg_raw HS (13%bv : bv 5) Q13;
prreg HS (14%bv : bv 5) Q14; kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KE (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ | exact HPM
| rewrite Q2, E2; reflexivity | rewrite Q11, E11; reflexivity | rewrite Q13; acc_tac cc vv delta U33 U34
| rewrite Q14, E14; reflexivity | exact HKK ] ].

(* ---- entry: the symbolic state at A EXH_PC from the premises (the GOT word and the shadow cell by EXH_HGOT /
   EXH_HCELL and AR_laws_x's alx_const) ---- *)
Lemma exh_entry_ok : forall (W : world rsegs) regs memc mdc ly S Hp p o sp,
ARx ly S Hp W memc mdc ->
getr regs 2 = w64 sp -> 2 ^ 46 <= sp - 16 -> sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
exh_src_ok p -> exh_out_ok o -> o mod 4 = 0 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, sp - 16 <= x < sp -> apresent (w_H W) memc x) ->
st_ok rsegs (Ereg regs [w64 SHADOW_OFF]) ss_exh_e
(restrict (w_H W) (mkst regs (w64 EXH_PC) memc (seg_rom rsegs)))
/\ sh_ok rsegs EXH_Bx exh_SHe (Ereg regs [w64 SHADOW_OFF]) (mrestrict (w_H W) memc).
Proof.
intros W regs memc mdc ly S Hp p o sp HAR R2 Hsp0 Hsp1 Hsp16 R10 R11 HPa HOa HOal RAp RAo HPres.
pose proof (alx_const rsegs B ARx LAWS ly S Hp W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite EXH_HGOT, EXH_HCELL in Kgot. rewrite EXH_HCELL in Kcell.
destruct HPa as (HPlo & HPhi). destruct HOa as (HOlo & HOhi).
pose proof exh_obj_bounds as (Hg1 & Hgc & Hc2).
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
set (E := Ereg regs [w64 SHADOW_OFF]).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew E 10 = w64 p) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UBx : U E EXH_Bx = SHADOW_OFF) by (unfold EXH_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_exh_e. change (w64 EXH_PC) with (Z_to_bv 64 EXH_PC).
apply exh_entry_st_ok_full.
+ unfold E. apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, exh_stkE, exh_gotR, exh_cellR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
* rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros x Hx. apply (apresent_writable rsegs). apply HPres. lia.
* split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 EXH_GOT 8 (SLit EXH_CELL) EXH_CELL);
[cbn [sv_denot]; reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
* split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 EXH_CELL 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold exh_stkE, exh_gotR, exh_cellR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, EXH_SRC, EXH_OUTF, EXH_SPF, EXH_SBF. cbn [af_lo af_hi af_al2].
rewrite U2, U10, U11, U32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4.
rewrite !Z.mod_1_r. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, exh_SHe. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range rsegs (w_H W) memc E EXH_Bx 10 p 4 p 0 4 RAp UBx);
[apply (U_atom E 10 p E10); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
+ apply (shent_ok_of_range rsegs (w_H W) memc E EXH_Bx 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- the store tail (A EXH_PC + 0x9c): out's shadow (`srli a0,a1,3 ; add a0,a0,a4 ; lb a0,0(a0) ; bnez a0`), the
   4-byte store `sw a3,0(a1)` (EXH_PC + 0xb0), return 0 ---- *)
Lemma exh_finalP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
getr regs 2 = w64 sp -> getr regs 11 = w64 o -> getr regs 13 = w64 h -> getr regs 14 = w64 SHADOW_OFF ->
0 <= h < 65536 ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
exh_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (EXH_PC + 0x9c)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r EXH_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 0 /\
val_mem rsegs (mrestrict (w_H W) mem') o 4 h /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)).
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0
HJ HPM R1 Hra Hra2 R2 R11 R13 R14 Hh Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HOa HOal RAo HAWR HOpres HOsep.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 h]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 h) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U1 : bv_unsigned (ew E 1) = ra0) by (rewrite E1; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = h) by (rewrite E32; apply unsigned_lit_small; lia).
assert (UBx : U E EXH_BxL = SHADOW_OFF) by (unfold EXH_BxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_exh_f (restrict (w_H W) (mkst regs (w64 (EXH_PC + 0x9c)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exh_f. unfold w64 at 1. apply exh_entry_st_ok_full.
- unfold exh_fregs. apply regs_ok_pin; [unfold E; apply regs_ok_Ereg | discriminate |].
cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R13.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, exh_stkL, exh_outR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U11. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [|constructor].
intros x Hx. apply (apresent_writable rsegs). apply HOpres. lia.
- apply pairwise_disjoint_of_extents. unfold exh_stkL, exh_outR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U11.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, EXH_OUTF, EXH_SPF, EXH_SBF. cbn [af_lo af_hi af_al2].
rewrite U2, U11, U14, U32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4.
rewrite !Z.mod_1_r. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs EXH_BxL exh_SHf E (mrestrict (w_H W) memc)).
{ unfold sh_ok, exh_SHf. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E EXH_BxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
xrunP HS HJ HPM SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_exh_f In] in Hin;
destruct Hin as [<-|[<-|[]]]; unfold exh_stkL, exh_outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply HAWR; lia ]. }
intros ws ms' mat' Hlen HS' SHOK' HJ' HPM' HF HFr HG.
cbn [sh_j sh_ss] in Hlen, HS', SHOK'.
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]).
destruct ws; [clear Hlen | discriminate Hlen].
cbn [extK length Nat.add] in HS', SHOK'.
cbn [ms_mem mkst] in HF, HFr, HG, HJ', HPM'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs [w64 h]) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 h] EXH_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
pose proof (exh_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 11%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))]) HS' eq_refl) as HRout.
destruct HRout as (_ & _ & _ & Hcs).
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
cbn [YP09.r_base YP09.r_chunks YP09.c_off YP09.c_val base_val] in Hcs.
rewrite !ew_ewset_other in Hcs by lia. rewrite U11 in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)) as Hchunk. clear Hcs.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS A_prog_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HPM'|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; reflexivity|].
split.
- cbn [ms_mem restrict] in Hchunk |- *.
assert (HV : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (o + 0) (N.to_nat 4) h).
{ lazymatch type of Hchunk with YP09.chunk_ok _ ?EE _ _ _ =>
apply (val_of_chunk_ok rsegs EE _ o 0 4 (SOff 32 0) h) end;
[ exact Hchunk
| cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; lia | lia]. }
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HV. rewrite Z.add_0_r in HV. exact HV.
- intros x Hx Hnot. cbn [ms_mem].
apply (exh_frame_aview E (ss_mem ss_exh_f) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_exh_f In] in Hin.
destruct Hin as [<-|[<-|[]]]; unfold exh_stkL, exh_outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply Hnot; lia ].
Qed.

(* ---- the failure return (A EXH_PC + 0xb8): a0 = -1, nothing written ---- *)
Lemma exh_failretP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 -> getr regs 2 = w64 sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
SRr rsegs W (mkCfg (mkst regs (w64 (EXH_PC + 0xb8)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r EXH_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 (-1) /\ exh_keeps W memc mem').
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0
HJ HPM R1 Hra Hra2 R2 Hsp16 Hsplo Hsphi Mra.
set (E := Ereg regs (@nil word)).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_exh_q (restrict (w_H W) (mkst regs (w64 (EXH_PC + 0xb8)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exh_q. unfold w64 at 1. apply exh_entry_st_ok_full.
- unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, exh_stkL;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, EXH_SPF. cbn [af_lo af_hi af_al2].
rewrite U2. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs EXH_BxL (@nil shent) E (mrestrict (w_H W) memc)) by (unfold sh_ok; apply Forall_nil).
xrunP HS HJ HPM SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_exh_q In] in Hin;
destruct Hin as [<-|[]]; unfold exh_stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
xafterP HS' HJ' HPM' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs (@nil word) EXH_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS A_prog_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HPM'|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; apply bv_eq; vm_compute; reflexivity|].
intros x Hx. cbn [ms_mem].
apply (exh_frame_aview E (ss_mem ss_exh_q) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_exh_q In] in Hin.
destruct Hin as [<-|[]]; unfold exh_stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.

(* ---- one digit (A EXH_PC + 0x28 to + 0x84): the cursor's shadow check (shent of range_addressable p 4), the byte c
   (`lbu t0,0(a0)`), the three range tests and the two `bltz`s after the letter subtractions (refuted: c - 87 >= 10
   and c - 55 >= 10 on their arms) ---- *)
Lemma exh_turnP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o sp ra0 i v c (Q : world rsegs -> config -> Prop),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
0 <= i <= 3 -> 0 <= v < 4096 -> 0 <= c < 256 ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 ->
exh_turn_regs regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
exh_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
val_mem rsegs (mrestrict (w_H W) memc) (p + i) 1 c ->
exh_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(sp + 16 <= p \/ p + 4 <= sp) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 <> 0 ->
exh_keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
exh_turn_regs regs2 p (i + 1) o (16 * v + d) sp ->
(forall r, In r EXH_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (EXH_PC + 0x28)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 = 0 ->
exh_keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
getr regs2 2 = w64 sp -> getr regs2 11 = w64 o -> getr regs2 13 = w64 (16 * v + d) ->
getr regs2 14 = w64 SHADOW_OFF ->
(forall r, In r EXH_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (EXH_PC + 0x9c)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall mem2 mdc2 regs2, PjGrammar.hexval c = None ->
exh_keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
getr regs2 2 = w64 sp ->
(forall r, In r EXH_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (EXH_PC + 0xb8)) mem2 (seg_rom rsegs)) mdc2) Q) ->
SRr rsegs W (mkCfg (mkst regs (w64 (EXH_PC + 0x28)) memc (seg_rom rsegs)) mdc) Q.
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c Q
HJ HPM Hi Hv Hc256 R1 Hra (R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17)
Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p KS KE KF.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HPa as (HPlo & HPhi).
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 (p + i)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 v) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (4 - i)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p + i) by (rewrite E32; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 4 - i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (UBx : U E EXH_BxL = SHADOW_OFF) by (unfold EXH_BxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_exh_l (restrict (w_H W) (mkst regs (w64 (EXH_PC + 0x28)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exh_l. unfold w64 at 1. apply exh_entry_st_ok_full.
- unfold exh_lregs.
repeat (apply regs_ok_pin; [|discriminate|cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [exact R12 | exact R10 | exact R15 | exact R16 | exact R17 | exact R13
| rewrite E32; exact R12 | rewrite E32; exact R10 | rewrite E35; exact R15 | rewrite E34; exact R13]]).
unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, exh_stkL, exh_curR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U32. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ (p + i) 0 1 (SOff 33 0) c);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Mc.
- apply pairwise_disjoint_of_extents. unfold exh_stkL, exh_curR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, EXH_SRC, EXH_OUTF, EXH_SPF, EXH_SBF. cbn [af_lo af_hi af_al2].
rewrite U2, U11, U14, U32, U33, U34, U35.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4. rewrite !Z.mod_1_r.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs EXH_BxL exh_SHl E (mrestrict (w_H W) memc)).
{ unfold sh_ok, exh_SHl. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E EXH_BxL 32 p 4 (p + i) 0 1 RAp UBx);
[apply (U_atom E 32 (p + i) E32); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E EXH_BxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HAE : env_agree 32 (Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]) E)
by (unfold E; apply env_agree_refl).
assert (HKEEP : exh_keeps W memc memc) by apply exh_keeps_refl.
assert (HGROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
(* A EXH_PC + 0x28 .. + 0x3c: the shadow check of a2 = p + i (decided by exh_SHl), `lbu t0,0(a0)`, t1 := c - 58 *)
xrunP HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
(* A EXH_PC + 0x40 `bgeu c - 58, -10`: taken iff c is a decimal digit *)
xbr BC_GEU (SOff 33 (-58)) (SLit (-10)) HS Hb2.
+ zcond Hb2. rewrite U33 in Hb2.
assert (Nd : 48 <= c <= 57) by (clear - Hb2 Hc256; exh_unmod Hb2; lia). clear Hb2.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-48) KS KE E2 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
+ zcond Hb2. rewrite U33 in Hb2.
assert (Nd : ~ (48 <= c <= 57)) by (clear - Hb2 Hc256; exh_unmod Hb2; lia). clear Hb2.
xrunP HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
(* A EXH_PC + 0x48 `bltu 5, c - 97`: not taken iff c is a lower-case hex letter *)
xbr BC_LTU (SLit 5) (SOff 33 (-97)) HS Hb3.
* zcond Hb3. rewrite U33 in Hb3.
assert (Nl : ~ (97 <= c <= 102)) by (clear - Hb3 Hc256; exh_unmod Hb3; lia). clear Hb3.
xrunP HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
(* A EXH_PC + 0x64 `bltu 5, c - 65`: not taken iff c is an upper-case hex letter *)
xbr BC_LTU (SLit 5) (SOff 33 (-65)) HS Hb4.
-- zcond Hb4. rewrite U33 in Hb4.
assert (Nu : ~ (65 <= c <= 70)) by (clear - Hb4 Hc256; exh_unmod Hb4; lia). clear Hb4.
xruntoP (EXH_PC + 0xb8) HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
prreg HS (2%bv : bv 5) Q2. kept_at regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] HS HAE HKK.
pmkst HS.
eapply KF; [ hexval_solve | exact HKEEP | exact HGROW | exact HJ | exact HPM | rewrite Q2, E2; reflexivity | exact HKK ].
-- zcond Hb4. rewrite U33 in Hb4.
assert (Nu : 65 <= c <= 70) by (clear - Hb4 Hc256; exh_unmod Hb4; lia). clear Hb4.
xrunP HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
(* A EXH_PC + 0x6c `bltz c - 55`: not taken, c - 55 >= 10 *)
xbr BC_LT (SOff 33 (-55)) (SLit 0) HS Hb5.
++ exfalso. rewrite (exh_bltz_off _ 33 (-55) c) in Hb5; [discriminate Hb5 | | lia].
repeat (rewrite ew_ewset_other by lia). exact U33.
++ clear Hb5.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-55) KS KE E2 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
* zcond Hb3. rewrite U33 in Hb3.
assert (Nl : 97 <= c <= 102) by (clear - Hb3 Hc256; exh_unmod Hb3; lia). clear Hb3.
xrunP HS HJ HPM SHOK. { apply exh_awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
(* A EXH_PC + 0x50 `bltz c - 87`: not taken, c - 87 >= 10 *)
xbr BC_LT (SOff 33 (-87)) (SLit 0) HS Hb5.
-- exfalso. rewrite (exh_bltz_off _ 33 (-87) c) in Hb5; [discriminate Hb5 | | lia].
repeat (rewrite ew_ewset_other by lia). exact U33.
-- clear Hb5.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-87) KS KE E2 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
Qed.
Definition exh_loop_post (W : world rsegs) regs (STK sp0 : Z) FP ly S Hp W0 mem0 md0 own lyc Sc Hpc
(memc : word -> option byte) (k o sp : Z) (res : option Z) : world rsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r EXH_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
match res with
| Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
end.
(* the loop from the i-th digit on (n = 3 - i more turns) *)
Lemma exh_loopP : forall (n : nat) (i v : Z) (W : world rsegs) regs memc mdc
STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 (rest : list Z),
Z.of_nat n = 3 - i -> 0 <= i <= 3 -> 0 <= v < 16 ^ i ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
exh_turn_regs regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
exh_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 rsegs (mrestrict (w_H W) memc) (p + i) rest -> Z.of_nat (length rest) = 4 - i ->
exh_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= p \/ p + 4 <= sp) -> (sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (EXH_PC + 0x28)) memc (seg_rom rsegs)) mdc)
(exh_loop_post W regs STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k o sp (exh_hacc v rest)).
Proof.
induction n as [|n IH]; intros i v W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest
Hn Hi Hv HJ HPM R1 Hra Hra2 TR Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HPa RAp GBS Hlen HOa HOal RAo HAWR HOpres Hsp_p Hsp_o;
(pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL);
(pose proof HPa as (HPlo & HPhi));
(pose proof HOa as (HOlo & HOhi));
(destruct rest as [|c rest']; [cbn [length] in Hlen; exfalso; lia|]);
(destruct (exh_garr8_hd W memc (p + i) c rest' GBS) as (Mc & Hc256));
(cbn [length] in Hlen);
(assert (Hvb : 0 <= v < 4096)
by (assert (16 ^ i <= 16 ^ 3) by (apply Z.pow_le_mono_r; lia); cbn in *; lia));
(eapply (exh_turnP W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c _
HJ HPM Hi Hvb Hc256 R1 Hra TR Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p)).
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 HPM2 TR2 HKK. exfalso. lia. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 HPM2 R2' R11' R13' R14' HKK.
pose proof (exh_hexval_range c d Hhv) as Hd.
assert (Hi3 : i = 3) by lia.
eapply SRr_mono.
- eapply (exh_finalP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp (16 * v + d) ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2' | exact R11' | exact R13' | exact R14'
| subst i; cbn in Hv; lia | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (exh_keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HOa | exact HOal
| exact (exh_keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & MV & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [exh_hacc]. rewrite Hhv.
assert (Hr0 : rest' = []) by (destruct rest' as [|y r2]; [reflexivity | cbn [length] in Hlen; exfalso; lia]).
rewrite Hr0. cbn [exh_hacc]. split; [exact R10' | exact MV]. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 HPM2 R2' HKK.
eapply SRr_mono.
- eapply (exh_failretP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (exh_keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [exh_hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 HPM2 TR2 HKK.
pose proof (exh_hexval_range c d Hhv) as Hd.
eapply SRr_mono.
- eapply (IH (i + 1) (16 * v + d) W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest');
[ lia | lia | rewrite Z.pow_add_r by lia; cbn [Z.pow Z.pow_pos Pos.iter]; lia
| exact HJ2 | exact HPM2 | rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2
| exact TR2 | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (exh_keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HPa
| exact (exh_keeps_ra W memc mem2 p 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAp)
| replace (p + (i + 1)) with (p + i + 1) by lia;
exact (exh_keeps_garr8 W memc mem2 (p + i + 1) rest' HK2 ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) (exh_garr8_tl W memc (p + i) c rest' GBS))
| lia | exact HOa | exact HOal
| exact (exh_keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_p | exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & HKEEP' & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [exh_hacc]. rewrite Hhv.
destruct (exh_hacc (16 * v + d) rest') as [h|].
+ destruct Hres as (R10' & MV). split; [exact R10' | exact MV].
+ destruct Hres as (R10' & Hk). split; [exact R10' | intros x Hx; rewrite (Hk x Hx);
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 HPM2 R2' R11' R13' R14' HKK. exfalso. lia. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 HPM2 R2' HKK.
eapply SRr_mono.
- eapply (exh_failretP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (exh_keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [exh_hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
Qed.
(* entry to return: the prologue (frame, ra saved, the shadow offset loaded through the GOT word and the cell), the
   constants, and the loop from the first digit *)
Lemma exh_mainP : forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (p o : Z) (BS : list Z),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - EXH_STK -> spZ regs <= sp0 ->
(forall x, spZ regs - EXH_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
4096 <= p -> amem_range p 4 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 rsegs (mrestrict (w_H W) memc) p BS -> Z.of_nat (length BS) = 4 ->
spZ regs <= o -> o + 4 <= sp0 -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(o + 4 <= p \/ p + 4 <= o) ->
(spZ regs <= p \/ p + 4 <= spZ regs - EXH_STK) ->
SRr rsegs W (cfg_at rsegs EXH_PC regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\ Pinv mem' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - EXH_STK <= x < spZ regs) -> ~ (o <= x < o + 4) ->
aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
match PjGrammar.hex4 BS with
| Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
end).
Proof.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS
HJ HPM Hret Hra4 R10 R11 Hsp16 Hsp0a Hsp0b HPres HPlo HPam RAp GBS Hlen HOlo HOhi HOal RAo HOpres Hsep Hsp_p.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
assert (HPhi : p + 4 < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia).
assert (HPa : exh_src_ok p)
by (split; [exact HPlo | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof (exh_ret_ok_mod2 _ Hret) as Hra2.
assert (Hra64 : 4096 <= raZ regs < 2 ^ 64).
{ pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hx.
change (bv_modulus 64) with (2 ^ 64) in Hx. unfold raZ in *. lia. }
set (spE := spZ regs) in *. set (ra0 := raZ regs) in *.
assert (R1 : getr regs 1 = w64 ra0) by (unfold ra0, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R2 : getr regs 2 = w64 spE) by (unfold spE, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HspL : 2 ^ 46 <= spE - 16) by (unfold spE, EXH_STK, ASAN_CEIL in *; lia).
assert (HspH : spE <= 2 ^ 47) by (unfold spE, EXH_STK, ASAN_CEIL in *; lia).
assert (HOa : exh_out_ok o) by (unfold exh_out_ok; split; lia).
assert (HAWR : forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x)
by (intros x Hx; unfold awr_byte; left; unfold EXH_STK in Hsp0a; lia).
assert (Hsp_o : spE <= o \/ o + 4 <= spE - EXH_STK) by (left; exact HOlo).
destruct (exh_entry_ok W regs memc mdc lyc Sc Hpc p o spE (proj1 HJ) R2 HspL HspH Hsp16
R10 R11 HPa HOa HOal RAp RAo HPres) as (HS & SHOK).
unfold cfg_at.
xruntoP (EXH_PC + 0x28) HS HJ HPM SHOK.
{ intros a (r & Hin & Hr). cbn [ss_mem ss_exh_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold exh_stkE, exh_gotR, exh_cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ | lia | lia ].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. left. unfold EXH_STK in *. lia. }
xafterP HS' HJ' HPM' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
prreg HS' (11%bv : bv 5) P11. prreg HS' (12%bv : bv 5) P12. prreg HS' (13%bv : bv 5) P13.
prreg HS' (14%bv : bv 5) P14. prreg HS' (15%bv : bv 5) P15. prreg HS' (16%bv : bv 5) P16.
prreg HS' (17%bv : bv 5) P17.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (Ereg regs [w64 SHADOW_OFF])) by apply env_agree_refl.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 SHADOW_OFF] EXH_KEPT HS'
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKE.
cbn [ms_regs restrict] in HKE, P1, P2, P10, P11, P12, P13, P14, P15, P16, P17.
pose proof (exh_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS' eq_refl) as HRstk.
destruct HRstk as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs.
assert (HKO : exh_keeps_out W (spE - 16) spE memc (ms_mem msx)).
{ intros x Hx Hnot. apply (exh_frame_aview (Ereg regs [w64 SHADOW_OFF]) (ss_mem ss_exh_e) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_exh_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold exh_stkE, exh_gotR, exh_cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia|lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. lia. }
assert (Mra : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (spE - 16 + 8) 8 ra0).
{ replace (spE - 16 + 8) with (spE + -8) by lia.
apply (val_of_chunk_ok rsegs (Ereg regs [w64 SHADOW_OFF]) _ spE (-8) 8 (SOff 1 0) ra0);
[ | cbn [sv_denot]; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), R1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| lia | lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hcs. unfold w64 in Hcs.
rewrite (unsigned_lit_small spE) in Hcs by lia.
exact (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)). }
pmkst HS'.
eapply SRr_mono.
- eapply (exh_loopP 3%nat 0 0 W (ms_regs msx) (ms_mem msx) _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o (spE - 16) ra0 BS);
[ cbn; reflexivity | lia | cbn; lia | exact HJ' | exact HPM'
| rewrite P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1 | exact Hra64 | exact Hra2
| unfold exh_turn_regs; repeat split;
  [ rewrite P2, (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2; unfold w64;
rewrite (unsigned_lit_small spE) by lia; f_equal; lia
  | rewrite P10, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P11, (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11
  | rewrite P12, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P13; reflexivity
  | rewrite P14; cbn [ew Ereg nth Nat.ltb Nat.leb]; reflexivity
  | rewrite P15; unfold w64; f_equal; lia
  | rewrite P16; apply bv_eq; vm_compute; reflexivity | rewrite P17; reflexivity ]
| lia | lia | lia | unfold EXH_STK in Hsp0a; lia | lia
| exact Mra | exact HPa
| exact (exh_out_ra W (spE - 16) spE memc (ms_mem msx) p 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAp)
| rewrite Z.add_0_r;
exact (exh_out_garr8 W (spE - 16) spE memc (ms_mem msx) p BS HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)
ltac:(unfold EXH_STK in Hsp_p; lia) GBS)
| rewrite Z.sub_0_r; exact Hlen | exact HOa | exact HOal
| exact (exh_out_ra W (spE - 16) spE memc (ms_mem msx) o 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAo)
| exact HAWR
| intros x Hx; exact (apresent_grows (w_H W) memc (ms_mem msx) x HG (HOpres x Hx))
| unfold EXH_STK in Hsp_p; lia | unfold EXH_STK in Hsp_o; lia ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ2 & HPM2 & HKK & R2' & HKEEP & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); reflexivity|].
split; [exact HJ2|].
split.
{ apply (exh_regs_pres_of_kept regs regs').
- intros r Hr. rewrite (HKK r Hr). exact (HKE r Hr).
- rewrite R2', R2. unfold w64. f_equal. lia. }
split; [exact HPM2|].
split.
{ intros x Hx Hn1 Hn2. unfold EXH_STK in Hn1.
rewrite (HKEEP x Hx Hn2). exact (HKO x Hx ltac:(lia)). }
rewrite (exh_hacc_hex4 BS Hlen) in Hres.
destruct (PjGrammar.hex4 BS) as [h|].
+ exact Hres.
+ destruct Hres as (R10' & Hk). split; [exact R10'|].
intros x Hx. rewrite (Hk x Hx).
exact (HKO x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold EXH_STK in *; lia)).
Qed.
End a.

(* ---- THE RUN FORM: ex_hex4 at image A' proves ExsA_Callee.v's texhex4_runA at A_prog_sigma AS_ex_hex4, the
   memory invariant instantiated as the memnorm keep (YSRrMemnorm.srr_inv_laws_imp of srr_inv_laws_memnorm_k, as
   the donor's) ---- *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis EXH_HGOT : as_got_shadow B = A_prog_val (A_OBJ 0).
Hypothesis EXH_HCELL : as_shadow_cell B = A_prog_val (A_OBJ 12).
Theorem ex_hex4_run_A : texhex4_runA SK B PST ARx (A_prog_sigma AS_ex_hex4).
Proof.
unfold texhex4_runA.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS HJ.
exact (exh_mainP SK B PST ARx LAWS EXH_HGOT EXH_HCELL
  (fun m : word -> option byte => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m)
  (YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) memc (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs))
  STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS HJ (fun h => h)).
Qed.
End f.
