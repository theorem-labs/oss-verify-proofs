(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: what reac_grant_build_sweep's walk shares between its files (the cuts' symbolic states, the facts a cut carries, the cut lemmas' statements, and the walk's own tactics), adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v (the seat of a cut: submem, facts_incl, the havoc of the dead registers, and the writable-window case list of the flag-store run) and lib/A/ACa2.v (a loop walk split into cut-indexed lemmas); module paths changed. *)
(* reac_grant_build_sweep (fuzz_grant.asan 0x848f0) on the ASan build: what the
   walk of GrantBuildSweep.v's contract shares between files — the cuts'
   symbolic states (the loop head 0x84aec, the cell-loop head 0x84b04, the
   instruction after the loop 0x84b44), the facts every cut carries, the cut
   lemmas' statements, and the helper lemmas and tactics of the walk.
   GrantBuildSweepWalk.v proves the contract from the cut lemmas, which
   GrantBuildSweepWalk.v (head, induction), GrantBuildSweepCell.v (cell) and
   GrantBuildSweepTail.v (tail) prove. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC4b YC81 YC88 YCbw YCkd YC1g YC1h YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1i ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective CtrlBuildGrantSweepSpec.
(* CtrlFinish's names (tcj_kept, twr_ok, tsrc_ok) are used qualified: its SB would hide the one the walk tactics unfold. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require CtrlFinish.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Export GrantBuildSweep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- tactics ------------------------------------------------------------- *)
Ltac ulits := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
rewrite (unsigned_lit_small z) by (unfold SB in *; lia) end.
(* The writable windows of a flag-store run: the machine stack (the saved
   registers and the realigned frame), the side-stack frame and its shadow,
   and the flag byte itself. *)
Ltac bs_wrange AG fpos F EFA EFL Hsp1 FFS :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; rewrite FFS; clear - Hr Hsp1; lia
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| fail 2 "bs_wrange: a window outside the stack, the frame, its shadow and the flag" ]
| ]);
destruct Hin.
(* The dead registers deads to fresh atoms N, N+1, ... (their values). *)
Ltac bs_havoc_regs HS N deads :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS.
(* Seat a run's end on a cut: keep the regions rs (a subsequence of the
   state's regions, each a subregion of its partner) and the atom facts fa,
   and give the dead registers deads the atoms N, N+1, ... (through 900, so
   that the old atoms N.. leave the state first). The env stays
   `havoc _ N _` for the caller to read the new atoms' values. *)
Ltac bs_rejoin HS AG rs fa deads N :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in rs in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let fa' := eval vm_compute in fa in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa' [] [] HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
bs_havoc_regs HS 900%nat deads;
let HEv := fresh "HEv" in ACj1.rebaseE HS AG HEv; clear HEv;
bs_havoc_regs HS N deads.
(* Carry `HK : forall a, lo <= a < hi -> aview (cur mem) a = aview mem0 a`
   across a run whose writes HFr bounds: btac proves `0 <= a < 2 ^ 64` from
   `Ha_rng : lo <= a < hi`, and tac proves False from Ha_rng and `Hrg_rng`,
   a's place in one writable window (bounds as base_val terms; tac clears
   the context and evaluates them itself, which keeps its lia small). *)
Ltac upd_rngW HK HFr btac tac :=
let HK' := fresh "HK" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HK with forall a, ?lo <= a < ?hi -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HK' : forall a, lo <= a < hi -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in
intros a Ha_rng; refine (eq_trans _ (HK a Ha_rng)); apply aview_eq_of; apply HFr;
rewrite unsigned_lit_small by btac;
let rg := fresh "rg" in let Hin := fresh "Hin" in
intros (rg & Hin & Hrg_rng);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg_rng; tac |]);
destruct Hin
| clear HK; rename HK' into HK ] end end.
(* awrFL's rule for the row region (base atom 601 = F + 32 + 3c, three bytes,
   inside the own frame F): use as `awrFL_with ltac:(idtac; awr_row_rule AG fpos F
   EFA Hc Hw1) AG fpos F EFA` with Hc : 0 <= c < w and Hw1 : 1 <= w <= 40. *)
Ltac awr_row_rule AG fpos F EFA Hc Hw1 :=
lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 601%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?cl, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 601%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
right; right; right; exists cl, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; fsb_lits; rewrite ?EFA; fold F; clear - Ha Hc Hw1; lia
| ] end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* TBSW_STK (GrantBuildSweep.v) is the 192-byte machine frame, the 16 bytes the
   `andi sp,sp,-32` at 0x84930 may drop, and the deeper of the two callees'
   stacks (reac_ctrl_build_grant_sweep's). *)
Lemma TBSW_STK_callees : TBSW_STK = 208 + Z.max TEFF_STK TBGS_STK.
Proof. reflexivity. Qed.
(* The entry state's extra atoms: 32 the shadow base, 33 al[0] (base),
   34 al[1] (width), 35 al's shadow cell, 36 the byte that cell holds. *)
Definition bs_extra (al base w shv : Z) : list word := map (Z_to_bv 64) [SB; base; w; SB + al / 8; shv].
(* ---- the two cuts' symbolic states --------------------------------------- *)
(* Registers at both cuts. The atoms below 33 are the entry registers, 60 the
   realigned sp (s1), 516 the side-stack frame F, 528 its flag, 529 F's shadow
   cell. 600 is the loop counter (s8), 601 the next row's address F + 32 + 3c
   (s2); 602..619 are the dead registers ra, t0..t2, a0..a7, s9, s11, t3..t6. *)
Definition bs_deads : list (bv 5) := [24; 18; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 25; 27; 28; 29; 30; 31]%bv.
Definition bs_sr_L : list sv :=
[SLit 0; SOff 602 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 603 0; SOff 604 0; SOff 605 0;
SOff 2 0; SOff 60 0; SOff 606 0; SOff 607 0; SOff 608 0; SOff 609 0; SOff 610 0; SOff 611 0;
SOff 612 0; SOff 613 0; SOff 601 0; SOff 12 0; SOff 34 0; SOff 13 0; SLit 3; SOff 35 0;
SOff 600 0; SOff 614 0; SOff 529 0; SOff 615 0; SOff 616 0; SOff 617 0; SOff 618 0; SOff 619 0].
(* The byte al's shadow cell holds: 0, or (z = false) the atom 36, which is 2..7. *)
Definition bs_shc (z : bool) : sv := if z then SLit 0 else SOff 36 0.
(* The regions both cuts keep: al's shadow cell, al's two bytes, F's shadow
   (bytes 4..18, the values buffer's, marked usable), F's header (the
   epilogue writes F + 0), F's tail with the flag pointer at F + 248, the
   realigned frame's slots, and the saved registers. *)
Definition bs_RL0 (z : bool) : smem :=
[ YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (bs_shc z))];
YP09.mkRegion (Some 12%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))];
YP09.mkRegion (Some 529%nat) 0 32 0 32
[YP09.mkChunk 18 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 16 (CVal 1 (SLit 0));
YP09.mkChunk 15 (CVal 1 (SLit 0)); YP09.mkChunk 14 (CVal 1 (SLit 0)); YP09.mkChunk 13 (CVal 1 (SLit 0));
YP09.mkChunk 12 (CVal 1 (SLit 0)); YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 0));
YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0)); YP09.mkChunk 8 (CVal 1 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 152 256 152 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 88 0 88
[YP09.mkChunk 24 (CVal 8 (SOff 516 32)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 48 (CVal 8 (SOff 516 0));
YP09.mkChunk 56 (CVal 8 (SOff 516 0)); YP09.mkChunk 40 (CVal 8 (SOff 11 0)); YP09.mkChunk 32 (CVal 8 (SOff 10 0));
YP09.mkChunk 80 (CVal 8 (SOff 516 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ].
(* The next row of the values buffer, the three bytes a loop turn writes. *)
Definition bs_row : YP09.region := YP09.mkRegion (Some 601%nat) 0 3 0 3 [].
Definition bs_FL (z : bool) : list (nat * afact) :=
(if z then [] else [(36%nat, mkAF 2 7 0)]) ++
[ (35%nat, mkAF (SB + 512) (SB + 17592186044416) 0); (34%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0);
(12%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF (SB + 512) (SB + 17592186044416) 2);
(528%nat, HPTR 0); (516%nat, HPTR 5); (60%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ].
(* The head of the loop over the width (0x84aec = listing offset 17468). *)
Definition ss_L (z : bool) : sstate := mkSS 17468 bs_sr_L (bs_row :: bs_RL0 z) None (mkFacts (bs_FL z) [] []).
(* The instruction after the loop (0x84b44 = listing offset 17556). *)
Definition ss_X (z : bool) : sstate := mkSS 17556 bs_sr_L (bs_RL0 z) None (mkFacts (bs_FL z) [] []).
(* The head of the loop over a column's three cells (0x84b04 = listing offset
   17492), with p of them written: s11 = p, s9 = the column (base + c) & 255,
   s8 and s2 still the atoms 600 and 601; the dead registers ra, t0..t2,
   a0..a7, t3..t6 hold the atoms 602..617 (bs_rejoin .. bs_deads_I 602). *)
Definition bs_ch : sv := SAlu ALU_AND (SAlu ALU_ADD (SOff 33 0) (SOff 600 0)) (SLit 255).
Definition bs_deads_I : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition bs_sr_I (p : Z) : list sv :=
[SLit 0; SOff 602 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 603 0; SOff 604 0; SOff 605 0;
SOff 2 0; SOff 60 0; SOff 606 0; SOff 607 0; SOff 608 0; SOff 609 0; SOff 610 0; SOff 611 0;
SOff 612 0; SOff 613 0; SOff 601 0; SOff 12 0; SOff 34 0; SOff 13 0; SLit 3; SOff 35 0;
SOff 600 0; bs_ch; SOff 529 0; SLit p; SOff 614 0; SOff 615 0; SOff 616 0; SOff 617 0].
Definition ss_I (z : bool) (p : Z) : sstate := mkSS 17492 (bs_sr_I p) (bs_row :: bs_RL0 z) None (mkFacts (bs_FL z) [] []).
(* Releasing a side-stack frame changes only the frame-stack part of the state. *)
Lemma set_fs_free : forall f S cid pos, exists g, stack_free_state cid pos (set_fs f S) = set_fs g S.
Proof. intros f S cid pos. eexists. unfold stack_free_state, set_fs. cbn. reflexivity. Qed.
Lemma set_fs_set_fs : forall f g S, set_fs g (set_fs f S) = set_fs g S.
Proof. intros f g S. reflexivity. Qed.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* ---- the contract's post-condition and the cuts' facts -------------------- *)
Definition bs_post (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) mem md
(s mx al tx base w : Z) (T : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B TBSW_STK (bsw_FP s al mx base w) regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists f, S' = set_fs f S) /\
getr regs' 10 = w64 (if bsw_ok s al mx base w then 8 + 3 * w else -1) /\
(bsw_ok s al mx base w = true ->
garr8 SEGS (mrestrict (w_H W') mem') s
(map bv_unsigned (SWEEP base (Z.to_nat w) (sweep_vals T tx base (Z.to_nat w)))))).
(* What a cut knows of the call: the contract's premises (al <> 0 and the
   width checks passed), al's frame (cid, pos), the own frame (2, fpos) in
   S2, and the realigned sp. *)
Definition bs_ctx ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte)
(fpos : Z) (S2 : astate) (sp1 cid pos : Z) : Prop :=
afn_pre SEGS B TBSW_STK ly S W regs mem md ch /\ Z.of_nat (length (frames S)) <= 7 /\ spZ regs + 32 <= ly_top ly /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 s /\ getr regs 11 = w64 mx /\ getr regs 12 = w64 al /\ getr regs 13 = w64 tx /\
0 <= s < 2 ^ 63 /\ - 2 ^ 31 <= mx < 2 ^ 31 /\
In (tx, TX_SIZE) (ablocks B ly S) /\ length T = 460%nat /\ tx_set01 T /\ tx_legal T /\
(bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) /\
s <> 0 /\ al <> 0 /\ 1 <= w <= 40 /\ 0 <= base < 256 /\ base + w <= 48 /\
In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos <= al /\ al + 2 <= frame_addr ly cid pos + fs_frame_bytes cid /\
al mod 8 = 0 /\
frames S2 = (2, fpos) :: frames S /\ ablocks B ly S2 = ablocks B ly S /\ (exists f, S2 = set_fs f S) /\
spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0.
(* The atoms' values at a cut, for loop counter c: the atoms below 32 are the
   entry registers, 32 the shadow base. *)
Definition bs_env (regs : bvmap 5 word) (al base w shv sp1 F FL c : Z) (Ec : env) : Prop :=
img_env VAL A_LIM Ec /\ (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ec n = getr regs r) /\ ew Ec 32 = Z_to_bv 64 SB /\
ew Ec 33 = Z_to_bv 64 base /\ ew Ec 34 = Z_to_bv 64 w /\ ew Ec 35 = Z_to_bv 64 (SB + al / 8) /\ ew Ec 36 = Z_to_bv 64 shv /\
ew Ec 60 = Z_to_bv 64 sp1 /\ ew Ec 516 = Z_to_bv 64 F /\ ew Ec 528 = Z_to_bv 64 FL /\ ew Ec 529 = Z_to_bv 64 (SB + F / 8) /\
ew Ec 600 = Z_to_bv 64 c /\ ew Ec 601 = Z_to_bv 64 (F + 32 + 3 * c).
(* The memory at a cut with nv values written: the journal since the call
   began, the caller's stack above sp untouched, the first nv values in the
   frame's values buffer, and the head-amp table. *)
Definition bs_mem ly S W (regs : bvmap 5 word) mem md (s mx al tx base w : Z) (T : list byte) (fpos : Z) (S2 : astate)
(ms3 : machine_state) (md3 : Model) (nv : Z) : Prop :=
ajournal SEGS B TBSW_STK (spZ regs) (bsw_FP s al mx base w) ly S W mem md [(2, fpos)] ly S2 W (ms_mem ms3) md3 0 /\
(forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a) /\
garr8 SEGS (mrestrict (w_H W) (ms_mem ms3)) (frame_addr ly 2 fpos + 32)
(map bv_unsigned (firstn (Z.to_nat nv) (sweep_vals T tx base (Z.to_nat w)))) /\
obj_at SEGS (mrestrict (w_H W) (ms_mem ms3)) tx LAY_TX (tx_vals T).
(* The loop's cut lemma: from the head of the loop with c columns written. *)
Definition bs_loop_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(n : nat) (c : Z) (Ec : env) (ms3 : machine_state) (md3 : Model),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos ->
n = Z.to_nat (w - c) -> 0 <= c < w ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_L z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c) ->
SRr SEGS W (mkCfg ms3 md3) (bs_post ly S W regs mem md s mx al tx base w T).
(* The tail's cut lemma: from the instruction after the loop (0x84b44), all
   3w values written, to the contract's post. *)
Definition bs_tail_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(Ec : env) (ms3 : machine_state) (md3 : Model),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) w Ec ->
st_ok_pi SEGS VAL Ec (ss_X z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * w) ->
SRr SEGS W (mkCfg ms3 md3) (bs_post ly S W regs mem md s mx al tx base w T).
(* The head segment: from the loop head (0x84aec) through al's shadow check
   and the column's load to the head of the cell loop (0x84b04), p = 0. *)
Definition bs_head_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(c : Z) (Ec : env) (ms3 : machine_state) (md3 : Model) (Q : world SEGS -> config -> Prop),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos -> 0 <= c < w ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_L z) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c) ->
(forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec' ->
st_ok_pi SEGS VAL Ec' (ss_I z 0) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * c) -> SRr SEGS W (mkCfg ms' md') Q) ->
SRr SEGS W (mkCfg ms3 md3) Q.
(* The cell segment: from the head of the cell loop with cell p of column c
   next (0x84b04), through the call of reac_headamp_tx_effective (0x84b10) and
   the store of its byte at F + 32 + 3c + p, to the next cell (p < 2), or
   through the column step to the loop head (c + 1 < w) or to the instruction
   after the loop (c + 1 = w). *)
Definition bs_cell_spec : Prop :=
forall (z : bool) ly S W (regs : bvmap 5 word) mem md ch (s mx al tx base w : Z) (T : list byte) shv fpos S2 sp1 cid pos
(c p : Z) (Ec : env) (ms3 : machine_state) (md3 : Model) (Q : world SEGS -> config -> Prop),
bs_ctx ly S W regs mem md ch s mx al tx base w T fpos S2 sp1 cid pos -> 0 <= c < w -> 0 <= p < 3 ->
bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec ->
st_ok_pi SEGS VAL Ec (ss_I z p) (restrict (w_H W) ms3) ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms3 md3 (3 * c + p) ->
(p < 2 -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) c Ec' ->
st_ok_pi SEGS VAL Ec' (ss_I z (p + 1)) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * c + p + 1) -> SRr SEGS W (mkCfg ms' md') Q) ->
(p = 2 -> c + 1 < w -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) (c + 1) Ec' ->
st_ok_pi SEGS VAL Ec' (ss_L z) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * (c + 1)) -> SRr SEGS W (mkCfg ms' md') Q) ->
(p = 2 -> c + 1 = w -> forall Ec' ms' md', bs_env regs al base w shv sp1 (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) w Ec' ->
st_ok_pi SEGS VAL Ec' (ss_X z) (restrict (w_H W) ms') ->
bs_mem ly S W regs mem md s mx al tx base w T fpos S2 ms' md' (3 * w) -> SRr SEGS W (mkCfg ms' md') Q) ->
SRr SEGS W (mkCfg ms3 md3) Q.
(* ---- helper lemmas ------------------------------------------------------- *)
(* The rows the call may write lie in a heap block, so they miss every frame
   the caller took and those frames' shadow. *)
Lemma bsw_fp_frames : forall ly S W mem md s al mx base w,
AR SEGS B ly S W mem md ->
(bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP (bsw_FP s al mx base w) a.
Proof.
intros ly S W mem md s al mx base w HAR HSB cid pos a Hf Ha. unfold bsw_FP.
destruct (bsw_ok s al mx base w) eqn:Hb; [|apply inFP_nil].
destruct (HSB eq_refl) as (sb & sn & Hin & Hlo & Hhi).
pose proof (bsw_ok_spec s al mx base w Hb) as (_ & _ & Hw & _).
intros Hfp. apply inFP_cons in Hfp. destruct Hfp as [Hfp | Hfp]; [|exact (inFP_nil _ Hfp)].
pose proof (sep_block_frame SEGS B LAWS ly S W mem md sb sn cid pos HAR Hin Hf) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md sb sn HAR Hin) as (_ & H4096 & Hceil & [Hih Hia] & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hf) as (Hf4096 & Hfceil & Hfapp).
pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia).
rewrite Hrq in *.
unfold zdisjoint, in_zr, frame_rng, shadow_addr, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *.
destruct Ha as [Ha | Ha]; [lia|].
assert (frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr ly cid pos + fs_frame_bytes cid) / 8).
{ pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)).
pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
apply Z.div_le_lower_bound; lia. }
assert ((frame_addr ly cid pos + fs_frame_bytes cid) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia).
assert (alloc_ceiling / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
End e.
(* The shadow cell of a pointer a little above an 8-aligned one. *)
Lemma shadow_decl_okc : forall E (p b s : nat) (pv Bv c : Z),
ew E p = Z_to_bv 64 pv -> 0 <= pv -> 0 <= c -> pv + c < 2 ^ 64 -> (pv + c) / 8 = pv / 8 ->
ew E b = Z_to_bv 64 Bv ->
ew E s = Z_to_bv 64 (Bv + pv / 8) ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p c) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
intros E p b s pv Bv c Hp Hpv Hc Hpc Hdiv Hb Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs, !Z.add_0_r.
rewrite (unsigned_lit_small pv) by lia. rewrite (zcanon_id (pv + c)) by (unfold M64; lia). rewrite Hdiv.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64. rewrite (Z.mod_mod Bv) by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite (Z.mod_mod (Bv + pv / 8)) by lia. f_equal. lia.
Qed.
Lemma shadow_in_frame : forall fa fs x, fa mod 64 = 0 -> fs mod 64 = 0 -> 0 <= fa -> 0 <= fs -> fa <= x < fa + fs ->
fa / 8 <= x / 8 < fa / 8 + fs / 8.
Proof.
intros fa fs x Ha Hf Ha0 Hf0 Hx.
pose proof (Z.div_mod fa 64 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
pose proof (Z.div_mod fs 64 ltac:(lia)) as Df. rewrite Hf, Z.add_0_r in Df.
assert (Ea : fa / 8 = 8 * (fa / 64)) by (rewrite Da at 1; replace (64 * (fa / 64)) with ((8 * (fa / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (Ef : fs / 8 = 8 * (fs / 64)) by (rewrite Df at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
split; [apply Z.div_le_mono; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
(* The checks at 0x84a74 (`width - 41 <u -40`) and 0x84a84 (`48 <u base + width`). *)
Lemma bsw_false_fits : forall s al mx base w, fits base w = false -> bsw_ok s al mx base w = false.
Proof. intros s al mx base w H. unfold bsw_ok. rewrite H, andb_false_r. reflexivity. Qed.
Lemma bsw_bad_w : forall s al mx base w, 0 <= w < 256 -> (w + -41) mod 2 ^ 64 < 18446744073709551576 ->
bsw_ok s al mx base w = false.
Proof.
intros s al mx base w Hw H. apply bsw_false_fits. unfold fits.
destruct (Z_lt_le_dec w 41) as [Hl | Hl].
- rewrite <- (Z.mod_unique (w + -41) (2 ^ 64) (-1) (w + -41 + 2 ^ 64)) in H by lia.
rewrite (proj2 (Z.leb_gt 1 w)) by lia. reflexivity.
- rewrite (proj2 (Z.leb_gt w 40)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma bsw_good_w : forall w, 0 <= w < 256 -> 18446744073709551576 <= (w + -41) mod 2 ^ 64 -> 1 <= w <= 40.
Proof.
intros w Hw H. destruct (Z_lt_le_dec w 41) as [Hl | Hl].
- rewrite <- (Z.mod_unique (w + -41) (2 ^ 64) (-1) (w + -41 + 2 ^ 64)) in H by lia. lia.
- rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma bsw_bad_bw : forall s al mx base w, 48 < base + w -> bsw_ok s al mx base w = false.
Proof.
intros s al mx base w H. apply bsw_false_fits. unfold fits.
rewrite (proj2 (Z.leb_gt (base + w) 48)) by lia. rewrite andb_false_r. reflexivity.
Qed.
End d.
End b.
(* ---- the preamble of a cut lemma ------------------------------------------ *)
(* Unpack a cut's three facts (bs_ctx, bs_env, bs_mem) into the names the
   walk tactics and GrantBuildSweep.v use: the entry facts (HPRE ..), the
   atoms' values (EE, E32 .. E601, E10 .. E13), the journal HJ2, the stack
   above sp HUP, the values HVALS, the table HOBJ, the own frame F (flag FL)
   and its bounds, al's frame (cid, pos) and its bounds, and the image facts. *)
Ltac bs_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec :=
let L := rnLAWS in
destruct HCTX as (HPRE & Hroom & Htop32 & HROD & H10 & H11 & H12 & H13 & Rs & Rmx & Htx & HTlen & H01 & HTL & HSB &
Hsn & Haln & Hw1 & Hb8 & Hbw & Hfin & Hcid0 & Hflo & Hfhi & Hal8 & Hfrs2 & Eab & (fS2 & ES2) & Hsp1 & Hsp1al);
destruct HENV as (HEI & EE & E32 & E33 & E34 & E35 & E36 & E60 & RF & E528 & E529 & E600 & E601);
destruct HMEM as (HJ2 & HUP & HVALS & HOBJ);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
assert (FFS : TBSW_STK = 6224) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
lazymatch type of H10 with getr _ _ = w64 ?v => assert (E10 : ew Ec 10 = Z_to_bv 64 v) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10) end;
lazymatch type of H11 with getr _ _ = w64 ?v => assert (E11 : ew Ec 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11) end;
lazymatch type of H12 with getr _ _ = w64 ?v => assert (E12 : ew Ec 12 = Z_to_bv 64 v) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12) end;
lazymatch type of H13 with getr _ _ = w64 ?v => assert (E13 : ew Ec 13 = Z_to_bv 64 v) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13) end;
lazymatch type of H10 with getr ?rg _ = _ => assert (Usp : bv_unsigned (ew Ec 2) = spZ rg) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
assert (AG : forall n, (n < 33)%nat -> ew Ec n = ew Ec n) by (intros; reflexivity);
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by (intros; reflexivity);
img_factsF Ec; img_hull_factsF;
pose proof (proj1 HJ2) as HAR2;
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
destruct (al_frames _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres);
destruct (frames_bounds _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img;
destruct (frames_bounds _ _ L ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
destruct (frame_al64 _ _ ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb64');
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin);
let fl1 := fresh "fl1" in let fl2 := fresh "fl2" in let Efl := fresh "Efl" in
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ L ly S2 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC;
destruct (al_blocks _ _ L ly S W mem md _ _ HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & _);
change (req_size TX_SIZE) with 460 in Htxceil, Htxia;
pose proof Htx as HtxS2; rewrite <- Eab in HtxS2;
pose proof (sep_block_frame _ _ L ly S2 W _ _ _ _ 2 fpos HAR2 HtxS2 Hfin2) as HtxF;
unfold zdisjoint in HtxF; cbn [fst snd] in HtxF; change (req_size TX_SIZE) with 460 in HtxF;
change (fs_frame_bytes 2) with 256 in *;
let F := fresh "F" in let FL := fresh "FL" in
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : F / 8 + 32 <= 17592184995840) by (rewrite <- (Z.div_add F 32 8) by lia; apply Z.div_le_upper_bound; lia);
lazymatch type of H12 with getr _ _ = w64 ?al =>
assert (Hal512 : 512 <= al / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia);
assert (Hal8d : al = 8 * (al / 8)) by (pose proof (Z.div_mod al 8 ltac:(lia)); lia) end.
