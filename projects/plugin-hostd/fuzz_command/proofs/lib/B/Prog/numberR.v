(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the release of number's class-0 side-stack frame (0x8e5a0..0x8e618, cgif's exitRA in A/ACam.v) and number's return. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/numberR.v (a working branch a7e5999afe4) for fuzz_command.asan-ubsan: module paths and the release's addresses in that image (0x8e0ac..0x8e124, the same code as A's 0x8e5a0..0x8e618). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require number.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c numberE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* number's post (number_c.v:117-124) *)
Definition n_Q (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (out : Z) (wd : list byte) :=
fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
match Verbs.number_m wd with
| Some v => getr regs' 10 = w64 1 /\ aval_mem (rdW W' mem') out 4 v
| None => getr regs' 10 = w64 0 /\ (forall i, 0 <= i < 4 -> rdW W' mem' (out + i) = rdW W mem (out + i))
end /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
ly' = ly /\ (exists f, S' = set_fs f S).
Definition n_byte0 (wd : list byte) : Z := bv_unsigned (nth 0 (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Definition n_byteE (wd : list byte) : Z := bv_unsigned (nth (Z.to_nat (__intscan_c.s10_end wd)) (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).

(* the release of the class-0 frame (0x8e0ac..0x8e124) and number's return: the walk poisons the frame's shadow
   f8 / f5, stores the cookie word, clears the frame's flag byte (which frees the frame) and returns.  The three
   writable windows of the release (the frame's shadow [0, 8), the frame's words [0, 32) and the flag byte) all
   lie inside the frame the journal owns, so the result cell keeps the bytes it had. The side-stack state is the
   entry's up to set_fs (the frame taken by __asan_stack_malloc_0 and freed by the flag store). *)
Lemma n_release : forall ly S W (regs : bvmap 5 word) mem md ch out (wd : list byte) ms md3 S2 fpos Ev retv,
afn_pre SEGS B NUMBER_STK ly S W regs mem md ch ->
((exists cid pos, In (cid, pos) (frames S) /\
   frame_addr ly cid pos <= out /\ out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
 (spZ regs <= out /\ out + 4 <= ly_top ly)) ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_rel0 (restrict (w_H W) ms) ->
ajournal SEGS B NUMBER_STK (spZ regs) [(out, out + 4)] ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md3 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f, S2 = set_fs f S) ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (nsp1 (spZ regs)) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
ew Ev 1100 = Z_to_bv 64 retv ->
match Verbs.number_m wd with
| Some v => retv = 1 /\ aval_mem (rdW W (ms_mem ms)) out 4 v
| None => retv = 0 /\ (forall i, 0 <= i < 4 -> rdW W (ms_mem ms) (out + i) = rdW W mem (out + i))
end ->
SRr SEGS W (mkCfg ms md3)
(apost_base SEGS B NUMBER_STK [(out, out + 4)] regs ly S W mem md EV_NUMBER (n_Q ly S W mem out wd)).
Proof.
intros ly S W regs mem md ch out wd ms md3 S2 fpos Ev retv HPRE HOUT HEI HS HJ Hfrs2 Eab HS2f AGR
E32 E33 E1028 E1040 E1041 E1100 HRET.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : NUMBER_STK = 12400) by reflexivity.
set (sp0 := spZ regs) in *. set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HAR3.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B ly S2 W _ _ 0 fpos HAR3 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W (ms_mem ms) md3 0 fpos HAR3 Hfin2)
  as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz2 & HFLceil)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
fold F in HFal32, HFapp, HFpres, HFSpres, HF4096, HFceil, HF64.
fold FL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLz2, HFLceil.
(* the frame's address is a multiple of 64, so F / 8 is linear in F *)
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; exact D).
assert (HF8d : F / 8 = 8 * (F / 64))
  by (rewrite HFq at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : F / 8 * 8 = F) by lia.
assert (HFS8 : forall i, 0 <= i < 8 -> apresent (w_H W) (ms_mem ms) (SB + F / 8 + i)).
{ unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
  intros i Hi. exact (proj1 (HFSpres i Hi)). }
(* the atoms of the release's state *)
assert (U2 : bv_unsigned (ew Ev 2) = sp0) by (rewrite (AGR 2%nat 2%bv eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew Ev 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
destruct (nsp1_facts sp0 Hal16) as (Hs1al & Hs1).
assert (U33 : bv_unsigned (ew Ev 33) = nsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U1028 : bv_unsigned (ew Ev 1028) = F) by (rewrite E1028; apply unsigned_lit_small; lia).
assert (U1040 : bv_unsigned (ew Ev 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (U1041 : bv_unsigned (ew Ev 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
(* the flag cell is owned, the frame's bytes are not, so the flag cell is outside the frame *)
assert (HFLout : FL < F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hx | Hx]; [left; exact Hx|].
  destruct (Z_lt_le_dec FL (F + 64)) as [Hy | Hy]; [exfalso | right; exact Hy].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
(* the frame's shadow [0, 8) and the frame's words [0, 32) are the release's writable windows *)
n_rewin HS 1041%nat 0 0 8 ltac:(rewrite U1041; intros o Ho; apply (apresent_writable SEGS); apply HFS8; lia).
n_rewin HS 1028%nat 0 0 32 ltac:(rewrite U1028; intros o Ho; apply (apresent_writable SEGS);
  apply (proj1 (HFpres (F + o) ltac:(lia)))).
(* and the flag byte is the third *)
pose proof (conj HFLout (conj HFL4096 (conj HFLz2 (conj HFLceil (conj HF4096 (conj HFceil (conj HF8
  (conj C1 (conj Hceil (conj Hslo FFS)))))))))) as AM.
lazymatch type of AM with ?T => change (nam T) in AM end.
let r := eval unfold n_flag_r in n_flag_r in
addreg HS r ltac:(rewrite U1040; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres
  | apply Forall_nil ]).
clear AM.
(* every byte the release writes is a byte of the frame it owns, or the frame's flag byte *)
assert (INF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 -> in_frames ly [(0, fpos)] a).
{ intros a Ha. exists 0, fpos. split; [left; reflexivity|].
  unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. change (64 / 8) with 8.
  fold F. rewrite <- SB_SHADOW_OFF. lia. }
paj_run_flag_sh RUNF HS HJ.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U1040, ?U1041, ?U1028, ?U2 in Hr;
    first [ right; lia
    | left; right; right; right; left; apply INF; lia
    | exfalso; lia ] |]);
  destruct Hin.
- intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ev (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U1040
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0.
  rewrite Z.add_0_r in V0. exact V0.
- (* the return *)
  clear HF HG.
  (* the bytes outside the three windows are the bytes the state had at the release *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 32) \/ a = FL) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U1040, ?U1041, ?U1028, ?U2 in Hrr; lia |]);
    destruct Hin)) as UNCH.
  (* the result cell and the errno cell are outside them *)
  assert (HOUTK : forall i, 0 <= i < 4 ->
    ~ ((SB + F / 8 <= out + i < SB + F / 8 + 8) \/ (F <= out + i < F + 32) \/ out + i = FL)).
  { destruct HOUT as [(c & p & Hc & Hp1 & Hp2) | (Hq1 & Hq2)].
    - assert (HcS2 : In (c, p) (frames S2)) by (rewrite Hfrs2; right; exact Hc).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hc) as (Hc0 & Hc1 & Hc2).
      destruct (al_frames _ _ LAWS _ _ _ _ _ c p HAR3 HcS2) as (_ & _ & Hcpres & _).
      destruct (in_split _ _ Hc) as (l1 & l2 & Hsp).
      pose proof (sep_frames_pos SEGS B LAWS ly S2 W (ms_mem ms) md3 (0, fpos) (c, p) [] l1 l2 HAR3
        ltac:(rewrite Hfrs2, Hsp; reflexivity)) as Hdj.
      unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj.
      change (fs_frame_bytes 0) with 64 in Hdj. fold F in Hdj.
      unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hc2.
      intros i Hi [Hsh | [Hfr | Hfl]].
      + unfold SB in Hsh. lia.
      + lia.
      + exact (proj2 (Hcpres (out + i) ltac:(lia)) ltac:(rewrite Hfl; exact HFLown)).
    - intros i Hi [Hsh | [Hfr | Hfl]]; unfold SB in *; lia. }
  assert (HOUT64 : 4096 <= out /\ out + 4 <= 2 ^ 47).
  { destruct HOUT as [(c & p & Hc & Hp1 & Hp2) | (Hq1 & Hq2)].
    - destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hc) as (Hc0 & Hc1 & _). lia.
    - lia. }
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
  lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists ly, (stack_free_state 0 fpos S2), rg, mm, mdx end.
  split; [rewrite R1, (AGR 1%nat 1%bv eq_refl); unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split.
  { apply aregs_preserved_eqs;
    [ prreg HS (2%bv : bv 5) Rq; rewrite Rq, (AGR 2%nat 2%bv eq_refl); reflexivity
    | prreg HS (3%bv : bv 5) Rq; rewrite Rq, (AGR 3%nat 3%bv eq_refl); reflexivity
    | prreg HS (4%bv : bv 5) Rq; rewrite Rq, (AGR 4%nat 4%bv eq_refl); reflexivity
    | prreg HS (8%bv : bv 5) Rq; rewrite Rq, (AGR 8%nat 8%bv eq_refl); reflexivity
    | prreg HS (9%bv : bv 5) Rq; rewrite Rq, (AGR 9%nat 9%bv eq_refl); reflexivity
    | prreg HS (18%bv : bv 5) Rq; rewrite Rq, (AGR 18%nat 18%bv eq_refl); reflexivity
    | prreg HS (19%bv : bv 5) Rq; rewrite Rq, (AGR 19%nat 19%bv eq_refl); reflexivity
    | prreg HS (20%bv : bv 5) Rq; rewrite Rq, (AGR 20%nat 20%bv eq_refl); reflexivity
    | prreg HS (21%bv : bv 5) Rq; rewrite Rq, (AGR 21%nat 21%bv eq_refl); reflexivity
    | prreg HS (22%bv : bv 5) Rq; rewrite Rq, (AGR 22%nat 22%bv eq_refl); reflexivity
    | prreg HS (23%bv : bv 5) Rq; rewrite Rq, (AGR 23%nat 23%bv eq_refl); reflexivity
    | prreg HS (24%bv : bv 5) Rq; rewrite Rq, (AGR 24%nat 24%bv eq_refl); reflexivity
    | prreg HS (25%bv : bv 5) Rq; rewrite Rq, (AGR 25%nat 25%bv eq_refl); reflexivity
    | prreg HS (26%bv : bv 5) Rq; rewrite Rq, (AGR 26%nat 26%bv eq_refl); reflexivity
    | prreg HS (27%bv : bv 5) Rq; rewrite Rq, (AGR 27%nat 27%bv eq_refl); reflexivity ]. }
  unfold n_Q. split; [|split; [|split]].
  + rewrite R10, E1100. destruct (Verbs.number_m wd) as [v|]; destruct HRET as (Hretv & Hrest); subst retv.
    * split; [reflexivity|]. intros k Hk.
      rewrite (UNCH (out + Z.of_nat k) ltac:(lia) (HOUTK (Z.of_nat k) ltac:(lia))). exact (Hrest k Hk).
    * split; [reflexivity|]. intros i Hi.
      rewrite (UNCH (out + i) ltac:(lia) (HOUTK i Hi)). exact (Hrest i Hi).
  + assert (Hab : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
      by (unfold ablocks; rewrite blocks_stack_free_state; exact Eab).
    rewrite Hab. apply Permutation_refl.
  + reflexivity.
  + destruct HS2f as (f2 & ->). eexists. unfold stack_free_state, set_fs. reflexivity.
Qed.
End e.
End f.
End d.
