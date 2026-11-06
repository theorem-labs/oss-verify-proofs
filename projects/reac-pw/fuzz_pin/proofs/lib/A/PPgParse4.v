(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* reac_box_pin_parse of reac-pw/fuzz_pin, image A (fuzz_pin.asan): segment 4 of the walk, 0x80d9c -> `ret`.
   The frame on the side stack is given back: its first word is set to 0x45E0360E, `beqz s2` is not taken (s2 = F,
   at least 4096), its 8 shadow bytes are set to 0xf5, the flag pointer is loaded from F + 56 and the flag byte is
   set to 0 (astack_free_law), a0 = a3, ra and s0..s11 are reloaded from the save area and sp is the entry sp. The
   post of the contract (pin_post_parse) follows from the kept-memory fact KE the walk carries, the out-cell values
   of INV_P4 and the result a3 of INV_P4. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec PPgParseLib PPgParseCx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The out-cells of a live call lie in frames the caller owns, so no byte of a heap block of the caller is one. *)
Lemma pp4_blk_not_out : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (sa mo lb : Z) cidm posm cidl posl b m i,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(pin_parse_live sa mo lb = true ->
 In (cidm, posm) own /\ frame_addr lyc cidm posm <= mo /\ mo + 8 <= frame_addr lyc cidm posm + fs_frame_bytes cidm /\
 In (cidl, posl) own /\ frame_addr lyc cidl posl <= lb /\ lb + 8 <= frame_addr lyc cidl posl + fs_frame_bytes cidl) ->
In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
~ (pin_parse_live sa mo lb = true /\ pin_out_cell mo lb (b + i)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sa mo lb cidm posm cidl posl b m i HJ Hlive Hb Hi (Hl & Ho).
destruct (Hlive Hl) as (Hm & Hm1 & Hm2 & Hl' & Hl1 & Hl2).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : forall c p, In (c, p) own -> In (c, p) (frames Sc)) by (intros c p Hcp; rewrite Hfrs; apply in_or_app; left; exact Hcp).
destruct Ho as [Ho | Ho].
- pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W memc mdc b m cidm posm HAR Hb (Hfin _ _ Hm)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W memc mdc b m cidl posl HAR Hb (Hfin _ _ Hl')) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* pin_post_parse at the return, from what the walk holds there. *)
Lemma pp4_post_of : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) cat DP (sa mo lb : Z) (s : list byte)
lyc Sc W memc mdc cidm posm cidl posl ly2 S2 W2 (regs2 : bvmap 5 word) mem2 md2,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(pin_parse_live sa mo lb = true ->
 In (cidm, posm) own /\ frame_addr lyc cidm posm <= mo /\ mo + 8 <= frame_addr lyc cidm posm + fs_frame_bytes cidm /\
 In (cidl, posl) own /\ frame_addr lyc cidl posl <= lb /\ lb + 8 <= frame_addr lyc cidl posl + fs_frame_bytes cidl) ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
aregs_preserved regs regs2 -> frames S2 = frames Sc ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> same_io mdc md2 -> mo_le MT Sc S2 0 ->
acall_kept tfibsegs B lyc Sc W memc W2 mem2 (spZ regs - T_parse_STK) (spZ regs)
 (fun a => pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a) ->
getr regs2 10 = w64 (parse_rc (pin_parse_res cat DP sa mo lb s)) ->
(forall row lab, pin_parse_res cat DP sa mo lb s = Some (row, lab) ->
 val_mem tfibsegs (mrestrict (w_H W2) mem2) mo 8%nat row /\ val_mem tfibsegs (mrestrict (w_H W2) mem2) lb 8%nat lab) ->
pin_post_parse tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs cat DP sa mo lb s lyc Sc W memc mdc
W2 (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs cat DP sa mo lb s lyc Sc W memc mdc cidm posm cidl posl ly2 S2 W2 regs2 mem2 md2
HJc Hlive HJ2 Hregs Hfrs2 HPerm Hio Hmo (K1 & K2 & K3 & K4 & _ & _) Ha0 Hout.
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [unfold EV_parse; rewrite Z.add_0_r; exact HJ2|].
split; [exact Hregs|].
split; [exact Hfrs2|].
split; [exact HPerm|].
split; [exact Hio|].
split; [exact Hmo|].
split; [intros a Ha Hs _; exact (K1 a Ha Hs)|].
split; [intros b m i Hb Hi; exact (K2 b m i Hb Hi (pp4_blk_not_out STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sa mo lb cidm posm cidl posl b m i HJc Hlive Hb Hi))|].
split; [intros c p a Hin Hr Ho; apply (K4 c p a Hin Hr); intros (_ & Ho'); exact (Ho Ho')|].
split; [intros a Hi Ho He; exact (K3 a Hi Ho He)|].
split; [exact Ha0 | exact Hout].
Qed.
Lemma pp4_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
End b.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.          Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.                Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.             Hypothesis FFL : frame_flag_lawP tfibsegs B.
Variables RLO RHI cat : Z.  Variables TP DP : nat -> Z.

Lemma pp_seg4 : PP_seg4 B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg4.
pp_prelude.
destruct HINV as (Erc & Hout).
unfold pp_post.
cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch c_sa c_mo c_lb c_s
 c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0].
pose proof (proj1 HJ0) as HARc.
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrsc & _).
destruct (FFL _ _ _ _ _ 0 fpos HARN Hfin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
rewrite !EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLz, HFLce. fold FL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLz, HFLce.
assert (Usp' : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (ELF : ly_F lyN = ly_F lyc) by (eapply pp_lyF; [exact HJ0 | exact HJ]).
assert (HOCF : pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl).
{ intros Hl. destruct (Hlive Hl) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hl' & _ & _ & Hl1 & Hl2 & _).
  rewrite Hfrsc. split; [apply in_or_app; left; exact Hm|]. split; [exact Hm1|]. split; [exact Hm2|].
  split; [apply in_or_app; left; exact Hl'|]. split; [exact Hl1 | exact Hl2]. }
destruct (pz_nf_sep B LAWS lyc lyN Sc SN WN (ms_mem msN) mdN fpos F FL HARN Hfrs HPERM ELF eq_refl eq_refl FFL)
as (N1 & N2 & N3 & N4).
(* 1. the frame's shadow bytes made writable, the flag byte as a writable region of one byte *)
pp_fs_rw HS E88 HFSpres.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); replace (FL + o) with FL by lia; exact HFLpres)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split;
[ destruct (Z_lt_ge_dec FL (SHADOW_OFF + F / 8)); [left; unfold SHADOW_OFF in *; lia|];
  destruct (Z_lt_ge_dec FL (SHADOW_OFF + F / 8 + 8)); [exfalso | right; unfold SHADOW_OFF in *; lia];
  apply (proj2 (HFSpres (FL - (SHADOW_OFF + F / 8)) ltac:(lia))); unfold shadow_addr;
  replace (SHADOW_OFF + F / 8 + (FL - (SHADOW_OFF + F / 8))) with FL by lia; exact HFLown
| destruct (Z_lt_ge_dec FL F); [left; lia|]; destruct (Z_lt_ge_dec FL (F + 64)); [exfalso | right; lia];
  exact (proj2 (HFpres FL ltac:(lia)) HFLown)
| left; lia ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* 2. the run to `ret`: F[0] := 0x45E0360E, `beqz s2` not taken, the shadow bytes := 0xf5, the flag byte := 0,
   a0 = a3, the saved registers reloaded *)
aj_run_flag_sh tfibtbl_lib_ok HS HJ.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr.
  - right. rewrite EFL. fold FL. lia.
  - left. right; right; right. exists 0, fpos. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr; cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. rewrite EFA. fold F.
    unfold SHADOW_OFF. unfold SB in Hr. lia.
  - left. right; right; right. exists 0, fpos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 0) with 64. rewrite EFA. fold F. lia.
  - left. left. lia. }
{ flag0 E87 EFL. }
(* 3. what the run kept: everything outside the save area, the frame, its shadow bytes and its flag byte *)
lazymatch type of HFr with frame_of ?Ef ?rsf _ _ =>
assert (HZs : forall a, in_wrange Ef rsf a -> (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a);
[ intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
  [ right; right; right; lia
  | right; right; left; unfold SHADOW_OFF; unfold SB in Hr; lia
  | right; left; lia
  | left; change T_parse_STK with 8400; lia ]
| assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange Ef rsf a ->
    aview tfibsegs (w_H WN) (ms_mem ms) a = aview tfibsegs (w_H WN) (ms_mem msN) a)
  by (intros a Ha Hz; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by exact Ha; exact Hz);
  pose proof (pz_kept_own B LAWS lyc lyN Sc SN W memc mdc WN (ms_mem msN) mdN WN (ms_mem msN) WN (ms_mem ms)
    (spZ regs - T_parse_STK) (spZ regs) fpos F FL _ (in_wrange Ef rsf) HARc HARN Hfrs HPERM ELF eq_refl eq_refl FFL
    ltac:(change T_parse_STK with 8400; lia) ltac:(lia)
    (proj1 (pp_oc_sep tfibsegs B LAWS lyc Sc W memc mdc _ mo lb cidm posm cidl posl HARc HOCF))
    (pp_oc_img B lyc Sc W memc mdc _ mo lb cidm posm cidl posl HARc HOCF)
    ltac:(intros a Ha; destruct (HZs a Ha) as [H|H]; [left; exact H | right; right; exact H])
    HKE HKP (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as KE2 ] end.
(* 4. `ret` *)
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'.
replace (v_jalr (getr (ms_regs ms) 1) 0) with (getr regs 1)
by (rewrite Rra; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (AG 1%nat) by lia;
    rewrite (EE 1%nat 1%bv eq_refl); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact (eq_sym Hret)).
eapply (pp4_post_of B MT LAWS STK sp0 FP ly S W0 mem0 md0 own k regs cat DP sa mo lb s lyc Sc W memc mdc cidm posm cidl posl).
- exact HJ0.
- intros Hl. destruct (Hlive Hl) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hl' & _ & _ & Hl1 & Hl2 & _).
  repeat split; assumption.
- apply (ajournal_materialize tfibsegs _ LAWS tfib_segs_low). exact HJ.
- apply aregs_preserved_eqs; creg HS AG EE.
- change (frames (stack_free_state 0 fpos SN)) with (del_pos (frames SN) 0 fpos). rewrite Hfrs. cbn [del_pos].
  rewrite !Z.eqb_refl. reflexivity.
- unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B lyN SN). exact HPERM.
- repeat (first [exact HIO | eapply same_io_trans; [| apply pp4_same_io_wvb]]).
- unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact HMLE.
- exact KE2.
- rewrite Ra0. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. unfold PN_rc in Erc. rewrite Erc. reflexivity.
- intros row lab Hrl. destruct (Hout row lab Hrl) as (Vm & Vl).
  assert (Hl : pin_parse_live sa mo lb = true)
  by (unfold pin_parse_res in Hrl; destruct (pin_parse_live sa mo lb); [reflexivity | discriminate]).
  destruct (HOCF Hl) as (Hm & Hm1 & Hm2 & Hl' & Hl1 & Hl2).
  destruct (Hlive Hl) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & _).
  assert (Hcell : forall c p x, In (c, p) (frames Sc) -> frame_addr lyc c p <= x < frame_addr lyc c p + fs_frame_bytes c ->
    pin_out_cell mo lb x -> aview tfibsegs (w_H WN) (ms_mem ms) x = aview tfibsegs (w_H WN) (ms_mem msN) x).
  { intros c p x Hin Hx Ho. destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc c p HARc Hin) as (G4096 & Gce & _).
    apply HKP; [lia|]. intros Hz. destruct (HZs x Hz) as [Hw | Hn]; [exact (HOS x Ho Hw)|].
    apply (N3 c p x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn]. }
  split.
  + apply (val_mem_kept tfibsegs (w_H WN) (w_H WN) (ms_mem msN) (ms_mem ms)); [|exact Vm].
    intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. apply (Hcell cidm posm); [exact Hm | lia | left; lia].
  + apply (val_mem_kept tfibsegs (w_H WN) (w_H WN) (ms_mem msN) (ms_mem ms)); [|exact Vl].
    intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. apply (Hcell cidl posl); [exact Hl' | lia | right; lia].
Qed.
End c.

(* ---- shared by segments 1 and 3 (PPgParse1.v, PPgParse3.v) ---- *)
(* The hand-off to the next continuation RC : pp_from .. ss INV, as lib/A/PPgParseCx.v's pp_hand, with the pp_E
   goal closed from pp_prelude's AG E70 E75 E87 E88 by conversion. Leaves, in pp_from's order, the goals the
   eassumption does not close (journal, frames, Permutation, mo_le, same_io, wle, KE) and the invariant. *)
Ltac pp_hand2 RC HS AG E70 E75 E87 E88 :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (pp_post _ _ _ _ _ _ _ ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ W3 ms3 md3);
[ lazymatch goal with H0 : pp_base _ _ _ _ _ _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with
    | |- pp_E _ (havoc _ _ _) => apply pp_E_havoc; [unfold PW_P4, PW_P2, PW_P3, PW_PL, PP_N0; clear; cbn; lia|]
    | |- pp_E _ (ewset _ _ _) => apply pp_E_ewset; [unfold PW_P4, PW_P2, PW_P3, PW_PL, PP_N0; clear; cbn; lia|] end);
  unfold pp_E, pp_F, pp_FL; cbn [c_lyc c_fpos c_E0 c_sp1];
  split; [exact AG|]; split; [exact E70|]; split; [exact E75|]; split; [exact E87 | exact E88]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch
   c_sa c_mo c_lb c_s c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0]
| exact HS ] end end.
(* The frame region 75 read-only (0, 0) for a run of the token runner (its static check needs every writable
   window that may meet the shadow band covered, and the frame's own bytes are not marked usable), and writable
   (0, 64) again before a join: the form of lib/A/PPgParseCx.v's pp_fs_ro / pp_fs_rw at the frame region.
   Hp : forall a, F <= a < F + 64 -> apresent (w_H W) m a /\ _ at the CURRENT memory. *)
Ltac pp_fr_ro HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 75%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac pp_fr_rw HS E75 F Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 75%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 64) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 64 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E75, unsigned_lit_small by lia;
intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (Hp (F + o) ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* After a run (HFr / HG from the run tactics): the kept-memory fact HKE carried to the run's end memory. Every writable
   window of the run's state is the call's stack window (the save area 2, the spills 70), the class-0 frame (75),
   its shadow (88) or its flag byte (87), or an out-cell region, which octac places in the excluded set
   (the goal `pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a` with Hr : b + wlo <= a < b + whi). *)
Ltac pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL octac :=
let LAWS := rnLAWS in
let FFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end in
lazymatch type of HARc with AR _ ?B ?lyc ?Sc ?W ?memc ?mdc =>
lazymatch type of HARN with AR _ _ ?lyN ?SN ?W2 ?mem2 ?md2 =>
lazymatch type of HKE with acall_kept _ _ _ _ _ _ ?WX ?memX ?slo ?shi ?Eo =>
lazymatch type of HOCF with pp_oc_frames _ _ ?live ?mo ?lb ?cidm ?posm ?cidl ?posl =>
lazymatch type of Hfrs with frames _ = (0, ?fpos) :: _ =>
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict (w_H WX) memX) (mrestrict (w_H ?WY) ?memY),
                    HG : mem_grows (mrestrict _ memX) (mrestrict _ ?memY) |- _ =>
let HZs := fresh "HZs" in let HKP := fresh "HKP" in let KE2 := fresh "KE2" in
assert (HZs : forall a, in_wrange Ef rsf a -> (slo <= a < shi) \/ Eo a \/ pp_nf F FL a);
[ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr; cbv beta;
    first [ exfalso; clear - Hr; lia
    | left; change T_parse_STK with 8400; lia
    | right; right; left; lia
    | right; right; right; left; unfold SHADOW_OFF; unfold SB in Hr; lia
    | right; right; right; right; lia
    | right; left; octac
    | match goal with |- ?g => idtac "PPKEEP-FAIL" g end; fail 2 "pp_keep" ]
  | ]);
  destruct Hin
| assert (HKP : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange Ef rsf a ->
    aview tfibsegs (w_H WY) memY a = aview tfibsegs (w_H WX) memX a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by exact Ha; exact Hz);
  pose proof (pz_kept_own B LAWS lyc lyN Sc SN W memc mdc W2 mem2 md2 WX memX WY memY slo shi fpos F FL Eo (in_wrange Ef rsf)
    HARc HARN Hfrs HPERM ELF eq_refl eq_refl FFL
    ltac:(change T_parse_STK with 8400; lia) ltac:(lia)
    (proj1 (pp_oc_sep tfibsegs B LAWS lyc Sc W memc mdc live mo lb cidm posm cidl posl HARc HOCF))
    (pp_oc_img B lyc Sc W memc mdc live mo lb cidm posm cidl posl HARc HOCF)
    HZs HKE HKP (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as KE2;
  clear HKE HFr HG HKP HZs; rename KE2 into HKE ] end end end end end end.

Print Assumptions pp_seg4.
