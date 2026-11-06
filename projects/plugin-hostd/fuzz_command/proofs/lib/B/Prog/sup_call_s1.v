(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACkc.v and lib/A/ACja.v, the
   walk-tactic kit of cgif's ASan program walks, over fuzz_command's listing: module paths, csym; the image-class
   section is over any listing (PAImg L) instead of cgif's. One copy of each name ACkc.v and ACja.v both define;
   evalE is ACja.v's (ACj1.v's) final form. Also copied: boxed, box and unbox from lib/A/ACj1.v, relowF from
   lib/A/ACjb.v. fuzz_command's PaDenot.v has YC4b.v's norm_ss and reshok_bx, which match st_ok only; ACkc.v ran on
   lib/A/ACjr.v's, which also match st_ok_pi: they are here as norm_ss_pi and reshok_bx_pi, and the copied tactics
   call them. Dropped: awrF_rec's rule for cgif's Frame block (atom 11, FRAME_SIZE); the names TFLUSH_STK,
   TRAWADD_STK and LZW_TSTK from the unfold lists of awrF_rec and keptFL (awrFL computes the stack size of its goal
   instead, and keptFL the stack size of its ajournal hypothesis, by stk_lit); the RO (ro_below_ofl) context, which
   no lemma used. Changed: fuzz_command's awr_ok (lib/Reusable/YCbq.v) takes segs, B and an fr0 list that cgif's
   does not, and its awr_byte has a fifth case, so awrF_rec's and awrFL's patterns and lemma arguments have three
   more places and the frame rules pick the fourth case (in_frames) with right; right; right; left. The frame rules
   of awrF_rec and keptFL (atoms 516 and 529) take the frame class from the goal (the head of the owned-frame
   list, or the frames hypothesis) and compute its frame size by ffb_goal, where cgif's wrote class 2 and 256 / 32
   bytes; awrF_rec's rule for atom 60 takes any bounds sp0 - x <= sp1 <= sp0 - y, where cgif's wrote 400 and 384;
   upd_aboveW_init takes the segment list from the world's type, where ACja.v let typeclass search find pa_segs;
   add_atom's st_ok arm uses st_ok_havoc_hi (new here), where ACja.v used the st_ok_pi lemma, which does not apply
   to an st_ok hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaWalk.v, with its module paths, module names and numbers changed; 275 of its 421 lines of code are new or changed and 508 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, part 1: the walk tactics, the symbolic
   entry state with its seed, and the symbolic state of the walk's frame from 0x8b030 on with its seed (from the
   concrete facts of sup_call_s3.v's sc_live).

   The tactics are cgif_file_fuzzer's walk tactics (cgif lib/A/ACkc.v:32-389) as A's sup_resp walk carried
   them over to fuzz_command's listing (an earlier version of lib/A/Prog/sup_resp_s1.v, lines 33-207),
   here over B's kit (lib/B/Prog). The entry state is sup_resp's (the same reads: the 96-byte frame below the entry
   sp, the shadow GOT word 0xa5f50 and its cell, the use-after-return GOT word 0xa5fa8 and its flag).

   The frame state (sc_mid_ss): the registers are their own atoms 0..31, atom 32 is the frame's flag address FL and
   atoms 33..43 are the eleven saved registers' entry values (sc_saved, ra .. s9), so that every chunk is a closed
   term (a trap measured in libreac/fuzz_grant: vm_compute on an open term). Regions: the frame's shadow at
   s7 = (F >> 3) + SB (8 bytes, write window [wlo, whi), one-byte chunks l), the frame header at s8 = F ([F, F + 24),
   writable), the flag-byte word at F + 56 (read-only, = FL), and the saves at s0 = sp0 ([sp0 - 88, sp0), read-only). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3 sup_call_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- cgif's walk tactics (cgif lib/A/ACkc.v), over fuzz_command's listing ---- *)
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac hei_pose Eo kk ws :=
let Ho := rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac hei_havoc HS :=
lazymatch type of HS with
| st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ => first [ let H0 := rnHEI constr:(havoc Eo kk ws) in idtac | hei_pose Eo kk ws ]
| _ => idtac end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 32)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
(* the environment's second component is kept too (havoc and ewset change ew only), for aregs_preserved_of_st_ok *)
try (lazymatch goal with AD : ed ?Eo = ed E0 |- _ =>
  let AD2 := fresh "AD" in assert (AD2 : ed Ev = ed E0) by (rewrite HEv; exact AD); clear AD; rename AD2 into AD end);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 32 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac idx_of_off cs off :=
lazymatch cs with
| YP09.mkChunk off _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_off tl off in constr:(S i)
end.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Ltac upd_aboveW HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
(* the 32-aligned frame base (`andi sp,sp,-32`) and the apartness of two ranges: CmdSnText.v's snt_sp1_facts,
   snt_land_m32, snt_denot_and_m32, snt_zr_apart *)
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Ltac aconstsF HJx Kgot Kcell Kguar Kuar :=
let L := rnLAWS in let TL := rnTL in
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ L _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
let TLF := rnTLF in
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg; rewrite (pal_cell _ TL) in Kc;
rewrite (palf_got_uar _ TLF) in Kgu;
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu.
Ltac upd_aboveW_init HFr AG HUP :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of Wx with world ?sg =>
lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview sg (w_H Wx) (ms_mem msX) a = aview sg (w_H Wx) m0 a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end end end.
Lemma chunk_ok_redenote : forall segs E m base off w e e',
sv_denot E e' = sv_denot E e -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)) -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e')).
Proof. intros segs E m base off w e e' He H i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cbyte] in *. rewrite He. exact (H i Hi). Qed.
Lemma region_ok_rechunk : forall segs E m r j off w e e',
region_ok segs E m r -> nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) -> sv_denot E e' = sv_denot E e ->
region_ok segs E m (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))).
Proof.
intros segs E m r j off w e e' (H1 & H2 & H3 & H4) Hj He. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_list_upd; [exact H4|]. apply (chunk_ok_redenote segs E m _ off w e e' He).
exact (proj1 (Forall_forall _ _) H4 _ (nth_error_In _ _ Hj)).
Qed.
Ltac rqs_goal := repeat (match goal with |- context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v | Z0 => change (req_size n) with v end end).
Ltac norm_ssp HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac reshok HS := reshok_bx HS 32%nat.

(* ---- sup_call's entry state (sup_resp's, at sup_call's entry) ---- *)
Definition SC_Bx : sv := SOff 32 0.
Definition SC_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sc_regions0 : smem :=
[ stack_region 96; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sc_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_sc0 : sstate := mkSS AF_sup_call sr_atoms sc_regions0 None (mkFacts sc_atoms0 [] []).
Definition sc_extra (uar : Z) : list word := map (Z_to_bv 64) [SB; uar].

(* ---- the frame state from 0x8b030 on ---- *)
(* the frame's shadow (base s7, atom 23): 8 bytes, write window [wlo, whi), the one-byte chunks of l *)
Definition sc_shadow_chunks (l : list (Z * Z)) : list YP09.chunk :=
map (fun ov => YP09.mkChunk (fst ov) (CVal 1 (SLit (snd ov)))) l.
Definition sc_mid_shadow (l : list (Z * Z)) (wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some 23%nat) 0 8 wlo whi (sc_shadow_chunks l).
(* the frame header at F (base s8, atom 24): magic, description, pc, written at 0x8affc .. 0x8b004 and 0x8b098 *)
Definition sc_mid_hdr : YP09.region := YP09.mkRegion (Some 24%nat) 0 24 0 24 [].
(* the flag-byte word at F + 56, read at 0x8b0c4 *)
Definition sc_mid_flagw : YP09.region := YP09.mkRegion (Some 24%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
(* the saves below sp0 (base s0, atom 8), read by the epilogue 0x8b0f4 .. 0x8b11c: slot sp0 - 8 - 8 j holds atom
   33 + j *)
Definition sc_mid_saves : YP09.region :=
YP09.mkRegion (Some 8%nat) (-88) 0 0 0
[YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 33 0))].
Definition sc_mid_regions (l : list (Z * Z)) (wlo whi : Z) : smem :=
[sc_mid_shadow l wlo whi; sc_mid_hdr; sc_mid_flagw; sc_mid_saves].
Definition sc_mid_atoms : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (24%nat, HPTR 5);
  (23%nat, mkAF (SB + 512) (SB + 17592186044416) 2); (32%nat, HPTR 0) ].
Definition sc_mid_ss (pc : Z) (l : list (Z * Z)) (wlo whi : Z) : sstate :=
mkSS (AF_sup_call + pc) sr_atoms (sc_mid_regions l wlo whi) None (mkFacts sc_mid_atoms [] []).
(* the extra atoms: FL, then the entry's saved registers *)
Definition sc_mid_extra (regs0 : bvmap 5 word) (FL : Z) : list word :=
Z_to_bv 64 FL :: map (fun r => getr regs0 (Z_to_bv 5 r)) sc_saved.
Lemma sc_le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256 Hv). rewrite (Z.mod_small v 256 Hv). reflexivity.
Qed.
(* the shadow bytes a part knows at its start: offset, value *)
Definition sc_shadow_ok (rd : reader) (F : Z) (l : list (Z * Z)) : Prop :=
Forall (fun ov => 0 <= fst ov < 8 /\ 0 <= snd ov < 256 /\ rd (SB + F / 8 + fst ov) = Some (snd ov)) l.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the frame state's environment *)
Definition sc_mid_E (regs0 regsc : bvmap 5 word) (FL : Z) : env := Eimg (Ereg regsc (sc_mid_extra regs0 FL)).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma sc_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sc_extra (as_uar_cell B)))) ss_sc0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_call)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sc_extra (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_sc0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sc_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FFS. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold sc_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok sc_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.

Section m.
Variable MT : ameter_ops.
(* the frame state at the start of parts b, l and t, from sc_live (sup_call_s3.v): pc is the part's offset in
   sup_call (SC_PC_A, SC_PC_B, SC_PC_R), l the shadow bytes the part knows, [wlo, whi) the shadow bytes it writes *)
Lemma sc_seed : forall (pc : Z) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (O : list (Z * Z)) fpos F FL
  lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k (l : list (Z * Z)) wlo whi,
sc_live B ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc k ->
sc_shadow_ok (rdW Wc memc) F l -> regions_wf (sc_mid_regions l wlo whi) = true -> 0 <= wlo -> wlo <= whi -> whi <= 8 ->
st_ok_pi SEGS VAL (sc_mid_E regs regsc FL) (sc_mid_ss pc l wlo whi)
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_call + pc))) memc (seg_rom SEGS))).
Proof.
intros pc ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc k l wlo whi HL HSH HWF Hw0 Hw1 Hw2.
pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as (HJ & EF & EFL & HR & HFR & HFL).
destruct HR as (Esp & E8 & E18 & E24 & E19 & E20 & E21 & E23 & E25 & E3 & E4 & E26 & E27).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hfin : In (0, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR Hfin) as (HF64 & _ & _).
destruct (FFL lyc Sc Wc memc mdc 0 fpos HAR Hfin) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *.
rewrite EF in *. rewrite EFL in *.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres. change (64 / 8) with 8 in HFSpres.
pose proof HFLrng as ((HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & Hsp1al).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HFz : F + 64 <= SB \/ 0x10007fff8000 <= F)
  by (clear - HFhigh; unfold in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB in *; lia).
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
rewrite restrict_mkst_fx.
set (E := sc_mid_E regs regsc FL).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; unfold sc_mid_E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5;
      change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (U2 : bv_unsigned (ew E 2) = sc_sp1 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Esp).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite (EE 8%nat 8%bv eq_refl), E8; reflexivity).
assert (U23 : bv_unsigned (ew E 23) = SB + F / 8)
  by (rewrite (EE 23%nat 23%bv eq_refl), E23; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (U24 : bv_unsigned (ew E 24) = F)
  by (rewrite (EE 24%nat 24%bv eq_refl), E24; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 FL)
  by (subst E; unfold sc_mid_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (EX : forall j r, nth_error sc_saved j = Some r -> ew E (33 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj. subst E. unfold sc_mid_E.
  assert (Hj11 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sc_saved) with 11%nat in Hj11.
  rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite ew_Ereg_extra. unfold sc_mid_extra. cbn [nth].
  apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
assert (SAV : forall j r, nth_error sc_saved j = Some r ->
  YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs) (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0)))).
{ intros j r Hj.
  apply (chunk_ok_val SEGS E _ _ _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite (EX j r Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - apply val_mem_of_aval. replace (spZ regs + (-8 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    exact (HFR j r Hj). }
assert (SHC : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (SB + F / 8)) (sc_shadow_chunks l)).
{ unfold sc_shadow_chunks. apply Forall_map. eapply Forall_impl; [|exact HSH].
  intros [o v] (Ho & Hv & Hrd). cbn [fst snd] in *.
  apply (chunk_ok_val SEGS E _ _ o 1 (SLit v) v).
  - cbn [sv_denot]. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - apply val_mem_of_aval. intros kk Hkk. replace kk with 0%nat by lia. rewrite Z.add_0_r, Hrd. f_equal.
    exact (eq_sym (sc_le_byte1 v Hv)). }
unfold sc_mid_ss. apply pa_entry_st_ok_full.
- subst E. unfold sc_mid_E. apply regs_ok_Eimg_Ereg.
- exact HWF.
- unfold sc_mid_regions, sc_mid_shadow, sc_mid_hdr, sc_mid_flagw, sc_mid_saves.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
    split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|exact SHC].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ F 56 8 (SOff 32 0) FL).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HFL).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [exact (SAV 10%nat 25 eq_refl)|].
    apply Forall_cons; [exact (SAV 9%nat 24 eq_refl)|].
    apply Forall_cons; [exact (SAV 8%nat 23 eq_refl)|].
    apply Forall_cons; [exact (SAV 7%nat 22 eq_refl)|].
    apply Forall_cons; [exact (SAV 6%nat 21 eq_refl)|].
    apply Forall_cons; [exact (SAV 5%nat 20 eq_refl)|].
    apply Forall_cons; [exact (SAV 4%nat 19 eq_refl)|].
    apply Forall_cons; [exact (SAV 3%nat 18 eq_refl)|].
    apply Forall_cons; [exact (SAV 2%nat 9 eq_refl)|].
    apply Forall_cons; [exact (SAV 1%nat 8 eq_refl)|].
    apply Forall_cons; [exact (SAV 0%nat 1 eq_refl)|].
    apply Forall_nil.
- apply pairwise_disjoint_of_extents.
  unfold sc_mid_regions, sc_mid_shadow, sc_mid_hdr, sc_mid_flagw, sc_mid_saves, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U24, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite FFS in Hstk0, Hslo, Hbot.
  assert (HF8m : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
  clear - HFz HF4096 HFceil HF8lo HF8hi HF8m Hslo Hshi H47 Hceil C1 C3 Hstk0.
  unfold SB in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok sc_mid_atoms]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U24, U23, U32.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (HFq : F mod 32 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  assert (HSHq : (SB + F / 8) mod 4 = 0) by (unfold SB; clear - HF64; Z.div_mod_to_equations; lia).
  repeat match goal with |- _ /\ _ => split end; first [exact Hsp1al | exact Hal16 | exact HFq | exact HSHq | unfold SB in *; lia].
Qed.
End m.
End c.
End b.
End a.
