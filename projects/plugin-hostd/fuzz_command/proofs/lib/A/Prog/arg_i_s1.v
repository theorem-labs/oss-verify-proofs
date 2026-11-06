(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACkc.v, with its module paths, module names and numbers changed; 503 of its 679 lines of code are new or changed and 254 lines of the source are left out. *)
(* arg_i's walk on the ASan build of plugin-hostd/fuzz_command, part 1: the walk tactics, the symbolic entry state
   and its seed lemma.

   The tactics are cgif_file_fuzzer's walk tactics (cgif lib/A/ACkc.v:32-389, the support of its cgif_close and
   flushFrame walks), over fuzz_command's listing; module paths changed, and the frame-chain and sink parts that
   arg_i does not reach left out. The entry state follows cgif's flushFrame seed (cgif lib/A/ACj0.v:40-53,
   lib/A/AChz.v:57-196): the stack below the entry sp, the shadow GOT word and cell, the use-after-return GOT word
   and flag, and the one field of the call slot that arg_i reads before it writes (c->nargs). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
(* the plain proof's printf facts on "%d" (lib/Prog/arg_i.v:36-54); its module shares the walk's base name, so it is
   named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.
Lemma ai_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
(* snprintf(b, 16, "%d", v) writes dec v and its terminator: the text is at most 11 bytes *)
Lemma ai_dec_text : forall v, -2^31 <= v < 2^31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (dec_length v Hv) as Hl. pose proof (ai_dec_len v Hv) as Hl2.
rewrite firstn_all2 by (rewrite Hl2; change (Z.to_nat (16 - 1)) with 15%nat; lia).
unfold PF.pf_bytes in *. rewrite map_app. rewrite <- (PAI.ai_pf_dec v Hv). reflexivity.
Qed.

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
(* evalE without its closing lia, and with closed side conditions: for hypotheses about to be fed to a small lia *)
Ltac evalEq AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (clear; lia);
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by (clear; lia) end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB.
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
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
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
(* The frame's shadow region (atom [s]) lies inside the shadow band, so an app_entries entry for its writable
   window cannot hold (app_apart asks the window to be OUTSIDE the band). cgif's walks narrow that window to the
   empty one before every sh_ok rebuild and widen it again for the shadow stores (cgif lib/A/ACkc.v:247-261,
   `fs_roF`, used at ACa2.v:367). *)
Ltac ai_fs_ro HS s :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs s in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS
| st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs s in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS end.
(* the reverse: widen it to the frame's 8 shadow bytes for the release stores; [Es] is  ew E s = Z_to_bv 64 (SB + F / 8)
   and [Hp] the frame's shadow presence  forall o, 0 <= o < 8 -> apresent _ _ (shadow_addr F + o) /\ _ *)
Ltac ai_fs_rw HS s Es Hp :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs s in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 8) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 8 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst];
           cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
           rewrite Es, unsigned_lit_small by (unfold SB; lia);
           intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
           apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS
| st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs s in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region _ Ex ssx msx i r (set_window r 0 8) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 8 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst];
           cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
           rewrite Es, unsigned_lit_small by (unfold SB; lia);
           intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
           apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS end.
(* the branch  blt (SLit z) (SOff n 0): cgif's cw_lt_atom with the two sides exchanged *)
Lemma ai_lt_rev : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SLit z)) (sv_denot E (SOff n 0)) = (z <? v).
Proof.
intros E n v z Hn Hv Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* the address arg_i computes for c->args[m] (0x8a37c .. 0x8a38c): (c + 8) + (m << 3) *)
Lemma ai_args_U : forall E c m, ew E 10 = Z_to_bv 64 c -> ew E 34 = Z_to_bv 64 m -> 0 <= c < 2 ^ 62 -> 0 <= m <= 6 ->
U E (SAlu ALU_ADD (SOff 10 8) (SAlu ALU_SLL (SOff 34 0) (SLit 3))) = c + 8 + 8 * m.
Proof.
intros E c m H10 H34 Hc Hm. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 c 8 H10 ltac:(lia) ltac:(lia)), (U_atom E 34 m H34 ltac:(lia)), U_SLit.
change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (m * 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the 1-byte region of the frame's flag byte (atom [Efl] holds its address), for the store that releases the
   frame; it is apart from every other region of the state: it is owned by the allocator (so not a byte of the
   frame, [HnoF]), outside the image and below the shadow band ([HFLrng]) (cgif lib/A/ACk5.v:273-302) *)
Ltac ai_flag_region HS AG Efl HFLpres HFLrng HFLown HnoF :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1028%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
  rewrite Efl, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable _);
  lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact HFLpres)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
  repeat split;
  first [ zone_lia
        | lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
          let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
          destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
          destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
          apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown] end
        | match goal with |- ?g => idtac "FLAGDISJ:" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS end.
(* the same with closed checks: [tacd] shows the flag byte apart from a region that is not the frame's, with a
   small lia; the frame's regions go by the ownership argument *)
Ltac ai_flag_region_q HS AG Efl HFLpres HFLrng HFLown HnoF tacd :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1028%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
  rewrite Efl, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable _);
  lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact HFLpres)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalEq AG;
  repeat split;
  first [ lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
          let Hlt := fresh "Hlt" in let Hge := fresh "Hge" in let Hlt2 := fresh "Hlt2" in let Hge2 := fresh "Hge2" in
          destruct (Z_lt_ge_dec fl (x + l)) as [Hlt | Hge]; [left; clear - Hlt; lia|];
          destruct (Z_lt_ge_dec fl (x + h)) as [Hlt2 | Hge2]; [exfalso | right; clear - Hge2; lia];
          apply (HnoF fl); [clear - Hge Hlt2; lia | exact HFLown] end
        | tacd
        | match goal with |- ?g => idtac "FLAGDISJ:" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ssp HS end.
(* every writable byte of the state's regions at the frame's release is one the journal admits (the function's own
   stack window, or a byte of the frame it owns, or its shadow), or the frame's flag byte itself
   (cgif lib/A/ACk5.v:323-340, `wrangeR`) *)
Ltac ai_wrange AG fpos Fr FLr :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
  first [ exfalso; clear - Hr; lia
        | right; fold FLr; clear - Hr; lia
        | left; left; clear - Hr; unfold ARG_I_STK, ESTACK, XSTRDUP_STK, ASTACK; lia
        | left; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
          first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold Fr; clear - Hr; lia
                | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
                  change (fs_frame_bytes 0 / 8) with 8; fold Fr; unfold SB in *; clear - Hr; lia ]
        | left; left; lia
        | match goal with |- ?g => idtac "WRFAIL:" g end;
          match type of Hr with ?t => idtac "WRHYP:" t end; fail 2 "ai_wrange" ]
| ]);
destruct Hin.
(* the same after a program call: the layout is a later one, [EFr] / [EFLr] rewrite its frame and flag addresses
   back to [Fr] / [FLr]; [tacx] shows awr_byte for the program-static windows *)
Ltac ai_wrange_x AG fpos Fr FLr EFr EFLr tacx :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalEq AG; intros Hr;
  first [ exfalso; clear - Hr; lia
        | right; rewrite ?EFLr; fold FLr; clear - Hr; lia
        | left; left; clear - Hr; unfold ARG_I_STK, ESTACK, XSTRDUP_STK, ASTACK; lia
        | left; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
          first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EFr; fold Fr;
                  clear - Hr; lia
                | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite ?EFr; rewrite <- SB_SHADOW_OFF;
                  change (fs_frame_bytes 0 / 8) with 8; fold Fr; unfold SB in *; clear - Hr; lia ]
        | left; tacx Hr
        | left; left; lia
        | match goal with |- ?g => idtac "WRFAIL:" g end;
          match type of Hr with ?t => idtac "WRHYP:" t end; fail 2 "ai_wrange_x" ]
| ]);
destruct Hin.
(* closes  ~ in_wrange E rs a  for a byte [a] of a range whose apartness from every window of the state is the one
   fact [HPA a Ha] (so each check is a small lia) *)
Ltac ai_nowrange2 AG HPA a Ha :=
let HPAa := fresh "HPAa" in pose proof (HPA a Ha) as HPAa;
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalEq AG; intros Hr;
   first [ clear - Hr HPAa; lia | match type of Hr with ?t => idtac "NOWRANGE2:" t end; fail 2 "ai_nowrange2" ] |]);
destruct Hin.
(* a region chunk's bytes, read through the view: val_mem of the restricted memory gives aval_mem *)
Lemma ai_aval_of_val : forall segs H (m : word -> option byte) a (n : nat) v,
val_mem segs (mrestrict H m) a n v -> aval_mem (aview segs H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* the flag byte is 0 in the state the run ends in: the flag region's chunk (cgif lib/A/ACk5.v:341-355, `flag0`) *)
Ltac ai_flag0 Efl :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in let V0 := fresh "V0" in
intros msr HSr;
lazymatch type of HSr with
| st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
  ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Efl;
        apply unsigned_lit_small; lia)
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end
| st_ok _ ?Ex ?ssx _ =>
pose proof (st_ok_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
  ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Efl;
        apply unsigned_lit_small; lia)
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
(* a byte outside every write window of a run's regions keeps its value (cgif lib/A/ACk5.v:356-368, `upd_above`,
   for one address) *)
Lemma ai_aview_kept : forall segs E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview segs H m' a = aview segs H m a.
Proof.
intros segs E rs H m m' a Hf Ha Hw. unfold aview, mbyte.
rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hw.
Qed.
(* closes  ~ in_wrange E rs a  by running through the state's regions *)
Ltac ai_nowrange AG :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
   first [ lia | match type of Hr with ?t => idtac "NOWRANGE:" t end; fail 2 "ai_nowrange" ] |]);
destruct Hin.
(* one byte of the frame's shadow region (atom 1029), as the state holds it: its chunk at [off] is 0 *)
Ltac ai_sh_byte HS Es off V :=
let HR := fresh "HRsh" in
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 1029%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msx) n _ cs lo hi wlo whi off 1%N (SLit 0) 0 HR
  ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Es;
        apply unsigned_lit_small; unfold SB; lia)
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V end
| st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 1029%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msx) n _ cs lo hi wlo whi off 1%N (SLit 0) 0 HR
  ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Es;
        apply unsigned_lit_small; unfold SB; lia)
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
clear HR; cbn [ms_mem restrict] in V.
(* one callee-saved register of aregs_preserved_eqs: the epilogue reloaded it from its entry slot, so its symbolic
   value is the register's own entry atom (cgif lib/A/ACk5.v:268-272, `creg`) *)
Ltac ai_creg HS AG EE :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in prreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite AG by lia;
apply EE; reflexivity end.
(* awr_ok over a state's regions: read-only regions drop out; each writable window is shown in awr_byte by [tacw]
   on a goal  awr_byte ... a  with  b + wlo <= a < b + whi  as Ha *)
Ltac ai_awr AG tacw :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?f0 ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc f0 ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply awr_ok_cons_gen; [reflexivity | evalE AG |
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; tacw |] ].
(* after each run or call the model is left as with_vm_backing (m_vm_lazy md) mat md in goal and journal; name it,
   so the term does not double over a chain of runs *)
Ltac mdclr := repeat match goal with
| |- context [with_vm_backing ?l ?m ?d] => let mdv := fresh "mdv" in set (mdv := with_vm_backing l m d) in *; clearbody mdv
| H : context [with_vm_backing ?l ?m ?d] |- _ => let mdv := fresh "mdv" in set (mdv := with_vm_backing l m d) in *; clearbody mdv
end.
Lemma zr_apart : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
(forall a, lo1 <= a < hi1 -> ~ (lo2 <= a < hi2)) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof. intros lo1 hi1 lo2 hi2 H1 H2 H. destruct (Z_le_gt_dec hi1 lo2); [left; exact l|]. right.
destruct (Z_le_gt_dec hi2 lo1); [exact l|]. exfalso. apply (H (Z.max lo1 lo2)); lia. Qed.

(* ---- arg_i's entry state ---- *)
Definition AI_Bx : sv := SOff 32 0.
Definition AI_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* sh_ok of a state whose regions' app entries hold, with the call slot's entry (atom 10, [0, 56)) from [HZc] *)
Ltac ai_reshok HS AG HZc :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto_with SH AI_Bx Ex (mrestrict (w_H Wx) (ms_mem msx)) [mkSHE 10 0 56]
ltac:(eapply (shent_ok_of_range _ (w_H Wx) (ms_mem msx) Ex AI_Bx 10 _ 56 _ 0 56 HZc);
  [ unfold AI_Bx; apply (U_atom Ex 32 SB); [evalE AG | unfold SB; lia]
  | apply U_atom; [evalE AG | lia] | lia | lia
  | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SHADOW_OFF; cbn [Z.min Z.max] in Hx; lia ]) end.
(* the same with a second entry: c->args[m]'s 8 bytes (atom 1030) from [HZa] *)
Ltac ai_reshok2 HS AG HZc HZa :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto_with SH AI_Bx Ex (mrestrict (w_H Wx) (ms_mem msx)) [mkSHE 10 0 56; mkSHE 1030 0 8]
ltac:(first
  [ eapply (shent_ok_of_range _ (w_H Wx) (ms_mem msx) Ex AI_Bx 10 _ 56 _ 0 56 HZc);
    [ unfold AI_Bx; apply (U_atom Ex 32 SB); [evalE AG | unfold SB; lia]
    | apply U_atom; [evalE AG | lia] | lia | lia
    | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SHADOW_OFF; cbn [Z.min Z.max] in Hx; lia ]
  | eapply (shent_ok_of_range _ (w_H Wx) (ms_mem msx) Ex AI_Bx 1030 _ 8 _ 0 8 HZa);
    [ unfold AI_Bx; apply (U_atom Ex 32 SB); [evalE AG | unfold SB; lia]
    | apply U_atom; [evalE AG | lia] | lia | lia
    | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SHADOW_OFF; cbn [Z.min Z.max] in Hx; lia ] ]) end.
(* c->nargs: the 4 bytes at c + 4 (RecInv.v CALL_OFF_NARGS) hold atom 34 *)
Definition ai_slot_region : YP09.region := YP09.mkRegion (Some 10%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition ai_regions0 : smem :=
[ stack_region 112; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33; ai_slot_region ].
Definition ai_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 0x606000 3); (32%nat, mkAF SB SB 0);
  (33%nat, mkAF 0x10000 0x606000 2); (34%nat, mkAF 0 6 0) ].
Definition ss_ai0 : sstate := mkSS AF_arg_i sr_atoms ai_regions0 None (mkFacts ai_atoms0 [] []).
Definition ai_extra (uar m : Z) : list word := map (Z_to_bv 64) [SB; uar; m].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section z.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
(* the call slot's shadow: the slot lies in the record's zero-shadow range of the image's .data/.bss (CmdZsh) *)
Lemma ai_zc : forall ly S W mem md c,
AR SEGS B ly S W mem md ->
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
range_addressable (rdW W mem) SHADOW_OFF c 56.
Proof.
intros ly S W mem md c HAR Hc.
destruct Hc as [(i & Hi & ->) | ->]; unfold OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_G_REC, A_REC_SPILL in *.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) _ 56 HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | cbn [fst snd]; lia | cbn [fst snd]; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) _ 56 HAR);
  [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity | cbn [fst snd]; lia | cbn [fst snd]; lia].
Qed.
Lemma ai_ro_lit : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f00 RO_lit_21f00.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat match type of H with
| abytes_atR _ 0x21f00 _ /\ _ => fail 1
| _ /\ _ => destruct H as [_ H] end.
exact (proj1 H).
Qed.
End z.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis HB : CmdBSyms B.
(* every byte of the program's statics is in the record's as_prog_static (CmdBSyms' ts_prog); the core's
   prog_static_sep keeps those bytes apart from the record's own cells *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_exists.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
[exists (0x5e3740, 960) | exists (0x5e3be0, 56) | exists (0x5e3c60, 4)]; cbn [In];
(split; [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | unfold in_zr; cbn [fst snd]; lia]).
Qed.
Lemma ai_slot_PG : forall c a,
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
c <= a < c + 56 -> inFP cmd_PG a.
Proof.
intros c a Hc Ha. unfold cmd_PG. destruct Hc as [(i & Hi & ->) | ->];
unfold OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_G_REC, A_REC_SPILL, A_G_QUITTING in *;
[exists (6174528, 6174528 + 960); cbn [In fst snd]; split; [left; reflexivity | lia]
|exists (6175712, 6175712 + 56); cbn [In fst snd]; split; [right; left; reflexivity | lia]].
Qed.
Lemma ai_slot_apart : forall ly S W mem md c,
AR SEGS B ly S W mem md ->
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
forall a, c <= a < c + 56 -> ~ Exists (in_zr a) (asyms_areas B) /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly S W mem md c HAR Hc a Ha.
assert (Hp : Exists (in_zr a) (as_prog_static B)) by (apply HPROG; exact (ai_slot_PG c a Hc Ha)).
pose proof (prog_static_sep B a (am_syms _ _ _ _ (proj1 HAR)) Hp) as (H1 & H2 & H3). auto.
Qed.
(* the read-only bytes the record does not own survive a journal whose footprint misses them and does not open the
   sink (CmdBase's arodata_ok_journalP, with the sink case closed instead of the ro_below_ofl class) *)
Lemma ai_aro_journal : forall RLO RHI STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP -> (forall a, RLO <= a < RHI -> in_img SEGS a) -> (forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros RLO RHI STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hso Hrelro HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed FP a Hso (HFP a Hro))].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (Hrelro a Hgot)].
Qed.
(* the slot's alignment and place in the image *)
Lemma ai_slot_range : forall c,
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
c mod 8 = 0 /\ 0x5e3740 <= c /\ c + 56 <= 0x5e3c18.
Proof.
intros c [(i & Hi & ->) | ->]; unfold OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_G_REC, A_REC_SPILL in *.
- split; [|lia]. replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia. apply Z_mod_mult.
- split; [reflexivity | lia].
Qed.
Lemma in_areas_cells : forall x len, In (x, len)
  [(as_shadow_cell B, 8); (as_uar_cell B, 4); (as_got_shadow B, 8); (as_got_uar B, 8)] -> In (x, len) (asyms_areas B).
Proof. intros x len H. unfold asyms_areas. cbn [In] in *. tauto. Qed.
Lemma ai_entry : forall W ly S regs mem md ch c m,
afn_pre SEGS B ARG_I_STK ly S W regs mem md ch ->
getr regs 10 = w64 c ->
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 m -> 0 <= m <= REC_ARGS_MAX ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ai_extra (as_uar_cell B) m))) ss_ai0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arg_i)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch c m HPRE H10 Hc Hm Hm6.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : ARG_I_STK = 16528) by reflexivity.
pose proof (ai_slot_range c Hc) as (Hc8 & Hc0 & Hc1).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
pose proof (ai_slot_apart ly S W mem md c HAR Hc) as Hap.
assert (Hareas : forall x len, In (x, len) [(as_shadow_cell B, 8); (as_uar_cell B, 4); (as_got_shadow B, 8); (as_got_uar B, 8)] ->
  c + 8 <= x \/ x + len <= c + 4).
{ intros x len Hin.
  assert (Hlen : 0 < len) by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as _ <-; lia|]); destruct Hin).
  apply zr_apart; [lia | lia |]. intros a Ha Hx. apply (proj1 (Hap a ltac:(lia))). apply Exists_exists. exists (x, len).
  split; [exact (in_areas_cells x len Hin) | unfold in_zr; cbn [fst snd]; lia]. }
pose proof (Hareas _ _ ltac:(cbn [In]; left; reflexivity)) as D12.
pose proof (Hareas _ _ ltac:(cbn [In]; right; left; reflexivity)) as Du.
pose proof (Hareas _ _ ltac:(cbn [In]; right; right; left; reflexivity)) as D0.
pose proof (Hareas _ _ ltac:(cbn [In]; right; right; right; left; reflexivity)) as D1.
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite (pal_got_shadow B TL) in D0. rewrite (pal_cell B TL) in D12. rewrite (palf_got_uar B TLF) in D1.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ai_extra (as_uar_cell B) m))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_ai0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ai_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, ai_slot_region.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
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
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 10%nat c E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ c 4 4 (SOff 34 0) m);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold REC_ARGS_MAX in Hm6; zside | zside |].
  exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hm).
- apply pairwise_disjoint_of_extents.
unfold ai_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, ai_slot_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat c E10), (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep Hc0 Hc1 D0 D1 D12 Du. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok ai_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34.
rewrite !unsigned_lit_small by (unfold SB, REC_ARGS_MAX in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold REC_ARGS_MAX in Hm6.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.
End c.
End b.
End a.
