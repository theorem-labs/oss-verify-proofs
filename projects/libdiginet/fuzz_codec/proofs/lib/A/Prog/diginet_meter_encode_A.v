(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_personality_A.v, with its module names changed; 691 of its 735 lines of code are new or changed and 247 lines of the source are left out. *)
(* diginet_meter_encode (diginet_codec.c:217-231) at image A 0x85600, 141 instructions, real frame 48, no side-stack
   frame (diginet_meter_mask and diginet_sysex_encode are inlined), against lib/A/Prog/CPgEncC.v's cdc_meter_specX.
   a0 = p (the personality), a1 = channel, a2 = right (int), a3 = segments, a4 = out (all lw).
   - p = NULL (pd = None): 0x85620 beqz a4 is taken, a0 = -1 = E_ARG, out is not written (meter_none). Otherwise
     the facts of p and out (0 < p, 0 < out) decide the two NULL tests.
   - 0x85630 bltu 31, channel and 0x85638 bltu 14, segments: taken -> a0 = -11 = E_RANGE, out not written.
   - 0x8563c-0x85670: the shadow offset SB through the .got slot and its cell (the base regions of CPgWalk),
     s1 = channel | (right != 0) << 5, the mask ~(-1 << segments) (sllw), and the payload bytes s1, mask >> 7,
     mask & 0x7f stored at sp + 13 .. sp + 15 of the frame. At 0x85674 the walk drops the two cells (cw_drop_gb)
     and adds p->device (p + 16, read-only, its byte from pers_argA's garr8); its checked load is paid by the shadow
     entry mkSHE 10 16 20 (cimg_range's cimg_usable at the walk's AR).
   - 0x8568c bltz on the device byte: taken (bit 7 set) -> a0 = -1 = E_ARG, out not written.
   - 0x8569c, 0x8569c + 12: the payload loop's bltz on the bytes ch and mask >> 7, refuted (each is below 0x80); the
     engine decides the third byte (mask & 0x7f). From here the four pieces of out the code stores to are regions
     (twr_ok); out's checks are paid by mkSHE 14 0 32 (cdst_ok).
   - 0x856ac-0x85710: out[0..4) = f0, 13, device, 10; 0x85720 __asan_memcpy(out + 4, sp + 13, 3) through
     CPgWalkIntr.cw_intrin_call (the source on the function's own real stack: CPgWalkFrame.cw_stack_src).
   - 0x85724-0x857b4: out[7] = f7, out[24] = 8, out[25] = 0, the 4-byte key ch | 0x40000 at out + 28, a0 = 0.
   Every error-path call (errpath_load1 / errpath_store1 / errpath_store4) sits behind a shadow check the entries
   decide. The memory clause: the walk writes only the frame [sp - 48, sp), the runtime's window below it and out
   (mt_zone), all inside the call's window [sp - T_meter, sp) or out. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YC85 YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgWalkIntr CPgWalkFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_METER : Z := 0x85600.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.

(* bytes kept in a view keep a byte array *)
Lemma garr8_of_kept : forall (W : world tfibsegs) (m m' : word -> option byte) base l,
garr8 tfibsegs (mrestrict (w_H W) m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
garr8 tfibsegs (mrestrict (w_H W) m') base l.
Proof.
intros W m m' base l H Hk. apply (garr8_frame tfibsegs _ _ base l H). intros a Ha.
apply (mbyte_of_aview tfibsegs). exact (Hk a Ha).
Qed.

Lemma meter_none : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs
  channel right segments out before,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter ->
getr regs 10 = w64 0 ->
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_meter out before ->
SRr tfibsegs W (cfg_at tfibsegs A_METER regs memc mdc)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T_meter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res tfibsegs out before (meter_spec None channel right segments))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs channel right segments out before HE H10 HOUT.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ0 as HJ. pose proof HJ as (HAR & _).
assert (HT : T_meter = 4144) by reflexivity.
pose proof HOUT as ((Hout0 & Houtn & Htdst & Htwr & Hra_o & Hhull_o & Hamr_o & Hcw_o) & Hbefore & Hlen).
pose proof (cw_entry_base B TL LAWS A_METER 48 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter HE
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HEq.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
clear HEq.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_meter <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_METER) with (Z_to_bv 64 A_METER).
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
cw_branch Hb.
- (* 0x85620 beqz a4 TAKEN (p = 0): to 0x857a0 with a0 = -1, restore, ret *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc
      out 32 a HAR Htdst Ha Himg)) ltac:(intros a Ha; left; exact Ha))
    ltac:(unfold cenc_res; cbn [meter_spec fst snd cmd_outZ]; split;
      [ rewrite R10; apply bv_eq; vm_compute; reflexivity
      | apply (garr8_of_kept W memc _ out before Hbefore); rewrite Hlen; change (Z.of_nat 32) with 32;
        intros a Ha; apply KE; [lia|]; destruct Hcw_o; lia ]).
- (* not taken: refuted, p = 0 *)
  exfalso. rewrite branch_eq_U, (cw_U_atom0 E 10 0 E10 ltac:(lia)), U_lit in Hb by lia. discriminate Hb.
Qed.

Definition mt_zone (sp out a : Z) : Prop :=
(sp - T_meter <= a < sp) \/ (out <= a < out + 8) \/ (out + 24 <= a < out + 26) \/ (out + 28 <= a < out + 32).
Definition mt_AF : list (nat * afact) := [(10%nat, mkAF 1 (2 ^ 47 - 21) 0); (14%nat, mkAF 1 (2 ^ 47 - 33) 0)].
Definition mt_SH : list shent := [mkSHE 10 16 20; mkSHE 14 0 32].
(* the device byte p->device (p + 16), read-only; the four pieces of out the code stores to *)
Definition mt_p16 : YP09.region := YP09.mkRegion (Some 10%nat) 16 20 16 16 [YP09.mkChunk 16 (CVal 1 (SOff 33 0))].
Definition mt_o0 : YP09.region := YP09.mkRegion (Some 14%nat) 0 4 0 4 [].
Definition mt_o7 : YP09.region := YP09.mkRegion (Some 14%nat) 7 8 7 8 [].
Definition mt_o24 : YP09.region := YP09.mkRegion (Some 14%nat) 24 26 24 26 [].
Definition mt_o28 : YP09.region := YP09.mkRegion (Some 14%nat) 28 32 28 32 [].

(* the zone of a state's write windows: the save area and the pieces of out *)
Ltac mt_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta; try unfold mt_zone;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other in Hb by lia;
repeat match goal with Bq : bv_unsigned (ew _ _) = _ |- _ => rewrite Bq in Hb end; lia | ]);
destruct Hr.
(* the write-range obligation: the save area of atom 2, the pieces of out (twr_ok), read-only regions *)
Ltac mt_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| match goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia; rewrite B2; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| match goal with B14 : bv_unsigned (ew _ 14) = ?q, Htw : twr_ok _ _ _ _ _ _ _ _ _ _ ?Wv ?mv _ ?q 32 |- _ =>
  eapply (cw_awr_ok_cons_twr _ _ _ _ _ _ _ _ _ _ _ _ Wv mv _ q 32 14%nat);
  [reflexivity | rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia; exact B14
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | exact Htw |] end ]
end.
(* add region r to the walk's state HS *)
Ltac mt_add HS r rok dis :=
norm_ss HS;
lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssv ?msv =>
let H := fresh "HSa" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv r HS ltac:(vm_compute; reflexivity) ltac:(rok) ltac:(dis)) as H;
clear HS; rename H into HS; norm_ss HS end.
(* a piece of out: its window bytes are present (twr_ok, at the walk's current journal HJ) *)
Ltac mt_rok_o :=
lazymatch goal with B14 : bv_unsigned (ew _ 14) = ?q, Htw : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?q 32,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
unfold region_ok, mt_o0, mt_o7, mt_o24, mt_o28, mt_p16;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia; rewrite B14; split; [lia|]; split; [lia|]; split; [|constructor];
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable tfibsegs);
exact (proj1 (awr_byte_present tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + o) HJ (proj1 (Htw (q + o) ltac:(lia)))))
end.
(* p->device: its byte is d_dev d (pers_argA), kept by the walk so far (KE) *)
Ltac mt_rok_p :=
lazymatch goal with B10 : bv_unsigned (ew ?Ev 10) = ?pv, E33 : ew ?Ev 33 = Z_to_bv 64 ?dv,
  HV16 : val_mem _ _ (?pv + 16) 1 ?dv, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
unfold region_ok, mt_o0, mt_o7, mt_o24, mt_o28, mt_p16;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
rewrite B10; split; [lia|]; split; [lia|]; split; [let o := fresh "o" in intros o ?; lia|];
constructor; [|constructor];
apply (chunk_ok_val tfibsegs Ev _ pv 16 1 (SOff 33 0) dv);
[ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |];
refine (cw_val_mem_kept _ _ _ _ (pv + 16) 1 dv _ HV16);
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; change (Z.of_nat 1) with 1 in Hx;
apply KE; [lia|]; cbv beta; try unfold mt_zone; lia
end.
(* the regions of the state are pairwise apart: the frame and out (coff_win), p->device and both *)
Ltac mt_dis :=
unfold mt_o0, mt_o7, mt_o24, mt_o28, mt_p16; cbn [ss_mem YP09.all_disjoint]; unfold YP09.extent_disjoint;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia;
repeat match goal with Bq : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Bq end; repeat split; lia.
(* a branch condition over a later env, restated over the walk's base env (the atoms below 34 are unchanged) *)
Ltac mt_toE H :=
lazymatch goal with HAE0 : env_agree 32 (Ereg _ _) ?E0 |- _ =>
repeat match type of H with context [sv_denot ?Ec ?e] =>
  lazymatch Ec with E0 => fail | _ =>
  rewrite (YP06.sv_denot_agree 34 E0 Ec e ltac:(env_agree_chain (YP06.env_agree_refl 34 E0))
    ltac:(vm_compute; reflexivity)) in H end end end.

(* ================================ the arithmetic ================================ *)
Lemma mt_forall_range : forall (P : Z -> bool) (n : Z),
forallb P (map Z.of_nat (seq 0 (Z.to_nat n))) = true -> forall z, 0 <= z < n -> P z = true.
Proof.
intros P n H z Hz. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat z). split; [apply Z2Nat.id; lia|]. apply in_seq. lia.
Qed.
(* enumerate the integer x from the bound Hl : lo <= x up to hi, closing each case by tac *)
Ltac zcases x hi tac :=
lazymatch goal with Hl : ?lo <= x |- _ =>
lazymatch eval vm_compute in (Z.leb lo hi) with
| true => let Heq := fresh "Heq" in let Hne := fresh "Hne" in
  destruct (Z.eq_dec x lo) as [Heq | Hne];
  [ subst x; tac
  | let lo' := eval vm_compute in (lo + 1) in assert (lo' <= x) by lia; clear Hl Hne; zcases x hi tac ]
| false => exfalso; lia
end end.
Lemma mt_s32_small : forall c, 0 <= c < 2 ^ 31 -> s32 c = c.
Proof. intros c Hc. unfold s32. destruct (Z.ltb_spec c (2 ^ 31)); lia. Qed.
(* a 32-bit unsigned argument loaded with lw *)
Lemma mt_U_u32 : forall E n c, ew E n = Z_to_bv 64 (s32 c) -> 0 <= c < 2 ^ 32 ->
U E (SOff n 0) = if c <? 2 ^ 31 then c else c + 18446744069414584320.
Proof.
intros E n c Hn Hc. rewrite U_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. unfold s32.
destruct (Z.ltb_spec c (2 ^ 31)); [apply Z.mod_small; lia|].
replace (c - 2 ^ 32) with ((c + 18446744069414584320) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* `bltu k, r` with r = a lw-loaded unsigned c and a small constant k: taken exactly when k < c *)
Lemma mt_br_ltu_u32 : forall E n c k, ew E n = Z_to_bv 64 (s32 c) -> 0 <= c < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot E (SLit k)) (sv_denot E (SOff n 0)) = (k <? c).
Proof.
intros E n c k Hn Hc Hk. rewrite branch_ltu_U, U_lit by lia. rewrite (mt_U_u32 E n c Hn Hc).
destruct (Z.ltb_spec c (2 ^ 31)); [reflexivity|].
destruct (Z.ltb_spec k (c + 18446744069414584320)); destruct (Z.ltb_spec k c); first [reflexivity | lia].
Qed.
Lemma mt_sx8_check : forall v, 0 <= v < 256 -> (YO0b.s64 (zcanon (bv_swrap 8 v)) <? YO0b.s64 (zcanon 0)) = (128 <=? v).
Proof.
intros v Hv.
pose proof (mt_forall_range (fun v => Bool.eqb (YO0b.s64 (zcanon (bv_swrap 8 v)) <? YO0b.s64 (zcanon 0)) (128 <=? v)) 256
  ltac:(vm_compute; reflexivity) v Hv) as K.
apply Bool.eqb_prop in K. exact K.
Qed.
(* `lb; bltz`: the loaded byte is negative exactly when its bit 7 is set *)
Lemma mt_br_sx8e : forall E e,
branch_taken BC_LT (sv_denot E (SExt true 8 e)) (sv_denot E (SLit 0)) = (128 <=? U E e mod 256).
Proof.
intros E e. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SExt true 8 e))) with (U E (SExt true 8 e)).
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SExt, U_SLit. cbv iota beta. change (2 ^ Z.of_N 8) with 256.
apply mt_sx8_check. apply Z.mod_pos_bound. lia.
Qed.
(* the payload's first byte: channel, with 0x20 when right is not 0 *)
Definition mch (ch r : Z) : Z := Z.lor ch (bit_or_0 (negb (r =? 0)) 0x20).
Lemma mt_U_int : forall E n r, ew E n = Z_to_bv 64 r -> U E (SOff n 0) = r mod 2 ^ 64.
Proof.
intros E n r Hn. rewrite U_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma mt_U_ch : forall E c r, ew E 11 = Z_to_bv 64 c -> ew E 12 = Z_to_bv 64 r -> 0 <= c -> c <= 31 ->
- 2 ^ 31 <= r < 2 ^ 31 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) (SOff 11 0)) = mch c r.
Proof.
intros E c r H11 H12 Hc0 Hc1 Hr. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom E 11 c H11) by lia.
rewrite (mt_U_int E 12 r H12).
replace (zcanon 0 <? r mod 2 ^ 64) with (negb (r =? 0)).
2: { change (zcanon 0) with 0. destruct (Z.eqb_spec r 0) as [->|Hne]; [reflexivity|]. symmetry. apply Z.ltb_lt.
  destruct (Z.ltb_spec r 0).
  - rewrite <- (Z.mod_add r 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
unfold mch, bit_or_0. destruct (negb (r =? 0)); zcases c 31 ltac:(vm_compute; reflexivity).
Qed.
Lemma mch_range : forall c r, 0 <= c < 32 -> 0 <= mch c r < 64.
Proof.
intros c r H. unfold mch, bit_or_0. destruct (negb (r =? 0)); destruct H as [H0 H1]; zcases c 31 ltac:(repeat split; vm_compute; congruence).
Qed.
(* `li a0,-1; sllw a3,a0,a3; not a3,a3` on segments s gives meter_mask; its two payload bytes *)
Definition sv_mask : sv := SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 13 0)) (SLit (-1)).
Lemma mt_U_mask : forall E s, ew E 13 = Z_to_bv 64 s -> 0 <= s -> s <= 14 ->
U E sv_mask = meter_mask_spec s /\ U E (SAlu ALU_SRL sv_mask (SLit 7)) = Z.shiftr (meter_mask_spec s) 7 /\
U E (SAlu ALU_AND sv_mask (SLit 127)) = Z.land (meter_mask_spec s) 127.
Proof.
intros E s H13 Hs0 Hs1. unfold sv_mask. rewrite !U_SAlu, !U_SLit, U_of_S, S_SAluw, !U_SLit, (U_atom E 13 s H13) by lia.
cbn [zalu_raw]. zcases s 14 ltac:(vm_compute; repeat (split || reflexivity)).
Qed.
Lemma mask_bytes : forall s, 0 <= s -> s <= 14 ->
0 <= Z.shiftr (meter_mask_spec s) 7 < 128 /\ 0 <= Z.land (meter_mask_spec s) 127 < 128.
Proof. intros s H0 H1. zcases s 14 ltac:(repeat split; vm_compute; congruence). Qed.

(* ================================ meter_spec on each path ================================ *)
Lemma mt_spec_range_ch : forall d ch r s, 32 <= ch -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
intros d ch r s H. cbv beta iota zeta delta [meter_spec].
replace (0x20 <=? ch) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma mt_spec_range_seg : forall d ch r s, 14 < s -> meter_spec (Some d) ch r s = (E_RANGE, None).
Proof.
intros d ch r s H. cbv beta iota zeta delta [meter_spec].
replace (14 <? s) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity.
Qed.
Lemma mt_spec_dev_hi : forall d ch r s, ch < 32 -> s <= 14 -> 128 <= d_dev d ->
meter_spec (Some d) ch r s = (E_ARG, None).
Proof.
intros d ch r s H1 H2 H3. cbv beta iota zeta delta [meter_spec].
replace (0x20 <=? ch) with false by (symmetry; apply Z.leb_gt; lia).
replace (14 <? s) with false by (symmetry; apply Z.ltb_ge; lia).
cbv beta iota zeta delta [orb sysex_spec].
replace (0x7f <? d_dev d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.


(* ================================ shadow bytes and kept memory ================================ *)
(* the shadow byte of an address below 2 ^ 47, and its 8-byte shadow granule, lie in [SHADOW_OFF, kHighMemBeg) *)
Lemma mt_shadow_band : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= SHADOW_OFF + x / 8 < kHighMemBeg.
Proof.
intros x Hx. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma mt_hull_band : forall x, 0 <= x < 2 ^ 47 ->
SHADOW_OFF <= shadow_addr x / 8 * 8 /\ shadow_addr x / 8 * 8 + 8 <= kHighMemBeg.
Proof.
intros x Hx. pose proof (mt_shadow_band x Hx) as [H1 H2]. unfold shadow_addr.
remember (SHADOW_OFF + x / 8) as y eqn:Hy. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
(* no shadow byte is in the walk's zone: the zone is the stack window and out, both off the shadow band *)
Lemma mt_shadow_not_zone : forall sp out y, SHADOW_OFF <= y < kHighMemBeg -> 2 ^ 46 <= sp - T_meter ->
amem_range out 32 -> ~ mt_zone sp out y.
Proof. intros sp out y Hy Hs Ho. unfold mt_zone, amem_range, kHighMemBeg, kHighMemEnd, kLowMemEnd, SHADOW_OFF, T_meter, ESTACK in *. lia. Qed.
Lemma mt_ra_kept : forall (W : world tfibsegs) (m m' : word -> option byte) q n,
range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF q n ->
(forall x, q <= x < q + n -> aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) =
  aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF q n.
Proof. intros W m m' q n H Hk x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. rewrite Hk by exact Hx. auto. Qed.
Lemma mt_hull_kept : forall (W : world tfibsegs) (m m' : word -> option byte) x n,
shadow_hull_vis (aview tfibsegs (w_H W) m) x n ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  aview tfibsegs (w_H W) m' s = aview tfibsegs (w_H W) m s) ->
shadow_hull_vis (aview tfibsegs (w_H W) m') x n.
Proof. intros W m m' x n H Hk s Hs. rewrite Hk by exact Hs. exact (H s Hs). Qed.
Lemma mt_hull_sub : forall rd x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
Qed.
(* a byte of a chunk *)
Lemma mt_chunk_byte : forall E m b off (w : N) e i, YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal w e)) ->
0 <= i < Z.of_N w -> mbyte tfibsegs m (b + off + i) = Some (Z_to_bv 8 (Z.shiftr (U E e) (8 * i))).
Proof.
intros E m b off w e i H Hi. destruct (H i Hi) as (x & Hc & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hc, Hm.
injection Hc as <-. rewrite Hm. reflexivity.
Qed.

Lemma mt_U_agree : forall k E E' e, env_agree k E E' -> sv_atoms_lt k e = true -> U E' e = U E e.
Proof. intros k E E' e H1 H2. unfold U. rewrite (YP06.sv_denot_agree k E E' e H1 H2). reflexivity. Qed.

(* ================================ the bytes of out at the return ================================ *)
Lemma mt_testbit7_small : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
intros x Hx. pose proof (mt_forall_range (fun y => negb (Z.testbit y 7)) 128 ltac:(vm_compute; reflexivity) x Hx) as K.
apply negb_true_iff in K. exact K.
Qed.
Lemma mt_spec_ok : forall d c r s, 0 <= c < 32 -> 0 <= s <= 14 -> 0 <= d_dev d < 128 ->
meter_spec (Some d) c r s =
(0, Some ([0xf0; 0x13; d_dev d; 0x10; mch c r; Z.shiftr (meter_mask_spec s) 7; Z.land (meter_mask_spec s) 0x7f; 0xf7],
  KEY 4 (mch c r), 0)).
Proof.
intros d c r s H1 H2 H3.
pose proof (mch_range c r ltac:(lia)) as HM. pose proof (mask_bytes s ltac:(lia) ltac:(lia)) as [HA HB].
cbv beta iota zeta delta [meter_spec].
replace (0x20 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
replace (14 <? s) with false by (symmetry; apply Z.ltb_ge; lia).
change (Z.lor c (bit_or_0 (negb (r =? 0)) 0x20)) with (mch c r).
unfold u8. rewrite (Z.mod_small (mch c r) 256) by lia.
rewrite (Z.mod_small (Z.shiftr (meter_mask_spec s) 7) 256) by lia.
rewrite (Z.mod_small (Z.land (meter_mask_spec s) 0x7f) 256) by lia.
unfold sysex_spec. replace (0x7f <? d_dev d) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [existsb].
rewrite (mt_testbit7_small (mch c r)), (mt_testbit7_small (Z.shiftr (meter_mask_spec s) 7)),
  (mt_testbit7_small (Z.land (meter_mask_spec s) 0x7f)) by lia.
reflexivity.
Qed.
(* a byte array from its bytes *)
Lemma mt_garr8_of_bytes : forall m a l,
(forall j, (j < length l)%nat -> mbyte tfibsegs m (a + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)) /\ 0 <= nth j l 0 < 256) ->
garr8 tfibsegs m a l.
Proof.
intros m a l H j Hj. destruct (H j Hj) as [Hb Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.
(* the byte `sb` stores of a `lb`-loaded byte v *)
Lemma mt_sx8_byte : forall v, 0 <= v < 256 -> Z_to_bv 8 (zcanon (bv_swrap 8 (v mod 2 ^ Z.of_N 8))) = Z_to_bv 8 v.
Proof.
intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (mt_forall_range (fun v => bv_wrap 8 (zcanon (bv_swrap 8 (v mod 2 ^ Z.of_N 8))) =? bv_wrap 8 v) 256
  ltac:(vm_compute; reflexivity) v Hv) as K.
apply Z.eqb_eq in K. exact K.
Qed.
Lemma mt_chunk_byte0 : forall E m b off (w : N) e, YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal w e)) ->
0 < Z.of_N w -> mbyte tfibsegs m (b + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E m b off w e H Hw. pose proof (mt_chunk_byte E m b off w e 0 H ltac:(lia)) as K.
rewrite Z.add_0_r in K. change (8 * 0) with 0 in K. rewrite Z.shiftr_0_r in K. exact K.
Qed.
Lemma mt_mbyte_aview2 : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a1 a2,
aview tfibsegs H2 m2 a2 = aview tfibsegs H1 m1 a1 -> mbyte tfibsegs (mrestrict H2 m2) a2 = mbyte tfibsegs (mrestrict H1 m1) a1.
Proof.
intros H1 H2 m1 m2 a1 a2 Hv. unfold aview in Hv.
destruct (mbyte tfibsegs (mrestrict H2 m2) a2) as [b2|], (mbyte tfibsegs (mrestrict H1 m1) a1) as [b1|];
cbn in Hv; try discriminate; [|reflexivity]. injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
(* the four bytes `sw` stores of the key ch | 0x40000 *)
Lemma mt_key_bytes : forall v i, 0 <= v < 64 -> 0 <= i < 4 ->
Z_to_bv 8 (Z.shiftr (zcanon (zalu_raw 63 64 ALU_OR v (zcanon 262144))) (8 * i)) = Z_to_bv 8 (nth (Z.to_nat i) (le4Z (KEY 4 v)) 0).
Proof.
intros v i Hv Hi. apply bv_eq. rewrite !Z_to_bv_unsigned. destruct Hi as [Hi0 Hi1]. destruct Hv as [Hv0 Hv1].
zcases i 3 ltac:(idtac; zcases v 63 ltac:(vm_compute; reflexivity)).
Qed.
Lemma mt_key_range : forall v i, 0 <= v < 64 -> 0 <= nth i (le4Z (KEY 4 v)) 0 < 256.
Proof.
intros v i Hv. unfold le4Z. destruct i as [|[|[|[|i]]]]; cbn [nth];
first [ apply Z.mod_pos_bound; lia | destruct i; cbn; lia ].
Qed.

Lemma meter_some : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs
  (d : desk) p channel right segments out before,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter ->
getr regs 10 = w64 p -> pers_argA tfibsegs B W memc (spZ regs) T_meter p (Some d) ->
arg_u32A (getr regs 11) channel -> arg_s32A (getr regs 12) right -> arg_u32A (getr regs 13) segments ->
getr regs 14 = w64 out ->
cenc_out tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_meter out before ->
cpers_disj (Some d) p out 32 ->
SRr tfibsegs W (cfg_at tfibsegs A_METER regs memc mdc)
(cdc_post tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T_meter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res tfibsegs out before (meter_spec (Some d) channel right segments))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs d p channel right segments out before
  HE H10 HP H11 H12 H13 H14 HOUT HDJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ0 as HJ. pose proof HJ as (HAR & _).
assert (HT : T_meter = 4144) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
destruct HP as (Hp0 & Hp20 & Hdev & Hstr & Hchr & Hcnt & HPB & HPR).
pose proof HOUT as (HCD & Hbefore & Hlen).
pose proof HCD as (Hout0 & Houtn & Htdst & Htwr & Hra_o & Hhull_o & Hamr_o & Hcw_o).
pose proof HPR as (_ & _ & _ & Hamr_p & Hcw_p & Himg_p & Husable_p).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold coff_win in Hcw_o, Hcw_p.
destruct H11 as (Hch & H11). destruct H12 as (Hrt & H12). destruct H13 as (Hsg & H13).
assert (Hpb : p <= 2 ^ 47 - 21) by (unfold amem_range in Hamr_p; rewrite C3, C4, C5 in Hamr_p; lia).
assert (Hob : out <= 2 ^ 47 - 33) by (unfold amem_range in Hamr_o; rewrite C3, C4, C5 in Hamr_o; lia).
cbn [cpers_disj] in HDJ.
pose proof (HPB 0%nat ltac:(cbn; lia)) as (HV16 & _). cbn [nth Z.of_nat] in HV16. rewrite Z.add_0_r in HV16.
pose proof (cw_entry_base_af B TL LAWS A_METER 48 [d_dev d] mt_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs T_meter HE ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(unfold mt_AF; cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite (cw_ew_reg regs [d_dev d] 10 10%bv eq_refl), (cw_ew_reg regs [d_dev d] 14 14%bv eq_refl), H10, H14;
    unfold w64; rewrite !unsigned_lit_small by lia; rewrite Z.pow_0_r, !Z.mod_1_r; repeat split; lia)) as HS.
remember (Ereg regs (cw_extra [d_dev d])) as E eqn:HEq.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (s32 channel)) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 right) by (subst E; rewrite (cw_ew_reg regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 (s32 segments)) by (subst E; rewrite (cw_ew_reg regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E3g : ew E 3 = getr regs 3) by (subst E; exact (cw_ew_reg regs _ 3 3%bv eq_refl)).
assert (E4g : ew E 4 = getr regs 4) by (subst E; exact (cw_ew_reg regs _ 4 4%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (subst E; exact (cw_ew_x regs [d_dev d] 0)).
assert (HAE : env_agree 32 (Ereg regs (cw_extra [d_dev d])) E) by (subst E; apply env_agree_refl).
clear HEq.
assert (B14 : bv_unsigned (ew E 14) = out) by (rewrite E14; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs CW_Bx mt_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, mt_SH. constructor; [|constructor; [|constructor]].
  - exact (cw_shent_ra_off W memc E 10 p 16 4 (proj1 (Husable_p lyc Sc W memc mdc HAR)) Hamr_p ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) E10 E32).
  - exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_meter E 14 out 32 HCD E14 E32 ltac:(lia)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_meter <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_METER) with (Z_to_bv 64 A_METER).
(* 0x85600-0x85630: frame, saves, the NULL tests (decided by the facts of p and out), `bltu 31, channel` *)
cw_run mt_awr. cw_keep cw_kwr_stk. cw_branch Hb1.
- (* channel > 31: a0 = -11 = E_RANGE, out unchanged *)
  rewrite (mt_br_ltu_u32 E 11 channel 31 E11 Hch ltac:(lia)) in Hb1. apply Z.ltb_lt in Hb1.
  cw_run mt_awr. cw_keep cw_kwr_stk.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W
      memc mdc out 32 a HAR Htdst Ha Himg)) ltac:(intros a Ha; left; exact Ha))
    ltac:(unfold cenc_res; rewrite (mt_spec_range_ch d channel right segments ltac:(lia)); cbn [fst snd cmd_outZ]; split;
      [ rewrite R10; apply bv_eq; vm_compute; reflexivity
      | apply (garr8_of_kept W memc _ out before Hbefore); rewrite Hlen; change (Z.of_nat 32) with 32;
        intros a Ha; apply KE; lia ]).
- rewrite (mt_br_ltu_u32 E 11 channel 31 E11 Hch ltac:(lia)) in Hb1. apply Z.ltb_ge in Hb1.
  cw_run mt_awr. cw_keep cw_kwr_stk. cw_branch Hb2.
  + (* segments > 14: a0 = -11 = E_RANGE, out unchanged *)
    rewrite (mt_br_ltu_u32 E 13 segments 14 E13 Hsg ltac:(lia)) in Hb2. apply Z.ltb_lt in Hb2.
    cw_run mt_awr. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W
        memc mdc out 32 a HAR Htdst Ha Himg)) ltac:(intros a Ha; left; exact Ha))
      ltac:(unfold cenc_res; rewrite (mt_spec_range_seg d channel right segments ltac:(lia)); cbn [fst snd cmd_outZ]; split;
        [ rewrite R10; apply bv_eq; vm_compute; reflexivity
        | apply (garr8_of_kept W memc _ out before Hbefore); rewrite Hlen; change (Z.of_nat 32) with 32;
          intros a Ha; apply KE; lia ]).
  + rewrite (mt_br_ltu_u32 E 13 segments 14 E13 Hsg ltac:(lia)) in Hb2. apply Z.ltb_ge in Hb2.
    rewrite (mt_s32_small channel) in E11 by lia. rewrite (mt_s32_small segments) in E13 by lia.
    (* 0x8563c-0x85670: s1 = the payload's first byte, the shadow offset in s2, the payload in the frame *)
    cw_run_to mt_awr 0x85674. cw_keep cw_kwr_stk.
    (* 0x85674: drop the two shadow-offset cells, add p->device *)
    cw_drop_gb.
    mt_add HS mt_p16 ltac:(idtac; mt_rok_p) ltac:(idtac; mt_dis).
    (* 0x85674-0x8568c: the checked load of p->device (shadow entry of p + 16), `bltz` on it *)
    cw_run mt_awr. cw_keep cw_kwr_stk. cw_branch Hb3.
    * (* bit 7 of the device byte set: a0 = -1 = E_ARG, out unchanged *)
      mt_toE Hb3. rewrite mt_br_sx8e, (U_atom E 33 (d_dev d) E33), Z.mod_small in Hb3 by lia. apply Z.leb_le in Hb3.
      cw_run mt_awr. cw_keep cw_kwr_stk.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W
          memc mdc out 32 a HAR Htdst Ha Himg)) ltac:(intros a Ha; left; exact Ha))
        ltac:(unfold cenc_res; rewrite (mt_spec_dev_hi d channel right segments ltac:(lia) ltac:(lia) Hb3);
          cbn [fst snd cmd_outZ]; split;
          [ rewrite R10; apply bv_eq; vm_compute; reflexivity
          | apply (garr8_of_kept W memc _ out before Hbefore); rewrite Hlen; change (Z.of_nat 32) with 32;
            intros a Ha; apply KE; lia ]).
    * mt_toE Hb3. rewrite mt_br_sx8e, (U_atom E 33 (d_dev d) E33), Z.mod_small in Hb3 by lia. apply Z.leb_gt in Hb3.
      pose proof (mch_range channel right ltac:(lia)) as Hmch.
      pose proof (mt_U_ch E channel right E11 E12 ltac:(lia) ltac:(lia) ltac:(lia)) as Uch.
      pose proof (mt_U_mask E segments E13 ltac:(lia) ltac:(lia)) as (Um & Um7 & Um127). unfold sv_mask in Um, Um7, Um127.
      pose proof (mask_bytes segments ltac:(lia) ltac:(lia)) as (Hm7 & Hm127).
      (* 0x85690-0x856a8: the payload loop reads the three frame bytes back; bit 7 is clear in each *)
      cw_run mt_awr. cw_keep cw_kwr_stk. cw_branch Hb4.
      -- exfalso. mt_toE Hb4. rewrite mt_br_sx8e, Uch, Z.mod_small in Hb4 by lia. apply Z.leb_le in Hb4. lia.
      -- clear Hb4.
         (* the stores to out begin: add its four pieces; the kept zone now holds them *)
         lazymatch type of KE with forall a, _ -> ~ _ -> aview tfibsegs ?Hh ?mm a = aview tfibsegs ?Hh memc a =>
           assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ mt_zone (spZ regs) out a ->
             aview tfibsegs Hh mm a = aview tfibsegs Hh memc a)
             by (intros a Ha Hz; apply KE; [exact Ha | intros Hs; apply Hz; left; exact Hs]) end.
         clear KE. rename KE' into KE.
         mt_add HS mt_o28 ltac:(idtac; mt_rok_o) ltac:(idtac; mt_dis).
         mt_add HS mt_o24 ltac:(idtac; mt_rok_o) ltac:(idtac; mt_dis).
         mt_add HS mt_o7 ltac:(idtac; mt_rok_o) ltac:(idtac; mt_dis).
         mt_add HS mt_o0 ltac:(idtac; mt_rok_o) ltac:(idtac; mt_dis).
         cw_run mt_awr. cw_keep mt_kwr. cw_branch Hb5.
         ++ exfalso. mt_toE Hb5. rewrite mt_br_sx8e, Um7, Z.mod_small in Hb5 by lia. apply Z.leb_le in Hb5. lia.
         ++ clear Hb5. cw_run mt_awr. cw_keep mt_kwr.
            (* 0x85720 jal __asan_memcpy(out + 4, sp + 13, 3) *)
            norm_ss HS.
            lazymatch type of HS with YP0l.st_ok _ ?Ec _ (restrict (w_H W) ?msv) =>
              rename msv into msT; remember Ec as E3 eqn:HE3 end.
            assert (HAg3 : env_agree 34 E E3) by (rewrite HE3; env_agree_chain (YP06.env_agree_refl 34 E)).
            lazymatch type of HS with YP0l.st_ok _ _ ?ssv _ =>
              pose proof (st_ok_region_nth E3 ssv (restrict (w_H W) msT) 5 _ HS eq_refl) as HRst;
              pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 ssv msT HS eq_refl) as Hms end.
            rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
            rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
            pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT & _).
            (* the three payload bytes in the frame: the save area's chunks at -35, -34, -33 *)
            unfold region_ok in HRst.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HRst.
            destruct HRst as (_ & _ & _ & HCs).
            apply Forall_cons_iff in HCs. destruct HCs as [HC33 HCs].
            apply Forall_cons_iff in HCs. destruct HCs as [HC34 HCs].
            apply Forall_cons_iff in HCs. destruct HCs as [HC35 _].
            assert (B2T : bv_unsigned (ew E3 2) = spZ regs) by (rewrite HE3, !ew_ewset_other by lia; exact B2).
            pose proof (mt_chunk_byte E3 _ _ (-35) 1 _ 0 HC35 ltac:(cbn; lia)) as P0.
            pose proof (mt_chunk_byte E3 _ _ (-34) 1 _ 0 HC34 ltac:(cbn; lia)) as P1.
            pose proof (mt_chunk_byte E3 _ _ (-33) 1 _ 0 HC33 ltac:(cbn; lia)) as P2.
            rewrite B2T in P0, P1, P2. change (8 * 0) with 0 in P0, P1, P2. rewrite !Z.shiftr_0_r in P0, P1, P2.
            rewrite (mt_U_agree 34 E E3 _ HAg3) in P0 by reflexivity. rewrite Uch in P0.
            rewrite (mt_U_agree 34 E E3 _ HAg3) in P1 by reflexivity. rewrite Um7 in P1.
            rewrite (mt_U_agree 34 E E3 _ HAg3) in P2 by reflexivity. rewrite Um127 in P2.
            assert (HspT : spZ (ms_regs msT) = spZ regs - 48).
            { unfold spZ at 1. rewrite Rsp. cbn [sv_denot]. rewrite B2T, unsigned_lit_small by lia. lia. }
            pose proof (cw_stack_src B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msT) _ k (spZ regs - 35) 3 LAWS HJ
              ltac:(lia) ltac:(lia) ltac:(lia)) as (Samr & Sra & Shull & Svis).
            lazymatch type of HS with YP0l.st_ok _ _ ?ssv _ =>
              let rs := eval vm_compute in (ss_mem ssv) in
              apply (cw_intrin_call B LAWS OCpy 0x51998 AMEMCPY W E3 ssv msT _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
                (out + 4) (spZ regs - 35) 3 546596 40 rs) end.
            { exact HS. }
            { reflexivity. }
            { reflexivity. }
            { exact HJ. }
            { rewrite Ra0. cbn [sv_denot]. rewrite HE3, !ew_ewset_other by lia. rewrite B14. reflexivity. }
            { rewrite Ra1. cbn [sv_denot]. rewrite B2T. unfold w64. f_equal; try lia. }
            { rewrite Ra2. reflexivity. }
            { lia. }
            { lia. }
            { lia. }
            { rewrite HspT. lia. }
            { rewrite HspT. lia. }
            { rewrite HspT. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
            { exact Hsp0al. }
            { rewrite Rgp, HE3, !ew_ewset_other by lia. rewrite E3g. exact Hgp. }
            { rewrite Rtp, HE3, !ew_ewset_other by lia. rewrite E4g. exact Htp. }
            { reflexivity. }
            { lia. }
            { unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
            { intros a Ha. split; [exact (proj1 (Htwr a ltac:(lia))) | rewrite HspT; lia]. }
            { unfold amem_range in *. rewrite C3, C4, C5 in *. lia. }
            { apply (range_addressable_sub _ _ out 32 (out + 4) 3); [|lia|lia].
              apply (mt_ra_kept W memc _ out 32 Hra_o). intros x Hx. unfold shadow_of_addr.
              pose proof (mt_shadow_band x ltac:(lia)) as Hb. apply KE.
              - unfold SHADOW_OFF, kHighMemBeg in *. lia.
              - apply mt_shadow_not_zone; [exact Hb | lia | exact Hamr_o]. }
            { intros _. apply (mt_hull_sub _ out 32 (out + 4) 3); [|lia|lia].
              apply (mt_hull_kept W memc _ out 32 (Hhull_o ltac:(lia))). intros s0 Hs0.
              pose proof (mt_hull_band out ltac:(lia)) as Hhb1. pose proof (mt_hull_band (out + 32 - 1) ltac:(lia)) as Hhb2.
              apply KE.
              - unfold SHADOW_OFF, kHighMemBeg in *. lia.
              - apply mt_shadow_not_zone; [lia | lia | exact Hamr_o]. }
            { split; [lia|]. split; [lia|].
              split; [intros a Ha; split; [apply Svis; lia | rewrite HspT; lia]|].
              split; [lia|]. split; [exact Samr|]. split; [exact Sra | intros _; exact Shull]. }
            { vm_compute. reflexivity. }
            { vm_compute. reflexivity. }
            { vm_compute. reflexivity. }
            { vm_compute. reflexivity. }
            { apply submem_refl. }
            { rewrite HspT. unfold mt_o0, mt_o7, mt_o24, mt_o28, mt_p16.
              repeat apply Forall_cons; try apply Forall_nil;
              (split; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite HE3, ?ew_ewset_other in Ha by lia;
                        repeat match goal with Bq : bv_unsigned (ew E _) = _ |- _ => rewrite Bq in Ha end; split; lia
                      | cbn; lia ]). }
            intros regs2 mem2 md2 HJ2 HP2 Ha02 Heff Hfr2 Hpres2 HSM2 HS2.
            (* 0x85724: the state after the call; out + 4 .. out + 6 hold the payload *)
            subst E3. clear HS B2T. rename HS2 into HS. norm_ss HS.
            assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ mt_zone (spZ regs) out a ->
              aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
            { intros a Ha Hz. rewrite (Hfr2 a Ha) by (rewrite ?HspT; intros ?; apply Hz; unfold mt_zone; lia).
              apply KE; [exact Ha | exact Hz]. }
            clear KE. rename KE2 into KE.
            lazymatch type of HS with YP0l.st_ok _ ?E4 _ _ =>
              assert (E4_10 : ew E4 10 = Z_to_bv 64 p) by (rewrite ew_havoc_old, !ew_ewset_other by lia; exact E10);
              assert (E4_14 : ew E4 14 = Z_to_bv 64 out) by (rewrite ew_havoc_old, !ew_ewset_other by lia; exact E14);
              assert (E4_32 : ew E4 32 = Z_to_bv 64 SB) by (rewrite ew_havoc_old, !ew_ewset_other by lia; exact E32);
              assert (SHOK2 : sh_ok tfibsegs CW_Bx mt_SH E4 (mrestrict (w_H W) mem2)) end.
            { unfold sh_ok, mt_SH. constructor; [|constructor; [|constructor]].
              - exact (cw_shent_ra_off W mem2 _ 10 p 16 4 (proj1 (Husable_p lyc Sc W mem2 md2 (proj1 HJ2))) Hamr_p
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E4_10 E4_32).
              - apply (cw_shent_ra W mem2 _ 14 out 32); [| exact Hamr_o | lia | lia | lia | exact E4_14 | exact E4_32].
                apply (mt_ra_kept W memc mem2 out 32 Hra_o). intros x Hx. unfold shadow_of_addr.
                pose proof (mt_shadow_band x ltac:(lia)) as Hb. apply KE.
                + unfold SHADOW_OFF, kHighMemBeg in *. lia.
                + apply mt_shadow_not_zone; [exact Hb | lia | exact Hamr_o]. }
            (* 0x85724-0x857b4: out[7], len, display, key (4-byte check), a0 = 0, restore, ret *)
            cw_run mt_awr.
            lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
              pose proof (cw_kept_run (fun a => (spZ regs - T_meter <= a < spZ regs) \/ (out <= a < out + 4) \/
                  (out + 7 <= a < out + 8) \/ (out + 24 <= a < out + 26) \/ (out + 28 <= a < out + 32))
                  _ _ _ m1 m1 m2 (fun _ _ _ => eq_refl) HFr) as K4 end.
            lazymatch type of K4 with ?P -> _ => let KW := fresh "KW" in assert (KW : P) by mt_kwr; specialize (K4 KW) end.
            lazymatch type of K4 with forall a, _ -> _ -> aview _ _ ?m2 a = aview _ _ ?m1 a =>
              assert (K4b : forall i, 0 <= i < 3 -> aview tfibsegs (w_H W) m2 (out + 4 + i) = aview tfibsegs (w_H W) m1 (out + 4 + i))
              by (intros i Hi; apply K4; [lia | cbv beta; lia]) end.
            clear K4.
            cw_keep mt_kwr.
            (* 0x857b4 ret: the bytes of out *)
            norm_ss HS.
            lazymatch type of HS with YP0l.st_ok _ ?Ef ?ssf (restrict (w_H W) ?msf) =>
              rename msf into msF;
              pose proof (st_ok_region_nth Ef ssf _ 0 _ HS eq_refl) as RO0;
              pose proof (st_ok_region_nth Ef ssf _ 1 _ HS eq_refl) as RO7;
              pose proof (st_ok_region_nth Ef ssf _ 2 _ HS eq_refl) as RO24;
              pose proof (st_ok_region_nth Ef ssf _ 3 _ HS eq_refl) as RO28;
              assert (BF14 : bv_unsigned (ew Ef 14) = out)
                by (rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia; exact B14);
              assert (EF33 : ew Ef 33 = Z_to_bv 64 (d_dev d))
                by (rewrite ?ew_havoc_old, ?ew_ewset_other, ?ew_havoc_old, ?ew_ewset_other by lia; exact E33);
              assert (HAgF : env_agree 34 E Ef) by (env_agree_chain (YP06.env_agree_refl 34 E)) end.
            unfold region_ok in RO0, RO7, RO24, RO28.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in RO0, RO7, RO24, RO28.
            rewrite BF14 in RO0, RO7, RO24, RO28.
            destruct RO0 as (_ & _ & _ & CK0). apply Forall_cons_iff in CK0. destruct CK0 as [CK3 CK0].
            apply Forall_cons_iff in CK0. destruct CK0 as [CK2 CK0]. apply Forall_cons_iff in CK0. destruct CK0 as [CK1 CK0].
            apply Forall_cons_iff in CK0. destruct CK0 as [CK00 _].
            destruct RO7 as (_ & _ & _ & CK7). apply Forall_cons_iff in CK7. destruct CK7 as [CK7 _].
            destruct RO24 as (_ & _ & _ & CK24). apply Forall_cons_iff in CK24. destruct CK24 as [CK25 CK24].
            apply Forall_cons_iff in CK24. destruct CK24 as [CK24 _].
            destruct RO28 as (_ & _ & _ & CK28). apply Forall_cons_iff in CK28. destruct CK28 as [CK28 _].
            (* the payload bytes: copied from the frame (Heff), kept by the last run (K4b) *)
            assert (F4 : mbyte tfibsegs (mrestrict (w_H W) (ms_mem msF)) (out + 4) = Some (Z_to_bv 8 (mch channel right))).
            { pose proof (K4b 0 ltac:(lia)) as K. pose proof (Heff 0 ltac:(lia)) as K'.
              replace (out + 4 + 0) with (out + 4) in K, K' by lia. replace (spZ regs - 35 + 0) with (spZ regs + -35 + 0) in K' by lia.
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) mem2 (ms_mem msF) (out + 4) (out + 4) K).
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) (ms_mem msT) mem2 (spZ regs + -35 + 0) (out + 4) K'). exact P0. }
            assert (F5 : mbyte tfibsegs (mrestrict (w_H W) (ms_mem msF)) (out + 5) = Some (Z_to_bv 8 (Z.shiftr (meter_mask_spec segments) 7))).
            { pose proof (K4b 1 ltac:(lia)) as K. pose proof (Heff 1 ltac:(lia)) as K'.
              replace (out + 4 + 1) with (out + 5) in K, K' by lia. replace (spZ regs - 35 + 1) with (spZ regs + -34 + 0) in K' by lia.
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) mem2 (ms_mem msF) (out + 5) (out + 5) K).
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) (ms_mem msT) mem2 (spZ regs + -34 + 0) (out + 5) K'). exact P1. }
            assert (F6 : mbyte tfibsegs (mrestrict (w_H W) (ms_mem msF)) (out + 6) = Some (Z_to_bv 8 (Z.land (meter_mask_spec segments) 127))).
            { pose proof (K4b 2 ltac:(lia)) as K. pose proof (Heff 2 ltac:(lia)) as K'.
              replace (out + 4 + 2) with (out + 6) in K, K' by lia. replace (spZ regs - 35 + 2) with (spZ regs + -33 + 0) in K' by lia.
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) mem2 (ms_mem msF) (out + 6) (out + 6) K).
              rewrite (mt_mbyte_aview2 (w_H W) (w_H W) (ms_mem msT) mem2 (spZ regs + -33 + 0) (out + 6) K'). exact P2. }
            (* the bytes no store writes: kept since the entry (KE), the bytes of before *)
            assert (FK : forall j, 0 <= j < 32 -> ~ mt_zone (spZ regs) out (out + j) ->
              mbyte tfibsegs (mrestrict (w_H W) (ms_mem msF)) (out + j) = Some (Z_to_bv 8 (nth (Z.to_nat j) before 0)) /\
              0 <= nth (Z.to_nat j) before 0 < 256).
            { intros j Hj Hz. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) memc (ms_mem msF) (out + j) (KE (out + j) ltac:(lia) Hz)).
              replace (out + j) with (out + Z.of_nat (Z.to_nat j)) by lia.
              split; [apply garr8_mbyte; [exact Hbefore | rewrite Hlen; lia] | apply (Hbefore (Z.to_nat j)); rewrite Hlen; lia]. }
            (* the key ch | 0x40000 *)
            lazymatch type of HS with YP0l.st_ok _ ?Ef _ _ =>
              assert (UK : U Ef (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) (SOff 11 0))
                (SLit 262144)) = zcanon (zalu_raw 63 64 ALU_OR (mch channel right) (zcanon 262144))) end.
            { rewrite U_SAlu, U_SLit. rewrite (mt_U_agree 34 E _ _ HAgF) by reflexivity. rewrite Uch. reflexivity. }
            cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W
                memc mdc out 32 a HAR Htdst Ha Himg)) ltac:(intros a Ha; cbv beta in Ha; unfold mt_zone in Ha; unfold cenc_wr; lia))
              ltac:(idtac).
            unfold cenc_res. rewrite (mt_spec_ok d channel right segments ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd].
            split; [rewrite R10; apply bv_eq; vm_compute; reflexivity|].
            do 32 (destruct before as [|?x before]; [discriminate Hlen|]). destruct before; [|discriminate Hlen].
            cbn [cmd_outZ map length firstn skipn app]. unfold u8. change (Z.of_nat 8) with 8.
            rewrite (Z.mod_small (d_dev d) 256), (Z.mod_small (mch channel right) 256),
              (Z.mod_small (Z.shiftr (meter_mask_spec segments) 7) 256), (Z.mod_small (Z.land (meter_mask_spec segments) 127) 256) by lia.
            apply mt_garr8_of_bytes. intros j Hj. cbn [length] in Hj.
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 0) with (out + 0) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 0 _ _ CK00 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 1) with (out + 1) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 1 _ _ CK1 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 2) with (out + 2) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 2 _ _ CK2 ltac:(cbn; lia)), U_SExt, (U_atom _ 33 (d_dev d) EF33) by lia; cbv iota beta;
              rewrite (mt_sx8_byte (d_dev d)) by lia; split; [reflexivity | lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 3) with (out + 3) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 3 _ _ CK3 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 4) with (out + 4) by lia;
              split; [exact F4 | first [apply mch_range; lia | lia]] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 5) with (out + 5) by lia;
              split; [exact F5 | first [apply mch_range; lia | lia]] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 6) with (out + 6) by lia;
              split; [exact F6 | first [apply mch_range; lia | lia]] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 7) with (out + 7) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 7 _ _ CK7 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 8) with (out + 8) by lia;
              exact (FK 8 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 9) with (out + 9) by lia;
              exact (FK 9 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 10) with (out + 10) by lia;
              exact (FK 10 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 11) with (out + 11) by lia;
              exact (FK 11 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 12) with (out + 12) by lia;
              exact (FK 12 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 13) with (out + 13) by lia;
              exact (FK 13 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 14) with (out + 14) by lia;
              exact (FK 14 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 15) with (out + 15) by lia;
              exact (FK 15 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 16) with (out + 16) by lia;
              exact (FK 16 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 17) with (out + 17) by lia;
              exact (FK 17 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 18) with (out + 18) by lia;
              exact (FK 18 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 19) with (out + 19) by lia;
              exact (FK 19 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 20) with (out + 20) by lia;
              exact (FK 20 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 21) with (out + 21) by lia;
              exact (FK 21 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 22) with (out + 22) by lia;
              exact (FK 22 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 23) with (out + 23) by lia;
              exact (FK 23 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 24) with (out + 24) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 24 _ _ CK24 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 25) with (out + 25) by lia;
              rewrite (mt_chunk_byte0 _ _ _ 25 _ _ CK25 ltac:(cbn; lia)); split; [f_equal; apply bv_eq; vm_compute; reflexivity | apply Z.mod_pos_bound; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 26) with (out + 26) by lia;
              exact (FK 26 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 27) with (out + 27) by lia;
              exact (FK 27 ltac:(lia) ltac:(unfold mt_zone; lia)) |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 28) with (out + 28) by lia;
              pose proof (mt_chunk_byte _ _ _ 28 4 _ 0 CK28 ltac:(cbn; lia)) as Hk; replace (out + 28 + 0) with (out + 28) in Hk by lia;
              rewrite Hk, UK, (mt_key_bytes (mch channel right) 0) by (try apply mch_range; lia);
              split; [reflexivity | apply mt_key_range; apply mch_range; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 29) with (out + 29) by lia;
              pose proof (mt_chunk_byte _ _ _ 28 4 _ 1 CK28 ltac:(cbn; lia)) as Hk; replace (out + 28 + 1) with (out + 29) in Hk by lia;
              rewrite Hk, UK, (mt_key_bytes (mch channel right) 1) by (try apply mch_range; lia);
              split; [reflexivity | apply mt_key_range; apply mch_range; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 30) with (out + 30) by lia;
              pose proof (mt_chunk_byte _ _ _ 28 4 _ 2 CK28 ltac:(cbn; lia)) as Hk; replace (out + 28 + 2) with (out + 30) in Hk by lia;
              rewrite Hk, UK, (mt_key_bytes (mch channel right) 2) by (try apply mch_range; lia);
              split; [reflexivity | apply mt_key_range; apply mch_range; lia] |].
            destruct j as [|j]; [cbn [nth]; replace (out + Z.of_nat 31) with (out + 31) by lia;
              pose proof (mt_chunk_byte _ _ _ 28 4 _ 3 CK28 ltac:(cbn; lia)) as Hk; replace (out + 28 + 3) with (out + 31) in Hk by lia;
              rewrite Hk, UK, (mt_key_bytes (mch channel right) 3) by (try apply mch_range; lia);
              split; [reflexivity | apply mt_key_range; apply mch_range; lia] |].
            cbn in Hj. lia.
Qed.

Theorem diginet_meter_encode_A_holds : cdc_meter_specX tfibsegs B MT A_METER.
Proof using MTL TL LAWS ML AMEMCPY.
unfold cdc_meter_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p channel right segments out before
  HE H10 HP H11 H12 H13 H14 HOUT HDJ.
destruct pd as [d|].
- exact (meter_some STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs d p channel right segments out before
    HE H10 HP H11 H12 H13 H14 HOUT HDJ).
- cbn [pers_argA] in HP. subst p.
  exact (meter_none STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs channel right segments out before HE H10 HOUT).
Qed.
End b.
