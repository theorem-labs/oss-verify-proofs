(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_disco's program walk, over fuzz_disco's listing. Image objects follow fuzz_disco.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 66 (atom 307) and the side-stack flag cell is object 67 (atom 308), so img_factsF and img_hull_factsF give E240 E241 E242 E307 E308 and Hob241 Hob242 Hob307 Hob308, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and DiscoFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACja.v, with its module paths, module names and numbers changed; 628 of its 693 lines of code are new or changed and 266 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd AmemBlock8.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tjr_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tjr_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tjr_awr_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tjr_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tjr_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tjr_awr: no rule for the head region" ];
tjr_awr_rec hd AG fpos F EFA
end.
Ltac tjr_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tjr_awr_rec hd AG fpos F EFA.
Ltac tjr_notw AG tac :=
let rg := fresh "rg" in let Hin := fresh "Hin" in
intros (rg & Hin & Hrgkb);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrgkb; revert Hrgkb; evalE AG; intros Hrgkb; tac|]);
destruct Hin.
Ltac tjr_kb HKb AG b n tac :=
lazymatch type of HKb with forall a, _ -> aview ?sg ?Hh ?m0 a = aview _ _ ?m3 a =>
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
let H := fresh "HKb" in
assert (H : forall a, b <= a < b + n -> aview sg Hh m1 a = aview sg Hh m3 a)
by (intros akb Hakb; transitivity (aview sg Hh m0 akb); [|exact (HKb akb Hakb)];
eapply aview_kept_out; [exact HFr | tac | tjr_notw AG tac]);
clear HKb; rename H into HKb end end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac tjr_kept AG Hfr Hpres2 tac :=
eapply region_kept_aview; [evalE AG | intros akb Hakb; apply Hfr; tac | exact Hpres2].
Ltac tjr_fs_rw HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma tjr_str_end_bound : forall w s, w + Z.of_nat (length s) + 1 <= str_end w s <= w + Z.of_nat (length s) + 8.
Proof.
intros w s. unfold str_end. pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.
Lemma tjr_swrap : forall u r, 0 <= u < 2 ^ 32 -> bv_swrap 32 u = r -> 0 <= r < 2 ^ 31 -> u = r.
Proof.
intros u r Hu Hs Hr. unfold bv_swrap, bv_wrap in Hs.
change (bv_half_modulus 32) with (2 ^ 31) in Hs. change (bv_modulus 32) with (2 ^ 32) in Hs.
destruct (Z_lt_ge_dec u (2 ^ 31)) as [Hl|Hl].
- rewrite Z.mod_small in Hs by lia. lia.
- replace (u + 2 ^ 31) with ((u - 2 ^ 31) + 1 * 2 ^ 32) in Hs by ring.
rewrite Z_mod_plus_full, Z.mod_small in Hs by lia. lia.
Qed.
Lemma tjr_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
- rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
- replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjr_Uadd2 : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = va + vb.
Proof.
intros E a b va vb Ha Hb H0 H1 H2. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a va Ha), (U_atom E b vb Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma tjr_Uadd3 : forall E p a b vp va vb, ew E p = Z_to_bv 64 vp -> ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
0 <= vp -> 0 <= va -> 0 <= vb -> vp + va + vb < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff p 0) (SOff a 0)) (SOff b 0)) = vp + va + vb.
Proof.
intros E p a b vp va vb Hp Ha Hb H0 H1 H2 H3. rewrite U_SAlu. cbn [zalu_raw].
rewrite (tjr_Uadd2 E p a vp va Hp Ha) by lia. rewrite (U_atom E b vb Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma tjr_Usub2 : forall E c a b vc va vb z, ew E c = Z_to_bv 64 vc -> ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
zcanon z = 2 ^ 64 - 1 -> 0 <= va -> 0 <= vb -> va + vb <= vc -> vc < 2 ^ 63 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff c 0) (SMd M_MUL (SOff a 0) (SLit z))) (SMd M_MUL (SOff b 0) (SLit z))) = vc - va - vb.
Proof.
intros E c a b vc va vb z Hc Ha Hb Hz H0 H1 H2 H3.
rewrite !U_SAlu, !U_SMd. cbn [zalu_raw zmd_raw]. rewrite !U_SLit.
rewrite (U_atom E c vc Hc), (U_atom E a va Ha), (U_atom E b vb Hb) by lia.
rewrite (tjr_sub vc va z Hz) by lia. rewrite (tjr_sub (vc - va) vb z Hz) by lia. lia.
Qed.
Lemma tjr_Uxor : forall E x vx, U E x = vx -> 1 <= vx ->
U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU x (SLit 1))) = 1.
Proof.
intros E x vx Hx H1. rewrite (U_SAlu E ALU_XOR), (U_SAlu E ALU_SLTU), Hx, !U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
destruct (Z.ltb_spec vx 1); [lia|]. reflexivity.
Qed.
Lemma tjr_U_ewset : forall E k w v, sv_atoms_lt k v = true -> U (ewset E k w) v = U E v.
Proof.
intros E k w v Hv. unfold U. f_equal. apply (sv_denot_agree k E (ewset E k w) v); [|exact Hv].
split; [intros n Hn; apply ew_ewset_other; lia | reflexivity].
Qed.
Lemma tjr_zm1 : zcanon (-1) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.
Definition tjr_obj (r : Z) : nat := if r =? 1 then 45%nat else if r =? 2 then 44%nat else 43%nat.
Definition tjr_ps : list pf_piece :=
[PLit 44; PLit 34; PLit 114; PLit 111; PLit 108; PLit 101; PLit 34; PLit 58; PLit 34; Ps; PLit 34].
Definition tjr_txt (r : Z) : list Z := [44; 34; 114; 111; 108; 101; 34; 58; 34] ++ rolename r ++ [34].
Lemma tjr_parse : pf_parse tj_f_role = Some tjr_ps.
Proof. vm_compute. reflexivity. Qed.
Lemma tjr_disco : Forall pf_disco_piece tjr_ps.
Proof. repeat constructor. Qed.
Lemma tjr_text : forall r, pf_text tjr_ps [APtr (rolename r)] = Some (tjr_txt r).
Proof. intros r. reflexivity. Qed.
Lemma tjr_P2 : forall e, P2 e = tjr_txt (e_role e).
Proof. intros e. reflexivity. Qed.
Lemma tjr_txt_len : forall r, (Z.of_nat (length (tjr_txt r)) <= 17).
Proof. intros r. unfold tjr_txt, rolename. destruct (r =? 1); [cbn; lia|]. destruct (r =? 2); cbn; lia. Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma tjr_garr8_u4 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 4 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 4 (disco_table_c.u_at T k 4).
Proof.
intros m a k T HG Hk HkT j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 4) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 4); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 4)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 4)) as H1.
assert (Hlen : length (disco_table_c.sub T k 4) = 4%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
rewrite Hlen in H1. rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma tjr_u4_range : forall (T : list byte) k, 0 <= disco_table_c.u_at T k 4 < 2 ^ 32.
Proof.
intros T k. unfold disco_table_c.u_at.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 4)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 4)) as H1.
assert (Hlen : (length (disco_table_c.sub T k 4) <= 4)%nat) by (unfold disco_table_c.sub; rewrite length_firstn; lia).
assert (2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
lia.
Qed.
Lemma tjr_str : forall r, tj_strs -> tj_ro_at (tjr_obj r) (rolename r).
Proof.
intros r H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbox & Hmaster & Hunk & _).
unfold tjr_obj, rolename. destruct (r =? 1); [exact Hbox|]. destruct (r =? 2); [exact Hmaster | exact Hunk].
Qed.
Lemma tjr_garr8_of_aview : forall H m p l,
(forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) -> garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l. revert p. induction l as [|x l IH]; intros p Hl.
- intros j Hj. cbn in Hj. lia.
- change (x :: l) with ([x] ++ l). apply (proj2 (garr8_app SEGS _ _ _ _)). split.
  + apply garr8_one_of_aview. pose proof (Hl 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
  + apply IH. intros j Hj. pose proof (Hl (S j) ltac:(cbn; lia)) as H1.
    replace (p + Z.of_nat (S j)) with (p + Z.of_nat (length [x]) + Z.of_nat j) in H1 by (cbn [length]; lia). exact H1.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Context {PRP : YXcalls.PARoPresent lib_both3_0_listing}.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis TJS : tj_strs.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tjr_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
tj_baseX B IMG cx ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
own ly' S' W' mem' md' k ->
tj_keep B cx W' mem'.
Proof.
intros cx own ly' S' W' mem' md' k HB HJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HB. unfold tj_keep.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HB, HJ |- *.
destruct HB as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof Hobj as ((cid & pos & Hin & Hcid & Hal8 & Hflo & Hfhi) & Ht8 & Hra).
assert (HnF : forall x, inFP (tj_fp buf cap) x -> (x < kLowShadowBeg \/ kHighShadowEnd <= x) /\
~ (frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)).
{ intros x Hx. unfold tj_fp in Hx. destruct (Z.ltb_spec cap 3) as [Hc|Hc]; [destruct Hx as (r & [] & _)|].
destruct (Hbuf Hc) as (Hbin & Hbsz).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md buf Nb cid pos HAR Hbin Hin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF.
destruct Hx as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. split; lia. }
split; [exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)|].
split.
- intros j Hj. destruct (Harr j Hj) as (Hv & Hr). split; [|exact Hr].
rewrite length_map, HlenT in Hj.
eapply val_mem_entry_frame; [exact HJ | exact Hin | lia | lia | | exact Hv].
intros x Hx HF. destruct (HnF x HF) as (_ & Hn). apply Hn. lia.
- split; [exists cid, pos; repeat split; assumption|]. split; [exact Ht8|].
eapply range_addressable_entry_frame; [exact LAWS | exact HJ | exact Hin | exact Hcid | exact Hflo | exact Hfhi | exact Hal8 | | exact HAR | exact Hra].
intros x HF. exact (proj1 (HnF x HF)).
Qed.
Lemma tjr_aview_rom : forall H mem x, seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H mem x <> None.
Proof.
intros H mem x Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 x)); [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate | contradiction].
Qed.
Lemma tjr_ro_bytes : forall ly S (W : world SEGS) mem md (k : nat) s,
AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> tj_ro_at k s ->
forall j, 0 <= j <= Z.of_nat (length s) -> aview SEGS (w_H W) mem (VAL (A_OBJ k) + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0).
Proof.
intros ly S W mem md k s HAR HROD (Hg & Hro & Hlo & Hhi & Hch & Hby) j Hj.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + j) HROD
(Hro (VAL (A_OBJ k) + j) ltac:(lia)) (tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hby (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hq. rewrite Z2Nat.id in Hq by lia. exact Hq.
Qed.
Lemma tjr_fmt_at : forall ly S (W : world SEGS) mem md (k : nat) s rs,
AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> tj_ro_at k s ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros ly S W mem md k s rs HAR HROD HT Hd.
pose proof (tjr_ro_bytes ly S W mem md k s HAR HROD HT) as Hb.
destruct HT as (Hg & Hro & Hlo & Hhi & Hch & Hby). unfold IMG_LO, IMG_TOP in Hlo, Hhi.
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ k)) _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) GM Hg HV HAR
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_LO; lia) ltac:(unfold IMG_TOP; lia)) as [Hra Hhu].
unfold fmt_at. split; [lia|]. split; [exact Hb|]. split; [exact Hd|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
split; assumption.
Qed.
Lemma tjr_str_arg : forall ly S (W : world SEGS) mem md (k : nat) s rs,
AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> tj_ro_at k s ->
Forall (zdisjoint (VAL (A_OBJ k), str_end (VAL (A_OBJ k)) s - VAL (A_OBJ k))) rs ->
pf_arg_asan (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) (APtr s).
Proof.
intros ly S W mem md k s rs HAR HROD HT Hd.
pose proof (tjr_ro_bytes ly S W mem md k s HAR HROD HT) as Hb.
pose proof HT as HT0.
destruct HT as (Hg & Hro & Hlo & Hhi & Hch & Hby). unfold IMG_LO, IMG_TOP in Hlo, Hhi.
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ k)) _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) GM Hg HV HAR
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_LO; lia) ltac:(unfold IMG_TOP; lia)) as [Hra Hhu].
unfold pf_arg_asan. split; [exact Hch|]. split; [lia|]. split; [lia|]. split; [exact Hb|].
split; [intros x Hx; apply tjr_aview_rom; exact (tj_pad_ro k s HT0 x Hx)|].
split; [exact Hd|]. split; [unfold amem_range, kLowMemEnd; left; lia|]. split; assumption.
Qed.
Theorem pb_tj_seg_role : tj_seg_role B IMG.
Proof.
unfold tj_seg_role. intros i FX FR.
unfold tj_fromM, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
unfold INV_tjM, tj_lbody, tj_split, tj_wrote, tj_keep, tj_after1, tj_e, tj_age in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros nn Hnn; apply AG34; lia).
destruct HINV as (Hk0 & (Hperm & (HRODk & Harrk & HobjT) & Hcap3 & Hi & E721 & E722 & E740 & E741) & acc &
(o1 & o2 & E733 & E764 & Ho1 & Ho2 & Ho12) & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 4736 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; lia).
assert (HSTKv : REAC_DISCO_TABLE_JSON_STK = 12416) by (unfold REAC_DISCO_TABLE_JSON_STK; lia).
rewrite HSTKv in Hslo.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(lia)); exact HE033).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HF8hi2 : F / 8 <= 17592184995808) by (clear - HFq HF8 HFceil C1; lia).
pose proof HobjT as ((cidT & posT & HinT & HcidT & HTal & HTlo & HThi) & Ht8 & HraT).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidT posT HAR HinT) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR HinT) as HTimg.
destruct (in_split _ _ HinT) as (l2 & l3 & Hspl).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cidT, posT) [] l2 l3 HAR3 ltac:(rewrite HFR, Hspl; reflexivity)) as HdFT.
unfold zdisjoint, frame_rng in HdFT. cbn [fst snd] in HdFT. rewrite !EFA0 in HdFT. fold F in HdFT. change (fs_frame_bytes 2) with 256 in HdFT.
set (TF := frame_addr ly cidT posT) in *. set (TN := fs_frame_bytes cidT) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg in HTapp. unfold off_img, IMG_LO, IMG_TOP in HTimg.
pose proof Hok as (HT1 & HT2 & HT3 & HT4). unfold disco_table_c.tbl_T1 in HT1.
unfold w64 in E740, E733, E764.
assert (HV4 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + 48 * i + 8) 4 (disco_table_c.u_at T (48 * i + 8) 4)).
{ replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia. apply tjr_garr8_u4; [exact Harrk | lia | rewrite HlenT; lia]. }
pose proof (tjr_u4_range T (48 * i + 8)) as HU4.
destruct (Hbuf Hcap3) as (Hbin0 & Hcapb).
assert (Hspc : alloc_ceiling + 12112 <= sp1) by (clear - Hceil Hslo Hsp1; lia).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hbin0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hbin0) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
set (L := Z.of_nat (length acc)) in *.
assert (Hbufsp : buf + cap + 11792 <= sp1) by (clear - Hbceil Hcapb Hspc C1; lia).
assert (UA : U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0) (SOff 733 0)) (SOff 764 0)) = buf + L).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 12 buf E12), (U_atom E 733 o1 E733), (U_atom E 764 o2 E764) by lia.
rewrite (zcanon_id (buf + o1)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
assert (UX : U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0) (SOff 733 0)) (SOff 764 0)) (SLit 1))) = 1).
{ rewrite (U_SAlu E ALU_XOR), (U_SAlu E ALU_SLTU), UA, !U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
destruct (Z.ltb_spec (buf + L) 1); [lia|]. reflexivity. }
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hbin3 Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cidT posT HAR Hbin0 HinT) as HdBT.
unfold zdisjoint in HdBT. cbn [fst snd] in HdBT. fold TF TN in HdBT.
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR Hbin0) as Hbimg.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
pose proof (img_env_atomP E 284 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E284.
pose proof (img_env_atomP E 285 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E285.
pose proof (img_env_atomP E 286 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E286.
pose proof (img_env_atomP E 287 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E287.
pose proof TJS as (_ & _ & _ & HR46 & _).
pose proof HR46 as (_ & _ & H46lo & H46hi & _). cbv [A_OBJ Nat.add] in H46lo, H46hi. unfold IMG_LO, IMG_TOP in H46lo, H46hi.
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof tj_snp_cr as HCR.
assert (HKb : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 740 (HPTR 3) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E740, unsigned_lit_small by lia; change (2 ^ 3) with 8;
split; [lia|]; split; [|lia]; replace (t + 48 * i) with (t + (6 * i) * 8) by ring; rewrite Z_mod_plus_full; exact Ht8)) as HS1;
clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 799 (mkAF 0 (2 ^ 64 - 1) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Z.pow_0_r, Z.mod_1_r;
pose proof (bv_unsigned_in_range 64 (ew Ev 799)) as Hr799; change (bv_modulus 64) with (2 ^ 64) in Hr799;
split; [lia|]; split; [reflexivity | lia])) as HS1;
clear HS; rename HS1 into HS end.
norm_ss HS.
destruct (HT2 i Hi) as [Hr | [Hr | Hr]].
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
assert (Hu : disco_table_c.u_at T (48 * i + 8) 4 = r) by (apply tjr_swrap; [exact HU4 | exact Hrr | lia]);
rewrite Hu in HV4;
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 740%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SLit r))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 8 4 (SLit r) r); [reflexivity | cbn; lia | cbn; lia | exact HV4])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 C5 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8hi2 Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HdFT HTlo HThi HT1 Hi; unfold SB in *; repeat split; lia)) as HS1;
clear HS; rename HS1 into HS end end.
all: norm_ss HS.
all: shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3)).
all: (hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan).
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => tjr_awr ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0 | _ => idtac end.
all: tjr_kb HKb AG buf cap ltac:(idtac; first [ clear - Hrgkb Hakb Hbsep Hbceil Hcapb Hsp1 Hceil Hslo Hstk0 HSK C1 Hb4096 HF4096 HFceil; lia | clear - Hakb Hb4096 Hbceil Hcapb C1 Hceil; lia | lia ]).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: try (lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
exfalso; rewrite branch_ltu_U, UA, (U_atom E 12 buf E12) in Hc by lia; apply Z.ltb_lt in Hc; lia end).
all: repeat match goal with H : branch_taken _ _ _ = false |- _ => clear H end.
all: (hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan).
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => tjr_awr ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0 | _ => idtac end.
all: tjr_kb HKb AG buf cap ltac:(idtac; first [ clear - Hrgkb Hakb Hbsep Hbceil Hcapb Hsp1 Hceil Hslo Hstk0 HSK C1 Hb4096 HF4096 HFceil; lia | clear - Hakb Hb4096 Hbceil Hcapb C1 Hceil; lia | lia ]).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: try (lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
exfalso; rewrite branch_eq_U, UX, U_SLit in Hc; vm_compute in Hc; discriminate Hc end).
all: repeat match goal with H : branch_taken _ _ _ = false |- _ => clear H end.
all: (hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan).
all: lazymatch goal with
| |- range_addressable (rd_of _ (mrestrict _ (ms_mem _))) _ _ _ =>
let HKx := fresh "HKx" in let HraX := fresh "HraX" in
pose proof (tjr_keep_journal (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ) as HKx;
unfold tj_keep in HKx; cbn [c_t c_T c_ly c_S] in HKx;
destruct HKx as (_ & _ & (_ & _ & HraX));
rewrite (U_atom_off E 740 (t + 48 * i) 8 E740) by lia;
eapply (obl_of_range SEGS _ _ E (SOff 32 0) _ 4 t 400 HraX); [rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity | lia | lia]
| |- awr_ok _ _ _ _ _ _ _ _ _ => tjr_awr ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0
| _ => idtac end.
all: tjr_kb HKb AG buf cap ltac:(idtac; first [ clear - Hrgkb Hakb Hbsep Hbceil Hcapb Hsp1 Hceil Hslo Hstk0 HSK C1 Hb4096 HF4096 HFceil; lia | clear - Hakb Hb4096 Hbceil Hcapb C1 Hceil; lia | lia ]).
all: rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite !tjr_U_ewset by reflexivity; exact UA) Ra0.
all: rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite !tjr_U_ewset by reflexivity;
rewrite (tjr_Usub2 E 13 733 764 cap o1 o2 18446744073709551615 E13 E733 E764) by (first [reflexivity | lia]); lia) Ra1.
all: prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp; prreg HS (1%bv : bv 5) Qra;
prreg HS (12%bv : bv 5) Qa2; prreg HS (13%bv : bv 5) Qa3.
all: pmkst HS.
all: rewrite HSNPC.
all: pose proof (proj1 HJ) as HARc.
all: pose proof (tjr_keep_journal (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ) as HKc.
all: unfold tj_keep in HKc; cbn [c_t c_T c_ly c_S] in HKc; destruct HKc as (HRODc & _ & _).
all: destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
pose proof (tjr_str r TJS) as HSTR; pose proof (tjr_txt_len r) as HTL;
let OB := eval vm_compute in (tjr_obj r) in
let KK := eval vm_compute in (A_OBJ OB) in
change (tjr_obj r) with OB in HSTR;
pose proof HSTR as (_ & _ & HSlo & HShi & _); cbv [A_OBJ Nat.add] in HSlo, HShi; unfold IMG_LO, IMG_TOP in HSlo, HShi;
assert (HA3 : argZ (ms_regs ms1) 3 = VAL (A_OBJ OB))
by (unfold argZ; replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity);
rewrite Qa3, (img_env_atomP E KK HEI ltac:(unfold A_TEXT, A_LIM; lia)); rewrite unsigned_lit_small by lia; reflexivity)
end.
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq)
W3 (ms_regs ms1) (ms_mem ms1) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k
(buf + L) (cap - L) (VAL 287) tj_f_role tjr_ps [] (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) [APtr (rolename r)] (tjr_txt r)
cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24124)) _ HJ HRODc) end.
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
lazymatch goal with
| |- spZ _ = _ => unfold spZ at 1; rewrite Qsp, E60;
rewrite unsigned_lit_small by (clear - Hbufsp Hspc Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); clear - Hbufsp Hspc Hsp1; lia
| |- _ mod 16 = 0 => rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity
| |- getr _ _ = _ => first [ exact Ra0 | exact Ra1 | exact Qra | rewrite Qgp, E3; exact Hgp | rewrite Qtp, E4; exact Htp
| rewrite Qa2, E287; reflexivity ]
| |- YK0s.ret_ok _ => apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| |- consts_view _ _ _ _ => exact (tj_snp_consts _ _ HRODc)
| |- rdword _ _ = _ => first [ exact HG1 | exact HG2 ]
| |- pf_parse _ = _ => exact tjr_parse
| |- Forall pf_disco_piece _ => exact tjr_disco
| |- pf_text _ _ = _ => apply tjr_text
| |- va_words _ _ _ _ _ => split; [reflexivity | intros jj Hjj; cbn in Hjj; lia]
| |- pf_args_asan _ _ _ _ => cbn [map app pf_args_asan]; rewrite HA3; split; [|exact I];
apply (tjr_str_arg _ _ _ _ _ _ _ _ HARc HRODc HSTR); cbv [A_OBJ Nat.add];
lazymatch goal with |- Forall (zdisjoint (?v, _)) _ => pose proof (tjr_str_end_bound v (rolename r)) as HSE end;
let LS := eval vm_compute in (Z.of_nat (length (rolename r))) in change (Z.of_nat (length (rolename r))) with LS in HSE;
unfold snp_out; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hbufsp Hspc HSE HSlo HShi Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP; lia
| |- fmt_at _ _ _ _ => apply (tjr_fmt_at _ _ _ _ _ 46 tj_f_role _ HARc HRODc HR46); cbv [A_OBJ Nat.add];
change (Z.of_nat (length tj_f_role) + 1) with 13;
unfold snp_out; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hbufsp Hspc H46lo H46hi Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP; lia
| |- Forall (fun _ => Forall _ _) _ => eapply Forall_impl; [|exact HCR];
intros [lo0 n0] (Hq1 & Hq2 & Hq3); cbn [fst snd] in *; unfold IMG_LO, IMG_TOP in *;
unfold snp_out; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hbufsp Hspc Hq1 Hq2 Hq3 Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP; lia
| |- Forall (zdisjoint _) _ =>
unfold snp_out; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd length Z.of_nat];
clear - Hbufsp Hspc Hgc1 Hgc2 Hgv1 Hgv2 Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP; lia
| |- Forall _ _ => eapply Forall_impl; [|exact HCR];
intros [lo0 n0] (Hq1 & Hq2 & Hq3); cbn [fst snd] in *; unfold IMG_LO, IMG_TOP in *; clear - Hbufsp Hspc Hq1 Hq2 Hq3; lia
| |- pairwise _ _ => unfold snp_out; cbn [pairwise];
split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd];
clear - Hbufsp Hspc Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP; lia
| apply Forall_nil] | split; [apply Forall_nil | exact I]]
| |- amem_range _ _ => apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hbin3);
clear - Hbufsp Hspc Ho1 Ho2 Ho12 Hacc Hcapb Hb4096; lia
| |- range_addressable _ _ _ _ => apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hbin3);
clear - Hbufsp Hspc Ho1 Ho2 Ho12 Hacc Hcapb Hb4096; lia
| |- shadow_hull_vis _ _ _ => apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hbin3);
clear - Hbufsp Hspc Ho1 Ho2 Ho12 Hacc Hcapb Hb4096; lia
| |- forall _, _ -> _ /\ _ => intros aa Haa; split;
[ right; left; split;
[ exists (buf, buf + cap); split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity
| cbn [fst snd]; clear - Hbufsp Hspc Haa Ho1 Ho2 Ho12 Hacc; lia]
| exists buf, Nb; split; [exact Hbin3 | clear - Hbufsp Hspc Haa Ho1 Ho2 Ho12 Hacc Hcapb; lia] ]
| clear - Hbufsp Hspc Haa Ho1 Ho2 Ho12 Hacc Hcapb Hb4096 Hbceil Hsp1 Hceil Hslo Hstk0 HSK C1 Hes; rewrite ?Hes; lia ]
| |- Z.land _ _ = _ => exact Hfrm
| |- zdisjoint _ _ => eapply tj_dest_off_globals;
[ exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hbin3
| clear - Hbufsp Hspc Ho1 Ho2 Ho12 Hacc Hcapb Hb4096; lia | clear - Hbufsp Hspc Ho1 Ho2 Ho12 Hacc Hcapb Hb4096; lia ]
| |- disco_fmt_lo <= _ /\ _ => exact (tj_ro_fmt_rng 46 tj_f_role HR46 ltac:(cbv; lia))
| |- not (_ = _) => unfold tj_f_role; discriminate
| |- SnFF.pf_args_amem _ _ => cbn [map app SnFF.pf_args_amem]; rewrite HA3; split; [|exact I]; exact (tj_ro_amem8 _ _ HSTR)
| |- _ => first [ clear - Hbufsp Hspc HTL Hgc1 Hgc2 Hgv1 Hgv2 Hb4096 Hbceil Hcapb Hbapp Hbimg Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3
Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP Hes;
unfold REAC_DISCO_TABLE_JSON_STK; rewrite ?HSNP; cbn [length Z.of_nat]; lia | idtac ]
end end.
all: intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
all: replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia.
all: rewrite HSNP in Hfr.
all: assert (HKp : forall a, buf <= a < buf + L -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a)
by (intros aa Haa; transitivity (aview SEGS (w_H W3) (ms_mem ms1) aa);
[ apply Hfr; clear - Haa Hbufsp Hspc Hb4096 Hbceil Hcapb Hacc Ho1 Ho2 Ho12 Hcap3 Hcap C1 Hsp1; lia
| apply HKb; clear - Haa Hacc Ho1 Ho2 Ho12; lia ]).
all: reseat HS HJ2 HP2 [0;1;2;3;4;5;6;7;8]%nat AG
ltac:(idtac; tjr_kept AG Hfr Hpres2
ltac:(clear - Hakb HdBT HTlo HThi HTceil HT4096 Hbsep HF4096 HFceil HF8lo HF8hi Hob241 Hob242 Hob253 Huar
Hbapp Hbimg Hb4096 Hbceil Hcapb Hbufsp Hspc Hsp1 C1 C2 C3 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap HSNP
Hi HT1 Hshi H47 Htop Htop2 Hceil Hslo Hstk0 HSK; lia)).
all: apply (st_ok_pi_restrict_fx fq fx') in HS.
all: clear RUN RUNTO BR.
all: pose (RUN := paj_run (fx := fx') B LAWS).
all: pose (RUNTO := paj_run_to (fx := fx') B LAWS).
all: pose (BR := paj_branch (fx := fx') (PI := PI)).
all: assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem2 a) by (intros; reflexivity).
all: assert (HL : L = Z.of_nat (length acc)) by reflexivity.
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
assert (HPtxt : P2 (reac_disco_table_json_c.tj_entry T i) = tjr_txt r)
by (rewrite tjr_P2; cbn [reac_disco_table_json_c.tj_entry e_role]; rewrite Hrr; reflexivity) end.
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
let LEN := eval vm_compute in (Z.of_nat (length (tjr_txt r))) in
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_pin_reg' Ev ssx msx (10%bv : bv 5) LEN HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0'; unfold w64; f_equal; vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end end.
all: norm_ss HS.
all: assert (E13v : ew E5 13 = Z_to_bv 64 cap)
by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
all: assert (Usub : U E5 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1))))
(SMd M_MUL (SOff 764 0) (SLit (-1)))) = cap - L)
by (rewrite (tjr_Usub2 E5 13 733 764 cap o1 o2 (-1) E13v E733 E764 tjr_zm1)
by (clear - Ho1 Ho2 Ho12 Hacc Hcap; lia); clear - Ho12; lia).
all: reshok HS.
all: (hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK Bspan).
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => tjr_awr ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0 | _ => idtac end.
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
let LEN := eval vm_compute in (Z.of_nat (length (tjr_txt r))) in
assert (HLEN : Z.of_nat (length (tjr_txt r)) = LEN) by reflexivity end.
all: tjr_kb HK2 AG buf cap ltac:(idtac; first [ clear - Hrgkb Hakb Hbsep Hbceil Hcapb Hsp1 Hceil Hslo Hstk0 HSK C1 Hb4096 HF4096 HFceil Hshi H47; lia | clear - Hakb Hb4096 Hbceil Hcapb C1 Hceil; lia ]).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: lazymatch goal with
| Hc : branch_taken _ _ _ = true |- _ => rewrite branch_geu_U, Usub, U_SLit, zcanon_id in Hc by (unfold M64; lia);
apply negb_true_iff, Z.ltb_ge in Hc
| Hc : branch_taken _ _ _ = false |- _ => rewrite branch_geu_U, Usub, U_SLit, zcanon_id in Hc by (unfold M64; lia);
apply negb_false_iff, Z.ltb_lt in Hc end.
all: lazymatch type of Hc with
| _ <= _ => (hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 25204)
| _ < _ => (hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 24132) end.
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => tjr_awr ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0 | _ => idtac end.
all: tjr_kb HK2 AG buf cap ltac:(idtac; first [ clear - Hrgkb Hakb Hbsep Hbceil Hcapb Hsp1 Hceil Hslo Hstk0 HSK C1 Hb4096 HF4096 HFceil Hshi H47; lia | clear - Hakb Hb4096 Hbceil Hcapb C1 Hceil; lia ]).
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin) as (_ & _ & _ & HFSx).
all: rewrite EFA0 in HFSx; fold F in HFSx; change (fs_frame_bytes 2 / 8) with 32 in HFSx.
all: tjr_fs_rw HS E529 HFSx.
all: lazymatch type of Hc with
| _ <= _ => prreg HS (23%bv : bv 5) R23
| _ < _ => rregU HS (26%bv : bv 5) L ltac:(rewrite (tjr_Uadd2 _ 733 764 o1 o2 E733 E764) by (clear - Ho1 Ho2 Ho12 Hacc Hcap; lia);
clear - Ho12; lia) R26; prreg HS (10%bv : bv 5) R10 end.
all: lazymatch type of Hc with
| _ <= _ => (ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
ra_join_val HS 640%nat 13%nat R23 E653)
| _ < _ => (ra_join HS ss_tjR 780%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
ra_join_val HS 780%nat 4%nat R10 E784; ra_join_val HS 780%nat 13%nat R26 E793) end.
all: hei_havoc HS.
all: rebaseE HS AG HEv.
all: clear HEv.
all: lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of Hc with
| _ <= _ => eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2)
| _ < _ => eapply (tj_from0_at_fx B IMG _ _ FR (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2)
end end end.
all: lazymatch goal with
| |- tj_baseX _ _ _ => exact HBASE
| |- tj_EX _ _ => unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg;
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33, HE033; reflexivity | apply AG; lia] |];
split; [exact E60|]; split; [exact E516|]; split; [exact E528|]; split; [exact E529 | assumption]
| |- ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HJ2
| |- frames _ = _ => exact HFR
| |- st_ok_pi _ _ _ _ _ => exact HS
| _ => idtac end.
all: try (progress unfold INV_tjX; cbn [c_cap c_T c_now c_buf c_ly c_S];
lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
split; [lia|]; split; [exact Hperm|]; exists (-1); split;
[rewrite E653; apply bv_eq; unfold w64; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|];
split; [intros; lia|]; split; [|intros _ _; reflexivity];
intros _ Hlt; exfalso; unfold tj_len in Hlt; rewrite Htxt, !length_app, HPtxt in Hlt;
clear - Hlt Hc HL HLEN; lia end).
all: try (progress unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_age; cbn [c_cap c_T c_now c_buf c_ly c_S c_t];
lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
split; [lia|]; split;
[ split; [exact Hperm|];
split; [exact (tjr_keep_journal (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ2)|];
split; [lia|]; split; [lia|]; repeat split; assumption
| exists (acc ++ tjr_txt r); split;
[ exists L, (Z.of_nat (length (tjr_txt r))); rewrite HLEN; split; [exact E793|]; split; [exact E784|];
split; [clear - Ho1 Ho2 Ho12; lia|]; split; [clear; lia|]; rewrite length_app, Nat2Z.inj_add, <- HL, HLEN; reflexivity
| split; [rewrite length_app, Nat2Z.inj_add, <- HL, HLEN; clear - Hc; lia|];
split; [rewrite Htxt, HPtxt, <- app_assoc; reflexivity|];
rewrite <- app_assoc;
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf);
[ intros aa Haa; rewrite !length_app in Haa; cbn [length] in Haa; apply HK2; clear - Haa Hc HL HLEN Ho1 Ho2 Ho12; lia |];
apply (proj2 (garr8_app SEGS _ _ _ _)); split;
[ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc);
[ intros aa Haa; apply HKp; clear - Haa HL; lia | exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)) ] |];
rewrite <- HL; apply tjr_garr8_of_aview; intros j Hj; rewrite length_app in Hj; cbn [length] in Hj;
destruct (Nat.lt_ge_cases j (length (tjr_txt r))) as [Hjl | Hjl];
[ rewrite app_nth1 by lia; pose proof (Hwr (Z.of_nat j) ltac:(clear - Hjl Hc HLEN; lia)) as Hq; rewrite Nat2Z.id in Hq; exact Hq
| assert (Hj2 : j = length (tjr_txt r)) by lia; subst j; rewrite app_nth2, Nat.sub_diag by lia; cbn [nth];
replace (buf + L + Z.of_nat (length (tjr_txt r))) with (buf + L + Z.min (Z.of_nat (length (tjr_txt r))) (cap - L - 1))
by (clear - Hc HLEN; lia); exact Hnul ] ] ] end).
Qed.
End h.
End f.
End d.
