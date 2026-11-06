(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_disco's program walk, over fuzz_disco's listing. Image objects follow fuzz_disco.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 66 (atom 307) and the side-stack flag cell is object 67 (atom 308), so img_factsF and img_hull_factsF give E240 E241 E242 E307 E308 and Hob241 Hob242 Hob307 Hob308, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and DiscoFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACja.v, with its module paths and module names changed; 912 of its 978 lines of code are new or changed and 265 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YK00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tjt_clrmod :=
repeat match goal with
| H : _ mod _ = _ |- _ => clear H
| H : _ = _ * (_ / _) |- _ => clear H
| H : _ / _ = _ * (_ / _) |- _ => clear H
end.
Local Ltac gadd H := let HG := fresh "HGq" in match goal with G : boxed _ |- _ => pose proof (conj G H) as HG; clear G; box HG end.
Local Ltac glia := first [match goal with HG : boxed _ |- _ => clear - HG; unbox; lia end | clear; lia | lia].
Local Ltac gliam := first [match goal with HG : boxed _ |- _ => clear - HG; unbox; lia end | clear; lia | tjt_clrmod; lia].
Local Ltac glia_with H := first [match goal with HG : boxed _ |- _ => clear - H HG; unbox; lia end | tjt_clrmod; lia].
#[local] Ltac evalE AG ::=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by glia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by glia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; glia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => glia | |- _ <= _ => glia | |- _ < _ => glia | |- _ <= _ < _ => glia | |- _ <= _ <= _ => glia | |- _ < _ <= _ => glia end
| idtac ].
Local Ltac tjt_notw AG Ha :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG;
first [match goal with HG : boxed _ |- _ => clear - Ha HG; intros; unbox; lia end | intros Hrg; tjt_clrmod; lia]|]);
destruct Hin.
Ltac tjt_fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjt_kept AG Hfr Hpres2 :=
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; glia_with Ha | exact Hpres2].
Ltac tjt_gk HG AG :=
match goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
lazymatch type of HG with garr8 ?sg (mrestrict ?Hh m0) ?b ?l =>
let HG2 := fresh "HGb" in
assert (HG2 : garr8 sg (mrestrict Hh m1) b l);
[ solve [ apply (garr8_aview_kept sg Hh Hh m0 m1 b l);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply aview_kept_out; [exact HFr | glia_with Ha | tjt_notw AG Ha]
  | exact HG ] ]
| clear HG; rename HG2 into HG ] end end; clear_frames.
Ltac tjt_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tjt_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tjt_awr_rec hd AG fpos F EFA :=
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
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tjt_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tjt_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tjt_awr: no rule for the head region" ];
tjt_awr_rec hd AG fpos F EFA
end.
Ltac tjt_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tjt_awr_rec hd AG fpos F EFA.
Ltac tjt_rw32 HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by glia;
rewrite E529, unsigned_lit_small by (unfold SB; glia);
intros o Ho; apply (apresent_writable _); apply Hp; clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma tjt_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia.
replace (c + l * (2 ^ 64 - 1)) with ((c - l) + l * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjt_s32 : forall T k v, 0 <= v < 2 ^ 31 -> disco_table_c.s32_at T k = v ->
length (disco_table_c.sub T k 4) = 4%nat -> disco_table_c.u_at T k 4 = v.
Proof.
intros T k v Hv Hs Hl. unfold disco_table_c.s32_at, disco_table_c.u_at in *.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 4)) as Hb. rewrite Hl in Hb.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 4)) as Hn.
set (x := bytes_le_to_Z (disco_table_c.sub T k 4)) in *.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
change (bv_swrap 32 x) with ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) in Hs.
pose proof (Z.div_mod (x + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M.
lia.
Qed.
Lemma tjt_u8 : forall T k, (Z.to_nat k + 8 <= length T)%nat -> 0 <= disco_table_c.u_at T k 8 < 2 ^ 64.
Proof.
intros T k Hl. unfold disco_table_c.u_at.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 8)) as Hb.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 8)) as Hn.
assert (HL : length (disco_table_c.sub T k 8) = 8%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
rewrite HL in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb. lia.
Qed.
Lemma tjt_digits_eq : forall f x acc, PfFacts.pf_digits f x acc = printf_facts_c.pf_digits f x acc.
Proof.
induction f as [|f IH]; intros x acc; cbn [PfFacts.pf_digits printf_facts_c.pf_digits]; [reflexivity|].
destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma tjt_udec_eq : forall u, PfFacts.pf_udec u = printf_facts_c.pf_udec u.
Proof. intros u. unfold PfFacts.pf_udec, printf_facts_c.pf_udec. apply tjt_digits_eq. Qed.
Lemma tjt_blt : forall E a b va vb, U E a = va -> U E b = vb -> 0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (va <? vb).
Proof.
intros E a b va vb Ha Hb Hra Hrb. rewrite (denot_lit_U E a), (denot_lit_U E b), Ha, Hb.
cbn [branch_taken]. unfold bv_lts. rewrite !YK00.bv_signed_small by lia. reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Lemma tjt_vm : forall m t T k n, garr8 SEGS m t (map bv_unsigned T) -> 0 <= k ->
(Z.to_nat k + n <= length T)%nat -> val_mem SEGS m (t + k) n (disco_table_c.u_at T k n).
Proof.
intros m t T k n HG Hk Hl j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m t _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (t + Z.of_nat (Z.to_nat k + j)) with (t + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k n) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k n)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k n)) as H1.
assert (Hlen : length (disco_table_c.sub T k n) = n) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
rewrite Hlen in H1. rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat n))) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma tjt_rd_rom : forall H (mem : word -> option byte) x, seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H mem x <> None.
Proof.
intros H mem x Hr. unfold aview, mbyte, mrestrict. cbv beta.
destruct (H (Z_to_bv 64 x)); [| destruct (mem (Z_to_bv 64 x)); [discriminate|]];
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate | exfalso; exact (Hr eq_refl) | discriminate | exfalso; exact (Hr eq_refl)].
Qed.
Lemma tjt_garr8_snp : forall H (m m2 : word -> option byte) b acc T n,
garr8 SEGS (mrestrict H m) b (acc ++ [0]) -> Z.of_nat (length T) < n ->
(forall j, 0 <= j < Z.min (Z.of_nat (length T)) (n - 1) -> aview SEGS H m2 (b + Z.of_nat (length acc) + j) = Some (nth (Z.to_nat j) T 0)) ->
aview SEGS H m2 (b + Z.of_nat (length acc) + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0 ->
(forall a, b <= a < b + Z.of_nat (length acc) -> aview SEGS H m2 a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H m2) b (acc ++ T ++ [0]).
Proof.
intros H m m2 b acc T n HG Hn Hw Hz Hk. rewrite Z.min_l in Hw, Hz by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
- apply (garr8_aview_kept SEGS H H m m2 b acc); [exact Hk|]. exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) HG)).
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply val_mem1_of_aview.
destruct (Nat.lt_ge_cases j (length T)) as [Hjl | Hjl].
+ rewrite app_nth1 by lia. rewrite (Hw (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
+ assert (Ej : j = length T) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hz.
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
Lemma tjt_ro_rd : forall k s rd, tj_ro_at k s -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd ->
forall j, 0 <= j <= Z.of_nat (length s) -> rd (VAL (A_OBJ k) + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0).
Proof.
intros k s rd (Hg & Hro & Hlo & Hhi & Hc & Hb) HA j Hj.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B rd (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + j) HA
(Hro (VAL (A_OBJ k) + j) ltac:(lia)) (tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
replace (VAL (A_OBJ k) + j) with (VAL (A_OBJ k) + Z.of_nat (Z.to_nat j)) by lia.
apply Hb. rewrite length_app. cbn [length]. lia.
Qed.
Lemma tjt_fmt : forall k s ly S (W : world SEGS) mem md rs, tj_ro_at k s -> AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros k s ly S W mem md rs Hk HAR HA Hrs. pose proof Hk as (Hg & Hro & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (_ & _ & _ & _ & C5).
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k))
(Z.of_nat (length s) + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhu].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold fmt_at. split; [lia|]. split; [exact (tjt_ro_rd k s _ Hk HA)|]. split; [exact Hrs|].
split; [unfold amem_range; left; rewrite C5; lia|]. split; assumption.
Qed.
Lemma tjt_strarg : forall k s ly S (W : world SEGS) mem md rs, tj_ro_at k s -> AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 8)) rs ->
pf_arg_asan (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) (APtr s).
Proof.
intros k s ly S W mem md rs Hk HAR HA Hrs. pose proof Hk as (Hg & Hro & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (_ & _ & _ & _ & C5).
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k))
(Z.of_nat (length s) + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhu].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold pf_arg_asan. split; [exact Hc|]. split; [lia|]. split; [lia|].
split; [exact (tjt_ro_rd k s _ Hk HA)|].
split; [intros x Hx; apply tjt_rd_rom; exact (tj_pad_ro k s Hk x Hx)|].
split.
{ eapply Forall_impl; [|exact Hrs]. intros r Hr. unfold zdisjoint in *. cbn [fst snd] in *. unfold str_end.
pose proof (Z.mod_pos_bound (VAL (A_OBJ k) + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
split; [unfold amem_range; left; rewrite C5; lia|]. split; assumption.
Qed.
Lemma tjt_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
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
Set Default Goal Selector "all".
Theorem pb_tj_tail : tj_seg_tail B IMG.
Proof.
unfold tj_seg_tail, tj_fromT, tj_from0.
intros i FX FC FL cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
clear HB0 HX0.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG34; glia).
unfold INV_tjT, tj_lbody, tj_wrote in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & acc & E852 & Hacc & Htxt & Hgarr).
unfold w64 in E721, E722, E740, E741, E852.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSKe : REAC_DISCO_TABLE_JSON_STK = 640 + 11776) by (unfold REAC_DISCO_TABLE_JSON_STK; glia).
assert (HSK : 4736 <= REAC_DISCO_TABLE_JSON_STK) by glia.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
assert (Ho16 : boxed ((sp1 - spZ regs) mod 16 = 0))
by (unfold boxed; rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(glia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(glia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(glia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(glia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(glia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat ltac:(glia)); rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(glia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(glia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(glia)); exact HE032).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(glia)); exact HE033).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(glia)); exact HE02).
assert (F12 : ew E0 12 = Z_to_bv 64 buf) by (rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (F13 : ew E0 13 = Z_to_bv 64 cap) by (rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (F10 : ew E0 10 = Z_to_bv 64 t) by (rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
clear AG34.
img_factsF E.
img_hull_factsF.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(glia)); glia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by glia; rewrite Z.div_mul by glia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; glia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; glia).
unfold tj_keep, afobj in HKEEP. cbn [c_t c_ly c_S c_T] in HKEEP.
destruct HKEEP as (HROD3 & HG3 & ((cidt & post & Hint & Hcidt & Hfa8 & Htlo & Hthi) & Ht8 & HRA3)).
assert (Hint3 : In (cidt, post) (frames S3)) by (rewrite HFR; right; exact Hint).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidt post HAR Hint) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hint3) as HTimg. rewrite EFA in HTimg.
assert (HTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (cidt, post))).
{ destruct (in_split _ _ Hint) as (l2 & l3 & El). apply (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ [] l2 l3 HAR3).
rewrite HFR, El. reflexivity. }
unfold zdisjoint, frame_rng in HTF. cbn [fst snd] in HTF. rewrite !EFA in HTF. fold F in HTF.
change (fs_frame_bytes 2) with 256 in HTF.
pose proof (fs_frame_bytes_nonneg cidt) as HTb0.
set (TB := fs_frame_bytes cidt) in *. set (FT := frame_addr ly cidt post) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold off_img, IMG_LO, IMG_TOP in HTimg.
destruct Hok as (HT1 & HT2 & HT3 & HT4). unfold disco_table_c.tbl_T1 in HT1.
destruct (HT4 i Hi) as (_ & _ & Hown).
pose proof TJS as (Ho39 & Hc55 & Hm42 & Hr46 & Hmo49 & Hw50 & Hmu47 & Hw48 & Hs53 & Hs54 & Hc40 & He41 & Hb45 & Hm44 & Hu43 & Hs51 & Hs52 & Hkd).
assert (Ht400 : t + 400 <= FT + TB) by glia.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cidt post HAR3 Hinb Hint3) as Hbsep2.
rewrite EFA0 in Hbsep, Hbsep2. fold F FT in Hbsep, Hbsep2. change (fs_frame_bytes 2) with 256 in Hbsep. fold TB in Hbsep2.
unfold zdisjoint in Hbsep, Hbsep2. cbn [fst snd] in Hbsep, Hbsep2.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
assert (HGEO : boxed (
4096 <= buf /\ buf + cap <= alloc_ceiling /\
(buf + cap <= 2147450880 \/ 17594333495296 <= buf) /\
(buf + cap <= 65536 \/ 6283264 <= buf) /\
(buf + cap <= FT \/ FT + TB <= buf) /\
FT <= t /\ t + 400 <= FT + TB /\ 4096 <= FT /\ FT + TB <= alloc_ceiling /\ 0 <= TB /\
(buf + cap <= F \/ F + 256 <= buf) /\ 4096 <= F /\ F + 256 <= alloc_ceiling /\
(F + 256 <= FT \/ FT + TB <= F) /\
512 <= F / 8 /\ F / 8 < 17592186044416 /\
cap < 2 ^ 31 /\ 0 <= i /\ i <= 7 /\ 0 <= L /\ L < cap /\ 3 <= cap /\ cap <= req_size Nb /\
alloc_ceiling + 12416 <= spZ regs /\ spZ regs - 304 <= sp1 /\ sp1 <= spZ regs - 288 /\ spZ regs < 2 ^ 63 /\
140735332483072 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\
SNPRINTF_STK = 11776 /\ ESTACK = 4096 /\ REAC_DISCO_TABLE_JSON_STK = 12416))
by (unfold boxed; repeat split; clear - Hb4096 Hbceil Hcapb Hbapp Hbimg Hbsep2 Htlo Hthi HT4096 HTceil Ht400 HTb0 HTF Hbsep HF4096 HFceil HF8lo HF8hi
Hi HT1 Hceil Hsp1 HSK HSKe Hstk0 Hshi Hslo H47 Hbot Htop Htop2 Hacc Hcap3 Hcap C1 C2 C3 C4 C5 HSNP Hes; lia).
gadd (conj Hob241 (conj Hob242 (conj Hob253 Huar))).
gadd (conj HlenT Hk0).
assert (UA : U E (SAlu ALU_ADD (SOff 12 0) (SOff 852 0)) = buf + L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 12 buf E12), (U_atom E 852 L E852) by glia; apply zcanon_id; unfold M64; glia).
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 740 (PTR 3) HS
ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite E740; rewrite unsigned_lit_small by glia;
change (2 ^ 3) with 8; split; [glia|]; split; [|glia]; rewrite Z.add_mod by glia; rewrite Ht8;
replace (48 * i) with (8 * (6 * i)) by glia; rewrite Z.mul_comm, Z_mod_mult; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 852 (mkAF 0 2147483647 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E852; rewrite unsigned_lit_small by glia;
rewrite Z.pow_0_r, Z.mod_1_r; glia)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
destruct Hown as [Hown | Hown];
[ assert (Hu : disco_table_c.u_at T (48 * i + 24) 4 = 0)
  by (apply tjt_s32; [glia | exact Hown | unfold disco_table_c.sub; rewrite length_firstn, length_skipn; glia])
| assert (Hu : disco_table_c.u_at T (48 * i + 24) 4 = 1)
  by (apply tjt_s32; [glia | exact Hown | unfold disco_table_c.sub; rewrite length_firstn, length_skipn; glia]) ].
1: assert (Hsel : exists kw sw, tj_ro_at kw sw /\ VAL (A_OBJ kw) = VAL 293 /\ (sw = s_true \/ sw = s_false) /\
owned_text (reac_disco_table_json_c.tj_entry T i) = sw)
by (exists 52%nat, s_false; split; [exact Hs52|];
split; [reflexivity|]; split; [right; reflexivity|]; unfold owned_text, reac_disco_table_json_c.tj_entry; cbn [e_owned];
rewrite Hown; reflexivity).
2: assert (Hsel : exists kw sw, tj_ro_at kw sw /\ VAL (A_OBJ kw) = VAL 292 /\ (sw = s_true \/ sw = s_false) /\
owned_text (reac_disco_table_json_c.tj_entry T i) = sw)
by (exists 51%nat, s_true; split; [exact Hs51|];
split; [reflexivity|]; split; [left; reflexivity|]; unfold owned_text, reac_disco_table_json_c.tj_entry; cbn [e_owned];
rewrite Hown; reflexivity).
destruct Hsel as (kw & sw & Hsw & HkwV & Hswv & Hotxt).
pose proof (tjt_vm _ t T (48 * i + 24) 4 HG3 ltac:(glia) ltac:(rewrite HlenT; glia)) as Hvm.
rewrite Hu in Hvm.
lazymatch type of Hu with _ = ?ov =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit ov))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; rewrite unsigned_lit_small by glia; split; [glia|]; split; [glia|]; split; [intros o Ho; glia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 24 4 (SLit ov) ov); [reflexivity | zside | zside |];
replace (t + 48 * i + 24) with (t + (48 * i + 24)) by glia; exact Hvm)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTF Htlo Ht400 Hi HT1 HTb0;
repeat split; lia)) as HS3 end end.
clear HS; rename HS3 into HS; norm_ss HS.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3)).
pose proof Hgarr as HGb.
assert (HLb : Z.of_nat (length (acc ++ [0])) <= cap) by (rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; fold L; glia).
gadd HLb.
paj_run_tok RUN HS HJ SHOK Bspan.
first [ solve [tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0] | idtac ].
tjt_gk HGb AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
lazymatch goal with
| Hc : branch_taken _ _ _ = true |- _ => exfalso; rewrite branch_ltu_U, UA, (U_atom E 12 buf E12) in Hc by glia; apply Z.ltb_lt in Hc; glia_with Hc
| Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
paj_run_tok RUN HS HJ SHOK Bspan.
first [ solve [tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0] | idtac ].
lazymatch goal with
| |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) (ms_mem ?msx))) _ _ _ =>
  let HKc := fresh "HKc" in pose proof (tjt_keep_journal _ _ _ _ _ _ _ _ HBASE HJ) as HKc;
  unfold tj_keep, afobj in HKc; cbn [c_t c_T c_ly c_S] in HKc; destruct HKc as (_ & _ & (_ & _ & HRAc));
  change (rd_of SEGS (mrestrict (w_H Wx) (ms_mem msx))) with (aview SEGS (w_H Wx) (ms_mem msx));
  rewrite (U_atom E 32 SB E32) by (unfold SB; glia); rewrite (U_atom_off E 740 (t + 48 * i) 24 E740) by glia;
  rewrite SB_SHADOW_OFF; apply (range_addressable_sub _ SHADOW_OFF t 400); [exact HRAc | glia | glia]
| _ => idtac end.
tjt_gk HGb AG.
lazymatch type of HS with st_ok _ ?Enew _ _ => assert (HEIn : img_env VAL A_LIM Enew) by (repeat apply img_env_ewset_hi; first [exact HEI | unfold A_LIM; glia]) end.
rebaseE HS AG HEv.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (eq_trans (AG 12%nat ltac:(glia)) F12) as E12c; pose proof (eq_trans (AG 13%nat ltac:(glia)) F13) as E13c;
let HEv := rnHEI Ev in
pose proof (img_env_atomP Ev 292 HEv ltac:(unfold A_TEXT, A_LIM; glia)) as E292;
pose proof (img_env_atomP Ev 293 HEv ltac:(unfold A_TEXT, A_LIM; glia)) as E293;
pose proof (img_env_atomP Ev 294 HEv ltac:(unfold A_TEXT, A_LIM; glia)) as E294 end.
pose proof (proj1 HJ) as HARc.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2).
unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
gadd (conj Hgc1 (conj Hgc2 (conj Hgv1 Hgv2))).
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 12 buf E12c), (U_atom _ 852 L E852) by glia; apply zcanon_id; unfold M64; glia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom _ 13 cap E13c), (U_atom _ 852 L E852) by glia; rewrite U_SLit; apply tjt_sub; [reflexivity | glia | glia]) Ra1.
prreg HS (2%bv : bv 5) Qsp.
prreg HS (3%bv : bv 5) Qgp.
prreg HS (4%bv : bv 5) Qtp.
prreg HS (1%bv : bv 5) Qra.
prreg HS (12%bv : bv 5) Qa2.
prreg HS (13%bv : bv 5) Qa3.
pose proof Hs53 as (_ & _ & H53lo & H53hi & _). pose proof Hsw as (_ & _ & Hswlo & Hswhi & _).
unfold IMG_LO, IMG_TOP in H53lo, H53hi, Hswlo, Hswhi. cbv [A_OBJ Nat.add] in H53lo, H53hi.
change (Z.of_nat (length tj_f_owned)) with 11 in H53lo, H53hi.
gadd (conj H53lo (conj H53hi (conj Hswlo Hswhi))).
assert (Hswl : (length sw <= 5)%nat) by (destruct Hswv as [-> | ->]; cbn; glia).
gadd Hswl.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (A3 : argZ (ms_regs msx) 3 = VAL (A_OBJ kw))
by (lazymatch type of Qa3 with getr ?rg _ = ?v =>
  change (bv_unsigned (getr rg (Z_to_bv 5 (10 + 3))) = VAL (A_OBJ kw));
  replace (getr rg (Z_to_bv 5 (10 + 3))) with v by (rewrite <- Qa3; reflexivity) end;
  first [rewrite E293 | rewrite E292]; rewrite HkwV; apply unsigned_lit_small; pose proof (pa_val_range 293%nat); pose proof (pa_val_range 292%nat); glia) end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR (SIGMA AS___interceptor_trampoline_snprintf)
(eq_ind_r (fun p => SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR p) (ASNP fq) HSNPC)
W3 (ms_regs msX) (ms_mem msX) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL 294) tj_f_owned
ltac:(let v := eval vm_compute in (pf_parse tj_f_owned) in lazymatch v with Some ?p => exact p end)
[] (map (argZ (ms_regs msX)) [3; 4; 5; 6; 7] ++ []) [APtr sw] ([44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24700)) _ HJ HRODc) end;
[ tjt_clrmod; unfold spZ at 1; rewrite Qsp, E60, unsigned_lit_small by glia; glia
| tjt_clrmod; exact Ho16
| gliam
| gliam
| tjt_clrmod; rewrite Qgp, (AG 3%nat) by glia; rewrite (HE0 3%nat 3%bv eq_refl); exact Hgp
| tjt_clrmod; rewrite Qtp, (AG 4%nat) by glia; rewrite (HE0 4%nat 4%bv eq_refl); exact Htp
| tjt_clrmod; exact Qra
| tjt_clrmod; apply ret_ok_codeptr_v; [glia | reflexivity]
| tjt_clrmod; exact Ra0
| tjt_clrmod; exact Ra1
| tjt_clrmod; rewrite Qa2, E294; reflexivity
| tjt_clrmod; exact (tj_snp_consts _ _ HRODc)
| tjt_clrmod; eapply Forall_impl; [|exact tj_snp_cr]; intros r Hr; cbv beta in *; unfold IMG_LO, IMG_TOP in Hr; clear - Hr; lia
| tjt_clrmod; eapply Forall_impl; [|exact tj_snp_cr]; intros r Hr; cbv beta in *; unfold IMG_LO, IMG_TOP in Hr; unfold snp_out;
  tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia_with Hr)
| tjt_clrmod; exact HG1
| tjt_clrmod; exact HG2
| gliam | gliam | gliam | gliam
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; apply (tjt_fmt 53 tj_f_owned _ _ _ _ _ _ Hs53 HARc HRODc);
  change (Z.of_nat (length tj_f_owned)) with 11; cbv [A_OBJ Nat.add]; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; exact (tj_ro_fmt_rng 53 tj_f_owned Hs53 ltac:(cbv; glia))
| tjt_clrmod; unfold tj_f_owned; discriminate
| tjt_clrmod; reflexivity
| tjt_clrmod; repeat (apply Forall_cons; [exact I|]); apply Forall_nil
| tjt_clrmod; split; [reflexivity | intros j Hj; cbn in Hj; clear - Hj; lia]
| tjt_clrmod; cbn; glia
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; cbn [pf_args_asan map app]; split; [|exact I]; rewrite A3;
  apply (tjt_strarg kw sw _ _ _ _ _ _ Hsw HARc HRODc); unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; cbn [map app SnFF.pf_args_amem]; rewrite A3; split; [|exact I]; exact (tj_ro_amem8 kw sw Hsw)
| tjt_clrmod; cbn; rewrite app_nil_r; reflexivity
| gliam
| tjt_clrmod; rewrite length_app; cbn [length]; glia
| gliam
| gliam
| tjt_clrmod; unfold snp_out; cbn [pairwise];
  split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]
| tjt_clrmod; intros a Ha; split; [|glia_with Ha]; right; left; split;
  [ exists (buf, buf + cap); split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; glia_with Ha]
  | exists buf, Nb; split; [exact Hinb | glia_with Ha] ]
| tjt_clrmod; apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia
| tjt_clrmod; apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia
| tjt_clrmod; apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia
| tjt_clrmod; eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | glia | glia]
| exact Hfrm
| idtac ].
intros fx1 regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by glia.
rewrite HSNP in Hfr.
reseat HS HJ2 HP2 [1; 2; 3; 4; 5; 6; 7; 8]%nat AG ltac:(idtac; tjt_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx1) in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx1) B LAWS). pose (RUNTO := paj_run_to (fx := fx1) B LAWS).
pose (BR := paj_branch (fx := fx1) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx1) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx1) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx1) B LAWS).
prreg HS (10%bv : bv 5) Qr0.
cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
assert (HL1 : Z.of_nat (length ([44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw)) = 9 + Z.of_nat (length sw))
  by (rewrite length_app; cbn [length]; glia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (U0 : U Ev (SOff 863 0) = 9 + Z.of_nat (length sw)) by (rewrite <- HL1; apply U_atom; [exact Qr0 | rewrite HL1; glia]);
  assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 852 0) (SLit (-1)))) = cap - L)
  by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap ltac:(rewrite (AG 13%nat) by glia; exact F13)), (U_atom Ev 852 L E852) by glia; rewrite U_SLit; apply tjt_sub; [reflexivity | glia | glia]) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 863 (mkAF 0 2147483647 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qr0, unsigned_lit_small by (rewrite HL1; glia); rewrite Z.pow_0_r, Z.mod_1_r; rewrite HL1; glia)) as HS3 end.
clear HS; rename HS3 into HS; norm_ss HS.
destruct (al_frames _ _ LAWS ly3 S3 W3 _ _ 2 fpos (proj1 HJ2) Hfin) as (_ & _ & _ & HFSp2).
change (fs_frame_bytes 2) with 256 in HFSp2. rewrite EFA in HFSp2. fold F in HFSp2.
unfold shadow_addr in HFSp2. rewrite <- SB_SHADOW_OFF in HFSp2.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (Hp529 : forall o, 0 <= o < 32 -> apresent (w_H W3) (ms_mem msx) (SB + F / 8 + o))
  by (intros o Ho; cbn [ms_mem mkst]; apply (proj1 (HFSp2 o ltac:(change (256 / 8) with 32; glia)))) end.
tjt_rw32 HS E529 Hp529.
paj_run_shc RUNP RUNC HS HJ2; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ].
psrr_branch_pi RUNP BR HS.
lazymatch type of Hc with
| _ = true =>
  rewrite branch_geu_U, U0, U4 in Hc; apply negb_true_iff, Z.ltb_ge in Hc;
  paj_run_to_shc RUNTOP HS HJ2 0x6274; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ];
  prreg HS (23%bv : bv 5) R23;
  ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
  ra_join_val HS 640%nat 13%nat R23 E653;
  hei_havoc HS; rebaseE HS AG HEv; clear HEv;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx1 Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end;
  [ exact HBASE
  | unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg;
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; clear - Hn Hn33; lia]|];
    split; [exact E60|]; split; [exact E516|]; split; [exact E528|]; split; [exact E529 | assumption]
  | cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]; exact HJ2
  | cbn [c_S c_fpos]; exact HFR
  | unfold INV_tjX; cbn [c_cap c_T c_now c_buf c_ly c_S];
    assert (Hcl : cap <= tj_len T now)
    by (unfold tj_len; rewrite Htxt; unfold tj_after4, tj_e; cbn [c_T c_now];
        rewrite !length_app; unfold P5, key, k_owned; rewrite Hotxt; rewrite !length_app; cbn [length]; unfold L in Hc; glia_with Hc);
    split; [glia|]; split; [exact Hperm|]; exists (-1); split;
    [ rewrite E653; apply bv_eq; unfold w64; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity |];
    split; [intros; glia|]; split; [intros _ Hlt; exfalso; glia | intros _ _; reflexivity]
  | exact HS ]
| _ = false => idtac
end.
rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hb1.
gadd (conj Hb1 HL1).
assert (HGb2 : garr8 SEGS (mrestrict (w_H W3) mem2) buf (acc ++ ([44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ [0]))
by (apply (tjt_garr8_snp (w_H W3) _ mem2 buf acc ([44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) (cap - L) HGb);
    [ rewrite HL1; unfold L in Hb1; glia | exact Hwr | exact Hnul | intros a Ha; apply Hfr; glia_with Ha ]).
clear HGb.
assert (HLb2 : Z.of_nat (length (acc ++ ([44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ [0])) <= cap)
by (rewrite !length_app; cbn [length]; rewrite !Nat2Z.inj_add; fold L; glia).
gadd HLb2.
tjt_gk HGb2 AG.
paj_run_shc RUNP RUNC HS HJ2; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ].
tjt_gk HGb2 AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UA2 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0) (SOff 852 0)) (SOff 863 0)) = buf + L + (9 + Z.of_nat (length sw)))
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite U0, (U_atom _ 12 buf (eq_trans (AG 12%nat ltac:(glia)) F12)), (U_atom _ 852 L E852) by glia;
rewrite (zcanon_id (buf + L)) by (unfold M64; glia); apply zcanon_id; unfold M64; glia) end.
psrr_branch_pi RUNP BR HS.
lazymatch type of Hc with
| _ = true => exfalso; rewrite branch_ltu_U, UA2, (U_atom _ 12 buf (eq_trans (AG 12%nat ltac:(glia)) F12)) in Hc by glia;
  apply Z.ltb_lt in Hc; glia_with Hc
| _ = false => clear Hc
end.
paj_run_shc RUNP RUNC HS HJ2; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ].
tjt_gk HGb2 AG.
pose (age := tj_age (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
fold age in E741.
assert (Hage : 0 <= age < 10 ^ 19)
by (unfold age, tj_age; cbn [c_now c_T]; pose proof (tjt_u8 T (48 * i + 40) ltac:(rewrite HlenT; glia)) as Hl8;
    unfold age_of, disco_table_c.last_of;
    destruct (disco_table_c.u_at T (48 * i + 40) 8 <? now) eqn:Elt;
    [apply Z.ltb_lt in Elt; split; [apply Z.div_pos; glia | apply Z.div_lt_upper_bound; glia] | glia]).
assert (HT2len : (length (pf_udec age) <= 20)%nat) by (rewrite tjt_udec_eq, <- (tj_lemmas.dec_udec age Hage); apply tj_lemmas.dec_len).
gadd (conj HT2len Hage).
pose proof (proj1 HJ2) as HARc2.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HRODc2.
destruct (tj_snp_canary _ _ _ _ _ HARc2) as (cval2 & HG12 & HG22).
pose proof Hs54 as (_ & _ & H54lo & H54hi & _). unfold IMG_LO, IMG_TOP in H54lo, H54hi. cbv [A_OBJ Nat.add] in H54lo, H54hi.
change (Z.of_nat (length tj_f_age)) with 15 in H54lo, H54hi.
gadd (conj H54lo H54hi).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HEv := rnHEI Ev in pose proof (img_env_atomP Ev 295 HEv ltac:(unfold A_TEXT, A_LIM; glia)) as E295 end.
rregU HS (10%bv : bv 5) (buf + (L + (9 + Z.of_nat (length sw)))) ltac:(rewrite UA2; glia) Ra02.
rregU HS (11%bv : bv 5) (cap - (L + (9 + Z.of_nat (length sw))))
ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom _ 13 cap (eq_trans (AG 13%nat ltac:(glia)) F13)), (U_atom _ 852 L E852), U0, !U_SLit by glia;
rewrite (tjt_sub cap L) by (first [reflexivity | glia]); rewrite tjt_sub by (first [reflexivity | glia]); glia) Ra12.
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2.
prreg HS (1%bv : bv 5) Qra2. prreg HS (12%bv : bv 5) Qa22. prreg HS (13%bv : bv 5) Qa32.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (A3g : argZ (ms_regs msx) 3 = age)
by (lazymatch type of Qa32 with getr ?rg _ = ?v =>
change (bv_unsigned (getr rg (Z_to_bv 5 (10 + 3))) = age);
replace (getr rg (Z_to_bv 5 (10 + 3))) with v by (rewrite <- Qa32; reflexivity) end;
rewrite E741; apply unsigned_lit_small; glia) end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fx1 GC GV IMGLO IMGHI CR (SIGMA AS___interceptor_trampoline_snprintf)
(eq_ind_r (fun p => SnprintfDefR.sh_asnprintf_realizesR (fx := fx1) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR p) (ASNP fx1) HSNPC)
W3 (ms_regs msX) (ms_mem msX) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k
(buf + (L + (9 + Z.of_nat (length sw)))) (cap - (L + (9 + Z.of_nat (length sw)))) (VAL 295) tj_f_age
ltac:(let v := eval vm_compute in (pf_parse tj_f_age) in lazymatch v with Some ?p => exact p end)
[] (map (argZ (ms_regs msX)) [3; 4; 5; 6; 7] ++ []) [AU64 age] ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125])
cval2 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24760)) _ HJ2 HRODc2) end;
[ tjt_clrmod; unfold spZ at 1; rewrite Qsp2, E60, unsigned_lit_small by glia; glia
| tjt_clrmod; exact Ho16
| gliam
| gliam
| tjt_clrmod; rewrite Qgp2, (AG 3%nat) by glia; rewrite (HE0 3%nat 3%bv eq_refl); exact Hgp
| tjt_clrmod; rewrite Qtp2, (AG 4%nat) by glia; rewrite (HE0 4%nat 4%bv eq_refl); exact Htp
| tjt_clrmod; exact Qra2
| tjt_clrmod; apply ret_ok_codeptr_v; [glia | reflexivity]
| tjt_clrmod; exact Ra02
| tjt_clrmod; exact Ra12
| tjt_clrmod; rewrite Qa22, E295; reflexivity
| tjt_clrmod; exact (tj_snp_consts _ _ HRODc2)
| tjt_clrmod; eapply Forall_impl; [|exact tj_snp_cr]; intros r Hr; cbv beta in *; unfold IMG_LO, IMG_TOP in Hr; clear - Hr; lia
| tjt_clrmod; eapply Forall_impl; [|exact tj_snp_cr]; intros r Hr; cbv beta in *; unfold IMG_LO, IMG_TOP in Hr; unfold snp_out;
  tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia_with Hr)
| tjt_clrmod; exact HG12
| tjt_clrmod; exact HG22
| gliam | gliam | gliam | gliam
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; apply (tjt_fmt 54 tj_f_age _ _ _ _ _ _ Hs54 HARc2 HRODc2);
  change (Z.of_nat (length tj_f_age)) with 15; cbv [A_OBJ Nat.add]; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; exact (tj_ro_fmt_rng 54 tj_f_age Hs54 ltac:(cbv; glia))
| tjt_clrmod; unfold tj_f_age; discriminate
| tjt_clrmod; reflexivity
| tjt_clrmod; repeat (apply Forall_cons; [exact I|]); apply Forall_nil
| tjt_clrmod; split; [reflexivity | intros j Hj; cbn in Hj; clear - Hj; lia]
| tjt_clrmod; cbn; glia
| tjt_clrmod; unfold snp_out; tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia)
| tjt_clrmod; cbn [pf_args_asan map app]; split; [cbn [pf_arg_asan]; exact A3g | exact I]
| tjt_clrmod; cbn [map app SnFF.pf_args_amem]; exact I
| tjt_clrmod; reflexivity
| gliam
| tjt_clrmod; rewrite !length_app; cbn [length]; glia
| gliam
| gliam
| tjt_clrmod; unfold snp_out; cbn [pairwise];
  split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]
| tjt_clrmod; intros a Ha; split; [|glia_with Ha]; right; left; split;
  [ exists (buf, buf + cap); split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; glia_with Ha]
  | exists buf, Nb; split; [exact Hinb | glia_with Ha] ]
| tjt_clrmod; apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); glia
| tjt_clrmod; apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); glia
| tjt_clrmod; apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); glia
| tjt_clrmod; eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc2 | exact Hinb | glia | glia]
| exact Hf2
| idtac ].
intros fx2 regs3 mem3 md3c Hg1 Hg2 HJ3x HP3x Ha03 Hwr3 Hnul3 Hfr3 Hpres3x Hsame3.
assert (Hh1 : forall r : bv 5, bv_unsigned r <> 10 -> Sem.reg_get (@fp_regs fx2) r = Sem.reg_get (@fp_regs fq) r)
by (intros r Hr; rewrite (Hg1 r Hr); exact (Hf1 r Hr)).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr3 by glia.
rewrite HSNP in Hfr3.
reseat HS HJ3x HP3x [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tjt_kept AG Hfr3 Hpres3x).
apply (st_ok_pi_restrict_fx _ fx2) in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx2) B LAWS). pose (RUNTO := paj_run_to (fx := fx2) B LAWS).
pose (BR := paj_branch (fx := fx2) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx2) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx2) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx2) B LAWS).
prreg HS (10%bv : bv 5) Qr03. cbn [ms_regs] in Qr03. rewrite Ha03 in Qr03. symmetry in Qr03. unfold w64 in Qr03.
assert (HL2 : Z.of_nat (length ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125])) = 11 + Z.of_nat (length (pf_udec age)))
by (rewrite !length_app; cbn [length]; glia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U03 : U Ev (SOff 879 0) = 11 + Z.of_nat (length (pf_udec age))) by (rewrite <- HL2; apply U_atom; [exact Qr03 | rewrite HL2; glia]);
assert (U43 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 852 0) (SLit (-1)))) (SMd M_MUL (SOff 863 0) (SLit (-1)))) = cap - (L + (9 + Z.of_nat (length sw))))
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom _ 13 cap (eq_trans (AG 13%nat ltac:(glia)) F13)), (U_atom _ 852 L E852), (U_atom _ 863 _ Qr0), HL1, !U_SLit by (rewrite ?HL1; glia);
rewrite (tjt_sub cap L) by (first [reflexivity | glia]); rewrite tjt_sub by (first [reflexivity | glia]); glia) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 879 (mkAF 0 2147483647 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Qr03, unsigned_lit_small by (rewrite HL2; glia); rewrite Z.pow_0_r, Z.mod_1_r; rewrite HL2; glia)) as HS3 end.
clear HS; rename HS3 into HS; norm_ss HS.
paj_run_shc RUNP RUNC HS HJ3x; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ].
psrr_branch_pi RUNP BR HS.
lazymatch type of Hc with
| _ = true =>
  rewrite branch_geu_U, U03, U43 in Hc; apply negb_true_iff, Z.ltb_ge in Hc;
  paj_run_to_shc RUNTOP HS HJ3x 0x6274; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ];
  prreg HS (23%bv : bv 5) R23;
  ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
  ra_join_val HS 640%nat 13%nat R23 E653;
  hei_havoc HS; rebaseE HS AG HEv; clear HEv;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k ly3 S3 Wg msF mdF Hh1 Hg2) end end;
  [ exact HBASE
  | unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg;
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; clear - Hn Hn33; lia]|];
    split; [exact E60|]; split; [exact E516|]; split; [exact E528|]; split; [exact E529 | assumption]
  | cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]; exact HJ3x
  | cbn [c_S c_fpos]; exact HFR
  | unfold INV_tjX; cbn [c_cap c_T c_now c_buf c_ly c_S];
    assert (Hcl : cap <= tj_len T now)
    by (unfold tj_len; rewrite Htxt; unfold tj_after4, tj_e; cbn [c_T c_now];
        rewrite !length_app; unfold P5, P6, key, k_owned, k_age_ms; rewrite Hotxt;
        change (dec (age_of now (e_last_seen (reac_disco_table_json_c.tj_entry T i)))) with (dec age);
        rewrite (tj_lemmas.dec_udec age Hage), <- tjt_udec_eq; rewrite !length_app; cbn [length]; unfold L in Hc; glia_with Hc);
    split; [glia|]; split; [exact Hperm|]; exists (-1); split;
    [ rewrite E653; apply bv_eq; unfold w64; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity |];
    split; [intros; glia|]; split; [intros _ Hlt; exfalso; glia | intros _ _; reflexivity]
  | exact HS ]
| _ = false => idtac
end.
rewrite branch_geu_U, U03, U43 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hb2.
gadd (conj Hb2 HL2).
rewrite app_assoc in HGb2.
assert (HGb3 : garr8 SEGS (mrestrict (w_H W3) mem3) buf ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]) ++ [0]))
by (apply (tjt_garr8_snp (w_H W3) _ mem3 buf (acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]) (cap - (L + (9 + Z.of_nat (length sw)))) HGb2);
    [ rewrite HL2; glia
    | intros j Hj; replace (buf + Z.of_nat (length (acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw)) + j) with (buf + (L + (9 + Z.of_nat (length sw))) + j)
      by (rewrite length_app, Nat2Z.inj_add, HL1; fold L; glia); apply Hwr3; exact Hj
    | replace (buf + Z.of_nat (length (acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw))) with (buf + (L + (9 + Z.of_nat (length sw))))
      by (rewrite length_app, Nat2Z.inj_add, HL1; fold L; glia); exact Hnul3
    | intros a Ha; rewrite length_app, Nat2Z.inj_add, HL1 in Ha; fold L in Ha; apply Hfr3; glia_with Ha ]).
clear HGb2.
assert (HLb3 : Z.of_nat (length ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]) ++ [0])) <= cap)
by (rewrite !length_app; cbn [length]; rewrite !Nat2Z.inj_add; fold L; glia).
gadd HLb3.
tjt_gk HGb3 AG.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 900 Ev ssv msv [Z_to_bv 64 (disco_table_c.n_of T)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 900%nat [Z_to_bv 64 (disco_table_c.n_of T)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E900 : ew Ev 900 = Z_to_bv 64 (disco_table_c.n_of T))
by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 (disco_table_c.n_of T)] 0 (Z_to_bv 64 0) ltac:(cbn; glia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 900 (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E900, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia)) as HS3 end.
clear HS; rename HS3 into HS; norm_ss HS.
pose proof (tjt_keep_journal _ _ _ _ _ _ _ _ HBASE HJ3x) as HKn. unfold tj_keep, afobj in HKn. cbn [c_t c_T c_ly c_S] in HKn.
destruct HKn as (_ & HGn & (_ & _ & HRAn)).
pose proof (tjt_vm _ t T 384 4 HGn ltac:(glia) ltac:(rewrite HlenT; glia)) as Hvmn.
assert (Hun : disco_table_c.u_at T 384 4 = disco_table_c.n_of T)
by (apply tjt_s32; [glia | reflexivity | unfold disco_table_c.sub; rewrite length_firstn, length_skipn; glia]).
rewrite Hun in Hvmn.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 900 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite (eq_trans (AG 10%nat ltac:(glia)) F10); rewrite unsigned_lit_small by glia; split; [glia|]; split; [glia|]; split; [intros o Ho; glia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ t 384 4 (SOff 900 0) (disco_table_c.n_of T)); [cbn [sv_denot]; rewrite E900, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hvmn])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTF Htlo Ht400 Hi HT1 HTb0;
repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_ss HS.
try clear SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msx) => shok_auto SHOK (SOff 32 0) Ev (mrestrict (w_H Wx) (ms_mem msx)) end.
paj_run_tok RUN HS HJ3x SHOK Bspan.
first [ solve [tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0] | idtac ].
lazymatch goal with
| |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) (ms_mem ?msx))) _ _ _ =>
  let HKc := fresh "HKc" in pose proof (tjt_keep_journal _ _ _ _ _ _ _ _ HBASE HJ3x) as HKc;
  unfold tj_keep, afobj in HKc; cbn [c_t c_T c_ly c_S] in HKc; destruct HKc as (_ & _ & (_ & _ & HRAc));
  change (rd_of SEGS (mrestrict (w_H Wx) (ms_mem msx))) with (aview SEGS (w_H Wx) (ms_mem msx));
  rewrite (U_atom _ 32 SB (eq_trans (AG 32%nat ltac:(glia)) HE032)) by (unfold SB; glia);
  rewrite (U_atom_off _ 10 t 384 (eq_trans (AG 10%nat ltac:(glia)) F10)) by glia;
  rewrite SB_SHADOW_OFF; apply (range_addressable_sub _ SHADOW_OFF t 400); [exact HRAc | glia | glia]
| _ => idtac end.
tjt_gk HGb3 AG.
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ => assert (HEIn3 : img_env VAL A_LIM Enew) by (repeat apply img_env_ewset_hi; first [assumption | unfold A_LIM; glia]) end.
rebaseE HS AG HEv. clear HEv.
assert (HP5 : P5 (reac_disco_table_json_c.tj_entry T i) = [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw)
by (unfold P5, key, k_owned; rewrite Hotxt; reflexivity).
assert (HP6 : P6 now (reac_disco_table_json_c.tj_entry T i) = [44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125])
by (unfold P6, key, k_age_ms; change (dec (age_of now (e_last_seen (reac_disco_table_json_c.tj_entry T i)))) with (dec age);
rewrite (tj_lemmas.dec_udec age Hage), <- tjt_udec_eq; reflexivity).
assert (Htxt2 : reac_disco_table_json_c.tj_text T now = ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125])) ++ tj_lemmas.tj_rest T now (i + 1))
by (rewrite Htxt; unfold tj_after4, tj_e; cbn [c_T c_now]; rewrite HP5, HP6, <- !app_assoc; reflexivity).
assert (Hacc2 : Z.of_nat (length ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]))) = L + (9 + Z.of_nat (length sw)) + (11 + Z.of_nat (length (pf_udec age))))
by (rewrite !length_app; cbn [length]; rewrite !Nat2Z.inj_add; fold L; glia).
psrr_branch_tok RUN BR HS SHOK Bspan.
lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
assert (Ua4 : U Ev a = i + 1) by (rewrite (U_atom_off Ev 722 i 1 E722) by glia; reflexivity);
assert (Ua1 : U Ev b = disco_table_c.n_of T) by (apply (U_atom Ev 900); [exact E900 | glia]) end.
rewrite (tjt_blt _ _ _ (i + 1) (disco_table_c.n_of T) Ua4 Ua1) in Hc by glia.
lazymatch type of Hc with
| _ = true =>
  apply Z.ltb_lt in Hc;
  paj_run_to_shc RUNTOP HS HJ3x 23700; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ];
  tjt_gk HGb3 AG;
  destruct (al_frames _ _ LAWS ly3 S3 W3 _ _ 2 fpos (proj1 HJ3x) Hfin) as (_ & _ & _ & HFSp3);
  change (fs_frame_bytes 2) with 256 in HFSp3; rewrite EFA in HFSp3; fold F in HFSp3; unfold shadow_addr in HFSp3; rewrite <- SB_SHADOW_OFF in HFSp3;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (Hp529c : forall o, 0 <= o < 32 -> apresent (w_H W3) (ms_mem msx) (SB + F / 8 + o))
  by (intros o Ho; cbn [ms_mem mkst]; apply (proj1 (HFSp3 o ltac:(change (256 / 8) with 32; glia)))) end;
  tjt_rw32 HS E529 Hp529c;
  rregU HS (19%bv : bv 5) (48 * (i + 1)) ltac:(rewrite (U_atom_off _ 721 (48 * i) 48 E721) by glia; glia) R19;
  rregU HS (14%bv : bv 5) (i + 1) ltac:(rewrite (U_atom_off _ 722 i 1 E722) by glia; reflexivity) R14;
  rregU HS (26%bv : bv 5) (L + (9 + Z.of_nat (length sw)) + (11 + Z.of_nat (length (pf_udec age))))
  ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 852 L E852), (U_atom _ 863 _ Qr0), HL1, (U_atom _ 879 _ Qr03), HL2 by (rewrite ?HL1, ?HL2; glia);
  rewrite (zcanon_id (L + (9 + Z.of_nat (length sw)))) by (unfold M64; glia); apply zcanon_id; unfold M64; glia) R26;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let tg := eval red in ss_tjL in
  let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
  let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
  pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3 end;
  clear HS; rename HS3 into HS; norm_ss HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let vals := eval cbn [map ms_regs restrict] in (map (fun r : bv 5 => getr (ms_regs msx) r) ([19; 14]%bv : list (bv 5))) in
  pose proof (st_ok_pi_havoc_hi 910 Ex ssx msx vals HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; set_regs_rec HS 910%nat vals 0%nat ([19; 14]%bv : list (bv 5)) end;
  hei_havoc HS; rebaseE HS AG HEv; clear HEv;
  ra_join HS ss_tjL 720%nat ([1; 19; 14; 5; 6; 7; 10; 11; 12; 15; 16; 17; 23; 26; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
  ra_join_val HS 720%nat 1%nat R19 E721n;
  ra_join_val HS 720%nat 2%nat R14 E722n;
  ra_join_val HS 720%nat 13%nat R26 E733n;
  hei_havoc HS; rebaseE HS AG HEv; clear HEv;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (tj_from0_at_fx B IMG _ _ FL (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k ly3 S3 Wg msF mdF Hh1 Hg2) end end;
  [ exact HBASE
  | unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg;
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; clear - Hn Hn33; lia]|];
    split; [exact E60|]; split; [exact E516|]; split; [exact E528|]; split; [exact E529 | assumption]
  | cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]; exact HJ3x
  | cbn [c_S c_fpos]; exact HFR
  | unfold INV_tjL; cbn [c_cap c_T c_now c_buf c_ly c_S];
    split; [glia|]; split; [exact Hperm|]; split; [exact (tjt_keep_journal _ _ _ _ _ _ _ _ HBASE HJ3x)|];
    split; [glia|]; split; [glia|]; split; [unfold w64; exact E721n|]; split; [unfold w64; exact E722n|];
    exists ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]));
    split; [unfold w64; rewrite E733n, Hacc2; reflexivity|];
    split; [rewrite Hacc2; glia|];
    split; [exact Htxt2|];
    rewrite <- app_assoc; exact HGb3
  | exact HS ]
| _ = false =>
  apply Z.ltb_ge in Hc;
  assert (Hin1 : i + 1 = disco_table_c.n_of T) by glia;
  paj_run_to_shc RUNTOP HS HJ3x 25076; [ tjt_awr ltac:(idtac; tjt_hd AG HSK) AG fpos F EFA0 | ];
  tjt_gk HGb3 AG;
  destruct (al_frames _ _ LAWS ly3 S3 W3 _ _ 2 fpos (proj1 HJ3x) Hfin) as (_ & _ & _ & HFSp3);
  change (fs_frame_bytes 2) with 256 in HFSp3; rewrite EFA in HFSp3; fold F in HFSp3; unfold shadow_addr in HFSp3; rewrite <- SB_SHADOW_OFF in HFSp3;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (Hp529c : forall o, 0 <= o < 32 -> apresent (w_H W3) (ms_mem msx) (SB + F / 8 + o))
  by (intros o Ho; cbn [ms_mem mkst]; apply (proj1 (HFSp3 o ltac:(change (256 / 8) with 32; glia)))) end;
  tjt_rw32 HS E529 Hp529c;
  rregU HS (26%bv : bv 5) (L + (9 + Z.of_nat (length sw)) + (11 + Z.of_nat (length (pf_udec age))))
  ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 852 L E852), (U_atom _ 863 _ Qr0), HL1, (U_atom _ 879 _ Qr03), HL2 by (rewrite ?HL1, ?HL2; glia);
  rewrite (zcanon_id (L + (9 + Z.of_nat (length sw)))) by (unfold M64; glia); apply zcanon_id; unfold M64; glia) R26;
  ra_join HS ss_tjC 680%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac;
  ra_join_val HS 680%nat 15%nat R26 E695n;
  hei_havoc HS; rebaseE HS AG HEv; clear HEv;
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (tj_from0_at_fx B IMG _ _ FC (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx2 Ev k ly3 S3 Wg msF mdF Hh1 Hg2) end end;
  [ exact HBASE
  | unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg;
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; clear - Hn Hn33; lia]|];
    split; [exact E60|]; split; [exact E516|]; split; [exact E528|]; split; [exact E529 | assumption]
  | cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]; exact HJ3x
  | cbn [c_S c_fpos]; exact HFR
  | unfold INV_tjC; cbn [c_cap c_T c_now c_buf c_ly c_S];
    split; [glia|]; split; [exact Hperm|]; split; [exact (tjt_keep_journal _ _ _ _ _ _ _ _ HBASE HJ3x)|]; split; [glia|];
    exists ((acc ++ [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ sw) ++ ([44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec age ++ [125]));
    split; [unfold w64; rewrite E695n, Hacc2; reflexivity|];
    split; [rewrite Hacc2; glia|];
    split; [rewrite Htxt2, Hin1, (tj_lemmas.tj_rest_end T now) by glia; reflexivity|];
    rewrite <- app_assoc; exact HGb3
  | exact HS ]
end.
Qed.
Set Default Goal Selector "1".
End h.
End f.
End d.
