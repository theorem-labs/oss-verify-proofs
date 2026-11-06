(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CheckGroupaWalk.v, with its module paths and module names changed; 906 of its 982 lines of code are new or changed and 1111 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YO0c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tj_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tj_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tj_awr_rec hd AG fpos F EFA :=
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
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tj_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tj_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tj_awr: no rule for the head region" ];
tj_awr_rec hd AG fpos F EFA
end.
Ltac tj_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tj_awr_rec hd AG fpos F EFA.
Ltac tj_kb_lia Hx KB :=
clear - Hx KB; repeat match goal with H : _ /\ _ |- _ => destruct H end;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia.
Ltac tj_kb0 KB :=
clear - KB; repeat match goal with H : _ /\ _ |- _ => destruct H end;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia.
Ltac tj_buf_out AG KB :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let x := fresh "x" in let Hx := fresh "Hx" in
intros rg Hin x Hx;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; evalE AG; tj_kb_lia Hx KB
| ]);
destruct Hin.
Ltac tj_keepg lem HFx H AG KB name :=
pose proof (lem _ _ _ _ _ _ HFx H) as name;
lazymatch type of name with ?P1 -> ?P2 -> ?P3 -> _ =>
let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
assert (h1 : P1) by (tj_kb0 KB); assert (h2 : P2) by (cbn [Z.of_nat Pos.of_succ_nat]; tj_kb0 KB);
assert (h3 : P3) by (tj_buf_out AG KB); specialize (name h1 h2 h3); clear h1 h2 h3 end.
Ltac tj_keepv lem HFx H AG KB name :=
pose proof (lem _ _ _ _ _ _ _ HFx H) as name;
lazymatch type of name with ?P1 -> ?P2 -> ?P3 -> _ =>
let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
assert (h1 : P1) by (tj_kb0 KB); assert (h2 : P2) by (cbn [Z.of_nat Pos.of_succ_nat]; tj_kb0 KB);
assert (h3 : P3) by (tj_buf_out AG KB); specialize (name h1 h2 h3); clear h1 h2 h3 end.
Ltac tj_kb_lia2 Hx KB Hb :=
clear - Hx KB Hb; repeat match goal with H : _ /\ _ |- _ => destruct H end;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia.
Ltac tj_nowin AG KB Hb :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; tj_kb_lia2 Hrg KB Hb
| ]);
destruct Hin.
Ltac tj_rw529 HS E529 Hp :=
lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let Hw := fresh "Hw" in
assert (Hw : forall o, 0 <= o < 32 -> writable_at sg (ms_mem msx) (base_val Ex (YP09.r_base r) + o));
[ let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
  cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529;   rewrite unsigned_lit_small by (unfold SB; lia);   apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;   apply (proj1 (Hp o ltac:(change (fs_frame_bytes 2 / 8) with 32; lia)))
| ];
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) Hw)) as HS3;
clear HS Hw; rename HS3 into HS; norm_ss HS end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Definition tj_rbn_rng (q n : Z) : Prop :=
forall x, q <= x < q + n -> in_roP SEGS pa_relro_lo pa_relro_hi x.
Definition tj_rbn_str (q sz : Z) (s : list Z) : Prop :=
In (q, sz) tfib_globs /\ tj_rbn_rng q sz /\ Z.of_nat (length s) + 1 <= sz /\
IMG_LO + 64 <= q /\ q + sz + 64 <= IMG_TOP /\
Forall (fun c => 0 < c < 256) s /\ tj_rom_bytes q (s ++ [0]) /\
(forall x, q + Z.of_nat (length s) < x < q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8 ->
seg_rom SEGS (Z_to_bv 64 x) <> None).
Definition tj_rbn_word (a v : Z) : Prop :=
forall k, (k < 8)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)).
Definition tj_rbn_rom : Prop :=
tj_rbn_rng MC_CONSTS_LO (MC_CONSTS_HI - MC_CONSTS_LO) /\
exists t1 t2 t3 : Z,
VAL (A_OBJ 26) mod 8 = 0 /\ In (VAL (A_OBJ 26), 24) tfib_globs /\ tj_rbn_rng (VAL (A_OBJ 26)) 24 /\
IMG_LO + 64 <= VAL (A_OBJ 26) /\ VAL (A_OBJ 26) + 24 + 64 <= IMG_TOP /\
tj_rbn_word (VAL (A_OBJ 26)) t1 /\ tj_rbn_word (VAL (A_OBJ 26) + 8) t2 /\ tj_rbn_word (VAL (A_OBJ 26) + 16) t3 /\
tj_rbn_str t1 7 (bn_STEM 1) /\ tj_rbn_str t2 7 (bn_STEM 2) /\ tj_rbn_str t3 8 (bn_STEM 3) /\
tj_rbn_str (VAL (A_OBJ 27)) 5 (bn_STEM 0) /\
tj_rbn_str (VAL (A_OBJ 28)) 3 [32; 40] /\
tj_rbn_str (VAL (A_OBJ 29)) 7 [32; 105; 110; 32; 47; 32] /\
tj_rbn_str (VAL (A_OBJ 30)) 6 [32; 111; 117; 116; 41].
Lemma tj_mbyte_of_aview : forall (H : word -> bool) (mem : word -> option byte) x (b : byte),
aview SEGS H mem x = Some (bv_unsigned b) -> mbyte SEGS (mrestrict H mem) x = Some b.
Proof.
intros H mem x b Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) x) as [b'|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma tj_aview_pres : forall H (mem : word -> option byte) a, apresent H mem a -> aview SEGS H mem a <> None.
Proof. intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. cbv beta. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma tj_aview0_of_chunk : forall E H (mem : word -> option byte) b cs lo hi wlo whi j,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 529%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 529) = b -> In (YP09.mkChunk j (CVal 1 (SLit 0))) cs ->
aview SEGS H mem (b + j) = Some 0.
Proof.
intros E H mem b cs lo hi wlo whi j HR Hb Hin.
pose proof (field_of_region E (mrestrict H mem) 529 b cs lo hi wlo whi j 1%N (SLit 0) 0 HR Hb Hin eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
specialize (Hv 0%nat ltac:(cbn; lia)). cbn [Z.of_nat N.to_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. vm_compute. reflexivity.
Qed.
Lemma tj_ra_frame : forall (rd : Z -> option Z) F a n j0,
F mod 8 = 0 -> a = F + 8 * j0 -> 0 <= n ->
(forall j, j0 <= j < j0 + (n + 7) / 8 -> rd (SB + F / 8 + j) = Some 0) ->
range_addressable rd SHADOW_OFF a n.
Proof.
intros rd F a n j0 HF Ha Hn Hz x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia.
apply Hz. subst a. lia.
Qed.
Lemma tj_hull_frame : forall (rd : Z -> option Z) F b n,
F mod 32 = 0 -> 0 < n -> F + 32 <= b -> b + n <= F + 224 ->
(forall o, 0 <= o < 32 -> rd (SB + F / 8 + o) <> None) ->
shadow_hull_vis rd b n.
Proof.
intros rd F b n HF Hn Hb1 Hb2 Hp s Hs. unfold shadow_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs.
replace s with (SB + F / 8 + (s - SB - F / 8)) by lia. apply Hp.
unfold SB in *. lia.
Qed.
Lemma tj_acc_lens : forall f sd i o A n1 B0 n2 C n3,
reac_box_name_c.bn_accept f sd i o A n1 B0 n2 C n3 = true ->
bn_ret f sd i o = 0 /\ Z.of_nat (length (bn_NM f sd i o)) < n1 /\
Z.of_nat (length (bn_TK (bn_NM f sd i o))) < n2 /\ Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) < n3.
Proof.
intros f sd i o A n1 B0 n2 C n3 H. unfold reac_box_name_c.bn_accept in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1]. apply andb_prop in H as [_ H0].
apply Z.eqb_eq in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. auto.
Qed.
Lemma tj_rbn_wr_in : forall f i o F a,
rbn_wr f [] i o (F + 32) 24 (F + 96) 24 (F + 160) 48 a -> F + 32 <= a < F + 208.
Proof.
intros f i o F a (Hacc & Hr). destruct (tj_acc_lens _ _ _ _ _ _ _ _ _ _ Hacc) as (_ & L1 & L2 & L3). lia.
Qed.
Lemma tj_vm_keep : forall H H' (m m' : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v ->
(forall k, (k < n)%nat -> aview SEGS H' m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk k Hlt. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hk k Hlt)). exact (Hv k Hlt).
Qed.
Lemma tj_vm_frame : forall E rs (m m' : word -> option byte) a n v,
frame_of E rs m m' -> val_mem SEGS m a n v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall r, In r rs -> forall x, a <= x < a + Z.of_nat n ->
~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= x < base_val E (YP09.r_base r) + YP09.r_whi r)) ->
val_mem SEGS m' a n v.
Proof.
intros E rs m m' a n v HF Hv Ha Hb Hout k Hk.
rewrite (mbyte_of_frame_x SEGS E rs m m' (a + Z.of_nat k) HF ltac:(lia)); [exact (Hv k Hk)|].
intros r Hr. apply (Hout r Hr). lia.
Qed.
Lemma tj_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite YO0c.alu64_srl, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia.
change (3 mod 2 ^ 64 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (Z.mod_small (x / 8)); [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma tj_ro_img : forall q n x, tj_rbn_rng q n -> q <= x < q + n -> in_img SEGS x.
Proof.
intros q n x Hr Hx. destruct (Hr x Hx) as [(sg & Hs & _ & Hb) | Hrel].
- exists sg. split; [exact Hs | exact Hb].
- exact (pa_relro_img x Hrel).
Qed.
Lemma tj_garr8_kept : forall E rs (m m' : word -> option byte) a l,
frame_of E rs m m' -> garr8 SEGS m a l -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
(forall r, In r rs -> forall x, a <= x < a + Z.of_nat (length l) ->
~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= x < base_val E (YP09.r_base r) + YP09.r_whi r)) ->
garr8 SEGS m' a l.
Proof.
intros E rs m m' a l HF HG Ha Hb Hout. apply (garr8_frame SEGS m m' a l HG).
intros x Hx. apply (mbyte_of_frame_x SEGS E rs m m' x HF); [lia|].
intros r Hr. exact (Hout r Hr x Hx).
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis RBR : tj_rbn_rom.
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis RBN : treac_box_name_spec B.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tj_mc_consts : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem.
Proof.
intros W mem HRO a Ha. destruct RBR as (Hmc & _).
destruct (mc_consts_unowned a Ha) as (H1 & H2).
exact (HRO a (Hmc a ltac:(unfold MC_CONSTS_LO, MC_CONSTS_HI in *; lia)) H1 H2).
Qed.
Lemma tj_ro_aview : forall (W : world SEGS) mem q sz x,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
In (q, sz) tfib_globs -> tj_rbn_rng q sz -> q <= x < q + sz ->
aview SEGS (w_H W) mem x = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x)).
Proof.
intros W mem q sz x HRO Hin Hr Hx.
assert (Hr2 : In (q, sz) tfib_ro_ranges) by (unfold tfib_ro_ranges; apply in_or_app; left; exact Hin).
exact (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ q sz x HRO (Hr x Hx) (tfib_ro_unowned_at B q sz DRO Hr2) Hx).
Qed.
Lemma tj_word_ok : forall (W : world SEGS) mem q sz a v,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
In (q, sz) tfib_globs -> tj_rbn_rng q sz -> q <= a -> a + 8 <= q + sz ->
tj_rbn_word a v -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v.
Proof.
intros W mem q sz a v HRO Hin Hr H1 H2 Hw k Hk. apply tj_mbyte_of_aview.
rewrite (tj_ro_aview W mem q sz (a + Z.of_nat k) HRO Hin Hr ltac:(lia)), (Hw k Hk). reflexivity.
Qed.
Lemma tj_rbn_stem_ok : forall ly S (W : world SEGS) mem md q sz s,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_rbn_str q sz s -> rbn_stem B W mem q s.
Proof.
intros ly S W mem md q sz s HAR HRO (Hin & Hrng & Hlen & Hlo & Hhi & Hch & Hrom & Htl).
assert (Hq : 0 < q /\ q + sz + 64 <= IMG_TOP) by (unfold IMG_LO, IMG_TOP in *; lia).
destruct (ro_read_ok_glob _ _ tfib_globs ly S W mem md q sz q (Z.of_nat (length s) + 1) GM Hin HV HAR
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhv].
assert (HG : garr8 SEGS (mrestrict (w_H W) mem) q (s ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  assert (Hv : aview SEGS (w_H W) mem (q + Z.of_nat j) = Some (nth j (s ++ [0]) 0)).
  { rewrite (tj_ro_aview W mem q sz (q + Z.of_nat j) HRO Hin Hrng ltac:(lia)). apply Hrom.
    rewrite length_app. cbn [length]. lia. }
  exact (val_mem1_of_aview SEGS (w_H W) mem _ _ Hv). }
split; [|split].
2: { intros x Hx. split; [exact (tj_ro_img q sz x Hrng ltac:(lia))|].
  assert (Hr2 : In (q, sz) tfib_ro_ranges) by (unfold tfib_ro_ranges; apply in_or_app; left; exact Hin).
  exact (tfib_ro_unowned_at B q sz DRO Hr2 x ltac:(lia)). }
2: { intros x Hx. apply Htl. lia. }
refine (conj Hch (conj HG (conj _ (conj _ (conj _ (conj _ (conj Hra (conj Hhv _)))))))).
- lia.
- unfold IMG_TOP in *. lia.
- unfold IMG_TOP in *. lia.
- left. unfold kLowMemEnd, IMG_TOP in *. lia.
- intros x Hx. unfold aview, mbyte.
  destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)) as [b|]; [cbn [option_map]; discriminate|].
  pose proof (Htl x Hx) as Hn. destruct (seg_rom SEGS (Z_to_bv 64 x)) as [b|]; [cbn [option_map]; discriminate | contradiction].
Qed.
Lemma tj_rbn_lit_ok : forall (W : world SEGS) mem q s, rbn_stem B W mem q s -> rbn_lit W mem q s.
Proof.
intros W mem q s ((_ & HG & _ & _ & _ & _ & Hra & _) & Himg & _).
exact (conj HG (conj Hra (fun x Hx => proj1 (Himg x Hx)))).
Qed.
Lemma tj_rbn_img : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
rbn_img B W mem.
Proof.
intros ly S W mem md HAR HRO.
destruct RBR as (_ & t1 & t2 & t3 & H8 & Hin & Hrng & Hlo & Hhi & Hw1 & Hw2 & Hw3 & Hs1 & Hs2 & Hs3 & Hs0 & Hl28 & Hl29 & Hl30).
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs1) as St1.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs2) as St2.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs3) as St3.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs0) as St0.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl28)) as Lt28.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl29)) as Lt29.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl30)) as Lt30.
exists t1, t2, t3.
refine (conj H8 (conj _ (conj _ (conj _ (conj _ (conj _ (conj St1 (conj St2 (conj St3 (conj St0
(conj Lt28 (conj Lt29 (conj Lt30 (conj Hin (conj (proj1 Hs1) (conj (proj1 Hs2) (conj (proj1 Hs3)
(conj (proj1 Hs0) (conj (proj1 Hl28) (conj (proj1 Hl29) (proj1 Hl30))))))))))))))))))))).
- intros x Hx. exact (tj_ro_img _ _ x Hrng Hx).
- exact (ro_usable_glob _ _ tfib_globs ly S W mem md (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26)) 24 GM Hin HAR
(Z.le_refl _) (Z.le_refl _)).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26)) t1 HRO Hin Hrng ltac:(lia) ltac:(lia) Hw1).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26) + 8) t2 HRO Hin Hrng ltac:(lia) ltac:(lia) Hw2).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26) + 16) t3 HRO Hin Hrng ltac:(lia) ltac:(lia) Hw3).
Qed.
Lemma tj_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
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
Lemma tj_garr8_u1 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 1 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 1 (disco_table_c.u_at T k 1) /\ 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
intros m a k T HG Hk HkT.
assert (Hlen : length (disco_table_c.sub T k 1) = 1%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 1)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 1)) as H1. rewrite Hlen in H1.
split; [|unfold disco_table_c.u_at; change (2 ^ (8 * Z.of_nat 1)) with 256 in H1; lia].
intros j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 1) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 1); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
assert (Ej : j = 0%nat) by lia. subst j. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8 in *.
change (2 ^ 8) with 256 in *. rewrite ?Z.shiftr_0_r, ?Z.pow_0_r, ?Z.div_1_r.
rewrite !(Z.mod_small (bytes_le_to_Z (disco_table_c.sub T k 1)) 256) by lia. reflexivity.
Qed.
Theorem pb_tj_box : tj_seg_box B IMG.
Proof.
unfold tj_seg_box. intros i FU FK. unfold tj_fromU, tj_fromK, tj_from0 in FU, FK.
unfold tj_fromR, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
pose proof (tj_keep_journal cx) as HKJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_e, tj_age, tj_after2 in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS, HKJ.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
destruct HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(lia)); exact HE033).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG34; lia). clear AG34.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & acc & (o1 & o2 & E793 & E784 & Ho1 & Ho2 & Ho12) & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSK : 12416 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK, SNPRINTF_STK, VSNPRINTF_ICPT_STK, VFPRINTF_ICPT_STK, ESTACK; lia).
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
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite (AG n ltac:(lia)); exact (HE0 n r Hn)).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
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
assert (HF8hi : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; lia).
pose proof HKEEP as HKP. unfold tj_keep in HKP.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HKP.
destruct HKP as (HROD3 & Hgt3 & Hobj3).
pose proof Hobj3 as ((tcid & tpos & Htin & Htcid & HTF8 & HTFlo & HTFhi) & Ht8 & Htra).
assert (Htin3 : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HAR3 Htin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Htin3) as HTimg. rewrite EFA in HTimg.
set (TF := frame_addr ly tcid tpos) in *.
assert (HdTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (tcid, tpos))).
{ destruct (in_split _ _ Htin) as (l2 & l3 & Hsp).
eapply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (tcid, tpos) [] l2 l3 HAR3). rewrite HFR, Hsp. reflexivity. }
unfold zdisjoint, frame_rng in HdTF. cbn [fst snd] in HdTF. rewrite !EFA in HdTF. fold F TF in HdTF. change (fs_frame_bytes 2) with 256 in HdTF.
pose proof Hok as (Hn8 & _). unfold disco_table_c.tbl_T1 in Hn8.
destruct (Hbuf Hcap3) as (Hbin & Hbsz).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hbin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hbin3) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 buf Nb 2 fpos HAR3 Hbin3 Hfin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 2) with 256 in HdBF. rewrite EFA in HdBF. fold F in HdBF.
assert (Hacc1 : Z.of_nat (length (acc ++ [0])) <= req_size Nb) by (rewrite length_app; cbn [length]; lia).
pose proof (conj Hb4096 (conj Hbceil (conj Hbapp (conj HdBF (conj Hacc1 (conj Hsp1 (conj Hceil (conj Hslo (conj Hstk0 (conj Hshi (conj H47 (conj HSK (conj C1 (conj C3 (conj HF4096 (conj HFceil (conj HF8lo (conj HF8hi HFhigh)))))))))))))))))) as KB.
set (e := t + 48 * i) in *. assert (He : e = t + 48 * i) by reflexivity.
destruct (tj_garr8_u1 _ t (48 * i + 12) T Hgt3 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vhd & Rhd).
destruct (tj_garr8_u1 _ t (48 * i + 13) T Hgt3 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vdin & Rdin).
destruct (tj_garr8_u1 _ t (48 * i + 14) T Hgt3 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vdout & Rdout).
destruct (tj_garr8_u1 _ t (48 * i + 15) T Hgt3 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vfam & Rfam).
replace (t + (48 * i + 12)) with (e + 12) in Vhd by (unfold e; lia).
replace (t + (48 * i + 13)) with (e + 13) in Vdin by (unfold e; lia).
replace (t + (48 * i + 14)) with (e + 14) in Vdout by (unfold e; lia).
replace (t + (48 * i + 15)) with (e + 15) in Vfam by (unfold e; lia).
set (hd := disco_table_c.u_at T (48 * i + 12) 1) in *.
set (din := disco_table_c.u_at T (48 * i + 13) 1) in *.
set (dout := disco_table_c.u_at T (48 * i + 14) 1) in *.
set (fam := disco_table_c.u_at T (48 * i + 15) 1) in *.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 900 Ev ssv msv [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 900%nat [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E900 : ew Ev 900 = Z_to_bv 64 hd) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E901 : ew Ev 901 = Z_to_bv 64 din) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E902 : ew Ev 902 = Z_to_bv 64 dout) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E903 : ew Ev 903 = Z_to_bv 64 fam) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 3 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 740 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E740; unfold w64; rewrite unsigned_lit_small by lia; change (2 ^ 3) with 8; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 900 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E900, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 901 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E901, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 902 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E902, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 903 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E903, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 12 16 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 900 0)); YP09.mkChunk 13 (CVal 1 (SOff 901 0)); YP09.mkChunk 14 (CVal 1 (SOff 902 0)); YP09.mkChunk 15 (CVal 1 (SOff 903 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; unfold w64; rewrite unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 12 1 _ hd); [cbn [sv_denot]; rewrite E900, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vhd]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 13 1 _ din); [cbn [sv_denot]; rewrite E901, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vdin]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 14 1 _ dout); [cbn [sv_denot]; rewrite E902, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vdout]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 15 1 _ fam); [cbn [sv_denot]; rewrite E903, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vfam]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740; unfold w64; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi HdTF Hi Hn8;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 HSK C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres3; clear - Ho Hsp1 HSK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E740; unfold w64; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi Hi Hn8;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
paj_run_shc RUNP RUNC HS HJ. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
tj_keepg tj_garr8_kept HFx Hgarr AG KB Hgarr1 end.
clear_frames.
fs_roF HS.
pose proof (HKJ _ _ _ _ _ _ _ HBASE HJ) as HK4. unfold tj_keep in HK4.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HK4.
destruct HK4 as (HROD4 & Hgt4 & ((tcid4 & tpos4 & _) & _ & Htra4)).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msX) =>
assert (SH740 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem msX)) (mkSHE 740 0 48));
[ apply (shent_ok_of_range SEGS (w_H W3) (ms_mem msX) _ (SOff 32 0) 740 t 400 e 0 48 Htra4);
  [ apply U_atom; [rewrite (AG 32%nat) by lia; rewrite HE032; reflexivity | split; vm_compute; congruence]
  | apply U_atom; [rewrite E740; reflexivity | lia]
  | lia | lia
  | intros x Hx; clear - Hx HTapp HTFlo HTFhi Hi Hn8 He; unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; cbn [Z.min Z.max] in Hx; lia ]
| ];
assert (SH516 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem msX)) (mkSHE 516 256 0));
[ apply (shent_ok_of_range SEGS (w_H W3) (ms_mem msX) _ (SOff 32 0) 516 (F + 256) 0 F 256 0);
  [ apply range_addressable_nil; lia
  | apply U_atom; [rewrite (AG 32%nat) by lia; rewrite HE032; reflexivity | split; vm_compute; congruence]
  | apply U_atom; [exact E516 | lia]
  | lia | lia
  | intros x Hx; clear - Hx HFhigh; unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; cbn [Z.min Z.max] in Hx; lia ]
| ];
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 740 0 48; mkSHE 516 256 0] Ev (mrestrict (w_H W3) (ms_mem msX)))
by (unfold sh_ok; apply Forall_cons; [exact SH740 | apply Forall_cons; [exact SH516 | apply Forall_nil]]) end.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
tj_keepg tj_garr8_kept HFx Hgarr1 AG KB Hgarr2 end.
clear_frames. rebaseE HS AG HEv. rewrite <- HEv in SHOK. clear HEv.
psrr_branch_tok RUN BR HS SHOK Bspan.
-   hc_bool Hc ltac:(fun H => rewrite (U_atom _ 900 hd E900 ltac:(lia)) in H). hc_prop Hc.
  hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 24344. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  tj_keepg tj_garr8_kept HFx Hgarr2 AG KB Hgarr3 end.
  clear_frames. rebaseE HS AG HEv. clear HEv. clear SHOK.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ) Hfin) as (_ & _ & _ & HFSp).
  rewrite EFA in HFSp. fold F in HFSp.
  tj_rw529 HS E529 HFSp.
  prreg HS (26%bv : bv 5) R26.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
  assert (R26v : getr (ms_regs msX) 26 = Z_to_bv 64 (Z.of_nat (length acc))) end.
  { rewrite R26, E784, E793. unfold w64. rewrite alu64_add_lit. f_equal. lia. }
  ra_join HS ss_tjU 800%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
  ra_join_val HS 800%nat 13%nat R26v E813.
  rebaseE HS AG HEv. clear HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msX) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
  refine (FU (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wx msX mdX HBASE _ HJ HFR _ HS) end end.
  + unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia] |].
    split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|]. assumption.
  + unfold INV_tjU, tj_lbody, tj_wrote, tj_after2, tj_e. cbn [c_t c_T c_now c_cap c_buf c_ly c_S].
    split; [exact Hk0|]. split.
    * split; [exact Hperm|]. split; [exact (HKJ _ _ _ _ _ _ _ HBASE HJ)|]. split; [exact Hcap3|]. split; [exact Hi|].
      split; [exact E721|]. split; [exact E722|]. split; [exact E740|exact E741].
    * split.
      -- unfold model_of. cbn [reac_disco_table_json_c.tj_entry e_has_decl]. unfold disco_table_c.hd_of. fold hd. rewrite Hc. reflexivity.
      -- exists acc. split; [exact E813|]. split; [exact Hacc|]. split; [exact Htxt | exact Hgarr3].
-   hc_bool Hc ltac:(fun H => rewrite (U_atom _ 900 hd E900 ltac:(lia)) in H). hc_prop Hc.
  hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  tj_keepg tj_garr8_kept HFx Hgarr2 AG KB Hgarr3 end.
  clear_frames. clear SHOK.
  lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msX) => rename Ex into EC; rename msX into msC end.
  prreg HS (1%bv : bv 5) RX1. prreg HS (2%bv : bv 5) RX2. prreg HS (3%bv : bv 5) RX3. prreg HS (4%bv : bv 5) RX4.
  prreg HS (8%bv : bv 5) RX8. prreg HS (10%bv : bv 5) RX10. prreg HS (11%bv : bv 5) RX11. prreg HS (12%bv : bv 5) RX12.
  prreg HS (13%bv : bv 5) RX13. prreg HS (14%bv : bv 5) RX14. prreg HS (15%bv : bv 5) RX15. prreg HS (16%bv : bv 5) RX16.
  prreg HS (17%bv : bv 5) RX17.
  rewrite E903 in RX10. rewrite E901 in RX12. rewrite E902 in RX13.
  rewrite E516, unsigned_lit_small in RX14 by lia. rewrite E516, unsigned_lit_small in RX16 by lia.
  rewrite E60, unsigned_lit_small in RX2 by lia.
  rewrite (AG 3%nat) in RX3 by lia. rewrite (HE0 3%nat 3%bv eq_refl) in RX3.
  rewrite (AG 4%nat) in RX4 by lia. rewrite (HE0 4%nat 4%bv eq_refl) in RX4.
  rewrite (AG 2%nat) in RX8 by lia. rewrite (HE0 2%nat 2%bv eq_refl) in RX8.
  assert (Hsp : spZ (ms_regs msC) = sp1 - 16) by (unfold spZ; rewrite RX2, unsigned_lit_small by lia; lia).
  assert (Hs0 : s0Z (ms_regs msC) = spZ regs) by (unfold s0Z, spZ; rewrite RX8; reflexivity).
  assert (HraC : raZ (ms_regs msC) = BASE + 24336) by (unfold raZ; rewrite RX1; apply unsigned_lit_small; lia).
  assert (Usp' : bv_unsigned (ew EC 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact HE02).
  pose proof (HKJ _ _ _ _ _ _ _ HBASE HJ) as HK5. unfold tj_keep in HK5.
  cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HK5.
  destruct HK5 as (HRODC & _ & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ) Hfin) as (_ & _ & HFpC & HFSpC).
  rewrite EFA in HFpC, HFSpC. fold F in HFpC, HFSpC.
  unfold shadow_addr in HFSpC. rewrite <- SB_SHADOW_OFF in HFSpC.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  let r5 := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth EC ssx _ 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  pose proof (st_ok_region_nth EC ssx _ 2 r2 HS ltac:(vm_compute; reflexivity)) as HR529;
  pose proof (st_ok_region_nth EC ssx _ 3 r3 HS ltac:(vm_compute; reflexivity)) as HR516;
  pose proof (st_ok_region_nth EC ssx _ 5 r5 HS ltac:(vm_compute; reflexivity)) as HR2 end.
  cbn [ms_mem restrict] in HR516.
  assert (VFL : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (F + 248) 8 (bv_unsigned (Z_to_bv 64 FLg))).
  { pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 FLg)) as Hr64. change (bv_modulus 64) with (2 ^ 64) in Hr64.
    apply (field_of_region EC _ 516 F _ _ _ _ _ 248 8%N (SOff 528 0) (bv_unsigned (Z_to_bv 64 FLg)) HR516).
    - rewrite E516. apply unsigned_lit_small. lia.
    - cbn [YP09.r_chunks]. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite E528, Z.add_0_r. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  cbn [ms_mem restrict] in HR0, HR529, HR2.
  assert (Z0 : forall j, In j [4; 5; 6; 12; 13; 14; 20; 21; 22; 23; 24; 25] ->
    aview SEGS (w_H W3) (ms_mem msC) (SB + F / 8 + j) = Some 0).
  { intros j Hj. apply (tj_aview0_of_chunk EC (w_H W3) (ms_mem msC) (SB + F / 8) _ _ _ _ _ j HR529).
    - rewrite E529. apply unsigned_lit_small. unfold SB; lia.
    - cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [cbn [In]; repeat (first [left; reflexivity | right]) |]). destruct Hj. }
  assert (HFv : forall o, 0 <= o < 32 -> aview SEGS (w_H W3) (ms_mem msC) (SB + F / 8 + o) <> None)
  by (intros o Ho; apply tj_aview_pres; apply (proj1 (HFSpC o ltac:(change (fs_frame_bytes 2 / 8) with 32; lia)))).
  assert (HF32 : F mod 32 = 0) by (rewrite HFq; rewrite Z.mul_comm; apply Z_mod_mult).
  assert (HF8m : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
  assert (V8 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ regs - 8) = Some (raZ regs)).
  { replace (spZ regs - 8) with (spZ regs + -8) by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr64. change (bv_modulus 64) with (2 ^ 64) in Hr64.
    apply rdword_of_val_mem; [|unfold raZ; lia].
    apply (field_of_region EC _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR2 Usp').
    - cbn [YP09.r_chunks]. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite (AG 1%nat) by lia. rewrite (HE0 1%nat 1%bv eq_refl). unfold raZ. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold raZ. cbn. lia.
    - cbn. lia. }
  assert (V16 : rdword (aview SEGS (w_H W3) (ms_mem msC)) (spZ regs - 16) = Some (s0Z regs)).
  { replace (spZ regs - 16) with (spZ regs + -16) by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr64. change (bv_modulus 64) with (2 ^ 64) in Hr64.
    apply rdword_of_val_mem; [|unfold s0Z; lia].
    apply (field_of_region EC _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR2 Usp').
    - cbn [YP09.r_chunks]. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite (AG 8%nat) by lia. rewrite (HE0 8%nat 8%bv eq_refl). unfold s0Z. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold s0Z. cbn. lia.
    - cbn. lia. }
  assert (HCH : exists CH, achain ly3 (aview SEGS (w_H W3) (ms_mem msC)) (spZ (ms_regs msC)) (s0Z (ms_regs msC)) CH).
  { rewrite Hs0. pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
    destruct (Z_lt_ge_dec (spZ regs) (ly_top ly - 16)) as [Hlt|Hge].
    - exists ((spZ regs, raZ regs, s0Z regs) :: ch). apply (achain_ly_top ly ly3); [exact Etop3|].
      apply (achain_push ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) (raZ regs) ch (spZ (ms_regs msC)) Hch).
      + lia.
      + intros a Ha. exact (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha).
      + exact V8.
      + exact V16.
      + exact Hra4.
      + lia.
      + clear - Hal16; lia.
      + exact Hlt.
      + rewrite Hsp; lia.
    - exists []. left. split; [right; left; rewrite Etop3; lia | reflexivity]. }
  destruct HCH as (CH & HCH).
  pmkst HS. rewrite pa_sigma_reac_box_name.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdC) _ =>
  refine (SRr_bind _ _ _ _ _ (RBN fq REAC_DISCO_TABLE_JSON_STK (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 W3
    (ms_mem msC) mdC k (ms_regs msC) CH fam 0 din dout (F + 32) 24 (F + 96) 24 (F + 160) 48 [] HJ HRODC
    (tj_mc_consts W3 _ HRODC) ?[Pret] ?[Pra] ?[Pgp] ?[Ptp] HCH ?[Pal] ?[Pstk] ?[Ptop] ?[Pfr]
    RX10 ?[Pf] RX11 ?[Psd] RX12 ?[Pi] RX13 ?[Po] RX14 ?[Pn] RX15 ?[Pnl] RX16 ?[Ptk] RX17 ?[Ptl]
    ?[Pdsp] ?[Pd] ?[Pdl] ?[Pdlr] ?[Pimg] ?[Pbuf]) ?[Pcont]) end.
  [Pret]: { rewrite RX1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  [Pra]: { rewrite HraC. lia. }
  [Pgp]: { rewrite RX3. exact Hgp. }
  [Ptp]: { rewrite RX4. exact Htp. }
  [Pal]: { rewrite Hsp. clear - Hsp1al16; lia. }
  [Pstk]: { rewrite Hsp. unfold REAC_BOX_NAME_STK, ESTACK. lia. }
  [Ptop]: { rewrite Hsp. lia. }
  [Pfr]: { rewrite HFR. cbn [length]. lia. }
  [Pf]: { lia. }
  [Psd]: { lia. }
  [Pi]: { lia. }
  [Po]: { lia. }
  [Pn]: { lia. }
  [Pnl]: { lia. }
  [Ptk]: { lia. }
  [Ptl]: { lia. }
  [Pdsp]: { rewrite Hsp. replace (sp1 - 16) with (sp1 + -16) by lia.
    apply (field_of_region EC _ 60 sp1 _ _ _ _ _ (-16) 8%N (SOff 516 160) (F + 160) HR0).
    - rewrite E60. apply unsigned_lit_small. lia.
    - cbn [YP09.r_chunks]. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite E516, unsigned_lit_small by lia. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  [Pd]: { lia. }
  [Pdl]: { rewrite Hsp. replace (sp1 - 16 + 8) with (sp1 + -8) by lia.
    apply (field_of_region EC _ 60 sp1 _ _ _ _ _ (-8) 8%N (SLit 48) 48 HR0).
    - rewrite E60. apply unsigned_lit_small. lia.
    - cbn [YP09.r_chunks]. repeat (first [left; reflexivity | right]).
    - reflexivity.
    - cbn. lia.
    - cbn. lia. }
  [Pdlr]: { lia. }
  [Pimg]: { exact (tj_rbn_img ly3 S3 W3 (ms_mem msC) _ (proj1 HJ) HRODC). }
  [Pbuf]: {
    intros _. split; [left; split; reflexivity|].
    unfold rbn_bufs, rbn_buf. rewrite Hsp. change (Z.min 24 24) with 24. change (Z.min 48 48) with 48.
    split; [|split; [|split; [|split; [lia | split; lia]]]].
    - split; [lia|]. split; [lia|]. split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|].
      split; [right; unfold REAC_BOX_NAME_STK, ESTACK; lia|].
      split; [apply (tj_ra_frame _ F (F + 32) 24 4 HF8m ltac:(lia) ltac:(lia)); intros j Hj; apply Z0; cbn [In]; lia|].
      split; [apply (tj_hull_frame _ F (F + 32) 24 HF32 ltac:(lia) ltac:(lia) ltac:(lia) HFv)|].
      intros a Ha. split.
      + right; right; right. exists 2, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA0. change (fs_frame_bytes 2) with 256. fold F. lia.
      + apply (proj1 (HFpC a ltac:(change (fs_frame_bytes 2) with 256; lia))).
    - split; [lia|]. split; [lia|]. split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|].
      split; [right; unfold REAC_BOX_NAME_STK, ESTACK; lia|].
      split; [apply (tj_ra_frame _ F (F + 96) 24 12 HF8m ltac:(lia) ltac:(lia)); intros j Hj; apply Z0; cbn [In]; lia|].
      split; [apply (tj_hull_frame _ F (F + 96) 24 HF32 ltac:(lia) ltac:(lia) ltac:(lia) HFv)|].
      intros a Ha. split.
      + right; right; right. exists 2, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA0. change (fs_frame_bytes 2) with 256. fold F. lia.
      + apply (proj1 (HFpC a ltac:(change (fs_frame_bytes 2) with 256; lia))).
    - split; [lia|]. split; [lia|]. split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|].
      split; [right; unfold REAC_BOX_NAME_STK, ESTACK; lia|].
      split; [apply (tj_ra_frame _ F (F + 160) 48 20 HF8m ltac:(lia) ltac:(lia)); intros j Hj; apply Z0; cbn [In]; lia|].
      split; [apply (tj_hull_frame _ F (F + 160) 48 HF32 ltac:(lia) ltac:(lia) ltac:(lia) HFv)|].
      intros a Ha. split.
      + right; right; right. exists 2, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA0. change (fs_frame_bytes 2) with 256. fold F. lia.
      + apply (proj1 (HFpC a ltac:(change (fs_frame_bytes 2) with 256; lia))). }
  [Pcont]: {
  intros W2 c2 HWle (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Hfrs2 & Hperm2 & Ha02 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Hout).
  subst c2. rewrite RX1.
  assert (HK : acall_kept SEGS B ly3 S3 W3 (ms_mem msC) W2 mem2 (spZ (ms_regs msC) - REAC_BOX_NAME_STK) (spZ (ms_regs msC))
    (rbn_wr fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48)).
  { refine (conj _ (conj Q2 (conj Q3 (conj Q4 (conj Q5 Q6))))).
    intros a Ha Hs. apply (Q1 a Ha Hs). intros Hw. apply tj_rbn_wr_in in Hw. lia. }
  pose proof HJ2 as (HAR2 & Hly2 & _).
  destruct (al_layout _ _ LAWS ly S W mem md ly2 HAR Hly2) as (_ & EFA2 & _).
  assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (_ & _ & HFp2 & HFSp2).
  rewrite EFA2 in HFp2, HFSp2. fold F in HFp2, HFSp2.
  aconstsF HJ Kgot Kcell Kguar Kuar. aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
  assert (Hgarr4 : garr8 SEGS (mrestrict (w_H W2) mem2) buf (acc ++ [0])).
  { apply (garr8_frame SEGS _ _ _ _ Hgarr3). intros x Hx. apply (mbyte_of_aview SEGS).
    replace x with (buf + (x - buf)) by lia. apply (Q2 buf Nb (x - buf) Hbin3); [lia|].
    intros Hw. apply tj_rbn_wr_in in Hw. lia. }
  pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
  destruct (reac_box_name_c.bn_accept fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48) eqn:HACC.
  2: {
  assert (HnoW : forall a, ~ rbn_wr fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48 a)
    by (intros a (Ha & _); rewrite HACC in Ha; discriminate).
  reseat HS HJ2 HP2 [0; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; first
    [ lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
        apply (region_kept_val_at Ex _ _ 33%nat (as_uar_cell B) 4 1); [evalE AG | exact Kuar | exact Kuar2 | lia] end
    | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
        eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin
        | right; rewrite EFA0; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; unfold SB; lia
        | intros a Ha; apply HnoW | intros a Ha; lia ] end
    | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
        eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin
        | left; rewrite EFA0; fold F; change (fs_frame_bytes 2) with 256; lia
        | intros a Ha; apply HnoW | intros a Ha; apply (proj1 (HFp2 a ltac:(change (fs_frame_bytes 2) with 256; lia))) ] end
    | keptFL HK HJ2 AG Kgot Kgot2 Kcell Kcell2 Kguar Kguar2 Kuar Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) ]).
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_pin_reg' Ev ssx msx (10%bv : bv 5) 18446744073709551615 HS
    ltac:(cbn [ms_regs restrict mkst]; rewrite Ha02; apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS3 end.
  clear HS; rename HS3 into HS; norm_ss HS.
  paj_run_to_shc RUNTOP HS HJ2 24344. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA2. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  tj_keepg tj_garr8_kept HFx Hgarr4 AG KB Hgarr5 end.
  clear_frames. rebaseE HS AG HEv. clear HEv.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (_ & _ & _ & HFSp3).
  rewrite EFA2 in HFSp3. fold F in HFSp3.
  tj_rw529 HS E529 HFSp3.
  prreg HS (26%bv : bv 5) R26.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
  assert (R26v : getr (ms_regs msX) 26 = Z_to_bv 64 (Z.of_nat (length acc))) end.
  { rewrite R26, E784, E793. unfold w64. rewrite alu64_add_lit. f_equal. lia. }
  ra_join HS ss_tjU 800%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
  ra_join_val HS 800%nat 13%nat R26v E813.
  rebaseE HS AG HEv. clear HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msX) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
  refine (FU (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly2 S2 Wx msX mdX HBASE _ HJ2
    ltac:(rewrite Hfrs2; exact HFR) _ HS) end end.
  + unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia] |].
    split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|]. assumption.
  + unfold INV_tjU, tj_lbody, tj_wrote, tj_after2, tj_e. cbn [c_t c_T c_now c_cap c_buf c_ly c_S].
    split; [exact Hk0|]. split.
    * split; [exact (Permutation_trans Hperm2 Hperm)|]. split; [exact (HKJ _ _ _ _ _ _ _ HBASE HJ2)|]. split; [exact Hcap3|]. split; [exact Hi|].
      split; [exact E721|]. split; [exact E722|]. split; [exact E740|exact E741].
    * split.
      -- unfold model_of, reac_disco_table_json_c.box_tok. cbn [reac_disco_table_json_c.tj_entry e_has_decl e_family e_decl_in e_decl_out].
         unfold disco_table_c.hd_of, disco_table_c.din_of, disco_table_c.dout_of. fold hd din dout fam.
         rewrite (proj2 (Z.eqb_neq hd 0) Hc).
         assert (Hr : bn_ret fam [] din dout <> 0).
         { intros Hr0. pose proof (tj_lemmas.tj_accept fam din dout (F + 32) (F + 96) (F + 160) Hr0 ltac:(lia) ltac:(lia) ltac:(lia)) as Hacc'.
           rewrite Hacc' in HACC. discriminate. }
         rewrite (proj2 (Z.eqb_neq _ 0) Hr). reflexivity.
      -- exists acc. split; [exact E813|]. split; [exact Hacc|]. split; [exact Htxt | exact Hgarr5]. }
  assert (HnoW : forall a, SB + F / 8 <= a < SB + F / 8 + 32 -> ~ rbn_wr fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48 a)
    by (intros a Ha Hw; apply tj_rbn_wr_in in Hw; unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *; lia).
  destruct (Hout eq_refl) as (_ & Htok & _).
  assert (VFL2 : val_mem SEGS (mrestrict (w_H W2) mem2) (F + 248) 8 (bv_unsigned (Z_to_bv 64 FLg))).
  { apply (tj_vm_keep _ _ _ _ _ _ _ VFL). intros j Hj. apply (Q4 2 fpos _ Hfin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA0. fold F. change (fs_frame_bytes 2) with 256. lia.
    - intros Hw. apply tj_rbn_wr_in in Hw. lia. }
  assert (Z02 : forall j, 12 <= j < 15 -> aview SEGS (w_H W2) mem2 (SB + F / 8 + j) = Some 0).
  { intros j Hj. rewrite (Q4 2 fpos (SB + F / 8 + j) Hfin).
    - apply Z0. cbn [In]. lia.
    - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA0. fold F. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 2 / 8) with 32. lia.
    - apply HnoW. lia. }
  reseat HS HJ2 HP2 [0; 4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; first
    [ lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
        apply (region_kept_val_at Ex _ _ 33%nat (as_uar_cell B) 4 1); [evalE AG | exact Kuar | exact Kuar2 | lia] end
    | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
        eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin
        | right; rewrite EFA0; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; unfold SB; lia
        | intros a Ha; apply HnoW; unfold SB in *; lia | intros a Ha; lia ] end
    | keptFL HK HJ2 AG Kgot Kgot2 Kcell Kcell2 Kguar Kguar2 Kuar Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) ]).
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_pin_reg' Ev ssx msx (10%bv : bv 5) 0 HS
    ltac:(cbn [ms_regs restrict mkst]; rewrite Ha02; apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS3 end.
  clear HS; rename HS3 into HS; norm_ss HS.
  paj_run_to_shc RUNTOP HS HJ2 24460. { tj_awr ltac:(idtac; tj_hd AG HSK) AG fpos F EFA2. }
  destruct (tj_acc_lens _ _ _ _ _ _ _ _ _ _ HACC) as (Hret0 & LNM & LTK & LDP).
  set (tok := bn_TK (bn_NM fam [] din dout)) in *.
  assert (Ltok : Z.of_nat (length (tok ++ [0])) <= 24) by (rewrite length_app; cbn [length]; lia).
  pose proof (conj Ltok KB) as KBt.
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 FLg)) as HFLr. change (bv_modulus 64) with (2 ^ 64) in HFLr.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ ?mK) |- _ =>
  tj_keepg tj_garr8_kept HFx Hgarr4 AG KB Hgarr5;
  tj_keepg tj_garr8_kept HFx Htok AG KBt Htok2;
  tj_keepv tj_vm_frame HFx VFL2 AG KB VFL3;
  assert (Z03 : forall j, 12 <= j < 15 -> aview SEGS (w_H W2) mK (SB + F / 8 + j) = Some 0);
  [ intros j Hj; erewrite (aview_kept_out _ _ _ _ _ HFx (SB + F / 8 + j) ltac:(unfold SB; lia)); [apply Z02; lia | tj_nowin AG KB Hj] | ] end.
  clear_frames. rebaseE HS AG HEv. clear HEv.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFp3 & HFSp3).
  rewrite EFA2 in HFp3, HFSp3. fold F in HFp3, HFSp3.
  unfold shadow_addr in HFSp3. rewrite <- SB_SHADOW_OFF in HFSp3.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp3 (F + o) ltac:(change (fs_frame_bytes 2) with 256; lia)))
  | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ (bv_unsigned (Z_to_bv 64 FLg)));
    [cbn [sv_denot]; rewrite E528, Z.add_0_r; reflexivity | zside | zside | exact VFL3] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ss HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 529%nat) 0 32 0 32 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSp3 o ltac:(change (fs_frame_bytes 2 / 8) with 32; lia)))
  | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob253 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ss HS.
  prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
  assert (R26v : getr (ms_regs msX) 26 = Z_to_bv 64 (Z.of_nat (length acc)));
  [ rewrite R26, E784, E793; unfold w64; rewrite alu64_add_lit; f_equal; lia
  | assert (R27v : getr (ms_regs msX) 27 = Z_to_bv 64 (SB + (e + 14) / 8));
    [ rewrite R27, E740; unfold w64; rewrite unsigned_lit_small by lia; rewrite tj_srl3 by lia;
      rewrite (AG 32%nat) by lia; rewrite HE032, alu64_add_lit; f_equal; lia | ] ] end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_havoc_hi 834 Ex ssx msx [Z_to_bv 64 (SB + (e + 13) / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ex 834%nat [Z_to_bv 64 (SB + (e + 13) / 8)] end.
  clear HS. rename HS3 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E834 : ew Ev 834 = Z_to_bv 64 (SB + (e + 13) / 8))
  by exact (ew_havoc_new _ 834 [Z_to_bv 64 (SB + (e + 13) / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) end.
  rebaseE HS AG HEv. clear HEv.
  rechunk HS 3%nat 1%nat (SOff 834 0) ltac:(cbn [sv_denot]; rewrite E834, E740, (AG 32%nat), HE032 by lia; unfold w64;
    rewrite !unsigned_lit_small by (unfold SB; lia); rewrite tj_srl3 by lia; rewrite alu64_add_lit; f_equal; lia).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let tg := eval red in ss_tjK in let rs := eval cbn [ss_mem] in (ss_mem tg) in
  pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
  clear HS; rename HS3 into HS; norm_ss HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let dl := eval cbv in ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 27; 26]%bv : list (bv 5)) in
  let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
  let vals' := eval cbn [map ms_regs restrict] in vals in
  pose proof (st_ok_pi_havoc_hi 820 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; set_regs_rec HS 820%nat vals' 0%nat dl end.
  norm_ss HS.
  ra_join_val HS 820%nat 12%nat R27v E832.
  ra_join_val HS 820%nat 13%nat R26v E833.
  rebaseE HS AG HEv. clear HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let dl := eval cbv in ([28; 29; 30; 31]%bv : list (bv 5)) in
  let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
  let vals' := eval cbn [map ms_regs restrict] in vals in
  pose proof (st_ok_pi_havoc_hi 835 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; set_regs_rec HS 835%nat vals' 0%nat dl end.
  norm_ss HS.
  rebaseE HS AG HEv. clear HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let tg := eval red in ss_tjK in
  let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
  let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
  let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
  pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3 end.
  clear HS; rename HS3 into HS; norm_ss HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wx) ?msX) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
  refine (FK (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly2 S2 Wx msX mdX HBASE _ HJ2
    ltac:(rewrite Hfrs2; exact HFR) _ HS) end end.
  + unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
    split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia] |].
    split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|]. assumption.
  + unfold INV_tjK, tj_lbody, tj_wrote, tj_after2, tj_e. cbn [c_t c_T c_now c_cap c_buf c_ly c_S].
    split; [exact Hk0|]. split.
    { split; [exact (Permutation_trans Hperm2 Hperm)|]. split; [exact (HKJ _ _ _ _ _ _ _ HBASE HJ2)|]. split; [exact Hcap3|]. split; [exact Hi|].
      split; [exact E721|]. split; [exact E722|]. split; [exact E740|exact E741]. }
    split; [exact E834|]. split; [exact E832|]. split.
    { exists tok. split.
      - unfold model_of, reac_disco_table_json_c.box_tok. cbn [reac_disco_table_json_c.tj_entry e_has_decl e_family e_decl_in e_decl_out].
        unfold disco_table_c.hd_of, disco_table_c.din_of, disco_table_c.dout_of. fold hd din dout fam.
        rewrite (proj2 (Z.eqb_neq hd 0) Hc). rewrite Hret0. reflexivity.
      - split; [exact Htok2|]. split.
        + apply (tj_ra_frame _ F (F + 96) (Z.of_nat (length tok) + 1) 12 HF8m ltac:(lia) ltac:(lia)).
          intros j Hj. apply Z03. rewrite length_app in Ltok. cbn [length] in Ltok. lia.
        + apply (tj_hull_frame _ F (F + 96) (Z.of_nat (length tok) + 1) HF32 ltac:(lia) ltac:(lia)
            ltac:(rewrite length_app in Ltok; cbn [length] in Ltok; lia)).
          intros o Ho. apply tj_aview_pres. apply (proj1 (HFSp3 o ltac:(change (fs_frame_bytes 2 / 8) with 32; lia))). }
    exists acc. split; [exact E833|]. split; [exact Hacc|]. split; [exact Htxt | exact Hgarr5]. }
Qed.
End h.
End f.
End d.
