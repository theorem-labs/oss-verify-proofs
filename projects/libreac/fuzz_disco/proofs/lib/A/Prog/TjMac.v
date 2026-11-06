(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths, module names and numbers changed; 1071 of its 1108 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/TjModel.v, with its numbers changed; 583 of its 790 lines of code are new or changed and 901 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import AmemBlock8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma tjm_sub_nth : forall (T : list byte) (j w k : nat), (k < w)%nat ->
nth_error (disco_table_c.sub T (Z.of_nat j) w) k = nth_error T (j + k).
Proof.
intros T j w k Hk. unfold disco_table_c.sub. rewrite Nat2Z.id, nth_error_firstn.
destruct (Nat.ltb_spec k w); [|lia]. apply nth_error_skipn.
Qed.
Lemma tjm_garr8_nth : forall segs (m : word -> option byte) base (L : list byte) j b,
garr8 segs m base (map bv_unsigned L) -> nth_error L j = Some b ->
mbyte segs m (base + Z.of_nat j) = Some b.
Proof.
intros segs m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte segs m base (map bv_unsigned L) j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth (map bv_unsigned L) j 0 (map_nth_error bv_unsigned j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma tjm_u_range : forall (T : list byte) k (n : nat), 0 <= disco_table_c.u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T k n. unfold disco_table_c.u_at.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k n)) as X.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k n)) as Y.
assert (L : (length (disco_table_c.sub T k n) <= n)%nat) by (unfold disco_table_c.sub; rewrite length_firstn; lia).
assert (P : 2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k n))) <= 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_le_mono_r; lia).
lia.
Qed.
Lemma tjm_val_u : forall segs (m : word -> option byte) t (T : list byte) (j n : nat),
garr8 segs m t (map bv_unsigned T) -> (j + n <= length T)%nat ->
val_mem segs m (t + Z.of_nat j) n (disco_table_c.u_at T (Z.of_nat j) n).
Proof.
intros segs m t T j n GT Hjn k Hk.
pose proof (tjm_u_range T (Z.of_nat j) n) as Hb.
destruct (nth_error T (j + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + Z.of_nat j + Z.of_nat k) with (t + Z.of_nat (j + k)) by lia.
rewrite (tjm_garr8_nth segs m t T (j + k) b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hb | lia].
rewrite <- (tjm_sub_nth T j n k Hk) in Hb2.
pose proof (YA0j.nth_error_le_byte _ _ _ Hb2) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold disco_table_c.u_at. rewrite <- Hv.
first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma tjm_val_at : forall segs (m : word -> option byte) t (T : list byte) k (n : nat),
garr8 segs m t (map bv_unsigned T) -> 0 <= k -> (Z.to_nat k + n <= length T)%nat ->
val_mem segs m (t + k) n (disco_table_c.u_at T k n).
Proof.
intros segs m t T k n GT Hk Hl. pose proof (tjm_val_u segs m t T (Z.to_nat k) n GT Hl) as X.
rewrite Z2Nat.id in X by exact Hk. exact X.
Qed.
Lemma tjm_U_sh : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 47 ->
ew E 32 = Z_to_bv 64 SB ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = SB + (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc H32. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv) by lia. rewrite (U_atom E 32 SB H32) by (unfold SB; lia). rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SB; lia). lia.
Qed.
Ltac rrw HS r e' Utac :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
let e0 := eval vm_compute in (sr_get (ss_regs ssx) r) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_reg_fp Ex ssx (restrict Hh msx) r e' HS ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx r HS);
change (sr_get (ss_regs ssx) r) with e0; rewrite !(denot_lit_U Ex); f_equal; Utac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac tjm_bytef HS n En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite En, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
Lemma tjm_age_U : forall E now ls, ew E 11 = Z_to_bv 64 now -> ew E 783 = Z_to_bv 64 ls -> 0 <= ls < now -> now < 2 ^ 64 ->
U E (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SOff 11 0) (SMd M_MUL (SOff 783 0) (SLit (-1))))
(SLit 4835703278458516699)) (SLit 18)) = (now - ls) / 1000000.
Proof.
intros E now ls H11 H783 Hl Hn.
repeat (rewrite U_SAlu || rewrite U_SMd). cbn [zalu_raw zmd_raw].
rewrite (U_atom E 11 now H11) by lia. rewrite (U_atom E 783 ls H783) by lia. rewrite !U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon 18) with 18. change (Z.land 18 63) with 18.
change (zcanon 4835703278458516699) with tj_lemmas.KDv.
assert (Hs : zcanon (now + zcanon (ls * (2 ^ 64 - 1))) = now - ls).
{ unfold zcanon, M64. replace (ls * (2 ^ 64 - 1)) with ((- ls) + ls * 2 ^ 64) by ring. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_r. replace (now + - ls) with (now - ls) by ring. apply Z.mod_small. lia. }
rewrite Hs. change (Z.of_N 64) with 64.
pose proof (tj_lemmas.tj_quot_mach (now - ls) ltac:(lia)) as Q. rewrite unsigned_lit in Q.
rewrite Q. apply zcanon_id. unfold M64. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.
Ltac tjm_havoc2 HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) ([10%bv; 11%bv] : list (bv 5))) in
let vals' := eval cbn [map ms_regs restrict] in vals in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi 785 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; set_regs_rec HS 785%nat vals' 0%nat ([10%bv; 11%bv] : list (bv 5)) end.
Ltac tjm_noconds HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let al := eval vm_compute in (f_alias (ss_facts ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl Ev ssx msx fa al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
Ltac tjm_notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Ltac tjm_kg Hg HFr AG :=
lazymatch type of Hg with garr8 ?sg (mrestrict ?H ?m) ?p ?L =>
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
let Hg2 := fresh "Hg" in
assert (Hg2 : garr8 sg (mrestrict H m1) p L);
[ apply (garr8_aview_kept sg H H m m1 p L); [| exact Hg];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite ?length_app in Ha; cbn [length] in Ha;
eapply aview_kept_out; [exact HFr | lia | tjm_notw AG]
| clear Hg; rename Hg2 into Hg ] end end.
Lemma tjm_csub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 < l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjm_hex : forall v, 0 <= v < 256 -> pf_hex2 v = hex2 v.
Proof. intros v Hv. exact (tj_lemmas.pf_hex2_hex2 v Hv). Qed.
Definition tjm_ps : list pf_piece := [Ps; PLit 123; PLit 34; PLit 109; PLit 97; PLit 99; PLit 34; PLit 58; PLit 34; Px02;
PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 34].
Lemma tjm_region_sub : forall segs E m b lo hi wlo whi cs cs', (forall x, In x cs' -> In x cs) ->
region_ok segs E m (YP09.mkRegion b lo hi wlo whi cs) -> region_ok segs E m (YP09.mkRegion b lo hi wlo whi cs').
Proof.
intros segs E m b lo hi wlo whi cs cs' Hin (H1 & H2 & H3 & H4). unfold region_ok in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) H4 x (Hin x Hx)).
Qed.
Ltac tjm_reorder HS i r' :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(tjm_region_sub _ Ex _ _ _ _ _ _ _ _ ltac:(incl_lit_tac) (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac tjm_fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjm_kept AG Hfr Hpres2 :=
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; lia | exact Hpres2].
Ltac tjm_arg HS j :=
lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
unfold argZ; rewrite (st_ok_restrict_reg sg Hh Ex ssx msx (Z_to_bv 5 (10 + j)) HS);
let e := eval vm_compute in (sr_get (ss_regs ssx) (Z_to_bv 5 (10 + j))) in
change (sr_get (ss_regs ssx) (Z_to_bv 5 (10 + j))) with e end.
Lemma tjm_bltz_false : forall E x v, U E x = v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E x) (sv_denot E (SLit 0)) = true -> False.
Proof.
intros E x v HU Hv Hc. cbn [branch_taken] in Hc. unfold bv_lts in Hc.
assert (Hsx : bv_signed (sv_denot E x) = v) by (rewrite (YK11.bv_signed_small (sv_denot E x)); [exact HU | unfold U in HU; rewrite HU; lia]).
assert (Hs0 : bv_signed (sv_denot E (SLit 0)) = 0).
{ rewrite (YK11.bv_signed_small (sv_denot E (SLit 0)));
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)); rewrite U_SLit; change (zcanon 0) with 0; [reflexivity | lia]. }
rewrite Hsx, Hs0 in Hc. apply Z.ltb_lt in Hc. lia.
Qed.
Ltac tjm_chain AG :=
repeat match goal with
| HF : frame_of _ _ (mrestrict ?H ?m0) (mrestrict _ ?m1) |- context [aview ?sg ?H ?m1 ?a] =>
rewrite (aview_kept_out _ _ H m0 m1 HF a ltac:(lia) ltac:(tjm_notw AG))
end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition ss_tjmC : sstate :=
(mkSS 23844 [SLit 0; SOff 720 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 721 0; SOff 722 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 740 0) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SOff 785 0; SOff 786 0; SOff 726 0; SOff 784 0; SOff 728 0; SOff 729 0; SOff 730 0; SOff 731 0; SOff 516 0; SOff 741 0; SOff 13 0; SOff 10 384; SOff 529 0; SOff 740 0; SOff 12 0; SOff 32 0; SOff 733 0; SOff 11 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 740 40) (SLit 3)) (SOff 32 0); SOff 735 0; SOff 736 0; SOff 737 0] [(YP09.mkRegion (Some 740%nat) 0 48 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 777 0)); YP09.mkChunk 1 (CVal 1 (SOff 778 0)); YP09.mkChunk 2 (CVal 1 (SOff 779 0)); YP09.mkChunk 3 (CVal 1 (SOff 780 0)); YP09.mkChunk 4 (CVal 1 (SOff 781 0)); YP09.mkChunk 5 (CVal 1 (SOff 782 0)); YP09.mkChunk 40 (CVal 8 (SOff 783 0))]); (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 []); (YP09.mkRegion (Some 529%nat) 0 32 0 0 []); (YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]); (YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 32 (CVal 8 (SOff 281 0)); YP09.mkChunk 40 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 48 (CVal 8 (SOff 516 160)); YP09.mkChunk 56 (CVal 8 (SOff 516 32)); YP09.mkChunk 64 (CVal 8 (SOff 10 0)); YP09.mkChunk 72 (CVal 8 (SOff 11 0)); YP09.mkChunk 80 (CVal 8 (SOff 10 384)); YP09.mkChunk 88 (CVal 8 (SOff 516 0)); YP09.mkChunk 96 (CVal 8 (SOff 516 96)); YP09.mkChunk 104 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 112 (CVal 8 (SOff 282 0))]); (YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]); (YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 307 0))]); (YP09.mkRegion (Some 307%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]); (YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 308 0))]); (YP09.mkRegion (Some 308%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))])] None (mkFacts [(782%nat, mkAF 0 255 0); (781%nat, mkAF 0 255 0); (780%nat, mkAF 0 255 0); (779%nat, mkAF 0 255 0); (778%nat, mkAF 0 255 0); (777%nat, mkAF 0 255 0); (740%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)] [] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : pa_sigma DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Hypothesis tj_pad : forall k s, tj_ro_at k s -> forall x, VAL (A_OBJ k) + Z.of_nat (length s) < x < str_end (VAL (A_OBJ k)) s ->
seg_rom SEGS (Z_to_bv 64 x) <> None.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Hypothesis HEV : 8 * EVB <= EV.
Lemma tjm_aview_rom : forall (H : word -> bool) (mem : word -> option byte) a,
seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)); [discriminate | contradiction].
Qed.
Lemma tjm_ro_str : forall k s ly' S' (W' : world SEGS) mem' md', tj_ro_at k s -> AR SEGS B ly' S' W' mem' md' ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem') ->
(forall j, 0 <= j <= Z.of_nat (length s) ->
aview SEGS (w_H W') mem' (VAL (A_OBJ k) + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0)) /\
range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview SEGS (w_H W') mem') (VAL (A_OBJ k)) (Z.of_nat (length s) + 1).
Proof.
intros k s ly' S' W' mem' md' (Hg & Hro & Hlo & Hhi & Hc & Hb) HAR' HROD'.
split; [| exact (ro_read_ok_glob SEGS B disco_globs ly' S' W' mem' md' (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) GM Hg HV HAR'
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))].
intros j Hj.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + j) HROD'
(Hro (VAL (A_OBJ k) + j) ltac:(lia)) (disco_ro_unowned_at B _ _ DRO ltac:(unfold disco_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as X. rewrite Z2Nat.id in X by lia. exact X.
Qed.
Lemma tjm_ptr_arg : forall k s ly' S' (W' : world SEGS) mem' md' rs, tj_ro_at k s -> AR SEGS B ly' S' W' mem' md' ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem') ->
Forall (fun r => IMG_TOP <= fst r \/ fst r + snd r <= IMG_LO) rs ->
pf_arg_asan (aview SEGS (w_H W') mem') rs (VAL (A_OBJ k)) (APtr s).
Proof.
intros k s ly' S' W' mem' md' rs HK HAR' HROD' Hrs.
destruct (tjm_ro_str k s ly' S' W' mem' md' HK HAR' HROD') as (Hby & Hra & Hhu).
pose proof HK as (Hg & Hro & Hlo & Hhi & Hc & Hb).
pose proof (Z.mod_pos_bound (VAL (A_OBJ k) + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
unfold IMG_LO, IMG_TOP in *.
cbn [pf_arg_asan]. split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [exact Hby|].
split; [intros x Hx; apply tjm_aview_rom; exact (tj_pad k s HK x Hx)|].
split; [eapply Forall_impl; [|exact Hrs]; intros r Hr; unfold zdisjoint, str_end, IMG_LO, IMG_TOP in *; cbn [fst snd] in *; lia|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
split; assumption.
Qed.
Lemma tjm_fmt_at : forall k s ly' S' (W' : world SEGS) mem' md' rs, tj_ro_at k s -> AR SEGS B ly' S' W' mem' md' ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem') ->
Forall (fun r => IMG_TOP <= fst r \/ fst r + snd r <= IMG_LO) rs ->
fmt_at (aview SEGS (w_H W') mem') rs (VAL (A_OBJ k)) s.
Proof.
intros k s ly' S' W' mem' md' rs HK HAR' HROD' Hrs.
destruct (tjm_ro_str k s ly' S' W' mem' md' HK HAR' HROD') as (Hby & Hra & Hhu).
pose proof HK as (Hg & Hro & Hlo & Hhi & Hc & Hb).
unfold IMG_LO, IMG_TOP in *.
unfold fmt_at. split; [lia|]. split; [exact Hby|].
split; [eapply Forall_impl; [|exact Hrs]; intros r Hr; unfold zdisjoint, IMG_LO, IMG_TOP in *; cbn [fst snd] in *; lia|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
split; assumption.
Qed.
Lemma tjm_garr8_of_aview : forall (H : word -> bool) (m : word -> option byte) p l,
(forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) -> garr8 SEGS (mrestrict H m) p l.
Proof. intros H m p l HE j Hj. exact (val_mem1_of_aview SEGS H m (p + Z.of_nat j) (nth j l 0) (HE j Hj)). Qed.
Theorem pb_tj_mac : tj_seg_mac B STK EV EVB IMG.
Proof.
unfold tj_seg_mac. intros i FX FM.
unfold tj_fromL, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
change (frames S3 = (2, fpos) :: frames S) in HFR.
unfold INV_tjL in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & acc & E733 & Hacc & Htxt & Hgarr).
pose proof Hok as (HT1 & HT2 & HT3 & HT4). unfold disco_table_c.tbl_T1 in HT1.
assert (Hi8 : 0 <= i < 8) by lia.
set (e := t + 48 * i).
set (ls := disco_table_c.last_of T i).
set (age := age_of now ls).
set (m0 := disco_table_c.u_at T (48 * i + 0) 1). set (m1 := disco_table_c.u_at T (48 * i + 1) 1).
set (m2 := disco_table_c.u_at T (48 * i + 2) 1). set (m3 := disco_table_c.u_at T (48 * i + 3) 1).
set (m4 := disco_table_c.u_at T (48 * i + 4) 1). set (m5 := disco_table_c.u_at T (48 * i + 5) 1).
set (sepp := if i =? 0 then VAL (A_OBJ 41) else VAL (A_OBJ 40)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 740 Ev ssv msv [Z_to_bv 64 e; Z_to_bv 64 age] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 740%nat [Z_to_bv 64 e; Z_to_bv 64 age] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E740 : ew Ev 740 = Z_to_bv 64 e) by (rewrite HEv; exact (ew_havoc_new _ 740 [Z_to_bv 64 e; Z_to_bv 64 age] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E741 : ew Ev 741 = Z_to_bv 64 age) by (rewrite HEv; exact (ew_havoc_new _ 740 [Z_to_bv 64 e; Z_to_bv 64 age] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 777 Ev ssv msv [Z_to_bv 64 m0; Z_to_bv 64 m1; Z_to_bv 64 m2; Z_to_bv 64 m3; Z_to_bv 64 m4; Z_to_bv 64 m5; Z_to_bv 64 ls; Z_to_bv 64 sepp] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 777%nat [Z_to_bv 64 m0; Z_to_bv 64 m1; Z_to_bv 64 m2; Z_to_bv 64 m3; Z_to_bv 64 m4; Z_to_bv 64 m5; Z_to_bv 64 ls; Z_to_bv 64 sepp] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => lazymatch type of HEv with _ = havoc _ _ ?ws =>
assert (E777 : ew Ev 777 = Z_to_bv 64 m0) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E778 : ew Ev 778 = Z_to_bv 64 m1) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E779 : ew Ev 779 = Z_to_bv 64 m2) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E780 : ew Ev 780 = Z_to_bv 64 m3) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 3 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E781 : ew Ev 781 = Z_to_bv 64 m4) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 4 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E782 : ew Ev 782 = Z_to_bv 64 m5) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 5 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E783 : ew Ev 783 = Z_to_bv 64 ls) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 6 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E784 : ew Ev 784 = Z_to_bv 64 sepp) by (rewrite HEv; exact (ew_havoc_new _ 777 ws 7 (Z_to_bv 64 0) ltac:(cbn; lia))) end end.
clear HEv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
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
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => rename Ev into Ew end.
assert (Er1 : ew Ew 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (Er2 : ew Ew 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (Er3 : ew Ew 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (Er4 : ew Ew 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew Ew 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew Ew 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat ltac:(lia)); rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew Ew 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew Ew 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew Ew 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew Ew 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF Ew.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
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
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold tj_keep in HKEEP. cbn [c_ly c_S c_t c_T] in HKEEP.
destruct HKEEP as (HROD3 & HgT & HobjT).
destruct HobjT as ((cid & pos & Hcin & Hcid & Hcal & Htlo & Hthi) & Ht8 & HraT).
assert (Hcin3 : In (cid, pos) (frames S3)) by (rewrite HFR; right; exact Hcin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hcin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hcin3) as HTimg. rewrite EFA in HTimg.
destruct (in_split _ _ Hcin) as (l2 & l3 & Hl23).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cid, pos) [] l2 l3 HAR3 ltac:(rewrite HFR, Hl23; reflexivity)) as HTsep.
unfold frame_rng, zdisjoint in HTsep. cbn [fst snd] in HTsep. rewrite !EFA in HTsep. fold F in HTsep. change (fs_frame_bytes 2) with 256 in HTsep.
assert (Rm0 : 0 <= m0 < 256) by exact (tjm_u_range T (48 * i + 0) 1).
assert (Rm1 : 0 <= m1 < 256) by exact (tjm_u_range T (48 * i + 1) 1).
assert (Rm2 : 0 <= m2 < 256) by exact (tjm_u_range T (48 * i + 2) 1).
assert (Rm3 : 0 <= m3 < 256) by exact (tjm_u_range T (48 * i + 3) 1).
assert (Rm4 : 0 <= m4 < 256) by exact (tjm_u_range T (48 * i + 4) 1).
assert (Rm5 : 0 <= m5 < 256) by exact (tjm_u_range T (48 * i + 5) 1).
assert (Rls : 0 <= ls < 2 ^ 64) by exact (tjm_u_range T (48 * i + 40) 8).
assert (Rage : 0 <= age < 2 ^ 64) by (unfold age, age_of; destruct (ls <? now) eqn:X; [apply Z.ltb_lt in X; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia | lia]).
pose proof ASAN_CEIL_range as HAC. unfold ASAN_CEIL in HAC.
assert (HF8hi2 : F / 8 <= 17592185044960) by (apply Z.div_le_upper_bound; lia).
assert (Ht : 4096 <= t /\ t + 400 <= 140737479966720) by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
unfold w64 in E721, E722, E723, E734, E733.
assert (Hsepp : sepp = VAL (A_OBJ 41) \/ sepp = VAL (A_OBJ 40)) by (unfold sepp; destruct (i =? 0); [left | right]; reflexivity).
assert (Htd0 : 0 <= t / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Htd40 : 0 <= (t + 40) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Hel : t <= e /\ e + 48 <= t + 400) by (unfold e; lia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
rrw HS (28%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 740 40) (SLit 3)) (SOff 32 0))
ltac:(idtac; rewrite (tjm_U_sh Ew 740 e 40 E740 ltac:(unfold e; lia) ltac:(unfold e; lia) E32);
rewrite (U_atom Ew 734 _ E734) by (unfold SB; lia);
unfold e; replace (t + 48 * i + 40) with ((t + 40) + (6 * i) * 8) by lia; rewrite Z.div_add by lia; lia).
rrw HS (7%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 740 0) (SLit 3)) (SOff 32 0))
ltac:(idtac; rewrite (tjm_U_sh Ew 740 e 0 E740 ltac:(unfold e; lia) ltac:(unfold e; lia) E32);
rewrite (U_atom Ew 723 _ E723) by (unfold SB; lia);
unfold e; replace (t + 48 * i + 0) with (t + (6 * i) * 8) by lia; rewrite Z.div_add by lia; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres3; clear - Ho Hsp1 HSK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob307 Hob308 Huar;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
assert (VM : forall c n, 0 <= c -> c + Z.of_nat n <= 48 ->
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (e + c) n (disco_table_c.u_at T (48 * i + c) n)).
{ intros c n Hc Hn. replace (e + c) with (t + (48 * i + c)) by (unfold e; lia).
apply (tjm_val_at SEGS _ t T (48 * i + c) n HgT); [lia | rewrite HlenT; lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 0 48 0 0
[YP09.mkChunk 0 (CVal 1 (SOff 777 0)); YP09.mkChunk 1 (CVal 1 (SOff 778 0)); YP09.mkChunk 2 (CVal 1 (SOff 779 0));
YP09.mkChunk 3 (CVal 1 (SOff 780 0)); YP09.mkChunk 4 (CVal 1 (SOff 781 0)); YP09.mkChunk 5 (CVal 1 (SOff 782 0));
YP09.mkChunk 40 (CVal 8 (SOff 783 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740, unsigned_lit_small by (unfold e; lia); split; [unfold e; lia|]; split; [unfold e; lia|]; split; [intros o Ho; lia|];
repeat apply Forall_cons; try apply Forall_nil;
(eapply chunk_ok_val; [cbn [sv_denot]; first [rewrite E777 | rewrite E778 | rewrite E779 | rewrite E780 | rewrite E781 | rewrite E782 | rewrite E783];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | ]);
first [exact (VM 0 1%nat ltac:(lia) ltac:(cbn; lia)) | exact (VM 1 1%nat ltac:(lia) ltac:(cbn; lia))
| exact (VM 2 1%nat ltac:(lia) ltac:(cbn; lia)) | exact (VM 3 1%nat ltac:(lia) ltac:(cbn; lia))
| exact (VM 4 1%nat ltac:(lia) ltac:(cbn; lia)) | exact (VM 5 1%nat ltac:(lia) ltac:(cbn; lia))
| exact (VM 40 8%nat ltac:(lia) ltac:(cbn; lia))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hel Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob307 Hob308 Huar
Ht Htlo Hthi HTsep HTapp HTimg HTceil HT4096 Hi8 HAC HF8hi2;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, ASAN_CEIL in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 740 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E740, unsigned_lit_small by (unfold e; lia); change (2 ^ 3) with 8;
split; [unfold e; lia|]; split; [unfold e; replace (t + 48 * i) with (t + (6 * i) * 8) by lia; rewrite Z_mod_plus_full; exact Ht8 | lia])) as HS3;
clear HS; rename HS3 into HS end.
tjm_bytef HS 777%nat E777. tjm_bytef HS 778%nat E778. tjm_bytef HS 779%nat E779.
tjm_bytef HS 780%nat E780. tjm_bytef HS 781%nat E781. tjm_bytef HS 782%nat E782.
norm_ss HS.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
shok_auto_with SHOK (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) [mkSHE 740 0 48]
ltac:(idtac; apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) Ev (SOff 32 0) 740 t 400 e 0 48 HraT);
[ rewrite (U_atom Ev 32 SB E32) by (unfold SB; lia); reflexivity
| rewrite (U_atom Ev 740 e E740) by lia; reflexivity
| lia | lia
| intros x Hx; cbn [Z.min Z.max] in Hx; clear - Hx Hel Hi8 Ht Htlo Hthi HTapp HAC;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia ]) end.
lazymatch goal with |- SRr _ _ _ ?Q =>
assert (KC : forall (v0 v1 : word) (msc : machine_state) mdc,
ajournal SEGS B STK (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msc) mdc k ->
garr8 SEGS (mrestrict (w_H W3) (ms_mem msc)) buf (acc ++ [0]) ->
st_ok_pi SEGS VAL (havoc Ew 785 [v0; v1]) ss_tjmC (restrict (w_H W3) msc) ->
SRr SEGS W3 (mkCfg msc mdc) Q) end.
{ clear HS HJ SHOK Hgarr.
intros v0 v1 msc mdc HJ Hgarr HS.
norm_ss HS.
hei_pose Ew 785%nat [v0; v1].
rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => rename Ev into Ec end. clear HEv.
assert (F32 : ew Ec 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
pose proof (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE HJ) as HKP.
unfold tj_keep in HKP. cbn [c_ly c_S c_t c_T] in HKP.
destruct HKP as (HRODc & HgTc & ((cidc & posc & _) & _ & HraTc)).
shok_auto_with SHOK (SOff 32 0) Ec (mrestrict (w_H W3) (ms_mem msc)) [mkSHE 740 0 48]
ltac:(idtac; apply (shent_ok_of_range SEGS (w_H W3) (ms_mem msc) Ec (SOff 32 0) 740 t 400 e 0 48 HraTc);
[ rewrite (U_atom Ec 32 SB F32) by (unfold SB; lia); reflexivity
| rewrite (U_atom Ec 740 e E740) by lia; reflexivity
| lia | lia
| intros x Hx; cbn [Z.min Z.max] in Hx; clear - Hx Hel Hi8 Ht Htlo Hthi HTapp HAC;
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia ]).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
tjm_kg Hgarr HFr AG. clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof tj_snp_cr as Hcr.
assert (F12 : ew Ec 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (F13 : ew Ec 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (F3 : ew Ec 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (F4 : ew Ec 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
pose proof (img_env_atomP (PI := PI) Ec 283 ltac:(let H := rnHEI Ec in exact H) ltac:(unfold A_TEXT, A_LIM; lia)) as E283.
pose proof (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE HJ) as HKx.
unfold tj_keep in HKx. cbn [c_ly c_S c_t c_T] in HKx. destruct HKx as (HRODx & _ & _).
pose proof TJS as (_ & _ & Hf42 & _ & _ & _ & _ & _ & _ & _ & Hs40 & Hs41 & _).
set (sepS := if Nat.eqb (Z.to_nat i) 0 then (@nil Z) else [44]).
assert (HSEP : exists sk, tj_ro_at sk sepS /\ sepp = VAL (A_OBJ sk)).
{ unfold sepS, sepp. destruct (Z.eqb_spec i 0) as [Hi0 | Hi0].
- exists 41%nat. rewrite Hi0. split; [exact Hs41 | reflexivity].
- exists 40%nat. replace (Nat.eqb (Z.to_nat i) 0) with false by (symmetry; apply Nat.eqb_neq; lia). split; [exact Hs40 | reflexivity]. }
destruct HSEP as (sk & Hsk & Hskv).
assert (Rsep : 0 <= sepp < 2 ^ 64) by (destruct Hsepp as [-> | ->]; apply pa_val_range).
pose proof (tj_lemmas.tj_P1_eq 335160 341392 8 0 408 3 T ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(lia) ltac:(lia) HlenT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) i ltac:(lia)) as HP1.
assert (HL1 : (length (P1 (Z.to_nat i) (reac_disco_table_json_c.tj_entry T i)) <= 28)%nat)
by (rewrite HP1; destruct (Nat.eqb (Z.to_nat i) 0); cbn; lia).
rregU HS (10%bv : bv 5) (buf + L) ltac:(idtac; rewrite U_SAlu; cbn [zalu_raw];
rewrite (U_atom Ec 12 buf F12), (U_atom Ec 733 L E733) by lia; apply zcanon_id; unfold M64; lia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(idtac; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw];
rewrite (U_atom Ec 13 cap F13), (U_atom Ec 733 L E733) by lia; rewrite U_SLit; apply tjm_csub; [reflexivity | lia | lia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra.
prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4. prreg HS (15%bv : bv 5) Qa5.
prreg HS (16%bv : bv 5) Qa6. prreg HS (17%bv : bv 5) Qa7.
rewrite E60, unsigned_lit_small in Qsp by lia.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_region_nth Ev ssx msx 1 _ HS eq_refl) as HRw end.
cbn [ms_mem restrict] in HRw.
pose proof (field_of_region Ec _ 60 sp1 _ (-16) 0 (-16) 0 (-16) 8 (SOff 781 0) m4 HRw
ltac:(rewrite E60; apply unsigned_lit_small; lia) ltac:(cbn [In]; tauto)
ltac:(cbn [sv_denot]; rewrite E781, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(lia)) as VW4.
pose proof (field_of_region Ec _ 60 sp1 _ (-16) 0 (-16) 0 (-8) 8 (SOff 782 0) m5 HRw
ltac:(rewrite E60; apply unsigned_lit_small; lia) ltac:(cbn [In]; tauto)
ltac:(cbn [sv_denot]; rewrite E782, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(lia)) as VW5.
pose proof (rdword_of_val_mem SEGS (w_H W3) _ _ _ VW4 ltac:(lia)) as RW4.
pose proof (rdword_of_val_mem SEGS (w_H W3) _ _ _ VW5 ltac:(lia)) as RW5.
clear HRw VW4 VW5.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (A3 : argZ (ms_regs msx) 3 = sepp) by (tjm_arg HS 3; pose proof (U_atom Ec 784 sepp E784 ltac:(lia)) as HU; unfold U in HU; exact HU);
assert (A4 : argZ (ms_regs msx) 4 = m0) by (tjm_arg HS 4; pose proof (U_atom Ec 777 m0 E777 ltac:(lia)) as HU; unfold U in HU; exact HU);
assert (A5 : argZ (ms_regs msx) 5 = m1) by (tjm_arg HS 5; pose proof (U_atom Ec 778 m1 E778 ltac:(lia)) as HU; unfold U in HU; exact HU);
assert (A6 : argZ (ms_regs msx) 6 = m2) by (tjm_arg HS 6; pose proof (U_atom Ec 779 m2 E779 ltac:(lia)) as HU; unfold U in HU; exact HU);
assert (A7 : argZ (ms_regs msx) 7 = m3) by (tjm_arg HS 7; pose proof (U_atom Ec 780 m3 E780 ltac:(lia)) as HU; unfold U in HU; exact HU) end.
pmkst HS. rewrite HSNPC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs msx) (ms_mem msx) (spZ regs)
(tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL (A_OBJ 42)) tj_f_mac tjm_ps [m4; m5]
(map (argZ (ms_regs msx)) [3; 4; 5; 6; 7] ++ [m4; m5]) [APtr sepS; AInt m0; AInt m1; AInt m2; AInt m3; AInt m4; AInt m5]
(P1 (Z.to_nat i) (reac_disco_table_json_c.tj_entry T i)) cval (sp1 - 16 - spZ regs) (Z_to_bv 64 (BASE + 24028)) _ HJ HRODx) end.
{ unfold spZ at 1. rewrite Qsp, unsigned_lit_small by lia. lia. }
{ replace (sp1 - 16 - spZ regs) with (sp1 - spZ regs + (-1) * 16) by lia. rewrite Z_mod_plus_full.
rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp, F3. exact Hgp. }
{ rewrite Qtp, F4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E283. reflexivity. }
{ exact (tj_snp_consts _ _ HRODx). }
{ eapply Forall_impl; [|exact Hcr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact Hcr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out.
tjm_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tjm_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. tjm_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ apply (tjm_fmt_at 42 tj_f_mac ly3 S3 W3 _ _ _ Hf42 HARc HRODx).
unfold snp_out. tjm_fa2 ltac:(cbn [fst snd]; unfold IMG_LO, IMG_TOP; lia). }
{ exact (tj_ro_fmt_rng 42 tj_f_mac Hf42 ltac:(cbn; lia)). }
{ unfold tj_f_mac; discriminate. }
{ reflexivity. }
{ unfold tjm_ps. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity|]. intros j Hj. cbn [length] in Hj.
destruct j as [|[|j]]; [| |lia]; cbn [nth Z.of_nat].
+ replace (spZ regs + (sp1 - 16 - spZ regs) + 8 * Z.of_nat 0) with (sp1 + -16) by lia. exact RW4.
+ replace (spZ regs + (sp1 - 16 - spZ regs) + 8 * Z.of_nat 1) with (sp1 + -8) by lia. exact RW5. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. cbn [length Z.of_nat]. tjm_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ cbn [map app pf_args_asan]. rewrite A3, A4, A5, A6, A7.
split; [rewrite Hskv; apply (tjm_ptr_arg sk sepS ly3 S3 W3 _ _ _ Hsk HARc HRODx);
unfold snp_out; tjm_fa2 ltac:(cbn [fst snd]; unfold IMG_LO, IMG_TOP; lia)|].
repeat (split; [cbn [pf_arg_asan]; split; [lia | reflexivity]|]). exact I. }
{ cbn [map app SnFF.pf_args_amem]. rewrite A3, Hskv. split; [exact (tj_ro_amem8 sk sepS Hsk) | exact I]. }
{ rewrite HP1. unfold tjm_ps. cbn [pf_text option_map app]. rewrite !tjm_hex by lia. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - 16 - spZ regs)) with (sp1 - 16) in Hfr by lia. rewrite HSNP in Hfr.
set (P := P1 (Z.to_nat i) (reac_disco_table_json_c.tj_entry T i)) in *.
assert (HgM : Z.of_nat (length P) < cap - L -> garr8 SEGS (mrestrict (w_H W3) mem2) buf ((acc ++ P) ++ [0])).
{ intros Hlt. rewrite <- app_assoc. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
- apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) mem2 buf acc); [| exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr))].
intros a Ha. fold L in Ha. apply Hfr; lia.
- fold L. apply tjm_garr8_of_aview. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length P)) as [Hjp | Hjp].
+ rewrite app_nth1 by lia. pose proof (Hwr (Z.of_nat j) ltac:(lia)) as X. rewrite Nat2Z.id in X. exact X.
+ assert (Hj2 : j = length P) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
rewrite Z.min_l in Hnul by lia. exact Hnul. }
reseat HS HJ2 HP2 [2; 3; 4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; tjm_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx') B LAWS). pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?na = _ =>
assert (G13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap G13), (U_atom Ev 733 L E733) by lia;
rewrite U_SLit; apply tjm_csub; [reflexivity | lia | lia]);
assert (U0 : U Ev (SOff na 0) = Z.of_nat (length P)) by (apply U_atom; [exact Qr0 | lia]) end.
paj_run_to_shc RUNTOP HS HJ2 0x5de0. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken BC_LT (sv_denot ?Eb _) _ = _ =>
exact (tjm_bltz_false Eb (SOff 789 0) (Z.of_nat (length P)) U0 ltac:(pose proof HL1; lia) Hc) end. }
assert (HtxtP : reac_disco_table_json_c.tj_text T now =
(acc ++ P) ++ tj_after1 (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
{ rewrite Htxt, (tj_lemmas.tj_rest_step T now i) by lia.
unfold obj_text, tj_after1, tj_after2, tj_after4, tj_e. cbn [c_T c_now]. rewrite <- !app_assoc. reflexivity. }
assert (Hlen : L + Z.of_nat (length P) <= tj_len T now).
{ unfold tj_len. rewrite HtxtP, !length_app, !Nat2Z.inj_add. unfold L. lia. }
paj_run_to_shc RUNTOP HS HJ2 0x5de4. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
psrr_branch_pi RUNP BR HS.
{ lazymatch goal with Hg : branch_taken BC_GEU _ _ = _ |- _ =>
rewrite branch_geu_U, U0, U4 in Hg; apply negb_true_iff, Z.ltb_ge in Hg; rename Hg into Hge end.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
clear_frames.
lazymatch goal with Hj : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof Hj as (HARx & _) end.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
rewrite HF3 in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
fs_rwF HS E529 HFSx.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
{ exact HBASE. }
{ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]. }
{ lazymatch goal with Hj : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact Hj end. }
{ exact HFR. }
{ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [pose proof (Z.mul_le_mono_nonneg_l i 8 EVB HEVB ltac:(lia)) as Hm; lia|].
split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|].
split; [intros _ Hlt'; exfalso; lia|].
intros _ _; reflexivity. }
{ exact HS. } }
{ lazymatch goal with Hg : branch_taken BC_GEU _ _ = _ |- _ =>
rewrite branch_geu_U, U0, U4 in Hg; apply negb_false_iff, Z.ltb_lt in Hg; rename Hg into Hlt end.
paj_run_to_shc RUNTOP HS HJ2 0x5de8. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
assert (HgF : garr8 SEGS (mrestrict (w_H W3) (ms_mem msF)) buf ((acc ++ P) ++ [0]));
[ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 (ms_mem msF) buf ((acc ++ P) ++ [0])); [| exact (HgM Hlt)];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
tjm_chain AG; reflexivity | ] end.
clear_frames.
lazymatch goal with Hj : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => pose proof Hj as (HARm & _) end.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARm Hfin) as (_ & _ & _ & HFSm).
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
rewrite HF3 in HFSm. change (fs_frame_bytes 2 / 8) with 32 in HFSm.
fs_rwF HS E529 HFSm.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E32m : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032) end.
rechunk_off HS 60%nat 128 (SOff 734 0) ltac:(idtac;
lazymatch goal with |- sv_denot ?Ev _ = _ =>
rewrite !(denot_lit_U Ev); f_equal;
rewrite (U_atom Ev 734 _ E734) by (unfold SB; lia);
rewrite (tjm_U_sh Ev 740 e 40 E740 ltac:(lia) ltac:(lia) E32m);
unfold e; replace (t + 48 * i + 40) with ((t + 40) + (6 * i) * 8) by lia; rewrite Z.div_add by lia; lia end).
rechunk_off HS 60%nat 136 (SOff 723 0) ltac:(idtac;
lazymatch goal with |- sv_denot ?Ev _ = _ =>
rewrite !(denot_lit_U Ev); f_equal;
rewrite (U_atom Ev 723 _ E723) by (unfold SB; lia);
rewrite (tjm_U_sh Ev 740 e 0 E740 ltac:(lia) ltac:(lia) E32m);
unfold e; replace (t + 48 * i + 0) with (t + (6 * i) * 8) by lia; rewrite Z.div_add by lia; lia end).
prreg HS (10%bv : bv 5) RA0. rewrite Qr0 in RA0.
ra_join HS ss_tjM 760%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 760%nat 4%nat RA0 E764.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FM (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
{ exact HBASE. }
{ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]. }
{ lazymatch goal with Hj : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact Hj end. }
{ exact HFR. }
{ unfold INV_tjM, tj_lbody, tj_split, tj_wrote. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [exact Hk0|].
split.
{ split; [exact Hperm|].
split; [lazymatch goal with Hj : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
exact (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE Hj) end|].
split; [exact Hcap3|]. split; [exact Hi|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|].
split; [exact E740|]. unfold tj_age. cbn [c_now c_T]. exact E741. }
exists (acc ++ P). split.
{ exists L, (Z.of_nat (length P)).
split; [rewrite ew_havoc_old by (cbn; lia); exact E733|]. split; [exact E764|].
split; [lia|]. split; [lia|]. rewrite length_app, Nat2Z.inj_add. unfold L. lia. }
split; [rewrite length_app, Nat2Z.inj_add; unfold L; lia|].
split; [exact HtxtP|]. exact HgF. }
{ exact HS. } } }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5cf4. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
tjm_kg Hgarr HFr AG. clear HF HFr HG.
rrw HS (23%bv : bv 5) (SOff 740 0)
ltac:(idtac; rewrite (U_atom Ew 740 e E740) by lia; rewrite U_SAlu; cbn [zalu_raw];
rewrite (U_atom Ew 10 t E10) by lia; rewrite (U_atom Ew 721 (48 * i) E721) by lia;
rewrite zcanon_id by (unfold M64; lia); reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
tjm_kg Hgarr HFr AG. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: paj_run_tok RUN HS HJ SHOK Bspan; [ awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0 | ].
all: tjm_kg Hgarr HFr AG. all: clear HF HFr HG.
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5d24; [ awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0 | ].
all: tjm_kg Hgarr HFr AG. all: clear HF HFr HG.
all: pose proof (img_env_atomP (PI := PI) Ew 282 ltac:(let H := rnHEI Ew in exact H) ltac:(unfold A_TEXT, A_LIM; lia)) as E282.
all: pose proof (img_env_atomP (PI := PI) Ew 281 ltac:(let H := rnHEI Ew in exact H) ltac:(unfold A_TEXT, A_LIM; lia)) as E281.
all: pose proof (pa_val_range 282) as R282. all: pose proof (pa_val_range 281) as R281.
all: assert (Rsep : 0 <= sepp < 2 ^ 64) by (destruct Hsepp as [-> | ->]; assumption).
all: lazymatch goal with Hc : branch_taken BC_GEU _ _ = _ |- _ =>
rewrite branch_geu_U, (U_atom Ew 783 ls E783), (U_atom Ew 11 now E11) in Hc by lia end.
all: lazymatch goal with Hc : branch_taken BC_EQ _ _ = _ |- _ =>
rewrite branch_eq_U, (U_atom Ew 721 (48 * i) E721), U_lit in Hc by lia end.
all: rrw HS (19%bv : bv 5) (SOff 741 0)
ltac:(idtac; rewrite (U_atom Ew 741 age E741) by lia;
lazymatch goal with Hc : negb (_ <? _) = _ |- _ =>
first [ apply negb_true_iff, Z.ltb_ge in Hc; rewrite U_lit by lia; unfold age, age_of; rewrite (proj2 (Z.ltb_ge _ _) Hc); reflexivity
| apply negb_false_iff, Z.ltb_lt in Hc; rewrite (tjm_age_U Ew now ls E11 E783) by lia;
unfold age, age_of; rewrite (proj2 (Z.ltb_lt _ _) Hc); reflexivity ] end).
all: rrw HS (13%bv : bv 5) (SOff 784 0)
ltac:(idtac; rewrite (U_atom Ew 784 sepp E784) by lia;
lazymatch goal with Hc : (_ * _ =? 0) = _ |- _ =>
first [ apply Z.eqb_eq in Hc; rewrite (U_atom Ew 282 _ E282) by lia; unfold sepp;
rewrite (proj2 (Z.eqb_eq i 0) ltac:(lia)); reflexivity
| apply Z.eqb_neq in Hc; rewrite (U_atom Ew 281 _ E281) by lia; unfold sepp;
rewrite (proj2 (Z.eqb_neq i 0) ltac:(lia)); reflexivity ] end).
all: tjm_havoc2 HS.
all: tjm_noconds HS.
all: eapply KC; [exact HJ | exact Hgarr | exact HS].
Qed.
End h.
End f.
End d.
