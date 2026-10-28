(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YP0n YP0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL01 YN03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14 YI07 YI19 YI15 UI5b UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition lits_FILE (buffered : bool) : list (option Z) :=
[Some 4; Some 0; Some 0; Some ubs0_A_stdio_close; (if buffered then None else Some 0); (if buffered then None else Some 0); Some 0;
(if buffered then None else Some 0); Some ubs0_A_stdio_read; Some ubs0_A_stdio_write; Some ubs0_A_stdio_seek; None; Some 1024;
Some 0; Some 0; None; Some 0; Some 0; Some (if buffered then 4294967295 else 0); Some 4294967295; Some 4294967295;
Some 0; Some 0; Some 0; Some 0; Some 0; Some 0; Some 0; Some 0; Some 0; Some 0].
Definition reg_got : YP09.region :=
YP09.mkRegion None ubs0_D_got_stack_chk_guard (ubs0_D_got_stack_chk_guard + 8) 0 0
[mkChunk ubs0_D_got_stack_chk_guard (CVal 8 (SLit ubs0_D_stack_chk_guard))].
Definition reg_guard : YP09.region :=
YP09.mkRegion None ubs0_D_stack_chk_guard (ubs0_D_stack_chk_guard + 8) 0 0
[mkChunk ubs0_D_stack_chk_guard (CVal 8 (SOff 63%nat 0))].
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_errno_low_f : errno_addr ubs0_msyms + 4 <= alloc_ceiling.
Proof using. pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Lemma ubs0_sink_code_ok : sink_code_ok.
Proof using. unfold sink_code_ok. repeat split; vm_compute; congruence. Qed.
Lemma regs_ok_pin : forall E sr (regs : bvmap 5 word) (r : reg) z,
regs_ok E sr regs -> bv_eqb r 0 = false -> getr regs r = Z_to_bv 64 z -> regs_ok E (sr_set sr r (SLit z)) regs.
Proof using.
intros E sr regs r z H Hr0 Hz r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. exact Hz.
- rewrite sr_get_set_other by exact Hne. apply H.
Qed.
Lemma U_sub_form : forall E a b, U E b <= U E a -> U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = U E a - U E b.
Proof using.
intros E a b Hle. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change (-1 mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite Zplus_mod_idemp_r.
replace (U E a + U E b * (2 ^ 64 - 1)) with (U E a - U E b + U E b * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_mul1 : forall E a, U E (SMd M_MUL a (SLit 1)) = U E a.
Proof using.
intros E a. rewrite U_SMd, U_SLit. cbn [zmd_raw]. rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite Z.mul_1_r. apply zcanon_id. apply U_range.
Qed.
Lemma U_iovcnt : forall E a b,
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) (SLit 1)) (SLit 0)) = (if U E a =? U E b then 1 else 2).
Proof using.
intros E a b. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 0), (zcanon_id 1) by (unfold M64; lia).
pose proof (Z_lxor_range (U E a) (U E b) Ra Rb) as Hx.
rewrite (zcanon_id (Z.lxor (U E a) (U E b))) by (unfold M64; exact Hx).
destruct (Z.eqb_spec (U E a) (U E b)) as [Eab|Nab].
- rewrite Eab, Z.lxor_nilpotent. cbn. reflexivity.
- assert (Z.lxor (U E a) (U E b) <> 0) by (intros H0; apply Z.lxor_eq in H0; contradiction).
replace (0 <? Z.lxor (U E a) (U E b)) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.
Lemma U_sub_form_gen : forall E a b z, z mod 2 ^ 64 = 2 ^ 64 - 1 -> U E b <= U E a -> U E (SAlu ALU_ADD a (SMd M_MUL b (SLit z))) = U E a - U E b.
Proof using.
intros E a b z Hz Hle. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64. rewrite Hz.
rewrite Zplus_mod_idemp_r.
replace (U E a + U E b * (2 ^ 64 - 1)) with (U E a - U E b + U E b * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_add2 : forall E a b, U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = U E a + U E b.
Proof using.
intros E a b H. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma garr8_copy : forall segs (m1 m2 : word -> option byte) src d l,
garr8 segs m1 src l -> (forall i, 0 <= i < Z.of_nat (length l) -> mbyte segs m2 (d + i) = mbyte segs m1 (src + i)) ->
garr8 segs m2 d l.
Proof using.
intros segs m1 m2 src d l H Hcp j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk). cbn [Z.of_nat] in *. rewrite Z.add_0_r in *.
rewrite Hcp by lia. exact Hv.
Qed.
Lemma region_kept_abs_ro : forall segs E (mem mem' : word -> option byte) lo hi cs d n,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem' x = mem x) ->
0 <= lo -> hi <= 2 ^ 64 -> (hi <= d \/ d + n <= lo) ->
region_kept segs E mem mem' (YP09.mkRegion None lo hi 0 0 cs).
Proof using.
intros segs E mem mem' lo hi cs d n Hout Hlo Hhi Hdis. split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; intros a Ha; [|lia].
unfold mbyte. rewrite (Hout (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma blk_off_img : forall lo len f m,
covered ubs0_msyms lo len = true -> 0 < m -> 0 < len ->
(forall i, 0 <= i < m -> ~ in_img ubs0_msyms (f + i)) -> f + m <= lo \/ lo + len <= f.
Proof using.
intros lo len f m Hc Hm Hl Hno.
destruct (Z_le_gt_dec (f + m) lo); [left; lia|]. destruct (Z_le_gt_dec (lo + len) f); [right; lia|]. exfalso.
destruct (Z_le_gt_dec lo f).
- apply (Hno 0); [lia|]. apply (covered_sound ubs0_msyms lo len); [exact Hc | lia].
- apply (Hno (lo - f)); [lia|]. replace (f + (lo - f)) with lo by lia. apply (covered_sound ubs0_msyms lo len); [exact Hc | lia].
Qed.
Lemma ubs0_stdio_env_kept : forall FP (mem mem' : word -> option byte),
img_kept ubs0_msyms FP mem mem' -> stdio_env ubs0_msyms mem -> stdio_env ubs0_msyms mem'.
Proof using.
intros FP mem mem' Hk Henv.
assert (Hb : forall a, env_addr a -> ~ (332136 <= a < 332144) -> mbyte ubs0segs mem' a = mbyte ubs0segs mem a).
{ intros a Hea Hnh. destruct (skl_env ubs0_msyms a Hea) as (T1 & T2 & T3 & T4).
apply (Hk a T1 T2 T3 T4). intros [_ Hh]. change sk_ofl_head with 332136 in Hh. lia. }
destruct Henv as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). unfold stdio_env.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- eapply (val_mem_frame ubs0_msyms); [|exact H1]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
apply Hb; [right; left; lia | change sk_threaded with 331065 in Hx; lia].
- eapply (val_mem_frame ubs0_msyms); [|exact H2]. intros x Hx. change (Z.of_nat 4) with 4 in Hx.
apply Hb; [right; right; left; lia | change sk_ofl_lock with 332128 in Hx; lia].
- eapply garr8_frame; [exact H3|]. intros x Hx. cbn [length app sink_path_Z] in Hx.
apply Hb; [right; right; right; left; lia | change sk_path_addr with 66308 in Hx; lia].
- eapply garr8_frame; [exact H4|]. intros x Hx. cbn [length app sink_mode_Z] in Hx.
apply Hb; [right; right; right; right; left; lia | change sk_mode_addr with 66210 in Hx; lia].
- eapply garr8_frame; [exact H5|]. intros x Hx. cbn [length app sink_trailer_Z] in Hx.
apply Hb; [right; right; right; right; right; left; lia | change sk_trailer_addr with 66321 in Hx; lia].
- eapply garr8_frame; [exact H6|]. intros x Hx. cbn [length sink_rwa_Z] in Hx.
apply Hb; [do 6 right; left; lia | change sk_rwa_addr with 66448 in Hx; lia].
- eapply garr8_frame; [exact H7|]. intros x Hx. cbn [length sink_highs_Z] in Hx.
apply Hb; [do 7 right; left; lia | change sk_highs_addr with 66488 in Hx; lia].
- eapply garr8_frame; [exact H8|]. intros x Hx. cbn [length sink_ones_Z] in Hx.
apply Hb; [do 8 right; lia | change sk_ones_addr with 66504 in Hx; lia].
Qed.
Lemma val_of_zero_chunk : forall E (mem : word -> option byte) base o l off n,
chunk_ok ubs0segs E mem base (mkChunk o (CZero l)) -> o <= off -> off + Z.of_nat n <= o + l ->
val_mem ubs0segs mem (base + off) n 0.
Proof using.
intros E mem base o l off n H Ho Hl k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
destruct (H (off - o + Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. injection Hb1 as <-.
replace (base + o + (off - o + Z.of_nat k)) with (base + off + Z.of_nat k) in Hb2 by lia. rewrite Hb2.
f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma obj_at_of_chunks_gen2 : forall E (mem : word -> option byte) a (cs : list YP09.chunk) lay vals,
Forall (chunk_ok ubs0segs E mem a) cs -> lay_widths_ok lay = true ->
Forall2 (fun (f : Z * N) v => 0 <= v < 2 ^ (8 * Z.of_N (snd f)) /\
((exists e, In (mkChunk (fst f) (CVal (snd f) e)) cs /\ bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N (snd f)) = v) \/
(v = 0 /\ exists o l, In (mkChunk o (CZero l)) cs /\ o <= fst f /\ fst f + Z.of_N (snd f) <= o + l))) lay vals ->
obj_at ubs0segs mem a lay vals.
Proof using.
intros E mem a cs lay vals Hcs. revert vals. induction lay as [|f lay IH]; intros vals Hw H2; inversion H2; subst; [exact I|].
unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw]. apply Z.leb_le in Hw1.
cbn [obj_at]. split; [|apply IH; assumption].
rewrite Forall_forall in Hcs.
match goal with H : _ /\ _ |- _ => destruct H as (Hr & [(e & Hin & He) | (-> & o & l & Hin & Ho & Hl)]) end.
- split; [|exact Hr]. destruct f as [off w]. cbn [fst snd] in *. exact (val_of_chunk_ok_mod ubs0segs E mem a off w e _ (Hcs _ Hin) He Hw1).
- split; [|exact Hr]. destruct f as [off w]. cbn [fst snd] in *.
apply (val_of_zero_chunk E mem a o l off (N.to_nat w) (Hcs _ Hin) Ho). rewrite N_nat_Z. exact Hl.
Qed.
End c.
Ltac resume_reg_sr segs r :=
lazymatch goal with
| Hregs : regs_ok ?E ?sr _ |- _ => let rv := eval vm_compute in (sr_get sr r) in resume_sv_sr segs rv
end.
Ltac fld_in := repeat first [left; reflexivity | right].
Ltac fld_lit := split; [vm_compute; split; [intros Hx; discriminate Hx | reflexivity] | eexists; split; [fld_in | vm_compute; reflexivity]].
Ltac fld_off HEk :=
cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; lia
| eexists; split; [fld_in | cbn [sv_denot]; ew_havoc;
lazymatch type of HEk with _ = Z_to_bv 64 ?v => rewrite HEk, (unsigned_lit_small v) by lia end;
rewrite unsigned_lit_small by lia;
change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; rewrite Z.mod_small by lia; lia]].
Ltac fld_atom HEk :=
cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; lia
| eexists; split; [fld_in | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; rewrite HEk, unsigned_lit_small by lia;
change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; apply Z.mod_small; lia]].
Ltac fld_lit2 := split; [vm_compute; split; [intros Hx; discriminate Hx | reflexivity] | left; eexists; split; [fld_in | vm_compute; reflexivity]].
Ltac fld_off2 HEk :=
cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; lia
| left; eexists; split; [fld_in | cbn [sv_denot]; ew_havoc;
lazymatch type of HEk with _ = Z_to_bv 64 ?v => rewrite HEk, (unsigned_lit_small v) by lia end;
rewrite unsigned_lit_small by lia;
change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; rewrite Z.mod_small by lia; lia]].
Ltac fld_atom2 HEk :=
cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; lia
| left; eexists; split; [fld_in | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; rewrite HEk, unsigned_lit_small by lia;
change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; apply Z.mod_small; lia]].
Ltac find_zero_chunk cs off w :=
lazymatch cs with
| (mkChunk ?o (CZero ?l)) :: ?rest =>
let ok := eval vm_compute in (Z.leb o off && Z.leb (off + w) (o + l))%bool in
lazymatch ok with true => constr:((o, l)) | false => find_zero_chunk rest off w end
| _ :: ?rest => find_zero_chunk rest off w
end.
Ltac fld_zero := cbn [fst snd]; split; [change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32; lia | right; split; [reflexivity |
lazymatch goal with |- exists o l, In _ ?cs /\ o <= ?off /\ ?off + ?w <= o + l =>
let r := find_zero_chunk cs off w in lazymatch r with (?o, ?l) => exists o, l; split; [fld_in | lia] end end]].
