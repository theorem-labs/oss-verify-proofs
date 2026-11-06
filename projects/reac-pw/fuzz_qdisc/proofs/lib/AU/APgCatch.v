(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes
   6ebe35ba632 (itself ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, ACeu.v, AD28.v and ACeh.v at
   c8557374ad2e) for reac-pw/fuzz_qdisc's image A: it walks reac_qdisc_etf_catchup_slots against
   lib/A/QPgCSpec.v's qdisc_slots_specX on the CONCRETE image tfibsegs / tfibtbl_lib, without knock's PAImg layer,
   object region, shadow entry, GOT and shadow-cell regions or obj_at post; the divisor cell 0x10350 is a base-None
   region with the literal chunk QD_MAGIC, paid by the contract's val_mem premise; knock's branch arithmetic is
   replaced by U_T300 / U_use / U_zx32 / U_prod / U_quot / U_sextw0 / br_ge0 and lib/Prog/qdisc_div.v's lemmas;
   the walk's plumbing (qd_run, qd_keep, qd_branch, qd_r10, qd_leaf) is shared with the check_slots walk. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgSlots.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062):
   the imports move to the lib/AU twins and lib/AU/APgRt.v (entry A_QD_SLOTS 0x7e984, divisor cell A_QD_MAGIC
   0x10350). The function's 24 instructions are the asan image's, every pc 0x38 higher, the same registers and
   immediates, and the divisor load `auipc a0,0xfff92` 0x7e9c8 / `ld a0,-0x678(a0)` forms the same cell 0x10350
   (capstone 5.0.7 over both pinned images); the proof text is the A file's. The function has no UBSan check. *)
(* reac_qdisc_etf_catchup_slots, 0x7e984, 96 bytes, 24 instructions: a pure leaf (no sp move, no store, no shadow
   check). a0 = lead (0 <= lead <= 65535), a1 = fps (an int). The engine stops at three branches; each is split and
   its recorded condition turned into a Z fact:
   B1 0x7e988 blez a1 -- the engine's BC_GE 0 fps, which br_ge0 makes `fps <= 0`.
      TAKEN (fps <= 0): to 0x7e9dc, a0 = sext.w a2 = 1 = slots_spec lead fps (qdisc_spec_nonpos).
      not taken (0 < fps): 0x7e98c-0x7e998 give u = max 0 (lead - 300) (U_use, the branchless form
      qdisc_usable_bv states for the plain image), 0x7e9a0-0x7e9a4 zero-extend it (U_zx32), 0x7e9a8 gives
      p = u * fps, which does not wrap (U_prod, qdisc_product_range: p < 2^47).
   B2 0x7e9b0 bltu a1,a0 -- p < 10^6.
      TAKEN: to 0x7e9dc, a0 = 1 = slots_spec (qdisc_spec_small).  not taken: 10^6 <= p.
   B3 0x7e9c4 bltu a2,a1 -- 10^12 + 999999 < p.
      TAKEN: to 0x7e9d8 mv a2,a0 with a0 = 10^6: a0 = 10^6 = slots_spec (qdisc_spec_cap).
      not taken (p <= 10^12 + 999999): 0x7e9c8-0x7e9d4 load QD_MAGIC from 0x10350 (the slots_entry region),
      mulhu, srli 18 = p / 10^6 (U_quot, qdisc_magic_shift), sext.w keeps it (U_sextw0, qdisc_n_range):
      a0 = p / 10^6 = slots_spec (qdisc_spec_mid).
   All four paths end at 0x7e9e0 ret. Every region of every state is read-only (kwr_ro), so no byte is written and
   the contract's memory clause holds at every address. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import QPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import APgRt.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec qdisc_div.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the arithmetic of the two leaves, over the engine's symbolic values ---- *)
(* `addiw t, lead, -300` on a u16 lead: t = (lead - 300) mod 2^64 *)
Lemma U_T300 : forall E n lead, ew E n = Z_to_bv 64 lead -> 0 <= lead <= 65535 ->
U E (SAluw ALU_ADD (SOff n 0) (SLit (-300))) = (lead - 300) mod 2 ^ 64.
Proof.
intros E n lead Hn Hl. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E n lead Hn) by lia. rewrite U_SLit.
change (zcanon (-300) mod 2 ^ 32) with 4294966996.
rewrite (Z.mod_small lead (2 ^ 32)) by lia.
replace (bv_swrap 32 (lead + 4294966996)) with (lead - 300).
- unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
- unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
replace (lead + 4294966996 + 2 ^ 31) with ((lead - 300 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* `addiw t, lead, -300; sltu c, lead, t; addi c, c, -1; and u, c, t`: u = max 0 (lead - 300)
   (the branchless form lib/Prog/qdisc_div.v's qdisc_usable_bv states for the plain image) *)
Definition sv_use (n : nat) : sv :=
SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff n 0) (SAluw ALU_ADD (SOff n 0) (SLit (-300)))) (SLit (-1)))
(SAluw ALU_ADD (SOff n 0) (SLit (-300))).
Lemma U_use : forall E n lead, ew E n = Z_to_bv 64 lead -> 0 <= lead <= 65535 ->
U E (sv_use n) = Z.max 0 (lead - 300).
Proof.
intros E n lead Hn Hl. unfold sv_use. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n lead Hn) by lia. rewrite (U_T300 E n lead Hn Hl). rewrite U_SLit.
unfold zcanon, M64.
destruct (Z.ltb_spec lead 300) as [Hlt|Hge].
- replace ((lead - 300) mod 2 ^ 64) with (lead - 300 + 2 ^ 64)
by (rewrite <- (Z.mod_add (lead - 300) 1) by lia; rewrite Z.mod_small by lia; lia).
rewrite (proj2 (Z.ltb_lt lead (lead - 300 + 2 ^ 64))) by lia.
change ((1 mod 2 ^ 64 + (-1) mod 2 ^ 64) mod 2 ^ 64) with 0.
rewrite Z.land_0_l. change (0 mod 2 ^ 64) with 0. lia.
- rewrite (Z.mod_small (lead - 300) (2 ^ 64)) by lia.
rewrite (proj2 (Z.ltb_ge lead (lead - 300))) by lia.
change ((0 mod 2 ^ 64 + (-1) mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. rewrite !(Z.mod_small (lead - 300)) by lia. lia.
Qed.
(* `slli 32; srli 32` of a value below 2^32 *)
Lemma U_zx32 : forall E e u, U E e = u -> 0 <= u < 2 ^ 32 -> U E (SAlu ALU_SRL (SAlu ALU_SLL e (SLit 32)) (SLit 32)) = u.
Proof.
intros E e u He Hu. rewrite !U_SAlu. cbn [zalu_raw]. rewrite He, !U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (u * 2 ^ 32)) by (unfold M64; nia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* `mul p, u, fps` for a positive int fps: no wrap (lib/Prog/qdisc_div.v's qdisc_product_range) *)
Lemma U_prod : forall E e m u fps, U E e = u -> 0 <= u <= 65235 -> ew E m = Z_to_bv 64 fps -> 0 < fps < 2 ^ 31 ->
U E (SMd M_MUL e (SOff m 0)) = u * fps.
Proof.
intros E e m u fps He Hu Hm Hf. rewrite U_SMd. cbn [zmd_raw]. rewrite He, (U_atom E m fps Hm) by lia.
apply zcanon_id. unfold M64. nia.
Qed.
(* `mulhu q, p, QD_MAGIC; srli q, q, 18` = p / 10^6 (lib/Prog/qdisc_div.v's qdisc_magic_shift); the literal is
   QPgCSpec.QD_MAGIC, written out because the engine's SLit holds the number *)
Lemma U_quot : forall E e p, U E e = p -> 0 <= p <= 1000000999999 ->
U E (SAlu ALU_SRL (SMd M_MULHU e (SLit 4835703278458516699)) (SLit 18)) = p / 1000000.
Proof.
intros E e p He Hp. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite He, !U_SLit.
change (zcanon 4835703278458516699) with 4835703278458516699. change (Z.land (zcanon 18) 63) with 18.
change (Z.of_N 64) with 64. unfold zcanon, M64. replace (2 ^ 64) with 18446744073709551616 by reflexivity.
rewrite (qdisc_magic_shift p Hp). pose proof (qdisc_n_range p Hp). apply Z.mod_small. lia.
Qed.
(* `sext.w a0, x` of a small non-negative x, as the engine leaves it *)
Lemma U_sextw0 : forall E e q, U E e = q -> 0 <= q < 2 ^ 31 -> U E (SAluw ALU_ADD (SAlu ALU_ADD e (SLit 0)) (SLit 0)) = q.
Proof.
intros E e q He Hq. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite He, !U_SLit.
unfold zcanon, M64. rewrite !Z.mod_0_l by lia. rewrite !Z.add_0_r. rewrite !(Z.mod_small q) by lia.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
(* `blez fps` is the engine's BC_GE 0 fps: a signed compare of the sign-extended int *)
Lemma br_ge0 : forall E n fps, ew E n = Z_to_bv 64 fps -> - 2 ^ 31 <= fps < 2 ^ 31 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = negb (0 <? fps).
Proof.
intros E n fps Hn Hf. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 0) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
rewrite (bv_swrap_small 64 fps) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
reflexivity.
Qed.
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in [knock A/APgStep.v:91-99 kept_step,
   with knock's object zone made a parameter] *)
Lemma kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m1 a = aview tfibsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m2 a = aview tfibsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Definition qd_magic_region : YP09.region :=
YP09.mkRegion None A_QD_MAGIC (A_QD_MAGIC + 8) 0 0 [YP09.mkChunk A_QD_MAGIC (CVal 8 (SLit QD_MAGIC))].
Definition slots_regions : smem := [ qd_magic_region ].
Definition ss_slots : sstate := mkSS A_QD_SLOTS sr_atoms slots_regions None (mkFacts [] [] []).
(* ---- the walk's plumbing, shared with APgCheck.v ---- *)
(* the read-only write-range obligation of a state with no writable window *)
Ltac kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
(* one run of the engine to its next stop [knock A/APgStep.v:446, paj_run_tok without the PAImg layer] *)
Ltac qd_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SHOK RTBspan; [awr | ] end.
(* fold the run's frame into the kept-memory fact KE [knock A/APgStep.v:378-385 kkeep] *)
Ltac qd_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the branch the engine cannot decide, with its condition named [knock A/APgLoop0.v:265-268 br_split] *)
Ltac qd_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a0 at the stop, as the engine's symbolic value *)
Ltac qd_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.
(* the `ret` leaf [knock A/APgStep.v:402-443, lib/A/AE37.v:212-233]: post is qd_post_slots or qd_post_check,
   mtac closes the memory clause from KE, vtac the clause on a0 (catchup only) from R10 *)
Ltac qd_leaf mtac vtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in qd_r10 R10;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [try unfold EV_slots; try unfold EV_check; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
first [ split; [mtac | rewrite R10; vtac] | mtac ]
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Lemma slots_entry : forall (W : world tfibsegs) regs memc,
val_mem tfibsegs (mrestrict (w_H W) memc) A_QD_MAGIC 8 QD_MAGIC ->
st_ok tfibsegs (Ereg regs rt_extra) ss_slots (restrict (w_H W) (mkst regs (Z_to_bv 64 A_QD_SLOTS) memc (seg_rom tfibsegs))).
Proof.
intros W regs memc HV.
rewrite restrict_mkst_fx.
set (E := Ereg regs rt_extra).
unfold ss_slots. apply (entry_st_ok_full tfibsegs); change (Ereg regs rt_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold slots_regions, qd_magic_region. repeat apply Forall_cons; try apply Forall_nil.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_QD_MAGIC.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x10350) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x10350 8 (SLit QD_MAGIC) QD_MAGIC); [reflexivity | unfold QD_MAGIC; zside | zside |].
exact HV.
- apply pairwise_disjoint_of_extents.
unfold slots_regions, qd_magic_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Theorem qdisc_pb_slotsX : qdisc_slots_specX tfibsegs B MT A_QD_SLOTS A_QD_MAGIC.
Proof using MTL TL LAWS ML.
unfold qdisc_slots_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs lead fps
HJ Hra Hra4 Hgp Htp H10 Hlead H11 Hfps Hal16 Hwlo Hwhi HV Hev.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (slots_entry W regs memc HV) as HS.
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 lead) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 fps) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
clear HE.
assert (SHOK : sh_ok tfibsegs RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a)
by (intros; reflexivity).
(* u = max 0 (lead - 300): 0x7e98c-0x7e998 (addiw/sltu/addi/and), zero-extended by 0x7e9a0-0x7e9a4 *)
pose proof (U_use E 10 lead E10 Hlead) as Uu. unfold sv_use in Uu.
pose proof (U_zx32 E _ _ Uu ltac:(lia)) as Uz. clear Uu.
unfold cfg_at. change (w64 A_QD_SLOTS) with (Z_to_bv 64 A_QD_SLOTS).
(* 0x7e984 addi a2,zero,1; stop at 0x7e988 blez a1 *)
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_branch Hb1.
- (* blez TAKEN (fps <= 0, br_ge0): to 0x7e9dc, a0 = sext.w a2 = 1 = slots_spec (qdisc_spec_nonpos) *)
rewrite (br_ge0 E 11 fps E11 Hfps) in Hb1. apply negb_true_iff, Z.ltb_ge in Hb1.
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_leaf ltac:(intros a Ha _; exact (KE a Ha (fun x => x)))
ltac:(rewrite (qdisc_spec_nonpos lead fps Hb1); reflexivity).
- (* blez not taken: 0 < fps *)
rewrite (br_ge0 E 11 fps E11 Hfps) in Hb1. apply negb_false_iff, Z.ltb_lt in Hb1.
(* p = u * fps (0x7e9a8 mul), below 2^47 (qdisc_product_range) *)
pose proof (U_prod E _ 11 _ fps Uz ltac:(lia) E11 ltac:(lia)) as Up.
remember (Z.max 0 (lead - 300) * fps) as p eqn:Hp.
assert (Bp : 0 <= p < 2 ^ 47) by (rewrite Hp; apply qdisc_product_range; lia).
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_branch Hb2.
+ (* 0x7e9b0 bltu a1,a0 TAKEN (p < 10^6): to 0x7e9dc, a0 = 1 (qdisc_spec_small) *)
rewrite branch_ltu_U, Up, U_lit in Hb2 by lia. apply Z.ltb_lt in Hb2.
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_leaf ltac:(intros a Ha _; exact (KE a Ha (fun x => x)))
ltac:(rewrite (qdisc_spec_small lead fps p Hb1 Hp Hb2); reflexivity).
+ (* not taken: 10^6 <= p *)
rewrite branch_ltu_U, Up, U_lit in Hb2 by lia. apply Z.ltb_ge in Hb2.
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_branch Hb3.
* (* 0x7e9c4 bltu a2,a1 TAKEN (10^12 + 999999 < p): 0x7e9d8 mv a2,a0 = 10^6 (qdisc_spec_cap) *)
rewrite branch_ltu_U, Up, U_lit in Hb3 by lia. apply Z.ltb_lt in Hb3.
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_leaf ltac:(intros a Ha _; exact (KE a Ha (fun x => x)))
ltac:(rewrite (qdisc_spec_cap lead fps p Hb1 Hp Hb3); reflexivity).
* (* not taken (p <= 10^12 + 999999): 0x7e9c8-0x7e9d4 load QD_MAGIC from 0x10350, mulhu, srli 18 = p / 10^6
     (qdisc_magic_shift through U_quot), which is slots_spec (qdisc_spec_mid) *)
rewrite branch_ltu_U, Up, U_lit in Hb3 by lia. apply Z.ltb_ge in Hb3.
pose proof (U_quot E _ p Up ltac:(lia)) as Uq.
pose proof (qdisc_n_range p ltac:(lia)) as Bq.
qd_run awr_ok_tac. qd_keep kwr_ro.
qd_leaf ltac:(intros a Ha _; exact (KE a Ha (fun x => x)))
ltac:(rewrite (qdisc_spec_mid lead fps p Hb1 Hp ltac:(lia)), denot_lit_U, (U_sextw0 E _ _ Uq ltac:(lia)); reflexivity).
Qed.
End d.
End b.
