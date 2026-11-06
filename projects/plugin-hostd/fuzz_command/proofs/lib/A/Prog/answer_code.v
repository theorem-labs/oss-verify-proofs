(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of answer_code on plugin-hostd/fuzz_command's ASan build, in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v (entry state, run, call, return), A/AChf.v (a side-stack frame taken by __asan_stack_malloc_N, its header and shadow) and A/AChx.v (its release by the flag store); the frame-flag law is A/ACed.v's tfibX_FFL. The snprintf call goes through the shared contract (lib/A/Rt/RtPFShared.v) and the FP lifts of lib/A/Prog/PaFx.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo hand_back_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRo CmdRecRest RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's writable statics, base and length: the kit's recb_PG (lib/A/Prog/RecBLemmas.v:33) *)
Import RecBLemmas(recb_PG, recb_run_keeps_m, recb_ablocks_nodup_m).

(* a register's symbolic value in a symbolic state, without normalising the denotation (CmdPaLib's prreg
   normalises it) *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* an address outside every write window of a symbolic memory *)
Ltac nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---------- arithmetic and denotation facts ---------- *)
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E : 32 * (x / 32) = Z.shiftl (Z.shiftr x 5) 5).
{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. lia. }
rewrite E. replace (2 ^ 64 - 32) with (Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity.
apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.lt_ge_cases n 5) as [H5|H5].
- rewrite Z.shiftl_spec_low by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
replace (n <? 5) with true by (symmetry; apply Z.ltb_lt; lia). cbn. destruct (Z.testbit x n), (n <? 64); reflexivity.
- rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (n - 5 + 5) with n by lia.
replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
replace (n <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.lt_ge_cases n 64) as [H64|H64].
+ replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. destruct (Z.testbit x n); reflexivity.
+ replace (n <? 64) with false by (symmetry; apply Z.ltb_ge; lia). cbn. rewrite Bool.andb_false_r.
symmetry. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma denot_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 96 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = Z_to_bv 64 (32 * ((v - 96) / 32)).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))))). f_equal.
change (U E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = 32 * ((v - 96) / 32)).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + -96)) by lia.
replace (-32 mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite land_m32 by lia. replace (v + -96) with (v - 96) by lia.
pose proof (Z.div_pos (v - 96) 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (v - 96) 32 ltac:(lia)).
apply Z.mod_small. lia.
Qed.

Lemma denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma sp1_facts : forall sp, sp mod 16 = 0 -> 2 ^ 46 <= sp ->
sp - 112 <= 32 * ((sp - 96) / 32) <= sp - 96 /\ (32 * ((sp - 96) / 32)) mod 32 = 0 /\
(32 * ((sp - 96) / 32) - sp) mod 16 = 0.
Proof.
intros sp H16 Hlo.
pose proof (Z.div_mod (sp - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp - 96) 32 ltac:(lia)) as M.
assert (Hm : (sp - 96) mod 32 = 0 \/ (sp - 96) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as D2. rewrite H16 in D2. lia. }
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
destruct Hm as [Hm|Hm].
- replace (32 * ((sp - 96) / 32) - sp) with (-96) by lia. reflexivity.
- replace (32 * ((sp - 96) / 32) - sp) with (-112) by lia. reflexivity.
Qed.

Lemma not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* a range of the image (the format, the guard cells, the read-only words of the snprintf chain) is apart from the
   snprintf call's stack window and from a destination in a side-stack frame *)
Lemma zd_img_out : forall lo n K sp d w, 0x10000 <= lo -> lo + n <= 0x606000 -> 0 <= n ->
0x606000 <= sp - K -> 0 <= K -> (d + w <= 0x10000 \/ 0x606000 <= d) ->
Forall (zdisjoint (lo, n)) (snp_out K sp d w).
Proof.
intros lo n K sp d w H1 H2 H3 H4 H5 H6. unfold snp_out.
apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
Qed.
Lemma snp_cr_in : forall r, In r CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) cmd_snp_cr_img r Hr) as Hb.
unfold in_cmd_img, CMD_IMG_LO, CMD_IMG_HI in Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Lemma snp_cr_bounds : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) CMD_SNP_CR.
Proof. apply Forall_forall. intros r Hr. pose proof (snp_cr_in r Hr). lia. Qed.
Lemma snp_cr_out : forall K sp d w, 0x606000 <= sp - K -> 0 <= K -> (d + w <= 0x10000 \/ 0x606000 <= d) ->
Forall (fun r => Forall (zdisjoint r) (snp_out K sp d w)) CMD_SNP_CR.
Proof.
intros K sp d w H1 H2 H3. apply Forall_forall. intros [lo n] Hr. pose proof (snp_cr_in _ Hr) as Hb. cbn [fst snd] in Hb.
apply zd_img_out; lia.
Qed.
Lemma in_filter_old : forall (old : Z) (O : list (Z * Z)) x, In x (filter (fun pn : Z * Z => fst pn =? old) O) -> In x O.
Proof.
intros old O x. induction O as [|y O IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) in H; [destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H] | right; apply IH; exact H].
Qed.
Lemma in_filter_old_intro : forall (old : Z) (O : list (Z * Z)) x, In x O -> fst x = old ->
In x (filter (fun pn : Z * Z => fst pn =? old) O).
Proof.
intros old O x. induction O as [|y O IH]; intros H Hx; [destruct H|].
cbn. destruct (decide _) as [Hd | Hd].
- destruct H as [<- | H]; [left; reflexivity | right; apply IH; [exact H | exact Hx]].
- destruct H as [<- | H]; [exfalso; apply Hd; rewrite Hx, Z.eqb_refl; first [exact I | reflexivity] | apply IH; [exact H | exact Hx]].
Qed.
Lemma aval_mem8_eq : forall rd a v1 v2, aval_mem rd a 8 v1 -> aval_mem rd a 8 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
intros rd a v1 v2 H1 H2 B1 B2.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v1 8 k = YG0f.le_byte v2 8 k).
{ intros k Hk. pose proof (H1 k Hk) as X1. rewrite (H2 k Hk) in X1. injection X1 as X. symmetry. exact X. }
rewrite <- (le_bytes8 v1 B1), <- (le_bytes8 v2 B2).
rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia. reflexivity.
Qed.
Lemma Z_mod_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). rewrite H in H0. rewrite H0. replace (16 * (x / 16) + 0) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult. Qed.
Lemma ro_lit_21d00 : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21d00 RO_lit_21d00.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. assumption. Qed.
Lemma resp_fmt_no0 : ~ In (Z_to_bv 8 0) (PF.pf_bytes RecAns.RESP_FMT).
Proof.
intros H. unfold PF.pf_bytes in H. apply in_map_iff in H as (z & Hz & Hin). apply (f_equal bv_unsigned) in Hz.
rewrite !Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz. cbn in Hin.
repeat (destruct Hin as [<- | Hin]; [vm_compute in Hz; discriminate | ]); destruct Hin.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma aview_byte_range : forall H (m : word -> option byte) a v, aview SEGS H m a = Some v -> 0 <= v < 256.
Proof.
intros H m a v E. unfold aview, mbyte in E.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|].
- injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
- destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; [|discriminate].
  injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
(* a symbolic state of a machine state built at one FP state describes the same machine state built at another:
   st_ok's FP clauses hold by construction (mkst puts fx's registers and fcsr in the state) *)
Lemma st_ok_pi_mkst_fx : forall (fxa fxb : YK11.FPState) E ss regs pc mem rom,
st_ok_pi (fx := fxa) SEGS VAL E ss (@mkst fxa regs pc mem rom) ->
st_ok_pi (fx := fxb) SEGS VAL E ss (@mkst fxb regs pc mem rom).
Proof.
intros fxa fxb E ss regs pc mem rom (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (answer_code_c.v:65-70) *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses (cgif's names) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
(* the side-stack frame's state change and the meter (cgif's MLAWF, ameter_fs_laws, lib/YC5d.v:50-53) *)
Hypothesis MTLF : ameter_fs_laws MT.
(* named facts the statement does not give yet, each to be replaced by the lemma or premise named in the report *)
Hypothesis HSIG : cmd_sig_prog.
(* arodata_okP's transport through the journal (CmdBase.arodata_ok_journalP) and cmd_ro_ok back from arodata_okP
   at any AR state (cmd_ro_ok_of_aro, lib/A/Prog/CmdRecRo.v) *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis ZSH_lit_21d00 : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21d00 8.
Hypothesis HULL_lit_21d00 : forall ly S W mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21d00 8.
Hypothesis cmd_rec_cells : forall ly S W mem md, AR SEGS B ly S W mem md ->
rdW W mem A_FLAG_REPLACE_STR = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
exists ev, rd32 (rdW W mem) (as_errno B) ev.
(* the image facts of the binary (the kit's CmdRecBase.cmd_img_facts; RecBClosed closes it by cmd_img_facts_tfib):
   the read-only words the snprintf chain reads are shown by arodata_okP (CmdRecImg.cmd_consts_view_snp) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma nodup_of_pairwise : forall (l : list (Z * Z)) (f : Z * Z -> Z * Z),
pairwise zdisjoint (map f l) -> (forall x, In x l -> 0 < snd (f x)) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros f Hp Hpos; [constructor|].
constructor.
- intros Hin. apply in_split in Hin as (t1 & t2 & Et).
assert (Hd : zdisjoint (f x) (f x)).
{ apply (pairwise_zdisjoint_split (map f (x :: t)) (f x) (f x) Hp).
exists [], (map f t1), (map f t2). left. rewrite Et. cbn. rewrite map_app. reflexivity. }
pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. lia.
- apply (IH f); [| intros y Hy; apply Hpos; right; exact Hy].
change (map f (x :: t)) with ([f x] ++ map f t) in Hp. exact (proj2 (pairwise_app_l _ _ _ Hp)).
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (AF0m.ts_universe B HB).
(* the block the recorder's answer field points at is one of the recorder's blocks O (it is the only live block
   that starts at old: blocks are disjoint and old = 0 when there is no answer) *)
Lemma old_in_O : forall ly S (W : world SEGS) mem md R O old pn, AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
In pn (ablocks B ly S) -> fst pn = old -> In pn O.
Proof.
intros ly S W mem md R O old [p n] HAR HREP HOLD Hold Hpn Hfst. cbn [fst] in Hfst. subst p.
pose proof HREP as (Q & HA & HO).
destruct HA as (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ old n HAR Hpn) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn).
pose proof alloc_ceiling_lt as Hac.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:EQ; try contradiction.
- destruct Ha as (A1 & A2 & A3 & _). cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR A3) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
assert (Rq : 0 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Eq : q = old) by (apply (aval_mem8_eq _ _ q old A1 HOLD); [lia | exact Hold]). subst q.
assert (HqO : In (old, m) O).
{ apply HO. unfold lay_blocks. rewrite EQ. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (Z.eq_dec n m) as [<- | Nnm]; [exact HqO|].
assert (Ne : (old, n) <> (old, m)) by (intros E; injection E; lia).
exfalso. pose proof (sep_blocks SEGS B LAWS ly S W mem md old n old m HAR Hpn A3 Ne) as Hd.
unfold zdisjoint, req_size in Hd. cbn [fst snd] in Hd. destruct (Z.eqb_spec n 0), (Z.eqb_spec m 0); lia.
- assert (E0 : old = 0) by (apply (aval_mem8_eq _ _ old 0 HOLD Ha); lia). lia.
Qed.
Lemma FFL : frame_flag_lawP SEGS B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (pa_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Definition fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition fr_flg : YP09.region := YP09.mkRegion (Some 1028%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 1040 0))].
Definition fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 16 0 16 [].
Definition shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).
Definition ac_extra (sp1 : Z) : list word := map (Z_to_bv 64) [SB; as_uar_cell B; sp1].
Definition ac_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [];
 YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [];
 YP09.mkRegion (Some 34%nat) 24 32 24 32 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition ac_facts0 : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_ac0 : sstate := mkSS AF_answer_code sr_atoms ac_regions0 None ac_facts0.

Lemma ac_entry : forall W ly S regs mem md ch,
afn_pre SEGS B ANSWER_CODE_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ac_extra (32 * ((spZ regs - 96) / 32))))) ss_ac0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_answer_code)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : ANSWER_CODE_STK = 16560) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 96) / 32)).
destruct (sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
set (E := Eimg (Ereg regs (ac_extra sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_ac0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[rewrite denot_off0; exact E253 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[rewrite denot_off0; exact E32 | unfold SB; lia | lia |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[rewrite denot_off0; exact E33 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [ac_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.

(* the write windows of the six regions the walk carries from the frame setup on (the frame's shadow, its flag
   word, its header, two pieces of the own stack frame, the realigned stack word) *)
Ltac awr6 fpos sp1 regs FS Vs Vf V2 V34 EFA :=
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1041%nat); [reflexivity | exact Vs |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia |];
apply (awr_ok_cons_ro _ _); [cbn; lia|];
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1028%nat); [reflexivity | exact Vf |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1) with 128; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |];
apply (awr_ok_nil _ _).

Theorem tanswer_code_holds : tanswer_code_spec B MT.
Proof.
unfold tanswer_code_spec.
intros ly S W regs mem md ch code old R O HPRE HFRM HROD HRO H10 Hcode HREP HOLD Hold64 Hfr Hev Hlive MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (ac_entry W ly S regs mem md ch HPRE) as HS.
set (FP := (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O)).
pose proof (ajournal_init SEGS B ANSWER_CODE_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : ANSWER_CODE_STK = 16560) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (sp1 := 32 * ((spZ regs - 96) / 32)) in HS.
destruct (sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
remember (Eimg (Ereg regs (ac_extra sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ac_extra sp1)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_answer_code)) with (Z_to_bv 64 (BASE + AF_answer_code)).
(* run 1: the prologue, the use-after-return flag (1, pinned by the record) and the call of __asan_stack_malloc_1 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_ac0, ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
preg HS (2%bv : bv 5) R2. preg HS (9%bv : bv 5) R9. preg HS (1%bv : bv 5) R1. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
rewrite (denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R2. fold sp1 in R2.
rewrite denot_add0, (denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R9. fold sp1 in R9.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 26172) in R1.
rewrite denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (palf_sm B TLF 1 ltac:(cbn; tauto)) as SM1. change (cs_stack_malloc 1) with CS___asan_stack_malloc_1 in SM1.
rewrite SM1.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML (CmdRecRest.cmd_stack_malloc_progress B) 1 (ASTACK1 fx) ltac:(lia) W (ms_regs ms1) (ms_mem ms1)
ANSWER_CODE_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 26172)) HJ);
[ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| pose proof (count_cid_le_length 1 (frames S)); change (fs_frames 1) with 8192; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & _ & HK3 & _ & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 R9 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (ac_extra sp1)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)). fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
replace (F + 128 - 8) with (F + 120) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFin : in_app F 128) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (ac_extra sp1)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv shx_F (SOff 1041 0) HS (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_hdr HS eq_refl
ltac:(unfold region_ok, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_flg HS eq_refl
ltac:(unfold region_ok, fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F 120 8 (SOff 1040 0) FL); [rewrite denot_off0; exact E1040 | lia | lia |];
exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_flg, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_shd HS eq_refl
ltac:(unfold region_ok, fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres o ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_shd, fr_flg, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1041, V1028, V2, V34; unfold SB; pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 1) with 128; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in *; clearbody md3 | _ => idtac end.
(* where the recorder's state, the format literal and the live blocks lie: none of them in the frame, its shadow,
   its flag or the stack *)
set (KA := fun a : Z => (A_G_REC <= a < A_G_REC + 960) \/ (A_REC_SPILL <= a < A_REC_SPILL + 56) \/
(exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KIMG : forall a, KA a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(in_img SEGS a /\ 0x10000 <= a < 0x606000 /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))).
{ intros a Ha. rewrite (AF0m.ts_owned B HB), (AF0m.ts_errno B HB). unfold AF0m.TFIB_ERRNO.
destruct Ha as [Ha | [Ha | Ha]]; [right | right | left; exact Ha].
- split; [apply cmd_prog_img; left; unfold in_zr, REC_SIZE; cbn [fst snd]; exact Ha|]. unfold A_G_REC in Ha. split; [lia|].
split; [apply (not_in_ranges _ 0x5e3740 0x5e3b00); [vm_compute; reflexivity | lia] | lia].
- split; [apply cmd_prog_img; right; left; unfold in_zr, SC_SIZE; cbn [fst snd]; exact Ha|]. unfold A_REC_SPILL in Ha. split; [lia|].
split; [apply (not_in_ranges _ 0x5e3be0 0x5e3c18); [vm_compute; reflexivity | lia] | lia]. }
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\ a <> FL).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & Hr & _ & _)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 1 fpos HAR2 Hpn2 Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo).
- split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _). apply (recb_run_keeps_m E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
nwin_tac ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ pose proof HK as (_ & HK2 & _ & _ & _ & _).
intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & _ & Ho & He)].
- replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []].
- exact (HK3 a Hi Ho He). }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (recb_run_keeps_m E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
nwin_tac ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
(* the call of the snprintf wrapper: snprintf(buf = F + 32, 32, "resp %d", code) *)
assert (HFPB : forall ly' S' a, inFP FP a -> Exists (in_zr a) recb_PG \/
exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n).
{ intros ly' S' a (r & Hr & Ha). destruct Hr as [<- | Hr].
- left. apply Exists_exists. exists (A_G_REC, REC_SIZE). split; [left; reflexivity|].
unfold in_zr, OFF_ANSWER, REC_SIZE in *. cbn [fst snd] in *. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn).
apply in_filter_old in Hpn.
exists p, n. split; [apply in_or_app; left; exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn) | cbn [fst snd] in Ha; exact Ha]. }
assert (HFPRO : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a).
{ intros a Hro (r & Hr0 & Hra0). destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg]. pose proof (pa_img_range a Hi) as Hrg.
destruct Hr0 as [<- | Hr0].
- apply Hpg. apply Exists_exists. exists (A_G_REC, REC_SIZE). split; [left; reflexivity|].
unfold in_zr, REC_SIZE, OFF_ANSWER in *. cbn [fst snd] in *. lia.
- unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
pose proof (blk_off_imgP B ly S W mem md p n HAR (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)) as Hoff.
unfold off_img in Hoff. cbn [fst snd] in Hra0. lia. }
pmkst HS.
preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11. preg HS (12%bv : bv 5) R12. preg HS (13%bv : bv 5) R13.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
cbn [sv_denot] in R10, R11, R1. rewrite V1028 in R10. rewrite (img_env_codeptr E2 HEI2 26352) in R1.
assert (VSTR : VAL (A_OBJ 47) = 0x21d00) by (rewrite (VOBJS 47%nat) by (apply Nat.ltb_lt; vm_compute; reflexivity); vm_compute; reflexivity).
rewrite denot_off0, (img_env_atomP E2 288 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)) in R12.
change (VAL 288) with (VAL (A_OBJ 47)) in R12. rewrite VSTR in R12.
rewrite denot_off0, OLD2 in R13 by lia. rewrite (EE 10%nat 10%bv eq_refl), H10 in R13.
rewrite denot_off0, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pose proof (proj1 HJ2) as HAR3.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3))).
{ exact (arodata_ok_journalP SEGS RLO RHI (CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG) (RO := RRO) B _ _ FP ly S W mem md _ ly S2 W (ms_mem ms3) _ 0 HJ2 HFPRO HROD). }
pose proof (cmd_ro_ok_of_aro ly S2 W (ms_mem ms3) _ HAR3 HROD3) as HRO3.
pose proof (ro_lit_21d00 _ HRO3) as HLIT3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin) as (_ & _ & HFpres3 & _). fold F in HFpres3. change (fs_frame_bytes 1) with 128 in HFpres3.
assert (ZS3 : forall j, 4 <= j < 8 -> rdW W (ms_mem ms3) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E2 _ _ 0 _ HS eq_refl) as HR0.
cbn [ms_mem restrict mkst] in HR0.
assert (Hj4 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct Hj4 as [-> | [-> | [-> | ->]]];
(apply (aview_of_val_mem1 SEGS); [|lia]);
(lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
refine (field_of_region E2 _ 1041 (SB + F / 8) _ 0 16 0 16 od 1%N (SLit 0) 0 HR0 V1041 _ _ _ _) end;
[cbn [In]; tauto | reflexivity | lia | lia]). }
(* the text snprintf renders and the bytes it writes: "resp <code>" and its terminator, at most 17 bytes, all of
   which fit the 32-byte buffer *)
set (TT := RecAns.RESP_HEAD ++ PF.pf_dec code).
pose proof (RecAns.resp_len code Hcode) as RLT. fold TT in RLT.
set (WN := sn_len (32 - 1) TT).
assert (SNL : WN = Z.of_nat (length TT) + 1).
{ unfold WN, sn_len, sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite length_app, firstn_all2 by lia. cbn [length]. lia. }
assert (SNB : sn_bytes (32 - 1) TT = TT ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (HWN : 7 <= WN <= 17) by lia.
assert (HKS : CMD_SNP_K = 8192) by (unfold CMD_SNP_K; rewrite Hes; reflexivity).
pose proof (ecall_pre_stk_at SEGS B CMD_SNP_K ANSWER_CODE_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly S2 W (ms_mem ms3) md3 0
(ms_regs ms3) (sp1 - spZ regs) HJ2 Qsp3 Hsp1b ltac:(lia) ltac:(rewrite HKS; lia) ltac:(rewrite HKS, FS; lia)
ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp))
as (HEC3 & HSLO3 & HSCR3).
destruct (cmd_rec_cells _ _ _ _ _ HAR3) as (_ & (HGW1 & cval & HGW2) & _).
assert (HDO : F + 32 + WN <= 0x10000 \/ 0x606000 <= F + 32) by lia.
assert (HSPK : 0x606000 <= spZ (ms_regs ms3) - CMD_SNP_K) by lia.
assert (HDK : F + 32 + WN <= spZ (ms_regs ms3) - CMD_SNP_K) by lia.
eapply SRr_bind.
{ eapply (aj_art_own_atF (fx := fx) SEGS B LAWS pa_segs_low CMD_SNP_K (fun a => F + 32 <= a < F + 32 + WN)
(SIG CS___interceptor_trampoline_snprintf) W (ms_regs ms3) (ms_mem ms3) ANSWER_CODE_STK (spZ regs) FP ly S W mem md
[(1, fpos)] ly S2 md3 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 26352)) _ HJ2 Qsp3 Hsp1b).
- lia.
- rewrite HKS; lia.
- rewrite HKS, FS; lia.
- exact R1.
- intros a Ha. right; right; right; left. exists 1, fpos. split; [left; reflexivity|].
left. unfold in_zr; cbn [fst snd]. fold F. change (fs_frame_bytes 1) with 128. lia.
- apply (srr_art_postF_of_pf (fx := fx) SEGS B CMD_SNP_K ly S2 W (ms_regs ms3) (ms_mem ms3) md3 _ (F + 32) WN
(sn_bytes (32 - 1) TT) (Z.of_nat (length TT)) HSCR3).
apply (ASNPRINTF fx ly S2 W (ms_regs ms3) (ms_mem ms3) md3 (F + 32) 32 0x21d00 []
(map (argZ (ms_regs ms3)) [3; 4; 5; 6; 7] ++ []) TT cval).
+ exact HEC3.
+ exact HSLO3.
+ exact HSCR3.
+ exact R10.
+ exact R11.
+ exact R12.
+ exact (CmdRecImg.cmd_consts_view_snp SEGS B LAWS HB IMG CMD_RLO CMD_RHI W (ms_mem ms3) HROD3).
+ exact snp_cr_bounds.
+ apply snp_cr_out; [exact HSPK | rewrite HKS; lia | exact HDO].
+ exact HGW1.
+ exact HGW2.
+ lia.
+ lia.
+ lia.
+ lia.
+ apply zd_img_out; [lia | lia | lia | exact HSPK | rewrite HKS; lia | exact HDO].
+ apply zd_img_out; [lia | lia | lia | exact HSPK | rewrite HKS; lia | exact HDO].
+ split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
+ cbn [length]. lia.
+ cbn [length]. unfold snp_out.
apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
+ apply (FR_cmd_intro _ _ _ _ _ RecAns.RESP_FMT RecAns.RESP_PS [PF.AInt code]).
* unfold fmt_at. change (Z.of_nat (length RecAns.RESP_FMT)) with 7.
split; [lia|]. split.
{ intros i Hi.
pose proof (HLIT3 (Z.to_nat i) ltac:(unfold RO_lit_21d00; rewrite length_map; cbn [length]; lia)) as Hk.
rewrite Z2Nat.id in Hk by lia. rewrite Hk. f_equal.
assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity. }
split; [apply zd_img_out; [lia | lia | lia | exact HSPK | rewrite HKS; lia | exact HDO]|].
split; [left; unfold kLowMemEnd; lia|].
split; [exact (ZSH_lit_21d00 _ _ _ _ _ HAR3) | exact (HULL_lit_21d00 _ _ _ _ _ HAR3)].
* exact RecAns.resp_parse.
* cbn [map arg_of app pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hcode|].
unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite R13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (Zmod_div_mod (2 ^ 32) (2 ^ 64) code); [reflexivity | lia | lia | exists (2 ^ 32); reflexivity].
* exact (RecAns.resp_text code).
* vm_compute. exact I.
* vm_compute; reflexivity.
+ lia.
+ lia.
+ lia.
+ lia.
+ cbn [pairwise snp_out]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]|].
split; [apply Forall_nil | exact I].
+ intros a Ha. destruct (HFpres3 a ltac:(lia)) as [Hp Hno].
split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. lia.
+ exact (amem_range_sub_app F 128 (F + 32) (WN + 8) HFapp HFceil ltac:(lia) ltac:(lia) ltac:(lia)).
+ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS3.
assert (F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia].
+ apply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W (ms_mem ms3) _ 1 fpos (F + 32) WN HAR3 Hfin);
[fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia | lia].
+ unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. lia.
+ exact HFRM. }
cbv beta. intros W4 c4 _ (-> & fx1 & regs4 & mem4 & md4 & Hfx1 & -> & HJ4 & HP4 & (Ha04 & Hbuf4) & Hkeep4).
(* from here the walk runs at the FP state fx1 snprintf returned *)
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx1|].
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin) as (_ & _ & HFpres4 & HFSpres4). fold F in HFpres4, HFSpres4.
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4.
assert (K34 : forall a, KA a -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem ms3) a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & _). apply Hkeep4; lia. }
jafter_call_keep_hi HS 1042%nat regs4 (mrestrict (w_H W) mem4) HP4 [0;1;2;3;4;5]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_hi; [exact V1041 | intros a Ha; apply Hkeep4; unfold SB in *; lia |].
intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
exact (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))).
- eapply region_kept_hi; [exact V1028 | intros a Ha; apply Hkeep4; lia | intros a Ha; lia].
- eapply region_kept_hi; [exact V1028 | intros a Ha; apply Hkeep4; lia | intros a Ha; exact (proj1 (HFpres4 a ltac:(lia)))].
- eapply region_kept_hi; [exact V2 | intros a Ha; apply Hkeep4; lia | intros a Ha; apply HJ4pres; rewrite FS; lia].
- eapply region_kept_hi; [exact V2 | intros a Ha; apply Hkeep4; lia | intros a Ha; apply HJ4pres; rewrite FS; lia].
- eapply region_kept_hi; [exact V34 | intros a Ha; apply Hkeep4; lia | intros a Ha; apply HJ4pres; rewrite FS; lia]. }
apply (st_ok_pi_mkst_fx fx fx1) in HS4.
rewrite <- (restrict_mkst_fx (fx := fx1)) in HS4. clear HS. rename HS4 into HS.
remember (havoc E2 1042 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (ac_extra sp1)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1042)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
clear HE3.
assert (W2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (W34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (W1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (W1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (W1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
assert (EFA : frame_addr ly 1 fpos = F) by reflexivity.
clear R1 R2 R3 R4 R10 R11 R12 R13.
(* the run and call rules at fx1 *)
pose proof (SRr_run_pi_AJ (fx := fx1) (PL := PL_cmd) (PI := PI) B LAWS) as RUNP1.
pose proof (SRr_run_pi_AJ_call (fx := fx1) (PL := PL_cmd) (PI := PI) B LAWS) as RUNC1.
(* run 3: a0 := buf, the call of hand_back *)
paj_run_shc RUNP1 RUNC1 HS HJ4.
{ awr6 fpos sp1 regs FS W1041 W1028 W2 W34 EFA. }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md5 := m) in *; clearbody md5 | _ => idtac end.
(* the call of hand_back(buf) *)
assert (SIGHB : SIG CS_hand_back = BASE + AF_hand_back).
{ rewrite (HSIG CS_hand_back ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). reflexivity. }
pmkst HS. rewrite SIGHB.
preg HS (10%bv : bv 5) R10. preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3.
preg HS (4%bv : bv 5) R4. preg HS (8%bv : bv 5) R8.
cbn [sv_denot] in R10, R1. rewrite W1028 in R10. rewrite (img_env_codeptr E3 HEI3 26360) in R1.
rewrite denot_off0, OLD3, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite denot_off0, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite denot_off0, OLD3, OLD2, Esp in R8 by lia.
pose proof (proj1 HJ4) as HAR5.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms5)))
by exact (arodata_ok_journalP SEGS RLO RHI (CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG) (RO := RRO) B _ _ FP ly S W mem md _ ly S2 W (ms_mem ms5) _ 0 HJ4 HFPRO HROD).
assert (HPS : as_prog_static B = recb_PG) by (rewrite (AF0m.ts_prog B HB); reflexivity).
assert (K45 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem4 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (recb_run_keeps_m E3 _ (w_H W) mem4 (ms_mem ms5) a HFr5); [lia|].
nwin_tac ltac:(fun H => rewrite ?W2, ?W34, ?W1028, ?W1041 in H; lia). }
assert (K05 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K45 a Ha), (K34 a Ha); exact (K03 a Ha)).
pose proof (RecAns.resp_len code Hcode) as RL. pose proof (resp_length code Hcode) as RL2.
assert (ELT : length (resp code) = length TT).
{ rewrite <- (RecAns.pf_resp code Hcode). unfold PF.pf_bytes. rewrite length_map. reflexivity. }
assert (HSTR5 : astr_atR (rdW W (ms_mem ms5)) (F + 32) (resp code)).
{ split; [|exact (resp_no0 code)]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (recb_run_keeps_m E3 _ (w_H W) mem4 (ms_mem ms5) (F + 32 + Z.of_nat i) HFr5); [| lia |
nwin_tac ltac:(fun H => rewrite ?W2, ?W34, ?W1028, ?W1041 in H; unfold SB in *; lia)].
pose proof (Hbuf4 (Z.of_nat i) ltac:(rewrite SNL; lia)) as Hb. rewrite SNB, Nat2Z.id in Hb. rewrite Hb.
pose proof (aview_byte_range _ _ _ _ Hb) as Hr8. f_equal.
rewrite <- (RecAns.pf_resp code Hcode). unfold PF.pf_bytes.
replace (map (Z_to_bv 8) (RecAns.RESP_HEAD ++ PF.pf_dec code) ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (TT ++ [0]))
by (rewrite map_app; reflexivity).
rewrite (map_nth (Z_to_bv 8) (TT ++ [0]) 0 i). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity. }
assert (ZS5 : forall j, 4 <= j < 8 -> rdW W (ms_mem ms5) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E3 _ _ 0 _ HS eq_refl) as HR0.
cbn [ms_mem restrict mkst] in HR0.
assert (Hj4 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct Hj4 as [-> | [-> | [-> | ->]]];
(apply (aview_of_val_mem1 SEGS); [|lia]);
(lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
refine (field_of_region E3 _ 1041 (SB + F / 8) _ 0 16 0 16 od 1%N (SLit 0) 0 HR0 W1041 _ _ _ _) end;
[cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HF8m : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
assert (HRA5 : range_addressable (rdW W (ms_mem ms5)) SHADOW_OFF (F + 32) (Z.of_nat (length (resp code)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS5.
split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
assert (HREP5 : rec_repA B ly S2 (rdW W (ms_mem ms5)) R O).
{ apply (rec_repA_kept ly S (rdW W mem) ly S2 (rdW W (ms_mem ms5)) R O HREP).
- intros pn Hpn. rewrite Eab. exact (rec_repA_in _ _ _ _ _ HREP pn Hpn).
- intros a Ha. apply K05. left. exact Ha.
- intros a Ha. apply K05. right. left. exact Ha.
- intros p n i Hpn Hi. apply K05. right. right. exists p, n.
split; [exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
assert (HOLD5 : aval_mem (rdW W (ms_mem ms5)) (A_G_REC + OFF_ANSWER) 8 old).
{ apply (aval_mem_kept (rdW W mem)); [exact HOLD|]. intros k Hk. apply K05. left. unfold OFF_ANSWER. lia. }
assert (HMO5 : mo_ok MT S2 (XM_HAND_BACK MT (resp code))).
{ rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL _ _ (XM_ANSWER_CODE MT code)); [exact MOK|].
unfold XM_ANSWER_CODE. pose proof (mo_free_nonneg MT MTL). lia. }
assert (HNFP : forall a, spZ regs <= a < 2 ^ 64 -> ~ inFP FP a).
{ intros a Ha (r & Hr & Hrq). destruct Hr as [<- | Hr]; [cbn [fst snd] in Hrq; unfold A_G_REC, OFF_ANSWER in Hrq; lia|].
unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)) as (_ & _ & Hpc & _).
cbn [fst snd] in Hrq. lia. }
assert (HCH5 : exists ch5, achain ly (rdW W (ms_mem ms5)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms5)) ch5).
{ unfold s0Z. rewrite R8, unsigned_lit_small by lia.
pose proof (st_ok_region_nth E3 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
eapply (achain_push ly (rdW W mem) (rdW W (ms_mem ms5)) (spZ regs) (s0Z regs) (raZ regs) ch); [exact Hch | lia | | | | exact Hra4 | lia | exact (Z_mod_16_8 _ Hal16) | exact Hlt | lia].
+ intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ4 a Ha (HNFP a Ha)).
+ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
replace (spZ regs - 8) with (spZ regs + -8) by lia.
refine (field_of_region E3 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 W2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
| unfold raZ; apply bv_unsigned_in_range | lia].
+ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
replace (spZ regs - 16) with (spZ regs + -16) by lia.
refine (field_of_region E3 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 W2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
| unfold s0Z; apply bv_unsigned_in_range | lia].
- exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH5 as (ch5 & HCH5).
assert (HFPKA : forall a, inFP FP a -> KA a).
{ intros a (r & Hr & Hrq). destruct Hr as [<- | Hr].
- left. cbn [fst snd] in Hrq. unfold OFF_ANSWER in Hrq. lia.
- right. right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
exists p, n. split; [exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn) | cbn [fst snd] in Hrq; exact Hrq]. }
assert (HBS : HAND_BACK_STK = 16448) by (vm_compute; reflexivity).
assert (HAFO5 : afobj SEGS B ly S2 W (ms_mem ms5) (F + 32) (Z.of_nat (length (resp code)) + 1)).
{ split; [exists 1, fpos; split; [exact Hfin|]; split; [lia|]; fold F; split; [exact HF8m|]; split; [lia | change (fs_frame_bytes 1) with 128; lia]|].
split; [rewrite Zplus_mod, HF8m; reflexivity | exact HRA5]. }
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) (PI := PI) B LAWS W (ms_regs ms5) (ms_mem ms5) (Z_to_bv 64 (BASE + AF_hand_back)) ANSWER_CODE_STK (spZ regs) FP ly S W mem md
[(1, fpos)] ly S2 _ 0 HAND_BACK_STK FP EV_HAND_BACK (sp1 - spZ regs) (getr (ms_regs ms5) 1) ch5 _ HJ4 Qsp5 Hsp1b);
[ lia | rewrite HBS; lia | rewrite HBS, FS; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp | reflexivity
| rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite R1, unsigned_lit_small by lia; lia
| exact HCH5
| intros HPRE5; exact (THAND_BACK fx1 ly S2 W (ms_regs ms5) (ms_mem ms5) _ ch5 (F + 32) old (resp code) R O HPRE5 HROD5 R10 ltac:(lia) HSTR5
ltac:(unfold LMAX; lia) HAFO5 HREP5 HOLD5 Hold64 ltac:(unfold EV_ANSWER_CODE in Hev; lia) ltac:(unfold LIVE_ANSWER_CODE in Hlive; lia) HMO5)
| intros a Ha; destruct (HFPB ly S2 a Ha) as [Hpg | (b & n & Hbn & Hba)];
[ right; right; right; right; left; split; [exact Ha|]; rewrite HPS; split; [exact Hpg | exact (cmd_prog_img a Hpg)]
| right; left; split; [exact Ha|]; exists b, n; split; [apply in_app_or in Hbn as [Hbn | Hbn]; [rewrite Eab; exact Hbn | exact Hbn] | exact Hba] ]
| intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _; exfalso; destruct (KLOC a (HFPKA a Ha)) as (Hb & _); rewrite FS in Hw; lia ]. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & HK6).
cbv zeta in HK6. destruct HK6 as (p1 & p2 & O' & Ha06 & Hp2 & Hp12 & Hnp & Hbl6 & HREP6 & HO' & HSTR6 & HBB6 & HMLE6).
rewrite R1.
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6c as (_ & Hly6 & _ & _ & _ & Hfrs6 & _). cbn [app] in Hfrs6.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR5 Hly6) as (Eab6 & Efa6 & _).
assert (EFA6 : frame_addr ly6 1 fpos = F) by (rewrite Efa6; reflexivity).
assert (Hfin6 : In (1, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6). rewrite EFA6 in HFpres6, HFSpres6.
change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6. change (128 / 8) with 16 in HFSpres6.
jafter_call_keep_hi HS 1058%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0;1;2;3;4;5]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJ6c W1041 Hfin);
[ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
| unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & _ & HnS & _); lia
| intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 1 fpos HJ6c W1028 Hfin);
[ fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
| intros a Ha; lia ].
- eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 1 fpos HJ6c W1028 Hfin);
[ fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
| intros a Ha; exact (proj1 (HFpres6 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W2);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W2);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W34);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia]. }
rewrite <- restrict_mkst_fx in HS6. clear HS. rename HS6 into HS.
remember (havoc E3 1058 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (ac_extra sp1)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1058)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
assert (E1062 : ew E4 1062 = Z_to_bv 64 p2).
{ rewrite HE4. change 1062%nat with (1058 + 4)%nat. rewrite (ew_havoc_new E3 1058 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha06. }
clear HE4.
assert (X2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact W2).
assert (X34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact W34).
assert (X1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact W1028).
assert (X1040 : bv_unsigned (ew E4 1040) = FL) by (rewrite OLD4 by lia; exact W1040).
assert (X1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact W1041).
clear R1 R2 R3 R4 R8 R10.
(* run 4: the call of the free wrapper on hand_back's returned copy *)
paj_run_shc RUNP1 RUNC1 HS HJ6.
{ awr6 fpos sp1 regs FS X1041 X1028 X2 X34 EFA6. }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md7 := m) in *; clearbody md7 | _ => idtac end.
(* the call of the free wrapper: free(hand_back's returned copy) *)
pmkst HS. rewrite (pal_free B TL).
preg HS (10%bv : bv 5) R10. preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3.
preg HS (4%bv : bv 5) R4. preg HS (8%bv : bv 5) R8.
rewrite denot_off0, E1062 in R10. cbn [sv_denot] in R1. rewrite (img_env_codeptr E4 HEI4 26364) in R1.
rewrite denot_off0, OLD4, OLD3, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, Esp in R8 by lia.
pose proof (proj1 HJ6) as HAR7.
assert (Qsp7 : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
pose proof HJ6 as (_ & Hly7 & _ & _ & _ & _ & Hnev7 & _).
pose proof Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop7 & _).
assert (HCP7 : exists ch7, chain_pre ly6 (rdW W6 (ms_mem ms7)) (ms_regs ms7) ch7).
{ pose proof (st_ok_region_nth E4 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
assert (Hs07 : s0Z (ms_regs ms7) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
assert (Hra7 : 4096 <= raZ (ms_regs ms7)) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
apply (achain_chain_pre ly6 _ (spZ regs + (sp1 - spZ regs)) (spZ regs) _ (ms_regs ms7)); [| rewrite Qsp7; lia | exact Hs07 | exact Hra7].
eapply (achain_push ly6 (rdW W mem) (rdW W6 (ms_mem ms7)) (spZ regs) (s0Z regs) (raZ regs) ch);
[apply (achain_ly_top ly ly6); [exact Etop7 | exact Hch] | rewrite Etop7; lia | | | | exact Hra4 | lia | exact (Z_mod_16_8 _ Hal16) | rewrite Etop7; exact Hlt | lia].
+ intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ6 a Ha (HNFP a Ha)).
+ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
replace (spZ regs - 8) with (spZ regs + -8) by lia.
refine (field_of_region E4 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 X2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
| unfold raZ; apply bv_unsigned_in_range | lia].
+ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
replace (spZ regs - 16) with (spZ regs + -16) by lia.
refine (field_of_region E4 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 X2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
| unfold s0Z; apply bv_unsigned_in_range | lia].
- exists []. apply (achain_chain_pre ly6 _ (spZ regs + (sp1 - spZ regs)) (spZ regs) [] (ms_regs ms7));
[left; split; [right; left; rewrite Etop7; lia | reflexivity] | rewrite Qsp7; lia | exact Hs07 | exact Hra7]. }
destruct HCP7 as (ch7 & HCP7).
assert (Hinp2 : In (p2, Z.of_nat (length (resp code)) + 1) (ablocks B ly6 S6)) by (apply Hbl6; right; right; reflexivity).
assert (HMO7 : mo_ok MT S6 (mo_free MT)).
{ apply (mo_ok_step MT MTL S2 S6 (XM_HAND_BACK MT (resp code)) (mo_free MT)); [|exact HMLE6].
rewrite ES2. apply (mo_ok_set_fs MT MTLF). exact MOK. }
eapply SRr_bind.
{ eapply (afree04_sub (fx := fx1) SEGS B LAWS pa_segs_low MT (AFREE4 fx1) W6 (ms_regs ms7) (ms_mem ms7) ANSWER_CODE_STK (spZ regs) FP ly S W mem md
[(1, fpos)] ly6 S6 _ _ p2 (Z.of_nat (length (resp code)) + 1) (sp1 - spZ regs) (Z_to_bv 64 (BASE + 26364)) ch7 HJ6 Hinp2 R10 Qsp7 Hsp1b);
[ lia | rewrite Has, FS; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| unfold EV_ANSWER_CODE in Hev; lia | exact HCP7
| intros Hin i Hi; destruct (Z.eq_dec p2 old) as [Eo | Ne];
[ destruct (inFP_ablocks_fp (filter (fun pn => fst pn =? old) O) p2 (Z.of_nat (length (resp code)) + 1) i
(in_filter_old_intro old O _ (old_in_O ly S W mem md R O old _ HAR HREP HOLD Hold64 Hin Eo) Eo) Hi) as (r & Hr & Hrr);
exists r; split; [right; exact Hr | exact Hrr]
| exfalso; exact (proj2 (Hnp _ ltac:(rewrite Eab; exact Hin) Ne) eq_refl) ]
| exact HMO7 ]. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1 & l2 & El1 & El2) & Hfrs8 & HK8 & HMLE8 & HJ8c).
pose proof (proj1 HJ8) as HAR8.
pose proof HJ8c as (_ & Hly8 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly8 HAR7 Hly8) as (_ & Efa8 & _).
assert (EFA8 : frame_addr ly8 1 fpos = F) by (rewrite Efa8; exact EFA6).
assert (Hfin8 : In (1, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin6).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). rewrite EFA8 in HFpres8, HFSpres8.
change (fs_frame_bytes 1) with 128 in HFpres8, HFSpres8. change (128 / 8) with 16 in HFSpres8.
pose proof HK8 as (HK81 & HK82 & HK83 & _ & _ & _).
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ8pres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR7 Hinp2) as (_ & Hp24096 & Hp2ceil & Hp2app & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly6 S6 W6 (ms_mem ms7) _ p2 _ 1 fpos HAR7 Hinp2 Hfin6) as Hd2.
unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. rewrite EFA6 in Hd2. change (fs_frame_bytes 1) with 128 in Hd2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hp2app.
jafter_call_keep_hi HS 1074%nat regs8 (mrestrict (w_H W8) mem8) HP8 [0;1;2;3;4;5]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_ownframe_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1041 0 16 0 16 _ (SB + F / 8) 1 fpos HK8 X1041 Hfin6);
[ right; unfold shadow_addr; rewrite EFA6, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| intros a Ha Hp; unfold SB in *; lia
| intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres8 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1028 120 128 120 120 _ F 1 fpos HK8 X1028 Hfin6);
[ rewrite EFA6; lia | rewrite EFA6; change (fs_frame_bytes 1) with 128; lia | lia | intros a Ha Hp; lia ].
- eapply (region_kept_ownframe_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1028 0 32 0 24 _ F 1 fpos HK8 X1028 Hfin6);
[ left; rewrite EFA6; change (fs_frame_bytes 1) with 128; lia | intros a Ha Hp; lia | intros a Ha; exact (proj1 (HFpres8 a ltac:(lia))) ].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 2 (spZ regs)); [exact X2 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 2 (spZ regs)); [exact X2 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 34 sp1); [exact X34 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS8. clear HS. rename HS8 into HS.
remember (havoc E4 1074 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (ac_extra sp1)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1074)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (Y2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact X1028).
assert (Y1040 : bv_unsigned (ew E5 1040) = FL) by (rewrite OLD5 by lia; exact X1040).
assert (Y1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact X1041).
assert (EFL8 : flag_addr ly8 1 fpos = FL).
{ pose proof EFA8 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (FFL _ _ _ _ _ 1 fpos HAR8 Hfin8) as (HFLp8 & HFLo8 & _ & _). rewrite EFL8 in HFLp8, HFLo8.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 16)).
{ intros Hx. apply (proj2 (HFSpres8 (FL - (SB + F / 8)) ltac:(lia))).
replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia). exact HFLo8. }
assert (HFLnF : ~ (F <= FL < F + 128)) by (intros Hx; exact (proj2 (HFpres8 FL Hx) HFLo8)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp8)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y1040, Y1041, Y1028, Y2, Y34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the epilogue: buf's shadow := f8, the frame's magic retired, the frame's shadow := f5, its flag byte := 0 (the
   release), the saved registers back, a0 := code, return *)
pose (RUNF := aj_flag_store_pi (fx := fx1) (PL := PL_cmd) (PI := PI) B LAWS ML AFREE_LAW FFL).
paj_run_flag_sh RUNF HS HJ8.
- lia.
- intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
destruct Hin as [<- | Hin]; [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Y1040 in Hr; rewrite EFL8; lia|]. left.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Y1041, ?Y1028, ?Y2, ?Y34 in Hr;
first [ exfalso; lia | left; rewrite FS; lia
| right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA8; change (fs_frame_bytes 1) with 128; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA8, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia ] ] |]).
destruct Hin.
- intros msr HSr. rewrite EFL8.
pose proof (st_ok_pi_region_nth E5 _ _ 0 _ HSr eq_refl) as HR0.
pose proof (field_of_region E5 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 Y1040 ltac:(cbn [In]; tauto) eq_refl ltac:(lia) ltac:(lia)) as HV.
specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
-
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
clear R1 R2 R3 R4 R8 R10.
preg HS (1%bv : bv 5) R1. preg HS (10%bv : bv 5) R10.
rewrite denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) in R1 by lia.
rewrite denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in R10 by lia.
(* the recorder's bytes and the surviving blocks from hand_back's return to here *)
pose proof (recb_ablocks_nodup_m B _ _ _ _ _ HAR7) as ND. rewrite El1 in ND.
assert (EAB9 : ablocks B ly8 (stack_free_state 1 fpos S8) = l1 ++ l2).
{ unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly8 S8). exact El2. }
assert (HO'B : forall pn, In pn O' -> In pn (l1 ++ l2)).
{ intros pn Hpn. pose proof (rec_repA_in _ _ _ _ _ HREP6 pn Hpn) as H6. rewrite El1 in H6.
apply in_app_or in H6 as [H | [H | H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
exfalso. rewrite <- H in Hpn. apply HO' in Hpn as [[Ho Hoo] | Hp].
- exact (proj2 (Hnp _ ltac:(rewrite Eab; exact (rec_repA_in _ _ _ _ _ HREP _ Ho)) Hoo) eq_refl).
- injection Hp as Eqp. apply Hp12. symmetry. exact Eqp. }
set (KB := fun a : Z => (A_G_REC <= a < A_G_REC + 960) \/ (A_REC_SPILL <= a < A_REC_SPILL + 56) \/
(exists p n, In (p, n) (l1 ++ l2) /\ p <= a < p + req_size n)).
assert (KBLOC : forall a, KB a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\ a <> FL).
{ intros a Ha. destruct Ha as [Ha | [Ha | (p & n & Hpn & Hpa)]].
- apply KLOC. left. exact Ha.
- apply KLOC. right. left. exact Ha.
- rewrite <- El2 in Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR8 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres8 & _).
pose proof (sep_block_frame SEGS B LAWS ly8 S8 W8 mem8 md8 p n 1 fpos HAR8 Hpn Hfin8) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA8 in Hd. change (fs_frame_bytes 1) with 128 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (proj2 (Hpres8 FL ltac:(lia)) HFLo8). }
assert (K69 : forall a, KB a -> aview SEGS (w_H W8) (ms_mem ms9) a = aview SEGS (w_H W6) mem6 a).
{ intros a Ha. destruct (KBLOC a Ha) as (Hb & HnF & HnS & HnFL).
rewrite (recb_run_keeps_m E5 _ (w_H W8) mem8 (ms_mem ms9) a HFr9); [| lia | nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1040, ?Y1041 in H; lia)].
rewrite <- (recb_run_keeps_m E4 _ (w_H W6) mem6 (ms_mem ms7) a HFr7); [| lia | nwin_tac ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; lia)].
destruct Ha as [Ha | [Ha | (p & n & Hpn & Hpa)]].
- apply HK83; [apply cmd_prog_img; left; unfold in_zr, REC_SIZE; cbn [fst snd]; exact Ha
| rewrite (AF0m.ts_owned B HB); apply (not_in_ranges _ 0x5e3740 0x5e3b00); [vm_compute; reflexivity | unfold A_G_REC in Ha; lia]
| rewrite (AF0m.ts_errno B HB); unfold AF0m.TFIB_ERRNO, A_G_REC in *; lia].
- apply HK83; [apply cmd_prog_img; right; left; unfold in_zr, SC_SIZE; cbn [fst snd]; exact Ha
| rewrite (AF0m.ts_owned B HB); apply (not_in_ranges _ 0x5e3be0 0x5e3c18); [vm_compute; reflexivity | unfold A_REC_SPILL in Ha; lia]
| rewrite (AF0m.ts_errno B HB); unfold AF0m.TFIB_ERRNO, A_REC_SPILL in *; lia].
- assert (Hpn6 : In (p, n) (ablocks B ly6 S6)) by (rewrite El1; apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]).
assert (Hne : (p, n) <> (p2, Z.of_nat (length (resp code)) + 1)) by (intros Eqp; rewrite Eqp in Hpn; exact (List.NoDup_remove_2 _ _ _ ND Hpn)).
pose proof (sep_blocks SEGS B LAWS ly6 S6 W6 (ms_mem ms7) _ p n p2 _ HAR7 Hpn6 Hinp2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
replace a with (p + (a - p)) by lia. apply (HK82 p n (a - p) Hpn6); [lia | cbv beta; lia]. }
eapply (paj_ret_at (fx := fx1) (PL := PL_cmd) (PI := PI) W8 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. apply (apost_baseF_of_base (fx := fx1) SEGS). unfold apost_base.
eexists ly8, (stack_free_state 1 fpos S8), (ms_regs ms9), (ms_mem ms9), _.
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
split; [rewrite R1, Hra'; reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ8 | unfold EV_ANSWER_CODE; lia]|].
split; [eapply (aregs_preserved_of_st_ok SEGS (w_H W8) E5 _ ms9 regs (ac_extra sp1) HS HAE5); vm_compute; reflexivity|].
exists p1, O'. cbv zeta.
split; [rewrite R10; reflexivity|].
split; [intros pn Hpn Hpo; exact (proj1 (Hnp pn ltac:(rewrite Eab; exact Hpn) Hpo))|].
split.
{ intros pn. rewrite EAB9. split.
- intros Hpn.
assert (Hpn6 : In pn (ablocks B ly6 S6)) by (rewrite El1; apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]).
assert (Hne : pn <> (p2, Z.of_nat (length (resp code)) + 1)) by (intros Eqp; rewrite Eqp in Hpn; exact (List.NoDup_remove_2 _ _ _ ND Hpn)).
apply Hbl6 in Hpn6 as [H | [H | H]]; [left; rewrite <- Eab; exact H | right; exact H | exfalso; exact (Hne H)].
- intros Hpn.
assert (Hpn6 : In pn (ablocks B ly6 S6)) by (apply Hbl6; destruct Hpn as [[H1 H2] | H]; [left; split; [rewrite Eab; exact H1 | exact H2] | right; left; exact H]).
rewrite El1 in Hpn6. apply in_app_or in Hpn6 as [H | [H | H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
exfalso. rewrite <- H in Hpn. destruct Hpn as [[H1 H1o] | H2]; [exact (proj2 (Hnp _ ltac:(rewrite Eab; exact H1) H1o) eq_refl) | injection H2 as Eqp; apply Hp12; symmetry; exact Eqp]. }
split.
{ change (fst (rec_answer_code R code)) with (fst (hand_back R (resp code))).
apply (rec_repA_kept ly6 S6 (rdW W6 mem6) ly8 (stack_free_state 1 fpos S8) (rdW W8 (ms_mem ms9)) _ O' HREP6).
- intros pn Hpn. rewrite EAB9. exact (HO'B pn Hpn).
- intros a Ha. apply K69. left. exact Ha.
- intros a Ha. apply K69. right. left. exact Ha.
- intros p n i Hpn Hi. apply K69. right. right. exists p, n. split; [exact (HO'B _ Hpn)|].
unfold req_size. destruct (Z.eqb_spec n 0); lia. }
split; [exact HO'|].
split.
{ assert (B9 : blocks_bytes (stack_free_state 1 fpos S8) = bsum (ablocks B ly8 (stack_free_state 1 fpos S8))) by apply blocks_bytes_bsum.
assert (B6 : blocks_bytes S6 = bsum (ablocks B ly6 S6)) by apply blocks_bytes_bsum.
assert (B2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
rewrite B9, EAB9, bsum_app. rewrite B6, El1, bsum_app, bsum_cons, B2 in HBB6. cbn [snd] in HBB6.
unfold LIVE_ANSWER_CODE. lia. }
unfold XM_ANSWER_CODE, stack_free_state. apply (mo_le_set_fs_r MT MTLF).
apply (mo_le_trans MT MTL S S6 S8); [| exact HMLE8].
apply (mo_le_set_fs_l MT MTLF S S6 fS2). rewrite <- ES2. exact HMLE6.
Qed.
End e.
End f.
End d.
Check tanswer_code_holds.
Print Assumptions tanswer_code_holds.
