(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Rt/Memmove.v, with its module paths changed; 389 of its 420 lines of code are new or changed and 114 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPmW.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* The walk of ASan's printf_common (fm.asan 0x44d84) for one of fm's snprintf formats, generic in the format: the
   entry state (st0), five symbolic runs with their stops (internal_strlen of the format done; internal_memset's
   alignment branch; the 4-byte load of the zeroed dir.fieldPrecision; the %s argument's internal_strlen, where the
   READ_RANGE check is pcm_scheck; the final ret), the shape checks of the stopped states as one boolean, and the
   contract's facts give apcommon_realizesU's post. Each format instantiates it with its own runs (FMsnprintfPm1..7). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE3i YE39 YE3h YE38 YE7d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require YE2t YE35.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMsnprintfI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPmChk FMsnprintfPmK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- shape checks ---- *)
Definition wok (rs : smem) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, - WIN, 0) || (snd t <=? snd (fst t))) (windows rs).
Definition stk_shape (r : YP09.region) : bool :=
obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_lo r =? - WIN) && (YP09.r_hi r =? 0) && (YP09.r_wlo r =? - WIN) && (YP09.r_whi r =? 0).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) v.
Definition chunk1_is (off : Z) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 1 && sv_eqb e (SLit 0) | _ => false end.
Definition resv_none (ss : sstate) : bool := match ss_resv ss with None => true | Some _ => false end.
Definition top_ok (ss : sstate) : bool := match ss_mem ss with r :: _ => stk_shape r | [] => false end.
(* the 4-byte load of dir.fieldPrecision at PC_LW: s8 = sp0 - 2184, its 4 bytes zero chunks *)
Definition lw_ok (e : sstate) : bool :=
(ss_pc e =? PC_LW) && resv_none e && ss_atoms_lt 40 e && reg_is e 24 (SOff 2 (-2184)) && top_ok e &&
match ss_mem e with r :: _ => forallb (fun kk => existsb (chunk1_is (-2212 + kk)) (YP09.r_chunks r)) [0; 1; 2; 3] | [] => false end.
(* the %s argument's internal_strlen call: the string in atom 32 + jx *)
Definition rest_ok (n : nat) (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r) && (0 <=? YP09.r_lo r) &&
match YP09.r_base r with None => YP09.r_hi r <=? 2 ^ 43 | Some 12%nat => YP09.r_hi r <=? 8 * Z.of_nat n | _ => false end.
Definition chk_ok (n jx : nat) (e : sstate) : bool :=
(ss_pc e =? A_ISL) && resv_none e && ss_atoms_lt 40 e &&
reg_is e 1 (SLit PC_SLCALL) && reg_is e 2 (SOff 2 OSP) && reg_is e 10 (SOff (32 + jx) 0) && reg_is e 22 (SOff (32 + jx) 0) &&
regions_wf (ss_mem (pc_after 40 e)) && no_cdata (ss_mem (pc_after 40 e)) && mem_atoms_lt 40 (ss_mem (pc_after 40 e)) &&
match ss_mem e with r :: rest => stk_shape r && forallb (chunk_inside r) (YP09.r_chunks r) && forallb (rest_ok n) rest | [] => false end.
(* the final ret: callee-saved registers and ra are the entry atoms *)
Definition end_ok (e : sstate) : bool :=
resv_none e && top_ok e && reg_is e 1 (SOff 1 0) &&
match clookup tbl_fp (ss_pc e) with Some w => w =? RET_WORD_r | None => false end &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs e) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED.
Definition wchk (n jx : nat) (s0 e1 e2 e3 e4 e5 : sstate) : bool :=
regions_wf (ss_mem s0) && wok (ss_mem s0) && wok (ss_mem e1) && wok (ss_mem e2) && wok (ss_mem e3) &&
wok (ss_mem (pc_after 40 e4)) && top_ok e1 && top_ok e2 && top_ok e3 && top_ok e4 &&
lw_ok e3 && chk_ok n jx e4 && end_ok e5.
Lemma reg_is_sound : forall ss r v, reg_is ss r v = true -> sr_get (ss_regs ss) (Z_to_bv 5 r) = v.
Proof. intros ss r v H. unfold reg_is in H. apply sv_eqb_eq in H. exact H. Qed.
Lemma resv_none_sound : forall ss, resv_none ss = true -> ss_resv ss = None.
Proof. intros ss H. unfold resv_none in H. destruct (ss_resv ss); [discriminate | reflexivity]. Qed.
Lemma stk_shape_sound : forall r, stk_shape r = true ->
YP09.r_base r = Some 2%nat /\ YP09.r_lo r = - WIN /\ YP09.r_hi r = 0 /\ YP09.r_wlo r = - WIN /\ YP09.r_whi r = 0.
Proof.
intros r H. unfold stk_shape in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply obase_eqb_eq in H1. apply Z.eqb_eq in H2, H3, H4, H5. repeat split; assumption.
Qed.
Lemma chunk1_is_sound : forall off c, chunk1_is off c = true -> c = YP09.mkChunk off (CVal 1 (SLit 0)).
Proof.
intros off [o cv] Hc. unfold chunk1_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
(* the memory a run with only the stack window writable keeps *)
Lemma meq_of_frame : forall E rs (m m' : word -> option byte) sp0, wok rs = true -> bv_unsigned (ew E 2) = sp0 ->
frame_of E rs m m' -> forall z : word, ~ (sp0 - WIN <= bv_unsigned z < sp0) -> m' z = m z.
Proof.
intros E rs m m' sp0 Hw Usp HF z Hz. apply HF. intros Hin. apply Hz.
pose proof (in_wrange_single_b E rs (bv_unsigned z) 2 (- WIN) 0 sp0 Hw Usp Hin). lia.
Qed.
(* the stack window is present in a state whose first region is the stack region *)
Lemma win_present : forall (H : word -> bool) E ss ms sp0, st_ok tfibsegs E ss (restrict H ms) -> top_ok ss = true ->
bv_unsigned (ew E 2) = sp0 -> TFIB_IMG_END <= sp0 - WIN -> sp0 <= 2 ^ 64 ->
forall a, sp0 - WIN <= a < sp0 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms sp0 HS Ht Usp Hlo Hhi a Ha. unfold top_ok in Ht. destruct (ss_mem ss) as [|r rest] eqn:Hm; [discriminate|].
apply stk_shape_sound in Ht as (Hb & _ & _ & Hwl & Hwh).
apply (st_ok_window_apresent H E ss ms 0 r a HS ltac:(rewrite Hm; reflexivity)); [| lia].
rewrite Hb, Hwl, Hwh. cbn [base_val]. rewrite Usp. lia.
Qed.
Section a.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma aru_win : forall ly S U W mem md mem' md' sp0,
ARU tfibsegs B ly S U W mem md -> ly_stk_lo ly <= sp0 - WIN -> sp0 <= ly_stk_hi ly -> 0 <= sp0 - WIN -> sp0 < 2 ^ 64 ->
(forall z : word, ~ (sp0 - WIN <= bv_unsigned z < sp0) -> mem' z = mem z) ->
(forall a, sp0 - WIN <= a < sp0 -> apresent (w_H W) mem a) ->
(forall a, sp0 - WIN <= a < sp0 -> apresent (w_H W) mem' a) ->
same_but_materialized md md' ->
ARU tfibsegs B ly S U W mem' md'.
Proof.
intros ly S U W mem md mem' md' sp0 HAR Hlo Hhi H0 H64 MEQ P0 P1 Hsbm.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - WIN <= a < sp0) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply YF0x.aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hn. }
apply (ARU_frame tfibsegs B LAWS ly S U W mem md mem' md' HAR).
- intros a Hr Hown. apply AV; [exact Hr|]. intros Hs. exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HAR ltac:(lia) Hown).
- intros a Hv. rewrite (YE2y.aview_mod _ mem' a). rewrite (YE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - WIN)) as [L1|L1]; [rewrite AV by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV by lia; exact Hv].
apply YE2y.aview_some_of_apresent. apply P1. lia.
- apply (same_but_materialized_frame md _ Hsbm).
- apply (same_but_materialized_frame md _ Hsbm).
- apply (same_but_materialized_frame md _ Hsbm).
- exact (YE2y.hs_kept_win _ mem mem mem' (sp0 - WIN) sp0 (sp0 - WIN) sp0 MEQ P0 ltac:(lia) ltac:(lia)).
Qed.
End a.
(* ---- the argument slots, the %s string ---- *)
Lemma slots_ok : forall (W : world tfibsegs) mem E P (args : list Z) n,
bv_unsigned (ew E 12) = P -> (forall j, (j < n)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j args 0)) ->
(forall j, (j < n)%nat -> 0 <= nth j args 0 < 2 ^ 64) ->
0 <= P -> P + 8 * Z.of_nat n <= 2 ^ 64 -> (n <= length args)%nat -> slots_at W mem P args ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (slots n).
Proof.
intros W mem E P args n HP Hx Hr HP0 HPn Hn Hsl. unfold region_ok, slots.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HP.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
apply (chunk_ok_val tfibsegs E _ P (8 * Z.of_nat j) 8 (SOff (32 + j) 0) (nth j args 0)).
- cbn [sv_denot]. rewrite (Hx j ltac:(lia)). rewrite unsigned_lit_small by (apply Hr; lia). rewrite Z.add_0_r. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Hr. lia.
- change (Z.of_N 8) with 8. lia.
- change (N.to_nat 8) with 8%nat. exact (Hsl j ltac:(lia)).
Qed.
Lemma vm1_aview : forall (H : word -> bool) (m : word -> option byte) a v,
val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
replace (YO0f.le_byte v 1 0) with v.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
- unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.
Lemma cstr_vf : forall (W : world tfibsegs) mem p l, cstr_ok tfibsegs W mem p l -> vf_str W mem p (map (Z_to_bv 8) l).
Proof.
intros W mem p l ((Hg & Hnz) & _).
assert (Hb : forall i, (i < length l)%nat -> aview tfibsegs (w_H W) mem (p + Z.of_nat i) = Some (nth i l 0) /\ 0 <= nth i l 0 < 256).
{ intros i Hi. destruct (Hg i ltac:(rewrite length_app; cbn; lia)) as [Hv Hr]. rewrite app_nth1 in Hv, Hr by lia.
split; [exact (vm1_aview _ _ _ _ Hv Hr) | exact Hr]. }
split; [|split].
- intros i Hi. rewrite length_map in Hi. destruct (Hb i Hi) as [Hv Hr]. rewrite Hv. f_equal.
replace (0%bv : byte) with (Z_to_bv 8 0) by (apply bv_eq; reflexivity). rewrite map_nth.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
- rewrite length_map. destruct (Hg (length l) ltac:(rewrite length_app; cbn; lia)) as [Hv Hr].
rewrite app_nth2 in Hv, Hr by lia. rewrite Nat.sub_diag in Hv, Hr. cbn [nth] in Hv, Hr. exact (vm1_aview _ _ _ _ Hv Hr).
- apply Forall_forall. intros b Hin. apply in_map_iff in Hin as (c & <- & Hc).
apply In_nth with (d := 0) in Hc as (i & Hi & <-). destruct (Hb i Hi) as [_ Hr].
pose proof (proj1 (Forall_forall _ _) Hnz _ (nth_In l 0 Hi)) as Hne.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. exact Hne.
Qed.
Lemma hull_bounds : forall ly lo hb, hull_ok ly lo hb = true -> 0x7fffa000 <= lo /\ lo + Z.of_nat (length hb) <= 0x7fffe000.
Proof.
intros ly lo hb Hh. unfold hull_ok in Hh. apply andb_prop in Hh as [Hh Hhi]. apply andb_prop in Hh as [_ Hlo].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. split; assumption.
Qed.
Lemma amem_range_le : forall p n n', amem_range p n -> 0 <= n' <= n -> amem_range p n'.
Proof. intros p n n' H Hn. unfold amem_range in *. lia. Qed.
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma pcm_entry : forall ly S U (W : world tfibsegs) regs mem md f lo hb n fj args P,
ARU tfibsegs B ly S U W mem md -> rom_viewN tfibsegs B W mem -> hull_ok ly lo hb = true ->
regions_wf (ss_mem (st0 f lo hb n fj)) = true ->
getr regs 11 = w64 f -> getr regs 12 = w64 P ->
2 ^ 44 <= spZ regs < 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
spZ regs <= P -> P + 8 * Z.of_nat n <= 2 ^ 47 -> slots_at W mem P args ->
(n <= length args)%nat -> (forall j, (j < n)%nat -> 0 <= nth j args 0 < 2 ^ 64) ->
(forall j, In j fj -> 4096 <= nth j args 0 <= 2 ^ 47 /\ (j < n)%nat) ->
st_ok tfibsegs (YE2y.Env regs args) (st0 f lo hb n fj) (restrict (w_H W) (mkst regs (Z_to_bv 64 PC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md f lo hb n fj args P HAR Hrom Hh Hwf G11 G12 Hsp Hal Hpres HP1 HP2 Hsl Hn Hrng Hfj.
set (E := YE2y.Env regs args).
assert (EE2 : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (YE2y.Env_reg regs args 2 2%bv eq_refl); reflexivity).
assert (EE12 : bv_unsigned (ew E 12) = P) by (unfold E; rewrite (YE2y.Env_reg regs args 12 12%bv eq_refl), G12; unfold w64; apply unsigned_lit_small; lia).
assert (EEx : forall j, (j < n)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j args 0)).
{ intros j Hj. unfold E. apply YE2y.Env_x. apply nth_error_nth'. lia. }
pose proof (hull_bounds ly lo hb Hh) as [Hlo Hhi].
pose proof (Nat.Div0.mul_div_le (length hb) 8) as LD. apply inj_le in LD. rewrite Nat2Z.inj_mul in LD.
rewrite restrict_mkst_fx. unfold st0.
apply (st_ok_regs tfibsegs E (mkSS PC_ENTRY sr_atoms (stk :: shz lo hb :: slots n :: pimg :: map ro_region icpt_rodata) None (sfacts fj)) _ (sregs0 f)).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold E; rewrite (YE2y.Env_reg regs _ 11 11%bv eq_refl), G11; reflexivity) ] |]).
destruct Hr. }
unfold E, YE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) args)) with E.
- apply regs_ok_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]]].
+ unfold stk. apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- WIN)); [exact EE2 | unfold WIN; lia | lia |].
intros a Ha. apply YE2y.apresent_writable. apply Hpres. lia.
+ exact (shz_ok B LAWS TB ly S U W mem md E lo hb HAR Hh).
+ apply (slots_ok W mem E P args n EE12 EEx Hrng ltac:(lia) ltac:(lia) Hn Hsl).
+ exact (pimg_ok B TB W mem E Hrom).
+ exact (icpt_rodata_okU B TB ly S U W mem md E HAR).
- apply pairwise_disjoint_of_extents. unfold stk, shz, slots, pimg, icpt_rodata, ro_region, extent_of_region, WIN, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2, EE12.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- unfold sfacts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. split.
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EE2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
+ clear - Hfj EEx. induction fj as [|j fj IH]; [exact I|]. cbn [map atoms_ok]. split.
* destruct (Hfj j (or_introl eq_refl)) as [Hr Hj]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EEx j Hj).
rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
* apply IH. intros j' Hj'. apply Hfj. right. exact Hj'.
Qed.
Definition pcom_post ly S U (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_PCOM <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Theorem pcm_walk : forall (f lo : Z) (hb : list Z) (n jx : nat) (fj : list nat) (e1 e2 e3 e4 e5 : sstate)
ly S U (W : world tfibsegs) regs mem md P (args : list Z) (str : list Z),
RUNTO PC_FMTD (st0 f lo hb n fj) = (e1, RS_running) ->
RUNTOS e1 = (e2, RS_stopped (SR_branch BC_EQ MSC (SLit 0))) ->
RUNTOS (YP06.add_cond e2 (mkAC BC_NE MSC (SLit 0))) = (e3, RS_stopped (SR_load (Some 2%nat) (-2212))) ->
RUNTOS (LW0 e3) = (e4, RS_running) ->
RUNTOS (pc_after 40 e4) = (e5, RS_stopped (SR_jalr (SOff 1 0))) ->
wchk n jx (st0 f lo hb n fj) e1 e2 e3 e4 e5 = true ->
hull_ok ly lo hb = true ->
ecall_preU tfibsegs B ly S U W regs mem md -> alloc_ceiling <= ly_stk_lo ly ->
ly_stk_lo ly + STK_PCOM <= spZ regs -> (forall a, spZ regs - STK_PCOM <= a < spZ regs -> apresent (w_H W) mem a) ->
rom_viewN tfibsegs B W mem -> getr regs 11 = w64 f -> getr regs 12 = w64 P ->
spZ regs <= P -> P + 8 * Z.of_nat (length args) <= ly_stk_hi ly -> slots_at W mem P args ->
(n <= length args)%nat -> (forall j, (j < n)%nat -> 0 <= nth j args 0 < 2 ^ 64) ->
(forall j, In j fj -> 4096 <= nth j args 0 <= 2 ^ 47 /\ (j < n)%nat) ->
(jx < n)%nat -> cstr_ok tfibsegs W mem (nth jx args 0) str -> Z.of_nat (length str) + 1 < 2 ^ 31 ->
SRr tfibsegs W (cfg_at tfibsegs PC_ENTRY regs mem md) (pcom_post ly S U W regs mem md).
Proof.
intros f lo hb n jx fj e1 e2 e3 e4 e5 ly S U W regs mem md P args str R1 R2 R3 R4 R5 HC Hh HPRE Hac Hslo Hpres Hrom G11 G12
HP1 HP2 Hsl Hn Hrng Hfj Hjx Hstr Hlen.
pose proof YF0x.Hwx_tfa as Hwx.
destruct HPRE as ((HARu & Hra & Hal16 & HsloE & Htop & _ & Hgp & Htp) & Hok & Hpo).
assert (HAR : ARU tfibsegs B ly S U W mem md) by (split; [exact HARu | split; assumption]).
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof YE2y.asan_consts as (AC1 & _ & _ & _ & _).
unfold STK_PCOM, ESTACK in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 < 2 ^ 47) by lia.
assert (HWIN : WIN = 4096) by reflexivity. assert (HIE : TFIB_IMG_END = 0x5f7000) by reflexivity.
(* the shape checks *)
unfold wchk in HC.
apply andb_prop in HC as [HC Cend]. apply andb_prop in HC as [HC Cchk]. apply andb_prop in HC as [HC Clw].
apply andb_prop in HC as [HC Ct4]. apply andb_prop in HC as [HC Ct3]. apply andb_prop in HC as [HC Ct2]. apply andb_prop in HC as [HC Ct1].
apply andb_prop in HC as [HC Cw4]. apply andb_prop in HC as [HC Cw3]. apply andb_prop in HC as [HC Cw2]. apply andb_prop in HC as [HC Cw1].
apply andb_prop in HC as [Cwf Cw0].
(* the environment *)
set (E := YE2y.Env regs args).
assert (EE2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (YE2y.Env_reg regs args 2 2%bv eq_refl); reflexivity).
assert (EE12 : bv_unsigned (ew E 12) = P) by (unfold E; rewrite (YE2y.Env_reg regs args 12 12%bv eq_refl), G12; unfold w64; apply unsigned_lit_small; lia).
assert (EEx : forall j, (j < n)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j args 0)).
{ intros j Hj. unfold E. apply YE2y.Env_x. apply nth_error_nth'. lia. }
assert (PRS0 : forall a, sp0 - WIN <= a < sp0 -> apresent H mem a) by (intros a Ha; apply Hpres; lia).
assert (HS0 : st_ok tfibsegs E (st0 f lo hb n fj) (restrict H (mkst regs (Z_to_bv 64 PC_ENTRY) mem (seg_rom tfibsegs)))).
{ apply (pcm_entry ly S U W regs mem md f lo hb n fj args P HAR Hrom Hh Cwf G11 G12 Hsp Hal16 PRS0 HP1 ltac:(lia) Hsl Hn Hrng Hfj). }
(* phase 1: internal_strlen (format) and its READ_RANGE *)
unfold cfg_at, w64.
eapply SRr_bind; [exact (YE2t.fp_phase_to W E PC_FMTD _ _ _ _ md HS0 R1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _). set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *. change (st_ok tfibsegs E e1 (restrict H ms1)) in HS1.
pose proof (meq_of_frame E _ _ _ sp0 Cw0 EE2 HF1) as MEQ1. cbn [ms_mem mkst] in MEQ1.
(* phase 2: to internal_memset's alignment branch *)
eapply SRr_bind; [exact (YE2t.fp_phase_to W E A_ISL _ _ _ _ _ HS1 R2)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & _). set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *. change (st_ok tfibsegs E e2 (restrict H ms2)) in HS2.
pose proof (meq_of_frame E _ _ _ sp0 Cw1 EE2 HF2) as MEQ2.
pose proof (st_ok_add_cond_neg tfibsegs E e2 _ BC_EQ MSC (SLit 0) HS2 (YE35.br_memset_align E sp0 2216 EE2 Hal16 eq_refl ltac:(lia) ltac:(lia))) as HS2'.
change (neg_bc BC_EQ) with BC_NE in HS2'.
(* phase 3: to the load of dir.fieldPrecision *)
eapply SRr_bind; [exact (YE2t.fp_phase_to W E A_ISL _ _ _ _ _ HS2' R3)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & _). set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *. change (st_ok tfibsegs E e3 (restrict H ms3)) in HS3.
pose proof (meq_of_frame E (ss_mem e2) _ _ sp0 Cw2 EE2 HF3) as MEQ3.
(* the 4-byte load of zero bytes *)
unfold lw_ok in Clw.
apply andb_prop in Clw as [Clw Cby]. apply andb_prop in Clw as [Clw _]. apply andb_prop in Clw as [Clw C24].
apply andb_prop in Clw as [Clw Cat3]. apply andb_prop in Clw as [Cpc3 Crv3].
apply Z.eqb_eq in Cpc3. apply resv_none_sound in Crv3. apply reg_is_sound in C24.
replace (Z_to_bv 5 24) with (24%bv : bv 5) in C24 by (apply bv_eq; reflexivity).
destruct (ss_mem e3) as [|r3 rest3] eqn:Hm3; [discriminate Cby|].
unfold top_ok in Ct3. rewrite Hm3 in Ct3. apply stk_shape_sound in Ct3 as (Hb3 & _ & _ & _ & _).
pose proof YE2t.lw_fetch as [LWlk LWdec].
assert (Hb4 : forall kk, 0 <= kk < 4 -> mbyte tfibsegs (mrestrict H (ms_mem ms3)) (sp0 - 2184 + bv_signed (4068%bv : bv 12) + kk) = Some (Z_to_bv 8 0)).
{ intros kk Hkk. change (bv_signed (4068%bv : bv 12)) with (-28).
pose proof (st_ok_mem_ok tfibsegs E e3 _ HS3) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hm3 in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
rewrite forallb_forall in Cby.
assert (Hkk' : In kk [0; 1; 2; 3]) by (cbn; lia).
specialize (Cby kk Hkk'). apply existsb_exists in Cby as (c & Hc & Hc1). apply chunk1_is_sound in Hc1. subst c.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hb3 in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
pose proof (val_of_chunk_ok tfibsegs E _ _ (-2212 + kk) 1 (SLit 0) 0 Hck eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
replace (sp0 - 2184 + -28 + kk) with (sp0 + (-2212 + kk)) by lia. etransitivity; [exact Hv0 | reflexivity]. }
assert (LWrs : sv_denot E (sr_get (ss_regs e3) 24%bv) = Z_to_bv 64 (sp0 - 2184)).
{ rewrite C24. cbn [sv_denot]. rewrite EE2. f_equal; lia. }
pose proof (YE2t.fp_lw_zero W E e3 ms3 md3 11%bv 24%bv (4068%bv : bv 12) YE2t.W_LW (sp0 - 2184) 40
HS3 Crv3 Cat3 ltac:(rewrite Cpc3; exact LWlk) LWdec eq_refl LWrs
ltac:(change (bv_signed (4068%bv : bv 12)) with (-28); lia)
ltac:(change (bv_signed (4068%bv : bv 12)) with (-28); lia)
ltac:(lia) Hb4) as STEP.
eapply SRr_bind; [exact STEP|]. clear STEP.
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4). set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
rewrite Cpc3 in HS4. change (set_regs_pc e3 [(11%bv, SLit 0)] (PC_LW + 4)) with (LW0 e3) in HS4.
(* phase 4: to the %s argument's internal_strlen *)
eapply SRr_bind; [exact (YE2t.fp_phase_to W E A_ISL _ _ _ _ _ HS4 R4)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & _). change (st_ok tfibsegs E e4 (restrict H ms5)) in HS5.
assert (Cw3' : wok (ss_mem (LW0 e3)) = true) by (change (ss_mem (LW0 e3)) with (ss_mem e3); rewrite Hm3; exact Cw3).
pose proof (meq_of_frame E (ss_mem (LW0 e3)) _ _ sp0 Cw3' EE2 HF5) as MEQ5.
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4) in *.
assert (SB5 : same_but_materialized md md5).
{ apply (same_but_materialized_trans _ md4); [|apply with_vm_backing_same].
apply (same_but_materialized_trans _ md3); [|apply with_vm_backing_same].
apply (same_but_materialized_trans _ md2); [|apply with_vm_backing_same].
apply (same_but_materialized_trans _ md1); apply with_vm_backing_same. }
assert (M5 : forall z : word, ~ (sp0 - WIN <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (MEQ5 z Hz). rewrite HM4. rewrite (MEQ3 z Hz). rewrite (MEQ2 z Hz). exact (MEQ1 z Hz). }
assert (PRS5 : forall a, sp0 - WIN <= a < sp0 -> apresent H (ms_mem ms5) a)
by (apply (win_present H E e4 ms5 sp0 HS5 Ct4 EE2); lia).
assert (HAR5 : ARU tfibsegs B ly S U W (ms_mem ms5) md5)
by (apply (aru_win B LAWS ly S U W mem md (ms_mem ms5) md5 sp0 HAR); first [lia | exact M5 | exact PRS0 | exact PRS5 | exact SB5]).
(* the %s check *)
unfold chk_ok in Cchk.
destruct (ss_mem e4) as [|r4 rest4] eqn:Hm4; [rewrite !Bool.andb_false_r in Cchk; discriminate Cchk|].
apply andb_prop in Cchk as [Cchk Cmem]. apply andb_prop in Cmem as [Cmem Crest]. apply andb_prop in Cmem as [Cr4 Cci].
apply andb_prop in Cchk as [Cchk Cma]. apply andb_prop in Cchk as [Cchk Cnc]. apply andb_prop in Cchk as [Cchk Cwf4].
apply andb_prop in Cchk as [Cchk S22]. apply andb_prop in Cchk as [Cchk S10]. apply andb_prop in Cchk as [Cchk S2].
apply andb_prop in Cchk as [Cchk S1]. apply andb_prop in Cchk as [Cchk Cat4]. apply andb_prop in Cchk as [Cpc4 Crv4].
apply Z.eqb_eq in Cpc4. apply resv_none_sound in Crv4.
apply reg_is_sound in S1, S2, S10, S22.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 5 2) with (2%bv : bv 5) in S2 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 10) with (10%bv : bv 5) in S10 by (apply bv_eq; reflexivity). replace (Z_to_bv 5 22) with (22%bv : bv 5) in S22 by (apply bv_eq; reflexivity).
apply stk_shape_sound in Cr4 as (Sb4 & Slo4 & Shi4 & Swl4 & Swh4).
rewrite forallb_forall in Crest.
set (x := nth jx args 0) in *.
pose proof Hstr as Hstr'. destruct Hstr' as (_ & Hx4096 & Hxhi & Hl40 & Hamx & Hrax & Hhullx & _).
assert (AVx : forall a, 0 <= a < sp0 - WIN -> aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem a).
{ intros a Ha. apply YF0x.aview_same. apply M5. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (pcm_scheck B LAWS TB W E e4 ms5 md5 ly S U sp0 r4 rest4 40 (32 + jx) x (Z.of_nat (length str)) (map (Z_to_bv 8) str)
HS5 Cpc4 Crv4 EE2 (EEx jx Hjx) Hm4 Sb4 Slo4 Shi4 Swl4 Swh4 S1 S2 S10 S22 Cat4 Cwf4 Cnc Cma Cci).
- intros r Hr. specialize (Crest r Hr). unfold rest_ok in Crest. apply andb_prop in Crest as [Crest _].
apply andb_prop in Crest as [Crest _]. apply Z.leb_le in Crest. exact Crest.
- intros r a Hr Ha. specialize (Crest r Hr). unfold rest_ok in Crest. apply andb_prop in Crest as [Crest Cb].
apply andb_prop in Crest as [_ Cl]. apply Z.leb_le in Cl. unfold OSP.
destruct (YP09.r_base r) as [[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]|] eqn:Hb; try discriminate Cb.
+ apply Z.leb_le in Cb. cbn [base_val] in Ha. rewrite EE12 in Ha. lia.
+ apply Z.leb_le in Cb. cbn [base_val] in Ha. lia.
- exact HAR5.
- lia.
- exact Hal16.
- lia.
- lia.
- exact PRS5.
- apply (vf_str_xfer W mem); [exact (cstr_vf W mem x str Hstr)|]. intros a Ha. rewrite length_map in Ha. apply AVx. lia.
- rewrite length_map. reflexivity.
- lia.
- lia.
- lia.
- apply (amem_range_le x (Z.of_nat (length str) + 8)); [exact Hamx | lia].
- eapply range_addressable_agree; [|exact Hrax]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (YE2y.shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AVx. lia.
- intros s' Hs'. rewrite AVx; [exact (Hhullx s' Hs') |].
pose proof (YE2y.shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (YE2y.shadow_addr_bounds (x + (Z.of_nat (length str) + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2.
set (q1 := shadow_addr x / 8) in *. set (q2 := shadow_addr (x + (Z.of_nat (length str) + 1) - 1) / 8) in *.
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (shadow_addr (x + (Z.of_nat (length str) + 1) - 1)) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (shadow_addr (x + (Z.of_nat (length str) + 1) - 1)) 8 ltac:(lia)) as D4.
fold q1 in D1. fold q2 in D3.
set (m1 := shadow_addr x mod 8) in *. set (m2 := shadow_addr (x + (Z.of_nat (length str) + 1) - 1) mod 8) in *. lia. }
cbv beta. intros W6 c6 _ (-> & ms6 & md6 & -> & HS6 & HAR6 & SB6 & MEQ6 & PM6).
unfold OSP in MEQ6.
(* phase 5: the rest of the format, the epilogue *)
set (E1 := havoc E 40 (map (getr (ms_regs ms6)) YE2t.CLOBP)) in HS6.
assert (E1_2 : bv_unsigned (ew E1 2) = sp0) by (subst E1; rewrite ew_havoc_old by lia; exact EE2).
eapply SRr_bind; [exact (YE2t.fp_phase_to W E1 A_ISL _ _ _ _ _ HS6 R5)|].
intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & _). change (st_ok tfibsegs E1 e5 (restrict H ms7)) in HS7.
pose proof (meq_of_frame E1 _ _ _ sp0 Cw4 E1_2 HF7) as MEQ7.
assert (M7 : forall z : word, ~ (sp0 - WIN <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (MEQ7 z Hz). rewrite (MEQ6 z ltac:(lia)). exact (M5 z Hz). }
set (md7 := with_vm_backing (m_vm_lazy md6) mat7 md6) in *.
assert (SB7 : same_but_materialized md md7).
{ subst md7. eapply same_but_materialized_trans; [exact SB5|]. eapply same_but_materialized_trans; [exact SB6|]. apply with_vm_backing_same. }
(* the final ret *)
unfold end_ok in Cend.
apply andb_prop in Cend as [Cend Ccs]. apply andb_prop in Cend as [Cend Clk]. apply andb_prop in Cend as [Cend C1].
apply andb_prop in Cend as [Crv5 Ct5]. apply resv_none_sound in Crv5. apply reg_is_sound in C1.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in C1 by (apply bv_eq; reflexivity).
assert (Hlk5 : clookup tbl_fp (ss_pc e5) = Some RET_WORD_r).
{ destruct (clookup tbl_fp (ss_pc e5)) as [w|]; [|discriminate Clk]. apply Z.eqb_eq in Clk. rewrite Clk. reflexivity. }
assert (PRS7 : forall a, sp0 - WIN <= a < sp0 -> apresent H (ms_mem ms7) a)
by (apply (win_present H E1 e5 ms7 sp0 HS7 Ct5 E1_2); lia).
apply (SRr_ret_at tfibsegs tbl_fp tbl_fp_ok Hwx W E1 e5 ms7 md7 _ HS7 Crv5 Hlk5).
intros mat'. set (md8 := with_vm_backing (m_vm_lazy md7) mat' md7).
assert (SB8 : same_but_materialized md md8) by (subst md8; eapply same_but_materialized_trans; [exact SB7 | apply with_vm_backing_same]).
assert (R7_1 : getr (ms_regs ms7) 1 = getr regs 1).
{ rewrite (YF0x.st_ok_reg_denot H E1 e5 ms7 1%bv HS7), C1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
subst E1. rewrite ew_havoc_old by lia. unfold E. apply (YE2y.Env_reg regs args 1 1%bv eq_refl). }
split; [reflexivity|]. exists (ms_regs ms7), (ms_mem ms7), md8.
split; [|split; [|split; [|split; [|split]]]].
- unfold cfg_at. f_equal. f_equal. rewrite R7_1. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. exact Hra.
- apply (aru_win B LAWS ly S U W mem md (ms_mem ms7) md8 sp0 HAR); first [lia | exact M7 | exact PRS0 | exact PRS7 | exact SB8].
- apply (YE2y.aregs_preserved_of_st_ok H E1 e5 ms7 regs (map (Z_to_bv 64) args) HS7); [|exact Ccs].
subst E1. apply env_agree_havoc_ge; [lia|]. apply env_agree_refl.
- exact SB8.
- intros a Ha Hna. unfold STK_PCOM, ESTACK in Hna. fold sp0 in Hna. apply YF0x.aview_same. apply M7. rewrite unsigned_lit_small by lia. lia.
- intros a Hp. rewrite (YE2y.apresent_mod _ (ms_mem ms7) a). rewrite (YE2y.apresent_mod _ mem a) in Hp.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hmr. set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - WIN)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms7) a'); [apply M7; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS7; lia|].
apply (apresent_same H mem (ms_mem ms7) a'); [apply M7; rewrite unsigned_lit_small by lia; lia | exact Hp].
Qed.
End m.
End w.
