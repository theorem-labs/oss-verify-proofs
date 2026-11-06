(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_crtE.v, relocated by b_reloc.py (crt): every image
   numeral re-derived by symbol / section / string content, revcheck report (internal path). *)
(* check_round_trip, the loop's control stretches (fuzz_manifest.c:274-288): the loop setup after as_ruled (0x810c4),
   the loop head (0x810f8): the ASan shadow check of uri[k - 1] through s9, the '>' test, `addi s9,s9,1` with its UBSan
   trap guard, and the plain (uri + k) call; the plain = false step (0x81124), and the loop step (0x811c8). The report
   of the shadow check at 0x811dc is unreachable: the byte uri[k - 1] is addressable (cstr_ok's range_addressable), so
   the tok executor (YCbq aj_run_to_tok) takes the fast path through it. The trap guard 0x81118 (`beqz s9` -> the
   `unimp` at 0x81270) is refuted: there s9 = uri + k, and 4096 <= uri. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the loop head's symbolic state: the byte uri[k - 1] (atom 32) one below s3, s9 = uri + k - 1 in the low band,
   s10 = the shadow base; the shadow entry says the byte at s9 is addressable ---- *)
Definition crtL_byte : YP09.region := YP09.mkRegion (Some 19%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))].
Definition ss_crtL : sstate :=
  mkSS CRT_L sr_atoms [crtL_byte] None
    (mkFacts [(25%nat, mkAF 4096 (2 ^ 47 - 16) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] []).
Definition CRT_Bx : sv := SOff 26 0.
Definition CRT_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Definition CRT_SH : list shent := [mkSHE 25 0 1].

Section E. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- small kit ---- *)
(* a resumed state with atom facts and no regions *)
Lemma crt_resume_f : forall (W : world tfibsegs) regs extra mem pc fs, atoms_ok (Ereg regs extra) fs ->
  st_ok tfibsegs (Ereg regs extra) (mkSS pc sr_atoms [] None (mkFacts fs [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W regs extra mem pc fs Hfs. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- cbn. tauto.
- split; [exact Hfs | split; exact I].
Qed.
Lemma crt_afact : forall regs extra n (r : bv 5) v lo hi, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  0 <= v < 2 ^ 64 -> lo <= v <= hi -> afact_ok (Ereg regs extra) n (mkAF lo hi 0).
Proof.
intros regs extra n r v lo hi Hn Hr Hv Hlh. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* a register the run left as an offset of an entry atom, read as w64 *)
Lemma crt_reg_w64 : forall (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + z).
Proof.
intros H E ss ms r n z v HS Hr Hn Hv.
pose proof (fmw_reg_off H E ss ms r n z v HS Hr Hn Hv) as Hu.
unfold w64. rewrite <- Hu. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the unsigned value of a register known as w64 v *)
Lemma crt_u64 : forall regs (r : bv 5) v, getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr regs r) = v.
Proof. intros regs r v Hr Hv. rewrite Hr. unfold w64. apply unsigned_lit_small. lia. Qed.
(* a register the run left as an atom, under any environment *)
Lemma crt_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fmw_SOff0.
Qed.

(* the frame of check_round_trip lies above the allocation ceiling and is 16-aligned *)
Lemma crt_sp_bounds : forall cx ly S (W : world tfibsegs) mem md k0, crt_J B cx ly S W mem md k0 ->
  alloc_ceiling + CRT_FRAME <= cx_sp0 cx /\ cx_sp0 cx <= 2 ^ 47 /\ (cx_sp0 cx - CRT_FRAME) mod 16 = 0.
Proof.
intros cx ly S W mem md k0 HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
split; [unfold CRT_FRAME; lia|]. split; [lia|].
replace (cx_sp0 cx - CRT_FRAME) with (cx_sp0 cx + (-7) * 16) by (unfold CRT_FRAME; lia).
rewrite Z_mod_plus_full. exact Hal16.
Qed.

(* crt_tcore is kept by a stretch that changes only the loop registers and leaves memory as it was *)
Lemma crt_tcore_same : forall cx ly S (W : world tfibsegs) regs mem md regs' mem' md' k0 t m,
  crt_tcore B cx ly S W regs mem md k0 t m ->
  crt_J B cx ly S W mem' md' k0 -> same_below mem mem' (2 ^ 64) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 26 = getr regs 26 ->
  crt_tcore B cx ly S W regs' mem' md' k0 t m.
Proof.
intros cx ly S W regs mem md regs' mem' md' k0 t m
  ((HJ & HFR & Hsp & R3 & R4 & R8 & R26 & Hu & Hku & HRO) & Hk0 & Hn1 & R9 & R18 & Ht & Hperm & HG)
  HJ' SB Q2 Q3 Q4 Q8 Q9 Q18 Q26.
pose proof (crt_sp_bounds cx ly S W mem md k0 HJ) as (Hsplo & Hsp2 & _).
pose proof (proj1 alloc_ceiling_val) as HAC.
assert (SBc : same_below mem mem' alloc_ceiling)
  by (apply (same_below_mono _ _ _ _ SB); unfold CRT_FRAME in *; lia).
split; [split; [exact HJ'|] | split; [exact Hk0 | split; [exact Hn1|]]].
- split; [exact (crt_frame_below cx W mem mem' SB ltac:(unfold CRT_FRAME in *; lia) Hsp2 HFR)|].
  split; [unfold spZ in *; rewrite Q2; exact Hsp|].
  split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|]. split; [rewrite Q8; exact R8|].
  split; [rewrite Q26; exact R26|].
  split; [exact (cstr_ok_below W mem mem' _ _ SBc Hu)|].
  split; [exact Hku|]. exact (arodata_below B W mem mem' SBc HRO).
- split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|]. split; [exact Ht|].
  split; [exact Hperm|]. exact (fm_glob_below W mem mem' _ _ _ _ SBc HG).
Qed.
(* the loop registers are kept by a stretch that keeps s3, s4..s9, s11 *)
Lemma crt_lregs_same : forall cx regs regs' k h,
  crt_lregs cx regs k h ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 -> getr regs' 27 = getr regs 27 ->
  crt_lregs cx regs' k h.
Proof.
intros cx regs regs' k h (R19 & R25 & R20 & R21 & R22 & R23 & R24 & R27) Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q27.
split; [rewrite Q19; exact R19|]. split; [rewrite Q25; exact R25|]. split; [rewrite Q20; exact R20|].
split; [rewrite Q21; exact R21|]. split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|].
split; [rewrite Q24; exact R24|]. rewrite Q27; exact R27.
Qed.

(* ---- the pure loop facts ---- *)
Lemma crt_firstn_S : forall (l : list Z) k, (k < length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
intros l. induction l as [|c l IH]; intros k Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; cbn [firstn nth app]; [reflexivity|].
rewrite (IH k ltac:(lia)). reflexivity.
Qed.
Lemma crt_gt_step : forall (ub : list Z) (k : nat), (1 <= k)%nat -> (k - 1 < length ub)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn (k - 1) ub) = true -> ManifestModel.byte_at ub (k - 1) <> 62 ->
  forallb (fun c => negb (c =? 62)) (firstn k ub) = true.
Proof.
intros ub k Hk1 Hk Hf Hb. destruct k as [|k']; [lia|].
replace (S k' - 1)%nat with k' in Hk, Hf, Hb by lia.
rewrite (crt_firstn_S ub k' Hk), forallb_app. apply andb_true_intro. split; [exact Hf|].
cbn [forallb andb]. rewrite andb_true_r. unfold ManifestModel.byte_at in Hb.
apply negb_true_iff. apply Z.eqb_neq. exact Hb.
Qed.
(* the reader calls the split points from k on make, in terms of the ones from k + 1 on *)
Lemma crt_rest_step : forall cx (k : nat), (k < length (cx_ub cx))%nat ->
  ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62 ->
  crt_rest cx k = 4 * (if ManifestModel.plain_name (skipn k (cx_ub cx)) then 1 else 0) + crt_rest cx (S k).
Proof.
intros cx k Hk Hb. unfold crt_rest.
replace (length (cx_ub cx) - k + 1)%nat with (S (length (cx_ub cx) - S k + 1)) by lia.
cbn [rt_used].
replace ((k <? length (cx_ub cx))%nat && negb (ManifestModel.byte_at (cx_ub cx) (k - 1) =? 62))%bool with true.
2:{ symmetry. apply andb_true_intro. split; [apply Nat.ltb_lt; lia|].
    apply negb_true_iff. apply Z.eqb_neq. exact Hb. }
rewrite Nat2Z.inj_add. destruct (ManifestModel.plain_name (skipn k (cx_ub cx))); cbn [Z.of_nat]; lia.
Qed.
(* at the last split point there is nothing left *)
Lemma crt_rest_end : forall cx (k : nat), (length (cx_ub cx) <= k)%nat -> crt_rest cx k = 0.
Proof.
intros cx k Hk. unfold crt_rest. replace (length (cx_ub cx) - k + 1)%nat with 1%nat by lia.
cbn [rt_used]. replace ((k <? length (cx_ub cx))%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
cbn [andb Z.of_nat]. lia.
Qed.
(* a split point whose byte is '>' ends the loop *)
Lemma crt_rest_gt : forall cx (k : nat), ManifestModel.byte_at (cx_ub cx) (k - 1) = 62 -> crt_rest cx k = 0.
Proof.
intros cx k Hb. unfold crt_rest.
destruct (length (cx_ub cx) - k + 1)%nat as [|f] eqn:Ef; [cbn [rt_used]; lia|].
cbn [rt_used]. rewrite Hb, Z.eqb_refl. rewrite andb_false_r. cbn [Z.of_nat]. lia.
Qed.
(* n = 1: the loop body never runs *)
Lemma crt_calls_one : forall (ub : list Z), length ub = 1%nat -> rt_calls ub = 3.
Proof.
intros ub Hl. destruct ub as [|c ub']; cbn [length] in Hl; [lia|].
destruct ub'; cbn [length] in Hl; [|lia]. unfold rt_calls, rt_nk, rt_used. cbn [length].
replace ((1 <? 1)%nat) with false by reflexivity. cbn [andb Z.of_nat]. lia.
Qed.

Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis PLAIN : plain_spec tfibsegs B.

(* ---- 0x811c8: s3++, s11--, s4++ (addiw); bnez s11 -> the loop head at k + 1, else the exit. s9 = uri + k stays: the
   head moved it on ---- *)
Lemma crt_segI : forall cx ly' S' W' regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_I B cx ly' S' W' regs' mem' md' k0 t m k ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_L B cx ly'' S'' W'' regs'' mem'' md'' k0 t m (S k) ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_L regs'' mem'' md'') (crt_post B cx)) ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_X B cx ly'' S'' W'' regs'' mem'' md'' k0 t ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_X regs'' mem'' md'') (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L9 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB (HT & HL & Hk & Hm & Hgt) KL KX.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HB as (_ & _ & _ & Hu0 & _ & Hlu & _).
pose proof HL as (R19 & R25 & R20 & R21 & R22 & R23 & R24 & R27).
pose proof HT as ((HJ & HFR & Hsp & _) & _).
pose proof HJ as HJ0. unfold crt_J in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 alloc_ceiling_val).
pose proof (crt_sp_bounds cx ly S W mem md k0 HJ0) as (Hsplo & Hsphi & Hspmod).
assert (Hsp0 : 0 <= cx_sp0 cx - CRT_FRAME /\ cx_sp0 cx <= 2 ^ 47) by (unfold CRT_FRAME in *; lia).
assert (Hn : 1 <= Z.of_nat k < cx_n cx) by exact Hk.
unfold cx_n in Hn. unfold cx_n in Hlu.
pose proof (crt_resume_f W regs [] mem CRT_L9 [(20%nat, mkAF 1 255 0)]
  (conj (crt_afact regs [] 20 20%bv (Z.of_nat k) 1 255 eq_refl R20 ltac:(lia) ltac:(lia)) I)) as HS.
set (E := Ereg regs ([] : list word)) in HS.
pose proof Hu0 as (_ & H4096u & Hclu & _).
assert (U19 : bv_unsigned (ew E 19) = cx_u cx + Z.of_nat k)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); apply crt_u64; [exact R19 | lia]).
assert (U20 : bv_unsigned (ew E 20) = Z.of_nat k)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); apply crt_u64; [exact R20 | lia]).
assert (U27 : bv_unsigned (ew E 27) = Z.of_nat (length (cx_ub cx)) - Z.of_nat k)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); apply crt_u64; [exact R27 | lia]).
unfold cfg_at. change (w64 CRT_L9) with (Z_to_bv 64 CRT_L9).
aj_run fmw_tbl_crt_ok HS HJ0.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
clear HF HFr HG.
assert (U27m : U E (SOff 27 (-1)) = Z.of_nat (length (cx_ub cx)) - Z.of_nat k + -1).
{ apply (U_atom_off E 27 (Z.of_nat (length (cx_ub cx)) - Z.of_nat k) (-1));
    [unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27 | lia | lia]. }
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 27 (-1)) (b := SLit 0); [exact HS | intros Hb HS2 | intros Hb HS2];
  rewrite ?branch_ne_U, U27m, (U_lit E 0 ltac:(lia)) in Hb; clear HS.
- (* n - k - 1 <> 0: back to the loop head at k + 1 *)
  assert (Hne : Z.of_nat (length (cx_ub cx)) - Z.of_nat k - 1 <> 0)
    by (apply negb_true_iff, Z.eqb_neq in Hb; lia).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_L.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) (2 ^ 64))
    by (match goal with H : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ => exact (frame_nil_same _ _ _ H) end).
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1 SB2) as SB.
  pose proof (fmw_reg_atom _ regs _ _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs _ _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs _ _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs _ _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs _ _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs _ _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs _ _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  pose proof (fmw_reg_atom _ regs _ _ ms2 22%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q22.
  pose proof (fmw_reg_atom _ regs _ _ ms2 23%bv 23%bv 23 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q23.
  pose proof (fmw_reg_atom _ regs _ _ ms2 24%bv 24%bv 24 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q24.
  pose proof (fmw_reg_atom _ regs _ _ ms2 25%bv 25%bv 25 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q25.
  pose proof (fmw_reg_atom _ regs _ _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  pose proof (crt_reg_w64 _ E _ ms2 19%bv 19 1 _ HS2 ltac:(vm_compute; reflexivity) U19 ltac:(lia)) as Q19.
  pose proof (crt_reg_w64 _ E _ ms2 20%bv 20 1 _ HS2 ltac:(vm_compute; reflexivity) U20 ltac:(lia)) as Q20.
  pose proof (crt_reg_w64 _ E _ ms2 27%bv 27 (-1) _ HS2 ltac:(vm_compute; reflexivity) U27 ltac:(lia)) as Q27.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 CRT_L) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_L (ms_regs ms2) (ms_mem ms2) mm).
  apply (KL ly S W (ms_regs ms2) (ms_mem ms2) _).
  split; [|split; [|split]].
  + eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms2) (ms_mem ms2) _ k0 t m HT HJ0 SB); assumption.
  + (* s9 = uri + k addresses the next split point's uri[(k + 1) - 1] *)
    split; [rewrite Q19; unfold w64; f_equal; lia|].
    split; [rewrite Q25, R25; unfold w64; f_equal; lia|].
    split; [rewrite Q20; unfold w64; f_equal; lia|].
    split; [rewrite Q21; exact R21|]. split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|].
    split; [rewrite Q24; exact R24|].
    rewrite Q27; unfold cx_n; unfold w64; f_equal; lia.
  + unfold cx_n. lia.
  + split; [exact Hm|].
    replace (Datatypes.S k - 1)%nat with k by lia. exact Hgt.
- (* n - k - 1 = 0: the exit *)
  assert (Heq : Z.of_nat (length (cx_ub cx)) - Z.of_nat k - 1 = 0)
    by (apply negb_false_iff, Z.eqb_eq in Hb; lia).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_X.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) (2 ^ 64))
    by (match goal with H : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ => exact (frame_nil_same _ _ _ H) end).
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1 SB2) as SB.
  pose proof (fmw_reg_atom _ regs _ _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs _ _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs _ _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs _ _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs _ _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs _ _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs _ _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 CRT_X) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_X (ms_regs ms2) (ms_mem ms2) mm).
  apply (KX ly S W (ms_regs ms2) (ms_mem ms2) _).
  unfold crt_X. replace (rt_calls (cx_ub cx)) with m.
  2:{ rewrite <- Hm. rewrite (crt_rest_end cx (Datatypes.S k) ltac:(lia)). lia. }
  eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms2) (ms_mem ms2) _ k0 t m HT HJ0 SB); assumption.
Qed.

(* ---- 0x81124: plain (uri + k) answered 0; beqz a0 taken -> the loop step ---- *)
Lemma crt_segL1n : forall cx ly' S' W' regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_L1 B cx ly' S' W' regs' mem' md' k0 t m k ->
  ManifestModel.plain_name (skipn k (cx_ub cx)) = false ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_I B cx ly'' S'' W'' regs'' mem'' md'' k0 t m k ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_L9 regs'' mem'' md'') (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L1 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB ((HT & HL & Hk & Hm & Hgt) & Hb62 & H10) Hpf KI.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HB as (_ & _ & _ & Hu0 & _ & Hlu & _).
pose proof HT as ((HJ & HFR & Hsp & _) & _).
pose proof HJ as HJ0. unfold crt_J in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 alloc_ceiling_val).
pose proof (crt_sp_bounds cx ly S W mem md k0 HJ0) as (Hsplo & Hsphi & Hspmod).
assert (Hsp0 : 0 <= cx_sp0 cx - CRT_FRAME /\ cx_sp0 cx <= 2 ^ 47) by (unfold CRT_FRAME in *; lia).
assert (Hn : 1 <= Z.of_nat k < cx_n cx) by exact Hk. unfold cx_n in Hn. unfold cx_n in Hlu.
rewrite Hpf in H10.
pose proof (fmw_resume_nr W regs [] mem CRT_L1) as HS.
set (E := Ereg regs ([] : list word)) in HS.
assert (U10 : U E (SOff 10 0) = 0)
  by (apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10 | lia]).
unfold cfg_at. change (w64 CRT_L1) with (Z_to_bv 64 CRT_L1).
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hbr HS2 | intros Hbr HS2];
  rewrite ?branch_eq_U, U10, (U_lit E 0 ltac:(lia)) in Hbr; clear HS.
2:{ exfalso. cbn in Hbr. discriminate Hbr. }
aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_L9.
{ apply awr_ok_nil. }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms1 end.
assert (SB : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
pose proof (fmw_reg_atom _ regs _ _ ms1 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs _ _ ms1 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs _ _ ms1 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs _ _ ms1 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs _ _ ms1 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
pose proof (fmw_reg_atom _ regs _ _ ms1 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
pose proof (fmw_reg_atom _ regs _ _ ms1 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
pose proof (fmw_reg_atom _ regs _ _ ms1 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q20.
pose proof (fmw_reg_atom _ regs _ _ ms1 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
pose proof (fmw_reg_atom _ regs _ _ ms1 22%bv 22%bv 22 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q22.
pose proof (fmw_reg_atom _ regs _ _ ms1 23%bv 23%bv 23 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q23.
pose proof (fmw_reg_atom _ regs _ _ ms1 24%bv 24%bv 24 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q24.
pose proof (fmw_reg_atom _ regs _ _ ms1 25%bv 25%bv 25 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q25.
pose proof (fmw_reg_atom _ regs _ _ ms1 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
pose proof (fmw_reg_atom _ regs _ _ ms1 27%bv 27%bv 27 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q27.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS2 eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 CRT_L9) (ms_mem ms1) (seg_rom tfibsegs)) ?mm)
  with (cfg_at tfibsegs CRT_L9 (ms_regs ms1) (ms_mem ms1) mm).
apply (KI ly S W (ms_regs ms1) (ms_mem ms1) _).
split; [|split; [|split]].
- eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms1) (ms_mem ms1) _ k0 t m HT HJ0 SB); assumption.
- eapply (crt_lregs_same cx regs (ms_regs ms1) k 1 HL); assumption.
- unfold cx_n. lia.
- split.
  + rewrite <- Hm. rewrite (crt_rest_step cx k ltac:(lia) Hb62), Hpf. lia.
  + exact (crt_gt_step (cx_ub cx) k ltac:(lia) ltac:(lia) Hgt Hb62).
Qed.

(* ---- 0x810f8: the shadow check of uri[k - 1] through s9, the '>' test, s9 := uri + k and its trap guard, and
   plain (uri + k) ---- *)
Lemma crtL_entry : forall (W : world tfibsegs) mem regs u k c,
  getr regs 19 = w64 (u + k) -> getr regs 25 = w64 (u + k - 1) -> getr regs 26 = w64 FMW_SB ->
  4096 <= u -> 1 <= k -> u + k <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (rdW W mem) (u + k - 1) 1 c ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 c]) ss_crtL (restrict (w_H W) (mkst regs (Z_to_bv 64 CRT_L) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs u k c R19 R25 R26 Hu Hk Hc Hcr Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs [Z_to_bv 64 c]).
assert (U19 : bv_unsigned (ew E 19) = u + k)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = u + k - 1)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), R26; unfold w64; rewrite unsigned_lit_small;
      unfold FMW_SB, SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
unfold ss_crtL. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 c]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold crtL_byte. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ (u + k) (-1) 1 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
  replace (u + k + -1) with (u + k - 1) by lia. exact Vc.
- apply pairwise_disjoint_of_extents. unfold crtL_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U25, U26, E32, unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma crt_segL : forall cx ly' S' W' regs' mem' md' k0 t m (k : nat),
  crt_base B cx -> crt_L B cx ly' S' W' regs' mem' md' k0 t m k ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_X B cx ly'' S'' W'' regs'' mem'' md'' k0 t ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_X regs'' mem'' md'') (crt_post B cx)) ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_L1 B cx ly'' S'' W'' regs'' mem'' md'' k0 t m k ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_L1 regs'' mem'' md'') (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_L regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t m k HB HLL KX K1.
pose proof HLL as (HT & HL & Hk & Hm & Hgt).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & HCTX & H10e & Hu0 & Hku0 & Hlu & HG0 & HQ & Hlive & Hev & Hbb).
pose proof HL as (R19 & R25 & R20 & R21 & R22 & R23 & R24 & R27).
rewrite Z.add_0_r in R25.
pose proof HT as (HC & Hk0 & Hn1 & R9 & R18 & Ht & Hperm & Hglob).
pose proof HC as (HJ0 & HFR & Hsp & R3 & R4 & R8 & R26 & Hu & Hku & HRO).
pose proof HJ0 as HJ. unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 alloc_ceiling_val).
pose proof (crt_sp_bounds cx ly S W mem md k0 HJ0) as (Hsplo & Hsphi & Hspmod).
assert (Hsp0 : 0 <= cx_sp0 cx - CRT_FRAME /\ cx_sp0 cx <= 2 ^ 47) by (unfold CRT_FRAME in *; lia).
assert (Hspl : alloc_ceiling <= cx_sp0 cx - CRT_FRAME) by (unfold CRT_FRAME in *; lia).
assert (Hn : 1 <= Z.of_nat k < cx_n cx) by exact Hk. unfold cx_n in Hn. unfold cx_n in Hlu.
pose proof Hu as ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & HRA & Hhv & Htl).
assert (Hkn : (k - 1 < length (cx_ub cx))%nat) by lia.
destruct (Hg (k - 1)%nat ltac:(rewrite length_app; cbn; lia)) as (Vc & Hcr).
rewrite app_nth1 in Vc, Hcr by exact Hkn.
replace (cx_u cx + Z.of_nat (k - 1)) with (cx_u cx + Z.of_nat k - 1) in Vc by lia.
pose proof (crtL_entry W mem regs (cx_u cx) (Z.of_nat k) (nth (k - 1) (cx_ub cx) 0) R19 R25 R26 H4096
  ltac:(lia) ltac:(lia) Hcr Vc) as HS.
set (c := nth (k - 1) (cx_ub cx) 0) in *.
set (E := Ereg regs [Z_to_bv 64 c]) in HS.
assert (SHOK : sh_ok tfibsegs CRT_Bx CRT_SH E (rdW W (ms_mem (mkst regs (Z_to_bv 64 CRT_L) mem (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E CRT_Bx 25 (cx_u cx) (Z.of_nat (length (cx_ub cx)) + 1)
    (cx_u cx + Z.of_nat k - 1) 0 1 HRA).
  - unfold CRT_Bx. apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia. }
assert (U19 : bv_unsigned (ew E 19) = cx_u cx + Z.of_nat k)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); apply crt_u64; [exact R19 | lia]).
assert (U25 : bv_unsigned (ew E 25) = cx_u cx + Z.of_nat k - 1)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); apply crt_u64; [exact R25 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (Hc256 : 0 <= c < 256) by exact Hcr.
unfold cfg_at. change (w64 CRT_L) with (Z_to_bv 64 CRT_L).
change mem with (ms_mem (mkst regs (Z_to_bv 64 CRT_L) mem (seg_rom tfibsegs))) in HJ0.
aj_run_to_tok fmw_tbl_crt_ok HS HJ0 SHOK CRT_Bspan 0x81110.
{ awr_ok_tac. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS, SHOK end.
assert (AG : forall n, (n < 33)%nat -> ew E1 n = ew E n)
  by (intros n Hn33; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (AGr : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r Hn32 Hr; rewrite (AG n ltac:(lia)); unfold E; apply ew_Ereg_nat; exact Hr).
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64)).
{ match goal with H : frame_of _ ?rs mem (ms_mem ms1) |- _ =>
    apply (same_below_frame E rs mem (ms_mem ms1) (2 ^ 64) H); [|lia] end.
  cbn [ss_mem ss_crtL add_cond]. unfold crtL_byte. apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
assert (U10 : U E1 (SOff 32 0) = c)
  by (apply U_atom; [rewrite (AG 32%nat ltac:(lia)); exact E32 | lia]).
assert (U11 : U E1 (SLit 62) = 62) by (apply U_lit; lia).
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 32 0) (b := SLit 62); [exact HS | intros Hbr HS2 | intros Hbr HS2];
  rewrite ?branch_eq_U, U10, U11 in Hbr; clear HS.
- (* uri[k - 1] = '>': the exit; no split point from k on makes a reader call *)
  assert (Hc62 : ManifestModel.byte_at (cx_ub cx) (k - 1) = 62) by (apply Z.eqb_eq in Hbr; exact Hbr).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_X.
  { awr_ok_tac. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) (2 ^ 64)).
  { match goal with H : frame_of _ ?rs (ms_mem ms1) (ms_mem ms2) |- _ =>
      apply (same_below_frame E1 rs (ms_mem ms1) (ms_mem ms2) (2 ^ 64) H); [|lia] end.
    cbn [ss_mem ss_crtL add_cond]. unfold crtL_byte. apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1 SB2) as SB.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 2%bv 2 HS2 ltac:(vm_compute; reflexivity)) (AGr 2%nat 2%bv ltac:(lia) eq_refl)) as Q2.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 3%bv 3 HS2 ltac:(vm_compute; reflexivity)) (AGr 3%nat 3%bv ltac:(lia) eq_refl)) as Q3.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 4%bv 4 HS2 ltac:(vm_compute; reflexivity)) (AGr 4%nat 4%bv ltac:(lia) eq_refl)) as Q4.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 8%bv 8 HS2 ltac:(vm_compute; reflexivity)) (AGr 8%nat 8%bv ltac:(lia) eq_refl)) as Q8.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 9%bv 9 HS2 ltac:(vm_compute; reflexivity)) (AGr 9%nat 9%bv ltac:(lia) eq_refl)) as Q9.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 18%bv 18 HS2 ltac:(vm_compute; reflexivity)) (AGr 18%nat 18%bv ltac:(lia) eq_refl)) as Q18.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 26%bv 26 HS2 ltac:(vm_compute; reflexivity)) (AGr 26%nat 26%bv ltac:(lia) eq_refl)) as Q26.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 CRT_X) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_X (ms_regs ms2) (ms_mem ms2) mm).
  apply (KX ly S W (ms_regs ms2) (ms_mem ms2) _).
  unfold crt_X. replace (rt_calls (cx_ub cx)) with m by (rewrite <- Hm; rewrite (crt_rest_gt cx k Hc62); lia).
  eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms2) (ms_mem ms2) _ k0 t m HT HJ0 SB); assumption.
- (* uri[k - 1] <> '>': s9 := uri + k, its trap guard, plain (uri + k) *)
  assert (Hc62 : ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62) by (apply Z.eqb_neq in Hbr; exact Hbr).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 0x81118.
  { awr_ok_tac. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into msg end.
  assert (SBg : same_below (ms_mem ms1) (ms_mem msg) (2 ^ 64)).
  { match goal with H : frame_of _ ?rs (ms_mem ms1) (ms_mem msg) |- _ =>
      apply (same_below_frame E1 rs (ms_mem ms1) (ms_mem msg) (2 ^ 64) H); [|lia] end.
    cbn [ss_mem ss_crtL add_cond]. unfold crtL_byte. apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
  (* s9 after `addi s9,s9,1` (0x81114): uri + k *)
  assert (U25g : U E1 (SOff 25 1) = cx_u cx + Z.of_nat k - 1 + 1).
  { apply (U_atom_off E1 25 (cx_u cx + Z.of_nat k - 1) 1); [|lia|lia].
    rewrite (AG 25%nat ltac:(lia)). unfold E. rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl). exact R25. }
  (* UBSan trap guard 0x81118 -> 0x81270, refuted *)
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 25 1) (b := SLit 0);
    [exact HS2 | intros Htr HS3 | intros Htr HS3]; clear HS2.
  { fm_kill_trap Htr. }
  rename HS3 into HS2.
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 A_plain.
  { awr_ok_tac. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem msg) (ms_mem ms2) (2 ^ 64)).
  { match goal with H : frame_of _ ?rs (ms_mem msg) (ms_mem ms2) |- _ =>
      apply (same_below_frame E1 rs (ms_mem msg) (ms_mem ms2) (2 ^ 64) H); [|lia] end.
    cbn [ss_mem ss_crtL add_cond]. unfold crtL_byte. apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1
    (same_below_trans (ms_mem ms1) (ms_mem msg) (ms_mem ms2) (2 ^ 64) SBg SB2)) as SB.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (crt_reg_w64 _ E1 _ ms2 10%bv 19 0 _ HS2 ltac:(vm_compute; reflexivity)
    ltac:(rewrite (AG 19%nat ltac:(lia)); exact U19) ltac:(lia)) as P10.
  rewrite Z.add_0_r in P10.
  pose proof (fmw_reg_lit _ E1 _ ms2 1%bv CRT_L1 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_L1; lia)) as P1.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 2%bv 2 HS2 ltac:(vm_compute; reflexivity)) (AGr 2%nat 2%bv ltac:(lia) eq_refl)) as Q2.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 3%bv 3 HS2 ltac:(vm_compute; reflexivity)) (AGr 3%nat 3%bv ltac:(lia) eq_refl)) as Q3.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 4%bv 4 HS2 ltac:(vm_compute; reflexivity)) (AGr 4%nat 4%bv ltac:(lia) eq_refl)) as Q4.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 8%bv 8 HS2 ltac:(vm_compute; reflexivity)) (AGr 8%nat 8%bv ltac:(lia) eq_refl)) as Q8.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 9%bv 9 HS2 ltac:(vm_compute; reflexivity)) (AGr 9%nat 9%bv ltac:(lia) eq_refl)) as Q9.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 18%bv 18 HS2 ltac:(vm_compute; reflexivity)) (AGr 18%nat 18%bv ltac:(lia) eq_refl)) as Q18.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 19%bv 19 HS2 ltac:(vm_compute; reflexivity)) (AGr 19%nat 19%bv ltac:(lia) eq_refl)) as Q19.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 20%bv 20 HS2 ltac:(vm_compute; reflexivity)) (AGr 20%nat 20%bv ltac:(lia) eq_refl)) as Q20.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 21%bv 21 HS2 ltac:(vm_compute; reflexivity)) (AGr 21%nat 21%bv ltac:(lia) eq_refl)) as Q21.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 22%bv 22 HS2 ltac:(vm_compute; reflexivity)) (AGr 22%nat 22%bv ltac:(lia) eq_refl)) as Q22.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 23%bv 23 HS2 ltac:(vm_compute; reflexivity)) (AGr 23%nat 23%bv ltac:(lia) eq_refl)) as Q23.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 24%bv 24 HS2 ltac:(vm_compute; reflexivity)) (AGr 24%nat 24%bv ltac:(lia) eq_refl)) as Q24.
  pose proof (crt_reg_w64 _ E1 _ ms2 25%bv 25 1 _ HS2 ltac:(vm_compute; reflexivity)
    ltac:(rewrite (AG 25%nat ltac:(lia)); exact U25) ltac:(lia)) as Q25.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 26%bv 26 HS2 ltac:(vm_compute; reflexivity)) (AGr 26%nat 26%bv ltac:(lia) eq_refl)) as Q26.
  pose proof (eq_trans (crt_reg_atom _ E1 _ ms2 27%bv 27 HS2 ltac:(vm_compute; reflexivity)) (AGr 27%nat 27%bv ltac:(lia) eq_refl)) as Q27.
  assert (Hsp2 : spZ (ms_regs ms2) = cx_sp0 cx - CRT_FRAME) by (unfold spZ at 1; rewrite Q2; exact Hsp).
  (* the data facts at the call site *)
  pose proof HJ0 as HJ2'.
  pose proof HPRE as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
  assert (FS0 : STK_check_round_trip = 16784) by reflexivity.
  assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms2)))
    by exact (arodata_below B W mem (ms_mem ms2) SBc HRO).
  assert (Hu2 : cstr_ok tfibsegs W (ms_mem ms2) (cx_u cx) (cx_ub cx))
    by exact (cstr_ok_below W mem (ms_mem ms2) _ _ SBc Hu).
  assert (HGL2 : fm_glob tfibsegs W (ms_mem ms2) (cx_live cx)
      (if m =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) (cx_cnt cx + m) SIZE_MAXZ)
    by exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc Hglob).
  assert (Hsuf : cstr_ok tfibsegs W (ms_mem ms2) (cx_u cx + Z.of_nat k) (skipn k (cx_ub cx)))
    by exact (cstr_ok_suffix W (ms_mem ms2) (cx_u cx) (cx_ub cx) k ltac:(lia) Hu2).
  assert (FS : STK_plain = 8224) by reflexivity.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms2 HS2 eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 A_plain) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
      with (cfg_at tfibsegs A_plain (ms_regs ms2) (ms_mem ms2) mm).
    apply (PLAIN ly S W (ms_regs ms2) (ms_mem ms2) _ [] (cx_u cx + Z.of_nat k) (skipn k (cx_ub cx))
      (cx_live cx) (if m =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) (cx_cnt cx + m) SIZE_MAXZ).
    - split; [|exact HRO2].
      apply (afn_pre_at tfibsegs B _ _ _ _ _ _ _ _ _ ly S W (ms_mem ms2) _ k0 (ms_regs ms2) STK_plain (- CRT_FRAME) [] HJ2' Hsp2).
      all: first [ reflexivity | (unfold CRT_FRAME in *; lia)
                 | (rewrite P1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold CRT_L1; lia); reflexivity)
                 | (unfold raZ; rewrite P1, unsigned_lit_small by (unfold CRT_L1; lia); unfold CRT_L1; lia)
                 | (rewrite Q3, R3; exact Hgp0) | (rewrite Q4, R4; exact Htp0)
                 | (apply achain_low; unfold s0Z; rewrite Q8, R8; unfold w64;
                    rewrite unsigned_lit_small by lia; lia) ].
    - exact HGL2.
    - exact P10.
    - exact Hsuf.
    - rewrite length_skipn. lia. }
  intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJc & HP3 & H10p & Hbl3 & HG3).
  pose proof (ajournal_sub_incl B _ _ _ _ _ _ _ _ _ ly S W (ms_mem ms2) _ k0 STK_plain (spZ (ms_regs ms2)) [] [] ly3 S3 W3 mem3 md3 0
    HJ2' HJc ltac:(rewrite Hsp2; unfold CRT_FRAME in *; lia) ltac:(rewrite Hsp2; unfold CRT_FRAME in *; lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ3.
  cbn [app] in HJ3. rewrite Z.add_0_r in HJ3.
  pose proof HJc as (HAR3 & _ & _ & _ & _ & _ & _ & _ & F1c & _).
  (* the frame window [sp0 - 112, sp0) is above the ceiling and above the callee's stack window *)
  assert (KF : forall a, cx_sp0 cx - CRT_FRAME <= a < cx_sp0 cx ->
      aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W) mem a).
  { intros a Ha. rewrite (F1c a ltac:(unfold CRT_FRAME in *; lia)
      ltac:(rewrite Hsp2; unfold CRT_FRAME in *; lia)).
    apply (aview_below (w_H W) mem (ms_mem ms2) (2 ^ 64) a SB). unfold CRT_FRAME in *; lia. }
  assert (Hinc3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3))
    by (intros x Hx; rewrite Hbl3; exact Hx).
  assert (HRO3 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W3) mem3))
    by (eapply (arodata_kept B); [exact HJc | exact nil_closed | exact nil_not_roP | exact HRO2]).
  assert (Hu3 : cstr_ok tfibsegs W3 mem3 (cx_u cx) (cx_ub cx))
    by (eapply (cstr_ok_kept B); [exact IMG | exact HJc | exact Hinc3
        | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HRO3 | exact Hku | exact Hu2]).
  assert (R'2 : getr regs3 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)).
  assert (R'3 : getr regs3 3 = getr (ms_regs ms2) 3) by exact (fmw_pres _ _ 3%bv HP3 ltac:(fmw_cs_side)).
  assert (R'4 : getr regs3 4 = getr (ms_regs ms2) 4) by exact (fmw_pres _ _ 4%bv HP3 ltac:(fmw_cs_side)).
  assert (R'8 : getr regs3 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HP3 ltac:(fmw_cs_side)).
  assert (R'9 : getr regs3 9 = getr (ms_regs ms2) 9) by exact (fmw_pres _ _ 9%bv HP3 ltac:(fmw_cs_side)).
  assert (R'18 : getr regs3 18 = getr (ms_regs ms2) 18) by exact (fmw_pres _ _ 18%bv HP3 ltac:(fmw_cs_side)).
  assert (R'19 : getr regs3 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HP3 ltac:(fmw_cs_side)).
  assert (R'20 : getr regs3 20 = getr (ms_regs ms2) 20) by exact (fmw_pres _ _ 20%bv HP3 ltac:(fmw_cs_side)).
  assert (R'21 : getr regs3 21 = getr (ms_regs ms2) 21) by exact (fmw_pres _ _ 21%bv HP3 ltac:(fmw_cs_side)).
  assert (R'22 : getr regs3 22 = getr (ms_regs ms2) 22) by exact (fmw_pres _ _ 22%bv HP3 ltac:(fmw_cs_side)).
  assert (R'23 : getr regs3 23 = getr (ms_regs ms2) 23) by exact (fmw_pres _ _ 23%bv HP3 ltac:(fmw_cs_side)).
  assert (R'24 : getr regs3 24 = getr (ms_regs ms2) 24) by exact (fmw_pres _ _ 24%bv HP3 ltac:(fmw_cs_side)).
  assert (R'25 : getr regs3 25 = getr (ms_regs ms2) 25) by exact (fmw_pres _ _ 25%bv HP3 ltac:(fmw_cs_side)).
  assert (R'26 : getr regs3 26 = getr (ms_regs ms2) 26) by exact (fmw_pres _ _ 26%bv HP3 ltac:(fmw_cs_side)).
  assert (R'27 : getr regs3 27 = getr (ms_regs ms2) 27) by exact (fmw_pres _ _ 27%bv HP3 ltac:(fmw_cs_side)).
  rewrite P1.
  change (mkCfg (mkst regs3 (Z_to_bv 64 CRT_L1) mem3 (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_L1 regs3 mem3 mm).
  apply (K1 ly3 S3 W3 regs3 mem3 md3).
  split; [split; [|split; [|split]]|].
  + (* crt_tcore *)
    split; [split; [exact HJ3|] | split; [exact Hk0 | split; [exact Hn1|]]].
    * split.
      { apply (crt_frame_kept cx W W3 mem mem3 KF HFR). }
      split; [unfold spZ at 1; rewrite R'2, Q2; exact Hsp|].
      split; [rewrite R'3, Q3; exact R3|]. split; [rewrite R'4, Q4; exact R4|].
      split; [rewrite R'8, Q8; exact R8|]. split; [rewrite R'26, Q26; exact R26|].
      split; [exact Hu3|].
      split; [exact (cstr_kept_kept B ly S ly3 S3 (cx_u cx) (cx_ub cx) Hinc3 Hku)|].
      exact HRO3.
    * split; [rewrite R'9, Q9; exact R9|]. split; [rewrite R'18, Q18; exact R18|]. split; [exact Ht|].
      split; [rewrite Hbl3; exact Hperm|].
      exact HG3.
  + (* crt_lregs at h = 1: the head moved s9 on to uri + k *)
    split; [rewrite R'19, Q19; exact R19|]. split; [rewrite R'25; exact Q25|].
    split; [rewrite R'20, Q20; exact R20|].
    split; [rewrite R'21, Q21; exact R21|]. split; [rewrite R'22, Q22; exact R22|].
    split; [rewrite R'23, Q23; exact R23|]. split; [rewrite R'24, Q24; exact R24|].
    rewrite R'27, Q27; exact R27.
  + unfold cx_n. lia.
  + split; [exact Hm | exact Hgt].
  + split; [exact Hc62 | exact H10p].
Qed.

(* ---- 0x810c4: s11 := n - 1; beqz s11 -> the exit; else the loop setup: s3 := uri + 1, s4 := 1, s5..s8 := the t1,
   t2, t3, t1x formats, s9 := uri; no store ---- *)
Lemma crt_segE : forall cx ly' S' W' regs' mem' md' k0 t,
  crt_base B cx -> crt_P7 B cx ly' S' W' regs' mem' md' k0 t ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_L B cx ly'' S'' W'' regs'' mem'' md'' k0 t 3 1 ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_L regs'' mem'' md'') (crt_post B cx)) ->
  (forall ly'' S'' W'' regs'' mem'' md'', crt_X B cx ly'' S'' W'' regs'' mem'' md'' k0 t ->
     SRr tfibsegs W'' (cfg_at tfibsegs CRT_X regs'' mem'' md'') (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_P7 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly S W regs mem md k0 t HB (HT & R19) KL KX.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & HCTX & H10e & Hu0 & Hku0 & Hlu & HG0 & HQ & Hlive & Hev & Hbb).
pose proof HT as (HC & Hk0 & Hn1 & R9 & R18 & Ht & Hperm & Hglob).
pose proof HC as (HJ0 & HFR & Hsp & R3 & R4 & R8 & R26 & Hu & Hku & HRO).
pose proof HJ0 as HJ. unfold crt_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 alloc_ceiling_val).
pose proof (crt_sp_bounds cx ly S W mem md k0 HJ0) as (Hsplo & Hsphi & Hspmod).
assert (Hsp0 : 0 <= cx_sp0 cx - CRT_FRAME /\ cx_sp0 cx <= 2 ^ 47) by (unfold CRT_FRAME in *; lia).
assert (Hspl : alloc_ceiling <= cx_sp0 cx - CRT_FRAME) by (unfold CRT_FRAME in *; lia).
unfold cx_n in Hn1, Hlu, R19.
pose proof Hu as ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & HRA & Hhv & Htl).
pose proof (fmw_resume_nr W regs [] mem CRT_P7) as HS.
set (E := Ereg regs ([] : list word)) in HS.
assert (U19 : bv_unsigned (ew E 19) = Z.of_nat (length (cx_ub cx)))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); apply crt_u64; [exact R19 | lia]).
assert (U8 : bv_unsigned (ew E 8) = cx_u cx)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); apply crt_u64; [exact R8 | lia]).
unfold cfg_at. change (w64 CRT_P7) with (Z_to_bv 64 CRT_P7).
aj_run fmw_tbl_crt_ok HS HJ0.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 19 (-1)) (b := SLit 0); [exact HS | intros Hbr HS2 | intros Hbr HS2];
  rewrite ?branch_eq_U, (U_atom_off E 19 _ (-1) ltac:(unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19) ltac:(lia) ltac:(lia)),
    (U_lit E 0 ltac:(lia)) in Hbr; clear HS.
- (* n = 1: no split point; the exit *)
  assert (Hn : Z.of_nat (length (cx_ub cx)) = 1) by (apply Z.eqb_eq in Hbr; lia).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_X.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) (2 ^ 64))
    by (match goal with H : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ => exact (frame_nil_same _ _ _ H) end).
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1 SB2) as SB.
  pose proof (fmw_reg_atom _ regs _ _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs _ _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs _ _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs _ _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs _ _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs _ _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs _ _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 CRT_X) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_X (ms_regs ms2) (ms_mem ms2) mm).
  apply (KX ly S W (ms_regs ms2) (ms_mem ms2) _).
  unfold crt_X. replace (rt_calls (cx_ub cx)) with 3 by (symmetry; apply crt_calls_one; lia).
  eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms2) (ms_mem ms2) _ k0 t 3 HT HJ0 SB); assumption.
- (* n >= 2: the loop setup, then the loop head at k = 1 *)
  assert (Hn : 2 <= Z.of_nat (length (cx_ub cx))) by (apply Z.eqb_neq in Hbr; lia).
  aj_run_to fmw_tbl_crt_ok HS2 HJ0 CRT_L.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) (2 ^ 64))
    by (match goal with H : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ => exact (frame_nil_same _ _ _ H) end).
  pose proof (same_below_trans mem (ms_mem ms1) (ms_mem ms2) (2 ^ 64) SB1 SB2) as SB.
  pose proof (fmw_reg_atom _ regs _ _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs _ _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs _ _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs _ _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs _ _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs _ _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs _ _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  pose proof (crt_reg_w64 _ E _ ms2 19%bv 8 1 _ HS2 ltac:(vm_compute; reflexivity) U8 ltac:(lia)) as Q19.
  pose proof (fmw_reg_lit _ E _ ms2 20%bv 1 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q20.
  pose proof (fmw_reg_lit _ E _ ms2 21%bv FMT_t1 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold FMT_t1; lia)) as Q21.
  pose proof (fmw_reg_lit _ E _ ms2 22%bv FMT_t2 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold FMT_t2; lia)) as Q22.
  pose proof (fmw_reg_lit _ E _ ms2 23%bv FMT_t3 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold FMT_t3; lia)) as Q23.
  pose proof (fmw_reg_lit _ E _ ms2 24%bv FMT_t1x HS2 ltac:(vm_compute; reflexivity) ltac:(unfold FMT_t1x; lia)) as Q24.
  pose proof (crt_reg_w64 _ E _ ms2 25%bv 8 0 _ HS2 ltac:(vm_compute; reflexivity) U8 ltac:(lia)) as Q25.
  pose proof (crt_reg_w64 _ E _ ms2 27%bv 19 (-1) _ HS2 ltac:(vm_compute; reflexivity) U19 ltac:(lia)) as Q27.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 CRT_L) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs CRT_L (ms_regs ms2) (ms_mem ms2) mm).
  apply (KL ly S W (ms_regs ms2) (ms_mem ms2) _).
  split; [|split; [|split]].
  + eapply (crt_tcore_same cx ly S W regs mem md (ms_regs ms2) (ms_mem ms2) _ k0 t 3 HT HJ0 SB); assumption.
  + (* s9 = uri addresses uri[1 - 1] *)
    split; [rewrite Q19; reflexivity|].
    split; [rewrite Q25; unfold w64; f_equal; cbn [Z.of_nat]; lia|].
    split; [rewrite Q20; reflexivity|]. split; [rewrite Q21; reflexivity|].
    split; [rewrite Q22; reflexivity|]. split; [rewrite Q23; reflexivity|]. split; [rewrite Q24; reflexivity|].
    rewrite Q27; unfold cx_n, w64; f_equal; cbn [Z.of_nat]; lia.
  + unfold cx_n. cbn [Z.of_nat]. lia.
  + split.
    * (* at k = 1 nothing has been counted yet besides the three fixed calls *)
      unfold crt_rest, rt_calls, rt_nk.
      destruct (cx_ub cx) as [|c0 ub0] eqn:Eub; [try rewrite Eub in Hn; cbn [length Z.of_nat] in Hn; lia|].
      cbn [length]. replace (Datatypes.S (length ub0) - 1 + 1)%nat with (Datatypes.S (length ub0)) by lia. lia.
    * reflexivity.
Qed.
End E.
