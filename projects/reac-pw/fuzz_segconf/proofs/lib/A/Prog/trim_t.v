(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 235 of its 270 lines of code are new or changed and 219 lines of the source are left out. *)
(* trim's image-A walk, the store and the return (0x89190 .. 0x891bc) and the trailing-blank loop (0x89148), the cut
   statements of lib/A/Prog/trim_k.v: tr_fin_ok : TR_FIN_stmt, tr_trail_ok : TR_FIN_stmt -> TR_TRAIL_stmt. Each
   segment re-seeds a symbolic state from tr_mid / tr_regs (fuzz_command's answer_l.v al_entry form) and runs the
   token executor (lib/A/Prog/SegPaLib.v paj_run_tok), which decides the inline checks:
     check 3 (0x89190-0x891c4, store1 at e): covered by the shadow entry of e, so its slow arm passes;
     check 2 (0x89148-0x89184, load1 at e - 1): the obligation that e - 1 is addressable, from trim_pre's sa_addr. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA trim_c trim_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma bvu64 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.
Lemma m16_sub32 : forall x, x mod 16 = 0 -> (x - 32) mod 16 = 0.
Proof. intros x H. replace (x - 32) with (x + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact H. Qed.
(* the bytes of the post's sa_bytes list: the kept prefix, then the NUL *)
Lemma sa_bytes_nth_lt : forall (l : list Z) i, (i < length l)%nat ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = Z_to_bv 8 (nth i l 0).
Proof.
intros l i Hi. unfold seg_spec.zb. rewrite app_nth1 by (rewrite length_map; exact Hi).
change ZB0 with (Z_to_bv 8 0). apply map_nth.
Qed.
Lemma sa_bytes_nth_end : forall (l : list Z) i, length l = i ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = seg_spec.ZERO.
Proof.
intros l i Hi. unfold seg_spec.zb. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, Hi, Nat.sub_diag. reflexivity.
Qed.
Lemma sa_bytes_len : forall (l : list Z), length (seg_spec.zb l ++ [seg_spec.ZERO]) = S (length l).
Proof. intros l. unfold seg_spec.zb. rewrite length_app, length_map. cbn [length]. lia. Qed.

(* ---- FIN, 0x89190: the regions are the prologue's four slots (s2, s1, s0, ra at sp, sp + 8, sp + 16, sp + 24; the
   entry's values as the extra atoms 32..35) and the NUL byte at e = a1 (written); the one shadow entry covers e ---- *)
Definition tf_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
     YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some 11%nat) 0 1 0 1 [] ].
Definition tf_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (18%nat, mkAF SB SB 0) ] [] [].
Definition tf_ss : sstate := mkSS TR_FIN sr_atoms tf_regions None tf_facts.
Definition tr_Bx : sv := SOff 18 0.
Definition tf_SH : list shent := [mkSHE 11 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition tf_E (regs regs1 : bvmap 5 word) : env :=
Eimg (Ereg regs1 [getr regs 18; getr regs 9; getr regs 8; getr regs 1]).

Lemma tf_entry : forall (W : world SEGS) (regs regs1 : bvmap 5 word) memc e,
getr regs1 2 = w64 (spZ regs - 32) -> getr regs1 11 = w64 e -> getr regs1 18 = w64 SB ->
2 ^ 46 <= spZ regs - 32 -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
4096 <= e <= 2 ^ 47 - 1 -> (e + 1 <= spZ regs - 32 \/ spZ regs <= e) ->
rdword (rdW W memc) (spZ regs - 8) = Some (bv_unsigned (getr regs 1)) ->
rdword (rdW W memc) (spZ regs - 16) = Some (bv_unsigned (getr regs 8)) ->
rdword (rdW W memc) (spZ regs - 24) = Some (bv_unsigned (getr regs 9)) ->
rdword (rdW W memc) (spZ regs - 32) = Some (bv_unsigned (getr regs 18)) ->
apresent (w_H W) memc e ->
st_ok_pi SEGS VAL (tf_E regs regs1) tf_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + TR_FIN)) memc (seg_rom SEGS))).
Proof.
intros W regs regs1 memc e H2 H11 H18 Hs1 Hs2 Hs16 He Hout K8 K16 K24 K32 Hpe.
set (E := tf_E regs regs1).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 32)) by (subst E; unfold tf_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl); exact H2).
assert (E11 : ew E 11 = Z_to_bv 64 e) by (subst E; unfold tf_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 11 11%bv eq_refl); exact H11).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; unfold tf_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact H18).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j [getr regs 18; getr regs 9; getr regs 8; getr regs 1] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold tf_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
pose proof (m16_sub32 _ Hs16) as Hm32.
rewrite restrict_mkst_fx. unfold tf_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold tf_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 0 8 (SOff 32 0) (bv_unsigned (getr regs 18)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bvu64 | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ K32).
    * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 8 8 (SOff 33 0) (bv_unsigned (getr regs 9)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bvu64 | lia |].
      replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ K24).
    * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 16 8 (SOff 34 0) (bv_unsigned (getr regs 8)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bvu64 | lia |].
      replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ K16).
    * apply (chunk_ok_val SEGS E _ (spZ regs - 32) 24 8 (SOff 35 0) (bv_unsigned (getr regs 1)));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bvu64 | lia |].
      replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ K8).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E11, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hpe.
- unfold tf_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E2, E11, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I].
  cbn [tf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E11, E18, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hm32. unfold SB. repeat split; lia.
Qed.

(* the byte a run wrote into a one-byte written region (fuzz_command's answer_l.v al_wbyte, any base atom) *)
Lemma tr_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
bv_unsigned (ew E n) = Pz ->
aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the NUL's address is one trim may write: the footprint byte, in the caller's side-stack frame, a live block, or
   the caller's real stack above sp *)
Lemma tr_awr_e : forall ly S W regs mem md ch p s,
tr_cx B ly S W regs mem md ch p s ->
awr_byte SEGS B STK_trim (spZ regs) (tr_FP p s) (ablocks B ly S) (ablocks B ly S) (frames S) ly [] (trim_end_addr p s).
Proof.
intros ly S W regs mem md ch p s HCX.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
destruct HSTR as ((HZS & NZ) & HTAIL).
pose proof (tr_e_range s NZ) as HER.
assert (HE : trim_end_addr p s = p + Z.of_nat (seg_spec.trim_lead s + length (SegModel.r_trim s))) by reflexivity.
assert (HFP : inFP (tr_FP p s) (trim_end_addr p s)) by (exists (trim_end_addr p s, trim_end_addr p s + 1); split; [left; reflexivity | cbn [fst snd]; lia]).
destruct HZONE as [([(cid & pos & Hin & Hcid & Hf1 & Hf2) | (b & m & Hin & Hb1 & Hb2)] & Hc) | (Hsp & Htop & _)].
- right; right; right; right. right; right. split; [exact HFP|].
  exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- right; left. split; [exact HFP|]. exists b, m. split; [exact Hin|].
  pose proof HCX as ((HAR & _) & _).
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrk]. lia.
- right; right; right; right. right; left. split; [exact HFP|]. lia.
Qed.

Lemma tr_fin_ok : TR_FIN_stmt B.
Proof.
unfold TR_FIN_stmt.
intros ly S W regs mem md ch p s regs1 memc mdc HCX HMID HRG H8 H11.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof (tr_awr_e ly S W regs mem md ch p s HCX) as HAWR.
pose proof HCX as (HPRE & HROD & H10 & Hp64 & _ & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HMID as (HJ & KEEP & KPR & K8 & K16 & K24 & K32).
destruct HRG as (R2 & R18 & RK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
destruct HSTR as ((HZS & NZ) & HTAIL).
pose proof (tr_e_range s NZ) as HER.
assert (HE : trim_end_addr p s = p + Z.of_nat (seg_spec.trim_lead s + length (SegModel.r_trim s))) by reflexivity.
set (k := (seg_spec.trim_lead s + length (SegModel.r_trim s))%nat) in *.
set (e := trim_end_addr p s) in *.
assert (He47 : 4096 <= e <= 2 ^ 47 - 1) by lia.
assert (Heout : e + 1 <= spZ regs - 32 \/ spZ regs <= e) by lia.
assert (Hpe : apresent (w_H W) memc e).
{ replace e with (p + (e - p)) by lia. destruct (HPR (e - p) ltac:(lia)) as [H1 H2]. exact (KPR (p + (e - p)) ltac:(lia) H1 H2). }
assert (HRAe : range_addressable (rdW W memc) SHADOW_OFF e 1).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W memc) (spZ regs - STK_trim) (spZ regs)); [exact KEEP | lia | lia | lia |].
  destruct HADDR as (_ & _ & _ & HRA & _). apply (range_addressable_sub _ _ p (Z.of_nat (length s) + 1)); [exact HRA | lia | lia]. }
pose proof (tf_entry W regs regs1 memc e R2 H11 R18 ltac:(lia) Hsp47 Hal16 He47 Heout K8 K16 K24 K32 Hpe) as HS.
assert (HEI : img_env VAL A_LIM (tf_E regs regs1)) by (unfold tf_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (tf_E regs regs1) n = getr regs1 r)
  by (intros n r Hn; unfold tf_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew (tf_E regs regs1) (32 + j) = nth j [getr regs 18; getr regs 9; getr regs 8; getr regs 1] (Z_to_bv 64 0))
  by (intros j Hj; unfold tf_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
revert HS HEI EE E32 E33 E34 E35. generalize (tf_E regs regs1) as E0. intros E0 HS HEI EE E32 E33 E34 E35.
assert (U11 : bv_unsigned (ew E0 11) = e) by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (UB : U E0 tr_Bx = SHADOW_OFF).
{ unfold tr_Bx. rewrite (U_atom E0 18 SB); [reflexivity | rewrite (EE 18%nat 18%bv eq_refl); exact R18 | unfold SB; lia]. }
assert (UE : U E0 (SOff 11 0) = e) by (apply U_atom; [rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia]).
assert (SHOK : sh_ok SEGS tr_Bx tf_SH E0 (mrestrict (w_H W) memc)).
{ unfold sh_ok, tf_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H W) memc E0 tr_Bx 11%nat e 1 e 0 1 HRAe UB UE); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  replace x with (p + (e - p)) by lia. apply HSB. lia. }
unfold tr_at, tr_post.
(* 0x89190 .. 0x891bc: check 3, the store, the epilogue, up to the ret *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 11%nat) (b := e); [reflexivity | exact U11 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. assert (a = e) as -> by lia. exact HAWR. }
(* the bytes the run kept: all but e *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> e -> rdW W (ms_mem ms) a = rdW W memc a).
{ intros a Ha Hne. apply (kept_of_frame (segs := SEGS) E0 _ (w_H W) memc (ms_mem ms) (fun a' => a' = e) HFr); [|exact Ha | exact Hne].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; [lia | rewrite U11 in Hrr; lia]. }
assert (HW0 : rdW W (ms_mem ms) e = Some 0).
{ pose proof (tr_wbyte _ _ _ _ 11%nat 1%nat e (SLit 0) HS ltac:(vm_compute; reflexivity)) as V.
  rewrite V; [reflexivity|]. lazymatch goal with HA : env_agree _ _ _ |- _ => idtac | _ => idtac end.
  cbn [extK]. exact U11. }
prreg HS (1%bv : bv 5) R1.
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold apost_base.
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists ly, S, rg, mm, mdx end.
split; [rewrite R1, E35; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split.
{ assert (RK' : forall r : bv 5, In r TR_KEPT -> ew E0 (Z.to_nat (bv_unsigned r)) = getr regs r).
  { intros r Hr. rewrite (EE _ r) by (pose proof (bv_unsigned_in_range 5 r); lia). exact (RK r Hr). }
  apply aregs_preserved_eqs.
  - prreg HS (2%bv : bv 5) Rq. rewrite Rq, (EE 2%nat 2%bv eq_refl), R2. unfold w64.
    rewrite unsigned_lit_small by lia. replace (spZ regs - 32 + 32) with (spZ regs) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - prreg HS (3%bv : bv 5) Rq. rewrite Rq. exact (RK' 3%bv ltac:(cbn; tauto)).
  - prreg HS (4%bv : bv 5) Rq. rewrite Rq. exact (RK' 4%bv ltac:(cbn; tauto)).
  - prreg HS (8%bv : bv 5) Rq. rewrite Rq. exact E34.
  - prreg HS (9%bv : bv 5) Rq. rewrite Rq. exact E33.
  - prreg HS (18%bv : bv 5) Rq. rewrite Rq. exact E32.
  - prreg HS (19%bv : bv 5) Rq. rewrite Rq. exact (RK' 19%bv ltac:(cbn; tauto)).
  - prreg HS (20%bv : bv 5) Rq. rewrite Rq. exact (RK' 20%bv ltac:(cbn; tauto)).
  - prreg HS (21%bv : bv 5) Rq. rewrite Rq. exact (RK' 21%bv ltac:(cbn; tauto)).
  - prreg HS (22%bv : bv 5) Rq. rewrite Rq. exact (RK' 22%bv ltac:(cbn; tauto)).
  - prreg HS (23%bv : bv 5) Rq. rewrite Rq. exact (RK' 23%bv ltac:(cbn; tauto)).
  - prreg HS (24%bv : bv 5) Rq. rewrite Rq. exact (RK' 24%bv ltac:(cbn; tauto)).
  - prreg HS (25%bv : bv 5) Rq. rewrite Rq. exact (RK' 25%bv ltac:(cbn; tauto)).
  - prreg HS (26%bv : bv 5) Rq. rewrite Rq. exact (RK' 26%bv ltac:(cbn; tauto)).
  - prreg HS (27%bv : bv 5) Rq. rewrite Rq. exact (RK' 27%bv ltac:(cbn; tauto)). }
unfold tr_Q. change (seg_spec.trim_lead s + length (SegModel.r_trim s))%nat with k.
change (trim_end_addr p s) with e. split; [|split; [|split]].
- prreg HS (10%bv : bv 5) R10. rewrite R10, (EE 8%nat 8%bv eq_refl), H8. reflexivity.
- intros i Hi. rewrite sa_bytes_len, length_firstn in Hi.
  replace (Nat.min k (length s)) with k in Hi by lia.
  destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
  + rewrite (sa_bytes_nth_lt (firstn k s) i) by (rewrite length_firstn; lia).
    rewrite nth_firstn.
    destruct (Nat.ltb_spec i k) as [_|]; [|lia].
    rewrite KM by lia. rewrite KEEP by lia.
    pose proof (sa_zs_nth _ p s i HZS ltac:(lia)) as Vi. rewrite Vi.
    destruct (aview_byte SEGS (w_H W) mem (p + Z.of_nat i) _ Vi) as (_ & _ & _ & Hr).
    rewrite bv8_small by exact Hr. reflexivity.
  + assert (i = k) as -> by lia.
    rewrite (sa_bytes_nth_end (firstn k s) k) by (rewrite length_firstn; lia).
    replace (p + Z.of_nat k) with e by lia. rewrite HW0. reflexivity.
- intros a Ha Hw He'. rewrite KM by lia. apply KEEP; [exact Ha | exact Hw].
- split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

End e.
End f.
End d.
