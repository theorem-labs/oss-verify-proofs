(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of xstrdup on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v), the malloc call through amalloc04_sub and the memcpy call through
   aj_intrin_atS (PaCall.v), and the strlen call through aj_art_at (PaArt.v). *)
(* The walk proves txstrdup_spec (xstrdup_c.v) from the statement's own hypotheses (AMALLOC4, AMEMCPY, ASTRLEN) and
   these: TL (the malloc trampoline is the malloc rule's entry, CmdPaLib.v pal_malloc); and HB, IMG (the allocator
   record of the image's symbols and the image facts), from which CmdRecFacts.v gives
   what the read-only branch of the source premise (astr_argA, CmdRep.v: the record's checks cmd_addr_b and
   cmd_hull_b) needs: the read-only bytes are image bytes (cmd_ro_prog_apart) and the shadow of the range
   (cmd_aread_ok_chk). The runtime contracts' read-only words at the strlen call (rt_rom_view) come from the
   statement's arodata_okP; the strlen tail is the statement's atail_vis premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdChk CmdBase CmdRep PaArt xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the symbolic state at the entry: every register its own atom, the 32-byte frame below sp writable, sp 16-aligned *)
Definition xs_ss0 : sstate := mkSS AF_xstrdup sr_atoms [stack_region 32] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* the symbolic state xs_ss0 holds of the entry configuration *)
Lemma xs_seed : forall W regs mem ly S md ch, afn_pre SEGS B XSTRDUP_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) xs_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_xstrdup)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HXS : XSTRDUP_STK = 16416) by reflexivity.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs) by (rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold xs_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. lia.
Qed.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's runtime entries (xstrdup_c.v), at every FP state (pass 4b); the walk keeps the FP state, so it uses
   each at the entry's fx *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
(* the malloc trampoline the listing calls is the malloc rule's entry (pal_malloc) *)
Hypothesis TL : PALib B.
(* the per-binary record (CmdRecFacts.v): the allocator record of the image's symbols (HB) and the image facts (IMG).
   Every read-only byte is an image byte (cmd_ro_prog_apart); the record's checks give the shadow of a range at every
   AR state (cmd_aread_ok_chk) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a :=
  fun a H => proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG a H).
Let cmd_aread_ok_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  cmd_addr_b a n = true -> cmd_hull_b a n = true ->
  range_addressable (rdW W mem) SHADOW_OFF a n /\ shadow_hull_vis (rdW W mem) a n :=
  cmd_aread_ok_chk SEGS B LAWS HB.
(* where the source string lies at the entry (the three branches of the statement's source premise), and the address
   range that gives *)
Definition xsrc (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (s n : Z) : Prop :=
(exists b m, In (b, m) (ablocks B ly S) /\ b <= s /\ s + n <= b + m) \/
((forall i, 0 <= i < n -> in_roP SEGS RLO RHI (s + i) /\ ~ Exists (in_zr (s + i)) (as_owned_static B) /\
    ~ (as_errno B <= s + i < as_errno B + 4)) /\ cmd_addr_b s n = true /\ cmd_hull_b s n = true) \/
afobj SEGS B ly S W mem s n.
Definition xzone (ly : alayout) (S : astate) (s n : Z) : Prop :=
(exists b m, In (b, m) (ablocks B ly S) /\ b <= s /\ s + n <= b + req_size m) \/
(0x10000 <= s /\ s + n <= 0x606000) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= s /\ s + n <= frame_addr ly cid pos + fs_frame_bytes cid).
Lemma not_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hr & _). destruct Hr. Qed.
(* from the entry to any later state of the walk (its journal, footprint []), the source bytes are kept and the source
   range is readable as the strlen and memcpy contracts ask *)
Lemma xsrc_at : forall ly S W mem md s n STK sp0 ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> xsrc ly S W mem s n -> 0 < n ->
ajournal SEGS B STK sp0 [] ly S W mem md [] ly' S' W' mem' md' k ->
(forall a, s <= a < s + n -> rdW W' mem' a = rdW W mem a) /\ xzone ly S s n /\
4096 <= s /\ s + n <= alloc_ceiling /\ amem_range s n /\
range_addressable (rdW W' mem') SHADOW_OFF s n /\ shadow_hull_vis (rdW W' mem') s n.
Proof.
intros ly S W mem md s n STK sp0 ly' S' W' mem' md' k HAR HX Hn HJ.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & F3 & F4 & Hgone & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HX as [(b & m & Hin & Hb1 & Hb2) | [(Hro & Hab & Hhb) | ((cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2) & Hs8 & Hra)]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hq1 Hq2].
  assert (Hin' : In (b, m) (ablocks B ly' S')).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly' S')) as [H|H]; [exact H|].
    exfalso. destruct (Hgone b m 0 Hin H ltac:(lia)) as (r & Hr & _). destruct Hr. }
  split.
  { intros a Ha. replace a with (b + (a - b)) by lia. apply (F2 b m (a - b) Hin Hin'); [lia|]. intros (r & Hr & _). destruct Hr. }
  split; [left; exists b, m; split; [exact Hin | lia]|].
  split; [lia|]. split; [lia|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md b m); [exact HAR | exact Hin | lia | lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly' S' W' mem' md' b m); [exact HAR' | exact Hin' | lia | lia]|].
  apply (shadow_hull_vis_of_block SEGS B LAWS ly' S' W' mem' md' b m); [exact HAR' | exact Hin' | lia | lia | lia].
- assert (Hro' : forall i, 0 <= i < n -> in_roP SEGS RLO RHI (s + i)) by (intros i Hi; exact (proj1 (Hro i Hi))).
  assert (Himg : forall i, 0 <= i < n -> 0x10000 <= s + i < 0x606000) by (intros i Hi; exact (pa_img_range _ (cif_ro_img _ (Hro' i Hi)))).
  pose proof (Himg 0 ltac:(lia)) as H0. pose proof (Himg (n - 1) ltac:(lia)) as H1.
  split.
  { intros a Ha. destruct (Hro (a - s) ltac:(lia)) as (Hra' & Ho & He). replace (s + (a - s)) with a in Hra', Ho, He by lia.
    apply F3; [exact (cif_ro_img a Hra') | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil (not_inFP_nil a))]. }
  split; [right; left; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
  exact (cmd_aread_ok_chk ly' S' W' mem' md' s n HAR' Hab Hhb).
- assert (Hfin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hfin).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly' HAR Hly) as (_ & Efa & _).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  split.
  { intros a Ha. apply (F4 cid pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros (r & Hr & _); destruct Hr]. }
  split; [right; right; exists cid, pos; split; [exact Hfin | lia]|]. split; [lia|]. split; [lia|].
  split; [apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Hfapp | lia | lia | lia | lia]|].
  split.
  { eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hfin | exact Hcid | exact Hf1 | exact Hf2 | exact Hfal | | exact HAR | exact Hra].
    intros x0 (r & Hr & _). destruct Hr. }
  apply (shadow_hull_vis_of_frame SEGS B LAWS ly' S' W' mem' md' cid pos s n HAR' Hfin'); rewrite ?Efa; lia.
Qed.
Lemma astr_atR_ext : forall (rd rd' : reader) p x, (forall a, p <= a < p + (Z.of_nat (length x) + 1) -> rd' a = rd a) ->
astr_atR rd p x -> astr_atR rd' p x.
Proof.
intros rd rd' p x Hk [Hb Hz]. split; [|exact Hz]. intros i Hi. rewrite Hk; [apply Hb; exact Hi|]. rewrite length_app in Hi; cbn in Hi; lia.
Qed.
Lemma astr_atR_some : forall (rd : reader) p x a, astr_atR rd p x -> p <= a < p + (Z.of_nat (length x) + 1) -> rd a <> None.
Proof.
intros rd p x a [Hb _] Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite Hb; [discriminate|]. rewrite length_app; cbn; lia.
Qed.
Lemma xs_seqz_add : forall a, 1 <= a < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 1)) = Z_to_bv 64 a.
Proof.
intros a Ha. apply bv_eq. rewrite alu64_unsigned. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma astr_atR_move : forall (rd rd' : reader) s p x,
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (s + i)) -> astr_atR rd s x -> astr_atR rd' p x.
Proof.
intros rd rd' s p x Hm [Hb Hz]. split; [|exact Hz]. intros i Hi. rewrite Hm; [apply Hb; exact Hi|]. rewrite length_app in Hi; cbn in Hi; lia.
Qed.
Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI). Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* the walk: the prologue, strlen, malloc, the null check (not taken: the block is at or above 4096), memcpy, the
   epilogue and ret *)
Theorem txstrdup_spec_holds : txstrdup_spec B MT.
Proof.
unfold txstrdup_spec. intros ly S W regs mem md ch s x HPRE HROD H10 HSRC HTAIL Hev Hlive MOK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HXS : XSTRDUP_STK = 16416) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (n := Z.of_nat (length x) + 1) in *.
assert (HX : astr_atR (rdW W mem) s x /\ n <= LMAX + 1 /\ xsrc ly S W mem s n).
{ unfold astr_argA in HSRC. cbv zeta in HSRC. fold n in HSRC.
  destruct HSRC as [(Hs0 & Hstr & Hn & [(HinB & _) | HRO]) | (Hstr & Hn & HF)].
  - split; [exact Hstr|]. split; [exact Hn|]. left. destruct HinB as (b & m & Hb & H1 & H2). exists b, m. auto.
  - split; [exact Hstr|]. split; [exact Hn|]. right; left. destruct HRO as (Hro & Hab & Hhb & _). exact (conj Hro (conj Hab Hhb)).
  - split; [exact Hstr|]. split; [exact Hn|]. right; right; exact HF. }
clear HSRC. destruct HX as (Hstr & Hn & HX).
assert (Hn0 : 0 < n) by lia.
pose proof (xs_seed W regs mem ly S md ch HPRE) as HS.
pose proof (ajournal_init SEGS B XSTRDUP_STK [] ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs [])) in HS. assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n0 r Hn1; subst E; apply ew_Eimg_Ereg_nat; exact Hn1).
unfold cfg_at. change (w64 (BASE + AF_xstrdup)) with (Z_to_bv 64 (BASE + AF_xstrdup)).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
destruct (xsrc_at ly S W mem md s n XSTRDUP_STK (spZ regs) ly S W (ms_mem ms) _ 0 HAR HX Hn0 HJ)
  as (Hkeep1 & Hzone & Hs4096 & Hsceil & Hamr & Hra1 & Hhull1).
assert (Hstr1 : astr_atR (rdW W (ms_mem ms)) s x) by (apply (astr_atR_ext (rdW W mem)); [exact Hkeep1 | exact Hstr]).
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - XSTRDUP_STK) (spZ regs))
by (intros a Ha Hna; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - XSTRDUP_STK <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite Usp in Hrr; rewrite HXS; lia|]);
    destruct Hin
  | exact Ha | exact Hna ]) end.
(* read-only words at the call: arodata_okP at the entry, kept by the prologue (it writes only its frame) *)
assert (HROM1 : rt_rom_view SEGS B W (ms_mem ms)).
{ intros a (sg & Hsg & Hw & Hr) Ho He.
  pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia.
  rewrite (KEEP1 a) by (rewrite ?HXS; lia).
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He). }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (R4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
    W (ms_regs ms) (ms_mem ms) XSTRDUP_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-32)
    (Z_to_bv 64 (BASE + 13372)) _ HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HXS; lia) R1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W (ms_regs ms) (ms_mem ms) _ s x).
  - exact (ecall_pre_stk_at SEGS B ESTACK XSTRDUP_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) (-32) HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HXS; lia) HraT R3' R4').
  - rewrite R10, (EE 10%nat 10%bv eq_refl). exact H10.
  - lia.
  - apply astr_atR_view. exact Hstr1.
  - unfold astr_len. fold n. split; [lia|]. split; [lia|]. split; [unfold LMAX in Hn; lia|].
    split; [|split; [exact Hamr | split; [exact Hra1 | intros _; exact Hhull1]]].
    intros a Ha. split; [exact (astr_atR_some _ s x a Hstr1 Ha)|]. unfold ascratch_stk. rewrite Hsp1. lia.
  - intros a Ha. apply (aview_keeps_vis SEGS (w_H W) mem (ms_mem ms) a HG). apply HTAIL. exact Ha.
  - exact HROM1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | rewrite Hes; lia | tauto].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite HXS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 32)%nat -> ew E2 n = ew E n) by (intros n0 Hn1; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn1).
assert (E36 : ew E2 36 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
clear HE2.
paj_run_shc RUNP RUNC HS HJ2.
{ awr_ok_tac. exact Usp2. }
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
assert (Hlen : astr_len x = Z.of_nat (length x)) by reflexivity.
assert (Q10' : getr (ms_regs ms0) 10 = w64 n).
{ rewrite Q10, E36, Ha02. unfold w64. rewrite unsigned_lit_small by (unfold astr_len, LMAX in *; lia).
  rewrite Hlen. fold n. apply xs_seqz_add. unfold LMAX in Hn; lia. }
assert (Hsp2 : spZ (ms_regs ms0) = spZ regs + -32).
{ unfold spZ at 1. rewrite Q2, Usp2. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hs0 : s0Z (ms_regs ms0) = s).
{ unfold s0Z. rewrite Q8, OLD2, (EE 10%nat 10%bv eq_refl), H10 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
ppcs.
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) _ (ms_regs ms0) (ms_mem ms0) XSTRDUP_STK (spZ regs) [] ly S W mem md []
    ly S _ 0 n (-32) (Z_to_bv 64 (BASE + 13388)) [] HJ2).
  - exact Q10'.
  - unfold MALLOC_MAX, LMAX in *. lia.
  - unfold LIVE_XSTRDUP in Hlive. exact Hlive.
  - exact Hsp2.
  - reflexivity.
  - lia.
  - rewrite Has, HXS. lia.
  - rewrite Q3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Q4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_XSTRDUP in Hev. lia.
  - apply (achain_chain_pre ly _ (spZ (ms_regs ms0)) s [] (ms_regs ms0)).
    + left. split; [left; lia | reflexivity].
    + lia.
    + exact Hs0.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - unfold XM_XSTRDUP in MOK. exact MOK. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres4096 & Eab3 & HK3 & MLE3 & HJt3).
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJt3 | exact HJ3 | exact Usp2 | lia | rewrite HXS; lia | lia | cbn; lia | cbn; lia | intros a _; apply not_inFP_nil]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E2 n) by (intros n0 Hn1; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn1).
assert (E52 : ew E3 52 = getr regs3 10) by (rewrite HE3; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
clear HE3.
assert (Hres_in : In (res, n) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res n (proj1 HJ3) Hres_in) as (_ & _ & Hrceil & _ & _ & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [Hq1 Hq2].
psrr_branch_pi RUNP BR HS.
{ exfalso. assert (U52 : U E3 (SOff 52 0) = res) by (apply U_atom; [rewrite E52; exact Ha03 | lia]).
  rewrite branch_eq_U, U_SLit, U52 in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
paj_run_shc RUNP RUNC HS HJ3.
{ awr_ok_tac. exact Usp3. }
pmkst HS.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (1%bv : bv 5) P1.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
assert (HAR3 : AR SEGS B ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3)) by exact (proj1 HJ3).
assert (Ra0 : getr (ms_regs ms1) 10 = w64 res) by (rewrite P10, E52; exact Ha03).
assert (Ra1 : getr (ms_regs ms1) 11 = w64 s) by (rewrite P11, OLD3, OLD2, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
assert (Ra2 : getr (ms_regs ms1) 12 = w64 n).
{ rewrite P12, OLD3, E36, Ha02 by lia. unfold w64. rewrite unsigned_lit_small by (unfold astr_len, LMAX in *; lia). rewrite Hlen. reflexivity. }
assert (Hsp3 : spZ (ms_regs ms1) = spZ regs + -32).
{ unfold spZ at 1. rewrite P2, Usp3. rewrite unsigned_lit_small by lia. reflexivity. }
destruct (xsrc_at ly S W mem md s n XSTRDUP_STK (spZ regs) ly3 S3 W3 (ms_mem ms1) _ _ HAR HX Hn0 HJ3)
  as (Hkeep3 & _ & _ & _ & Hamr3 & Hra3 & Hhull3).
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & Hfrs3' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR Hly3) as (_ & Efa3 & _).
assert (Hdisj : res + n <= s \/ s + n <= res).
{ destruct Hzone as [(b & m & Hbm & Hb1 & Hb2) | [Himg | (cid & pos & Hfin & Hf1 & Hf2)]].
  - apply in_split in Hbm as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ (b, m) (res, n) l1 l2 [] HAR3) as Hd.
    rewrite Eab3, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
  - pose proof (blk_off_imgP B ly3 S3 W3 _ _ res n HAR3 Hres_in) as Hoff. unfold off_img in Hoff. lia.
  - assert (Hfin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact Hfin).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ res n cid pos HAR3 Hres_in Hfin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa3 in Hd. lia. }
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) _ (ms_regs ms1) (ms_mem ms1) XSTRDUP_STK (spZ regs) [] ly S W mem md []
    ly3 S3 _ _ res s n (-32) (Z_to_bv 64 (BASE + 13408)) HJ3).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - unfold LMAX in Hn. lia.
  - lia.
  - lia.
  - exact Hsp3.
  - reflexivity.
  - lia.
  - rewrite Hes, HXS. lia.
  - rewrite P3, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite P4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (res + (a - res)) by lia.
    eapply (awr_new_block_any SEGS B LAWS); [exact HJ2 | exact HAR3 | exact Eab3 | lia | exact Hres_in | lia].
  - intros a _ Hf; exfalso; exact (not_inFP_nil a Hf).
  - eapply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ res n); [exact HAR3 | exact Hres_in | lia | lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ res n); [exact HAR3 | exact Hres_in | lia | lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) _ res n); [exact HAR3 | exact Hres_in | lia | lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [rewrite Hkeep3 by lia; exact (astr_atR_some _ s x a Hstr Ha) | rewrite Hsp3; lia]. }
    split; [exact Hdisj|]. split; [exact Hamr3|]. split; [exact Hra3 | intros _; exact Hhull3]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_aview (segs := SEGS) E3 (w_H W3) (ms_mem ms1) mem4 2 (spZ regs)); [exact Usp3 | | exact Hpres4].
  intros a Ha. apply Hfr4; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 64 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 64)%nat -> ew E4 n = ew E3 n) by (intros n0 Hn1; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn1).
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
clear HE4.
paj_run_shc RUNP RUNC HS HJ4.
{ awr_ok_tac. exact Usp4. }
prreg HS (10%bv : bv 5) F10. prreg HS (1%bv : bv 5) F1.
lazymatch goal with Hfr5 : frame_of E4 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) Hfr5
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4 in Hrr; lia|]); destruct Hin)) as UN5 end.
destruct (xsrc_at ly S W mem md s n XSTRDUP_STK (spZ regs) ly3 S3 W3 _ _ _ HAR HX Hn0 HJ4) as (Hkeep5 & _).
cbv beta iota in Heff.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
split.
{ rewrite F1, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ4 | unfold EV_XSTRDUP; lia]. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H W3) E4 _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite OLD4, OLD3, OLD2 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EE; reflexivity. }
exists res.
split; [rewrite F10, OLD4, E52 by lia; exact Ha03|].
split; [lia|].
split; [unfold LIVE_XSTRDUP; fold n; rewrite Eab3; apply Permutation_sym, Permutation_cons_append|].
split.
{ apply Forall_forall. intros [b m] Hbm. cbn [fst snd].
  assert (Hbm3 : In (b, m) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 Hbm3) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2].
  apply in_split in Hbm as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 _ _ (b, m) (res, n) l1 l2 [] HAR3) as Hd.
  rewrite Eab3, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  unfold iv_apart, LIVE_XSTRDUP. fold n. lia. }
split; [exists res, n; split; [exact Hres_in | unfold LIVE_XSTRDUP; fold n; lia]|].
split.
{ apply (astr_atR_move (rdW W mem) _ s); [|exact Hstr]. intros i Hi.
  rewrite UN5 by lia. rewrite (Heff i Hi). apply Hkeep3. lia. }
split; [apply (astr_atR_ext (rdW W mem)); [exact Hkeep5 | exact Hstr]|].
split.
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, YCbq.bsum_app, <- (blocks_bytes_bsum B ly S).
  unfold LIVE_XSTRDUP. fold n. cbn [YCbq.bsum fold_right snd]. lia. }
unfold XM_XSTRDUP. fold n. exact MLE3.
Qed.
End e.
End d.
End b.
