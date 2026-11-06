(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s1.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses, and the UBSan checks of `g_rec.reply[g_rec.reply_size - 1]` (0x86fcc-0x86fe0): the pointer-overflow branch (bltu) split and its taken arm refuted by the reply block's bounds; `snez` and `seqz` fold to 1 and 0 from the atoms' ranges, so the null checks fall through. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan-ubsan, 0x86e64), from the
   entry to the memchr call 0x86ffc (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/B/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at origin/ossv/recipes
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ffc; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh
  CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_k check_reply_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* two 8-byte little-endian reads of the same bytes give the same value mod 2^64 *)
Lemma aval_mem8_eq : forall (rd : reader) a v1 v2,
aval_mem rd a 8 v1 -> aval_mem rd a 8 v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
intros rd a v1 v2 H1 H2.
assert (E : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
{ intros k Hk. specialize (H1 k Hk). specialize (H2 k Hk). rewrite H1 in H2. injection H2 as H2. exact H2. }
assert (M : forall v k, le_byte (v mod 2 ^ 64) 8 k = le_byte v 8 k).
{ intros v k. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
rewrite <- (le_bytes8 (v1 mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite <- (le_bytes8 (v2 mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite !M. rewrite !E by lia. reflexivity.
Qed.
Lemma s1_unowned_range : forall lo hi a (l : list (Z * Z)),
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) l = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi a l H Ha HE. apply Exists_exists in HE as (r & Hin & Hr). rewrite forallb_forall in H.
specialize (H r Hin). unfold in_zr in Hr. apply orb_true_iff in H as [H | H]; apply Z.leb_le in H; lia.
Qed.
Lemma s1_ro_a6bc8 : forall (ro : Z -> Prop), cmd_ro_in ro -> forall i, 0 <= i < 8 -> ro (0xa6bc8 + i).
Proof. intros ro H. unfold cmd_ro_in in H. repeat (first [exact (proj1 H) | apply proj2 in H]). Qed.
Lemma s1_val_mem_of_aval : forall segs H (mem : word -> option byte) a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
try unfold YG0f.le_byte in *; try unfold YO0f.le_byte in *. rewrite <- Hv.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma s1_aval_mem_ext : forall (rd rd' : reader) a n v,
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
(* normalize a symbolic state; rewrite the atoms' values *)
Ltac s1_norm HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac s1_U := repeat match goal with H : bv_unsigned (ew ?Ev ?k) = _ |- context [bv_unsigned (ew ?Ev ?k)] => rewrite H end.
(* add a region to the symbolic state: its region_ok at the state's memory and its disjointness from the others *)
Ltac s1_add HS r0 rok rdj :=
  let r := eval vm_compute in r0 in
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssv ?msv =>
  let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in
  assert (Rok : region_ok sg Ev (ms_mem msv) r); [rok | ];
  assert (Rdj : all_disjoint Ev r (ss_mem ssv)); [rdj | ];
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pi_add_region Ev ssv msv r HS eq_refl Rok Rdj) as HS3;
  clear HS Rok Rdj; rename HS3 into HS; s1_norm HS end.
Definition s1_box (P : Prop) : Prop := P.
(* name the model after a run, so that the goal's and the journal's copies do not grow *)
Ltac s1_name_md := try match goal with |- context [with_vm_backing ?a ?b ?c] =>
  let m := fresh "mdv" in set (m := with_vm_backing a b c) in *; clearbody m end.
Ltac s1_lia := first [lia | unfold SBc, A_G_REC in *; lia].
Ltac s1_rok wtac :=
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; s1_U;
  split; [s1_lia|]; split; [s1_lia|]; split; [first [intros o Ho; lia | wtac] |];
  repeat (apply Forall_cons; [eapply chunk_ok_val;
    [cbn [sv_denot]; s1_U; rewrite ?Z.add_0_r; reflexivity | first [zside | unfold A_G_REC; zside] | zside | eassumption] |]);
  apply Forall_nil.
Ltac s1_dj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; s1_U;
  unfold s1_box, A_G_REC, SBc in *; repeat split; s1_lia.

(* a register of the state, as the symbolic state gives it; a region of the state, with its region_ok *)
Ltac s1_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.
Ltac s1_rnth HS i HR :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth i rs cr_nul) in
  pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict] in HR end.
Ltac s1_inl := repeat (first [left; reflexivity | right]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis HB : CmdBSyms B.
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* what the journal (no footprint) keeps: image bytes outside the owned statics and errno, g_rec, g_rec's GOT word *)
Lemma s1_img_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k a HJ Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He |].
apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil].
Qed.
Lemma s1_grec_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k -> A_G_REC <= a < A_G_REC + 960 ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k a HJ Ha.
destruct (cmd_prog_unowned SEGS B LAWS HB IMG a) as (Hi & Ho & He); [exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | exact Ha]|].
exact (s1_img_kept STK sp0 ly S W mem md own ly' S' W' mem' md' k a HJ Hi Ho He).
Qed.
Lemma s1_got_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k -> cmd_ro_in (in_roP SEGS RLO RHI) ->
0xa6bc8 <= a < 0xa6bd0 -> rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k a HJ HRI Ha.
apply (s1_img_kept STK sp0 ly S W mem md own ly' S' W' mem' md' k a HJ).
- pose proof (s1_ro_a6bc8 _ HRI (a - 0xa6bc8) ltac:(lia)) as Hro. replace (0xa6bc8 + (a - 0xa6bc8)) with a in Hro by lia.
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)].
- rewrite (ts_owned B HB). apply (s1_unowned_range 0xa6bc8 0xa6bd0); [vm_compute; reflexivity | exact Ha].
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.

Theorem cr_s1 : CR_MC_stmt B RLO RHI -> CR_ENTRY_stmt B RLO RHI.
Proof.
intros MC v CX0 BD0 HFRM.
destruct v as [ly S W regs mem md ch w ww p0 n rep ans ev xr w0 R O].
pose proof CX0 as CX. unfold cr_cx in CX.
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_w c_ww c_p0 c_n c_rep c_ans c_ev c_xr c_w0 c_R c_O] in CX.
destruct CX as (HPRE & Hfr7 & HROD & HGOT & HROK & HROI & HVO & HGRD & H10 & HREC & Hn1 & Hry & Hno0 & Hrep & Htr
  & Hans & Hta & Hw8 & Hspw & HWRA & Hww & Hnv & Hn & HN0 & HAOK & HRY & HFL & HERR & HEV & HWHI).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
(* the reply block (rec_repA's areply_at): (rp, rn) with |xr| + 1 <= rn, holding xr ++ [0] *)
set (nr := Z.of_nat (length xr)).
destruct HREC as (Q & (Hgr & Hsc & Hap & Hcalls & Hansw & Hrepl & Hsca & Hown) & HO).
unfold areply_at in Hrepl. rewrite Hry in Hrepl. destruct (l_reply Q) as [[rp rn]|]; [|destruct Hrepl].
destruct Hrepl as (Vrp & Vsz & Hrp0 & Hxne & Hrin & Hrsz & Hrb & Hrlen). cbn [fst snd] in *.
rewrite length_app in Hrsz, Vsz, Hrlen. cbn [length] in Hrsz, Vsz, Hrlen.
destruct (al_blocks _ _ LAWS ly S W mem md rp rn HAR Hrin) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrn).
pose proof (req_size_pos0 rn ltac:(lia)) as [Hrq0 Hrq].
assert (Erp : rp = rep mod 2 ^ 64).
{ rewrite <- (aval_mem8_eq _ _ _ _ Vrp Hrep). rewrite Z.mod_small by lia. reflexivity. }
subst rp. set (repv := rep mod 2 ^ 64) in *.
assert (HSTK144 : 144 <= CHECK_REPLY_STK) by (rewrite HSTK; lia). unfold LMAX in Hrsz, Hrlen.
rewrite Nat2Z.inj_add in Hrsz, Vsz, Hrlen. change (Z.of_nat 1) with 1 in Hrsz, Vsz, Hrlen. fold nr in Hrsz, Vsz, Hrlen.
pose proof (cr_entry B LAWS TL TLF ly S W regs mem md ch CHECK_REPLY_STK w repv nr ww n p0 HPRE HSTK144 H10 Hw8 Hspw HWHI
  ltac:(lia) Hr16 ltac:(lia) ltac:(lia) ltac:(lia) Hn) as HS.
pose proof (ajournal_init SEGS B CHECK_REPLY_STK [] ly S W regs mem md ch HPRE) as HJ.
set (E := crE regs repv nr ww n p0 (as_uar_cell B)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crE; apply Eimg_env).
set (sp0 := spZ regs) in *.
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (cr_extra repv nr ww n p0 (as_uar_cell B) sp0)) k)
  by (intros k Hk; subst E; unfold crE; apply Eimg_low; exact Hk).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (cr_extra repv nr ww n p0 (as_uar_cell B) sp0) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
cbn [Nat.add nth cr_extra map] in E32, E33, E34, E35, E36, E38, E40, E41. clear EX.
assert (E10 : ew E 10 = Z_to_bv 64 w) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hsp1 : sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
set (sp1 := sp1_of sp0) in *. destruct Hsp1 as [Hsp1 Hsp1m].
assert (Hsp1a : sp1 mod 32 = 0).
{ rewrite Hsp1. replace (sp0 - 128 - sp0 mod 32) with ((sp0 / 32 - 4) * 32) by (pose proof (Z.div_mod sp0 32 ltac:(lia)); lia).
  apply Z_mod_mult. }
assert (Hsp1b : sp0 - 144 <= sp1 <= sp0 - 128) by (rewrite Hsp1; destruct Hsp1m; lia). clear Hsp1m.
assert (U41 : bv_unsigned (ew E 41) = sp1) by (rewrite E41; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_check_reply)) with (Z_to_bv 64 (BASE + AF_check_reply)).
shok_auto SHOK crBx E (mrestrict (w_H W) mem).
(* the prologue: the frame of 128, the callee-saved stores, the realignment, the two GOT loads; up to the frame call *)
paj_run_tok RUN HS HJ SHOK crSpan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 41%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U41; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. s1_name_md.
(* the frame call: __asan_stack_malloc_1(96) at sp1 = sp0 + (sp1 - sp0) *)
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1. rewrite (pal_cell B TL) in Kcell1.
apply (val_mem_of_rdword SEGS) in Kgot1. apply (val_mem_of_rdword SEGS) in Kcell1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
assert (Hsm : pa_sigma CS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1)
  by exact (palf_sm B TLF 1 ltac:(right; left; reflexivity)).
rewrite Hsm.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 (ASM fx) ltac:(lia) W (ms_regs msX) (ms_mem msX)
    CHECK_REPLY_STK sp0 [] ly S W mem md [] ly S _ 0 (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E41, unsigned_lit_small by lia. lia.
  - replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16)
      by (pose proof (Z.div_mod sp1 32 ltac:(lia)); pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - rewrite HSTK. unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
apply (val_mem_of_rdword SEGS) in Kgot2. apply (val_mem_of_rdword SEGS) in Kcell2.
(* the state after the call: the prologue's stack stores, the realigned slot, the shadow GOT word and cell *)
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact U41 | lia | lia | lia | lia | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot1 | exact Kgot2 | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell1 | exact Kcell2 | lia]. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ev1 := havoc E 42 (map (getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT; cbn; lia]).
(* the frame F = frame_addr ly 1 fpos, its flag cell FL, its shadow SBc + F / 8 *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFoff.
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 repv rn 1 fpos HAR2 ltac:(rewrite Eab; exact Hrin) Hfin2) as HdRF.
pose proof (blk_off_imgP B ly S W mem md repv rn HAR Hrin) as Hroff.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. red in HFoff, Hroff.
assert (HFLb : 4096 <= FL < alloc_ceiling) by (clear - HFLapp HFLce; unfold in_app in HFLapp; lia).
(* the disjunctive zone facts, boxed so that lia sees them only where a disjointness needs them *)
assert (ZONES : s1_box ((F + 128 <= 0x10000 \/ (0x606000 <= F /\ F + 128 <= 0x7fff7000) \/ 0x10007fff8000 <= F) /\
  (repv + req_size rn <= 0x10000 \/ (0x606000 <= repv /\ repv + req_size rn <= 0x7fff7000) \/ 0x10007fff8000 <= repv) /\
  (repv + req_size rn <= F \/ F + 128 <= repv))).
{ unfold s1_box. clear - HFoff HFapp Hroff Hrapp HdRF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
clear HFoff HFapp Hroff Hrapp HdRF HFLapp.
assert (RF : 0 <= F < 2 ^ 64) by lia. assert (RFL : 0 <= FL < 2 ^ 64) by lia.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (E46a : ew Ev1 46 = Z_to_bv 64 F).
{ subst Ev1. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Ha0. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 58 Ev1 ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SBc + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SBc + F / 8)]) as Ev2 eqn:HEv2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HEv2; apply img_env_havoc; [exact HEI1 | unfold A_TEXT; cbn; lia]).
assert (AG : forall k, (k < 42)%nat -> ew Ev2 k = ew E k)
  by (intros k Hk; rewrite HEv2, ew_havoc_old by lia; subst Ev1; apply ew_havoc_old; lia).
assert (E46 : ew Ev2 46 = Z_to_bv 64 F) by (rewrite HEv2, ew_havoc_old by lia; exact E46a).
assert (E58 : ew Ev2 58 = Z_to_bv 64 FL)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SBc + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E59 : ew Ev2 59 = Z_to_bv 64 (SBc + F / 8))
  by (rewrite HEv2; exact (ew_havoc_new Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SBc + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv2 E46a.
assert (E32' : ew Ev2 32 = Z_to_bv 64 SBc) by (rewrite AG by lia; exact E32).
assert (U46 : bv_unsigned (ew Ev2 46) = F) by (rewrite E46; apply unsigned_lit_small; lia).
assert (U58 : bv_unsigned (ew Ev2 58) = FL) by (rewrite E58; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew Ev2 59) = SBc + F / 8) by (rewrite E59; apply unsigned_lit_small; unfold SBc; lia).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG by lia; exact Usp).
assert (U41b : bv_unsigned (ew Ev2 41) = sp1) by (rewrite AG by lia; exact U41).
assert (U32 : bv_unsigned (ew Ev2 32) = SBc) by (rewrite E32'; apply unsigned_lit_small; unfold SBc; lia).
assert (U33 : bv_unsigned (ew Ev2 33) = A_G_REC) by (rewrite AG, E33 by lia; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U34 : bv_unsigned (ew Ev2 34) = repv) by (rewrite AG, E34 by lia; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew Ev2 35) = nr + 1) by (rewrite AG, E35 by lia; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew Ev2 36) = repv + nr) by (rewrite AG, E36 by lia; apply unsigned_lit_small; lia).
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (rewrite HVO by (vm_compute; lia); vm_compute; reflexivity).
assert (V2 : VAL (A_OBJ 2) = 0xa6bc8) by (rewrite HVO by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (rewrite HVO by (vm_compute; lia); vm_compute; reflexivity).
assert (U241 : bv_unsigned (ew Ev2 241) = 0xa5f50) by (rewrite (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact V0).
assert (U243 : bv_unsigned (ew Ev2 243) = 0xa6bc8) by (rewrite (HEI2 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact V2).
assert (U253 : bv_unsigned (ew Ev2 253) = 0xb0c38) by (rewrite (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)); exact V12).
(* facts and the shadow alias of the frame *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 46 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U46; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFd8 : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 59 (mkAF (SBc + 512) (SBc + 2 ^ 44) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U59; change (2 ^ 2) with 4; unfold SBc;
          split; [lia|]; split; [rewrite HFd8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
          apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 46 32 59 F SBc E46 RF E32' E59)) as HS3 end.
clear HS. rename HS3 into HS. s1_norm HS.
(* the values the added regions hold at the state after the call *)
assert (VFL : val_mem SEGS (mrestrict (w_H W) mem2) (F + 120) 8 FL).
{ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
assert (VZ : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SBc + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz.
  replace (SBc + F / 8 + 8 * j + i) with (SHADOW_OFF + F / 8 + (8 * j + i)) by (unfold SBc, SHADOW_OFF; lia).
  apply Hz. change (128 / 8) with 16. lia. }
assert (VZ0 : val_mem SEGS (mrestrict (w_H W) mem2) (SBc + F / 8 + 0) 8 0)
  by (replace (SBc + F / 8 + 0) with (SBc + F / 8 + 8 * 0) by lia; apply VZ; lia).
assert (VZ8 : val_mem SEGS (mrestrict (w_H W) mem2) (SBc + F / 8 + 8) 8 0)
  by (replace (SBc + F / 8 + 8) with (SBc + F / 8 + 8 * 1) by lia; apply VZ; lia).
assert (VGOT : val_mem SEGS (mrestrict (w_H W) mem2) (0xa6bc8 + 0) 8 A_G_REC).
{ rewrite Z.add_0_r. apply s1_val_mem_of_aval. apply (s1_aval_mem_ext (rdW W mem)); [| exact (proj1 HGOT)].
  intros k Hk. eapply s1_got_kept; [exact HJ2 | exact HROI | lia]. }
pose proof Hsca as (_ & _ & HnrA & _).
assert (VG920 : val_mem SEGS (mrestrict (w_H W) mem2) (A_G_REC + 920) 4 1).
{ apply s1_val_mem_of_aval. apply (s1_aval_mem_ext (rdW W mem)); [| rewrite <- Hn1; exact HnrA].
  intros k Hk. eapply s1_grec_kept; [exact HJ2 | unfold A_G_REC; lia]. }
assert (VG928 : val_mem SEGS (mrestrict (w_H W) mem2) (A_G_REC + 928) 8 repv).
{ apply s1_val_mem_of_aval. apply (s1_aval_mem_ext (rdW W mem)); [| exact Vrp].
  intros k Hk. eapply s1_grec_kept; [exact HJ2 | unfold A_G_REC; lia]. }
assert (VG936 : val_mem SEGS (mrestrict (w_H W) mem2) (A_G_REC + 936) 8 (nr + 1)).
{ apply s1_val_mem_of_aval. apply (s1_aval_mem_ext (rdW W mem)); [| exact Vsz].
  intros k Hk. eapply s1_grec_kept; [exact HJ2 | unfold A_G_REC; lia]. }
assert (VNUL : val_mem SEGS (mrestrict (w_H W) mem2) (repv + nr + 0) 1 0).
{ rewrite Z.add_0_r. eapply val_mem_entry_block; [exact HJ2 | exact Hrin | rewrite Eab; exact Hrin | lia | cbn; lia
    | intros x _; apply inFP_nil |].
  apply s1_val_mem_of_aval. intros k Hk. assert (k = 0%nat) by lia. subst k.
  specialize (Hrb (length xr) ltac:(rewrite length_app; cbn; lia)).
  replace (repv + nr + Z.of_nat 0) with (repv + Z.of_nat (length xr)) by (unfold nr; lia). rewrite Hrb.
  rewrite app_nth2, Nat.sub_diag by lia. vm_compute. reflexivity. }
unfold shadow_addr in HFSpres.
(* the frame's tail with the flag pointer at 120, its header, its shadow (writable for the set-up's stores), g_rec's GOT
   word, g_rec's nreplies / reply / reply_size, the reply's NUL byte *)
s1_add HS (YP09.mkRegion (Some 46%nat) 64 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 58 0))]) ltac:(s1_rok idtac) ltac:(s1_dj).
s1_add HS (YP09.mkRegion (Some 46%nat) 0 32 0 32 [])
  ltac:(s1_rok ltac:(intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))) ltac:(s1_dj).
s1_add HS (YP09.mkRegion (Some 59%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))])
  ltac:(s1_rok ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite SBc_SHADOW_OFF; apply (proj1 (HFSpres o ltac:(lia)))))
  ltac:(s1_dj).
s1_add HS cr_grecgot ltac:(s1_rok idtac) ltac:(s1_dj).
s1_add HS cr_grec ltac:(s1_rok idtac) ltac:(s1_dj).
s1_add HS cr_nul ltac:(s1_rok idtac) ltac:(s1_dj).
(* the frame set-up: the header words, the frame's shadow, g_rec's GOT load; up to the first inline check 0x86f78 *)
paj_run_to_sh RUNTOP HS HJ2 0xa48.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  do 3 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_gen with (n := 59%nat) (b := SBc + F / 8); [reflexivity | exact U59 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1 / 8) with 16. unfold SBc in Ha. unfold SHADOW_OFF.
    lia. }
  eapply awr_ok_cons_gen with (n := 46%nat) (b := F); [reflexivity | exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 41%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U41b; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. s1_name_md.
(* the frame's shadow read-only for the token run (a writable region inside the shadow span breaks sh_static_ok) *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth 3 rs cr_nul) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 3 r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx 3 r HS ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HS3 end.
clear HS. rename HS3 into HS. s1_norm HS.
(* the shadow entries of the inline checks #1..#4: g_rec's fields, the reply's NUL byte *)
pose proof (proj1 HJ2) as HAR3.
assert (UBx : U Ev2 crBx = SHADOW_OFF) by (unfold crBx; rewrite (U_atom Ev2 32 SBc E32') by (unfold SBc; lia); reflexivity).
assert (UG : U Ev2 (SOff 33 0) = A_G_REC) by (apply U_atom; [rewrite AG, E33 by lia; reflexivity | unfold A_G_REC; lia]).
assert (UN : U Ev2 (SOff 36 0) = repv + nr) by (apply U_atom; [rewrite AG, E36 by lia; reflexivity | lia]).
assert (UF : U Ev2 (SOff 46 0) = F) by (apply U_atom; [exact E46 | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H W) ?ms3) =>
  assert (ZSHG : range_addressable (rdW W (ms_mem ms3)) SHADOW_OFF A_G_REC 960);
  [ apply (cmd_addressable_in SEGS B LAWS HB ly S2 W (ms_mem ms3) _ (0xad560, 0x5e3680 - 0xad560) A_G_REC 960 HAR3);
    [ unfold Tfib_zero_shadow; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
    | unfold A_G_REC; cbn [fst snd]; lia | unfold A_G_REC; cbn [fst snd]; lia ] | ];
  assert (ZSHN : range_addressable (rdW W (ms_mem ms3)) SHADOW_OFF (repv + nr) 1);
  [ eapply (range_addressable_of_block SEGS B LAWS); [exact HAR3 | rewrite Eab; exact Hrin | lia | lia] | ];
  shok_auto_with SHOK crBx Ex (mrestrict (w_H W) (ms_mem ms3)) [mkSHE 33 920 944; mkSHE 36 0 1]
    ltac:(first
      [ eapply (shent_ok_of_range SEGS (w_H W) (ms_mem ms3) Ex crBx 33%nat A_G_REC 960 A_G_REC 920 944 ZSHG UBx UG);
          [lia | lia | intros x Hx; unfold A_G_REC, SHADOW_OFF in *; lia]
      | eapply (shent_ok_of_range SEGS (w_H W) (ms_mem ms3) Ex crBx 36%nat (repv + nr) 1 (repv + nr) 0 1 ZSHN UBx UN);
          [lia | lia | intros x Hx; unfold s1_box in ZONES; unfold SHADOW_OFF; lia]
      | eapply (shent_app_of_frame SEGS B LAWS ly S2 W (ms_mem ms3) _ Ex crBx 46%nat F 1 fpos 0 32 _ HAR3 Hfin2 UBx UF);
          [fold F; lia | lia | fold F; change (fs_frame_bytes 1) with 128; lia] ])
end.
(* the reply checks: nreplies = 1, reply_size <> 0, the reply pointer's shadow; then the UBSan pointer-overflow check
   of `reply + (reply_size - 1)` (0x86fcc bltu a1,a0: rep + nr below rep), the run's one undecided branch *)
paj_run_tok RUN HS HJ2 SHOK crSpan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_gen with (n := 46%nat) (b := F); [reflexivity | exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 41%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U41b; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. s1_name_md.
psrr_branch_tok RUN paj_branch HS SHOK crSpan.
{ (* taken: rep + nr < rep, against the reply block's bounds (rep + nr + 1 <= alloc_ceiling < 2^64) *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  assert (UR : U Ev2 (SOff 34 0) = repv) by (apply U_atom; [rewrite AG, E34 by lia; reflexivity | lia]).
  rewrite UN, UR in Hc. assert (0 <= nr) by (unfold nr; lia). lia. }
(* not taken: `snez` of rep (>= 4096) is 1 and `seqz` of rep + nr (>= 4096) is 0, so neither 0x86fdc nor 0x86fe0
   goes to the trap; the last byte's shadow and the byte 0; up to the memchr call 0x86ffc *)
paj_run_to_tok RUNTO HS HJ2 SHOK crSpan CR_MEMCHR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_gen with (n := 46%nat) (b := F); [reflexivity | exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 41%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U41b; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. s1_name_md.
(* at the memchr call: the registers, the regions' fields, the journal; hand off to CR_MC_stmt *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ev3 := Ex) in * end.
assert (AG3 : forall k, (k < 1024)%nat -> ew Ev3 k = ew Ev2 k)
  by (intros k Hk; subst Ev3; repeat (rewrite ew_ewset_other by lia); reflexivity).
assert (G3 : forall k v, (k < 42)%nat -> ew E k = Z_to_bv 64 v -> ew Ev3 k = Z_to_bv 64 v)
  by (intros k v Hk H; rewrite AG3, AG by lia; exact H).
assert (GR3 : forall k (r : bv 5), (k < 42)%nat -> Z.of_nat k = bv_unsigned r -> ew Ev3 k = getr regs r)
  by (intros k r Hk Hr; rewrite AG3, AG by lia; exact (EE k r Hr)).
assert (D0 : forall k, sv_denot Ev3 (SOff k 0) = ew Ev3 k)
  by (intros k; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
pmkst HS.
assert (F41 : ew Ev3 41 = Z_to_bv 64 sp1) by (apply G3; [lia | exact E41]).
assert (F10 : ew Ev3 10 = Z_to_bv 64 w) by (apply G3; [lia | exact E10]).
assert (F33 : ew Ev3 33 = Z_to_bv 64 A_G_REC) by (apply G3; [lia | exact E33]).
assert (F34 : ew Ev3 34 = Z_to_bv 64 repv) by (apply G3; [lia | exact E34]).
assert (F35 : ew Ev3 35 = Z_to_bv 64 (nr + 1)) by (apply G3; [lia | exact E35]).
assert (F32 : ew Ev3 32 = Z_to_bv 64 SBc) by (rewrite AG3 by lia; exact E32').
assert (F46 : ew Ev3 46 = Z_to_bv 64 F) by (rewrite AG3 by lia; exact E46).
assert (F58 : ew Ev3 58 = Z_to_bv 64 FL) by (rewrite AG3 by lia; exact E58).
assert (F59 : ew Ev3 59 = Z_to_bv 64 (SBc + F / 8)) by (rewrite AG3 by lia; exact E59).
assert (UF3 : bv_unsigned (ew Ev3 46) = F) by (rewrite AG3 by lia; exact U46).
assert (US3 : bv_unsigned (ew Ev3 59) = SBc + F / 8) by (rewrite AG3 by lia; exact U59).
assert (U23 : bv_unsigned (ew Ev3 2) = sp0) by (rewrite AG3 by lia; exact U2).
assert (UG3 : bv_unsigned (ew Ev3 33) = A_G_REC) by (rewrite AG3 by lia; exact U33).
(* the registers *)
s1_reg HS (2%bv : bv 5) R2. s1_reg HS (3%bv : bv 5) R3. s1_reg HS (4%bv : bv 5) R4. s1_reg HS (8%bv : bv 5) R8.
s1_reg HS (9%bv : bv 5) R9. s1_reg HS (10%bv : bv 5) R10. s1_reg HS (11%bv : bv 5) R11. s1_reg HS (12%bv : bv 5) R12.
s1_reg HS (18%bv : bv 5) R18. s1_reg HS (19%bv : bv 5) R19. s1_reg HS (20%bv : bv 5) R20. s1_reg HS (22%bv : bv 5) R22.
s1_reg HS (23%bv : bv 5) R23. s1_reg HS (24%bv : bv 5) R24. s1_reg HS (25%bv : bv 5) R25. s1_reg HS (26%bv : bv 5) R26.
s1_reg HS (27%bv : bv 5) R27.
rewrite D0 in R2, R3, R4, R8, R9, R10, R18, R19, R22, R23, R24, R25, R27.
rewrite F41 in R2, R9. rewrite F10 in R19. rewrite F34 in R10. rewrite F46 in R18, R23. rewrite F59 in R22.
rewrite F32 in R24. rewrite F33 in R25.
rewrite (GR3 3%nat (3%bv : bv 5)) in R3 by (first [lia | reflexivity]).
rewrite (GR3 4%nat (4%bv : bv 5)) in R4 by (first [lia | reflexivity]).
rewrite (GR3 2%nat (2%bv : bv 5)) in R8 by (first [lia | reflexivity]).
rewrite (GR3 27%nat (27%bv : bv 5)) in R27 by (first [lia | reflexivity]).
cbn [sv_denot] in R11, R12, R20. rewrite F35, unsigned_lit_small in R12 by lia. rewrite UG3 in R20.
replace (nr + 1 + -1) with nr in R12 by lia.
rewrite (denot_shx Ev3 33 32 928 A_G_REC SBc F33 F32) in R26 by (unfold A_G_REC, SBc; lia).
(* the regions' fields: the flag pointer, refusal's shadow bytes, the saved registers, g_rec's reply fields *)
s1_rnth HS 5%nat HRt. s1_rnth HS 3%nat HRs. s1_rnth HS 7%nat HRk. s1_rnth HS 1%nat HRg.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H W) ?ms3) =>
assert (VFL3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) (F + 120) 8 FL)
  by exact (field_of_region _ _ _ F _ _ _ _ _ 120 8%N (SOff 58 0) FL HRt UF3 ltac:(s1_inl) ltac:(rewrite D0; exact F58)
    ltac:(zside) ltac:(zside));
assert (VS3 : forall i, 4 <= i < 8 -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) (SHADOW_OFF + F / 8 + i) 1 0);
[ intros i Hi; rewrite <- SBc_SHADOW_OFF; assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  destruct Hi' as [-> | [-> | [-> | ->]]];
  [ exact (field_of_region _ _ _ (SBc + F / 8) _ _ _ _ _ 4 1%N (SLit 0) 0 HRs US3 ltac:(s1_inl) eq_refl ltac:(zside) ltac:(zside))
  | exact (field_of_region _ _ _ (SBc + F / 8) _ _ _ _ _ 5 1%N (SLit 0) 0 HRs US3 ltac:(s1_inl) eq_refl ltac:(zside) ltac:(zside))
  | exact (field_of_region _ _ _ (SBc + F / 8) _ _ _ _ _ 6 1%N (SLit 0) 0 HRs US3 ltac:(s1_inl) eq_refl ltac:(zside) ltac:(zside))
  | exact (field_of_region _ _ _ (SBc + F / 8) _ _ _ _ _ 7 1%N (SLit 0) 0 HRs US3 ltac:(s1_inl) eq_refl ltac:(zside) ltac:(zside)) ]
| ];
assert (VK3 : cr_saved (mrestrict (w_H W) (ms_mem ms3)) sp0 regs);
[ intros j rr Hj;
  do 12 (destruct j as [|j]; [cbn [nth_error cr_saved_regs] in Hj; injection Hj as <-;
    lazymatch goal with |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?k) _ (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
      let off := eval cbv in (- 8 - 8 * Z.of_nat k) in
      let kr := eval cbv in (Z.to_nat r) in
      replace (sp0 - 8 - 8 * Z.of_nat k) with (sp0 + off) by (cbn; lia);
      exact (field_of_region _ _ _ sp0 _ _ _ _ _ off 8%N (SOff kr 0) (bv_unsigned (getr regs (Z_to_bv 5 r))) HRk U23
        ltac:(s1_inl)
        ltac:(rewrite D0, (GR3 kr (Z_to_bv 5 r)) by (first [lia | reflexivity]); symmetry; apply Z_to_bv_bv_unsigned)
        (bv_unsigned_in_range 64 _) ltac:(zside)) end |]);
  cbn in Hj; destruct j; discriminate
| ];
assert (VG3a : val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) (A_G_REC + 928) 8 repv)
  by exact (field_of_region _ _ _ A_G_REC _ _ _ _ _ 928 8%N (SOff 34 0) repv HRg UG3 ltac:(s1_inl) ltac:(rewrite D0; exact F34)
    ltac:(zside) ltac:(zside));
assert (VG3b : val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) (A_G_REC + 936) 8 (nr + 1))
  by exact (field_of_region _ _ _ A_G_REC _ _ _ _ _ 936 8%N (SOff 35 0) (nr + 1) HRg UG3 ltac:(s1_inl) ltac:(rewrite D0; exact F35)
    ltac:(zside) ltac:(zside))
end.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?ms3) _ (ms_mem ?ms3) _; cfg_model := ?mdc |} _ =>
  set (regs3 := ms_regs ms3) in *; set (mem3 := ms_mem ms3) in *;
  refine (MC (mkCRV ly S W regs mem md ch w ww p0 n rep ans ev xr w0 R O) ly S2 W regs3 mem3 mdc fpos CX0 _ _ _ _ _ _ BD0 _ HFRM) end.
- unfold cr_mid, c_sp, c_p, c_nr. cbn [c_ly c_S c_W c_regs c_mem c_md c_rep c_xr].
  split; [exact HJ2|]. split; [rewrite Eab; apply Permutation_refl|].
  split; [exact VFL3|]. split; [exact VS3|]. split; [exact VK3|]. split; [exact VG3a | exact VG3b].
- unfold cr_regs_at, c_sp. cbn [c_regs].
  split; [exact R2|]. split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
  split; [rewrite R8; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact R9|].
  split; [exact R18|]. split; [exact R23|]. split; [exact R22|]. split; [exact R24|]. split; [exact R25|].
  split; [exact R20|]. split; [exact R26 | exact R27].
- exact R19.
- exact R10.
- exact R11.
- exact R12.
- unfold cr_ls. cbn [c_ly c_S]. split; [reflexivity | exists fS2; exact ES2].
Qed.

End e.
End f.
End d.
