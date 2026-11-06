(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of pins_clear's ASan walk on plugin-hostd/fuzz_command
   (the inlined record(), recorder.c:205-221), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX, the
   entry segment of the cgif_close walk) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_clear_s3.v, with its module paths and module names changed; 147 of its 182 lines of code are new or changed and 655 lines of the source are left out. *)
(* check_arity, row 8 of the scan of g_parsed (plugin-hostd/fuzz_command, ASan image, lib/A).

   Row 8 has (mn, mx) = (3, 4). From the matched-row entry 0x87334 (CA_SEG) the walk takes the syntax arm (0x874d8)
   and the inlined syntax_has (dots_loop, loop head 0x87638), which calls the bcmp wrapper 17 times, all at the same
   site: the jal 0x8764c, return 0x87650 (retk = 4460 from BASE = 0x87140 - 0xc5c = 0x864e4), a1 = A_OBJ 19 = "..."
   (0x21880), a2 = 3. The items are 0x215BD, 0x215BE, ..., 0x215CD; none of them equals "...", so every `beqz a0` after
   a call falls through. The walk then reaches `ret` after 1,326 instructions.

   Each call is the step ca_bcmp_step (check_arity_s7.v: the bcmp wrapper's contract ABCMP through aj_bcmp_at). The
   per-site tactic (ca_site) is local to this file.

   Earlier work: a former lib/A/Prog/check_arity.v: an earlier ASan walk in the OLD
   lib/Lib `evt` / MState framework against the OLD statement (bcmp_wrap_contract). Its first half (dots_loop, synloop,
   fmtloop) compiled in earlier builds by its author's account; its second half (rest of rows_loop, minv_entry,
   linv_entry, cont_ok, look_ok, check_arity_holds) was never built. It is a TEMPLATE, NOT A SOURCE: porting it is a
   rewrite into another execution model, and our concrete-run method needs none of its loop invariants. Its pcs are
   cross-checks of this run: rows_loop head 0x87304 (its :1589), dots_loop 0x87638 (:457), fmtloop 0x873dc (:973), the
   format arm 0x87368 (:1255), the syntax arm 0x874d8 (:830). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s4 check_arity_s5 check_arity_s6 check_arity_s7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis HVO : cmd_val_objs.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* one call of row 8, with the environment tied to the entry's (E0) below A_TEXT rather than to the call's *)
Lemma ca_site8 : forall (x retk : Z) (kk : nat) E E0 ss (W : world SEGS) ms md sp0 ly S W0 mem0 md0 memc Q,
img_env VAL A_LIM E -> ca_call_ok 8 x retk kk ss = true ->
st_ok SEGS E ss (restrict (w_H W) ms) -> ss_pc ss = SIG CS___interceptor_trampoline_bcmp ->
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W0 mem0 md0 [] ly S W (ms_mem ms) md 0 ->
(forall n, (n < A_TEXT)%nat -> ew E n = ew E0 n) ->
bv_unsigned (ew E0 2) = sp0 - 112 -> 2 ^ 46 <= sp0 <= 2 ^ 47 ->
ew E0 3 = w64 (as_gp B) -> ew E0 4 = w64 (as_tp B) ->
cmd_ro_bytes (aview SEGS (w_H W) memc) -> ca_lowkept W memc (ms_mem ms) ->
(forall E2 ms2 md2, img_env VAL A_LIM E2 -> (forall n, (n < A_TEXT)%nat -> ew E2 n = ew E0 n) ->
   st_ok_pi SEGS VAL E2 (ss_after_call ss (ss_mem ss) kk retk) (restrict (w_H W) ms2) ->
   ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W0 mem0 md0 [] ly S W (ms_mem ms2) md2 0 ->
   ca_lowkept W memc (ms_mem ms2) ->
   (U E2 (SOff (kk + 4)%nat 0) = 0 <-> ca_eq3 8 x = true) ->
   SRr SEGS W (mkCfg ms2 md2) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros x retk kk E E0 ss W ms md sp0 ly S W0 mem0 md0 memc Q HEI Hok HS Hpc HJ AG U0 Hsp G0 T0 HRO HLK K.
pose proof (ca_call_okE 8 x retk kk ss Hok) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkk & _).
assert (Hlt : forall n, (n < A_TEXT)%nat -> (n < kk)%nat) by (intros n Hn; unfold A_TEXT, A_LIM in *; lia).
apply (ca_bcmp_step B HB ABCMP HVO 8 x retk kk E ss W ms md sp0 ly S W0 mem0 md0 ly S memc Q ltac:(lia) HEI Hok HS Hpc HJ).
- rewrite (AG 2%nat ltac:(unfold A_TEXT; lia)). exact U0.
- exact Hsp.
- rewrite (AG 3%nat ltac:(unfold A_TEXT; lia)). exact G0.
- rewrite (AG 4%nat ltac:(unfold A_TEXT; lia)). exact T0.
- exact HRO.
- exact HLK.
- intros E2 ms2 md2 HEI2 AG2 HS2 HJ2 HLK2 HIFF.
  apply (K E2 ms2 md2 HEI2); [| exact HS2 | exact HJ2 | exact HLK2 | exact HIFF].
  intros n Hn. rewrite (AG2 n (Hlt n Hn)). exact (AG n Hn).
Qed.

(* the per-site tactic. It finds its facts by their types: the entry's environment E0 (AG : the current environment
   agrees with E0 below A_TEXT; U0, Hsp0, G0, T0 : sp, gp and tp of E0), the read-only bytes of the entry memory
   (cmd_ro_bytes), the current state (st_ok / st_ok_pi, ajournal, ca_lowkept, img_env). *)
Ltac ca_awr_t :=
  lazymatch goal with
  | AG_ : forall n : nat, (n < A_TEXT)%nat -> ew _ n = ew _ n, U0_ : bv_unsigned (ew _ 2) = _ - 112 |- _ =>
    apply ca_awr_sh;
    [vm_compute; reflexivity | exact (eq_trans (f_equal bv_unsigned (AG_ 2%nat ltac:(unfold A_TEXT; lia))) U0_)]
  end.

(* after a run: carry ca_lowkept across its frame, drop the run's frame facts, and make the model an atom *)
Ltac ca_lk_step :=
  lazymatch goal with
  | Hfr_ : frame_of ?E ?rs (mrestrict _ ?m0) (mrestrict _ ?m1), Hlk_ : ca_lowkept ?W ?mc _,
    AG_ : forall n : nat, (n < A_TEXT)%nat -> ew _ n = ew _ n, U0_ : bv_unsigned (ew _ 2) = _ - 112 |- _ =>
    let SH := fresh "SH" in
    assert (SH : forallb ca_shape rs = true) by (vm_compute; reflexivity);
    let H40 := fresh "H40" in
    assert (H40 : 2 ^ 40 <= bv_unsigned (ew E 2))
      by (pose proof (eq_trans (f_equal bv_unsigned (AG_ 2%nat ltac:(unfold A_TEXT; lia))) U0_); lia);
    let HLK' := fresh "HLK'" in
    pose proof (ca_lowkept_run E rs W m0 m1 mc Hfr_ SH H40 Hlk_) as HLK';
    clear SH H40 Hlk_; rename HLK' into HLK
  end;
  lazymatch goal with
  | HF_ : frame_of _ _ _ _, HFr_ : frame_of _ _ _ _, HG_ : mem_grows _ _ |- _ => clear HF_ HFr_ HG_
  end;
  let mdn := fresh "mdv" in
  set (mdn := with_vm_backing _ _ _) in *; clearbody mdn.

(* at the wrapper's entry: one ca_site8 with the junk band kk *)
Ltac ca_bcmp kk :=
  lazymatch goal with
  | HS_ : st_ok _ ?E ?ss (restrict (w_H ?W) ?m), HJ_ : ajournal _ _ _ ?sp0 _ ?ly ?S ?W0 ?mem0 ?md0 _ _ _ _ _ _ _,
    HEI_ : img_env _ A_LIM _, AG_ : forall n : nat, (n < A_TEXT)%nat -> ew _ n = ew ?E0 n,
    U0_ : bv_unsigned (ew _ 2) = _ - 112, Hsp0_ : 2 ^ 46 <= _ <= 2 ^ 47,
    G0_ : ew _ 3 = w64 (as_gp _), T0_ : ew _ 4 = w64 (as_tp _),
    HROB_ : cmd_ro_bytes (aview _ _ ?memc), HLK_ : ca_lowkept _ _ _ |- SRr _ _ (mkCfg _ ?md) _ =>
    let x := eval vm_compute in (match sr_get (ss_regs ss) 10 with SLit v => v | _ => -1 end) in
    let rk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => -1 end) in
    apply (ca_site8 x rk kk E E0 ss W m md sp0 ly S W0 mem0 md0 memc _ HEI_
      ltac:(vm_compute; reflexivity) HS_ eq_refl HJ_ AG_ U0_ Hsp0_ G0_ T0_ HROB_ HLK_);
    clear HS_ HJ_ HEI_ AG_ HLK_;
    intros ?Ec ?ms ?md HEI AGc HS HJ HLK HIFF
  end.

(* the taken side of `beqz a0` after a call whose three bytes are not "..." *)
Ltac ca_kill :=
  exfalso;
  lazymatch goal with
  | Hc : branch_taken _ _ _ = true, HIFF : _ <-> ca_eq3 _ _ = true |- _ =>
    rewrite branch_eq_U, U_SLit in Hc; apply Z.eqb_eq in Hc; change (zcanon 0) with 0 in Hc;
    apply (proj1 HIFF) in Hc; vm_compute in Hc; discriminate Hc
  end.

Ltac ca_run :=
  lazymatch goal with
  | HS_ : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ_ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_shc RUNP RUNC HS_ HJ_
  end.

Ltac ca_site kk :=
  ca_run; [ca_awr_t | ca_lk_step; ca_bcmp kk];
  ca_run; [ca_awr_t | ca_lk_step];
  lazymatch goal with HS_ : st_ok_pi _ _ _ _ (restrict (w_H _) _) |- _ => psrr_branch_pi RUNP BR HS_ end;
  [ ca_kill
  | lazymatch goal with Hc_ : branch_taken _ _ _ = false, HI_ : _ <-> ca_eq3 _ _ = true |- _ => clear Hc_ HI_ end ].

Lemma ca_row_8 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B 8 3 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP G3 G4.
pose proof (ca_row_open B HB 8 3 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
clear HFR.
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
set (E0 := Eimg (Ereg regs (ca_extra s3v regs0))) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
assert (AGc : forall n, (n < A_TEXT)%nat -> ew E0 n = ew E0 n) by (intros; reflexivity).
assert (U0 : bv_unsigned (ew E0 2) = spZ regs0 - 112).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). exact Hsp. }
assert (G0 : ew E0 3 = w64 (as_gp B)).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact (eq_trans R3 G3). }
assert (T0 : ew E0 4 = w64 (as_tp B)).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact (eq_trans R4 G4). }
assert (Hsp0 : 2 ^ 46 <= spZ regs0 <= 2 ^ 47).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
  unfold CHECK_ARITY_STK, ESTACK in *. lia. }
assert (HROB : cmd_ro_bytes (aview SEGS (w_H W) memc)) by exact (proj1 HRO).
assert (HLK : ca_lowkept W memc memc) by apply ca_lowkept_refl.
clear HRO G3 G4.
ca_site 1024%nat.
ca_site 1040%nat.
ca_site 1056%nat.
ca_site 1072%nat.
ca_site 1088%nat.
ca_site 1104%nat.
ca_site 1120%nat.
ca_site 1136%nat.
ca_site 1152%nat.
ca_site 1168%nat.
ca_site 1184%nat.
ca_site 1200%nat.
ca_site 1216%nat.
ca_site 1232%nat.
ca_site 1248%nat.
ca_site 1264%nat.
ca_site 1280%nat.
paj_run_shc RUNP RUNC HS HJ; [ca_awr_t | ca_lk_step].
destruct (ca_regs_back_g (w_H W) _ _ _ regs regs0 s3v HS AGc ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

End e.
End f.
End d.
