(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of pins_clear's ASan walk on plugin-hostd/fuzz_command
   (the inlined record(), recorder.c:205-221), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX, the
   entry segment of the cgif_close walk) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_clear_s3.v, with its module paths and module names changed; 154 of its 189 lines of code are new or changed and 655 lines of the source are left out. *)
(* check_arity's bcmp call step (rows 0, 3, 8 and 14). At each of their call sites the inlined syntax_has scans the
   row's syntax string with a call of the bcmp wrapper against the literal "..." (CA_DOTS = 0x21880): the jal at
   0x8764c in dots_loop (head 0x87638), RETURN 0x87650 (retk = 4460 from BASE = 0x864e4), a1 = A_OBJ 19, a2 = 3.

   `ca_bcmp_step` takes the symbolic state at the wrapper's entry (plain st_ok: pa_sigma is absolute there), checks
   the site by computation (ca_call_ok, check_arity_s6.v), discharges the premises of cgif_file_fuzzer's
   aj_bcmp_at (lib/Reusable/YCbq.v:2444; the ABCMP contract of the statement, check_arity_c.v:84), and hands
   the walk the state after the call: a havoc of the environment above kk, the journal, the read-only invariant
   ca_lowkept, and the one fact the following `beqz a0` (0x87650) needs: the junk atom of a0 is zero exactly when
   the item's three bytes equal "..." (ca_eq3). Nothing of musl or of the ASan runtime is walked here.

   Template (not used as a source): a former lib/A/Prog/check_arity.v, an earlier
   ASan walk in the OLD lib/Lib `evt` / MState framework against the OLD statement (bcmp_wrap_contract). It is a
   TEMPLATE, NOT A SOURCE: porting it is a rewrite into another execution model, and our concrete-run method needs
   none of its loop invariants. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s4 check_arity_s5 check_arity_s6.
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

(* the second argument of every call: the atom of the literal "..." is its address *)
Lemma ca_dots_val : forall E, img_env VAL A_LIM E -> sv_denot E (SOff (A_OBJ 19) 0) = w64 CA_DOTS.
Proof.
intros E HE. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (HE (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
rewrite (HVO 19%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
reflexivity.
Qed.

Lemma ca_bcmp_step : forall (row : nat) (x retk : Z) (kk : nat) E ss (W : world SEGS) ms md
  (sp0 : Z) ly S W0 mem0 md0 lyc Sc memc Q,
(row < 22)%nat -> img_env VAL A_LIM E -> ca_call_ok row x retk kk ss = true ->
st_ok SEGS E ss (restrict (w_H W) ms) ->            (* plain st_ok: at a call pa_sigma is ABSOLUTE *)
ss_pc ss = SIG CS___interceptor_trampoline_bcmp ->
ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W0 mem0 md0 [] lyc Sc W (ms_mem ms) md 0 ->
bv_unsigned (ew E 2) = sp0 - 112 -> 2 ^ 46 <= sp0 <= 2 ^ 47 ->
ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
cmd_ro_bytes (aview SEGS (w_H W) memc) -> ca_lowkept W memc (ms_mem ms) ->
(forall E2 ms2 md2, img_env VAL A_LIM E2 -> (forall n, (n < kk)%nat -> ew E2 n = ew E n) ->
   st_ok_pi SEGS VAL E2 (ss_after_call ss (ss_mem ss) kk retk) (restrict (w_H W) ms2) ->
   ajournal SEGS B CHECK_ARITY_STK sp0 [] ly S W0 mem0 md0 [] lyc Sc W (ms_mem ms2) md2 0 ->
   ca_lowkept W memc (ms_mem ms2) ->
   (U E2 (SOff (kk + 4)%nat 0) = 0 <-> ca_eq3 row x = true) ->
   SRr SEGS W (mkCfg ms2 md2) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros row x retk kk E ss W ms md sp0 ly S W0 mem0 md0 lyc Sc memc Q
  Hrow HE HOK HS Hpc HJ Hsp Hsp0 E3 E4 HRO HLK Hk.
destruct (ca_call_okE row x retk kk ss HOK) as (R10 & R11 & R12 & R3 & R4 & R2 & R1 & Hrk & Hrk2 & Hkk & Hrv &
  Hat & Hwf & Hnc & Hmat & Hsh & Hx1 & Hx2 & Hhull).
destruct (ca_syn_bound row Hrow) as (Hsa & _ & Hsb & _).
pose proof HJ as (HAR & _).
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_restrict_reg SEGS (w_H W) E ss ms r HS)).
assert (D0 : forall n, sv_denot E (SOff n 0) = ew E n)
  by (intros n; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Ga0 : getr (ms_regs ms) 10 = w64 x) by (rewrite GR, R10; reflexivity).
assert (Ga1 : getr (ms_regs ms) 11 = w64 CA_DOTS) by (rewrite GR, R11; exact (ca_dots_val E HE)).
assert (Ga2 : getr (ms_regs ms) 12 = w64 3) by (rewrite GR, R12; reflexivity).
assert (Ggp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite GR, R3, D0; exact E3).
assert (Gtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite GR, R4, D0; exact E4).
assert (Gra : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk)) by (rewrite GR, R1; exact (codeptr_val E retk HE)).
assert (Gsp : spZ (ms_regs ms) = sp0 + -112) by (unfold spZ; rewrite GR, R2, D0, Hsp; lia).
pose proof ca_dots_len as HL4.
assert (SRCX : src_ok SEGS W (ms_regs ms) (ms_mem ms) x 3).
{ intros a Ha. split; [| rewrite Gsp; unfold ESTACK; lia].
  rewrite (HLK a ltac:(lia)).
  pose proof (ca_ro_syn _ HRO row Hrow) as HSYN.
  replace a with (ca_syn_addr row + Z.of_nat (Z.to_nat (a - ca_syn_addr row))) by lia.
  rewrite (HSYN (Z.to_nat (a - ca_syn_addr row)) ltac:(lia)). discriminate. }
assert (SRCY : src_ok SEGS W (ms_regs ms) (ms_mem ms) CA_DOTS 3).
{ intros a Ha. split; [| rewrite Gsp; unfold ESTACK, CA_DOTS in *; lia].
  rewrite (HLK a ltac:(unfold CA_DOTS in *; lia)).
  pose proof (ca_ro_dots _ HRO) as HD.
  replace a with (CA_DOTS + Z.of_nat (Z.to_nat (a - CA_DOTS))) by lia.
  rewrite (HD (Z.to_nat (a - CA_DOTS)) ltac:(lia)). discriminate. }
assert (BX : forall a, x <= a < x + 3 -> ~ (sp0 + -112 - 2 * ESTACK <= a < sp0 + -112))
  by (intros a Ha; unfold ESTACK; lia).
assert (BY : forall a, CA_DOTS <= a < CA_DOTS + 3 -> ~ (sp0 + -112 - 2 * ESTACK <= a < sp0 + -112))
  by (intros a Ha; unfold ESTACK, CA_DOTS in *; lia).
assert (MX : amem_range x 3) by (left; unfold kLowMemEnd; lia).
assert (MY : amem_range CA_DOTS 3) by (left; unfold kLowMemEnd, CA_DOTS; lia).
assert (RAX : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF x 3).
{ apply (range_addressable_sub _ _ _ _ x 3 (ca_syn_addressable B HB row _ _ W (ms_mem ms) md Hrow HAR)); lia. }
assert (HX : 0 < 3 -> shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) x 3)
  by (intros _; exact (ca_hull_of B HB _ _ W (ms_mem ms) md x 3 HAR Hhull)).
assert (RAY : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF CA_DOTS 3)
  by exact (ca_dots_addr B HB _ _ W (ms_mem ms) md HAR).
assert (HY : 0 < 3 -> shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) CA_DOTS 3)
  by (intros _; exact (ca_hull_of B HB _ _ W (ms_mem ms) md CA_DOTS 3 HAR ltac:(vm_compute; reflexivity))).
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv), Hpc.
eapply SRr_bind.
{ exact (aj_bcmp_at SEGS B LAWS pa_segs_low (SIG CS___interceptor_trampoline_bcmp) ABCMP W (ms_regs ms) (ms_mem ms)
    CHECK_ARITY_STK sp0 [] ly S W0 mem0 md0 [] lyc Sc md 0 x CA_DOTS 3 (-112) (Z_to_bv 64 (BASE + retk))
    HJ Ga0 Ga1 Ga2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold CA_DOTS; lia) ltac:(unfold CA_DOTS; lia)
    Gsp eq_refl ltac:(lia) ltac:(unfold CHECK_ARITY_STK, ESTACK; lia) Ggp Gtp Gra (ret_ok_codeptr_v retk Hrk Hrk2)
    SRCX SRCY BX BY MX MY RAX HX RAY HY). }
intros W' c' _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hres & Hcmp & Hfr & Hpres2).
assert (HAV : forall a, (0 <= a < 2 ^ 40 \/ sp0 - 112 <= a < sp0 - 112 + 112) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)
  by (intros a Ha; apply Hfr; unfold ESTACK; lia).
assert (HLK2 : ca_lowkept W memc mem2) by (intros a Ha; rewrite (HAV a ltac:(lia)); exact (HLK a Ha)).
pose proof (ca_kept E W (ms_mem ms) mem2 (ss_mem ss) (sp0 - 112) Hsh Hsp ltac:(lia) HAV Hpres2) as HKEPT.
pose proof (st_ok_pi_after_call_hi kk E ss (restrict (w_H W) ms) regs2 (mrestrict (w_H W) mem2) (ss_mem ss) retk
  HE Hrk HS Hrv Hat Hwf Hnc Hmat (submem_refl _) R1 HP HKEPT) as HS2.
apply (Hk (havoc E kk (map (getr regs2) CLOB)) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2).
- exact (img_env_havoc_hi E kk _ HE Hkk).
- intros n Hn. exact (ew_havoc_old E kk _ n Hn).
- exact HS2.
- exact HJ2.
- exact HLK2.
- rewrite U_SOff, Z.add_0_r.
  rewrite (ew_havoc_new E kk (map (getr regs2) CLOB) 4%nat (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  change (nth 4%nat (map (getr regs2) CLOB) (Z_to_bv 64 0)) with (getr regs2 10).
  rewrite Hres, zcanon_unsigned.
  rewrite <- (ca_cmp_bytes W memc (ms_mem ms) row x Hrow HRO HLK Hx1 Hx2), <- Hcmp.
  split; intros H.
  + apply bv_eq. rewrite H. reflexivity.
  + rewrite H. reflexivity.
Qed.

End e.
End f.
End d.

(* The per-site tactics of the bcmp rows. A row proof keeps these hypothesis names through its walk: HS (the
   walk's st_ok_pi, plain st_ok at a call), HJ (the journal), HEI (img_env of the current environment), Usp / Egp
   / Etp (its sp, gp and tp atoms: `bv_unsigned (ew E 2) = sp0 - 112`, `ew E 3 = w64 (as_gp B)`,
   `ew E 4 = w64 (as_tp B)`), AG (its agreement with the entry environment below A_TEXT, for ca_regs_back_g), HLK
   (ca_lowkept from the entry memory), HRO (cmd_ro_bytes of the entry memory) and Hsp0 (2 ^ 46 <= sp0 <= 2 ^ 47).
   CBS is ca_bcmp_step at the row's B (or a hypothesis of its statement), RUNP / RUNC the run lemmas of
   check_arity_s4.v, BR paj_branch. *)

(* after a symbolic run: ca_lowkept across it, the run's frame facts dropped, and the model seated as an atom
   (memory trap #1: chained runs otherwise nest the model term) *)
Ltac ca_after_run :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m) (mrestrict (w_H ?W) ?m'),
    Usp : bv_unsigned (ew ?E 2) = _, Hl : ca_lowkept ?W ?m0 ?m |- _ =>
    let H := fresh "HLKn" in
    assert (H : ca_lowkept W m0 m')
      by (apply (ca_lowkept_run E rs W m m' m0 HFr); [vm_compute; reflexivity | rewrite Usp; lia | exact Hl]);
    clear Hl; rename H into HLK
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  let mdv := fresh "mdv" in set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.

(* one symbolic run from HS, to a call, a branch or the ret *)
Ltac ca_run RUNP RUNC :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, Usp : bv_unsigned (ew ?E 2) = _ |- _ =>
    paj_run_shc RUNP RUNC HS HJ; [ apply ca_awr_sh; [vm_compute; reflexivity | exact Usp] | ca_after_run ]
  end.

(* at the wrapper's entry: the call step with the site's own a0, ra and junk band kk; the invariants re-seated
   on the environment after the call; HIFF is the fact the following beqz reads *)
Ltac ca_call CBS row kk :=
  lazymatch goal with
  | HS : st_ok _ ?E ?ssc (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ ?sp0 _ _ _ _ _ _ _ _ _ _ _ _ _,
    HEI : img_env _ _ ?E, Usp : bv_unsigned (ew ?E 2) = _, Egp : ew ?E 3 = _, Etp : ew ?E 4 = _,
    HRO : cmd_ro_bytes _, Hl : ca_lowkept _ _ _, Hsp0 : 2 ^ 46 <= ?sp0 <= 2 ^ 47,
    AG : forall n, (n < A_TEXT)%nat -> ew ?E n = ew ?EI n |- _ =>
    let x := eval vm_compute in (match sr_get (ss_regs ssc) 10 with SLit v => v | _ => 0 end) in
    let retk := eval vm_compute in (match sr_get (ss_regs ssc) 1 with SOff _ z => z | _ => 0 end) in
    let Hrow := fresh "Hrow" in let Hok := fresh "Hok" in
    assert (Hrow : (row < 22)%nat) by lia;
    assert (Hok : ca_call_ok row x retk kk ssc = true) by (vm_compute; reflexivity);
    apply (CBS row x retk kk E ssc W ms _ _ _ _ _ _ _ _ _ _ _ Hrow HEI Hok HS eq_refl HJ Usp Hsp0 Egp Etp HRO Hl);
    clear Hrow Hok HS HJ Hl;
    let E2 := fresh "E" in let ms2 := fresh "ms" in let md2 := fresh "md" in
    let HEI2 := fresh "HEIn" in let AG2 := fresh "AGc" in let AGn := fresh "AGn" in
    intros E2 ms2 md2 HEI2 AG2 HS HJ HLK HIFF;
    rewrite <- (AG2 2%nat) in Usp by lia;
    rewrite <- (AG2 3%nat) in Egp by lia;
    rewrite <- (AG2 4%nat) in Etp by lia;
    assert (AGn : forall n, (n < A_TEXT)%nat -> ew E2 n = ew EI n)
      by (intros n Hn; rewrite (AG2 n) by (unfold A_TEXT in Hn; lia); exact (AG n Hn));
    clear AG AG2 HEI; rename AGn into AG; rename HEI2 into HEI
  end.

(* the beqz a0 after a call whose three bytes differ from "...": the taken side dies by HIFF and ca_eq3 *)
Ltac ca_beqz_ne RUNP BR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HIFF : _ <-> ca_eq3 _ _ = true |- _ =>
    psrr_branch_pi RUNP BR HS;
    [ exfalso;
      lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
        rewrite branch_eq_U, U_SLit in Hc; apply Z.eqb_eq in Hc; change (zcanon 0) with 0 in Hc;
        apply HIFF in Hc; vm_compute in Hc; discriminate Hc end
    | lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end; clear HIFF ]
  end.

(* one bcmp site at the junk band kk: run to the call, the step, run to the beqz, its taken side killed *)
Ltac ca_site_ne CBS RUNP RUNC BR row kk :=
  ca_run RUNP RUNC; ca_call CBS row kk; ca_run RUNP RUNC; ca_beqz_ne RUNP BR.
