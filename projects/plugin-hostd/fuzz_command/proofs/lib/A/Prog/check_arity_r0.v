(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 152 of its 183 lines of code are new or changed and 381 lines of the source are left out. *)
(* check_arity on the ASan build of plugin-hostd/fuzz_command: ROW 0 of g_parsed, from the matched-row entry
   BASE + CA_SEG (0x87334) to `ret` (BASE + CA_RET, 0x8777c), shaped like check_arity_s4.v's ca_row_1.

   Row 0's syntax string is scanned by the inlined syntax_has with calls of the bcmp wrapper against the literal
   "..." (0x21880): 38 calls, all at the jal 0x8764c of dots_loop (return 0x87650, return key 4460 = 0x116c from
   BASE = 0x864e4), a1 = A_OBJ 19, a2 = 3; first item 0x21211; the items are not all consecutive; no site compares
   equal. 1,272 instructions are walked to `ret`.

   Each call is one ca_bcmp_step (check_arity_s7.v),
   named HBS below. It needs the section's ABCMP (the statement's bcmp contract) and HVO (cmd_val_objs). The per-site
   tactic (ca0_run, ca0_call, ca0_branch below) is LOCAL to this file: one symbolic run to the call, the step, the
   `beqz a0` that follows, whose dead side ca_eq3 (a computation on the row's bytes) closes.

   The row lemma has the two hypotheses `getr regs0 3 = w64 (as_gp B)` and `getr regs0 4 = w64 (as_tp B)` beside
   ca_row_pre (the step needs gp and tp; the entry has both from afn_pre).

   Template, cited and not used: a former lib/A/Prog/check_arity.v: an earlier ASan walk in
   the OLD lib/Lib `evt` / MState framework against the OLD statement (bcmp_wrap_contract). Its first half (dots_loop,
   synloop, fmtloop) compiled in earlier builds by its author's account; its second half (rest of rows_loop,
   minv_entry, linv_entry, cont_ok, look_ok, check_arity_holds) was never built. It is a TEMPLATE, NOT A SOURCE:
   porting it is a rewrite into another execution model, and our concrete-run method needs none of its loop
   invariants. Its pcs are cross-checks of this walk: rows_loop head 0x87304, dots_loop 0x87638, fmtloop 0x873dc,
   the format arm 0x87368, the syntax arm 0x874d8. *)
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

(* The per-site tactic, local to this file. The walk's invariant lives in hypotheses found by their types:
   HS (the symbolic state), HJ (the journal), HEI (img_env), Usp / Hsp46 (sp), Egp / Etp (gp, tp), HRO (the read-only
   bytes of the entry), LK (ca_lowkept from the entry's memory), AG (the environment agrees with the entry's below
   A_LIM). *)

(* one symbolic run from HS to the next stop (a call of the bcmp wrapper, or `ret`); carries HJ and LK, and re-seats
   the model as a fresh variable (a chain of runs otherwise nests the model term) *)
Ltac ca0_run B RUNP RUNC :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_shc RUNP RUNC HS HJ;
    [ lazymatch goal with Usp : bv_unsigned (ew _ 2) = _ - 112 |- _ =>
        apply (ca_awr_sh B); [vm_compute; reflexivity | exact Usp] end
    | lazymatch goal with
      | Usp : bv_unsigned (ew _ 2) = _ - 112, LK : ca_lowkept _ ?m0 _,
        HFr : frame_of ?E ?rs (mrestrict _ ?m) (mrestrict _ ?m') |- _ =>
        let LK2 := fresh "LK" in
        pose proof (ca_lowkept_run E rs _ m m' m0 HFr ltac:(vm_compute; reflexivity) ltac:(rewrite Usp; lia) LK) as LK2;
        clear LK; rename LK2 into LK
      end;
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
      lazymatch goal with
      | HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?md) ?mat ?md)) _ =>
        let mdv := fresh "md" in
        set (mdv := with_vm_backing (m_vm_lazy md) mat md) in HJ' |- *; clearbody mdv; try clear mat; try clear md
      end ]
  end.

(* the `beqz a0` after a call: a0 is the junk atom kk + 4, zero exactly when ca_eq3 row x; one side dies *)
Ltac ca0_branch RUNP BR row x Hiff :=
  let e := eval vm_compute in (ca_eq3 row x) in
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => psrr_branch_pi RUNP BR HS end;
  [ lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
      lazymatch e with
      | false => exfalso; rewrite branch_eq_U, U_lit in Hc by lia; apply Z.eqb_eq in Hc;
                 let Hx := fresh "Hx" in pose proof (proj1 Hiff Hc) as Hx; vm_compute in Hx; discriminate Hx
      | true => clear Hc Hiff
      end end
  | lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
      lazymatch e with
      | true => exfalso; rewrite branch_eq_U, U_lit in Hc by lia; apply Z.eqb_neq in Hc; apply Hc, Hiff;
                vm_compute; reflexivity
      | false => clear Hc Hiff
      end end ].

(* the call at the wrapper's entry: one bcmp step (STEP), then sp, gp, tp and the agreement below A_LIM at the new
   environment *)
Ltac ca0_call RUNP BR STEP row kk :=
  lazymatch goal with
  | HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HEI : img_env _ _ ?E, Usp : bv_unsigned (ew ?E 2) = _ - 112, Hsp46 : 2 ^ 46 <= _ <= 2 ^ 47,
    Egp : ew ?E 3 = _, Etp : ew ?E 4 = _, HRO : cmd_ro_bytes _, LK : ca_lowkept _ _ _,
    AG : forall n, (n < A_LIM)%nat -> ew ?E n = ew ?E0 n
    |- SRr _ _ (mkCfg ?ms ?md) _ =>
    let x := eval vm_compute in (match sr_get (ss_regs ss) 10 with SLit v => v | _ => -1 end) in
    let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => -1 end) in
    idtac "ca0_call: kk" kk "x" x "retk" retk;
    apply (STEP row x retk kk E ss W ms md _ _ _ _ _ _ _ _ _ _ ltac:(lia) HEI ltac:(vm_compute; reflexivity)
             HS eq_refl HJ Usp Hsp46 Egp Etp HRO LK);
    clear HS HJ LK HEI;
    let E2 := fresh "E" in let ms2 := fresh "ms" in let md2 := fresh "md" in
    let AG2 := fresh "AG" in let Hiff := fresh "Hiff" in
    intros E2 ms2 md2 HEI AG2 HS HJ LK Hiff;
    rewrite <- (AG2 2%nat ltac:(lia)) in Usp;
    rewrite <- (AG2 3%nat ltac:(lia)) in Egp;
    rewrite <- (AG2 4%nat ltac:(lia)) in Etp;
    let AG' := fresh "AG" in
    pose proof (fun n (Hn : (n < A_LIM)%nat) =>
      eq_trans (AG2 n (Nat.lt_le_trans n A_LIM kk Hn ltac:(unfold A_LIM; lia))) (AG n Hn)) as AG';
    clear AG AG2; rename AG' into AG;
    try clear ms; try clear md; try clear E;
    ca0_branch RUNP BR row x Hiff
  end.

Ltac ca0_site B RUNP RUNC BR STEP row kk := ca0_run B RUNP RUNC; ca0_call RUNP BR STEP row kk.

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
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (PI := PI).

Hypothesis ABCMP : abcmp_realizes SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis HVO : cmd_val_objs.
(* the bcmp call step at every site (check_arity_s7.v) *)
Let HBS := ca_bcmp_step B HB ABCMP HVO.

Lemma ca_row_0 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre B 0 2 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post B regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP G3 G4.
pose proof (ca_row_open B HB 0 2 4 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO0 & Hsp & HFR & R3 & R4 & _).
pose proof (proj1 HRO0) as HRO. clear HRO0 HFR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
assert (Hsp46 : 2 ^ 46 <= spZ regs0 <= 2 ^ 47) by lia.
clear Hstk HSTK0 Hceil Hslo Hshi H47 Hc1 Hc2.
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs0 - 112).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). exact Hsp. }
assert (Egp : ew (Eimg (Ereg regs (ca_extra s3v regs0))) 3 = w64 (as_gp B)).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact (eq_trans R3 G3). }
assert (Etp : ew (Eimg (Ereg regs (ca_extra s3v regs0))) 4 = w64 (as_tp B)).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact (eq_trans R4 G4). }
assert (AG : forall n, (n < A_LIM)%nat ->
  ew (Eimg (Ereg regs (ca_extra s3v regs0))) n = ew (Eimg (Ereg regs (ca_extra s3v regs0))) n)
  by (intros; reflexivity).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
pose proof (ca_lowkept_refl W memc) as LK.
(* the 38 calls of row 0, at kk = A_LIM + 16 j *)
ca0_site B RUNP RUNC BR HBS 0%nat 1024%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1040%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1056%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1072%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1088%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1104%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1120%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1136%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1152%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1168%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1184%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1200%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1216%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1232%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1248%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1264%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1280%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1296%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1312%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1328%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1344%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1360%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1376%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1392%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1408%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1424%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1440%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1456%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1472%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1488%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1504%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1520%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1536%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1552%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1568%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1584%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1600%nat.
ca0_site B RUNP RUNC BR HBS 0%nat 1616%nat.
(* the last run, to `ret` *)
ca0_run B RUNP RUNC.
lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict (w_H W) ?ms) |- _ =>
  destruct (ca_regs_back_g (w_H W) E ss ms regs regs0 s3v HS (fun n Hn => AG n (Nat.lt_trans _ _ _ Hn A_LIM_text))
    ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'];
  eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity))
end.
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

End e.
End f.
End d.
