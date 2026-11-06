(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0 ..
   0x8a61c), in the form of sup_resp's walk (cgif lib/A/AChf.v, flushFrame): the prologue, the realignment
   `andi sp,sp,-32`, the use-after-return flag (1: `beqz a2` falls through), the class-7 side-stack frame of
   __asan_stack_malloc_7 (not 0: `bnez s2` skips the real-stack fallback), the frame's header and shadow, the two
   shadow fills, up to the BODY cut (answer_s1.v AN_BODY_stmt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e.v, with its module paths, module names and numbers changed; 225 of its 274 lines of code are new or changed and 546 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: written after lib/A/Prog/check_words_chain_s1.v for fuzz_command.asan-ubsan:
   module paths, the 224-byte frame, B's spill slots at the realigned stack pointer, B's closed state at the take. *)
(* The walk of check_words_chain on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan),
   stage 1: from the entry to the take of the side-stack frame (0x890e0 .. 0x89158, 30 instructions).

   The stage runs the verified symbolic executor from the seed of check_words_chain_s0.v to the realignment of
   the stack (andi sp,sp,-32 at 0x89120), steps over it by hand (the executor cannot keep a stack pointer
   through an and), gives the realigned stack pointer an atom (1024) and its spill slots [0, 120) a region of
   their own, keeps of the entry's stack region only the saved registers (sp0 - 104 .. sp0), and runs on to the
   call of the class-4 side-stack entry at 0x89158. On the way the code spills read (80), the shadow base (88)
   and the recorded call (56) and keeps the word array in s3; the executor reads the shadow base through the GOT
   word 0xa5f50 and the record's shadow cell, and the use-after-return flag through the GOT word 0xa5fa8 and
   the record's flag cell; the flag is 1 (a const cell of the record, AR_const_law), so it decides the branch at
   0x89150 itself. No instrumented check and no UBSan trap site lies in this stage.

   The stage is stated in continuation form: whatever the rest of the walk proves from the state at 0x89158
   (ss_cwc_sm, the closed symbolic state the executor computed there, copied verbatim), it proves from the
   entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaWalk CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_chain_c check_words_chain_s0.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
Hypothesis GREC_RA : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS).
Hypothesis GREC_NOT_RT : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Let RUNTO := paj_run_to B LAWS.

Definition ss_cwc_sm : sstate := (mkSS 11304
      [SLit 0; SOff 1 0; SOff 1024 0; SOff 3 0; SOff 4 0;
       SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 1024 0;
       SLit 992; SOff 32 0; SLit 1; SOff 13 0; SOff 14 0;
       SOff 15 0; SOff 16 0; SOff 17 0; SOff 18 0; SOff 11 0;
       SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0;
       SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
       SOff 30 0; SOff 31 0]
      [{|
         r_base := Some 1024%nat;
         r_lo := 0;
         r_hi := 120;
         r_wlo := 0;
         r_whi := 120;
         r_chunks :=
           [{| c_off := 56; YP09.c_val := CVal 8 (SOff 10 0) |};
            {| c_off := 88; YP09.c_val := CVal 8 (SOff 32 0) |};
            {| c_off := 80; YP09.c_val := CVal 8 (SOff 12 0) |}]
       |};
       {|
         r_base := Some 2%nat;
         r_lo := -104;
         r_hi := 0;
         r_wlo := -104;
         r_whi := 0;
         r_chunks :=
           [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
            {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
            {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
            {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
            {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
            {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
            {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
            {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
            {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
            {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
            {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
            {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
            {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
       |};
       {|
         r_base := Some 241%nat;
         r_lo := 0;
         r_hi := 8;
         r_wlo := 0;
         r_whi := 0;
         r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}]
       |};
       {|
         r_base := Some 253%nat;
         r_lo := 0;
         r_hi := 8;
         r_wlo := 0;
         r_whi := 0;
         r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}]
       |};
       {|
         r_base := Some 242%nat;
         r_lo := 0;
         r_hi := 8;
         r_wlo := 0;
         r_whi := 0;
         r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}]
       |};
       {|
         r_base := Some 33%nat;
         r_lo := 0;
         r_hi := 4;
         r_wlo := 0;
         r_whi := 0;
         r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}]
       |};
       {|
         r_base := Some 10%nat;
         r_lo := 4;
         r_hi := 56;
         r_wlo := 0;
         r_whi := 0;
         r_chunks :=
           [{| c_off := 4; YP09.c_val := CVal 4 (SLit 3) |};
            {| c_off := 16; YP09.c_val := CVal 8 (SOff 34 0) |};
            {| c_off := 24; YP09.c_val := CVal 8 (SOff 35 0) |}]
       |}]
      None
      {|
        f_atoms :=
          [(1024%nat,
            {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
           (2%nat,
            {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |});
           (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
           (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
           (33%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 2 |})];
        f_conds := [];
        f_alias := []
      |}).

Lemma cwc_to_sm : forall ly S W regs mem md ch cp p1 p2 (Q : world SEGS -> config -> Prop),
afn_pre SEGS B CHECK_WORDS_CHAIN_STK ly S W regs mem md ch ->
cmd_val_objs ->
getr regs 10 = w64 cp ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_NARGS) 4 3 ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_ARGS + 8) 8 p1 -> 0 <= p1 < 2 ^ 64 ->
aval_mem (aview SEGS (w_H W) mem) (cp + CALL_OFF_ARGS + 16) 8 p2 -> 0 <= p2 < 2 ^ 64 ->
(forall (E0 : env) (ms0 : machine_state) (mdq : Model) (sp1 : Z),
  img_env VAL A_LIM E0 ->
  st_ok_pi SEGS VAL E0 ss_cwc_sm (restrict (w_H W) ms0) ->
  sh_ok SEGS CWC_Bx cwc_SH E0 (mrestrict (w_H W) (ms_mem ms0)) ->
  ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms0) mdq 0 ->
  (forall n, (n < 33)%nat -> ew E0 n = ew (Eimg (Ereg regs (cwc_extra B p1 p2))) n) ->
  ew E0 1024 = Z_to_bv 64 sp1 -> ew E0 33 = Z_to_bv 64 (as_uar_cell B) ->
  sp1 = 32 * ((spZ regs + -224) / 32) -> sp1 mod 32 = 0 -> spZ regs - 240 <= sp1 <= spZ regs - 224 ->
  SRr SEGS W (mkCfg ms0 mdq) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + CWC_ENTRY) regs mem md) Q.
Proof.
intros ly S W regs mem md ch cp p1 p2 Q HPRE HOBJ H10 Hlo Hhi Vn V1 R1 V2 R2 HK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12528) by reflexivity.
pose proof (ajournal_init SEGS B CHECK_WORDS_CHAIN_STK [] ly S W regs mem md ch HPRE) as HJ.
edestruct cwc_seed_entry as [HS SHOK]; [ .. | ]; try eassumption.
set (E := Eimg (Ereg regs (cwc_extra B p1 p2))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E2w : ew E 2 = Z_to_bv 64 (spZ regs))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl);
unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
unfold cfg_at. change (w64 (BASE + CWC_ENTRY)) with (Z_to_bv 64 (BASE + CWC_ENTRY)).
paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan (AF_check_words_chain + 0x44).
{ unfold ss_cwc, cwc_regions, cwc_stack, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, cwc_grec.
cbn [ss_mem].
eapply (awr_ok_cons_stack SEGS B E);
[reflexivity | exact E2 | cbn; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
clear_frames.
(* the model term a run leaves doubles over a chain of runs (a 66 GB compile was measured), so each
   run's model is abstracted here as soon as it is made *)
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
set (mdv1 := mdx) in *; clearbody mdv1 end.
set (sp1 := 32 * ((spZ regs + -224) / 32)) in *.
destruct (snt_sp1_facts (spZ regs + -224) ltac:(lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hsp0al; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 240 <= sp1 <= spZ regs - 224) by lia. clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(snt_denot_and_m32 Ev 2 (spZ regs) (-224) ltac:(exact E2w)
ltac:(lia) ltac:(lia) ltac:(lia)) RSP end.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs (cwc_extra B p1 p2) 1)).
assert (E10 : ew E 10 = Z_to_bv 64 cp)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
pose proof (palf_uar_img B TLF) as Huar.
pose proof (pa_obj_img 0 ltac:(lia)) as Img0. pose proof (pa_obj_img 1 ltac:(lia)) as Img1.
pose proof (pa_obj_img 12 ltac:(lia)) as Img12.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1024 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 1024%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1024 : ew Ev 1024 = Z_to_bv 64 sp1)
by (rewrite HEv; exact (ew_havoc_new _ 1024 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (sh_ok_agree SEGS CWC_Bx cwc_SH 33 E Ev _
ltac:(rewrite HEv; exact (env_agree_havoc_ge 33 1024 E E _ ltac:(lia) (env_agree_refl 33 E)))
eq_refl SHOK) as SHOK2 end.
clear SHOK. rename SHOK2 into SHOK.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 1024 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite E1024, Z.add_0_r, Z_to_bv_bv_unsigned; cbn [ms_regs restrict mkst]; rewrite RSP; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 1024%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1024, unsigned_lit_small by lia;
change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss_pi HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1024%nat) 0 120 0 120 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E1024, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E1024, unsigned_lit_small by lia;
rewrite (AG 2%nat) by lia; rewrite E2;
lazymatch goal with HEIx : img_env VAL A_LIM Ev |- _ =>
rewrite (HEIx 241%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 242%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end;
cbn [A_OBJ Nat.add] in Img0, Img1, Img12;
rewrite E33, (AG 10%nat) by lia; rewrite E10, !unsigned_lit_small
by (unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia);
unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss_pi HS.
paj_run_to_tok RUNTO HS HJ SHOK CWC_Bspan CWC_SM.
{ lazymatch goal with |- awr_ok _ _ ?Ex _ _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off SEGS B Ex) with (d := sp1 - spZ regs);
[reflexivity | rewrite E1024, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |];
eapply (awr_ok_cons_stack SEGS B Ex); [reflexivity | rewrite (AG 2%nat) by lia; exact E2 | cbn; lia | cbn; lia |] end;
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex _ (restrict ?Hh ?msx) =>
change (st_ok_pi sg vl Ex ss_cwc_sm (restrict Hh msx)) in HS;
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
apply (HK Ex msx mdx sp1) end end;
first [assumption | reflexivity].
Qed.
End e.
End c.
End b.
