(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: renumbers the symbolic variables in E_KB, E_BK, E_TOP and E_R, threads the new launch parameters and an entry_launch_ok_va hypothesis through SINV/argH, and generalizes the geo/art check lemmas and as0_art_handoff_h over HSA r h; the launch input takes its SIGPIPE disposition as a variable sdf; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0ArtHandoffInstK.v, 65 lines within its lines 12-240. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Ja0HandoffK Ja0ArtCellsK Ja0ArtHandoffK Ja0CertK_202 Ja0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA ArtRuns ArtBridge JatInv JatFsInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition E_KB : expr := EMd M_MUL (ELit 4096) (EVar 228).
Definition E_BK : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 228)) (EMd M_MUL (ELit (-4096)) (EVar 229)).
Definition E_AND : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 229)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 228)) (ELit 65535)).
Definition E_PG : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 10)).
Definition E_TOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 10)) (EMd M_MUL (ELit 4096) (EVar 382))).
Definition E_BOT : expr := eaddz E_TOP (-8388608).
Definition E_R : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 382))) (ELit 3935).
Definition geo_chk (cs : acs) : bool :=
let k := kn cs in
(expr_eqb (am_base (role cs I_KSPACE)) E_KB && expr_eqb (bK cs) E_BK && expr_eqb (topE cs) E_TOP && expr_eqb (botE cs) E_BOT
&& existsb (kentry_eqb (KRange (EVar 229) 0 15)) k && existsb (kentry_eqb (KRange E_AND 0 0)) k
&& existsb (kentry_eqb (KRange (EVar 228) 4295491576 34326181871)) k
&& existsb (kentry_eqb (KRange (EVar 382) 0 1)) k && existsb (kentry_eqb (KRange (EVar 6) 0 255)) k
&& existsb (kentry_eqb (KRange E_R 0 4095)) k
&& existsb (kentry_eqb (KRange E_PG 140735340871680 140737488351232)) k
&& lin_nowrapR k E_KB && lin_nowrapR k E_BK && lin_nowrapR k E_TOP && lin_nowrapR k E_BOT && lin_nowrapR k E_PG && lin_nowrapR k E_R
&& lin_nowrapR k e_sp0)%bool.
Section Geo.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Variable mbase : word.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool.
Variable ur : InputStream.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdf : bool.
Variable apc : N.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
#[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variable cs : acs.
Hypothesis GCHK : geo_chk cs = true.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
Ltac LINEQ e H :=
let Hn := fresh in
assert (Hn : lin_nowrapR (kn cs) e = true)
by (let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
unfold LZ in H;
match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
rewrite ?Z.add_0_r in H.
Ltac RANGE K H :=
let Hi := fresh in
assert (Hi : In K (kn cs))
by (apply hb_knb_In; let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model K HC Hi) as H; clear Hi; cbn [kentry_ok] in H.
#[using="GCHK"] Lemma geo_syn : am_base (role cs I_KSPACE) = E_KB /\ bK cs = E_BK /\ topE cs = E_TOP /\ botE cs = E_BOT.
Proof.
pose proof GCHK as G. unfold geo_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]).
repeat split; apply expr_eqb_eq; assumption.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_spb : rbase E cs I_KSPACE < uE E (bK cs) + 0x10000 <= rbase E cs I_KSPACE + 65536 /\ (uE E (bK cs) + 0x10000) mod 65536 = 0.
Proof.
destruct geo_syn as (S1 & S2 & _ & _). unfold rbase. rewrite S1, S2. unfold uE.
remember (bv_unsigned (edenot E E_KB)) as kbz eqn:Ekbz. remember (bv_unsigned (edenot E E_BK)) as bk eqn:Ebk.
LINEQ E_KB L1. rewrite <- Ekbz in L1. LINEQ E_BK L2. rewrite <- Ebk in L2.
RANGE (KRange (EVar 229) 0 15) R1. RANGE (KRange (EVar 228) 4295491576 34326181871) R2. RANGE (KRange E_AND 0 0) R3.
cbn [edenot] in R1, R2. change (bv_unsigned (ev E 229)) with (VZ E 229) in R1. change (bv_unsigned (ev E 228)) with (VZ E 228) in R2.
unfold E_AND in R3. cbn [edenot] in R3. rewrite u_add64, u_and64, !u_mul64 in R3.
rewrite (u64_lit 65535), (u64_lit 4096) in R3 by lia.
replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520 in R3 by (vm_compute; reflexivity).
change (bv_unsigned (ev E 229)) with (VZ E 229) in R3. change (bv_unsigned (ev E 228)) with (VZ E 228) in R3.
change 65535 with (Z.ones 16) in R3. rewrite Z.land_ones in R3 by lia. change (2 ^ 16) with 65536 in R3.
rewrite (Z.mod_small (4096 * VZ E 228) (2 ^ 64)) in R3 by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (HA : (4096 * VZ E 228) mod 65536 = 4096 * VZ E 229) by lia.
subst kbz bk. rewrite L1, L2. split; [|]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_stk : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
/\ uE E e_sp0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= uE E e_sp0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.
Proof.
destruct geo_syn as (_ & _ & S3 & S4). rewrite S3, S4. unfold uE.
remember (bv_unsigned (edenot E E_TOP)) as top eqn:Et. remember (bv_unsigned (edenot E E_BOT)) as bot eqn:Eb.
remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. remember (bv_unsigned (edenot E E_PG)) as pg eqn:Ep.
remember (bv_unsigned (edenot E E_R)) as rr eqn:Er.
LINEQ E_TOP L1. rewrite <- Et in L1. LINEQ E_BOT L2. rewrite <- Eb in L2. LINEQ e_sp0 L3. rewrite <- Es in L3.
LINEQ E_PG L4. rewrite <- Ep in L4. LINEQ E_R L5. rewrite <- Er in L5.
RANGE (KRange (EVar 382) 0 1) R1. RANGE (KRange (EVar 6) 0 255) R2. RANGE (KRange E_R 0 4095) R3. RANGE (KRange E_PG 140735340871680 140737488351232) R4.
cbn [edenot] in R1, R2. change (bv_unsigned (ev E 382)) with (VZ E 382) in R1. change (bv_unsigned (ev E 6)) with (VZ E 6) in R2.
rewrite <- Er in R3. rewrite <- Ep in R4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs cs GCHK R FULL model HC"] Lemma geo_spa : uE E e_sp0 mod 16 = 0.
Proof.
unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
Lemma geo_sp16 : uE E e_sp0 + 16 <= 2 ^ 47.
Proof.
unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau E cs R FULL model HC) as U0.
unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit.
pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
pose proof (Nat2Z.is_nonneg (length argv)). pose proof (Nat2Z.is_nonneg (length envp)).
lia.
Qed.
End Geo.
Lemma geo_chk_HSA : forall r h, (h < 2)%nat -> geo_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_lits_chk_HSA : forall r h, (h < 2)%nat -> art_lits_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_sym_chk_HSA : forall r h, (h < 2)%nat -> art_sym_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_lazy_chk_HSA : forall r h, (h < 2)%nat -> art_lazy_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Section Inst.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Variable mbase : word.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool.
Variable ur : InputStream.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdf : bool.
Variable apc : N.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
#[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variable BUDGET : Z.
Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
Let FSH : art_fsinv_handoff := art_fsinv_handoff_proved.
#[using="BUD_ge"] Lemma inst_bud : 0 <= BUDGET /\ 0 <= JatInv.KMAX /\ 0 <= JatInv.LENMAX < 2 ^ 62.
Proof. unfold JatInv.KMAX, JatInv.LENMAX. lia. Qed.
Theorem as0_art_handoff_h : forall r h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
art_handoff_target art_fsg (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
(as0_BASEx (HSA r h) E) BUDGET art_fsinv (as0_rn E (HSA r h)) art_fsg0 K0D 8192 (2 ^ 34) (as0_A0x (HSA r h) E) FULL (vml_of model).
Proof.
intros r h Hh E R FULL model HC.
assert (CH : as0_chk (HSA r h) = true /\ art_lits_chk (HSA r h) = true /\ art_sym_chk (HSA r h) = true /\ geo_chk (HSA r h) = true /\ art_lazy_chk (HSA r h) = true).
{ exact (conj (as0_chk_HSA r h Hh) (conj (art_lits_chk_HSA r h Hh) (conj (art_sym_chk_HSA r h Hh) (conj (geo_chk_HSA r h Hh) (art_lazy_chk_HSA r h Hh))))). }
destruct CH as (C0 & CL & CS & CG & CZ).
destruct (HSA_numbers r h Hh) as (N1 & N2 & N3 & N4).
pose proof (geo_spb sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GS.
pose proof (geo_stk sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GT.
pose proof (geo_sp16 sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva (HSA r h) CG E R FULL model HC Hve Hfit Hlau) as G16.
pose proof (geo_spa sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GA.
assert (BL : a_eager (HSA r h) + a_abytes (HSA r h) + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT) by (unfold AsanInitK.LIMIT, target_alloc_limit; lia).
assert (GP : AsanCeil.bottomup_floor + JatInv.LENMAX + (a_totsz (HSA r h) + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps (HSA r h))) + JatInv.KMAX) * (JatInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling).
{ rewrite N4, asan0_res_eq. change (n_resx ASAN0) with 2%nat. cbn [length Nat.add]. change (Z.of_nat 23) with 23.
unfold JatInv.KMAX, JatInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. }
eapply (as0_art_handoff sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva (HSA r h)); try eassumption; first [exact inst_bud | exact FSH].
Qed.
End Inst.
